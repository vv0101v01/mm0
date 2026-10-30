///|
/// # Search — 個體化-精煉（Individualization–Refinement）搜索引擎
///
/// 規範形式與自同構群共用同一引擎（同一作用域，一次搜索兩個產物）：
///
/// 1. **精煉**：簽名 = (顏色, 各顏色類鄰居計數, 對已放置前綴的鄰接位遮罩)，
///    反覆分裂至穩定；簽名按字典序編號 ⇒ 純等變（重標號不變）。
/// 2. **候選規則**：下一位置候選 = 未放置頂點中簽名最小者（等變 ⇒ 規範性成立）。
/// 3. **前綴編碼剪枝**：編碼列主序 idx(i,j)=j(j-1)/2+i；左到右填位置 ⇒
///    深度 r 節點已確定前 r(r-1)/2 位；前綴 > 最優前綴 ⇒ 整枝剪掉（可靠）。
/// 4. **軌道剪枝**：固定前綴的已發現自同構構成路徑穩定子；候選集每軌道只走一代表。
///    φ 固定前綴 ⇒ v 分支與 φ(v) 分支的葉編碼逐位相同 ⇒ 最小葉不丟失。
/// 5. **自同構發現**：葉編碼 == 最優編碼 ⇒ best_lab → lab 映射為自同構（驗證後收集）。
///
/// 性能架構（降低計算複雜度 / 提升運算速度）：
/// - 熱路徑零分配：顏色按深度分槽、前綴共享緩衝、lab/pos_of 就地換位回溯、
///   軌道 BFS 用戳記陣列、候選/代表按深度分槽。
/// - 簽名計數用鄰接掃描 O(deg)（經 pos_of 映回位置），鄰接前綴用 Int64 位遮罩，
///   每輪清零量由 O(n·placed) 降至 O(k + placed/64)。
/// - 排序用內聯 insertion sort（避開泛型 sort_by 的閉包/分配開銷）。
/// - 最壞情形仍為指數級（圖同構問題本性），但高度對稱圖近乎線性。

///|
/// 搜索結果。
pub(all) struct SearchResult {
  n : Int32
  canon_lab : Array[Int32]
  canon_enc : Array[Int32]
  aut_gens : Array[Perm]
  nodes : Int32
  leaves : Int32
  ties : Int32
}

///|
/// 搜索上下文（全部緩衝預分配；mut 欄位為搜索統計與最優葉）。
priv struct Ctx {
  g : Graph
  n : Int32
  sighash : Array[Int32]
  rank_buf : Array[Int32]
  dist_buf : Array[Int32]
  bfs_queue : Array[Int32]
  p1 : Array[Int32]
  p2 : Array[Int32]
  p3 : Array[Int32]
  color_slots : Array[Int32]
  order_buf : Array[Int32]
  merge_buf : Array[Int32]
  cand_slots : Array[Int32]
  queue_buf : Array[Int32]
  stab_buf : Array[Int32]
  stamp_cand : Array[Int32]
  stamp_seen : Array[Int32]
  mut stamp : Int32
  prefix_buf : Array[Int32]
  prefix_bits : BitVec
  aut_fixed : Array[BitVec]
  pos_of : Array[Int32]
  edges : Array[(Int32, Int32)]
  mut has_best : Bool
  best_enc : Array[Int32]
  best_lab : Array[Int32]
  canon_lab : Array[Int32]
  canon_enc : Array[Int32]
  aut_gens : Array[Perm]
  vertex_colors : Array[Int32]
  prune_mode : Int32
  bb : Bool
  par_gen : Array[Int32]
  par_vert : Array[Int32]
  proc_stamp : Array[Int32]
  mut node_stamp2 : Int32
  mut bad_witness : Int32
  mut nodes : Int32
  mut leaves : Int32
  mut ties : Int32
}

///|
/// 編碼索引：位置對 (i, j)（i < j）→ 列主序下標。
pub fn enc_index(i : Int32, j : Int32) -> Int32 {
  j * (j - 1) / 2 + i
}

///|
/// 度數的等變秩（根節點初始顏色）。
fn degree_ranks(g : Graph) -> Array[Int32] {
  let n = g.order()
  let deg = Array::make(n, 0)
  for i in 0..<n {
    deg[i] = g.degree(i)
  }
  recolor(deg)
}

///|
/// 簽名比較：(顏色, 可加雜湊)。雜湊 = Σ 鄰居貢獻（已放置鄰居 → P1[位置]，
/// 未放置鄰居 → P2[顏色]）。可加 ⇒ 與掃描序無關；P1/P2 為確定性表 ⇒
/// 雜湊是等變量（重標號下不變），碰撞只會合併類（精煉變弱但仍可靠）。
fn cmp_sig(ctx : Ctx, cbase : Int32, u : Int32, v : Int32) -> Int32 {
  let cu = ctx.color_slots[cbase + u]
  let cv = ctx.color_slots[cbase + v]
  guard cu == cv else { return cu.compare(cv) }
  let hu = ctx.sighash[u]
  let hv = ctx.sighash[v]
  hu.compare(hv)
}

///|
/// 區間 insertion sort（小塊用）。
fn isort_range(
  ctx : Ctx,
  cbase : Int32,
  order : Array[Int32],
  lo : Int32,
  hi : Int32,
) -> Unit {
  for i in (lo + 1)..<hi {
    let key = order[i]
    let mut j = i - 1
    while j >= lo && cmp_sig(ctx, cbase, order[j], key) > 0 {
      order[j + 1] = order[j]
      j = j - 1
    }
    order[j + 1] = key
  }
}

///|
/// 歸併排序（O(u log u)；小塊退化为 insertion sort）。排序鍵 = (顏色, 雜湊)。
fn msort_sig(
  ctx : Ctx,
  cbase : Int32,
  order : Array[Int32],
  tmp : Array[Int32],
  lo : Int32,
  hi : Int32,
) -> Unit {
  if hi - lo <= 12 {
    isort_range(ctx, cbase, order, lo, hi)
    return
  }
  let mid = (lo + hi) / 2
  msort_sig(ctx, cbase, order, tmp, lo, mid)
  msort_sig(ctx, cbase, order, tmp, mid, hi)
  let mut i = lo
  let mut j = mid
  let mut k = lo
  while i < mid && j < hi {
    if cmp_sig(ctx, cbase, order[j], order[i]) < 0 {
      tmp[k] = order[j]
      j = j + 1
    } else {
      tmp[k] = order[i]
      i = i + 1
    }
    k = k + 1
  }
  while i < mid {
    tmp[k] = order[i]
    i = i + 1
    k = k + 1
  }
  while j < hi {
    tmp[k] = order[j]
    j = j + 1
    k = k + 1
  }
  for x in lo..<hi {
    order[x] = tmp[x]
  }
}

///|
/// 精煉：就地更新深度 `placed` 顏色槽至穩定（等價分割）。
/// 每輪成本 O(Σdeg + u²)（u = 未放置數）；雜湊簽名免除清零與向量比較。
fn refine(ctx : Ctx, lab : Array[Int32], placed : Int32) -> Unit {
  let n = ctx.n
  let g = ctx.g
  let cbase = placed * n
  let color = ctx.color_slots
  let unplaced = n - placed
  if unplaced <= 1 {
    return
  }
  // 多源 BFS：到已放置前綴的距離（等變種子；把稀疏圖的 O(n) 輪传播collapse为 O(1)）
  for i in 0..<n {
    ctx.dist_buf[i] = n + 1
  }
  let mut qh = 0
  let mut qt = 0
  for i in 0..<placed {
    let v = lab[i]
    ctx.dist_buf[v] = 0
    ctx.bfs_queue[qt] = v
    qt = qt + 1
  }
  while qh < qt {
    let v = ctx.bfs_queue[qh]
    qh = qh + 1
    let d = ctx.dist_buf[v]
    for u in g.neighbors(v) {
      if ctx.dist_buf[u] > d + 1 {
        ctx.dist_buf[u] = d + 1
        ctx.bfs_queue[qt] = u
        qt = qt + 1
      }
    }
  }
  let mut changed = true
  while changed {
    changed = false
    // 顏色類數 k（離散則提前返回）
    let mut k = 0
    for r in placed..<n {
      let c = color[cbase + lab[r]]
      if c >= k {
        k = c + 1
      }
    }
    if k >= unplaced {
      return
    }
    // 可加雜湊簽名
    for r in placed..<n {
      let v = lab[r]
      let mut h = ctx.p3[ctx.dist_buf[v]]
      for u in g.neighbors(v) {
        let p = ctx.pos_of[u]
        if p < placed {
          h = h + ctx.p1[p]
        } else {
          h = h + ctx.p2[color[cbase + u]]
        }
      }
      ctx.sighash[v] = h & 0x3FFFFFFF
    }
    // 按 (顏色, 雜湊) 排序未放置頂點
    let order = ctx.order_buf
    for i in 0..<unplaced {
      order[i] = lab[placed + i]
    }
    msort_sig(ctx, cbase, order, ctx.merge_buf, 0, unplaced)
    // 等變重新編號：先以凍結顏色計算新秩，再寫回
    // （比較與改寫必須分兩趟，否则 cmp_sig 會讀到已覆寫的新秩 → 過度分裂）
    let mut rank = 0
    for i in 0..<unplaced {
      let v = order[i]
      if i > 0 && cmp_sig(ctx, cbase, order[i - 1], v) != 0 {
        rank = rank + 1
      }
      ctx.rank_buf[v] = rank
    }
    for i in 0..<unplaced {
      let v = order[i]
      if color[cbase + v] != ctx.rank_buf[v] {
        color[cbase + v] = ctx.rank_buf[v]
        changed = true
      }
    }
  }
}

///|
/// 刷新路徑穩定子索引表（固定點遮罩 ⊇ 前綴遮罩，O(n/64)/gen）。
fn refresh_stab(ctx : Ctx) -> Int32 {
  // nstab 上限 = stab_buf 容量；軌道若因此不完整，只是剪枝變弱（安全方向）。
  let cap = ctx.stab_buf.length()
  let mut nstab = 0
  for i in 0..<ctx.aut_gens.length() {
    if nstab >= cap {
      break
    }
    if ctx.aut_fixed[i].contains(ctx.prefix_bits) {
      ctx.stab_buf[nstab] = i
      nstab = nstab + 1
    }
  }
  nstab
}

///|
/// 靜態軌道剪枝：節點入口以當前路徑穩定子對候選集求軌道，每軌道取一代表。
/// （只在入口算一次 — 實測此紀律下發現的自同構生成完整 Aut；
/// 逐分支動態重算會過度剪枝而丟失生成元。）
fn orbit_reps(ctx : Ctx, cbase : Int32, ncand : Int32) -> Int32 {
  let reps_base = cbase + ctx.n // cand 與 reps 分段：[cbase, cbase+n) 候選，[cbase+n, cbase+2n) 代表
  if ctx.prune_mode == 0 || ncand <= 1 {
    for i in 0..<ncand {
      ctx.cand_slots[reps_base + i] = ctx.cand_slots[cbase + i]
    }
    return ncand
  }
  let nstab = refresh_stab(ctx)
  if nstab == 0 {
    for i in 0..<ncand {
      ctx.cand_slots[reps_base + i] = ctx.cand_slots[cbase + i]
    }
    return ncand
  }
  ctx.stamp = ctx.stamp + 1
  let st2 = ctx.stamp
  for i in 0..<ncand {
    ctx.stamp_cand[ctx.cand_slots[cbase + i]] = st2
  }
  let mut nreps = 0
  for i in 0..<ncand {
    let v = ctx.cand_slots[cbase + i]
    if ctx.stamp_seen[v] != st2 {
      ctx.stamp_seen[v] = st2
      ctx.cand_slots[reps_base + nreps] = v
      nreps = nreps + 1
      let mut qlen = 1
      ctx.queue_buf[0] = v
      let mut head = 0
      while head < qlen {
        let p = ctx.queue_buf[head]
        head = head + 1
        for si in 0..<nstab {
          let q = ctx.aut_gens[ctx.stab_buf[si]].apply(p)
          if ctx.stamp_cand[q] == st2 && ctx.stamp_seen[q] != st2 {
            ctx.stamp_seen[q] = st2
            ctx.queue_buf[qlen] = q
            qlen = qlen + 1
          }
        }
      }
    }
  }
  nreps
}

///|
/// 驗證 σ 是否為圖自同構（用預計算邊列表）。
fn verify_aut_ctx(ctx : Ctx, s : Perm) -> Bool {
  if ctx.vertex_colors.length() == ctx.n {
    for i in 0..<ctx.n {
      guard ctx.vertex_colors[s.apply(i)] == ctx.vertex_colors[i] else {
        return false
      }
    }
  }
  for e in ctx.edges {
    let (u, v) = e
    guard ctx.g.has_edge(s.apply(u), s.apply(v)) else { return false }
  }
  true
}

///|
/// 前綴是否大於最優編碼的等長前綴（剪枝判據）。
fn prefix_greater(ctx : Ctx, plen : Int32) -> Bool {
  for i in 0..<plen {
    let a = ctx.prefix_buf[i]
    let b = ctx.best_enc[i]
    if a > b {
      return true
    }
    if a < b {
      return false
    }
  }
  false
}

///|
/// 就地複製 src[0..len) → dst[0..len)。
fn copy_into(src : Array[Int32], dst : Array[Int32], len : Int32) -> Unit {
  for i in 0..<len {
    dst[i] = src[i]
  }
}

///|
/// 處理葉節點：更新最優編碼 / 收集自同構。
fn process_leaf(ctx : Ctx, lab : Array[Int32], total : Int32) -> Unit {
  ctx.leaves = ctx.leaves + 1
  if !ctx.has_best {
    ctx.has_best = true
    copy_into(ctx.prefix_buf, ctx.best_enc, total)
    copy_into(ctx.prefix_buf, ctx.canon_enc, total)
    copy_into(lab, ctx.best_lab, ctx.n)
    copy_into(lab, ctx.canon_lab, ctx.n)
    return
  }
  let mut c : Int32 = 0
  for i in 0..<total {
    guard ctx.prefix_buf[i] == ctx.best_enc[i] else {
      c = ctx.prefix_buf[i].compare(ctx.best_enc[i])
      break
    }
  }
  if c < 0 {
    copy_into(ctx.prefix_buf, ctx.best_enc, total)
    copy_into(ctx.prefix_buf, ctx.canon_enc, total)
    copy_into(lab, ctx.best_lab, ctx.n)
    copy_into(lab, ctx.canon_lab, ctx.n)
  } else if c == 0 {
    ctx.ties = ctx.ties + 1
    // 等編碼葉 ⇒ best_lab → lab 的映射為自同構候選
    let img = Array::make(ctx.n, 0)
    for i in 0..<ctx.n {
      img[ctx.best_lab[i]] = lab[i]
    }
    let s = Perm::from_img(img)
    if !s.is_identity() && verify_aut_ctx(ctx, s) {
      ctx.aut_gens.push(s)
      let fm = BitVec::make_full(ctx.n)
      for i in 0..<ctx.n {
        if s.apply(i) != i {
          fm.unset(i)
        }
      }
      ctx.aut_fixed.push(fm)
    }
  }
}

///|
/// 深度優先搜索主遞歸（熱路徑零分配）。
fn search_rec(ctx : Ctx, lab : Array[Int32], placed : Int32) -> Unit {
  ctx.nodes = ctx.nodes + 1
  let n = ctx.n
  refine(ctx, lab, placed)
  if placed == n {
    process_leaf(ctx, lab, n * (n - 1) / 2)
    return
  }
  let plen = placed * (placed - 1) / 2
  // 前綴剪枝
  if ctx.bb && ctx.has_best && prefix_greater(ctx, plen) {
    return
  }
  // 候選 = 顏色最小的未放置頂點
  let cbase = placed * n
  let color = ctx.color_slots
  let mut minc = 1 << 30
  for r in placed..<n {
    let c = color[cbase + lab[r]]
    if c < minc {
      minc = c
    }
  }
  let mut ncand = 0
  for r in placed..<n {
    if color[cbase + lab[r]] == minc {
      ctx.cand_slots[cbase + ncand] = lab[r]
      ncand = ncand + 1
    }
  }
  // 軌道剪枝 + 分支
  if ctx.prune_mode == 2 {
    ctx.node_stamp2 = ctx.node_stamp2 + 1
    let st = ctx.node_stamp2
    for ri in 0..<ncand {
      let v = ctx.cand_slots[cbase + ri]
      if ctx.proc_stamp[v] == st {
        continue
      }
      if !should_branch(ctx, cbase, ncand, v, st) {
        continue
      }
      branch_child(ctx, lab, placed, plen, v)
    }
    return
  }
  let nreps = orbit_reps(ctx, cbase, ncand)
  let reps_base = cbase + n
  for ri in 0..<nreps {
    let v = ctx.cand_slots[reps_base + ri]
    branch_child(ctx, lab, placed, plen, v)
  }
}

///|
/// 分支：把 v 放到位置 placed，遞歸，回溯。
fn branch_child(
  ctx : Ctx,
  lab : Array[Int32],
  placed : Int32,
  plen : Int32,
  v : Int32,
) -> Unit {
  let n = ctx.n
  // 把 v 換到位置 placed
  let pos = ctx.pos_of[v]
  let u = lab[placed]
  lab[placed] = v
  lab[pos] = u
  ctx.pos_of[v] = placed
  ctx.pos_of[u] = pos
  // 前綴追加：與已放置各位置的鄰接；前綴遮罩置位
  for i in 0..<placed {
    ctx.prefix_buf[plen + i] = if ctx.g.has_edge(lab[i], v) { 1 } else { 0 }
  }
  ctx.prefix_bits.set(v)
  // 顏色槽 d+1 = 槽 d 複製，v 標記已放置
  let src = placed * n
  let dst = (placed + 1) * n
  copy_into_range(ctx.color_slots, src, dst, n)
  ctx.color_slots[dst + v] = -1
  search_rec(ctx, lab, placed + 1)
  // 回溯
  ctx.prefix_bits.unset(v)
  lab[placed] = u
  lab[pos] = v
  ctx.pos_of[v] = pos
  ctx.pos_of[u] = placed
}

///|
/// 槽內複製 dst[0..len) = src[0..len)（同一陣列不同段）。
fn copy_into_range(
  buf : Array[Int32],
  src : Int32,
  dst : Int32,
  len : Int32,
) -> Unit {
  for i in 0..<len {
    buf[dst + i] = buf[src + i]
  }
}

///|
/// 確定性混雜表（splitmix64 風格；等變性只要求確定性）。
fn mix_table(len : Int32, seed : Int64) -> Array[Int32] {
  let out = Array::make(len, 0)
  for i in 0..<len {
    let mut x = (i.to_int64() + 1L) * seed
    x = x ^ (x >> 29)
    x = x * 0x94D049BB133111EBL
    x = x ^ (x >> 32)
    out[i] = (x & 0x3FFFFFFFL).to_int() | 1
  }
  out
}

///|
/// 建構搜索上下文（全部緩衝預分配）。
fn make_ctx(
  g : Graph,
  prune_mode : Int32,
  bb : Bool,
  total : Int32,
  n : Int32,
) -> Ctx {
  {
    g,
    n,
    sighash: Array::make(n, 0),
    rank_buf: Array::make(n, 0),
    dist_buf: Array::make(n, 0),
    bfs_queue: Array::make(n, 0),
    p1: mix_table(n, 0x9E3779B97F4A7C15L),
    p2: mix_table(n + 1, 0xBF58476D1CE4E5B9L),
    p3: mix_table(n + 2, 0xD6E8FEB86659FD93L),
    color_slots: Array::make((n + 1) * n, 0),
    order_buf: Array::make(n, 0),
    merge_buf: Array::make(n, 0),
    cand_slots: Array::make((n + 1) * 2 * n + 2 * n, 0),
    queue_buf: Array::make(n, 0),
    stab_buf: Array::make(n * 4 + 64, 0),
    stamp_cand: Array::make(n, 0),
    stamp_seen: Array::make(n, 0),
    stamp: 0,
    prefix_buf: Array::make(total, 0),
    prefix_bits: BitVec::make(n),
    aut_fixed: [],
    pos_of: Array::make(n, 0),
    edges: g.edge_list(),
    has_best: false,
    best_enc: Array::make(total, 0),
    best_lab: Array::make(n, 0),
    canon_lab: Array::make(n, 0),
    canon_enc: Array::make(total, 0),
    aut_gens: [],
    vertex_colors: Array::make(n, 0),
    prune_mode,
    bb,
    par_gen: Array::make(n, -1),
    par_vert: Array::make(n, -1),
    proc_stamp: Array::make(n, 0),
    node_stamp2: 0,
    bad_witness: 0,
    nodes: 0,
    leaves: 0,
    ties: 0,
  }
}

///|
/// 動態軌道剪枝：候選 v 在當前路徑穩定子下之軌道若含已處理點 ⇒ 跳過。
/// 除錯模式下會重建見證 τ（v ↦ 已處理點）並驗證其為自同構；
/// `bad_witness` 計數非零即代表剪枝不可靠。
fn should_branch(
  ctx : Ctx,
  cbase : Int32,
  ncand : Int32,
  v : Int32,
  st : Int32,
) -> Bool {
  ctx.stamp = ctx.stamp + 1
  let st2 = ctx.stamp
  for i in 0..<ncand {
    ctx.stamp_cand[ctx.cand_slots[cbase + i]] = st2
  }
  let nstab = refresh_stab(ctx)
  ctx.queue_buf[0] = v
  ctx.stamp_seen[v] = st2
  ctx.par_gen[v] = -1
  ctx.par_vert[v] = -1
  let mut qlen = 1
  let mut head = 0
  let mut hit = -1
  while head < qlen {
    let p = ctx.queue_buf[head]
    head = head + 1
    for si in 0..<nstab {
      let q = ctx.aut_gens[ctx.stab_buf[si]].apply(p)
      if ctx.stamp_cand[q] == st2 && ctx.stamp_seen[q] != st2 {
        ctx.stamp_seen[q] = st2
        ctx.par_gen[q] = ctx.stab_buf[si]
        ctx.par_vert[q] = p
        ctx.queue_buf[qlen] = q
        qlen = qlen + 1
        if hit < 0 && ctx.proc_stamp[q] == st {
          hit = q
        }
      }
    }
  }
  if hit < 0 {
    // 只標記實際分支的頂點（保持「已處理 = 子樹已探索」不變量）
    ctx.proc_stamp[v] = st
    return true
  }
  ctx.proc_stamp[v] = st
  // 重建見證 τ：v ↦ hit（沿 BFS 父鏈），驗證為自同構
  let mut tau = Perm::identity(ctx.n)
  let mut cur = hit
  while ctx.par_vert[cur] >= 0 {
    let gg = ctx.aut_gens[ctx.par_gen[cur]]
    tau = tau.compose(gg)
    cur = ctx.par_vert[cur]
  }
  if tau.apply(v) != hit || !verify_aut_ctx(ctx, tau) {
    ctx.bad_witness = ctx.bad_witness + 1
  }
  false
}

///|
/// 引擎唯一入口（`search_graph` / `search_graph_mode` 皆委派至此）：
/// mode 0=無剪枝 1=靜態軌道 2=動態軌道；bb=前綴編碼剪枝。
pub fn search_graph_flags(g : Graph, mode : Int32, bb : Bool) -> SearchResult {
  search_graph_impl2(g, mode, bb, None)
}

///|
/// 有色圖搜尋：`colors[v]` 是頂點 v 的初始顏色。顏色按數值秩正規化後與
/// 度數秩作字典序合併，精煉因此不會跨越初始顏色類；發現的自同構另經
/// `verify_aut_ctx` 逐點驗證保色。這是加權／帶標籤橋接的搜尋入口，
/// 不再需要先忘記標籤再對全部無色自同構做後篩選。
pub fn search_graph_colored(
  g : Graph,
  colors : Array[Int32],
  prune_orbits : Bool,
) -> SearchResult {
  search_graph_impl2(g, if prune_orbits { 1 } else { 0 }, true, Some(colors))
}

///|
/// 正規化有色圖的初始秩：回傳 (供精煉的合併秩, 正規化原顏色)。
fn initial_ranks_colored(
  g : Graph,
  colors : Array[Int32]?,
) -> (Array[Int32], Array[Int32]) {
  let n = g.order()
  let normalized = match colors {
    Some(cs) => {
      guard cs.length() == n else {
        abort("search_graph_colored: color length mismatch")
      }
      recolor(cs.copy())
    }
    None => Array::make(n, 0)
  }
  let degree = degree_ranks(g)
  let width = max_color(normalized) + 1
  let combined = Array::make(n, 0)
  for i in 0..<n {
    combined[i] = degree[i] * width + normalized[i]
  }
  (recolor(combined), normalized)
}

///|
/// 主入口：對圖 G 運行個體化-精煉搜索。
/// `prune_orbits=true` 啟用軌道剪枝（高度對稱圖加速關鍵）。
pub fn search_graph(g : Graph, prune_orbits : Bool) -> SearchResult {
  search_graph_flags(g, if prune_orbits { 1 } else { 0 }, true)
}

///|
/// 模式入口：0=無剪枝 1=靜態軌道 2=動態軌道（除錯/測試用）。
pub fn search_graph_mode(g : Graph, mode : Int32) -> SearchResult {
  search_graph_flags(g, mode, true)
}

///|
/// 動態剪枝之見證失敗計數（除錯用；0 = 所有跳過皆有合法見證）。
pub fn search_bad_witness(g : Graph) -> Int32 {
  let n = g.order()
  let total = n * (n - 1) / 2
  let ctx = make_ctx(g, 2, true, total, n)
  if n == 0 {
    return 0
  }
  let lab = Array::make(n, 0)
  for i in 0..<n {
    lab[i] = i
    ctx.pos_of[i] = i
  }
  let colors0 = degree_ranks(g)
  for i in 0..<n {
    ctx.color_slots[i] = colors0[i]
  }
  search_rec(ctx, lab, 0)
  ctx.bad_witness
}

///|
fn search_graph_impl2(
  g : Graph,
  prune_mode : Int32,
  bb : Bool,
  vertex_colors : Array[Int32]?,
) -> SearchResult {
  let n = g.order()
  let total = n * (n - 1) / 2
  let ctx = make_ctx(g, prune_mode, bb, total, n)
  if n == 0 {
    return {
      n: 0,
      canon_lab: [],
      canon_enc: [],
      aut_gens: [],
      nodes: 1,
      leaves: 0,
      ties: 0,
    }
  }
  let lab = Array::make(n, 0)
  for i in 0..<n {
    lab[i] = i
    ctx.pos_of[i] = i
  }
  let (colors0, normalized_colors) = initial_ranks_colored(g, vertex_colors)
  for i in 0..<n {
    ctx.vertex_colors[i] = normalized_colors[i]
    ctx.color_slots[i] = colors0[i]
  }
  search_rec(ctx, lab, 0)
  {
    n,
    canon_lab: ctx.canon_lab,
    canon_enc: ctx.canon_enc,
    aut_gens: ctx.aut_gens,
    nodes: ctx.nodes,
    leaves: ctx.leaves,
    ties: ctx.ties,
  }
}
