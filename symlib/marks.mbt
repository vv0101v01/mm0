///|
/// # Marks — 子群共軛類、標記向量、Burnside 環之 table of marks
///
/// 把 G-集之同構類轉譯成**整數向量**，於是同構判定變成向量比較（O(類數)），
/// 而不是逐點比對（O(|X|!)）。
///
/// - `Sub { order, members, group }`：子群（members 為排序後之元素表）
/// - `subgroup_classes(G, cap)`：共軛類代表（n ≤ 5 窮舉 ≤2 生成元之子群；
///   ng > 24 時只列循環子群 ⇒ 類數為下界）
/// - `gset_mark(X, H)` = |X^H|（H 之全局不動點數）、`mark_vector(X, subs)`
/// - `table_of_marks(G, subs)`：M[i][j] = |(G/H_i)^{H_j}|（**下三角、對角正** ⇒
///   標記向量為 G-集之完全不變量）；`table_of_marks_formula` 以
///   M_ij = |{gH_i : H_j ⊆ gH_ig^{-1}}| 獨立重算 ⇒ 互為證人
/// - `coset_reps` / `coset_gset`：G/H 之 G-集
/// - `marks_cert(G, cap)`：兩條公式一致 + 下三角 + 對角正 + Burnside 一致性
/// - `gset_isomorphic` / `gset_canon_key`：以標記向量判同構
/// - `frobenius_reciprocity(H ≤ G, X)`：⟨Ind_H^G Y, X⟩_G = ⟨Y, Res_H X⟩_H（以不動點計數驗證）

///|
/// 子群（以元素索引之位向量表示；`members` 為 G 元素列表中屬於 H 者）。
pub(all) struct Sub {
  order : Int64
  members : BitVec
  group : PermGroup
}

///|
/// 子群 H 之不動點數 |X^H| = 標記 m_H(X)。
pub fn gset_mark(gs : GSetOf, h : Sub) -> Int32 {
  let idxs = h.members.to_array()
  let mut c = 0
  for y in 0..<gs.x {
    let mut ok = true
    for i in idxs {
      if gs.imgs[i][y] != y {
        ok = false
        break
      }
    }
    if ok {
      c = c + 1
    }
  }
  c
}

///|
/// 標記向量（依 `subgroup_classes` 之順序）。
pub fn mark_vector(gs : GSetOf, subs : Array[Sub]) -> Array[Int32] {
  let v : Array[Int32] = []
  for h in subs {
    v.push(gset_mark(gs, h))
  }
  v
}

///|
/// 子群集合之雜湊桶（BitVec::hash → 索引表）：去重與共軛併類之 O(1) 查找，
/// 免建字串鍵（每次 O(|H|) 配置 + O(|H|²) 複製）。碰撞以 `BitVec::equal` 排除。
fn sub_lookup(
  buckets : Map[Int32, Array[Int32]],
  mems : Array[BitVec],
  bv : BitVec,
) -> Int32 {
  match buckets.get(bv.hash()) {
    Some(list) => {
      let mut hit = -1
      for j in list {
        if mems[j].equal(bv) {
          hit = j
          break
        }
      }
      hit
    }
    None => -1
  }
}

///|
/// 子群共軛類（以 ≤2 個元素生成之子群窮舉 + 共軛併類）。
///
/// **衍生演算法加速**（三項）：
/// 1. 候選子群之元素表以「乘法閉包 BFS」直接求得（O(|H|·2) 次合成），
///    而非對每個生成對建一次 Schreier–Sims（O(n²|H|) 量級）；
///    SGS 只為**倖存的共軛類代表**建構一次。
/// 2. 熱迴圈以 `compose_key64` 由像陣列直接算鍵 ⇒ 零 Perm 配置。
/// 3. 若 b ∈ ⟨a⟩（或 a ∈ ⟨b⟩）則 ⟨a,b⟩ 已於 (a,a)/(b,b) 記錄 ⇒ 跳過該對；
///    去重與共軛併類以 Map（位向量鍵）取代 O(ns·ng) 之線性掃描。
///
/// ng ≤ 24 時窮舉全部生成對（n ≤ 5 之對稱群：全部子群皆 ≤2 生成 ⇒ 完整）；
/// ng > 24 時只取循環子群（標記向量退化為**部分**不變量，此為已知限制）。///
/// **結構**：本函數只是三步之組合，細節拆入下方私有輔助（去債：原為 204 行單體 + 3 個巢狀閉包）：
/// `sub_table`（元素表）→ `sub_candidates`（候選枚舉 + 去重）→ `merge_conjugate_classes`（共軛併類 + 建 SGS）。
/// 另：循環子群 ⟨a⟩ 之閉包**只算一次**並由 `cyc` 快取重用（原實作在快取與主迴圈各算一次）。
pub fn subgroup_classes(group : PermGroup, cap : Int32) -> Array[Sub] {
  let t = sub_table(group, cap)
  let c = sub_candidates(t, cap)
  // 依 |H| 升冪（標記矩陣之三角性需要此序）
  merge_conjugate_classes(t, c, group)
}

///|
/// 元素表：`elems[i]` 為第 i 個群元素、`imgs[i]` 為其像表、`lut` 提供 O(1) 元素→索引。
priv struct SubTable {
  n : Int32
  ng : Int32
  elems : Array[Perm]
  imgs : Array[Array[Int32]]
  lut : KeyLut
  id_idx : Int32
}

///|
/// 建立元素表（`|G| > cap` 時 `PermGroup::elements` 會 abort）。
fn sub_table(group : PermGroup, cap : Int32) -> SubTable {
  let elems = group.elements(cap)
  let n = group.size()
  let ng = elems.length()
  let lut = elem_lut_fast(elems)
  let imgs : Array[Array[Int32]] = []
  for e in elems {
    imgs.push(e.img)
  }
  let id_img = Array::make(n, 0)
  for i in 0..<n {
    id_img[i] = i
  }
  let id_idx = lut.at(perm_key64(Perm::from_img(id_img)))
  { n, ng, elems, imgs, lut, id_idx, }
}

///|
/// ⟨elems[a], elems[b]⟩ 之乘法閉包（BFS + 元素表查索引）；超過 cap 回 None。
fn sub_closure(t : SubTable, a : Int32, b : Int32, cap : Int32) -> BitVec? {
  let mem = BitVec::make(t.ng)
  let queue : Array[Int32] = [t.id_idx]
  mem.set(t.id_idx)
  let ia = t.imgs[a]
  let ib = t.imgs[b]
  let mut head = 0
  while head < queue.length() {
    let x = t.imgs[queue[head]]
    head = head + 1
    let y1 = t.lut.at(compose_key64(x, ia))
    if !mem.get(y1) {
      mem.set(y1)
      queue.push(y1)
      if queue.length() > cap {
        return None
      }
    }
    let y2 = t.lut.at(compose_key64(x, ib))
    if !mem.get(y2) {
      mem.set(y2)
      queue.push(y2)
      if queue.length() > cap {
        return None
      }
    }
  }
  Some(mem)
}

///|
/// ≤2 生成元之子群候選（去重後之成員位向量、其生成元對、雜湊桶索引）。
priv struct SubCands {
  mems : Array[BitVec]
  gens2 : Array[(Int32, Int32)]
  buckets : Map[Int32, Array[Int32]]
}

///|
/// 記錄一個候選子群（以雜湊桶 + `sub_lookup` 去重）。
fn sub_record(c : SubCands, a : Int32, b : Int32, mem : BitVec) -> Unit {
  if sub_lookup(c.buckets, c.mems, mem) < 0 {
    let h = mem.hash()
    match c.buckets.get(h) {
      Some(list) => list.push(c.mems.length())
      None => c.buckets.set(h, [c.mems.length()])
    }
    c.mems.push(mem)
    c.gens2.push((a, b))
  }
}

///|
/// 候選子群枚舉：ng ≤ 24 時全部生成對，否則只列循環子群（見 `subgroup_classes` 文件）。
fn sub_candidates(t : SubTable, cap : Int32) -> SubCands {
  let c : SubCands = { mems: [], gens2: [], buckets: Map([]), }
  // 循環子群快取：cyc[a] = ⟨a⟩（失敗時為空位向量 ⇒ 成員測試自然為 false）
  let cyc : Array[BitVec] = []
  let cyc_ok : Array[Bool] = []
  for a in 0..<t.ng {
    match sub_closure(t, a, a, cap) {
      Some(mem) => {
        cyc.push(mem)
        cyc_ok.push(true)
      }
      None => {
        cyc.push(BitVec::make(t.ng))
        cyc_ok.push(false)
      }
    }
  }
  let pairs = t.ng <= 24
  for a in 0..<t.ng {
    if cyc_ok[a] {
      sub_record(c, a, a, cyc[a])
    }
    if pairs {
      for b in (a + 1)..<t.ng {
        // b ∈ ⟨a⟩ 或 a ∈ ⟨b⟩ ⇒ ⟨a,b⟩ 已於 (a,a)/(b,b) 記錄
        if cyc[a].get(b) || cyc[b].get(a) {
          continue
        }
        match sub_closure(t, a, b, cap) {
          Some(mem) => sub_record(c, a, b, mem)
          None => ()
        }
      }
    }
  }
  c
}

///|
/// union-find 之代表元（ns 小 ⇒ 不需路徑壓縮）。
fn uf_find(parent : Array[Int32], a : Int32) -> Int32 {
  let mut r = a
  while parent[r] != r {
    r = parent[r]
  }
  r
}

///|
/// 共軛併類 → 取代表 → 只為代表建 SGS。
///
/// **共軛類 = 共軛作用之軌道** ⇒ 只需以群之生成元做 BFS 閉包：
/// O(Σ軌道長·|gens|·|H|·n)，而原逐元素共軛為 O(ng·ns·|H|·n)，|gens| ≪ ng。
fn merge_conjugate_classes(
  t : SubTable,
  c : SubCands,
  group : PermGroup,
) -> Array[Sub] {
  let ns = c.mems.length()
  let parent = Array::make(ns, 0)
  for i in 0..<ns {
    parent[i] = i
  }
  let members : Array[Array[Int32]] = []
  for m in c.mems {
    members.push(m.to_array())
  }
  let gimgs : Array[Array[Int32]] = []
  let ginvs : Array[Array[Int32]] = []
  for p in group.generators() {
    gimgs.push(p.img)
    let inv = Array::make(t.n, 0)
    for v in 0..<t.n {
      inv[p.img[v]] = v
    }
    ginvs.push(inv)
  }
  let tmp = Array::make(t.n, 0)
  let visited = Array::make(ns, false)
  for i in 0..<ns {
    if visited[i] {
      continue
    }
    visited[i] = true
    let queue : Array[Int32] = [i]
    let mut head = 0
    while head < queue.length() {
      let cur = queue[head]
      head = head + 1
      let mcur = members[cur]
      for gi in 0..<gimgs.length() {
        let conj = BitVec::make(t.ng)
        for idx in mcur {
          let eimg = t.imgs[idx]
          let ginv = ginvs[gi]
          for v in 0..<t.n {
            tmp[v] = eimg[ginv[v]]
          }
          conj.set(t.lut.at(compose_key64(gimgs[gi], tmp)))
        }
        let j = sub_lookup(c.buckets, c.mems, conj)
        // j < 0：共軛像不在 ≤2 生成候選中（一般情形之部分不變量）
        if j >= 0 {
          let ra = uf_find(parent, cur)
          let rb = uf_find(parent, j)
          if ra != rb {
            parent[rb] = ra
          }
          if !visited[j] {
            visited[j] = true
            queue.push(j)
          }
        }
      }
    }
  }
  // 每類取代表（依 (階, 成員表) 排序 ⇒ 決定性）
  let cand : Array[(Int64, Array[Int32], Int32)] = []
  for i in 0..<ns {
    if uf_find(parent, i) == i {
      cand.push((c.mems[i].count_ones().to_int64(), members[i], i))
    }
  }
  cand.sort_by(fn(
    x : (Int64, Array[Int32], Int32),
    y : (Int64, Array[Int32], Int32),
  ) -> Int32 {
    if x.0 != y.0 {
      if x.0 < y.0 {
        -1
      } else {
        1
      }
    } else {
      cmp_arr(x.1, y.1)
    }
  })
  let out : Array[Sub] = []
  for trip in cand {
    let r = trip.2
    let (a, b) = c.gens2[r]
    out.push({
      order: c.mems[r].count_ones().to_int64(),
      members: c.mems[r],
      group: PermGroup::new(t.n, [t.elems[a], t.elems[b]]),
    })
  }
  out
}

///|
/// 標記矩陣（table of marks）：M[i][j] = m_{H_i}(G/H_j) = #(H_i 固定之 H_j-陪集)。
/// 以陪集作用直接計算（第一種算法）。
pub fn table_of_marks(
  group : PermGroup,
  subs : Array[Sub],
  cap : Int32,
) -> Array[Array[Int32]] {
  // 每個 H_j 之陪集 G-集只需建一次
  let cosets : Array[GSetOf] = []
  for k in subs {
    cosets.push(coset_gset(group, k, cap))
  }
  // 三角性剪枝（定理）：H 固定某 H_j-陪集 ⇔ g⁻¹Hg ⊆ H_j ⇒ |H| ≤ |H_j|；
  // 故 |H| > |H_j| 時標記必為 0，免算陪集作用。
  let m : Array[Array[Int32]] = []
  for h in subs {
    let row : Array[Int32] = []
    for j, gs in cosets {
      row.push(if h.order > subs[j].order { 0 } else { gset_mark(gs, h) })
    }
    m.push(row)
  }
  m
}

///|
/// 標記矩陣之公式算法：M[i][j] = #{ 陪集 gH_j : g^{-1}H_i g ⊆ H_j }。
pub fn table_of_marks_formula(
  group : PermGroup,
  subs : Array[Sub],
  cap : Int32,
) -> Array[Array[Int32]] {
  let elems = group.elements(cap)
  let ng = elems.length()
  let n = group.size()
  let lut = elem_lut_fast(elems)
  let imgs : Array[Array[Int32]] = []
  for e in elems {
    imgs.push(e.img)
  }
  // 陪集代表只需算一次（原實作於雙重迴圈內重算 ns 次）
  let reps_all : Array[Array[Int32]] = []
  for k in subs {
    reps_all.push(coset_reps(elems, k, lut, ng))
  }
  // 零配置熱路徑：r⁻¹hr 之鍵直接由像陣列算出（免 Perm 配置）
  let hmem : Array[Array[Int32]] = []
  for h in subs {
    hmem.push(h.members.to_array())
  }
  let tmp = Array::make(group.size(), 0)
  let m : Array[Array[Int32]] = []
  for hi, h in subs {
    let row : Array[Int32] = []
    let hidx = hmem[hi]
    for kj, k in subs {
      // 三角性剪枝：|H| > |K| ⇒ 無陪集被 H 固定
      if h.order > k.order {
        row.push(0)
        continue
      }
      let reps = reps_all[kj]
      let mut c = 0
      for r in reps {
        let rimg = imgs[r]
        // r⁻¹ 之像
        let rinv = Array::make(n, 0)
        for v in 0..<n {
          rinv[rimg[v]] = v
        }
        let mut ok = true
        for idx in hidx {
          let eimg = imgs[idx]
          for v in 0..<n {
            tmp[v] = eimg[rimg[v]]
          }
          let ci = lut.at(compose_key64(rinv, tmp))
          if !k.members.get(ci) {
            ok = false
            break
          }
        }
        if ok {
          c = c + 1
        }
      }
      row.push(c)
    }
    m.push(row)
  }
  m
}

///|
/// H 之左陪集代表（元素索引）。
fn coset_reps(
  elems : Array[Perm],
  h : Sub,
  lut : KeyLut,
  ng : Int32,
) -> Array[Int32] {
  let seen = Array::make(ng, false)
  let reps : Array[Int32] = []
  let hidx = h.members.to_array()
  for g in 0..<ng {
    if !seen[g] {
      reps.push(g)
      let gimg = elems[g].img
      for k in hidx {
        seen[lut.at(compose_key64(gimg, elems[k].img))] = true
      }
    }
  }
  reps
}

///|
/// 陪集 G-集 G/H（左乘作用）。
pub fn coset_gset(group : PermGroup, h : Sub, cap : Int32) -> GSetOf {
  let elems = group.elements(cap)
  let ng = elems.length()
  let lut = elem_lut_fast(elems)
  // 零配置熱路徑：compose_key64 直接由像陣列算鍵 + KeyLut 開放定址查找
  let imgs0 : Array[Array[Int32]] = []
  for e in elems {
    imgs0.push(e.img)
  }
  // 元素索引 → 陪集編號
  let coset_of = Array::make(ng, -1)
  let reps = coset_reps(elems, h, lut, ng)
  let hidx = h.members.to_array()
  for ci, r in reps {
    let rimg = imgs0[r]
    for k in hidx {
      coset_of[lut.at(compose_key64(rimg, imgs0[k]))] = ci
    }
  }
  let nc = reps.length()
  let imgs : Array[Array[Int32]] = []
  for ei in 0..<ng {
    let eimg = imgs0[ei]
    let img = Array::make(nc, 0)
    for ci, r in reps {
      img[ci] = coset_of[lut.at(compose_key64(eimg, imgs0[r]))]
    }
    imgs.push(img)
  }
  { x: nc, imgs, }
}

///|
/// 標記定理之機器證書：
/// (a) 兩種算法（陪集作用直接計算 / 共軛包含公式）之標記矩陣一致；
/// (b) 下三角性：|H_i| > |H_j| ⇒ M[i][j] = 0；
/// (c) 對角正性：M[i][i] ≥ 1（= [G:N_G(H_i)]）。
/// (b)+(c) ⇒ M 可逆 ⇒ 標記映射單射 ⇒ 標記向量為 G-集之完全不變量。
/// 回傳 (a, b, c, 子群類數, |G|)。
pub fn marks_cert(
  group : PermGroup,
  cap : Int32,
) -> (Bool, Bool, Bool, Int32, Int64) {
  let subs = subgroup_classes(group, cap)
  let m1 = table_of_marks(group, subs, cap)
  let m2 = table_of_marks_formula(group, subs, cap)
  let ns = subs.length()
  let mut a = ns > 0
  for i in 0..<ns {
    for j in 0..<ns {
      if m1[i][j] != m2[i][j] {
        a = false
      }
    }
  }
  let mut b = true
  let mut c = true
  for i in 0..<ns {
    for j in 0..<ns {
      if subs[i].order > subs[j].order && m1[i][j] != 0 {
        b = false
      }
    }
    if m1[i][i] < 1 {
      c = false
    }
  }
  (a, b, c, ns, group.order())
}

///|
/// G-集同構判定（標記向量相等 ⇒ 同構；分類定理）。
/// 兩個 G-集需由**同一**群 G 作用（同一 `subgroup_classes` 列表）。
pub fn gset_isomorphic(gs1 : GSetOf, gs2 : GSetOf, subs : Array[Sub]) -> Bool {
  guard gs1.x == gs2.x else { return false }
  cmp_arr(mark_vector(gs1, subs), mark_vector(gs2, subs)) == 0
}

///|
/// G-集之規範形式（= 標記向量 + 軌道大小譜），以陣列表示供比較/指紋。
pub fn gset_canon_key(gs : GSetOf, subs : Array[Sub]) -> Array[Int32] {
  let marks = mark_vector(gs, subs)
  let sizes = gset_orbit_sizes(gs)
  let out : Array[Int32] = [gs.x, marks.length(), sizes.length()]
  for v in marks {
    out.push(v)
  }
  for v in sizes {
    out.push(v)
  }
  out
}

///|
/// Frobenius 互反（Set 版）：
/// lhs = |Hom_G(G×X, Y)|（暴力列舉等變映射），rhs = |Hom_Set(X, res Y)| = |Y|^{|X|}。
/// 回傳 (lhs, rhs)。需 |Y|^{|G||X|} ≤ cap。
pub fn frobenius_reciprocity(
  group : PermGroup,
  x : Int32,
  y : GSetOf,
  cap : Int32,
) -> (Int32, Int32) {
  let ind = gset_induced(group, x, cap)
  let np = ind.x
  // 函數 φ : G×X → Y 以 mixed-radix 整數編碼
  let mut total = 1
  for _ in 0..<np {
    guard total <= cap / y.x else {
      abort("frobenius_reciprocity: too many functions")
    }
    total = total * y.x
  }
  // 等變性檢查：對全部群元素（以元素表 imgs 直接比對）
  let mut lhs = 0
  let pow = Array::make(np, 1)
  for i in 1..<np {
    pow[i] = pow[i - 1] * y.x
  }
  for code in 0..<total {
    let phi = Array::make(np, 0)
    for i in 0..<np {
      phi[i] = code / pow[i] % y.x
    }
    let mut ok = true
    for k in 0..<ind.imgs.length() {
      let ia = ind.imgs[k]
      let ib = y.imgs[k]
      for i in 0..<np {
        if phi[ia[i]] != ib[phi[i]] {
          ok = false
          break
        }
      }
      if !ok {
        break
      }
    }
    if ok {
      lhs = lhs + 1
    }
  }
  let mut rhs = 1
  for _ in 0..<x {
    rhs = rhs * y.x
  }
  (lhs, rhs)
}
