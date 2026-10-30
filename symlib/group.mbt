///|
/// # PermGroup — 置換群與增量 Schreier–Sims
///
/// 群以生成元表示，內建強生成集（SGS）：軌道-穩定子鏈
/// G = G^{(0)} ⊵ G^{(1)} ⊵ … ⊵ 1，G^{(i+1)} = Stab_{G^{(i)}}(b_i)。
/// - 群階 = Π |軌道_i|（軌道-穩定子定理），免列舉元素。
/// - 成員判定（sifting）：O(深度 × n)。
/// - 穩定子：Schreier 引理。
///
/// 關鍵不變量：第 i 層軌道必须在「全部 tag ≥ i 的強生成元」下閉包 —
/// 深層生成元（固定 b_0..b_{j-1}, j > i）仍會移動第 i 層軌道內的點，
/// 漏掉它們會低估軌道（經典錯誤；此處以全局生成元表 + 層級標籤保證）。

///|
/// 置換群（含強生成集）。
pub(all) struct PermGroup {
  n : Int32
  gens : Array[Perm]
  base : Array[Int32]
  orbits : Array[Array[Int32]]
  trans : Array[Array[Perm?]]
  orbit_size : Array[Int32]
}

///|
/// 置換數值雜湊（避免字串鍵的分配開銷）。
fn perm_hash(p : Perm) -> Int32 {
  let mut h = p.size()
  for i in 0..<p.size() {
    h = h * 1000003 + p.apply(i)
    h = h & 0x3FFFFFFF
  }
  h
}

///|
/// 去重 + 剔除恆等（雜湊桶 + 精確比較）。
fn dedupe_gens(gens : Array[Perm]) -> Array[Perm] {
  let buckets : Map[Int32, Array[Perm]] = Map([])
  let out : Array[Perm] = []
  for g in gens {
    if !g.is_identity() {
      let h = perm_hash(g)
      match buckets.get(h) {
        Some(arr) => {
          let mut dup = false
          for e in arr {
            if e == g {
              dup = true
              break
            }
          }
          if !dup {
            arr.push(g)
            out.push(g)
          }
        }
        None => {
          buckets.set(h, [g])
          out.push(g)
        }
      }
    }
  }
  out
}

///|
/// 橫截項讀取（**唯一**的橫截不變量斷言點）：
/// p 屬於第 i 層軌道 ⇒ `trans[i][p]` 必為 Some（軌道與橫截同步建構）。
/// 以具名函數取代散落的 `.unwrap()`，違規時給出可診斷訊息而非裸崩潰。
fn trans_at(tr : Array[Perm?], p : Int32) -> Perm {
  match tr[p] {
    Some(u) => u
    None => abort("trans_at: orbit/transversal invariant violated")
  }
}

///|
/// 軌道樹：`tr[q]` 為把 `b` 送到 `q` 的橫截（transversal）置換。
fn orbit_tree(
  gens : Array[Perm],
  n : Int32,
  b : Int32,
) -> (Array[Int32], Array[Perm?]) {
  let tr : Array[Perm?] = Array::make(n, None)
  tr[b] = Some(Perm::identity(n))
  let orb : Array[Int32] = [b]
  let mut head = 0
  while head < orb.length() {
    let p = orb[head]
    head = head + 1
    let u_p = trans_at(tr, p)
    for s in gens {
      let q = s.apply(p)
      if tr[q] is None {
        tr[q] = Some(s.compose(u_p))
        orb.push(q)
      }
    }
  }
  (orb, tr)
}

///|
/// 增量 SGS 建構器。`all_gens[j]` 為強生成元，`gen_tag[j]` 為其所屬層
///（元素固定 b_0..b_{tag-1}）。第 i 層軌道在 { gen : tag ≥ i } 下閉包。
priv struct Builder {
  n : Int32
  base : Array[Int32]
  all_gens : Array[Perm]
  gen_tag : Array[Int32]
  orbit : Array[Array[Int32]]
  trans : Array[Array[Perm?]]
  orbit_done : Array[Int32]
  gen_done : Array[Int32]
  wl_lvl : Array[Int32]
  wl_perm : Array[Perm]
  buckets : Map[Int32, Array[Int32]]
}

///|
fn builder_new(n : Int32) -> Builder {
  {
    n,
    base: [],
    all_gens: [],
    gen_tag: [],
    orbit: [],
    trans: [],
    orbit_done: [],
    gen_done: [],
    wl_lvl: [],
    wl_perm: [],
    buckets: Map([]),
  }
}

///|
fn push_wl(b : Builder, lvl : Int32, g : Perm) -> Unit {
  b.wl_lvl.push(lvl)
  b.wl_perm.push(g)
}

///|
/// 推送 Schreier 對 (p, s)：u_{s(p)}^{-1} ∘ s ∘ u_p ∈ G^{(i+1)}。
fn push_schreier_pair(b : Builder, i : Int32, p : Int32, s : Perm) -> Unit {
  let tr = b.trans[i]
  let up = trans_at(tr, p)
  let q = s.apply(p)
  let uq = trans_at(tr, q)
  let g = uq.inverse().compose(s).compose(up)
  if !g.is_identity() {
    push_wl(b, i + 1, g)
  }
}

///|
/// 閉包第 i 層軌道（在全部 tag ≥ i 的生成元下），並推送新 Schreier 配對。
fn close_orbit(b : Builder, i : Int32) -> Unit {
  let orbit = b.orbit[i]
  let tr = b.trans[i]
  let mut head = 0
  while head < orbit.length() {
    let p = orbit[head]
    head = head + 1
    let up = trans_at(tr, p)
    for j in 0..<b.all_gens.length() {
      if b.gen_tag[j] >= i {
        let s = b.all_gens[j]
        let q = s.apply(p)
        if tr[q] is None {
          tr[q] = Some(s.compose(up))
          orbit.push(q)
        }
      }
    }
  }
  // 新配對：新軌道點 × 全部可用 gen；全部點 × 新 gen
  let ng = b.all_gens.length()
  for pi in b.orbit_done[i]..<orbit.length() {
    for j in 0..<ng {
      if b.gen_tag[j] >= i {
        push_schreier_pair(b, i, orbit[pi], b.all_gens[j])
      }
    }
  }
  for j in b.gen_done[i]..<ng {
    if b.gen_tag[j] >= i {
      for pi in 0..<orbit.length() {
        push_schreier_pair(b, i, orbit[pi], b.all_gens[j])
      }
    }
  }
  b.orbit_done[i] = orbit.length()
  b.gen_done[i] = ng
}

///|
/// 加入強生成元（tag = lvl），並重新閉包所有 ≤ lvl 層的軌道
///（深層生成元會擴張淺層軌道 — 關鍵不變量）。
fn add_gen(b : Builder, lvl : Int32, g : Perm) -> Unit {
  // 去重：同元素已存在 ⇒ 只可能降低其 tag
  let h = perm_hash(g)
  match b.buckets.get(h) {
    Some(idxs) => {
      for idx in idxs {
        if b.all_gens[idx] == g {
          if b.gen_tag[idx] > lvl {
            b.gen_tag[idx] = lvl
            for i in 0..<=lvl {
              close_orbit(b, i)
            }
          }
          return
        }
      }
      idxs.push(b.all_gens.length())
    }
    None => b.buckets.set(h, [b.all_gens.length()])
  }
  b.all_gens.push(g)
  b.gen_tag.push(lvl)
  for i in 0..<=lvl {
    close_orbit(b, i)
  }
}

///|
/// 新基點層：g 固定全部現有基點但非恆等。
fn new_base(b : Builder, g : Perm) -> Unit {
  let mv = g.moved_points()
  let nb = mv[0]
  b.base.push(nb)
  let li = b.base.length() - 1
  let tr : Array[Perm?] = Array::make(b.n, None)
  tr[nb] = Some(Perm::identity(b.n))
  b.trans.push(tr)
  b.orbit.push([nb])
  b.orbit_done.push(0)
  b.gen_done.push(0)
  add_gen(b, li, g)
}

///|
/// 工作列插入：sift p（p ∈ G^{(lvl)}）沿鏈消去。
fn insert(b : Builder, lvl : Int32, p : Perm) -> Unit {
  let mut cur = p
  let mut i = lvl
  while i < b.base.length() {
    let x = cur.apply(b.base[i])
    match b.trans[i][x] {
      Some(u) => {
        cur = u.inverse().compose(cur)
        i = i + 1
      }
      None => {
        add_gen(b, i, cur)
        return
      }
    }
  }
  if cur.is_identity() {
    return
  }
  new_base(b, cur)
}

///|
/// 完整 SGS 建構。
fn sgs_build(n : Int32, gens : Array[Perm]) -> Builder {
  let b = builder_new(n)
  for g in gens {
    if !g.is_identity() {
      push_wl(b, 0, g)
    }
  }
  let mut steps = 0
  while b.wl_perm.length() > 0 {
    let g = b.wl_perm.pop().unwrap()
    let lvl = b.wl_lvl.pop().unwrap()
    insert(b, lvl, g)
    steps = steps + 1
    if steps > 4000000 {
      abort("sgs_build: worklist explosion")
    }
  }
  b
}

///|
/// 由生成元建構群並計算 Schreier–Sims 強生成集。
pub fn PermGroup::new(n : Int32, gens : Array[Perm]) -> PermGroup {
  for g in gens {
    guard g.size() == n else {
      abort("PermGroup::new: generator size mismatch")
    }
  }
  let dgens = dedupe_gens(gens)
  let b = sgs_build(n, dgens)
  let orbits : Array[Array[Int32]] = []
  let trans : Array[Array[Perm?]] = []
  let orbit_size : Array[Int32] = []
  for i in 0..<b.base.length() {
    orbits.push(b.orbit[i])
    trans.push(b.trans[i])
    orbit_size.push(b.orbit[i].length())
  }
  { n, gens: dgens, base: b.base, orbits, trans, orbit_size, }
}

///|
/// 平凡群。
pub fn PermGroup::trivial(n : Int32) -> PermGroup {
  PermGroup::new(n, [])
}

///|
/// 對稱群 S_n（生成元：n-輪 + 對換 (0 1)）。
pub fn PermGroup::symmetric(n : Int32) -> PermGroup {
  guard n >= 1 else { abort("PermGroup::symmetric: need n >= 1") }
  let cyc = Array::make(n, 0)
  for i in 0..<n {
    cyc[i] = i
  }
  let rot = Perm::from_cycles(n, [cyc])
  let swap = Perm::from_cycles(n, [[0, 1]])
  PermGroup::new(n, [rot, swap])
}

///|
/// 循環群 C_n（n-輪生成）。
pub fn PermGroup::cyclic(n : Int32) -> PermGroup {
  guard n >= 1 else { abort("PermGroup::cyclic: need n >= 1") }
  let cyc = Array::make(n, 0)
  for i in 0..<n {
    cyc[i] = i
  }
  PermGroup::new(n, [Perm::from_cycles(n, [cyc])])
}

///|
/// 二面體群 D_n（正 n 邊形對稱群，階 2n；n ≥ 3）。
pub fn PermGroup::dihedral(n : Int32) -> PermGroup {
  guard n >= 3 else { abort("PermGroup::dihedral: need n >= 3") }
  let cyc = Array::make(n, 0)
  for i in 0..<n {
    cyc[i] = i
  }
  let rot = Perm::from_cycles(n, [cyc])
  // 反射：i ↦ -i mod n
  let refl_img = Array::make(n, 0)
  for i in 0..<n {
    refl_img[i] = (n - i) % n
  }
  let refl = Perm::from_img(refl_img)
  PermGroup::new(n, [rot, refl])
}

///|
/// 階（Int64）：Π |軌道_i|（軌道-穩定子定理）。
pub fn PermGroup::order(self : PermGroup) -> Int64 {
  let mut o = 1L
  for s in self.orbit_size {
    o = o * s.to_int64()
  }
  o
}

///|
/// 底集合大小。
pub fn PermGroup::size(self : PermGroup) -> Int32 {
  self.n
}

///|
/// 生成元。
pub fn PermGroup::generators(self : PermGroup) -> Array[Perm] {
  self.gens
}

///|
/// 成員判定（sifting）。
pub fn PermGroup::contains(self : PermGroup, p : Perm) -> Bool {
  guard p.size() == self.n else { return false }
  let mut cur = p
  for i in 0..<self.base.length() {
    let b = self.base[i]
    let x = cur.apply(b)
    guard x >= 0 && x < self.n else { return false }
    let u = self.trans[i][x]
    guard u is Some(u) else { return false }
    cur = u.inverse().compose(cur)
  }
  cur.is_identity()
}

///|
/// 單點軌道（G 作用於 {0..n-1}）。
pub fn PermGroup::orbit(self : PermGroup, x : Int32) -> Array[Int32] {
  guard x >= 0 && x < self.n else {
    abort("PermGroup::orbit: point out of range")
  }
  let (orb, _) = orbit_tree(self.gens, self.n, x)
  orb
}

///|
/// 軌道代表（最小點）。
pub fn PermGroup::orbit_rep(self : PermGroup, x : Int32) -> Int32 {
  let mut r = x
  for v in self.orbit(x) {
    if v < r {
      r = v
    }
  }
  r
}

///|
/// 軌道分割。
pub fn PermGroup::orbit_partition(self : PermGroup) -> Array[Array[Int32]] {
  // 與 `FinAction::orbits` 共用 `orbit_partition_of`（action.mbt）
  orbit_partition_of(self.n, fn(x : Int32) -> Array[Int32] { self.orbit(x) })
}

///|
/// 是否可遷（單軌道）。
pub fn PermGroup::is_transitive(self : PermGroup) -> Bool {
  self.n > 0 && self.orbit(0).length() == self.n
}

///|
/// Schreier 引理：穩定子 G_x 的生成元。
pub fn PermGroup::stabilizer(self : PermGroup, x : Int32) -> PermGroup {
  guard x >= 0 && x < self.n else {
    abort("PermGroup::stabilizer: point out of range")
  }
  let (orb, tr) = orbit_tree(self.gens, self.n, x)
  let out : Array[Perm] = []
  for s in self.gens {
    for p in orb {
      let u_p = trans_at(tr, p)
      let u_sp = trans_at(tr, s.apply(p))
      let g = u_sp.inverse().compose(s).compose(u_p)
      if !g.is_identity() {
        out.push(g)
      }
    }
  }
  PermGroup::new(self.n, out)
}

///|
/// 逐點穩定子。
pub fn PermGroup::pointwise_stabilizer(
  self : PermGroup,
  pts : Array[Int32],
) -> PermGroup {
  let mut g = self
  for x in pts {
    g = g.stabilizer(x)
  }
  g
}

///|
/// 群元素列舉（僅限小群；超過 cap 中止）。
pub fn PermGroup::elements(self : PermGroup, cap : Int32) -> Array[Perm] {
  let out : Array[Perm] = []
  let levels = self.base.length()
  if levels == 0 {
    out.push(Perm::identity(self.n))
    return out
  }
  // DFS：唯一分解 g = u_0 ∘ u_1 ∘ … ∘ u_{k-1}（u_i ∈ 第 i 層橫截，u_i(b_i)=p_i）。
  // 注意複合次序：第 0 層橫截在最外側（最後作用）⇒ acc 以 `acc ∘ u` 累積。
  // （次序若反轉，映射 (p_0,…,p_{k-1}) ↦ u_{k-1}∘…∘u_0 非單射 ⇒ 重複且漏元素。）
  let stack : Array[(Int32, Perm)] = [(0, Perm::identity(self.n))]
  while stack.length() > 0 {
    let (lvl, acc) = stack.pop().unwrap()
    if lvl == levels {
      out.push(acc)
      guard out.length() <= cap else {
        abort("PermGroup::elements: group too large to enumerate")
      }
    } else {
      for p in self.orbits[lvl] {
        let u = trans_at(self.trans[lvl], p)
        stack.push((lvl + 1, acc.compose(u)))
      }
    }
  }
  out
}

///|
/// 固定 `x` 的元素個數（Burnside 原始和用；僅限小群）。
pub fn PermGroup::fixed_point_count(
  self : PermGroup,
  x : Int32,
  cap : Int32,
) -> Int32 {
  let mut c = 0
  for g in self.elements(cap) {
    if g.apply(x) == x {
      c = c + 1
    }
  }
  c
}

///|
/// 共軛像群 `p G p^{-1}`（Aut 函子性）。
pub fn PermGroup::conjugate_by(self : PermGroup, p : Perm) -> PermGroup {
  let out : Array[Perm] = []
  for g in self.gens {
    out.push(g.conjugate_by(p))
  }
  PermGroup::new(self.n, out)
}

///|
pub impl Show for PermGroup with fn to_string(self) {
  let mut bs = ""
  for i, b in self.base {
    if i > 0 {
      bs = bs + ","
    }
    bs = bs + b.to_string()
  }
  "PermGroup(n=\{self.n}, |G|=\{self.order()}, base=[\{bs}])"
}

///|
pub extend PermGroup with Show::{to_string, output}

///|
/// Debug（供 `assert_eq` / `inspect` 之結構化差異顯示；與 Show 同一摘要）。
pub impl Debug for PermGroup with fn to_repr(self) {
  Repr::literal(self.to_string())
}

///|
pub extend PermGroup with Debug::{to_repr}
