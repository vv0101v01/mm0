///|
/// # FinAction — 群作用、軌道與 Burnside 計數
///
/// 有限群在有限集合 X 上的作用以生成元像陣列表示（X = {0..size-1}）。
/// 內建推導作用（derived actions）：
/// - 點作用：G ↷ 頂點
/// - 邊作用：G ↷ 圖的邊集（軌道 = 邊軌道）
/// - 序對作用：G ↷ X×X（軌道計數供 Burnside 驗證）
/// 軌道計數恆等式：#軌道 = Σ_{x∈X} 1/|Orb(x)|（= Burnside 平均不動點數）。

///|
/// 作用之推導類型：決定如何把底置換（作用於 {0..base-1}）提升為本作用之置換。
pub enum ActionDerive {
  Points
  Pairs(Int32)
  Edges(Array[(Int32, Int32)], Map[Int32, Int32])
}

///|
/// 有限集合上的群作用（生成元像 + 推導描述，支持提升到導出作用）。
pub(all) struct FinAction {
  size : Int32
  base : Int32
  via : ActionDerive
  gens : Array[Array[Int32]]
}

///|
/// 由像陣列建構（驗證像在範圍內）。
pub fn FinAction::new(size : Int32, gens : Array[Array[Int32]]) -> FinAction {
  FinAction::with_derive(size, size, Points, gens)
}

///|
/// 建構並指定推導類型。
pub fn FinAction::with_derive(
  size : Int32,
  base : Int32,
  via : ActionDerive,
  gens : Array[Array[Int32]],
) -> FinAction {
  guard size >= 0 else { abort("FinAction::new: negative size") }
  for g in gens {
    guard g.length() == size else {
      abort("FinAction::new: image size mismatch")
    }
    for x in 0..<size {
      guard g[x] >= 0 && g[x] < size else {
        abort("FinAction::new: image out of range")
      }
    }
  }
  { size, base, via, gens, }
}

///|
/// 提升：把底集合置換 p（作用於 {0..base-1}）提升為本作用集合之像陣列。
/// 推導作用之群元素由此進入 Burnside 計數等需要「全部元素」的算法。
pub fn FinAction::lift(self : FinAction, p : Perm) -> Array[Int32] {
  guard p.size() == self.base else {
    abort("FinAction::lift: base size mismatch")
  }
  match self.via {
    Points => {
      let img = Array::make(self.size, 0)
      for i in 0..<self.size {
        img[i] = p.apply(i)
      }
      img
    }
    Pairs(n) => {
      let img = Array::make(self.size, 0)
      for x in 0..<n {
        for y in 0..<n {
          img[x * n + y] = p.apply(x) * n + p.apply(y)
        }
      }
      img
    }
    Edges(edges, idx) => {
      let img = Array::make(self.size, 0)
      for i, e in edges {
        let (u, v) = e
        let a = p.apply(u)
        let b = p.apply(v)
        let lo = if a < b { a } else { b }
        let hi = if a < b { b } else { a }
        img[i] = idx.get(lo * self.base + hi).unwrap()
      }
      img
    }
  }
}

///|
/// 置換群的點作用（X = {0..n-1}）。
pub fn FinAction::of_group(g : PermGroup) -> FinAction {
  let gens : Array[Array[Int32]] = []
  for p in g.generators() {
    let img = Array::make(p.size(), 0)
    for i in 0..<p.size() {
      img[i] = p.apply(i)
    }
    gens.push(img)
  }
  FinAction::with_derive(g.size(), g.size(), Points, gens)
}

///|
/// 序對作用：G ↷ X×X，序對 (x,y) 編號為 x·n+y。
pub fn FinAction::on_pairs(g : PermGroup) -> FinAction {
  let n = g.size()
  let gens : Array[Array[Int32]] = []
  for p in g.generators() {
    gens.push(pairs_img(p, n))
  }
  FinAction::with_derive(n * n, n, Pairs(n), gens)
}

///|
/// 序對作用之像陣列。
fn pairs_img(p : Perm, n : Int32) -> Array[Int32] {
  let img = Array::make(n * n, 0)
  for x in 0..<n {
    for y in 0..<n {
      img[x * n + y] = p.apply(x) * n + p.apply(y)
    }
  }
  img
}

///|
/// 邊作用：G ↷ 無向邊集 { {u,v} : u<v 且 (u,v) ∈ E }；邊編號按 edge_list 序。
pub fn FinAction::on_edges(g : PermGroup, graph : Graph) -> FinAction {
  let n = graph.order()
  let edges = graph.edge_list()
  let idx : Map[Int32, Int32] = Map([])
  for i, e in edges {
    let (u, v) = e
    idx.set(u * n + v, i)
  }
  let gens : Array[Array[Int32]] = []
  for p in g.generators() {
    gens.push(edges_img(p, edges, idx, n))
  }
  FinAction::with_derive(edges.length(), n, Edges(edges, idx), gens)
}

///|
/// 邊作用之像陣列。
fn edges_img(
  p : Perm,
  edges : Array[(Int32, Int32)],
  idx : Map[Int32, Int32],
  n : Int32,
) -> Array[Int32] {
  let img = Array::make(edges.length(), 0)
  for i, e in edges {
    let (u, v) = e
    let a = p.apply(u)
    let b = p.apply(v)
    let lo = if a < b { a } else { b }
    let hi = if a < b { b } else { a }
    img[i] = idx.get(lo * n + hi).unwrap()
  }
  img
}

///|
/// 集合大小。
pub fn FinAction::card(self : FinAction) -> Int32 {
  self.size
}

///|
/// 單點軌道。
pub fn FinAction::orbit(self : FinAction, x : Int32) -> Array[Int32] {
  guard x >= 0 && x < self.size else {
    abort("FinAction::orbit: point out of range")
  }
  let seen = Array::make(self.size, false)
  seen[x] = true
  let orb : Array[Int32] = [x]
  let mut head = 0
  while head < orb.length() {
    let p = orb[head]
    head = head + 1
    for g in self.gens {
      let q = g[p]
      if !seen[q] {
        seen[q] = true
        orb.push(q)
      }
    }
  }
  orb
}

///|
/// 軌道分割（代表元為各軌道最小點）。

///|
/// 軌道分割之通用機器：對 `0..<size` 逐點取單點軌道、標記已見、排序後收集。
/// `FinAction::orbits` 與 `PermGroup::orbit_partition` 共用此實作（去重）。
fn orbit_partition_of(
  size : Int32,
  orbit : (Int32) -> Array[Int32],
) -> Array[Array[Int32]] {
  let seen = Array::make(size, false)
  let out : Array[Array[Int32]] = []
  for s in 0..<size {
    if !seen[s] {
      let orb = orbit(s)
      for v in orb {
        seen[v] = true
      }
      orb.sort()
      out.push(orb)
    }
  }
  out
}

///|
pub fn FinAction::orbits(self : FinAction) -> Array[Array[Int32]] {
  orbit_partition_of(self.size, fn(s : Int32) -> Array[Int32] { self.orbit(s) })
}

///|
/// 頂點 → 軌道編號（軌道按代表元升序編號）。
pub fn FinAction::orbit_of(self : FinAction) -> Array[Int32] {
  let out = Array::make(self.size, -1)
  let orbs = self.orbits()
  for i, orb in orbs {
    for v in orb {
      out[v] = i
    }
  }
  out
}

///|
/// 軌道數。
pub fn FinAction::orbit_count(self : FinAction) -> Int32 {
  self.orbits().length()
}

///|
/// 是否可遷。
pub fn FinAction::is_transitive(self : FinAction) -> Bool {
  self.size > 0 && self.orbit(0).length() == self.size
}

///|
/// 軌道折疊的代表元集（每軌道最小點）。
pub fn FinAction::fundamental_domain(self : FinAction) -> Array[Int32] {
  let out : Array[Int32] = []
  for orb in self.orbits() {
    out.push(orb[0])
  }
  out
}

///|
/// 生成元 g 之不動點個數（Burnside 項）。
pub fn FinAction::fixed_points(self : FinAction, g : Array[Int32]) -> Int32 {
  let mut c = 0
  for x in 0..<self.size {
    if g[x] == x {
      c = c + 1
    }
  }
  c
}

///|
/// Burnside 軌道計數（列舉全部群元素版，僅限小群；用於驗證恆等式）：
/// #軌道 = (1/|G|) Σ_g |Fix(g)|。群元素經 `lift` 提升到本作用集合。
pub fn FinAction::burnside_orbit_count(
  self : FinAction,
  group : PermGroup,
  cap : Int32,
) -> Int32 {
  guard group.size() == self.base else {
    abort("FinAction::burnside_orbit_count: base size mismatch")
  }
  let elems = group.elements(cap)
  let mut sum = 0
  for p in elems {
    sum = sum + self.fixed_points(self.lift(p))
  }
  sum / elems.length()
}

///|
/// 軌道-穩定子：|Orb(x)| · |G_x| = |G|，回傳各軌道大小（等價 Σ 1/|Orb| = #軌道）。
pub fn FinAction::orbit_sizes(self : FinAction) -> Array[Int32] {
  let out : Array[Int32] = []
  for orb in self.orbits() {
    out.push(orb.length())
  }
  out
}

///|
/// 用群作用折疊後的「代表元個數」= 軌道數（軌道折疊的壓縮率指標）。
pub fn FinAction::fold_ratio(self : FinAction) -> Double {
  if self.size == 0 {
    return 0.0
  }
  self.orbit_count().to_double() / self.size.to_double()
}

///|
pub impl Show for FinAction with fn to_string(self) {
  "FinAction(size=\{self.size}, gens=\{self.gens.length()}, orbits=\{self.orbit_count()})"
}

///|
pub extend FinAction with Show::{to_string, output}

///|
/// Debug（供 `assert_eq` / `inspect` 之結構化差異顯示；與 Show 同一摘要）。
pub impl Debug for FinAction with fn to_repr(self) {
  Repr::literal(self.to_string())
}

///|
pub extend FinAction with Debug::{to_repr}
