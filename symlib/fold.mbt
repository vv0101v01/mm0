///|
/// # OrbitFold — 軌道折疊
///
/// 給定群作用 G ↷ X（結構的對稱），軌道折疊把 X 壓縮為商結構 X/G：
/// - 每個軌道收成一個「代表元」→ 尋找/計數問題的搜索空間縮小 Σ|軌道| → #軌道
/// - 商圖帶軌道大小與邊重數，保留重建（unfold）所需的全部資料
/// - 搜索空間折疊（orbit-stacking）：分支時每軌道只走一個代表元，
///   這是軌道折疊在同構搜索中的直接應用（壓縮因子 = Π|分支軌道|）。

///|
/// 軌道折疊後的商圖（摺疊結構）。
pub(all) struct FoldedGraph {
  n : Int32
  m : Int32
  k : Int32
  rep : Array[Int32]
  orbit_of : Array[Int32]
  orbit_size : Array[Int32]
  // mul[i][j]：軌道 i、j 之間的邊數（i == j 時為軌道內部邊數）
  mul : Array[Array[Int32]]
  edge_total : Int32
}

///|
/// 以群 G 折疊圖（頂點作用）。G 之元素必須是圖的自同構（否則商圖語義不保）。
pub fn fold_graph(g : Graph, group : PermGroup) -> FoldedGraph {
  guard group.size() == g.order() else { abort("fold_graph: size mismatch") }
  let act = FinAction::of_group(group)
  fold_graph_by_orbits(g, act.orbits(), act.orbit_of())
}

///|
/// 以給定軌道分割折疊圖（供非自同構群作用 / 測試用）。
pub fn fold_graph_by_orbits(
  g : Graph,
  orbs : Array[Array[Int32]],
  orbit_of : Array[Int32],
) -> FoldedGraph {
  let k = orbs.length()
  let rep = Array::make(k, 0)
  let orbit_size = Array::make(k, 0)
  for i, orb in orbs {
    let mut r = orb[0]
    for v in orb {
      if v < r {
        r = v
      }
    }
    rep[i] = r
    orbit_size[i] = orb.length()
  }
  let mul : Array[Array[Int32]] = Array::make(k, [])
  for i in 0..<k {
    mul[i] = Array::make(k, 0)
  }
  let mut edge_total = 0
  for e in g.edge_list() {
    let (u, v) = e
    let a = orbit_of[u]
    let b = orbit_of[v]
    let lo = if a < b { a } else { b }
    let hi = if a < b { b } else { a }
    mul[lo][hi] = mul[lo][hi] + 1
    edge_total = edge_total + 1
  }
  { n: g.order(), m: g.size(), k, rep, orbit_of, orbit_size, mul, edge_total, }
}

///|
/// 軌道數（商結構大小）。
pub fn FoldedGraph::orbit_count(self : FoldedGraph) -> Int32 {
  self.k
}

///|
/// 折疊壓縮率 = k / n。
pub fn FoldedGraph::ratio(self : FoldedGraph) -> Double {
  if self.n == 0 {
    return 0.0
  }
  self.k.to_double() / self.n.to_double()
}

///|
/// 商圖邊重數（i ≤ j）。
pub fn FoldedGraph::multiplicity(
  self : FoldedGraph,
  i : Int32,
  j : Int32,
) -> Int32 {
  let lo = if i < j { i } else { j }
  let hi = if i < j { j } else { i }
  self.mul[lo][hi]
}

///|
/// 是否單點商（頂點可遷的特徵：整圖對稱性極高）。
pub fn FoldedGraph::is_single_orbit(self : FoldedGraph) -> Bool {
  self.k == 1
}

///|
/// 邊軌道折疊：回傳 (邊軌道代表邊, 各軌道大小)。
pub fn fold_edges(
  g : Graph,
  group : PermGroup,
) -> (Array[(Int32, Int32)], Array[Int32]) {
  let act = FinAction::on_edges(group, g)
  let edges = g.edge_list()
  let reps : Array[(Int32, Int32)] = []
  let sizes : Array[Int32] = []
  for orb in act.orbits() {
    let mut r = orb[0]
    for v in orb {
      if v < r {
        r = v
      }
    }
    reps.push(edges[r])
    sizes.push(orb.length())
  }
  (reps, sizes)
}

///|
/// 基本域：每軌道一個代表元（搜索空間折疊的核心 API）。
/// 在分支決策上只允許代表元 → 搜索樹大小由 Π|候選| 降至 Π|軌道數|。
pub fn fundamental_domain(
  group : PermGroup,
  points : Array[Int32],
) -> Array[Int32] {
  let seen : Map[Int32, Unit] = Map([])
  for p in points {
    seen.set(p, ())
  }
  let out : Array[Int32] = []
  let sorted = points.copy()
  sorted.sort()
  for p in sorted {
    if seen.contains(p) {
      out.push(p)
      for q in group.orbit(p) {
        if seen.contains(q) {
          seen.remove(q)
        }
      }
    }
  }
  out
}

///|
/// 搜索空間折疊統計：分支集 `points` 在 `group` 下折疊後的規模。
pub fn fold_candidates(
  group : PermGroup,
  points : Array[Int32],
) -> (Array[Int32], Double) {
  let reps = fundamental_domain(group, points)
  let ratio = if points.length() == 0 {
    1.0
  } else {
    reps.length().to_double() / points.length().to_double()
  }
  (reps, ratio)
}

///|
/// 折疊結果摘要文字。
pub fn FoldedGraph::summary(self : FoldedGraph) -> String {
  let mut s = "FoldedGraph(k=\{self.k}/\{self.n}, edges=\{self.edge_total}, reps=["
  for i, r in self.rep {
    if i > 0 {
      s = s + ","
    }
    s = s + r.to_string()
  }
  s + "])"
}

///|
pub impl Show for FoldedGraph with fn to_string(self) {
  self.summary()
}

///|
pub extend FoldedGraph with Show::{to_string, output}

///|
/// Debug（供 `assert_eq` / `inspect` 之結構化差異顯示；與 Show 同一摘要）。
pub impl Debug for FoldedGraph with fn to_repr(self) {
  Repr::literal(self.to_string())
}

///|
pub extend FoldedGraph with Debug::{to_repr}
