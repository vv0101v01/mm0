///|
/// # Aut — 圖自同構群
///
/// Aut(G) = { σ ∈ S_V : (u,v) ∈ E ⇔ (σu, σv) ∈ E }。
/// 由 search_graph 引擎一次搜索同時產出：
/// - 生成元（等編碼葉之間的映射，逐一驗證）
/// - 群階（Schreier–Sims：Π 軌道大小，免列舉元素）
/// - 頂點/邊軌道（群作用 + 軌道折疊）

///|
/// 圖的自同構群（含強生成集）。
pub fn automorphism_group(g : Graph) -> PermGroup {
  let res = search_graph(g, true)
  PermGroup::new(g.order(), res.aut_gens)
}

///|
/// 自同構群階 |Aut(G)|（Int64）。
pub fn aut_order(g : Graph) -> Int64 {
  automorphism_group(g).order()
}

///|
/// 自同構群生成元。
pub fn aut_generators(g : Graph) -> Array[Perm] {
  search_graph(g, true).aut_gens
}

///|
/// 頂點軌道（Aut(G) ↷ V 的軌道分割）。
pub fn vertex_orbits(g : Graph) -> Array[Array[Int32]] {
  automorphism_group(g).orbit_partition()
}

///|
/// 邊軌道（Aut(G) ↷ E 的軌道分割；代表邊 + 軌道大小）。
pub fn edge_orbits(g : Graph) -> (Array[(Int32, Int32)], Array[Int32]) {
  fold_edges(g, automorphism_group(g))
}

///|
/// 是否頂點可遷（單軌道：所有頂點對稱等价）。
pub fn is_vertex_transitive(g : Graph) -> Bool {
  let n = g.order()
  n > 0 && automorphism_group(g).is_transitive()
}

///|
/// 是否非對稱圖（|Aut| = 1：除恆等外無自同構）。
pub fn is_asymmetric(g : Graph) -> Bool {
  automorphism_group(g).order() == 1L
}

///|
/// 是否邊可遷（邊軌道數 = 1）。
pub fn is_edge_transitive(g : Graph) -> Bool {
  let (reps, _) = edge_orbits(g)
  reps.length() <= 1
}

///|
/// 有色圖的保色自同構群。`colors` 的等值類是剛性的：
/// 群元素只可把同色頂點送到同色頂點。
pub fn automorphism_group_colored(
  g : Graph,
  colors : Array[Int32],
) -> PermGroup {
  let res = search_graph_colored(g, colors, true)
  PermGroup::new(g.order(), res.aut_gens)
}

///|
/// 有色圖的保色自同構驗證。
pub fn is_colored_automorphism(
  g : Graph,
  colors : Array[Int32],
  s : Perm,
) -> Bool {
  guard colors.length() == g.order() && is_automorphism(g, s) else {
    return false
  }
  for i in 0..<g.order() {
    guard colors[s.apply(i)] == colors[i] else { return false }
  }
  true
}
