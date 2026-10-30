///|
fn positive_mod64(x : Int64, modulus : Int64) -> Int64 {
  let r = x % modulus
  if r < 0L {
    r + modulus
  } else {
    r
  }
}

///|
fn pair_signature(w : Int32, w2 : Int32) -> Int64 {
  // A commutative multiset contribution: applications sum these terms,
  // so CSR order cannot change the initial color.  It is only a search
  // color; exact preservation is always checked entry by entry below.
  let a = positive_mod64(w.to_int64() + 1000003L, 1000000007L)
  let b = positive_mod64(w2.to_int64() + 2000003L, 1000000007L)
  positive_mod64(a * a + b * 1000003L + 97L, 1000000007L)
}

///|
/// Forget direction and weights, retaining the simple undirected support.
pub fn semiring_graph_support(g : @sgraph.Graph) -> @sym.Graph {
  let edges : Array[(Int32, Int32)] = []
  for u in 0..<g.n {
    for e in g.offsets[u]..<g.offsets[u + 1] {
      let v = g.to[e]
      if u != v {
        edges.push((u, v))
      }
    }
  }
  @sym.Graph::from_edges(g.n, edges)
}

///|
/// Dense reconstruction of the two CSR weight channels.  Repeated edges
/// follow `Graph::to_trop_mat`: the last triplet wins.
fn semiring_graph_dense(
  g : @sgraph.Graph,
) -> (Array[Bool], Array[Int32], Array[Int32]) {
  let n = g.n
  let present = Array::make(n * n, false)
  let first = Array::make(n * n, 0)
  let second = Array::make(n * n, 0)
  for u in 0..<n {
    for e in g.offsets[u]..<g.offsets[u + 1] {
      let k = u * n + g.to[e]
      present[k] = true
      first[k] = g.w[e]
      second[k] = g.w2[e]
    }
  }
  (present, first, second)
}

///|
/// Initial search colors from outgoing/incoming weighted-edge multisets.
pub fn semiring_graph_vertex_colors(g : @sgraph.Graph) -> Array[Int32] {
  let (present, first, second) = semiring_graph_dense(g)
  let n = g.n
  let out : Array[Int32] = []
  for v in 0..<n {
    let mut outgoing = 17L
    let mut incoming = 131L
    for u in 0..<n {
      let ko = v * n + u
      if present[ko] {
        outgoing = positive_mod64(
          outgoing + pair_signature(first[ko], second[ko]),
          1000000007L,
        )
      }
      let ki = u * n + v
      if present[ki] {
        incoming = positive_mod64(
          incoming + pair_signature(first[ki], second[ki]),
          1000000007L,
        )
      }
    }
    out.push(
      positive_mod64(outgoing * 1000003L + incoming, 1000000007L).to_int(),
    )
  }
  out
}

///|
/// Exact preservation of edge presence and both weight channels.
pub fn perm_preserves_semiring_graph(g : @sgraph.Graph, p : @sym.Perm) -> Bool {
  guard p.size() == g.n else { return false }
  let (present, first, second) = semiring_graph_dense(g)
  let n = g.n
  for i in 0..<n {
    for j in 0..<n {
      let a = i * n + j
      let b = p.apply(i) * n + p.apply(j)
      if present[a] != present[b] ||
        (present[a] && (first[a] != first[b] || second[a] != second[b])) {
        return false
      }
    }
  }
  true
}

///|
/// Enumerate weighted directed symmetries.  symlib's colored search can
/// only propose support automorphisms preserving the initial signature
/// colors; exact two-channel weights are then filtered entry by entry.
/// Enumeration is explicitly capped by `cap` candidate group elements.
pub fn semiring_graph_symmetries(
  g : @sgraph.Graph,
  cap : Int32,
) -> Array[@sym.Perm] {
  let group = @sym.automorphism_group_colored(
    semiring_graph_support(g),
    semiring_graph_vertex_colors(g),
  )
  let out : Array[@sym.Perm] = []
  for p in group.elements(cap) {
    if perm_preserves_semiring_graph(g, p) {
      out.push(p)
    }
  }
  out
}

///|
/// Candidate colored-support group order.  The exact weighted symmetry
/// group is a subgroup of this group.
pub fn semiring_graph_candidate_order(g : @sgraph.Graph) -> Int64 {
  @sym.automorphism_group_colored(
    semiring_graph_support(g),
    semiring_graph_vertex_colors(g),
  ).order()
}

///|
/// Group-average projector of all weighted symmetries.  It refuses an
/// incomplete enumeration instead of silently averaging a partial set.
pub fn semiring_graph_symmetry_projector(
  g : @sgraph.Graph,
  cap : Int32,
) -> Result[@cub.CMat, String] {
  if semiring_graph_candidate_order(g) > cap.to_int64() {
    return Err(
      "semiring_graph_symmetry_projector: 候選置換數 \{semiring_graph_candidate_order(g)} 超過上限 \{cap}（拒絕對不完整枚舉取平均）",
    )
  }
  average_permutation_matrices(semiring_graph_symmetries(g, cap))
}

///|
/// Complex matrix support as a symlib graph (nonzero test uses cubical's
/// existing floating tolerance through comparison with `cx_zero`).
pub fn matrix_support_graph(m : @cub.CMat) -> @sym.Graph {
  let edges : Array[(Int32, Int32)] = []
  for i in 0..<m.n {
    for j in 0..<m.n {
      if i != j && !@cub.cx_approx_eq(@cub.mat_get(m, i, j), @cub.cx_zero()) {
        edges.push((i, j))
      }
    }
  }
  @sym.Graph::from_edges(m.n, edges)
}

///|
fn matrix_support_colors(m : @cub.CMat) -> Array[Int32] {
  let out : Array[Int32] = []
  for i in 0..<m.n {
    let mut row = 0
    let mut col = 0
    for j in 0..<m.n {
      if !@cub.cx_approx_eq(@cub.mat_get(m, i, j), @cub.cx_zero()) {
        row = row + 1
      }
      if !@cub.cx_approx_eq(@cub.mat_get(m, j, i), @cub.cx_zero()) {
        col = col + 1
      }
    }
    out.push(row * 4099 + col)
  }
  out
}

///|
/// Entrywise approximate preservation of a floating complex matrix.
pub fn perm_preserves_matrix(m : @cub.CMat, p : @sym.Perm) -> Bool {
  guard p.size() == m.n else { return false }
  for i in 0..<m.n {
    for j in 0..<m.n {
      if !@cub.cx_approx_eq(
          @cub.mat_get(m, p.apply(i), p.apply(j)),
          @cub.mat_get(m, i, j),
        ) {
        return false
      }
    }
  }
  true
}

///|
/// Enumerate permutation symmetries of a complex matrix, capped.
pub fn matrix_permutation_symmetries(
  m : @cub.CMat,
  cap : Int32,
) -> Array[@sym.Perm] {
  let group = @sym.automorphism_group_colored(
    matrix_support_graph(m),
    matrix_support_colors(m),
  )
  let out : Array[@sym.Perm] = []
  for p in group.elements(cap) {
    if perm_preserves_matrix(m, p) {
      out.push(p)
    }
  }
  out
}

///|
/// One-stop report for a weighted directed graph.  It deliberately keeps
/// the three answers separate rather than pretending they are one type:
/// symlib canonical/symmetry data, semiring APSP data, and exact/floating
/// cubical matrix data.
pub(all) struct WeightedGraphReport {
  n : Int32
  directed_edges : Int32
  canonical_colors : Array[Int32]
  canonical_encoding : Array[Int32]
  candidate_group_order : Int64
  weighted_symmetry_count : Int32
  symmetry_projector : @cub.CMat
  distance_matrix : @smat.Mat[@semialg.Trop]
  reachable_pairs : Int32
  finite_distance_sum : Int64
  support_characteristic_poly : @algebra.QPoly
}

///|
pub fn weighted_graph_report(
  g : @sgraph.Graph,
  cap : Int32,
) -> Result[WeightedGraphReport, String] {
  let support = semiring_graph_support(g)
  let colors = semiring_graph_vertex_colors(g)
  let (canonical_colors, canonical_encoding) = @sym.colored_canonical_key(
    support, colors,
  )
  let symmetries = semiring_graph_symmetries(g, cap)
  let distances = @sgraph.apsp_dijkstra(g)
  let mut reachable = 0
  let mut distance_sum = 0L
  for i in 0..<g.n {
    for j in 0..<g.n {
      let d = distances.get(i, j)
      if !d.is_inf() {
        reachable = reachable + 1
        distance_sum = distance_sum + d.value().to_int64()
      }
    }
  }
  let rows : Array[Array[Int32]] = []
  for i in 0..<g.n {
    let row : Array[Int32] = []
    for j in 0..<g.n {
      row.push(if support.has_edge(i, j) { 1 } else { 0 })
    }
    rows.push(row)
  }
  let projector = match semiring_graph_symmetry_projector(g, cap) {
    Err(e) => return Err(e)
    Ok(v) => v
  }
  Ok({
    n: g.n,
    directed_edges: g.edges(),
    canonical_colors,
    canonical_encoding,
    candidate_group_order: semiring_graph_candidate_order(g),
    weighted_symmetry_count: symmetries.length(),
    symmetry_projector: projector,
    distance_matrix: distances,
    reachable_pairs: reachable,
    finite_distance_sum: distance_sum,
    support_characteristic_poly: @algebra.qmat_charpoly(
      @algebra.qmat_from_int_rows(rows),
    ),
  })
}

///|
/// A 2-cell square as an incidence graph.  Vertices 0..3 are corners,
/// 4..7 are edge cells and 8 is the square; colors are cell dimensions.
pub fn square_cell_incidence() -> (@sym.Graph, Array[Int32]) {
  let edges = [
    (4, 0),
    (4, 1),
    (5, 1),
    (5, 2),
    (6, 2),
    (6, 3),
    (7, 3),
    (7, 0),
    (8, 4),
    (8, 5),
    (8, 6),
    (8, 7),
  ]
  (@sym.Graph::from_edges(9, edges), [0, 0, 0, 0, 1, 1, 1, 1, 2])
}

///|
/// The square's dimension-colored incidence symmetries are exactly D4:
/// the 2-cell is fixed, corners form one orbit and edge cells another.
pub fn check_square_cell_symmetry() -> Bool {
  let (g, colors) = square_cell_incidence()
  let group = @sym.automorphism_group_colored(g, colors)
  group.order() == 8L &&
  group.orbit(8).length() == 1 &&
  group.orbit(0).length() == 4 &&
  group.orbit(4).length() == 4
}

///|
/// Flagship checks: a directed weighted C4 has four rotations (its
/// reflections reverse the directed cycle), their average is a trace-1
/// projector, and a two-identical-block complex matrix has 8 symmetries.
pub fn check_graph_symmetry_bridges() -> Bool {
  let g = @sgraph.Graph::build(4, [0, 1, 2, 3], [1, 2, 3, 0], [1, 1, 1, 1])
  let report = match weighted_graph_report(g, 32) {
    Err(_) => return false
    Ok(v) => v
  }
  if report.weighted_symmetry_count != 4 ||
    !@cub.is_projector(report.symmetry_projector) ||
    (@cub.mat_trace_re(report.symmetry_projector) - 1.0).abs() >= 0.000001 ||
    report.reachable_pairs != 16 ||
    report.finite_distance_sum != 24L {
    return false
  }
  // C4 adjacency characteristic polynomial is x^4 - 4x^2.
  let cp = report.support_characteristic_poly
  if !@algebra.rat_eq(@algebra.qpoly_coeff(cp, 4), @algebra.rat_int(1)) ||
    !@algebra.rat_eq(@algebra.qpoly_coeff(cp, 2), @algebra.rat_int(-4)) ||
    !@algebra.rat_eq(@algebra.qpoly_coeff(cp, 0), @algebra.rat_zero()) {
    return false
  }
  let z = @cub.cx_zero()
  let one = @cub.cx_real(1.0)
  let half = @cub.cx_real(0.5)
  let blocks = @cub.mat_from_rows([
    [one, half, z, z],
    [half, one, z, z],
    [z, z, one, half],
    [z, z, half, one],
  ])
  matrix_permutation_symmetries(blocks, 32).length() == 8 &&
  check_square_cell_symmetry()
}
