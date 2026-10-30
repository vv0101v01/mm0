///|
// Hermitian idempotent matrices as orthogonal projectors, and the
// well-formedness of their eigenspace decomposition.
//
// Mathematics being made executable:
//   P² = P, P† = P
//     ⇒  Cⁿ = im(P) ⊕ ker(P),  an *orthogonal* direct sum
//     ⇒  im(P) is the λ=1 eigenspace, ker(P) the λ=0 eigenspace
//     ⇒  every v decomposes uniquely as v = Pv + (I−P)v, ⟨Pv,(I−P)v⟩ = 0
//     ⇒  rank(P) = tr(P) ∈ R
// Commuting projectors are compatible: if PQ = QP then PQ is again a
// projector (onto the intersection of the eigenspaces).  This is the
// linear-algebra shadow of "system compatibility" used later for cubical
// partial elements: two conditions can be imposed in either order.

///|
/// Outer product v·v†.  For a unit vector this is the projector onto span(v).
pub fn outer(v : CVec) -> CMat {
  let n = v.length()
  let rows : Array[Array[Complex]] = []
  for i in 0..<n {
    let row : Array[Complex] = []
    for j in 0..<n {
      row.push(cx_mul(v[i], cx_conj(v[j])))
    }
    rows.push(row)
  }
  CMat::{ n, rows, }
}

///|
/// Projector onto the span of an orthonormal family: P = Σₖ vₖ·vₖ†.
pub fn projector_from_orthonormal(basis : Array[CVec], n : Int32) -> CMat {
  let mut acc = mat_zero(n)
  for k in 0..<basis.length() {
    acc = mat_add(acc, outer(basis[k]))
  }
  acc
}

///|
/// Complementary projector I − P (projects onto ker P).
pub fn complement(p : CMat) -> CMat {
  mat_sub(mat_identity(p.n), p)
}

///|
/// Orthogonal decomposition of a vector: v ↦ (Pv, (I−P)v).
pub fn decompose(p : CMat, v : CVec) -> (CVec, CVec) {
  (mat_vec(p, v), mat_vec(complement(p), v))
}

///|
/// Membership in the λ=1 eigenspace: P v ≈ v.
pub fn in_image(p : CMat, v : CVec) -> Bool {
  vec_approx_eq(mat_vec(p, v), v)
}

///|
/// Membership in the λ=0 eigenspace (kernel): P v ≈ 0.
pub fn in_kernel(p : CMat, v : CVec) -> Bool {
  vec_approx_eq(mat_vec(p, v), vec_zero(v.length()))
}

///|
/// Eigenvalue equations on the two components of a decomposition:
/// P(Pv) = Pv (λ=1) and P((I−P)v) = 0 (λ=0).
pub fn eigen_equations_hold(p : CMat, v : CVec) -> Bool {
  let (v1, v0) = decompose(p, v)
  vec_approx_eq(mat_vec(p, v1), v1) &&
  vec_approx_eq(mat_vec(p, v0), vec_zero(v.length()))
}

///|
/// Eigenspace well-formedness (良構性) for a candidate projector, checked on
/// a finite set of sample vectors:
///   1. P is Hermitian and idempotent;
///   2. every sample splits as v = Pv + (I−P)v;
///   3. the two components are orthogonal;
///   4. the eigenvalue equations hold on both components;
///   5. tr(P) is (numerically) a non-negative integer = dim im(P).
pub fn eigenspace_well_formed(p : CMat, samples : Array[CVec]) -> Bool {
  if !is_projector(p) {
    return false
  }
  for s in 0..<samples.length() {
    let v = samples[s]
    let (v1, v0) = decompose(p, v)
    if !vec_approx_eq(vec_add(v1, v0), v) {
      return false
    }
    if !vec_orthogonal(v1, v0) {
      return false
    }
    if !eigen_equations_hold(p, v) {
      return false
    }
  }
  let tr = mat_trace_re(p)
  let nearest = tr.to_int()
  (tr - nearest.to_double()).abs() < 0.000001 && nearest >= 0
}

///|
/// If two projectors commute, their product is the projector onto the
/// intersection of the λ=1 eigenspaces — order does not matter.
/// Returns the product so callers can inspect it.
pub fn commuting_product(p : CMat, q : CMat) -> CMat {
  mat_mul(p, q)
}

///|
/// Compatibility theorem (executable form):
/// P, Q projectors with PQ = QP  ⇒  PQ is a projector and PQ = QP.
pub fn commuting_projectors_compatible(p : CMat, q : CMat) -> Bool {
  if !is_projector(p) || !is_projector(q) {
    return false
  }
  if !mat_commutes(p, q) {
    return false
  }
  let pq = commuting_product(p, q)
  is_projector(pq) && mat_approx_eq(pq, mat_mul(q, p))
}

///|
/// Pruning a vector into the λ=1 eigenspace: the retraction P.
/// As a retraction it is the identity on the eigenspace itself, which is
/// exactly what makes Kan filling-by-retraction sound in cube.mbt:
/// pruning never moves boundary data that already lies in the eigenspace.
pub fn prune_to_eigenspace(p : CMat, v : CVec) -> CVec {
  mat_vec(p, v)
}

///|
/// Retraction laws: P is idempotent as a map and fixes its image pointwise.
pub fn pruning_is_retraction(p : CMat, samples : Array[CVec]) -> Bool {
  for s in 0..<samples.length() {
    let v = samples[s]
    let pv = prune_to_eigenspace(p, v)
    // P(Pv) = Pv : pruning twice is pruning once.
    if !vec_approx_eq(prune_to_eigenspace(p, pv), pv) {
      return false
    }
    // If v already lies in the eigenspace, pruning must not move it.
    if in_image(p, v) && !vec_approx_eq(pv, v) {
      return false
    }
  }
  true
}

///|
/// 1/√2 to double precision.
pub fn inv_sqrt2() -> Double {
  0.7071067811865476
}

///|
/// Unit vector spanning the example eigenspace: v = (1, i, 0)/√2.
pub fn example_unit() -> CVec {
  [cx(inv_sqrt2(), 0.0), cx(0.0, inv_sqrt2()), cx_zero()]
}

///|
/// The example Hermitian idempotent: P = v·v†.
pub fn example_projector() -> CMat {
  outer(example_unit())
}

///|
pub fn vec_e3() -> CVec {
  [cx_zero(), cx_zero(), cx_real(1.0)]
}
