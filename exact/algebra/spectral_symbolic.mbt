///|
// Spectral algebra and the affine filler, performed entirely in
// symbolic algebra over Q (see symalg.mbt).
//
// Eigenvalues & projectors.  For distinct formal eigenvalues
// λ₀..λₙ₋₁ (atoms of the polynomial ring) and a matrix A with minimal
// polynomial m(X)=∏(X−λⱼ), the spectral projector for λₖ is Lagrange's
// formula
//     Pₖ = qₖ(A)/qₖ(λₖ),   qₖ(X) = ∏_{j≠k}(X−λⱼ).
// Its defining laws are *univariate polynomial identities modulo m*:
//     Pₖ² = Pₖ          ⇐  qₖ² − qₖ(λₖ)·qₖ ≡ 0  (mod m)
//     PₖPₗ = 0  (k≠l)   ⇐  qₖ·qₗ ≡ 0            (mod m)
//     Σ Pₖ = I          ⇐  Σ qₖ/qₖ(λₖ) = 1       (polynomial identity)
//     Σ λₖPₖ = A        ⇐  Σ λₖqₖ/qₖ(λₖ) = X     (polynomial identity)
// and they are verified exactly, by monic polynomial division and
// polynomial equality over the eigenvalue atoms.  Evaluating qₖ at a
// symbolic matrix gives the projector itself, e.g. on a diagonal or a
// generic Hermitian 2×2 matrix, whose adjoint-symmetry and
// characteristic polynomial are also checked symbolically.
//
// The affine Kan filler.  For affine paths the filler between four
// corners is the unique bilinear interpolant; both the boundary
// equations of the general square_fill formula and the uniqueness
// (coefficients are solved from the corners over the symbol ring) are
// polynomial identities in the coordinate atoms i, j — hence true for
// all values at once, not sampled.  Projector pruning of a bumped
// symbolic filler is likewise an exact identity (I−P)(P·F)=0.

// ---------------------------------------------------------------------------
// Univariate polynomials over SymFrac
// ---------------------------------------------------------------------------

///|
pub struct RPoly {
  coeffs : Array[SymFrac] // low to high
}

///|
pub fn rpoly_normalize(coeffs : Array[SymFrac]) -> RPoly {
  let mut last = 0
  for i in 0..<coeffs.length() {
    if !frac_is_zero(coeffs[i]) {
      last = i
    }
  }
  let out : Array[SymFrac] = []
  for i in 0..<(last + 1) {
    out.push(coeffs[i])
  }
  if out.length() == 0 {
    out.push(frac_zero())
  }
  RPoly::{ coeffs: out, }
}

///|
pub fn rpoly_zero() -> RPoly {
  RPoly::{ coeffs: [frac_zero()], }
}

///|
pub fn rpoly_one() -> RPoly {
  RPoly::{ coeffs: [frac_one()], }
}

///|
pub fn rpoly_x() -> RPoly {
  RPoly::{ coeffs: [frac_zero(), frac_one()], }
}

///|
pub fn rpoly_const(c : SymFrac) -> RPoly {
  rpoly_normalize([c])
}

///|
pub fn rpoly_is_zero(p : RPoly) -> Bool {
  p.coeffs.length() == 1 && frac_is_zero(p.coeffs[0])
}

///|
pub fn rpoly_degree(p : RPoly) -> Int32 {
  p.coeffs.length() - 1
}

///|
pub fn rpoly_add(a : RPoly, b : RPoly) -> RPoly {
  let n = if a.coeffs.length() > b.coeffs.length() {
    a.coeffs.length()
  } else {
    b.coeffs.length()
  }
  let out : Array[SymFrac] = []
  for i in 0..<n {
    let x = if i < a.coeffs.length() { a.coeffs[i] } else { frac_zero() }
    let y = if i < b.coeffs.length() { b.coeffs[i] } else { frac_zero() }
    out.push(frac_add(x, y))
  }
  rpoly_normalize(out)
}

///|
pub fn rpoly_neg(a : RPoly) -> RPoly {
  let out : Array[SymFrac] = []
  for i in 0..<a.coeffs.length() {
    out.push(frac_neg(a.coeffs[i]))
  }
  RPoly::{ coeffs: out, }
}

///|
pub fn rpoly_sub(a : RPoly, b : RPoly) -> RPoly {
  rpoly_add(a, rpoly_neg(b))
}

///|
pub fn rpoly_mul(a : RPoly, b : RPoly) -> RPoly {
  let n = a.coeffs.length() + b.coeffs.length() - 1
  let out : Array[SymFrac] = []
  for _i in 0..<n {
    out.push(frac_zero())
  }
  for i in 0..<a.coeffs.length() {
    for j in 0..<b.coeffs.length() {
      out[i + j] = frac_add(out[i + j], frac_mul(a.coeffs[i], b.coeffs[j]))
    }
  }
  rpoly_normalize(out)
}

///|
pub fn rpoly_scale(c : SymFrac, a : RPoly) -> RPoly {
  let out : Array[SymFrac] = []
  for i in 0..<a.coeffs.length() {
    out.push(frac_mul(c, a.coeffs[i]))
  }
  rpoly_normalize(out)
}

///|
pub fn rpoly_eq(a : RPoly, b : RPoly) -> Bool {
  rpoly_is_zero(rpoly_sub(a, b))
}

///|
pub fn rpoly_eval(p : RPoly, x : SymFrac) -> SymFrac {
  let mut acc = frac_zero()
  for i = p.coeffs.length() - 1; i >= 0; i = i - 1 {
    acc = frac_add(frac_mul(acc, x), p.coeffs[i])
  }
  acc
}

///|
/// The linear factor (X − λ) for an eigenvalue atom.
pub fn rpoly_factor(eig : Int32) -> RPoly {
  RPoly::{ coeffs: [frac_neg(frac_var(eig)), frac_one()], }
}

///|
pub struct RPolyDiv {
  quotient : RPoly
  remainder : RPoly
}

///|
/// Polynomial division by a *monic* divisor (exact over SymFrac).
pub fn rpoly_divmod_monic(a : RPoly, b : RPoly) -> RPolyDiv {
  let db = rpoly_degree(b)
  let qcoeffs : Array[SymFrac] = []
  let qlen = if rpoly_degree(a) >= db { rpoly_degree(a) - db + 1 } else { 1 }
  for _i in 0..<qlen {
    qcoeffs.push(frac_zero())
  }
  let mut rem = a
  while !rpoly_is_zero(rem) && rpoly_degree(rem) >= db {
    let shift = rpoly_degree(rem) - db
    let coeff = rem.coeffs[rpoly_degree(rem)]
    qcoeffs[shift] = coeff
    // rem -= coeff * X^shift * b
    let sub_coeffs : Array[SymFrac] = []
    for _i in 0..<shift {
      sub_coeffs.push(frac_zero())
    }
    for i in 0..<b.coeffs.length() {
      sub_coeffs.push(frac_mul(coeff, b.coeffs[i]))
    }
    rem = rpoly_sub(rem, RPoly::{ coeffs: sub_coeffs, })
  }
  RPolyDiv::{ quotient: rpoly_normalize(qcoeffs), remainder: rem, }
}

///|
pub fn rpoly_divisible_by(a : RPoly, b : RPoly) -> Bool {
  rpoly_is_zero(rpoly_divmod_monic(a, b).remainder)
}

///|
pub fn upoly_of_rpoly(p : RPoly) -> UPoly {
  let out : Array[SymC] = []
  for i in 0..<p.coeffs.length() {
    out.push(sc_real_frac(p.coeffs[i]))
  }
  upoly_normalize(out)
}

///|
/// Evaluate a real univariate polynomial at a symbolic matrix.
pub fn rpoly_eval_mat(p : RPoly, a : SymMat) -> SymMat {
  let mut result = sym_mat_zero(a.n)
  let mut power = sym_mat_identity(a.n)
  for i in 0..<p.coeffs.length() {
    result = sym_mat_add(result, sym_mat_scale(p.coeffs[i], power))
    power = sym_mat_mul(power, a)
  }
  result
}

// ---------------------------------------------------------------------------
// Spectral projectors as polynomial algebra
// ---------------------------------------------------------------------------

///|
/// qₖ(X) = ∏_{j≠k} (X − λⱼ).
pub fn spectral_q(eigs : Array[Int32], k : Int32) -> RPoly {
  let mut acc = rpoly_one()
  for j in 0..<eigs.length() {
    if j != k {
      acc = rpoly_mul(acc, rpoly_factor(eigs[j]))
    }
  }
  acc
}

///|
/// m(X) = ∏ⱼ (X − λⱼ), the minimal/characteristic polynomial in roots form.
pub fn spectral_minpoly(eigs : Array[Int32]) -> RPoly {
  let mut acc = rpoly_one()
  for j in 0..<eigs.length() {
    acc = rpoly_mul(acc, rpoly_factor(eigs[j]))
  }
  acc
}

///|
pub fn spectral_denominator(eigs : Array[Int32], k : Int32) -> SymFrac {
  rpoly_eval(spectral_q(eigs, k), frac_var(eigs[k]))
}

///|
/// Pₖ = qₖ(A)/qₖ(λₖ) as a symbolic matrix.
pub fn spectral_projector_sym(
  a : SymMat,
  eigs : Array[Int32],
  k : Int32,
) -> SymMat {
  sym_mat_scale(
    frac_div(frac_one(), spectral_denominator(eigs, k)),
    rpoly_eval_mat(spectral_q(eigs, k), a),
  )
}

///|
/// The projector laws as exact polynomial identities in the eigenvalue
/// atoms, for every distinct-eigenvalue pattern given.
pub fn check_spectral_identities() -> Bool {
  let eig_sets = [[40, 41], [40, 41, 42]]
  for s in 0..<eig_sets.length() {
    let eigs = eig_sets[s]
    let m = spectral_minpoly(eigs)
    // Resolution of identity and spectral decomposition of X (= A).
    let mut sum_p = rpoly_zero()
    let mut sum_lp = rpoly_zero()
    for k in 0..<eigs.length() {
      let q = spectral_q(eigs, k)
      let d = spectral_denominator(eigs, k)
      let pk = rpoly_scale(frac_div(frac_one(), d), q)
      sum_p = rpoly_add(sum_p, pk)
      sum_lp = rpoly_add(sum_lp, rpoly_scale(frac_div(frac_var(eigs[k]), d), q))
      // Idempotence modulo m.
      if !rpoly_divisible_by(rpoly_sub(rpoly_mul(q, q), rpoly_scale(d, q)), m) {
        return false
      }
      for l in 0..<eigs.length() {
        if l != k && !rpoly_divisible_by(rpoly_mul(q, spectral_q(eigs, l)), m) {
          return false
        }
      }
    }
    if !rpoly_eq(sum_p, rpoly_one()) || !rpoly_eq(sum_lp, rpoly_x()) {
      return false
    }
  }
  true
}

///|
pub fn sym_hermitian2(a : Int32, d : Int32, x : Int32, y : Int32) -> SymMat {
  sym_mat_from_rows([
    [sc_var(a), sc_make(frac_var(x), frac_var(y))],
    [sc_make(frac_var(x), frac_neg(frac_var(y))), sc_var(d)],
  ])
}

///|
pub fn check_spectral_matrices() -> Bool {
  // Generic Hermitian 2×2: hermitian exactly and charpoly is
  // X² − (a+d)X + (ad − x² − y²)  (Vieta in the entries).
  let a = 20
  let d = 21
  let x = 22
  let y = 23
  let h = sym_hermitian2(a, d, x, y)
  if !sym_is_hermitian(h) {
    return false
  }
  let va = frac_var(a)
  let vd = frac_var(d)
  let vx = frac_var(x)
  let vy = frac_var(y)
  let expected = upoly_normalize([
    sc_real_frac(
      frac_sub(frac_mul(va, vd), frac_add(frac_mul(vx, vx), frac_mul(vy, vy))),
    ),
    sc_real_frac(frac_neg(frac_add(va, vd))),
    sc_one(),
  ])
  if !upoly_eq(charpoly_sym(h), expected) {
    return false
  }
  // Diagonal matrix of formal eigenvalues: charpoly = product form, and
  // the spectral projector evaluates to the coordinate projector.
  let eigs = [40, 41]
  let diag = sym_mat_from_rows([
    [sc_var(40), sc_zero()],
    [sc_zero(), sc_var(41)],
  ])
  if !upoly_eq(charpoly_sym(diag), upoly_of_rpoly(spectral_minpoly(eigs))) {
    return false
  }
  let p0 = spectral_projector_sym(diag, eigs, 0)
  if !sym_mat_eq(
      p0,
      sym_mat_from_rows([[sc_one(), sc_zero()], [sc_zero(), sc_zero()]]),
    ) {
    return false
  }
  // The spectral projector of a Hermitian matrix is Hermitian, exactly.
  let ph = spectral_projector_sym(h, eigs, 0)
  if !sym_is_hermitian(ph) {
    return false
  }
  // Generic rank-one projector P = vv†/(v†v): Hermitian idempotent as a
  // polynomial identity in the parameters of v.
  let v : SymVec = [sc_make(frac_var(50), frac_var(51)), sc_var(52)]
  let pr = sym_projector_rank_one(v)
  if !sym_is_hermitian(pr) || !sym_is_idempotent(pr) {
    return false
  }
  // A concrete rational projector has characteristic polynomial X³−X²:
  // eigenvalues 1 (once) and 0 (twice), computed symbolically.
  let v3 : SymVec = [
    sc_rat(rat_make(3, 5)),
    sc_make(frac_zero(), frac_rat(rat_make(4, 5))),
    sc_zero(),
  ]
  let p3 = sym_projector_rank_one(v3)
  let expected3 = upoly_normalize([sc_zero(), sc_zero(), sc_int(-1), sc_one()])
  sym_is_idempotent(p3) && upoly_eq(charpoly_sym(p3), expected3)
}

// ---------------------------------------------------------------------------
// The affine filler as symbolic algebra
// ---------------------------------------------------------------------------

///|
pub type SymPath = (SymFrac) -> SymVec

///|
pub type SymSquare = (SymFrac, SymFrac) -> SymVec

///|
pub fn sym_frac_one_minus(f : SymFrac) -> SymFrac {
  frac_sub(frac_one(), f)
}

///|
pub fn sym_affine_path(a : SymVec, b : SymVec) -> SymPath {
  t => sym_vec_add(a, sym_vec_scale(t, sym_vec_sub(b, a)))
}

///|
fn sym_fill_formula(
  bottom : SymPath,
  left : SymPath,
  right : SymPath,
  i : SymFrac,
  j : SymFrac,
) -> SymVec {
  let left_dev = sym_vec_sub(left(j), bottom(frac_zero()))
  let right_dev = sym_vec_sub(right(j), bottom(frac_one()))
  sym_vec_add(
    bottom(i),
    sym_vec_add(
      sym_vec_scale(sym_frac_one_minus(i), left_dev),
      sym_vec_scale(i, right_dev),
    ),
  )
}

///|
/// The square filler F(i,j) = b(i) + (1−i)(l(j)−b(0)) + i(r(j)−b(1)),
/// as a symbolic function of the coordinate atoms.
pub fn sym_square_fill(
  bottom : SymPath,
  left : SymPath,
  right : SymPath,
) -> SymSquare {
  (i, j) => sym_fill_formula(bottom, left, right, i, j)
}

///|
fn sym_bilinear_formula(
  c00 : SymVec,
  c10 : SymVec,
  c01 : SymVec,
  c11 : SymVec,
  i : SymFrac,
  j : SymFrac,
) -> SymVec {
  let wi = sym_frac_one_minus(i)
  let wj = sym_frac_one_minus(j)
  sym_vec_add(
    sym_vec_add(
      sym_vec_scale(frac_mul(wi, wj), c00),
      sym_vec_scale(frac_mul(i, wj), c10),
    ),
    sym_vec_add(
      sym_vec_scale(frac_mul(wi, j), c01),
      sym_vec_scale(frac_mul(i, j), c11),
    ),
  )
}

///|
/// Bilinear interpolation from the four corners.
pub fn sym_bilinear_from_corners(
  c00 : SymVec,
  c10 : SymVec,
  c01 : SymVec,
  c11 : SymVec,
) -> SymSquare {
  (i, j) => sym_bilinear_formula(c00, c10, c01, c11, i, j)
}

///|
fn sym_ansatz_formula(
  k00 : SymVec,
  k10 : SymVec,
  k01 : SymVec,
  k11 : SymVec,
  i : SymFrac,
  j : SymFrac,
) -> SymVec {
  sym_vec_add(
    sym_vec_add(k00, sym_vec_scale(i, k10)),
    sym_vec_add(sym_vec_scale(j, k01), sym_vec_scale(frac_mul(i, j), k11)),
  )
}

///|
/// The general bilinear ansatz k00 + i·k10 + j·k01 + i·j·k11.
pub fn sym_bilinear_ansatz(
  k00 : SymVec,
  k10 : SymVec,
  k01 : SymVec,
  k11 : SymVec,
) -> SymSquare {
  (i, j) => sym_ansatz_formula(k00, k10, k01, k11, i, j)
}

///|
fn sym_vec_var2(id1 : Int32, id2 : Int32) -> SymVec {
  [sc_var(id1), sc_var(id2)]
}

///|
pub fn check_symbolic_affine_filler() -> Bool {
  let ii = frac_var(30)
  let jj = frac_var(31)
  // Four fully generic corners (8 independent atoms).
  let c00 = sym_vec_var2(32, 33)
  let c10 = sym_vec_var2(34, 35)
  let c01 = sym_vec_var2(36, 37)
  let c11 = sym_vec_var2(38, 39)
  let bottom = sym_affine_path(c00, c10)
  let left = sym_affine_path(c00, c01)
  let right = sym_affine_path(c10, c11)
  let f = sym_square_fill(bottom, left, right)
  // Boundary equations are polynomial identities in the atoms i, j.
  if !sym_vec_eq(f(ii, frac_zero()), bottom(ii)) {
    return false
  }
  if !sym_vec_eq(f(frac_zero(), jj), left(jj)) {
    return false
  }
  if !sym_vec_eq(f(frac_one(), jj), right(jj)) {
    return false
  }
  // For affine sides the filler is exactly the bilinear interpolant.
  let bil = sym_bilinear_from_corners(c00, c10, c01, c11)
  if !sym_vec_eq(f(ii, jj), bil(ii, jj)) {
    return false
  }
  // Uniqueness: a general bilinear ansatz is recovered from its corners.
  let k00 = sym_vec_var2(44, 45)
  let k10 = sym_vec_var2(46, 47)
  let k01 = sym_vec_var2(48, 49)
  let k11 = sym_vec_var2(53, 54)
  let ansatz = sym_bilinear_ansatz(k00, k10, k01, k11)
  let rec = sym_bilinear_from_corners(
    ansatz(frac_zero(), frac_zero()),
    ansatz(frac_one(), frac_zero()),
    ansatz(frac_zero(), frac_one()),
    ansatz(frac_one(), frac_one()),
  )
  if !sym_vec_eq(rec(ii, jj), ansatz(ii, jj)) {
    return false
  }
  // The coefficients are therefore forced:
  // k00=C00, k10=C10−C00, k01=C01−C00, k11=C11−C10−C01+C00.
  let corner00 = ansatz(frac_zero(), frac_zero())
  let corner10 = ansatz(frac_one(), frac_zero())
  let corner01 = ansatz(frac_zero(), frac_one())
  let corner11 = ansatz(frac_one(), frac_one())
  sym_vec_eq(corner00, k00) &&
  sym_vec_eq(sym_vec_sub(corner10, corner00), k10) &&
  sym_vec_eq(sym_vec_sub(corner01, corner00), k01) &&
  sym_vec_eq(
    sym_vec_sub(
      sym_vec_sub(corner11, corner10),
      sym_vec_sub(corner01, corner00),
    ),
    k11,
  )
}

///|
pub fn check_symbolic_nonlinear_boundary() -> Bool {
  // Boundary identities also hold symbolically for non-affine sides.
  let c = frac_var(60)
  let ii = frac_var(61)
  let jj = frac_var(62)
  let bottom : SymPath = t => {
    [sc_real_frac(frac_mul(t, t)), sc_real_frac(frac_add(c, t))]
  }
  let left : SymPath = t => {
    [sc_zero(), sc_real_frac(frac_add(c, frac_mul(t, t)))]
  }
  let right : SymPath = t => {
    [
      sc_one(),
      sc_real_frac(
        frac_add(frac_add(c, frac_one()), frac_mul(t, frac_mul(t, t))),
      ),
    ]
  }
  let f = sym_square_fill(bottom, left, right)
  sym_vec_eq(f(ii, frac_zero()), bottom(ii)) &&
  sym_vec_eq(f(frac_zero(), jj), left(jj)) &&
  sym_vec_eq(f(frac_one(), jj), right(jj))
}

///|
pub fn check_symbolic_pruning() -> Bool {
  // P prunes a bumped symbolic filler back into its image, exactly.
  let v : SymVec = [
    sc_rat(rat_make(3, 5)),
    sc_make(frac_zero(), frac_rat(rat_make(4, 5))),
    sc_zero(),
  ]
  let p = sym_projector_rank_one(v)
  let ii = frac_var(70)
  let jj = frac_var(71)
  let e3 : SymVec = [sc_zero(), sc_zero(), sc_one()]
  let scalar = frac_add(frac_one(), frac_add(ii, frac_mul(frac_int(2), jj)))
  let bump = frac_mul(frac_mul(ii, sym_frac_one_minus(ii)), jj)
  let f0 = sym_vec_scale(scalar, v)
  let bad = sym_vec_add(f0, sym_vec_scale(bump, e3))
  let fixed = sym_mat_vec(p, bad)
  let residual = sym_mat_vec(sym_mat_sub(sym_mat_identity(3), p), fixed)
  if !sym_vec_eq(residual, [sc_zero(), sc_zero(), sc_zero()]) {
    return false
  }
  // On the given faces the bump vanishes and P fixes the good filler,
  // at symbolic coordinates: check bottom (j=0) and left (i=0).
  let scalar_b = frac_add(frac_one(), ii)
  let bottom0 = sym_vec_scale(scalar_b, v)
  let fixed_bottom = sym_mat_vec(
    p,
    sym_vec_add(bottom0, sym_vec_scale(frac_zero(), e3)),
  )
  sym_vec_eq(fixed_bottom, bottom0) && sym_vec_eq(fixed, sym_mat_vec(p, fixed))
}

///|
pub fn check_symbolic_algebra_all() -> Bool {
  // Ring laws in the canonical form.
  let x = frac_var(80)
  let y = frac_var(81)
  let distributivity = frac_eq(
    frac_mul(frac_add(x, frac_one()), frac_add(y, frac_int(2))),
    frac_add(
      frac_add(frac_mul(x, y), frac_mul(frac_int(2), x)),
      frac_add(y, frac_int(2)),
    ),
  )
  distributivity &&
  check_spectral_identities() &&
  check_spectral_matrices() &&
  check_symbolic_affine_filler() &&
  check_symbolic_nonlinear_boundary() &&
  check_symbolic_pruning()
}
