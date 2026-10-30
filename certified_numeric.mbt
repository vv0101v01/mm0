///|
// Certified counterparts of the numeric Hermitian/Kan layer.
//
// The original `Complex`/`CMat`/`Cube` layer is a floating-point
// model: its predicates use a tolerance and its cube laws are
// checked on sample grids.  This file provides the exact shadow of
// that layer.  Scalars are complex quadratic numbers
// `QuadC = QuadNum + i·QuadNum`, so examples involving `1/√2` are
// represented exactly.  Hermitian projectors are certified by exact
// matrix identities `P† = P`, `P² = P`, `P(I−P) = 0`, which imply the
// eigenspace decomposition for every vector, with no sampling.
// Cubes are polynomial cubes (degree at most 2 in each displayed
// coordinate, which covers lines, the bilinear filler, symmetry and
// the interior bump); face laws and "lies in the eigenspace" are
// coefficient identities, hence hold at every point of the cube.
//
// A numeric matrix can be certified against an exact shadow: the
// certificate records the exact projector proof for the shadow and
// the measured entrywise deviation and floating residual of the
// numeric matrix.  Equalities of the mathematical objects are thus
// decided exactly; `Double` values only measure how faithfully the
// floating matrix represents its shadow.

// ---------------------------------------------------------------------------
// Complex quadratic scalars
// ---------------------------------------------------------------------------

///|
pub struct QuadC {
  re : QuadNum
  im : QuadNum
} derive(Debug, Eq)

///|
pub extend QuadC with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend QuadC with Eq::{not_equal, equal}

///|
pub fn quad_to_double(x : QuadNum) -> Double {
  let a = @algebra.rat_to_double(x.a)
  if rat_is_zero(x.b) {
    a
  } else if x.d >= 0N {
    a + @algebra.rat_to_double(x.b) * @algebra.bigint_to_double(x.d).sqrt()
  } else {
    // A negative-radicand QuadNum is not a real scalar; this
    // projection is only a numeric shadow fallback.
    a
  }
}

///|
pub fn qcc_make(re : QuadNum, im : QuadNum) -> QuadC {
  QuadC::{ re, im, }
}

///|
pub fn qcc_zero() -> QuadC {
  QuadC::{ re: quad_zero(), im: quad_zero(), }
}

///|
pub fn qcc_one() -> QuadC {
  QuadC::{ re: quad_one(), im: quad_zero(), }
}

///|
pub fn qcc_i() -> QuadC {
  QuadC::{ re: quad_zero(), im: quad_one(), }
}

///|
pub fn qcc_rat(re : Rat, im : Rat) -> QuadC {
  QuadC::{ re: quad_rat(re), im: quad_rat(im), }
}

///|
pub fn qcc_real(x : QuadNum) -> QuadC {
  QuadC::{ re: x, im: quad_zero(), }
}

///|
pub fn qcc_add(a : QuadC, b : QuadC) -> QuadC {
  QuadC::{ re: quad_add(a.re, b.re), im: quad_add(a.im, b.im), }
}

///|
pub fn qcc_neg(a : QuadC) -> QuadC {
  QuadC::{ re: quad_neg(a.re), im: quad_neg(a.im), }
}

///|
pub fn qcc_sub(a : QuadC, b : QuadC) -> QuadC {
  qcc_add(a, qcc_neg(b))
}

///|
pub fn qcc_mul(a : QuadC, b : QuadC) -> QuadC {
  QuadC::{
    re: quad_sub(quad_mul(a.re, b.re), quad_mul(a.im, b.im)),
    im: quad_add(quad_mul(a.re, b.im), quad_mul(a.im, b.re)),
  }
}

///|
pub fn qcc_conj(a : QuadC) -> QuadC {
  QuadC::{ re: a.re, im: quad_neg(a.im), }
}

///|
pub fn qcc_scale_quad(c : QuadNum, a : QuadC) -> QuadC {
  QuadC::{ re: quad_mul(c, a.re), im: quad_mul(c, a.im), }
}

///|
pub fn qcc_eq(a : QuadC, b : QuadC) -> Bool {
  quad_eq(a.re, b.re) && quad_eq(a.im, b.im)
}

///|
pub fn qcc_is_zero(a : QuadC) -> Bool {
  quad_is_zero(a.re) && quad_is_zero(a.im)
}

///|
pub fn qcc_to_complex(a : QuadC) -> Complex {
  cx(quad_to_double(a.re), quad_to_double(a.im))
}

// ---------------------------------------------------------------------------
// Exact vectors and matrices
// ---------------------------------------------------------------------------

///|
pub type CertVec = Array[QuadC]

///|
pub struct CertMat {
  n : Int32
  rows : Array[Array[QuadC]]
}

///|
pub fn cert_vec_zero(n : Int32) -> CertVec {
  let out : CertVec = []
  for _i in 0..<n {
    out.push(qcc_zero())
  }
  out
}

///|
pub fn cert_vec_add(a : CertVec, b : CertVec) -> CertVec {
  let out : CertVec = []
  for i in 0..<a.length() {
    out.push(qcc_add(a[i], b[i]))
  }
  out
}

///|
pub fn cert_vec_sub(a : CertVec, b : CertVec) -> CertVec {
  let out : CertVec = []
  for i in 0..<a.length() {
    out.push(qcc_sub(a[i], b[i]))
  }
  out
}

///|
pub fn cert_vec_scale(c : QuadC, a : CertVec) -> CertVec {
  let out : CertVec = []
  for i in 0..<a.length() {
    out.push(qcc_mul(c, a[i]))
  }
  out
}

///|
pub fn cert_vec_scale_quad(c : QuadNum, a : CertVec) -> CertVec {
  let out : CertVec = []
  for i in 0..<a.length() {
    out.push(qcc_scale_quad(c, a[i]))
  }
  out
}

///|
pub fn cert_vec_eq(a : CertVec, b : CertVec) -> Bool {
  if a.length() != b.length() {
    return false
  }
  for i in 0..<a.length() {
    if !qcc_eq(a[i], b[i]) {
      return false
    }
  }
  true
}

///|
pub fn cert_inner(a : CertVec, b : CertVec) -> QuadC {
  let mut acc = qcc_zero()
  for i in 0..<a.length() {
    acc = qcc_add(acc, qcc_mul(qcc_conj(a[i]), b[i]))
  }
  acc
}

///|
pub fn cert_mat_zero(n : Int32) -> CertMat {
  let rows : Array[Array[QuadC]] = []
  for _i in 0..<n {
    rows.push(cert_vec_zero(n))
  }
  CertMat::{ n, rows, }
}

///|
pub fn cert_mat_identity(n : Int32) -> CertMat {
  let out = cert_mat_zero(n)
  for i in 0..<n {
    out.rows[i][i] = qcc_one()
  }
  out
}

///|
pub fn cert_mat_from_rows(rows : Array[Array[QuadC]]) -> CertMat {
  CertMat::{ n: rows.length(), rows, }
}

///|
pub fn cert_mat_add(a : CertMat, b : CertMat) -> CertMat {
  let rows : Array[Array[QuadC]] = []
  for i in 0..<a.n {
    rows.push(cert_vec_add(a.rows[i], b.rows[i]))
  }
  CertMat::{ n: a.n, rows, }
}

///|
pub fn cert_mat_sub(a : CertMat, b : CertMat) -> CertMat {
  let rows : Array[Array[QuadC]] = []
  for i in 0..<a.n {
    rows.push(cert_vec_sub(a.rows[i], b.rows[i]))
  }
  CertMat::{ n: a.n, rows, }
}

///|
pub fn cert_mat_mul(a : CertMat, b : CertMat) -> CertMat {
  let rows : Array[Array[QuadC]] = []
  for i in 0..<a.n {
    let row : Array[QuadC] = []
    for j in 0..<a.n {
      let mut acc = qcc_zero()
      for k in 0..<a.n {
        acc = qcc_add(acc, qcc_mul(a.rows[i][k], b.rows[k][j]))
      }
      row.push(acc)
    }
    rows.push(row)
  }
  CertMat::{ n: a.n, rows, }
}

///|
pub fn cert_mat_vec(a : CertMat, v : CertVec) -> CertVec {
  let out : CertVec = []
  for i in 0..<a.n {
    let mut acc = qcc_zero()
    for k in 0..<a.n {
      acc = qcc_add(acc, qcc_mul(a.rows[i][k], v[k]))
    }
    out.push(acc)
  }
  out
}

///|
pub fn cert_mat_adjoint(a : CertMat) -> CertMat {
  let rows : Array[Array[QuadC]] = []
  for i in 0..<a.n {
    let row : Array[QuadC] = []
    for j in 0..<a.n {
      row.push(qcc_conj(a.rows[j][i]))
    }
    rows.push(row)
  }
  CertMat::{ n: a.n, rows, }
}

///|
pub fn cert_mat_scale_quad(c : QuadNum, a : CertMat) -> CertMat {
  let rows : Array[Array[QuadC]] = []
  for i in 0..<a.n {
    rows.push(cert_vec_scale_quad(c, a.rows[i]))
  }
  CertMat::{ n: a.n, rows, }
}

///|
pub fn cert_mat_eq(a : CertMat, b : CertMat) -> Bool {
  if a.n != b.n {
    return false
  }
  for i in 0..<a.n {
    if !cert_vec_eq(a.rows[i], b.rows[i]) {
      return false
    }
  }
  true
}

///|
pub fn cert_mat_trace(a : CertMat) -> QuadC {
  let mut acc = qcc_zero()
  for i in 0..<a.n {
    acc = qcc_add(acc, a.rows[i][i])
  }
  acc
}

///|
pub fn cert_outer(v : CertVec) -> CertMat {
  let rows : Array[Array[QuadC]] = []
  for i in 0..<v.length() {
    let row : Array[QuadC] = []
    for j in 0..<v.length() {
      row.push(qcc_mul(v[i], qcc_conj(v[j])))
    }
    rows.push(row)
  }
  cert_mat_from_rows(rows)
}

///|
/// The exact rank-one orthogonal projector `vv†/(v†v)`.
pub fn cert_projector_of_vector(v : CertVec) -> CertMat? {
  let norm = cert_inner(v, v).re
  match quad_inv(norm) {
    Some(inv) => Some(cert_mat_scale_quad(inv, cert_outer(v)))
    None => None
  }
}

///|
pub fn cert_complement(p : CertMat) -> CertMat {
  cert_mat_sub(cert_mat_identity(p.n), p)
}

///|
pub fn cert_is_hermitian(p : CertMat) -> Bool {
  cert_mat_eq(cert_mat_adjoint(p), p)
}

///|
pub fn cert_is_idempotent(p : CertMat) -> Bool {
  cert_mat_eq(cert_mat_mul(p, p), p)
}

///|
pub fn cert_is_projector(p : CertMat) -> Bool {
  cert_is_hermitian(p) && cert_is_idempotent(p)
}

///|
pub fn cert_in_image(p : CertMat, v : CertVec) -> Bool {
  cert_vec_eq(cert_mat_vec(p, v), v)
}

///|
pub fn cert_in_kernel(p : CertMat, v : CertVec) -> Bool {
  cert_vec_eq(cert_mat_vec(p, v), cert_vec_zero(v.length()))
}

///|
/// A projector certificate is the finite list of exact matrix
/// identities from which the orthogonal eigenspace decomposition
/// `v = Pv + (I−P)v`, `P(Pv)=Pv`, and `P((I−P)v)=0` follow for all
/// vectors `v` by linearity.
pub struct ProjectorCertificate {
  matrix : CertMat
  hermitian : Bool
  idempotent : Bool
  complement_projector : Bool
  orthogonal_split : Bool
  trace : QuadC
}

///|
pub fn certify_projector(p : CertMat) -> ProjectorCertificate {
  let q = cert_complement(p)
  ProjectorCertificate::{
    matrix: p,
    hermitian: cert_is_hermitian(p),
    idempotent: cert_is_idempotent(p),
    complement_projector: cert_is_projector(q),
    orthogonal_split: cert_mat_eq(cert_mat_add(p, q), cert_mat_identity(p.n)) &&
    cert_mat_eq(cert_mat_mul(p, q), cert_mat_zero(p.n)) &&
    cert_mat_eq(cert_mat_mul(q, p), cert_mat_zero(p.n)),
    trace: cert_mat_trace(p),
  }
}

///|
pub fn projector_certificate_ok(c : ProjectorCertificate) -> Bool {
  c.hermitian && c.idempotent && c.complement_projector && c.orthogonal_split
}

///|
/// The exact shadow of the numeric example unit vector
/// `(1, i, 0)/√2`.
pub fn cert_example_unit() -> CertVec {
  let s = quad_sqrt_rat(rat_make(1, 2))
  [qcc_real(s), QuadC::{ re: quad_zero(), im: s, }, qcc_zero()]
}

///|
pub fn cert_example_projector() -> CertMat {
  cert_outer(cert_example_unit())
}

// ---------------------------------------------------------------------------
// Polynomial paths and squares (degree at most 2 per coordinate)
// ---------------------------------------------------------------------------

///|
pub struct CertPath {
  coeffs : Array[CertVec] // coefficients of 1, t, t^2
}

///|
pub struct CertSquare {
  coeffs : Array[Array[CertVec]] // coeffs[i][j] of x^i y^j, i,j ≤ 2
}

///|
fn cert_path_make(coeffs : Array[CertVec]) -> CertPath {
  let n = if coeffs.length() == 0 { 0 } else { coeffs[0].length() }
  let out : Array[CertVec] = []
  for i in 0..<3 {
    out.push(if i < coeffs.length() { coeffs[i] } else { cert_vec_zero(n) })
  }
  CertPath::{ coeffs: out, }
}

///|
pub fn cert_path_const(v : CertVec) -> CertPath {
  cert_path_make([v])
}

///|
pub fn cert_path_line(a : CertVec, b : CertVec) -> CertPath {
  cert_path_make([a, cert_vec_sub(b, a)])
}

///|
pub fn cert_path_start(p : CertPath) -> CertVec {
  p.coeffs[0]
}

///|
pub fn cert_path_end(p : CertPath) -> CertVec {
  cert_vec_add(cert_vec_add(p.coeffs[0], p.coeffs[1]), p.coeffs[2])
}

///|
pub fn cert_path_is_affine(p : CertPath) -> Bool {
  cert_vec_eq(p.coeffs[2], cert_vec_zero(p.coeffs[2].length()))
}

///|
pub fn cert_path_eq(a : CertPath, b : CertPath) -> Bool {
  for i in 0..<3 {
    if !cert_vec_eq(a.coeffs[i], b.coeffs[i]) {
      return false
    }
  }
  true
}

///|
/// Path symmetry by the polynomial substitution `t ↦ 1 − t`.
pub fn cert_path_sym(p : CertPath) -> CertPath {
  let c0 = cert_path_end(p)
  let c1 = cert_vec_sub(
    cert_vec_scale(qcc_rat(rat_int(-1), rat_zero()), p.coeffs[1]),
    cert_vec_scale(qcc_rat(rat_int(2), rat_zero()), p.coeffs[2]),
  )
  cert_path_make([c0, c1, p.coeffs[2]])
}

///|
fn cert_square_zero(n : Int32) -> CertSquare {
  let coeffs : Array[Array[CertVec]] = []
  for _i in 0..<3 {
    let row : Array[CertVec] = []
    for _j in 0..<3 {
      row.push(cert_vec_zero(n))
    }
    coeffs.push(row)
  }
  CertSquare::{ coeffs, }
}

///|
/// The bilinear square with corners in the order
/// `(0,0), (1,0), (0,1), (1,1)`.
pub fn cert_square_bilinear(
  c00 : CertVec,
  c10 : CertVec,
  c01 : CertVec,
  c11 : CertVec,
) -> CertSquare {
  let out = cert_square_zero(c00.length())
  out.coeffs[0][0] = c00
  out.coeffs[1][0] = cert_vec_sub(c10, c00)
  out.coeffs[0][1] = cert_vec_sub(c01, c00)
  out.coeffs[1][1] = cert_vec_add(
    cert_vec_sub(c11, c10),
    cert_vec_sub(c00, c01),
  )
  out
}

///|
/// The exact ambient filler for affine paths.  For non-affine input
/// paths only their endpoints are used; the certified laws below are
/// stated for affine boxes.
pub fn cert_square_fill(
  bottom : CertPath,
  left : CertPath,
  right : CertPath,
) -> CertSquare {
  cert_square_bilinear(
    cert_path_start(bottom),
    cert_path_end(bottom),
    cert_path_end(left),
    cert_path_end(right),
  )
}

///|
pub fn cert_square_add(a : CertSquare, b : CertSquare) -> CertSquare {
  let n = a.coeffs[0][0].length()
  let out = cert_square_zero(n)
  for i in 0..<3 {
    for j in 0..<3 {
      out.coeffs[i][j] = cert_vec_add(a.coeffs[i][j], b.coeffs[i][j])
    }
  }
  out
}

///|
/// Add the interior bump `x(1−x)y · normal`, as a polynomial.
pub fn cert_square_bump(s : CertSquare, normal : CertVec) -> CertSquare {
  let bump = cert_square_zero(normal.length())
  bump.coeffs[1][1] = normal
  bump.coeffs[2][1] = cert_vec_scale(qcc_rat(rat_int(-1), rat_zero()), normal)
  cert_square_add(s, bump)
}

///|
pub fn cert_square_face(s : CertSquare, face : Int32) -> CertPath {
  // face: 0 bottom (y=0), 1 top (y=1), 2 left (x=0), 3 right (x=1)
  let coeffs : Array[CertVec] = []
  if face == 0 {
    for i in 0..<3 {
      coeffs.push(s.coeffs[i][0])
    }
  } else if face == 1 {
    for i in 0..<3 {
      coeffs.push(
        cert_vec_add(
          cert_vec_add(s.coeffs[i][0], s.coeffs[i][1]),
          s.coeffs[i][2],
        ),
      )
    }
  } else if face == 2 {
    for j in 0..<3 {
      coeffs.push(s.coeffs[0][j])
    }
  } else {
    for j in 0..<3 {
      coeffs.push(
        cert_vec_add(
          cert_vec_add(s.coeffs[0][j], s.coeffs[1][j]),
          s.coeffs[2][j],
        ),
      )
    }
  }
  cert_path_make(coeffs)
}

///|
pub fn cert_square_eq(a : CertSquare, b : CertSquare) -> Bool {
  for i in 0..<3 {
    for j in 0..<3 {
      if !cert_vec_eq(a.coeffs[i][j], b.coeffs[i][j]) {
        return false
      }
    }
  }
  true
}

///|
/// Apply a linear map to every polynomial coefficient.  For a
/// projector this is exact pointwise pruning at every cube point.
pub fn cert_square_apply(p : CertMat, s : CertSquare) -> CertSquare {
  let out = cert_square_zero(p.n)
  for i in 0..<3 {
    for j in 0..<3 {
      out.coeffs[i][j] = cert_mat_vec(p, s.coeffs[i][j])
    }
  }
  out
}

///|
pub fn cert_path_in_image(p : CertMat, path : CertPath) -> Bool {
  for i in 0..<3 {
    if !cert_in_image(p, path.coeffs[i]) {
      return false
    }
  }
  true
}

///|
/// A polynomial square lies in `im(P)` at every point iff every
/// coefficient vector does: values are real-linear combinations of
/// the coefficients, and `im(P)` is a linear subspace fixed by `P`.
pub fn cert_square_in_image(p : CertMat, s : CertSquare) -> Bool {
  for i in 0..<3 {
    for j in 0..<3 {
      if !cert_in_image(p, s.coeffs[i][j]) {
        return false
      }
    }
  }
  true
}

///|
pub fn cert_open_box_wf(
  bottom : CertPath,
  left : CertPath,
  right : CertPath,
) -> Bool {
  cert_vec_eq(cert_path_start(left), cert_path_start(bottom)) &&
  cert_vec_eq(cert_path_start(right), cert_path_end(bottom))
}

///|
pub fn cert_filler_respects_box(
  filler : CertSquare,
  bottom : CertPath,
  left : CertPath,
  right : CertPath,
) -> Bool {
  cert_path_eq(cert_square_face(filler, 0), bottom) &&
  cert_path_eq(cert_square_face(filler, 2), left) &&
  cert_path_eq(cert_square_face(filler, 3), right)
}

///|
/// Full eigenspace Kan soundness for an affine certified box, as
/// coefficient identities rather than grid checks.
pub fn cert_eigenspace_kan_sound(
  p : CertMat,
  bottom : CertPath,
  left : CertPath,
  right : CertPath,
) -> Bool {
  if !projector_certificate_ok(certify_projector(p)) ||
    !cert_open_box_wf(bottom, left, right) ||
    !cert_path_is_affine(bottom) ||
    !cert_path_is_affine(left) ||
    !cert_path_is_affine(right) ||
    !cert_path_in_image(p, bottom) ||
    !cert_path_in_image(p, left) ||
    !cert_path_in_image(p, right) {
    return false
  }
  let filler = cert_square_apply(p, cert_square_fill(bottom, left, right))
  let cap = cert_square_face(filler, 1)
  cert_filler_respects_box(filler, bottom, left, right) &&
  cert_square_in_image(p, filler) &&
  cert_vec_eq(cert_path_start(cap), cert_path_end(left)) &&
  cert_vec_eq(cert_path_end(cap), cert_path_end(right)) &&
  cert_path_in_image(p, cap)
}

///|
/// Pruning repairs the bumped filler, exactly and coefficientwise.
pub fn cert_pruning_repairs_filler(
  p : CertMat,
  bottom : CertPath,
  left : CertPath,
  right : CertPath,
  normal : CertVec,
) -> Bool {
  let bad = cert_square_bump(cert_square_fill(bottom, left, right), normal)
  let fixed = cert_square_apply(p, bad)
  let bump_leaves = !cert_square_in_image(p, bad)
  let bump_has_kernel_part = !cert_in_image(p, normal)
  cert_filler_respects_box(fixed, bottom, left, right) &&
  cert_square_in_image(p, fixed) &&
  (!bump_has_kernel_part || bump_leaves)
}

// ---------------------------------------------------------------------------
// Numeric shadows and residuals
// ---------------------------------------------------------------------------

///|
pub fn cert_mat_to_numeric(a : CertMat) -> CMat {
  let rows : Array[Array[Complex]] = []
  for i in 0..<a.n {
    let row : Array[Complex] = []
    for j in 0..<a.n {
      row.push(qcc_to_complex(a.rows[i][j]))
    }
    rows.push(row)
  }
  mat_from_rows(rows)
}

///|
pub fn cert_vec_to_numeric(v : CertVec) -> CVec {
  let out : CVec = []
  for i in 0..<v.length() {
    out.push(qcc_to_complex(v[i]))
  }
  out
}

///|
/// Maximum entrywise deviation, measured in the max norm on real and
/// imaginary parts.
pub fn numeric_mat_max_deviation(a : CMat, b : CMat) -> Double {
  let mut best = 0.0
  for i in 0..<a.n {
    for j in 0..<a.n {
      let dr = (a.rows[i][j].re - b.rows[i][j].re).abs()
      let di = (a.rows[i][j].im - b.rows[i][j].im).abs()
      if dr > best {
        best = dr
      }
      if di > best {
        best = di
      }
    }
  }
  best
}

///|
/// The floating residual `max(|P²−P|, |P†−P|)` of a numeric matrix.
pub fn numeric_projector_residual(p : CMat) -> Double {
  let a = numeric_mat_max_deviation(mat_mul(p, p), p)
  let b = numeric_mat_max_deviation(mat_adjoint(p), p)
  if a > b {
    a
  } else {
    b
  }
}

///|
pub struct NumericProjectorCertificate {
  exact : ProjectorCertificate
  max_deviation : Double
  numeric_residual : Double
  tolerance : Double
  ok : Bool
}

///|
/// Certify a floating matrix against an exact projector shadow.
/// The equality being certified is the shadow's; the tolerance only
/// bounds the floating representation's deviation from that shadow.
pub fn certify_numeric_projector(
  numeric : CMat,
  shadow : CertMat,
  tolerance : Double,
) -> NumericProjectorCertificate {
  let exact = certify_projector(shadow)
  let deviation = numeric_mat_max_deviation(
    numeric,
    cert_mat_to_numeric(shadow),
  )
  let residual = numeric_projector_residual(numeric)
  NumericProjectorCertificate::{
    exact,
    max_deviation: deviation,
    numeric_residual: residual,
    tolerance,
    ok: projector_certificate_ok(exact) && deviation <= tolerance,
  }
}

///|
/// A rigorous dyadic enclosure of a finite Double: for `0 ≤ k ≤ 20`
/// and moderate `x`, returns rationals `lo ≤ x ≤ hi` with
/// `hi − lo = 2^(−k)`, computed by exact scaling by a power of two.
/// This is an interval certificate for the floating input itself,
/// independent of any exact shadow.
pub fn double_dyadic_interval(x : Double, k : Int32) -> (Rat, Rat)? {
  if k < 0 || k > 20 || x.is_nan() || x.is_inf() {
    return None
  }
  let mut scale = 1.0
  let mut den = 1
  for _i in 0..<k {
    scale = scale * 2.0
    den = den * 2
  }
  let scaled = x * scale
  if scaled.abs() > 1000000000.0 {
    return None
  }
  let mut floor = scaled.to_int()
  if scaled < 0.0 && floor.to_double() != scaled {
    floor = floor - 1
  }
  Some((rat_make(floor, den), rat_make(floor + 1, den)))
}
