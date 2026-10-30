///|
// Certified numeric layer over general algebraic extensions.
//
// `certified_numeric.mbt` works over `QuadC` (quadratic scalars)
// and polynomial cubes of degree at most 2 per coordinate.  This
// file lifts both restrictions using the exact-algebra package:
// scalars are complex numbers `AlgC` whose real and imaginary
// parts lie in a common algebraic extension `Q[X]/(m)` (elements
// `AlgNum`), and cubes are formal multivariate polynomials of
// arbitrary degree with `AlgC` coefficients.  Projector identities,
// eigenspace membership and face laws are exact coefficient
// identities in the extension, hence hold at every algebraic point
// of the cube.  The intended embedding of the extension generator
// is real, so complex conjugation is negation of the imaginary
// part.

// ---------------------------------------------------------------------------
// Scalars, vectors, matrices over an algebraic extension
// ---------------------------------------------------------------------------

///|
pub struct AlgC {
  re : AlgNum
  im : AlgNum
}

///|
pub fn algc_make(re : AlgNum, im : AlgNum) -> AlgC {
  AlgC::{ re, im, }
}

///|
pub fn algc_zero(modulus : QPoly) -> AlgC {
  AlgC::{ re: alg_zero(modulus), im: alg_zero(modulus), }
}

///|
pub fn algc_one(modulus : QPoly) -> AlgC {
  AlgC::{ re: alg_one(modulus), im: alg_zero(modulus), }
}

///|
pub fn algc_i(modulus : QPoly) -> AlgC {
  AlgC::{ re: alg_zero(modulus), im: alg_one(modulus), }
}

///|
pub fn algc_real(x : AlgNum) -> AlgC {
  AlgC::{ re: x, im: alg_zero_of(x), }
}

///|
fn alg_zero_of(x : AlgNum) -> AlgNum {
  alg_sub(x, x)
}

///|
pub fn algc_add(a : AlgC, b : AlgC) -> AlgC {
  AlgC::{ re: alg_add(a.re, b.re), im: alg_add(a.im, b.im), }
}

///|
pub fn algc_neg(a : AlgC) -> AlgC {
  AlgC::{ re: alg_neg(a.re), im: alg_neg(a.im), }
}

///|
pub fn algc_sub(a : AlgC, b : AlgC) -> AlgC {
  algc_add(a, algc_neg(b))
}

///|
pub fn algc_mul(a : AlgC, b : AlgC) -> AlgC {
  AlgC::{
    re: alg_sub(alg_mul(a.re, b.re), alg_mul(a.im, b.im)),
    im: alg_add(alg_mul(a.re, b.im), alg_mul(a.im, b.re)),
  }
}

///|
pub fn algc_conj(a : AlgC) -> AlgC {
  AlgC::{ re: a.re, im: alg_neg(a.im), }
}

///|
pub fn algc_scale_alg(c : AlgNum, a : AlgC) -> AlgC {
  AlgC::{ re: alg_mul(c, a.re), im: alg_mul(c, a.im), }
}

///|
pub fn algc_eq(a : AlgC, b : AlgC) -> Bool {
  alg_eq(a.re, b.re) && alg_eq(a.im, b.im)
}

///|
pub fn algc_is_zero(a : AlgC) -> Bool {
  alg_is_zero(a.re) && alg_is_zero(a.im)
}

///|
pub type AlgCertVec = Array[AlgC]

///|
pub struct AlgCertMat {
  n : Int32
  rows : Array[Array[AlgC]]
}

///|
pub fn alg_cert_vec_add(a : AlgCertVec, b : AlgCertVec) -> AlgCertVec {
  let out : AlgCertVec = []
  for i in 0..<a.length() {
    out.push(algc_add(a[i], b[i]))
  }
  out
}

///|
pub fn alg_cert_vec_scale(c : AlgC, a : AlgCertVec) -> AlgCertVec {
  let out : AlgCertVec = []
  for i in 0..<a.length() {
    out.push(algc_mul(c, a[i]))
  }
  out
}

///|
pub fn alg_cert_vec_eq(a : AlgCertVec, b : AlgCertVec) -> Bool {
  if a.length() != b.length() {
    return false
  }
  for i in 0..<a.length() {
    if !algc_eq(a[i], b[i]) {
      return false
    }
  }
  true
}

///|
/// Hermitian inner product `Σ conj(aᵢ)·bᵢ`.
pub fn alg_cert_inner(modulus : QPoly, a : AlgCertVec, b : AlgCertVec) -> AlgC {
  let mut acc = algc_zero(modulus)
  for i in 0..<a.length() {
    acc = algc_add(acc, algc_mul(algc_conj(a[i]), b[i]))
  }
  acc
}

///|
pub fn alg_cert_mat_from_rows(rows : Array[Array[AlgC]]) -> AlgCertMat {
  AlgCertMat::{ n: rows.length(), rows, }
}

///|
pub fn alg_cert_mat_vec(a : AlgCertMat, v : AlgCertVec) -> AlgCertVec {
  let out : AlgCertVec = []
  for i in 0..<a.n {
    let mut acc : AlgC = a.rows[i][0]
    acc = algc_mul(acc, v[0])
    for j in 1..<a.n {
      acc = algc_add(acc, algc_mul(a.rows[i][j], v[j]))
    }
    out.push(acc)
  }
  out
}

///|
pub fn alg_cert_mat_mul(a : AlgCertMat, b : AlgCertMat) -> AlgCertMat {
  let rows : Array[Array[AlgC]] = []
  for i in 0..<a.n {
    let row : Array[AlgC] = []
    for j in 0..<b.n {
      let mut acc = algc_mul(a.rows[i][0], b.rows[0][j])
      for k in 1..<a.n {
        acc = algc_add(acc, algc_mul(a.rows[i][k], b.rows[k][j]))
      }
      row.push(acc)
    }
    rows.push(row)
  }
  AlgCertMat::{ n: a.n, rows, }
}

///|
pub fn alg_cert_mat_adjoint(a : AlgCertMat) -> AlgCertMat {
  let rows : Array[Array[AlgC]] = []
  for i in 0..<a.n {
    let row : Array[AlgC] = []
    for j in 0..<a.n {
      row.push(algc_conj(a.rows[j][i]))
    }
    rows.push(row)
  }
  AlgCertMat::{ n: a.n, rows, }
}

///|
pub fn alg_cert_mat_eq(a : AlgCertMat, b : AlgCertMat) -> Bool {
  if a.n != b.n {
    return false
  }
  for i in 0..<a.n {
    for j in 0..<a.n {
      if !algc_eq(a.rows[i][j], b.rows[i][j]) {
        return false
      }
    }
  }
  true
}

///|
pub fn alg_cert_outer(v : AlgCertVec) -> AlgCertMat {
  let rows : Array[Array[AlgC]] = []
  for i in 0..<v.length() {
    let row : Array[AlgC] = []
    for j in 0..<v.length() {
      row.push(algc_mul(v[i], algc_conj(v[j])))
    }
    rows.push(row)
  }
  AlgCertMat::{ n: v.length(), rows, }
}

///|
/// The exact projector certificate over an algebraic extension:
/// `P† = P` and `P² = P` as identities in `Q[X]/(m)`.
pub fn alg_cert_is_projector(p : AlgCertMat) -> Bool {
  alg_cert_mat_eq(alg_cert_mat_adjoint(p), p) &&
  alg_cert_mat_eq(alg_cert_mat_mul(p, p), p)
}

///|
pub fn alg_cert_in_image(p : AlgCertMat, v : AlgCertVec) -> Bool {
  alg_cert_vec_eq(alg_cert_mat_vec(p, v), v)
}

// ---------------------------------------------------------------------------
// Formal polynomial paths and squares of arbitrary degree
// ---------------------------------------------------------------------------

///|
/// `coeffs[k]` is the coefficient vector of `t^k`.
pub struct AlgCertPath {
  coeffs : Array[AlgCertVec]
}

///|
pub fn alg_cert_path_eval(
  modulus : QPoly,
  p : AlgCertPath,
  t : AlgNum,
) -> AlgCertVec {
  let n = if p.coeffs.length() > 0 { p.coeffs[0].length() } else { 0 }
  let out : AlgCertVec = []
  for _i in 0..<n {
    out.push(algc_zero(modulus))
  }
  let acc = out
  let mut k = p.coeffs.length() - 1
  while k >= 0 {
    for i in 0..<n {
      acc[i] = algc_add(algc_scale_alg(t, acc[i]), p.coeffs[k][i])
    }
    k = k - 1
  }
  acc
}

///|
/// A formal path lies in `im(P)` at every algebraic point iff every
/// coefficient vector does (a polynomial identity).
pub fn alg_cert_path_in_image(p : AlgCertMat, path : AlgCertPath) -> Bool {
  for k in 0..<path.coeffs.length() {
    if !alg_cert_in_image(p, path.coeffs[k]) {
      return false
    }
  }
  true
}

///|
/// `coeffs[i][j]` is the coefficient vector of `s^i·t^j`.
pub struct AlgCertSquare {
  coeffs : Array[Array[AlgCertVec]]
}

///|
pub fn alg_cert_square_eval(
  modulus : QPoly,
  s : AlgCertSquare,
  x : AlgNum,
  y : AlgNum,
) -> AlgCertVec {
  let mut acc : AlgCertVec = []
  if s.coeffs.length() == 0 || s.coeffs[0].length() == 0 {
    return acc
  }
  // Evaluate in y for each x-row, then in x.
  let rows : Array[AlgCertVec] = []
  for i in 0..<s.coeffs.length() {
    rows.push(
      alg_cert_path_eval(modulus, AlgCertPath::{ coeffs: s.coeffs[i], }, y),
    )
  }
  acc = alg_cert_path_eval(modulus, AlgCertPath::{ coeffs: rows, }, x)
  acc
}

///|
pub fn alg_cert_square_in_image(p : AlgCertMat, s : AlgCertSquare) -> Bool {
  for i in 0..<s.coeffs.length() {
    for j in 0..<s.coeffs[i].length() {
      if !alg_cert_in_image(p, s.coeffs[i][j]) {
        return false
      }
    }
  }
  true
}

// ---------------------------------------------------------------------------
// A genuinely cubic example
// ---------------------------------------------------------------------------

///|
/// The modulus `X³ − 2`, for the real cube root of two.
pub fn cube_root_two_modulus() -> QPoly {
  qpoly_normalize([rat_int(-2), rat_zero(), rat_zero(), rat_int(1)])
}

///|
/// A unit vector over `Q(∛2)` from the rational parametrization of
/// the circle at `u = ∛2`, with an imaginary second component:
/// `v = ((1−u²)/(1+u²), i·2u/(1+u²))`.
pub fn cube_root_unit_vector(modulus : QPoly) -> AlgCertVec? {
  let u = alg_generator(modulus)
  let u2 = alg_mul(u, u)
  let one = alg_one(modulus)
  let denom = alg_add(one, u2)
  match (alg_div(alg_sub(one, u2), denom), alg_div(alg_scale2(u), denom)) {
    (Some(a), Some(b)) =>
      Some([algc_real(a), AlgC::{ re: alg_zero(modulus), im: b, }])
    _ => None
  }
}

///|
fn alg_scale2(x : AlgNum) -> AlgNum {
  alg_add(x, x)
}

///|
pub fn check_certified_algebraic_numeric() -> Bool {
  let modulus = cube_root_two_modulus()
  match cube_root_unit_vector(modulus) {
    Some(v) => {
      // Exact unit norm in Q(∛2): v†v = 1.
      if !algc_eq(alg_cert_inner(modulus, v, v), algc_one(modulus)) {
        return false
      }
      let p = alg_cert_outer(v)
      if !alg_cert_is_projector(p) || !alg_cert_in_image(p, v) {
        return false
      }
      // A degree-3 formal path inside the eigenspace, and exact
      // evaluation at t = ∛2.
      let zero_mod = modulus
      let zvec = [algc_zero(zero_mod), algc_zero(zero_mod)]
      let path = AlgCertPath::{
        coeffs: [v, zvec, alg_cert_vec_scale(algc_i(modulus), v), v],
      }
      if !alg_cert_path_in_image(p, path) {
        return false
      }
      let at = alg_cert_path_eval(modulus, path, alg_generator(modulus))
      if !alg_cert_in_image(p, at) {
        return false
      }
      // A formal square with a bump coefficient outside the
      // eigenspace is rejected coefficientwise; removing the bump
      // accepts it (all beyond the old degree-2 / QuadC fragment).
      let outside = [algc_one(modulus), algc_zero(modulus)]
      if alg_cert_in_image(p, outside) {
        return false
      }
      let square_bad = AlgCertSquare::{ coeffs: [[v, zvec], [zvec, outside]], }
      let square_good = AlgCertSquare::{ coeffs: [[v, zvec], [zvec, v]], }
      !alg_cert_square_in_image(p, square_bad) &&
      alg_cert_square_in_image(p, square_good) &&
      alg_cert_in_image(
        p,
        alg_cert_square_eval(
          modulus,
          square_good,
          alg_generator(modulus),
          alg_one(modulus),
        ),
      )
    }
    None => false
  }
}
