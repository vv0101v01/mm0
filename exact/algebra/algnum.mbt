///|
// Algebraic numbers and algebraic extensions over Q.
//
// Two normal forms are provided.
//
// * `QuadNum` is the canonical quadratic form `a + b√d` with
//   rational `a, b` and a squarefree integer `d` (`d = 1` exactly for
//   rationals).  Square roots of rationals are put in this form by
//   extracting square factors, and nested quadratic radicals can be
//   denested when their norm is a rational square.
// * `AlgNum` is an element of a general quotient `Q[X]/(m)`,
//   represented by its unique remainder polynomial of degree below
//   `deg m`.  Arithmetic reduces modulo `m`; division uses the
//   extended gcd and is therefore sound (returning `None`) even when
//   the modulus is not irreducible.  Norms, traces and minimal
//   polynomials are computed from the rational multiplication
//   matrix.  Matrices over an `AlgNum` extension support exact
//   generalized eigenspaces and Jordan chains for algebraic
//   eigenvalues such as `√2` or `i`.

// ---------------------------------------------------------------------------
// Integer and rational square roots
// ---------------------------------------------------------------------------

///|
pub fn int_sqrt_exact(n : Int32) -> Int32? {
  if n < 0 {
    return None
  }
  let mut r = 0
  while r * r < n {
    r = r + 1
  }
  if r * r == n {
    Some(r)
  } else {
    None
  }
}

///|
/// Write `n = s²·d` with `d` squarefree; returns `(s, d)`.
pub fn int_squarefree_decomp(n : Int32) -> (Int32, Int32) {
  if n == 0 {
    return (0, 1)
  }
  let sign = if n < 0 { -1 } else { 1 }
  let mut rest = int_abs(n)
  let mut scale = 1
  let mut p = 2
  while p * p <= rest {
    while rest % (p * p) == 0 {
      rest = rest / (p * p)
      scale = scale * p
    }
    p = p + 1
  }
  (scale, sign * rest)
}

///|
/// Floor square root of a nonnegative BigInt by Newton iteration.
pub fn bigint_sqrt_floor(n : BigInt) -> BigInt? {
  if n < 0N {
    return None
  }
  if n == 0N || n == 1N {
    return Some(n)
  }
  let shift = (n.bit_length() + 1) / 2
  let mut x = 1N << shift
  let mut y = (x + n / x) / 2N
  while y < x {
    x = y
    y = (x + n / x) / 2N
  }
  Some(x)
}

///|
pub fn bigint_sqrt_exact(n : BigInt) -> BigInt? {
  match bigint_sqrt_floor(n) {
    Some(r) => if r * r == n { Some(r) } else { None }
    None => None
  }
}

///|
/// Write a BigInt as `s^2*d` with `d` squarefree.  Perfect-square
/// extraction is Newton-based; the residual square factor search is
/// exact trial division (finite, but intentionally not a factoring
/// oracle for adversarial huge semiprimes).
pub fn bigint_squarefree_decomp(n : BigInt) -> (BigInt, BigInt) {
  if n == 0N {
    return (0N, 1N)
  }
  let sign = if n < 0N { -1N } else { 1N }
  let mut rest = bigint_abs(n)
  let mut scale = 1N
  let mut sqfree = 1N
  match bigint_sqrt_exact(rest) {
    Some(r) => return (r, sign)
    None => ()
  }
  let mut p = 2N
  while p * p <= rest {
    if rest % p == 0N {
      let mut e = 0
      while rest % p == 0N {
        rest = rest / p
        e = e + 1
      }
      for _ in 0..<(e / 2) {
        scale = scale * p
      }
      if e % 2 == 1 {
        sqfree = sqfree * p
      }
      match bigint_sqrt_exact(rest) {
        Some(r) => return (scale * r, sign * sqfree)
        None => ()
      }
    }
    p = if p == 2N { 3N } else { p + 2N }
  }
  (scale, sign * sqfree * rest)
}

///|
pub fn rat_sqrt_if_square(r : Rat) -> Rat? {
  match (bigint_sqrt_exact(r.num), bigint_sqrt_exact(r.den)) {
    (Some(a), Some(b)) => Some(rat_make_big(a, b))
    _ => None
  }
}

///|
pub fn rat_is_square(r : Rat) -> Bool {
  match rat_sqrt_if_square(r) {
    Some(_) => true
    None => false
  }
}

// ---------------------------------------------------------------------------
// Quadratic numbers a + b√d
// ---------------------------------------------------------------------------

///|
pub struct QuadNum {
  a : Rat
  b : Rat
  d : BigInt // squarefree; d == 1 exactly when b == 0
} derive(Debug, Eq)

///|
pub extend QuadNum with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend QuadNum with Eq::{not_equal, equal}

///|
pub fn quad_make_big(a : Rat, b : Rat, d0 : BigInt) -> QuadNum {
  if rat_is_zero(b) || d0 == 0N {
    return QuadNum::{ a, b: rat_zero(), d: 1N, }
  }
  let (scale, d) = bigint_squarefree_decomp(d0)
  let bb = rat_mul(b, rat_big_int(scale))
  if d == 1N {
    QuadNum::{ a: rat_add(a, bb), b: rat_zero(), d: 1N, }
  } else {
    QuadNum::{ a, b: bb, d, }
  }
}

///|
pub fn quad_make(a : Rat, b : Rat, d0 : Int32) -> QuadNum {
  quad_make_big(a, b, BigInt::from_int(d0))
}

///|
pub fn quad_rat(r : Rat) -> QuadNum {
  QuadNum::{ a: r, b: rat_zero(), d: 1N, }
}

///|
pub fn quad_int(n : Int32) -> QuadNum {
  quad_rat(rat_int(n))
}

///|
pub fn quad_zero() -> QuadNum {
  quad_int(0)
}

///|
pub fn quad_one() -> QuadNum {
  quad_int(1)
}

///|
/// `√r` in canonical form: square factors of the numerator and
/// denominator are extracted into a rational coefficient.
pub fn quad_sqrt_rat(r : Rat) -> QuadNum {
  if rat_is_zero(r) {
    return quad_zero()
  }
  // √(p/q) = √(p·q)/q for q > 0.
  let (scale, d) = bigint_squarefree_decomp(r.num * r.den)
  let coeff = rat_make_big(scale, r.den)
  if d == 1N {
    quad_rat(coeff)
  } else {
    QuadNum::{ a: rat_zero(), b: coeff, d, }
  }
}

///|
pub fn quad_sqrt_int(n : Int32) -> QuadNum {
  quad_sqrt_rat(rat_int(n))
}

///|
pub fn quad_is_rat(x : QuadNum) -> Bool {
  rat_is_zero(x.b)
}

///|
pub fn quad_to_rat(x : QuadNum) -> Rat? {
  if rat_is_zero(x.b) {
    Some(x.a)
  } else {
    None
  }
}

///|
pub fn quad_compatible(x : QuadNum, y : QuadNum) -> Bool {
  rat_is_zero(x.b) || rat_is_zero(y.b) || x.d == y.d
}

///|
fn quad_common(x : QuadNum, y : QuadNum) -> (QuadNum, QuadNum)? {
  if rat_is_zero(x.b) {
    Some((QuadNum::{ a: x.a, b: rat_zero(), d: y.d, }, y))
  } else if rat_is_zero(y.b) {
    Some((x, QuadNum::{ a: y.a, b: rat_zero(), d: x.d, }))
  } else if x.d == y.d {
    Some((x, y))
  } else {
    None
  }
}

///|
pub fn quad_neg(x : QuadNum) -> QuadNum {
  QuadNum::{ a: rat_neg(x.a), b: rat_neg(x.b), d: x.d, }
}

///|
/// Addition in a common quadratic field (rationals embed in every
/// field).  Incompatible radicands are a precondition violation and
/// yield the first argument.
pub fn quad_add(x : QuadNum, y : QuadNum) -> QuadNum {
  match quad_common(x, y) {
    Some((u, v)) => quad_make_big(rat_add(u.a, v.a), rat_add(u.b, v.b), u.d)
    None => x
  }
}

///|
pub fn quad_sub(x : QuadNum, y : QuadNum) -> QuadNum {
  quad_add(x, quad_neg(y))
}

///|
pub fn quad_mul(x : QuadNum, y : QuadNum) -> QuadNum {
  match quad_common(x, y) {
    Some((u, v)) =>
      quad_make_big(
        rat_add(rat_mul(u.a, v.a), rat_mul(rat_mul(u.b, v.b), rat_big_int(u.d))),
        rat_add(rat_mul(u.a, v.b), rat_mul(u.b, v.a)),
        u.d,
      )
    None => x
  }
}

///|
pub fn quad_conj(x : QuadNum) -> QuadNum {
  QuadNum::{ a: x.a, b: rat_neg(x.b), d: x.d, }
}

///|
pub fn quad_norm(x : QuadNum) -> Rat {
  rat_sub(rat_mul(x.a, x.a), rat_mul(rat_mul(x.b, x.b), rat_big_int(x.d)))
}

///|
pub fn quad_trace(x : QuadNum) -> Rat {
  rat_add(x.a, x.a)
}

///|
pub fn quad_inv(x : QuadNum) -> QuadNum? {
  let n = quad_norm(x)
  if rat_is_zero(n) {
    None
  } else {
    Some(quad_make_big(rat_div(x.a, n), rat_div(rat_neg(x.b), n), x.d))
  }
}

///|
pub fn quad_div(x : QuadNum, y : QuadNum) -> QuadNum? {
  match quad_inv(y) {
    Some(inv) =>
      if quad_compatible(x, inv) {
        Some(quad_mul(x, inv))
      } else {
        None
      }
    None => None
  }
}

///|
pub fn quad_pow(x : QuadNum, n : Int32) -> QuadNum {
  let mut acc = QuadNum::{ a: rat_one(), b: rat_zero(), d: x.d, }
  for _i in 0..<n {
    acc = quad_mul(acc, x)
  }
  acc
}

///|
pub fn quad_eq(x : QuadNum, y : QuadNum) -> Bool {
  match quad_common(x, y) {
    Some((u, v)) => rat_eq(u.a, v.a) && rat_eq(u.b, v.b)
    None => false
  }
}

///|
pub fn quad_is_zero(x : QuadNum) -> Bool {
  rat_is_zero(x.a) && rat_is_zero(x.b)
}

///|
/// Denest `√(a + b√d)` when the norm `a² − b²d` is a rational square
/// `s²`: then `√(a + b√d) = √((a+s)/2) ± √((a−s)/2)`, returned as the
/// pair of canonical simple radicals whose sum is the denesting.
pub fn quad_denested_sqrt(x : QuadNum) -> (QuadNum, QuadNum)? {
  if rat_is_zero(x.b) {
    return Some((quad_sqrt_rat(x.a), quad_zero()))
  }
  match rat_sqrt_if_square(quad_norm(x)) {
    Some(s) => {
      let half = rat_make(1, 2)
      let u = rat_mul(rat_add(x.a, s), half)
      let v = rat_mul(rat_sub(x.a, s), half)
      let first = quad_sqrt_rat(u)
      let second0 = quad_sqrt_rat(v)
      let second = if rat_sign(x.b) < 0 { quad_neg(second0) } else { second0 }
      Some((first, second))
    }
    None => None
  }
}

// ---------------------------------------------------------------------------
// General algebraic numbers Q[X]/(m)
// ---------------------------------------------------------------------------

///|
pub struct AlgNum {
  modulus : QPoly
  poly : QPoly // reduced representative, degree < degree(modulus)
} derive(Debug, Eq)

///|
pub extend AlgNum with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend AlgNum with Eq::{not_equal, equal}

///|
fn alg_normal_modulus(m : QPoly) -> QPoly {
  if qpoly_degree(m) < 1 {
    qpoly_x()
  } else {
    qpoly_monic(m)
  }
}

///|
pub fn alg_make(modulus : QPoly, poly : QPoly) -> AlgNum {
  let m = alg_normal_modulus(modulus)
  AlgNum::{ modulus: m, poly: qpoly_mod(poly, m), }
}

///|
pub fn alg_zero(modulus : QPoly) -> AlgNum {
  alg_make(modulus, qpoly_zero())
}

///|
pub fn alg_one(modulus : QPoly) -> AlgNum {
  alg_make(modulus, qpoly_one())
}

///|
pub fn alg_rat(modulus : QPoly, r : Rat) -> AlgNum {
  alg_make(modulus, qpoly_const(r))
}

///|
pub fn alg_int(modulus : QPoly, n : Int32) -> AlgNum {
  alg_rat(modulus, rat_int(n))
}

///|
/// The class of `X`, the canonical generator (formal root).
pub fn alg_generator(modulus : QPoly) -> AlgNum {
  alg_make(modulus, qpoly_x())
}

///|
pub fn alg_ext_degree(x : AlgNum) -> Int32 {
  qpoly_degree(x.modulus)
}

///|
/// Coefficients of the normal form in the power basis
/// `1, X, …, X^(d−1)`.
pub fn alg_coeffs(x : AlgNum) -> Array[Rat] {
  let out : Array[Rat] = []
  for i in 0..<alg_ext_degree(x) {
    out.push(qpoly_coeff(x.poly, i))
  }
  out
}

///|
pub fn alg_compatible(x : AlgNum, y : AlgNum) -> Bool {
  qpoly_eq(x.modulus, y.modulus)
}

///|
pub fn alg_is_zero(x : AlgNum) -> Bool {
  qpoly_is_zero(x.poly)
}

///|
pub fn alg_eq(x : AlgNum, y : AlgNum) -> Bool {
  alg_compatible(x, y) && qpoly_eq(x.poly, y.poly)
}

///|
pub fn alg_neg(x : AlgNum) -> AlgNum {
  AlgNum::{ modulus: x.modulus, poly: qpoly_neg(x.poly), }
}

///|
/// Binary operations require a common modulus; incompatible inputs
/// yield zero in the first argument's extension.
pub fn alg_add(x : AlgNum, y : AlgNum) -> AlgNum {
  if alg_compatible(x, y) {
    alg_make(x.modulus, qpoly_add(x.poly, y.poly))
  } else {
    alg_zero(x.modulus)
  }
}

///|
pub fn alg_sub(x : AlgNum, y : AlgNum) -> AlgNum {
  alg_add(x, alg_neg(y))
}

///|
pub fn alg_mul(x : AlgNum, y : AlgNum) -> AlgNum {
  if alg_compatible(x, y) {
    alg_make(x.modulus, qpoly_mul(x.poly, y.poly))
  } else {
    alg_zero(x.modulus)
  }
}

///|
pub fn alg_scale_rat(c : Rat, x : AlgNum) -> AlgNum {
  alg_make(x.modulus, qpoly_scale(c, x.poly))
}

///|
pub fn alg_pow(x : AlgNum, n : Int32) -> AlgNum {
  let mut acc = alg_one(x.modulus)
  for _i in 0..<n {
    acc = alg_mul(acc, x)
  }
  acc
}

///|
/// Evaluate a rational polynomial at an algebraic number; the result
/// is automatically reduced to normal form.
pub fn alg_eval_qpoly(p : QPoly, x : AlgNum) -> AlgNum {
  let mut acc = alg_zero(x.modulus)
  for i = p.coeffs.length() - 1; i >= 0; i = i - 1 {
    acc = alg_add(alg_mul(acc, x), alg_rat(x.modulus, p.coeffs[i]))
  }
  acc
}

///|
/// The inverse, when it exists in `Q[X]/(m)`: from an extended gcd
/// `s·f + t·m = 1`, the inverse of `f` is `s`.
pub fn alg_inv(x : AlgNum) -> AlgNum? {
  if alg_is_zero(x) {
    return None
  }
  let ext = qpoly_extgcd(x.poly, x.modulus)
  if qpoly_degree(ext.g) == 0 {
    // ext.g monic of degree 0 is 1.
    Some(alg_make(x.modulus, ext.s))
  } else {
    None
  }
}

///|
pub fn alg_div(x : AlgNum, y : AlgNum) -> AlgNum? {
  if !alg_compatible(x, y) {
    return None
  }
  match alg_inv(y) {
    Some(inv) => Some(alg_mul(x, inv))
    None => None
  }
}

///|
pub fn alg_to_rat(x : AlgNum) -> Rat? {
  if qpoly_degree(x.poly) <= 0 {
    Some(qpoly_coeff(x.poly, 0))
  } else {
    None
  }
}

///|
pub fn alg_of_quad(x : QuadNum) -> AlgNum {
  if rat_is_zero(x.b) {
    alg_make(qpoly_root_factor(x.a), qpoly_const(x.a))
  } else {
    let modulus = QPoly::{ coeffs: [rat_big_int(-x.d), rat_zero(), rat_one()], }
    alg_make(modulus, QPoly::{ coeffs: [x.a, x.b], })
  }
}

///|
/// A square root of a rational as a general algebraic number, in its
/// own (at most quadratic) extension.
pub fn alg_sqrt_rat(r : Rat) -> AlgNum {
  alg_of_quad(quad_sqrt_rat(r))
}

///|
/// The multiplication-by-`x` matrix in the power basis.
pub fn alg_multiplication_matrix(x : AlgNum) -> QMat {
  let d = alg_ext_degree(x)
  let cols : Array[QVec] = []
  for i in 0..<d {
    let monomial : Array[Rat] = []
    for _j in 0..<(i + 1) {
      monomial.push(rat_zero())
    }
    monomial[i] = rat_one()
    let product = qpoly_mod(
      qpoly_mul(x.poly, qpoly_normalize(monomial)),
      x.modulus,
    )
    let col : QVec = []
    for j in 0..<d {
      col.push(qpoly_coeff(product, j))
    }
    cols.push(col)
  }
  qmat_from_columns(cols)
}

///|
pub fn alg_norm(x : AlgNum) -> Rat {
  qmat_det(alg_multiplication_matrix(x))
}

///|
pub fn alg_trace(x : AlgNum) -> Rat {
  qmat_trace(alg_multiplication_matrix(x))
}

///|
/// The minimal polynomial of `x` over Q: the annihilator of the
/// vector `1` under the multiplication matrix.
pub fn alg_minimal_polynomial(x : AlgNum) -> QPoly {
  let d = alg_ext_degree(x)
  let e0 = qvec_zero(d)
  if d > 0 {
    e0[0] = rat_one()
  }
  qmat_vector_annihilator(alg_multiplication_matrix(x), e0)
}

///|
/// Re-present `x` in its own minimal extension `Q[X]/(minpoly x)`,
/// where it is the canonical generator.
pub fn alg_rebase_to_minimal(x : AlgNum) -> AlgNum {
  alg_generator(alg_minimal_polynomial(x))
}

///|
pub fn alg_modulus_irreducible_small(x : AlgNum) -> Bool {
  qpoly_irreducible_upto3(x.modulus)
}

// ---------------------------------------------------------------------------
// Matrices over an algebraic extension
// ---------------------------------------------------------------------------

///|
pub type AlgVec = Array[AlgNum]

///|
pub struct AlgMat {
  n : Int32
  rows : Array[Array[AlgNum]]
  modulus : QPoly
}

///|
pub fn algmat_zero(modulus : QPoly, n : Int32) -> AlgMat {
  let rows : Array[Array[AlgNum]] = []
  for _i in 0..<n {
    let row : Array[AlgNum] = []
    for _j in 0..<n {
      row.push(alg_zero(modulus))
    }
    rows.push(row)
  }
  AlgMat::{ n, rows, modulus: alg_normal_modulus(modulus), }
}

///|
pub fn algmat_identity(modulus : QPoly, n : Int32) -> AlgMat {
  let out = algmat_zero(modulus, n)
  for i in 0..<n {
    out.rows[i][i] = alg_one(modulus)
  }
  out
}

///|
pub fn algmat_from_qmat(a : QMat, modulus : QPoly) -> AlgMat {
  let rows : Array[Array[AlgNum]] = []
  for i in 0..<a.rows.length() {
    let row : Array[AlgNum] = []
    for j in 0..<a.rows[i].length() {
      row.push(alg_rat(modulus, a.rows[i][j]))
    }
    rows.push(row)
  }
  AlgMat::{ n: a.n, rows, modulus: alg_normal_modulus(modulus), }
}

///|
pub fn algmat_scalar(x : AlgNum, n : Int32) -> AlgMat {
  let out = algmat_zero(x.modulus, n)
  for i in 0..<n {
    out.rows[i][i] = x
  }
  out
}

///|
pub fn algvec_zero(modulus : QPoly, n : Int32) -> AlgVec {
  let out : AlgVec = []
  for _i in 0..<n {
    out.push(alg_zero(modulus))
  }
  out
}

///|
pub fn algvec_is_zero(v : AlgVec) -> Bool {
  for i in 0..<v.length() {
    if !alg_is_zero(v[i]) {
      return false
    }
  }
  true
}

///|
pub fn algmat_add(a : AlgMat, b : AlgMat) -> AlgMat {
  let rows : Array[Array[AlgNum]] = []
  for i in 0..<a.rows.length() {
    let row : Array[AlgNum] = []
    for j in 0..<a.rows[i].length() {
      row.push(alg_add(a.rows[i][j], b.rows[i][j]))
    }
    rows.push(row)
  }
  AlgMat::{ n: a.n, rows, modulus: a.modulus, }
}

///|
pub fn algmat_sub(a : AlgMat, b : AlgMat) -> AlgMat {
  let rows : Array[Array[AlgNum]] = []
  for i in 0..<a.rows.length() {
    let row : Array[AlgNum] = []
    for j in 0..<a.rows[i].length() {
      row.push(alg_sub(a.rows[i][j], b.rows[i][j]))
    }
    rows.push(row)
  }
  AlgMat::{ n: a.n, rows, modulus: a.modulus, }
}

///|
pub fn algmat_mul(a : AlgMat, b : AlgMat) -> AlgMat {
  let rows : Array[Array[AlgNum]] = []
  let inner = b.rows.length()
  let cols = if inner == 0 { 0 } else { b.rows[0].length() }
  for i in 0..<a.rows.length() {
    let row : Array[AlgNum] = []
    for j in 0..<cols {
      let mut acc = alg_zero(a.modulus)
      for k in 0..<inner {
        acc = alg_add(acc, alg_mul(a.rows[i][k], b.rows[k][j]))
      }
      row.push(acc)
    }
    rows.push(row)
  }
  AlgMat::{ n: a.n, rows, modulus: a.modulus, }
}

///|
pub fn algmat_vec(a : AlgMat, v : AlgVec) -> AlgVec {
  let out : AlgVec = []
  for i in 0..<a.rows.length() {
    let mut acc = alg_zero(a.modulus)
    for k in 0..<v.length() {
      acc = alg_add(acc, alg_mul(a.rows[i][k], v[k]))
    }
    out.push(acc)
  }
  out
}

///|
pub fn algmat_eq(a : AlgMat, b : AlgMat) -> Bool {
  if a.rows.length() != b.rows.length() {
    return false
  }
  for i in 0..<a.rows.length() {
    if a.rows[i].length() != b.rows[i].length() {
      return false
    }
    for j in 0..<a.rows[i].length() {
      if !alg_eq(a.rows[i][j], b.rows[i][j]) {
        return false
      }
    }
  }
  true
}

///|
pub fn algmat_pow(a : AlgMat, k : Int32) -> AlgMat {
  let mut acc = algmat_identity(a.modulus, a.n)
  for _i in 0..<k {
    acc = algmat_mul(acc, a)
  }
  acc
}

///|
pub fn algmat_trace(a : AlgMat) -> AlgNum {
  let mut acc = alg_zero(a.modulus)
  for i in 0..<a.n {
    acc = alg_add(acc, a.rows[i][i])
  }
  acc
}

///|
pub fn algmat_from_columns(modulus : QPoly, cols : Array[AlgVec]) -> AlgMat {
  if cols.length() == 0 {
    return algmat_zero(modulus, 0)
  }
  let n = cols[0].length()
  let rows : Array[Array[AlgNum]] = []
  for i in 0..<n {
    let row : Array[AlgNum] = []
    for j in 0..<cols.length() {
      row.push(cols[j][i])
    }
    rows.push(row)
  }
  AlgMat::{ n, rows, modulus: alg_normal_modulus(modulus), }
}

// ---------------------------------------------------------------------------
// Row reduction over an extension
// ---------------------------------------------------------------------------

///|
pub struct AlgRref {
  rows : Array[Array[AlgNum]]
  pivots : Array[Int32]
  rank : Int32
}

///|
fn algrows_copy(rows : Array[Array[AlgNum]]) -> Array[Array[AlgNum]] {
  let out : Array[Array[AlgNum]] = []
  for i in 0..<rows.length() {
    let row : Array[AlgNum] = []
    for j in 0..<rows[i].length() {
      row.push(rows[i][j])
    }
    out.push(row)
  }
  out
}

///|
/// Reduced row echelon form over `Q[X]/(m)`.  Pivots must be units;
/// over a field extension (irreducible `m`) every nonzero entry is.
pub fn algrows_rref(input : Array[Array[AlgNum]], ncols : Int32) -> AlgRref {
  let rows = algrows_copy(input)
  let pivots : Array[Int32] = []
  let mut r = 0
  for c in 0..<ncols {
    if r >= rows.length() {
      break
    }
    let mut pivot = -1
    let mut pivot_inv = alg_zero(
      if rows.length() > 0 && ncols > 0 {
        rows[0][0].modulus
      } else {
        qpoly_x()
      },
    )
    for i in r..<rows.length() {
      match alg_inv(rows[i][c]) {
        Some(inv) => {
          pivot = i
          pivot_inv = inv
          break
        }
        None => ()
      }
    }
    if pivot < 0 {
      continue
    }
    if pivot != r {
      let tmp = rows[r]
      rows[r] = rows[pivot]
      rows[pivot] = tmp
    }
    for j in 0..<ncols {
      rows[r][j] = alg_mul(rows[r][j], pivot_inv)
    }
    for i in 0..<rows.length() {
      if i != r && !alg_is_zero(rows[i][c]) {
        let factor = rows[i][c]
        for j in 0..<ncols {
          rows[i][j] = alg_sub(rows[i][j], alg_mul(factor, rows[r][j]))
        }
      }
    }
    pivots.push(c)
    r = r + 1
  }
  AlgRref::{ rows, pivots, rank: pivots.length(), }
}

///|
pub fn algvec_rank(vecs : Array[AlgVec]) -> Int32 {
  if vecs.length() == 0 {
    0
  } else {
    algrows_rref(vecs, vecs[0].length()).rank
  }
}

///|
pub fn algvec_in_span(vecs : Array[AlgVec], v : AlgVec) -> Bool {
  if algvec_is_zero(v) {
    return true
  }
  let with_v : Array[AlgVec] = []
  for i in 0..<vecs.length() {
    with_v.push(vecs[i])
  }
  with_v.push(v)
  algvec_rank(vecs) == algvec_rank(with_v)
}

///|
pub fn algrows_nullspace(
  modulus : QPoly,
  rows : Array[Array[AlgNum]],
  ncols : Int32,
) -> Array[AlgVec] {
  let rr = algrows_rref(rows, ncols)
  let is_pivot : Array[Bool] = []
  for _i in 0..<ncols {
    is_pivot.push(false)
  }
  for i in 0..<rr.pivots.length() {
    is_pivot[rr.pivots[i]] = true
  }
  let out : Array[AlgVec] = []
  for f in 0..<ncols {
    if !is_pivot[f] {
      let v = algvec_zero(modulus, ncols)
      v[f] = alg_one(modulus)
      for i in 0..<rr.pivots.length() {
        v[rr.pivots[i]] = alg_neg(rr.rows[i][f])
      }
      out.push(v)
    }
  }
  out
}

///|
pub fn algmat_nullspace(a : AlgMat) -> Array[AlgVec] {
  let cols = if a.rows.length() == 0 { a.n } else { a.rows[0].length() }
  algrows_nullspace(a.modulus, a.rows, cols)
}

///|
pub fn algmat_nullity(a : AlgMat) -> Int32 {
  algmat_nullspace(a).length()
}

///|
pub fn algmat_rank(a : AlgMat) -> Int32 {
  let cols = if a.rows.length() == 0 { 0 } else { a.rows[0].length() }
  algrows_rref(a.rows, cols).rank
}

// ---------------------------------------------------------------------------
// Characteristic polynomials and generalized eigenspaces over an extension
// ---------------------------------------------------------------------------

///|
fn algpoly_normalize(coeffs : Array[AlgNum]) -> Array[AlgNum] {
  let mut last = -1
  for i in 0..<coeffs.length() {
    if !alg_is_zero(coeffs[i]) {
      last = i
    }
  }
  let out : Array[AlgNum] = []
  if coeffs.length() == 0 {
    return out
  }
  if last < 0 {
    out.push(alg_zero(coeffs[0].modulus))
  } else {
    for i in 0..<(last + 1) {
      out.push(coeffs[i])
    }
  }
  out
}

///|
/// Characteristic polynomial over the extension, as low-to-high
/// `AlgNum` coefficients, by Newton's identities.
pub fn algmat_charpoly(a : AlgMat) -> Array[AlgNum] {
  let n = a.n
  let e : Array[AlgNum] = [alg_one(a.modulus)]
  let traces : Array[AlgNum] = [alg_zero(a.modulus)]
  let mut power = algmat_identity(a.modulus, n)
  for _k in 1..<(n + 1) {
    power = algmat_mul(power, a)
    traces.push(algmat_trace(power))
  }
  for k in 1..<(n + 1) {
    let mut acc = alg_zero(a.modulus)
    for i in 1..<(k + 1) {
      let term = alg_mul(e[k - i], traces[i])
      acc = if i % 2 == 1 { alg_add(acc, term) } else { alg_sub(acc, term) }
    }
    match alg_div(acc, alg_int(a.modulus, k)) {
      Some(v) => e.push(v)
      None => e.push(alg_zero(a.modulus))
    }
  }
  let coeffs : Array[AlgNum] = []
  for k in 0..<(n + 1) {
    let idx = n - k
    coeffs.push(if idx % 2 == 0 { e[idx] } else { alg_neg(e[idx]) })
  }
  algpoly_normalize(coeffs)
}

///|
fn algpoly_div_linear(
  coeffs0 : Array[AlgNum],
  root : AlgNum,
) -> (Array[AlgNum], AlgNum) {
  let coeffs = algpoly_normalize(coeffs0)
  if coeffs.length() <= 1 {
    let rem = if coeffs.length() == 0 {
      alg_zero(root.modulus)
    } else {
      coeffs[0]
    }
    return ([alg_zero(root.modulus)], rem)
  }
  let quotient : Array[AlgNum] = []
  for _i in 0..<(coeffs.length() - 1) {
    quotient.push(alg_zero(root.modulus))
  }
  let mut carry = alg_zero(root.modulus)
  for i = coeffs.length() - 1; i >= 1; i = i - 1 {
    carry = alg_add(coeffs[i], alg_mul(root, carry))
    quotient[i - 1] = carry
  }
  let remainder = alg_add(coeffs[0], alg_mul(root, carry))
  (algpoly_normalize(quotient), remainder)
}

///|
pub fn algmat_eigenvalue_multiplicity(a : AlgMat, lambda : AlgNum) -> Int32 {
  let mut coeffs = algmat_charpoly(a)
  let mut count = 0
  while coeffs.length() > 1 || (coeffs.length() == 1 && alg_is_zero(coeffs[0])) {
    if coeffs.length() == 1 {
      break
    }
    let (quotient, remainder) = algpoly_div_linear(coeffs, lambda)
    if !alg_is_zero(remainder) {
      break
    }
    coeffs = quotient
    count = count + 1
  }
  count
}

///|
pub struct AlgGeneralizedEigenspace {
  eigenvalue : AlgNum
  algebraic_multiplicity : Int32
  geometric_multiplicity : Int32
  index : Int32
  nullities : Array[Int32]
  block_sizes : Array[Int32]
  basis : Array[AlgVec]
}

///|
fn algmat_shifted(a : AlgMat, lambda : AlgNum) -> AlgMat {
  algmat_sub(a, algmat_scalar(lambda, a.n))
}

///|
pub fn algmat_generalized_eigenspace(
  a : AlgMat,
  lambda : AlgNum,
) -> AlgGeneralizedEigenspace {
  let alg = algmat_eigenvalue_multiplicity(a, lambda)
  if alg == 0 {
    return AlgGeneralizedEigenspace::{
      eigenvalue: lambda,
      algebraic_multiplicity: 0,
      geometric_multiplicity: 0,
      index: 0,
      nullities: [],
      block_sizes: [],
      basis: [],
    }
  }
  let shifted = algmat_shifted(a, lambda)
  let nullities : Array[Int32] = []
  let mut power = algmat_identity(a.modulus, a.n)
  for _k in 0..<a.n {
    power = algmat_mul(power, shifted)
    let nullity = algmat_nullity(power)
    nullities.push(nullity)
    if nullity >= alg {
      break
    }
  }
  let index = nullities.length()
  AlgGeneralizedEigenspace::{
    eigenvalue: lambda,
    algebraic_multiplicity: alg,
    geometric_multiplicity: if index > 0 {
      nullities[0]
    } else {
      0
    },
    index,
    nullities,
    block_sizes: block_sizes_of_nullities(nullities),
    basis: algmat_nullspace(algmat_pow(shifted, index)),
  }
}

///|
fn alg_quotient_representatives(
  kernel : Array[AlgVec],
  lower_kernel : Array[AlgVec],
  existing : Array[AlgVec],
) -> Array[AlgVec] {
  let forbidden : Array[AlgVec] = []
  for i in 0..<lower_kernel.length() {
    forbidden.push(lower_kernel[i])
  }
  for i in 0..<existing.length() {
    forbidden.push(existing[i])
  }
  let chosen : Array[AlgVec] = []
  for i in 0..<kernel.length() {
    let span_test : Array[AlgVec] = []
    for j in 0..<forbidden.length() {
      span_test.push(forbidden[j])
    }
    for j in 0..<chosen.length() {
      span_test.push(chosen[j])
    }
    if !algvec_in_span(span_test, kernel[i]) {
      chosen.push(kernel[i])
    }
  }
  chosen
}

///|
/// Jordan chains over an algebraic extension, head first.
pub fn algmat_Jordan_chains(
  a : AlgMat,
  lambda : AlgNum,
) -> Array[Array[AlgVec]] {
  let info = algmat_generalized_eigenspace(a, lambda)
  let chains : Array[Array[AlgVec]] = []
  if info.index == 0 {
    return chains
  }
  let shifted = algmat_shifted(a, lambda)
  let kernels : Array[Array[AlgVec]] = [[]]
  let mut power = algmat_identity(a.modulus, a.n)
  for _k in 0..<info.index {
    power = algmat_mul(power, shifted)
    kernels.push(algmat_nullspace(power))
  }
  let m = info.index
  let heads = alg_quotient_representatives(kernels[m], kernels[m - 1], [])
  for i in 0..<heads.length() {
    chains.push([heads[i]])
  }
  for k = m - 1; k >= 1; k = k - 1 {
    for c in 0..<chains.length() {
      let chain = chains[c]
      chain.push(algmat_vec(shifted, chain[chain.length() - 1]))
    }
    let tails : Array[AlgVec] = []
    for c in 0..<chains.length() {
      tails.push(chains[c][chains[c].length() - 1])
    }
    let fresh = alg_quotient_representatives(kernels[k], kernels[k - 1], tails)
    for i in 0..<fresh.length() {
      chains.push([fresh[i]])
    }
  }
  chains
}

///|
pub struct AlgJordanDecomposition {
  p : AlgMat
  j : AlgMat
  eigenvalues : Array[AlgNum]
  block_sizes : Array[Array[Int32]]
}

///|
/// Exact Jordan decomposition over an algebraic extension for given
/// distinct eigenvalues exhausting the spectrum.
pub fn algmat_Jordan_decomposition(
  a : AlgMat,
  eigenvalues : Array[AlgNum],
) -> AlgJordanDecomposition? {
  let columns : Array[AlgVec] = []
  let all_blocks : Array[Array[Int32]] = []
  let jordan = algmat_zero(a.modulus, a.n)
  let mut offset = 0
  for e in 0..<eigenvalues.length() {
    let lambda = eigenvalues[e]
    let chains = algmat_Jordan_chains(a, lambda)
    let sizes : Array[Int32] = []
    for c in 0..<chains.length() {
      let chain = chains[c]
      sizes.push(chain.length())
      for idx = chain.length() - 1; idx >= 0; idx = idx - 1 {
        columns.push(chain[idx])
      }
      for t in 0..<chain.length() {
        jordan.rows[offset + t][offset + t] = lambda
        if t + 1 < chain.length() {
          jordan.rows[offset + t][offset + t + 1] = alg_one(a.modulus)
        }
      }
      offset = offset + chain.length()
    }
    all_blocks.push(sizes)
  }
  if offset != a.n || columns.length() != a.n {
    return None
  }
  let p = algmat_from_columns(a.modulus, columns)
  if algmat_rank(p) != a.n {
    return None
  }
  if !algmat_eq(algmat_mul(a, p), algmat_mul(p, jordan)) {
    return None
  }
  Some(AlgJordanDecomposition::{
    p,
    j: jordan,
    eigenvalues,
    block_sizes: all_blocks,
  })
}
