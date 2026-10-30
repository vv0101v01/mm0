///|
// Exact univariate polynomials over Q.
//
// `QPoly` is the coefficient-level counterpart of the symbolic
// `RPoly`: coefficients are normalized rationals, polynomials are
// stored low-to-high with no trailing zeros, and the module provides
// division, gcd and extended gcd, derivatives, Yun's squarefree
// factorization, and rational-root extraction.  These are the
// operations needed for repeated eigenvalues, primary
// decompositions, and algebraic-number normal forms.  As everywhere
// in the exact layers, rational coefficients are arbitrary-precision `Rat`s.

///|
pub fn rat_inv(a : Rat) -> Rat {
  if a.num == 0 {
    rat_zero()
  } else {
    rat_make_big(a.den, a.num)
  }
}

///|
pub fn rat_div(a : Rat, b : Rat) -> Rat {
  rat_mul(a, rat_inv(b))
}

///|
pub fn rat_eq(a : Rat, b : Rat) -> Bool {
  a.num == b.num && a.den == b.den
}

///|
pub fn rat_is_one(a : Rat) -> Bool {
  a.num == 1N && a.den == 1N
}

///|
pub fn rat_sign(a : Rat) -> Int32 {
  if a.num > 0 {
    1
  } else if a.num < 0 {
    -1
  } else {
    0
  }
}

///|
pub struct QPoly {
  coeffs : Array[Rat] // low to high, normalized
} derive(Debug, Eq)

///|
pub extend QPoly with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend QPoly with Eq::{not_equal, equal}

///|
pub fn qpoly_normalize(coeffs : Array[Rat]) -> QPoly {
  let mut last = -1
  for i in 0..<coeffs.length() {
    if !rat_is_zero(coeffs[i]) {
      last = i
    }
  }
  let out : Array[Rat] = []
  if last < 0 {
    out.push(rat_zero())
  } else {
    for i in 0..<(last + 1) {
      out.push(rat_make_big(coeffs[i].num, coeffs[i].den))
    }
  }
  QPoly::{ coeffs: out, }
}

///|
pub fn qpoly_zero() -> QPoly {
  QPoly::{ coeffs: [rat_zero()], }
}

///|
pub fn qpoly_one() -> QPoly {
  QPoly::{ coeffs: [rat_one()], }
}

///|
pub fn qpoly_x() -> QPoly {
  QPoly::{ coeffs: [rat_zero(), rat_one()], }
}

///|
pub fn qpoly_const(c : Rat) -> QPoly {
  qpoly_normalize([c])
}

///|
pub fn qpoly_int(n : Int32) -> QPoly {
  qpoly_const(rat_int(n))
}

///|
pub fn qpoly_is_zero(p : QPoly) -> Bool {
  p.coeffs.length() == 1 && rat_is_zero(p.coeffs[0])
}

///|
/// Degree, with the zero polynomial of degree -1.
pub fn qpoly_degree(p : QPoly) -> Int32 {
  if qpoly_is_zero(p) {
    -1
  } else {
    p.coeffs.length() - 1
  }
}

///|
pub fn qpoly_coeff(p : QPoly, i : Int32) -> Rat {
  if i >= 0 && i < p.coeffs.length() {
    p.coeffs[i]
  } else {
    rat_zero()
  }
}

///|
pub fn qpoly_leading(p : QPoly) -> Rat {
  if qpoly_is_zero(p) {
    rat_zero()
  } else {
    p.coeffs[p.coeffs.length() - 1]
  }
}

///|
pub fn qpoly_add(a : QPoly, b : QPoly) -> QPoly {
  let n = if a.coeffs.length() > b.coeffs.length() {
    a.coeffs.length()
  } else {
    b.coeffs.length()
  }
  let out : Array[Rat] = []
  for i in 0..<n {
    out.push(rat_add(qpoly_coeff(a, i), qpoly_coeff(b, i)))
  }
  qpoly_normalize(out)
}

///|
pub fn qpoly_neg(a : QPoly) -> QPoly {
  let out : Array[Rat] = []
  for i in 0..<a.coeffs.length() {
    out.push(rat_neg(a.coeffs[i]))
  }
  qpoly_normalize(out)
}

///|
pub fn qpoly_sub(a : QPoly, b : QPoly) -> QPoly {
  qpoly_add(a, qpoly_neg(b))
}

///|
pub fn qpoly_scale(c : Rat, a : QPoly) -> QPoly {
  let out : Array[Rat] = []
  for i in 0..<a.coeffs.length() {
    out.push(rat_mul(c, a.coeffs[i]))
  }
  qpoly_normalize(out)
}

///|
fn int_poly_trim(a : Array[BigInt]) -> Array[BigInt] {
  let mut last = a.length() - 1
  while last > 0 && a[last] == 0N {
    last = last - 1
  }
  if last < 0 {
    return [0N]
  }
  let out : Array[BigInt] = []
  for i in 0..<(last + 1) {
    out.push(a[i])
  }
  out
}

///|
fn int_poly_is_zero(a : Array[BigInt]) -> Bool {
  for i in 0..<a.length() {
    if a[i] != 0N {
      return false
    }
  }
  true
}

///|
fn int_poly_coeff(a : Array[BigInt], i : Int32) -> BigInt {
  if i >= 0 && i < a.length() {
    a[i]
  } else {
    0N
  }
}

///|
fn int_poly_add(a : Array[BigInt], b : Array[BigInt]) -> Array[BigInt] {
  let n = if a.length() > b.length() { a.length() } else { b.length() }
  let out : Array[BigInt] = []
  for i in 0..<n {
    out.push(int_poly_coeff(a, i) + int_poly_coeff(b, i))
  }
  int_poly_trim(out)
}

///|
fn int_poly_sub(a : Array[BigInt], b : Array[BigInt]) -> Array[BigInt] {
  let n = if a.length() > b.length() { a.length() } else { b.length() }
  let out : Array[BigInt] = []
  for i in 0..<n {
    out.push(int_poly_coeff(a, i) - int_poly_coeff(b, i))
  }
  int_poly_trim(out)
}

///|
fn int_poly_slice(
  a : Array[BigInt],
  start : Int32,
  end : Int32,
) -> Array[BigInt] {
  let out : Array[BigInt] = []
  for i in start..<end {
    out.push(int_poly_coeff(a, i))
  }
  if out.length() == 0 {
    out.push(0N)
  }
  int_poly_trim(out)
}

///|
fn int_poly_shift(a : Array[BigInt], amount : Int32) -> Array[BigInt] {
  if int_poly_is_zero(a) {
    return [0N]
  }
  let out : Array[BigInt] = []
  for _i in 0..<amount {
    out.push(0N)
  }
  for i in 0..<a.length() {
    out.push(a[i])
  }
  out
}

///|
fn int_poly_mul_school(a : Array[BigInt], b : Array[BigInt]) -> Array[BigInt] {
  if int_poly_is_zero(a) || int_poly_is_zero(b) {
    return [0N]
  }
  let out : Array[BigInt] = []
  for _i in 0..<(a.length() + b.length() - 1) {
    out.push(0N)
  }
  for i in 0..<a.length() {
    if a[i] == 0N {
      continue
    }
    for j in 0..<b.length() {
      if b[j] != 0N {
        out[i + j] = out[i + j] + a[i] * b[j]
      }
    }
  }
  int_poly_trim(out)
}

///|
fn int_poly_mul_fast(a : Array[BigInt], b : Array[BigInt]) -> Array[BigInt] {
  let aa = int_poly_trim(a)
  let bb = int_poly_trim(b)
  if int_poly_is_zero(aa) || int_poly_is_zero(bb) {
    return [0N]
  }
  let shortest = if aa.length() < bb.length() {
    aa.length()
  } else {
    bb.length()
  }
  if shortest < 24 || aa.length() * bb.length() <= 4096 {
    return int_poly_mul_school(aa, bb)
  }
  let longest = if aa.length() > bb.length() {
    aa.length()
  } else {
    bb.length()
  }
  let split = longest / 2
  let a0 = int_poly_slice(aa, 0, split)
  let a1 = int_poly_slice(aa, split, aa.length())
  let b0 = int_poly_slice(bb, 0, split)
  let b1 = int_poly_slice(bb, split, bb.length())
  let z0 = int_poly_mul_fast(a0, b0)
  let z2 = int_poly_mul_fast(a1, b1)
  let z1_full = int_poly_mul_fast(int_poly_add(a0, a1), int_poly_add(b0, b1))
  let z1 = int_poly_sub(int_poly_sub(z1_full, z0), z2)
  int_poly_add(
    int_poly_add(z0, int_poly_shift(z1, split)),
    int_poly_shift(z2, 2 * split),
  )
}

///|
fn qpoly_integer_scaled(p : QPoly) -> (Array[BigInt], BigInt) {
  let mut denominator = 1N
  for i in 0..<p.coeffs.length() {
    denominator = bigint_lcm(denominator, p.coeffs[i].den)
  }
  let coeffs : Array[BigInt] = []
  for i in 0..<p.coeffs.length() {
    coeffs.push(p.coeffs[i].num * (denominator / p.coeffs[i].den))
  }
  (int_poly_trim(coeffs), denominator)
}

///|
fn qpoly_nonzero_count(p : QPoly) -> Int32 {
  let mut count = 0
  for i in 0..<p.coeffs.length() {
    if !rat_is_zero(p.coeffs[i]) {
      count = count + 1
    }
  }
  count
}

///|
pub fn qpoly_mul(a : QPoly, b : QPoly) -> QPoly {
  if qpoly_is_zero(a) || qpoly_is_zero(b) {
    return qpoly_zero()
  }
  // Sparse inputs retain the direct rational convolution (with
  // zero coefficients skipped).  Dense inputs are scaled once to
  // integer polynomials and multiplied by Karatsuba above the
  // schoolbook threshold, avoiding a gcd normalization for every
  // pair of rational coefficients.
  let sparse_work = qpoly_nonzero_count(a) * qpoly_nonzero_count(b)
  let dense_work = a.coeffs.length() * b.coeffs.length()
  if sparse_work <= 4096 || sparse_work * 4 <= dense_work {
    let out : Array[Rat] = []
    for _i in 0..<(a.coeffs.length() + b.coeffs.length() - 1) {
      out.push(rat_zero())
    }
    for i in 0..<a.coeffs.length() {
      if rat_is_zero(a.coeffs[i]) {
        continue
      }
      for j in 0..<b.coeffs.length() {
        if !rat_is_zero(b.coeffs[j]) {
          out[i + j] = rat_add(out[i + j], rat_mul(a.coeffs[i], b.coeffs[j]))
        }
      }
    }
    return qpoly_normalize(out)
  }
  let (aa, da) = qpoly_integer_scaled(a)
  let (bb, db) = qpoly_integer_scaled(b)
  let product = int_poly_mul_fast(aa, bb)
  let denominator = da * db
  let out : Array[Rat] = []
  for i in 0..<product.length() {
    out.push(rat_make_big(product[i], denominator))
  }
  qpoly_normalize(out)
}

///|
pub fn qpoly_pow(a : QPoly, n : Int32) -> QPoly {
  let mut acc = qpoly_one()
  let mut base = a
  let mut exponent = n
  while exponent > 0 {
    if exponent % 2 == 1 {
      acc = qpoly_mul(acc, base)
    }
    exponent = exponent / 2
    if exponent > 0 {
      base = qpoly_mul(base, base)
    }
  }
  acc
}

///|
pub fn qpoly_eq(a : QPoly, b : QPoly) -> Bool {
  qpoly_is_zero(qpoly_sub(a, b))
}

///|
pub fn qpoly_is_one(a : QPoly) -> Bool {
  qpoly_eq(a, qpoly_one())
}

///|
pub fn qpoly_monic(a : QPoly) -> QPoly {
  if qpoly_is_zero(a) {
    a
  } else {
    qpoly_scale(rat_inv(qpoly_leading(a)), a)
  }
}

///|
pub fn qpoly_eval(p : QPoly, x : Rat) -> Rat {
  let mut acc = rat_zero()
  for i = p.coeffs.length() - 1; i >= 0; i = i - 1 {
    acc = rat_add(rat_mul(acc, x), p.coeffs[i])
  }
  acc
}

///|
/// The primitive integer representative of a nonzero polynomial:
/// denominators cleared, integer content divided out, and leading
/// coefficient positive.  Zero is unchanged.
pub fn qpoly_primitive_part(p : QPoly) -> QPoly {
  if qpoly_is_zero(p) {
    return p
  }
  let ints = qpoly_integer_coeffs_big(p)
  let out : Array[Rat] = []
  for i in 0..<ints.length() {
    out.push(rat_big_int(ints[i]))
  }
  qpoly_normalize(out)
}

///|
/// Pseudo-remainder: for `e = deg(a) − deg(b) + 1`, a polynomial `r`
/// of degree below `deg(b)` with `lc(b)^e · a = q·b + r`.  Integer
/// inputs give integer outputs, which keeps the gcd remainder
/// sequence free of rational coefficient explosion.
pub fn qpoly_pseudo_remainder(a : QPoly, b : QPoly) -> QPoly {
  if qpoly_is_zero(b) || qpoly_degree(a) < qpoly_degree(b) {
    return a
  }
  let db = qpoly_degree(b)
  let lb = qpoly_leading(b)
  let mut r = a
  while !qpoly_is_zero(r) && qpoly_degree(r) >= db {
    let shift = qpoly_degree(r) - db
    // r := lb*r − lc(r)·X^shift·b
    let sub : Array[Rat] = []
    for _i in 0..<shift {
      sub.push(rat_zero())
    }
    for i in 0..<b.coeffs.length() {
      sub.push(rat_mul(qpoly_leading(r), b.coeffs[i]))
    }
    r = qpoly_sub(qpoly_scale(lb, r), qpoly_normalize(sub))
  }
  r
}

///|
pub fn qpoly_derivative(p : QPoly) -> QPoly {
  let out : Array[Rat] = []
  for i in 1..<p.coeffs.length() {
    out.push(rat_mul(rat_int(i), p.coeffs[i]))
  }
  qpoly_normalize(out)
}

///|
pub struct QPolyDiv {
  quotient : QPoly
  remainder : QPoly
}

///|
/// Euclidean division; a zero divisor yields quotient and remainder
/// zero (callers needing the distinction test the divisor first).
pub fn qpoly_divmod(a : QPoly, b : QPoly) -> QPolyDiv {
  if qpoly_is_zero(b) {
    return QPolyDiv::{ quotient: qpoly_zero(), remainder: qpoly_zero(), }
  }
  let db = qpoly_degree(b)
  let qcoeffs : Array[Rat] = []
  let qlen = if qpoly_degree(a) >= db { qpoly_degree(a) - db + 1 } else { 1 }
  for _i in 0..<qlen {
    qcoeffs.push(rat_zero())
  }
  let mut rem = a
  let lb = qpoly_leading(b)
  while !qpoly_is_zero(rem) && qpoly_degree(rem) >= db {
    let shift = qpoly_degree(rem) - db
    let coeff = rat_div(qpoly_leading(rem), lb)
    qcoeffs[shift] = coeff
    let sub : Array[Rat] = []
    for _i in 0..<shift {
      sub.push(rat_zero())
    }
    for i in 0..<b.coeffs.length() {
      sub.push(rat_mul(coeff, b.coeffs[i]))
    }
    rem = qpoly_sub(rem, qpoly_normalize(sub))
  }
  QPolyDiv::{ quotient: qpoly_normalize(qcoeffs), remainder: rem, }
}

///|
pub fn qpoly_mod(a : QPoly, b : QPoly) -> QPoly {
  qpoly_divmod(a, b).remainder
}

///|
pub fn qpoly_div_exact(a : QPoly, b : QPoly) -> QPoly {
  qpoly_divmod(a, b).quotient
}

///|
pub fn qpoly_gcd(a0 : QPoly, b0 : QPoly) -> QPoly {
  // Primitive pseudo-remainder sequence: exact over Q up to the
  // final monic scaling, without intermediate fraction growth.
  let mut a = qpoly_primitive_part(a0)
  let mut b = qpoly_primitive_part(b0)
  if qpoly_degree(a) < qpoly_degree(b) {
    let tmp = a
    a = b
    b = tmp
  }
  while !qpoly_is_zero(b) {
    let r = qpoly_primitive_part(qpoly_pseudo_remainder(a, b))
    a = b
    b = r
  }
  qpoly_monic(a)
}

///|
pub struct QPolyExtGcd {
  g : QPoly
  s : QPoly
  t : QPoly
}

///|
/// Extended gcd: `s·a + t·b = g`, with `g` monic.
pub fn qpoly_extgcd(a0 : QPoly, b0 : QPoly) -> QPolyExtGcd {
  let mut old_r = a0
  let mut r = b0
  let mut old_s = qpoly_one()
  let mut s = qpoly_zero()
  let mut old_t = qpoly_zero()
  let mut t = qpoly_one()
  while !qpoly_is_zero(r) {
    let dm = qpoly_divmod(old_r, r)
    let q = dm.quotient
    // Keep the remainder sequence primitive.  Replacing the
    // remainder by a rational scalar multiple is compensated by
    // scaling the Bezout coefficient recurrence by the same scalar.
    let next_r0 = dm.remainder
    let next_r = qpoly_primitive_part(next_r0)
    let scalar = if qpoly_is_zero(next_r0) {
      rat_one()
    } else {
      rat_div(qpoly_leading(next_r), qpoly_leading(next_r0))
    }
    let next_s = qpoly_scale(scalar, qpoly_sub(old_s, qpoly_mul(q, s)))
    let next_t = qpoly_scale(scalar, qpoly_sub(old_t, qpoly_mul(q, t)))
    old_r = r
    r = next_r
    old_s = s
    s = next_s
    old_t = t
    t = next_t
  }
  if qpoly_is_zero(old_r) {
    QPolyExtGcd::{ g: old_r, s: old_s, t: old_t, }
  } else {
    let inv = rat_inv(qpoly_leading(old_r))
    QPolyExtGcd::{
      g: qpoly_monic(old_r),
      s: qpoly_scale(inv, old_s),
      t: qpoly_scale(inv, old_t),
    }
  }
}

///|
/// The squarefree kernel (radical) `p / gcd(p, p')`, monic.
pub fn qpoly_squarefree_part(p : QPoly) -> QPoly {
  if qpoly_degree(p) <= 0 {
    return qpoly_one()
  }
  let f = qpoly_monic(p)
  let g = qpoly_gcd(f, qpoly_derivative(f))
  qpoly_monic(qpoly_div_exact(f, g))
}

///|
pub fn qpoly_is_squarefree(p : QPoly) -> Bool {
  qpoly_degree(p) <= 0 || qpoly_is_one(qpoly_gcd(p, qpoly_derivative(p)))
}

///|
pub struct QPolyFactor {
  factor : QPoly
  multiplicity : Int32
}

///|
pub fn qpoly_factor(factor : QPoly, multiplicity : Int32) -> QPolyFactor {
  QPolyFactor::{ factor, multiplicity, }
}

///|
/// Yun's squarefree factorization: monic squarefree factors grouped
/// by the multiplicity with which they occur in `p`.
pub fn qpoly_squarefree_factorization(p : QPoly) -> Array[QPolyFactor] {
  let out : Array[QPolyFactor] = []
  if qpoly_degree(p) <= 0 {
    return out
  }
  let f = qpoly_monic(p)
  let df = qpoly_derivative(f)
  let a0 = qpoly_gcd(f, df)
  let mut b = qpoly_div_exact(f, a0)
  let mut c = qpoly_div_exact(df, a0)
  let mut d = qpoly_sub(c, qpoly_derivative(b))
  let mut i = 1
  while qpoly_degree(b) > 0 {
    let a = qpoly_gcd(b, d)
    if qpoly_degree(a) > 0 {
      out.push(qpoly_factor(qpoly_monic(a), i))
    }
    b = qpoly_div_exact(b, a)
    c = qpoly_div_exact(d, a)
    i = i + 1
    d = qpoly_sub(c, qpoly_derivative(b))
  }
  out
}

///|
pub fn qpoly_root_factor(r : Rat) -> QPoly {
  QPoly::{ coeffs: [rat_neg(r), rat_one()], }
}

///|
/// Multiplicity of the rational root `r` (0 when not a root).
pub fn qpoly_root_multiplicity(p : QPoly, r : Rat) -> Int32 {
  if qpoly_is_zero(p) {
    return 0
  }
  let factor = qpoly_root_factor(r)
  let mut q = p
  let mut count = 0
  while !qpoly_is_zero(q) {
    let dm = qpoly_divmod(q, factor)
    if !qpoly_is_zero(dm.remainder) {
      break
    }
    q = dm.quotient
    count = count + 1
  }
  count
}

///|
/// Arbitrary-precision primitive integer coefficients of `p`:
/// common denominators cleared, content divided out, leading
/// coefficient positive.
pub fn qpoly_integer_coeffs_big(p : QPoly) -> Array[BigInt] {
  let mut lcm = 1N
  for i in 0..<p.coeffs.length() {
    lcm = bigint_lcm(lcm, p.coeffs[i].den)
  }
  let out : Array[BigInt] = []
  let mut content = 0N
  for i in 0..<p.coeffs.length() {
    let v = p.coeffs[i].num * (lcm / p.coeffs[i].den)
    out.push(v)
    content = bigint_gcd(content, v)
  }
  if content > 1N {
    for i in 0..<out.length() {
      out[i] = out[i] / content
    }
  }
  if out.length() > 0 && out[out.length() - 1] < 0N {
    for i in 0..<out.length() {
      out[i] = -out[i]
    }
  }
  out
}

///|
/// Legacy 32-bit view of `qpoly_integer_coeffs_big`.  It is exact
/// only when the primitive coefficients fit in `Int32`; new exact
/// algorithms use the BigInt form.
pub fn qpoly_integer_coeffs(p : QPoly) -> Array[Int32] {
  let big = qpoly_integer_coeffs_big(p)
  let out : Array[Int32] = []
  for i in 0..<big.length() {
    out.push(big[i].to_int())
  }
  out
}

///|
fn small_primes(limit : Int32) -> Array[BigInt] {
  let flags : Array[Bool] = []
  for _i in 0..<(limit + 1) {
    flags.push(true)
  }
  if limit >= 0 {
    flags[0] = false
  }
  if limit >= 1 {
    flags[1] = false
  }
  let mut p = 2
  while p * p <= limit {
    if flags[p] {
      let mut multiple = p * p
      while multiple <= limit {
        flags[multiple] = false
        multiple = multiple + p
      }
    }
    p = p + 1
  }
  let out : Array[BigInt] = []
  for i in 0..<(limit + 1) {
    if flags[i] {
      out.push(BigInt::from_int(i))
    }
  }
  out
}

///|
fn miller_rabin_round(n : BigInt, d : BigInt, s : Int32, a : BigInt) -> Bool {
  let mut x = a.pow(d, modulus=n)
  if x == 1N || x == n - 1N {
    return true
  }
  for _i in 1..<s {
    x = x * x % n
    if x == n - 1N {
      return true
    }
  }
  false
}

///|
/// Deterministic primality below the first-13-prime Miller-Rabin
/// bound `3,317,044,064,679,887,385,961,981`; above it, those rounds
/// must also be corroborated by the trial-division fallback in the
/// factorization code before an unfactored residue is reported prime.
fn bigint_miller_rabin(n : BigInt) -> Bool {
  let bases = [2N, 3N, 5N, 7N, 11N, 13N, 17N, 19N, 23N, 29N, 31N, 37N, 41N]
  for i in 0..<bases.length() {
    if n == bases[i] {
      return true
    }
    if n % bases[i] == 0N {
      return false
    }
  }
  let mut d = n - 1N
  let mut s = 0
  while d % 2N == 0N {
    d = d / 2N
    s = s + 1
  }
  for i in 0..<bases.length() {
    if !miller_rabin_round(n, d, s, bases[i] % n) {
      return false
    }
  }
  true
}

///|
fn pollard_rho_factor(n : BigInt) -> BigInt {
  if n % 2N == 0N {
    return 2N
  }
  if n % 3N == 0N {
    return 3N
  }
  for c_int in 1..<97 {
    let c = BigInt::from_int(c_int)
    let mut x = 2N + c
    let mut y = x
    let mut product = 1N
    let mut steps_since_gcd = 0
    for _step in 0..<300000 {
      x = (x * x + c) % n
      y = (y * y + c) % n
      y = (y * y + c) % n
      product = product * bigint_abs(x - y) % n
      steps_since_gcd = steps_since_gcd + 1
      if steps_since_gcd == 127 {
        let d = bigint_gcd(product, n)
        if d > 1N && d < n {
          return d
        }
        if d == n {
          break
        }
        product = 1N
        steps_since_gcd = 0
      }
    }
  }
  n
}

///|
fn trial_factor(n : BigInt) -> BigInt {
  let mut d = 2N
  while d * d <= n {
    if n % d == 0N {
      return d
    }
    d = if d == 2N { 3N } else { d + 2N }
  }
  n
}

///|
fn factor_collect(n0 : BigInt, out : Array[BigInt]) -> Unit {
  let mut n = n0
  let primes = small_primes(1009)
  for i in 0..<primes.length() {
    let p = primes[i]
    while n > 1N && n % p == 0N {
      out.push(p)
      n = n / p
    }
  }
  if n == 1N {
    return
  }
  match bigint_sqrt_exact(n) {
    Some(r) => {
      factor_collect(r, out)
      factor_collect(r, out)
      return
    }
    None => ()
  }
  let deterministic_bound = BigInt::from_string("3317044064679887385961981")
  if bigint_miller_rabin(n) && n < deterministic_bound {
    out.push(n)
    return
  }
  let d = if bigint_miller_rabin(n) {
    // Above the deterministic bound, only a completed trial proves
    // primality in this exact interface.
    trial_factor(n)
  } else {
    let candidate = pollard_rho_factor(n)
    if candidate > 1N && candidate < n {
      candidate
    } else {
      trial_factor(n)
    }
  }
  if d == n {
    out.push(n)
  } else {
    factor_collect(d, out)
    factor_collect(n / d, out)
  }
}

///|
/// Prime factorization of the absolute value, as `(prime, exponent)`
/// pairs in increasing order.  Small factors are sieved, medium
/// composites are split by Pollard rho, and trial division remains
/// the exact fallback.
pub fn bigint_prime_factorization(n0 : BigInt) -> Array[(BigInt, Int32)] {
  let factors : Array[BigInt] = []
  factor_collect(bigint_abs(n0), factors)
  // Sorting by repeated minimum extraction avoids relying on the
  // order in which recursive splitting discovered factors.
  let sorted : Array[BigInt] = []
  let used : Array[Bool] = []
  for _i in 0..<factors.length() {
    used.push(false)
  }
  for _k in 0..<factors.length() {
    let mut best = -1
    for i in 0..<factors.length() {
      if !used[i] && (best < 0 || factors[i] < factors[best]) {
        best = i
      }
    }
    used[best] = true
    sorted.push(factors[best])
  }
  let out : Array[(BigInt, Int32)] = []
  for i in 0..<sorted.length() {
    if out.length() > 0 && out[out.length() - 1].0 == sorted[i] {
      let (p, e) = out[out.length() - 1]
      out[out.length() - 1] = (p, e + 1)
    } else {
      out.push((sorted[i], 1))
    }
  }
  out
}

///|
/// All positive divisors of a nonzero BigInt, in increasing order,
/// generated from its prime factorization.
pub fn bigint_divisors(n0 : BigInt) -> Array[BigInt] {
  if n0 == 0N {
    return []
  }
  let factorization = bigint_prime_factorization(n0)
  let divisors : Array[BigInt] = [1N]
  for i in 0..<factorization.length() {
    let (p, exponent) = factorization[i]
    let base_len = divisors.length()
    let mut power = 1N
    for _e in 0..<exponent {
      power = power * p
      for j in 0..<base_len {
        divisors.push(divisors[j] * power)
      }
    }
  }
  for _pass in 0..<divisors.length() {
    for j in 0..<(divisors.length() - 1) {
      if divisors[j + 1] < divisors[j] {
        let tmp = divisors[j]
        divisors[j] = divisors[j + 1]
        divisors[j + 1] = tmp
      }
    }
  }
  divisors
}

///|
fn rat_array_contains(xs : Array[Rat], x : Rat) -> Bool {
  for i in 0..<xs.length() {
    if rat_eq(xs[i], x) {
      return true
    }
  }
  false
}

///|
/// All distinct rational roots, by the rational-root theorem.  For
/// the zero polynomial the (infinite) root set is reported as empty.
pub fn qpoly_rational_roots(p : QPoly) -> Array[Rat] {
  let out : Array[Rat] = []
  if qpoly_is_zero(p) || qpoly_degree(p) <= 0 {
    return out
  }
  let mut q = p
  // Extract the root 0 first so the remaining constant term is nonzero.
  while qpoly_degree(q) > 0 && rat_is_zero(qpoly_coeff(q, 0)) {
    q = qpoly_div_exact(q, qpoly_x())
  }
  if qpoly_degree(q) != qpoly_degree(p) {
    out.push(rat_zero())
  }
  if qpoly_degree(q) <= 0 {
    return out
  }
  let ints = qpoly_integer_coeffs_big(q)
  let ps = bigint_divisors(ints[0])
  let qs = bigint_divisors(ints[ints.length() - 1])
  for pi in 0..<ps.length() {
    for qi in 0..<qs.length() {
      for sign in 0..<2 {
        let num = if sign == 0 { ps[pi] } else { -ps[pi] }
        let cand = rat_make_big(num, qs[qi])
        if !rat_array_contains(out, cand) && rat_is_zero(qpoly_eval(q, cand)) {
          out.push(cand)
        }
      }
    }
  }
  out
}

///|
pub struct QPolyRationalFactorization {
  roots : Array[Rat]
  multiplicities : Array[Int32]
  residual : QPoly
}

///|
/// Factor out every rational root with its multiplicity; the monic
/// residual has no rational roots.
pub fn qpoly_factor_rational_roots(p : QPoly) -> QPolyRationalFactorization {
  let roots = qpoly_rational_roots(p)
  let multiplicities : Array[Int32] = []
  let mut residual = qpoly_monic(p)
  for i in 0..<roots.length() {
    let m = qpoly_root_multiplicity(p, roots[i])
    multiplicities.push(m)
    for _k in 0..<m {
      residual = qpoly_div_exact(residual, qpoly_root_factor(roots[i]))
    }
  }
  QPolyRationalFactorization::{
    roots,
    multiplicities,
    residual: qpoly_monic(residual),
  }
}

///|
/// Irreducibility over Q, decided for degrees at most 3 (where the
/// absence of a rational root is decisive).  Higher degrees report
/// `false`; use the quotient-ring normal forms of `AlgNum`, whose
/// division is partial and therefore sound for any modulus.
pub fn qpoly_irreducible_upto3(p : QPoly) -> Bool {
  let d = qpoly_degree(qpoly_monic(p))
  if d == 1 {
    true
  } else if d == 2 || d == 3 {
    qpoly_rational_roots(p).length() == 0
  } else {
    false
  }
}

///|
/// Independent check of the fast dense multiplication path against
/// schoolbook integer convolution, plus binary powering on a dense
/// binomial power.  Coefficients are deterministic pseudo-random
/// small integers, so the comparison is exact.
pub fn check_qpoly_fast_arithmetic() -> Bool {
  let a_int : Array[BigInt] = []
  let b_int : Array[BigInt] = []
  let a_rat : Array[Rat] = []
  let b_rat : Array[Rat] = []
  for i in 0..<97 {
    let av = i * 37 % 101 - 50
    let bv = i * 53 % 89 - 44
    a_int.push(BigInt::from_int(av))
    b_int.push(BigInt::from_int(bv))
    a_rat.push(rat_int(av))
    b_rat.push(rat_int(bv))
  }
  let expected = int_poly_mul_school(a_int, b_int)
  let product = qpoly_mul(qpoly_normalize(a_rat), qpoly_normalize(b_rat))
  if qpoly_degree(product) != expected.length() - 1 {
    return false
  }
  for i in 0..<expected.length() {
    if !rat_eq(qpoly_coeff(product, i), rat_big_int(expected[i])) {
      return false
    }
  }
  let power = qpoly_pow(qpoly_add(qpoly_x(), qpoly_int(1)), 37)
  qpoly_degree(power) == 37 &&
  rat_eq(qpoly_coeff(power, 0), rat_int(1)) &&
  rat_eq(qpoly_coeff(power, 1), rat_int(37)) &&
  rat_eq(qpoly_coeff(power, 37), rat_int(1))
}
