///|
// Exact symbolic algebra over Q: rationals, multivariate polynomials,
// fractions, complex symbolic scalars, symbolic matrices, univariate
// polynomials.
//
// This is the exact counterpart of the numeric complex.mbt: no eps, no
// sampling.  Multivariate polynomials have a canonical form (merged,
// zero-free, lexicographically sorted terms over Q); fractions are kept
// as numerator/denominator pairs and compared by cross-multiplication,
// so every equality decided here is a polynomial identity.  Complex
// quantities are pairs of *real* symbolic fractions (re, im), hence
// conjugation is negation of the imaginary part and hermitian
// conditions are exact symbolic equations.
//
// Variable convention: atoms are integer ids.  This file is generic;
// spectral_symbolic.mbt fixes ids for matrix entries, eigenvalues and
// cube coordinates (i, j) when it builds examples and theorems.

// ---------------------------------------------------------------------------
// Rationals
// ---------------------------------------------------------------------------

///|
/// An exact rational in lowest terms, backed by arbitrary-precision
/// integers.  The denominator is always positive; zero is `0/1`.
pub struct Rat {
  num : BigInt
  den : BigInt
} derive(Debug, Eq)

///|
pub extend Rat with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend Rat with Eq::{not_equal, equal}

///|
pub fn int_abs(x : Int32) -> Int32 {
  if x < 0 {
    0 - x
  } else {
    x
  }
}

///|
pub fn int_gcd(a0 : Int32, b0 : Int32) -> Int32 {
  let mut a = int_abs(a0)
  let mut b = int_abs(b0)
  while b != 0 {
    let r = a % b
    a = b
    b = r
  }
  if a == 0 {
    1
  } else {
    a
  }
}

///|
pub fn bigint_abs(x : BigInt) -> BigInt {
  if x < 0N {
    -x
  } else {
    x
  }
}

///|
/// Greatest common divisor of arbitrary-precision integers.  The
/// result is positive; `gcd(0,0)` is defined as 1 so rational
/// normalization is total.
pub fn bigint_gcd(a0 : BigInt, b0 : BigInt) -> BigInt {
  let mut a = bigint_abs(a0)
  let mut b = bigint_abs(b0)
  while b != 0N {
    let r = a % b
    a = b
    b = r
  }
  if a == 0N {
    1N
  } else {
    a
  }
}

///|
pub fn bigint_lcm(a : BigInt, b : BigInt) -> BigInt {
  if a == 0N || b == 0N {
    0N
  } else {
    bigint_abs(a / bigint_gcd(a, b) * b)
  }
}

///|
/// Normalize a pair of arbitrary-precision integers to a rational.
/// A zero denominator follows the legacy total convention and gives 0.
pub fn rat_make_big(n : BigInt, d : BigInt) -> Rat {
  if n == 0N || d == 0N {
    return Rat::{ num: 0N, den: 1N, }
  }
  let g = bigint_gcd(n, d)
  let nn = n / g
  let dd = d / g
  if dd < 0N {
    Rat::{ num: -nn, den: -dd, }
  } else {
    Rat::{ num: nn, den: dd, }
  }
}

///|
pub fn rat_make(n : Int32, d : Int32) -> Rat {
  rat_make_big(BigInt::from_int(n), BigInt::from_int(d))
}

///|
pub fn rat_big_int(n : BigInt) -> Rat {
  Rat::{ num: n, den: 1N, }
}

///|
pub fn rat_make_decimal_strings(n : String, d : String) -> Rat {
  rat_make_big(BigInt::from_string(n), BigInt::from_string(d))
}

///|
pub fn rat_int(n : Int32) -> Rat {
  Rat::{ num: BigInt::from_int(n), den: 1N, }
}

///|
pub fn rat_zero() -> Rat {
  rat_int(0)
}

///|
pub fn rat_one() -> Rat {
  rat_int(1)
}

///|
pub fn rat_to_string(a : Rat) -> String {
  if a.den == 1N {
    a.num.to_string()
  } else {
    a.num.to_string() + "/" + a.den.to_string()
  }
}

///|
fn bigint_scaled_mantissa(x : BigInt) -> (Double, Int32) {
  let ax = bigint_abs(x)
  if ax == 0N {
    return (0.0, 0)
  }
  let bits = ax.bit_length()
  let normalized = if bits > 53 { ax >> (bits - 53) } else { ax << (53 - bits) }
  let top = normalized.to_int64().to_double()
  let mut mantissa = top
  for _i in 0..<52 {
    mantissa = mantissa / 2.0
  }
  (mantissa, bits - 1)
}

///|
fn scale_double_pow2(x : Double, exponent : Int32) -> Double {
  let mut out = x
  if exponent >= 0 {
    let n = if exponent > 4000 { 4000 } else { exponent }
    for _i in 0..<n {
      out = out * 2.0
      if out == 1.0 / 0.0 {
        break
      }
    }
  } else {
    let n0 = 0 - exponent
    let n = if n0 > 4000 { 4000 } else { n0 }
    for _i in 0..<n {
      out = out / 2.0
      if out == 0.0 {
        break
      }
    }
  }
  out
}

///|
/// A correctly scaled floating approximation of a BigInt.  This is
/// only a display/diagnostic conversion: exact algorithms never use it.
pub fn bigint_to_double(x : BigInt) -> Double {
  let (mantissa, exponent) = bigint_scaled_mantissa(x)
  let value = scale_double_pow2(mantissa, exponent)
  if x < 0N {
    -value
  } else {
    value
  }
}

///|
/// Floating approximation of an exact rational, computed from scaled
/// leading bits so huge numerators and denominators do not first
/// overflow as separate machine integers.
pub fn rat_to_double(a : Rat) -> Double {
  if a.num == 0N {
    return 0.0
  }
  let (nm, ne) = bigint_scaled_mantissa(a.num)
  let (dm, de) = bigint_scaled_mantissa(a.den)
  let value = scale_double_pow2(nm / dm, ne - de)
  if a.num < 0N {
    -value
  } else {
    value
  }
}

///|
/// Whether both components fit in signed 32-bit integers.  This is a
/// compatibility query for legacy algorithms; the rational itself is
/// never truncated.
pub fn rat_fits_int32(a : Rat) -> Bool {
  a.num >= BigInt::from_int(-2147483647 - 1) &&
  a.num <= BigInt::from_int(2147483647) &&
  a.den <= BigInt::from_int(2147483647)
}

///|
pub fn rat_add(a : Rat, b : Rat) -> Rat {
  // Add over the lcm of denominators; with BigInt this is an
  // efficiency measure rather than an overflow-avoidance measure.
  let g = bigint_gcd(a.den, b.den)
  let ad = a.den / g
  let bd = b.den / g
  rat_make_big(a.num * bd + b.num * ad, ad * b.den)
}

///|
pub fn rat_neg(a : Rat) -> Rat {
  Rat::{ num: -a.num, den: a.den, }
}

///|
pub fn rat_sub(a : Rat, b : Rat) -> Rat {
  rat_add(a, rat_neg(b))
}

///|
pub fn rat_mul(a : Rat, b : Rat) -> Rat {
  let g1 = bigint_gcd(a.num, b.den)
  let g2 = bigint_gcd(b.num, a.den)
  rat_make_big(a.num / g1 * (b.num / g2), a.den / g2 * (b.den / g1))
}

///|
pub fn rat_is_zero(a : Rat) -> Bool {
  a.num == 0N
}

// ---------------------------------------------------------------------------
// Multivariate polynomials over Q (canonical form)
// ---------------------------------------------------------------------------

///|
pub struct PolyTerm {
  mut coeff : Rat
  exps : Array[Int32]
}

///|
pub struct Poly {
  terms : Array[PolyTerm]
}

///|
fn exps_pad(e : Array[Int32], n : Int32) -> Array[Int32] {
  let out : Array[Int32] = []
  for i in 0..<n {
    if i < e.length() {
      out.push(e[i])
    } else {
      out.push(0)
    }
  }
  out
}

///|
fn exps_eq(a : Array[Int32], b : Array[Int32]) -> Bool {
  let n = if a.length() > b.length() { a.length() } else { b.length() }
  for i in 0..<n {
    let x = if i < a.length() { a[i] } else { 0 }
    let y = if i < b.length() { b[i] } else { 0 }
    if x != y {
      return false
    }
  }
  true
}

///|
fn exps_gt(a : Array[Int32], b : Array[Int32]) -> Bool {
  let n = if a.length() > b.length() { a.length() } else { b.length() }
  for i in 0..<n {
    let x = if i < a.length() { a[i] } else { 0 }
    let y = if i < b.length() { b[i] } else { 0 }
    if x != y {
      return x > y
    }
  }
  false
}

///|
pub fn poly_normalize(raw : Array[PolyTerm]) -> Poly {
  let mut width = 0
  for t in 0..<raw.length() {
    if raw[t].exps.length() > width {
      width = raw[t].exps.length()
    }
  }
  let merged : Array[PolyTerm] = []
  for t in 0..<raw.length() {
    let term = PolyTerm::{
      coeff: raw[t].coeff,
      exps: exps_pad(raw[t].exps, width),
    }
    let mut found = false
    for k in 0..<merged.length() {
      if exps_eq(merged[k].exps, term.exps) {
        merged[k].coeff = rat_add(merged[k].coeff, term.coeff)
        found = true
      }
    }
    if !found {
      merged.push(term)
    }
  }
  let kept : Array[PolyTerm] = []
  for t in 0..<merged.length() {
    if !rat_is_zero(merged[t].coeff) {
      kept.push(merged[t])
    }
  }
  // Truncate trailing always-zero exponent columns (canonical width).
  let mut useful = 0
  for t in 0..<kept.length() {
    for i in 0..<kept[t].exps.length() {
      if kept[t].exps[i] != 0 && i + 1 > useful {
        useful = i + 1
      }
    }
  }
  let out : Array[PolyTerm] = []
  for t in 0..<kept.length() {
    out.push(PolyTerm::{
      coeff: kept[t].coeff,
      exps: exps_pad(kept[t].exps, useful),
    })
  }
  for _pass in 0..<out.length() {
    for j in 0..<(out.length() - 1) {
      if exps_gt(out[j + 1].exps, out[j].exps) {
        let tmp = out[j]
        out[j] = out[j + 1]
        out[j + 1] = tmp
      }
    }
  }
  Poly::{ terms: out, }
}

///|
pub fn poly_zero() -> Poly {
  Poly::{ terms: [], }
}

///|
pub fn poly_const(c : Rat) -> Poly {
  poly_normalize([PolyTerm::{ coeff: c, exps: [], }])
}

///|
pub fn poly_one() -> Poly {
  poly_const(rat_one())
}

///|
pub fn poly_int(n : Int32) -> Poly {
  poly_const(rat_int(n))
}

///|
pub fn poly_var(id : Int32) -> Poly {
  let e : Array[Int32] = []
  for _i in 0..<(id + 1) {
    e.push(0)
  }
  e[id] = 1
  Poly::{ terms: [PolyTerm::{ coeff: rat_one(), exps: e, }], }
}

///|
pub fn poly_is_zero(p : Poly) -> Bool {
  p.terms.length() == 0
}

///|
pub fn poly_add(a : Poly, b : Poly) -> Poly {
  let raw : Array[PolyTerm] = []
  for i in 0..<a.terms.length() {
    raw.push(a.terms[i])
  }
  for i in 0..<b.terms.length() {
    raw.push(b.terms[i])
  }
  poly_normalize(raw)
}

///|
pub fn poly_neg(a : Poly) -> Poly {
  let raw : Array[PolyTerm] = []
  for i in 0..<a.terms.length() {
    raw.push(PolyTerm::{
      coeff: rat_neg(a.terms[i].coeff),
      exps: a.terms[i].exps,
    })
  }
  Poly::{ terms: raw, }
}

///|
pub fn poly_sub(a : Poly, b : Poly) -> Poly {
  poly_add(a, poly_neg(b))
}

///|
pub fn poly_mul(a : Poly, b : Poly) -> Poly {
  let raw : Array[PolyTerm] = []
  for i in 0..<a.terms.length() {
    for j in 0..<b.terms.length() {
      let ea = a.terms[i].exps
      let eb = b.terms[j].exps
      let n = if ea.length() > eb.length() { ea.length() } else { eb.length() }
      let e : Array[Int32] = []
      for k in 0..<n {
        let x = if k < ea.length() { ea[k] } else { 0 }
        let y = if k < eb.length() { eb[k] } else { 0 }
        e.push(x + y)
      }
      raw.push(PolyTerm::{
        coeff: rat_mul(a.terms[i].coeff, b.terms[j].coeff),
        exps: e,
      })
    }
  }
  poly_normalize(raw)
}

///|
pub fn poly_scale(c : Rat, a : Poly) -> Poly {
  poly_mul(poly_const(c), a)
}

///|
pub fn poly_eq(a : Poly, b : Poly) -> Bool {
  poly_is_zero(poly_sub(a, b))
}

// ---------------------------------------------------------------------------
// Symbolic fractions of polynomials
// ---------------------------------------------------------------------------

///|
pub struct SymFrac {
  num : Poly
  den : Poly
}

///|
pub fn frac_make(num : Poly, den : Poly) -> SymFrac {
  if poly_is_zero(num) || poly_is_zero(den) {
    SymFrac::{ num: poly_zero(), den: poly_one(), }
  } else {
    SymFrac::{ num, den, }
  }
}

///|
pub fn frac_poly(p : Poly) -> SymFrac {
  frac_make(p, poly_one())
}

///|
pub fn frac_zero() -> SymFrac {
  frac_poly(poly_zero())
}

///|
pub fn frac_one() -> SymFrac {
  frac_poly(poly_one())
}

///|
pub fn frac_int(n : Int32) -> SymFrac {
  frac_poly(poly_int(n))
}

///|
pub fn frac_rat(c : Rat) -> SymFrac {
  frac_poly(poly_const(c))
}

///|
pub fn frac_var(id : Int32) -> SymFrac {
  frac_poly(poly_var(id))
}

///|
pub fn frac_neg(a : SymFrac) -> SymFrac {
  SymFrac::{ num: poly_neg(a.num), den: a.den, }
}

///|
pub fn frac_add(a : SymFrac, b : SymFrac) -> SymFrac {
  frac_make(
    poly_add(poly_mul(a.num, b.den), poly_mul(b.num, a.den)),
    poly_mul(a.den, b.den),
  )
}

///|
pub fn frac_sub(a : SymFrac, b : SymFrac) -> SymFrac {
  frac_add(a, frac_neg(b))
}

///|
pub fn frac_mul(a : SymFrac, b : SymFrac) -> SymFrac {
  frac_make(poly_mul(a.num, b.num), poly_mul(a.den, b.den))
}

///|
pub fn frac_div(a : SymFrac, b : SymFrac) -> SymFrac {
  frac_make(poly_mul(a.num, b.den), poly_mul(a.den, b.num))
}

///|
/// Exact equality of rational expressions, by cross-multiplication.
pub fn frac_eq(a : SymFrac, b : SymFrac) -> Bool {
  poly_eq(poly_mul(a.num, b.den), poly_mul(b.num, a.den))
}

///|
pub fn frac_is_zero(a : SymFrac) -> Bool {
  poly_is_zero(a.num)
}

// ---------------------------------------------------------------------------
// Complex symbolic scalars, vectors, matrices
// ---------------------------------------------------------------------------

///|
pub struct SymC {
  re : SymFrac
  im : SymFrac
}

///|
pub fn sc_make(re : SymFrac, im : SymFrac) -> SymC {
  SymC::{ re, im, }
}

///|
pub fn sc_zero() -> SymC {
  sc_make(frac_zero(), frac_zero())
}

///|
pub fn sc_one() -> SymC {
  sc_make(frac_one(), frac_zero())
}

///|
pub fn sc_int(n : Int32) -> SymC {
  sc_make(frac_int(n), frac_zero())
}

///|
pub fn sc_rat(c : Rat) -> SymC {
  sc_make(frac_rat(c), frac_zero())
}

///|
pub fn sc_real_frac(f : SymFrac) -> SymC {
  sc_make(f, frac_zero())
}

///|
pub fn sc_var(id : Int32) -> SymC {
  sc_make(frac_var(id), frac_zero())
}

///|
pub fn sc_i() -> SymC {
  sc_make(frac_zero(), frac_one())
}

///|
pub fn sc_add(a : SymC, b : SymC) -> SymC {
  sc_make(frac_add(a.re, b.re), frac_add(a.im, b.im))
}

///|
pub fn sc_neg(a : SymC) -> SymC {
  sc_make(frac_neg(a.re), frac_neg(a.im))
}

///|
pub fn sc_sub(a : SymC, b : SymC) -> SymC {
  sc_add(a, sc_neg(b))
}

///|
pub fn sc_mul(a : SymC, b : SymC) -> SymC {
  sc_make(
    frac_sub(frac_mul(a.re, b.re), frac_mul(a.im, b.im)),
    frac_add(frac_mul(a.re, b.im), frac_mul(a.im, b.re)),
  )
}

///|
pub fn sc_conj(a : SymC) -> SymC {
  sc_make(a.re, frac_neg(a.im))
}

///|
pub fn sc_scale_frac(f : SymFrac, a : SymC) -> SymC {
  sc_make(frac_mul(f, a.re), frac_mul(f, a.im))
}

///|
pub fn sc_eq(a : SymC, b : SymC) -> Bool {
  frac_eq(a.re, b.re) && frac_eq(a.im, b.im)
}

///|
pub fn sc_is_zero(a : SymC) -> Bool {
  frac_is_zero(a.re) && frac_is_zero(a.im)
}

///|
pub type SymVec = Array[SymC]

///|
pub fn sym_vec_add(a : SymVec, b : SymVec) -> SymVec {
  let out : SymVec = []
  for i in 0..<a.length() {
    out.push(sc_add(a[i], b[i]))
  }
  out
}

///|
pub fn sym_vec_sub(a : SymVec, b : SymVec) -> SymVec {
  let out : SymVec = []
  for i in 0..<a.length() {
    out.push(sc_sub(a[i], b[i]))
  }
  out
}

///|
pub fn sym_vec_scale(f : SymFrac, a : SymVec) -> SymVec {
  let out : SymVec = []
  for i in 0..<a.length() {
    out.push(sc_scale_frac(f, a[i]))
  }
  out
}

///|
pub fn sym_vec_scale_c(c : SymC, a : SymVec) -> SymVec {
  let out : SymVec = []
  for i in 0..<a.length() {
    out.push(sc_mul(c, a[i]))
  }
  out
}

///|
pub fn sym_vec_eq(a : SymVec, b : SymVec) -> Bool {
  if a.length() != b.length() {
    return false
  }
  for i in 0..<a.length() {
    if !sc_eq(a[i], b[i]) {
      return false
    }
  }
  true
}

///|
pub fn sym_inner(a : SymVec, b : SymVec) -> SymC {
  let mut acc = sc_zero()
  for i in 0..<a.length() {
    acc = sc_add(acc, sc_mul(sc_conj(a[i]), b[i]))
  }
  acc
}

///|
pub struct SymMat {
  n : Int32
  rows : Array[Array[SymC]]
}

///|
pub fn sym_mat_zero(n : Int32) -> SymMat {
  let rows : Array[Array[SymC]] = []
  for _i in 0..<n {
    let row : Array[SymC] = []
    for _j in 0..<n {
      row.push(sc_zero())
    }
    rows.push(row)
  }
  SymMat::{ n, rows, }
}

///|
pub fn sym_mat_identity(n : Int32) -> SymMat {
  let rows : Array[Array[SymC]] = []
  for i in 0..<n {
    let row : Array[SymC] = []
    for j in 0..<n {
      row.push(if i == j { sc_one() } else { sc_zero() })
    }
    rows.push(row)
  }
  SymMat::{ n, rows, }
}

///|
pub fn sym_mat_from_rows(rows : Array[Array[SymC]]) -> SymMat {
  SymMat::{ n: rows.length(), rows, }
}

///|
pub fn sym_scalar_matrix(f : SymFrac, n : Int32) -> SymMat {
  let rows : Array[Array[SymC]] = []
  for i in 0..<n {
    let row : Array[SymC] = []
    for j in 0..<n {
      row.push(if i == j { sc_real_frac(f) } else { sc_zero() })
    }
    rows.push(row)
  }
  SymMat::{ n, rows, }
}

///|
pub fn sym_mat_add(a : SymMat, b : SymMat) -> SymMat {
  let rows : Array[Array[SymC]] = []
  for i in 0..<a.n {
    rows.push(sym_vec_add(a.rows[i], b.rows[i]))
  }
  SymMat::{ n: a.n, rows, }
}

///|
pub fn sym_mat_sub(a : SymMat, b : SymMat) -> SymMat {
  let rows : Array[Array[SymC]] = []
  for i in 0..<a.n {
    rows.push(sym_vec_sub(a.rows[i], b.rows[i]))
  }
  SymMat::{ n: a.n, rows, }
}

///|
pub fn sym_mat_mul(a : SymMat, b : SymMat) -> SymMat {
  let rows : Array[Array[SymC]] = []
  for i in 0..<a.n {
    let row : Array[SymC] = []
    for j in 0..<a.n {
      let mut acc = sc_zero()
      for k in 0..<a.n {
        acc = sc_add(acc, sc_mul(a.rows[i][k], b.rows[k][j]))
      }
      row.push(acc)
    }
    rows.push(row)
  }
  SymMat::{ n: a.n, rows, }
}

///|
pub fn sym_mat_vec(m : SymMat, v : SymVec) -> SymVec {
  let out : SymVec = []
  for i in 0..<m.n {
    let mut acc = sc_zero()
    for k in 0..<m.n {
      acc = sc_add(acc, sc_mul(m.rows[i][k], v[k]))
    }
    out.push(acc)
  }
  out
}

///|
pub fn sym_mat_adjoint(m : SymMat) -> SymMat {
  let rows : Array[Array[SymC]] = []
  for i in 0..<m.n {
    let row : Array[SymC] = []
    for j in 0..<m.n {
      row.push(sc_conj(m.rows[j][i]))
    }
    rows.push(row)
  }
  SymMat::{ n: m.n, rows, }
}

///|
pub fn sym_mat_scale(f : SymFrac, m : SymMat) -> SymMat {
  let rows : Array[Array[SymC]] = []
  for i in 0..<m.n {
    rows.push(sym_vec_scale(f, m.rows[i]))
  }
  SymMat::{ n: m.n, rows, }
}

///|
pub fn sym_mat_eq(a : SymMat, b : SymMat) -> Bool {
  if a.n != b.n {
    return false
  }
  for i in 0..<a.n {
    if !sym_vec_eq(a.rows[i], b.rows[i]) {
      return false
    }
  }
  true
}

///|
pub fn sym_mat_trace(m : SymMat) -> SymC {
  let mut acc = sc_zero()
  for i in 0..<m.n {
    acc = sc_add(acc, m.rows[i][i])
  }
  acc
}

///|
pub fn sym_is_hermitian(m : SymMat) -> Bool {
  sym_mat_eq(sym_mat_adjoint(m), m)
}

///|
pub fn sym_is_idempotent(m : SymMat) -> Bool {
  sym_mat_eq(sym_mat_mul(m, m), m)
}

///|
pub fn sym_outer(v : SymVec) -> SymMat {
  let n = v.length()
  let rows : Array[Array[SymC]] = []
  for i in 0..<n {
    let row : Array[SymC] = []
    for j in 0..<n {
      row.push(sc_mul(v[i], sc_conj(v[j])))
    }
    rows.push(row)
  }
  SymMat::{ n, rows, }
}

///|
/// Rank-one orthogonal projector v·v† / (v†v), symbolically.  The inner
/// product is a real fraction (its imaginary part cancels exactly).
pub fn sym_projector_rank_one(v : SymVec) -> SymMat {
  let norm = sym_inner(v, v)
  sym_mat_scale(frac_div(frac_one(), norm.re), sym_outer(v))
}

///|
fn sym_minor(m : SymMat, skip_r : Int32, skip_c : Int32) -> SymMat {
  let rows : Array[Array[SymC]] = []
  for i in 0..<m.n {
    if i == skip_r {
      continue
    }
    let row : Array[SymC] = []
    for j in 0..<m.n {
      if j != skip_c {
        row.push(m.rows[i][j])
      }
    }
    rows.push(row)
  }
  SymMat::{ n: m.n - 1, rows, }
}

///|
pub fn sym_det(m : SymMat) -> SymC {
  if m.n == 0 {
    return sc_one()
  }
  if m.n == 1 {
    return m.rows[0][0]
  }
  let mut acc = sc_zero()
  for j in 0..<m.n {
    let term = sc_mul(m.rows[0][j], sym_det(sym_minor(m, 0, j)))
    if j % 2 == 0 {
      acc = sc_add(acc, term)
    } else {
      acc = sc_sub(acc, term)
    }
  }
  acc
}

// ---------------------------------------------------------------------------
// Univariate polynomials over SymC (for characteristic polynomials)
// ---------------------------------------------------------------------------

///|
pub struct UPoly {
  coeffs : Array[SymC] // low to high
}

///|
pub fn upoly_normalize(coeffs : Array[SymC]) -> UPoly {
  let mut last = 0
  for i in 0..<coeffs.length() {
    if !sc_is_zero(coeffs[i]) {
      last = i
    }
  }
  let out : Array[SymC] = []
  for i in 0..<(last + 1) {
    out.push(coeffs[i])
  }
  if out.length() == 0 {
    out.push(sc_zero())
  }
  UPoly::{ coeffs: out, }
}

///|
pub fn upoly_zero() -> UPoly {
  UPoly::{ coeffs: [sc_zero()], }
}

///|
pub fn upoly_const(c : SymC) -> UPoly {
  upoly_normalize([c])
}

///|
pub fn upoly_x() -> UPoly {
  UPoly::{ coeffs: [sc_zero(), sc_one()], }
}

///|
pub fn upoly_add(a : UPoly, b : UPoly) -> UPoly {
  let n = if a.coeffs.length() > b.coeffs.length() {
    a.coeffs.length()
  } else {
    b.coeffs.length()
  }
  let out : Array[SymC] = []
  for i in 0..<n {
    let x = if i < a.coeffs.length() { a.coeffs[i] } else { sc_zero() }
    let y = if i < b.coeffs.length() { b.coeffs[i] } else { sc_zero() }
    out.push(sc_add(x, y))
  }
  upoly_normalize(out)
}

///|
pub fn upoly_neg(a : UPoly) -> UPoly {
  let out : Array[SymC] = []
  for i in 0..<a.coeffs.length() {
    out.push(sc_neg(a.coeffs[i]))
  }
  UPoly::{ coeffs: out, }
}

///|
pub fn upoly_sub(a : UPoly, b : UPoly) -> UPoly {
  upoly_add(a, upoly_neg(b))
}

///|
pub fn upoly_mul(a : UPoly, b : UPoly) -> UPoly {
  let n = a.coeffs.length() + b.coeffs.length() - 1
  let out : Array[SymC] = []
  for _i in 0..<n {
    out.push(sc_zero())
  }
  for i in 0..<a.coeffs.length() {
    for j in 0..<b.coeffs.length() {
      out[i + j] = sc_add(out[i + j], sc_mul(a.coeffs[i], b.coeffs[j]))
    }
  }
  upoly_normalize(out)
}

///|
pub fn upoly_eq(a : UPoly, b : UPoly) -> Bool {
  let n = if a.coeffs.length() > b.coeffs.length() {
    a.coeffs.length()
  } else {
    b.coeffs.length()
  }
  for i in 0..<n {
    let x = if i < a.coeffs.length() { a.coeffs[i] } else { sc_zero() }
    let y = if i < b.coeffs.length() { b.coeffs[i] } else { sc_zero() }
    if !sc_eq(x, y) {
      return false
    }
  }
  true
}

///|
fn det_upoly_rows(rows : Array[Array[UPoly]]) -> UPoly {
  let n = rows.length()
  if n == 0 {
    return upoly_const(sc_one())
  }
  if n == 1 {
    return rows[0][0]
  }
  let mut acc = upoly_zero()
  for j in 0..<n {
    let minor : Array[Array[UPoly]] = []
    for i in 1..<n {
      let row : Array[UPoly] = []
      for k in 0..<n {
        if k != j {
          row.push(rows[i][k])
        }
      }
      minor.push(row)
    }
    let term = upoly_mul(rows[0][j], det_upoly_rows(minor))
    if j % 2 == 0 {
      acc = upoly_add(acc, term)
    } else {
      acc = upoly_sub(acc, term)
    }
  }
  acc
}

///|
/// The characteristic polynomial det(X·I − A), exactly.
pub fn charpoly_sym(a : SymMat) -> UPoly {
  let rows : Array[Array[UPoly]] = []
  for i in 0..<a.n {
    let row : Array[UPoly] = []
    for j in 0..<a.n {
      if i == j {
        row.push(upoly_sub(upoly_x(), upoly_const(a.rows[i][j])))
      } else {
        row.push(upoly_const(sc_neg(a.rows[i][j])))
      }
    }
    rows.push(row)
  }
  det_upoly_rows(rows)
}
