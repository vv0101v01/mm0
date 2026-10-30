///|
// Certified Hermitian Jacobi iteration by rational interval arithmetic.
//
// A point Hermitian matrix with rational complex entries is enclosed
// by a complex interval matrix.  At every step the pivot and the
// Jacobi angle are chosen from the midpoint matrix (an ordinary exact
// rational matrix), but the coefficients c, s and a/|a| of the exact
// unitary rotation are replaced by rational intervals proved to
// contain them by interval arithmetic, including outward square-root
// enclosures.  The similarity transform and the accumulated
// eigenvector transform are then evaluated over interval matrices and
// outwardly rounded to a fixed dyadic denominator.
//
// Every stored rotation is independently checkable:
//   * coefficient intervals contain the coefficients recomputed from
//     the stored before-matrix;
//   * J† J - I, evaluated in interval arithmetic, contains zero;
//   * the stored after-matrix contains J† · before · J;
//   * the stored transform-after contains transform-before · J.
// The final eigenvalue intervals are the Gershgorin discs of the
// final Hermitian interval matrix, grouped into clusters with counts.

///|
pub fn rat_cmp_exact(a : Rat, b : Rat) -> Int32 {
  let left = a.num * b.den
  let right = b.num * a.den
  if left > right {
    1
  } else if left < right {
    -1
  } else {
    0
  }
}

///|
pub fn rat_le_exact(a : Rat, b : Rat) -> Bool {
  rat_cmp_exact(a, b) <= 0
}

///|
pub fn rat_abs_exact(a : Rat) -> Rat {
  if a.num < 0N {
    rat_neg(a)
  } else {
    a
  }
}

///|
fn rat_min_exact(a : Rat, b : Rat) -> Rat {
  if rat_le_exact(a, b) {
    a
  } else {
    b
  }
}

///|
fn rat_max_exact(a : Rat, b : Rat) -> Rat {
  if rat_le_exact(a, b) {
    b
  } else {
    a
  }
}

///|
fn floor_rat_pow2_scaled(a : Rat, bits : Int32) -> BigInt {
  let shifted = if a.num >= 0N { a.num << bits } else { -a.num << bits }
  if a.num >= 0N {
    shifted / a.den
  } else {
    -((shifted + a.den - 1N) / a.den)
  }
}

///|
/// The greatest multiple of `2^-bits` not above `a`, for arbitrary
/// nonnegative `bits` and arbitrary-magnitude `a`.
pub fn rat_round_down_pow2(a : Rat, bits : Int32) -> Rat {
  let b = if bits < 0 { 0 } else { bits }
  rat_make_big(floor_rat_pow2_scaled(a, b), 1N << b)
}

///|
/// The least multiple of `2^-bits` not below `a`.
pub fn rat_round_up_pow2(a : Rat, bits : Int32) -> Rat {
  rat_neg(rat_round_down_pow2(rat_neg(a), bits))
}

///|
pub struct RatInterval {
  lo : Rat
  hi : Rat
} derive(Debug, Eq)

///|
pub extend RatInterval with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend RatInterval with Eq::{not_equal, equal}

///|
pub fn rat_interval(lo : Rat, hi : Rat) -> RatInterval {
  if rat_le_exact(lo, hi) {
    RatInterval::{ lo, hi, }
  } else {
    RatInterval::{ lo: hi, hi: lo, }
  }
}

///|
pub fn rat_interval_point(a : Rat) -> RatInterval {
  RatInterval::{ lo: a, hi: a, }
}

///|
pub fn rat_interval_contains(x : RatInterval, a : Rat) -> Bool {
  rat_le_exact(x.lo, a) && rat_le_exact(a, x.hi)
}

///|
pub fn rat_interval_subset(a : RatInterval, b : RatInterval) -> Bool {
  rat_le_exact(b.lo, a.lo) && rat_le_exact(a.hi, b.hi)
}

///|
pub fn rat_interval_hull(a : RatInterval, b : RatInterval) -> RatInterval {
  RatInterval::{ lo: rat_min_exact(a.lo, b.lo), hi: rat_max_exact(a.hi, b.hi), }
}

///|
pub fn rat_interval_midpoint(a : RatInterval) -> Rat {
  rat_div(rat_add(a.lo, a.hi), rat_int(2))
}

///|
pub fn rat_interval_width(a : RatInterval) -> Rat {
  rat_sub(a.hi, a.lo)
}

///|
pub fn rat_interval_normalize(a : RatInterval, bits : Int32) -> RatInterval {
  RatInterval::{
    lo: rat_round_down_pow2(a.lo, bits),
    hi: rat_round_up_pow2(a.hi, bits),
  }
}

///|
pub fn rat_interval_add(a : RatInterval, b : RatInterval) -> RatInterval {
  RatInterval::{ lo: rat_add(a.lo, b.lo), hi: rat_add(a.hi, b.hi), }
}

///|
pub fn rat_interval_neg(a : RatInterval) -> RatInterval {
  RatInterval::{ lo: rat_neg(a.hi), hi: rat_neg(a.lo), }
}

///|
pub fn rat_interval_sub(a : RatInterval, b : RatInterval) -> RatInterval {
  rat_interval_add(a, rat_interval_neg(b))
}

///|
pub fn rat_interval_mul(a : RatInterval, b : RatInterval) -> RatInterval {
  let p1 = rat_mul(a.lo, b.lo)
  let p2 = rat_mul(a.lo, b.hi)
  let p3 = rat_mul(a.hi, b.lo)
  let p4 = rat_mul(a.hi, b.hi)
  RatInterval::{
    lo: rat_min_exact(rat_min_exact(p1, p2), rat_min_exact(p3, p4)),
    hi: rat_max_exact(rat_max_exact(p1, p2), rat_max_exact(p3, p4)),
  }
}

///|
pub fn rat_interval_abs(a : RatInterval) -> RatInterval {
  if rat_le_exact(rat_zero(), a.lo) {
    a
  } else if rat_le_exact(a.hi, rat_zero()) {
    rat_interval_neg(a)
  } else {
    RatInterval::{
      lo: rat_zero(),
      hi: rat_max_exact(rat_abs_exact(a.lo), rat_abs_exact(a.hi)),
    }
  }
}

///|
pub fn rat_interval_recip(a : RatInterval) -> RatInterval? {
  if rat_interval_contains(a, rat_zero()) {
    None
  } else {
    Some(rat_interval(rat_inv(a.lo), rat_inv(a.hi)))
  }
}

///|
pub fn rat_interval_div(a : RatInterval, b : RatInterval) -> RatInterval? {
  match rat_interval_recip(b) {
    Some(r) => Some(rat_interval_mul(a, r))
    None => None
  }
}

///|
/// An exact rational interval around `sqrt(x)` of width at most
/// `2^-bits`, computed as a BigInt integer square root of
/// `floor(x * 4^bits)`.  There is no floating search variable, bit
/// cap, or magnitude cap.  Returns `None` for negative `x`.
pub fn rat_sqrt_interval(x : Rat, bits : Int32) -> RatInterval? {
  if rat_cmp_exact(x, rat_zero()) < 0 {
    return None
  }
  let b = if bits < 0 { 0 } else { bits }
  let (lo_rat, hi_rat) = rat_sqrt_bounds(x, b)
  if rat_eq(rat_mul(lo_rat, lo_rat), x) {
    Some(rat_interval_point(lo_rat))
  } else {
    Some(RatInterval::{ lo: lo_rat, hi: hi_rat, })
  }
}

///|
pub fn rat_interval_sqrt(a : RatInterval, bits : Int32) -> RatInterval? {
  match (rat_sqrt_interval(a.lo, bits), rat_sqrt_interval(a.hi, bits)) {
    (Some(x), Some(y)) => Some(RatInterval::{ lo: x.lo, hi: y.hi, })
    _ => None
  }
}

///|
pub struct QCpx {
  re : Rat
  im : Rat
} derive(Debug, Eq)

///|
pub extend QCpx with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend QCpx with Eq::{not_equal, equal}

///|
pub fn qcpx(re : Rat, im : Rat) -> QCpx {
  QCpx::{ re, im, }
}

///|
pub fn qcpx_real(re : Rat) -> QCpx {
  QCpx::{ re, im: rat_zero(), }
}

///|
pub fn qcpx_is_zero(a : QCpx) -> Bool {
  rat_is_zero(a.re) && rat_is_zero(a.im)
}

///|
pub struct QCpxMat {
  n : Int32
  rows : Array[Array[QCpx]]
} derive(Debug, Eq)

///|
pub extend QCpxMat with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend QCpxMat with Eq::{not_equal, equal}

///|
pub fn qcpx_mat_from_rows(rows : Array[Array[QCpx]]) -> QCpxMat {
  QCpxMat::{ n: rows.length(), rows, }
}

///|
pub fn qcpx_mat_from_qmat(a : QMat) -> QCpxMat {
  let rows : Array[Array[QCpx]] = []
  for i in 0..<a.rows.length() {
    let row : Array[QCpx] = []
    for j in 0..<a.rows[i].length() {
      row.push(qcpx_real(a.rows[i][j]))
    }
    rows.push(row)
  }
  qcpx_mat_from_rows(rows)
}

///|
pub fn qcpx_mat_is_hermitian(a : QCpxMat) -> Bool {
  if a.rows.length() != a.n {
    return false
  }
  for i in 0..<a.n {
    if a.rows[i].length() != a.n || !rat_is_zero(a.rows[i][i].im) {
      return false
    }
    for j in (i + 1)..<a.n {
      let x = a.rows[i][j]
      let y = a.rows[j][i]
      if !rat_eq(x.re, y.re) || !rat_eq(x.im, rat_neg(y.im)) {
        return false
      }
    }
  }
  true
}

///|
pub struct CInterval {
  re : RatInterval
  im : RatInterval
} derive(Debug, Eq)

///|
pub extend CInterval with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend CInterval with Eq::{not_equal, equal}

///|
pub fn cinterval(re : RatInterval, im : RatInterval) -> CInterval {
  CInterval::{ re, im, }
}

///|
pub fn cinterval_point(a : QCpx) -> CInterval {
  CInterval::{ re: rat_interval_point(a.re), im: rat_interval_point(a.im), }
}

///|
pub fn cinterval_zero() -> CInterval {
  cinterval_point(qcpx_real(rat_zero()))
}

///|
pub fn cinterval_one() -> CInterval {
  cinterval_point(qcpx_real(rat_one()))
}

///|
pub fn cinterval_conj(a : CInterval) -> CInterval {
  CInterval::{ re: a.re, im: rat_interval_neg(a.im), }
}

///|
pub fn cinterval_add(a : CInterval, b : CInterval) -> CInterval {
  CInterval::{
    re: rat_interval_add(a.re, b.re),
    im: rat_interval_add(a.im, b.im),
  }
}

///|
pub fn cinterval_neg(a : CInterval) -> CInterval {
  CInterval::{ re: rat_interval_neg(a.re), im: rat_interval_neg(a.im), }
}

///|
pub fn cinterval_sub(a : CInterval, b : CInterval) -> CInterval {
  cinterval_add(a, cinterval_neg(b))
}

///|
pub fn cinterval_mul(a : CInterval, b : CInterval) -> CInterval {
  CInterval::{
    re: rat_interval_sub(
      rat_interval_mul(a.re, b.re),
      rat_interval_mul(a.im, b.im),
    ),
    im: rat_interval_add(
      rat_interval_mul(a.re, b.im),
      rat_interval_mul(a.im, b.re),
    ),
  }
}

///|
pub fn cinterval_contains(a : CInterval, x : QCpx) -> Bool {
  rat_interval_contains(a.re, x.re) && rat_interval_contains(a.im, x.im)
}

///|
pub fn cinterval_subset(a : CInterval, b : CInterval) -> Bool {
  rat_interval_subset(a.re, b.re) && rat_interval_subset(a.im, b.im)
}

///|
pub fn cinterval_hull(a : CInterval, b : CInterval) -> CInterval {
  CInterval::{
    re: rat_interval_hull(a.re, b.re),
    im: rat_interval_hull(a.im, b.im),
  }
}

///|
pub fn cinterval_normalize(a : CInterval, bits : Int32) -> CInterval {
  CInterval::{
    re: rat_interval_normalize(a.re, bits),
    im: rat_interval_normalize(a.im, bits),
  }
}

///|
pub fn cinterval_midpoint(a : CInterval) -> QCpx {
  QCpx::{ re: rat_interval_midpoint(a.re), im: rat_interval_midpoint(a.im), }
}

///|
fn cinterval_abs_sq_upper(a : CInterval) -> Rat {
  let re = rat_interval_abs(a.re).hi
  let im = rat_interval_abs(a.im).hi
  rat_add(rat_mul(re, re), rat_mul(im, im))
}

///|
pub struct QCIntervalMat {
  n : Int32
  rows : Array[Array[CInterval]]
} derive(Debug, Eq)

///|
pub extend QCIntervalMat with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend QCIntervalMat with Eq::{not_equal, equal}

///|
pub fn qci_mat_from_rows(rows : Array[Array[CInterval]]) -> QCIntervalMat {
  QCIntervalMat::{ n: rows.length(), rows, }
}

///|
pub fn qci_mat_from_point(a : QCpxMat) -> QCIntervalMat {
  let rows : Array[Array[CInterval]] = []
  for i in 0..<a.rows.length() {
    let row : Array[CInterval] = []
    for j in 0..<a.rows[i].length() {
      row.push(cinterval_point(a.rows[i][j]))
    }
    rows.push(row)
  }
  qci_mat_from_rows(rows)
}

///|
pub fn qci_mat_identity(n : Int32) -> QCIntervalMat {
  let rows : Array[Array[CInterval]] = []
  for i in 0..<n {
    let row : Array[CInterval] = []
    for j in 0..<n {
      row.push(if i == j { cinterval_one() } else { cinterval_zero() })
    }
    rows.push(row)
  }
  qci_mat_from_rows(rows)
}

///|
pub fn qci_mat_zero(n : Int32) -> QCIntervalMat {
  let rows : Array[Array[CInterval]] = []
  for _i in 0..<n {
    let row : Array[CInterval] = []
    for _j in 0..<n {
      row.push(cinterval_zero())
    }
    rows.push(row)
  }
  qci_mat_from_rows(rows)
}

///|
pub fn qci_mat_adjoint(a : QCIntervalMat) -> QCIntervalMat {
  let rows : Array[Array[CInterval]] = []
  for i in 0..<a.n {
    let row : Array[CInterval] = []
    for j in 0..<a.n {
      row.push(cinterval_conj(a.rows[j][i]))
    }
    rows.push(row)
  }
  qci_mat_from_rows(rows)
}

///|
pub fn qci_mat_add(a : QCIntervalMat, b : QCIntervalMat) -> QCIntervalMat {
  let rows : Array[Array[CInterval]] = []
  for i in 0..<a.n {
    let row : Array[CInterval] = []
    for j in 0..<a.n {
      row.push(cinterval_add(a.rows[i][j], b.rows[i][j]))
    }
    rows.push(row)
  }
  qci_mat_from_rows(rows)
}

///|
pub fn qci_mat_sub(a : QCIntervalMat, b : QCIntervalMat) -> QCIntervalMat {
  let rows : Array[Array[CInterval]] = []
  for i in 0..<a.n {
    let row : Array[CInterval] = []
    for j in 0..<a.n {
      row.push(cinterval_sub(a.rows[i][j], b.rows[i][j]))
    }
    rows.push(row)
  }
  qci_mat_from_rows(rows)
}

///|
pub fn qci_mat_mul(a : QCIntervalMat, b : QCIntervalMat) -> QCIntervalMat {
  let rows : Array[Array[CInterval]] = []
  for i in 0..<a.n {
    let row : Array[CInterval] = []
    for j in 0..<a.n {
      let mut acc = cinterval_zero()
      for k in 0..<a.n {
        acc = cinterval_add(acc, cinterval_mul(a.rows[i][k], b.rows[k][j]))
      }
      row.push(acc)
    }
    rows.push(row)
  }
  qci_mat_from_rows(rows)
}

///|
pub fn qci_mat_normalize(a : QCIntervalMat, bits : Int32) -> QCIntervalMat {
  let rows : Array[Array[CInterval]] = []
  for i in 0..<a.n {
    let row : Array[CInterval] = []
    for j in 0..<a.n {
      row.push(cinterval_normalize(a.rows[i][j], bits))
    }
    rows.push(row)
  }
  qci_mat_from_rows(rows)
}

///|
/// Outward Hermitian symmetrization.  If both off-diagonal boxes
/// contain conjugate exact entries, replacing the pair by their hull
/// (and its conjugate) still contains those entries.
pub fn qci_mat_hermitian_hull(a : QCIntervalMat) -> QCIntervalMat {
  let out = qci_mat_zero(a.n)
  for i in 0..<a.n {
    for j in 0..<a.n {
      out.rows[i][j] = a.rows[i][j]
    }
  }
  for i in 0..<a.n {
    let d = out.rows[i][i]
    if rat_interval_contains(d.im, rat_zero()) {
      out.rows[i][i] = CInterval::{
        re: d.re,
        im: rat_interval_point(rat_zero()),
      }
    }
    for j in (i + 1)..<a.n {
      let common = cinterval_hull(
        out.rows[i][j],
        cinterval_conj(out.rows[j][i]),
      )
      out.rows[i][j] = common
      out.rows[j][i] = cinterval_conj(common)
    }
  }
  out
}

///|
pub fn qci_mat_is_hermitian(a : QCIntervalMat) -> Bool {
  for i in 0..<a.n {
    if a.rows[i][i].im.lo != rat_zero() || a.rows[i][i].im.hi != rat_zero() {
      return false
    }
    for j in (i + 1)..<a.n {
      if a.rows[j][i] != cinterval_conj(a.rows[i][j]) {
        return false
      }
    }
  }
  true
}

///|
pub fn qci_mat_contains_point(a : QCIntervalMat, x : QCpxMat) -> Bool {
  if a.n != x.n {
    return false
  }
  for i in 0..<a.n {
    for j in 0..<a.n {
      if !cinterval_contains(a.rows[i][j], x.rows[i][j]) {
        return false
      }
    }
  }
  true
}

///|
pub fn qci_mat_contains(a : QCIntervalMat, b : QCIntervalMat) -> Bool {
  if a.n != b.n {
    return false
  }
  for i in 0..<a.n {
    for j in 0..<a.n {
      if !cinterval_subset(b.rows[i][j], a.rows[i][j]) {
        return false
      }
    }
  }
  true
}

///|
pub fn qci_mat_midpoint(a : QCIntervalMat) -> QCpxMat {
  let rows : Array[Array[QCpx]] = []
  for i in 0..<a.n {
    let row : Array[QCpx] = []
    for j in 0..<a.n {
      row.push(cinterval_midpoint(a.rows[i][j]))
    }
    rows.push(row)
  }
  qcpx_mat_from_rows(rows)
}

///|
/// An exact rational upper bound on the squared off-diagonal
/// Frobenius norm of every matrix in the enclosure.
pub fn qci_off_frobenius_sq_upper(a : QCIntervalMat) -> Rat {
  let mut acc = rat_zero()
  for i in 0..<a.n {
    for j in 0..<a.n {
      if i != j {
        acc = rat_add(acc, cinterval_abs_sq_upper(a.rows[i][j]))
      }
    }
  }
  acc
}

///|
pub struct JacobiCoefficients {
  p : Int32
  q : Int32
  cosine : RatInterval
  sine : RatInterval
  phase : CInterval
  modulus : RatInterval
} derive(Debug, Eq)

///|
pub extend JacobiCoefficients with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend JacobiCoefficients with Eq::{not_equal, equal}

///|
fn jacobi_largest_pivot(a : QCpxMat) -> (Int32, Int32, Rat) {
  let mut best_p = -1
  let mut best_q = -1
  let mut best = rat_zero()
  for i in 0..<a.n {
    for j in (i + 1)..<a.n {
      let x = a.rows[i][j]
      let score = rat_add(rat_mul(x.re, x.re), rat_mul(x.im, x.im))
      if rat_cmp_exact(score, best) > 0 {
        best = score
        best_p = i
        best_q = j
      }
    }
  }
  (best_p, best_q, best)
}

///|
/// Interval enclosures of the exact complex Jacobi coefficients for
/// the displayed pivot of a point Hermitian matrix.  With
/// `u = a_pq/|a_pq|`, the unitary block is
/// `[[c, s u],[-s conj(u), c]]`.
pub fn jacobi_coefficients(
  a : QCpxMat,
  p : Int32,
  q : Int32,
  bits : Int32,
) -> JacobiCoefficients? {
  if p < 0 || q <= p || q >= a.n || !qcpx_mat_is_hermitian(a) {
    return None
  }
  let entry = a.rows[p][q]
  if qcpx_is_zero(entry) {
    return None
  }
  let mod_sq = rat_add(rat_mul(entry.re, entry.re), rat_mul(entry.im, entry.im))
  let modulus = match rat_sqrt_interval(mod_sq, bits) {
    Some(x) => rat_interval_normalize(x, bits)
    None => return None
  }
  let phase_re = match rat_interval_div(rat_interval_point(entry.re), modulus) {
    Some(x) => rat_interval_normalize(x, bits)
    None => return None
  }
  let phase_im = match rat_interval_div(rat_interval_point(entry.im), modulus) {
    Some(x) => rat_interval_normalize(x, bits)
    None => return None
  }
  let alpha = a.rows[p][p].re
  let beta = a.rows[q][q].re
  let numerator = rat_sub(beta, alpha)
  let tau = match
    rat_interval_div(
      rat_interval_point(numerator),
      rat_interval_mul(rat_interval_point(rat_int(2)), modulus),
    ) {
    Some(x) => rat_interval_normalize(x, bits)
    None => return None
  }
  let tau_sq = rat_interval_mul(tau, tau)
  let root = match
    rat_interval_sqrt(
      rat_interval_add(rat_interval_point(rat_one()), tau_sq),
      bits,
    ) {
    Some(x) => rat_interval_normalize(x, bits)
    None => return None
  }
  let denom = rat_interval_add(rat_interval_abs(tau), root)
  let sign = if rat_cmp_exact(numerator, rat_zero()) < 0 {
    rat_int(-1)
  } else {
    rat_int(1)
  }
  let t = match rat_interval_div(rat_interval_point(sign), denom) {
    Some(x) => rat_interval_normalize(x, bits)
    None => return None
  }
  let c_root = match
    rat_interval_sqrt(
      rat_interval_add(rat_interval_point(rat_one()), rat_interval_mul(t, t)),
      bits,
    ) {
    Some(x) => rat_interval_normalize(x, bits)
    None => return None
  }
  let cosine = match rat_interval_div(rat_interval_point(rat_one()), c_root) {
    Some(x) => rat_interval_normalize(x, bits)
    None => return None
  }
  let sine = rat_interval_normalize(rat_interval_mul(t, cosine), bits)
  Some(JacobiCoefficients::{
    p,
    q,
    cosine,
    sine,
    phase: CInterval::{ re: phase_re, im: phase_im, },
    modulus,
  })
}

///|
/// The interval unitary matrix for enclosed Jacobi coefficients.
pub fn jacobi_unitary_interval(
  n : Int32,
  coeffs : JacobiCoefficients,
  bits~ : Int32 = 10,
) -> QCIntervalMat {
  let precision = bits
  let out = qci_mat_identity(n)
  let c = CInterval::{ re: coeffs.cosine, im: rat_interval_point(rat_zero()), }
  let s = CInterval::{ re: coeffs.sine, im: rat_interval_point(rat_zero()), }
  out.rows[coeffs.p][coeffs.p] = c
  out.rows[coeffs.q][coeffs.q] = c
  out.rows[coeffs.p][coeffs.q] = cinterval_mul(s, coeffs.phase)
  out.rows[coeffs.q][coeffs.p] = cinterval_neg(
    cinterval_mul(s, cinterval_conj(coeffs.phase)),
  )
  // Outward dyadic rounding bounds every denominator before the
  // subsequent similarity/residual multiplications.
  qci_mat_normalize(out, precision)
}

///|
pub fn jacobi_unitary_residual_contains_zero(
  u : QCIntervalMat,
  bits : Int32,
) -> Bool {
  let residual = qci_mat_normalize(
    qci_mat_sub(qci_mat_mul(qci_mat_adjoint(u), u), qci_mat_identity(u.n)),
    bits,
  )
  for i in 0..<u.n {
    for j in 0..<u.n {
      if !cinterval_contains(residual.rows[i][j], qcpx_real(rat_zero())) {
        return false
      }
    }
  }
  true
}

///|
pub struct JacobiRotationCertificate {
  before : QCIntervalMat
  after : QCIntervalMat
  transform_before : QCIntervalMat
  transform_after : QCIntervalMat
  coeffs : JacobiCoefficients
  unitary_residual_contains_zero : Bool
  before_off_sq_upper : Rat
  after_off_sq_upper : Rat
} derive(Debug, Eq)

///|
pub extend JacobiRotationCertificate with @moonbitlang/core/debug.Debug::{
  to_repr,
}

///|
pub extend JacobiRotationCertificate with Eq::{not_equal, equal}

///|
pub struct EigenInterval {
  lo : Rat
  hi : Rat
  count : Int32
} derive(Debug, Eq)

///|
pub extend EigenInterval with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend EigenInterval with Eq::{not_equal, equal}

///|
pub struct JacobiCertificate {
  precision_bits : Int32
  initial : QCIntervalMat
  final_matrix : QCIntervalMat
  transform : QCIntervalMat
  rotations : Array[JacobiRotationCertificate]
  eigenvalues : Array[EigenInterval]
} derive(Debug, Eq)

///|
pub extend JacobiCertificate with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend JacobiCertificate with Eq::{not_equal, equal}

///|
/// Interval similarity transform with outward dyadic rounding after
/// each multiplication.  Rounding the intermediate product is essential:
/// it both preserves inclusion and keeps Int32 rational numerators in
/// the range where the next exact endpoint arithmetic is meaningful.
pub fn jacobi_similarity_interval(
  a : QCIntervalMat,
  u : QCIntervalMat,
  bits : Int32,
) -> QCIntervalMat {
  let middle = qci_mat_normalize(qci_mat_mul(a, u), bits)
  qci_mat_hermitian_hull(
    qci_mat_normalize(qci_mat_mul(qci_mat_adjoint(u), middle), bits),
  )
}

///|
fn jacobi_apply_step(
  current : QCIntervalMat,
  transform : QCIntervalMat,
  coeffs : JacobiCoefficients,
  bits : Int32,
) -> JacobiRotationCertificate {
  let u = jacobi_unitary_interval(current.n, coeffs, bits~)
  let after = jacobi_similarity_interval(current, u, bits)
  let transform_after = qci_mat_normalize(qci_mat_mul(transform, u), bits)
  JacobiRotationCertificate::{
    before: current,
    after,
    transform_before: transform,
    transform_after,
    coeffs,
    unitary_residual_contains_zero: jacobi_unitary_residual_contains_zero(
      u, bits,
    ),
    before_off_sq_upper: qci_off_frobenius_sq_upper(current),
    after_off_sq_upper: qci_off_frobenius_sq_upper(after),
  }
}

///|
fn jacobi_eigenvalue_intervals(
  a : QCIntervalMat,
  bits : Int32,
) -> Array[EigenInterval] {
  let discs : Array[EigenInterval] = []
  for i in 0..<a.n {
    let mut radius = rat_interval_point(rat_zero())
    for j in 0..<a.n {
      if i != j {
        let root = match
          rat_sqrt_interval(cinterval_abs_sq_upper(a.rows[i][j]), bits) {
          Some(x) => x
          None => rat_interval_point(rat_zero())
        }
        radius = rat_interval_add(radius, root)
      }
    }
    radius = rat_interval_normalize(radius, bits)
    discs.push(EigenInterval::{
      lo: rat_sub(a.rows[i][i].re.lo, radius.hi),
      hi: rat_add(a.rows[i][i].re.hi, radius.hi),
      count: 1,
    })
  }
  // Insertion sort by lower endpoint (the matrices here are small).
  for i in 1..<discs.length() {
    let mut j = i
    while j > 0 && rat_cmp_exact(discs[j - 1].lo, discs[j].lo) > 0 {
      let tmp = discs[j - 1]
      discs[j - 1] = discs[j]
      discs[j] = tmp
      j = j - 1
    }
  }
  let out : Array[EigenInterval] = []
  for i in 0..<discs.length() {
    if out.length() == 0 {
      out.push(discs[i])
    } else {
      let last = out[out.length() - 1]
      if rat_le_exact(discs[i].lo, last.hi) {
        out[out.length() - 1] = EigenInterval::{
          lo: last.lo,
          hi: rat_max_exact(last.hi, discs[i].hi),
          count: last.count + 1,
        }
      } else {
        out.push(discs[i])
      }
    }
  }
  out
}

///|
/// Run certified Jacobi sweeps.  `tolerance_sq` is applied to the
/// largest squared off-diagonal entry of the midpoint matrix; the
/// returned certificate is meaningful whether or not that stopping
/// threshold was reached.
pub fn jacobi_interval_eigen(
  input : QCpxMat,
  max_steps~ : Int32 = 24,
  tolerance_sq~ : Rat = rat_make(1, 1048576),
  precision_bits~ : Int32 = 10,
) -> JacobiCertificate? {
  let steps = max_steps
  let tol = tolerance_sq
  let bits = precision_bits
  if !qcpx_mat_is_hermitian(input) || steps < 0 {
    return None
  }
  let initial = qci_mat_from_point(input)
  let mut current = initial
  let mut transform = qci_mat_identity(input.n)
  let rotations : Array[JacobiRotationCertificate] = []
  for _step in 0..<steps {
    let midpoint = qci_mat_midpoint(current)
    let (p, q, score) = jacobi_largest_pivot(midpoint)
    if p < 0 || rat_le_exact(score, tol) {
      break
    }
    match jacobi_coefficients(midpoint, p, q, bits) {
      Some(coeffs) => {
        let cert = jacobi_apply_step(current, transform, coeffs, bits)
        current = cert.after
        transform = cert.transform_after
        rotations.push(cert)
      }
      None => break
    }
  }
  Some(JacobiCertificate::{
    precision_bits: bits,
    initial,
    final_matrix: current,
    transform,
    rotations,
    eigenvalues: jacobi_eigenvalue_intervals(current, bits),
  })
}

///|
fn jacobi_coefficients_contained(
  expected : JacobiCoefficients,
  candidate : JacobiCoefficients,
) -> Bool {
  candidate.p == expected.p &&
  candidate.q == expected.q &&
  rat_interval_subset(expected.cosine, candidate.cosine) &&
  rat_interval_subset(expected.sine, candidate.sine) &&
  rat_interval_subset(expected.modulus, candidate.modulus) &&
  cinterval_subset(expected.phase, candidate.phase)
}

///|
/// Independently verify the symbolic interval inclusions in one
/// Jacobi rotation and in the final Gershgorin eigenvalue discs.
pub fn jacobi_certificate_sound(
  input : QCpxMat,
  cert : JacobiCertificate,
) -> Bool {
  if !qcpx_mat_is_hermitian(input) {
    return false
  }
  if cert.initial != qci_mat_from_point(input) ||
    !qci_mat_is_hermitian(cert.final_matrix) {
    return false
  }
  let mut expected_before = cert.initial
  let mut expected_transform = qci_mat_identity(input.n)
  for i in 0..<cert.rotations.length() {
    let step = cert.rotations[i]
    if step.before != expected_before ||
      step.transform_before != expected_transform {
      return false
    }
    let midpoint = qci_mat_midpoint(step.before)
    let expected_coeffs = match
      jacobi_coefficients(
        midpoint,
        step.coeffs.p,
        step.coeffs.q,
        cert.precision_bits,
      ) {
      Some(x) => x
      None => return false
    }
    if !jacobi_coefficients_contained(expected_coeffs, step.coeffs) {
      return false
    }
    let u = jacobi_unitary_interval(
      input.n,
      step.coeffs,
      bits=cert.precision_bits,
    )
    if !step.unitary_residual_contains_zero ||
      !jacobi_unitary_residual_contains_zero(u, cert.precision_bits) {
      return false
    }
    let computed_after = jacobi_similarity_interval(
      step.before,
      u,
      cert.precision_bits,
    )
    if !qci_mat_contains(step.after, computed_after) {
      return false
    }
    let computed_transform = qci_mat_normalize(
      qci_mat_mul(step.transform_before, u),
      cert.precision_bits,
    )
    if !qci_mat_contains(step.transform_after, computed_transform) {
      return false
    }
    if step.before_off_sq_upper != qci_off_frobenius_sq_upper(step.before) ||
      step.after_off_sq_upper != qci_off_frobenius_sq_upper(step.after) {
      return false
    }
    expected_before = step.after
    expected_transform = step.transform_after
  }
  if expected_before != cert.final_matrix ||
    expected_transform != cert.transform {
    return false
  }
  let expected_eigs = jacobi_eigenvalue_intervals(
    cert.final_matrix,
    cert.precision_bits,
  )
  if expected_eigs.length() != cert.eigenvalues.length() {
    return false
  }
  let mut total = 0
  for i in 0..<expected_eigs.length() {
    if expected_eigs[i] != cert.eigenvalues[i] {
      return false
    }
    total = total + cert.eigenvalues[i].count
  }
  total == input.n
}

///|
pub fn eigen_interval_contains(e : EigenInterval, x : Rat) -> Bool {
  rat_le_exact(e.lo, x) && rat_le_exact(x, e.hi)
}

///|
pub fn check_Jacobi_interval() -> Bool {
  let sqrt2 = match rat_sqrt_interval(rat_int(2), 10) {
    Some(x) =>
      rat_le_exact(rat_mul(x.lo, x.lo), rat_int(2)) &&
      rat_le_exact(rat_int(2), rat_mul(x.hi, x.hi))
    None => false
  }
  if !sqrt2 {
    return false
  }
  let block = qcpx_mat_from_qmat(
    qmat_from_int_rows([[2, 1, 0], [1, 2, 0], [0, 0, -1]]),
  )
  let block_cert = match jacobi_interval_eigen(block) {
    Some(c) => c
    None => return false
  }
  if !jacobi_certificate_sound(block, block_cert) ||
    block_cert.eigenvalues.length() != 3 {
    return false
  }
  if !eigen_interval_contains(block_cert.eigenvalues[0], rat_int(-1)) ||
    !eigen_interval_contains(block_cert.eigenvalues[1], rat_int(1)) ||
    !eigen_interval_contains(block_cert.eigenvalues[2], rat_int(3)) {
    return false
  }
  for i in 0..<block_cert.eigenvalues.length() {
    let e = block_cert.eigenvalues[i]
    if e.count != 1 || rat_cmp_exact(rat_sub(e.hi, e.lo), rat_make(1, 8)) > 0 {
      return false
    }
  }
  // A genuinely complex Hermitian example.  Its characteristic
  // polynomial is checked only through certified disjoint discs and
  // the trace interval.
  let complex_input = qcpx_mat_from_rows([
    [qcpx_real(rat_int(2)), qcpx(rat_zero(), rat_int(1)), qcpx_real(rat_zero())],
    [
      qcpx(rat_zero(), rat_int(-1)),
      qcpx_real(rat_int(3)),
      qcpx_real(rat_int(1)),
    ],
    [qcpx_real(rat_zero()), qcpx_real(rat_int(1)), qcpx_real(rat_int(6))],
  ])
  let complex_cert = match jacobi_interval_eigen(complex_input, max_steps=30) {
    Some(c) => c
    None => return false
  }
  if !jacobi_certificate_sound(complex_input, complex_cert) ||
    complex_cert.eigenvalues.length() != 3 {
    return false
  }
  let mut trace_lo = rat_zero()
  let mut trace_hi = rat_zero()
  for i in 0..<complex_cert.eigenvalues.length() {
    let e = complex_cert.eigenvalues[i]
    trace_lo = rat_add(trace_lo, e.lo)
    trace_hi = rat_add(trace_hi, e.hi)
  }
  rat_le_exact(trace_lo, rat_int(11)) && rat_le_exact(rat_int(11), trace_hi)
}

///|
pub fn check_Jacobi_arbitrary_precision() -> Bool {
  let big = BigInt::from_string("100000000000000000000000000012345")
  let x = rat_make_big(big * big, BigInt::from_string("100000000000000000000"))
  let sqrt_ok = match rat_sqrt_interval(x, 100) {
    Some(iv) =>
      rat_cmp_exact(rat_mul(iv.lo, iv.lo), x) <= 0 &&
      rat_cmp_exact(x, rat_mul(iv.hi, iv.hi)) <= 0 &&
      rat_cmp_exact(rat_interval_width(iv), rat_pow2_neg(99)) <= 0
    None => false
  }
  let rounded = rat_round_down_pow2(
    rat_make_big(-big, BigInt::from_string("9876543210987654321")),
    100,
  )
  let original = rat_make_big(-big, BigInt::from_string("9876543210987654321"))
  sqrt_ok &&
  rat_cmp_exact(rounded, original) <= 0 &&
  rat_cmp_exact(rat_sub(original, rounded), rat_pow2_neg(99)) <= 0
}

// ---------------------------------------------------------------------------
// Phase 12: cluster-aware interval Jacobi iteration.
//
// The plain iteration stops on a global off-diagonal tolerance,
// which can leave overlapping Gershgorin discs merged into one
// wide cluster, and its fixed rounding precision can make disc
// radii stagnate before a tight cluster separates.  The
// cluster-aware variant drives the iteration itself by the
// cluster structure of the current discs: while a
// multi-eigenvalue cluster wider than `target_width` remains,
// rotations are chosen among index pairs inside such a cluster
// (even after the global tolerance is met); if a precision
// level stagnates, the run restarts from the initial matrix at
// doubled rounding precision, keeping the certificate with the
// best cluster penalty (fewest multi-clusters, then narrowest
// widest multi-cluster, then narrowest total width).  The
// returned certificate is an ordinary `JacobiCertificate` and
// is checked by `jacobi_certificate_sound`; exact
// characteristic-polynomial separation (`jacobi_separate_clusters`)
// remains available and now typically receives singleton
// clusters from this iteration.
// ---------------------------------------------------------------------------

///|
pub struct JacobiClusterAwareReport {
  certificate : JacobiCertificate
  precision_bits_used : Int32
  restarts : Int32
  separated : Bool
  max_cluster_width : Rat
} derive(Debug, Eq)

///|
pub extend JacobiClusterAwareReport with @moonbitlang/core/debug.Debug::{
  to_repr,
}

///|
pub extend JacobiClusterAwareReport with Eq::{not_equal, equal}

///|
/// Per-row Gershgorin discs, the cluster index of each row, and
/// the merged clusters.
fn jacobi_discs_and_clusters(
  a : QCIntervalMat,
  bits : Int32,
) -> (Array[EigenInterval], Array[Int32], Array[EigenInterval]) {
  let discs : Array[EigenInterval] = []
  for i in 0..<a.n {
    let mut radius = rat_interval_point(rat_zero())
    for j in 0..<a.n {
      if i != j {
        let root = match
          rat_sqrt_interval(cinterval_abs_sq_upper(a.rows[i][j]), bits) {
          Some(x) => x
          None => rat_interval_point(rat_zero())
        }
        radius = rat_interval_add(radius, root)
      }
    }
    radius = rat_interval_normalize(radius, bits)
    discs.push(EigenInterval::{
      lo: rat_sub(a.rows[i][i].re.lo, radius.hi),
      hi: rat_add(a.rows[i][i].re.hi, radius.hi),
      count: 1,
    })
  }
  let order : Array[Int32] = []
  for i in 0..<a.n {
    order.push(i)
  }
  for i in 1..<order.length() {
    let mut j = i
    while j > 0 && rat_cmp_exact(discs[order[j - 1]].lo, discs[order[j]].lo) > 0 {
      let tmp = order[j - 1]
      order[j - 1] = order[j]
      order[j] = tmp
      j = j - 1
    }
  }
  let cluster_of : Array[Int32] = []
  for _i in 0..<a.n {
    cluster_of.push(0)
  }
  let clusters : Array[EigenInterval] = []
  for oi in 0..<order.length() {
    let idx = order[oi]
    if clusters.length() == 0 {
      clusters.push(discs[idx])
      cluster_of[idx] = 0
    } else {
      let last = clusters[clusters.length() - 1]
      if rat_le_exact(discs[idx].lo, last.hi) {
        clusters[clusters.length() - 1] = EigenInterval::{
          lo: last.lo,
          hi: rat_max_exact(last.hi, discs[idx].hi),
          count: last.count + 1,
        }
        cluster_of[idx] = clusters.length() - 1
      } else {
        clusters.push(discs[idx])
        cluster_of[idx] = clusters.length() - 1
      }
    }
  }
  (discs, cluster_of, clusters)
}

///|
fn jacobi_cluster_penalty(clusters : Array[EigenInterval]) -> (Int32, Rat, Rat) {
  let mut multi = 0
  let mut max_multi_width = rat_zero()
  let mut total_width = rat_zero()
  for i in 0..<clusters.length() {
    let width = rat_sub(clusters[i].hi, clusters[i].lo)
    total_width = rat_add(total_width, width)
    if clusters[i].count > 1 {
      multi = multi + 1
      if rat_cmp_exact(width, max_multi_width) > 0 {
        max_multi_width = width
      }
    }
  }
  (multi, max_multi_width, total_width)
}

///|
fn jacobi_penalty_better(a : (Int32, Rat, Rat), b : (Int32, Rat, Rat)) -> Bool {
  if a.0 != b.0 {
    return a.0 < b.0
  }
  if rat_cmp_exact(a.1, b.1) != 0 {
    return rat_cmp_exact(a.1, b.1) < 0
  }
  rat_cmp_exact(a.2, b.2) < 0
}

///|
fn jacobi_run_cluster_aware(
  input : QCpxMat,
  bits : Int32,
  max_steps : Int32,
  tol : Rat,
  target_width : Rat,
) -> JacobiCertificate {
  let initial = qci_mat_from_point(input)
  let mut current = initial
  let mut transform = qci_mat_identity(input.n)
  let rotations : Array[JacobiRotationCertificate] = []
  for _step in 0..<max_steps {
    let (_, cluster_of, clusters) = jacobi_discs_and_clusters(current, bits)
    let mut needs_work = false
    for i in 0..<clusters.length() {
      if clusters[i].count > 1 &&
        rat_cmp_exact(rat_sub(clusters[i].hi, clusters[i].lo), target_width) > 0 {
        needs_work = true
      }
    }
    let midpoint = qci_mat_midpoint(current)
    let (gp, gq, gscore) = jacobi_largest_pivot(midpoint)
    if !needs_work && (gp < 0 || rat_le_exact(gscore, tol)) {
      break
    }
    let mut p = gp
    let mut q = gq
    let mut score = gscore
    if needs_work {
      let mut best = rat_zero()
      let mut best_p = -1
      let mut best_q = -1
      for i in 0..<input.n {
        for j in (i + 1)..<input.n {
          let cl = clusters[cluster_of[i]]
          if cluster_of[i] == cluster_of[j] &&
            cl.count > 1 &&
            rat_cmp_exact(rat_sub(cl.hi, cl.lo), target_width) > 0 {
            let x = midpoint.rows[i][j]
            let s = rat_add(rat_mul(x.re, x.re), rat_mul(x.im, x.im))
            if rat_cmp_exact(s, best) > 0 {
              best = s
              best_p = i
              best_q = j
            }
          }
        }
      }
      if best_p >= 0 {
        p = best_p
        q = best_q
        score = best
      }
    }
    if p < 0 || rat_is_zero(score) {
      break
    }
    match jacobi_coefficients(midpoint, p, q, bits) {
      Some(coeffs) => {
        let cert = jacobi_apply_step(current, transform, coeffs, bits)
        current = cert.after
        transform = cert.transform_after
        rotations.push(cert)
      }
      None => break
    }
  }
  JacobiCertificate::{
    precision_bits: bits,
    initial,
    final_matrix: current,
    transform,
    rotations,
    eigenvalues: jacobi_eigenvalue_intervals(current, bits),
  }
}

///|
/// Cluster-aware certified Jacobi iteration (see the section
/// doc).  Escalates rounding precision from `initial_bits` by
/// doubling up to `max_bits` while the best certificate still
/// has a multi-eigenvalue cluster wider than `target_width`.
pub fn jacobi_interval_eigen_cluster_aware(
  input : QCpxMat,
  target_width~ : Rat = rat_make(1, 64),
  max_steps~ : Int32 = 48,
  tolerance_sq~ : Rat = rat_make(1, 1048576),
  initial_bits~ : Int32 = 10,
  max_bits~ : Int32 = 40,
) -> JacobiClusterAwareReport? {
  if !qcpx_mat_is_hermitian(input) || max_steps < 0 || initial_bits <= 0 {
    return None
  }
  let mut bits = initial_bits
  let mut restarts = 0
  let mut best : JacobiCertificate? = None
  let mut best_bits = bits
  let mut best_penalty = (input.n + 1, rat_zero(), rat_zero())
  let mut first = true
  while first || bits <= max_bits {
    first = false
    let cert = jacobi_run_cluster_aware(
      input, bits, max_steps, tolerance_sq, target_width,
    )
    let penalty = jacobi_cluster_penalty(cert.eigenvalues)
    if best == None || jacobi_penalty_better(penalty, best_penalty) {
      best = Some(cert)
      best_bits = bits
      best_penalty = penalty
    }
    if penalty.0 == 0 || rat_le_exact(penalty.1, target_width) {
      break
    }
    bits = bits * 2
    if bits <= max_bits {
      restarts = restarts + 1
    }
  }
  let cert = match best {
    Some(v) => v
    None => return None
  }
  let mut max_width = rat_zero()
  for i in 0..<cert.eigenvalues.length() {
    let width = rat_sub(cert.eigenvalues[i].hi, cert.eigenvalues[i].lo)
    if rat_cmp_exact(width, max_width) > 0 {
      max_width = width
    }
  }
  Some(JacobiClusterAwareReport::{
    certificate: cert,
    precision_bits_used: best_bits,
    restarts,
    separated: best_penalty.0 == 0,
    max_cluster_width: max_width,
  })
}

///|
pub fn check_jacobi_cluster_aware_iteration() -> Bool {
  // Eigenvalues of [[2, 1/8], [1/8, 2 + 1/64]] differ by about
  // 0.252.  With the loose stopping tolerance 1/16 the plain
  // iteration stops before any rotation (the pivot score
  // 1/64 meets the tolerance) and reports one merged cluster.
  let input = qcpx_mat_from_rows([
    [qcpx_real(rat_int(2)), qcpx_real(rat_make(1, 8))],
    [qcpx_real(rat_make(1, 8)), qcpx_real(rat_make(129, 64))],
  ])
  let plain = match jacobi_interval_eigen(input, tolerance_sq=rat_make(1, 16)) {
    Some(c) => c
    None => return false
  }
  let mut plain_multi = false
  for i in 0..<plain.eigenvalues.length() {
    if plain.eigenvalues[i].count > 1 {
      plain_multi = true
    }
  }
  if !plain_multi || plain.rotations.length() != 0 {
    return false
  }
  // The cluster-aware iteration keeps rotating inside the wide
  // cluster and separates it into singletons.
  let report = match
    jacobi_interval_eigen_cluster_aware(
      input,
      target_width=rat_make(1, 16),
      tolerance_sq=rat_make(1, 16),
    ) {
    Some(r) => r
    None => return false
  }
  if !report.separated ||
    report.certificate.eigenvalues.length() != 2 ||
    report.certificate.rotations.length() == 0 ||
    !jacobi_certificate_sound(input, report.certificate) {
    return false
  }
  for i in 0..<2 {
    let e = report.certificate.eigenvalues[i]
    if e.count != 1 || rat_cmp_exact(rat_sub(e.hi, e.lo), rat_make(1, 16)) > 0 {
      return false
    }
  }
  let e0 = report.certificate.eigenvalues[0]
  let e1 = report.certificate.eigenvalues[1]
  if rat_cmp_exact(e0.hi, e1.lo) >= 0 {
    return false
  }
  // Exact post-separation agrees: each singleton cluster
  // receives exactly one eigenvalue of multiplicity one.
  let separation = match
    jacobi_separate_clusters(input, report.certificate, 24) {
    Some(s) => s
    None => return false
  }
  separation.complete &&
  separation.intervals.length() == 2 &&
  jacobi_cluster_separation_certified(input, report.certificate, separation)
}
