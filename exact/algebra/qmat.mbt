///|
// Exact rational matrices and linear algebra.
//
// This is the Q-linear-algebra layer beneath generalized
// eigenspaces and Jordan form: Gaussian elimination, rank,
// nullspaces, determinants, characteristic polynomials by Newton
// identities, and minimal polynomials by Krylov annihilators.  All
// operations are exact rational operations.

///|
pub type QVec = Array[Rat]

///|
pub struct QMat {
  n : Int32
  rows : Array[Array[Rat]]
} derive(Debug, Eq)

///|
pub extend QMat with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend QMat with Eq::{not_equal, equal}

///|
pub fn qmat_zero(n : Int32) -> QMat {
  let rows : Array[Array[Rat]] = []
  for _i in 0..<n {
    let row : Array[Rat] = []
    for _j in 0..<n {
      row.push(rat_zero())
    }
    rows.push(row)
  }
  QMat::{ n, rows, }
}

///|
pub fn qmat_identity(n : Int32) -> QMat {
  let rows : Array[Array[Rat]] = []
  for i in 0..<n {
    let row : Array[Rat] = []
    for j in 0..<n {
      row.push(if i == j { rat_one() } else { rat_zero() })
    }
    rows.push(row)
  }
  QMat::{ n, rows, }
}

///|
pub fn qmat_from_rows(rows : Array[Array[Rat]]) -> QMat {
  QMat::{ n: rows.length(), rows, }
}

///|
pub fn qmat_from_int_rows(input : Array[Array[Int32]]) -> QMat {
  let rows : Array[Array[Rat]] = []
  for i in 0..<input.length() {
    let row : Array[Rat] = []
    for j in 0..<input[i].length() {
      row.push(rat_int(input[i][j]))
    }
    rows.push(row)
  }
  qmat_from_rows(rows)
}

///|
pub fn qmat_from_columns(cols : Array[QVec]) -> QMat {
  if cols.length() == 0 {
    return qmat_zero(0)
  }
  let n = cols[0].length()
  let rows : Array[Array[Rat]] = []
  for i in 0..<n {
    let row : Array[Rat] = []
    for j in 0..<cols.length() {
      row.push(cols[j][i])
    }
    rows.push(row)
  }
  // Jordan bases are square; for a nonsquare column list the stored
  // row count is authoritative through `rows`, while `n` records the
  // ambient dimension.
  QMat::{ n, rows, }
}

///|
pub fn qmat_scalar(c : Rat, n : Int32) -> QMat {
  let rows : Array[Array[Rat]] = []
  for i in 0..<n {
    let row : Array[Rat] = []
    for j in 0..<n {
      row.push(if i == j { c } else { rat_zero() })
    }
    rows.push(row)
  }
  QMat::{ n, rows, }
}

///|
pub fn qvec_zero(n : Int32) -> QVec {
  let out : QVec = []
  for _i in 0..<n {
    out.push(rat_zero())
  }
  out
}

///|
pub fn qvec_is_zero(v : QVec) -> Bool {
  for i in 0..<v.length() {
    if !rat_is_zero(v[i]) {
      return false
    }
  }
  true
}

///|
pub fn qvec_add(a : QVec, b : QVec) -> QVec {
  let out : QVec = []
  for i in 0..<a.length() {
    out.push(rat_add(a[i], b[i]))
  }
  out
}

///|
pub fn qvec_sub(a : QVec, b : QVec) -> QVec {
  let out : QVec = []
  for i in 0..<a.length() {
    out.push(rat_sub(a[i], b[i]))
  }
  out
}

///|
pub fn qvec_scale(c : Rat, a : QVec) -> QVec {
  let out : QVec = []
  for i in 0..<a.length() {
    out.push(rat_mul(c, a[i]))
  }
  out
}

///|
pub fn qvec_eq(a : QVec, b : QVec) -> Bool {
  if a.length() != b.length() {
    return false
  }
  for i in 0..<a.length() {
    if !rat_eq(a[i], b[i]) {
      return false
    }
  }
  true
}

///|
pub fn qmat_add(a : QMat, b : QMat) -> QMat {
  let rows : Array[Array[Rat]] = []
  for i in 0..<a.rows.length() {
    rows.push(qvec_add(a.rows[i], b.rows[i]))
  }
  QMat::{ n: a.n, rows, }
}

///|
pub fn qmat_sub(a : QMat, b : QMat) -> QMat {
  let rows : Array[Array[Rat]] = []
  for i in 0..<a.rows.length() {
    rows.push(qvec_sub(a.rows[i], b.rows[i]))
  }
  QMat::{ n: a.n, rows, }
}

///|
pub fn qmat_scale(c : Rat, a : QMat) -> QMat {
  let rows : Array[Array[Rat]] = []
  for i in 0..<a.rows.length() {
    rows.push(qvec_scale(c, a.rows[i]))
  }
  QMat::{ n: a.n, rows, }
}

///|
pub fn qmat_mul(a : QMat, b : QMat) -> QMat {
  let rows : Array[Array[Rat]] = []
  let inner = b.rows.length()
  let cols = if inner == 0 { 0 } else { b.rows[0].length() }
  for i in 0..<a.rows.length() {
    let row : Array[Rat] = []
    for j in 0..<cols {
      let mut acc = rat_zero()
      for k in 0..<inner {
        acc = rat_add(acc, rat_mul(a.rows[i][k], b.rows[k][j]))
      }
      row.push(acc)
    }
    rows.push(row)
  }
  QMat::{ n: a.n, rows, }
}

///|
pub fn qmat_vec(a : QMat, v : QVec) -> QVec {
  let out : QVec = []
  for i in 0..<a.rows.length() {
    let mut acc = rat_zero()
    for k in 0..<v.length() {
      acc = rat_add(acc, rat_mul(a.rows[i][k], v[k]))
    }
    out.push(acc)
  }
  out
}

///|
pub fn qmat_transpose(a : QMat) -> QMat {
  let cols = if a.rows.length() == 0 { 0 } else { a.rows[0].length() }
  let rows : Array[Array[Rat]] = []
  for j in 0..<cols {
    let row : Array[Rat] = []
    for i in 0..<a.rows.length() {
      row.push(a.rows[i][j])
    }
    rows.push(row)
  }
  QMat::{ n: a.n, rows, }
}

///|
pub fn qmat_eq(a : QMat, b : QMat) -> Bool {
  if a.rows.length() != b.rows.length() {
    return false
  }
  for i in 0..<a.rows.length() {
    if !qvec_eq(a.rows[i], b.rows[i]) {
      return false
    }
  }
  true
}

///|
pub fn qmat_trace(a : QMat) -> Rat {
  let mut acc = rat_zero()
  for i in 0..<a.n {
    acc = rat_add(acc, a.rows[i][i])
  }
  acc
}

///|
pub fn qmat_pow(a : QMat, k : Int32) -> QMat {
  let mut acc = qmat_identity(a.n)
  for _i in 0..<k {
    acc = qmat_mul(acc, a)
  }
  acc
}

///|
pub fn qmat_poly_eval(p : QPoly, a : QMat) -> QMat {
  let mut result = qmat_zero(a.n)
  let mut power = qmat_identity(a.n)
  for i in 0..<p.coeffs.length() {
    result = qmat_add(result, qmat_scale(p.coeffs[i], power))
    power = qmat_mul(power, a)
  }
  result
}

///|
pub fn qmat_is_zero(a : QMat) -> Bool {
  qmat_eq(a, qmat_zero(a.n))
}

///|
/// Convert a rational matrix to the symbolic complex matrix format.
pub fn sym_mat_of_qmat(a : QMat) -> SymMat {
  let rows : Array[Array[SymC]] = []
  for i in 0..<a.rows.length() {
    let row : Array[SymC] = []
    for j in 0..<a.rows[i].length() {
      row.push(sc_rat(a.rows[i][j]))
    }
    rows.push(row)
  }
  sym_mat_from_rows(rows)
}

// ---------------------------------------------------------------------------
// Row reduction
// ---------------------------------------------------------------------------

///|
fn qrows_copy(rows : Array[Array[Rat]]) -> Array[Array[Rat]] {
  let out : Array[Array[Rat]] = []
  for i in 0..<rows.length() {
    let row : Array[Rat] = []
    for j in 0..<rows[i].length() {
      row.push(rows[i][j])
    }
    out.push(row)
  }
  out
}

///|
pub struct QRref {
  rows : Array[Array[Rat]]
  pivots : Array[Int32]
  rank : Int32
}

///|
/// Reduced row echelon form of a rational row system.
pub fn qrows_rref(input : Array[Array[Rat]], ncols : Int32) -> QRref {
  let rows = qrows_copy(input)
  let pivots : Array[Int32] = []
  let mut r = 0
  for c in 0..<ncols {
    if r >= rows.length() {
      break
    }
    let mut pivot = -1
    for i in r..<rows.length() {
      if !rat_is_zero(rows[i][c]) {
        pivot = i
        break
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
    let pv = rows[r][c]
    for j in 0..<ncols {
      rows[r][j] = rat_div(rows[r][j], pv)
    }
    for i in 0..<rows.length() {
      if i != r && !rat_is_zero(rows[i][c]) {
        let factor = rows[i][c]
        for j in 0..<ncols {
          rows[i][j] = rat_sub(rows[i][j], rat_mul(factor, rows[r][j]))
        }
      }
    }
    pivots.push(c)
    r = r + 1
  }
  QRref::{ rows, pivots, rank: pivots.length(), }
}

///|
pub fn qrows_rank(rows : Array[Array[Rat]], ncols : Int32) -> Int32 {
  qrows_rref(rows, ncols).rank
}

///|
pub fn qmat_rank(a : QMat) -> Int32 {
  let cols = if a.rows.length() == 0 { 0 } else { a.rows[0].length() }
  qrows_rank(a.rows, cols)
}

///|
pub fn qvec_rank(vecs : Array[QVec]) -> Int32 {
  if vecs.length() == 0 {
    0
  } else {
    qrows_rank(vecs, vecs[0].length())
  }
}

///|
pub fn qvec_in_span(vecs : Array[QVec], v : QVec) -> Bool {
  if qvec_is_zero(v) {
    return true
  }
  let with_v : Array[QVec] = []
  for i in 0..<vecs.length() {
    with_v.push(vecs[i])
  }
  with_v.push(v)
  qvec_rank(vecs) == qvec_rank(with_v)
}

///|
pub fn qvec_independent_subset(vecs : Array[QVec]) -> Array[QVec] {
  let out : Array[QVec] = []
  for i in 0..<vecs.length() {
    if !qvec_in_span(out, vecs[i]) {
      out.push(vecs[i])
    }
  }
  out
}

///|
/// A basis of `{x | rows · x = 0}`.
pub fn qrows_nullspace(rows : Array[Array[Rat]], ncols : Int32) -> Array[QVec] {
  let rr = qrows_rref(rows, ncols)
  let is_pivot : Array[Bool] = []
  for _i in 0..<ncols {
    is_pivot.push(false)
  }
  for i in 0..<rr.pivots.length() {
    is_pivot[rr.pivots[i]] = true
  }
  let out : Array[QVec] = []
  for f in 0..<ncols {
    if !is_pivot[f] {
      let v = qvec_zero(ncols)
      v[f] = rat_one()
      for i in 0..<rr.pivots.length() {
        v[rr.pivots[i]] = rat_neg(rr.rows[i][f])
      }
      out.push(v)
    }
  }
  out
}

///|
pub fn qmat_nullspace(a : QMat) -> Array[QVec] {
  let cols = if a.rows.length() == 0 { a.n } else { a.rows[0].length() }
  qrows_nullspace(a.rows, cols)
}

///|
pub fn qmat_nullity(a : QMat) -> Int32 {
  qmat_nullspace(a).length()
}

///|
/// Determinant by exact Gaussian elimination.
pub fn qmat_det(a : QMat) -> Rat {
  let n = a.n
  let rows = qrows_copy(a.rows)
  let mut det_sign = 1
  let mut det = rat_one()
  for c in 0..<n {
    let mut pivot = -1
    for i in c..<n {
      if !rat_is_zero(rows[i][c]) {
        pivot = i
        break
      }
    }
    if pivot < 0 {
      return rat_zero()
    }
    if pivot != c {
      let tmp = rows[c]
      rows[c] = rows[pivot]
      rows[pivot] = tmp
      det_sign = 0 - det_sign
    }
    let pv = rows[c][c]
    det = rat_mul(det, pv)
    for i in (c + 1)..<n {
      if !rat_is_zero(rows[i][c]) {
        let factor = rat_div(rows[i][c], pv)
        for j in c..<n {
          rows[i][j] = rat_sub(rows[i][j], rat_mul(factor, rows[c][j]))
        }
      }
    }
  }
  rat_mul(rat_int(det_sign), det)
}

// ---------------------------------------------------------------------------
// Characteristic and minimal polynomials
// ---------------------------------------------------------------------------

///|
/// Characteristic polynomial `det(XI − A)` by Newton's identities
/// from the power traces `tr(A^k)`.
pub fn qmat_charpoly(a : QMat) -> QPoly {
  let n = a.n
  // e[k] = k-th elementary symmetric function of the eigenvalues.
  let e : Array[Rat] = [rat_one()]
  let traces : Array[Rat] = [rat_zero()]
  let mut power = qmat_identity(n)
  for _k in 1..<(n + 1) {
    power = qmat_mul(power, a)
    traces.push(qmat_trace(power))
  }
  for k in 1..<(n + 1) {
    let mut acc = rat_zero()
    for i in 1..<(k + 1) {
      let term = rat_mul(e[k - i], traces[i])
      acc = if i % 2 == 1 { rat_add(acc, term) } else { rat_sub(acc, term) }
    }
    e.push(rat_div(acc, rat_int(k)))
  }
  let coeffs : Array[Rat] = []
  for k in 0..<(n + 1) {
    // Coefficient of X^k is (-1)^(n-k) e[n-k].
    let idx = n - k
    coeffs.push(if idx % 2 == 0 { e[idx] } else { rat_neg(e[idx]) })
  }
  qpoly_normalize(coeffs)
}

///|
/// The monic annihilator of one vector: the least-degree polynomial
/// `p` with `p(A)·v = 0`, from the first Krylov dependency.
pub fn qmat_vector_annihilator(a : QMat, v : QVec) -> QPoly {
  let krylov : Array[QVec] = []
  let mut current = v
  for k in 0..<(a.n + 1) {
    krylov.push(current)
    // Columns krylov[0..k]; look for a dependency.
    let cols : Array[Array[Rat]] = []
    for i in 0..<a.n {
      let row : Array[Rat] = []
      for j in 0..<krylov.length() {
        row.push(krylov[j][i])
      }
      cols.push(row)
    }
    let deps = qrows_nullspace(cols, krylov.length())
    if deps.length() > 0 {
      let dep = deps[0]
      if !rat_is_zero(dep[k]) {
        let lc = dep[k]
        let coeffs : Array[Rat] = []
        for j in 0..<dep.length() {
          coeffs.push(rat_div(dep[j], lc))
        }
        return qpoly_normalize(coeffs)
      }
    }
    current = qmat_vec(a, current)
  }
  qpoly_one()
}

///|
fn qpoly_lcm(a : QPoly, b : QPoly) -> QPoly {
  if qpoly_is_zero(a) || qpoly_is_zero(b) {
    return qpoly_zero()
  }
  qpoly_monic(qpoly_div_exact(qpoly_mul(a, b), qpoly_gcd(a, b)))
}

///|
/// The minimal polynomial of a rational matrix: the lcm of the
/// annihilators of the standard basis vectors.
pub fn qmat_minimal_polynomial(a : QMat) -> QPoly {
  let mut acc = qpoly_one()
  for i in 0..<a.n {
    let e = qvec_zero(a.n)
    e[i] = rat_one()
    acc = qpoly_lcm(acc, qmat_vector_annihilator(a, e))
  }
  acc
}

///|
/// The inverse of a rational matrix, by Gauss–Jordan elimination on
/// the augmented system `[A | I]`.
pub fn qmat_inverse(a : QMat) -> QMat? {
  let n = a.n
  let augmented : Array[Array[Rat]] = []
  for i in 0..<n {
    let row : Array[Rat] = []
    for j in 0..<n {
      row.push(a.rows[i][j])
    }
    for j in 0..<n {
      row.push(if i == j { rat_one() } else { rat_zero() })
    }
    augmented.push(row)
  }
  let rr = qrows_rref(augmented, 2 * n)
  if rr.rank != n {
    return None
  }
  for i in 0..<n {
    if rr.pivots[i] != i {
      return None
    }
  }
  let rows : Array[Array[Rat]] = []
  for i in 0..<n {
    let row : Array[Rat] = []
    for j in 0..<n {
      row.push(rr.rows[i][n + j])
    }
    rows.push(row)
  }
  Some(QMat::{ n, rows, })
}
