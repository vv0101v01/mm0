///|
// Complex numbers, vectors and square matrices over C.
//
// This file is the linear-algebra substrate.  Everything else in the
// project (eigenspace Kan filling, pruning by a projector, orthogonal
// decomposition) is built on these executable predicates:
//   * hermitian    : P† = P        (adjoint is conjugate transpose)
//   * idempotent   : P · P = P
// A matrix satisfying both is exactly an orthogonal projector.

///|
pub struct Complex {
  re : Double
  im : Double
} derive(Debug, Eq)

///|
pub extend Complex with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend Complex with Eq::{not_equal, equal}

///|
pub fn cx(re : Double, im : Double) -> Complex {
  Complex::{ re, im, }
}

///|
pub fn cx_real(x : Double) -> Complex {
  Complex::{ re: x, im: 0.0, }
}

///|
pub fn cx_zero() -> Complex {
  Complex::{ re: 0.0, im: 0.0, }
}

///|
pub fn cx_add(a : Complex, b : Complex) -> Complex {
  Complex::{ re: a.re + b.re, im: a.im + b.im, }
}

///|
pub fn cx_sub(a : Complex, b : Complex) -> Complex {
  Complex::{ re: a.re - b.re, im: a.im - b.im, }
}

///|
pub fn cx_mul(a : Complex, b : Complex) -> Complex {
  Complex::{ re: a.re * b.re - a.im * b.im, im: a.re * b.im + a.im * b.re, }
}

///|
pub fn cx_scale(r : Double, a : Complex) -> Complex {
  Complex::{ re: r * a.re, im: r * a.im, }
}

///|
pub fn cx_conj(a : Complex) -> Complex {
  Complex::{ re: a.re, im: 0.0 - a.im, }
}

///|
pub fn cx_approx_eq(a : Complex, b : Complex) -> Bool {
  (a.re - b.re).abs() < eps && (a.im - b.im).abs() < eps
}

///|
/// A vector in C^n.
pub type CVec = Array[Complex]

///|
pub fn vec_zero(n : Int32) -> CVec {
  let out : CVec = []
  for _i in 0..<n {
    out.push(cx_zero())
  }
  out
}

///|
pub fn vec_add(a : CVec, b : CVec) -> CVec {
  let out : CVec = []
  for i in 0..<a.length() {
    out.push(cx_add(a[i], b[i]))
  }
  out
}

///|
pub fn vec_sub(a : CVec, b : CVec) -> CVec {
  let out : CVec = []
  for i in 0..<a.length() {
    out.push(cx_sub(a[i], b[i]))
  }
  out
}

///|
pub fn vec_scale(r : Double, a : CVec) -> CVec {
  let out : CVec = []
  for i in 0..<a.length() {
    out.push(cx_scale(r, a[i]))
  }
  out
}

///|
pub fn vec_scale_c(c : Complex, a : CVec) -> CVec {
  let out : CVec = []
  for i in 0..<a.length() {
    out.push(cx_mul(c, a[i]))
  }
  out
}

///|
/// Hermitian inner product, linear in the second argument:
/// ⟨a, b⟩ = Σᵢ conj(aᵢ) · bᵢ.
pub fn inner(a : CVec, b : CVec) -> Complex {
  let mut acc = cx_zero()
  for i in 0..<a.length() {
    acc = cx_add(acc, cx_mul(cx_conj(a[i]), b[i]))
  }
  acc
}

///|
pub fn vec_norm2(a : CVec) -> Double {
  inner(a, a).re
}

///|
pub fn vec_approx_eq(a : CVec, b : CVec) -> Bool {
  if a.length() != b.length() {
    return false
  }
  for i in 0..<a.length() {
    if !cx_approx_eq(a[i], b[i]) {
      return false
    }
  }
  true
}

///|
/// Orthogonality w.r.t. the Hermitian inner product: ⟨a,b⟩ ≈ 0.
pub fn vec_orthogonal(a : CVec, b : CVec) -> Bool {
  cx_approx_eq(inner(a, b), cx_zero())
}

///|
/// A square complex matrix, stored as rows.
pub struct CMat {
  n : Int32
  rows : Array[Array[Complex]]
}

///|
pub fn mat_identity(n : Int32) -> CMat {
  let rows : Array[Array[Complex]] = []
  for i in 0..<n {
    let row : Array[Complex] = []
    for j in 0..<n {
      if i == j {
        row.push(cx_real(1.0))
      } else {
        row.push(cx_zero())
      }
    }
    rows.push(row)
  }
  CMat::{ n, rows, }
}

///|
pub fn mat_zero(n : Int32) -> CMat {
  let rows : Array[Array[Complex]] = []
  for _i in 0..<n {
    rows.push(vec_zero(n))
  }
  CMat::{ n, rows, }
}

///|
pub fn mat_from_rows(rows : Array[Array[Complex]]) -> CMat {
  CMat::{ n: rows.length(), rows, }
}

///|
pub fn mat_get(m : CMat, i : Int32, j : Int32) -> Complex {
  m.rows[i][j]
}

///|
pub fn mat_add(a : CMat, b : CMat) -> CMat {
  let rows : Array[Array[Complex]] = []
  for i in 0..<a.n {
    rows.push(vec_add(a.rows[i], b.rows[i]))
  }
  CMat::{ n: a.n, rows, }
}

///|
pub fn mat_sub(a : CMat, b : CMat) -> CMat {
  let rows : Array[Array[Complex]] = []
  for i in 0..<a.n {
    rows.push(vec_sub(a.rows[i], b.rows[i]))
  }
  CMat::{ n: a.n, rows, }
}

///|
pub fn mat_mul(a : CMat, b : CMat) -> CMat {
  let rows : Array[Array[Complex]] = []
  for i in 0..<a.n {
    let row : Array[Complex] = []
    for j in 0..<a.n {
      let mut acc = cx_zero()
      for k in 0..<a.n {
        acc = cx_add(acc, cx_mul(a.rows[i][k], b.rows[k][j]))
      }
      row.push(acc)
    }
    rows.push(row)
  }
  CMat::{ n: a.n, rows, }
}

///|
pub fn mat_vec(m : CMat, v : CVec) -> CVec {
  let out : CVec = []
  for i in 0..<m.n {
    let mut acc = cx_zero()
    for k in 0..<m.n {
      acc = cx_add(acc, cx_mul(m.rows[i][k], v[k]))
    }
    out.push(acc)
  }
  out
}

///|
/// Adjoint M†: conjugate transpose.
pub fn mat_adjoint(m : CMat) -> CMat {
  let rows : Array[Array[Complex]] = []
  for i in 0..<m.n {
    let row : Array[Complex] = []
    for j in 0..<m.n {
      row.push(cx_conj(m.rows[j][i]))
    }
    rows.push(row)
  }
  CMat::{ n: m.n, rows, }
}

///|
pub fn mat_approx_eq(a : CMat, b : CMat) -> Bool {
  if a.n != b.n {
    return false
  }
  for i in 0..<a.n {
    if !vec_approx_eq(a.rows[i], b.rows[i]) {
      return false
    }
  }
  true
}

///|
/// Hermitian check: M† ≈ M.
pub fn is_hermitian(m : CMat) -> Bool {
  mat_approx_eq(mat_adjoint(m), m)
}

///|
/// Idempotence check: M · M ≈ M.
pub fn is_idempotent(m : CMat) -> Bool {
  mat_approx_eq(mat_mul(m, m), m)
}

///|
/// An orthogonal projector is precisely a Hermitian idempotent matrix.
pub fn is_projector(m : CMat) -> Bool {
  is_hermitian(m) && is_idempotent(m)
}

///|
pub fn mat_trace_re(m : CMat) -> Double {
  let mut acc = 0.0
  for i in 0..<m.n {
    acc = acc + m.rows[i][i].re
  }
  acc
}

///|
pub fn mat_commutes(a : CMat, b : CMat) -> Bool {
  mat_approx_eq(mat_mul(a, b), mat_mul(b, a))
}
