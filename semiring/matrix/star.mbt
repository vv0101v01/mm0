// ===========================================================================
// Kleene 閉包（矩陣星運算）
//
// 這一份檔案是「型別即定理」的核心：
//
//   定理 A（Aho–Hopcroft–Ullman；Backhouse–Carré）
//     Floyd–Warshall 的**原地**更新 d[i][j] ⊕= d[i][k]⊗d[k][j] 對所有半環
//     都正確 ⟺ 該半環冪等。非冪等時同一條路徑會被重複累加。
//     ⇒ 原地版本以 `IdempotentSemiring` 作為型別約束（編譯期擋掉誤用）。
//
//   定理 A'（為什麼「每輪快照」不夠）
//     即使把第 k 列/行先快照，DP 式
//        d^k[i][j] = d^{k-1}[i][j] ⊕ d^{k-1}[i][k]·d^{k-1}[k][j]
//     在非冪等半環仍然是錯的：漏掉了「在 k 上打轉任意次」的因子
//     d[k][k]*。正確的一般化是 Lehmann 的消去法（見 closure_lehmann）。
//
//   定理 B（Lehmann 1977 / R-Kleene）
//     對 2×2 分塊 M = [[A,B],[C,D]]：
//        M* = [[A₁ ⊕ B₁·D₁·C₁, B₁·D₁], [D₁·C₁, D₁]]
//        A₁ = A*，B₁ = A₁·B，C₁ = C·A₁，D₁ = (D ⊕ C₁·B₁)*
//     ⇒ 分治法，運算量仍是 O(n³)，但工作集隨遞迴深度縮小，
//       記憶體存取次數（不是 op 數）顯著下降。
// ===========================================================================

///|
/// 在指定 n×n 子區塊上做原地 Warshall（呼叫端需先放好單位元）。
pub fn[E : IdempotentSemiring] fw_region(
  m : Mat[E],
  r0 : Int32,
  c0 : Int32,
  n : Int32,
  ops? : Ops,
) -> Unit {
  let w = m.cols
  for k in 0..<n {
    let krow = (r0 + k) * w + c0
    for i in 0..<n {
      let irow = (r0 + i) * w + c0
      let dik = m.d[irow + k]
      if Semiring::is_zero(dik) {
        continue // 0 ⊗ x = 0，整列可跳過
      }
      for j in 0..<n {
        let dkj = m.d[krow + j]
        if Semiring::is_zero(dkj) {
          continue
        }
        let cand = Semiring::times(dik, dkj)
        m.d[irow + j] = Semiring::plus(m.d[irow + j], cand)
        if ops is Some(o) {
          o.record_times()
          o.record_plus()
        }
      }
    }
  }
}

///|
/// 矩陣星運算（原地 Floyd–Warshall）。
///
/// 輸入是邊矩陣（對角線不必是單位元），輸出是 I ⊕ M ⊕ M² ⊕ …。
/// **要求 `IdempotentSemiring`**：這是定理 A 的前提。
pub fn[E : IdempotentSemiring] closure_fw_inplace(
  edges : Mat[E],
  ops? : Ops,
) -> Mat[E] {
  if !edges.is_square() {
    abort("closure: matrix must be square")
  }
  let m = edges.copy()
  let n = m.rows
  for i in 0..<n {
    m.d[i * n + i] = Semiring::plus(m.d[i * n + i], Semiring::one())
  }
  fw_region(m, 0, 0, n, ops?)
  m
}

///|
/// Lehmann 消去法：對**任意封閉半環**（含非冪等）都正確。
///
/// 每一輪把頂點 k 消去：
///   1. d[k][k] ← d[k][k]*
///   2. i≠k：d[i][k] ← d[i][k] ⊗ d[k][k]
///   3. j≠k：d[k][j] ← d[k][k] ⊗ d[k][j]
///   4. i,j≠k：d[i][j] ← d[i][j] ⊕ d[i][k] ⊗ d[k][j]
///
/// 與原地 FW 的差別就在第 1 步的 star：它補上了「在 k 上任意次打轉」的
/// 因子，這正是非冪等半環中被漏掉的部分。
pub fn[E : StarSemiring] closure_lehmann(edges : Mat[E], ops? : Ops) -> Mat[E] {
  if !edges.is_square() {
    abort("closure_lehmann: matrix must be square")
  }
  // 注意：**不**先把單位元加到對角線。Lehmann 的第 1 步 star(d[k][k])
  // 本身就包含空路徑（star(0) = 1），重複加入會讓非冪等半環多算一次。
  let m = edges.copy()
  let n = m.rows
  for k in 0..<n {
    let dkk = StarSemiring::star(m.d[k * n + k])
    m.d[k * n + k] = dkk
    for i in 0..<n {
      if i == k {
        continue
      }
      let v = m.d[i * n + k]
      if Semiring::is_zero(v) {
        continue
      }
      m.d[i * n + k] = Semiring::times(v, dkk)
      if ops is Some(o) {
        o.record_times()
      }
    }
    for j in 0..<n {
      if j == k {
        continue
      }
      let v = m.d[k * n + j]
      if Semiring::is_zero(v) {
        continue
      }
      m.d[k * n + j] = Semiring::times(dkk, v)
      if ops is Some(o) {
        o.record_times()
      }
    }
    for i in 0..<n {
      if i == k {
        continue
      }
      let dik = m.d[i * n + k]
      if Semiring::is_zero(dik) {
        continue
      }
      for j in 0..<n {
        if j == k {
          continue
        }
        let dkj = m.d[k * n + j]
        if Semiring::is_zero(dkj) {
          continue
        }
        m.d[i * n + j] = Semiring::plus(
          m.d[i * n + j],
          Semiring::times(dik, dkj),
        )
        if ops is Some(o) {
          o.record_times()
          o.record_plus()
        }
      }
    }
  }
  m
}

///|
/// 分塊（R-Kleene 形式）的矩陣星運算：`IdempotentSemiring` 版本。
pub fn[E : IdempotentSemiring] closure_blocked(
  edges : Mat[E],
  threshold~ : Int32 = 32,
  ops? : Ops,
) -> Mat[E] {
  if !edges.is_square() {
    abort("closure_blocked: matrix must be square")
  }
  let m = edges.copy()
  let n = m.rows
  for i in 0..<n {
    m.d[i * n + i] = Semiring::plus(m.d[i * n + i], Semiring::one())
  }
  closure_rec(m, 0, 0, n, if threshold < 1 { 1 } else { threshold }, ops?)
  m
}

///|
/// 遞迴核心（允許奇數邊長：左半 h1 = n/2、右半 h2 = n − h1）。
fn[E : IdempotentSemiring] closure_rec(
  m : Mat[E],
  r0 : Int32,
  c0 : Int32,
  n : Int32,
  threshold : Int32,
  ops? : Ops,
) -> Unit {
  if n <= threshold {
    fw_region(m, r0, c0, n, ops?)
    return
  }
  let h1 = n / 2
  let h2 = n - h1
  // 區塊：A = 左上 (h1×h1)、B = 右上 (h1×h2)、C = 左下 (h2×h1)、D = 右下
  let ar = r0
  let ac = c0
  let br = r0
  let bc = c0 + h1
  let cr = r0 + h1
  let cc = c0
  let dr = r0 + h1
  let dc = c0 + h1
  // 1) A ← A*
  closure_rec(m, ar, ac, h1, threshold, ops?)
  // 緩衝：最大需要 h2×h2
  let buf = FixedArray::make(h2 * h2, Semiring::zero())
  // 2) B ← A*·B
  mul_region(m, ar, ac, br, bc, buf, h1, h1, h2, ops?)
  copy_region_in(m, br, bc, buf, h1, h2)
  // 3) C ← C·A*
  mul_region(m, cr, cc, ar, ac, buf, h2, h1, h1, ops?)
  copy_region_in(m, cr, cc, buf, h2, h1)
  // 4) D ← D ⊕ C·A*·B
  mul_region(m, cr, cc, br, bc, buf, h2, h1, h2, ops?)
  for i in 0..<h2 {
    for j in 0..<h2 {
      let idx = (dr + i) * m.cols + dc + j
      m.d[idx] = Semiring::plus(m.d[idx], buf[i * h2 + j])
    }
  }
  // 5) D ← D*
  closure_rec(m, dr, dc, h2, threshold, ops?)
  // 6) B ← B·D*
  mul_region(m, br, bc, dr, dc, buf, h1, h2, h2, ops?)
  copy_region_in(m, br, bc, buf, h1, h2)
  // 7) C ← D*·C
  mul_region(m, dr, dc, cr, cc, buf, h2, h2, h1, ops?)
  copy_region_in(m, cr, cc, buf, h2, h1)
  // 8) A ← A* ⊕ B·C
  mul_region(m, br, bc, cr, cc, buf, h1, h2, h1, ops?)
  for i in 0..<h1 {
    for j in 0..<h1 {
      let idx = (ar + i) * m.cols + ac + j
      m.d[idx] = Semiring::plus(m.d[idx], buf[i * h1 + j])
    }
  }
}

// ---------------------------------------------------------------------------
// 不封閉半環：截斷級數 + 收斂判據
// ---------------------------------------------------------------------------

///|
/// 級數近似：回傳 ⊕_{i=0}^{k} M^i 與「是否已收斂」。
///
/// 收斂判據由呼叫端提供（`is_small`）：浮點半環用 |x| < ε，
/// 精確半環用 `is_zero`。對不收斂的半環（例如譜半徑 ≥ 1 的機率矩陣）
/// 會回傳 `false`，**不會**無限迴圈，也不會給出假的結果。
pub fn[E : Semiring] closure_series(
  edges : Mat[E],
  k~ : Int32 = 16,
  is_small? : (E) -> Bool,
) -> (Mat[E], Bool) {
  if !edges.is_square() {
    abort("closure_series: matrix must be square")
  }
  let n = edges.rows
  let small = match is_small {
    Some(f) => f
    None => fn(x : E) { Semiring::is_zero(x) }
  }
  let mut acc = Mat::identity(n)
  let mut pw = Mat::identity(n)
  let mut converged = false
  for _ in 0..<k {
    pw = mul_ikj(pw, edges)
    acc = mat_plus(acc, pw)
    if mat_all(pw, small) {
      converged = true
      break
    }
  }
  (acc, converged)
}

///|
/// 所有元素都滿足 f。
pub fn[E] mat_all(m : Mat[E], f : (E) -> Bool) -> Bool {
  for i in 0..<m.d.length() {
    if !f(m.d[i]) {
      return false
    }
  }
  true
}

///|
/// 矩陣加法（逐元素 ⊕）。
pub fn[E : Semiring] mat_plus(a : Mat[E], b : Mat[E]) -> Mat[E] {
  if a.rows != b.rows || a.cols != b.cols {
    abort("mat_plus: shape mismatch")
  }
  let out = Mat::new(a.rows, a.cols, Semiring::zero())
  for i in 0..<a.d.length() {
    out.d[i] = Semiring::plus(a.d[i], b.d[i])
  }
  out
}

///|
/// 是否為零矩陣。
pub fn[E : Semiring] mat_is_zero(a : Mat[E]) -> Bool {
  for i in 0..<a.d.length() {
    if !Semiring::is_zero(a.d[i]) {
      return false
    }
  }
  true
}

///|
/// 兩個矩陣是否逐元素相等。
pub fn[E : Semiring] mat_equal(a : Mat[E], b : Mat[E]) -> Bool {
  if a.rows != b.rows || a.cols != b.cols {
    return false
  }
  for i in 0..<a.d.length() {
    if a.d[i] != b.d[i] {
      return false
    }
  }
  true
}
