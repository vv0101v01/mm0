// ===========================================================================
// 樣條空間（B-spline space）
//
// 數學結構：以節點向量 t₀ ≤ … ≤ t_{n+p} 與次數 p 定義的分段多項式空間
//   S = span{ B_{i,p} }，  dim S = n
// 三個「結構 ⇒ 演算法」的推論：
//
//   (1) 局部支撐：B_{i,p} 的支撐是 [t_i, t_{i+p+1}] ⇒ 配點矩陣
//       A[i][j] = B_{j,p}(x_i) 只有 p+1 條非零對角線（帶狀）。
//       ⇒ 解係數可以用帶狀 LU 在 O(n·p²) 完成，而不是稠密 O(n³)。
//
//   (2) 均勻節點 + 三次時，配點矩陣是循環矩陣 (z⁻¹ + 4 + z)/6，
//       其生成函數在 ℤ[z,z⁻¹] 上分解成 (1-ζz⁻¹)(1-ζz)（ζ = -2+√3）。
//       ⇒ 求逆等於兩個一階遞推，O(n) 完成（Unser–Aldroubi–Eden 1993）。
//       每個一階遞推 u_i = ζ·u_{i-1} + y_i 都是**仿射么半群**的元素，
//       所以整條濾波是么半群前綴掃描，而不是序列依賴的迴圈。
//
//   (3) de Boor 演算法是 Cox–de Boor 遞迴的數值穩定形式，O(p²)
//       （本庫另提供 p² · 每次求值 的基準版用於交叉驗證）。
// ===========================================================================

///|
using @mon {type AffineM, type OppositeM, prefix_scan}

///|
/// 均勻節點向量：t_i = i - p（i = 0..n+p），使曲線定義域為 [0, n-p]。
pub fn uniform_knots(p : Int32, n : Int32) -> Array[Double] {
  let len = n + p + 1
  Array::makei(len, fn(i) { (i - p).to_double() })
}

///|
/// Cox–de Boor 遞迴：第 i 個 p 次 B 樣條在 t 的值。
///
/// 直接照定義遞迴，O(p²)。用於驗證 de Boor 演算法（交叉檢查）。
pub fn bspline_basis(
  knots : Array[Double],
  p : Int32,
  i : Int32,
  t : Double,
) -> Double {
  if p == 0 {
    if (t >= knots[i] && t < knots[i + 1]) ||
      (t == knots[i + 1] && i + 1 == knots.length() - 1) {
      return 1.0
    }
    return 0.0
  }
  let mut left = 0.0
  let d1 = knots[i + p] - knots[i]
  if d1 > 0.0 {
    left = (t - knots[i]) / d1 * bspline_basis(knots, p - 1, i, t)
  }
  let mut right = 0.0
  let d2 = knots[i + p + 1] - knots[i + 1]
  if d2 > 0.0 {
    right = (knots[i + p + 1] - t) / d2 * bspline_basis(knots, p - 1, i + 1, t)
  }
  left + right
}

///|
/// 找到 t 所屬的區間索引（knots[span] ≤ t < knots[span+1]）。
fn find_span(knots : Array[Double], p : Int32, n : Int32, t : Double) -> Int32 {
  if t >= knots[n] {
    return n - 1
  }
  if t <= knots[p] {
    return p
  }
  let mut lo = p
  let mut hi = n
  while lo < hi - 1 {
    let mid = (lo + hi) / 2
    if t >= knots[mid] {
      lo = mid
    } else {
      hi = mid
    }
  }
  lo
}

///|
/// de Boor 演算法：O(p²) 且數值穩定地算出曲線在 t 的值。
pub fn eval_deboor(
  coeffs : Array[Double],
  knots : Array[Double],
  p : Int32,
  t : Double,
) -> Double {
  let n = coeffs.length()
  let span = find_span(knots, p, n, t)
  let d = Array::make(p + 1, 0.0)
  for j in 0..<=p {
    d[j] = coeffs[span - p + j]
  }
  for r in 1..<=p {
    let mut j = p
    while j >= r {
      let i = j + span - p
      let denom = knots[i + p + 1 - r] - knots[i]
      let alpha = if denom == 0.0 { 0.0 } else { (t - knots[i]) / denom }
      d[j] = (1.0 - alpha) * d[j - 1] + alpha * d[j]
      j = j - 1
    }
  }
  d[p]
}

// ---------------------------------------------------------------------------
// 配點（collocation）系統：三種解法
// ---------------------------------------------------------------------------

///|
/// 均勻三次樣條在整數節點的配點矩陣是循環矩陣 (z⁻¹+4+z)/6。
/// 這裡回傳其「整數版本」的係數：對角 4、次對角 1。
fn collocation_dense(n : Int32, periodic : Bool) -> Array[Array[Double]] {
  let a = Array::makei(n, fn(_i) { Array::make(n, 0.0) })
  for i in 0..<n {
    a[i][i] = 4.0
    if i + 1 < n {
      a[i][i + 1] = 1.0
      a[i + 1][i] = 1.0
    }
  }
  if periodic && n > 2 {
    a[0][n - 1] = 1.0
    a[n - 1][0] = 1.0
  }
  a
}

///|
/// 稠密高斯消去（部分主元）。O(n³)，作為正確性基準與「慢」的對照。
///
/// 回傳 Option：奇異矩陣時為 None（而不是回傳垃圾數值）。
pub fn solve_dense(
  a : Array[Array[Double]],
  b : Array[Double],
) -> Array[Double]? {
  let n = b.length()
  let m = Array::makei(n, fn(i) { a[i].copy() })
  let x = b.copy()
  for k in 0..<n {
    // 部分主元
    let mut piv = k
    let mut best = m[k][k].abs()
    for i in (k + 1)..<n {
      if m[i][k].abs() > best {
        best = m[i][k].abs()
        piv = i
      }
    }
    if best < 1.0e-300 {
      return None
    }
    if piv != k {
      let tmp = m[k]
      m[k] = m[piv]
      m[piv] = tmp
      let t2 = x[k]
      x[k] = x[piv]
      x[piv] = t2
    }
    let d = m[k][k]
    for i in (k + 1)..<n {
      let f = m[i][k] / d
      if f == 0.0 {
        continue
      }
      for j in k..<n {
        m[i][j] = m[i][j] - f * m[k][j]
      }
      x[i] = x[i] - f * x[k]
    }
  }
  // 回代：必須由後往前（由前往後會用到尚未求解的 x[j]）
  let mut i = n - 1
  while i >= 0 {
    let mut s = x[i]
    for j in (i + 1)..<n {
      s = s - m[i][j] * x[j]
    }
    let d = m[i][i]
    if d.abs() < 1.0e-300 {
      return None
    }
    x[i] = s / d
    i = i - 1
  }
  Some(x)
}

///|
/// 帶狀矩陣：以「對角線主序」儲存，`a[i][d]` 表示 A[i][i + d − band]。
pub(all) struct Banded {
  n : Int32
  band : Int32
  a : Array[Array[Double]]
}

///|
/// 由三對角（常數對角值）建立帶狀矩陣。
pub fn Banded::tridiag(n : Int32, diag : Double, off : Double) -> Banded {
  let band = 1
  let a = Array::makei(n, fn(_i) { Array::make(2 * band + 1, 0.0) })
  for i in 0..<n {
    a[i][band] = diag
    if i > 0 {
      a[i][band - 1] = off
    }
    if i + 1 < n {
      a[i][band + 1] = off
    }
  }
  { n, band, a, }
}

///|
/// 取元素（帶外視為 0）。
pub fn Banded::get(self : Banded, i : Int32, j : Int32) -> Double {
  let d = j - i + self.band
  if d < 0 || d > 2 * self.band {
    0.0
  } else {
    self.a[i][d]
  }
}

///|
/// 帶狀 LU（無主元）+ 回代：O(n·band²)。
///
/// 不帶主元的前提是「嚴格對角佔優」，B 樣條配點矩陣滿足此條件
/// （凸包性質）。仍然檢查主元大小，退化時回傳 None。
pub fn solve_banded(bm : Banded, b : Array[Double]) -> Array[Double]? {
  let n = bm.n
  let band = bm.band
  let x = b.copy()
  for i in 0..<n {
    let piv = bm.get(i, i)
    if piv.abs() < 1.0e-300 {
      return None
    }
    let rmax = (i + band).min(n - 1)
    for r in (i + 1)..<=rmax {
      let f = bm.get(r, i) / piv
      if f == 0.0 {
        continue
      }
      let cmax = (i + 2 * band).min(n - 1)
      for c in i..<=cmax {
        let d = c - r + band
        if d >= 0 && d <= 2 * band {
          bm.a[r][d] = bm.a[r][d] - f * bm.get(i, c)
        }
      }
      x[r] = x[r] - f * x[i]
    }
  }
  let mut i = n - 1
  while i >= 0 {
    let mut s = x[i]
    let cmax = (i + band).min(n - 1)
    for c in (i + 1)..<=cmax {
      s = s - bm.get(i, c) * x[c]
    }
    let piv = bm.get(i, i)
    if piv.abs() < 1.0e-300 {
      return None
    }
    x[i] = s / piv
    i = i - 1
  }
  Some(x)
}

// ---------------------------------------------------------------------------
// 遞迴（IIR）解法：O(n)，且是么半群前綴掃描
// ---------------------------------------------------------------------------

///|
/// 三次 B 樣條配點系統的極點 ζ = -2 + √3（|ζ| < 1）。
///
/// 由 (1 - ζ z⁻¹)(1 - ζ z) ∝ (z⁻¹ + 4 + z) 解出：ζ² + 4ζ + 1 = 0。
pub fn cubic_pole() -> Double {
  -2.0 + 1.7320508075688772
}

///|
/// 把仿射步驟陣列做前綴掃描，回傳 each prefix 的映射。
/// 這是「么半群 ⇒ 濾波」的橋樑：每個遞推步都是 x ↦ ζx + y_i。
pub fn affine_steps(zeta : Double, ys : Array[Double]) -> Array[AffineM] {
  // 用反么半群，使掃描結果的「套用順序」與資料流方向一致：
  //   out[i] = A_i ∘ … ∘ A_0 ，out[i](0) 就是逐步遞推的第 i 步結果。
  let steps = Array::makei(ys.length(), fn(i) {
    OppositeM::{ inner: AffineM::new(zeta, ys[i]), }
  })
  let scanned : Array[OppositeM[AffineM]] = []
  prefix_scan(steps, out=scanned)
  Array::makei(ys.length(), fn(i) { scanned[i].inner })
}

///|
/// 均勻三次樣條的係數：解 (1/6)(c_{i-1} + 4c_i + c_{i+1}) = y_i（週期邊界）。
///
/// 推導：z⁻¹ + 4 + z = (−1/ζ)(1 − ζz⁻¹)(1 − ζz)，ζ = −2+√3。
/// 於是方程等價於兩個一階遞推：
///   forward  u_i = (−6ζ)·y_i + ζ·u_{i−1}
///   backward c_i = u_i + ζ·c_{i+1}
/// 每個遞推步都是仿射映射 x ↦ ζx + b，因此可以寫成么半群前綴掃描。
///
/// 邊界以幾何級數**精確**初始化（不是「多掃幾遍等它收斂」——
/// 當 n 小或少數幾個掃描時，後者會殘留 O(|ζ|^n) 的誤差）。
pub fn interp_cubic_periodic(y : Array[Double]) -> Array[Double] {
  let n = y.length()
  if n == 0 {
    return []
  }
  let z = cubic_pole()
  let g = -6.0 * z
  // U_{-1} = g·Σ_{k≥0} ζ^k y_{n-1-k}（週期索引）
  let mut u_prev = 0.0
  let mut zk = 1.0
  let mut idx = n - 1
  for _ in 0..<64 {
    if zk.abs() < 1.0e-18 {
      break
    }
    u_prev = u_prev + zk * y[idx]
    zk = zk * z
    idx = if idx == 0 { n - 1 } else { idx - 1 }
  }
  u_prev = g * u_prev
  let u = Array::make(n, 0.0)
  for i in 0..<n {
    u_prev = g * y[i] + z * u_prev
    u[i] = u_prev
  }
  // 反向遞推 c_i = u_i + ζ·c_{i+1} 展開為 c_i = Σ_{k≥0} ζ^k u_{i+k}，
  // 因此 c_n（= c_0）的初值要用「往前」的幾何級數。
  let mut c_next = 0.0
  let mut zk2 = 1.0
  let mut j = 0
  for _ in 0..<64 {
    if zk2.abs() < 1.0e-18 {
      break
    }
    c_next = c_next + zk2 * u[j]
    zk2 = zk2 * z
    j = (j + 1) % n
  }
  let c = Array::make(n, 0.0)
  let mut i = n - 1
  while i >= 0 {
    c_next = u[i] + z * c_next
    c[i] = c_next
    i = i - 1
  }
  c
}

///|
/// 稠密解（O(n³)），**循環**（週期）配點系統 —— 正確性基準與複雜度對照。
pub fn interp_cubic_dense(y : Array[Double]) -> Array[Double] {
  let n = y.length()
  let a = collocation_dense(n, true)
  for i in 0..<n {
    for j in 0..<n {
      a[i][j] = a[i][j] / 6.0
    }
  }
  match solve_dense(a, y) {
    Some(x) => x
    None => abort("interp_cubic_dense: singular collocation matrix")
  }
}

///|
/// 稠密解（O(n³)），**開放邊界**配點系統（不捲繞）。
pub fn interp_cubic_banded(y : Array[Double]) -> Array[Double] {
  let n = y.length()
  let bm = Banded::tridiag(n, 4.0 / 6.0, 1.0 / 6.0)
  match solve_banded(bm, y) {
    Some(x) => x
    None => abort("interp_cubic_banded: singular banded matrix")
  }
}

///|
/// 稠密解（O(n³)），開放邊界配點系統；與 `interp_cubic_banded` 對照。
pub fn interp_cubic_dense_open(y : Array[Double]) -> Array[Double] {
  let n = y.length()
  let a = collocation_dense(n, false)
  for i in 0..<n {
    for j in 0..<n {
      a[i][j] = a[i][j] / 6.0
    }
  }
  match solve_dense(a, y) {
    Some(x) => x
    None => abort("interp_cubic_dense_open: singular")
  }
}

// ---------------------------------------------------------------------------
// 量化：樣條空間的「么半群聚合」用法
// ---------------------------------------------------------------------------
