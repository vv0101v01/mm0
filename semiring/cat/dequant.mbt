// ===========================================================================
// 範疇化 III：Maslov 解量化——熱帶代數是普通代數的 h → 0 極限
//
// 另一條「解範疇化 / 退化」的路線。考慮把半環元素寫成指數形式：
//
//     a  ↦  e^(−A/h)        （A 是「熱帶座標」，h > 0）
//
// 則
//     a ⊕ b  ↦  e^(−A/h) + e^(−B/h)   →(h→0)  e^(−min(A,B)/h)  ↦ A ⊕ B
//     a ⊗ b  ↦  e^(−A/h) · e^(−B/h)   =       e^(−(A+B)/h)     ↦ A ⊗ B
//
// 也就是說：
//     −h·ln( Σ_i e^(−x_i/h) )  ─── h→0 ───▶  min_i x_i
//
// 這就是**解量化（dequantization）**：一般算術在 h→0 時退化成熱帶算術。
// 它和「取基數」是同一件事的兩種面貌——都是「忘掉結構」的半環同態，
// 一個忘掉的是加法裡的「多條路徑相加」，一個忘掉的是集合的基數。
//
// 為什麼要寫成程式：因為「極限」很容易講成信仰。這裡給出的是**誤差曲線**：
// h 每降一個數量級，min-plus 乘積與一般乘積的差距就跟著降，直到浮點下溢為止。
// 報告 §17 印出的就是這條曲線，以及它在那裡開始崩（這是誠實的部分：
// 極限在浮點上不可能真的到達，只能說「在可表示的範圍內一致」）。
// ===========================================================================

///|
/// 解量化（穩定版，log-sum-exp）：`−h·ln(Σ_i e^(−x_i/h))`。
///
/// 直接照公式算會在 h 小時**下溢**：`e^(−1/h)` 在 h < 1/709 時就變成 0，
/// 於是 ln(0) = −∞。所以實作先減去最小值 m：
///
///     −h·ln( Σ e^(−(x_i−m)/h) · e^(−m/h) ) = m − h·ln Σ e^(−(x_i−m)/h)
///
/// 這是等價變換（不是近似），但最小項的指數固定為 0，永遠不會下溢。
/// 報告 §17 同時印出「樸素版」的結果，讓下溢這件事看得見。
pub fn dequantize(xs : Array[Double], h : Double) -> Double {
  let mut m = 1.0e300
  for x in xs {
    if x < m {
      m = x
    }
  }
  if m >= 1.0e300 {
    return 1.0e300
  }
  let mut s = 0.0
  for x in xs {
    if x >= 1.0e300 {
      continue
    }
    s = s + @math.exp(-(x - m) / h)
  }
  m - h * @math.ln(s)
}

///|
/// 樸素版（照公式直接算）：只用於示範浮點下溢，不建議使用。
pub fn dequantize_naive(xs : Array[Double], h : Double) -> Double {
  let mut s = 0.0
  for x in xs {
    if x >= 1.0e300 {
      continue
    }
    s = s + @math.exp(-x / h)
  }
  -h * @math.ln(s)
}

///|
/// 一維驗證：`dequantize(xs, h)` 與 `min(xs)` 的差。
pub fn dequant_error(xs : Array[Double], h : Double) -> Double {
  let mut m = 1.0e300
  for x in xs {
    if x < m {
      m = x
    }
  }
  let d = dequantize(xs, h)
  let e = d - m
  if e < 0.0 {
    -e
  } else {
    e
  }
}

///|
/// 熱帶（min-plus）矩陣乘法：`C[i][j] = min_k (A[i][k] + B[k][j])`。
///
/// 直接以 Double 實作，方便與解量化版本逐格對照。
pub fn minplus_mul(
  a : Array[Array[Double]],
  b : Array[Array[Double]],
) -> Array[Array[Double]] {
  let n = a.length()
  let m = b[0].length()
  let k_len = b.length()
  let out : Array[Array[Double]] = []
  for i in 0..<n {
    let row : Array[Double] = []
    for j in 0..<m {
      let mut best = 1.0e300
      for k in 0..<k_len {
        let v = a[i][k] + b[k][j]
        if v < best {
          best = v
        }
      }
      row.push(best)
    }
    out.push(row)
  }
  out
}

///|
/// 一般矩陣乘法作用在「解量化後」的矩陣上：
///   P = exp(−A/h)、Q = exp(−B/h)、(PQ)[i][j] = Σ_k P[i][k]·Q[k][j]
/// 再以 `−h·ln` 取回熱帶座標。實作用同一套 log-sum-exp 移位技巧。
pub fn dequantized_mul(
  a : Array[Array[Double]],
  b : Array[Array[Double]],
  h : Double,
) -> Array[Array[Double]] {
  let n = a.length()
  let m = b[0].length()
  let k_len = b.length()
  let out : Array[Array[Double]] = []
  for i in 0..<n {
    let row : Array[Double] = []
    for j in 0..<m {
      let sums : Array[Double] = []
      for k in 0..<k_len {
        sums.push(a[i][k] + b[k][j])
      }
      row.push(dequantize(sums, h))
    }
    out.push(row)
  }
  out
}

///|
/// 兩個矩陣的最大絕對差。
pub fn max_abs_diff(
  a : Array[Array[Double]],
  b : Array[Array[Double]],
) -> Double {
  let mut worst = 0.0
  for i in 0..<a.length() {
    for j in 0..<a[i].length() {
      let d = a[i][j] - b[i][j]
      let ad = if d < 0.0 { -d } else { d }
      if ad > worst {
        worst = ad
      }
    }
  }
  worst
}

///|
/// 對每個 k 記錄「哪一個 k 在 min-plus 中勝出」，用於檢查解量化是否保留了 argmin 結構。
///
/// 解量化之後，取貢獻最大的 k（`e^(−x/h)` 最大 ⇔ x 最小）必須與 min-plus 的 argmin 相同——
/// 這是熱帶幾何裡「領先項」的概念，也是 h 夠小時可以完全決定的部分。
pub fn argmin_k(a : Array[Double], b : Array[Double]) -> Int32 {
  let mut best = 1.0e300
  let mut idx = -1
  for k in 0..<a.length() {
    let v = a[k] + b[k]
    if v < best {
      best = v
      idx = k
    }
  }
  idx
}
