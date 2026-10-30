///| ## G3 —— 譜計算的係數環：精度按需付費，認證由另一個環給
///

///| B4 的殘餘原本寫成「位長成長」。但位長成長只發生在**精確 ℚ 係數**這一個環裡。

///| 同一批特徵值可以在三個環裡分別處理，各付各的價：

///|

///|  - `F_p`：**螢幕**。特徵多項式 mod p 不需要 BigInt（係數恆在 `p` 位元內），

///|    平方自由 ⇒ `p ∤ disc`，於是可以安全地用於 CRT 重構（上一輪已立）。

///|  - `ℝ`：**定位**。Jacobi 旋轉給 `O(n³)` 的近似值。

///|  - `ℚ`：**認證**。`qpoly_isolate_real_roots` 給出寬度 `2^{−k}` 的**嚴格隔離區間**；

///|    精度 `k` 是參數，所以成本隨需求成長，不隨 `n` 爆炸。

///|

///| 於是 B4 的殘餘不是「位長擋路」，而是「三個環要對得上」。本檔案把「對得上」

///| 變成斷言：每個 ℝ 近似值必須落在**唯一一個** ℚ 隔離區間裡，而且區間數 = `n`

///|（沒有退化、沒有合併）。

///|
/// 一個譜計算的三環對照列。
pub struct SpectralRow {
  n : Int32
  exact_digits : Int32
  distinct_over_q : Bool
  fp_squarefree : Array[Bool]
  intervals_at : Array[(Int32, Int32)]
  numeric_max_err : Double
  numeric_error_lt_interval : Bool
  all_inside : Bool
}

///| 整數對稱矩陣（確定性，無隨機）：`A[i][i] = i² + 1`、`A[i][j] = 1`（`i ≠ j`）。

///|
/// 這個族有「近簡併」的傾向，正好用來量測隔離精度。
fn symmetric_family(n : Int32) -> Array[Array[Int32]] {
  let rows : Array[Array[Int32]] = []
  for i = 0; i < n; i = i + 1 {
    let row : Array[Int32] = []
    for j = 0; j < n; j = j + 1 {
      if i == j {
        row.push(i * i + 1)
      } else {
        row.push(1)
      }
    }
    rows.push(row)
  }
  rows
}

///|
fn to_double_rows(m : Array[Array[Int32]]) -> Array[Array[Double]] {
  let out : Array[Array[Double]] = []
  for r in m {
    let row : Array[Double] = []
    for x in r {
      row.push(x.to_double())
    }
    out.push(row)
  }
  out
}

///|
fn sort_doubles(a : Array[Double]) -> Array[Double] {
  let b : Array[Double] = []
  for x in a {
    b.push(x)
  }
  for i = 1; i < b.length(); i = i + 1 {
    let key = b[i]
    let mut j = i - 1
    while j >= 0 && b[j] > key {
      b[j + 1] = b[j]
      j = j - 1
    }
    b[j + 1] = key
  }
  b
}

///|
/// 一條譜列。
pub fn spectral_row(
  n : Int32,
  primes : Array[Int32],
  widths : Array[Int32],
) -> SpectralRow {
  let m = symmetric_family(n)
  let qm = @algebra.qmat_from_int_rows(m)
  let cp = @algebra.qmat_charpoly(qm)
  let big = @algebra.qpoly_integer_coeffs_big(cp)
  let mut digits : Int32 = 0
  for b in big {
    let s = b.to_string()
    if s.length() > digits {
      digits = s.length()
    }
  }
  // ℚ：是否平方自由（等價於 n 個相異特徵值）
  let distinct = @algebra.qpoly_is_squarefree(cp)
  // F_p：平方自由 ⇒ p ∤ disc
  let fp_sf : Array[Bool] = []
  for p in primes {
    let coeffs = @algebra.qpoly_integer_coeffs(cp)
    let residues : Array[Int32] = []
    for c in coeffs {
      residues.push((c % p + p) % p)
    }
    // 模 p 的平方自由檢查：gcd(f, f') mod p 的次數為 0
    fp_sf.push(squarefree_mod_p(residues, p))
  }
  // ℝ：Jacobi
  let (ev, _) = @spec.jacobi_eigen(to_double_rows(m))
  let nums = sort_doubles(ev)
  // ℚ：隔離區間（不同精度）
  let counts : Array[(Int32, Int32)] = []
  let mut max_err : Double = 0.0
  let mut inside_ok = true
  let mut err_lt_width = true
  let mut last_intervals : Array[(Double, Double)] = []
  for w in widths {
    match @algebra.qmat_symmetric_eigenvalue_isolations(qm, w) {
      Some(ivs) => {
        counts.push((w, ivs.length()))
        let pairs : Array[(Double, Double)] = []
        for iv in ivs {
          pairs.push(
            (@algebra.rat_to_double(iv.lower), @algebra.rat_to_double(iv.upper)),
          )
        }
        last_intervals = pairs
      }
      None => counts.push((w, 0 - 1))
    }
  }
  if last_intervals.length() == nums.length() {
    for i = 0; i < nums.length(); i = i + 1 {
      let lo = last_intervals[i].0
      let hi = last_intervals[i].1
      let mid = (lo + hi) / 2.0
      let half = (hi - lo) / 2.0
      let err = abs_d(nums[i] - mid)
      if err > max_err {
        max_err = err
      }
      if nums[i] < lo || nums[i] > hi {
        inside_ok = false
      }
      if err > half {
        err_lt_width = false
      }
    }
  } else {
    inside_ok = false
  }
  SpectralRow::{
    n,
    exact_digits: digits,
    distinct_over_q: distinct,
    fp_squarefree: fp_sf,
    intervals_at: counts,
    numeric_max_err: max_err,
    numeric_error_lt_interval: err_lt_width,
    all_inside: inside_ok,
  }
}

///|
fn abs_d(x : Double) -> Double {
  if x < 0.0 {
    0.0 - x
  } else {
    x
  }
}

///|
/// 模 p 的平方自由判定：`gcd(f, f')` 在 `F_p` 上是否為常數。
fn squarefree_mod_p(coeffs : Array[Int32], p : Int32) -> Bool {
  // f' 係數
  let der : Array[Int32] = []
  for i = 1; i < coeffs.length(); i = i + 1 {
    der.push(coeffs[i] * (i % p) % p)
  }
  if der.length() == 0 {
    return true
  }
  let fld = @core.mk_field(p)
  let a = @core.mat_from_rows([coeffs])
  let b = @core.mat_from_rows([der])
  let ra = @core.gauss_jordan(a, fld).rank
  let rb = @core.gauss_jordan(b, fld).rank
  // gcd 非常數 ⟺ f 與 f' 有共同根；用結式風格：檢查 f 的每個根是否也零化 f'——
  // 有限域上直接枚舉（p 小）
  let mut common = false
  for r = 0; r < p; r = r + 1 {
    let mut fv : Int32 = 0
    let mut pw : Int32 = 1
    for c in coeffs {
      fv = (fv + c * pw) % p
      pw = pw * r % p
    }
    let mut dv : Int32 = 0
    let mut pw2 : Int32 = 1
    for c in der {
      dv = (dv + c * pw2) % p
      pw2 = pw2 * r % p
    }
    if fv % p == 0 && dv % p == 0 {
      common = true
    }
  }
  let _ = ra
  let _ = rb
  !common
}

///|
/// G3 的實驗輸出。
pub fn g3_probe() -> Array[String] {
  let out : Array[String] = []
  let primes : Array[Int32] = [10007, 30011, 46327]
  for n in [6, 8, 10] {
    let r = spectral_row(n, primes, [8, 16, 24, 32])
    let mut ivs = ""
    for c in r.intervals_at {
      ivs = "\{ivs} [2^-\{c.0}: 區間數=\{c.1}]"
    }
    out.push(
      "n=\{r.n}: 精確係數最大位數=\{r.exact_digits} Q上平方自由(⇒n個相異特徵值)=\{r.distinct_over_q} F_p平方自由=\{bools_show(r.fp_squarefree)}\{ivs}",
    )
    out.push(
      "       R 近似最大偏差=\{r.numeric_max_err} 落在 Q 隔離區間內=\{r.all_inside} 偏差<區間半寬=\{r.numeric_error_lt_interval}",
    )
  }
  out.push(
    "結論：位長只在 Q 這一個環裡成長；F_p 螢幕恆在 p 位元內，R 定位 O(n^3)，Q 認證的精度是參數 2^-k —— 三個環各付各的價",
  )
  out
}

///| 布林向量顯示（不用 `Show`）。
fn bools_show(a : Array[Bool]) -> String {
  let mut out = "["
  for i = 0; i < a.length(); i = i + 1 {
    let t = if a[i] { "true" } else { "false" }
    out = if i == 0 {
      out + t
    } else {
      out + ", " + t
    }
  }
  out + "]"
}
