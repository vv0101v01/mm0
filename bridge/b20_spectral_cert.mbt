///| ## 橋 20：譜流／Witten 指標 ↔ Jacobi 區間認證（`super ↔ cubical`）
///
///| golden 的 `super/spec` 用**浮點**算譜流：沿 `H(t) = (1−t)H₀ + tH₁` 取樣，
///| 用 Jacobi 迭代求特徵值，數每條分支的符號變化。它有兩個說不清楚的地方：
///|
///|  1. **取樣數是參數**：`samples` 給多少，答案就可能跟著變（死區 `1e-7` 內不算）；
///|  2. **端點退化時它照樣給數字**：某條特徵值在 `t = 0` 或 `t = 1` 恰好是 0，譜流根本沒定義，
///|     浮點版不會說「不確定」。
///|
///| 這一支橋用 `exact/algebra` 的**精確根隔離**（`qmat_symmetric_eigenvalue_isolations`，
///| 也就是 golden `algebra/Jacobi_interval.mbt` 那套區間認證的同一個內容，只是走特徵多項式的根隔離）
///| 把同一件事做成**不需要取樣、能說不確定**的版本：
///|
///|  - 對稱路徑的第 `k` 小特徵值是連續函數 ⇒ 依序號配對就是正確的分支配對（不需要追蹤）；
///|  - 端點特徵值用**有理區間**夾住，區間落在正/負半軸才算「決定」；
///|  - 譜流 = Σ_k (sgn_k(1) − sgn_k(0)) / 2，全整數運算。
///|
///| 誠實的結論：浮點版在多數例子裡與認證版一致（它的序號配對其實是對的），
///| 但**它給不出「不確定」**，而且答案依賴 `samples`。認證版把這兩件事都補上。

///| 一個端點的特徵值區間（排序後）。
pub struct SpecPoint {
  signs : Array[Int32]
  widths : Array[String]
  undecided : Int32
}

///| 有理對稱矩陣的特徵值符號序列（依大小排序，重數展開）。
pub fn certified_signs(m : @algebra.QMat, bits : Int32) -> SpecPoint? {
  match @algebra.qmat_symmetric_eigenvalue_isolations(m, bits) {
    None => None
    Some(roots) => {
      // 依下界排序（防止實作順序改變）
      let idx : Array[Int32] = []
      for i = 0; i < roots.length(); i = i + 1 {
        idx.push(i)
      }
      let mut i = 1
      while i < idx.length() {
        let x = idx[i]
        let mut j = i - 1
        while j >= 0 && @algebra.rat_cmp_exact(roots[idx[j]].lower, roots[x].lower) > 0 {
          idx[j + 1] = idx[j]
          j = j - 1
        }
        idx[j + 1] = x
        i = i + 1
      }
      let signs : Array[Int32] = []
      let widths : Array[String] = []
      let mut undecided = 0
      for k in idx {
        let r = roots[k]
        let lo = r.lower
        let hi = r.upper
        let sgn = if @algebra.rat_cmp_exact(lo, @algebra.rat_zero()) > 0 {
          1
        } else if @algebra.rat_cmp_exact(hi, @algebra.rat_zero()) < 0 {
          -1
        } else {
          undecided = undecided + 1
          0
        }
        let iv = @algebra.rat_interval(lo, hi)
        for _m = 0; _m < r.multiplicity; _m = _m + 1 {
          signs.push(sgn)
          widths.push(@algebra.rat_to_string(@algebra.rat_interval_width(iv)))
        }
      }
      Some(SpecPoint::{ signs, widths, undecided })
    }
  }
}

///| 認證譜流：`None` = 端點有特徵值無法與 0 分離（不確定）。
pub fn certified_spectral_flow(
  h0 : Array[Array[Int32]],
  h1 : Array[Array[Int32]],
) -> Int32? {
  let p0 = certified_signs(@algebra.qmat_from_int_rows(h0), 24)
  let p1 = certified_signs(@algebra.qmat_from_int_rows(h1), 24)
  match (p0, p1) {
    (Some(a), Some(b)) => {
      if a.undecided > 0 || b.undecided > 0 || a.signs.length() != b.signs.length() {
        None
      } else {
        let mut flow = 0
        for k = 0; k < a.signs.length(); k = k + 1 {
          if a.signs[k] != b.signs[k] {
            if a.signs[k] < 0 {
              flow = flow + 1
            } else {
              flow = flow - 1
            }
          }
        }
        Some(flow)
      }
    }
    _ => None
  }
}

///| 浮點版（golden `super/spec`）。
pub fn float_spectral_flow(
  h0 : Array[Array[Int32]],
  h1 : Array[Array[Int32]],
  samples : Int32,
) -> Int32 {
  let a : Array[Array[Double]] = []
  let b : Array[Array[Double]] = []
  for r in h0 {
    let row : Array[Double] = []
    for x in r {
      row.push(x.to_double())
    }
    a.push(row)
  }
  for r in h1 {
    let row : Array[Double] = []
    for x in r {
      row.push(x.to_double())
    }
    b.push(row)
  }
  @spec.spectral_flow(a, b, samples)
}

///| Witten 指標：`dim ker D − dim ker Dᵀ`，用精確秩算（不是假設 `m − n`）。
pub fn witten_index_exact(d : Array[Array[Int32]]) -> Int32 {
  let m = if d.length() == 0 { 0 } else { d[0].length() }
  let n = d.length()
  let r = @algebra.qmat_rank(@algebra.qmat_from_int_rows(d))
  (m - r) - (n - r)
}

///| 一行對照。
pub struct SpecRow {
  name : String
  certified : String
  floats : String
  verdict : String
}

///|

pub fn spec_row_show(r : SpecRow) -> String {
  "\{r.name}: 認證=\{r.certified} 浮點(取樣數→答案)=\{r.floats} —— \{r.verdict}"
}

///| 對一組路徑做完整對照。
pub fn spec_row(
  name : String,
  h0 : Array[Array[Int32]],
  h1 : Array[Array[Int32]],
) -> SpecRow {
  let cert = certified_spectral_flow(h0, h1)
  let mut fl = ""
  let mut all_same = true
  let mut first = true
  let mut base = 0
  for s in [2, 3, 5, 9, 17, 65] {
    let f = float_spectral_flow(h0, h1, s)
    if first {
      base = f
      first = false
    } else if f != base {
      all_same = false
    }
    fl = "\{fl}\{s}→\{f} "
  }
  let cert_s = match cert {
    None => "不確定（端點有 λ≈0）"
    Some(v) => v.to_string()
  }
  let verdict = match cert {
    None => "認證版說「不確定」；浮點版仍給 0 或某個數字 —— 這是它最危險的地方"
    Some(v) =>
      if all_same && v == base {
        "一致，且浮點答案不隨取樣數改變"
      } else if all_same {
        "不一致：認證 \{v} vs 浮點 \{base}"
      } else {
        "浮點答案隨取樣數漂移；認證版固定為 \{v}"
      }
  }
  SpecRow::{ name, certified: cert_s, floats: fl, verdict }
}

///| 橋 20 的完整量測。
pub fn spectral_cert_probe() -> Array[String] {
  let out : Array[String] = []
  // 1. 兩條分支同時由負轉正
  out.push(spec_row_show(spec_row(
    "diag(−1,−1,1) → diag(1,1,1)",
    [[0 - 1, 0, 0], [0, 0 - 1, 0], [0, 0, 1]],
    [[1, 0, 0], [0, 1, 0], [0, 0, 1]],
  )))
  // 2. 交換：一條上去一條下來，淨譜流 0
  out.push(spec_row_show(spec_row(
    "diag(−1,1) → diag(1,−1)",
    [[0 - 1, 0], [0, 1]],
    [[1, 0], [0, 0 - 1]],
  )))
  // 3. 帶非對角項：分支本身不單調，但序號配對仍連續
  out.push(spec_row_show(spec_row(
    "[[−2,1],[1,−2]] → [[2,1],[1,2]]",
    [[0 - 2, 1], [1, 0 - 2]],
    [[2, 1], [1, 2]],
  )))
  // 4. 端點退化：t=0 有一條 λ=0 ⇒ 譜流沒定義
  out.push(spec_row_show(spec_row(
    "[[0,0],[0,−1]] → [[1,0],[0,−1]]（端點退化）",
    [[0, 0], [0, 0 - 1]],
    [[1, 0], [0, 0 - 1]],
  )))
  out.push("")
  // Witten 指標
  out.push("Witten 指標（精確秩）：")
  for (name, d) in [
    ("D: 2×3, rank 2", [[1, 0, 0], [0, 1, 0]]),
    ("D = 0 (2×3)", [[0, 0, 0], [0, 0, 0]]),
    ("D: 3×2, rank 1", [[1, 0], [0, 0], [0, 0]]),
    ("D: 2×2, rank 2", [[1, 2], [3, 4]]),
  ] {
    let idx = witten_index_exact(d)
    let n = d.length()
    let m = if n == 0 { 0 } else { d[0].length() }
    let via_spec = @spec.susy_index(@spec.susy_of(@core.mat_from_rows(d), 2147483647))
    out.push(
      "  \{name}: 指標=\{idx}（m−n=\{m - n}）與 `@spec.susy_index` 一致=\{idx == via_spec}",
    )
  }
  out.push("")
  out.push(
    "結論：譜流是一個整數，但「怎麼得到它」有兩種品質 —— 浮點取樣（參數依賴、端點退化時沉默）與精確區間認證（無參數、會說不確定）。B4 的「精確」在這裡第一次伸進 `super` 的譜",
  )
  out
}
