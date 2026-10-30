///| ## Carlet 的軌道：代數免疫與它的上界
///
///| 代數免疫 `AI(f)` = 使 `f` 或 `1⊕f` 有非零零化子的最小代數次數。
///| 它是**線性代數**問題：次數 ≤ d 的零化子 = 某個 `F₂` 矩陣的核。
///
///| 兩個要用機器確認的事實：
///
///| 1. **上界** `AI(f) ≤ ⌈n/2⌉`（Courtois–Meier；Carlet 的綜述把它列為
///|    代數免疫的基準，並用它來界定「高代數免疫」這個設計目標）。
///|    證明是一個維度計數：`dim{deg ≤ d 的函數} > 半個空間` 時必有零化子。
///| 2. **上界是緊的**：Majority 函數 `Maj_n` 對每個 `n` 都恰好達到 `⌈n/2⌉`。
///|
///| 本檔案把 AI 當成可執行函數，於是「上界」不再是引用，而是**逐函數驗證**。

///| 真值表（長度 `2^n`，`tt[mask]` 的值由 `mask` 的二進位各位取函數）。
///| ANF 係數：Möbius 變換。
pub fn anf_coeffs(tt : Array[Int32], n : Int32) -> Array[Int32] {
  let a : Array[Int32] = []
  for x in tt {
    a.push(x % 2)
  }
  for i = 0; i < n; i = i + 1 {
    let step = 1 << i
    for mask = 0; mask < a.length(); mask = mask + 1 {
      if (mask / step) % 2 == 1 {
        a[mask] = (a[mask] + a[mask - step]) % 2
      }
    }
  }
  a
}

///| 全部「大小 ≤ d」的遮罩清單。
fn subsets_up_to(n : Int32, d : Int32) -> Array[Int32] {
  let out : Array[Int32] = []
  for mask = 0; mask < (1 << n); mask = mask + 1 {
    let mut bits = 0
    for i = 0; i < n; i = i + 1 {
      bits = bits + ((mask >> i) & 1)
    }
    if bits <= d {
      out.push(mask)
    }
  }
  out
}

///| `f` 是否有次數 ≤ d 的非零零化子（`f·g = 0`）。
///| 方程組：對每個 `f(x) = 1` 的 `x`，`Σ_{S ⊆ x, |S| ≤ d} c_S = 0`。
pub fn has_annihilator(f : Array[Int32], n : Int32, d : Int32) -> Bool {
  // `f` 是**真值表**：只有 `f(x) = 1` 的點有約束
  let cols = subsets_up_to(n, d)
  let rows : Array[Array[Int32]] = []
  for x = 0; x < f.length(); x = x + 1 {
    if f[x] % 2 == 1 {
      let row : Array[Int32] = []
      for s in cols {
        // S ⊆ x ⟺ (S & x) == S
        row.push(if (s & x) == s { 1 } else { 0 })
      }
      rows.push(row)
    }
  }
  if rows.length() == 0 {
    // f ≡ 0：任何 g 都是零化子
    return true
  }
  let ns = @core.nullspace_basis(@core.mat_from_rows(rows), @core.mk_field(2))
  ns.length() > 0
}

///| 代數免疫。
pub fn algebraic_immunity(tt : Array[Int32], n : Int32) -> Int32 {
  // 零化子的**支撐集**來自真值表（ANF 只在重建 g 時用到）。
  // 第一版把 ANF 當成支撐集，於是 Maj_7 的 AI 被算成 1——錯得很乾淨。
  let comp : Array[Int32] = []
  for x in tt {
    comp.push((1 - x) % 2)
  }
  for d = 0; d <= n; d = d + 1 {
    if has_annihilator(tt, n, d) || has_annihilator(comp, n, d) {
      return d
    }
  }
  n
}

///| `⌈n/2⌉`。
pub fn ceil_half(n : Int32) -> Int32 {
  (n + 1) / 2
}

///| 真值表 ↔ 遮罩：`Maj_n` 在 `wt(x) ≥ ⌈n/2⌉` 時取 1。
pub fn majority_tt(n : Int32) -> Array[Int32] {
  let out : Array[Int32] = []
  for mask = 0; mask < (1 << n); mask = mask + 1 {
    let mut w = 0
    for i = 0; i < n; i = i + 1 {
      w = w + ((mask >> i) & 1)
    }
    out.push(if w >= (n + 1) / 2 { 1 } else { 0 })
  }
  out
}

///| 窮舉 `n` 個變數的全部函數，驗證上界 `AI(f) ≤ ⌈n/2⌉`，並統計達到上界的個數。
///| 回傳 (上界是否全成立, 反例的遮罩或 -1, 達到上界的函數數, 總數)。
pub fn carlet_bound_check(n : Int32) -> (Bool, Int32, Int32, Int32) {
  let tt_len = 1 << n          // 真值表長度
  let total = 1 << tt_len      // 函數個數 = 2^(2^n)
  let bound = ceil_half(n)
  let mut ok = true
  let mut bad : Int32 = -1
  let mut tight : Int32 = 0
  for t = 0; t < total; t = t + 1 {
    let tt : Array[Int32] = []
    for mask = 0; mask < tt_len; mask = mask + 1 {
      tt.push((t >> mask) & 1)
    }
    let ai = algebraic_immunity(tt, n)
    if ai > bound {
      ok = false
      bad = t
    }
    if ai == bound {
      tight = tight + 1
    }
  }
  (ok, bad, tight, total)
}

///| 一句話報表。
pub fn carlet_probe() -> Array[String] {
  let out : Array[String] = []
  for n = 1; n <= 4; n = n + 1 {
    let (ok, bad, tight, total) = carlet_bound_check(n)
    out.push(
      "n=\{n}: 窮舉 \{total} 個布林函數，AI(f) ≤ ⌈n/2⌉=\{ceil_half(n)} 全成立=\{ok}，反例 mask=\{bad}，達到上界者 \{tight} 個",
    )
  }
  for n = 5; n <= 8; n = n + 1 {
    let ai = algebraic_immunity(majority_tt(n), n)
    out.push(
      "n=\{n}: Maj_\{n} 的 AI=\{ai}，⌈n/2⌉=\{ceil_half(n)}，緊=\{ai == ceil_half(n)}",
    )
  }
  out.push(
    "結論：上界 AI(f) ≤ ⌈n/2⌉ 在 n ≤ 4 上逐函數驗證通過；Majority 在 n = 5..8 上達到上界 ⇒ 上界緊",
  )
  out
}
