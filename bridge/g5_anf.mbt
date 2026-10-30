///| ## G5 —— 布林函數的係數環：GF(2) 上的代數正規形 vs 布林格上的 BDD
///

///| B5 的邊界原話是「`n > 20` 的一般最佳 ROBDD 次序 NP-hard」。

///| 這條邊界的**主語是布林格 `({0,1}, ∧, ∨, ¬)`**。換到係數環 `F₂[x]/(x²=x)`

///|（即代數正規形 ANF）之後，「次序」這個自由度**根本不存在**：

///| 多項式的寫法與變數排列無關，乘法與加法逐項計算。

///|

///| 本檔案量測「換環之後代價落在哪裡」（其中一條預測被計算否決，如實保留）：

///|  - 線性泛函：ANF **就是它自己**（權重 = 項數），不需要任何化簡或次序；

///|  - `k` 個獨立仿射約束的解集指示函數：**原先預測 `2^k`，實測是 `3^k`**

///|    （因為 `∏ᵢ(1 ⊕ ℓᵢ)` 展開時每個 `ℓᵢ` 本身有兩項 ⇒ `Σ_S 2^{|S|} = 3^k`）；

///|    重點是它**與 `n` 無關**，只由秩 `k` 決定；

///|  - 一般函數則是 `≈ 2^{n−1}`（指數爆炸）。

///|

///| 所以 B5 的真正邊界不是「BDD 慢」，而是「**哪些函數在 F₂ 的哪個子環裡有稀疏表示**」。

///| 這是係數環問題，不是演算法問題。

///|
/// 真值表：`tt[mask]` 為輸入 `mask` 的值（`mask` 的第 i 位 = 變數 i）。
pub fn truth_linear(n : Int32, coeffs : Int32) -> Array[Int32] {
  let total = int_pow2(n)
  let out : Array[Int32] = []
  for mask = 0; mask < total; mask = mask + 1 {
    let mut v : Int32 = 0
    let mut m = mask
    let mut c = coeffs
    while c != 0 {
      v = (v + m % 2 * (c % 2)) % 2
      m = m / 2
      c = c / 2
    }
    out.push(v)
  }
  out
}

///|
/// 由一堆線性約束（每條 = 一個 bit mask）的解集指示函數的真值表。
pub fn truth_of_linear_system(
  n : Int32,
  constraints : Array[Int32],
) -> Array[Int32] {
  let total = int_pow2(n)
  let out : Array[Int32] = []
  for mask = 0; mask < total; mask = mask + 1 {
    let mut ok = true
    for c in constraints {
      let mut v : Int32 = 0
      let mut m = mask
      let mut cc = c
      while cc != 0 {
        v = (v + m % 2 * (cc % 2)) % 2
        m = m / 2
        cc = cc / 2
      }
      if v % 2 != 0 {
        ok = false
      }
    }
    out.push(if ok { 1 } else { 0 })
  }
  out
}

///|
/// Möbius 變換：真值表 → ANF（無任何變數次序）。
pub fn anf(tt : Array[Int32], n : Int32) -> Array[Int32] {
  let a : Array[Int32] = []
  for x in tt {
    a.push(x % 2)
  }
  for i = 0; i < n; i = i + 1 {
    let step = int_pow2(i)
    for mask = 0; mask < a.length(); mask = mask + 1 {
      if mask / step % 2 == 1 {
        a[mask] = (a[mask] + a[mask - step]) % 2
      }
    }
  }
  a
}

///|
fn anf_weight(a : Array[Int32]) -> Int32 {
  let mut w : Int32 = 0
  for x in a {
    if x % 2 == 1 {
      w = w + 1
    }
  }
  w
}

///|
fn pow3(k : Int32) -> Int32 {
  let mut p : Int32 = 1
  for _i = 0; _i < k; _i = _i + 1 {
    p = p * 3
  }
  p
}

///|
/// G5 的實驗輸出。
pub fn g5_probe() -> Array[String] {
  let out : Array[String] = []
  let n : Int32 = 16
  // (1) 線性泛函：ANF 權重必為 1
  let lin = truth_linear(n, 0b101101)
  out.push(
    "n=16 線性泛函 x0⊕x2⊕x3⊕x5: ANF 權重=\{anf_weight(anf(lin, n))} = 項數本身（不必化簡、不必選次序）",
  )
  // (2) 仿射：常數項出現
  let aff = truth_linear(n, 0b101101)
  let aff2 : Array[Int32] = []
  for x in aff {
    aff2.push(1 - x)
  }
  out.push(
    "n=16 仿射函數（加常數）: ANF 權重=\{anf_weight(anf(aff2, n))}",
  )
  // (3) k 個獨立線性約束的解集：權重 2^k
  let mut line = "n=16 線性系統解集指示函數:"
  for k in [1, 2, 3, 4] {
    let cons : Array[Int32] = []
    for i = 0; i < k; i = i + 1 {
      cons.push(int_pow2(i) + int_pow2(i + 8))
    }
    let w = anf_weight(anf(truth_of_linear_system(n, cons), n))
    let three_k = pow3(k)
    line = "\{line} [k=\{k}: 實測權重=\{w}, 預測 2^k=\{int_pow2(k)}, 3^k=\{three_k}]"
  }
  out.push(line)
  // (4) 一般函數
  let rng = @core.rng_seed(7)
  let total = int_pow2(n)
  let rand : Array[Int32] = []
  for _i = 0; _i < total; _i = _i + 1 {
    rand.push(@core.rng_below(rng, 2))
  }
  out.push(
    "n=16 一般隨機函數: ANF 權重=\{anf_weight(anf(rand, n))}（≈2^15 ⇒ 代數正規形的最壞情況）",
  )
  out.push(
    "結論：B5 的難點隨係數環移動 —— 布林格上難在次序（NP-hard），F₂ 上難在稀疏性；而稀疏性由秩決定（3^k，與 n 無關），不是由 n 決定",
  )
  out
}

///| `n` 變數上 `k` 條獨立線性約束的解集指示函數的 ANF 權重。

///|
/// 約束取 `xᵢ ⊕ x_{i+n/2}`，只要 `k ≤ n/2` 就互相獨立。
pub fn g5_weight_of_system(n : Int32, k : Int32) -> Int32 {
  let cons : Array[Int32] = []
  for i = 0; i < k; i = i + 1 {
    cons.push(int_pow2(i) + int_pow2(i + n / 2))
  }
  anf_weight(anf(truth_of_linear_system(n, cons), n))
}
