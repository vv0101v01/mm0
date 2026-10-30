///| ## Hopf 不變量的代數阻礙（殘餘 1 的核心）
///
///| 假設存在 `f: S^{2n−1} → S^n` 且 Hopf 不變量為奇數。它的餘纖維
///| `X = S^n ∪_f e^{2n}` 只有三個胞腔（維度 `0, n, 2n`），于是：
///
///|  - `H^n(X;F₂) = F₂⟨x⟩`、`H^{2n}(X;F₂) = F₂⟨x²⟩`；
///|  - Steenrod 的定理 `Sq^{|x|}(x) = x²` 給出 `Sq^n x = x²`；
///|  - 但對 `0 < i < n`，`Sq^i x ∈ H^{n+i}(X) = 0`（中間沒有胞腔）。
///
///| 把 Adem 關係 `Sq^a Sq^b = Σ_j C(b−1−j, a−2j) Sq^{a+b−j} Sq^j`（`a < 2b`）
///| 用在 `x` 上：只要存在 `a ≥ 1`、`a + b = n`、`a < 2b` 使 `C(b−1, a)` 為奇數，
///| 左邊 `Sq^a(Sq^b x) = 0`（因為 `0 < b < n`），右邊的 `j = 0` 項卻是 `x²` —— 矛盾。
///
///| **本檔案把這個判據全算了**，並如實報告它在哪裡失效：
///| 判據通過 ⟺ `n` 是 `2` 的冪。所以一次阻礙證明了所有「非 2 的冪」都不可能；
///| 剩下的 `n = 16, 32, 64, …` 需要 Adams 的二次操作。**這就是殘餘的準確座標。**

///| 二項係數 `C(n, k) mod 2`（Lucas 定理：逐位元的 AND）。
pub fn binom_mod2(n : Int32, k : Int32) -> Int32 {
  if k < 0 || k > n {
    return 0
  }
  // C(n,k) 為奇 ⟺ (k & n) == k
  if (k & n) == k {
    1
  } else {
    0
  }
}

///| 一次阻礙在維度 `n` 是否**消失**（= 沒有矛盾 ⇒ 允許 Hopf 不變量 1）。
///| 回傳第一個「殺死」它的 Adem 關係的 `(a, b)`（沒有則 `None`）。
pub fn primary_obstruction(n : Int32) -> (Int32, Int32)? {
  for a = 1; a < n; a = a + 1 {
    let b = n - a
    if a < 2 * b && b >= 1 && binom_mod2(b - 1, a) == 1 {
      return Some((a, b))
    }
  }
  None
}

///| 是否為 2 的冪。
pub fn is_pow2(n : Int32) -> Bool {
  n >= 1 && (n & (n - 1)) == 0
}

///| 一張 `n = 2..33` 的表：一次阻礙是否消失、是否 2 的冪、是否真的存在（`1,2,4,8`）。
pub fn steenrod_probe() -> Array[String] {
  let out : Array[String] = []
  let mut ok_list = ""
  let mut blocked_list = ""
  for n = 2; n <= 33; n = n + 1 {
    match primary_obstruction(n) {
      Some(ab) => {
        if blocked_list.length() < 90 {
          blocked_list = "\{blocked_list} \{n}(Sq^\{ab.0}Sq^\{ab.1})"
        }
      }
      None => {
        ok_list = "\{ok_list} \{n}"
      }
    }
  }
  out.push("一次阻礙通過（未被 Adem 關係殺死）的維度: \{ok_list}")
  out.push("一次阻礙殺死的維度（括號為見證的 Adem 關係）: \{blocked_list} …")
  // 判據與「2 的冪」的等價性：0..33 全掃
  let mut agree = true
  for n = 2; n <= 200; n = n + 1 {
    let pass = match primary_obstruction(n) {
      Some(_) => false
      None => true
    }
    if pass != is_pow2(n) {
      agree = false
    }
  }
  out.push("判據「一次阻礙通過 ⟺ n 是 2 的冪」在 n = 2..200 上全等: \{agree}")
  out.push(
    "真正存在 Hopf 不變量 1 的維度只有 n = 1, 2, 4, 8（Adams；對應 ℝ/ℂ/ℍ/𝕆）——一次阻礙在 16, 32, … 上失效，那正是 Adams 二次操作要補的洞",
  )
  out
}
