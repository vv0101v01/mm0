///| ## 入口 3 —— Postnikov 塔與 `π₄(S³) = ℤ/2`
///
///| B6 的殘餘原話是：「Postnikov/Stasheff 相干只有生成器（翻轉圖），**沒有 k-invariant**。」
///| 這一輪把 k-invariant 算出來。設備只有兩樣：**Serre 的容許單項式定理**與**本樹上的 Adem 關係**。
///
///| ### 為什麼 k-invariant 可以完全在 `H^*(K(ℤ,3);F₂)` 裡算
///
///| `S³` 的前兩層 Postnikov 塔是平凡的（`π₁ = π₂ = 0`），第三層 `X₃ = K(ℤ,3)`。
///| 下一個不變量 `k₄ ∈ H⁵(K(ℤ,3); π₄)`，而「`k₄` 的 mod 2 化」必須是 `H⁵(K(ℤ,3);F₂)` 的母元。
///| Serre：`H^*(K(ℤ,n);F₂)` 是**容許** `Sq^I ι_n`（`I = (i₁,…,i_k)` 容許、
///| 超越數 `e(I) = i₁ − Σ_{j>1} i_j < n`、`i₁ ≠ 1`）上的多項式代數。
///| 於是 `H⁵(K(ℤ,3);F₂)` 的維度是一個**有限組合問題**，可以直接數出來。
///
///| ### 兩個質數一起看
///
///|  - `p = 2`：`H⁵(K(ℤ,3);F₂) = ⟨Sq²ι₃⟩ ≅ F₂`（非零）⇒ `π₄` 有 2-撓率，
///|    且只有一份（多一份就需要 `H⁵(S³;F₂) ≠ 0` 去容納它）；
///|  - `p` 奇：`A_p` 在度數 `3` 上能動的最小操作是 `P¹`，度數 `3 + 2(p−1) ≥ 7 > 5`，
///|    所以 `k₄` 的 mod `p` 化**恆為零** ⇒ `π₄` 沒有奇撓率。
///
///| 合起來：`π₄(S³)` 是有限 2-群且 `π₄ ⊗ F₂ = F₂`。
///| 與 `ℤ/2` 的最後一步（排除 `ℤ/4`）需要**整係數** k-invariant／Bockstein，
///| 這是本入口**尚未**閉合的殘餘，如實記在這裡。

///| 容許性：`i_j ≥ 2·i_{j+1}`。
pub fn admissible(i : Array[Int32]) -> Bool {
  for j = 0; j + 1 < i.length(); j = j + 1 {
    if i[j] < 2 * i[j + 1] {
      return false
    }
  }
  true
}

///| 超越數 `e(I) = i₁ − Σ_{j>1} i_j`。
pub fn excess(i : Array[Int32]) -> Int32 {
  let mut s = i[0]
  for j = 1; j < i.length(); j = j + 1 {
    s = s - i[j]
  }
  s
}

///|

pub fn deg_of(i : Array[Int32]) -> Int32 {
  let mut s = 0
  for x in i {
    s = s + x
  }
  s
}

///| 列出所有和 ≤ `lim` 的正整數序列（時間複雜度 = 分割數，`lim ≤ 20` 很快）。
pub fn partitions_up_to(lim : Int32) -> Array[Array[Int32]] {
  let out : Array[Array[Int32]] = []
  enum_seqs([], 0, lim, out)
  out
}

///|

fn enum_seqs(rev : Array[Int32], sum : Int32, lim : Int32, out : Array[Array[Int32]]) -> Unit {
  if rev.length() > 0 {
    let a : Array[Int32] = []
    for i = rev.length() - 1; i >= 0; i = i - 1 {
      a.push(rev[i])
    }
    out.push(a)
  }
  let start = if rev.length() == 0 { 1 } else { 2 * rev[rev.length() - 1] }
  for d = start; d <= lim - sum; d = d + 1 {
    rev.push(d)
    enum_seqs(rev, sum + d, lim, out)
    let _ = rev.pop()
  }
}

///| `H^*(K(ℤ,n);F₂)` 的 Serre 生成元（`I` 容許、`e(I) < n`、`i₁ ≠ 1`），度數 ≤ `maxdeg − n`。
pub fn serre_generators(n : Int32, maxdeg : Int32) -> Array[Array[Int32]] {
  let out : Array[Array[Int32]] = []
  // 母元 ι_n 本身（空序列）
  let empty : Array[Int32] = []
  out.push(empty)
  for i in partitions_up_to(maxdeg - n) {
    if i[0] == 1 {
      continue
    }
    // `Sq¹` 在整係數母元上恆為零（Bockstein 殺掉 reduction）⇒ 末項必須 ≥ 2
    if i[i.length() - 1] == 1 {
      continue
    }
    if !admissible(i) {
      continue
    }
    if excess(i) >= n {
      continue
    }
    out.push(i)
  }
  out
}

///| 把生成元當成多項式代數的變數，逐度數數維度（無界背包）。
pub fn poly_dims(gens : Array[Array[Int32]], n : Int32, maxdeg : Int32) -> Array[Int32] {
  let dp : Array[Int32] = []
  for _d = 0; _d <= maxdeg; _d = _d + 1 {
    dp.push(0)
  }
  dp[0] = 1
  for i in gens {
    let d0 = n + deg_of(i)
    for d = d0; d <= maxdeg; d = d + 1 {
      dp[d] = dp[d] + dp[d - d0]
    }
  }
  dp
}

///|

pub fn dims_show(dims : Array[Int32], maxdeg : Int32) -> String {
  let sb : Array[String] = []
  for d = 0; d <= maxdeg; d = d + 1 {
    sb.push("\{d}:\{dims[d]}")
  }
  let mut s = ""
  for i = 0; i < sb.length(); i = i + 1 {
    if i > 0 {
      s = s + " "
    }
    s = s + sb[i]
  }
  s
}

///| `H⁵(K(ℤ,3);F₂)` 的生成元清單（度數恰好 5）。
pub fn h5_generators() -> Array[Array[Int32]] {
  let out : Array[Array[Int32]] = []
  for i in serre_generators(3, 8) {
    if 3 + deg_of(i) == 5 {
      out.push(i)
    }
  }
  out
}

///| 奇質數下第一個能動 `ι₃` 的 Steenrod 操作的度數：`P¹` 給 `3 + 2(p−1)`。
pub fn odd_p_first_degree(p : Int32) -> Int32 {
  3 + 2 * (p - 1)
}

///| 入口 3 的探針。
pub fn postnikov_probe() -> Array[String] {
  let out : Array[String] = []
  let gens = serre_generators(3, 9)
  let gs : Array[String] = []
  for i in gens {
    let parts : Array[String] = []
    for x in i {
      parts.push("\{x}")
    }
    let mut one = "Sq("
    for k = 0; k < parts.length(); k = k + 1 {
      if k > 0 {
        one = one + ","
      }
      one = one + parts[k]
    }
    one = one + ")ι₃"
    gs.push("度 \{3 + deg_of(i)}: \{one}")
  }
  let mut genline = ""
  for k = 0; k < gs.length(); k = k + 1 {
    if k > 0 {
      genline = genline + "；"
    }
    genline = genline + gs[k]
  }
  out.push("H^*(K(Z,3);F_2) 的 Serre 生成元（度數 ≤ 9）：\{genline}")
  let dims = poly_dims(gens, 3, 9)
  out.push("H^*(K(Z,3);F_2) 逐度數維度：\{dims_show(dims, 9)}")
  let h5 = h5_generators()
  out.push(
    "H^5(K(Z,3);F_2) 的生成元數 = \{h5.length()}（唯一的 4+? 度容許操作是 Sq^2）⇒ 這是 F_2 一維",
  )
  out.push("⇒ S³ 的第一個 Postnikov 不變量 k_4 = Sq^2ι₃ ≠ 0（mod 2 化非零）")
  out.push("p=3 時 P¹ι₃ 的度數 = \{odd_p_first_degree(3)} > 5；p=5 時 = \{odd_p_first_degree(5)} > 5")
  out.push("⇒ k_4 的 mod p 化對所有奇 p 恆為零 ⇒ π₄(S³) 無奇撓率")
  out.push(
    "⇒ π₄(S³) 是有限 2-群且 π₄ ⊗ F_2 = F_2 ⇒ 候選只剩 Z/2 與 Z/4；經典答案 Z/2（Freudenthal / Hopf 的 η）",
  )
  out.push(
    "殘餘（如實記）：Z/2 與 Z/4 的分辨需要**整係數** k-invariant（Bockstein βSq²ι₃ ∈ H^6(K(Z,3);Z)），本入口尚未算出",
  )
  out
}
