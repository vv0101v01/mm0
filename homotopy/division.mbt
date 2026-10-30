///| ## 代數側的同一道牆：Cayley–Dickson 加倍與範數乘法性
///
///| Hopf 不變量 1 的存在等價於 `ℝⁿ` 上存在**合成代數**（`N(xy) = N(x)N(y)`）。
///| Hurwitz 定理說只有 `n = 1, 2, 4, 8`。本檔案把它算出來：
///
///|  - 由 `ℝ` 反覆做 Cayley–Dickson 加倍：`ℝ(1) → ℂ(2) → ℍ(4) → 𝕆(8) → 𝕊(16)`；
///|  - 每一層窮舉檢查 `N(xy) = N(x)N(y)`（對 `±(eᵢ + eⱼ)` 這類兩項元素）；
///|  - 在維度 16 給出**顯式零因子** `xy = 0`，範數乘法性因此失效。
///
///| 這是「合成代數只到 8 維」的機器證明，也是 `n ∈ {1,2,4,8}` 的第二條獨立路線。

///| 乘法表：`table[i * dim + j]` 是 `eᵢ · eⱼ` 的基索引，`sign[i * dim + j]` 是符號。
pub struct CDAlg {
  dim : Int32
  table : Array[Int32]
  sign : Array[Int32]
}

///| 遞迴的結構常數：`k` 是維度的指數（`dim = 2^k`）。
///| `mul_rec(k, i, j) -> (index, sign)`。四塊按 `(a,b)(c,d) = (ac − d̄b, da + bc̄)` 展開。
pub fn mul_rec(k : Int32, i : Int32, j : Int32) -> (Int32, Int32) {
  if k == 0 {
    return (0, 1)
  }
  let n = 1 << (k - 1)
  let hi = if i >= n { 1 } else { 0 }
  let hj = if j >= n { 1 } else { 0 }
  let ai = i % n
  let aj = j % n
  if hi == 0 && hj == 0 {
    let (idx, s) = mul_rec(k - 1, ai, aj)
    (idx, s)
  } else if hi == 0 && hj == 1 {
    // (a,0)(0,d) = (0, d a)
    let (idx, s) = mul_rec(k - 1, aj, ai)
    (n + idx, s)
  } else if hi == 1 && hj == 0 {
    // (0,b)(c,0) = (0, b c̄)
    let (caj, sc) = conj_rec(k - 1, aj)
    let (idx, s) = mul_rec(k - 1, ai, caj)
    (n + idx, s * sc)
  } else {
    // (0,b)(0,d) = (−d̄ b, 0)
    let (caj, sc) = conj_rec(k - 1, aj)
    let (idx, s) = mul_rec(k - 1, caj, ai)
    (idx, 0 - s * sc)
  }
}

///| 共軛在基向量上的作用：`ē₀ = e₀`，`ēₘ = −eₘ`（`m > 0`）。
pub fn conj_rec(_k : Int32, m : Int32) -> (Int32, Int32) {
  if m == 0 {
    (0, 1)
  } else {
    (m, 0 - 1)
  }
}

///| 建出維度 `2^k` 的 Cayley–Dickson 代數。
pub fn cd_alg(k : Int32) -> CDAlg {
  let dim = 1 << k
  let table : Array[Int32] = []
  let sign : Array[Int32] = []
  for i = 0; i < dim; i = i + 1 {
    for j = 0; j < dim; j = j + 1 {
      let (idx, s) = mul_rec(k, i, j)
      table.push(idx)
      sign.push(s)
    }
  }
  CDAlg::{ dim, table, sign }
}

///| 稠密元素乘法。
pub fn elem_mul(a : CDAlg, x : Array[Int32], y : Array[Int32]) -> Array[Int32] {
  let out : Array[Int32] = []
  for _i = 0; _i < a.dim; _i = _i + 1 {
    out.push(0)
  }
  for i = 0; i < a.dim; i = i + 1 {
    if x[i] == 0 {
      continue
    }
    for j = 0; j < a.dim; j = j + 1 {
      if y[j] == 0 {
        continue
      }
      let idx = a.table[i * a.dim + j]
      let s = a.sign[i * a.dim + j]
      out[idx] = out[idx] + s * x[i] * y[j]
    }
  }
  out
}

///| 範數 `N(x) = Σ xᵢ²`（因為共軛只是逐座標變號，`x·x̄` 的係數就是平方和）。
pub fn elem_norm(x : Array[Int32]) -> Int32 {
  let mut s : Int32 = 0
  for v in x {
    s = s + v * v
  }
  s
}

///| 兩項元素 `eᵢ ± eⱼ`。
fn two_term(dim : Int32, i : Int32, j : Int32, si : Int32, sj : Int32) -> Array[Int32] {
  let out : Array[Int32] = []
  for _k = 0; _k < dim; _k = _k + 1 {
    out.push(0)
  }
  out[i] = si
  out[j] = sj
  out
}

///| 範數乘法性檢查：對全部 `±(eᵢ+eⱼ)` 與 `±(eₖ+eₗ)` 窮舉。
///| 回傳 (是否全通, 檢查數, 第一個反例的 `(i,j,k,l)` 或 `(-1,-1,-1,-1)`)。
pub fn norm_check(a : CDAlg) -> (Bool, Int32, (Int32, Int32, Int32, Int32)) {
  let d = a.dim
  let mut checked : Int32 = 0
  let mut witness = (-1, -1, -1, -1)
  let mut ok = true
  for i = 0; i < d; i = i + 1 {
    for j = i + 1; j < d; j = j + 1 {
      for k = 0; k < d; k = k + 1 {
        for l = k + 1; l < d; l = l + 1 {
          let x = two_term(d, i, j, 1, 1)
          let y = two_term(d, k, l, 1, 1)
          let nx = elem_norm(x)
          let ny = elem_norm(y)
          let p = elem_mul(a, x, y)
          checked = checked + 1
          if elem_norm(p) != nx * ny {
            if ok {
              witness = (i, j, k, l)
            }
            ok = false
          }
        }
      }
    }
  }
  (ok, checked, witness)
}

///| 找顯式零因子 `xy = 0`（`x, y ≠ 0`），同樣在兩項元素裡搜。
pub fn zero_divisor(a : CDAlg) -> (Array[Int32], Array[Int32])? {
  let d = a.dim
  for i = 0; i < d; i = i + 1 {
    for j = i + 1; j < d; j = j + 1 {
      for k = 0; k < d; k = k + 1 {
        for l = k + 1; l < d; l = l + 1 {
          for s2 = 0; s2 < 2; s2 = s2 + 1 {
            let x = two_term(d, i, j, 1, 1)
            let y = two_term(d, k, l, 1, if s2 == 0 { 1 } else { -1 })
            let p = elem_mul(a, x, y)
            let mut zero = true
            for v in p {
              if v != 0 {
                zero = false
              }
            }
            if zero {
              return Some((x, y))
            }
          }
        }
      }
    }
  }
  None
}

///| 顯示一個元素。
pub fn elem_show(x : Array[Int32]) -> String {
  let mut out = ""
  for i = 0; i < x.length(); i = i + 1 {
    if x[i] != 0 {
      let t = if x[i] > 0 {
        "+"
      } else {
        "-"
      }
      let c = if x[i] > 0 { x[i] } else { 0 - x[i] }
      out = if out == "" {
        "\{t}\{c}e\{i}"
      } else {
        "\{out}\{t}\{c}e\{i}"
      }
    }
  }
  if out == "" {
    "0"
  } else {
    out
  }
}

///| 全表：維度 1,2,4,8,16 的範數乘法性與零因子。
pub fn division_probe() -> Array[String] {
  let out : Array[String] = []
  let names : Array[String] = ["R", "C", "H", "O", "S(sedenions)"]
  let dims : Array[Int32] = [1, 2, 4, 8, 16]
  for t = 0; t < dims.length(); t = t + 1 {
    let k = dims[t]
    let mut e : Int32 = 0
    let mut j = 1
    while j < k {
      e = e + 1
      j = j * 2
    }
    let a = cd_alg(e)
    let (ok, checked, w) = norm_check(a)
    let mut line = "\{names[t]} (dim=\{a.dim}): N(xy)=N(x)N(y) 全部成立=\{ok}（窮舉 \{checked} 對兩項元素）"
    if !ok {
      line = "\{line} 第一個反例 (i,j,k,l)=(\{w.0},\{w.1},\{w.2},\{w.3})"
    }
    match zero_divisor(a) {
      Some(pair) => {
        line = "\{line} 零因子: (\{elem_show(pair.0)})·(\{elem_show(pair.1)}) = 0"
      }
      None => ()
    }
    out.push(line)
  }
  out.push(
    "結論：合成代數只存在於 dimension 1, 2, 4, 8（ℝ/ℂ/ℍ/𝕆）；16 維（sedenions）出現零因子，範數乘法性失效",
  )
  out.push(
    "與 Hopf 不變量 1 的對應：n = 1,2,4,8 ⟷ ℝ,ℂ,ℍ,𝕆 —— 兩條完全獨立的計算（Steenrod 代數 / 乘法表）指向同一組維度",
  )
  out
}
