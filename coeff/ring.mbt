///| # `coeff` —— 係數環作為一等公民
///

///| 這一輪的核心論斷（來自上一輪的診斷）：

///| **B4（精確代數）與 B6（球面同倫）的真正障礙不是算力，是係數環。**

///| 有理係數對撓率全盲（`H₁(RP²;ℚ)=0`），所以任何以 ℚ 為中心的認證系統

///| 都看不見 `ℤ/2`、`ℤ/3` 這些離散阻礙。
///

///| 本套件把「用哪個環算」升成一個可傳遞的參數 `Coeff`，並保證：

///|  1. 每個環用**互不相干的演算法**計算（ℚ 用精確有理秩、ℤ 用 Smith 標準形、

///|     `F_p` 用模 p 高斯消元），因此彼此的吻合是**交叉驗證**而不是同義反覆；

///|  2. 係數變換由**萬有係數定理**（UCT）給出，並用第 1 條的三條獨立路徑反查；

///|  3. `0 → ℤ/p → ℤ/p² → ℤ/p → 0` 的連接映射（Bockstein）用「提升到 ℤ/p² 再除 p」

///|     直接算出，因此撓率的**階**可被看見，而不是只有秩。

///|
/// 係數環。
pub enum Coeff {
  CZ
  CQ
  CFp(Int32)
  CZm(Int32)
}

///|
pub fn coeff_show(c : Coeff) -> String {
  match c {
    CZ => "Z"
    CQ => "Q"
    CFp(p) => "F_\{p}"
    CZm(m) => "Z/\{m}"
  }
}

///|
/// 是否為域（域上「秩 ⇒ 可解」成立；非域不成立——本倉庫踩過 ℤ/4 的坑）。
pub fn coeff_is_field(c : Coeff) -> Bool {
  match c {
    CZ => false
    CQ => true
    CFp(p) => @core.is_prime(p)
    CZm(m) => m == 2 || m == 3 || m == 5 || m == 7 || m == 11
  }
}

// ------------------------------------------------------------ 有限生成交換群 --

///|
/// `ℤ^free ⊕ ℤ/d₁ ⊕ …`（`dᵢ > 1`，升序）。
pub struct Ab {
  free : Int32
  tors : Array[Int32]
}

///|
/// 正規化：丟掉 1、升序排列（≡ 同構類的典範表示）。
pub fn ab_make(free : Int32, tors : Array[Int32]) -> Ab {
  let keep : Array[Int32] = []
  for d in tors {
    if d > 1 {
      keep.push(d)
    }
  }
  for i = 1; i < keep.length(); i = i + 1 {
    let key = keep[i]
    let mut j = i - 1
    while j >= 0 && keep[j] > key {
      keep[j + 1] = keep[j]
      j = j - 1
    }
    keep[j + 1] = key
  }
  Ab::{ free, tors: keep, }
}

///|
pub fn ab_show(a : Ab) -> String {
  let mut out = if a.free == 0 {
    ""
  } else if a.free == 1 {
    "Z"
  } else {
    "Z^\{a.free}"
  }
  for d in a.tors {
    out = if out == "" { "Z/\{d}" } else { "\{out}+Z/\{d}" }
  }
  if out == "" {
    "0"
  } else {
    out
  }
}

///|
pub fn ab_eq(a : Ab, b : Ab) -> Bool {
  if a.free != b.free || a.tors.length() != b.tors.length() {
    return false
  }
  for i = 0; i < a.tors.length(); i = i + 1 {
    if a.tors[i] != b.tors[i] {
      return false
    }
  }
  true
}

///|
/// 依係數環顯示（`ℤ/m` 時自由部分印成 `(ℤ/m)^k`，避免與 `ℤ` 混淆）。
pub fn ab_show_ring(a : Ab, c : Coeff) -> String {
  match c {
    CZm(m) =>
      if a.tors.length() == 0 && a.free == 0 {
        "0"
      } else {
        let mut out = if a.free == 0 {
          ""
        } else if a.free == 1 {
          "(Z/\{m})"
        } else {
          "(Z/\{m})^\{a.free}"
        }
        for d in a.tors {
          out = if out == "" { "Z/\{d}" } else { "\{out}+Z/\{d}" }
        }
        out
      }
    _ => ab_show(a)
  }
}

///|
/// `dim_{F_p}(A ⊗ F_p)`
pub fn ab_dim_tensor_fp(a : Ab, p : Int32) -> Int32 {
  let mut d = a.free
  for x in a.tors {
    if x % p == 0 {
      d = d + 1
    }
  }
  d
}

///|
/// `dim_{F_p} Tor(A, F_p)`
pub fn ab_dim_tor_fp(a : Ab, p : Int32) -> Int32 {
  let mut d : Int32 = 0
  for x in a.tors {
    if x % p == 0 {
      d = d + 1
    }
  }
  d
}

///| `A ⊗ ℤ/m` 中 **`ℤ/m` 直和項**的個數（只來自自由部分：`ℤ ⊗ ℤ/m = ℤ/m`）。
///|
/// `ℤ/x ⊗ ℤ/m = ℤ/gcd(x,m)` 的撓率項清單（去掉平凡的 1）。
pub fn ab_tensor_torsion_zm(a : Ab, m : Int32) -> Array[Int32] {
  let out : Array[Int32] = []
  for x in a.tors {
    let g = @core.igcd(x, m)
    if g > 1 {
      out.push(g)
    }
  }
  out
}

///|
/// `Tor(ℤ/x, ℤ/m) = ℤ/gcd(x,m)`；`Tor(ℤ, ℤ/m) = 0`。
pub fn ab_tor_torsion_zm(a : Ab, m : Int32) -> Array[Int32] {
  ab_tensor_torsion_zm(a, m)
}

///| UCT 的兩個直和項合成：

///| `H_k(C;ℤ/m) ≅ (H_k ⊗ ℤ/m) ⊕ Tor(H_{k−1}, ℤ/m)`。

///|
/// 回傳的 `Ab` 中 `free` 欄位代表 **`ℤ/m` 的拷貝數**（見 `homology_zm` 的說明）。
pub fn ab_uct(a : Ab, prev : Ab?, m : Int32) -> Ab {
  let tors : Array[Int32] = ab_tensor_torsion_zm(a, m)
  match prev {
    Some(pr) =>
      for d in ab_tor_torsion_zm(pr, m) {
        tors.push(d)
      }
    None => ()
  }
  ab_make(a.free, tors)
}
