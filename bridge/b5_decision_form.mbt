///| ## B5 —— BDD／SAT／宿主立方邊界：把「次序搜尋」換成正規形的選擇
///

///| golden SPEC §四 第五條殘餘邊界：單一無對稱不可分解稠密布林函數在 `n > 20` 時

///| 一般最佳 ROBDD 排序仍屬 NP-hard（誠實回報 `exact=false`）；

///| `5` 軸以上純黑盒閉包須提升為 `CheckedDCube`。
///

///| 合併動作（剔除 + 變化）：

///|  (a) **剔除**：`n>20` 的難處是「ROBDD 這個正規形需要選次序」。若輸入本身是

///|      線性／XOR 結構（奇偶約束），**代數正規形（ANF）不需要任何次序**：

///|      GF(2) 消元直接給秩與解，並可用 Fredholm 對偶寫出多項式大小的 UNSAT 證書。

///|      解析（resolution）在此類實例上是指數下界（Tseitin／Urquhart），

///|      DPLL 走 CNF 會撞牆，而消元不必。

///|  (b) **變化**：邊界不是被消滅，而是被**搬移**：ANF 的最壞情況是係數爆炸。

///|      於是真正的問題變成「按輸入的表示選正規形」，而那是一個可判定的元問題

///|      （若約束全為仿射 ⇒ 消元；若為一般電路 ⇒ BDD／立方）。

///|  (c) `5` 軸黑盒探針邊界：由 `CheckedDCube` 收緊的前提不變，但**證書種類**變多：

///|      秩證書（rank certificate）可以在不枚舉 2^k 個點的情況下證否。

// ---------------------------------------------------- GF(2) 線性系統 ----

///|
/// 在 F₂ 上建立關聯矩陣（每列一個頂點約束，每行一條邊）。
pub fn incidence_gf2(
  nv : Int32,
  edges : Array[(Int32, Int32)],
) -> Array[Array[Int32]] {
  let rows : Array[Array[Int32]] = []
  for _v = 0; _v < nv; _v = _v + 1 {
    rows.push(Array::make(edges.length(), 0))
  }
  for e = 0; e < edges.length(); e = e + 1 {
    let a = edges[e].0
    let b = edges[e].1
    rows[a][e] = 1
    rows[b][e] = 1
  }
  rows
}

///|
/// 一個奇偶系統的判定結果（含證書）。
pub struct ParityVerdict {
  nvars : Int32
  rank_a : Int32
  rank_aug : Int32
  satisfiable : Bool
  certificate_support : String
  certificate_ok : Bool
  solutions : Int32
}

///| [E-GF2] 判定 `A x = b`（F₂）：

///|  可解 ⟺ rank(A) = rank([A|b])；不可解時由左零空間取證書 y（Aᵀy = 0 且 y·b = 1），

///|
///  這是 Fredholm 對偶的多項式大小反證 —— 與解析證明的指數下界形成對照。
pub fn parity_decide(
  a : Array[Array[Int32]],
  b : Array[Int32],
) -> ParityVerdict {
  let fld = @core.mk_field(2)
  let nv = if a.length() > 0 { a[0].length() } else { 0 }
  let aug : Array[Array[Int32]] = []
  for i = 0; i < a.length(); i = i + 1 {
    let row : Array[Int32] = []
    for x in a[i] {
      row.push(x)
    }
    row.push(b[i])
    aug.push(row)
  }
  let ra = @core.gauss_jordan(@core.mat_from_rows(a), fld).rank
  let rb = @core.gauss_jordan(@core.mat_from_rows(aug), fld).rank
  let sat = ra == rb
  // 左零空間：ker(Aᵀ)
  let at : Array[Array[Int32]] = []
  for c = 0; c < nv; c = c + 1 {
    let row : Array[Int32] = []
    for r = 0; r < a.length(); r = r + 1 {
      row.push(a[r][c])
    }
    at.push(row)
  }
  let left = @core.nullspace_basis(@core.mat_from_rows(at), fld)
  let mut supp = ""
  let mut cert_ok = false
  if !sat {
    for y in left {
      let mut dot : Int32 = 0
      for i = 0; i < b.length(); i = i + 1 {
        dot = dot + y[i] * b[i]
      }
      if dot % 2 == 1 && !cert_ok {
        // 驗證 Aᵀy = 0 與 y·b = 1
        let mut allz = true
        let ay = @core.mat_mul_vec(@core.mat_from_rows(at), y, 2)
        for x in ay {
          if x % 2 != 0 {
            allz = false
          }
        }
        cert_ok = allz && dot % 2 == 1
        supp = support_bits(y)
      }
    }
  }
  let mut sols : Int32 = 0
  if sat {
    sols = int_pow2(nv - ra)
  }
  ParityVerdict::{
    nvars: nv,
    rank_a: ra,
    rank_aug: rb,
    satisfiable: sat,
    certificate_support: supp,
    certificate_ok: cert_ok,
    solutions: sols,
  }
}

///|
fn int_pow2(k : Int32) -> Int32 {
  let mut p : Int32 = 1
  for _i = 0; _i < k; _i = _i + 1 {
    p = p * 2
  }
  p
}

///|
fn support_bits(v : Array[Int32]) -> String {
  let mut out = "["
  let mut first = true
  for i = 0; i < v.length(); i = i + 1 {
    if v[i] % 2 != 0 {
      if !first {
        out = "\{out},"
      }
      out = "\{out}\{i}"
      first = false
    }
  }
  "\{out}]"
}

///| 12 頂點「奇偶 Tseitin」實例：每個頂點要求關聯邊之和 ≡ charge(v)，

///| 但 charge 總和為奇數 ⇒ 不可滿足。DPLL 需指數大小的解析證明；

///|
/// 消元用 1 個秩比較 + 1 個左零向量即可。
pub fn tseitin_probe() -> Array[String] {
  let out : Array[String] = []
  // 一個 12 頂點的「梯子 + 兩條交叉邊」圖（無特殊對稱）
  let edges : Array[(Int32, Int32)] = [
    (0, 1),
    (1, 2),
    (2, 3),
    (3, 4),
    (4, 5),
    (5, 6),
    (6, 7),
    (7, 8),
    (8, 9),
    (9, 10),
    (10, 11),
    (11, 0),
    (0, 6),
    (2, 8),
    (4, 10),
  ]
  let nv : Int32 = 12
  let a = incidence_gf2(nv, edges)
  let b0 : Array[Int32] = Array::make(nv, 0)
  let b_odd = Array::make(nv, 0)
  b_odd[0] = 1
  let v_ok = parity_decide(a, b0)
  let v_bad = parity_decide(a, b_odd)
  out.push(
    "Tseitin 12 頂點/15 邊: 一致電荷 ⇒ sat=\{v_ok.satisfiable} 解數=2^\{v_ok.nvars - v_ok.rank_a}；奇電荷 ⇒ sat=\{v_bad.satisfiable} 證書 y 支撐=\{v_bad.certificate_support} 驗證=\{v_bad.certificate_ok}",
  )
  out.push(
    "秩證書大小 = O(#邊) 位元；解析（resolution）對 Tseitin 圖族為指數下界 ⇒ 「表示選擇」本身就是能力邊界的位移",
  )
  out
}

// ------------------------------------------------------------- ANF ----

///|
/// [E-Mobius] 由 2^n 真值表求 ANF（Möbius／zeta 變換）：O(n·2^n)，**不需任何變量次序**。
pub fn anf_of_truth(tt : Array[Int32], n : Int32) -> Array[Int32] {
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
/// 由 ANF 求回真值表（往返檢查：ANF 是無次序的典範形）。
pub fn truth_of_anf(anf : Array[Int32], n : Int32) -> Array[Int32] {
  let a : Array[Int32] = []
  for x in anf {
    a.push(x % 2)
  }
  let total = int_pow2(n)
  let out = Array::make(total, 0)
  for mask = 0; mask < total; mask = mask + 1 {
    let mut v : Int32 = 0
    for m = 0; m < total; m = m + 1 {
      if a[m] % 2 == 1 && (m & mask) == m {
        v = (v + 1) % 2
      }
    }
    out[mask] = v
  }
  out
}

///|
/// ANF 探針：n 變量隨機布林函數，量測 ANF 權重（= 無次序典範形的大小）。
pub fn anf_probe(n : Int32) -> Array[String] {
  let out : Array[String] = []
  let total = int_pow2(n)
  let rng = @core.rng_seed(4242)
  let tt : Array[Int32] = []
  for _i = 0; _i < total; _i = _i + 1 {
    tt.push(@core.rng_below(rng, 2))
  }
  let anf = anf_of_truth(tt, n)
  let mut w : Int32 = 0
  for x in anf {
    if x % 2 == 1 {
      w = w + 1
    }
  }
  let back = truth_of_anf(anf, n)
  let mut same = true
  for i = 0; i < total; i = i + 1 {
    if back[i] % 2 != tt[i] % 2 {
      same = false
    }
  }
  out.push(
    "ANF n=\{n}: 真值表 2^\{n}=\{total} 點 → ANF 單項數=\{w}（約一半，典型）；往返一致=\{same}；決策等價 = 支持集相等，**變量次序搜尋 = 0**",
  )
  out
}

///|
/// B5 的實驗輸出。
pub fn b5_probe() -> Array[String] {
  let out = tseitin_probe()
  for s in anf_probe(16) {
    out.push(s)
  }
  out.push(
    "邊界搬移：BDD 之難在次序（NP-hard），ANF 之難在係數爆炸（另一種最壞情況）⇒ 合併後的邊界是「表示選擇」而非「單一正規形的最壞情況」",
  )
  out
}
