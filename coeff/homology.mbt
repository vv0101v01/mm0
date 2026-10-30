///| ## 同調：同一個複形，四種係數環，三種獨立演算法
///

///| 這是本套件的核心表。任何一行都可以用 `moon test` 重跑：
///

///|  - `homology_z`  —— Smith 標準形（`elim/core.smith_diagonal`）

///|  - `homology_q`  —— 精確有理秩（`exact/algebra.qmat_rank`）

///|  - `homology_fp` —— 模 p 高斯消元（`elim/core.rank_mod`）

///|  - `homology_zm` —— 由 `homology_z` 經**萬有係數定理**變換（不是重算）
///

///| 因為四條路徑用的演算法互不相干，`homology_fp` 與 `homology_zm` 的吻合

///| 是一個**真檢查**：它同時驗證了 UCT 與三個消元實作。

///| 一個複形在指定係數環下的同調。
///

///| **欄位語義約定**：`CZ`/`CQ`/`CFp` 時 `Ab.free` 是 `ℤ`（或 `F_p`）的拷貝數；

///| `CZm` 時 `Ab.free` 是 **`ℤ/m` 的拷貝數**，`tors` 是剩下的 `ℤ/d` 直和項（`d | m`）。

///|
/// 這個混淆是本輪踩到的第一個坑：`ℤ/2 ⊗ ℤ/4 = ℤ/2` 是撓率項，不是 `ℤ/4`。
pub struct Homology {
  coeff : Coeff
  groups : Array[Ab]
  how : String
}

///|
pub fn hom_show(h : Homology) -> String {
  let mut out = ""
  for k = 0; k < h.groups.length(); k = k + 1 {
    if k > 0 {
      out = "\{out} "
    }
    out = "\{out}H\{k}=\{ab_show_ring(h.groups[k], h.coeff)}"
  }
  out
}

///|
/// 整係數同調（Smith 標準形）。
pub fn homology_z(cx : ChainComplex) -> Homology {
  let top = cc_top(cx)
  let groups : Array[Ab] = []
  let rk : Array[Int32] = Array::make(top + 2, 0)
  for d = 1; d <= top; d = d + 1 {
    rk[d] = rank_z(cc_boundary(cx, d))
  }
  for k = 0; k <= top; k = k + 1 {
    let free = cx.cells[k] - rk[k] - rk[k + 1]
    let tors = if k + 1 <= top {
      smith_invariants(cc_boundary(cx, k + 1))
    } else {
      []
    }
    groups.push(ab_make(free, tors))
  }
  Homology::{ coeff: CZ, groups, how: "Smith normal form (Z)", }
}

///|
/// ℚ 係數同調（精確有理秩）。
pub fn homology_q(cx : ChainComplex) -> Homology {
  let top = cc_top(cx)
  let groups : Array[Ab] = []
  let rk : Array[Int32] = Array::make(top + 2, 0)
  for d = 1; d <= top; d = d + 1 {
    rk[d] = rank_q(cc_boundary(cx, d))
  }
  for k = 0; k <= top; k = k + 1 {
    groups.push(ab_make(cx.cells[k] - rk[k] - rk[k + 1], []))
  }
  Homology::{ coeff: CQ, groups, how: "exact rational rank (Q)", }
}

///|
/// `F_p` 係數同調（模 p 高斯消元）。
pub fn homology_fp(cx : ChainComplex, p : Int32) -> Homology {
  let top = cc_top(cx)
  let groups : Array[Ab] = []
  let rk : Array[Int32] = Array::make(top + 2, 0)
  for d = 1; d <= top; d = d + 1 {
    rk[d] = rank_fp(cc_boundary(cx, d), p)
  }
  for k = 0; k <= top; k = k + 1 {
    groups.push(ab_make(cx.cells[k] - rk[k] - rk[k + 1], []))
  }
  Homology::{ coeff: CFp(p), groups, how: "mod-p Gaussian elimination", }
}

///| 任意係數 `ℤ/m`：由整係數同調經 UCT 變換。

///|
/// `H_k(C; ℤ/m) ≅ (H_k(C;ℤ) ⊗ ℤ/m) ⊕ Tor(H_{k−1}(C;ℤ), ℤ/m)`
pub fn homology_zm(cx : ChainComplex, m : Int32) -> Homology {
  let hz = homology_z(cx)
  let groups : Array[Ab] = []
  for k = 0; k < hz.groups.length(); k = k + 1 {
    let prev = if k > 0 { Some(hz.groups[k - 1]) } else { None }
    groups.push(ab_uct(hz.groups[k], prev, m))
  }
  Homology::{ coeff: CZm(m), groups, how: "UCT from H_*(Z)", }
}

///|
/// 依係數分派。
pub fn homology(cx : ChainComplex, c : Coeff) -> Homology {
  match c {
    CZ => homology_z(cx)
    CQ => homology_q(cx)
    CFp(p) => homology_fp(cx, p)
    CZm(m) => homology_zm(cx, m)
  }
}

// ------------------------------------------------------------- 交叉驗證 ----

///|
/// 一列驗證結果。
pub struct UctCheck {
  p : Int32
  dim_direct : Array[Int32]
  dim_predicted : Array[Int32]
  ok : Bool
}

///| 交叉驗證：`dim_{F_p} H_k(C;F_p)`（模 p 消元）

///| 對比 `β_k + t_k(p) + t_{k−1}(p)`（Smith 標準形 + UCT）。

///|
/// 兩邊演算法完全不同 ⇒ 相等是真結果，不是恆等式。
pub fn uct_check(cx : ChainComplex, p : Int32) -> UctCheck {
  let hz = homology_z(cx)
  let hf = homology_fp(cx, p)
  let dim_direct : Array[Int32] = []
  let dim_pred : Array[Int32] = []
  let mut ok = true
  for k = 0; k < hf.groups.length(); k = k + 1 {
    let a = hf.groups[k].free
    dim_direct.push(a)
    let mut b = ab_dim_tensor_fp(hz.groups[k], p)
    if k > 0 {
      b = b + ab_dim_tor_fp(hz.groups[k - 1], p)
    }
    dim_pred.push(b)
    if a != b {
      ok = false
    }
  }
  UctCheck::{ p, dim_direct, dim_predicted: dim_pred, ok, }
}

///|
/// 第三條交叉驗證：`rank_ℚ = rank_ℤ`（有理秩 vs Smith 秩）。
pub fn rank_paths_agree(cx : ChainComplex) -> Bool {
  for d = 1; d <= cc_top(cx); d = d + 1 {
    let m = cc_boundary(cx, d)
    if rank_q(m) != rank_z(m) {
      return false
    }
  }
  true
}

// ------------------------------------------------------------ 可見性表 ----

///| 「撓率在哪些係數環下可見」——本文最重要的一張表。

///| 對每個模型、每個係數環列出同調的完整同構類；

///|
/// `ℚ` 那一欄會把所有撓率抹成 0，這正是「缺失係數環」的直接證據。
pub fn visibility_table(
  models : Array[(String, ChainComplex)],
  rings : Array[Coeff],
) -> Array[String] {
  let out : Array[String] = []
  for m in models {
    let name = m.0
    let cx = m.1
    let mut line = "\{name}:"
    for c in rings {
      let h = homology(cx, c)
      line = "\{line}  [\{coeff_show(c)}] \{hom_show(h)}"
    }
    out.push(line)
  }
  out
}
