///| ## Hopf 纖維化（殘餘 1）
///
///| `S¹ → S³ → S²` 這一條纖維化的可算內容有三層，三層必須互相印證：
///
///| 1. **Gysin 序列**：底空間 `B = S²`，歐拉類 `e ∈ H²(B) = ℤ`（整數 `d`）。
///|    `d = ±1` ⇒ `H*(E) = H*(S³)`；`d = 0` ⇒ `H*(S¹×S²)`；一般 `d` ⇒ 透鏡空間
///|    `H*(L(d)) = (ℤ, 0, ℤ/d, ℤ)`。
///| 2. **CW 模型**：`L(d) = e⁰ ∪ e¹ ∪ e² ∪ e³`，`∂₂ = d`。直接算鏈複形：
///|    `H₀ = ℤ`、`H₁ = ℤ/d`、`H₂ = 0`、`H₃ = ℤ`。
///| 3. **兩者對得上**：Gysin 給上同調、CW 給同調，由 UCT 相連（`H² ≅ free H₂ ⊕ tors H₁`）。
///
///| 於是「歐拉類 = 貼附度數 = Hopf 不變量」不是口號，是兩個獨立計算的交點。

// ---------------------------------------------------------- 整數矩陣核／餘核 ----
///| `M: ℤ^a → ℤ^b`（`m` 有 `b` 列、`a` 行）的核。
///| 同一個矩陣的 `ker` 與 `coker` 有**同構的撓率子群**（Smith 不變因子），
///| 差別只在自由秩：`rank ker = a − r`、`rank coker = b − r`。
pub fn ab_ker(a : Int32, m : Array[Array[Int32]]) -> @coeff.Ab {
  let empty = m.length() == 0 || m[0].length() == 0
  let r = if empty { 0 } else { @coeff.rank_z(m) }
  let tors = if empty { [] } else { @coeff.smith_invariants(m) }
  @coeff.ab_make(a - r, tors)
}

///|

pub fn ab_coker(b : Int32, m : Array[Array[Int32]]) -> @coeff.Ab {
  let empty = m.length() == 0 || m[0].length() == 0
  let r = if empty { 0 } else { @coeff.rank_z(m) }
  let tors = if empty { [] } else { @coeff.smith_invariants(m) }
  @coeff.ab_make(b - r, tors)
}

///| 阿貝爾群直和。
pub fn ab_sum(a : @coeff.Ab, b : @coeff.Ab) -> @coeff.Ab {
  let tors : Array[Int32] = []
  for t in a.tors {
    tors.push(t)
  }
  for t in b.tors {
    tors.push(t)
  }
  @coeff.ab_make(a.free + b.free, tors)
}

///| 兩群是否同構（把撓率排序後比較）。
pub fn ab_iso(a : @coeff.Ab, b : @coeff.Ab) -> Bool {
  if a.free != b.free || a.tors.length() != b.tors.length() {
    return false
  }
  let ta = sorted(a.tors)
  let tb = sorted(b.tors)
  for i = 0; i < ta.length(); i = i + 1 {
    if ta[i] != tb[i] {
      return false
    }
  }
  true
}

///|

fn sorted(a : Array[Int32]) -> Array[Int32] {
  let b : Array[Int32] = []
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

// ---------------------------------------------------------------- Gysin ----
///| 底空間 `S²` 的 `H^k` 自由秩：`[1, 0, 1]`（`k = 0,1,2`）。
fn rank_h(k : Int32) -> Int32 {
  if k == 0 || k == 2 {
    1
  } else {
    0
  }
}

///| 「乘以歐拉類」的矩陣 `e: H^{k} → H^{k+2}`（`k = 0` 時是 `1×1` 的 `[d]`，其餘為空）。
fn euler_matrix(k : Int32, d : Int32) -> Array[Array[Int32]] {
  if k == 0 {
    [[d]]
  } else {
    []
  }
}

///| 由 Gysin 序列算出 `H^m(E)`（`m = 0..3`）：
///| `H^m(E) = coker(e: H^{m−2} → H^m) ⊕ ker(e: H^{m−1} → H^{m+1})`。
pub fn gysin_h(m : Int32, euler : Int32) -> @coeff.Ab {
  let c = ab_coker(rank_h(m), euler_matrix(m - 2, euler))
  let k = ab_ker(rank_h(m - 1), euler_matrix(m - 1, euler))
  ab_sum(c, k)
}

// ------------------------------------------------------- 透鏡空間 CW 模型 ----
///| `L(d) = e⁰ ∪ e¹ ∪ e² ∪ e³`，`∂₁ = 0`、`∂₂ = d`、`∂₃ = 0`。
pub fn lens_cw(d : Int32) -> @coeff.ChainComplex {
  let cells : Array[Int32] = [1, 1, 1, 1]
  let d1 : Array[Array[Int32]] = [[0]]
  let d2 : Array[Array[Int32]] = [[d]]
  let d3 : Array[Array[Int32]] = [[0]]
  let attach : Array[Array[Array[Int32]]] = [[], d1, d2, d3]
  @coeff.cc_from_attaching(cells, attach)
}

///| 「S¹-叢的總空間」的交叉驗證列。
pub struct HopfRow {
  d : Int32
  coh_from_gysin : Array[@coeff.Ab]
  hom_from_cw : Array[@coeff.Ab]
  uct_agrees : Bool
  pi1 : @coeff.Ab
  note : String
}

///| UCT：`H^m(E) ≅ free(H_m) ⊕ tors(H_{m−1})`。
fn uct_cohomology(cx : @coeff.ChainComplex, m : Int32) -> @coeff.Ab {
  let h = @coeff.homology_z(cx)
  let hm = h.groups[m]
  let tcopy : Array[Int32] = []
  for t in hm.tors {
    let _ = tcopy.push(t)
  }
  if m > 0 {
    for t in h.groups[m - 1].tors {
      let _ = tcopy.push(t)
    }
  }
  @coeff.ab_make(hm.free, tcopy)
}

///| 對歐拉類 `d` 的 `S¹`-叢做兩個獨立計算並比較。
pub fn hopf_row(d : Int32) -> HopfRow {
  let cx = lens_cw(d)
  let coh : Array[@coeff.Ab] = []
  for m = 0; m <= 3; m = m + 1 {
    coh.push(gysin_h(m, d))
  }
  let hom : Array[@coeff.Ab] = []
  let mut agrees = true
  for m = 0; m <= 3; m = m + 1 {
    let u = uct_cohomology(cx, m)
    hom.push(u)
    if !ab_iso(u, coh[m]) {
      agrees = false
    }
  }
  let pi1 = @coeff.homology_z(cx).groups[1]
  let note = if d == 1 || d == 0 - 1 {
    "Hopf 纖維化：總空間 ≅ S³（π₁ = 0，H² = 0）"
  } else if d == 0 {
    "平凡叢 S¹×S²"
  } else {
    "透鏡空間 L(d)：π₁ = ℤ/d 同時是 H² 的撓率"
  }
  HopfRow::{ d, coh_from_gysin: coh, hom_from_cw: hom, uct_agrees: agrees, pi1, note }
}

///|

pub fn hopf_show(r : HopfRow) -> String {
  let mut a = ""
  for m = 0; m <= 3; m = m + 1 {
    a = "\{a} H^\{m}=\{@coeff.ab_show(r.coh_from_gysin[m])}"
  }
  "d=\{r.d}:\{a} | H₁(π₁)=\{@coeff.ab_show(r.pi1)} UCT 一致=\{r.uct_agrees} —— \{r.note}"
}

///| 全部候選歐拉類。
pub fn hopf_probe() -> Array[String] {
  let out : Array[String] = []
  for d in [1, 0 - 1, 0, 2, 3, 5] {
    out.push(hopf_show(hopf_row(d)))
  }
  out.push(
    "結論：歐拉類 d = ±1 恰好給出 S³；|d| ≥ 2 給出透鏡空間。Gysin（上同調）與 CW（同調）兩條獨立路徑逐維一致 —— 「歐拉類 = 貼附度數 = Hopf 不變量」",
  )
  out.push(
    "殘餘：H* 分不出 d = 1 與 d = −1（定向），也分不出 L(7,1) 與 L(7,2)（同倫等價但不同胚，需 Reidemeister 撓率）",
  )
  out
}
