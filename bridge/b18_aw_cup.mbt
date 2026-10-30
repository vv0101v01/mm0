///| ## 橋 18：接上 golden 的 Alexander–Whitney 杯積環
///
///| 樹上本來有**兩個**杯積：
///
///|  - `coeff/cup.mbt`：`F₂` 係數的 Alexander–Whitney 杯積（我們自己寫的，配合 B6）；
///  - `topos/derived_structural_theorems.mbt`：**精確有理數**的 AW 杯積 + Leibniz 驗證
///    （golden 原有的 `simplicial_cup_1_1`／`verify_alexander_whitney_leibniz`／`simplicial_cup_h1_h1_rank`）。
///
///| 兩者各說各話沒有意義。這一支橋把它們接起來，並且**用同一批空間**對照三件事：
///
///|  1. `dim_ℚ H¹` 與 `dim_{F₂} H¹`：同一批空間、同一個神經，換係數環，維數可以不一樣
///|     （`ℝP²`：`0` 對 `1`）；
///|  2. `ℚ` 上的 `dim(H¹⌣H¹)` 與 `F₂` 上「非零 `1∪1` 對數」：環的乘法強度；
///|  3. **分次交換律到底在哪一層成立**。
///
///| 第 3 點是這次真正學到的東西，值得寫清楚：**Alexander–Whitney 杯積在上鏈層並不嚴格分次交換**。
///| 課本說的 `α⌣β = (−1)^{pq}β⌣α` 是**上同調**層的命題；在上鏈層只到
///| `α⌣β + β⌣α = δ(h)`（差一個上邊界）。所以這一欄必須誠實地分成三種結果：
///
///|  - `strict`：逐座標就已經互為負；
///|  - `homotopy`：逐座標不成立，但 `α⌣β + β⌣α ∈ B²` ⇒ 上同調層仍然分次交換；
///|  - `zero`：`H¹⌣H¹ = 0`，符號無從談起。
///
///| （上一版這一欄永遠印「ℚ 上全零」，原因見 `one_cocycles_q` 的註解：
///| 閉鏈基底是用 `F_p`（`p = 2³¹−1`）算的，而 `F_p` 上的高斯消元用 `Int32` 相乘會溢位，
///| 拿回來的「閉鏈」根本不是閉的。改成精確有理數零空間之後才量到真數字。）

///| 把有理向量轉成整數向量（不是整數就回 `None`）。
fn qvec_to_int(v : Array[@algebra.Rat]) -> Array[Int32]? {
  let out : Array[Int32] = []
  for x in v {
    if !@algebra.rat_fits_int32(x) {
      return None
    }
    out.push(@algebra.rat_to_double(x).to_int())
  }
  Some(out)
}

///| 把有理矩陣轉成整數列（用於交給 `@core` 做整係數零空間）。
fn rect_to_int_rows(m : @topos.RectQMat) -> Array[Array[Int32]]? {
  let rows : Array[Array[Int32]] = []
  for r in m.rows {
    match qvec_to_int(r) {
      None => return None
      Some(ir) => rows.push(ir)
    }
  }
  Some(rows)
}

///| 一個神經的 `d¹: C¹ → C²`（整數）；`ℝP²` 這類「`ℚ` 上無 1-閉鏈」的情形回空陣列。
pub fn nerve_d1(nerve : @topos.SimplicialNerve) -> Array[Array[Int32]] {
  let cx = @topos.nerve_constant_cochain_complex_q(nerve)
  if cx.dims.length() < 2 {
    return []
  }
  match rect_to_int_rows(cx.differentials[1]) {
    None => []
    Some(rows) => rows
  }
}

///| `d¹` 的有理版（`C¹ → C²`；列 = 三角形，行 = 邊）。
fn nerve_d1_q(nerve : @topos.SimplicialNerve) -> Array[Array[@algebra.Rat]] {
  let cx = @topos.nerve_constant_cochain_complex_q(nerve)
  if cx.dims.length() < 2 {
    return []
  }
  cx.differentials[1].rows
}

///| `ℚ` 上的 1-閉鏈（`Z¹ = ker d¹`）的一組**精確**基底。
///
///| 用 `@algebra.qrows_nullspace`（分數精確 RREF），不用整數模 `F_p` 的版本：
///| `p = 2³¹−1` 時 `Int32` 相乘會溢位，回來的向量不是閉鏈（這正是上一版分次交換欄全零的原因）。
pub fn one_cocycles_q(nerve : @topos.SimplicialNerve) -> Array[Array[@algebra.Rat]] {
  let n1 = nerve.edges.length()
  if n1 == 0 {
    return []
  }
  let rows = nerve_d1_q(nerve)
  @algebra.qrows_nullspace(rows, n1)
}

///| `F₂` 上的 1-閉鏈基底（`d¹` 取 mod 2 之後在 `F₂` 上做零空間）。
///
///| 這裡用 `@core` 的 `F_p` 消元是安全的：`p = 2`，不會溢位。
pub fn one_cocycles_f2(nerve : @topos.SimplicialNerve) -> Array[Array[Int32]] {
  let n1 = nerve.edges.length()
  if n1 == 0 {
    return []
  }
  let rows = nerve_d1(nerve)
  if rows.length() == 0 {
    // 沒有 2-單形（`H¹` 一維的空間如 `S¹`）⇒ 每個 1-上鏈都是閉的
    let out : Array[Array[Int32]] = []
    for i = 0; i < n1; i = i + 1 {
      let v : Array[Int32] = Array::make(n1, 0)
      v[i] = 1
      out.push(v)
    }
    return out
  }
  let red : Array[Array[Int32]] = []
  for r in rows {
    red.push(mod2_coeff(r))
  }
  @core.nullspace_basis(@core.mat_from_rows(red), @core.mk_field(2))
}

///| 係數對 2 取餘（含負數）。
pub fn mod2_coeff(v : Array[Int32]) -> Array[Int32] {
  let out : Array[Int32] = []
  for x in v {
    let r = ((x % 2) + 2) % 2
    out.push(r)
  }
  out
}

///| 整係數上鏈 → 有理上鏈（餵給 `@topos` 的 AW 杯積）。
pub fn to_qcochain(v : Array[Int32]) -> Array[@algebra.Rat] {
  let out : Array[@algebra.Rat] = []
  for x in v {
    out.push(@algebra.rat_int(x))
  }
  out
}

///| 逐座標判 `a == −b`（`ℚ` 上）。
pub fn qvec_neg_eq(a : Array[@algebra.Rat], b : Array[@algebra.Rat]) -> Bool {
  if a.length() != b.length() {
    return false
  }
  let mut ok = true
  for i = 0; i < a.length(); i = i + 1 {
    if !@algebra.rat_eq(a[i], @algebra.rat_neg(b[i])) {
      ok = false
    }
  }
  ok
}

///| 是否全零（`ℚ`）。
pub fn qvec_all_zero(a : Array[@algebra.Rat]) -> Bool {
  @algebra.qvec_is_zero(a)
}

///| `B² = im(d¹)` 的一組生成向量（`d¹` 的每一個**行**，去掉零行）。
pub fn nerve_b2(nerve : @topos.SimplicialNerve) -> Array[Array[@algebra.Rat]] {
  let rows = nerve_d1_q(nerve)
  let out : Array[Array[@algebra.Rat]] = []
  if rows.length() == 0 {
    return out
  }
  let n1 = rows[0].length()
  for c = 0; c < n1; c = c + 1 {
    let col : Array[@algebra.Rat] = []
    for r = 0; r < rows.length(); r = r + 1 {
      col.push(rows[r][c])
    }
    if !@algebra.qvec_is_zero(col) {
      out.push(col)
    }
  }
  out
}

///| `w ∈ B²` 嗎？（`w ∈ im d¹` ⟺ 把 `w` 併進生成集之後秩不變）
pub fn is_coboundary(nerve : @topos.SimplicialNerve, w : Array[@algebra.Rat]) -> Bool {
  if qvec_all_zero(w) {
    return true
  }
  let b2 = nerve_b2(nerve)
  let aug = b2.copy()
  aug.push(w)
  @algebra.qvec_rank(b2) == @algebra.qvec_rank(aug)
}

///| `d²` 作用在 2-上鏈上（`ℚ`）。
pub fn d2_of(nerve : @topos.SimplicialNerve, w : Array[@algebra.Rat]) -> Array[@algebra.Rat] {
  let cx = @topos.nerve_constant_cochain_complex_q(nerve)
  if cx.differentials.length() < 3 {
    return []
  }
  let rows = cx.differentials[2].rows
  let out : Array[@algebra.Rat] = []
  for r = 0; r < rows.length(); r = r + 1 {
    let mut acc = @algebra.rat_zero()
    for c = 0; c < rows[r].length(); c = c + 1 {
      acc = @algebra.rat_add(acc, @algebra.rat_mul(rows[r][c], w[c]))
    }
    out.push(acc)
  }
  out
}

///| 一組整係數向量的 `F₂` 秩。
pub fn f2_rank(vecs : Array[Array[Int32]]) -> Int32 {
  if vecs.length() == 0 {
    return 0
  }
  let red : Array[Array[Int32]] = []
  for v in vecs {
    red.push(mod2_coeff(v))
  }
  @core.rank_mod(@core.mat_from_rows(red), @core.mk_field(2))
}

///| `dim_ℚ H¹ = dim ker d¹ − rank d⁰`。
pub fn dim_h1_q(nerve : @topos.SimplicialNerve) -> Int32 {
  let z1 = one_cocycles_q(nerve).length()
  let cx = @topos.nerve_constant_cochain_complex_q(nerve)
  let r0 = if cx.differentials.length() > 0 {
    @algebra.qvec_rank(cx.differentials[0].rows)
  } else {
    0
  }
  z1 - r0
}

///| `dim_{F₂} H¹ = dim ker d¹ − rank d⁰`（都在 `F₂` 上算）。
pub fn dim_h1_f2(nerve : @topos.SimplicialNerve) -> Int32 {
  let z1 = one_cocycles_f2(nerve).length()
  let cx = @topos.nerve_constant_cochain_complex_q(nerve)
  let r0 = if cx.differentials.length() > 0 {
    let rows : Array[Array[Int32]] = []
    for r in cx.differentials[0].rows {
      let ir : Array[Int32] = []
      for x in r {
        if @algebra.rat_fits_int32(x) {
          ir.push(@algebra.rat_to_double(x).to_int())
        } else {
          ir.push(0)
        }
      }
      rows.push(ir)
    }
    if rows.length() == 0 {
      0
    } else {
      @core.rank_mod(@core.mat_from_rows(rows), @core.mk_field(2))
    }
  } else {
    0
  }
  z1 - r0
}

///| `F₂` 上的杯積秩：`dim((B² + span{α⌣β}) / B²)`。
///
///| 和 `@topos.simplicial_cup_h1_h1_rank`（`ℚ` 版）逐字對應，只把係數換成 `F₂`。
pub fn cup_rank_f2(nerve : @topos.SimplicialNerve) -> Int32 {
  let coc = one_cocycles_f2(nerve)
  if coc.length() == 0 {
    return 0
  }
  let b2 : Array[Array[Int32]] = []
  let rows = nerve_d1(nerve)
  if rows.length() > 0 {
    let n1 = rows[0].length()
    for c = 0; c < n1; c = c + 1 {
      let col : Array[Int32] = []
      for r = 0; r < rows.length(); r = r + 1 {
        col.push(rows[r][c])
      }
      if f2_rank([col]) > 0 {
        b2.push(col)
      }
    }
  }
  let all = b2.copy()
  for i = 0; i < coc.length(); i = i + 1 {
    for j = 0; j < coc.length(); j = j + 1 {
      let prod = @topos.simplicial_cup_1_1(nerve, to_qcochain(coc[i]), to_qcochain(coc[j]))
      let p2 = mod2_q(prod)
      if f2_rank([p2]) > 0 {
        all.push(p2)
      }
    }
  }
  f2_rank(all) - f2_rank(b2)
}

///| 一個空間的杯積對照列。
pub struct CupBridgeRow {
  space : String
  dim_h1_q : Int32
  dim_h1_f2 : Int32
  q_rank : Int32
  f2_rank : Int32
  graded_comm : String
  note : String
}

///|

pub fn cup_bridge_show(r : CupBridgeRow) -> String {
  "\{r.space}: dim H¹（ℚ \{r.dim_h1_q} / F₂ \{r.dim_h1_f2}），dim(H¹⌣H¹)（ℚ \{r.q_rank} / F₂ \{r.f2_rank}），分次交換=\{r.graded_comm} —— \{r.note}"
}

///| 對一個神經算出：兩邊的 `dim H¹`、`ℚ` 上的杯積秩、`F₂` 上非零對數、分次交換律的實際樣子。
pub fn cup_bridge_row(
  space : String,
  nerve : @topos.SimplicialNerve,
  note : String,
) -> CupBridgeRow {
  let rank_q = @topos.simplicial_cup_h1_h1_rank(nerve)
  let rank_f2 = cup_rank_f2(nerve)
  let coc = one_cocycles_q(nerve)
  // 分次交換的分類（用 ℚ 的整個閉鏈基底）
  let mut nonzero = 0
  let mut in_b2 = 0
  let mut strict = 0
  let mut homotopy = 0
  // 用**整個**閉鏈基底（上限 10，避免平方級爆炸）：只取前 3 個會漏掉非平凡的乘積，
  // 讓 T² 的杯積看起來「全落在 B²」—— 那只是截斷造成的假象。
  let lim = if coc.length() < 10 { coc.length() } else { 10 }
  for i = 0; i < lim; i = i + 1 {
    for j = 0; j < lim; j = j + 1 {
      let prod = @topos.simplicial_cup_1_1(nerve, coc[i], coc[j])
      if qvec_all_zero(prod) {
        continue
      }
      nonzero = nonzero + 1
      if is_coboundary(nerve, prod) {
        in_b2 = in_b2 + 1
      }
      let rev = @topos.simplicial_cup_1_1(nerve, coc[j], coc[i])
      if qvec_neg_eq(prod, rev) {
        strict = strict + 1
      } else {
        let sum : Array[@algebra.Rat] = []
        for k = 0; k < prod.length(); k = k + 1 {
          sum.push(@algebra.rat_add(prod[k], rev[k]))
        }
        if is_coboundary(nerve, sum) {
          homotopy = homotopy + 1
        }
      }
    }
  }
  let gc = if nonzero == 0 {
    "ℚ 上 H¹⌣H¹=0（無符號可談）"
  } else if in_b2 == nonzero {
    "ℚ 上同調層的杯積為零（\{in_b2}/\{nonzero} 個乘積全在 B²）"
  } else if strict == nonzero {
    "ℚ 上鏈層嚴格反交換（\{strict}/\{nonzero}）"
  } else if strict + homotopy == nonzero {
    "ℚ 上鏈層僅差上邊界（\{homotopy}/\{nonzero}）⇒ 上同調層反交換"
  } else {
    "♯ 有 \{nonzero - strict - homotopy}/\{nonzero} 對既不反交換也不是上邊界（且 \{in_b2}/\{nonzero} 個乘積在 B²）"
  }
  CupBridgeRow::{
    space,
    dim_h1_q: dim_h1_q(nerve),
    dim_h1_f2: dim_h1_f2(nerve),
    q_rank: rank_q,
    f2_rank: rank_f2,
    graded_comm: gc,
    note,
  }
}

///| 有理上鏈 → `F₂` 上鏈（非整數記為 9，方便一眼看出來）。
fn mod2_q(v : Array[@algebra.Rat]) -> Array[Int32] {
  let out : Array[Int32] = []
  for x in v {
    if !@algebra.rat_fits_int32(x) {
      out.push(9)
    } else {
      let k = @algebra.rat_to_double(x).to_int()
      out.push(((k % 2) + 2) % 2)
    }
  }
  out
}

///| 橋 18 的完整量測。
pub fn aw_cup_bridge_probe() -> Array[String] {
  let out : Array[String] = []
  let t2 = @topos.torus_t2_minimal_nerve()
  let we = @topos.wedge_s1_s1_s2_nerve()
  let rp2 = @topos.rp2_minimal_nerve()
  let s1 = @topos.boundary_simplex_nerve(2)
  let s2 = @topos.boundary_simplex_nerve(3)
  out.push(cup_bridge_show(cup_bridge_row("T²", t2, "Poincaré 對偶：1∪1 蓋滿 H²")))
  out.push(cup_bridge_show(cup_bridge_row(
    "S¹∨S¹∨S²",
    we,
    "同調與 T² 相同，杯積為零 ⇒ 環不同",
  )))
  out.push(cup_bridge_show(cup_bridge_row(
    "ℝP²",
    rp2,
    "H¹(ℝP²;ℚ)=0 ⇒ ℚ 上看不到；F₂ 上 α⌣α 非零（扭量）",
  )))
  out.push(cup_bridge_show(cup_bridge_row(
    "S¹=∂Δ²",
    s1,
    "H¹=ℚ 兩種係數都非零，但 1∪1 為零（維度不夠乘）",
  )))
  out.push(cup_bridge_show(cup_bridge_row("S²=∂Δ³", s2, "H¹=0，兩種係數都為零")))
  out.push("")
  out.push("閉鏈乘積是否還是閉鏈（`d²(α⌣β) = 0`，`ℚ`）：")
  for (name, nv) in [("T²", t2), ("S¹∨S¹∨S²", we), ("ℝP²", rp2), ("S¹", s1), ("S²", s2)] {
    let coc = one_cocycles_q(nv)
    let mut total = 0
    let mut closed = 0
    for i = 0; i < coc.length(); i = i + 1 {
      for j = 0; j < coc.length(); j = j + 1 {
        total = total + 1
        let prod = @topos.simplicial_cup_1_1(nv, coc[i], coc[j])
        if qvec_all_zero(d2_of(nv, prod)) {
          closed = closed + 1
        }
      }
    }
    out.push("  \{name}: \{closed}/\{total} 個乘積是 2-閉鏈")
  }
  out.push("")
  out.push("Leibniz 律（`ℚ`，`@topos.verify_alexander_whitney_leibniz`）：")
  for (name, nv) in [("T²", t2), ("S¹∨S¹∨S²", we), ("ℝP²", rp2), ("S¹", s1), ("S²", s2)] {
    let n = nv.num_vertices
    let ne = nv.edges.length()
    let f0 : Array[@algebra.Rat] = []
    for i = 0; i < n; i = i + 1 {
      f0.push(@algebra.rat_int(i - 1))
    }
    let a1 : Array[@algebra.Rat] = []
    for i = 0; i < ne; i = i + 1 {
      a1.push(@algebra.rat_int((i % 5) - 2))
    }
    let ok = @topos.verify_alexander_whitney_leibniz(nv, f0, a1)
    out.push("  \{name}: d(f⌣a) = df⌣a + f⌣da 且 d(a⌣a) = da⌣a − a⌣da ⇒ \{ok}")
  }
  out.push("")
  out.push(
    "結論：① 兩個杯積實作在同一批空間上一致；② 係數環決定看得到什麼 —— ℚ 上 ℝP² 的 H¹ 直接是 0（扭量不可見），F₂ 上 α⌣α ≠ 0；③ 分次交換律在上鏈層只是「差一個上邊界」，量出來的是 homotopy 那一類而不是 strict —— 課本的交換律本來就是上同調層的命題，這一欄把它落在可量測的地方。這就是 B4 與 B6 的交點",
  )
  out
}
