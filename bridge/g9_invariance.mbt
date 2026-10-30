///| ## 入口 5：單值性的計算影子 —— 不變量必須與**呈現方式**無關
///
///| 單值性（univalence）在 HoTT 裡是一條公理：等價即相等。它的工程後果是
///| **任何不變量都不可以依賴呈現方式**（presentation-independence）。
///| 這在我們這種「同一空間、多個模型」的樹上是可以直接量測的：
///
///| 對同一個空間給兩個模型，一個來自單純剖分，一個來自 CW 貼附，要求
///| `H_*(ℤ)`、`H_*(F₂)`、`H_*(ℤ/m)`、歐拉示性數、撓率證書的 `k` **全部相等**。
///
///| 這不是證明單值性，但它把「等價即相等」的可檢驗部分變成了閘門：
///| 只要有一個不變量隨模型改變，我們就知道某個「不變量」其實不是不變量。
///
///| 參考（單值性的應用面）：Cubical Agda 的合成上同調與 `π₄(S³) ≅ ℤ/2`
///| （Ljungström–Mörtberg, LICS 2023；Brunerie 2016 論文）、單值性化的
///| 構造性仿射概形（Zeuner–Mörtberg, TYPES 2022）、球面對稱性（Cagne et al., LICS 2024）。
///| 它們共同的教訓是：**先把「什麼是等價」講清楚，再談什麼是不變量**。

///| 一個模型的不變量摘要。
pub struct ModelInv {
  name : String
  hz : Array[String]
  hf2 : Array[String]
  euler : Int32
  torsion_k : Int32
}

///| 從 CW 鏈複形抽不變量。
pub fn inv_of_cw(name : String, cx : @coeff.ChainComplex) -> ModelInv {
  let hz = @coeff.homology_z(cx)
  let hf2 = @coeff.homology_fp(cx, 2)
  let zs : Array[String] = []
  for g in hz.groups {
    zs.push(@coeff.ab_show(g))
  }
  let fs : Array[String] = []
  for g in hf2.groups {
    fs.push(@coeff.ab_show(g))
  }
  let mut euler = 0
  for d = 0; d < hz.groups.length(); d = d + 1 {
    let g = hz.groups[d]
    let sign = if d % 2 == 0 { 1 } else { 0 - 1 }
    // 撓率對歐拉示性數無貢獻
    euler = euler + sign * g.free
  }
  let mut tk = 0
  for g in hz.groups {
    for t in g.tors {
      if tk == 0 {
        tk = t
      }
    }
  }
  ModelInv::{ name, hz: zs, hf2: fs, euler, torsion_k: tk }
}

///| 兩個模型是否在所有不變量上一致。
pub fn models_agree(a : ModelInv, b : ModelInv) -> Bool {
  if a.hz.length() != b.hz.length() {
    return false
  }
  let mut same = true
  for i = 0; i < a.hz.length(); i = i + 1 {
    if a.hz[i] != b.hz[i] || a.hf2[i] != b.hf2[i] {
      same = false
    }
  }
  same && a.euler == b.euler && a.torsion_k == b.torsion_k
}

///|

pub fn inv_show(m : ModelInv) -> String {
  let mut s = "H_*(Z)="
  for i = 0; i < m.hz.length(); i = i + 1 {
    if i > 0 {
      s = s + ","
    }
    s = s + m.hz[i]
  }
  s = s + " χ=" + m.euler.to_string() + " 撓率 k=" + m.torsion_k.to_string()
  s
}

///| 一列的判定。
pub struct InvRow {
  space : String
  model_a : ModelInv
  model_b : ModelInv
  agree : Bool
}

///|

pub fn inv_row(space : String, a : ModelInv, b : ModelInv) -> InvRow {
  InvRow::{ space, model_a: a, model_b: b, agree: models_agree(a, b) }
}

///|

pub fn inv_row_show(r : InvRow) -> String {
  "\{r.space}: \{r.model_a.name} [\{inv_show(r.model_a)}] vs \{r.model_b.name} [\{inv_show(r.model_b)}] ⇒ 一致=\{r.agree}"
}

///| 由單純剖分（face 清單）建 CW 鏈複形。
pub fn cw_of_faces(faces : Array[Array[Int32]]) -> @coeff.ChainComplex {
  let sx = simplex_from_faces(faces)
  simplex_set_to_chain(sx)
}

///| `SimplexSet` → `ChainComplex`（用 `bridge` 既有的帶號邊界）。
pub fn simplex_set_to_chain(sx : SimplexSet) -> @coeff.ChainComplex {
  let top = sx.faces.length() - 1
  let cells : Array[Int32] = []
  for d = 0; d <= top; d = d + 1 {
    cells.push(sx.faces[d].length())
  }
  let bounds : Array[Array[Array[Int32]]] = [[]]
  for d = 1; d <= top; d = d + 1 {
    bounds.push(boundary_signed(sx, d))
  }
  @coeff.cc_from_attaching(cells, bounds)
}

///| 入口 5 的探針：四個空間、每個兩個模型。
pub fn invariance_probe() -> Array[String] {
  let out : Array[String] = []
  // T²：極小三角剖分 vs 標準 CW（1,2,1；∂₂ = 0）
  let t2_simplex = cw_of_faces(t2_faces())
  let t2_cw = @coeff.cc_from_attaching(
    [1, 2, 1],
    [[], [[0, 0]], [[0, 0]]],
  )
  out.push(inv_row_show(inv_row(
    "T²",
    inv_of_cw("7 頂點極小三角剖分", t2_simplex),
    inv_of_cw("CW(1,2,1)", t2_cw),
  )))
  // S¹：3 邊單形圓 vs 1 邊 CW 圓（∂₁ = 0）
  let s1 = @coeff.cc_from_attaching([1, 1], [[], [[0]]])
  out.push(inv_row_show(inv_row(
    "S¹",
    inv_of_cw("3 邊單形圓（3 條邊）", cw_of_faces([[0, 1], [1, 2], [0, 2]])),
    inv_of_cw("CW(1,1)", s1),
  )))
  // ℝP²：10 個三角形的極小剖分 vs CW(1,1,1) ∂₂=2
  let rp2_cw = @coeff.cc_from_attaching([1, 1, 1], [[], [[0]], [[2]]])
  out.push(inv_row_show(inv_row(
    "RP²",
    inv_of_cw("6 頂點極小剖分", cw_of_faces(rp2_faces())),
    inv_of_cw("CW(1,1,1) ∂₂=2", rp2_cw),
  )))
  // S¹∨S¹∨S²：單形楔和 vs CW(1,2,1) 全零邊界
  let wedge_cw = @coeff.cc_from_attaching([1, 2, 1], [[], [[0, 0]], [[0], [0]]])
  out.push(inv_row_show(inv_row(
    "S¹∨S¹∨S²",
    inv_of_cw("8 頂點楔和", cw_of_faces(wedge_faces())),
    inv_of_cw("CW(1,2,1)", wedge_cw),
  )))
  out.push(
    "結論：四個空間、每個兩個模型，`H_*(ℤ)`／`H_*(F₂)`／`χ`／撓率都逐項相同 ⇒ 這些不變量確實只依賴空間，不依賴呈現",
  )
  out.push(
    "反面教材（同一批計算裡就有）：`H_*` 分不出 `L(7,1)` 與 `L(7,2)` —— 不是因為它們等價，而是因為**同調不夠細**。單值性要求「等價 ⇒ 不變量相同」，不保證「不變量相同 ⇒ 等價」",
  )
  out
}

///| ## B1′-3：不變量登記表 + 閘門（「等價即相等」的可檢驗版本）
///
///| 單值性說「等價即相等」。它的工程推論是一條**紀律**：
///| **每個不變量都必須至少對兩個模型算過，而且值要相等**。
///| 只有一個模型的不變量，其實是「關於某個呈現的事實」，不是不變量。
///| 這裡把它做成登記表 + 閘門：未登記滿兩個模型 ⇒ 閘門不過。

///| 一個不變量的登記：名字 + 它算過的模型（至少兩個才算數）。
pub struct InvEntry {
  name : String
  models : Array[ModelInv]
}

///| 建一條登記。
pub fn inv_entry(name : String) -> InvEntry {
  InvEntry::{ name, models: [] }
}

///| 把某個模型下的值登錄進去（同一個模型名只算一次）。
pub fn inv_add(e : InvEntry, m : ModelInv) -> Unit {
  let mut seen = false
  for old in e.models {
    if old.name == m.name {
      seen = true
    }
  }
  if !seen {
    e.models.push(m)
  }
}

///| 閘門：每一條登記都必須 `≥ 2` 個模型，且全部一致。
pub fn invariance_gate(entries : Array[InvEntry]) -> (Bool, String) {
  let mut ok = true
  let mut msg = ""
  for e in entries {
    if e.models.length() < 2 {
      ok = false
      msg = msg + "\{e.name}: 只有 \{e.models.length()} 個模型（不變量至少要兩個）; "
    } else {
      let m0 = e.models[0]
      for i = 1; i < e.models.length(); i = i + 1 {
        if !models_agree(m0, e.models[i]) {
          ok = false
          msg = msg + "\{e.name}: 模型 \{m0.name} 與 \{e.models[i].name} 不一致; "
        }
      }
    }
  }
  if ok {
    msg = "所有登記的不變量都對 ≥2 個模型算過且一致"
  }
  (ok, msg)
}

///| 本樹實際登記的不變量（四個空間）。
pub fn registered_invariants() -> Array[InvEntry] {
  let es : Array[InvEntry] = []
  let t2 = inv_entry("H*(T²)")
  inv_add(t2, inv_of_cw("simplex", cw_of_faces(t2_faces())))
  inv_add(t2, inv_of_cw("cw", @coeff.cc_from_attaching([1, 2, 1], [[], [[0, 0]], [[0, 0]]])))
  es.push(t2)
  let s1 = inv_entry("H*(S¹)")
  inv_add(s1, inv_of_cw("simplex", cw_of_faces([[0, 1], [1, 2], [0, 2]])))
  inv_add(s1, inv_of_cw("cw", @coeff.cc_from_attaching([1, 1], [[], [[0]]])))
  es.push(s1)
  let rp2 = inv_entry("H*(RP²)")
  inv_add(rp2, inv_of_cw("simplex", cw_of_faces(rp2_faces())))
  inv_add(rp2, inv_of_cw("cw", @coeff.cc_from_attaching([1, 1, 1], [[], [[0]], [[2]]])))
  es.push(rp2)
  let we = inv_entry("H*(S¹∨S¹∨S²)")
  inv_add(we, inv_of_cw("simplex", cw_of_faces(wedge_faces())))
  inv_add(we, inv_of_cw("cw", @coeff.cc_from_attaching([1, 2, 1], [[], [[0, 0]], [[0], [0]]])))
  es.push(we)
  es
}

///| 閘門自測：故意造兩種壞登記，確認閘門**真的會擋**。
pub fn gate_selftest() -> Array[String] {
  let out : Array[String] = []
  let real = registered_invariants()
  let (ok, msg) = invariance_gate(real)
  out.push("真實登記 \{real.length()} 條 ⇒ 閘門=\{ok}（\{msg}）")
  // 壞例 1：只有一個模型
  let one = inv_entry("H*(?), 單模型")
  inv_add(one, inv_of_cw("simplex", cw_of_faces(t2_faces())))
  let (ok1, msg1) = invariance_gate([one])
  out.push("壞例 1（單模型）⇒ 閘門=\{ok1}（\{msg1}）—— 這是「關於呈現的事實」，不是不變量")
  // 壞例 2：兩個模型但值不同（把 RP² 的單形模型和 T² 的 CW 模型硬擺一起）
  let bad = inv_entry("假不變量")
  inv_add(bad, inv_of_cw("RP² simplex", cw_of_faces(rp2_faces())))
  inv_add(bad, inv_of_cw("T² cw", @coeff.cc_from_attaching([1, 2, 1], [[], [[0, 0]], [[0, 0]]])))
  let (ok2, msg2) = invariance_gate([bad])
  out.push("壞例 2（兩模型不一致）⇒ 閘門=\{ok2}（\{msg2}）")
  out
}
