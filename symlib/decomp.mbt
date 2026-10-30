///|
/// # Decomp — 分解式規範形式與積公式（衍生演算法 I）
///
/// 由「規範形式」導出的第一族衍生演算法。核心定理：
///
/// **分解定理**：設 G = C_1 ⊔ … ⊔ C_k 為連通分量之不交併，則
/// 1. **不變量**：G ≅ H ⇔ 分量規範編碼之多集相等。
///    ⇒ 排序後的 `Decomp::encs` 是 G 之完全不變量（`decomp_key`）。
/// 2. **積公式**：Aut(G) ≅ Π_{同構類} ( Aut(C) ≀ S_m )，故
///    |Aut(G)| = Π_{同構類} ( |Aut(C)|^m · m! )，其中 m 為該類的分量個數。
/// 3. **塊規範編碼**：把各分量的規範標號按編碼字典序排序後「塊狀拼接」，
///    得到 `block_encoding`。它是**另一個**完全不變量（等價於分量多集），
///    但與引擎之全域最小編碼 `canon_encoding` **不必逐位相同**：
///    列主序編碼的全域最小化會把零列提前，因而不相鄰地散布分量
///    （反例：2K₂⊔K₁ 之最小編碼為 `0000010100`，塊拼接為 `0010000001`）。
///    兩者皆為同構類之完整代表；`decomp_key_equal` 用前者（可證明單射），
///    `decomp_cert` 檢驗後者之重標號不變性與冪等性。
///
/// **複雜度收益**：整體搜索 O(search(G)) → Σ_i O(search(C_i)) + O(k log k)。
/// 對「多重同構分量」的高對稱圖收益最大：例如 2×Petersen 之 |Aut| = 120²·2 = 28800，
/// 直接搜索要在 28800 個並列葉子間反覆打平；積公式 + 派生生成元則瞬間完成。

///|
/// 分解結果：分量（已按規範編碼排序）、其規範資料、以及同構類分組。
pub(all) struct Decomp {
  n : Int32
  /// 分量之頂點集（全域編號），依規範順序排列
  comps : Array[Array[Int32]]
  /// 分量之導出子圖（區域編號 0..s-1）
  graphs : Array[Graph]
  /// 分量之規範標號（區域位置 → 區域頂點）
  labs : Array[Array[Int32]]
  /// 分量之規範編碼（已排序：同構分量之編碼相同）
  encs : Array[Array[Int32]]
  /// 分量之 |Aut|
  auts : Array[Int64]
  /// 分量之 Aut 生成元（區域置換）
  gens : Array[Array[Perm]]
  /// 各分量在全域規範標號中的起始位置
  offsets : Array[Int32]
  /// 各分量所屬同構類
  cls_of : Array[Int32]
  /// 各同構類之分量個數 m
  cls_count : Array[Int32]
}

///|
/// Int64 冪（帶溢位偵測：溢位回 -1L）。
fn ipow_chk(a : Int64, e : Int32) -> Int64 {
  if a < 0L {
    return -1L
  }
  let mut r = 1L
  for _ in 0..<e {
    let nx = imul_chk(r, a)
    guard nx >= 0L else { return -1L }
    r = nx
  }
  r
}

///|
/// Int64 乘法（溢位回 -1L）。以 Double 預估商界。
fn imul_chk(a : Int64, b : Int64) -> Int64 {
  if a <= 0L || b <= 0L {
    return if a == 0L || b == 0L { 0L } else { -1L }
  }
  let max = 9223372036854775807L
  if b > max / a {
    return -1L
  }
  a * b
}

///|
/// 階乘（Int64，溢位回 -1L）。
fn ifact_chk(m : Int32) -> Int64 {
  let max = 9223372036854775807L
  let mut r = 1L
  for i in 2..<(m + 1) {
    let b = i.to_int64()
    if b > max / r {
      return -1L
    }
    r = r * b
  }
  r
}

///|
/// 分量排序鍵比較：先比編碼長度（= s(s-1)/2），再比字典序。
fn cmp_enc(a : Array[Int32], b : Array[Int32]) -> Int32 {
  cmp_arr(a, b)
}

///|
/// 分解：求連通分量 → 逐分量規範化 → 依規範編碼排序 → 分同構類。
pub fn decompose(g : Graph) -> Decomp {
  let n = g.order()
  let raw = g.components()
  let k = raw.length()
  // 逐分量搜索（小問題；彼此獨立 ⇒ 可平行化）
  let subg : Array[Graph] = []
  let subl : Array[Array[Int32]] = []
  let sube : Array[Array[Int32]] = []
  let suba : Array[Int64] = []
  let subg_ens : Array[Array[Perm]] = []
  for c in raw {
    let sub = g.induced_subgraph(c)
    let res = search_graph(sub, true)
    subg.push(sub)
    subl.push(res.canon_lab)
    sube.push(res.canon_enc)
    let grp = PermGroup::new(sub.order(), res.aut_gens)
    suba.push(grp.order())
    subg_ens.push(res.aut_gens)
  }
  // 依規範編碼排序（分量之順序在全域規範標號中由此決定）
  let ord : Array[Int32] = []
  for i in 0..<k {
    ord.push(i)
  }
  ord.sort_by(fn(a : Int32, b : Int32) -> Int32 { cmp_enc(sube[a], sube[b]) })
  let comps : Array[Array[Int32]] = []
  let graphs : Array[Graph] = []
  let labs : Array[Array[Int32]] = []
  let encs : Array[Array[Int32]] = []
  let auts : Array[Int64] = []
  let gens : Array[Array[Perm]] = []
  let offsets : Array[Int32] = []
  let mut off = 0
  for i in ord {
    comps.push(raw[i])
    graphs.push(subg[i])
    labs.push(subl[i])
    encs.push(sube[i])
    auts.push(suba[i])
    gens.push(subg_ens[i])
    offsets.push(off)
    off = off + raw[i].length()
  }
  // 同構類：排序後同構分量相鄰 ⇒ 線性分組
  let cls_of = Array::make(k, 0)
  let cls_count : Array[Int32] = []
  let mut c = 0
  for i in 0..<k {
    if i > 0 && cmp_enc(encs[i], encs[i - 1]) == 0 {
      cls_of[i] = c
      cls_count[c] = cls_count[c] + 1
    } else {
      c = if i == 0 { 0 } else { c + 1 }
      cls_of[i] = c
      cls_count.push(1)
    }
  }
  { n, comps, graphs, labs, encs, auts, gens, offsets, cls_of, cls_count, }
}

///|
/// 同構類數。
pub fn Decomp::class_count(self : Decomp) -> Int32 {
  self.cls_count.length()
}

///|
/// 分量數。
pub fn Decomp::block_count(self : Decomp) -> Int32 {
  self.comps.length()
}

///|
/// 塊規範編碼：把各分量之規範編碼按其全域偏移嵌入（塊狀拼接）。
/// 分量之間無邊 ⇒ 跨分量位元皆為 0。為完全不變量（≅ 類之代表）。
pub fn Decomp::block_encoding(self : Decomp) -> Array[Int32] {
  let n = self.n
  let total = n * (n - 1) / 2
  let enc = Array::make(total, 0)
  for t in 0..<self.comps.length() {
    let off = self.offsets[t]
    let s = self.comps[t].length()
    let e = self.encs[t]
    for j in 1..<s {
      for i in 0..<j {
        if e[enc_index(i, j)] != 0 {
          enc[enc_index(off + i, off + j)] = 1
        }
      }
    }
  }
  enc
}

///|
/// 塊規範標號：位置 → 原頂點（分量按規範順序塊狀排列）。
pub fn Decomp::labeling(self : Decomp) -> Array[Int32] {
  let lab = Array::make(self.n, 0)
  for t in 0..<self.comps.length() {
    let off = self.offsets[t]
    let c = self.comps[t]
    let l = self.labs[t]
    for i in 0..<c.length() {
      lab[off + i] = c[l[i]]
    }
  }
  lab
}

///|
/// 塊規範形式圖（≅ 類之典範代表；與 `canonical_form` 同構但標號約定不同）。
pub fn Decomp::canonical_form(self : Decomp) -> Graph {
  // 由塊規範編碼直接重建（避免重標號之邊列表開銷）
  let enc = self.block_encoding()
  let edges : Array[(Int32, Int32)] = []
  for j in 1..<self.n {
    for i in 0..<j {
      if enc[enc_index(i, j)] != 0 {
        edges.push((i, j))
      }
    }
  }
  Graph::from_edges(self.n, edges)
}

///|
/// 積公式：|Aut(G)| = Π_類 ( |Aut(C)|^m · m! )。溢位回 -1L。
pub fn Decomp::aut_order(self : Decomp) -> Int64 {
  let max = 9223372036854775807L
  let mut r = 1L
  let mut t = 0
  for c in 0..<self.cls_count.length() {
    let m = self.cls_count[c]
    let a = self.auts[t]
    guard a >= 0L else { return -1L }
    let p = ipow_chk(a, m)
    guard p >= 0L else { return -1L }
    let f = ifact_chk(m)
    guard f >= 0L else { return -1L }
    guard p <= max / f else { return -1L }
    let term = p * f
    guard term <= max / r else { return -1L }
    r = r * term
    t = t + m
  }
  r
}

///|
/// 積公式之 Double 版（用於 |Aut| 超出 Int64 之情形，如空圖 E_60 ⇒ 60!）。
pub fn Decomp::aut_order_double(self : Decomp) -> Double {
  let mut r = 1.0
  let mut t = 0
  for c in 0..<self.cls_count.length() {
    let m = self.cls_count[c]
    let a = self.auts[t].to_double()
    for _ in 0..<m {
      r = r * a
    }
    let mut f = 1.0
    for i in 2..<(m + 1) {
      f = f * i.to_double()
    }
    r = r * f
    t = t + m
  }
  r
}

///|
/// 區域置換嵌入全域（固定分量外之點）。
fn embed_perm(comp : Array[Int32], p : Perm, n : Int32) -> Perm {
  let img = Array::make(n, 0)
  for v in 0..<n {
    img[v] = v
  }
  for i in 0..<comp.length() {
    img[comp[i]] = comp[p.apply(i)]
  }
  Perm::from_img(img)
}

///|
/// 兩個同構分量之互換置換（以規範標號對齊 ⇒ 必為 G 之自同構）。
fn swap_perm(
  ca : Array[Int32],
  la : Array[Int32],
  cb : Array[Int32],
  lb : Array[Int32],
  n : Int32,
) -> Perm {
  let img = Array::make(n, 0)
  for v in 0..<n {
    img[v] = v
  }
  for i in 0..<ca.length() {
    let a = ca[la[i]]
    let b = cb[lb[i]]
    img[a] = b
    img[b] = a
  }
  Perm::from_img(img)
}

///|
/// 派生生成元：Aut(G) = Π_類 (Π_i Aut(C_i)) ⋊ S_m。
/// - 每個分量之 Aut 生成元嵌入全域；
/// - 同類分量間以「第 0 塊 ↔ 第 k 塊」互換生成 S_m。
pub fn Decomp::aut_generators(self : Decomp) -> Array[Perm] {
  let out : Array[Perm] = []
  let k = self.comps.length()
  for t in 0..<k {
    for p in self.gens[t] {
      if !p.is_identity() {
        out.push(embed_perm(self.comps[t], p, self.n))
      }
    }
  }
  let mut t = 0
  for c in 0..<self.cls_count.length() {
    let m = self.cls_count[c]
    for j in 1..<m {
      out.push(
        swap_perm(
          self.comps[t],
          self.labs[t],
          self.comps[t + j],
          self.labs[t + j],
          self.n,
        ),
      )
    }
    t = t + m
  }
  out
}

///|
/// 派生自同構群（SGS 建構；其階應等於積公式）。
pub fn Decomp::automorphism_group(self : Decomp) -> PermGroup {
  PermGroup::new(self.n, self.aut_generators())
}

///|
/// 分解式規範形式（衍生演算法之入口）。
pub fn canonical_form_decomposed(g : Graph) -> Graph {
  decompose(g).canonical_form()
}

///|
/// 分解式規範編碼。
pub fn block_encoding_of(g : Graph) -> Array[Int32] {
  decompose(g).block_encoding()
}

///|
/// 分解式 |Aut|（積公式）。
pub fn aut_order_decomposed(g : Graph) -> Int64 {
  decompose(g).aut_order()
}

///|
/// 分解鍵相等（分量規範編碼之多集相等）：可證明之完全不變量。
pub fn decomp_key_equal(d1 : Decomp, d2 : Decomp) -> Bool {
  guard d1.n == d2.n && d1.comps.length() == d2.comps.length() else {
    return false
  }
  for t in 0..<d1.comps.length() {
    guard cmp_enc(d1.encs[t], d2.encs[t]) == 0 else { return false }
  }
  true
}

///|
/// 分解式同構判定：比較完全不變量 `encs`（排序後之分量規範編碼序列）。
pub fn isomorphic_decomposed(g1 : Graph, g2 : Graph) -> Bool {
  guard g1.order() == g2.order() && g1.size() == g2.size() else { return false }
  decomp_key_equal(decompose(g1), decompose(g2))
}

///|
/// 分解式顯式同構 σ : G1 → G2（逐分量以規範標號對齊；附驗證證書）。
pub fn isomorphism_decomposed(g1 : Graph, g2 : Graph) -> Perm? {
  guard isomorphic_decomposed(g1, g2) else { return None }
  let d1 = decompose(g1)
  let d2 = decompose(g2)
  let n = d1.n
  if n == 0 {
    return Some(Perm::identity(0))
  }
  let img = Array::make(n, 0)
  for t in 0..<d1.comps.length() {
    let c1 = d1.comps[t]
    let c2 = d2.comps[t]
    let l1 = d1.labs[t]
    let l2 = d2.labs[t]
    for i in 0..<c1.length() {
      img[c1[l1[i]]] = c2[l2[i]]
    }
  }
  let s = Perm::from_img(img)
  // 證書：逐邊驗證
  for e in g1.edge_list() {
    let (u, v) = e
    guard g2.has_edge(s.apply(u), s.apply(v)) else { return None }
  }
  Some(s)
}

///|
/// 分解定理之機器證書：
/// (a) 塊規範編碼之重標號不變性（σ 隨機，由呼叫端給定）；
/// (b) 積公式 == 引擎 |Aut|（積公式定理）；
/// (c) 派生生成元皆為真自同構、引擎生成元皆在派生群中、且階相同
///     （Aut(G) ≅ Π (Aut(C) ≀ S_m) 之生成完整性）；
/// (d) 塊規範形式之冪等性（再分解得到相同鍵）。
/// 回傳 (a, b, c, d)。
pub fn decomp_cert(g : Graph, sigma : Perm) -> (Bool, Bool, Bool, Bool) {
  let d = decompose(g)
  let res = search_graph(g, true)
  let a = cmp_enc(
      d.block_encoding(),
      decompose(g.relabel(sigma)).block_encoding(),
    ) ==
    0
  let grp = PermGroup::new(g.order(), res.aut_gens)
  let b = d.aut_order() == grp.order()
  // (c) 派生生成元皆為自同構，且與引擎生成同一群
  let dgens = d.aut_generators()
  let mut c = true
  for p in dgens {
    if !is_automorphism(g, p) {
      c = false
      break
    }
  }
  if c {
    let dgrp = PermGroup::new(g.order(), dgens)
    for p in res.aut_gens {
      if !dgrp.contains(p) {
        c = false
        break
      }
    }
    if c && dgrp.order() != grp.order() {
      c = false
    }
  }
  // (d) 冪等：塊規範形式再分解 ⇒ 同一分解鍵
  let cf = d.canonical_form()
  let dd = decomp_key_equal(decompose(cf), d)
  (a, b, c, dd)
}

///|
/// 分解摘要（展示用）。
pub fn Decomp::summary(self : Decomp) -> String {
  let nb = self.comps.length()
  let nc = self.cls_count.length()
  let mut s = "Decomp(n=" + self.n.to_string() + ", blocks=" + nb.to_string()
  s = s + ", classes=" + nc.to_string() + ")"
  let mut t = 0
  for c in 0..<nc {
    let m = self.cls_count[c]
    let sz = self.comps[t].length()
    let ord = self.auts[t]
    s = s + " class" + c.to_string() + ": " + m.to_string() + " x size"
    s = s + sz.to_string() + ", |Aut(C)|=" + ord.to_string() + ";"
    t = t + m
  }
  s = s + " |Aut(G)|=" + self.aut_order().to_string()
  s
}

///|
pub impl Show for Decomp with fn to_string(self) {
  self.summary()
}

///|
pub extend Decomp with Show::{to_string, output}

///|
/// Debug（供 `assert_eq` / `inspect` 之結構化差異顯示；與 Show 同一摘要）。
pub impl Debug for Decomp with fn to_repr(self) {
  Repr::literal(self.to_string())
}

///|
pub extend Decomp with Debug::{to_repr}
