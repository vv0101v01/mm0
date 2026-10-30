///|
/// # Canon — 規範形式（Canonical Form）
///
/// 規範形式 = 同構類的完全不變量：G ≅ H ⇔ canon(G) = canon(H)。
/// 由 search_graph 的個體化-精煉引擎直接產出：
/// - `canonical_labeling`：規範標號（位置 → 原頂點）
/// - `canonical_form`：規範標號下的圖（重標號像）
/// - `canon_digest`：編碼位串之十六進制指紋（等價判定 O(n²/64)）
/// - `isomorphism`：由兩圖的規範標號合成顯式同構映射

///|
/// 圖的規範標號：位置 i 的頂點為 lab[i]。
pub fn canonical_labeling(g : Graph) -> Array[Int32] {
  search_graph(g, true).canon_lab
}

///|
/// 規範標號陣列 → 重標號置換 σ：σ(lab[i]) = i（第 i 個規範位置由原頂點 lab[i] 佔據）。
/// 這是 `canonical_form` 所用之 σ；任何在原標號下算得之自同構 p，
/// 搬到規範標號下即 `p.conjugate_by(labeling_perm(lab))` = σ∘p∘σ⁻¹。
/// **衍生用途**：一次搜索即可同時得到規範圖與（規範標號下之）自同構群，免第二次搜索。
pub fn labeling_perm(lab : Array[Int32]) -> Perm {
  let n = lab.length()
  let img = Array::make(n, 0)
  for i in 0..<n {
    img[lab[i]] = i
  }
  Perm::from_img(img)
}

///|
/// 規範編碼（0/1 序列，列主序 idx(i,j)=j(j-1)/2+i）。
pub fn canon_encoding(g : Graph) -> Array[Int32] {
  search_graph(g, true).canon_enc
}

///|
/// 規範形式圖：以規範標號重排頂點後的圖。
pub fn canonical_form(g : Graph) -> Graph {
  let res = search_graph(g, true)
  g.relabel(labeling_perm(res.canon_lab))
}

///|
/// 位串打包為 64-bit 字組。
pub fn pack_bits(bits : Array[Int32]) -> Array[Int64] {
  let words = (bits.length() + 63) / 64
  let out = Array::make(words, 0L)
  for i, b in bits {
    if b != 0 {
      out[i / 64] = out[i / 64] | (1L << (i % 64))
    }
  }
  out
}

///|
/// 十六進制字元。
fn hex_digit(d : Int32) -> String {
  let digits = [
    "0", "1", "2", "3", "4", "5", "6", "7", "8", "9", "a", "b", "c", "d", "e", "f",
  ]
  digits[d]
}

///|
/// 規範指紋：n + 編碼位串之十六進制（同構 ⇔ 指紋相同）。
pub fn canon_digest(g : Graph) -> String {
  let res = search_graph(g, true)
  // 十六進位打包由 `digest_from`（report.mbt）統一負責（去重）
  digest_from(res.n, res.canon_enc)
}

///|
/// 同構判定（完整不變量比較）。
pub fn isomorphic(g1 : Graph, g2 : Graph) -> Bool {
  guard g1.order() == g2.order() && g1.size() == g2.size() else { return false }
  // 快速否證：結構不變量（度序列 + 精煉顏色）
  guard graph_invariant(g1) == graph_invariant(g2) else { return false }
  canon_digest(g1) == canon_digest(g2)
}

///|
/// 顯式同構 σ : G1 → G2（不存在則 None）。合成方式：
/// σ = lab2 ∘ lab1^{-1}（兩圖的規範標號把同一規範位置映到各自頂點）。
pub fn isomorphism(g1 : Graph, g2 : Graph) -> Perm? {
  guard g1.order() == g2.order() && g1.size() == g2.size() else { return None }
  let n = g1.order()
  if n == 0 {
    return Some(Perm::identity(0))
  }
  let r1 = search_graph(g1, true)
  let r2 = search_graph(g2, true)
  guard cmp_arr(r1.canon_enc, r2.canon_enc) == 0 else { return None }
  let img = Array::make(n, 0)
  for i in 0..<n {
    img[r1.canon_lab[i]] = r2.canon_lab[i]
  }
  let s = Perm::from_img(img)
  // 驗證：G1 的每條邊映為 G2 的邊
  for e in g1.edge_list() {
    let (u, v) = e
    guard g2.has_edge(s.apply(u), s.apply(v)) else { return None }
  }
  Some(s)
}

///|
/// 自同構驗證：σ ∈ Aut(G) ⇔ 重標號像等於原圖。
pub fn is_automorphism(g : Graph, s : Perm) -> Bool {
  guard s.size() == g.order() else { return false }
  for e in g.edge_list() {
    let (u, v) = e
    guard g.has_edge(s.apply(u), s.apply(v)) else { return false }
  }
  true
}

///|
/// 有色圖規範鍵：依序為規範位置上的正規化顏色列與鄰接編碼。
/// 顏色列必須與鄰接編碼一起比較；只比後者會退化成無色同構。
pub fn colored_canonical_key(
  g : Graph,
  colors : Array[Int32],
) -> (Array[Int32], Array[Int32]) {
  guard colors.length() == g.order() else {
    abort("colored_canonical_key: color length mismatch")
  }
  let normalized = recolor(colors.copy())
  let res = search_graph_colored(g, normalized, true)
  let seq = Array::make(g.order(), 0)
  for i in 0..<g.order() {
    seq[i] = normalized[res.canon_lab[i]]
  }
  (seq, res.canon_enc)
}

///|
/// 有色圖同構判定（固定顏色標籤，不允許全域重命名顏色）。
pub fn isomorphic_colored(
  g1 : Graph,
  colors1 : Array[Int32],
  g2 : Graph,
  colors2 : Array[Int32],
) -> Bool {
  guard g1.order() == g2.order() && g1.size() == g2.size() else { return false }
  let (seq1, enc1) = colored_canonical_key(g1, colors1)
  let (seq2, enc2) = colored_canonical_key(g2, colors2)
  cmp_arr(seq1, seq2) == 0 && cmp_arr(enc1, enc2) == 0
}
