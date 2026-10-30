///|
/// # Dual — 補圖對偶（衍生演算法 II）
///
/// 由「規範形式」導出的第二族衍生演算法，基礎是兩條定理：
///
/// **對偶定理 1（自同構不變）**：Aut(G) = Aut(Ḡ)。
/// 任何保持鄰接的置換也保持非鄰接 ⇒ 補圖不改變自同構群。
///
/// **對偶定理 2（編碼對偶）**：同一標號 λ 下 enc_λ(Ḡ) = mask ⊕ enc_λ(G)。
/// 定義 G 之**對偶規範編碼** `dual_enc(G) := mask ⊕ canon_enc(Ḡ)`：
/// - 它由標號 λ = canon_lab(Ḡ) **實現**（即確為 G 在某標號下之編碼，`dual_cert` (b) 驗證）；
/// - 它是 G 之**第二個完全不變量**：G ≅ H ⇔ Ḡ ≅ H̄ ⇔ canon_enc(Ḡ) = canon_enc(H̄)
///   ⇔ dual_enc(G) = dual_enc(H)（⊕ mask 為雙射）。
/// 注意：本引擎之 `canon_enc` 是「等變且完整」之規範編碼，**不必**是全域字典序最小者，
/// 故 `dual_enc(G)` 亦不必是 G 之最大編碼；兩者同為同構類之典範代表。
///
/// **衍生演算法**：搜索代價隨度（精煉時 Σ_v deg(v) 之鄰接掃描）上升，
/// 故對稠密圖改為搜索其稀疏補圖，再把結果映射回來：
/// - `canonical_dual`：自動選擇稀疏側，回傳 (dual 旗標, 規範編碼, 規範標號, Aut 生成元)；
/// - `isomorphic_dual` / `isomorphism_dual`：分支由 (n, m) 決定，
///   而 (n, m) 是同構不變量 ⇒ 同構圖必走同一分支 ⇒ 判定正確；
///   且 Ḡ → H̄ 的同構就是 G → H 的同構（同一置換），映射可直接沿用。
/// - `automorphism_group_dual`：由對偶定理 1，稠密圖之 Aut 直接取自補圖。

///|
/// n 個頂點之無序對數。
fn pair_count(n : Int32) -> Int32 {
  n * (n - 1) / 2
}

///|
/// 位元反轉（於 n(n-1)/2 位元之內）。
fn xor_mask(enc : Array[Int32]) -> Array[Int32] {
  let out = Array::make(enc.length(), 0)
  for i, b in enc {
    out[i] = 1 - b
  }
  out
}

///|
/// 是否走「補圖側」：m·2 > n(n-1)/2（严格稠密）。
/// 只依賴 (n, m) ⇒ 同構圖必得同一答案。
pub fn is_dual_side(g : Graph) -> Bool {
  g.size() * 2 > pair_count(g.order())
}

///|
/// 對偶規範資料。`dual = true` 表示搜索在補圖側進行，
/// `enc` = 補圖規範編碼之位元對偶（= G 之對偶規範編碼），`lab` 為實現它之標號。
pub(all) struct DualCanon {
  n : Int32
  m : Int32
  dual : Bool
  enc : Array[Int32]
  lab : Array[Int32]
  aut_gens : Array[Perm]
  nodes : Int32
}

///|
/// 對偶規範化：自動選稀疏側搜索。
pub fn canonical_dual(g : Graph) -> DualCanon {
  let n = g.order()
  let dual = is_dual_side(g)
  let target = if dual { g.complement() } else { g }
  let res = search_graph(target, true)
  let enc = if dual { xor_mask(res.canon_enc) } else { res.canon_enc }
  {
    n,
    m: g.size(),
    dual,
    enc,
    lab: res.canon_lab,
    aut_gens: res.aut_gens,
    nodes: res.nodes,
  }
}

///|
/// G 之對偶規範編碼（= mask ⊕ canon_enc(Ḡ)；對偶定理 2）。
pub fn canon_encoding_dual(g : Graph) -> Array[Int32] {
  xor_mask(canon_encoding(g.complement()))
}

///|
/// **一次搜索，兩份規範形式**：G 與 Ḡ 共用同一 Aut 群（對偶定理 1），
/// 且兩者之規範編碼互為位元對偶（對偶定理 2）⇒ 只需在稀疏側搜索一次。
/// 回傳 (canon(G), canon(Ḡ))。
/// 退化情形 m = n(n-1)/4（自補邊數）時兩側同分支，需兩次搜索。
/// 一般情形省下 50% 搜索成本。
pub fn dual_pair(g : Graph) -> (DualCanon, DualCanon) {
  let c = g.complement()
  let d1 = is_dual_side(g)
  let d2 = is_dual_side(c)
  if d1 == d2 {
    return (canonical_dual(g), canonical_dual(c))
  }
  // 稀疏側只搜一次；兩份規範形式由位元對偶互推
  let sparse = if d1 { c } else { g }
  let res = search_graph(sparse, true)
  let enc_plain = res.canon_enc
  let enc_dual = xor_mask(res.canon_enc)
  let n = g.order()
  let mk = fn(m : Int32, dual : Bool) -> DualCanon {
    {
      n,
      m,
      dual,
      enc: if dual {
        enc_dual
      } else {
        enc_plain
      },
      lab: res.canon_lab,
      aut_gens: res.aut_gens,
      nodes: res.nodes,
    }
  }
  (mk(g.size(), d1), mk(c.size(), d2))
}

///|
/// 雙通道交叉驗證：在 G 與 Ḡ 上**獨立**運行引擎，要求
/// |Aut(G)| == |Aut(Ḡ)| 且兩群互相包含（對偶定理 1 之機器驗證）。
/// 這是無需外部參考實作之自我驗證手段（雙式記帳）。
pub fn dual_cross_check(g : Graph) -> Bool {
  let g1 = PermGroup::new(g.order(), search_graph(g, true).aut_gens)
  let g2 = PermGroup::new(
    g.order(),
    search_graph(g.complement(), true).aut_gens,
  )
  guard g1.order() == g2.order() else { return false }
  for p in g1.generators() {
    guard g2.contains(p) else { return false }
  }
  for p in g2.generators() {
    guard g1.contains(p) else { return false }
  }
  true
}

///|
/// 對偶指紋：分支前綴 + 編碼之十六進制（同構 ⇔ 指紋相同）。
pub fn dual_digest(g : Graph) -> String {
  let d = canonical_dual(g)
  let tag = if d.dual { "D" } else { "S" }
  tag + ":" + digest_from(d.n, d.enc)
}

///|
/// 對偶同構判定。
pub fn isomorphic_dual(g1 : Graph, g2 : Graph) -> Bool {
  guard g1.order() == g2.order() && g1.size() == g2.size() else { return false }
  guard graph_invariant(g1) == graph_invariant(g2) else { return false }
  let d1 = canonical_dual(g1)
  let d2 = canonical_dual(g2)
  guard d1.dual == d2.dual else { return false }
  cmp_arr(d1.enc, d2.enc) == 0
}

///|
/// 對偶顯式同構 σ : G1 → G2。
/// 補圖側之同構即原圖之同構（同一置換），故可直接沿用規範標號合成。
pub fn isomorphism_dual(g1 : Graph, g2 : Graph) -> Perm? {
  guard g1.order() == g2.order() && g1.size() == g2.size() else { return None }
  let n = g1.order()
  if n == 0 {
    return Some(Perm::identity(0))
  }
  let d1 = canonical_dual(g1)
  let d2 = canonical_dual(g2)
  guard d1.dual == d2.dual && cmp_arr(d1.enc, d2.enc) == 0 else { return None }
  let img = Array::make(n, 0)
  for i in 0..<n {
    img[d1.lab[i]] = d2.lab[i]
  }
  let s = Perm::from_img(img)
  // 證書：在**原圖**上逐邊驗證
  for e in g1.edge_list() {
    let (u, v) = e
    guard g2.has_edge(s.apply(u), s.apply(v)) else { return None }
  }
  Some(s)
}

///|
/// 對偶自同構群：Aut(G) = Aut(Ḡ)（對偶定理 1），取稀疏側搜索結果。
pub fn automorphism_group_dual(g : Graph) -> PermGroup {
  let d = canonical_dual(g)
  PermGroup::new(g.order(), d.aut_gens)
}

///|
/// 對偶定理之機器證書：
/// (a) 補圖搜索所得生成元確為 G 之自同構，且與引擎在 G 上直接求得之群同階；
/// (b) 對偶規範編碼確由 `lab = canon_lab(Ḡ)` 達成（對偶定理 2 之實現性）；
/// (c) 對偶規範形式之重標號不變性。
/// 回傳 (a, b, c)。
pub fn dual_cert(g : Graph, sigma : Perm) -> (Bool, Bool, Bool) {
  let n = g.order()
  let total = pair_count(n)
  // (a)
  let mut a = true
  let cg = g.complement()
  let rc = search_graph(cg, true)
  let rcg = PermGroup::new(n, rc.aut_gens)
  let rg = PermGroup::new(n, search_graph(g, true).aut_gens)
  if rcg.order() != rg.order() {
    a = false
  } else {
    for p in rc.aut_gens {
      if !is_automorphism(g, p) {
        a = false
        break
      }
    }
  }
  // (b) lab 在 G 上達成 max-enc；在 Ḡ 上達成 min-enc
  let mut b = true
  let enc_g = Array::make(total, 0)
  let enc_c = Array::make(total, 0)
  for j in 1..<n {
    for i in 0..<j {
      let u = rc.canon_lab[i]
      let v = rc.canon_lab[j]
      if g.has_edge(u, v) {
        enc_g[enc_index(i, j)] = 1
      } else {
        enc_c[enc_index(i, j)] = 1
      }
    }
  }
  if cmp_arr(enc_c, rc.canon_enc) != 0 ||
    cmp_arr(xor_mask(rc.canon_enc), enc_g) != 0 {
    b = false
  }
  // (c)
  let d1 = canonical_dual(g)
  let d2 = canonical_dual(g.relabel(sigma))
  let c = d1.dual == d2.dual && cmp_arr(d1.enc, d2.enc) == 0
  (a, b, c)
}

///|
/// 對偶摘要。
pub fn DualCanon::summary(self : DualCanon) -> String {
  let side = if self.dual { "dual(complement)" } else { "direct" }
  "DualCanon(n=" +
  self.n.to_string() +
  ", m=" +
  self.m.to_string() +
  ", " +
  side +
  ", nodes=" +
  self.nodes.to_string() +
  ")"
}

///|
pub impl Show for DualCanon with fn to_string(self) {
  self.summary()
}

///|
pub extend DualCanon with Show::{to_string, output}

///|
/// Debug（供 `assert_eq` / `inspect` 之結構化差異顯示；與 Show 同一摘要）。
pub impl Debug for DualCanon with fn to_repr(self) {
  Repr::literal(self.to_string())
}

///|
pub extend DualCanon with Debug::{to_repr}
