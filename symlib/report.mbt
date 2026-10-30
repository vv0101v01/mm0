///|
/// # Report — 統一分析管線（一次搜索，多模組消費）
///
/// 架構管理：search_graph 的單次結果同時餵給
/// 規範形式（canon）/ 自同構群（aut+group）/ 群作用（action）/
/// 軌道折疊（fold）/ 範疇化摘要（cat），避免重複搜索。
/// 並以單子線程化：StateM 累積統計，ListM 列舉全部同構。

///|
/// 對稱性分析報告（各演算法模組的共享作用域產物）。
pub(all) struct SymmetryReport {
  n : Int32
  m : Int32
  canon_lab : Array[Int32]
  digest : String
  aut_gens : Array[Perm]
  group : PermGroup
  order : Int64
  vertex_orbits : Array[Array[Int32]]
  edge_orbits : Array[(Int32, Int32)]
  edge_orbit_sizes : Array[Int32]
  folded : FoldedGraph
  nodes : Int32
  leaves : Int32
}

///|
/// 搜索統計（StateM 的狀態）。
pub(all) struct SearchStats {
  nodes : Int32
  leaves : Int32
  autos : Int32
}

///|
/// 由編碼直接計算指紋（canon 與 report 共用）。
pub fn digest_from(n : Int32, enc : Array[Int32]) -> String {
  let words = pack_bits(enc)
  let mut s = "n\{n}:"
  for w in words {
    for k in 0..<16 {
      let d = ((w >> (60 - k * 4)) & 15L).to_int()
      s = s + hex_digit(d)
    }
  }
  s
}

///|
/// 一次性完整分析（規範形式 + 自同構群 + 軌道折疊 + 統計）。
pub fn analyze(g : Graph) -> SymmetryReport {
  let res = search_graph(g, true)
  let group = PermGroup::new(g.order(), res.aut_gens)
  let folded = fold_graph(g, group)
  let (ereps, esizes) = fold_edges(g, group)
  {
    n: g.order(),
    m: g.size(),
    canon_lab: res.canon_lab,
    digest: digest_from(res.n, res.canon_enc),
    aut_gens: res.aut_gens,
    group,
    order: group.order(),
    vertex_orbits: group.orbit_partition(),
    edge_orbits: ereps,
    edge_orbit_sizes: esizes,
    folded,
    nodes: res.nodes,
    leaves: res.leaves,
  }
}

///|
/// StateM 版分析：統計以狀態線程化（單子與管線的交互）。
pub fn analyze_m(g : Graph) -> StateM[SearchStats, SymmetryReport] {
  StateM::pure(()).bind(fn(_) {
    let res = search_graph(g, true)
    let upd = fn(s : SearchStats) -> SearchStats {
      {
        nodes: s.nodes + res.nodes,
        leaves: s.leaves + res.leaves,
        autos: s.autos + res.aut_gens.length(),
      }
    }
    StateM::modify(upd).bind(fn(_) {
      let group = PermGroup::new(g.order(), res.aut_gens)
      let folded = fold_graph(g, group)
      let (ereps, esizes) = fold_edges(g, group)
      StateM::pure({
        n: g.order(),
        m: g.size(),
        canon_lab: res.canon_lab,
        digest: digest_from(res.n, res.canon_enc),
        aut_gens: res.aut_gens,
        group,
        order: group.order(),
        vertex_orbits: group.orbit_partition(),
        edge_orbits: ereps,
        edge_orbit_sizes: esizes,
        folded,
        nodes: res.nodes,
        leaves: res.leaves,
      })
    })
  })
}

///|
/// StateM 版規範標號（只取標號，統計入狀態）。
pub fn canonical_labeling_m(g : Graph) -> StateM[SearchStats, Array[Int32]] {
  analyze_m(g).map(fn(r : SymmetryReport) -> Array[Int32] { r.canon_lab })
}

///|
/// ListM 版同構列舉：全部同構 σ : G1 → G2（= 一個基同構 ∘ Aut(G1)）。
/// 僅適合小群（cap 限制列舉規模）；非同構則回傳空單子。
pub fn isomorphisms_m(g1 : Graph, g2 : Graph, cap : Int32) -> ListM[Perm] {
  match isomorphism(g1, g2) {
    None => { arr: [], }
    Some(base) => {
      let auts = automorphism_group(g1).elements(cap)
      ListM::from_array(auts).map(fn(a : Perm) -> Perm { base.compose(a) })
    }
  }
}

///|
/// 報告摘要文字（一行式，供 CLI / 測試 inspect）。
pub fn SymmetryReport::summary(self : SymmetryReport) -> String {
  let mut s = "SymmetryReport(n=\{self.n}, m=\{self.m}, |Aut|=\{self.order}"
  s = s +
    ", orbits=\{self.vertex_orbits.length()}, edge_orbits=\{self.edge_orbits.length()}"
  s = s +
    ", fold=\{self.folded.k}/\{self.n}, nodes=\{self.nodes}, leaves=\{self.leaves})"
  s
}

///|
/// 完整報告（多行）。
pub fn SymmetryReport::to_report_string(self : SymmetryReport) -> String {
  let mut s = self.summary() + "\n"
  s = s + "  canon_lab = ["
  for i, v in self.canon_lab {
    if i > 0 {
      s = s + ","
    }
    s = s + v.to_string()
  }
  s = s + "]\n"
  s = s + "  digest    = \{self.digest}\n"
  s = s + "  aut_gens  = ["
  for i, g in self.aut_gens {
    if i > 0 {
      s = s + ", "
    }
    s = s + g.to_string()
  }
  s = s + "]\n"
  s = s + "  orbits    = ["
  for i, o in self.vertex_orbits {
    if i > 0 {
      s = s + ", "
    }
    s = s + "{"
    for j, v in o {
      if j > 0 {
        s = s + ","
      }
      s = s + v.to_string()
    }
    s = s + "}"
  }
  s = s + "]\n"
  s = s + "  folded    = \{self.folded.summary()}"
  s
}

///|
pub impl Show for SymmetryReport with fn to_string(self) {
  self.summary()
}

///|
pub extend SymmetryReport with Show::{to_string, output}

///|
/// Debug（供 `assert_eq` / `inspect` 之結構化差異顯示；與 Show 同一摘要）。
pub impl Debug for SymmetryReport with fn to_repr(self) {
  Repr::literal(self.to_string())
}

///|
pub extend SymmetryReport with Debug::{to_repr}

///|
/// 整數陣列之緊湊字串 `"[1,2,3]"`。
/// 去債：報告、證書 detail、測試斷言訊息原先各自手寫拼接迴圈（≥4 份）。
pub fn ints_to_string(a : Array[Int32]) -> String {
  let mut s = "["
  for i, v in a {
    if i > 0 {
      s = s + ","
    }
    s = s + v.to_string()
  }
  s + "]"
}

///|
/// 整數矩陣之緊湊字串（逐列 `ints_to_string` 串接）——標記矩陣等之展示/斷言用。
pub fn int_rows_to_string(m : Array[Array[Int32]]) -> String {
  let mut s = ""
  for row in m {
    s = s + ints_to_string(row)
  }
  s
}
