///|
/// # Theorem (all) — 全庫定理電池 `prove_all`
///
/// `prove_all(cap)` 一次跑完 20 條跨模組定理證書（範疇公理、(co)limit 泛性質、米田引理、
/// Kan = 歸納/上歸納、Frobenius 互反、單子律、CSP=極限 vs 單子搜索、Cayley、標記矩陣、
/// SGS 元素表、已知 |Aut| 文獻值…），並由 `cert_report` 彙整。
/// 每條證書皆為**有限情形之逐點計算**：以一條演算法驗證另一條演算法。
///
/// 編號註解（`// 1 …`、`// 2 …`）與 `Cert.name` 一一對應，便於定位失敗項。

///|
/// # Theorem (all) — 全庫定理電池 `prove_all`
///
/// `prove_all(cap)` 一次跑完 20 條跨模組定理證書（範疇公理、(co)limit 泛性質、米田引理、
/// Kan = 歸納/上歸納、Frobenius 互反、單子律、CSP=極限 vs 單子搜索、Cayley、標記矩陣、
/// SGS 元素表、已知 |Aut| 文獻值…），並由 `cert_report` 彙整。
/// 每條證書皆為**有限情形之逐點計算**：以一條演算法驗證另一條演算法。
///
/// 編號註解（`// 1 …`、`// 2 …`）與 `Cert.name` 一一對應，便於定位失敗項。

///|
/// 全庫定理電池：範疇 / 單子 / 群作用 / G-集 / Cayley / CSP。
pub fn prove_all(cap : Int32) -> Array[Cert] {
  let out : Array[Cert] = []
  // 1 範疇公理
  let cats : Array[FinCat] = [
    cat_discrete(3),
    cat_terminal(),
    cat_arrow(),
    cat_cospan(),
    cat_span(),
    cat_poset(3, [(0, 1), (1, 2)]),
    cat_parallel(),
    cat_group(PermGroup::symmetric(3), cap),
  ]
  let mut ok1 = true
  for c in cats {
    if !is_category(c) {
      ok1 = false
    }
  }
  out.push(
    cert(
      "category-axioms", ok1, "8 個建構（含 BG）之恆等律與結合律窮舉成立",
    ),
  )
  // 2 (co)limit 之泛性質計數
  let f = FinMap::new(4, 3, [0, 1, 1, 2])
  let gm = FinMap::new(4, 3, [0, 0, 1, 2])
  let eqs = equalizer_set(f, gm)
  let mut beq = 0
  for x in 0..<4 {
    if f.img[x] == gm.img[x] {
      beq = beq + 1
    }
  }
  let pbs = pullback_set(f, gm)
  let mut bpb = 0
  for x in 0..<4 {
    for y in 0..<4 {
      if f.img[x] == gm.img[y] {
        bpb = bpb + 1
      }
    }
  }
  let ad = arrow_diagram(f)
  out.push(
    cert(
      "limits-universal",
      eqs.length() == beq &&
      pbs.length() == bpb &&
      limit_card(ad, 100000) == f.dom &&
      colimit_card(ad) == f.cod &&
      product_set(3, 4).length() == 12 &&
      coproduct_card(3, 4) == 7,
      "等化子/拉回/箭頭圖之 limit=A,colimit=B/積/餘積 皆與暴力計數一致",
    ),
  )
  // 3 米田引理
  let pc = cat_poset(3, [(0, 1), (1, 2)])
  let p1 = presheaf_new(pc, [3, 2, 2], [
    [0, 1, 2],
    [0, 1],
    [0, 1],
    [0, 1],
    [0, 1],
    [0, 1],
  ])
  let p2 = presheaf_new(pc, [4, 3, 2], [
    [0, 1, 2, 3],
    [0, 1, 2],
    [0, 1],
    [2, 1, 0],
    [1, 2],
    [1, 0],
  ])
  let mut ok3 = is_presheaf(p1) && is_presheaf(p2)
  for p in [p1, p2] {
    for a in [0, 1, 2] {
      let (ra, rb, rc) = yoneda_roundtrip(p, a, cap)
      if !(ra && rb && rc) {
        ok3 = false
      }
    }
  }
  out.push(
    cert(
      "yoneda-lemma", ok3, "Nat(h^a,F) ≅ F(a)：兩個預層 × 三個對象，雙向映射互逆且計數相等",
    ),
  )
  // 4 Kan 沿恆等函子
  let dpos = diagram_new(pc, [3, 2, 2], [
    [0, 1, 2],
    [0, 1],
    [0, 1],
    [0, 1, 1],
    [0, 1, 1],
    [0, 1],
  ])
  let idf = id_functor(pc)
  let lid = lan(idf, dpos, cap)
  let rid = ran(idf, dpos, cap)
  out.push(
    cert(
      "kan-identity",
      is_functor(dpos) && lid.size == dpos.size && rid.size == dpos.size,
      "Lan_Id F = F = Ran_Id F（comma 範疇有終端/始端對象）",
    ),
  )
  // 5-6 Kan 沿 1 → BG = 歸納 / 上歸納
  let grp = PermGroup::symmetric(3)
  let ng = grp.order().to_int()
  let bg = cat_group(grp, cap)
  let kterm : FinFunctor = {
    src: cat_terminal(),
    dst: bg,
    obj: [0],
    mor: [bg.id[0]],
  }
  let x = 2
  let fterm = diagram_new(cat_terminal(), [x], [id_map(x)])
  let lr = lan(kterm, fterm, cap)
  let rr = ran(kterm, fterm, cap * cap)
  let elems = grp.elements(cap)
  let ind = induced_gset(grp, x, cap)
  let coi = gset_coinduced(grp, x, cap)
  let mut ok5 = is_fin_functor(kterm) && lr.size[0] == ng * x
  for m0 in 0..<bg.nmor {
    match lan_map(lr, m0, 0, 0) {
      Some(arr) =>
        if cmp_arr(arr, induced_lift(grp, x, cap, elems[m0])) != 0 {
          ok5 = false
        }
      None => ok5 = false
    }
  }
  let iorbs = FinAction::orbits(ind)
  let mut free = iorbs.length() == x
  for o in iorbs {
    if o.length() != ng {
      free = false
    }
  }
  out.push(
    cert(
      "kan-induction",
      ok5 && free,
      "Lan_{1→BG} F = G×X（|·|=" +
      lr.size[0].to_string() +
      "=" +
      ng.to_string() +
      "·" +
      x.to_string() +
      "），態射映射 = 左正則作用，" +
      iorbs.length().to_string() +
      " 個自由軌道",
    ),
  )
  let mut ok6 = rr.size[0] == pow_int(x, ng)
  for m0 in 0..<bg.nmor {
    match ran_map(rr, m0, 0, 0) {
      Some(arr) =>
        if cmp_arr(arr, coinduced_lift(grp, x, cap, elems[m0])) != 0 {
          ok6 = false
        }
      None => ok6 = false
    }
  }
  let gfix = gset_global_fixed(coi)
  out.push(
    cert(
      "kan-coinduction",
      ok6 && gfix == x,
      "Ran_{1→BG} F = X^G（|·|=" +
      rr.size[0].to_string() +
      "=" +
      x.to_string() +
      "^" +
      ng.to_string() +
      "），(Ran)^G = F ⇒ 不動點=" +
      gfix.to_string(),
    ),
  )
  // 7 Frobenius 互反（Set 版）
  let yact = gset_points(PermGroup::cyclic(3), cap)
  let (lhs, rhs) = frobenius_reciprocity(PermGroup::cyclic(3), 1, yact, 4096)
  let (l2, r2) = frobenius_reciprocity(grp, 1, gset_points(grp, cap), 4096)
  out.push(
    cert(
      "frobenius-reciprocity",
      lhs == rhs && l2 == r2,
      "|Hom_G(G×X,Y)|=" +
      lhs.to_string() +
      " = |Hom(X,res Y)|=" +
      rhs.to_string() +
      "；S₃ 版 " +
      l2.to_string() +
      "=" +
      r2.to_string(),
    ),
  )
  // 8 自由 G-集單子（伴隨之複合）
  let mut ok8 = gset_monad_laws(grp, 1, cap) && gset_monad_laws(grp, 2, cap)
  ok8 = ok8 && gset_monad_naturality(grp, FinMap::new(2, 3, [1, 2]), cap)
  out.push(
    cert(
      "monad-from-adjunction", ok8, "T=res∘Lan=G×- 之 η/μ 滿足左單位、右單位、結合律與自然性",
    ),
  )
  // 9 冪集單子（FinSet 層面）
  let mut ok9 = true
  for i in 0..<=3 {
    if !pow_monad_laws(i) {
      ok9 = false
    }
  }
  for i in 0..<=3 {
    if !pow_naturality(FinMap::new(i, 3, Array::make(i, 0))) {
      ok9 = false
    }
  }
  out.push(
    cert(
      "powerset-monad", ok9, "P 之單子律與自然性（n ≤ 3 窮舉）",
    ),
  )
  // 10 ListM / StateM 單子律
  out.push(
    cert("monad-list-state", monad_laws_cert(), "ListM/StateM/Kleisli 三律"),
  )
  // 11 約束解集 = 極限（與單子搜索交叉驗證）
  let qn = 4
  let dom : Array[Int32] = [qn, qn, qn, qn]
  let sols = csp_limit(dom, queen_constraints(qn), 100000)
  let vals : Array[Array[Int32]] = []
  for _ in 0..<qn {
    let a : Array[Int32] = []
    for r in 0..<qn {
      a.push(r)
    }
    vals.push(a)
  }
  let nd = search_nd(vals, fn(sol : Array[Int32]) -> Bool {
    for i in 0..<sol.length() {
      for j in (i + 1)..<sol.length() {
        let da = sol[i] - sol[j]
        let ad = if da < 0 { 0 - da } else { da }
        if sol[i] == sol[j] || ad == j - i {
          return false
        }
      }
    }
    true
  })
  let nda = nd.to_array()
  let mut ok11 = sols.length() == nda.length()
  for s in sols {
    let mut found = false
    for t in nda {
      if cmp_arr(s, t) == 0 {
        found = true
        break
      }
    }
    if !found {
      ok11 = false
    }
  }
  out.push(
    cert(
      "csp-limit-vs-monad",
      ok11,
      "4-皇后：limit（範疇）= " +
      sols.length().to_string() +
      " = search_nd（ListM 單子）",
    ),
  )
  // 12 Cayley 圖定理
  cert_cayley(out, cap)
  // 13 標記定理
  cert_marks(out, cap)
  // 14 G-集之 Burnside 與標記（點/序對/邊/歸納/上歸納）
  cert_gset_marks(out, cap)
  // 15 Whitney 例外對
  cert_whitney_exception(out)
  // 16 孤立點 ⇒ 線圖丟失資訊
  cert_line_isolated(out)
  // 17 SGS 元素表（多個群）
  cert_sgs_elements(out, cap)
  // 18 已知 |Aut| 值
  cert_known_aut_orders(out)
  // 19 分解 vs 引擎（不交併）
  cert_decomp_vs_engine(out)
  // 20 單子搜索之守恆（search_nd 之解皆滿足謂詞）
  cert_search_nd_sound(out, nda)
  out
}

///|
/// Cayley 圖定理：Cay(G) 之 Aut ⊇ 左正則像，且 |Aut| 與引擎一致。
fn cert_cayley(out : Array[Cert], cap : Int32) -> Unit {
  // 12 Cayley 圖定理
  let mut ok12 = true
  let mut det12 = ""
  for
    gg in [
      PermGroup::cyclic(4),
      PermGroup::symmetric(3),
      PermGroup::dihedral(4),
    ] {
    let (ca, cb, cc, aord, gord) = cayley_cert(gg, cap)
    if !(ca && cb && cc && aord >= gord) {
      ok12 = false
    }
    det12 = det12 +
      "|G|=" +
      gord.to_string() +
      "≤|Aut(Cay)|=" +
      aord.to_string() +
      " "
  }
  out.push(
    cert(
      "cayley-embedding",
      ok12,
      "左正則表示 λ:G↪Aut(Cay(G,S)) 單射；" + det12,
    ),
  )
}

///|
/// 標記定理：table of marks 兩條獨立公式一致、下三角、對角正 ⇒ 標記向量為完全不變量。
fn cert_marks(out : Array[Cert], cap : Int32) -> Unit {
  // 13 標記定理
  let mut ok13 = true
  let mut det13 = ""
  for
    gg in [
      PermGroup::symmetric(3),
      PermGroup::cyclic(6),
      PermGroup::symmetric(4),
    ] {
    let (ma, mb, mc, ns, gord) = marks_cert(gg, cap)
    if !(ma && mb && mc) {
      ok13 = false
    }
    det13 = det13 + "|G|=" + gord.to_string() + ":" + ns.to_string() + "類 "
  }
  out.push(
    cert(
      "marks-triangular",
      ok13,
      "table of marks 下三角 + 對角正 ⇒ 可逆 ⇒ 標記向量為完全不變量；" +
      det13,
    ),
  )
}

///|
/// G-集之 Burnside 與標記：點/序對/邊/歸納/上歸納五種 G-集之軌道數與 Burnside 和一致。
fn cert_gset_marks(out : Array[Cert], cap : Int32) -> Unit {
  // 14 G-集之 Burnside 與標記（點/序對/邊/歸納/上歸納）
  let d3 = PermGroup::dihedral(3)
  let subs = subgroup_classes(d3, cap)
  let gss : Array[GSetOf] = [
    gset_points(d3, cap),
    gset_pairs(d3, cap),
    gset_edges(d3, Graph::cycle(3), cap),
    gset_induced(d3, 2, cap),
    gset_coinduced(d3, 2, cap),
  ]
  let mut ok14 = true
  for gs in gss {
    let (orb, burn) = gset_burnside(gs)
    if orb != burn {
      ok14 = false
    }
    let mv = mark_vector(gs, subs)
    if mv.length() != subs.length() {
      ok14 = false
    }
  }
  // 點作用 ≅ 邊作用（三角形），≠ 序對作用
  let gs_p = gset_points(d3, cap)
  let gs_e = gset_edges(d3, Graph::cycle(3), cap)
  let gs_q = gset_pairs(d3, cap)
  ok14 = ok14 &&
    gset_isomorphic(gs_p, gs_e, subs) &&
    !gset_isomorphic(gs_p, gs_q, subs)
  out.push(
    cert(
      "gset-burnside-marks", ok14, "5 個 G-集：#orbits = Burnside 平均；V ≅ E（三角形）而 V ≇ V×V（標記判別）",
    ),
  )
}

///|
/// Whitney 例外對：K3 與 K1,3 之線圖同構但原圖不同構（唯一例外）。
fn cert_whitney_exception(out : Array[Cert]) -> Unit {
  // 15 Whitney 例外對
  let k3 = Graph::complete(3)
  let claw = Graph::star(3)
  out.push(
    cert(
      "whitney-exception",
      whitney_exception(k3, claw) &&
      isomorphic(line_graph(k3), line_graph(claw)) &&
      !isomorphic(k3, claw) &&
      !isomorphic_line(k3, claw),
      "L(K₃)=L(K₁,₃)=K₃ 但 K₃≇K₁,₃；衍生判定正確排除例外",
    ),
  )
}

///|
/// 孤立點 ⇒ 線圖丟失資訊：ker Φ ≅ S_{孤立點} × (ℤ/2)^{K₂分量數}。
fn cert_line_isolated(out : Array[Cert]) -> Unit {
  // 16 孤立點 ⇒ 線圖丟失資訊
  let c5 = Graph::cycle(5)
  let c5k1 = Graph::from_edges(6, c5.edge_list())
  out.push(
    cert(
      "line-loses-isolated",
      isomorphic(line_graph(c5), line_graph(c5k1)) &&
      !isomorphic(c5, c5k1) &&
      line_kernel_order(c5k1) == 1L,
      "L(G⊔K₁)=L(G)：孤立點在線圖中消失（故 Whitney 需無孤立點）",
    ),
  )
}

///|
/// SGS 元素表：多個群之 `elements(cap)` 與暴力乘積閉包一致（階、成員、封閉性）。
fn cert_sgs_elements(out : Array[Cert], cap : Int32) -> Unit {
  // 17 SGS 元素表（多個群）
  let mut ok17 = true
  for
    gg in [
      PermGroup::symmetric(4),
      PermGroup::dihedral(4),
      PermGroup::cyclic(7),
      automorphism_group(Graph::petersen()),
    ] {
    if !elements_cert(gg, cap) {
      ok17 = false
    }
  }
  out.push(
    cert(
      "sgs-elements-exact", ok17, "S₄/D₈/C₇/Aut(Petersen) 之元素表：相異、完整、封閉",
    ),
  )
}

///|
/// 已知 |Aut| 值：K_n=n!、C_n=2n、Petersen=120、Q4=384、Q6=46080 等文獻值。
fn cert_known_aut_orders(out : Array[Cert]) -> Unit {
  // 18 已知 |Aut| 值
  let known : Array[(String, Graph, Int64)] = [
    ("K5", Graph::complete(5), 120L),
    ("C6", Graph::cycle(6), 12L),
    ("P5", Graph::path(5), 2L),
    ("Q4", Graph::hypercube(4), 384L),
    ("Petersen", Graph::petersen(), 120L),
    ("K3,3", Graph::complete_bipartite(3, 3), 72L),
  ]
  let mut ok18 = true
  for t in known {
    let (nm, gg, want) = t
    if aut_order(gg) != want {
      ok18 = false
    }
    let _ = nm
  }
  out.push(
    cert("known-aut-orders", ok18, "6 個圖譜之 |Aut| 與文獻值相符"),
  )
}

///|
/// 分解 vs 引擎：不交併之 |Aut| 積公式與引擎直接搜尋相符。
fn cert_decomp_vs_engine(out : Array[Cert]) -> Unit {
  // 19 分解 vs 引擎（不交併）
  let pet = Graph::petersen()
  let edges2 : Array[(Int32, Int32)] = []
  for e in pet.edge_list() {
    let (u, v) = e
    edges2.push((u, v))
    edges2.push((u + 10, v + 10))
  }
  let two_pet = Graph::from_edges(20, edges2)
  let dec = decompose(two_pet)
  let dgrp = dec.automorphism_group()
  out.push(
    cert(
      "decomp-vs-engine",
      dec.aut_order() == 28800L &&
      dgrp.order() == 28800L &&
      dec.class_count() == 1 &&
      dec.block_count() == 2,
      "2×Petersen：Π 公式 = 派生群階 = 120²·2 = 28800",
    ),
  )
}

///|
/// 單子搜索之守恆：`search_nd` 回傳之每個解皆滿足全部約束（與 `csp_limit` 交叉驗證）。
fn cert_search_nd_sound(out : Array[Cert], nda : Array[Array[Int32]]) -> Unit {
  // 20 單子搜索之守恆（search_nd 之解皆滿足謂詞）
  let mut ok20 = true
  for s in nda {
    for i in 0..<s.length() {
      for j in (i + 1)..<s.length() {
        let da = s[i] - s[j]
        let ad = if da < 0 { 0 - da } else { da }
        if s[i] == s[j] || ad == j - i {
          ok20 = false
        }
      }
    }
  }
  out.push(
    cert("search-nd-sound", ok20, "search_nd 之每個解皆滿足約束"),
  )
}
