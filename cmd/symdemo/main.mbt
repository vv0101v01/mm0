///|
/// symlib 演示：圖自同構群 / 群作用 / 軌道折疊 / 單子 / 規範形式 / 範疇化
/// 全部演算法同一作用域，一次搜索多模組消費。
///
/// 運行（推薦原生 release）：moon run cmd/main --target native --release
/// 或（wasm 直譯，較慢）：      moon run cmd/main

///|
fn timed(label : String, f : () -> String) -> Unit {
  let t0 = @bench.monotonic_clock_start()
  let out = f()
  let dt = @bench.monotonic_clock_end(t0) / 1000.0 // µs → ms
  println("  \{label}: \{out}  [\{dt}ms]")
}

///|
/// 「衍生演算法 vs 直接演算法」之計時對照（同一結果，兩條路徑）。
fn versus(label : String, a : () -> String, b : () -> String) -> Unit {
  let t0 = @bench.monotonic_clock_start()
  let ra = a()
  let t1 = @bench.monotonic_clock_end(t0) / 1000.0 // µs → ms
  let t2 = @bench.monotonic_clock_start()
  let rb = b()
  let t3 = @bench.monotonic_clock_end(t2) / 1000.0 // µs → ms
  println(
    "  " +
    label +
    ":\n    衍生: " +
    ra +
    "  [" +
    t1.to_string() +
    "ms]\n    直接: " +
    rb +
    "  [" +
    t3.to_string() +
    "ms]  ⇒ " +
    (t3 / t1).to_string() +
    "×",
  )
}

///|
fn main {
  println("=== symlib 演算法數學庫（MoonBit）===")

  println("\n[1] 規範形式：重標號不變性 + 同構判定")
  let petersen = @symlib.Graph::petersen()
  timed("canon-invariance", fn() {
    let sigma = @symlib.Perm::from_cycles(10, [[0, 3, 7, 1, 9, 5, 2, 8, 4, 6]])
    let p2 = petersen.relabel(sigma)
    let d1 = @symlib.canon_digest(petersen)
    let d2 = @symlib.canon_digest(p2)
    "digest stable = \{d1 == d2}"
  })
  timed("iso-hard-cases", fn() {
    let sigma = @symlib.Perm::from_cycles(10, [[0, 3, 7, 1, 9, 5, 2, 8, 4, 6]])
    let p2 = petersen.relabel(sigma)
    let c10 = @symlib.Graph::cycle(10)
    // Petersen 與 C10 同度序列 — 需要完整規範形式才能區分
    "petersen≅relabel=\{@symlib.isomorphic(petersen, p2)} petersen≅C10=\{@symlib.isomorphic(petersen, c10)}"
  })

  println(
    "\n[2] 自同構群 + 軌道折疊：經典圖譜（|Aut| 已知值對照）",
  )
  let cases : Array[(String, @symlib.Graph, Int64)] = [
    ("K5", @symlib.Graph::complete(5), 120L),
    ("K3,3", @symlib.Graph::complete_bipartite(3, 3), 72L),
    ("C6", @symlib.Graph::cycle(6), 12L),
    ("P5", @symlib.Graph::path(5), 2L),
    ("Q4", @symlib.Graph::hypercube(4), 384L),
    ("star4", @symlib.Graph::star(4), 24L),
    ("Petersen", petersen, 120L),
  ]
  for (name, g, expect) in cases {
    timed(name, fn() {
      let r = @symlib.analyze(g)
      let ok = if r.order == expect { "OK" } else { "FAIL" }
      "|Aut|=\{r.order}(\{ok}) 頂點軌道=\{r.vertex_orbits.length()} 邊軌道=\{r.edge_orbits.length()} 折疊=\{r.folded.k}/\{g.order()} 節點=\{r.nodes}"
    })
  }

  println("\n[3] 群作用：Burnside 軌道計數恆等式驗證")
  timed("burnside(C6)", fn() {
    let c6 = @symlib.Graph::cycle(6)
    let grp = @symlib.automorphism_group(c6)
    let act = @symlib.FinAction::of_group(grp)
    let direct = act.orbit_count()
    let burn = act.burnside_orbit_count(grp, 100)
    "#軌道=\{direct} Burnside平均不動點=\{burn} 一致=\{direct == burn}"
  })
  timed("burnside(pairs)", fn() {
    // 導出作用（序對）之 Burnside：群元素經 lift 提升
    let c6 = @symlib.Graph::cycle(6)
    let grp = @symlib.automorphism_group(c6)
    let pairs = @symlib.FinAction::on_pairs(grp)
    "序對軌道=\{pairs.orbit_count()} Burnside=\{pairs.burnside_orbit_count(grp, 100)} (36 序對)"
  })

  println("\n[4] 軌道折疊：搜索空間壓縮")
  timed("fold(Q4)", fn() {
    let q4 = @symlib.Graph::hypercube(4)
    let r = @symlib.analyze(q4)
    "Q4: 16 頂點 → \{r.folded.k} 軌道（可遷 ⇒ 單點商）壓縮率=\{r.folded.ratio()}"
  })
  timed("fold-candidates", fn() {
    let c6 = @symlib.Graph::cycle(6)
    let grp = @symlib.automorphism_group(c6)
    let (reps, ratio) = @symlib.fold_candidates(grp, [0, 1, 2, 3, 4, 5])
    "分支候選 6 → 軌道代表 \{reps.length()}（壓縮率 \{ratio}）— 搜索樹按此摺疊"
  })

  println("\n[5] 單子：定律驗證 + 管線應用")
  timed("monad-laws", fn() {
    "ListM=\{list_monad_laws_ok()} StateM=\{state_monad_laws_ok()}"
  })
  timed("isomorphisms_m(C4)", fn() {
    let c4 = @symlib.Graph::cycle(4)
    let isos = @symlib.isomorphisms_m(c4, c4, 100)
    "全部自同構經 ListM 列舉：\{isos.to_array().length()} 個（=|Aut(C4)|）"
  })
  timed("analyze_m(StateM)", fn() {
    let init : @symlib.SearchStats = { nodes: 0, leaves: 0, autos: 0, }
    let prog = @symlib.analyze_m(@symlib.Graph::cycle(6))
    let (rep, stats) = (prog.run)(init)
    "StateM 線程化統計：|Aut|=\{rep.order} nodes=\{stats.nodes} leaves=\{stats.leaves}"
  })

  println("\n[6] 範疇化：冪集單子 = 內函子範疇中的幺半群")
  timed("pow-monad", fn() {
    let laws3 = @symlib.pow_monad_laws(3)
    let laws1 = @symlib.pow_monad_laws(1) // n≤1 才能驗結合律（2^(2^n) 規模）
    let f = @symlib.FinMap::new(3, 3, [1, 2, 0])
    "單位律(n=3)=\{laws3} 全定律(n=1)=\{laws1} 自然性=\{@symlib.pow_naturality(f)}"
  })
  timed("aut-functor", fn() {
    let c6 = @symlib.Graph::cycle(6)
    let rot = @symlib.Perm::from_cycles(6, [[0, 1, 2, 3, 4, 5]])
    let refl = @symlib.Perm::from_img([0, 5, 4, 3, 2, 1])
    let grp = @symlib.automorphism_group(c6)
    let (composed, stepped) = @symlib.aut_functorial(rot, refl, grp)
    "F(φ2∘φ1)=F(φ2)∘F(φ1)：|·|=\{composed.order()} vs \{stepped.order()}（Aut(C6)=12）"
  })
  timed("groupoid", fn() {
    let c6 = @symlib.Graph::cycle(6)
    let gs = @symlib.GSet::of(@symlib.automorphism_group(c6))
    // 廣群基數 |X//G| = Σ 1/|G_x| = |X|/|G|；Burnside 形式 Σ 1/|Orb(x)| = #軌道
    "|C6//D6|=\{gs.groupoid_cardinality()} (=6/12) 骨架計數=\{gs.orbit_sum_cardinality()} (=1 軌道)"
  })

  println(
    "\n[7] 剪枝模式對比（同一引擎三種紀律；規範指紋必須一致）",
  )
  timed("modes(Petersen)", fn() {
    let r0 = @symlib.search_graph_mode(petersen, 0)
    let r1 = @symlib.search_graph_mode(petersen, 1)
    let r2 = @symlib.search_graph_mode(petersen, 2)
    let d0 = @symlib.digest_from(r0.n, r0.canon_enc)
    let d1 = @symlib.digest_from(r1.n, r1.canon_enc)
    let d2 = @symlib.digest_from(r2.n, r2.canon_enc)
    "無剪枝 nodes=\{r0.nodes} | 靜態 nodes=\{r1.nodes} | 動態 nodes=\{r2.nodes}；指紋一致=\{d0 == d1 && d1 == d2}"
  })

  println(
    "\n[8] 定理電池：由規範形式 × 範疇化導出、可機器驗證之定理證書",
  )
  timed("prove_graph(Petersen)", fn() {
    let sigma = @symlib.Perm::from_cycles(10, [[0, 3, 7, 1, 9, 5, 2, 8, 4, 6]])
    let certs = @symlib.prove_graph(petersen, sigma, 200)
    "22 條定理：全部成立=\{@symlib.all_hold(certs)}（\{certs.length()} 條證書）"
  })
  timed("prove_pair(C6 vs 2×C3)", fn() {
    let c6 = @symlib.Graph::cycle(6)
    let two_c3 = @symlib.Graph::disjoint_union([
      @symlib.Graph::complete(3),
      @symlib.Graph::complete(3),
    ])
    let certs = @symlib.prove_pair(c6, two_c3)
    "四條獨立同構通道互證 C6 ≇ 2×C3：全部成立=\{@symlib.all_hold(certs)}"
  })
  timed("prove_all(全庫)", fn() {
    let all = @symlib.prove_all(200)
    let bad = @symlib.failed_certs(all)
    "\{all.length()} 條跨模組定理，失敗 \{bad.length()} 條"
  })
  println("  證書清單（prove_all）：")
  println(@symlib.cert_report(@symlib.prove_all(200)))

  println(
    "\n[9] 衍生演算法：定理 ⇒ 免搜索 / 免枚舉之捷徑（同一結果，兩條路徑）",
  )
  versus(
    "分量分解 |Aut(2×Petersen)|（積公式 vs 全搜索）",
    fn() {
      let g = @symlib.Graph::disjoint_union([petersen, petersen])
      "|Aut|=\{@symlib.decompose(g).aut_order()}（= 120²·2!）"
    },
    fn() {
      let g = @symlib.Graph::disjoint_union([petersen, petersen])
      "|Aut|=\{@symlib.aut_order(g)}"
    },
  )
  versus(
    "Whitney |Aut(L(K5))|（|Aut(G)|/|kerΦ| vs 搜索 L(G)）",
    fn() {
      let k5 = @symlib.Graph::complete(5)
      let d = @symlib.aut_order(k5) / @symlib.line_kernel_order(k5)
      "|Aut(L(K5))|=\{d}（L(K5) 有 10 頂點 30 邊）"
    },
    fn() {
      "|Aut(L(K5))|=\{@symlib.aut_order(@symlib.line_graph(@symlib.Graph::complete(5)))}"
    },
  )
  versus(
    "補圖對偶 dual_pair(n=32)（一次搜索 vs 兩次）",
    fn() {
      let g = @symlib.Graph::random(32, 50, 44).0
      let (dg, dc) = @symlib.dual_pair(g)
      "G 與 Ḡ 兩份規範編碼（nodes=\{dg.nodes}/\{dc.nodes}）"
    },
    fn() {
      let g = @symlib.Graph::random(32, 50, 44).0
      let _ = @symlib.canonical_form(g)
      let _ = @symlib.canonical_form(g.complement())
      "G 與 Ḡ 兩份規範編碼（各搜一次）"
    },
  )
  versus(
    "規範折疊 fold_canonical(Q4)（共軛搬運 vs 二次搜索）",
    fn() {
      let f = @symlib.fold_canonical(@symlib.Graph::hypercube(4))
      "k=\{f.k}/16 重標號不變"
    },
    fn() {
      let q4 = @symlib.Graph::hypercube(4)
      let cf = @symlib.canonical_form(q4)
      let f = @symlib.fold_graph(cf, @symlib.automorphism_group(cf))
      "k=\{f.k}/16 重標號不變"
    },
  )
  timed("標記向量判定 G-集同構（S4）", fn() {
    let s4 = @symlib.PermGroup::symmetric(4)
    let subs = @symlib.subgroup_classes(s4, 400)
    let c2 : Array[@symlib.Sub] = []
    for h in subs {
      if h.order == 2L {
        c2.push(h)
      }
    }
    let x = @symlib.coset_gset(s4, c2[0], 400)
    let y = @symlib.coset_gset(s4, c2[1], 400)
    let iso = @symlib.gset_isomorphic(x, y, subs)
    "|X|=|Y|=\{x.x}（S4/⟨對換⟩ vs S4/⟨雙對換⟩）同構=\{iso}；暴力需 \{x.x}! ≈ 4.8e8 個雙射"
  })
  timed("標記向量（64 點 G-集）", fn() {
    let s3 = @symlib.PermGroup::symmetric(3)
    let subs = @symlib.subgroup_classes(s3, 200)
    let coi = @symlib.gset_coinduced(s3, 2, 200)
    let mv = @symlib.mark_vector(coi, subs)
    let mut s = "["
    for v in mv {
      s = s + v.to_string() + " "
    }
    "|X|=\{coi.x}=2^6 軌道=\{@symlib.gset_orbits(coi).length()} 標記=\{s + "]"}；暴力判定需 64! ≈ 1e89"
  })
  timed("Cayley 定理下界", fn() {
    let d4 = @symlib.PermGroup::dihedral(4)
    let cay = @symlib.cayley_graph(d4, 400)
    "|Aut(Cay(D4,S))|=\{@symlib.aut_order(cay)} ≥ |D4|=\{d4.order()}（下界 O(1) 免搜索）"
  })

  println("\n=== 完成 ===")
}

///|
/// ListM 單子律（左單位 / 右單位 / 結合）。
fn list_monad_laws_ok() -> Bool {
  let f = fn(x : Int32) -> @symlib.ListM[Int32] {
    @symlib.ListM::from_array([x, x + 1])
  }
  let g = fn(x : Int32) -> @symlib.ListM[Int32] {
    @symlib.ListM::from_array([x * 2])
  }
  let l1 = @symlib.ListM::pure(3).bind(f).to_array() == f(3).to_array()
  let m = @symlib.ListM::from_array([1, 2, 3])
  let l2 = m.bind(fn(x) { @symlib.ListM::pure(x) }).to_array() == m.to_array()
  let lhs = m.bind(f).bind(g).to_array()
  let rhs = m.bind(@symlib.kleisli_list(f, g)).to_array()
  l1 && l2 && lhs == rhs
}

///|
/// StateM 單子律。
fn state_monad_laws_ok() -> Bool {
  let f = fn(x : Int32) -> @symlib.StateM[Int32, Int32] {
    @symlib.StateM::modify(fn(s) { s + x }).bind(fn(_) {
      @symlib.StateM::pure(x * 2)
    })
  }
  let g = fn(x : Int32) -> @symlib.StateM[Int32, Int32] {
    @symlib.StateM::pure(x + 1)
  }
  let l1 = @symlib.StateM::pure(5).bind(f).eval(0) == f(5).eval(0)
  let m : @symlib.StateM[Int32, Int32] = @symlib.StateM::pure(7)
  let l2 = m.bind(fn(x) { @symlib.StateM::pure(x) }).eval(0) == m.eval(0)
  let lhs = m.bind(f).bind(g).eval(0)
  let rhs = m.bind(@symlib.kleisli_state(f, g)).eval(0)
  l1 && l2 && lhs == rhs
}
