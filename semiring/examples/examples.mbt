///|
/// README 的程式片段，全部以可編譯的形式保留在此（`moon check` 會驗證它們）。
/// 這裡沒有 main，只是讓範例與 API 不會互相漂移。

///|
pub fn example_shortest_path() -> (Double, Bool) {
  let g = @graph.Graph::random(@alg.Rng::new(42UL), 200, 5, 30)
  let dist = @graph.apsp_dijkstra(g)
  let (_d2, has_neg) = @graph.apsp_kleene(g)
  (dist.d[0 * 200 + 7].value().to_double(), has_neg)
}

///|
pub fn example_counting_paths(n : Int32) -> @mat.Mat[@alg.Counting] {
  let e = @mat.Mat::new(n, n, @alg.Counting::new(0L))
  @mat.closure_lehmann(e)
}

///|
pub fn example_pareto(n : Int32) -> (Int32, Bool) {
  let g = @graph.Graph::random_two(@alg.Rng::new(7UL), n, 25, 20)
  let (labels, converged) = @graph.pareto_sssp(g, 0)
  (@graph.total_labels(labels), converged)
}

///|
pub fn example_spline(
  y : Array[Double],
) -> (Array[Double], Array[Double], Double) {
  let c = @spline.interp_cubic_periodic(y)
  let c2 = @spline.interp_cubic_banded(y)
  let v = @spline.eval_deboor(c, @spline.uniform_knots(3, c.length()), 3, 5.0)
  (c, c2, v)
}

///|
pub fn example_aggregates() -> (Int64, Int64, Int64) {
  let data = [@mon.SumI64::of(1L), @mon.SumI64::of(2L), @mon.SumI64::of(3L)]
  let tree = @mon.SegTree::build(data)
  let maxs : Array[@mon.MaxI64] = [{ v: 4L, }, { v: 9L, }, { v: 6L, }]
  let sp = @mon.SparseTable::build(maxs)
  let fen = @mon.Fenwick::build(data)
  (tree.query(0, 3).v, sp.query(0, 3).v, fen.range(0, 3).v)
}

///|
pub fn example_ratelimit(key : UInt64, now_us : Int64) -> @rl.Decision {
  // 每鍵 1000 req/s（burst 20）＋ 全域 50000 req/s（burst 100）＋ 4096 格鍵表
  let lim = @rl.Limiter::with_gate(1000.0, 20, 50000.0, 100, 4096)
  lim.admit(key, now_us)
}

///|
/// CSR 稀疏路徑：建圖 → 單源最短路 → SpGEMM。
pub fn example_csr(n : Int32) -> (@alg.Trop, Int32, Bool) {
  let from : Array[Int32] = []
  let to : Array[Int32] = []
  let w : Array[@alg.Trop] = []
  for i in 1..<n {
    from.push((i - 1) / 2)
    to.push(i)
    w.push(@alg.Trop::new(1))
  }
  let g = @mat.Csr::from_triplets(n, n, from, to, w)
  let (dist, _neg) = @mat.csr_sssp(g, 0)
  let sq = @mat.csr_mul_minplus(g, g)
  (dist[n - 1], g.nnz(), sq.nnz() > 0)
}

///|
/// 浮點 min-plus：同樣的內核，Double 權重。
pub fn example_float_minplus() -> Double {
  let a = @mat.Mat::new(2, 2, @alg.TropF::inf())
  let b = @mat.Mat::new(2, 2, @alg.TropF::inf())
  a.d[0] = @alg.TropF::of(0.0)
  a.d[3] = @alg.TropF::of(0.0)
  a.d[1] = @alg.TropF::of(1.5)
  b.d[2] = @alg.TropF::of(0.25)
  let c = @mat.mul_trop_generic(a, b)
  // c[0][0] = min(a[0][0]+b[0][0], a[0][1]+b[1][0]) = min(∞, 1.5+0.25)
  c.d[0].value()
}

///|
/// 分塊大小由快取預算決定，而不是硬寫。
pub fn example_blocking() -> Int32 {
  @mat.choose_block_l1(@mat.default_l1_bytes, 4, 4096)
}

///|
/// 平行後端：分段任務 + 確定性歸約（結果與序列版本相同）。
pub fn example_parallel(n : Int32) -> (String, Int64) {
  let total = @par.par_sum(n, 64, fn(i) { i.to_int64() })
  (@par.backend(), total)
}

// ---------------------------------------------------------------------------
// v4：熱帶幾何 / 規範形式 / 範疇化 / 代數路徑 / 連帶相信
// ---------------------------------------------------------------------------

///|
/// 熱帶根：下凸包的斜率，含重數。
pub fn example_tropical_roots() -> Array[@trop.Rat] {
  let p = @trop.UniPoly::new([0, 10, 3, 7, 1, 9, 4])
  p.roots()
}

///|
/// 雙變數熱帶曲面：細分面數、對偶邊數、平衡殘差最大值。
pub fn example_tropical_curve() -> (Int32, Int32, Int64) {
  let poly = @trop.BPoly::new([
    @trop.BTerm::new(0, 0, 0),
    @trop.BTerm::new(1, 2, 0),
    @trop.BTerm::new(2, 0, 2),
    @trop.BTerm::new(3, 2, 2),
    @trop.BTerm::new(-3, 1, 1),
  ])
  let faces = poly.subdivision()
  let edges = poly.dual_curve(faces)
  let res = @trop.balancing_residuals(edges, faces.length())
  let mut worst = 0L
  for r in res {
    let ax = if r.1 < 0L { -r.1 } else { r.1 }
    let ay = if r.2 < 0L { -r.2 } else { r.2 }
    let m = if ax > ay { ax } else { ay }
    if m > worst {
      worst = m
    }
  }
  (faces.length(), edges.length(), worst)
}

///|
/// 熱帶行列式 = 最佳指派。
pub fn example_tropical_det() -> Int64 {
  let a : Array[Array[Int64]] = [[3L, 1L, 4L], [1L, 5L, 9L], [2L, 6L, 5L]]
  @trop.trop_det(a)
}

///|
/// 兩個正規表示式是否等價（最小 DFA 正規形）。
pub fn example_regex_equiv() -> Bool {
  let a = @nf.RChar(0)
  let b = @nf.RChar(1)
  let lhs = @nf.r_star(@nf.r_sum(a, b))
  let rhs = @nf.r_star(@nf.r_prod(@nf.r_star(a), @nf.r_star(b)))
  @nf.regex_equiv(lhs, rhs, [0, 1])
}

///|
/// 最大 DFA 的最小狀態數（Myhill–Nerode 等價類個數）。
pub fn example_min_dfa_states() -> Int32 {
  let a = @nf.RChar(0)
  let b = @nf.RChar(1)
  let r = @nf.r_star(@nf.r_prod(@nf.r_sum(a, b), @nf.r_sum(a, b)))
  @nf.regex_state_count(r, [0, 1])
}

///|
/// 自由範疇：路徑數（= ℕ 半環上的 Kleene 星）。
pub fn example_free_category() -> Int64 {
  let g = @cat.DiGraph::new(4)
  g.edge(0, 1)
  g.edge(0, 2)
  g.edge(1, 3)
  g.edge(2, 3)
  g.edge(1, 2)
  let cnt = g.path_counts()
  cnt[0][3]
}

///|
/// 一份程式、五種代數：同一段 `app_closure`。
pub fn example_app_five_semirings() -> (Bool, Int32, Int32) {
  let n = 4
  let es : Array[(Int32, Int32, Int32)] = [
    (0, 1, 3),
    (1, 2, 4),
    (2, 3, 5),
    (0, 3, 20),
  ]
  let reach = @app.app_bool(n, [(0, 1), (1, 2), (2, 3), (0, 3)])
  let dist = @app.app_minplus(n, es)
  let wide = @app.app_widest(n, es)
  (reach.get(0, 2).b, dist.get(0, 3).value(), wide.get(0, 3).value())
}

///|
/// 訊息傳遞（GDL）：樹上的邊緣機率。
pub fn example_belief() -> (Double, Int64) {
  let card : Array[Int32] = [2, 2]
  let f : @bp.Factor[@alg.Prob] = @bp.Factor::new([0, 1], [
    @alg.Prob::new(0.9),
    @alg.Prob::new(0.1),
    @alg.Prob::new(0.2),
    @alg.Prob::new(0.8),
  ])
  let g : @bp.FactorGraph[@alg.Prob] = { nvar: 2, card, factors: [f], }
  let (m, ops) = @bp.marginals_sum_product(g)
  (m[0][0], ops)
}
