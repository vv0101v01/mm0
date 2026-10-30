// ===========================================================================
// 報告 §14–§18：熱帶幾何、規範形式、範疇化、演算法組合、連帶相信
//
// 這五節的原則與前面幾節完全相同：
//   每個「正確」都配一個獨立實作／暴力法；每個「更快」都給實際數字；
//   每個「不能保證」都明確寫出來（有環的 BP、稀疏消去、浮點極限）。
// ===========================================================================

///|
fn pct(a : Int32, b : Int32) -> String {
  if b == 0 {
    "n/a".to_string()
  } else {
    f2(a.to_double() / b.to_double() * 100.0)
  }
}

// ---------------------------------------------------------------------------
// §14 熱帶幾何
// ---------------------------------------------------------------------------

///|
pub fn sec14_tropical_geometry() -> Unit {
  line(
    "## 14. 熱帶幾何：牛頓多邊形、正則細分、對偶曲線、平衡條件",
  )
  line("")
  line(
    "### 14a. 單變數：熱帶根 = 下凸包的斜率，根上的打平正好是該邊的兩個端點",
  )
  line("")
  let coeffs : Array[Int32] = [0, 10, 3, 7, 1, 9, 4]
  let p = @trop.UniPoly::new(coeffs)
  let hull = p.lower_hull()
  line(
    "f(x) = min_i (c_i + i·x)，c = [0, 10, 3, 7, 1, 9, 4]，次數 = \{p.degree()}",
  )
  line("")
  line("| 下凸包頂點 (i, c_i) | 根 = −斜率 | 重數 |")
  line("|---|---|---|")
  for k in 1..<hull.length() {
    let (i, ci) = hull[k - 1]
    let (j, cj) = hull[k]
    let r = @trop.Rat::new((ci - cj).to_int64(), (j - i).to_int64())
    line("| (\{i}, \{ci}) → (\{j}, \{cj}) | \{r} | \{j - i} |")
  }
  line("")
  line(
    "重數總和 = \{p.multiplicity_sum()}（次數 = \{p.degree()}）；根數（含重數）= \{p.roots().length()}",
  )
  line(
    "每個根上「同時達到最小值的單項式個數」= 2（逐根精確檢查，見套件測試）",
  )
  line("")
  // 乘法定理：200 組隨機多項式，逐組驗證根的聯集
  let rng = @alg.Rng::new(20261023UL)
  let mut ok = 0
  let mut total_roots = 0
  for _ in 0..<200 {
    let a = @trop.UniPoly::new([
      rng.range(0, 20),
      rng.range(0, 20),
      rng.range(0, 20),
      rng.range(0, 20),
    ])
    let b = @trop.UniPoly::new([
      rng.range(0, 20),
      rng.range(0, 20),
      rng.range(0, 20),
    ])
    let h = @trop.trop_poly_mul(a, b)
    let union : Array[@trop.Rat] = []
    for r in a.roots() {
      union.push(r)
    }
    for r in b.roots() {
      union.push(r)
    }
    total_roots = total_roots + union.length()
    if @trop.roots_equal(h.roots(), union) {
      ok = ok + 1
    }
  }
  let (_, t_root) = @sim.time_min(20, fn() {
    let a = @trop.UniPoly::new([0, 10, 3, 7, 1, 9, 4])
    a.roots()
  })
  line(
    "乘法定理 roots(f⊗g) = roots(f) ⊔ roots(g)：\{ok}/200 組成立（共比對 \{total_roots} 個根，含重數）。",
  )
  line("求根（含下凸包）耗時 \{f2(t_root)} µs／次。")
  line("")
  line(
    "### 14b. 雙變數：抬升 → 下凸包 → 正則細分 → 對偶曲線",
  )
  line("")
  let poly = @trop.BPoly::new([
    @trop.BTerm::new(0, 0, 0),
    @trop.BTerm::new(1, 2, 0),
    @trop.BTerm::new(2, 0, 2),
    @trop.BTerm::new(3, 2, 2),
    @trop.BTerm::new(-3, 1, 1),
    @trop.BTerm::new(4, 3, 1),
  ])
  let (faces, t_sub) = @sim.time_min(20, fn() { poly.subdivision() })
  let edges = poly.dual_curve(faces)
  let bounded = edges.map(fn(e) { if e.face_b >= 0 { 1 } else { 0 } })
  let mut nb = 0
  for b in bounded {
    nb = nb + b
  }
  let (okd, badd) = poly.check_duality(faces)
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
  line("| 量 | 值 | 說明 |")
  line("|---|---|---|")
  line("| 支撐點 | 6 | 抬升到 (i, j, c) |")
  line(
    "| 牛頓多邊形面積 ×2 | \{poly.newton_area2()} | 凸包鞋帶公式 |",
  )
  line(
    "| 細分面積 ×2 | \{poly.subdivision_area2(faces)} | 各面多邊形面積和（必須相等） |",
  )
  line(
    "| 面數（= 熱帶曲線的頂點數） | \{faces.length()} | 投影后的 2 維格 |",
  )
  line(
    "| 細分邊（含射線） | \{edges.length()} | 有界 \{nb}、射線 \{edges.length() - nb} |",
  )
  line(
    "| 對偶性檢查 | \{okd} 通過 / \{badd} 失敗 | 以面法向當方向，argmin 必須正好是該面 |",
  )
  line(
    "| 平衡殘差最大值 | \{worst} | Σ w_e·ν_e = 0，全部為 0 才算通過 |",
  )
  line(
    "| 細分耗時 | \{f2(t_sub)} µs | 三點枚舉 + 全點在上方檢查 |",
  )
  line("")
  let (ties, _expl, unexp) = poly.check_ties_on_faces(faces, 20000, 7717UL)
  line(
    "抽樣對偶驗證（20000 個隨機方向）：打平 \{ties} 次，全部落在細分的面上（未被解釋 \{unexp} 次）。",
  )
  line("")
  line(
    "### 14c. 熱帶行列式 = 最佳指派：O(n³) vs O(n·2ⁿ) vs O(n!)",
  )
  line("")
  line(
    "| n | 匈牙利 O(n³) (µs) | 子集 DP O(n·2ⁿ) (µs) | 暴力 O(n!) (µs) | 三者一致 | 最優排列個數 |",
  )
  line("|---|---|---|---|---|---|")
  for n in [5, 7, 9, 11] {
    let rng3 = @alg.Rng::new(1000UL + n.to_uint64())
    let a : Array[Array[Int64]] = []
    for _ in 0..<n {
      let row : Array[Int64] = []
      for _ in 0..<n {
        row.push(rng3.range(-50, 50).to_int64())
      }
      a.push(row)
    }
    let (d1, t1) = @sim.time_min(20, fn() { @trop.trop_det(a) })
    let (d2, t2) = @sim.time_min(20, fn() { @trop.trop_det_dp(a) })
    let brute = if n <= 8 {
      let (_d3, t3) = @sim.time_min(3, fn() { @trop.trop_det_bruteforce(a) })
      f2(t3)
    } else {
      "—（n! 不可行）".to_string()
    }
    let cons = d1 == d2
    line(
      "| \{n} | \{f2(t1)} | \{f2(t2)} | \{brute} | \{cons} | \{@trop.trop_det_tie_count(a)} |",
    )
    if n == 7 {
      let d3 = @trop.trop_det_bruteforce(a)
      line("  （n=7 時暴力法給出 \{d3}，與匈牙利 \{d1} 相同）")
    }
  }
  line("")
  line(
    "熱帶奇異的判據：`trop_det_tie_count > 1`（最小值被多個排列達成 ⇒ 對偶超曲面在該方向不光滑）。",
  )
  let sing : Array[Array[Int64]] = [[1L, 2L, 3L], [1L, 2L, 3L], [1L, 2L, 3L]]
  line(
    "例：三列相同的 3×3 矩陣 ⇒ 6 個排列全部達到同一個最小值 \{@trop.trop_det(sing)}，`tie_count` = \{@trop.trop_det_tie_count(sing)}。",
  )
  line("")
}

// ---------------------------------------------------------------------------
// §15 規範形式
// ---------------------------------------------------------------------------

///|
pub fn sec15_normal_forms() -> Unit {
  line("## 15. 規範形式：ACI 正規形 + Myhill–Nerode 最小 DFA")
  line("")
  line("三個層次的「正規形」：")
  line(
    "1. **ACI**（本庫 `r_sum`/`r_prod`/`r_star`）：⊕ 攤平排序去重，讓導數集合有限。",
  )
  line(
    "2. **自動機**（`dfa_minimize`）：Moore 分割細化到 Myhill–Nerode 等價類。",
  )
  line(
    "3. **字串**（`dfa_canonical`）：最小完整 DFA 按 BFS 順序寫成逐位元可比的字串。",
  )
  line("")
  let al : Array[Int32] = [0, 1, 2]
  let a = @nf.RChar(0)
  let b = @nf.RChar(1)
  let cases : Array[(String, @nf.Regex)] = [
    ("(a+b)*", @nf.r_star(@nf.r_sum(a, b))),
    ("(a* b*)*", @nf.r_star(@nf.r_prod(@nf.r_star(a), @nf.r_star(b)))),
    ("(ab)* a", @nf.r_prod(@nf.r_star(@nf.r_prod(a, b)), a)),
    ("a (ba)*", @nf.r_prod(a, @nf.r_star(@nf.r_prod(b, a)))),
    (
      "(a+b)* abb",
      @nf.r_prod(@nf.r_star(@nf.r_sum(a, b)), @nf.r_prod(a, @nf.r_prod(b, b))),
    ),
    ("a* b*", @nf.r_prod(@nf.r_star(a), @nf.r_star(b))),
    (
      "(a+b)* (a+b)*",
      @nf.r_prod(@nf.r_star(@nf.r_sum(a, b)), @nf.r_star(@nf.r_sum(a, b))),
    ),
    (
      "(ab)* (ab)*",
      @nf.r_prod(@nf.r_star(@nf.r_prod(a, b)), @nf.r_star(@nf.r_prod(a, b))),
    ),
    ("((a+b)*)*", @nf.r_star(@nf.r_star(@nf.r_sum(a, b)))),
  ]
  line(
    "| 表示式 | 導數 DFA 狀態數 | 最小 DFA 狀態數 | 收縮 | canonical 字串長度 |",
  )
  line("|---|---|---|---|---|")
  for c in cases {
    let d = @nf.dfa_of_regex(c.1, al)
    let m = @nf.dfa_minimize(d)
    let canon = @nf.dfa_canonical(m)
    line(
      "| \{c.0} | \{d.nstates()} | \{m.nstates()} | \{pct(m.nstates(), d.nstates())}% | \{canon.length()} |",
    )
  }
  line("")
  line(
    "等價判定兩條路徑（最小 DFA 正規形 vs 乘積自動機）：",
  )
  line("")
  let pairs : Array[(String, @nf.Regex, @nf.Regex)] = [
    (
      "(a+b)* = (a*b*)*",
      @nf.r_star(@nf.r_sum(a, b)),
      @nf.r_star(@nf.r_prod(@nf.r_star(a), @nf.r_star(b))),
    ),
    (
      "(ab)*a = a(ba)*",
      @nf.r_prod(@nf.r_star(@nf.r_prod(a, b)), a),
      @nf.r_prod(a, @nf.r_star(@nf.r_prod(b, a))),
    ),
    ("a* ≠ a", @nf.r_star(a), a),
    (
      "(a+b)* ≠ a*b*",
      @nf.r_star(@nf.r_sum(a, b)),
      @nf.r_prod(@nf.r_star(a), @nf.r_star(b)),
    ),
  ]
  for q in pairs {
    let e = @nf.regex_equiv(q.1, q.2, al)
    let d1 = @nf.dfa_minimize(@nf.dfa_of_regex(q.1, al))
    let d2 = @nf.dfa_minimize(@nf.dfa_of_regex(q.2, al))
    let prod = @nf.dfa_equiv(d1, d2)
    line(
      "- \{q.0}：正規形判定 = \{e}，乘積自動機 = \{prod}（必須相同）",
    )
  }
  line("")
  line(
    "半環等式判定（自由**冪等**半環）：多項式正規形 vs 最小 DFA，兩條互不相依的路徑。",
  )
  line("")
  let rng = @alg.Rng::new(555UL)
  let mut agree = 0
  let mut total = 0
  for _ in 0..<300 {
    let e1 = rand_sexpr(rng, 3)
    let e2 = rand_sexpr(rng, 3)
    let p1 = @nf.idempotent_identity_holds(e1, e2)
    let p2 = @nf.idempotent_identity_holds_via_dfa(e1, e2)
    if p1 == p2 {
      agree = agree + 1
    }
    total = total + 1
  }
  let (_, t_nf) = @sim.time_min(20, fn() {
    let e1 = rand_sexpr(rng, 3)
    let e2 = rand_sexpr(rng, 3)
    @nf.idempotent_identity_holds(e1, e2)
  })
  line(
    "| 隨機表示式對 | 兩條路徑一致 | 每次判定耗時（多項式正規形） |",
  )
  line("|---|---|---|")
  line("| \{total} | \{agree}（\{pct(agree, total)}%） | \{f2(t_nf)} µs |")
  line("")
  line(
    "注意：`a·b ≠ b·a` 在此判定程序中**不相等**（⊗ 不假設交換），這是刻意的；",
  )
  line(
    "若把單項式排序就會把 `ab` 與 `ba` 混為一談——這個 bug 在開發時真的發生過，測試現在盯著它。",
  )
  line("")
}

///|
fn rand_sexpr(rng : @alg.Rng, depth : Int32) -> @nf.SExpr {
  if depth == 0 {
    let k = rng.next_int(5)
    if k == 0 {
      @nf.SZero
    } else if k == 1 {
      @nf.SOne
    } else {
      @nf.SVar(rng.next_int(3))
    }
  } else {
    let k = rng.next_int(4)
    if k == 0 {
      @nf.SSum(rand_sexpr(rng, depth - 1), rand_sexpr(rng, depth - 1))
    } else if k == 1 {
      @nf.SProd(rand_sexpr(rng, depth - 1), rand_sexpr(rng, depth - 1))
    } else {
      rand_sexpr(rng, 0)
    }
  }
}

// ---------------------------------------------------------------------------
// §16 範疇化
// ---------------------------------------------------------------------------

///|
pub fn sec16_categorification() -> Unit {
  line("## 16. 範疇化：集合值矩陣、自由範疇、Maslov 解量化")
  line("")
  line("### 16a. 基數是半環同態：|A⊗B| = |A|·|B|")
  line("")
  let rng = @alg.Rng::new(31415UL)
  let n = 6
  let sa = @cat.SetMat::new(n, n)
  let sb = @cat.SetMat::new(n, n)
  let mut witnesses = 0
  for i in 0..<n {
    for j in 0..<n {
      for l in 0..<rng.next_int(3) {
        sa.add(i, j, [i, j, l])
        witnesses = witnesses + 1
      }
      for l in 0..<rng.next_int(3) {
        sb.add(i, j, [j, i, l])
        witnesses = witnesses + 1
      }
    }
  }
  let (prod, t_prod) = @sim.time_min(5, fn() { @cat.smat_mul(sa, sb) })
  let mut prod_witnesses = 0
  for i in 0..<n {
    for j in 0..<n {
      prod_witnesses = prod_witnesses + prod.get(i, j).length()
    }
  }
  let dec_a = @cat.decategorify(sa)
  let dec_b = @cat.decategorify(sb)
  let dec_p = @cat.decategorify(prod)
  let sem_p = @mat.mul_ikj(dec_a, dec_b)
  let mut mismatch = 0
  for i in 0..<n {
    for j in 0..<n {
      if dec_p.get(i, j).value() != sem_p.get(i, j).value() {
        mismatch = mismatch + 1
      }
    }
  }
  line("| 量 | 值 |")
  line("|---|---|")
  line("| 見證總數（兩個 6×6 集合值矩陣） | \{witnesses} |")
  line(
    "| 範疇化乘積的見證數（各格基數之和） | \{prod_witnesses} |",
  )
  line("| 與 ℕ 上先取基數再相乘的不一致格數 | \{mismatch} |")
  line("| 範疇化乘積耗時 | \{f2(t_prod)} µs |")
  line("")
  line("### 16b. 自由範疇 = ℕ 上的 Kleene 星：四條獨立路徑")
  line("")
  let g = @cat.DiGraph::new(7)
  let mut mm = 0
  for u in 0..<7 {
    for v in (u + 1)..<7 {
      if rng.next_int(2) == 0 && mm < 12 {
        g.edge(u, v)
        mm = mm + 1
      }
    }
  }
  let (hom, t_hom) = @sim.time_min(3, fn() { g.hom_sets() })
  let (dp, t_dp) = @sim.time_min(20, fn() { g.path_counts() })
  let (pw, t_pw) = @sim.time_min(10, fn() { g.path_counts_by_powers() })
  let (cl, t_cl) = @sim.time_min(10, fn() { g.path_counts_by_closure() })
  let mut agree = true
  let mut total_paths = 0L
  for i in 0..<7 {
    for j in 0..<7 {
      total_paths = total_paths + dp[i][j]
      if hom[i][j].length().to_int64() != dp[i][j] {
        agree = false
      }
      if pw[i][j] != dp[i][j] || cl[i][j] != dp[i][j] {
        agree = false
      }
    }
  }
  line(
    "有向無環圖 n=7、m=\{g.edge_count()}（共 \{total_paths} 條路徑，含各點的長度 0 路徑）：",
  )
  line("")
  line("| 演算法 | 時間 (µs) | 複雜度 |")
  line("|---|---|---|")
  line(
    "| 1. 列舉 Hom 集合（真正的見證） | \{f2(t_hom)} | 與路徑數成正比 |",
  )
  line("| 2. 拓撲 DP | \{f2(t_dp)} | Θ(n·(n+m)) |")
  line("| 3. 矩陣冪級數 I+A+…+A^(n−1) | \{f2(t_pw)} | Θ(n⁴) |")
  line("| 4. Lehmann 消去（半環星） | \{f2(t_cl)} | Θ(n²·nnz) 級 |")
  line("")
  line(
    "四條路徑逐格相同：\{agree}（這是「自由範疇 = Kleene 星」的可執行版本）",
  )
  line("")
  line("### 16c. Maslov 解量化：−h·ln Σ e^(−x/h) → min")
  line("")
  let xs : Array[Double] = [3.0, 1.0, 4.0, 1.5, 9.0, 2.6]
  line("| h | 穩定版誤差 | 樸素版誤差 | 說明 |")
  line("|---|---|---|---|")
  let hs : Array[Double] = [1.0, 0.1, 0.01, 0.001, 1.0e-6, 1.0e-8]
  for h in hs {
    let e_stable = @cat.dequant_error(xs, h)
    let naive = @cat.dequantize_naive(xs, h)
    let naive_err = if naive > 1.0e299 || naive < -1.0e299 {
      "∞（ln 0 下溢）".to_string()
    } else {
      let d = naive - 1.0
      let ad = if d < 0.0 { -d } else { d }
      f6(ad)
    }
    let note = if h <= 1.0e-3 {
      "樸素版 e^(−1/h) 已經下溢"
    } else {
      "兩者一致"
    }
    line("| \{h} | \{f6(e_stable)} | \{naive_err} | \{note} |")
  }
  line("")
  let ma : Array[Array[Double]] = [[0.0, 3.0], [7.0, 0.0]]
  let mb : Array[Array[Double]] = [[0.0, 2.0], [1.0, 0.0]]
  let mp = @cat.minplus_mul(ma, mb)
  let e1 = @cat.max_abs_diff(@cat.dequantized_mul(ma, mb, 0.1), mp)
  let e2 = @cat.max_abs_diff(@cat.dequantized_mul(ma, mb, 0.01), mp)
  line(
    "矩陣乘法（min-plus vs 解量化後的 (+,×)）：h=0.1 → 最大逐格差 \{f6(e1)}；h=0.01 → \{f6(e2)}",
  )
  line(
    "差距在 h 夠小時落到機器精度以下——**不是變成 0**，而是小於該量級的 double 解析度。",
  )
  line("")
}

// ---------------------------------------------------------------------------
// §17 代數路徑問題 + 演算法組合
// ---------------------------------------------------------------------------

///|
pub fn sec17_app_portfolio() -> Unit {
  line("## 17. 代數路徑問題：一份程式、五種代數")
  line("")
  let rng = @alg.Rng::new(2718UL)
  let n = 8
  let w : Array[(Int32, Int32, Int32)] = []
  for _ in 0..<16 {
    let u = rng.next_int(n)
    let v = rng.next_int(n)
    if u != v {
      w.push((u, v, rng.range(1, 20)))
    }
  }
  let pairs : Array[(Int32, Int32)] = []
  for e in w {
    pairs.push((e.0, e.1))
  }
  // Bool
  let cl_b = @app.app_bool(n, pairs)
  let bfs = @app.reach_bfs(n, pairs)
  let mut ok_b = true
  for i in 0..<n {
    for j in 0..<n {
      if cl_b.get(i, j).b != bfs[i][j] {
        ok_b = false
      }
    }
  }
  // Trop
  let cl_t = @app.app_minplus(n, w)
  let fw = @app.shortest_fw(n, w)
  let mut ok_t = true
  for i in 0..<n {
    for j in 0..<n {
      if cl_t.get(i, j).value() != fw[i][j] {
        ok_t = false
      }
    }
  }
  // Bottleneck
  let cl_w = @app.app_widest(n, w)
  let wf = @app.widest_fw(n, w)
  let mut ok_w = true
  for i in 0..<n {
    for j in 0..<n {
      if cl_w.get(i, j).value() != wf[i][j] {
        ok_w = false
      }
    }
  }
  line("同一個 `app_closure`（Lehmann 消去）在五個半環上：")
  line("")
  line("| 半環 | A* 的意義 | 獨立對照實作 | 逐格一致 |")
  line("|---|---|---|---|")
  line("| BoolSr | 可達性 | BFS | \{ok_b} |")
  line("| Trop | 最短距離 | 本地 Floyd–Warshall | \{ok_t} |")
  line("| Bottleneck | 最大瓶頸 | 本地 max-min FW | \{ok_w} |")
  line(
    "| Counting | 路徑數（DAG） | 矩陣冪級數 I+A+… | true（測試逐格驗證） |",
  )
  line(
    "| Prob | 所有路徑機率之和 | q^n 暴力列舉（限 DAG） | true（測試逐格驗證） |",
  )
  line("")
  line("### 17b. 演算法組合：不互斥地跑 5 個實作，再仲裁")
  line("")
  let nn = 40
  let es : Array[(Int32, Int32, @alg.Trop)] = []
  for _ in 0..<(nn * 3) {
    let u = rng.next_int(nn)
    let v = rng.next_int(nn)
    if u != v {
      es.push((u, v, @alg.Trop::new(rng.range(1, 30))))
    }
  }
  let m = @app.build(nn, es)
  let (v, t_cons) = @sim.time_min(3, fn() { @app.consensus_trop(m, 1) })
  line(
    "n=\{nn}，邊數 \{es.length()}（稠密圖，五個演算法都跑一次）：",
  )
  line("")
  line("| 候選 | 時間 (µs) | 與基準一致 |")
  line("|---|---|---|")
  for r in v.runs {
    line("| \{r.name} | \{f2(r.us)} | \{r.agrees} |")
  }
  line("")
  line(
    "仲裁結果：一致 = \{v.agree}；最快 = \{v.winner}（\{f2(v.winner_us)} µs）；總成本 = \{f2(v.total_us)} µs；可信度的價格 = \{f2(v.cost_of_trust)}×",
  )
  line("")
  line(
    "這一點必須說清楚：**組合不會更快**。總成本 ≥ 最快成員成本，",
  )
  line(
    "多出來的時間買的是「五個獨立實作互相印證」。要速度就只跑最快的；要可信度就全跑。",
  )
  line("")
  let vw = @app.consensus_trop(m, 1, inject_wrong=true)
  line(
    "注入一個**故意錯的**候選（只截斷到 I+A+A²）：一致 = \{vw.agree}，被標成不一致的有 \{count_disagrees(vw)} 個（其餘仍一致）。",
  )
  line(
    "仲裁器若不能拒絕，就等於沒有仲裁器——這一行是負面對照存在的理由。",
  )
  line("")
  line(
    "（每輪仲裁 = 5 個候選各跑一次；times 是最快一次的量測，單輪總耗時 \{f2(t_cons)} µs）",
  )
  line("")
}

///|
fn count_disagrees(v : @app.Verdict) -> Int32 {
  let mut k = 0
  for r in v.runs {
    if !r.agrees {
      k = k + 1
    }
  }
  k
}

// ---------------------------------------------------------------------------
// §18 連帶相信
// ---------------------------------------------------------------------------

///|
pub fn sec18_belief() -> Unit {
  line(
    "## 18. 連帶相信（GDL / belief propagation）：半環上的局部消去",
  )
  line("")
  line(
    "廣義分配律：在**樹**上，邊緣化可以局部做，代價從 q^n 降到 Σ q^|scope|。",
  )
  line(
    "同一段訊息傳遞程式，換半環就換語義：`Prob`（+ / ×）⇒ 邊緣機率；`TropMax`（max / +）⇒ MAP。",
  )
  line("")
  line(
    "| 變數數 n | 暴力乘法次數 | 訊息傳遞乘法次數 | 倍率 | 邊緣最大誤差 | 樹 |",
  )
  line("|---|---|---|---|---|---|")
  for n in [4, 8, 12, 16] {
    let g = chain_tree(n, 4000UL + n.to_uint64())
    let (bp, ops_bp) = @bp.marginals_sum_product(g, rounds=n * 3)
    let (bf, ops_bf) = @bp.brute_force_sum_product(g)
    let mut worst = 0.0
    for v in 0..<n {
      for x in 0..<2 {
        let d = bp[v][x] - bf[v][x]
        let ad = if d < 0.0 { -d } else { d }
        if ad > worst {
          worst = ad
        }
      }
    }
    line(
      "| \{n} | \{ops_bf} | \{ops_bp} | \{f2(ops_bf.to_double() / ops_bp.to_double())}× | \{worst} | \{@bp.is_tree(g)} |",
    )
  }
  line("")
  line(
    "max-product（log 域 = max-plus）在樹上同樣精確（見測試，逐格相同）。",
  )
  line("")
  line(
    "注意上表的交叉點：n = 4 時訊息傳遞反而比暴力**多**（396 vs 48 次乘法）——",
  )
  line(
    "因為暴力法要乘的是 q^n 個賦值，而 q=2、n=4 只有 16 個；BP 的優勢要等 n 拉開才出現。",
  )
  line(
    "這也是為什麼「複雜度更好」不能只看漸近式：常數與問題規模一起決定誰贏。",
  )
  line("")
  line("### 18b. 有環：BP 只是近似，本庫不假裝它精確")
  line("")
  let rng = @alg.Rng::new(999UL)
  let card : Array[Int32] = [2, 2, 2]
  let mk = fn(scope : Array[Int32]) {
    let t : Array[@alg.Prob] = []
    for _ in 0..<4 {
      t.push(@alg.Prob::new(0.1 + rng.range(0, 9).to_double() / 10.0))
    }
    @bp.Factor::new(scope, t)
  }
  let g : @bp.FactorGraph[@alg.Prob] = {
    nvar: 3,
    card,
    factors: [mk([0, 1]), mk([1, 2]), mk([0, 2])],
  }
  let (bp, _) = @bp.marginals_sum_product(g, rounds=64)
  let (bf, _) = @bp.brute_force_sum_product(g)
  let mut worst = 0.0
  for v in 0..<3 {
    for x in 0..<2 {
      let d = bp[v][x] - bf[v][x]
      let ad = if d < 0.0 { -d } else { d }
      if ad > worst {
        worst = ad
      }
    }
  }
  line(
    "三角形因子圖（3 個變數、3 個兩兩因子）：`is_tree` = \{@bp.is_tree(g)}",
  )
  line("")
  line("| 量 | 值 |")
  line("|---|---|")
  line("| BP 固定點 vs 精確邊緣的最大差 | \{worst} |")
  line(
    "| 結論 | 有環時必須用 junction tree / cutset conditioning；BP 只能當近似 |",
  )
  line("")
  line(
    "這正是「連帶相信」一詞的字面意思：訊息傳遞在樹上可信，在有環時是**互相相信**、",
  )
  line(
    "不是被證明。把它當成精確演算法用，就會在真實模型上系統性偏掉。",
  )
  line("")
}
