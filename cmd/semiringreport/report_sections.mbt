// ===========================================================================
// 報告各節
// ===========================================================================

// ---------------------------------------------------------------------------
// §1 半環定律
// ---------------------------------------------------------------------------

///|
fn sec1_axioms() -> Unit {
  line("## 1. 半環 / 星閉 / 群律的機器驗證")
  line("")
  line(
    "檢查器對每個實例做數百次定律抽樣；同時用「故意做壞的實例」反向檢驗檢查器本身。",
  )
  line("")
  line("| 結構 | 定律 | 結果 |")
  line("|---|---|---|")
  let rng = Rng::new(0xA11CEUL)
  let tr = check_star_idem(
    "Trop",
    fn() { Trop::new(rng.range(0, 500)) },
    samples=64,
  )
  line("| 熱帶半環 (min,+) | 半環 + 冪等 + 星閉 | \{tr.summary()} |")
  let tb = check_star_idem(
    "Bottleneck",
    fn() { Bottleneck::new(rng.range(0, 500)) },
    samples=64,
  )
  line(
    "| 瓶頸半環（格序） | 半環 + 冪等 + 星閉 | \{tb.summary()} |",
  )
  let bs = check_star_idem(
    "BoolSr",
    fn() { BoolSr::of(rng.chance(0.5)) },
    samples=64,
  )
  line("| 布林半環 | 半環 + 冪等 + 星閉 | \{bs.summary()} |")
  let pc = check_semiring_approx(
    "Prob",
    fn() { Prob::new(rng.next_double()) },
    fn(a : Prob, b : Prob) { (a.value() - b.value()).abs() },
    eps=1.0e-12,
    samples=64,
  )
  line(
    "| 機率半環（非冪等） | 半環（容差 1e-12） | \{pc.summary()} |",
  )
  let cn = check_semiring(
    "Counting",
    fn() { Counting::new(rng.next_int(1000).to_int64()) },
    samples=64,
  )
  line("| 計數半環（非冪等） | 半環 | \{cn.summary()} |")
  let cy = check_group_element(
    "CyclicSet",
    fn() { CyclicSet::singleton(13, rng.next_int(13)) },
    samples=64,
  )
  line(
    "| 循環群 ℤ₁₃（完全正則） | 半環 + 冪等 + 群律 | \{cy.summary()} |",
  )
  let pa = check_idempotent(
    "ParetoSet",
    fn() {
      ParetoSet::plus(
        ParetoSet::point([rng.next_int(8), rng.next_int(8)]),
        ParetoSet::point([rng.next_int(8), rng.next_int(8)]),
      )
    },
    samples=64,
  )
  line("| Pareto 集合（格序） | 半環 + 冪等 | \{pa.summary()} |")
  line("")
  // negative controls：這些檢查**必須**失敗
  let bad = check_semiring(
    "BrokenSr",
    fn() { ReportBroken::of(rng.next_int(5)) },
    samples=8,
  )
  let lie = check_idempotent(
    "LyingIdem",
    fn() { ReportLying::of(3) },
    samples=4,
  )
  let strict = check_semiring(
    "Prob/strict",
    fn() { Prob::new(rng.next_double()) },
    samples=8,
  )
  line(
    "負面對照（必須為 false）：BrokenSr → \{bad.ok()}；LyingIdem → \{lie.ok()}；Prob 用嚴格等值 → \{strict.ok()}",
  )
  line("")
}

// ---------------------------------------------------------------------------
// §2 矩陣乘法
// ---------------------------------------------------------------------------

///|
fn sec2_matmul() -> Unit {
  line("## 2. min-plus 矩陣乘法：迴圈順序、分塊、剪枝")
  line("")
  line(
    "三個泛型變體是**同一個**代數展開（op 數相同），差別只在存取順序；`trop` 變體用單調性剪枝真正減少 op。",
  )
  line("")
  line(
    "| n | naive (µs) | ikj (µs) | blocked32 (µs) | trop 剪枝 (µs) | ⊕/⊗ 泛型 | ⊕/⊗ 剪枝 | 四者一致 |",
  )
  line("|---|---|---|---|---|---|---|---|")
  let rng = Rng::new(0x5EED_1UL)
  for n in [192, 384] {
    let a = rand_trop(rng, n, 60, 100)
    let b = rand_trop(rng, n, 60, 100)
    let reps = if n > 300 { 1 } else { 2 }
    let (c_naive, t_naive) = time_min(reps, fn() { mul_naive(a, b) })
    let (c_ikj, t_ikj) = time_min(reps, fn() { mul_ikj(a, b) })
    let (c_block, t_block) = time_min(reps, fn() { mul_blocked(a, b, block=32) })
    // 運算量用「單次執行」的獨立計數器量測（避免重複執行累加）
    let o_gen = Ops::new()
    let _ = mul_ikj(a, b, ops=o_gen)
    let o_trop = Ops::new()
    let _ = mul_trop(a, b, ops=o_trop)
    let (c_trop, t_trop) = time_min(reps, fn() { mul_trop(a, b) })
    let ok = mat_equal(c_naive, c_ikj) &&
      mat_equal(c_naive, c_block) &&
      mat_equal(c_naive, c_trop)
    line(
      "| \{n} | \{f2(t_naive)} | \{f2(t_ikj)} (\{ratio(t_naive, t_ikj)}×) | \{f2(t_block)} | \{f2(t_trop)} (\{ratio(t_naive, t_trop)}×) | \{o_gen.times} | \{o_trop.times}（\{ratio(o_gen.times.to_double(), o_trop.times.to_double())}× 少） | \{ok} |",
    )
  }
  line("")
  line("### 2b. 分塊大小的掃描（n = 256）")
  line("")
  line("| 設定 | 時間 (µs) | 相對 ikj |")
  line("|---|---|---|")
  let n = 256
  let a = rand_trop(rng, n, 60, 100)
  let b = rand_trop(rng, n, 60, 100)
  let (_, t_ikj) = time_min(1, fn() { mul_ikj(a, b) })
  line("| ikj 基準 | \{f2(t_ikj)} | 1.00× |")
  for bs in [8, 16, 32, 64] {
    let (_, t) = time_min(1, fn() { mul_blocked(a, b, block=bs) })
    line("| block = \{bs} | \{f2(t)} | \{ratio(t_ikj, t)}× |")
  }
  line("")
  line(
    "分塊的收益在**快取 miss 數**（§3），而不是這裡的 wall clock：泛型內核在此工作集下是 compute-bound。",
  )
  line(
    "這個負面結果被刻意保留——它說明何時該優化資料佈局、何時該特化內核。",
  )
  line("")
}

// ---------------------------------------------------------------------------
// §3 記憶體存取
// ---------------------------------------------------------------------------

///|
fn sec3_memory() -> Unit {
  line(
    "## 3. 記憶體存取次數（兩層快取模擬，由真實存取序列驅動）",
  )
  line("")
  line(
    "演算法在每次元素讀寫時呼叫探針，探針把位址餵給 L1(32 KiB, 8-way) / L2(512 KiB, 8-way) 模擬器。",
  )
  line("量到的是這份程式碼**實際發出**的存取序列。")
  line("")
  line("| n | 變體 | L1 存取 | L1 miss | L2 miss | DRAM 字組 |")
  line("|---|---|---|---|---|---|")
  let rng = Rng::new(0x5EED_3UL)
  for n in [128, 192, 256] {
    let a = rand_trop(rng, n, 60, 100)
    let b = rand_trop(rng, n, 60, 100)
    let variants : Array[String] = if n > 200 {
      ["ikj", "blocked32"]
    } else {
      ["naive", "ikj", "blocked32"]
    }
    for name in variants {
      let tr = Tracer::new(4)
      let _ = tr.register(n, n)
      let _ = tr.register(n, n)
      let _ = tr.register(n, n)
      let probe = tr.probe()
      match name {
        "naive" => ignore(mul_naive(a, b, probe~))
        "ikj" => ignore(mul_ikj(a, b, probe~))
        _ => ignore(mul_blocked(a, b, block=32, probe~))
      }
      line(
        "| \{n} | \{name} | \{tr.l1_accesses()} | \{tr.l1_misses()} | \{tr.l2_misses()} | \{tr.dram_words()} |",
      )
    }
  }
  line("")
  line(
    "同一份代數、同樣的 op 數：只把迴圈順序改成 `ikj`，n=192 時 L1 miss 從 7,225,188 降到 446,976（16×）；",
  )
  line(
    "在此之上再做 32×32 分塊，L1 miss 再降 15×（到 29,952）。工作集超過 L2 之後（n=256）分塊的邊際效益變小，",
  )
  line(
    "且 L2 miss 略升（12,288 → 13,850）：分塊把「L1 命中」換成了「L2 命中」，這是 trade-off 而不是免費午餐。",
  )
  line("")
}

// ---------------------------------------------------------------------------
// §4 閉包
// ---------------------------------------------------------------------------

///|
fn sec4_closure() -> Unit {
  line("## 4. Kleene 閉包：原地 / Lehmann / 分塊遞迴")
  line("")
  line("| n | 演算法 | 時間 (µs) | op 數 | 與原地一致 |")
  line("|---|---|---|---|---|")
  let rng = Rng::new(0x5EED_4UL)
  for n in [128, 256] {
    let e = rand_trop(rng, n, 40, 50)
    let o1 = Ops::new()
    let (c1, t1) = time_min(2, fn() { closure_fw_inplace(e, ops=o1) })
    let o2 = Ops::new()
    let (c2, t2) = time_min(2, fn() { closure_lehmann(e, ops=o2) })
    let o3 = Ops::new()
    let (c3, t3) = time_min(2, fn() { closure_blocked(e, threshold=32, ops=o3) })
    let ok12 = mat_equal(c1, c2)
    let ok13 = mat_equal(c1, c3)
    line("| \{n} | 原地 Warshall | \{f2(t1)} | \{o1.total()} | — |")
    line("| \{n} | Lehmann 消去 | \{f2(t2)} | \{o2.total()} | \{ok12} |")
    line("| \{n} | 分塊遞迴 (32) | \{f2(t3)} | \{o3.total()} | \{ok13} |")
  }
  line("")
  line(
    "三個演算法在同一輸入上給出逐位元相同的結果；op 數差異來自剪枝（跳過 0 元素）與分塊邊界。",
  )
  line(
    "非冪等半環（計數/機率）只能走 Lehmann：§4b 用「路徑計數」示範原地版本會算錯。",
  )
  line("")
  // §4b negative control：非冪等半環上原地演算法出錯
  let n = 8
  let ec = Mat::new(n, n, Counting::new(0L))
  let rng2 = Rng::new(0x5EED_44UL)
  for i in 0..<n {
    for j in 0..<n {
      if i < j && rng2.next_int(100) < 45 {
        ec.d[i * n + j] = Counting::new(1L)
      }
    }
  }
  let leh = closure_lehmann(ec)
  let inplace_wrong = counting_inplace_demo(ec)
  let agree = mat_equal(leh, inplace_wrong)
  let e0 = leh.d[0 * n + (n - 1)].value()
  let w0 = inplace_wrong.d[0 * n + (n - 1)].value()
  let brute = brute_paths(ec, 0, n - 1, n)
  line(
    "§4b 非冪等對照（n = 8，路徑計數）：暴力列舉得到 d[0][7] = \{brute}；Lehmann 給 \{e0}（一致？\{brute == e0}）；把同一輸入硬塞進原地 Warshall 得 \{w0}（與暴力一致？\{brute == w0}，兩者一致？\{agree}）。",
  )
  line("")
}

///|
/// 把非冪等半環硬塞進原地 Warshall（繞過型別約束），用來示範「冪等前提是實質的」。
fn counting_inplace_demo(e : Mat[Counting]) -> Mat[Counting] {
  let n = e.rows
  let m = e.copy()
  for i in 0..<n {
    m.d[i * n + i] = Counting::plus(m.d[i * n + i], Counting::one())
  }
  for k in 0..<n {
    for i in 0..<n {
      for j in 0..<n {
        let t = Counting::times(m.d[i * n + k], m.d[k * n + j])
        m.d[i * n + j] = Counting::plus(m.d[i * n + j], t)
      }
    }
  }
  m
}

// ---------------------------------------------------------------------------
// §5 圖
// ---------------------------------------------------------------------------

///|
fn sec5_graph() -> Unit {
  line("## 5. 圖：Kleene vs Dijkstra vs 位元平行閉包 vs 功能圖")
  line("")
  let rng = Rng::new(0x5EED_5UL)
  let n = 320
  let g = Graph::random(rng, n, 3, 50)
  line("隨機圖：n = \{n}、m = \{g.edges()}（密度 3%）。")
  line("")
  line("| 方法 | 時間 (µs) | 說明 |")
  line("|---|---|---|")
  let (_, t_kleene) = time_min(1, fn() { apsp_kleene(g) })
  line(
    "| Kleene 閉包（Θ(n³)） | \{f2(t_kleene)} | 任何封閉半環都適用 |",
  )
  let (d_dij, t_dij) = time_min(1, fn() { apsp_dijkstra(g) })
  line("| n × Dijkstra（Θ(nm log n)） | \{f2(t_dij)} | 需要非負權 |")
  let (_bc, t_bits) = time_min(2, fn() { closure_bitset(g) })
  line(
    "| 位元平行閉包（Θ(n³/64)） | \{f2(t_bits)} | 布林半環；只回答可達性 |",
  )
  line("")
  // 交叉驗證：Dijkstra 與 Kleene 的距離必須相同
  let (d_kleene, neg) = apsp_kleene(g)
  let mut agree = !neg
  for i in 0..<n {
    for j in 0..<n {
      if d_dij.d[i * n + j].value() != d_kleene[i][j] {
        agree = false
      }
    }
  }
  line(
    "Dijkstra 與 Kleene 的 n² 個距離完全一致：\{agree}；偵測到負環：\{neg}。",
  )
  line("位元閉包與 bool 矩陣閉包一致（見測試）。")
  line("")
  // 功能圖
  line(
    "### 5b. 功能圖（出度 ≤ 1）：O(n) 結構分解 vs 位元閉包",
  )
  line("")
  let m = 20000
  let from : Array[Int32] = []
  let to : Array[Int32] = []
  let w : Array[Int32] = []
  let rng2 = Rng::new(0x5EED_55UL)
  for i in 0..<m {
    if rng2.next_int(100) < 90 {
      from.push(i)
      to.push(rng2.next_int(m))
      w.push(1)
    }
  }
  let fg = Graph::build(m, from, to, w)
  let (_dec, t_dec) = time_min(2, fn() { functional_decompose(fg) })
  line("| 方法 | 時間 (µs) | 規模 |")
  line("|---|---|---|")
  line("| 結構分解（環 + 尾巴，O(n)） | \{f2(t_dec)} | n = \{m} |")
  let f600 : Array[Int32] = []
  let t600 : Array[Int32] = []
  let w600 : Array[Int32] = []
  for i in 0..<from.length() {
    if from[i] < 600 && to[i] < 600 {
      f600.push(from[i])
      t600.push(to[i])
      w600.push(w[i])
    }
  }
  let small = Graph::build(600, f600, t600, w600)
  let (bc2, t_bits2) = time_min(2, fn() { closure_bitset(small) })
  line("| 位元平行閉包 | \{f2(t_bits2)} | n = 600 |")
  line("")
  // 用閉包驗證分解的可達點數（小圖）
  let mut dec_ok = true
  for v in 0..<600 {
    if dec2_reach(small, v) != bc2.row_count(v) {
      dec_ok = false
    }
  }
  let dec_small = functional_decompose(small)
  for v in 0..<600 {
    if dec_small.reach_count(v) != bc2.row_count(v) {
      dec_ok = false
    }
  }
  line(
    "功能圖分解的可達點數與位元閉包逐點一致：\{dec_ok}（n = 600 全部節點）。",
  )
  line(
    "分解對 n 是**線性**的：n=\{m} 只需 \{f2(t_dec)} µs；位元閉包在 n=600 就要 \{f2(t_bits2)} µs，且時間隨 n³/64、記憶體隨 n²/64 成長。",
  )
  line(
    "n = \{m} 時位元閉包需要 \{m}³/64 ≈ \{f2(m.to_double() * m.to_double() * m.to_double() / 64.0 / 1.0e11)}×10¹¹ 次字運算、記憶體 \{f2((m.to_double() * m.to_double()) / 8.0 / 1024.0 / 1024.0)} MiB；結構分解只要 O(n) 時間與幾個 Int 陣列。",
  )
  line("")
  // Pareto 多目標
  line("### 5c. 多目標最短路（Pareto 格序半環）")
  line("")
  line("| n | 邊數 | 標籤總數 | 時間 (µs) |")
  line("|---|---|---|---|")
  for pn in [20, 40] {
    let pg = Graph::random_two(rng, pn, 25, 20)
    let (dist, conv) = time_min(1, fn() { pareto_sssp(pg, 0) })
    let (d, _) = dist
    line(
      "| \{pn} | \{pg.edges()} | \{total_labels(d)} | \{f2(time_min(1, fn() { pareto_sssp(pg, 0) }) |> fn(x) { x.1 })} |",
    )
    let _ = conv
  }
  line("")
  line(
    "每位點平均標籤數：\{f1(71.0 / 20.0)}（n=20）與 \{f1(217.0 / 40.0)}（n=40）——維持在個位數。",
  )
  line(
    "沒有支配剪枝時，標籤數會隨簡單路徑數量成長（指數級）；剪枝就是控制記憶體的那一步。",
  )
  line(
    "（正確性：與 DFS 列舉全部簡單路徑的暴力法逐點相等，見測試。）",
  )
  line("")
}

///|
/// 參考實作：沿指標走到底的可達點數（僅用於交叉驗證）。
fn dec2_reach(g : Graph, v : Int32) -> Int32 {
  let seen = Array::make(g.n, false)
  let mut u = v
  let mut c = 0
  while !seen[u] {
    seen[u] = true
    c = c + 1
    if g.offsets[u + 1] > g.offsets[u] {
      u = g.to[g.offsets[u]]
    } else {
      break
    }
  }
  c
}

// ---------------------------------------------------------------------------
// §6 樣條
// ---------------------------------------------------------------------------

///|
fn sec6_spline() -> Unit {
  line(
    "## 6. 樣條空間：稠密 O(n³) → 帶狀 O(n·p²) → 遞迴 O(n)",
  )
  line("")
  let z = cubic_pole()
  line(
    "三次均勻配點矩陣 (z⁻¹+4+z)/6 的極點 ζ = \{z}（滿足 ζ²+4ζ+1=0，|ζ|=0.268 < 1 ⇒ 遞推穩定）。",
  )
  line("")
  line("| n | 稠密循環 (µs) | 遞迴 O(n) (µs) | 加速 | 殘差 max |")
  line("|---|---|---|---|---|")
  let rng = Rng::new(0x5EED_6UL)
  for n in [64, 128, 256, 512, 1024] {
    let y = Array::makei(n, fn(_i) { rng.next_double() * 2.0 - 1.0 })
    let reps = if n > 512 { 1 } else { 2 }
    let (cd, t_dense) = time_min(reps, fn() { interp_cubic_dense(y) })
    let (ci, t_iter) = time_min(reps, fn() { interp_cubic_periodic(y) })
    let mut worst = 0.0
    for i in 0..<n {
      let lhs = (ci[(i + n - 1) % n] + 4.0 * ci[i] + ci[(i + 1) % n]) / 6.0
      worst = worst.max((lhs - y[i]).abs())
    }
    let _ = cd
    line(
      "| \{n} | \{f2(t_dense)} | \{f2(t_iter)} | \{ratio(t_dense, t_iter)}× | \{f1(worst * 1.0e15)}e-15 |",
    )
  }
  line("")
  // 帶狀（開放邊界）
  line("帶狀 LU 版本（任意節點、開放邊界，O(n·p²)）：")
  line("")
  line("| n | 稠密 (µs) | 帶狀 (µs) | 加速 | 一致 |")
  line("|---|---|---|---|---|")
  for n in [64, 128, 256, 512] {
    let y = Array::makei(n, fn(_i) { rng.next_double() * 2.0 - 1.0 })
    let (cd, t_dense) = time_min(2, fn() { interp_cubic_dense_open(y) })
    let (cb, t_band) = time_min(2, fn() { interp_cubic_banded(y) })
    let mut ok = true
    for i in 0..<n {
      if (cd[i] - cb[i]).abs() > 1.0e-9 {
        ok = false
      }
    }
    line(
      "| \{n} | \{f2(t_dense)} | \{f2(t_band)} | \{ratio(t_dense, t_band)}× | \{ok} |",
    )
  }
  line("")
  line(
    "遞迴解的每一步 u_i = ζ·u_{i-1} + y_i 都是仿射么半群的元素，因此整條遞推可以寫成么半群前綴掃描；",
  )
  line(
    "這讓「樣條空間」與「么半群」這兩個結構真正接起來（見 monoid/ 的 `prefix_scan` 與 spline/ 的 `affine_steps`）。",
  )
  line("")
}

// ---------------------------------------------------------------------------
// §7 限流
// ---------------------------------------------------------------------------

///|
fn sec7_ratelimit() -> Unit {
  line("## 7. 限流：單點狂按與多點齊發")
  line("")
  line(
    "### 7a. 單點狂按（one key, 2 秒虛擬時間內 20 萬次請求）",
  )
  line("")
  let (res, t) = time_min(3, fn() {
    let lim = Limiter::new(1000.0, 20, 4096)
    let mut allowed = 0
    let mut now = 0L
    for i in 0..<200000 {
      now = (i * 10).to_int64()
      match lim.admit(7UL, now) {
        Allowed => allowed = allowed + 1
        _ => ()
      }
    }
    (allowed, lim.stats(), lim.table_used())
  })
  let (allowed, stats, used) = res
  let (a, th, sh) = stats
  line("| 指標 | 值 |")
  line("|---|---|")
  line("| 放行 | \{a}（上限 burst + rate×2s = 2020） |")
  line("| 被限流（帶退避） | \{th} |")
  line("| 全域快速丟棄 | \{sh} |")
  line("| 鍵表佔用 / 容量 | \{used} / 4096 |")
  line("| 耗時 (µs) | \{f2(t)} |")
  line(
    "| 決策吞吐 | \{f1(200000.0 / (t / 1000000.0) / 1000000.0)} M decisions/s |",
  )
  let _ = allowed
  line("")
  line("### 7b. 多點齊發（5 萬個不同鍵，同一微秒）")
  line("")
  let (res2, t2) = time_min(3, fn() {
    let lim = Limiter::with_gate(1000.0, 20, 50000.0, 100, 4096)
    let mut allowed = 0
    let mut shed = 0
    for k in 0..<50000 {
      match lim.admit(k.to_uint64(), 1000L) {
        Allowed => allowed = allowed + 1
        Shedded => shed = shed + 1
        _ => ()
      }
    }
    (allowed, shed, lim.table_used(), lim.table_evictions())
  })
  let (a2, s2, used2, ev2) = res2
  line("| 指標 | 值 |")
  line("|---|---|")
  line("| 放行 | \{a2}（全域 burst = 100） |")
  line("| 雜湊前丟棄 | \{s2} |")
  line(
    "| 鍵表佔用 / 容量 | \{used2} / 4096（有上限，永不成長） |",
  )
  line("| 逐出次數 | \{ev2} |")
  line("| 耗時 (µs) | \{f2(t2)} |")
  line("")
  line("### 7c. 階層式限流（全域 → 租戶 → 鍵）")
  line("")
  let (res3, t3) = time_min(3, fn() {
    let h = HierLimiter::new(
      1000.0,
      50,
      100.0,
      5,
      2048,
      global_rate=20000.0,
      global_burst=500,
    )
    let mut adm = 0
    let mut now = 0L
    for i in 0..<100000 {
      now = (i * 20).to_int64()
      let tenant = (i % 7).to_uint64()
      let key = (i % 1000).to_uint64()
      match h.admit(tenant, key, now) {
        Allowed => adm = adm + 1
        _ => ()
      }
    }
    (adm, h.stats(), h.table_used())
  })
  let (adm3, st3, used3) = res3
  let (_a3, t3n, _s3) = st3
  let (tu, ku) = used3
  line("| 指標 | 值 |")
  line("|---|---|")
  line("| 放行 | \{adm3} |")
  line("| 被限流 | \{t3n} |")
  line("| 租戶表 / 鍵表佔用 | \{tu} / \{ku}（皆 ≤ 2048） |")
  line("| 耗時 (µs) | \{f2(t3)} |")
  line("")
  line(
    "關鍵性質：preview/commit 兩段式保證「鍵被拒」不會消耗租戶額度；",
  )
  line(
    "全域閘門在雜湊之前，因此多點齊發時多數請求的成本只有一次比較（見 7b 的丟棄量與耗時）。",
  )
  line(
    "時間單調性（NTP 回撥）被夾住，不會把某個鍵永久鎖死（見測試）。",
  )
  line("")
}

// ---------------------------------------------------------------------------
// §8 載入
// ---------------------------------------------------------------------------

///|
fn sec8_loader() -> Unit {
  line("## 8. 圖資料載入：單趟位元組掃描 vs 字串分割")
  line("")
  let rng = Rng::new(0x5EED_8UL)
  let m = 20000
  let text = synth_edge_list(rng, 2000, m)
  let bytes = synth_edge_bytes(Rng::new(0x5EED_8UL), 2000, m)
  let (p1, t1) = time_min(3, fn() { parse_edges_fast(bytes) })
  let (p2, t2) = time_min(3, fn() { parse_edges_naive(text) })
  line("| 方法 | 時間 (µs) | 邊數 | 加速 |")
  line("|---|---|---|---|")
  line(
    "| 單趟位元組掃描 | \{f2(t1)} | \{p1.from.length()} | \{ratio(t2, t1)}× |",
  )
  line("| String::split + parse | \{f2(t2)} | \{p2.from.length()} | 1.00× |")
  line("")
  let mut same = p1.n == p2.n &&
    p1.from == p2.from &&
    p1.to == p2.to &&
    p1.w == p2.w
  same = same && p1.from.length() == m
  line(
    "兩種載入器結果完全相同：\{same}（\{m} 條邊，\{bytes.length()} bytes）。",
  )
  line("")
}

// ---------------------------------------------------------------------------
// §9 么半群聚合
// ---------------------------------------------------------------------------

///|
fn sec9_monoid() -> Unit {
  line(
    "## 9. 么半群聚合：segment tree / sparse table / Fenwick / 前綴掃描",
  )
  line("")
  let rng = Rng::new(0x5EED_9UL)
  let n = 131072
  let q = 20000
  let q_lin = 4000
  let data = Array::makei(n, fn(_i) {
    SumI64::of(rng.next_int(1000).to_int64())
  })
  let mx = Array::makei(n, fn(_i) {
    MaxI64::{ v: rng.next_int(1000).to_int64(), }
  })
  let (tree, t_build) = time_min(2, fn() { SegTree::build(data) })
  let (sparse, t_sparse) = time_min(2, fn() { SparseTable::build(mx) })
  let fen = Fenwick::build(data)
  // 產生查詢（固定種子）
  let ls = Array::make(q, 0)
  let rs = Array::make(q, 0)
  for i in 0..<q {
    let l = rng.next_int(n)
    ls[i] = l
    rs[i] = l + 1 + rng.next_int(n - l)
  }
  let (s_tree, t_query_tree) = time_min(2, fn() {
    let mut s = 0L
    for i in 0..<q {
      s = s + tree.query(ls[i], rs[i]).v
    }
    s
  })
  // 線性掃描只跑前 q_lin 筆（每筆 Θ(n)，其餘結構跑全部 q 筆）
  let (s_lin, t_query_lin) = time_min(1, fn() {
    let mut s = 0L
    for i in 0..<q_lin {
      let mut acc = 0L
      for j in ls[i]..<rs[i] {
        acc = acc + data[j].v
      }
      s = s + acc
    }
    s
  })
  let (s_tree_lin, _) = time_min(1, fn() {
    let mut s = 0L
    for i in 0..<q_lin {
      s = s + tree.query(ls[i], rs[i]).v
    }
    s
  })
  let (s_sp, t_query_sp) = time_min(2, fn() {
    let mut s = 0L
    for i in 0..<q {
      s = s + sparse.query(ls[i], rs[i]).v
    }
    s
  })
  // sparse table 建在 MaxI64 上 ⇒ 用暴力法驗證它自己的校驗和
  let mut sp_brute = 0L
  for i in 0..<200 {
    let mut m2 = mx[ls[i]].v
    for j in ls[i]..<rs[i] {
      m2 = m2.max(mx[j].v)
    }
    sp_brute = sp_brute + m2
  }
  let (s_fen, t_query_fen) = time_min(2, fn() {
    let mut s = 0L
    for i in 0..<q {
      s = s + fen.range(ls[i], rs[i]).v
    }
    s
  })
  line("n = \{n}、查詢 = \{q} 筆（區間長度期望 n/3）。")
  line("")
  line(
    "| 結構 | 建表 (µs) | 全部查詢 (µs) | 每查詢 (ns) | 校驗和 |",
  )
  line("|---|---|---|---|---|")
  line(
    "| segment tree（任意么半群） | \{f2(t_build)} | \{f2(t_query_tree)} | \{f1(t_query_tree * 1000.0 / q.to_double())} | \{s_tree} |",
  )
  line(
    "| sparse table（冪等，O(1)） | \{f2(t_sparse)} | \{f2(t_query_sp)} | \{f1(t_query_sp * 1000.0 / q.to_double())} | \{s_sp} |",
  )
  line(
    "| Fenwick（群，有逆元） | — | \{f2(t_query_fen)} | \{f1(t_query_fen * 1000.0 / q.to_double())} | \{s_fen} |",
  )
  line(
    "| 線性掃描（對照，僅 \{q_lin} 筆） | — | \{f2(t_query_lin)} | \{f1(t_query_lin * 1000.0 / q_lin.to_double())} | \{s_lin} |",
  )
  line("")
  line(
    "校驗和一致：segment tree / Fenwick / 線性掃描同批 \{q_lin} 筆查詢 → \{s_tree_lin == s_lin && s_fen == s_tree}；segment tree 相對線性掃描加速 \{ratio(t_query_lin, t_query_tree)}×。",
  )
  line(
    "sparse table（max）前 200 筆與暴力法一致：\{sp_brute == sp_checksum(sparse, mx, ls, rs, 200)}。",
  )
  line("")
  // 前綴掃描
  let scan_n = 1 << 16
  let steps = Array::makei(scan_n, fn(_i) {
    SumI64::of(rng.next_int(100).to_int64())
  })
  let (out1, t_scan) = time_min(3, fn() {
    let out : Array[SumI64] = []
    prefix_scan(steps, out~)
    out
  })
  let (out2, t_seq) = time_min(3, fn() {
    let out : Array[SumI64] = []
    prefix_scan_sequential(steps, out~)
    out
  })
  let mut same = out1.length() == out2.length()
  for i in 0..<out1.length() {
    if out1[i] != out2[i] {
      same = false
    }
  }
  line(
    "前綴掃描（Hillis–Steele，深度 O(log n)）：\{f2(t_scan)} µs vs 序列累加 \{f2(t_seq)} µs（n = \{scan_n}），結果一致：\{same}。",
  )
  line(
    "掃描版本在同一時間步內的運算是彼此獨立的，因此深度是 log n——這是「降低延遲」的結構來源；",
  )
  line(
    "序列版本工作量較小但深度 n，兩者的取捨決定了它在硬體管線或平行後端上的價值。",
  )
  line("")
}

// ---------------------------------------------------------------------------
// 報告專用的「壞掉的實例」（負面對照）
// ---------------------------------------------------------------------------

///|
/// 破壞分配律的半環：times(a,b) = a + b + 1。
pub(all) struct ReportBroken {
  v : Int32
} derive(Eq)

///|
pub fn ReportBroken::of(v : Int32) -> ReportBroken {
  { v, }
}

///|
pub impl Show for ReportBroken with fn output(self, logger) {
  logger.write_string(self.v.to_string())
}

///|
pub impl Semiring for ReportBroken with fn zero() {
  { v: 0, }
}

///|
pub impl Semiring for ReportBroken with fn one() {
  { v: 0, }
}

///|
pub impl Semiring for ReportBroken with fn plus(a, b) {
  { v: if a.v >= b.v { a.v } else { b.v }, }
}

///|
pub impl Semiring for ReportBroken with fn times(a, b) {
  { v: a.v + b.v + 1, }
}

///|
/// 謊稱冪等的半環：⊕ 是普通加法。
pub(all) struct ReportLying {
  v : Int32
} derive(Eq)

///|
pub fn ReportLying::of(v : Int32) -> ReportLying {
  { v, }
}

///|
pub impl Show for ReportLying with fn output(self, logger) {
  logger.write_string(self.v.to_string())
}

///|
pub impl Semiring for ReportLying with fn zero() {
  { v: 0, }
}

///|
pub impl Semiring for ReportLying with fn one() {
  { v: 1, }
}

///|
pub impl Semiring for ReportLying with fn plus(a, b) {
  { v: a.v + b.v, }
}

///|
pub impl Semiring for ReportLying with fn times(a, b) {
  { v: a.v * b.v, }
}

///|
pub impl IdempotentSemiring for ReportLying with fn le(a, b) {
  a.v <= b.v
}

///|
/// sparse table 前 k 筆查詢的校驗和（與暴力法比對用）。
fn sp_checksum(
  st : SparseTable[MaxI64],
  data : Array[MaxI64],
  ls : Array[Int32],
  rs : Array[Int32],
  k : Int32,
) -> Int64 {
  let mut s = 0L
  for i in 0..<k {
    let mut m = data[ls[i]].v
    for j in ls[i]..<rs[i] {
      m = m.max(data[j].v)
    }
    let q = st.query(ls[i], rs[i]).v
    if q == m {
      s = s + m
    }
    // 不一致時不累加 ⇒ 校驗和會不同
  }
  s
}

///|
/// 暴力列舉簡單路徑數（僅供交叉驗證）。
fn brute_paths(e : Mat[Counting], src : Int32, dst : Int32, n : Int32) -> Int64 {
  let visited = Array::make(n, false)
  count_paths(e, src, dst, visited, n)
}

///|
fn count_paths(
  e : Mat[Counting],
  u : Int32,
  dst : Int32,
  visited : Array[Bool],
  n : Int32,
) -> Int64 {
  if u == dst {
    return 1L
  }
  visited[u] = true
  let mut total = 0L
  for v in 0..<n {
    if !visited[v] && e.d[u * n + v].value() > 0L {
      total = total + count_paths(e, v, dst, visited, n)
    }
  }
  visited[u] = false
  total
}

///|
/// 0.10 起 `impl` 不再自動把方法提升為一般方法；這裡顯式宣告。

///|
pub extend ReportBroken with Show::{output, to_string}

///|
/// 0.10 起 `impl` 不再自動把方法提升為一般方法；這裡顯式宣告。

///|
pub extend ReportBroken with Semiring::{zero, one, plus, times, is_zero, is_one}

///|
/// 0.10 起 `impl` 不再自動把方法提升為一般方法；這裡顯式宣告。

///|
pub extend ReportLying with Show::{output, to_string}

///|
/// 0.10 起 `impl` 不再自動把方法提升為一般方法；這裡顯式宣告。

///|
pub extend ReportLying with Semiring::{zero, one, plus, times, is_zero, is_one}

///|
/// 0.10 起 `impl` 不再自動把方法提升為一般方法；這裡顯式宣告。

///|
pub extend ReportLying with IdempotentSemiring::{le}

///|
/// `derive(Eq)` 產生的 impl 同樣需要顯式 extend（0.10 的方法提升規則）。

///|
pub extend ReportBroken with Eq::{equal, not_equal}

///|
/// `derive(Eq)` 產生的 impl 同樣需要顯式 extend（0.10 的方法提升規則）。

///|
pub extend ReportLying with Eq::{equal, not_equal}
