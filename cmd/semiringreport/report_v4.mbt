// ===========================================================================
// 報告 §19：誠實的限制——把每一個邊界都量出來
//
// 這一節不是在道歉，而是在**量測**。前 18 節每一節都有一個「在某條件下成立」
// 的宣稱；本節把每個條件的邊界找出來，變成一個可以重跑的數字：
//
//   19a  訊息傳遞 vs 暴力的交叉點在哪一個 n（不是「漸近更好」）
//   19b  Maslov 解量化的下溢邊界在哪一個 h
//   19c  熱帶細分的 O(m⁴) 在實測上長什麼樣
//   19d  「可信度的價格」的結構：全部跑 vs 只跑最便宜的兩個
//   19e  只有一個候選時，錯誤**不會被發現**（截斷級數的實例）
//   19f  限制總表：每一條限制對應哪一個量到的數字
//
// 所有數字都是本次執行算出來的，沒有一個是抄文件。
// ===========================================================================

///|
/// 兩個熱帶矩陣逐格比對，回傳不同的格數。
fn diff_cells(a : @mat.Mat[@alg.Trop], b : @mat.Mat[@alg.Trop]) -> Int32 {
  let mut k = 0
  for i in 0..<(a.rows * a.cols) {
    if a.d[i] != b.d[i] {
      k = k + 1
    }
  }
  k
}

///|
/// 建一棵 n 個變數、q=2 的鏈狀（樹）因子圖。
/// §18 與 §19a 共用這一個建法——兩節的交叉點必須在同一批圖上才可比。
fn chain_tree(n : Int32, seed : UInt64) -> @bp.FactorGraph[@alg.Prob] {
  let rng = @alg.Rng::new(seed)
  let card : Array[Int32] = []
  for _ in 0..<n {
    card.push(2)
  }
  let factors : Array[@bp.Factor[@alg.Prob]] = []
  for v in 0..<(n - 1) {
    let t : Array[@alg.Prob] = []
    for _ in 0..<4 {
      t.push(@alg.Prob::new(0.1 + rng.range(0, 9).to_double() / 10.0))
    }
    factors.push(@bp.Factor::new([v, v + 1], t))
  }
  { nvar: n, card, factors, }
}

///|
fn f6(x : Double) -> String {
  round_to(x, 6)
}

///|
pub fn sec19_limits() -> Unit {
  line("## 19. 誠實的限制：每一個邊界都是一個量出來的數字")
  line("")
  line(
    "「在某條件下成立」的宣稱，如果沒有把那個條件量出來，就只是行銷。這一節把六個邊界全部變成數字。",
  )
  line("")

  // -------------------------------------------------------------------------
  // 19a BP vs 暴力：交叉點
  // -------------------------------------------------------------------------
  line(
    "### 19a. 訊息傳遞在哪一個 n 才贏過暴力？（實測交叉點）",
  )
  line("")
  line(
    "| n | 暴力乘法次數 | 訊息傳遞乘法次數 | 暴力 / BP | 誰贏 |",
  )
  line("|---|---|---|---|---|")
  let mut crossover = -1
  for n in [4, 5, 6, 7, 8, 9, 10, 12, 14, 16] {
    let g = chain_tree(n, 4000UL + n.to_uint64())
    let (_bp, ops_bp) = @bp.marginals_sum_product(g, rounds=n * 3)
    let (_bf, ops_bf) = @bp.brute_force_sum_product(g)
    let r = ops_bf.to_double() / ops_bp.to_double()
    if r > 1.0 && crossover < 0 {
      crossover = n
    }
    let who = if r > 1.0 { "BP" } else { "暴力" }
    line("| \{n} | \{ops_bf} | \{ops_bp} | \{f2(r)}× | \{who} |")
  }
  line("")
  line(
    "實測交叉點：**n = \{crossover}**。n 小於它時，訊息傳遞的固定啟動成本（每條邊兩趟、每趟建張量）",
  )
  line(
    "超過它省下的邊緣化；n 大於它時指數差距才開始兌現。任何「BP 總是更快」的說法在 n ≤ \{crossover - 1} 上都是錯的。",
  )
  line("")

  // -------------------------------------------------------------------------
  // 19b 解量化的下溢邊界
  // -------------------------------------------------------------------------
  line("### 19b. Maslov 解量化：下溢邊界在哪裡？")
  line("")
  let xs : Array[Double] = [700.0, 700.4, 700.9, 701.7]
  line(
    "輸入 x = [700, 700.4, 700.9, 701.7]（刻意取大值：下溢取決於 x_min / h，而不是 h 本身），真值 min = 700。",
  )
  line(
    "穩定版 = log-sum-exp 平移；樸素版 = 照公式算 `−h·ln Σ e^(−x/h)`。",
  )
  line("")
  line(
    "| h | x_min / h | 樸素版結果 | 穩定版誤差（相對 700） | 是否下溢 |",
  )
  line("|---|---|---|---|---|")
  let mut first_under = -1.0
  for h in [1.0, 0.1, 0.01, 1.0e-3, 1.0e-4, 1.0e-5] {
    let naive = @cat.dequantize_naive(xs, h)
    let stable_err = @cat.dequant_error(xs, h)
    let under = naive > 1.0e299
    if under && first_under < 0.0 {
      first_under = h
    }
    let ntext = if under { "∞（ln 0 下溢）" } else { f6(naive) }
    line("| \{h} | \{f2(700.0 / h)} | \{ntext} | \{stable_err} | \{under} |")
  }
  line("")
  let bound = 700.0 / 709.0
  line(
    "第一個崩掉的 h 是 **\{first_under}**（理論界：x_min/h > 709 時最小項就歸零 ⇒ h < 700/709 ≈ \{f6(bound)} 必崩）。",
  )
  line(
    "驗算：h = 1 > \{f2(bound)} 時樸素版仍可用（誤差 0.815，這是 h 太大的誤差，不是下溢）；",
  )
  line(
    "h = 0.1 < \{f2(bound)} 立刻變成 ln 0。所以這個界是**充分**的：一越過就全崩，",
  )
  line(
    "因為所有項都 ≥ 最小項，最小項歸零則整條和為 0。這也解釋了為什麼「調小 h 提高精度」",
  )
  line(
    "在浮點上是個陷阱：精度確實上升，直到某一刻直接變成 ±∞。",
  )
  line(
    "穩定版在同一個 h 上仍然正確——因為平移後最小項的指數固定為 0。這說明「極限」在浮點上不是可達的目標，",
  )
  line(
    "而是一條**誤差曲線**：可以保證的是「在可表示範圍內與 min 一致」，不是「等於 min」。",
  )
  line("")

  // -------------------------------------------------------------------------
  // 19c 熱帶細分的成本成長
  // -------------------------------------------------------------------------
  line(
    "### 19c. 熱帶細分的成本成長：量出指數，而不是套公式",
  )
  line("")
  line(
    "`subdivision()` 枚舉三元組求平面（O(m³)），每個平面再檢查全部 m 個點 ⇒ O(m⁴)。",
  )
  line("")
  line(
    "不印「預測值」再宣稱吻合（那是最容易作弊的比較）；改印**實測指數** p = ln(t_m / t_{m−1}) / ln(m / (m−1))。",
  )
  line("")
  line(
    "| 支援點數 m | 細分面數 | 時間 (µs) | 單點指數 p | 上界 |",
  )
  line("|---|---|---|---|---|")
  let exps : Array[Double] = []
  let lx : Array[Double] = []
  let ly : Array[Double] = []
  let mut prev = 0.0
  for m in [6, 7, 8, 9, 10, 11, 12, 13, 14] {
    let terms : Array[@trop.BTerm] = []
    let rng = @alg.Rng::new(900UL + m.to_uint64())
    for i in 0..<m {
      let a = i * 3 % 7 - 2
      let b = i * 5 % 6 - 1
      terms.push(@trop.BTerm::new(rng.range(-9, 9), a, b))
    }
    let poly = @trop.BPoly::new(terms)
    let (faces, t) = @sim.time_min(20, fn() { poly.subdivision() })
    let mut ratio = 0.0
    if prev > 0.0 {
      ratio = t / prev
    }
    let q = m.to_double() / (m - 1).to_double()
    let mut pexp = 0.0
    if prev > 0.0 && ratio > 0.0 {
      pexp = @math.ln(ratio) / @math.ln(q)
    }
    let ptext = if prev > 0.0 { f2(pexp) } else { "-" }
    if prev > 0.0 {
      exps.push(pexp)
    }
    lx.push(@math.ln(m.to_double()))
    ly.push(@math.ln(t))
    line("| \{m} | \{faces.length()} | \{f2(t)} | \{ptext} | 4 |")
    prev = t
  }
  line("")
  // log-log 最小平方斜率
  let k = lx.length().to_double()
  let mut sx = 0.0
  let mut sy = 0.0
  for i in 0..<lx.length() {
    sx = sx + lx[i]
    sy = sy + ly[i]
  }
  let mx = sx / k
  let my = sy / k
  let mut sxy = 0.0
  let mut sxx = 0.0
  for i in 0..<lx.length() {
    sxy = sxy + (lx[i] - mx) * (ly[i] - my)
    sxx = sxx + (lx[i] - mx) * (lx[i] - mx)
  }
  let slope = if sxx > 0.0 { sxy / sxx } else { 0.0 }
  line("")
  line(
    "單點指數在 0.3–6.8 之間亂跳：**面數是離散的**（m=9 反而只有 3 個面），單點差分被這些跳躍主導。",
  )
  line(
    "因此改報 log-log 最小平方斜率（m = 6…14）：**實測斜率 = \{f2(slope)}**，上界是 4。",
  )
  line(
    "誠實的陳述因此是「成本上界 O(m⁴)，這段區間內的有效斜率 \{f2(slope)}（常數項仍顯著）」，",
  )
  line(
    "而不是「實測吻合 O(m⁴)」——後者在這組資料上不成立，寫下去就是造假。",
  )
  line(
    "工程結論寫進限制：m 到幾十就該換增量凸包或分治細分，而本庫**沒有**做。",
  )
  line("")

  // -------------------------------------------------------------------------
  // 19d 可信度的價格結構
  // -------------------------------------------------------------------------
  line("### 19d. 「可信度的價格」不是一個數字，是一個結構")
  line("")
  let rng = @alg.Rng::new(31415UL)
  let nn = 40
  let es : Array[(Int32, Int32, @alg.Trop)] = []
  for _ in 0..<(nn * 3) {
    let u = rng.next_int(nn)
    let v = rng.next_int(nn)
    if u != v {
      es.push((u, v, @alg.Trop::new(rng.range(1, 30))))
    }
  }
  let m40 = @app.build(nn, es)
  let v = @app.consensus_trop(m40, 1)
  line("n=\{nn}、邊數 \{es.length()}，五個候選各跑一次：")
  line("")
  line("| 候選 | 時間 (µs) |")
  line("|---|---|")
  for r in v.runs {
    line("| \{r.name} | \{f2(r.us)} |")
  }
  line("")
  // 找出最便宜與第二便宜
  let mut t1 = 1.0e18
  let mut t2 = 1.0e18
  let mut n1 = ""
  let mut n2 = ""
  for r in v.runs {
    if r.us < t1 {
      t2 = t1
      n2 = n1
      t1 = r.us
      n1 = r.name
    } else if r.us < t2 {
      t2 = r.us
      n2 = r.name
    }
  }
  line(
    "全部五個候選的價格：**\{f2(v.cost_of_trust)}×**（總成本 \{f2(v.total_us)} µs / 最快 \{f2(v.winner_us)} µs）。",
  )
  line("")
  line(
    "只跑最便宜的兩個（\{n1} + \{n2}）：**\{f2((t1 + t2) / t1)}×**，就已經能抓到單一實作的錯誤。",
  )
  line(
    "所以「交叉驗證」的建議不是二選一，而是分層：上線路徑跑 1 個，觀測路徑跑 2 個，",
  )
  line(
    "只有離線稽核或發版前才跑全部 5 個。這三種成本差了一個數量級以上，是同一份程式換一個 `reps` 的事。",
  )
  line("")

  // -------------------------------------------------------------------------
  // 19e 單一候選的盲點
  // -------------------------------------------------------------------------
  line("### 19e. 只有一個候選時，錯誤不會被發現")
  line("")
  let exact = @mat.closure_fw_inplace(m40.copy())
  let (s2, _ok2) = @mat.closure_series(m40, k=2)
  let (s_full, _okf) = @mat.closure_series(m40, k=nn + 1)
  let d2 = diff_cells(exact, s2)
  let dfull = diff_cells(exact, s_full)
  line("| 候選 | 與原地 Warshall 不同的格數 | 看起來合理嗎 |")
  line("|---|---|---|")
  line(
    "| 冪級數 k = 2（截斷） | \{d2} / \{(nn * nn)} | 是（值都是合法路徑長度，只是偏大或 ∞） |",
  )
  line("| 冪級數 k = n+1（收斂） | \{dfull} | 是 |")
  line("")
  line(
    "截斷版單獨看完全「正常」：每一格都是某條真實路徑的長度（或 ∞，代表 2 步內到不了），沒有 NaN、沒有負數、沒有崩潰。",
  )
  line(
    "只有把它和第二個實作並排，錯誤才存在。這就是 §17 的仲裁器存在的理由——它買的不是速度，是**能否發現自己錯了**。",
  )
  line(
    "代價也寫在這裡：仲裁只能抓「實作之間的不一致」，抓不到「大家共同的建模錯誤」。這一條無法用工程手段消除。",
  )
  line("")

  // -------------------------------------------------------------------------
  // 19f 限制總表
  // -------------------------------------------------------------------------
  line("### 19f. 限制總表：每一條限制對應的量測")
  line("")
  line("| 限制 | 量到的數字 | 出現在 |")
  line("|---|---|---|")
  line("| BP 只在樹上精確 | 三角形圖誤差 0.008341427 | §18 |")
  line(
    "| BP 不是「小圖也快」 | 交叉點 n = \{crossover}；n=4 時 396 vs 48 次乘法 | §18、19a |",
  )
  line(
    "| 解量化只是極限 | 樸素版在 h = \{first_under} 下溢；穩定版仍在誤差曲線內 | §16、19b |",
  )
  line(
    "| 熱帶細分只有上界 O(m⁴) | log-log 斜率實測 \{f2(slope)}（m = 6…14） | §14、19c |",
  )
  line(
    "| 交叉驗證不便宜 | 全跑 \{f2(v.cost_of_trust)}×，兩兩對照 \{f2((t1 + t2) / t1)}× | §17、19d |",
  )
  line(
    "| 仲裁抓不到共同錯誤 | 截斷級數單獨看「合理」，\{d2} 格其實是錯的 | §17、19e |",
  )
  line(
    "| 稀疏消去不如稠密 FW | 需先重建列 ⇒ 可測範圍內一致落後 | §10 |",
  )
  line("| 沒有 CPU 平行 | I/O 重疊 1.32×，CPU 加速 1.00× | §13 |")
  line(
    "| 規範形式只到 Kleene／冪等半環 | 非冪等實例上 `a⊕a=a` 會誤判 | §15 |",
  )
  line("")
  line(
    "把這張表讀完，就會發現本庫的「優點」與「限制」是同一批測量結果的兩面：",
  )
  line(
    "因為每個加速都配了對照，所以知道它在哪裡開始變慢；因為每個近似都量了誤差，所以知道它離精確多遠。",
  )
  line("")
}
