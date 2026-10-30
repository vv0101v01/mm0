// ===========================================================================
// 演算法組合：不互斥地同時執行 + 一致性仲裁（「連帶相信」）
//
// 傳統的演算法選擇是**互斥**的：挑一個、相信它。這裡改成組合：
//
//   1. 對同一個問題跑 k 個**互相獨立**的實作（不同演算法、不同資料結構）；
//   2. 逐格比對結果；任何一格不同就整體標記為「不一致」；
//   3. 只有在全部一致時才「相信」這個答案（N-version programming 的精神）；
//   4. 同時記錄每個成員的耗時與總成本。
//
// 這樣做的代價是**時間**：總成本 = Σ 成員成本 ≥ 最快成員成本。
// 本庫不打算把這件事說成「更快」——它買的是**可信度**，不是速度。
// 報告 §16 會把兩個數字都印出來（`cost_of_trust` = 總成本 / 最快成員）。
//
// 關鍵設計：仲裁必須能**拒絕**答案。所以 `consensus_trop` 允許注入
// 「故意錯的候選」，測試與報告都會示範它被抓出來——
// 一個永遠說「一致」的仲裁器等於沒有仲裁器。
// ===========================================================================

///|
/// 一個候選演算法的執行結果。
pub(all) struct Run {
  name : String
  us : Double
  /// 是否與仲裁基準逐格相同
  agrees : Bool
}

///|
/// 仲裁結果。
pub(all) struct Verdict {
  runs : Array[Run]
  /// 全部成員都與第一個成員相同
  agree : Bool
  winner : String
  winner_us : Double
  total_us : Double
  /// 總成本 / 最快成員成本（「可信度的價格」）
  cost_of_trust : Double
}

///|
fn trop_matrix_equal(a : @mat.Mat[@alg.Trop], b : @mat.Mat[@alg.Trop]) -> Bool {
  if a.rows != b.rows || a.cols != b.cols {
    return false
  }
  for i in 0..<(a.rows * a.cols) {
    if a.d[i] != b.d[i] {
      return false
    }
  }
  true
}

///|
/// 熱帶（min-plus）閉包的一致性仲裁。
///
/// 五個候選：原地 Warshall、Lehmann 消去、分塊遞迴、冪級數、稀疏 CSR 逐源 SSSP。
/// 它們的資料結構、迴圈順序、複雜度都不同，同時錯成同一個樣子的機率極低。
///
/// `inject_wrong`：額外加入一個**故意錯的**候選（把非冪等的原地更新用在
/// Counting 上再轉回來），用來證明仲裁器真的會拒絕。
pub fn consensus_trop(
  edges : @mat.Mat[@alg.Trop],
  reps : Int32,
  inject_wrong~ : Bool = false,
) -> Verdict {
  let n = edges.rows
  let names : Array[String] = []
  let times : Array[Double] = []
  let mats : Array[@mat.Mat[@alg.Trop]] = []
  // 1. 原地 Warshall
  {
    let (m, t) = @sim.time_min(reps, fn() {
      @mat.closure_fw_inplace(edges.copy())
    })
    names.push("warshall-inplace")
    times.push(t)
    mats.push(m)
  }
  // 2. Lehmann 消去
  {
    let (m, t) = @sim.time_min(reps, fn() { @mat.closure_lehmann(edges) })
    names.push("lehmann")
    times.push(t)
    mats.push(m)
  }
  // 3. 分塊遞迴
  {
    let (m, t) = @sim.time_min(reps, fn() {
      @mat.closure_blocked(edges, threshold=32)
    })
    names.push("blocked-32")
    times.push(t)
    mats.push(m)
  }
  // 4. 冪級數
  {
    let (r, t) = @sim.time_min(reps, fn() {
      @mat.closure_series(edges, k=n + 1)
    })
    names.push("series")
    times.push(t)
    mats.push(r.0)
  }
  // 5. 稀疏 CSR + n 次 SSSP
  {
    let csr = @mat.Csr::from_dense(edges)
    let (rows, t) = @sim.time_min(reps, fn() { @mat.csr_apsp(csr) })
    let m = @mat.Mat::zero(n, n)
    for i in 0..<n {
      for j in 0..<n {
        m.set(i, j, rows[i][j])
      }
    }
    names.push("csr-apsp")
    times.push(t)
    mats.push(m)
  }
  // （可選）故意錯的候選
  if inject_wrong {
    let bad = wrong_candidate(edges)
    names.push("WRONG(negative control)")
    times.push(0.0)
    mats.push(bad)
  }
  // 仲裁：全部與第一個比
  let runs : Array[Run] = []
  let mut all_ok = true
  for i in 0..<mats.length() {
    let ok = trop_matrix_equal(mats[0], mats[i])
    if !ok {
      all_ok = false
    }
    runs.push({ name: names[i], us: times[i], agrees: ok, })
  }
  // 最快（且正確）的成員
  let mut winner = names[0]
  let mut winner_us = times[0]
  let mut total = 0.0
  for i in 0..<times.length() {
    total = total + times[i]
    if runs[i].agrees && times[i] < winner_us {
      winner_us = times[i]
      winner = names[i]
    }
  }
  let cost = if winner_us > 0.0 { total / winner_us } else { 0.0 }
  {
    runs,
    agree: all_ok,
    winner,
    winner_us,
    total_us: total,
    cost_of_trust: cost,
  }
}

///|
/// 負面對照：只截斷到 `I ⊕ A ⊕ A²`（路徑長度 ≤ 2）。
///
/// 這是一個「看起來很合理、實際上錯」的候選：在路徑長度 ≤ 2 的圖上它完全正確，
/// 但只要有一條最短路徑經過 3 個以上的邊，它就會給出偏大的值。
/// 仲裁器必須把它抓出來——否則整個一致性機制就是恆真測試。
pub fn wrong_candidate(edges : @mat.Mat[@alg.Trop]) -> @mat.Mat[@alg.Trop] {
  let r = @mat.closure_series(edges, k=2)
  r.0
}
