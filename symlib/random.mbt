///|
/// # Random — 確定性偽隨機實例產生器（測試 / 基準 / 演示共用）
///
/// 以 LCG（Numerical Recipes 常數：a=1103515245, c=12345, mod 2³¹）驅動，
/// **同一 seed ⇒ 同一實例**，故測試與基準可重現、可回歸比對。
///
/// 去債紀錄：原本 `symlib_test.mbt`、`cmd/bench/derived.mbt`、`cmd/main/main.mbt`
/// 各自實作一份 LCG + Fisher–Yates + G(n,p)（共 5 份、約 60 行重複程式碼），
/// 現統一為此二個公開建構子；測試端只保留種子選擇。

///|
/// 一步 LCG（回傳 [0, 2³¹) 之偽隨機整數）。
pub fn lcg_step(seed : Int32) -> Int32 {
  ((seed.to_int64() * 1103515245L + 12345L) & 0x7FFFFFFFL).to_int()
}

///|
/// 偽隨機圖 G(n, prob%)：逐對 (u,v) 以 LCG 抽邊。回傳 (圖, 新種子) 以便串接。
pub fn Graph::random(n : Int32, prob : Int32, seed : Int32) -> (Graph, Int32) {
  guard n >= 0 else { abort("Graph::random: negative n") }
  let mut s = seed
  let edges : Array[(Int32, Int32)] = []
  for u in 0..<n {
    for v in (u + 1)..<n {
      s = lcg_step(s)
      if s % 100 < prob {
        edges.push((u, v))
      }
    }
  }
  (Graph::from_edges(n, edges), s)
}

///|
/// 偽隨機置換（Fisher–Yates，均勻）。回傳 (置換, 新種子)。
pub fn Perm::random(n : Int32, seed : Int32) -> (Perm, Int32) {
  guard n >= 0 else { abort("Perm::random: negative n") }
  let mut s = seed
  let arr = Array::make(n, 0)
  for i in 0..<n {
    arr[i] = i
  }
  for i in 1..<n {
    s = lcg_step(s)
    let j = s % (i + 1)
    let t = arr[i]
    arr[i] = arr[j]
    arr[j] = t
  }
  (Perm::from_img(arr), s)
}

///|
/// 偽隨機序列（值域 [0, k)）：用於 CSP / 標號 / 顏色之隨機實例。
pub fn random_ints(
  len : Int32,
  k : Int32,
  seed : Int32,
) -> (Array[Int32], Int32) {
  guard k > 0 else { abort("random_ints: k must be positive") }
  let mut s = seed
  let out = Array::make(len, 0)
  for i in 0..<len {
    s = lcg_step(s)
    out[i] = s % k
  }
  (out, s)
}
