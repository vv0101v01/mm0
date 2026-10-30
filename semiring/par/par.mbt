// ===========================================================================
// 平行執行後端：介面與確定性演算法
//
// 這一層把「平行」與「後端」分開：
//   * `par_for(chunks, f)` 是**唯一**與後端相關的primitive。
//     native 上由 `moonbitlang/async` 的結構化併發（task group）驅動；
//     其他 target 上退化成序列迴圈。
//   * 所有高階演算法（分塊 map、確定性歸約、對數深度掃描）都只依賴
//     `par_for`，因此換後端不需要改任何演算法。
//
// **關於「平行」的誠實說明**（量測見報告 §13）：
// MoonBit 0.10.17 的 `moonbitlang/async` 是**單執行緒協作式**執行環境，
// 使用者程式碼只會用到一個 CPU 核心（官方 README 明載，官方部落格亦同）。
// 因此本層對「CPU 密集」的工作不會帶來加速（實測 1.0–1.1×）；
// 它真正的收益在**重疊 I/O**（實測 7×）與**結構化的生命週期/取消**。
// 程式碼的平行結構（列區塊互不相交、歸約順序固定）是為將來真正的
// 執行緒後端準備的：只要把 `par_for` 換掉即可，演算法與結果都不變。
// ===========================================================================

///|
/// 後端名稱（用於報告與測試，確保我們知道自己跑在哪個後端上）。
pub fn backend() -> String {
  backend_name()
}

///|
/// 把 `total` 切成 `chunks` 段後，每一段的長度（最後一段吃掉餘數）。
pub fn chunk_size(total : Int32, chunks : Int32) -> Int32 {
  if chunks <= 0 {
    total
  } else if total <= 0 {
    0
  } else {
    let c = (total + chunks - 1) / chunks
    if c < 1 {
      1
    } else {
      c
    }
  }
}

///|
/// 分段 map：對 `[0, total)` 的每一段呼叫 `body(start, end)`。
///
/// 每一段寫入的目標必須互不相交（呼叫端責任），這樣換成任何後端
/// 都不需要鎖；`mul_rows_par` 與 `closure_fw_par` 都遵守這一點。
pub fn par_map_chunks(
  total : Int32,
  chunks : Int32,
  body : (Int32, Int32) -> Unit,
) -> Unit {
  let c = chunk_size(total, chunks)
  if c == 0 {
    return
  }
  let n_chunk = (total + c - 1) / c
  par_for(n_chunk, fn(k) {
    let lo = k * c
    let hi = if lo + c > total { total } else { lo + c }
    body(lo, hi)
  })
}

///|
/// 確定性歸約：每段各自算出 Int64，最後**依索引順序**相加。
///
/// 順序固定的理由：浮點或非結合運算的結果會依歸約順序改變；
/// 固定順序讓「平行」不會改變任何一個位元（測試逐位元比對）。
pub fn par_sum(total : Int32, chunk : Int32, f : (Int32) -> Int64) -> Int64 {
  if total <= 0 {
    return 0L
  }
  let n_chunk = (total + chunk - 1) / chunk
  let parts : Array[Int64] = Array::make(n_chunk, 0L)
  par_for(n_chunk, fn(k) {
    let lo = k * chunk
    let hi = if lo + chunk > total { total } else { lo + chunk }
    let mut s = 0L
    for i in lo..<hi {
      s = s + f(i)
    }
    parts[k] = s
  })
  let mut acc = 0L
  for p in parts {
    acc = acc + p
  }
  acc
}

///|
/// Hillis–Steele 掃描：深度 O(log n)，每一層的更新彼此獨立（可平行）。
///
/// 與序列累加的差別是**深度**而非工作量：工作量 O(n log n) > O(n)，
/// 但深度只剩 log n。這是為真正多核後端準備的結構。
pub fn par_scan(values : Array[Int64]) -> Array[Int64] {
  let n = values.length()
  let out = values.copy()
  let mut distance = 1
  while distance < n {
    let snap = out.copy()
    par_map_chunks(n, if n > 4096 { 16 } else { 1 }, fn(lo, hi) {
      for i in lo..<hi {
        if i >= distance {
          out[i] = snap[i] + snap[i - distance]
        }
      }
    })
    distance = distance * 2
  }
  out
}

///|
/// 掃描需要多少層（Hillis–Steele 的深度）。
pub fn scan_depth(n : Int32) -> Int32 {
  let mut d = 0
  let mut w = 1
  while w < n {
    w = w * 2
    d = d + 1
  }
  d
}

///|
/// 序列版本的掃描（對照組）。
pub fn scan_sequential(values : Array[Int64]) -> Array[Int64] {
  let out : Array[Int64] = []
  let mut acc = 0L
  for v in values {
    acc = acc + v
    out.push(acc)
  }
  out
}
