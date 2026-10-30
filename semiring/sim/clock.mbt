// ===========================================================================
// 計時器（單調時鐘，microseconds）
//
// 所有量測都取「重複 k 次的最小值」，因為最小值最接近「無干擾時」的真實
// 成本，且對作業系統排程抖動不敏感（平均值會被其他行程污染）。
// ===========================================================================

///|
using @bench {monotonic_clock_start, monotonic_clock_end}

///|
/// 單調時鐘起點。
pub struct Timer {
  t0 : @bench.Timestamp
}

///|
pub fn Timer::start() -> Timer {
  { t0: monotonic_clock_start(), }
}

///|
/// 經過的微秒數。
pub fn Timer::elapsed_us(self : Timer) -> Double {
  monotonic_clock_end(self.t0)
}

///|
/// 量測 `f` 的執行時間（微秒），重複 `reps` 次取最小值。
pub fn[T] time_min(reps : Int32, f : () -> T) -> (T, Double) {
  let mut best = 1.0e18
  let mut out = f()
  for _ in 0..<reps {
    let t = Timer::start()
    out = f()
    let e = t.elapsed_us()
    if e < best {
      best = e
    }
  }
  (out, best)
}
