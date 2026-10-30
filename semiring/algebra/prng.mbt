// ===========================================================================
// 可重現的偽隨機數（SplitMix64）
//
// 所有測試、基準與壓力測試都使用固定的種子與本 PRNG，
// 因此任何一次執行（包含 CI 與不同 target）都會得到相同的資料與結論。
// ===========================================================================

///|
/// SplitMix64 狀態機。週期 2^64，無配置、單一 UInt64 狀態。
pub struct Rng {
  mut state : UInt64
}

///|
pub fn Rng::new(seed : UInt64) -> Rng {
  { state: seed, }
}

///|
pub fn Rng::next_u64(self : Rng) -> UInt64 {
  self.state = self.state + 0x9E37_79B9_7F4A_7C15UL
  let mut z = self.state
  z = (z ^ (z >> 30)) * 0xBF58_476D_1CE4_E5B9UL
  z = (z ^ (z >> 27)) * 0x94D0_49BB_1331_11EBUL
  z ^ (z >> 31)
}

///|
/// [0, bound) 的均勻整數（bound ≤ 0 時回傳 0）。
pub fn Rng::next_int(self : Rng, bound : Int32) -> Int32 {
  if bound <= 0 {
    return 0
  }
  let u = self.next_u64() >> 33
  u.to_int() % bound
}

///|
/// [lo, hi] 的均勻整數。
pub fn Rng::range(self : Rng, lo : Int32, hi : Int32) -> Int32 {
  lo + self.next_int(hi - lo + 1)
}

///|
/// [0, 1) 的均勻 Double。
pub fn Rng::next_double(self : Rng) -> Double {
  let u = self.next_u64() >> 11
  u.to_double() / 9007199254740992.0
}

///|
/// 以機率 p 回傳 true。
pub fn Rng::chance(self : Rng, p : Double) -> Bool {
  self.next_double() < p
}
