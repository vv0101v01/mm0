// ===========================================================================
// 限流：GCRA（Generic Cell Rate Algorithm）+ 有界鍵表 + 階層式組合
//
// 為什麼是 GCRA 而不是 token bucket：
//   * token bucket 需要「補充」計算，時間戳一旦漂移就會多放或少放；
//     GCRA 只維護一個「理論到達時間 TAT」，判斷式是純比較 ⇒ O(1)、
//     無漂移、無背景計時器。
//   * GCRA 的狀態是 Int64 微秒時間戳，記憶體 8 bytes/鍵。
//
// 兩個攻擊面：
//   多點齊發（many keys, one tick）  → 全域閘門 (global gate) 先擋，
//                                      且在**雜湊之前**就拒絕 ⇒ 便宜。
//   單點狂按（one key, many ticks）  → 每鍵 GCRA + 連續被拒的指數退避，
//                                      並且鍵表有容量上限（防記憶體 DoS）。
//
// 關鍵設計：preview / commit 兩段式。
//   階層式限流（全域 → 租戶 → 鍵）必須「全部通過才扣額度」，
//   否則先扣的那一層會被子請求耗盡（phantom consumption）。
//   這裡讓 preview 只讀狀態、commit 才寫狀態 ⇒ 不需要 rollback。
// ===========================================================================

///|
/// 一次限流判定。
pub(all) enum Decision {
  Allowed
  ///
  /// 被限流；`retry_after_us` 為建議重試延遲。
  Throttled(Int64)
  ///
  /// 被全域閘門在雜湊前直接丟棄（多點齊發防禦的快速路徑）。
  Shedded
} derive(Eq)

///|
pub impl Show for Decision with fn output(self, logger) {
  match self {
    Allowed => logger.write_string("Allowed")
    Throttled(r) => logger.write_string("Throttled(retry_after_us=\{r})")
    Shedded => logger.write_string("Shedded")
  }
}

///|
pub extend Decision with Eq::{equal, not_equal}

///|
pub extend Decision with Show::{output, to_string}

///|
/// GCRA 參數。
///
/// `interval_us` = 1/rate（每個請求的排放間隔）；
/// `burst` = 允許的突發量；容忍度 τ = (burst − 1) · interval。
pub(all) struct Gcra {
  interval_us : Int64
  burst : Int32
}

///|
/// 以「每秒 rate 個、突發 burst 個」建立。
pub fn Gcra::new(rate_per_sec : Double, burst : Int32) -> Gcra {
  let iv = if rate_per_sec <= 0.0 {
    1000000L
  } else {
    (1000000.0 / rate_per_sec).to_int64().max(1L)
  }
  { interval_us: iv, burst: burst.max(1), }
}

///|
/// 容忍度 τ。
pub fn Gcra::tolerance(self : Gcra) -> Int64 {
  (self.burst - 1).to_int64() * self.interval_us
}

///|
/// 對「目前 TAT」做一次不改變狀態的判定。
///
/// `strikes` 為連續被拒次數：≥2 起開始指數退避（每次最多 ×64），
/// 讓「單點狂按」的請求在越後面越便宜地被丟掉。
pub fn Gcra::preview(
  self : Gcra,
  tat : Int64,
  now : Int64,
  strikes : Int32,
) -> Decision {
  let tau = self.tolerance()
  let backoff = self.backoff(strikes)
  let allowed_at = tat - tau + backoff
  if now >= allowed_at {
    Allowed
  } else {
    Throttled(allowed_at - now)
  }
}

///|
/// 退避量：0 for strikes ≤ 1，之後 1×interval 起指數成長，上限 64×。
pub fn Gcra::backoff(self : Gcra, strikes : Int32) -> Int64 {
  if strikes <= 1 {
    return 0L
  }
  let shift = (strikes - 1).min(6)
  self.interval_us * (1L << shift)
}

///|
/// 通過後的新 TAT：`max(now, tat) + interval`。
pub fn Gcra::commit(self : Gcra, tat : Int64, now : Int64) -> Int64 {
  let base = if now > tat { now } else { tat }
  base + self.interval_us
}

// ---------------------------------------------------------------------------
// 有界鍵表（開放定址 + CLOCK 近似 LRU）
// ---------------------------------------------------------------------------

///|
/// 單一鍵的狀態（32 bytes，緊湊佈局）。
pub(all) struct KeyState {
  mut key : UInt64
  mut tat : Int64
  mut strikes : Int32
  mut referenced : Bool
  mut occupied : Bool
}

///|
/// 有界鍵表：容量固定、每次請求 O(1) 攤還、**永不成長**。
///
/// 這是防禦「用無限多個不同 key 打爆記憶體」的核心：
/// 容量滿時以 CLOCK 演算法逐出（近似 LRU，不需要排序或額外結構）。
pub(all) struct KeyTable {
  slots : FixedArray[KeyState]
  mask : Int32
  mut used : Int32
  mut hand : Int32
  mut evictions : Int64
  mut probes : Int64
}

///|
/// `capacity_pow2` 必須是 2 的冪（呼叫端保證，內部再檢查一次）。
pub fn KeyTable::new(capacity_pow2 : Int32) -> KeyTable {
  let mut cap = 1
  while cap < capacity_pow2 {
    cap = cap * 2
  }
  {
    slots: FixedArray::makei(cap, fn(_i) {
      { key: 0UL, tat: 0L, strikes: 0, referenced: false, occupied: false, }
    }),
    mask: cap - 1,
    used: 0,
    hand: 0,
    evictions: 0L,
    probes: 0L,
  }
}

///|
/// 32-bit 混洗雜湊（乘法 + xor-shift），單一乘法即可。
fn hash64(k : UInt64) -> UInt64 {
  let mut x = k
  x = (x ^ (x >> 33)) * 0xFF51AFD7ED558CCDUL
  x = (x ^ (x >> 33)) * 0xC4CEB9FE1A85EC53UL
  x ^ (x >> 33)
}

///|
/// 找到 key 所在的槽；不存在時回傳 (false, 可插入的槽)。
fn KeyTable::locate(self : KeyTable, key : UInt64) -> (Bool, Int32) {
  let h = hash64(key).to_int()
  let mut idx = h & self.mask
  let mut probes = 0
  while probes <= self.mask {
    self.probes = self.probes + 1L
    let s = self.slots[idx]
    if !s.occupied {
      return (false, idx)
    }
    if s.key == key {
      return (true, idx)
    }
    idx = (idx + 1) & self.mask
    probes = probes + 1
  }
  (false, -1)
}

///|
/// 取得（或建立）鍵的槽；必要時逐出 CLOCK 犧牲者。
pub fn KeyTable::get_or_insert(
  self : KeyTable,
  key : UInt64,
  now : Int64,
) -> Int32 {
  let (found, idx) = self.locate(key)
  if found {
    let s = self.slots[idx]
    s.referenced = true
    return idx
  }
  let mut slot = idx
  if slot < 0 {
    slot = self.evict(now)
  }
  let s = self.slots[slot]
  s.key = key
  s.tat = now
  s.strikes = 0
  s.referenced = true
  s.occupied = true
  self.used = self.used + 1
  slot
}

///|
/// CLOCK 逐出：最多掃兩輪，回傳被清空的槽。
fn KeyTable::evict(self : KeyTable, now : Int64) -> Int32 {
  let cap = self.slots.length()
  for _ in 0..<(2 * cap) {
    let s = self.slots[self.hand]
    self.hand = (self.hand + 1) & self.mask
    if !s.occupied {
      return (self.hand - 1 + cap) & self.mask
    }
    if s.referenced {
      s.referenced = false
    } else {
      s.occupied = false
      self.used = self.used - 1
      self.evictions = self.evictions + 1L
      return (self.hand - 1 + cap) & self.mask
    }
  }
  // 全部都被引用：直接犧牲手上的那格（CLOCK 的最壞情形，仍然 O(1) 攤還）
  let victim = self.hand
  let s = self.slots[victim]
  s.occupied = false
  self.used = self.used - 1
  self.evictions = self.evictions + 1L
  self.hand = (self.hand + 1) & self.mask
  let _ = now
  victim
}

///|
pub fn KeyTable::capacity(self : KeyTable) -> Int32 {
  self.slots.length()
}
