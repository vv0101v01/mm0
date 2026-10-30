// ===========================================================================
// 限流器：全域閘門 + 每鍵 GCRA + 階層（租戶）
//
// 判定順序刻意設計成「由便宜到昂貴」：
//   1. 全域閘門（一個 Int64 比較，**在雜湊之前**）
//   2. 租戶（一次雜湊）
//   3. 鍵（一次雜湊）
// 多點齊發時，絕大多數請求在第 1 步就被丟掉，成本 ~1 個比較；
// 單點狂按時，第 3 步的 strikes 退避會讓後續請求快速被拒。
// ===========================================================================

///|
/// 單層限流器（可選全域閘門）。
pub(all) struct Limiter {
  key_gcra : Gcra
  gate : Gcra?
  table : KeyTable
  mut gate_tat : Int64
  mut last_now : Int64
  mut admitted : Int64
  mut throttled : Int64
  mut shedded : Int64
}

///|
/// 只有每鍵限流（沒有全域閘門）。
pub fn Limiter::new(
  rate_per_sec : Double,
  burst : Int32,
  capacity_pow2 : Int32,
) -> Limiter {
  {
    key_gcra: Gcra::new(rate_per_sec, burst),
    gate: None,
    table: KeyTable::new(capacity_pow2),
    gate_tat: 0L,
    last_now: 0L,
    admitted: 0L,
    throttled: 0L,
    shedded: 0L,
  }
}

///|
/// 加上全域閘門（多點齊發的第一道防線）。
pub fn Limiter::with_gate(
  rate_per_sec : Double,
  burst : Int32,
  global_rate : Double,
  global_burst : Int32,
  capacity_pow2 : Int32,
) -> Limiter {
  let base = Limiter::new(rate_per_sec, burst, capacity_pow2)
  {
    key_gcra: base.key_gcra,
    gate: Some(Gcra::new(global_rate, global_burst)),
    table: base.table,
    gate_tat: 0L,
    last_now: 0L,
    admitted: 0L,
    throttled: 0L,
    shedded: 0L,
  }
}

///|
/// 單調時鐘保護：時間倒退時夾住（雲端 NTP 調時、跨節點 clock skew 都會發生，
/// 若不夾住，TAT 會被推到未來而讓該鍵長期被誤鎖）。
fn Limiter::clamp_now(self : Limiter, now : Int64) -> Int64 {
  let t = if now > self.last_now { now } else { self.last_now }
  self.last_now = t
  t
}

///|
/// 單層判定。
pub fn Limiter::admit(self : Limiter, key : UInt64, now_us : Int64) -> Decision {
  let now = self.clamp_now(now_us)
  // 1) 全域閘門：在雜湊之前
  if self.gate is Some(g) {
    match g.preview(self.gate_tat, now, 0) {
      Throttled(_) => {
        self.shedded = self.shedded + 1L
        return Shedded
      }
      _ => ()
    }
  }
  // 2) 每鍵
  let idx = self.table.get_or_insert(key, now)
  let st = self.table.slots[idx]
  match self.key_gcra.preview(st.tat, now, st.strikes) {
    Throttled(r) => {
      st.strikes = st.strikes + 1
      self.throttled = self.throttled + 1L
      return Throttled(r)
    }
    _ => ()
  }
  // 3) 全部通過 → commit
  st.tat = self.key_gcra.commit(st.tat, now)
  st.strikes = 0
  if self.gate is Some(g) {
    self.gate_tat = g.commit(self.gate_tat, now)
  }
  self.admitted = self.admitted + 1L
  Allowed
}

///|
/// 階層式限流：全域 → 租戶 → 鍵。
///
/// preview/commit 兩段式的價值在這裡：三個層級都先 preview，
/// 全部通過才一起 commit ⇒ 不會有「租戶額度被下層拒絕的請求吃掉」。
pub(all) struct HierLimiter {
  gate : Gcra?
  tenant_gcra : Gcra
  key_gcra : Gcra
  tenants : KeyTable
  keys : KeyTable
  mut gate_tat : Int64
  mut last_now : Int64
  mut admitted : Int64
  mut throttled : Int64
  mut shedded : Int64
}

///|
pub fn HierLimiter::new(
  tenant_rate : Double,
  tenant_burst : Int32,
  key_rate : Double,
  key_burst : Int32,
  capacity_pow2 : Int32,
  global_rate? : Double,
  global_burst? : Int32,
) -> HierLimiter {
  let gate = match (global_rate, global_burst) {
    (Some(r), Some(b)) => Some(Gcra::new(r, b))
    _ => None
  }
  {
    gate,
    tenant_gcra: Gcra::new(tenant_rate, tenant_burst),
    key_gcra: Gcra::new(key_rate, key_burst),
    tenants: KeyTable::new(capacity_pow2),
    keys: KeyTable::new(capacity_pow2),
    gate_tat: 0L,
    last_now: 0L,
    admitted: 0L,
    throttled: 0L,
    shedded: 0L,
  }
}

///|
/// 階層判定。
pub fn HierLimiter::admit(
  self : HierLimiter,
  tenant : UInt64,
  key : UInt64,
  now_us : Int64,
) -> Decision {
  let now = if now_us > self.last_now { now_us } else { self.last_now }
  self.last_now = now
  // preview 全域
  if self.gate is Some(g) {
    match g.preview(self.gate_tat, now, 0) {
      Throttled(_) => {
        self.shedded = self.shedded + 1L
        return Shedded
      }
      _ => ()
    }
  }
  let ti = self.tenants.get_or_insert(tenant, now)
  let ts = self.tenants.slots[ti]
  match self.tenant_gcra.preview(ts.tat, now, ts.strikes) {
    Throttled(r) => {
      ts.strikes = ts.strikes + 1
      self.throttled = self.throttled + 1L
      return Throttled(r)
    }
    _ => ()
  }
  let ki = self.keys.get_or_insert(key, now)
  let ks = self.keys.slots[ki]
  match self.key_gcra.preview(ks.tat, now, ks.strikes) {
    Throttled(r) => {
      ks.strikes = ks.strikes + 1
      self.throttled = self.throttled + 1L
      return Throttled(r)
    }
    _ => ()
  }
  // commit（三層一起）
  ts.tat = self.tenant_gcra.commit(ts.tat, now)
  ts.strikes = 0
  ks.tat = self.key_gcra.commit(ks.tat, now)
  ks.strikes = 0
  if self.gate is Some(g) {
    self.gate_tat = g.commit(self.gate_tat, now)
  }
  self.admitted = self.admitted + 1L
  Allowed
}

///|
/// 讓 `Decision` 的統計可被外部讀取（用於報表）。
pub fn Limiter::stats(self : Limiter) -> (Int64, Int64, Int64) {
  (self.admitted, self.throttled, self.shedded)
}

///|
pub fn HierLimiter::stats(self : HierLimiter) -> (Int64, Int64, Int64) {
  (self.admitted, self.throttled, self.shedded)
}

///|
/// 鍵表佔用（記憶體上界檢查用）。
pub fn Limiter::table_used(self : Limiter) -> Int32 {
  self.table.used
}

///|
pub fn Limiter::table_evictions(self : Limiter) -> Int64 {
  self.table.evictions
}

///|
pub fn HierLimiter::table_used(self : HierLimiter) -> (Int32, Int32) {
  (self.tenants.used, self.keys.used)
}

///|
pub fn HierLimiter::table_evictions(self : HierLimiter) -> (Int64, Int64) {
  (self.tenants.evictions, self.keys.evictions)
}
