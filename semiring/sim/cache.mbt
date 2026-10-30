// ===========================================================================
// 兩層快取模擬器（set-associative LRU）
//
// 用途：把演算法**實際發出**的元素存取序列（由 Probe 回呼產生）換算成
// L1 / L2 / DRAM 的存取次數。這使得「降低記憶體讀寫次數」變成可量測的
// 數字，而不是口號；也讓「分塊」是否真的有用可以被否證。
//
// 這是純函式模擬（沒有 OS、沒有計時器），因此結果完全可重現。
// ===========================================================================

///|
/// 單層 set-associative LRU 快取。
pub struct Cache {
  sets : Int32
  ways : Int32
  shift : Int32
  tags : Array[Int32]
  stamp : Array[Int32]
  mut clock : Int32
  mut hits : Int64
  mut misses : Int64
  ///
  /// 每個 cache line 的位元組數（用於計算 traffic）。
  line_bytes : Int32
}

///|
/// 建立容量為 sets×ways、line 為 line_bytes 的快取。
pub fn Cache::new(sets : Int32, ways : Int32, line_bytes : Int32) -> Cache {
  let mut shift = 0
  let mut sz = 1
  while sz < line_bytes {
    sz = sz * 2
    shift = shift + 1
  }
  {
    sets,
    ways,
    shift,
    tags: Array::make(sets * ways, -1),
    stamp: Array::make(sets * ways, 0),
    clock: 0,
    hits: 0L,
    misses: 0L,
    line_bytes,
  }
}

///|
/// 存取一個位元組位址；回傳是否命中。
pub fn Cache::access(self : Cache, addr : Int32, write : Bool) -> Bool {
  self.clock = self.clock + 1
  let line = addr >> self.shift
  let set = line % self.sets
  let tag = line / self.sets
  let base = set * self.ways
  let mut victim = base
  let mut oldest = 0x7FFF_FFFF
  for w in 0..<self.ways {
    if self.tags[base + w] == tag {
      self.stamp[base + w] = self.clock
      self.hits = self.hits + 1L
      return true
    }
    if self.stamp[base + w] < oldest {
      oldest = self.stamp[base + w]
      victim = base + w
    }
  }
  // miss：逐出 LRU
  self.tags[victim] = tag
  self.stamp[victim] = self.clock
  self.misses = self.misses + 1L
  let _ = write
  false
}

///|
pub fn Cache::accesses(self : Cache) -> Int64 {
  self.hits + self.misses
}

///|
pub fn Cache::reset(self : Cache) -> Unit {
  for i in 0..<self.tags.length() {
    self.tags[i] = -1
    self.stamp[i] = 0
  }
  self.clock = 0
  self.hits = 0L
  self.misses = 0L
}

///|
/// 兩層階層：L1 miss 才打 L2，L2 miss 才打 DRAM。
///
/// 「記憶體讀寫次數」以 DRAM 交易數（= L2 miss × line_bytes / 8）表示。
pub struct MemHierarchy {
  l1 : Cache
  l2 : Cache
  mut dram_reads : Int64
  mut dram_writes : Int64
}

///|
/// 典型桌上型參數：L1 32 KiB / 8-way / 64 B，L2 512 KiB / 8-way / 64 B。
pub fn MemHierarchy::typical() -> MemHierarchy {
  {
    l1: Cache::new(64, 8, 64),
    l2: Cache::new(1024, 8, 64),
    dram_reads: 0L,
    dram_writes: 0L,
  }
}

///|
/// 存取：位址是「矩陣基底 + 元素索引 × 元素大小」。
pub fn MemHierarchy::access(
  self : MemHierarchy,
  addr : Int32,
  write : Bool,
) -> Unit {
  if self.l1.access(addr, write) {
    return
  }
  if self.l2.access(addr, write) {
    return
  }
  if write {
    self.dram_writes = self.dram_writes + 1L
  } else {
    self.dram_reads = self.dram_reads + 1L
  }
}

///|
pub fn MemHierarchy::reset(self : MemHierarchy) -> Unit {
  self.l1.reset()
  self.l2.reset()
  self.dram_reads = 0L
  self.dram_writes = 0L
}

///|
/// DRAM 交易總數（以 8 bytes 為一個 word 計算的 word 傳輸量）。
pub fn MemHierarchy::dram_words(self : MemHierarchy) -> Int64 {
  (self.dram_reads + self.dram_writes) * (self.l1.line_bytes / 8).to_int64()
}

///|
/// 追蹤器：把演算法的 (矩陣ID, row, col, is_write) 回呼映射成位址。
///
/// 每個矩陣註冊時取得一段互不重疊的虛擬位址空間，因此 A/B/C 不會
/// 在模擬器裡互相「假命中」。
pub struct Tracer {
  sim : MemHierarchy
  base : Array[Int32]
  cols : Array[Int32]
  elem_bytes : Int32
  mut next_base : Int32
}

///|
pub fn Tracer::new(elem_bytes : Int32) -> Tracer {
  {
    sim: MemHierarchy::typical(),
    base: [],
    cols: [],
    elem_bytes,
    next_base: 0,
  }
}

///|
/// 註冊一個矩陣，回傳其 ID。
pub fn Tracer::register(self : Tracer, rows : Int32, cols : Int32) -> Int32 {
  let id = self.base.length()
  self.base.push(self.next_base)
  self.cols.push(cols)
  self.next_base = self.next_base + rows * cols * self.elem_bytes + 4096
  id
}

///|
/// 取得可直接傳給演算法的 probe。
pub fn Tracer::probe(self : Tracer) -> (Int32, Int32, Int32, Bool) -> Unit {
  fn(mid : Int32, i : Int32, j : Int32, w : Bool) {
    if mid >= self.base.length() {
      return
    }
    let addr = self.base[mid] + (i * self.cols[mid] + j) * self.elem_bytes
    self.sim.access(addr, w)
  }
}

///|
pub fn Tracer::reset(self : Tracer) -> Unit {
  self.sim.reset()
}

///|
pub fn Tracer::l1_misses(self : Tracer) -> Int64 {
  self.sim.l1.misses
}

///|
pub fn Tracer::l2_misses(self : Tracer) -> Int64 {
  self.sim.l2.misses
}

///|
pub fn Tracer::l1_accesses(self : Tracer) -> Int64 {
  self.sim.l1.accesses()
}

///|
pub fn Tracer::dram_words(self : Tracer) -> Int64 {
  self.sim.dram_words()
}
