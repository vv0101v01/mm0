///|
/// # BitVec — 位向量
///
/// 64-bit 字組構成的定長位向量。用於圖的鄰接行、頂點子集、軌道代表集等。
/// 所有集合運算（交/併/差/計數）以字組並行，複雜度 O(n/64)。
/// 屬於最底層，供 perm / graph / group / search 等模組共用（同一作用域）。

///|
/// 定長位向量。`n` 為位元數，`words[i]` 儲存第 i 個 64 位字組。
pub(all) struct BitVec {
  n : Int32
  mut words : Array[Int64]
}

///|
/// 建立長度 `n` 的全零位向量。
pub fn BitVec::make(n : Int32) -> BitVec {
  guard n >= 0 else { abort("BitVec::make: negative length") }
  let w = (n + 63) / 64
  { n, words: Array::make(w, 0L), }
}

///|
/// 建立長度 `n` 的全一位向量（超出 n 的高位自動清零）。
pub fn BitVec::make_full(n : Int32) -> BitVec {
  let bv = BitVec::make(n)
  for i in 0..<n {
    bv.set(i)
  }
  bv
}

///|
/// 複製。
pub fn BitVec::copy(self : BitVec) -> BitVec {
  { n: self.n, words: self.words.copy(), }
}

///|
/// 位元數。
pub fn BitVec::length(self : BitVec) -> Int32 {
  self.n
}

///|
/// 讀取第 `i` 位。
pub fn BitVec::get(self : BitVec, i : Int32) -> Bool {
  guard i >= 0 && i < self.n else { abort("BitVec::get: index out of range") }
  let w = self.words[i / 64]
  let s = i % 64
  ((w >> s) & 1L) != 0L
}

///|
/// 置第 `i` 位為 1。
pub fn BitVec::set(self : BitVec, i : Int32) -> Unit {
  guard i >= 0 && i < self.n else { abort("BitVec::set: index out of range") }
  let wi = i / 64
  let s = i % 64
  self.words[wi] = self.words[wi] | (1L << s)
}

///|
/// 置第 `i` 位為 0。
pub fn BitVec::unset(self : BitVec, i : Int32) -> Unit {
  guard i >= 0 && i < self.n else { abort("BitVec::unset: index out of range") }
  let wi = i / 64
  let s = i % 64
  self.words[wi] = self.words[wi] & (1L << s).lnot()
}

///|
/// 併入 `other`（OR）。
pub fn BitVec::or_in_place(self : BitVec, other : BitVec) -> Unit {
  guard self.n == other.n else { abort("BitVec::or_in_place: length mismatch") }
  for i in 0..<self.words.length() {
    self.words[i] = self.words[i] | other.words[i]
  }
}

///|
/// 交上 `other`（AND）。
pub fn BitVec::and_in_place(self : BitVec, other : BitVec) -> Unit {
  guard self.n == other.n else {
    abort("BitVec::and_in_place: length mismatch")
  }
  for i in 0..<self.words.length() {
    self.words[i] = self.words[i] & other.words[i]
  }
}

///|
/// 自身減去 `other`（AND-NOT）。
pub fn BitVec::and_not_in_place(self : BitVec, other : BitVec) -> Unit {
  guard self.n == other.n else {
    abort("BitVec::and_not_in_place: length mismatch")
  }
  for i in 0..<self.words.length() {
    self.words[i] = self.words[i] & other.words[i].lnot()
  }
}

///|
/// 計算 1 的個數（Kernighan 演算法，O(設定位元數)）。
pub fn BitVec::count_ones(self : BitVec) -> Int32 {
  let mut c = 0
  for i in 0..<self.words.length() {
    let mut w = self.words[i]
    while w != 0L {
      w = w & (w - 1L)
      c = c + 1
    }
  }
  c
}

///|
/// 是否全零。
pub fn BitVec::is_empty(self : BitVec) -> Bool {
  for i in 0..<self.words.length() {
    guard self.words[i] == 0L else { return false }
  }
  true
}

///|
/// 依遞增次序走訪所有設定位元。
pub fn BitVec::each(self : BitVec, f : (Int32) -> Unit) -> Unit {
  for wi in 0..<self.words.length() {
    let base = wi * 64
    let mut w = self.words[wi]
    while w != 0L {
      let bit = w & -w
      let s = bit.ctz()
      f(base + s)
      w = w & (w - 1L)
    }
  }
}

///|
/// 設定位元的遞增陣列。
pub fn BitVec::to_array(self : BitVec) -> Array[Int32] {
  let out : Array[Int32] = []
  self.each(fn(i) { out.push(i) })
  out
}

///|
/// 是否包含 other 的全部設定位（self ⊇ other）。
pub fn BitVec::contains(self : BitVec, other : BitVec) -> Bool {
  guard self.n == other.n else { abort("BitVec::contains: length mismatch") }
  for i in 0..<self.words.length() {
    guard (self.words[i] & other.words[i]) == other.words[i] else {
      return false
    }
  }
  true
}

///|
/// 兩位向量逐字比較。
pub fn BitVec::equal(self : BitVec, other : BitVec) -> Bool {
  guard self.n == other.n else { return false }
  for i in 0..<self.words.length() {
    guard self.words[i] == other.words[i] else { return false }
  }
  true
}

///|
/// 內容雜湊（供 Map 鍵用）。
pub fn BitVec::hash(self : BitVec) -> Int32 {
  let mut h = self.n
  for i in 0..<self.words.length() {
    h = h * 31 + self.words[i].hash()
  }
  h
}

///|
pub impl Show for BitVec with fn to_string(self) {
  let mut s = "{"
  let arr = self.to_array()
  for i, v in arr {
    if i > 0 {
      s = s + ","
    }
    s = s + v.to_string()
  }
  s + "}"
}

///|
pub extend BitVec with Show::{to_string, output}

///|
/// Debug（供 `assert_eq` / `inspect` 之結構化差異顯示；與 Show 同一摘要）。
pub impl Debug for BitVec with fn to_repr(self) {
  Repr::literal(self.to_string())
}

///|
pub extend BitVec with Debug::{to_repr}
