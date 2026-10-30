// ===========================================================================
// 么半群（Monoid）與其上的三種聚合結構
//
//   SegTree      任意么半群，O(log n) 區間查詢 / O(log n) 單點更新
//   SparseTable  冪等么半群（型別約束！），O(1) 查詢 / O(n log n) 建表
//   Fenwick      群（有逆元，型別約束！），O(n) 建表 / O(log n) 前綴與區間
//
// 「為什麼要型別約束」不是潔癖：
//   * Sparse table 的 O(1) 查詢靠「兩個重疊區間」覆蓋查詢區間，
//     重疊部分會被算兩次——只有冪等才算得對（max/min/gcd 可以，
//     sum/product 不行）。這是經典的 off-by-law 錯誤來源。
//   * Fenwick 的區間查詢 = prefix(r) − prefix(l)，需要逆元。
// ===========================================================================

///|
using @alg {
  trait Monoid,
  trait CommutativeMonoid,
  trait IdempotentMonoid,
  trait GroupMonoid,
}

// ---------------------------------------------------------------------------
// 常用實例
// ---------------------------------------------------------------------------

///|
/// 加法么半群（Int64），飽和運算避免溢位回繞。
pub(all) struct SumI64 {
  v : Int64
} derive(Eq)

///|
pub fn SumI64::of(v : Int64) -> SumI64 {
  { v, }
}

///|
pub impl Monoid for SumI64 with fn empty() {
  { v: 0L, }
}

///|
pub impl Monoid for SumI64 with fn combine(a, b) {
  let s = a.v + b.v
  if s < 0L && a.v > 0L && b.v > 0L {
    { v: 0x7FFF_FFFF_FFFF_FFFFL, }
  } else {
    { v: s, }
  }
}

///|
pub impl CommutativeMonoid for SumI64

///|
pub impl GroupMonoid for SumI64 with fn invert(a) {
  { v: -a.v, }
}

///|
pub impl Show for SumI64 with fn output(self, logger) {
  logger.write_string(self.v.to_string())
}

///|
/// 最大值么半群（冪等）。
pub(all) struct MaxI64 {
  v : Int64
} derive(Eq)

///|
/// 最小值么半群（冪等）。
pub(all) struct MinI64 {
  v : Int64
} derive(Eq)

///|
pub impl Monoid for MaxI64 with fn empty() {
  { v: -0x7FFF_FFFF_FFFF_FFFFL, }
}

///|
pub impl Monoid for MaxI64 with fn combine(a, b) {
  if a.v >= b.v {
    a
  } else {
    b
  }
}

///|
pub impl CommutativeMonoid for MaxI64

///|
pub impl IdempotentMonoid for MaxI64

///|
pub impl Show for MaxI64 with fn output(self, logger) {
  logger.write_string(self.v.to_string())
}

///|
pub impl Monoid for MinI64 with fn empty() {
  { v: 0x7FFF_FFFF_FFFF_FFFFL, }
}

///|
pub impl Monoid for MinI64 with fn combine(a, b) {
  if a.v <= b.v {
    a
  } else {
    b
  }
}

///|
pub impl CommutativeMonoid for MinI64

///|
pub impl IdempotentMonoid for MinI64

///|
pub impl Show for MinI64 with fn output(self, logger) {
  logger.write_string(self.v.to_string())
}

///|
/// 仿射映射 x ↦ a·x + b，組合為函數合成（么半群，非交換）。
///
/// 這是本庫在 spline 裡的關鍵：一階線性遞推 u_i = z·u_{i-1} + y_i
/// 的每一步都是仿射映射，整條遞推就是這些映射的乘積 ⇒ 可以用
/// 么半群前綴掃描（prefix scan）以 O(n) 且無序列依賴的方式算出。
pub(all) struct AffineM {
  a : Double
  b : Double
}

///|
pub fn AffineM::new(a : Double, b : Double) -> AffineM {
  { a, b, }
}

///|
/// 對 x 求值。
pub fn AffineM::apply(self : AffineM, x : Double) -> Double {
  self.a * x + self.b
}

///|
pub impl Eq for AffineM with fn equal(x, y) {
  x.a == y.a && x.b == y.b
}

///|
pub impl Monoid for AffineM with fn empty() {
  { a: 1.0, b: 0.0, }
}

///|
/// combine(f, g) = f ∘ g（先 g 後 f）。
pub impl Monoid for AffineM with fn combine(f, g) {
  { a: f.a * g.a, b: f.a * g.b + f.b, }
}

///|
pub impl Show for AffineM with fn output(self, logger) {
  logger.write_string("\{self.a}·x + \{self.b}")
}

// ---------------------------------------------------------------------------
// 前綴掃描（work-efficient, Blelloch 上掃/下掃）
// ---------------------------------------------------------------------------

///|
/// 包含式前綴掃描（Hillis–Steele 原地版）：
///   out[i] = combine(data[0], …, data[i])
///
/// 工作量 O(n log n)、額外記憶體 O(1)、**深度 O(log n)**。
/// 深度小是它在硬體/平行環境下的價值（Blelloch 版本工作量 O(n) 但需要
/// 額外 O(n) 緩衝；兩者都實作於此，讓「延遲」與「總工作量」可以取捨）。
pub fn[M : Monoid] prefix_scan(data : Array[M], out~ : Array[M]) -> Unit {
  let n = data.length()
  out.clear()
  for i in 0..<n {
    out.push(data[i])
  }
  let mut step = 1
  while step < n {
    // 由後往前，保證讀到的是上一層的值
    let mut i = n - 1
    while i >= step {
      out[i] = Monoid::combine(out[i - step], out[i])
      i = i - 1
    }
    step = step * 2
  }
}

///|
/// 逐項累加（O(n) 但完全序列）——對照組，用於驗證與量測。
pub fn[M : Monoid] prefix_scan_sequential(
  data : Array[M],
  out~ : Array[M],
) -> Unit {
  out.clear()
  let mut acc = Monoid::empty()
  for x in data {
    acc = Monoid::combine(acc, x)
    out.push(acc)
  }
}

// ---------------------------------------------------------------------------
// Segment tree
// ---------------------------------------------------------------------------

///|
/// 迭代式 segment tree（size 向上取 2 的冪，2·size 個節點）。
pub(all) struct SegTree[M] {
  size : Int32
  d : Array[M]
}

///|
pub fn[M : Monoid] SegTree::build(data : Array[M]) -> SegTree[M] {
  let n = data.length()
  let mut size = 1
  while size < n {
    size = size * 2
  }
  let d = Array::make(2 * size, Monoid::empty())
  for i in 0..<n {
    d[size + i] = data[i]
  }
  let mut i = size - 1
  while i > 0 {
    d[i] = Monoid::combine(d[2 * i], d[2 * i + 1])
    i = i - 1
  }
  { size, d, }
}

///|
/// 單點更新。
pub fn[M : Monoid] SegTree::set(self : SegTree[M], idx : Int32, v : M) -> Unit {
  let mut i = idx + self.size
  self.d[i] = v
  i = i / 2
  while i > 0 {
    self.d[i] = Monoid::combine(self.d[2 * i], self.d[2 * i + 1])
    i = i / 2
  }
}

///|
/// 區間查詢 [l, r)（左閉右開），O(log n)。
pub fn[M : Monoid] SegTree::query(self : SegTree[M], l : Int32, r : Int32) -> M {
  let mut res_l = Monoid::empty()
  let mut res_r = Monoid::empty()
  let mut a = l + self.size
  let mut b = r + self.size
  while a < b {
    if a % 2 == 1 {
      res_l = Monoid::combine(res_l, self.d[a])
      a = a + 1
    }
    if b % 2 == 1 {
      b = b - 1
      res_r = Monoid::combine(self.d[b], res_r)
    }
    a = a / 2
    b = b / 2
  }
  Monoid::combine(res_l, res_r)
}

///|
pub fn[M] SegTree::len(self : SegTree[M]) -> Int32 {
  self.size
}

// ---------------------------------------------------------------------------
// Sparse table（需要冪等么半群）
// ---------------------------------------------------------------------------

///|
/// 靜態 O(1) 區間查詢：O(n log n) 建表，查詢用兩個重疊的 2^k 區塊。
///
/// 型別上要求 `IdempotentMonoid`：重疊部分會被算兩次，只有冪等才安全。
pub(all) struct SparseTable[M] {
  levels : Array[Array[M]]
  logs : Array[Int32]
}

///|
pub fn[M : IdempotentMonoid] SparseTable::build(
  data : Array[M],
) -> SparseTable[M] {
  let n = data.length()
  let levels = Array(capacity=1)
  levels.push(data.copy())
  let mut k = 1
  while 1 << k <= n {
    let prev = levels[k - 1]
    let span = 1 << (k - 1)
    let cur = Array::make(n - (1 << k) + 1, Monoid::empty())
    for i in 0..<cur.length() {
      cur[i] = Monoid::combine(prev[i], prev[i + span])
    }
    levels.push(cur)
    k = k + 1
  }
  let logs = Array::make(n + 1, 0)
  for i in 2..<=n {
    logs[i] = logs[i / 2] + 1
  }
  { levels, logs, }
}

///|
/// [l, r) 的聚合，O(1)。
pub fn[M : IdempotentMonoid] SparseTable::query(
  self : SparseTable[M],
  l : Int32,
  r : Int32,
) -> M {
  let len = r - l
  let k = self.logs[len]
  let span = 1 << k
  Monoid::combine(self.levels[k][l], self.levels[k][r - span])
}

// ---------------------------------------------------------------------------
// Fenwick（需要群）
// ---------------------------------------------------------------------------

///|
/// Fenwick tree：前綴和 O(log n)，區間和 O(log n)。
///
/// 型別上要求 `GroupMonoid`：區間和 = prefix(r) ⊖ prefix(l) 需要逆元。
pub(all) struct Fenwick[M] {
  n : Int32
  d : Array[M]
}

///|
pub fn[M : GroupMonoid] Fenwick::build(data : Array[M]) -> Fenwick[M] {
  let n = data.length()
  let d = Array::make(n + 1, Monoid::empty())
  for i in 1..<=n {
    d[i] = Monoid::combine(d[i], data[i - 1])
    let j = i + (i & -i)
    if j <= n {
      d[j] = Monoid::combine(d[j], d[i])
    }
  }
  { n, d, }
}

///|
/// 位置 idx（0-based）加上 delta。
pub fn[M : GroupMonoid] Fenwick::add(
  self : Fenwick[M],
  idx : Int32,
  delta : M,
) -> Unit {
  let mut i = idx + 1
  while i <= self.n {
    self.d[i] = Monoid::combine(self.d[i], delta)
    i = i + (i & -i)
  }
}

///|
/// 前綴聚合 [0, end)。
pub fn[M : GroupMonoid] Fenwick::prefix(self : Fenwick[M], end : Int32) -> M {
  let mut acc = Monoid::empty()
  let mut i = end
  while i > 0 {
    acc = Monoid::combine(acc, self.d[i])
    i = i - (i & -i)
  }
  acc
}

///|
/// 區間聚合 [l, r)。
pub fn[M : GroupMonoid] Fenwick::range(
  self : Fenwick[M],
  l : Int32,
  r : Int32,
) -> M {
  Monoid::combine(self.prefix(r), GroupMonoid::invert(self.prefix(l)))
}

// ---------------------------------------------------------------------------
// 反么半群（opposite monoid）：只把 combine 的順序顛倒
// ---------------------------------------------------------------------------

///|
/// 反么半群：`combine(a, b) = Monoid::combine(b, a)`。
///
/// 「函數合成」這個么半群的乘法方向與資料流方向相反；當需要
/// 「依序套用」而非「由右而左合成」時，取反么半群是最乾淨的做法，
/// 而且不改變任何演算法的結構（前綴掃描本身不需要交換律）。
pub(all) struct OppositeM[M] {
  inner : M
}

///|
pub fn[M] OppositeM::of(x : M) -> OppositeM[M] {
  { inner: x, }
}

///|
pub impl[M : Monoid] Monoid for OppositeM[M] with fn empty() {
  { inner: Monoid::empty(), }
}

///|
pub impl[M : Monoid] Monoid for OppositeM[M] with fn combine(a, b) {
  { inner: Monoid::combine(b.inner, a.inner), }
}

///|
pub impl[M : Show] Show for OppositeM[M] with fn output(self, logger) {
  self.inner.output(logger)
}

///|
pub impl[M : Monoid] Eq for OppositeM[M] with fn equal(a, b) {
  a.inner == b.inner
}

///|
/// 0.10 起 `impl` 不再自動把方法提升為一般方法；這裡顯式宣告。

///|
pub extend SumI64 with Monoid::{empty, combine}

///|
/// 0.10 起 `impl` 不再自動把方法提升為一般方法；這裡顯式宣告。

///|
pub extend SumI64 with GroupMonoid::{invert}

///|
/// 0.10 起 `impl` 不再自動把方法提升為一般方法；這裡顯式宣告。

///|
pub extend SumI64 with Show::{output, to_string}

///|
/// 0.10 起 `impl` 不再自動把方法提升為一般方法；這裡顯式宣告。

///|
pub extend MaxI64 with Monoid::{empty, combine}

///|
/// 0.10 起 `impl` 不再自動把方法提升為一般方法；這裡顯式宣告。

///|
pub extend MaxI64 with Show::{output, to_string}

///|
/// 0.10 起 `impl` 不再自動把方法提升為一般方法；這裡顯式宣告。

///|
pub extend MinI64 with Monoid::{empty, combine}

///|
/// 0.10 起 `impl` 不再自動把方法提升為一般方法；這裡顯式宣告。

///|
pub extend MinI64 with Show::{output, to_string}

///|
/// 0.10 起 `impl` 不再自動把方法提升為一般方法；這裡顯式宣告。

///|
pub extend AffineM with Eq::{equal, not_equal}

///|
/// 0.10 起 `impl` 不再自動把方法提升為一般方法；這裡顯式宣告。

///|
pub extend AffineM with Monoid::{empty, combine}

///|
/// 0.10 起 `impl` 不再自動把方法提升為一般方法；這裡顯式宣告。

///|
pub extend AffineM with Show::{output, to_string}

///|
/// 0.10 起 `impl` 不再自動把方法提升為一般方法；這裡顯式宣告。

///|
pub extend OppositeM with Monoid::{empty, combine}

///|
/// 0.10 起 `impl` 不再自動把方法提升為一般方法；這裡顯式宣告。

///|
pub extend OppositeM with Show::{output, to_string}

///|
/// 0.10 起 `impl` 不再自動把方法提升為一般方法；這裡顯式宣告。

///|
pub extend OppositeM with Eq::{equal, not_equal}

///|
/// `derive(Eq)` 產生的 impl 同樣需要顯式 extend（0.10 的方法提升規則）。

///|
pub extend MaxI64 with Eq::{equal, not_equal}

///|
/// `derive(Eq)` 產生的 impl 同樣需要顯式 extend（0.10 的方法提升規則）。

///|
pub extend MinI64 with Eq::{equal, not_equal}

///|
/// `derive(Eq)` 產生的 impl 同樣需要顯式 extend（0.10 的方法提升規則）。

///|
pub extend SumI64 with Eq::{equal, not_equal}
