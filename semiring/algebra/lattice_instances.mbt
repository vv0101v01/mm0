// ===========================================================================
// 格序半環的兩個「非平凡」實例
//
//   1. ParetoSet：多目標（向量）成本的互不支配集（antichain）。
//      ⊕ = 取聯集後做支配剪枝（冪等），⊗ = 閔可夫斯基和後剪枝。
//      這是 docs/DESIGN.md §5 多目標最短路的核心代數。
//
//   2. CyclicSet：有限循環群 ℤ_m 的冪集半環（⊕ = ∪、⊗ = 循環和）。
//      每個元素都落在一個有限子群中 ⇒ 完全正則 ⇒ star 可用
//      O(log m) 次乘法算出（group_star.mbt）。
// ===========================================================================

// ---------------------------------------------------------------------------
// ParetoSet
// ---------------------------------------------------------------------------

///|
/// 維度固定、載體為「互不支配」標籤集的半環。
///
/// 語義：`pts` 內任意兩點互不支配（canonical form）。
/// 支配：p ≼ q ⟺ ∀i. p[i] ≤ q[i] 且 p ≠ q。
pub(all) struct ParetoSet {
  dim : Int32
  pts : Array[Int32]
}

///|
/// 空集，即半環零元（不可達）。
pub fn ParetoSet::empty(dim : Int32) -> ParetoSet {
  { dim, pts: [], }
}

///|
/// 單位元 {0}^dim。
pub fn ParetoSet::one_of(dim : Int32) -> ParetoSet {
  { dim, pts: Array::make(dim, 0), }
}

///|
/// 由單一向量建立。
pub fn ParetoSet::point(vec : Array[Int32]) -> ParetoSet {
  { dim: vec.length(), pts: vec.copy(), }
}

///|
pub fn ParetoSet::size(self : ParetoSet) -> Int32 {
  if self.dim == 0 {
    return 0
  }
  self.pts.length() / self.dim
}

///|
/// 取出第 i 個標籤（回傳副本）。
pub fn ParetoSet::label(self : ParetoSet, i : Int32) -> Array[Int32] {
  let out = Array::make(self.dim, 0)
  for j in 0..<self.dim {
    out[j] = self.pts[i * self.dim + j]
  }
  out
}

///|
/// i 是否嚴格支配 j（以扁平標籤陣列表示）。
fn pareto_dominates(
  px : Array[Int32],
  i : Int32,
  py : Array[Int32],
  j : Int32,
  dim : Int32,
) -> Bool {
  let mut le_all = true
  let mut strict = false
  for d in 0..<dim {
    let x = px[i * dim + d]
    let y = py[j * dim + d]
    if x > y {
      le_all = false
      break
    }
    if x < y {
      strict = true
    }
  }
  le_all && strict
}

///|
fn pareto_equal(
  px : Array[Int32],
  i : Int32,
  py : Array[Int32],
  j : Int32,
  dim : Int32,
) -> Bool {
  for d in 0..<dim {
    if px[i * dim + d] != py[j * dim + d] {
      return false
    }
  }
  true
}

///|
/// 支配剪枝：移除被支配點與重複點，回傳 canonical form。
///
/// 複雜度 O(k²·d)，k 為標籤數。選擇 O(k²) 是因為它零配置、
/// 且本庫的實際 k 為數十量級（見 docs/DESIGN.md §5 的實測）。
fn pareto_prune(pts : Array[Int32], dim : Int32) -> Array[Int32] {
  if dim == 0 {
    return pts
  }
  let k = pts.length() / dim
  if k <= 1 {
    return pts
  }
  let keep = Array::make(k, true)
  for i in 0..<k {
    if !keep[i] {
      continue
    }
    for j in 0..<k {
      if i == j || !keep[j] {
        continue
      }
      if pareto_dominates(pts, j, pts, i, dim) {
        keep[i] = false
        break
      }
      if pareto_equal(pts, j, pts, i, dim) && j < i {
        keep[i] = false
        break
      }
    }
  }
  // canonical form：保留的標籤按字典序排序，使 ⊕ 對「相同的集合」得到
  // 逐位元相同的表示（⇒ 交換律、冪等律在值層面嚴格成立）。
  let idx = Array(capacity=k)
  for i in 0..<k {
    if keep[i] {
      idx.push(i)
    }
  }
  // 插入排序：k 很小（實測數十），且不需要額外比較物件
  let n = idx.length()
  for i in 1..<n {
    let cur = idx[i]
    let mut j = i - 1
    while j >= 0 && pareto_less(pts, cur, pts, idx[j], dim) {
      idx[j + 1] = idx[j]
      j = j - 1
    }
    idx[j + 1] = cur
  }
  let out = Array(capacity=idx.length() * dim)
  for i in idx {
    for d in 0..<dim {
      out.push(pts[i * dim + d])
    }
  }
  out
}

///|
/// 字典序嚴格小於（用於 canonical 排序）。
fn pareto_less(
  px : Array[Int32],
  i : Int32,
  py : Array[Int32],
  j : Int32,
  dim : Int32,
) -> Bool {
  for d in 0..<dim {
    let x = px[i * dim + d]
    let y = py[j * dim + d]
    if x != y {
      return x < y
    }
  }
  false
}

///|
/// 半環零元：不可達（空標籤集，dim ≥ 0）。
pub impl Semiring for ParetoSet with fn zero() {
  { dim: 0, pts: [], }
}

///|
/// 半環單位元。因為維度是值的一部分，而 `one()` 無從得知維度，
/// 這裡用 `dim = -1` 作為「單位元哨兵」；`⊗` 遇到哨兵直接回傳另一邊。
pub impl Semiring for ParetoSet with fn one() {
  { dim: -1, pts: [], }
}

///|
/// 是否為單位元哨兵。
pub fn ParetoSet::is_identity(self : ParetoSet) -> Bool {
  self.dim < 0
}

///|
/// ⊕ = 聯集 + 支配剪枝（冪等）。
pub impl Semiring for ParetoSet with fn plus(a, b) {
  if a.is_identity() || b.is_identity() {
    // 單位元帶有 {0}^d，在全序意義下支配所有非負標籤 ⇒ join 被它吸收
    return { dim: -1, pts: [], }
  }
  if a.pts.length() == 0 {
    return b
  }
  if b.pts.length() == 0 {
    return a
  }
  let dim = a.dim
  let merged = Array(capacity=a.pts.length() + b.pts.length())
  merged.append(a.pts[:])
  merged.append(b.pts[:])
  { dim, pts: pareto_prune(merged, dim), }
}

///|
/// ⊗ = 閔可夫斯基和 + 支配剪枝。
pub impl Semiring for ParetoSet with fn times(a, b) {
  if a.is_identity() {
    return b
  }
  if b.is_identity() {
    return a
  }
  if a.pts.length() == 0 || b.pts.length() == 0 {
    return { dim: a.dim.max(b.dim), pts: [], }
  }
  let dim = a.dim
  let ka = a.pts.length() / dim
  let kb = b.pts.length() / dim
  let out = Array(capacity=ka * kb * dim)
  for i in 0..<ka {
    for j in 0..<kb {
      for d in 0..<dim {
        out.push(a.pts[i * dim + d] + b.pts[j * dim + d])
      }
    }
  }
  { dim, pts: pareto_prune(out, dim), }
}

///|
pub impl Semiring for ParetoSet with fn is_zero(self) {
  !self.is_identity() && self.pts.length() == 0
}

///|
pub impl Semiring for ParetoSet with fn is_one(self) {
  self.is_identity()
}

///|
pub impl IdempotentSemiring for ParetoSet with fn le(a, b) {
  // a ≤ b ⟺ 每個 a 的標籤都被某個 b 的標籤支配（或相等）
  if b.is_identity() {
    return true // 單位元是最大元
  }
  if a.is_identity() {
    return false
  }
  if a.pts.length() == 0 {
    return true
  }
  if b.pts.length() == 0 {
    return false
  }
  let dim = a.dim
  if dim != b.dim {
    return false
  }
  let ka = a.pts.length() / dim
  let kb = b.pts.length() / dim
  for i in 0..<ka {
    let mut covered = false
    for j in 0..<kb {
      if pareto_dominates(b.pts, j, a.pts, i, dim) ||
        pareto_equal(b.pts, j, a.pts, i, dim) {
        covered = true
        break
      }
    }
    if !covered {
      return false
    }
  }
  true
}

///|
/// 格的 meet：兩個 antichain 以「分量 min」生成的共同下界集合。
pub impl OrderedSemiring for ParetoSet with fn meet(a, b) {
  if a.is_identity() || b.is_identity() {
    return { dim: 0, pts: [], }
  }
  if a.pts.length() == 0 || b.pts.length() == 0 {
    return { dim: a.dim, pts: [], }
  }
  let dim = a.dim
  let ka = a.pts.length() / dim
  let kb = b.pts.length() / dim
  let out = Array(capacity=ka * kb * dim)
  for i in 0..<ka {
    for j in 0..<kb {
      for d in 0..<dim {
        let x = a.pts[i * dim + d]
        let y = b.pts[j * dim + d]
        out.push(if x <= y { x } else { y })
      }
    }
  }
  { dim, pts: pareto_prune(out, dim), }
}

///|
pub impl OrderedSemiring for ParetoSet with fn top() {
  { dim: -1, pts: [], }
}

///|
pub impl Show for ParetoSet with fn output(self, logger) {
  logger.write_string("{")
  let k = self.size()
  for i in 0..<k {
    if i > 0 {
      logger.write_string(", ")
    }
    logger.write_string("(")
    for j in 0..<self.dim {
      if j > 0 {
        logger.write_string(",")
      }
      logger.write_string(self.pts[i * self.dim + j].to_string())
    }
    logger.write_string(")")
  }
  logger.write_string("}")
}

///|
pub impl Eq for ParetoSet with fn equal(a, b) {
  if a.is_identity() || b.is_identity() {
    return a.is_identity() == b.is_identity()
  }
  if a.pts.length() == 0 || b.pts.length() == 0 {
    return a.pts.length() == b.pts.length()
  }
  a.dim == b.dim && a.pts == b.pts
}

// ---------------------------------------------------------------------------
// CyclicSet：完全正則半環的非平凡實例
// ---------------------------------------------------------------------------

///|
/// 循環群 ℤ_m 的冪集：變數儲存於 64-bit 位元遮罩（1 ≤ m ≤ 64）。
///
/// ⊕ = ∪（位元 OR，冪等）、⊗ = 循環閔可夫斯基和（位移後 OR）。
/// 支撐集落在有限群中 ⇒ 完全正則：
///   群逆 S° = {−x : x ∈ S}，S ⊗ S° ⊗ S = S。
pub(all) struct CyclicSet {
  m : Int32
  bits : UInt64
}

///|

///|
/// 群階的合成：0 視為「未指定」，兩個都指定時必須一致（取大者）。
fn cyclic_dim(a : Int32, b : Int32) -> Int32 {
  if a == 0 {
    b
  } else if b == 0 {
    a
  } else if a > b {
    a
  } else {
    b
  }
}

///|
pub fn CyclicSet::empty(m : Int32) -> CyclicSet {
  { m, bits: 0UL, }
}

///|
/// ℤ_m 中的 {0}（乘法單位元語義下的 one）。
pub fn CyclicSet::one_of(m : Int32) -> CyclicSet {
  { m, bits: 1UL, }
}

///|
pub fn CyclicSet::singleton(m : Int32, x : Int32) -> CyclicSet {
  { m, bits: 1UL << (x % m), }
}

///|
pub fn CyclicSet::of_range(m : Int32, elements : Array[Int32]) -> CyclicSet {
  let mut bits = 0UL
  for x in elements {
    bits = bits | (1UL << (x % m))
  }
  { m, bits, }
}

///|
pub fn CyclicSet::contains(self : CyclicSet, x : Int32) -> Bool {
  ((self.bits >> (x % self.m)) & 1UL) == 1UL
}

///|
pub fn CyclicSet::cardinality(self : CyclicSet) -> Int32 {
  popcount64(self.bits)
}

///|
fn popcount64(x : UInt64) -> Int32 {
  let mut v = x
  let mut c = 0
  while v != 0UL {
    v = v & (v - 1UL)
    c = c + 1
  }
  c
}

///|
fn rotl64(x : UInt64, m : Int32, r : Int32) -> UInt64 {
  let r = (r % m + m) % m
  if r == 0 {
    return x
  }
  let mask = if m >= 64 { 0xFFFF_FFFF_FFFF_FFFFUL } else { (1UL << m) - 1UL }
  let hi = x << r
  let lo = x >> (m - r)
  (hi | lo) & mask
}

///|
pub impl Semiring for CyclicSet with fn zero() {
  { m: 0, bits: 0UL, }
}

///|
pub impl Semiring for CyclicSet with fn one() {
  { m: 0, bits: 1UL, }
}

///|
pub impl Semiring for CyclicSet with fn plus(a, b) {
  { m: cyclic_dim(a.m, b.m), bits: a.bits | b.bits, }
}

///|
pub impl Semiring for CyclicSet with fn times(a, b) {
  let m = cyclic_dim(a.m, b.m)
  let mut acc = 0UL
  let mut rest = b.bits
  let mut j = 0
  while rest != 0UL && j < m {
    if (rest & 1UL) == 1UL {
      acc = acc | rotl64(a.bits, m, j)
    }
    rest = rest >> 1
    j = j + 1
  }
  { m, bits: acc, }
}

///|
pub impl Semiring for CyclicSet with fn is_zero(self) {
  self.bits == 0UL
}

///|
pub impl Semiring for CyclicSet with fn is_one(self) {
  self.bits == 1UL
}

///|
pub impl IdempotentSemiring for CyclicSet with fn le(a, b) {
  (a.bits & b.bits) == a.bits
}

///|
pub impl GroupElement for CyclicSet with fn group_inv(a) {
  let m = a.m
  let mut acc = 0UL
  let mut rest = a.bits
  let mut j = 0
  while rest != 0UL && j < m {
    if (rest & 1UL) == 1UL {
      acc = acc | (1UL << ((m - j) % m))
    }
    rest = rest >> 1
    j = j + 1
  }
  { m, bits: acc, }
}

///|
/// 子群階的上界就是群階 m（a^m = e 對循環群恆成立）。
pub impl GroupElement for CyclicSet with fn order_bound(a) {
  a.m
}

///|
/// star = ⋃_{k=0}^{m} a^k，用倍增法在 O(log m) 次乘法內完成。
pub impl StarSemiring for CyclicSet with fn star(a) {
  star_by_doubling(a)
}

///|

///|
/// 只有支撐集參與等值判定；`m` 是「所在群」的元資料。
pub impl Eq for CyclicSet with fn equal(a, b) {
  a.bits == b.bits
}

///|
pub impl Show for CyclicSet with fn output(self, logger) {
  logger.write_string("{")
  let mut first = true
  for j in 0..<self.m {
    if self.contains(j) {
      if !first {
        logger.write_string(",")
      }
      logger.write_string(j.to_string())
      first = false
    }
  }
  logger.write_string("}")
}

///|
/// 0.10 起 `impl` 不再自動把方法提升為一般方法；這裡顯式宣告。

///|
pub extend ParetoSet with Semiring::{zero, one, plus, times, is_zero, is_one}

///|
/// 0.10 起 `impl` 不再自動把方法提升為一般方法；這裡顯式宣告。

///|
pub extend ParetoSet with IdempotentSemiring::{le}

///|
/// 0.10 起 `impl` 不再自動把方法提升為一般方法；這裡顯式宣告。

///|
pub extend ParetoSet with OrderedSemiring::{join, meet, top, bottom}

///|
/// 0.10 起 `impl` 不再自動把方法提升為一般方法；這裡顯式宣告。

///|
pub extend ParetoSet with Show::{output, to_string}

///|
/// 0.10 起 `impl` 不再自動把方法提升為一般方法；這裡顯式宣告。

///|
pub extend ParetoSet with Eq::{equal, not_equal}

///|
/// 0.10 起 `impl` 不再自動把方法提升為一般方法；這裡顯式宣告。

///|
pub extend CyclicSet with Semiring::{zero, one, plus, times, is_zero, is_one}

///|
/// 0.10 起 `impl` 不再自動把方法提升為一般方法；這裡顯式宣告。

///|
pub extend CyclicSet with IdempotentSemiring::{le}

///|
/// 0.10 起 `impl` 不再自動把方法提升為一般方法；這裡顯式宣告。

///|
pub extend CyclicSet with GroupElement::{group_inv, order_bound, group_id}

///|
/// 0.10 起 `impl` 不再自動把方法提升為一般方法；這裡顯式宣告。

///|
pub extend CyclicSet with StarSemiring::{star}

///|
/// 0.10 起 `impl` 不再自動把方法提升為一般方法；這裡顯式宣告。

///|
pub extend CyclicSet with Eq::{equal, not_equal}

///|
/// 0.10 起 `impl` 不再自動把方法提升為一般方法；這裡顯式宣告。

///|
pub extend CyclicSet with Show::{output, to_string}
