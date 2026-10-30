// ===========================================================================
// 熱帶半環 (min,+)
//
//   ⊕ = min, ⊗ = +, 零元 0_{Trop} = +∞, 單位元 1_{Trop} = 0
//
// 數值域：[-2^30+2, +∞]（Int32，4 bytes/element）。
// 以 INF = 2^30-1 表示 +∞，乘法做飽和加，保證不會整數溢位，
// 也就是說「錯的答案不會用溢位的方式偷偷出現」。
// ===========================================================================

///|
/// +∞，即熱帶半環的零元。
pub let trop_inf : Int32 = 0x3FFF_FFFF

///|
/// 熱帶半環元素（min-plus）。
pub(all) struct Trop {
  v : Int32
} derive(Eq)

///|
/// 建構：權值會被夾在合法範圍內（超過 INF 視為 +∞）。
pub fn Trop::new(w : Int32) -> Trop {
  if w >= trop_inf {
    { v: trop_inf, }
  } else if w <= -trop_inf {
    { v: -trop_inf, }
  } else {
    { v: w, }
  }
}

///|
/// +∞ 元素（半環零元）。
pub fn Trop::inf() -> Trop {
  { v: trop_inf, }
}

///|
/// 是否為 +∞。
pub fn Trop::is_inf(self : Trop) -> Bool {
  self.v >= trop_inf
}

///|
/// 取值（呼叫端需自行處理 is_inf）。
pub fn Trop::value(self : Trop) -> Int32 {
  self.v
}

///|
pub impl Show for Trop with fn output(self, logger) {
  if self.is_inf() {
    logger.write_string("inf")
  } else {
    logger.write_string(self.v.to_string())
  }
}

///|
pub impl Semiring for Trop with fn zero() {
  { v: trop_inf, }
}

///|
pub impl Semiring for Trop with fn one() {
  { v: 0, }
}

///|
/// ⊕ = min（冪等）。
pub impl Semiring for Trop with fn plus(a, b) {
  if a.v <= b.v {
    a
  } else {
    b
  }
}

///|
/// ⊗ = 飽和加法。
pub impl Semiring for Trop with fn times(a, b) {
  if a.v >= trop_inf {
    a
  } else if b.v >= trop_inf {
    b
  } else {
    let s = a.v + b.v
    if s >= trop_inf {
      { v: trop_inf, }
    } else {
      { v: s, }
    }
  }
}

///|
pub impl Semiring for Trop with fn is_zero(self) {
  self.v >= trop_inf
}

///|
pub impl Semiring for Trop with fn is_one(self) {
  self.v == 0
}

///|
pub impl IdempotentSemiring for Trop with fn le(a, b) {
  a.v >= b.v
}

///|
/// 星閉：x* = min(0, x, 2x, 3x, …)。
///
/// 定理（見 docs/DESIGN.md §3.1）：在 (ℝ∪{∞}, min, +) 中
///   x* = 0      若 x ≥ 0
///   x* = -∞     若 x < 0（負環 ⇒ 無窮負路徑，閉包不存在）
///
/// 本實作把「x < 0」回報成 +∞（零元）並由 `star_checked` 給出明確錯誤，
/// 避免悄悄回傳一個無意義的數值。
pub impl StarSemiring for Trop with fn star(a) {
  if a.v >= 0 {
    { v: 0, }
  } else {
    { v: trop_inf, }
  }
}

///|
/// 完全正則性：在 (ℝ, +) 這個乘法群中，a 的群逆就是 -a
/// （a ⊗ a° ⊗ a = a + (-a) + a = a）。群階無窮 ⇒ order_bound 回報 0。
pub impl GroupElement for Trop with fn group_inv(a) {
  if a.is_inf() {
    { v: trop_inf, }
  } else {
    Trop::new(-a.v)
  }
}

///|
pub impl GroupElement for Trop with fn order_bound(_a) {
  0
}

///|
/// 熱帶半環的最大值版本 (max,+)：⊕ = max、⊗ = +，零元 = -∞。
pub(all) struct TropMax {
  v : Int32
} derive(Eq)

///|
pub let trop_neg_inf : Int32 = -0x3FFF_FFFF

///|
pub fn TropMax::new(w : Int32) -> TropMax {
  if w <= trop_neg_inf {
    { v: trop_neg_inf, }
  } else if w >= -trop_neg_inf {
    { v: -trop_neg_inf, }
  } else {
    { v: w, }
  }
}

///|
pub fn TropMax::is_neg_inf(self : TropMax) -> Bool {
  self.v <= trop_neg_inf
}

///|
pub fn TropMax::value(self : TropMax) -> Int32 {
  self.v
}

///|
pub impl Show for TropMax with fn output(self, logger) {
  if self.is_neg_inf() {
    logger.write_string("-inf")
  } else {
    logger.write_string(self.v.to_string())
  }
}

///|
pub impl Semiring for TropMax with fn zero() {
  { v: trop_neg_inf, }
}

///|
pub impl Semiring for TropMax with fn one() {
  { v: 0, }
}

///|
pub impl Semiring for TropMax with fn plus(a, b) {
  if a.v >= b.v {
    a
  } else {
    b
  }
}

///|
pub impl Semiring for TropMax with fn times(a, b) {
  if a.v <= trop_neg_inf {
    a
  } else if b.v <= trop_neg_inf {
    b
  } else {
    let s = a.v + b.v
    if s <= trop_neg_inf {
      { v: trop_neg_inf, }
    } else {
      { v: s, }
    }
  }
}

///|
pub impl IdempotentSemiring for TropMax with fn le(a, b) {
  a.v <= b.v
}

///|
/// (max,+) 的 star：x* = max(0, x, 2x, …) 發散（除非 x ≤ 0），
/// 因此恆為 +∞ 意義的「不存在」，這裡以零元（-∞）回報。
pub impl StarSemiring for TropMax with fn star(a) {
  if a.v <= 0 {
    { v: 0, }
  } else {
    { v: trop_neg_inf, }
  }
}

///|
/// 對外可檢查的 star：回傳 star 值，並在閉包不存在時給出錯誤。
pub fn Trop::star_checked(self : Trop) -> Result[Trop, String] {
  if self.v < 0 {
    Err("negative cycle: tropical closure diverges (x = \{self.v})")
  } else {
    Ok({ v: 0, })
  }
}

// ---------------------------------------------------------------------------
// 瓶頸半環（widest path）：格序半環的典型實例
// ---------------------------------------------------------------------------

///|
/// 最大容量上界（同時是乘法單位元）。
pub let cap_max : Int32 = 0x3FFF_FFFF

///|
/// 瓶頸半環：(max, min)，零元 = 0（無連通）、單位元 = cap_max（無限容量）。
///
/// 這是一個格序半環：join = max = ⊕、meet = min = ⊗，
/// 且 min/max 互相分配，故 ⊗ 對 ⊕ 及 meet 皆分配。
pub(all) struct Bottleneck {
  w : Int32
} derive(Eq)

///|
pub fn Bottleneck::new(w : Int32) -> Bottleneck {
  if w < 0 {
    { w: 0, }
  } else if w > cap_max {
    { w: cap_max, }
  } else {
    { w, }
  }
}

///|
pub fn Bottleneck::value(self : Bottleneck) -> Int32 {
  self.w
}

///|
pub impl Show for Bottleneck with fn output(self, logger) {
  if self.w == 0 {
    logger.write_string("0(disconnected)")
  } else {
    logger.write_string(self.w.to_string())
  }
}

///|
pub impl Semiring for Bottleneck with fn zero() {
  { w: 0, }
}

///|
pub impl Semiring for Bottleneck with fn one() {
  { w: cap_max, }
}

///|
pub impl Semiring for Bottleneck with fn plus(a, b) {
  if a.w >= b.w {
    a
  } else {
    b
  }
}

///|
pub impl Semiring for Bottleneck with fn times(a, b) {
  if a.w <= b.w {
    a
  } else {
    b
  }
}

///|
pub impl IdempotentSemiring for Bottleneck with fn le(a, b) {
  a.w <= b.w
}

///|
pub impl OrderedSemiring for Bottleneck with fn meet(a, b) {
  if a.w <= b.w {
    a
  } else {
    b
  }
}

///|
pub impl OrderedSemiring for Bottleneck with fn top() {
  { w: cap_max, }
}

///|
/// x* = 1 ⊕ x = max(cap_max, x) = cap_max。
pub impl StarSemiring for Bottleneck with fn star(_a) {
  { w: cap_max, }
}

// ---------------------------------------------------------------------------
// 計數半環（非冪等）：路徑計數、以及「冪等前提」的負面對照組
// ---------------------------------------------------------------------------

///|
/// 計數半環 (Int64, +, ×) 帶飽和運算。
///
/// 這是**非冪等**半環：Floyd–Warshall 的原地更新在這裡是錯的
/// （同一條路徑會被重複累加），見 matrix/star.mbt 的型別約束與
/// tests 中的負面案例。
pub(all) struct Counting {
  n : Int64
} derive(Eq)

///|
pub fn Counting::new(n : Int64) -> Counting {
  { n, }
}

///|
pub fn Counting::value(self : Counting) -> Int64 {
  self.n
}

///|
pub impl Show for Counting with fn output(self, logger) {
  logger.write_string(self.n.to_string())
}

///|
pub impl Semiring for Counting with fn zero() {
  { n: 0L, }
}

///|
pub impl Semiring for Counting with fn one() {
  { n: 1L, }
}

///|
pub impl Semiring for Counting with fn plus(a, b) {
  let s = a.n + b.n
  if s < 0L {
    { n: 0x7FFF_FFFF_FFFF_FFFFL, }
  } else {
    { n: s, }
  }
}

///|
pub impl Semiring for Counting with fn times(a, b) {
  if a.n == 0L || b.n == 0L {
    { n: 0L, }
  } else {
    let p = a.n * b.n
    if a.n > 0x7FFF_FFFF_FFFF_FFFFL / b.n {
      { n: 0x7FFF_FFFF_FFFF_FFFFL, }
    } else {
      { n: p, }
    }
  }
}

///|
/// 計數半環的 star：1 + n + n² + … 僅在 n = 0 時收斂（有限 DAG 情形），
/// 其餘發散 ⇒ 飽和到 Int64 上限，並在結果上明確可見（不會悄悄回繞成負數）。
pub impl StarSemiring for Counting with fn star(a) {
  if a.n == 0L {
    { n: 1L, }
  } else {
    { n: 0x7FFF_FFFF_FFFF_FFFFL, }
  }
}

// ---------------------------------------------------------------------------
// 機率半環（非冪等、非封閉）：示範「閉包需要收斂前提」
// ---------------------------------------------------------------------------

///|
/// 機率半環 (Double, +, ×)。
pub(all) struct Prob {
  p : Double
} derive(Eq)

///|
pub fn Prob::new(p : Double) -> Prob {
  { p, }
}

///|
pub fn Prob::value(self : Prob) -> Double {
  self.p
}

///|
pub impl Show for Prob with fn output(self, logger) {
  logger.write_string(self.p.to_string())
}

///|
pub impl Semiring for Prob with fn zero() {
  { p: 0.0, }
}

///|
pub impl Semiring for Prob with fn one() {
  { p: 1.0, }
}

///|
pub impl Semiring for Prob with fn plus(a, b) {
  { p: a.p + b.p, }
}

///|
pub impl Semiring for Prob with fn times(a, b) {
  { p: a.p * b.p, }
}

///|
/// p* = 1/(1-p)，僅在 |p| < 1 時收斂 ⇒ 以 Option 明確表達前提。
pub fn Prob::star_checked(self : Prob) -> Result[Prob, String] {
  if self.p >= 1.0 || self.p <= -1.0 {
    Err("probability closure diverges: |p| >= 1")
  } else {
    Ok({ p: 1.0 / (1.0 - self.p), })
  }
}

///|
/// 布林半環 (∨, ∧)：可作為關係代數的標量版。
pub(all) struct BoolSr {
  b : Bool
} derive(Eq)

///|
pub fn BoolSr::of(b : Bool) -> BoolSr {
  { b, }
}

///|
pub impl Show for BoolSr with fn output(self, logger) {
  logger.write_string(self.b.to_string())
}

///|
pub impl Semiring for BoolSr with fn zero() {
  { b: false, }
}

///|
pub impl Semiring for BoolSr with fn one() {
  { b: true, }
}

///|
pub impl Semiring for BoolSr with fn plus(a, b) {
  { b: a.b || b.b, }
}

///|
pub impl Semiring for BoolSr with fn times(a, b) {
  { b: a.b && b.b, }
}

///|
pub impl IdempotentSemiring for BoolSr with fn le(a, b) {
  !a.b || b.b
}

///|
/// 在布林半環中 x* = 1 ⊕ x = true。
pub impl StarSemiring for BoolSr with fn star(_a) {
  { b: true, }
}

///|
/// 完全正則：布林半環每個元素都落在一個 1 階子群，群逆為自身。
pub impl GroupElement for BoolSr with fn group_inv(a) {
  a
}

///|
pub impl GroupElement for BoolSr with fn order_bound(_a) {
  1
}

///|
/// 0.10 起 `impl` 不再自動把方法提升為一般方法；這裡顯式宣告。

///|
pub extend Trop with Show::{output, to_string}

///|
/// 0.10 起 `impl` 不再自動把方法提升為一般方法；這裡顯式宣告。

///|
pub extend Trop with Semiring::{zero, one, plus, times, is_zero, is_one}

///|
/// 0.10 起 `impl` 不再自動把方法提升為一般方法；這裡顯式宣告。

///|
pub extend Trop with IdempotentSemiring::{le}

///|
/// 0.10 起 `impl` 不再自動把方法提升為一般方法；這裡顯式宣告。

///|
pub extend Trop with StarSemiring::{star}

///|
/// 0.10 起 `impl` 不再自動把方法提升為一般方法；這裡顯式宣告。

///|
pub extend Trop with GroupElement::{group_inv, order_bound, group_id}

///|
/// 0.10 起 `impl` 不再自動把方法提升為一般方法；這裡顯式宣告。

///|
pub extend TropMax with Show::{output, to_string}

///|
/// 0.10 起 `impl` 不再自動把方法提升為一般方法；這裡顯式宣告。

///|
pub extend TropMax with Semiring::{zero, one, plus, times, is_zero, is_one}

///|
/// 0.10 起 `impl` 不再自動把方法提升為一般方法；這裡顯式宣告。

///|
pub extend TropMax with IdempotentSemiring::{le}

///|
/// 0.10 起 `impl` 不再自動把方法提升為一般方法；這裡顯式宣告。

///|
pub extend TropMax with StarSemiring::{star}

///|
/// 0.10 起 `impl` 不再自動把方法提升為一般方法；這裡顯式宣告。

///|
pub extend Bottleneck with Show::{output, to_string}

///|
/// 0.10 起 `impl` 不再自動把方法提升為一般方法；這裡顯式宣告。

///|
pub extend Bottleneck with Semiring::{zero, one, plus, times, is_zero, is_one}

///|
/// 0.10 起 `impl` 不再自動把方法提升為一般方法；這裡顯式宣告。

///|
pub extend Bottleneck with IdempotentSemiring::{le}

///|
/// 0.10 起 `impl` 不再自動把方法提升為一般方法；這裡顯式宣告。

///|
pub extend Bottleneck with OrderedSemiring::{join, meet, top, bottom}

///|
/// 0.10 起 `impl` 不再自動把方法提升為一般方法；這裡顯式宣告。

///|
pub extend Bottleneck with StarSemiring::{star}

///|
/// 0.10 起 `impl` 不再自動把方法提升為一般方法；這裡顯式宣告。

///|
pub extend Counting with Show::{output, to_string}

///|
/// 0.10 起 `impl` 不再自動把方法提升為一般方法；這裡顯式宣告。

///|
pub extend Counting with Semiring::{zero, one, plus, times, is_zero, is_one}

///|
/// 0.10 起 `impl` 不再自動把方法提升為一般方法；這裡顯式宣告。

///|
pub extend Counting with StarSemiring::{star}

///|
/// 0.10 起 `impl` 不再自動把方法提升為一般方法；這裡顯式宣告。

///|
pub extend Prob with Show::{output, to_string}

///|
/// 0.10 起 `impl` 不再自動把方法提升為一般方法；這裡顯式宣告。

///|
pub extend Prob with Semiring::{zero, one, plus, times, is_zero, is_one}

///|
/// 0.10 起 `impl` 不再自動把方法提升為一般方法；這裡顯式宣告。

///|
pub extend BoolSr with Show::{output, to_string}

///|
/// 0.10 起 `impl` 不再自動把方法提升為一般方法；這裡顯式宣告。

///|
pub extend BoolSr with Semiring::{zero, one, plus, times, is_zero, is_one}

///|
/// 0.10 起 `impl` 不再自動把方法提升為一般方法；這裡顯式宣告。

///|
pub extend BoolSr with IdempotentSemiring::{le}

///|
/// 0.10 起 `impl` 不再自動把方法提升為一般方法；這裡顯式宣告。

///|
pub extend BoolSr with StarSemiring::{star}

///|
/// 0.10 起 `impl` 不再自動把方法提升為一般方法；這裡顯式宣告。

///|
pub extend BoolSr with GroupElement::{group_inv, order_bound, group_id}

///|
/// `derive(Eq)` 產生的 impl 同樣需要顯式 extend（0.10 的方法提升規則）。

///|
pub extend BoolSr with Eq::{equal, not_equal}

///|
/// `derive(Eq)` 產生的 impl 同樣需要顯式 extend（0.10 的方法提升規則）。

///|
pub extend Bottleneck with Eq::{equal, not_equal}

///|
/// `derive(Eq)` 產生的 impl 同樣需要顯式 extend（0.10 的方法提升規則）。

///|
pub extend Counting with Eq::{equal, not_equal}

///|
/// `derive(Eq)` 產生的 impl 同樣需要顯式 extend（0.10 的方法提升規則）。

///|
pub extend Prob with Eq::{equal, not_equal}

///|
/// `derive(Eq)` 產生的 impl 同樣需要顯式 extend（0.10 的方法提升規則）。

///|
pub extend Trop with Eq::{equal, not_equal}

///|
/// `derive(Eq)` 產生的 impl 同樣需要顯式 extend（0.10 的方法提升規則）。

///|
pub extend TropMax with Eq::{equal, not_equal}

// ---------------------------------------------------------------------------
// 浮點熱帶半環 (min, +)：Double 權重
//
// 為什麼需要第二個實例：Int32 版本適合「整數網路」（跳數、毫秒、歐幾里得
// 整數距離），但真實的邊權（經度距離、成本、時間）幾乎都是浮點。若把浮點
// 塞進 Int32，誤差會被量化；若改用泛型 min-plus，剪枝就失效（見 DESIGN §2.4）。
// 因此這裡提供 `TropF`：數值域是 Double，+∞ 用 IEEE 的 +inf 表示，
// 於是「不可達」與「很大但有限」在型別層面仍然可區分。
//
// 注意：NaN 不是合法的半環元素。`TropF::of` 把 NaN 正規化成 +∞，
// 這樣「壞輸入」不會靜靜地污染整張距離矩陣（NaN 的比較全為 false，
// 若允許它進來，min/加法都會給出無意義的結果）。
// ---------------------------------------------------------------------------

///|
/// 浮點熱帶半環元素（min-plus，Double 權重）。
pub(all) struct TropF {
  v : Double
}

///|
pub impl Eq for TropF with fn equal(a, b) {
  a.v == b.v
}

///|
pub impl Eq for TropF with fn not_equal(a, b) {
  a.v != b.v
}

///|
pub extend TropF with Eq::{equal, not_equal}

///|
/// 建構：NaN 一律視為 +∞（NaN 破壞全序，不是合法的半環元素）。
pub fn TropF::of(w : Double) -> TropF {
  if w != w {
    { v: @double.infinity, }
  } else {
    { v: w, }
  }
}

///|
/// 取值。
pub fn TropF::value(self : TropF) -> Double {
  self.v
}

///|
/// +∞（半環零元）。
pub fn TropF::inf() -> TropF {
  { v: @double.infinity, }
}

///|
/// 是否為 +∞。
pub fn TropF::is_inf(self : TropF) -> Bool {
  self.v == @double.infinity
}

///|
pub impl Show for TropF with fn output(self, logger) {
  if self.is_inf() {
    logger.write_string("inf")
  } else {
    logger.write_string(self.v.to_string())
  }
}

///|
pub impl Semiring for TropF with fn zero() {
  { v: @double.infinity, }
}

///|
pub impl Semiring for TropF with fn one() {
  { v: 0.0, }
}

///|
/// ⊕ = min。
pub impl Semiring for TropF with fn plus(a, b) {
  if a.v <= b.v {
    a
  } else {
    b
  }
}

///|
/// ⊗ = 加法（+∞ 吸收）。
pub impl Semiring for TropF with fn times(a, b) {
  if a.v == @double.infinity || b.v == @double.infinity {
    { v: @double.infinity, }
  } else {
    { v: a.v + b.v, }
  }
}

///|
pub impl Semiring for TropF with fn is_zero(self) {
  self.v == @double.infinity
}

///|
pub impl Semiring for TropF with fn is_one(self) {
  self.v == 0.0
}

///|
/// 自然序與 `Trop` 一致：x ≤ y ⟺ x ⊕ y = y ⟺ x ≥ y（數值上）。
pub impl IdempotentSemiring for TropF with fn le(a, b) {
  a.v >= b.v
}

///|
/// 星閉：x* = min(0, x, 2x, …)，x ≥ 0 時為 0、x < 0 時不存在（回報 +∞）。
pub impl StarSemiring for TropF with fn star(a) {
  if a.v >= 0.0 {
    { v: 0.0, }
  } else {
    { v: @double.infinity, }
  }
}

///|
/// 可檢查的 star：負權 ⇒ 明確錯誤，而不是一個看起來像答案的 +∞。
pub fn TropF::star_checked(self : TropF) -> Result[TropF, String] {
  if self.v < 0.0 {
    Err("negative cycle: tropical closure diverges (x = \{self.v})")
  } else {
    Ok({ v: 0.0, })
  }
}

///|
pub impl TropicalSemiring for TropF with fn inf() {
  { v: @double.infinity, }
}

///|
pub impl TropicalSemiring for TropF with fn is_inf(self) {
  self.v == @double.infinity
}

///|
pub impl TropicalSemiring for TropF with fn closer(cand, cur) {
  cand.v < cur.v
}

///|
/// `Trop` 也實作同一個熱帶介面，於是矩陣內核只需要一份泛型實作。
pub impl TropicalSemiring for Trop with fn inf() {
  { v: trop_inf, }
}

///|
pub impl TropicalSemiring for Trop with fn is_inf(self) {
  self.v >= trop_inf
}

///|
pub impl TropicalSemiring for Trop with fn closer(cand, cur) {
  cand.v < cur.v
}

///|
pub extend Trop with TropicalSemiring::{closer}

///|
pub extend TropF with Show::{output, to_string}

///|
pub extend TropF with Semiring::{zero, one, plus, times, is_zero, is_one}

///|
pub extend TropF with IdempotentSemiring::{le}

///|
pub extend TropF with StarSemiring::{star}

///|
pub extend TropF with TropicalSemiring::{closer}
