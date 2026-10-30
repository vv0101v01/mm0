// ===========================================================================
// 代數基礎：半環 / 冪等半環 / 星閉半環 / 格序半環 / 完全正則半環 / 么半群
//
// 這一層只放「結構」與「定律」，不含任何演算法。所有演算法套件都以此為
// 約束（constraint）來源：能在編譯期表達的前提，就不要放到執行期檢查。
// ===========================================================================

///|
/// 半環 (S, ⊕, ⊗, 0, 1)：
///   (S, ⊕, 0) 為交換么半群、(S, ⊗, 1) 為么半群、
///   ⊗ 對 ⊕ 雙邊分配、0 為 ⊗ 的吸收元。
///
/// `Eq` 是上界：半環定律的驗證與 `is_zero` 的預設實作都需要等值判定。
pub(open) trait Semiring: Eq {
  fn zero() -> Self
  fn one() -> Self
  fn plus(Self, Self) -> Self
  fn times(Self, Self) -> Self

  ///|
  /// 0 的判定。預設以 `zero()` 比較；熱路徑型別可覆寫成單一比較。
  fn is_zero(Self) -> Bool = _

  ///|
  /// 1 的判定。
  fn is_one(Self) -> Bool = _
}

///|
impl Semiring with fn is_zero(self) {
  self == Semiring::zero()
}

///|
impl Semiring with fn is_one(self) {
  self == Semiring::one()
}

///|
/// 冪等半環：⊕ 冪等 (x ⊕ x = x)。
///
/// 冪等性不是裝飾：它定義了自然序 (x ≤ y ⟺ x ⊕ y = y)，並且是
/// 「原地 Kleene 迭代合法」的充分條件（見 matrix/star.mbt 的型別約束）。
pub(open) trait IdempotentSemiring: Semiring {
  ///|
  /// 自然序：x ≤ y ⟺ x ⊕ y = y。
  fn le(Self, Self) -> Bool = _
}

///|
impl IdempotentSemiring with fn le(a, b) {
  Semiring::plus(a, b) == b
}

///|
/// 熱帶型半環：具有 +∞ 哨兵（零元）的冪等半環，⊗ 是「加權重」。
///
/// min-plus `(min, +)` 與 max-plus `(max, +)` 都屬於這一族。把「∞ 哨兵」與
/// 「嚴格更近」拉進型別之後，剪枝內核（matrix/mul.mbt 的 `mul_trop_generic`）
/// 就能同時服務 Int32 權重與 Double 權重，而**不需要**把權重轉成浮點來比較。
pub(open) trait TropicalSemiring: IdempotentSemiring {
  ///|
  /// 半環零元（+∞ 或在 max-plus 下的 −∞）。
  fn inf() -> Self

  ///|
  /// 是否為零元（不可達）。
  fn is_inf(Self) -> Bool

  ///|
  /// 嚴格更近：`cand` 是否應該取代 `cur`（min-plus：數值更小；max-plus：數值更大）。
  /// 這是剪枝的唯一判據，語義上等於 `cur ⊕ cand ≠ cur`。
  fn closer(Self, Self) -> Bool
}

///|
/// 星閉半環：帶 Kleene 星運算 x* = 1 ⊕ x ⊕ x² ⊕ …（無窮和）。
///
/// 「完全半環 (complete semiring)」要求任意無窮和存在且⊕ 連續；
/// 在實作層面我們用 `StarSemiring` 表達「star 有定義」，
/// 由各實例自行保證收斂條件（tropical 需無負環、機率需譜半徑 < 1）。
pub(open) trait StarSemiring: Semiring {
  fn star(Self) -> Self
}

///|
/// 格序半環：⊕ 的交（join）與一個額外的 meet 使載體成為格，
/// 且 ⊗ 對 join/meet 皆分配（格序半環）。
///
/// 典型例子：布林半環、瓶頸（widest path）半環、max-min 模糊半環。
pub(open) trait OrderedSemiring: IdempotentSemiring {
  ///|
  /// 格的 join，恆等於 ⊕（由冪等性保證）。
  fn join(Self, Self) -> Self = _

  ///|
  /// 格的 meet。
  fn meet(Self, Self) -> Self = _

  ///|
  /// 格的最大元（top）。
  fn top() -> Self

  ///|
  /// 格的最小元（bottom），恆等於 zero()。
  fn bottom() -> Self = _
}

///|
impl OrderedSemiring with fn join(a, b) {
  Semiring::plus(a, b)
}

///|
impl OrderedSemiring with fn bottom() {
  Semiring::zero()
}

///|
impl OrderedSemiring with fn meet(a, b) {
  if IdempotentSemiring::le(a, b) {
    a
  } else {
    b
  }
}

///|
/// 完全正則元素：每個元素 a 落在一個子群 G_a 中，即存在群逆 a°
/// 使得  a ⊗ a° ⊗ a = a  且  a ⊗ a° = a° ⊗ a = e_a（e_a 為冪等元）。
///
/// `order_bound` 回傳 a 所在子群的階之上界 m（a^m = e_a）。
/// 有了 m，star 只需 O(log m) 次乘法（見 group_star.mbt），
/// 而不需要 O(m) 次冪或無窮次迭代——這就是「完全正則 ⇒ star 可算」。
pub(open) trait GroupElement: Semiring {
  fn group_inv(Self) -> Self
  fn order_bound(Self) -> Int32

  ///|
  /// 子群單位元 e = a ⊗ a°。對全部元素都等於 one() 的半環，
  /// 可覆寫成 `one()` 以節省一次乘法。
  fn group_id(Self) -> Self = _
}

///|
impl GroupElement with fn group_id(a) {
  Semiring::times(a, GroupElement::group_inv(a))
}

// ---------------------------------------------------------------------------
// 么半群（供 monoid / spline / 區間聚合使用）
// ---------------------------------------------------------------------------

///|
/// 么半群 (M, ⊗, e)。
pub(open) trait Monoid: Eq {
  fn empty() -> Self
  fn combine(Self, Self) -> Self
}

///|
/// 交換么半群。
pub(open) trait CommutativeMonoid: Monoid {}

///|
/// 冪等么半群：x ⊗ x = x。
///
/// 這個標記是 sparse table 的型別級前提：只有冪等運算才允許
/// 兩個「重疊」區間合併出正確答案（見 monoid/sparse_table.mbt）。
pub(open) trait IdempotentMonoid: Monoid {}

///|
/// 群（么半群 + 逆元）。Fenwick tree 的更新需要逆元，這是型別級前提
/// （見 monoid/fenwick.mbt）。
pub(open) trait GroupMonoid: Monoid {
  fn invert(Self) -> Self
}

// ---------------------------------------------------------------------------
// 全域運算計數器（用於「操作次數」的實測，不用於熱路徑）
// ---------------------------------------------------------------------------

///|
/// 半環運算計數器：⊕ / ⊗ 的實際呼叫次數。
///
/// 這是「複雜度下降」的可驗證證據來源：同一份程式碼在 native 上執行，
/// 計數器給出的是演算法真正發生的基本運算量，而不是模型估算。
pub struct Ops {
  mut plus : Int64
  mut times : Int64
}

///|
pub fn Ops::new() -> Ops {
  { plus: 0L, times: 0L, }
}

///|
pub fn Ops::record_plus(self : Ops) -> Unit {
  self.plus = self.plus + 1L
}

///|
pub fn Ops::record_times(self : Ops) -> Unit {
  self.times = self.times + 1L
}

///|
pub fn Ops::total(self : Ops) -> Int64 {
  self.plus + self.times
}

///|
pub impl Show for Ops with fn output(self, logger) {
  logger.write_string("plus=\{self.plus}, times=\{self.times}")
}

///|
/// 0.10 起 `impl` 不再自動把方法提升為一般方法；這裡顯式宣告。

///|
pub extend Ops with Show::{output, to_string}
