// ===========================================================================
// 稠密矩陣（row-major）
//
// 設計原則：
//   * 元素型別由半環參數決定 ⇒ 同一份程式碼可以是 min-plus、max-min、
//     機率、計數、甚至 Pareto 標籤集。
//   * 沒有隱藏配置：所有演算法都可傳入 `Ops` 計數器與 `probe` 存取探針，
//     讓「複雜度」與「記憶體存取次數」都能被實際量測，而不是估算。
// ===========================================================================

///|
using @alg {
  trait Semiring,
  trait IdempotentSemiring,
  trait StarSemiring,
  trait TropicalSemiring,
  type Trop,
  type Ops,
}

///|
/// 稠密矩陣，row-major 連續儲存。
pub(all) struct Mat[E] {
  rows : Int32
  cols : Int32
  d : FixedArray[E]
}

///|
pub fn[E] Mat::new(rows : Int32, cols : Int32, fill : E) -> Mat[E] {
  { rows, cols, d: FixedArray::make(rows * cols, fill), }
}

///|
pub fn[E : Semiring] Mat::zero(rows : Int32, cols : Int32) -> Mat[E] {
  Mat::new(rows, cols, Semiring::zero())
}

///|
pub fn[E : Semiring] Mat::identity(n : Int32) -> Mat[E] {
  let m = Mat::new(n, n, Semiring::zero())
  for i in 0..<n {
    m.d[i * n + i] = Semiring::one()
  }
  m
}

///|
pub fn[E] Mat::from_flat(
  rows : Int32,
  cols : Int32,
  d : FixedArray[E],
) -> Mat[E] {
  { rows, cols, d, }
}

///|
pub fn[E] Mat::get(self : Mat[E], i : Int32, j : Int32) -> E {
  self.d[i * self.cols + j]
}

///|
pub fn[E] Mat::set(self : Mat[E], i : Int32, j : Int32, v : E) -> Unit {
  self.d[i * self.cols + j] = v
}

///|
pub fn[E] Mat::copy(self : Mat[E]) -> Mat[E] {
  { rows: self.rows, cols: self.cols, d: self.d.copy(), }
}

///|
pub fn[E] Mat::transpose(self : Mat[E]) -> Mat[E] {
  let out = Mat::new(self.cols, self.rows, self.d[0])
  for i in 0..<self.rows {
    for j in 0..<self.cols {
      out.d[j * self.rows + i] = self.d[i * self.cols + j]
    }
  }
  out
}

///|
pub fn[E] Mat::is_square(self : Mat[E]) -> Bool {
  self.rows == self.cols
}

///|
pub fn[E] Mat::byte_size(self : Mat[E]) -> Int32 {
  self.d.length() * 8
}

// ---------------------------------------------------------------------------
// 存取探針（用於快取模擬：量測真實的記憶體存取序列）
// ---------------------------------------------------------------------------

///|
/// 一次元素存取的探針回呼（矩陣 ID, row, col, is_write）。
///
/// 演算法在每一次真正的讀寫時呼叫它，因此快取模擬量到的是
/// **這份程式碼實際發出的存取序列**，不是另外寫的「示意」模型。
/// 矩陣 ID 約定：0 = A、1 = B、2 = C。
pub type Probe = (Int32, Int32, Int32, Bool) -> Unit

///|
/// 元素存取輔助：讀。
fn[E] rd(m : Mat[E], id : Int32, i : Int32, j : Int32, p : Probe?) -> E {
  if p is Some(f) {
    f(id, i, j, false)
  }
  m.d[i * m.cols + j]
}

///|
/// 元素存取輔助：寫。
fn[E] wr(
  m : Mat[E],
  id : Int32,
  i : Int32,
  j : Int32,
  v : E,
  p : Probe?,
) -> Unit {
  if p is Some(f) {
    f(id, i, j, true)
  }
  m.d[i * m.cols + j] = v
}
