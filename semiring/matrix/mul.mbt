// ===========================================================================
// 矩陣乘法：三種迴圈順序 + 熱帶特化
//
// 三種變體計算的是**同一個**代數結果（同一個 ⊕/⊗ 的 O(n³) 展開），
// 差別只在記憶體存取順序：
//   naive   (i,j,k)：b 的存取是「行優先」→ 每次內層都踩不同 cache line
//   ikj     (i,k,j)：對 c 的一整行做累加 → b 逐列流式存取
//   blocked          ：分塊後三個矩陣都在 L1/L2 預算內重用
// 因此 op 數完全相同、memory traffic 不同——這正是本庫要量測的對象。
// ===========================================================================

///|
/// (i,j,k) 迴圈：教科書版本，b 的存取 strided。
pub fn[E : Semiring] mul_naive(
  a : Mat[E],
  b : Mat[E],
  ops? : Ops,
  probe? : Probe,
) -> Mat[E] {
  if a.cols != b.rows {
    abort("mul_naive: shape mismatch")
  }
  let n = a.rows
  let k_len = a.cols
  let m = b.cols
  let c = Mat::new(n, m, Semiring::zero())
  for i in 0..<n {
    for j in 0..<m {
      let mut acc = Semiring::zero()
      for k in 0..<k_len {
        let x = rd(a, 0, i, k, probe)
        let y = rd(b, 1, k, j, probe)
        acc = Semiring::plus(acc, Semiring::times(x, y))
        if ops is Some(o) {
          o.record_plus()
          o.record_times()
        }
      }
      wr(c, 2, i, j, acc, probe)
    }
  }
  c
}

///|
/// (i,k,j) 迴圈：c 的一行留在暫存器，b 逐列流式讀取。
pub fn[E : Semiring] mul_ikj(
  a : Mat[E],
  b : Mat[E],
  ops? : Ops,
  probe? : Probe,
) -> Mat[E] {
  if a.cols != b.rows {
    abort("mul_ikj: shape mismatch")
  }
  let n = a.rows
  let k_len = a.cols
  let m = b.cols
  let c = Mat::new(n, m, Semiring::zero())
  for i in 0..<n {
    for k in 0..<k_len {
      let x = rd(a, 0, i, k, probe)
      for j in 0..<m {
        let y = rd(b, 1, k, j, probe)
        let cur = rd(c, 2, i, j, probe)
        wr(c, 2, i, j, Semiring::plus(cur, Semiring::times(x, y)), probe)
        if ops is Some(o) {
          o.record_plus()
          o.record_times()
        }
      }
    }
  }
  c
}

///|
/// 分塊 (i,k,j)：以 `block` 為邊長切磚，使 A/B/C 的當前磚都能留在快取內。
pub fn[E : Semiring] mul_blocked(
  a : Mat[E],
  b : Mat[E],
  block~ : Int32,
  ops? : Ops,
  probe? : Probe,
) -> Mat[E] {
  if a.cols != b.rows {
    abort("mul_blocked: shape mismatch")
  }
  let n = a.rows
  let k_len = a.cols
  let m = b.cols
  let bs = if block < 1 { 1 } else { block }
  let c = Mat::new(n, m, Semiring::zero())
  let mut k0 = 0
  while k0 < k_len {
    let k1 = (k0 + bs).min(k_len)
    let mut i0 = 0
    while i0 < n {
      let i1 = (i0 + bs).min(n)
      let mut j0 = 0
      while j0 < m {
        let j1 = (j0 + bs).min(m)
        for i in i0..<i1 {
          for k in k0..<k1 {
            let x = rd(a, 0, i, k, probe)
            for j in j0..<j1 {
              let y = rd(b, 1, k, j, probe)
              let cur = rd(c, 2, i, j, probe)
              wr(c, 2, i, j, Semiring::plus(cur, Semiring::times(x, y)), probe)
              if ops is Some(o) {
                o.record_plus()
                o.record_times()
              }
            }
          }
        }
        j0 = j1
      }
      i0 = i1
    }
    k0 = k1
  }
  c
}

// ---------------------------------------------------------------------------
// 熱帶（min,+）特化：以「單調性剪枝」真正減少運算量
// ---------------------------------------------------------------------------

///|
/// min-plus 矩陣乘法的剪枝版，泛型於任何 `TropicalSemiring`
/// （Int32 的 `Trop` 與 Double 的 `TropF` 共用同一份內核）。
///
/// 定理（docs/DESIGN.md §2.4）：若 b 的所有元素 ≥ 0（即 ≥ ⊗ 單位元），
/// 則 a[i][k] + b[k][j] ≥ a[i][k]。因此：
///   * a[i][k] = +∞  ⇒ 整個 k 列可跳過（省 m 次 ⊗）
///   * c[i][j] ≤ a[i][k] ⇒ 該 (i,j) 不必更新（省一次 ⊗）
/// 兩者都不改變結果，只減少實際發生的運算量。
///
/// 剪枝用 `closer`（嚴格更近）表達，因此不必把權重轉成浮點來比較：
/// Int32 熱帶半環仍然是整數運算，Double 版本則是浮點運算。
pub fn[E : TropicalSemiring] mul_trop_generic(
  a : Mat[E],
  b : Mat[E],
  ops? : Ops,
) -> Mat[E] {
  if a.cols != b.rows {
    abort("mul_trop_generic: shape mismatch")
  }
  let n = a.rows
  let k_len = a.cols
  let m = b.cols
  let c = Mat::new(n, m, TropicalSemiring::inf())
  for i in 0..<n {
    let arow = i * m
    for k in 0..<k_len {
      let x = a.d[i * k_len + k]
      if TropicalSemiring::is_inf(x) {
        continue
      }
      let brow = k * m
      for j in 0..<m {
        let y = b.d[brow + j]
        if TropicalSemiring::is_inf(y) {
          continue
        }
        let cand = Semiring::times(x, y)
        let cur = c.d[arow + j]
        if TropicalSemiring::closer(cand, cur) {
          c.d[arow + j] = cand
        }
        if ops is Some(o) {
          o.record_plus()
          o.record_times()
        }
      }
    }
  }
  c
}

///|
/// Int32 權重的 min-plus 乘法（`Trop` 的專用入口，等於 `mul_trop_generic`）。
pub fn mul_trop(a : Mat[Trop], b : Mat[Trop], ops? : Ops) -> Mat[Trop] {
  mul_trop_generic(a, b, ops?)
}

///|
/// 對照組：不做剪枝的 min-plus（每個元素都完整計算），用於量測剪枝的收益。
pub fn mul_trop_plain(a : Mat[Trop], b : Mat[Trop], ops? : Ops) -> Mat[Trop] {
  if a.cols != b.rows {
    abort("mul_trop_plain: shape mismatch")
  }
  let n = a.rows
  let k_len = a.cols
  let m = b.cols
  let c = Mat::new(n, m, Trop::inf())
  for i in 0..<n {
    for k in 0..<k_len {
      let x = a.d[i * k_len + k]
      for j in 0..<m {
        let y = b.d[k * m + j]
        let s = Trop::times(x, y)
        let cur = c.d[i * m + j]
        c.d[i * m + j] = Trop::plus(cur, s)
        if ops is Some(o) {
          o.record_plus()
          o.record_times()
        }
      }
    }
  }
  c
}

// ---------------------------------------------------------------------------
// 區塊（子矩陣）乘法：供分塊 closure 使用
// ---------------------------------------------------------------------------

///|
/// 在 `m` 的兩個子區塊上做 n×n 乘法，結果寫到 `dst`（獨立的 n×n 緩衝）。
///
/// 這是分塊 Kleene 閉包的內核：所有索引都被限制在 n×n 的子方塊內，
/// 因此遞迴深度增加時工作集反而縮小。
pub fn[E : Semiring] mul_region(
  m : Mat[E],
  ar : Int32,
  ac : Int32,
  br : Int32,
  bc : Int32,
  dst : FixedArray[E],
  rows : Int32,
  inner : Int32,
  cols : Int32,
  ops? : Ops,
) -> Unit {
  let width = m.cols
  for i in 0..<rows {
    let arow = (ar + i) * width
    let drow = i * cols
    for j in 0..<cols {
      dst[drow + j] = Semiring::zero()
    }
    for k in 0..<inner {
      let x = m.d[arow + ac + k]
      let brow = (br + k) * width + bc
      for j in 0..<cols {
        let cur = dst[drow + j]
        dst[drow + j] = Semiring::plus(cur, Semiring::times(x, m.d[brow + j]))
        if ops is Some(o) {
          o.record_plus()
          o.record_times()
        }
      }
    }
  }
}

///|
/// 把 n×n 緩衝寫回 `m` 的指定區塊。
pub fn[E] copy_region_in(
  m : Mat[E],
  r : Int32,
  c : Int32,
  src : FixedArray[E],
  rows : Int32,
  cols : Int32,
) -> Unit {
  let width = m.cols
  for i in 0..<rows {
    let mrow = (r + i) * width + c
    let srow = i * cols
    for j in 0..<cols {
      m.d[mrow + j] = src[srow + j]
    }
  }
}

///|
/// 把 `m` 的指定區塊複製到 n×n 緩衝。
pub fn[E] copy_region_out(
  m : Mat[E],
  r : Int32,
  c : Int32,
  dst : FixedArray[E],
  rows : Int32,
  cols : Int32,
) -> Unit {
  let width = m.cols
  for i in 0..<rows {
    let mrow = (r + i) * width + c
    let drow = i * cols
    for j in 0..<cols {
      dst[drow + j] = m.d[mrow + j]
    }
  }
}
