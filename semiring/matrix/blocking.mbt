// ===========================================================================
// 分塊大小的自選：以快取參數推導，而不是硬寫 32
//
// 分塊有兩個不同的「裝得下」條件，混在一起講就會選錯：
//
//   1. **內層磚**：`fw_region` 在 b×b 的子矩陣上做 Θ(b³) 運算，
//      A 磚 + C 磚（同一個 b×b 區塊）必須留在 **L1**，否則每次 ⊕/⊗ 都打 L2。
//          b ≤ sqrt( fill · L1 / (2 · elem) )
//   2. **遞迴切點**：分塊 Kleene 每一步會同時碰 2–3 個子矩陣，
//      這個面板必須留在 **L2**：
//          b ≤ sqrt( fill · L2 / (3 · elem) )
//
// 兩個條件的答案通常差一個數量級（L1 32 KiB vs L2 512 KiB）。
// 把「內層磚」與「遞迴切點」分開，才不會出現「用 L2 算出的 b
// 讓 L1 全 miss」這種看似有道理、實則變慢的設定。
// ===========================================================================

///|
/// 依快取容量與元素大小算出「裝得下」的最大磚邊長（向下取到 8 的倍數）。
///
/// `tiles` 是同時需要留在快取裡的磚數（FW 內層 = 2，分塊乘法 = 3）。
/// 回傳值至少是 8，且不超過 `n`。
pub fn choose_tile(
  cache_bytes : Int32,
  elem_bytes : Int32,
  tiles : Int32,
  n : Int32,
) -> Int32 {
  if tiles < 1 || elem_bytes < 1 || cache_bytes < 1 {
    return 8
  }
  // fill = 3/4：留 25% 給其他資料（索引、堆疊、其他矩陣）
  let budget = cache_bytes * 3 / 4
  let per = tiles * elem_bytes
  let mut b = 8
  // 用整數開方避免浮點誤差：逐步增大直到平方超過預算
  while (b + 8).to_int64() * (b + 8).to_int64() * per.to_int64() <=
        budget.to_int64() {
    b = b + 8
  }
  if b > n {
    // 整個矩陣都裝得下 ⇒ 一個磚就夠（分塊退化為整塊處理）
    n
  } else {
    b
  }
}

///|
/// 內層磚邊長：以 **L1** 為預算（FW 內層需要 2 個磚：當前區塊 + 暫存列）。
pub fn choose_block_l1(
  l1_bytes : Int32,
  elem_bytes : Int32,
  n : Int32,
) -> Int32 {
  choose_tile(l1_bytes, elem_bytes, 2, n)
}

///|
/// 遞迴切點：以 **L2** 為預算（分塊 Kleene 每一步最多 3 個子矩陣同時活著）。
pub fn choose_panel_l2(
  l2_bytes : Int32,
  elem_bytes : Int32,
  n : Int32,
) -> Int32 {
  choose_tile(l2_bytes, elem_bytes, 3, n)
}

///|
/// 典型桌機參數下的預設值（與 sim/cache.mbt 的 `MemHierarchy::typical` 一致）。
pub let default_l1_bytes : Int32 = 32768

///|
pub let default_l2_bytes : Int32 = 524288

///|
/// 分塊乘法：磚邊長由 L1/L2 預算自動選定。
pub fn[E : Semiring] mul_blocked_auto(
  a : Mat[E],
  b : Mat[E],
  l1_bytes~ : Int32 = default_l1_bytes,
  elem_bytes~ : Int32 = 4,
  ops? : Ops,
  probe? : Probe,
) -> Mat[E] {
  let blk = choose_block_l1(
    l1_bytes,
    elem_bytes,
    if a.rows > a.cols {
      a.rows
    } else {
      a.cols
    },
  )
  mul_blocked(a, b, block=blk, ops?, probe?)
}

///|
/// 分塊 Kleene 閉包：遞迴切點由 L1/L2 預算自動選定。
///
/// 切點取 `choose_block_l1`：遞迴終止時呼叫的是 `fw_region`（內層磚），
/// 它才是真正受 L1 限制的部分；L2 決定的是「面板多大時停止遞迴」，
/// 兩者取小值即同時滿足。
pub fn[E : IdempotentSemiring] closure_blocked_auto(
  edges : Mat[E],
  l1_bytes~ : Int32 = default_l1_bytes,
  l2_bytes~ : Int32 = default_l2_bytes,
  elem_bytes~ : Int32 = 4,
  ops? : Ops,
) -> Mat[E] {
  let n = edges.rows
  let b1 = choose_block_l1(l1_bytes, elem_bytes, n)
  let b2 = choose_panel_l2(l2_bytes, elem_bytes, n)
  let cut = if b1 < b2 { b1 } else { b2 }
  closure_blocked(edges, threshold=cut, ops?)
}
