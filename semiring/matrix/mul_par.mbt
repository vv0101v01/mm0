// ===========================================================================
// 列區塊平行：把獨立的工作分給後端，結果與序列版本逐位元相同
//
// 平行的正確性條件寫在型別與程式碼結構裡：
//   * `mul_rows_par`：每個 task 只寫自己的列區塊 ⇒ 沒有任何共享寫入；
//   * `closure_fw_par`：每一輪 k 先快照第 k 列，之後所有 i 的更新彼此獨立
//     （正是 Floyd–Warshall 的標準平行化），結果與序列 FW 相同。
//
// 注意：在 MoonBit 0.10.17 上，後端是單執行緒協作式（見 par/par.mbt），
// 所以這兩個函式**不會**因為平行而變快；它們存在是為了
//   (a) 在有真正執行緒後端時可以直接受益（結構已就緒），
//   (b) 讓「資料相依性」變成可檢查的程式碼結構，而不是口頭宣稱。
// ===========================================================================

///|
/// 列區塊平行矩陣乘法：每個 task 負責 `total / chunks` 列。
///
/// 每個區塊內部用 ikj 順序（對 c 的一整列累加），因此單一 task 的
/// 存取行為與 `mul_ikj` 相同；分塊只是把「列」切成互不相交的區段。
pub fn[E : Semiring] mul_rows_par(
  a : Mat[E],
  b : Mat[E],
  chunks : Int32,
  ops? : Ops,
) -> Mat[E] {
  if a.cols != b.rows {
    abort("mul_rows_par: shape mismatch")
  }
  let n = a.rows
  let k_len = a.cols
  let m = b.cols
  let c = Mat::new(n, m, Semiring::zero())
  @par.par_map_chunks(n, chunks, fn(lo, hi) {
    for i in lo..<hi {
      for k in 0..<k_len {
        let x = a.d[i * k_len + k]
        if Semiring::is_zero(x) {
          continue
        }
        let brow = k * m
        let crow = i * m
        for j in 0..<m {
          let y = b.d[brow + j]
          let cur = c.d[crow + j]
          c.d[crow + j] = Semiring::plus(cur, Semiring::times(x, y))
        }
        if ops is Some(o) {
          o.record_plus()
          o.record_times()
        }
      }
    }
  })
  c
}

///|
/// 平行 Floyd–Warshall：每一輪 k 先快照第 k 列/行，再讓所有 i ≠ k 獨立更新。
///
/// 快照是必要的：若不快照，i 的更新可能讀到同輪被別人改過的 `d[k][j]`；
/// 但因為更新只會讓值更小（冪等半環的自然序），讀到「已經更小」的值
/// 仍然是正確的——這正是 `closure_fw_inplace` 依賴的性質。
/// 平行版為了讓結果可重現，明確使用快照，因此與序列版逐位元相同。
pub fn[E : IdempotentSemiring] closure_fw_par(
  edges : Mat[E],
  chunks : Int32,
  ops? : Ops,
) -> Mat[E] {
  if !edges.is_square() {
    abort("closure_fw_par: matrix must be square")
  }
  let n = edges.rows
  let m = edges.copy()
  for i in 0..<n {
    m.d[i * n + i] = Semiring::plus(m.d[i * n + i], Semiring::one())
  }
  let rowk = FixedArray::make(n, Semiring::zero())
  let colk = FixedArray::make(n, Semiring::zero())
  for k in 0..<n {
    // 快照第 k 列與第 k 行
    for j in 0..<n {
      rowk[j] = m.d[k * n + j]
      colk[j] = m.d[j * n + k]
    }
    @par.par_map_chunks(n, chunks, fn(lo, hi) {
      for i in lo..<hi {
        if i == k {
          continue
        }
        let aik = colk[i]
        if Semiring::is_zero(aik) {
          continue
        }
        let crow = i * n
        for j in 0..<n {
          let prod = Semiring::times(aik, rowk[j])
          m.d[crow + j] = Semiring::plus(m.d[crow + j], prod)
          if ops is Some(o) {
            o.record_plus()
            o.record_times()
          }
        }
      }
    })
  }
  m
}
