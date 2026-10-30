// ===========================================================================
// CSR（壓縮稀疏列）上的半環運算
//
// 稠密矩陣的成本是 n² 記憶體 + n³ 運算；真實的圖卻是 m ≪ n²。
// 這裡把「同一個代數展開」搬到 CSR 上：
//
//   * `csr_mul`        一般半環的 SpGEMM（稀疏 × 稀疏 → 稀疏）
//   * `csr_mul_minplus` 熱帶剪枝版（∞ 直接跳過，min 就地比較）
//   * `csr_sssp`       單源 min-plus（heap-based label setting）
//   * `csr_apsp`       n × sssp
//   * `csr_closure`    稀疏 Floyd–Warshall（Lehmann 消去），O(n·nnz) 級
//
// 關鍵在於「稀疏不是資料結構的花招，而是複雜度類別的交換」：
// n × Dijkstra 是 Θ(n·m log n)，稀疏 FW 是 Θ(n·nnz)，稠密 FW 是 Θ(n³)。
// 三者在報告 §10 用同一張圖做實測對照。
// ===========================================================================

///|
/// 壓縮稀疏列矩陣：`row_ptr[i]..row_ptr[i+1]` 給出第 i 列在 `col`/`val` 中的範圍。
/// 每一列內的欄索引嚴格遞增（canonical form），因此 `get` 是二分搜尋、
/// 兩列合併是線性合併。
pub(all) struct Csr[E] {
  rows : Int32
  cols : Int32
  row_ptr : Array[Int32]
  col : Array[Int32]
  val : Array[E]
}

///|
/// 非零元素個數。
pub fn[E] Csr::nnz(self : Csr[E]) -> Int32 {
  self.col.length()
}

///|
/// 第 i 列的欄索引範圍。
pub fn[E] Csr::row_range(self : Csr[E], i : Int32) -> (Int32, Int32) {
  (self.row_ptr[i], self.row_ptr[i + 1])
}

///|
/// 二分搜尋：在第 i 列找欄 j，回傳位置或 -1。
fn[E] Csr::find_idx(self : Csr[E], i : Int32, j : Int32) -> Int32 {
  let mut lo = self.row_ptr[i]
  let mut hi = self.row_ptr[i + 1] - 1
  while lo <= hi {
    let mid = lo + (hi - lo) / 2
    let c = self.col[mid]
    if c == j {
      return mid
    } else if c < j {
      lo = mid + 1
    } else {
      hi = mid - 1
    }
  }
  -1
}

///|
/// 取元素（不存在 ⇒ `None`，代表半環零元）。
pub fn[E] Csr::get(self : Csr[E], i : Int32, j : Int32) -> E? {
  let p = self.find_idx(i, j)
  if p < 0 {
    None
  } else {
    Some(self.val[p])
  }
}

///|
/// 由三元組建構（欄索引排序、重複項以 ⊕ 合併）。
///
/// 重複項用 ⊕ 合併而不是覆寫：這在半環上是唯一正確的做法
/// （同一條邊被輸入兩次，其值必須是 `v ⊕ v`，對冪等半環是 v，
/// 對計數半環是 2v）。
pub fn[E : Semiring] Csr::from_triplets(
  rows : Int32,
  cols : Int32,
  from_nodes : Array[Int32],
  to_nodes : Array[Int32],
  weights : Array[E],
) -> Csr[E] {
  // 逐列收集、排序、合併
  let out_col : Array[Int32] = []
  let out_val : Array[E] = []
  let row_ptr : Array[Int32] = Array::make(rows + 1, 0)
  let bucket : Array[Array[Int32]] = Array::makei(rows, fn(_i) {
    Array::make(0, 0)
  })
  for p in 0..<from_nodes.length() {
    bucket[from_nodes[p]].push(p)
  }
  for i in 0..<rows {
    let idx = bucket[i]
    // 依欄索引排序（插入排序：單列的邊數通常很小）
    for a in 1..<idx.length() {
      let key = idx[a]
      let mut b = a - 1
      while b >= 0 && to_nodes[idx[b]] > to_nodes[key] {
        idx[b + 1] = idx[b]
        b = b - 1
      }
      idx[b + 1] = key
    }
    for a in 0..<idx.length() {
      let p = idx[a]
      let j = to_nodes[p]
      if out_col.length() > row_ptr[i] && out_col[out_col.length() - 1] == j {
        let last = out_val.length() - 1
        out_val[last] = Semiring::plus(out_val[last], weights[p])
      } else {
        out_col.push(j)
        out_val.push(weights[p])
      }
    }
    row_ptr[i + 1] = out_col.length()
  }
  { rows, cols, row_ptr, col: out_col, val: out_val, }
}

///|
/// 由稠密矩陣建構：丟掉 `is_zero` 的元素。
pub fn[E : Semiring] Csr::from_dense(m : Mat[E]) -> Csr[E] {
  let row_ptr : Array[Int32] = Array::make(m.rows + 1, 0)
  let col : Array[Int32] = []
  let val : Array[E] = []
  for i in 0..<m.rows {
    for j in 0..<m.cols {
      let x = m.d[i * m.cols + j]
      if !Semiring::is_zero(x) {
        col.push(j)
        val.push(x)
      }
    }
    row_ptr[i + 1] = col.length()
  }
  { rows: m.rows, cols: m.cols, row_ptr, col, val, }
}

///|
/// 轉回稠密矩陣。
pub fn[E : Semiring] Csr::to_dense(self : Csr[E]) -> Mat[E] {
  let m = Mat::new(self.rows, self.cols, Semiring::zero())
  for i in 0..<self.rows {
    for p in self.row_ptr[i]..<self.row_ptr[i + 1] {
      m.d[i * self.cols + self.col[p]] = self.val[p]
    }
  }
  m
}

///|
/// 每列的邊數（供成本模型與測試使用）。
pub fn[E] Csr::row_nnz(self : Csr[E], i : Int32) -> Int32 {
  self.row_ptr[i + 1] - self.row_ptr[i]
}

// ---------------------------------------------------------------------------
// SpGEMM：一般半環
// ---------------------------------------------------------------------------

///|
/// 稀疏 × 稀疏（Gustavson / SPA 風格）。
///
/// 對 a 的每一列 i：把 `a[i][k] ⊗ b[k][j]` 累加到一個「稀疏累加器」
/// （稠密陣列 + 時間戳標記 + 碰觸清單）。因為只碰觸真正出現的欄，
/// 工作量是 Θ(Σ_{(i,k)∈a} nnz(b_k))，而不是 Θ(n²) 每列。
///
/// 時間戳讓「清空累加器」變成 O(1)：不需要在每列開頭把 n 個格子歸零。
pub fn[E : Semiring] csr_mul(a : Csr[E], b : Csr[E], ops? : Ops) -> Csr[E] {
  if a.cols != b.rows {
    abort("csr_mul: shape mismatch")
  }
  let acc : Array[E] = Array::make(b.cols, Semiring::zero())
  let mark : Array[Int32] = Array::make(b.cols, -1)
  let touched : Array[Int32] = []
  let row_ptr : Array[Int32] = Array::make(a.rows + 1, 0)
  let out_col : Array[Int32] = []
  let out_val : Array[E] = []
  for i in 0..<a.rows {
    touched.clear()
    for p in a.row_ptr[i]..<a.row_ptr[i + 1] {
      let k = a.col[p]
      let av = a.val[p]
      for q in b.row_ptr[k]..<b.row_ptr[k + 1] {
        let j = b.col[q]
        let prod = Semiring::times(av, b.val[q])
        if mark[j] != i {
          mark[j] = i
          acc[j] = prod
          touched.push(j)
        } else {
          acc[j] = Semiring::plus(acc[j], prod)
        }
        if ops is Some(o) {
          o.record_plus()
          o.record_times()
        }
      }
    }
    // 碰觸清單排序後輸出（維持 canonical form）
    for t in 1..<touched.length() {
      let key = touched[t]
      let mut s = t - 1
      while s >= 0 && touched[s] > key {
        touched[s + 1] = touched[s]
        s = s - 1
      }
      touched[s + 1] = key
    }
    for j in touched {
      let v = acc[j]
      if !Semiring::is_zero(v) {
        out_col.push(j)
        out_val.push(v)
      }
    }
    row_ptr[i + 1] = out_col.length()
  }
  { rows: a.rows, cols: b.cols, row_ptr, col: out_col, val: out_val, }
}

///|
/// 熱帶剪枝版 SpGEMM：∞ 的乘法直接跳過，累加用「嚴格更近」判斷。
///
/// 與稠密 `mul_trop_generic` 是同一個定理（單調性剪枝），
/// 差別在於稀疏情況下「跳過」同時省下記憶體碰觸：一個 ∞ 的 a[i][k]
/// 連 b 的第 k 列都不會讀到。
pub fn[E : TropicalSemiring] csr_mul_minplus(
  a : Csr[E],
  b : Csr[E],
  ops? : Ops,
) -> Csr[E] {
  if a.cols != b.rows {
    abort("csr_mul_minplus: shape mismatch")
  }
  let acc : Array[E] = Array::make(b.cols, TropicalSemiring::inf())
  let mark : Array[Int32] = Array::make(b.cols, -1)
  let touched : Array[Int32] = []
  let row_ptr : Array[Int32] = Array::make(a.rows + 1, 0)
  let out_col : Array[Int32] = []
  let out_val : Array[E] = []
  for i in 0..<a.rows {
    touched.clear()
    for p in a.row_ptr[i]..<a.row_ptr[i + 1] {
      let k = a.col[p]
      let av = a.val[p]
      if TropicalSemiring::is_inf(av) {
        continue
      }
      for q in b.row_ptr[k]..<b.row_ptr[k + 1] {
        let bv = b.val[q]
        if TropicalSemiring::is_inf(bv) {
          continue
        }
        let j = b.col[q]
        let cand = Semiring::times(av, bv)
        if mark[j] != i {
          mark[j] = i
          acc[j] = cand
          touched.push(j)
        } else if TropicalSemiring::closer(cand, acc[j]) {
          acc[j] = cand
        }
        if ops is Some(o) {
          o.record_plus()
          o.record_times()
        }
      }
    }
    for t in 1..<touched.length() {
      let key = touched[t]
      let mut s = t - 1
      while s >= 0 && touched[s] > key {
        touched[s + 1] = touched[s]
        s = s - 1
      }
      touched[s + 1] = key
    }
    for j in touched {
      let v = acc[j]
      if !TropicalSemiring::is_inf(v) {
        out_col.push(j)
        out_val.push(v)
      }
    }
    row_ptr[i + 1] = out_col.length()
  }
  { rows: a.rows, cols: b.cols, row_ptr, col: out_col, val: out_val, }
}

// ---------------------------------------------------------------------------
// 單源 / 全源最短路（min-plus）
// ---------------------------------------------------------------------------

// 以「嚴格更近」排序的二元小根堆：鍵的比較由 `TropicalSemiring::closer`
// 提供，因此同一個堆同時服務 `Trop`（Int32）與 `TropF`（Double）。

///|
fn[E : TropicalSemiring] heap_push(
  keys : Array[E],
  nodes : Array[Int32],
  key : E,
  node : Int32,
) -> Unit {
  keys.push(key)
  nodes.push(node)
  let mut i = keys.length() - 1
  while i > 0 {
    let parent = (i - 1) / 2
    if TropicalSemiring::closer(keys[i], keys[parent]) {
      let tk = keys[i]
      keys[i] = keys[parent]
      keys[parent] = tk
      let tn = nodes[i]
      nodes[i] = nodes[parent]
      nodes[parent] = tn
      i = parent
    } else {
      break
    }
  }
}

///|
fn[E : TropicalSemiring] heap_pop(
  keys : Array[E],
  nodes : Array[Int32],
) -> (E, Int32) {
  let rk = keys[0]
  let rn = nodes[0]
  let last = keys.length() - 1
  keys[0] = keys[last]
  nodes[0] = nodes[last]
  let _ = keys.pop()
  let _ = nodes.pop()
  let n = keys.length()
  let mut i = 0
  while true {
    let l = 2 * i + 1
    let r = 2 * i + 2
    let mut best = i
    if l < n && TropicalSemiring::closer(keys[l], keys[best]) {
      best = l
    }
    if r < n && TropicalSemiring::closer(keys[r], keys[best]) {
      best = r
    }
    if best == i {
      break
    }
    let tk = keys[i]
    keys[i] = keys[best]
    keys[best] = tk
    let tn = nodes[i]
    nodes[i] = nodes[best]
    nodes[best] = tn
    i = best
  }
  (rk, rn)
}

///|
/// 單源最短路（label setting）。前提：非負權重（min-plus 星閉需要 x ≥ 0）。
/// 回傳 `(dist, has_negative)`；若偵測到負權邊則 `has_negative = true`，
/// 呼叫端不應該相信 `dist`。
pub fn[E : TropicalSemiring] csr_sssp(
  g : Csr[E],
  src : Int32,
  ops? : Ops,
) -> (Array[E], Bool) {
  let n = g.rows
  let dist : Array[E] = Array::make(n, TropicalSemiring::inf())
  let done : Array[Bool] = Array::make(n, false)
  let mut has_neg = false
  let hk : Array[E] = []
  let hn : Array[Int32] = []
  dist[src] = Semiring::one()
  heap_push(hk, hn, Semiring::one(), src)
  while hk.length() > 0 {
    let (d, u) = heap_pop(hk, hn)
    if done[u] {
      continue
    }
    done[u] = true
    // 已被更近的值取代 ⇒ 丟棄（lazy deletion）
    if TropicalSemiring::closer(dist[u], d) {
      continue
    }
    for p in g.row_ptr[u]..<g.row_ptr[u + 1] {
      let v = g.col[p]
      let w = g.val[p]
      if TropicalSemiring::is_inf(w) {
        continue
      }
      // 負權：min-plus 的標號法（Dijkstra 型）前提是 w ≥ 0 = ⊗ 單位元
      if TropicalSemiring::closer(w, Semiring::one()) {
        has_neg = true
      }
      let cand = Semiring::times(d, w)
      if TropicalSemiring::closer(cand, dist[v]) {
        dist[v] = cand
        heap_push(hk, hn, cand, v)
      }
      if ops is Some(o) {
        o.record_plus()
        o.record_times()
      }
    }
  }
  (dist, has_neg)
}

///|
/// 全源最短路：n 次單源。Θ(n·(m log n))，只依賴非負權。
pub fn[E : TropicalSemiring] csr_apsp(
  g : Csr[E],
  ops? : Ops,
) -> Array[Array[E]] {
  let n = g.rows
  let out : Array[Array[E]] = Array::make(
    n,
    Array::make(0, TropicalSemiring::inf()),
  )
  for s in 0..<n {
    let (d, _neg) = csr_sssp(g, s, ops?)
    out[s] = d
  }
  out
}

// ---------------------------------------------------------------------------
// 稀疏 Kleene 閉包（Lehmann 消去）
// ---------------------------------------------------------------------------

///|
/// 稀疏 Floyd–Warshall：對 k = 0…n−1 消去頂點 k。
///
/// 與稠密版的差別只有「走訪哪些 (i,j)」：這裡只走訪
/// `{ i : (i,k) 存在 } × { j : (k,j) 存在 }`，因此工作量是
///   Θ( Σ_k indeg(k) · avg_nnz(row) )
/// 而不是 Θ(n³)。在 m ≈ 3n 的圖上這是兩個數量級的差距（見報告 §10）。
///
/// 回傳 `(closure, has_negative)`；`has_negative` 表示某個 d[k][k] < 0，
/// 此時 min-plus 閉包不存在（負環）。
pub fn[E : TropicalSemiring] csr_closure(
  g : Csr[E],
  ops? : Ops,
) -> (Csr[E], Bool) {
  let n = g.rows
  // 可變的列（欄索引遞增）
  let rcol : Array[Array[Int32]] = Array::makei(n, fn(i) {
    let (lo, hi) = (g.row_ptr[i], g.row_ptr[i + 1])
    let out : Array[Int32] = []
    for p in lo..<hi {
      out.push(g.col[p])
    }
    out
  })
  let rval : Array[Array[E]] = Array::makei(n, fn(i) {
    let (lo, hi) = (g.row_ptr[i], g.row_ptr[i + 1])
    let out : Array[E] = []
    for p in lo..<hi {
      out.push(g.val[p])
    }
    out
  })
  let mut has_neg = false
  // 稠密暫存列（供 row k 的快照與 row i 的合併）
  let dk : Array[E] = Array::make(n, TropicalSemiring::inf())
  let dim : Array[Int32] = Array::make(n, -1)
  let dkc : Array[Int32] = []
  let acc : Array[E] = Array::make(n, TropicalSemiring::inf())
  let amark : Array[Int32] = Array::make(n, -1)
  let atouched : Array[Int32] = []
  for k in 0..<n {
    // --- 快照第 k 列，並把對角線換成 star(d[k][k])（Lehmann 第 1 步）---
    dkc.clear()
    for p in 0..<rcol[k].length() {
      let j = rcol[k][p]
      dk[j] = rval[k][p]
      dim[j] = k
      dkc.push(j)
    }
    let dkk = if dim[k] == k { dk[k] } else { TropicalSemiring::inf() }
    let star = if TropicalSemiring::is_inf(dkk) {
      Semiring::one()
    } else if TropicalSemiring::closer(dkk, Semiring::one()) {
      // d[k][k] < 0 ⇒ x* 發散（負環）
      has_neg = true
      TropicalSemiring::inf()
    } else {
      Semiring::one()
    }
    if dim[k] != k {
      dkc.push(k)
    }
    dk[k] = star
    // 第 k 列自身：d[k][j] ← star ⊗ d[k][j]
    for p in 0..<rcol[k].length() {
      let j = rcol[k][p]
      if j != k {
        rval[k][p] = Semiring::times(star, rval[k][p])
      }
    }
    if !TropicalSemiring::is_inf(star) {
      // 確定對角線存在（star 恆有限，除非負環）
      let mut found = false
      for p in 0..<rcol[k].length() {
        if rcol[k][p] == k {
          rval[k][p] = star
          found = true
        }
      }
      if !found {
        // 插入到正確位置
        let cols = rcol[k]
        let vals = rval[k]
        let mut pos = 0
        while pos < cols.length() && cols[pos] < k {
          pos = pos + 1
        }
        cols.insert(pos, k)
        vals.insert(pos, star)
        // 快照也要同步
        dim[k] = k
        dk[k] = star
        let mut has = false
        for t in dkc {
          if t == k {
            has = true
          }
        }
        if !has {
          dkc.push(k)
        }
      }
    }
    // --- 對每個 (i,k) 存在且 i ≠ k：row_i ⊕= (row_i[k] ⊗ row_k) ---
    for i in 0..<n {
      if i == k {
        continue
      }
      // 找 (i,k)
      let cols_i = rcol[i]
      let mut pos = 0
      while pos < cols_i.length() && cols_i[pos] != k {
        pos = pos + 1
      }
      if pos >= cols_i.length() {
        continue
      }
      let aik = rval[i][pos]
      if TropicalSemiring::is_inf(aik) {
        continue
      }
      let base = Semiring::times(aik, star)
      if TropicalSemiring::is_inf(base) {
        continue
      }
      // 把 row i 載入累加器
      atouched.clear()
      for p in 0..<cols_i.length() {
        let j = cols_i[p]
        acc[j] = rval[i][p]
        amark[j] = i
        atouched.push(j)
      }
      // 併入 base ⊗ row k
      for t in 0..<dkc.length() {
        let j = dkc[t]
        let vkj = dk[j]
        if TropicalSemiring::is_inf(vkj) {
          continue
        }
        let cand = Semiring::times(base, vkj)
        if amark[j] != i {
          amark[j] = i
          acc[j] = cand
          atouched.push(j)
        } else if TropicalSemiring::closer(cand, acc[j]) {
          acc[j] = cand
        }
        if ops is Some(o) {
          o.record_plus()
          o.record_times()
        }
      }
      // 排序後寫回（維持 canonical form）
      for t in 1..<atouched.length() {
        let key = atouched[t]
        let mut s = t - 1
        while s >= 0 && atouched[s] > key {
          atouched[s + 1] = atouched[s]
          s = s - 1
        }
        atouched[s + 1] = key
      }
      cols_i.clear()
      rval[i].clear()
      for j in atouched {
        let v = acc[j]
        if !TropicalSemiring::is_inf(v) {
          cols_i.push(j)
          rval[i].push(v)
        }
      }
    }
  }
  // 組回 CSR
  let row_ptr : Array[Int32] = Array::make(n + 1, 0)
  let col : Array[Int32] = []
  let val : Array[E] = []
  for i in 0..<n {
    for p in 0..<rcol[i].length() {
      col.push(rcol[i][p])
      val.push(rval[i][p])
    }
    row_ptr[i + 1] = col.length()
  }
  ({ rows: n, cols: n, row_ptr, col, val, }, has_neg)
}
