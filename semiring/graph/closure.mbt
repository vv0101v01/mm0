// ===========================================================================
// 傳遞閉包的三個層級
//
//   1. 一般 Kleene（matrix 套件）：O(n³) 次半環運算，任何封閉半環。
//   2. 位元平行 Warshall：布林半環中 ⊗ = AND，因此 64 個終點可壓進一個
//      UInt64，「或」一列只需 ⌈n/64⌉ 次字運算 ⇒ O(n³/64)。
//      這不是近似：它計算的是**同一個**布林半環閉包（定理 C）。
//   3. 功能圖（每點出度 ≤ 1）：閉包結構是「尾巴 + 環」，可 O(n) 求出。
//
//   定理 C：布林半環的 ⊗ 是 AND，故 M[i][k] ∧ M[k][*] 等價於
//           「若 bit(i,k) 則 row_i |= row_k」，即一次字運算處理 64 個終點。
// ===========================================================================

///|
/// 位元集形式的傳遞閉包。
pub(all) struct BitClosure {
  n : Int32
  ///
  /// 每列 ⌈n/64⌉ 個字，攤平儲存。
  words : Int32
  bits : FixedArray[UInt64]
}

///|
/// 取得第 (i, j) 位元。
pub fn BitClosure::get(self : BitClosure, i : Int32, j : Int32) -> Bool {
  ((self.bits[i * self.words + (j >> 6)] >> (j & 63)) & 1UL) == 1UL
}

///|
/// 第 i 列的可達點數。
pub fn BitClosure::row_count(self : BitClosure, i : Int32) -> Int32 {
  let mut c = 0
  for wd in 0..<self.words {
    let mut x = self.bits[i * self.words + wd]
    while x != 0UL {
      x = x & (x - 1UL)
      c = c + 1
    }
  }
  c
}

///|
/// 位元平行 Warshall：O(n³/64) 字運算。
///
/// 統計回傳實際執行的「列 OR」次數（= n³/64 量級的證據）。
pub fn closure_bitset(g : Graph, row_ops? : @alg.Ops) -> BitClosure {
  let n = g.n
  let words = (n + 63) / 64
  let bits = FixedArray::make(n * words, 0UL)
  for i in 0..<n {
    bits[i * words + (i >> 6)] = bits[i * words + (i >> 6)] | (1UL << (i & 63))
  }
  for u in 0..<n {
    for e in g.offsets[u]..<g.offsets[u + 1] {
      let v = g.to[e]
      bits[u * words + (v >> 6)] = bits[u * words + (v >> 6)] |
        (1UL << (v & 63))
    }
  }
  // Warshall：以 k 為中繼，把所有「reach k」的列 OR 上第 k 列
  for k in 0..<n {
    let kw = k * words
    let kb = k >> 6
    let kbit = 1UL << (k & 63)
    for i in 0..<n {
      if (bits[i * words + kb] & kbit) != 0UL && i != k {
        let iw = i * words
        for wd in 0..<words {
          bits[iw + wd] = bits[iw + wd] | bits[kw + wd]
        }
        if row_ops is Some(o) {
          o.record_plus()
          o.record_plus()
          o.record_plus()
          o.record_plus()
        }
      }
    }
  }
  { n, words, bits, }
}

///|
/// 功能圖（每點出度 ≤ 1）的結構分解，O(n)。
pub(all) struct FunctionalDecomp {
  ///
  /// 每點最終進入的環編號；-1 表示沒有環（純鏈）。
  cycle_id : Array[Int32]
  ///
  /// 到環的距離（在環上為 0）。
  dist_to_cycle : Array[Int32]
  ///
  /// 每個環的長度，以環編號索引。
  cycle_len : Array[Int32]
  ///
  /// 沒有環時，從該點到鏈尾的邊數。
  depth : Array[Int32]
}

///|
/// 以迭代方式（顯式堆疊）求功能圖的環與尾巴，時間 O(n)、額外記憶體 O(n)。
///
/// 這是「完全正則」在圖論上的體現：每個點落入一個有限週期子群（環），
/// 閉包的結構因此可以在線性時間內完整描述，而不需要 O(n³) 的 Warshall。
pub fn functional_decompose(g : Graph) -> FunctionalDecomp {
  let n = g.n
  let state = Array::make(n, 0)
  let cycle_id = Array::make(n, -1)
  let dist_to_cycle = Array::make(n, 0)
  let cycle_len : Array[Int32] = Array(capacity=n)
  let depth = Array::make(n, 0)
  let path = Array(capacity=n)
  let mut n_cycles = 0
  for s in 0..<n {
    if state[s] != 0 {
      continue
    }
    path.clear()
    let mut cur = s
    let mut dead_end = false
    while state[cur] == 0 {
      state[cur] = 1
      path.push(cur)
      if g.offsets[cur + 1] > g.offsets[cur] {
        cur = g.to[g.offsets[cur]]
      } else {
        dead_end = true
        break
      }
    }
    // 是否撞上本輪路徑 ⇒ 找到新環（死路不算環）
    let mut cycle_start = path.length()
    if !dead_end && state[cur] == 1 {
      let mut idx = path.length() - 1
      while idx >= 0 {
        if path[idx] == cur {
          cycle_start = idx
          break
        }
        idx = idx - 1
      }
    }
    if cycle_start < path.length() {
      let cid = n_cycles
      n_cycles = n_cycles + 1
      cycle_len.push(path.length() - cycle_start)
      for t in cycle_start..<path.length() {
        cycle_id[path[t]] = cid
        dist_to_cycle[path[t]] = 0
      }
      // 尾巴：由後往前
      let mut t = cycle_start - 1
      while t >= 0 {
        dist_to_cycle[path[t]] = dist_to_cycle[path[t + 1]] + 1
        cycle_id[path[t]] = cid
        t = t - 1
      }
    } else if cycle_id[cur] >= 0 {
      // 尾巴併入「已解析」的環：距離 = 錨點距離 + 1
      let cid = cycle_id[cur]
      let mut d = dist_to_cycle[cur] + 1
      let mut t = path.length() - 1
      while t >= 0 {
        cycle_id[path[t]] = cid
        dist_to_cycle[path[t]] = d
        d = d + 1
        t = t - 1
      }
    } else {
      // 純鏈：cur 是「已完成」的節點（距離 +1），或自己就是死路（距離 0）
      let mut d = if dead_end { 0 } else { depth[cur] + 1 }
      let mut t = path.length() - 1
      while t >= 0 {
        depth[path[t]] = d
        d = d + 1
        t = t - 1
      }
    }
    for x in path {
      state[x] = 2
    }
    state[cur] = 2
  }
  { cycle_id, dist_to_cycle, cycle_len, depth, }
}

///|
/// 功能圖中點 v 的可達點數（含自己），O(1)。
pub fn FunctionalDecomp::reach_count(
  self : FunctionalDecomp,
  v : Int32,
) -> Int32 {
  let cid = self.cycle_id[v]
  if cid < 0 {
    self.depth[v] + 1
  } else {
    self.cycle_len[cid] + self.dist_to_cycle[v]
  }
}

///|
/// 熱帶閉包後的負環偵測：對角線 < 0 即存在負環（可達性自反 ⇒ 無窮負）。
pub fn has_negative_cycle(m : @mat.Mat[Trop]) -> Bool {
  for i in 0..<m.rows {
    if m.d[i * m.cols + i].value() < 0 {
      return true
    }
  }
  false
}

///|
/// 由邊矩陣取得 APSP 距離矩陣並檢查負環。
pub fn apsp_kleene(g : Graph) -> (Array[Array[Int32]], Bool) {
  let e = g.to_trop_mat()
  let c = @mat.closure_fw_inplace(e)
  let neg = has_negative_cycle(c)
  let n = g.n
  let out = Array::makei(n, fn(_i) { Array::make(n, 0) })
  for i in 0..<n {
    for j in 0..<n {
      out[i][j] = c.d[i * n + j].value()
    }
  }
  (out, neg)
}
