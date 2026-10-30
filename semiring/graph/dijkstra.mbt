// ===========================================================================
// Dijkstra：在「選擇性半環 + 非負權」前提下的 O(m log n) 單源最短路
//
// 定理（Gondran–Minoux）：若半環是**選擇性**的（x ⊕ y ∈ {x,y}，熱帶與
// 瓶頸都是），且所有邊權 ≥ 1_{⊗}（即自然序下非負），則以標籤設定法
// （label-setting, 即 Dijkstra）求得的結果與 Kleene 閉包一致，
// 但只需要 O(m log n) 而非 O(n³)。
//
// 這裡把「非負」做成執行期檢查：發現負邊就明確報錯，而不是給出錯答案。
// ===========================================================================

///|
/// 二元最小堆（(distance, node) 配對；允許重複條目，靠 stale 檢查丟棄）。
pub struct MinHeap {
  d : Array[Int32]
  v : Array[Int32]
}

///|
pub fn MinHeap::new(cap : Int32) -> MinHeap {
  { d: Array(capacity=cap), v: Array(capacity=cap), }
}

///|
pub fn MinHeap::len(self : MinHeap) -> Int32 {
  self.d.length()
}

///|
pub fn MinHeap::push(self : MinHeap, dist : Int32, node : Int32) -> Unit {
  self.d.push(dist)
  self.v.push(node)
  let mut i = self.d.length() - 1
  while i > 0 {
    let p = (i - 1) / 2
    if self.d[p] <= self.d[i] {
      break
    }
    let td = self.d[p]
    let tv = self.v[p]
    self.d[p] = self.d[i]
    self.v[p] = self.v[i]
    self.d[i] = td
    self.v[i] = tv
    i = p
  }
}

///|
/// 彈出最小元素；空堆回傳 None。
pub fn MinHeap::pop(self : MinHeap) -> (Int32, Int32)? {
  let n = self.d.length()
  if n == 0 {
    return None
  }
  let rd = self.d[0]
  let rv = self.v[0]
  let last = n - 1
  self.d[0] = self.d[last]
  self.v[0] = self.v[last]
  self.d.pop() |> ignore
  self.v.pop() |> ignore
  let mut i = 0
  let m = self.d.length()
  while true {
    let l = 2 * i + 1
    let r = l + 1
    let mut best = i
    if l < m && self.d[l] < self.d[best] {
      best = l
    }
    if r < m && self.d[r] < self.d[best] {
      best = r
    }
    if best == i {
      break
    }
    let td = self.d[i]
    let tv = self.v[i]
    self.d[i] = self.d[best]
    self.v[i] = self.v[best]
    self.d[best] = td
    self.v[best] = tv
    i = best
  }
  Some((rd, rv))
}

///|
/// 單源最短路（min-plus）。
///
/// 回傳每個點的距離（`Trop::inf()` 表示不可達）與是否發現負邊
/// （負邊時 Dijkstra 的前提不成立，回傳的 second 為 true）。
pub fn dijkstra(g : Graph, src : Int32) -> (Array[Trop], Bool) {
  let n = g.n
  let dist = Array::make(n, Trop::inf())
  let done = Array::make(n, false)
  dist[src] = Trop::new(0)
  let heap = MinHeap::new(g.edges().min(1024) + 1)
  heap.push(0, src)
  let mut has_negative = false
  while heap.len() > 0 {
    let (d, u) = heap.pop().unwrap()
    if done[u] {
      continue
    }
    if d > dist[u].value() {
      continue // stale
    }
    done[u] = true
    for e in g.offsets[u]..<g.offsets[u + 1] {
      let w = g.w[e]
      if w < 0 {
        has_negative = true
        continue
      }
      let nd = d + w
      if nd < dist[g.to[e]].value() {
        dist[g.to[e]] = Trop::new(nd)
        heap.push(nd, g.to[e])
      }
    }
  }
  (dist, has_negative)
}

///|
/// 全源最短路：對每個點跑一次 Dijkstra，回傳 n×n 矩陣。
pub fn apsp_dijkstra(g : Graph) -> @mat.Mat[Trop] {
  let n = g.n
  let m = @mat.Mat::new(n, n, Trop::inf())
  for s in 0..<n {
    let (dist, _) = dijkstra(g, s)
    for v in 0..<n {
      m.d[s * n + v] = dist[v]
    }
  }
  m
}

///|
/// 單源最寬路徑（瓶頸半環）：最大化「路徑上最小邊權」。
///
/// 同樣的 label-setting 骨架，只是鬆弛改成 max-min。
pub fn widest_path(g : Graph, src : Int32) -> Array[Int32] {
  let n = g.n
  let best = Array::make(n, 0)
  let done = Array::make(n, false)
  best[src] = cap_top()
  let heap = MinHeap::new(g.edges().min(1024) + 1)
  // 以「負容量」放進最小堆，等效於最大堆
  heap.push(-best[src], src)
  while heap.len() > 0 {
    let (nd, u) = heap.pop().unwrap()
    if done[u] {
      continue
    }
    if -nd > best[u] {
      continue
    }
    done[u] = true
    for e in g.offsets[u]..<g.offsets[u + 1] {
      let cap = best[u].min(g.w[e])
      if cap > best[g.to[e]] {
        best[g.to[e]] = cap
        heap.push(-cap, g.to[e])
      }
    }
  }
  best
}

///|
/// 瓶頸半環的 top（無限容量）。
fn cap_top() -> Int32 {
  0x3FFF_FFFF
}
