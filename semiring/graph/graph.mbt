// ===========================================================================
// 圖的 CSR 表示 + 生成器（可重現）
//
// CSR（compressed sparse row）：`offsets[i]..offsets[i+1]` 為點 i 的出邊，
// 邊的終點與權重分別存在 `to` 與 `w`。這是快取最友善的稀疏格式，
// 也是「降低載入時間 + 降低讀取次數」在資料結構層的體現。
// ===========================================================================

///|
using @alg {type Trop, type Rng, type ParetoSet, type Ops}

///|
/// 有向圖（帶非負整數權重，權重也用於多目標的每一維）。
pub(all) struct Graph {
  n : Int32
  offsets : Array[Int32]
  to : Array[Int32]
  w : Array[Int32]
  w2 : Array[Int32]
}

///|
/// 由邊三元組建 CSR。
pub fn Graph::build(
  n : Int32,
  from : Array[Int32],
  to : Array[Int32],
  w : Array[Int32],
) -> Graph {
  let m = from.length()
  let deg = Array::make(n + 1, 0)
  for i in 0..<m {
    deg[from[i] + 1] = deg[from[i] + 1] + 1
  }
  for i in 0..<n {
    deg[i + 1] = deg[i + 1] + deg[i]
  }
  let offsets = deg.copy()
  let cur = deg.copy()
  let t2 = Array::make(m, 0)
  let w2 = Array::make(m, 0)
  let ww = Array::make(m, 0)
  for i in 0..<m {
    let u = from[i]
    let p = cur[u]
    t2[p] = to[i]
    w2[p] = w[i]
    ww[p] = 0
    cur[u] = p + 1
  }
  { n, offsets, to: t2, w: w2, w2: ww, }
}

///|
pub fn Graph::edges(self : Graph) -> Int32 {
  self.to.length()
}

///|
/// 新增第二維權重（多目標最短路用）。
pub fn Graph::with_second(self : Graph, w2 : Array[Int32]) -> Graph {
  { n: self.n, offsets: self.offsets, to: self.to, w: self.w, w2, }
}

///|
/// 隨機圖：`density`% 的邊機率，權重 [1, maxw]。
pub fn Graph::random(
  rng : Rng,
  n : Int32,
  density : Int32,
  maxw : Int32,
) -> Graph {
  let from : Array[Int32] = []
  let to : Array[Int32] = []
  let w : Array[Int32] = []
  for i in 0..<n {
    for j in 0..<n {
      if i != j && rng.next_int(100) < density {
        from.push(i)
        to.push(j)
        w.push(1 + rng.next_int(maxw))
      }
    }
  }
  Graph::build(n, from, to, w)
}

///|
/// 隨機圖的第二維權重與第一維負相關（產生 nontrivial 的 Pareto 前沿）。
pub fn Graph::random_two(
  rng : Rng,
  n : Int32,
  density : Int32,
  maxw : Int32,
) -> Graph {
  let g = Graph::random(rng, n, density, maxw)
  let w2 = Array::make(g.edges(), 0)
  for e in 0..<g.edges() {
    // 第二維 ≈ maxw + 1 - 第一維，再加一點擾動 ⇒ 兩維互相衝突
    w2[e] = (maxw + 1 - g.w[e]).max(1) + rng.next_int(3)
  }
  g.with_second(w2)
}

///|
/// 邊三元組轉成 min-plus 邊矩陣（對角線為 inf，代表「無自環」）。
pub fn Graph::to_trop_mat(self : Graph) -> @mat.Mat[Trop] {
  let m = @mat.Mat::new(self.n, self.n, Trop::inf())
  for u in 0..<self.n {
    for e in self.offsets[u]..<self.offsets[u + 1] {
      m.d[u * self.n + self.to[e]] = Trop::new(self.w[e])
    }
  }
  m
}
