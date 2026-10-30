///|
/// # Graph — 數學結構圖
///
/// 簡單無向圖：排序鄰接表（走訪用）+ 鄰接位向量行（O(1) 邊查詢、O(n/64) 交集）。
/// 「數學結構」在此以圖編碼：節點 = 對象/運算，邊 = 關係/態射。
/// 後續的自同構群、群作用、軌道折疊、規範形式皆作用於此結構。

///|
/// 簡單無向圖。
pub(all) struct Graph {
  n : Int32
  m : Int32
  adj : Array[Array[Int32]]
  rows : Array[BitVec]
}

///|
/// 由邊列表建構（無向；自動去重、忽略自環；會驗證端點範圍）。
pub fn Graph::from_edges(n : Int32, edges : Array[(Int32, Int32)]) -> Graph {
  guard n >= 0 else { abort("Graph::from_edges: negative order") }
  let adj : Array[Array[Int32]] = Array::make(n, [])
  for i in 0..<n {
    adj[i] = []
  }
  let seen = Array::make(n * n, false)
  let mut m = 0
  for e in edges {
    let (u, v) = e
    guard u >= 0 && u < n && v >= 0 && v < n else {
      abort("Graph::from_edges: endpoint out of range")
    }
    if u != v {
      let a = if u < v { u } else { v }
      let b = if u < v { v } else { u }
      if !seen[a * n + b] {
        seen[a * n + b] = true
        adj[u].push(v)
        adj[v].push(u)
        m = m + 1
      }
    }
  }
  Graph::build(n, m, adj)
}

///|
/// 內部建構：排序鄰接表並建立位向量行。
pub fn Graph::build(n : Int32, m : Int32, adj : Array[Array[Int32]]) -> Graph {
  for i in 0..<n {
    adj[i].sort()
  }
  let rows = Array::make(n, BitVec::make(0))
  for i in 0..<n {
    let bv = BitVec::make(n)
    for v in adj[i] {
      bv.set(v)
    }
    rows[i] = bv
  }
  { n, m, adj, rows, }
}

///|
/// n 個孤立點。
pub fn Graph::empty(n : Int32) -> Graph {
  Graph::from_edges(n, [])
}

///|
/// 路徑 P_n。
pub fn Graph::path(n : Int32) -> Graph {
  guard n >= 0 else { abort("Graph::path: negative order") }
  let edges : Array[(Int32, Int32)] = []
  for i in 0..<(n - 1) {
    edges.push((i, i + 1))
  }
  Graph::from_edges(n, edges)
}

///|
/// 圈 C_n。
pub fn Graph::cycle(n : Int32) -> Graph {
  guard n >= 3 else { abort("Graph::cycle: need n >= 3") }
  let edges : Array[(Int32, Int32)] = []
  for i in 0..<n {
    edges.push((i, (i + 1) % n))
  }
  Graph::from_edges(n, edges)
}

///|
/// 完全圖 K_n。
pub fn Graph::complete(n : Int32) -> Graph {
  guard n >= 0 else { abort("Graph::complete: negative order") }
  let edges : Array[(Int32, Int32)] = []
  for i in 0..<n {
    for j in (i + 1)..<n {
      edges.push((i, j))
    }
  }
  Graph::from_edges(n, edges)
}

///|
/// 完全二部圖 K_{a,b}（左 {0..a-1}，右 {a..a+b-1}）。
pub fn Graph::complete_bipartite(a : Int32, b : Int32) -> Graph {
  guard a >= 0 && b >= 0 else {
    abort("Graph::complete_bipartite: negative part")
  }
  let edges : Array[(Int32, Int32)] = []
  for i in 0..<a {
    for j in 0..<b {
      edges.push((i, a + j))
    }
  }
  Graph::from_edges(a + b, edges)
}

///|
/// 星 K_{1,n}。
pub fn Graph::star(n : Int32) -> Graph {
  guard n >= 1 else { abort("Graph::star: need n >= 1") }
  let edges : Array[(Int32, Int32)] = []
  for i in 1..<=n {
    edges.push((0, i))
  }
  Graph::from_edges(n + 1, edges)
}

///|
/// k 維超方體 Q_k（2^k 個頂點）。
pub fn Graph::hypercube(k : Int32) -> Graph {
  guard k >= 0 && k <= 16 else { abort("Graph::hypercube: need 0 <= k <= 16") }
  let n = 1 << k
  let edges : Array[(Int32, Int32)] = []
  for v in 0..<n {
    for b in 0..<k {
      let u = v ^ (1 << b)
      if v < u {
        edges.push((v, u))
      }
    }
  }
  Graph::from_edges(n, edges)
}

///|
/// Petersen 圖（|Aut| = 120，經典測試樣本）。
pub fn Graph::petersen() -> Graph {
  let edges : Array[(Int32, Int32)] = []
  // 外五邊形 0..4，內五角星 5..9
  for i in 0..<5 {
    edges.push((i, (i + 1) % 5))
    edges.push((5 + i, 5 + (i + 2) % 5))
    edges.push((i, 5 + i))
  }
  Graph::from_edges(10, edges)
}

///|
/// 空圖上的完全圖補圖（即 n 孤立點之補 = K_n，此處為一般補圖）。
pub fn Graph::complement(self : Graph) -> Graph {
  let edges : Array[(Int32, Int32)] = []
  for i in 0..<self.n {
    for j in (i + 1)..<self.n {
      if !self.has_edge(i, j) {
        edges.push((i, j))
      }
    }
  }
  Graph::from_edges(self.n, edges)
}

///|
/// 頂點數。
pub fn Graph::order(self : Graph) -> Int32 {
  self.n
}

///|
/// 邊數。
pub fn Graph::size(self : Graph) -> Int32 {
  self.m
}

///|
/// 邊查詢 O(1)。
pub fn Graph::has_edge(self : Graph, u : Int32, v : Int32) -> Bool {
  guard u >= 0 && u < self.n && v >= 0 && v < self.n else {
    abort("Graph::has_edge: vertex out of range")
  }
  self.rows[u].get(v)
}

///|
/// 度數。
pub fn Graph::degree(self : Graph, v : Int32) -> Int32 {
  self.adj[v].length()
}

///|
/// 鄰居（遞增排序）。
pub fn Graph::neighbors(self : Graph, v : Int32) -> Array[Int32] {
  self.adj[v]
}

///|
/// 不交併 ⊔：把若干圖放在一起（頂點編號依次位移），邊集為各分量之並。
/// 這是 `decomp.mbt` 積公式 |Aut(⊔Cᵢ)| = Π(Π|Aut(Cᵢ)|^{mᵢ}·mᵢ!) 之**逆操作**，
/// 也是測試/基準/演示建構多分量實例之共用入口
/// （去債：原先三處各有一份 `ext_union` / `bunion` / `funion`）。
pub fn Graph::disjoint_union(gs : Array[Graph]) -> Graph {
  let edges : Array[(Int32, Int32)] = []
  let mut off = 0
  let mut n = 0
  for g in gs {
    n = n + g.order()
    for e in g.edge_list() {
      let (u, v) = e
      edges.push((u + off, v + off))
    }
    off = off + g.order()
  }
  Graph::from_edges(n, edges)
}

///|
/// 全部邊（u < v，按字典序）。
pub fn Graph::edge_list(self : Graph) -> Array[(Int32, Int32)] {
  let out : Array[(Int32, Int32)] = []
  for u in 0..<self.n {
    for v in self.adj[u] {
      if u < v {
        out.push((u, v))
      }
    }
  }
  out
}

///|
/// 排序度數序列（結構不變量，供快速否證同構）。
pub fn Graph::degree_seq(self : Graph) -> Array[Int32] {
  let deg = Array::make(self.n, 0)
  for i in 0..<self.n {
    deg[i] = self.adj[i].length()
  }
  deg.sort()
  deg
}

///|
/// 按置換 σ 重標號：新圖含邊 (σ(u), σ(v)) 當且僅當舊圖含 (u, v)。
/// 用於驗證「規範形式與標號無關」以及自同構群作用。
pub fn Graph::relabel(self : Graph, s : Perm) -> Graph {
  guard s.size() == self.n else { abort("Graph::relabel: size mismatch") }
  let edges : Array[(Int32, Int32)] = []
  for (u, v) in self.edge_list() {
    let a = s.apply(u)
    let b = s.apply(v)
    edges.push(if a < b { (a, b) } else { (b, a) })
  }
  Graph::from_edges(self.n, edges)
}

///|
/// 導出子圖。
pub fn Graph::induced_subgraph(self : Graph, verts : Array[Int32]) -> Graph {
  let idx = Map([])
  for i, v in verts {
    idx.set(v, i)
  }
  let edges : Array[(Int32, Int32)] = []
  for (u, v) in self.edge_list() {
    match (idx.get(u), idx.get(v)) {
      (Some(a), Some(b)) => edges.push((a, b))
      _ => ()
    }
  }
  Graph::from_edges(verts.length(), edges)
}

///|
/// 是否正則圖。
pub fn Graph::is_regular(self : Graph) -> Bool {
  if self.n == 0 {
    return true
  }
  let d = self.adj[0].length()
  for i in 1..<self.n {
    guard self.adj[i].length() == d else { return false }
  }
  true
}

///|
/// 連通分量（頂點集的分割）。
pub fn Graph::components(self : Graph) -> Array[Array[Int32]] {
  let seen = Array::make(self.n, false)
  let out : Array[Array[Int32]] = []
  for s in 0..<self.n {
    if !seen[s] {
      let comp : Array[Int32] = []
      let stack : Array[Int32] = [s]
      seen[s] = true
      while stack.length() > 0 {
        let v = stack.pop().unwrap()
        comp.push(v)
        for u in self.adj[v] {
          if !seen[u] {
            seen[u] = true
            stack.push(u)
          }
        }
      }
      comp.sort()
      out.push(comp)
    }
  }
  out
}

///|
pub impl Show for Graph with fn to_string(self) {
  "Graph(n=\{self.n}, m=\{self.m})"
}

///|
pub extend Graph with Show::{to_string, output}

///|
/// Debug（供 `assert_eq` / `inspect` 之結構化差異顯示；與 Show 同一摘要）。
pub impl Debug for Graph with fn to_repr(self) {
  Repr::literal(self.to_string())
}

///|
pub extend Graph with Debug::{to_repr}

///|
pub impl Eq for Graph with fn equal(self : Graph, other : Graph) -> Bool {
  guard self.n == other.n && self.m == other.m else { return false }
  for i in 0..<self.n {
    guard self.rows[i].equal(other.rows[i]) else { return false }
  }
  true
}

///|
pub extend Graph with Eq::{equal, not_equal}
