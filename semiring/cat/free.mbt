// ===========================================================================
// 範疇化 II：圖的自由範疇 = ℕ 半環上的 Kleene 星
//
// 取一個有向圖 G（視為「生成態射」的集合）。它生成的**自由範疇**：
//   物件  = 頂點
//   態射  = 路徑（含每個頂點上的長度 0 路徑）
//   合成  = 路徑串接
//
// 定理（本檔要驗的就是它）：對 DAG，
//   |Hom_G(i,j)| = (I ⊕ A ⊕ A² ⊕ … ⊕ A^(n−1))[i][j]
// 右邊正是 ℕ 半環（`Counting`）上鄰接矩陣的 Kleene 星 A*。
//
// 所以「自由範疇」與「半環閉包」是同一個東西的兩種語言。這件事可執行的地方在於：
// 同一個數字有四條互不相依的算法可以算出來，四條必須一致——
//   1. 直接列舉路徑（真正把 Hom 集合建出來，範疇側）
//   2. 拓撲 DP（路徑計數，圖側）
//   3. 矩陣冪級數 I + A + … + A^(n−1)（線性代數側）
//   4. Lehmann 消去 / Kleene 星（半環側，matrix/star.mbt）
//
// 這也是本庫「結構嵌套」主張最具體的一處：圖論、線性代數、範疇論、
// 半環代數在這裡指的是同一個計算。
// ===========================================================================

///|
/// 有向圖（無權）。`adj[u]` 是 u 的出邊目標。
pub(all) struct DiGraph {
  n : Int32
  adj : Array[Array[Int32]]
}

///|
pub fn DiGraph::new(n : Int32) -> DiGraph {
  let adj : Array[Array[Int32]] = []
  for _ in 0..<n {
    adj.push([])
  }
  { n, adj, }
}

///|
pub fn DiGraph::edge(self : DiGraph, u : Int32, v : Int32) -> Unit {
  self.adj[u].push(v)
}

///|
pub fn DiGraph::edge_count(self : DiGraph) -> Int32 {
  let mut m = 0
  for u in self.adj {
    m = m + u.length()
  }
  m
}

///|
/// 是否有環（三色 DFS）。自由範疇在無環時才有限。
pub fn DiGraph::is_dag(self : DiGraph) -> Bool {
  let color : Array[Int32] = Array::make(self.n, 0)
  let mut ok = true
  for s in 0..<self.n {
    if color[s] == 0 {
      if !dfs_dag(self, s, color) {
        ok = false
      }
    }
  }
  ok
}

///|
fn dfs_dag(g : DiGraph, u : Int32, color : Array[Int32]) -> Bool {
  color[u] = 1
  let mut ok = true
  for v in g.adj[u] {
    if color[v] == 1 {
      ok = false
    } else if color[v] == 0 {
      if !dfs_dag(g, v, color) {
        ok = false
      }
    }
  }
  color[u] = 2
  ok
}

///|
/// 拓撲排序（Kahn）。非 DAG 回傳空陣列。
pub fn DiGraph::topo_order(self : DiGraph) -> Array[Int32] {
  let indeg : Array[Int32] = Array::make(self.n, 0)
  for u in 0..<self.n {
    for v in self.adj[u] {
      indeg[v] = indeg[v] + 1
    }
  }
  let q : Array[Int32] = []
  for u in 0..<self.n {
    if indeg[u] == 0 {
      q.push(u)
    }
  }
  let order : Array[Int32] = []
  let mut head = 0
  while head < q.length() {
    let u = q[head]
    order.push(u)
    for v in self.adj[u] {
      indeg[v] = indeg[v] - 1
      if indeg[v] == 0 {
        q.push(v)
      }
    }
    head = head + 1
  }
  if order.length() != self.n {
    []
  } else {
    order
  }
}

///|
/// 路徑數（拓撲 DP）：`cnt[i][j]` = 從 i 到 j 的路徑數（含長度 0）。
///
/// 逆拓撲序計算 `cnt[i][j] = [i=j] + Σ_{(i,k)∈E} cnt[k][j]`。
pub fn DiGraph::path_counts(self : DiGraph) -> Array[Array[Int64]] {
  let n = self.n
  let order = self.topo_order()
  let cnt : Array[Array[Int64]] = []
  for _ in 0..<n {
    cnt.push(Array::make(n, 0L))
  }
  if order.length() != n {
    return cnt
  }
  // 逆拓撲序：先算「後面」的點
  let mut k = n - 1
  while k >= 0 {
    let i = order[k]
    cnt[i][i] = cnt[i][i] + 1L
    for j in 0..<n {
      let mut s = cnt[i][j]
      for v in self.adj[i] {
        s = s + cnt[v][j]
      }
      cnt[i][j] = s
    }
    k = k - 1
  }
  cnt
}

///|
/// 自由範疇的 Hom 集合：`out[i][j]` 是所有從 i 到 j 的路徑（每條是頂點序列）。
///
/// 直接列舉（指數成長），只用於小圖——但它是**真正的見證**，
/// 讓「基數」不是算出來的數字，而是數出來的元素個數。
pub fn DiGraph::hom_sets(self : DiGraph) -> Array[Array[Array[Array[Int32]]]] {
  let n = self.n
  let out : Array[Array[Array[Array[Int32]]]] = []
  for i in 0..<n {
    let row : Array[Array[Array[Int32]]] = []
    for j in 0..<n {
      row.push(paths(self, i, j))
    }
    out.push(row)
  }
  out
}

///|
/// 從 i 到 j 的所有路徑（遞迴列舉；DAG 保證終止）。
fn paths(g : DiGraph, i : Int32, j : Int32) -> Array[Array[Int32]] {
  let out : Array[Array[Int32]] = []
  if i == j {
    out.push([i])
  }
  for v in g.adj[i] {
    for rest in paths(g, v, j) {
      let p : Array[Int32] = [i]
      for x in rest {
        p.push(x)
      }
      out.push(p)
    }
  }
  out
}

///|
/// 自由範疇的 Hom 集合數（以 `SetMat` 儲存見證）。
pub fn DiGraph::hom_setmat(self : DiGraph) -> SetMat {
  let n = self.n
  let out = SetMat::new(n, n)
  for i in 0..<n {
    for j in 0..<n {
      for p in paths(self, i, j) {
        out.add(i, j, p)
      }
    }
  }
  out
}

///|
/// 鄰接矩陣（`Counting`）。
pub fn DiGraph::adjacency(self : DiGraph) -> @mat.Mat[@alg.Counting] {
  let m = @mat.Mat::zero(self.n, self.n)
  for u in 0..<self.n {
    for v in self.adj[u] {
      m.set(u, v, @alg.Counting::new(1L))
    }
  }
  m
}

///|
/// 路線 3：矩陣冪級數 `I ⊕ A ⊕ A² ⊕ … ⊕ A^(n−1)`（DAG 上 A^n = 0）。
pub fn DiGraph::path_counts_by_powers(self : DiGraph) -> Array[Array[Int64]] {
  let n = self.n
  let a = self.adjacency()
  let mut acc = @mat.Mat::identity(n)
  let mut power = @mat.Mat::identity(n)
  for _ in 0..<(n - 1) {
    power = @mat.mul_ikj(power, a)
    acc = @mat.mat_plus(acc, power)
  }
  let out : Array[Array[Int64]] = []
  for i in 0..<n {
    let row : Array[Int64] = []
    for j in 0..<n {
      row.push(acc.get(i, j).value())
    }
    out.push(row)
  }
  out
}

///|
/// 路線 4：Lehmann 消去（半環側的 Kleene 星）。
pub fn DiGraph::path_counts_by_closure(self : DiGraph) -> Array[Array[Int64]] {
  let n = self.n
  let a = self.adjacency()
  let cl = @mat.closure_lehmann(a)
  let out : Array[Array[Int64]] = []
  for i in 0..<n {
    let row : Array[Int64] = []
    for j in 0..<n {
      row.push(cl.get(i, j).value())
    }
    out.push(row)
  }
  out
}
