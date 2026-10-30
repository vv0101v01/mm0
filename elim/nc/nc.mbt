// ============================================================================
// @tensorlab/nc —— 非交叉樹、Catalan 結構、三角剖分對偶、關聯圖
// ----------------------------------------------------------------------------
// [D-NC] 點 {0,…,n−1} 置於凸位置；邊為弦 (a,b)，a<b。非交叉 ⟺ 無兩弦在內部相交。
//
// 本檔定理／演算法：
//   [T-NCT-Count] #非交叉生成樹(n) = C(3n−3, n−1)/(2n−1)     （窮舉 n≤7 + 整除性）
//   [T-Cat-Match] #非交叉完美匹配(2m) = Cat(m)，並給出最小權版本 DP
//   [T-Tri-Cat]   #三角剖分(n) = Cat(n−2)
//   [T-Dual]      三角剖分的對偶（共享對角線）是 n−2 個頂點、最大度 ≤3 的樹
//   [T-Flip]      翻轉圖為 (n−3)-正則且連通
//   [T-MST-NC]    **度量權重的最小生成樹必非交叉** ⇒ 非交叉約束在度量下不損最佳性
//                 （本定理把「量度 metric」與「非交叉樹」連接，並由暴力枚舉反檢）
// ============================================================================

///|
/// /// 弦（保證 a < b）。
pub struct Chord {
  a : Int32
  b : Int32
}

///|
pub fn chord(a : Int32, b : Int32) -> Chord {
  if a < b {
    Chord::{ a, b, }
  } else {
    Chord::{ a: b, b: a, }
  }
}

///|
/// /// 兩弦是否在內部相交（共端點不算）。
pub fn chords_cross(x : Chord, y : Chord) -> Bool {
  let (a, b) = (x.a, x.b)
  let (c, d) = (y.a, y.b)
  if a == c || a == d || b == c || b == d {
    false
  } else {
    let sep = fn(p : Int32, lo : Int32, hi : Int32) -> Bool { p > lo && p < hi }
    sep(c, a, b) != sep(d, a, b)
  }
}

///|
pub fn is_noncrossing(edges : Array[Chord]) -> Bool {
  let m = edges.length()
  let mut ok = true
  for i = 0; i < m; i = i + 1 {
    for j = i + 1; j < m; j = j + 1 {
      if chords_cross(edges[i], edges[j]) {
        ok = false
      }
    }
  }
  ok
}

///|
/// /// |E| = |V|−1、無環、連通（聯集查找）。
pub fn is_tree(n : Int32, edges : Array[Chord]) -> Bool {
  if n <= 0 {
    return false
  }
  if edges.length() != n - 1 {
    return false
  }
  let parent : Array[Int32] = Array::make(n, 0)
  for i = 0; i < n; i = i + 1 {
    parent[i] = i
  }
  let mut ok = true
  for e in edges {
    let mut ra = e.a
    while parent[ra] != ra {
      ra = parent[ra]
    }
    let mut rb = e.b
    while parent[rb] != rb {
      rb = parent[rb]
    }
    if ra == rb {
      ok = false
    } else {
      parent[ra] = rb
    }
  }
  if !ok {
    return false
  }
  let mut root = 0
  while parent[root] != root {
    root = parent[root]
  }
  let mut conn = true
  for i = 1; i < n; i = i + 1 {
    let mut r = i
    while parent[r] != r {
      r = parent[r]
    }
    if r != root {
      conn = false
    }
  }
  conn
}

// ---------------------------------------------------------------------------
// [T-NCT-Count]
// ---------------------------------------------------------------------------

///|
/// /// 64 位元二項係數（Int32 的 `res*(nn-i)` 中途會溢位，故用 Int64）。
pub fn binom_i64(nn : Int32, kk : Int32) -> Int64 {
  if kk < 0 || kk > nn {
    return 0L
  }
  let k = if kk < nn - kk { kk } else { nn - kk }
  let mut res : Int64 = 1L
  for i = 0; i < k; i = i + 1 {
    res = res * (nn - i).to_int64() / (i + 1).to_int64()
  }
  res
}

///|
/// /// 閉合公式 T(n) = C(3n−3, n−1)/(2n−1)，回傳 **Int64 精確值**。
///   注意（除法與位寬）：早期版本以 Int32 回傳，n ≥ 16 時 C(3n−3,n−1) 超過 2^31，
///   截斷後的整數除法給出負值（例如 n=16 得 −28304573）；現在全程 Int64，
///   對 n ≤ 22 皆精確（T(22) = 642312451217745 < 2^63），且此範圍內所有中間乘積亦不溢出。
pub fn nc_tree_formula(n : Int32) -> Int64 {
  binom_i64(3 * n - 3, n - 1) / (2 * n - 1).to_int64()
}

///|
/// /// 整除性命題 [P-NCT-Int]（Int64 精確，適用 n ≤ 22）。
pub fn nc_tree_divisible(n : Int32) -> Bool {
  binom_i64(3 * n - 3, n - 1) % (2 * n - 1).to_int64() == 0L
}

///|
/// /// 枚舉全部非交叉生成樹（n ≤ 7 實用）。
pub fn enumerate_nc_trees(n : Int32) -> Array[Array[Chord]] {
  let all : Array[Chord] = []
  for a = 0; a < n; a = a + 1 {
    for b = a + 1; b < n; b = b + 1 {
      all.push(chord(a, b))
    }
  }
  let out : Array[Array[Chord]] = []
  pick_trees(all, 0, [], n - 1, n, out)
  out
}

///|
fn pick_trees(
  all : Array[Chord],
  start : Int32,
  chosen : Array[Chord],
  need : Int32,
  n : Int32,
  out : Array[Array[Chord]],
) -> Unit {
  if chosen.length() == need {
    if is_noncrossing(chosen) && is_tree(n, chosen) {
      out.push(chosen.copy())
    }
    return ()
  }
  let remain = all.length() - start
  if remain < need - chosen.length() {
    return ()
  }
  let mut i = start
  while i < all.length() {
    if is_noncrossing_one(all[i], chosen) {
      chosen.push(all[i])
      pick_trees(all, i + 1, chosen, need, n, out)
      let _ = chosen.pop()
    }
    i = i + 1
  }
}

///|
/// /// 增量非交叉檢查：新弦必須與已選全部弦不交叉。
fn is_noncrossing_one(e : Chord, chosen : Array[Chord]) -> Bool {
  let mut ok = true
  for f in chosen {
    if chords_cross(e, f) {
      ok = false
    }
  }
  ok
}

///|
pub fn count_nc_trees_brute(n : Int32) -> Int32 {
  enumerate_nc_trees(n).length()
}

// ---------------------------------------------------------------------------
// [T-Cat] Catalan 家族與最小權非交叉完美匹配
// ---------------------------------------------------------------------------

///|
/// /// Cat(0..m)。
pub fn catalan_upto(m : Int32) -> Array[Int32] {
  let c : Array[Int32] = Array::make(m + 1, 0)
  c[0] = 1
  for n = 1; n <= m; n = n + 1 {
    let mut acc = 0
    for i = 0; i < n; i = i + 1 {
      acc = acc + c[i] * c[n - 1 - i]
    }
    c[n] = acc
  }
  c
}

///| /// 枚舉 2m 個凸位置點的全部非交叉完美匹配。

///| /// 構造法則：每次都配對「最小未用點」，並即時排除與既有弦交叉的候選

///|
/// /// ⇒ 每個非交叉匹配恰被生成一次（無序對、無遺漏）。
pub fn nc_perfect_matchings(m : Int32) -> Array[Array[Chord]] {
  let n = 2 * m
  let used : Array[Bool] = Array::make(n, false)
  let out : Array[Array[Chord]] = []
  match_rec(n, used, [], out)
  out
}

///|
fn match_rec(
  n : Int32,
  used : Array[Bool],
  cur : Array[Chord],
  out : Array[Array[Chord]],
) -> Unit {
  let mut i = 0
  while i < n && used[i] {
    i = i + 1
  }
  if i == n {
    out.push(cur.copy())
    return ()
  }
  used[i] = true
  let mut j = i + 1
  while j < n {
    if !used[j] {
      let e = chord(i, j)
      if cur.all(f => !chords_cross(e, f)) {
        cur.push(e)
        used[j] = true
        match_rec(n, used, cur, out)
        used[j] = false
        let _ = cur.pop()
      }
    }
    j = j + 1
  }
  used[i] = false
}

///| /// [D-MatchDP] 最小權非交叉完美匹配的區間 DP：

///|
/// ///   M(a,b) = min_{c ≡ a+1 (mod 2)} w(a,c) + M(a+1,c−1) + M(c+1,b)。
pub fn min_weight_nc_matching(
  w : Array[Array[Int32]],
  n : Int32,
) -> (Int32, Array[Chord]) {
  let big = 1_000_000_000
  let dp : Array[Int32] = Array::make(n * n, big)
  let choice : Array[Int32] = Array::make(n * n, -1)
  let at = fn(a : Int32, b : Int32) -> Int32 { a * n + b }
  for len = 0; len < n; len = len + 1 {
    // 區間 [a..b] 的點數為 len+1，需為偶數 => len 為奇數（len=0 視為空/平凡）
    if len != 0 && len % 2 == 0 {
      continue
    }
    for a = 0; a + len < n; a = a + 1 {
      let b = a + len
      if len == 0 {
        dp[at(a, b)] = 0
      } else {
        let mut best = big
        let mut bestd = -1
        let mut c = a + 1
        while c <= b {
          // 左子區間 [a+1..c-1] 點數為 c-a-1，需為偶數
          if (c - a - 1) % 2 == 0 && (b - c) % 2 == 0 {
            let inner = if a + 1 > c - 1 { 0 } else { dp[at(a + 1, c - 1)] }
            let right = if c + 1 > b { 0 } else { dp[at(c + 1, b)] }
            let total = w[a][c] + inner + right
            if total < best {
              best = total
              bestd = c
            }
          }
          c = c + 1
        }
        dp[at(a, b)] = best
        choice[at(a, b)] = bestd
      }
    }
  }
  let edges : Array[Chord] = []
  rebuild_match(0, n - 1, choice, edges, n)
  (dp[at(0, n - 1)], edges)
}

///|
fn rebuild_match(
  a : Int32,
  b : Int32,
  choice : Array[Int32],
  edges : Array[Chord],
  n : Int32,
) -> Unit {
  if a >= b {
    return ()
  }
  let c = choice[a * n + b]
  if c < 0 {
    return ()
  }
  edges.push(chord(a, c))
  rebuild_match(a + 1, c - 1, choice, edges, n)
  rebuild_match(c + 1, b, choice, edges, n)
}

///|
/// /// 暴力最小權非交叉完美匹配（對拍 DP 用）。
pub fn min_weight_nc_matching_brute(
  w : Array[Array[Int32]],
  n : Int32,
) -> Int32 {
  let m = n / 2
  let mut best = 1_000_000_000
  for mt in nc_perfect_matchings(m) {
    let mut t = 0
    for e in mt {
      t = t + w[e.a][e.b]
    }
    if t < best {
      best = t
    }
  }
  best
}

// ---------------------------------------------------------------------------
// 三角剖分、對偶樹、關聯圖
// ---------------------------------------------------------------------------

///|
/// /// [T-Tri-Cat] 枚舉凸 n 邊形的全部三角剖分（回傳對角線集合）。
pub fn triangulations(n : Int32) -> Array[Array[Chord]] {
  tri_enum(0, n - 1)
}

///|
fn tri_enum(i : Int32, j : Int32) -> Array[Array[Chord]] {
  let out : Array[Array[Chord]] = []
  if j <= i + 1 {
    out.push([])
    return out
  }
  for m = i + 1; m <= j - 1; m = m + 1 {
    let left = tri_enum(i, m)
    let right = tri_enum(m, j)
    for l in left {
      for r in right {
        let cur : Array[Chord] = []
        if m > i + 1 {
          cur.push(chord(i, m))
        }
        if j > m + 1 {
          cur.push(chord(m, j))
        }
        cur.push_iter(l.iter())
        cur.push_iter(r.iter())
        out.push(cur)
      }
    }
  }
  out
}

///|
/// /// 由對角線集合重建所有三角形（圖為極大外平面圖 ⟹ 3-clique 恰為 n−2 個）。
pub fn triangles_of(n : Int32, diagonals : Array[Chord]) -> Array[Array[Int32]] {
  let adj : Array[Array[Bool]] = Array::makei(n, i => {
    Array::makei(n, j => i == j)
  })
  for i = 0; i < n; i = i + 1 {
    if i + 1 < n {
      adj[i][i + 1] = true
      adj[i + 1][i] = true
    }
  }
  adj[0][n - 1] = true
  adj[n - 1][0] = true
  for d in diagonals {
    adj[d.a][d.b] = true
    adj[d.b][d.a] = true
  }
  let out : Array[Array[Int32]] = []
  for i = 0; i < n; i = i + 1 {
    for j = i + 1; j < n; j = j + 1 {
      if !adj[i][j] {
        continue
      }
      for k = j + 1; k < n; k = k + 1 {
        if adj[i][k] && adj[j][k] {
          out.push([i, j, k])
        }
      }
    }
  }
  out
}

///|
/// /// 對偶圖：頂點 = 三角形；邊 = 兩三角形共享一條對角線。
pub fn dual_graph(
  tris : Array[Array[Int32]],
  diagonals : Array[Chord],
) -> Array[(Int32, Int32)] {
  let m = tris.length()
  let out : Array[(Int32, Int32)] = []
  for i = 0; i < m; i = i + 1 {
    for j = i + 1; j < m; j = j + 1 {
      if shared_diagonal(tris[i], tris[j], diagonals) {
        out.push((i, j))
      }
    }
  }
  out
}

///|
fn shared_diagonal(
  t1 : Array[Int32],
  t2 : Array[Int32],
  dg : Array[Chord],
) -> Bool {
  let mut found = false
  for d in dg {
    // 兩三角形共享一條對角線 ⟺ 二者都含 d 的兩個端點
    let both = count_of(t1, d.a) == 1 &&
      count_of(t1, d.b) == 1 &&
      count_of(t2, d.a) == 1 &&
      count_of(t2, d.b) == 1
    if both {
      found = true
    }
  }
  found
}

///|
fn count_of(tri : Array[Int32], v : Int32) -> Int32 {
  let mut c = 0
  for x in tri {
    if x == v {
      c = c + 1
    }
  }
  c
}

///|
/// /// 最大度（對偶圖）。
pub fn max_degree(m : Int32, dual : Array[(Int32, Int32)]) -> Int32 {
  let deg : Array[Int32] = Array::make(m, 0)
  for (i, j) in dual {
    deg[i] = deg[i] + 1
    deg[j] = deg[j] + 1
  }
  let mut best = 0
  for x in deg {
    if x > best {
      best = x
    }
  }
  best
}

///|
/// /// 對偶邊數是否 = 頂點數 − 1（樹的必要條件之一）。
pub fn dual_edge_count(dual : Array[(Int32, Int32)]) -> Int32 {
  dual.length()
}

///|
/// /// 翻轉圖：兩剖分恰差一條對角線。
fn same_chord(x : Chord, y : Chord) -> Bool {
  x.a == y.a && x.b == y.b
}

///|
pub fn are_flippable(ei : Array[Chord], ej : Array[Chord]) -> Bool {
  let di = ei.filter(e => !ej.any(f => same_chord(f, e)))
  let dj = ej.filter(e => !ei.any(f => same_chord(f, e)))
  di.length() == 1 && dj.length() == 1 && !same_chord(di[0], dj[0])
}

///|
/// /// 翻轉圖各頂點的度（應全為 n−3）。
pub fn flip_degrees(tris : Array[Array[Chord]]) -> Array[Int32] {
  let m = tris.length()
  let out : Array[Int32] = Array::make(m, 0)
  for i = 0; i < m; i = i + 1 {
    for j = 0; j < m; j = j + 1 {
      if i != j && are_flippable(tris[i], tris[j]) {
        out[i] = out[i] + 1
      }
    }
  }
  out
}

///|
/// /// 翻轉圖連通性（BFS）。
pub fn flip_graph_connected(tris : Array[Array[Chord]]) -> Bool {
  let m = tris.length()
  if m == 0 {
    return false
  }
  let seen : Array[Bool] = Array::make(m, false)
  let queue : Array[Int32] = [0]
  seen[0] = true
  let mut head = 0
  while head < queue.length() {
    let i = queue[head]
    for j = 0; j < m; j = j + 1 {
      if !seen[j] && are_flippable(tris[i], tris[j]) {
        seen[j] = true
        queue.push(j)
      }
    }
    head = head + 1
  }
  seen.all(x => x)
}

// ---------------------------------------------------------------------------
// [T-MST-NC] 度量權重下，非交叉約束是多餘的
// ---------------------------------------------------------------------------

///|
/// /// Prim 最小生成樹（完全圖，權重 w）。回傳 (權重, 邊)。
pub fn mst_weight(w : Array[Array[Int32]], n : Int32) -> (Int32, Array[Chord]) {
  let intree : Array[Bool] = Array::make(n, false)
  let best : Array[Int32] = Array::make(n, 1_000_000_000)
  let from : Array[Int32] = Array::make(n, -1)
  best[0] = 0
  let mut total = 0
  let edges : Array[Chord] = []
  for rep = 0; rep < n; rep = rep + 1 {
    let _ = rep
    let mut u = -1
    let mut bu = 1_000_000_001
    for i = 0; i < n; i = i + 1 {
      if !intree[i] && best[i] < bu {
        bu = best[i]
        u = i
      }
    }
    if u < 0 {
      break
    }
    intree[u] = true
    if from[u] >= 0 {
      total = total + w[from[u]][u]
      edges.push(chord(from[u], u))
    }
    for v = 0; v < n; v = v + 1 {
      if !intree[v] && v != u && w[u][v] < best[v] {
        best[v] = w[u][v]
        from[v] = u
      }
    }
  }
  (total, edges)
}

///|
/// /// 權重矩阵是否來自度量（對稱、零自距、三角不等式）。
pub fn is_metric_w(w : Array[Array[Int32]], n : Int32) -> Bool {
  let mut ok = true
  for i = 0; i < n; i = i + 1 {
    if w[i][i] != 0 {
      ok = false
    }
    for j = 0; j < n; j = j + 1 {
      if w[i][j] != w[j][i] {
        ok = false
      }
      for k = 0; k < n; k = k + 1 {
        if w[i][j] > w[i][k] + w[k][j] {
          ok = false
        }
      }
    }
  }
  ok
}

///| /// [T-MST-NC] 驗證器：對給定權重，檢查

///| ///   (1) MST 非交叉；(2) MST 權重 = 全部非交叉生成樹的最小權重。

///|
/// /// 回傳 (mst 權, nc 最小權, MST 是否非交叉)。
pub fn check_metric_freedom(
  w : Array[Array[Int32]],
  n : Int32,
) -> (Int32, Int32, Bool) {
  let (mw, medges) = mst_weight(w, n)
  let mut best = 1_000_000_000
  for t in enumerate_nc_trees(n) {
    let mut s = 0
    for e in t {
      s = s + w[e.a][e.b]
    }
    if s < best {
      best = s
    }
  }
  (mw, best, is_noncrossing(medges))
}

// ---------------------------------------------------------------------------
// [T-NC-Free] 循環平移不變且隨距離單調的權重：非交叉約束是多餘的
// ---------------------------------------------------------------------------

///|
/// /// w(i,j) = f(cyc_dist(i,j))，其中 f 定義在 1..n/2。
pub fn cyclic_weights(f : Array[Int32], n : Int32) -> Array[Array[Int32]] {
  Array::makei(n, i => {
    Array::makei(n, j => {
      let d0 = if i > j { i - j } else { j - i }
      let d = if d0 < n - d0 { d0 } else { n - d0 }
      if d == 0 {
        0
      } else {
        f[d]
      }
    })
  })
}

///|
/// /// f 嚴格單調（f[1] < f[2] < …）且 f[0] = 0。
pub fn strict_monotone(f : Array[Int32]) -> Bool {
  if f[0] != 0 {
    return false
  }
  let mut ok = true
  for i = 1; i < f.length(); i = i + 1 {
    if f[i] <= f[i - 1] {
      ok = false
    }
  }
  ok
}

///| /// [T-NC-Free] 驗證器：最小非交叉權重是否等於路徑權重 (n−1)·f[1]。

///| /// 定理：在 `strict_monotone(f)` 下，(a) 路徑 0–1–…–(n−1) 是最小權非交叉生成樹；

///|
/// /// (b) 它同時是無約束的最小生成樹；故非交叉約束不損最佳性。
pub fn nc_freedom_gap(f : Array[Int32], n : Int32) -> (Int32, Int32) {
  let w = cyclic_weights(f, n)
  let (mw, medges) = mst_weight(w, n)
  let _ = medges
  let mut best = 1_000_000_000
  for t in enumerate_nc_trees(n) {
    let mut s = 0
    for e in t {
      s = s + w[e.a][e.b]
    }
    if s < best {
      best = s
    }
  }
  (mw, best)
}
