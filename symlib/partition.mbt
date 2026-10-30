///|
/// # Part — 有序分割與不變量精煉
///
/// 有序分割 = 頂點的一列不交「格」（cell）。精煉（refinement）以鄰接計數簽名
/// 不斷分裂各格，得到等價分割（equitable partition）與正則顏色。
/// 所有精煉算法均為「重標號等變」（equivariant）：重標號後的分割是原分割的
/// 重標號像，故可安全用作同構不變量與搜尋引擎的剪枝依據。

///|
/// 有序分割：`lab` 為按格排列的頂點序列，`ptn[i] = 1` 表示 i 與 i+1 同格，
/// `ptn[i] = 0` 表示格在 i 結束。
pub(all) struct Part {
  n : Int32
  mut lab : Array[Int32]
  mut ptn : Array[Int32]
  mut cell_of : Array[Int32]
}

///|
/// 平凡分割（單一格含全部頂點）。
pub fn Part::trivial(n : Int32) -> Part {
  let lab = Array::make(n, 0)
  let ptn = Array::make(n, 0)
  let cell_of = Array::make(n, 0)
  for i in 0..<n {
    lab[i] = i
    if i < n - 1 {
      ptn[i] = 1
    } else {
      ptn[i] = 0
    }
    cell_of[i] = 0
  }
  { n, lab, ptn, cell_of, }
}

///|
/// 離散分割（每格一點；`order[pos]` 為該位置頂點）。
pub fn Part::discrete(order : Array[Int32]) -> Part {
  let n = order.length()
  let lab = Array::make(n, 0)
  let ptn = Array::make(n, 0)
  let cell_of = Array::make(n, 0)
  for i in 0..<n {
    lab[i] = order[i]
    ptn[i] = 0
    cell_of[order[i]] = i
  }
  { n, lab, ptn, cell_of, }
}

///|
/// 複製。
pub fn Part::copy(self : Part) -> Part {
  {
    n: self.n,
    lab: self.lab.copy(),
    ptn: self.ptn.copy(),
    cell_of: self.cell_of.copy(),
  }
}

///|
/// 格數。
pub fn Part::cell_count(self : Part) -> Int32 {
  let mut c = 0
  for i in 0..<self.n {
    if self.ptn[i] == 0 {
      c = c + 1
    }
  }
  c
}

///|
/// 格大小序列（按格序）。
pub fn Part::cell_sizes(self : Part) -> Array[Int32] {
  let out : Array[Int32] = []
  let mut start = 0
  for i in 0..<self.n {
    if self.ptn[i] == 0 {
      out.push(i - start + 1)
      start = i + 1
    }
  }
  out
}

///|
/// 各格頂點列表。
pub fn Part::cells(self : Part) -> Array[Array[Int32]] {
  let out : Array[Array[Int32]] = []
  let mut cur : Array[Int32] = []
  for i in 0..<self.n {
    cur.push(self.lab[i])
    if self.ptn[i] == 0 {
      out.push(cur)
      cur = []
    }
  }
  out
}

///|
/// 是否離散（每格恰一點）。
pub fn Part::is_discrete(self : Part) -> Bool {
  for i in 0..<self.n {
    guard self.ptn[i] == 0 else { return false }
  }
  true
}

///|
/// 顏色正則精煉（1-維 WL 型）：回傳頂點顏色陣列（按簽名大小排序編號，
/// 與頂點編號無關 → 純不變量）。複雜度 O((n+m)·rounds)。
pub fn refine_colors(g : Graph) -> Array[Int32] {
  let n = g.order()
  guard n > 0 else { return [] }
  // 初始顏色 = 度數
  let mut color = Array::make(n, 0)
  for i in 0..<n {
    color[i] = g.degree(i)
  }
  // 顏色重新編號（等變）
  color = recolor(color)
  let mut changed = true
  while changed {
    changed = false
    // 簽名：(color[v], 各顏色的鄰居計數)
    let k = max_color(color) + 1
    let sig : Array[Array[Int32]] = Array::make(n, [])
    for v in 0..<n {
      let s = Array::make(k + 1, 0)
      s[0] = color[v]
      for u in g.neighbors(v) {
        s[color[u] + 1] = s[color[u] + 1] + 1
      }
      sig[v] = s
    }
    let new_color = recolor_from_sigs(sig)
    for v in 0..<n {
      if new_color[v] != color[v] {
        changed = true
      }
    }
    color = new_color
  }
  color
}

///|
/// 由度數出發重新編號顏色：顏色號 = 簽名排序後的秩（等變）。
fn recolor(color : Array[Int32]) -> Array[Int32] {
  let n = color.length()
  let pairs : Array[(Int32, Int32)] = []
  for i in 0..<n {
    pairs.push((color[i], i))
  }
  pairs.sort_by(fn(a : (Int32, Int32), b : (Int32, Int32)) -> Int32 {
    fst(a).compare(fst(b))
  })
  let sorted = pairs
  let out = Array::make(n, 0)
  let mut rank = -1
  let mut prev = 0 - 1 - 1
  for p in sorted {
    let (c, i) = p
    if c != prev {
      rank = rank + 1
      prev = c
    }
    out[i] = rank
  }
  out
}

///|
/// 由簽名陣列重新編號顏色（等變：按簽名字典序編號）。
fn recolor_from_sigs(sig : Array[Array[Int32]]) -> Array[Int32] {
  let n = sig.length()
  let idx : Array[Int32] = []
  for i in 0..<n {
    idx.push(i)
  }
  idx.sort_by(fn(a : Int32, b : Int32) -> Int32 { cmp_arr(sig[a], sig[b]) })
  let sorted = idx
  let out = Array::make(n, 0)
  let mut rank = -1
  let mut prev : Array[Int32] = []
  let mut has_prev = false
  for i in sorted {
    if !has_prev || cmp_arr(sig[i], prev) != 0 {
      rank = rank + 1
      prev = sig[i]
      has_prev = true
    }
    out[i] = rank
  }
  out
}

///|
/// 整數陣列字典序比較。
pub fn cmp_arr(a : Array[Int32], b : Array[Int32]) -> Int32 {
  let la = a.length()
  let lb = b.length()
  let l = if la < lb { la } else { lb }
  for i in 0..<l {
    guard a[i] == b[i] else { return a[i].compare(b[i]) }
  }
  la.compare(lb)
}

///|
/// 陣列是否字典序小於。
pub fn arr_less(a : Array[Int32], b : Array[Int32]) -> Bool {
  cmp_arr(a, b) < 0
}

///|
/// 最大顏色值。
fn max_color(color : Array[Int32]) -> Int32 {
  let mut m = 0
  for c in color {
    if c > m {
      m = c
    }
  }
  m
}

///|
/// 投影輔助：取二元組第一分量。
fn fst(p : (Int32, Int32)) -> Int32 {
  let (a, _) = p
  a
}

///|
/// 等價分割精煉：以「各顏色鄰居計數向量」為簽名反覆分裂至穩定。
/// 結果為有序分割（格序 = 簽名排序序），可作搜尋引擎的初始狀態。
pub fn refine_equitable(g : Graph, initial : Part) -> Part {
  let n = g.order()
  guard n > 0 else { return initial }
  let mut part = initial.copy()
  let mut changed = true
  while changed {
    changed = false
    let k = part.cell_count()
    // 每點對各格的鄰居計數
    let cnt : Array[Array[Int32]] = Array::make(n, [])
    for v in 0..<n {
      cnt[v] = Array::make(k, 0)
    }
    for v in 0..<n {
      let c = part.cell_of[v]
      for u in g.neighbors(v) {
        cnt[u][c] = cnt[u][c] + 1
      }
    }
    // 每格按簽名 (cell_of, cnt) 分裂
    let new_part = split_cells_by(part, cnt)
    if new_part.cell_count() != k {
      changed = true
    }
    part = new_part
  }
  part
}

///|
/// 按簽名分裂各格（等變：簽名排序編號）。
fn split_cells_by(part : Part, cnt : Array[Array[Int32]]) -> Part {
  let n = part.n
  let new_cells : Array[Array[Int32]] = []
  for cell in part.cells() {
    // 依簽名排序該格
    cell.sort_by(fn(a : Int32, b : Int32) -> Int32 { cmp_arr(cnt[a], cnt[b]) })
    let sorted = cell
    let mut cur : Array[Int32] = [sorted[0]]
    for i in 1..<sorted.length() {
      if cmp_arr(cnt[sorted[i]], cnt[sorted[i - 1]]) != 0 {
        new_cells.push(cur)
        cur = [sorted[i]]
      } else {
        cur.push(sorted[i])
      }
    }
    new_cells.push(cur)
  }
  // 重建有序分割（格序 = 出現序；等變性由簽名唯一決定）
  let lab = Array::make(n, 0)
  let ptn = Array::make(n, 0)
  let cell_of = Array::make(n, 0)
  let mut pos = 0
  for ci, cell in new_cells {
    for j, v in cell {
      lab[pos] = v
      cell_of[v] = ci
      ptn[pos] = if j < cell.length() - 1 { 1 } else { 0 }
      pos = pos + 1
    }
  }
  { n, lab, ptn, cell_of, }
}

///|
/// 結構不變量簽名（供同構快速否證）：度數序列 + 精煉顏色多重集。
pub fn graph_invariant(g : Graph) -> Array[Int32] {
  let deg = g.degree_seq()
  let colors = refine_colors(g)
  colors.sort()
  let out = deg.copy()
  for c in colors {
    out.push(c)
  }
  out
}
