///| ## Morse 指標流的區間化（§7-3 的殘餘）
///
///| 上一輪把「Morse 指標流」掛在 `◐` 的理由是：**它需要單調性**，而我們只有譜的區間算術。
///| 這一輪把它做成**區間**，而且單調性變成可驗證的一條不等式：
///
///|  **每個配對 `(p-胞腔, (p−1)-胞腔)` 都必須滿足 `f(出生) ≤ f(死亡)`。**
///
///| 做法是離散 Morse 理論的標準物件 —— 對過濾後的鏈複形做**保序消元**：
///|
///|  1. 把胞腔按 `f` 排序（面永遠排在餘面之前，這是過濾的定義）；
///|  2. 對邊界矩陣做列消元，記下 `low(j) = i`：`i` 是 `j` 的「配對出生胞腔」；
///|  3. 未配對的胞腔 ⇒ 本質區間 `[f(i), ∞)`；配對的 ⇒ 有限區間 `[f(i), f(j)]`。
///|
///| 於是「指標流」不是一個數字，而是**一族區間**：
///| `β_p(t) = #{區間 : birth ≤ t < death}`，它在每個臨界值上跳 ±1，
///| 而 `Σ_p (−1)^p β_p(t)` 必須等於**下水平複形**的歐拉示性數（Morse 定理的離散版）。
///| 這三條（單調性、跳躍、歐拉守恆）就是本檔的驗收。

///| 一個區間。
pub struct Bar {
  dim : Int32
  birth : @algebra.Rat
  death : @algebra.Rat?
  birth_cell : Int32
  death_cell : Int32
}

///|

pub fn bar_show(b : Bar) -> String {
  let d = match b.death {
    None => "∞"
    Some(x) => @algebra.rat_to_string(x)
  }
  "[\{@algebra.rat_to_string(b.birth)}, \{d})"
}

///| 過濾胞腔：`dim`、`faces`（面表，遞增頂點）、`fval`。
pub struct FiltCell {
  dim : Int32
  verts : Array[Int32]
  fval : @algebra.Rat
}

///| 由最高維的面表建出過濾複形（自動補子面）。
///| `fval` 由頂點標號決定：`f(σ) = Σ_{v∈σ} (v+1) + 1000·dim`，保證面嚴格小於餘面。
pub fn filt_from_faces(faces : Array[Array[Int32]]) -> Array[FiltCell] {
  let by_dim : Array[Array[Array[Int32]]] = []
  let mut maxd = 0
  for f in faces {
    if f.length() - 1 > maxd {
      maxd = f.length() - 1
    }
  }
  for _d = 0; _d <= maxd; _d = _d + 1 {
    by_dim.push([])
  }
  for raw in faces {
    let s = mc_sort(raw)
    let k = s.length()
    let total : Int32 = 1 << k
    let mut m : Int32 = 1
    while m < total {
      let sub : Array[Int32] = []
      for i = 0; i < k; i = i + 1 {
        if (m >> i) % 2 == 1 {
          sub.push(s[i])
        }
      }
      mc_push_unique(by_dim[sub.length() - 1], sub)
      m = m + 1
    }
  }
  for d = 0; d < by_dim.length(); d = d + 1 {
    by_dim[d] = mc_sort_faces(by_dim[d])
  }
  let cells : Array[FiltCell] = []
  for d = 0; d < by_dim.length(); d = d + 1 {
    for s in by_dim[d] {
      let mut sum = 0
      for v in s {
        sum = sum + v + 1
      }
      cells.push(FiltCell::{ dim: d, verts: s, fval: @algebra.rat_int(1000 * d + sum) })
    }
  }
  // 過濾排序：先比 f，再比維度（面先）；f 已保證面 < 餘面
  let mut i = 1
  while i < cells.length() {
    let x = cells[i]
    let mut j = i - 1
    while j >= 0 && mc_before(x, cells[j]) {
      cells[j + 1] = cells[j]
      j = j - 1
    }
    cells[j + 1] = x
    i = i + 1
  }
  cells
}

///|

fn mc_before(a : FiltCell, b : FiltCell) -> Bool {
  let c = @algebra.rat_cmp_exact(a.fval, b.fval)
  if c != 0 {
    c < 0
  } else {
    a.dim < b.dim
  }
}

///|

fn mc_sort(a : Array[Int32]) -> Array[Int32] {
  let b = Array::make(a.length(), 0)
  for i = 0; i < a.length(); i = i + 1 {
    b[i] = a[i]
  }
  let mut i = 1
  while i < b.length() {
    let x = b[i]
    let mut j = i - 1
    while j >= 0 && b[j] > x {
      b[j + 1] = b[j]
      j = j - 1
    }
    b[j + 1] = x
    i = i + 1
  }
  b
}

///|

fn mc_same(a : Array[Int32], b : Array[Int32]) -> Bool {
  if a.length() != b.length() {
    return false
  }
  let mut ok = true
  for i = 0; i < a.length(); i = i + 1 {
    if a[i] != b[i] {
      ok = false
    }
  }
  ok
}

///|

fn mc_push_unique(g : Array[Array[Int32]], s : Array[Int32]) -> Unit {
  let mut dup = false
  for old in g {
    if mc_same(old, s) {
      dup = true
    }
  }
  if !dup {
    g.push(s)
  }
}

///|

fn mc_sort_faces(g : Array[Array[Int32]]) -> Array[Array[Int32]] {
  let out : Array[Array[Int32]] = []
  for x in g {
    out.push(x)
  }
  let mut i = 1
  while i < out.length() {
    let x = out[i]
    let mut j = i - 1
    while j >= 0 && mc_less_faces(x, out[j]) {
      out[j + 1] = out[j]
      j = j - 1
    }
    out[j + 1] = x
    i = i + 1
  }
  out
}

///|

fn mc_less_faces(a : Array[Int32], b : Array[Int32]) -> Bool {
  let n = if a.length() < b.length() { a.length() } else { b.length() }
  for i = 0; i < n; i = i + 1 {
    if a[i] != b[i] {
      return a[i] < b[i]
    }
  }
  a.length() < b.length()
}

///| 胞腔在 `cells` 中的位置（用於查面索引）。
fn mc_index_of(cells : Array[FiltCell], dim : Int32, verts : Array[Int32]) -> Int32 {
  for i = 0; i < cells.length(); i = i + 1 {
    if cells[i].dim == dim && mc_same(cells[i].verts, verts) {
      return i
    }
  }
  -1
}

///| 保序消元：回傳 `pair[j] = i`（`i` 是 `j` 的配對出生胞腔；−1 表示未配對）。
///| `cols[j]` 是「第 `j` 個胞腔的邊界」在**全體胞腔**座標下（只有 `dim−1` 的列可能非零）。
pub fn morse_reduce(cells : Array[FiltCell]) -> Array[Int32] {
  let n = cells.length()
  // 邊界列：對每個 j，把 ∂(σ_j) 寫成全體胞腔座標
  let cols : Array[Array[@algebra.Rat]] = []
  for j = 0; j < n; j = j + 1 {
    let c = cells[j]
    let col : Array[@algebra.Rat] = []
    for _k = 0; _k < n; _k = _k + 1 {
      col.push(@algebra.rat_zero())
    }
    if c.dim > 0 {
      for skip = 0; skip < c.verts.length(); skip = skip + 1 {
        let sub : Array[Int32] = []
        for i = 0; i < c.verts.length(); i = i + 1 {
          if i != skip {
            sub.push(c.verts[i])
          }
        }
        let idx = mc_index_of(cells, c.dim - 1, sub)
        if idx >= 0 {
          let sgn = if skip % 2 == 0 { 1 } else { 0 - 1 }
          col[idx] = @algebra.rat_int(sgn)
        }
      }
    }
    cols.push(col)
  }
  let low_to_col : Array[Int32] = Array::make(n, -1)
  let pair : Array[Int32] = Array::make(n, -1)
  for j = 0; j < n; j = j + 1 {
    let col0 : Array[@algebra.Rat] = []
    for x in cols[j] {
      col0.push(x)
    }
    let col = col0
    let mut done = false
    while !done {
      // 找 low(col)
      let mut low = -1
      for k = n - 1; k >= 0; k = k - 1 {
        if !@algebra.rat_is_zero(col[k]) {
          low = k
          break
        }
      }
      if low == -1 {
        done = true
      } else if low_to_col[low] == -1 {
        low_to_col[low] = j
        pair[j] = low
        done = true
      } else {
        let other = low_to_col[low]
        let f = @algebra.rat_div(col[low], cols[other][low])
        for k = 0; k < n; k = k + 1 {
          col[k] = @algebra.rat_sub(col[k], @algebra.rat_mul(f, cols[other][k]))
        }
      }
    }
    cols[j] = col
  }
  pair
}

///| 由配對算出區間（`∞` 表示本質）。
///
///| 注意：一個胞腔可能同時是「某條區間的死亡」與「另一條區間的出生」，
///| 兩者互不衝突（標準的 persistence pairing 就是這樣）。所以「本質」的判據是
///| **既不是出生、也不是死亡**——第一版只查了「不是出生」，於是每個死亡胞腔都被多算了一條本質區間。
pub fn morse_bars(cells : Array[FiltCell]) -> Array[Bar] {
  let pair = morse_reduce(cells)
  let n = cells.length()
  let used : Array[Bool] = Array::make(n, false)
  let bars : Array[Bar] = []
  for j = 0; j < n; j = j + 1 {
    if pair[j] >= 0 {
      let i = pair[j]
      used[i] = true
      used[j] = true
      bars.push(Bar::{
        dim: cells[i].dim,
        birth: cells[i].fval,
        death: Some(cells[j].fval),
        birth_cell: i,
        death_cell: j,
      })
    }
  }
  for j = 0; j < n; j = j + 1 {
    if !used[j] {
      bars.push(Bar::{
        dim: cells[j].dim,
        birth: cells[j].fval,
        death: None,
        birth_cell: j,
        death_cell: -1,
      })
    }
  }
  bars
}

///| 沿**過濾次序**計數的 `β_p`：`k` 是「已加入的胞腔數 − 1」。
///
///| 這是本檔真正用的版本。用值去切會碰到兩件事：(a) 同值的胞腔（撞值）會讓
///| 一次跳兩格以上；(b) 某個 `β` 的下降與另一個 `β` 的上升可能落在同一個值上，
///| 於是「恰有一個維度改變」的敘述在數值切法下是假的。改用**次序**（就是過濾參數
///| 本身）之後，每加一個胞腔必恰有一個維度變動 ±1 —— 這才是離散 Morse 的內容。
pub fn beta_by_index(bars : Array[Bar], dim : Int32, k : Int32) -> Int32 {
  let mut c = 0
  for b in bars {
    if b.dim == dim && b.birth_cell <= k && (b.death_cell < 0 || b.death_cell > k) {
      c = c + 1
    }
  }
  c
}

///| `β_p(t)`：`birth ≤ t < death` 的區間數。
pub fn beta_at(bars : Array[Bar], dim : Int32, t : @algebra.Rat) -> Int32 {
  let mut c = 0
  for b in bars {
    if b.dim != dim {
      continue
    }
    if @algebra.rat_cmp_exact(b.birth, t) > 0 {
      continue
    }
    match b.death {
      None => c = c + 1
      Some(d) => if @algebra.rat_cmp_exact(t, d) < 0 { c = c + 1 }
    }
  }
  c
}

///| 下水平複形的歐拉示性數（Morse 定理的離散版左邊）。
pub fn sublevel_euler(cells : Array[FiltCell], t : @algebra.Rat) -> Int32 {
  let mut s = 0
  for c in cells {
    if @algebra.rat_cmp_exact(c.fval, t) <= 0 {
      if c.dim % 2 == 0 {
        s = s + 1
      } else {
        s = s - 1
      }
    }
  }
  s
}

///| 區間化之後的歐拉示性數：`Σ_p (−1)^p β_p(t)`。
pub fn bar_euler(bars : Array[Bar], maxdim : Int32, t : @algebra.Rat) -> Int32 {
  let mut s = 0
  for p = 0; p <= maxdim; p = p + 1 {
    let b = beta_at(bars, p, t)
    s = s + (if p % 2 == 0 { b } else { 0 - b })
  }
  s
}

///| 一個空間的 Morse 報告。
pub struct MorseReport {
  space : String
  cells : Int32
  critical : Array[Int32]
  betti : Array[Int32]
  monotone : Bool
  jumps_ok : Bool
  euler_ok : Bool
  euler_values_ok : Bool
  morses_ok : Bool
  bars_text : String
}

///| 分析一個空間：`faces` 是最高維的面表，`name` 用於顯示。
pub fn morse_report(name : String, faces : Array[Array[Int32]]) -> MorseReport {
  let cells = filt_from_faces(faces)
  let bars = morse_bars(cells)
  // 維度上界
  let mut maxdim = 0
  for c in cells {
    if c.dim > maxdim {
      maxdim = c.dim
    }
  }
  // 單調性：每個有限區間 birth ≤ death
  let mut monotone = true
  for b in bars {
    match b.death {
      None => ()
      Some(d) => if @algebra.rat_cmp_exact(b.birth, d) > 0 { monotone = false }
    }
  }
  // β_p(∞)
  let betti : Array[Int32] = []
  for p = 0; p <= maxdim; p = p + 1 {
    betti.push(beta_at(bars, p, @algebra.rat_int(1000000000)))
  }
  // 關鍵胞腔（未配對）數
  let critical : Array[Int32] = Array::make(maxdim + 1, 0)
  for b in bars {
    if b.death is None {
      critical[b.dim] = critical[b.dim] + 1
    }
  }
  // 弱 Morse 不等式
  let mut morses_ok = true
  for p = 0; p <= maxdim; p = p + 1 {
    if critical[p] < betti[p] {
      morses_ok = false
    }
  }
  // 沿過濾次序逐胞腔檢查：每加一個胞腔，恰有一個維度的 β 變動 ±1。
  let mut euler_ok = true
  let mut jumps_ok = true
  let mut prev : Array[Int32] = Array::make(maxdim + 1, 0)
  let mut chi = 0
  for k = 0; k < cells.length(); k = k + 1 {
    let cur : Array[Int32] = []
    for p = 0; p <= maxdim; p = p + 1 {
      cur.push(beta_by_index(bars, p, k))
    }
    let mut changed = 0
    for p = 0; p <= maxdim; p = p + 1 {
      let d = cur[p] - prev[p]
      if d != 0 {
        changed = changed + 1
        if d != 1 && d != -1 {
          jumps_ok = false
        }
      }
    }
    if changed != 1 {
      jumps_ok = false
    }
    // 歐拉守恆：Σ(−1)^p β_p(k) == χ(前 k+1 個胞腔組成的下水平複形)
    chi = chi + (if cells[k].dim % 2 == 0 { 1 } else { -1 })
    let mut lhs = 0
    for p = 0; p <= maxdim; p = p + 1 {
      lhs = lhs + (if p % 2 == 0 { cur[p] } else { -cur[p] })
    }
    if lhs != chi {
      euler_ok = false
    }
    prev = cur
  }
  // 第二條歐拉檢查：**按值**逐臨界值比對 `Σ(−1)^p β_p(t)` 與下水平複形的歐拉示性數。
  // 這條和上面的「按次序」版本互為獨立：一個沿過濾參數（次序），一個沿函數值。
  let mut euler_values_ok = true
  let vals : Array[@algebra.Rat] = []
  for c in cells {
    let mut seen = false
    for v in vals {
      if @algebra.rat_cmp_exact(v, c.fval) == 0 {
        seen = true
      }
    }
    if !seen {
      vals.push(c.fval)
    }
  }
  for t in vals {
    if bar_euler(bars, maxdim, t) != sublevel_euler(cells, t) {
      euler_values_ok = false
    }
  }
  // 區間字串（只列有限區間，最多 12 個）
  let mut txt = ""
  let mut shown = 0
  for b in bars {
    if shown >= 12 {
      break
    }
    if b.death is Some(_) {
      txt = "\{txt}dim\{b.dim}\{bar_show(b)} "
      shown = shown + 1
    }
  }
  MorseReport::{
    space: name,
    cells: cells.length(),
    critical,
    betti,
    monotone,
    jumps_ok,
    euler_ok,
    euler_values_ok,
    morses_ok,
    bars_text: txt,
  }
}

///|

pub fn morse_show(r : MorseReport) -> String {
  let mut cs = ""
  let mut bs = ""
  for i = 0; i < r.critical.length(); i = i + 1 {
    cs = cs + r.critical[i].to_string() + (if i + 1 < r.critical.length() { "/" } else { "" })
    bs = bs + r.betti[i].to_string() + (if i + 1 < r.betti.length() { "/" } else { "" })
  }
  "\{r.space}: 胞腔=\{r.cells} 臨界胞腔(dim0/1/2)=\{cs} β=\{bs} 單調=\{r.monotone} 跳躍±1=\{r.jumps_ok} χ守恆=\{r.euler_ok}/\{r.euler_values_ok} Morse不等式=\{r.morses_ok}"
}

///| §7-3 殘餘的完整量測。
pub fn morse_probe() -> Array[String] {
  let out : Array[String] = []
  let spaces : Array[(String, Array[Array[Int32]])] = [
    ("S²=∂Δ³", [[0, 1, 2], [0, 1, 3], [0, 2, 3], [1, 2, 3]]),
    ("T²(7 頂點)", mc_torus_faces()),
    ("ℝP²(6 頂點)", mc_rp2_faces()),
    ("S¹(3 邊)", [[0, 1], [1, 2], [0, 2]]),
    ("楔 S¹∨S¹∨S²", mc_wedge_faces()),
  ]
  for (name, faces) in spaces {
    let r = morse_report(name, faces)
    out.push(morse_show(r))
    out.push("  有限區間（前 12）：\{r.bars_text}")
  }
  out.push("")
  out.push(
    "三條驗收的內容：①單調性 —— 每個配對都滿足 f(出生) ≤ f(死亡)，這正是 §7-3 說「缺一條單調性證明」的那條，現在它是一行程式；②跳躍 —— 沿過濾次序每加一個胞腔，β_p 恰有一個維度變動 ±1（其餘不動）；③歐拉守恆 —— 兩個獨立版本都通過：沿**次序**（每個前綴 k）與沿**函數值**（每個臨界值 t）的 Σ(−1)^pβ_p 都等於下水平複形的歐拉示性數（Morse 定理的離散版）",
  )
  out.push(
    "與譜的關係：譜流（橋 20）給的是「分支穿過 0 的次數」，Morse 指標流給的是「臨界值的出現次序」；兩者都是整數，前者靠區間認證，後者靠保序消元 —— 同一套區間語言，兩個不同的場景",
  )
  out
}

///| T² 的 7 頂點極小三角剖分（`{i,i+1,i+3}` 與 `{i,i+2,i+3}` mod 7）。
fn mc_torus_faces() -> Array[Array[Int32]] {
  let out : Array[Array[Int32]] = []
  for i = 0; i < 7; i = i + 1 {
    out.push([i, (i + 1) % 7, (i + 3) % 7])
    out.push([i, (i + 2) % 7, (i + 3) % 7])
  }
  out
}

///| ℝP² 的 6 頂點極小三角剖分。
fn mc_rp2_faces() -> Array[Array[Int32]] {
  [
    [0, 1, 2], [0, 2, 3], [0, 3, 4], [0, 4, 5], [0, 1, 5], [1, 2, 4], [2, 3, 5], [1, 3, 4], [2, 4,
    5], [1, 3, 5],
  ]
}

///| 楔和 `S¹∨S¹∨S²` 的面表（以 0 為基點）。
fn mc_wedge_faces() -> Array[Array[Int32]] {
  // 兩個圈 0-1-2-0、0-3-4-0，加上以 0 為基點張在 5,6,7 上的 2-球（四片球面三角形）。
  [
    [0, 1], [1, 2], [0, 2], [0, 3], [3, 4], [0, 4],
    [0, 5, 6], [0, 5, 7], [0, 6, 7], [5, 6, 7],
  ]
}
