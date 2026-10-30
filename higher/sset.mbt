///| ## `higher` —— 截斷單純集、Kan 條件、邊路徑基本群
///
///| 這條軌道處理 SPEC §四 B6 的「∞-groupoid」殘餘。核心觀察是：
///
///|   **∞-groupoid 的截斷階梯與係數環是同一件事的兩個尺度。**
///
///| 一個空間 `X` 的資訊依序被丟掉：
///
///|   `Π_∞(X)`（Kan 複形）  →  `Π_1(X)`（groupoid）  →  `π₁(X)`（群）  →  `H₁(X)`（阿貝爾群）  →  `C_*(X)`（鏈複形）
///
///| 每往右一步都是**線性化**，每一步都丟資訊：
///|  - `π₁ → H₁` 是阿貝爾化（丟非阿貝爾結構）
///|  - `H_ℤ → H_ℚ` 是 `⊗ℚ`（丟撓率）
///
///| 上一輪的係數環主軸處理的是第二種；這一輪把第一種也變成可量測的：
///| 用 `|Hom(−, S₃)|` 測「同態計數」，因為它對非阿貝爾結構敏感。

// ------------------------------------------------------------ 截斷單純集 ----
///| 截斷到維度 2 的單純集表示。
///| 1-單形 `edges[i] = (源, 靶)`；2-單形 `tris[j] = (d0, d1, d2)` 是三條邊的索引，
///| 滿足 `d0: v1→v2`、`d1: v0→v2`、`d2: v0→v1`。
///| `degen[i]` 標記該 1-單形是否是退化（恆等）單形。
pub struct SSet2 {
  nv : Int32
  edges : Array[(Int32, Int32)]
  degen : Array[Bool]
  tris : Array[(Int32, Int32, Int32)]
}

///| 由頂點數與邊、三角形建構（退化標記全為 false）。
pub fn sset2_make(
  nv : Int32,
  edges : Array[(Int32, Int32)],
  tris : Array[(Int32, Int32, Int32)],
) -> SSet2 {
  let degen : Array[Bool] = []
  for _e in edges {
    degen.push(false)
  }
  SSet2::{ nv, edges, degen, tris }
}
///| 三角形是否存在。
fn has_tri(s : SSet2, d0 : Int32, d1 : Int32, d2 : Int32) -> Bool {
  for t in s.tris {
    if t.0 == d0 && t.1 == d1 && t.2 == d2 {
      return true
    }
  }
  false
}

///| Kan 條件在維度 2 的檢查：三種角（inner + 兩個 outer）是否都能填。
///| 同兩個頂點之間可以有多條邊（一個群的環），所以候選必須**枚舉**，不能「找一條」。
///| 回傳 (是否全填, 未填角數, 檢查了多少個角)。
pub fn kan_dim2(s : SSet2) -> (Bool, Int32, Int32) {
  let mut missing : Int32 = 0
  let mut total : Int32 = 0
  let ne = s.edges.length()
  for a = 0; a < ne; a = a + 1 {
    for b = 0; b < ne; b = b + 1 {
      if s.degen[a] || s.degen[b] {
        continue
      }
      let (a0, a1) = s.edges[a]
      let (b0, b1) = s.edges[b]
      // Λ²₁（inner，合成）：d0 = a（v1→v2）、d2 = b（v0→v1）
      if a0 == b1 {
        total = total + 1
        let mut filled = false
        for c = 0; c < ne; c = c + 1 {
          let (c0, c1) = s.edges[c]
          if c0 == b0 && c1 == a1 && has_tri(s, a, c, b) {
            filled = true
          }
        }
        if !filled {
          missing = missing + 1
        }
      }
      // Λ²₀（outer）：d1 = a（v0→v2）、d2 = b（v0→v1）⇒ 需 d0: v1→v2
      if a0 == b0 {
        total = total + 1
        let mut filled = false
        for c = 0; c < ne; c = c + 1 {
          let (c0, c1) = s.edges[c]
          if c0 == b1 && c1 == a1 && has_tri(s, c, a, b) {
            filled = true
          }
        }
        if !filled {
          missing = missing + 1
        }
      }
      // Λ²₂（outer）：d0 = a（v1→v2）、d1 = b（v0→v2）⇒ 需 d2: v0→v1
      if a1 == b1 {
        total = total + 1
        let mut filled = false
        for c = 0; c < ne; c = c + 1 {
          let (c0, c1) = s.edges[c]
          if c0 == b0 && c1 == a0 && has_tri(s, a, b, c) {
            filled = true
          }
        }
        if !filled {
          missing = missing + 1
        }
      }
    }
  }
  (missing == 0 && total > 0, missing, total)
}

// ---------------------------------------------------------------- 建構器 ----
///| 圓 `S¹` 的極小單純模型：一個頂點、一個非退化邊、兩個退化 2-單形。
pub fn sset_circle() -> SSet2 {
  let s = sset2_make(1, [(0, 0), (0, 0)], [(0, 0, 0), (1, 1, 1)])
  SSet2::{
    nv: 1,
    edges: s.edges,
    degen: [false, true],
    tris: s.tris,
  }
}

///| `Δ²`：三個頂點、三條邊、一個 2-單形。
pub fn sset_delta2() -> SSet2 {
  // 邊：0:(0,1) 1:(0,2) 2:(1,2)；三角形 (d0,d1,d2) = (2, 1, 0)
  sset2_make(3, [(0, 1), (0, 2), (1, 2)], [(2, 1, 0)])
}

///| 一個群的歸一化神經（單一物件）。群由乘法表給出。
///| `N(G)_1 = G`、`N(G)_2 = G×G`（可合成對），退化邊 = 單位。
pub fn sset_nerve_group(n : Int32, mul : Array[Int32], one : Int32) -> SSet2 {
  let edges : Array[(Int32, Int32)] = []
  let degen : Array[Bool] = []
  for g = 0; g < n; g = g + 1 {
    edges.push((0, 0))
    degen.push(g == one)
  }
  // 三角形 (d0,d1,d2) 對應 (h, g, gh)：d0 = h、d1 = g·h、d2 = g
  let tris : Array[(Int32, Int32, Int32)] = []
  for g = 0; g < n; g = g + 1 {
    for h = 0; h < n; h = h + 1 {
      tris.push((h, mul[g * n + h], g))
    }
  }
  SSet2::{ nv: 1, edges, degen, tris }
}

// ---------------------------------------------------------- 邊路徑基本群 ----
///| 群表示：生成元 `0..<ngen`，關係字（整數序列；`k` 表示生成元 `k`，`-k-1` 表示其逆）。
///| 這裡用「帶符號的生成元索引」：`i ≥ 0` 為 `gᵢ`，`i < 0` 為 `g₋ᵢ₋₁⁻¹`。
pub struct Pres {
  ngen : Int32
  relators : Array[Array[Int32]]
}

fn enc(g : Int32, rev : Bool) -> Int32 {
  if rev {
    0 - g - 1
  } else {
    g
  }
}

fn dec_abs(x : Int32) -> Int32 {
  if x >= 0 {
    x
  } else {
    0 - x - 1
  }
}

fn dec_rev(x : Int32) -> Bool {
  x < 0
}

///| 由截斷單純集建構邊路徑基本群的表示：
///| 1. 取一株生成樹（並查集），樹邊被收縮；
///| 2. 每個非樹邊成為一個生成元（方向 = 該邊方向）；
///| 3. 每個 2-單形給一條關係：沿 `v0 →d2→ v1 →d0→ v2 ←d1← v0` 的圈字 = 恆等。
pub fn pi1_presentation(s : SSet2) -> Pres {
  let parent : Array[Int32] = []
  for i = 0; i < s.nv; i = i + 1 {
    parent.push(i)
  }
  fn find(parent : Array[Int32], x : Int32) -> Int32 {
    let mut y = x
    while parent[y] != y {
      y = parent[y]
    }
    y
  }
  // 非樹邊 → 生成元；同時記錄每條邊的「在生成元中的表示」
  let gen_of : Array[Int32] = []
  for i = 0; i < s.edges.length(); i = i + 1 {
    gen_of.push(-1)
  }
  let mut ngen : Int32 = 0
  for i = 0; i < s.edges.length(); i = i + 1 {
    if s.degen[i] {
      continue
    }
    let (u, v) = s.edges[i]
    let ru = find(parent, u)
    let rv = find(parent, v)
    if ru == rv {
      gen_of[i] = ngen
      ngen = ngen + 1
    } else {
      parent[ru] = rv
    }
  }
  let relators : Array[Array[Int32]] = []
  for t in s.tris {
    let (d0, d1, d2) = t
    if d0 < 0 || d1 < 0 || d2 < 0 {
      continue
    }
    if d0 >= s.edges.length() || d1 >= s.edges.length() || d2 >= s.edges.length() {
      continue
    }
    // 圈字：d2 · d0 · d1⁻¹
    let w : Array[Int32] = []
    let g2 = gen_of[d2]
    let g0 = gen_of[d0]
    let g1 = gen_of[d1]
    if g2 >= 0 {
      w.push(enc(g2, false))
    }
    if g0 >= 0 {
      w.push(enc(g0, false))
    }
    if g1 >= 0 {
      w.push(enc(g1, true))
    }
    if w.length() > 0 {
      relators.push(w)
    }
  }
  Pres::{ ngen, relators }
}

///| 把一個空間（單純複形）轉成 `SSet2`。
///| `sx` 是 `coeff` 的 `Simplex`；它的 `faces[k]` 是維度 `k` 的單形（每個是一組頂點）。
pub fn sset2_of_simplex(sx : @coeff.Simplex) -> SSet2 {
  let verts = sx.faces[0]
  let nv = verts.length()
  let edge_idx : Array[(Int32, Int32)] = []
  let e1 = if sx.faces.length() > 1 {
    sx.faces[1]
  } else {
    []
  }
  for e in e1 {
    let a = e[0]
    let b = e[1]
    edge_idx.push((a, b))
  }
  let tris : Array[(Int32, Int32, Int32)] = []
  let e2 = if sx.faces.length() > 2 {
    sx.faces[2]
  } else {
    []
  }
  for f in e2 {
    // f = {a<b<c}：邊 d2=(a,b) d1=(a,c) d0=(b,c)
    let a = f[0]
    let b = f[1]
    let c = f[2]
    let d0 = edge_index(edge_idx, b, c)
    let d1 = edge_index(edge_idx, a, c)
    let d2 = edge_index(edge_idx, a, b)
    if d0 >= 0 && d1 >= 0 && d2 >= 0 {
      tris.push((d0, d1, d2))
    }
  }
  let degen : Array[Bool] = []
  for _e in edge_idx {
    degen.push(false)
  }
  SSet2::{ nv, edges: edge_idx, degen, tris }
}

///|

fn edge_index(edges : Array[(Int32, Int32)], u : Int32, v : Int32) -> Int32 {
  for i = 0; i < edges.length(); i = i + 1 {
    if edges[i].0 == u && edges[i].1 == v {
      return i
    }
    if edges[i].0 == v && edges[i].1 == u {
      return i
    }
  }
  -1
}

// ------------------------------------------------------------ 阿貝爾化 ----
///| 表示的阿貝爾化：關係矩陣（列 = 關係，行 = 生成元，帶符號計數）的 Smith 不變因子。
pub fn pres_abelianize(p : Pres) -> @coeff.Ab {
  let rows : Array[Array[Int32]] = []
  let zeros : Array[Int32] = []
  let mut all_zero = true
  for _g = 0; _g < p.ngen; _g = _g + 1 {
    zeros.push(0)
  }
  for r in p.relators {
    let row : Array[Int32] = []
    for _g = 0; _g < p.ngen; _g = _g + 1 {
      row.push(0)
    }
    for w in r {
      let a = dec_abs(w)
      let s = if dec_rev(w) { -1 } else { 1 }
      row[a] = row[a] + s
      all_zero = false
    }
    rows.push(row)
  }
  let _ = all_zero
  if p.ngen == 0 {
    return @coeff.ab_make(0, [])
  }
  if rows.length() == 0 {
    return @coeff.ab_make(p.ngen, [])
  }
  let inv = @coeff.smith_invariants(rows)
  // 自由秩 = ngen − 關係矩陣的秩
  let r = @coeff.rank_z(rows)
  @coeff.ab_make(p.ngen - r, inv)
}
