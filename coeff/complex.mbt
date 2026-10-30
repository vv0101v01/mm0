///| ## 鏈複形：單純複形與有限 CW／Delta 複形
///

///| 兩種來源都歸約成同一個 `ChainComplex`（純整數邊界矩陣），

///| 因為「係數環」只在矩陣上作用，不在幾何上作用。

///| 這一層是「幾何 → 代數」的收斂點：之後所有 `Coeff` 的差異都只是同一組整數矩陣的不同算術。

///| 有限鏈複形：`cells[d]` = d 維胞腔數，`bounds[d]` = ∂_d 的整數矩陣

///|
///（`cells[d−1]` 列 × `cells[d]` 行）。
pub struct ChainComplex {
  cells : Array[Int32]
  bounds : Array[Array[Array[Int32]]]
}
///|
pub fn cc_top(cx : ChainComplex) -> Int32 {
  cx.cells.length() - 1
}

///|
/// ∂_d（`d ≥ 1`；`d = 0` 回傳空矩陣）。
pub fn cc_boundary(cx : ChainComplex, d : Int32) -> Array[Array[Int32]] {
  if d <= 0 || d >= cx.bounds.length() {
    let out : Array[Array[Int32]] = []
    for _i = 0; _i < cx.cells[0]; _i = _i + 1 {
      out.push([])
    }
    return out
  }
  cx.bounds[d]
}

///|
/// 鏈條件 `∂_{d−1} ∘ ∂_d = 0`（逐元素精確整數運算）。
pub fn cc_chain_ok(cx : ChainComplex) -> Bool {
  for d = 2; d <= cc_top(cx); d = d + 1 {
    let a = cc_boundary(cx, d - 1)
    let b = cc_boundary(cx, d)
    if a.length() > 0 && b.length() > 0 && a[0].length() > 0 {
      for i = 0; i < a.length(); i = i + 1 {
        for j = 0; j < b[0].length(); j = j + 1 {
          let mut acc : Int32 = 0
          for k = 0; k < b.length(); k = k + 1 {
            acc = acc + a[i][k] * b[k][j]
          }
          if acc != 0 {
            return false
          }
        }
      }
    }
  }
  true
}

// ------------------------------------------------------------ 三種獨立秩 ----

///|
/// ℚ 上的秩：`exact/algebra` 的精確有理高斯消元。
pub fn rank_q(m : Array[Array[Int32]]) -> Int32 {
  if m.length() == 0 || m[0].length() == 0 {
    return 0
  }
  @algebra.qmat_rank(@algebra.qmat_from_int_rows(m))
}

///|
/// `F_p` 上的秩：`elim/core` 的模 p 高斯消元。
pub fn rank_fp(m : Array[Array[Int32]], p : Int32) -> Int32 {
  if m.length() == 0 || m[0].length() == 0 {
    return 0
  }
  @core.rank_mod(@core.mat_from_rows(m), @core.mk_field(p))
}

///|
/// ℤ 上的秩：Smith 標準形的非零對角元個數（第三條獨立路徑）。
pub fn rank_z(m : Array[Array[Int32]]) -> Int32 {
  if m.length() == 0 || m[0].length() == 0 {
    return 0
  }
  let diag = @core.smith_diagonal(@core.mat_from_rows(m))
  let mut r : Int32 = 0
  for d in diag {
    if d != 0 {
      r = r + 1
    }
  }
  r
}

///|
/// Smith 不變因子（去掉 0 與 1，升序）。
pub fn smith_invariants(m : Array[Array[Int32]]) -> Array[Int32] {
  if m.length() == 0 || m[0].length() == 0 {
    return []
  }
  let diag = @core.smith_diagonal(@core.mat_from_rows(m))
  let out : Array[Int32] = []
  for d in diag {
    let v = if d < 0 { 0 - d } else { d }
    if v > 1 {
      out.push(v)
    }
  }
  out
}

// ------------------------------------------------------------- 單純複形 ----

///|
/// 有限單純複形（每維面表；頂點升序為典範表示）。
pub struct Simplex {
  faces : Array[Array[Array[Int32]]]
}

///|
fn sv_sort(a : Array[Int32]) -> Array[Int32] {
  let b : Array[Int32] = []
  for x in a {
    b.push(x)
  }
  for i = 1; i < b.length(); i = i + 1 {
    let key = b[i]
    let mut j = i - 1
    while j >= 0 && b[j] > key {
      b[j + 1] = b[j]
      j = j - 1
    }
    b[j + 1] = key
  }
  b
}

///|
fn sv_same(a : Array[Int32], b : Array[Int32]) -> Bool {
  if a.length() != b.length() {
    return false
  }
  for i = 0; i < a.length(); i = i + 1 {
    if a[i] != b[i] {
      return false
    }
  }
  true
}

///|
fn sv_less(a : Array[Int32], b : Array[Int32]) -> Bool {
  let n = if a.length() < b.length() { a.length() } else { b.length() }
  for i = 0; i < n; i = i + 1 {
    if a[i] != b[i] {
      return a[i] < b[i]
    }
  }
  a.length() < b.length()
}

///|
/// 由任意面表建單純複形（自動補齊所有子面、排序）。
pub fn simplex_of_faces(faces : Array[Array[Int32]]) -> Simplex {
  let mut maxd : Int32 = 0
  for f in faces {
    if f.length() - 1 > maxd {
      maxd = f.length() - 1
    }
  }
  let acc : Array[Array[Array[Int32]]] = []
  for _k = 0; _k <= maxd; _k = _k + 1 {
    acc.push([])
  }
  for raw in faces {
    let face = sv_sort(raw)
    let k = face.length()
    let total : Int32 = 1 << k
    let mut m : Int32 = 1
    while m < total {
      let sub : Array[Int32] = []
      for i = 0; i < k; i = i + 1 {
        if (m >> i) % 2 == 1 {
          sub.push(face[i])
        }
      }
      let d = sub.length() - 1
      let mut dup = false
      for old in acc[d] {
        if sv_same(old, sub) {
          dup = true
        }
      }
      if !dup {
        acc[d].push(sub)
      }
      m = m + 1
    }
  }
  for d = 0; d < acc.length(); d = d + 1 {
    let arr = acc[d]
    for i = 1; i < arr.length(); i = i + 1 {
      let key = arr[i]
      let mut j = i - 1
      while j >= 0 && sv_less(key, arr[j]) {
        arr[j + 1] = arr[j]
        j = j - 1
      }
      arr[j + 1] = key
    }
  }
  Simplex::{ faces: acc, }
}

///|
pub fn simplex_top(sx : Simplex) -> Int32 {
  sx.faces.length() - 1
}

///|
/// 帶符號邊界矩陣：第 `i` 個面取 `(−1)^i`。
pub fn simplex_boundary(sx : Simplex, d : Int32) -> Array[Array[Int32]] {
  let cur = sx.faces[d - 1]
  let top = sx.faces[d]
  let rows : Array[Array[Int32]] = []
  for _i = 0; _i < cur.length(); _i = _i + 1 {
    rows.push(Array::make(top.length(), 0))
  }
  for j = 0; j < top.length(); j = j + 1 {
    let f = top[j]
    for skip = 0; skip < f.length(); skip = skip + 1 {
      let sub : Array[Int32] = []
      for i = 0; i < f.length(); i = i + 1 {
        if i != skip {
          sub.push(f[i])
        }
      }
      for r = 0; r < cur.length(); r = r + 1 {
        if sv_same(cur[r], sub) {
          rows[r][j] = if skip % 2 == 0 { 1 } else { -1 }
        }
      }
    }
  }
  rows
}

///|
/// 單純複形 → 鏈複形。
pub fn simplex_cc(sx : Simplex) -> ChainComplex {
  let top = simplex_top(sx)
  let cells : Array[Int32] = []
  for d = 0; d <= top; d = d + 1 {
    cells.push(sx.faces[d].length())
  }
  let bounds : Array[Array[Array[Int32]]] = [[]]
  for d = 1; d <= top; d = d + 1 {
    bounds.push(simplex_boundary(sx, d))
  }
  ChainComplex::{ cells, bounds, }
}

// ------------------------------------------------------ CW／Delta 複形 ----

///| 由**貼附次數**建複形：`cells[d]` 個 d-胞腔，`attach[d]` 是 (d−1)-骨架上的

///| 整數邊界矩陣（`cells[d−1]` 列 × `cells[d]` 行），可含任意整數（黏貼度數）。

///| 這正是 `ℤ/3` 撓率（Moore 空間 `M(ℤ/3,1)`）唯一能被造出來的方式——

///|
/// 單純複形做不到奇數階撓率。
pub fn cc_from_attaching(
  cells : Array[Int32],
  attach : Array[Array[Array[Int32]]],
) -> ChainComplex {
  let bounds : Array[Array[Array[Int32]]] = [[]]
  for d = 1; d < attach.length(); d = d + 1 {
    bounds.push(attach[d])
  }
  ChainComplex::{ cells, bounds, }
}

///| Moore 空間 `M(ℤ/n, 1)`：一個 0-胞腔、一個 1-胞腔（迴路）、

///|
/// 一個 2-胞腔以度數 `n` 貼上。`H₁ = ℤ/n`，`H₀ = ℤ`，其餘為 0。
pub fn moore_space(n : Int32) -> ChainComplex {
  let cells : Array[Int32] = [1, 1, 1]
  let d1 : Array[Array[Int32]] = [[0]]
  let d2 : Array[Array[Int32]] = [[n]]
  let attach : Array[Array[Array[Int32]]] = [[], d1, d2]
  cc_from_attaching(cells, attach)
}

///|
/// 實射影平面 `RP²` 的 CW 模型：`∂₂ = 2`。
pub fn cw_rp2() -> ChainComplex {
  moore_space(2)
}
