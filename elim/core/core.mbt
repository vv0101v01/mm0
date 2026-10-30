// ============================================================================
// @tensorlab/core —— 數論與線性代數基底（消元引擎 Elimination Engine）
// ----------------------------------------------------------------------------
// 設計公理 [Ax-Elm]：本函式庫把「消元」視為萬用求解器。所有結構——張量、
// 扭曲 2-上迴圈、Radon 資料、關聯矩陣、度量矩陣——先被編碼成整數矩陣，
// 再由同一組演算法（Gauss–Jordan / Smith / 精確整數關係搜尋）處理。
//
// 本檔提供的定理實作：
//   [A-Elm]  消元公理：初等行變換保持行空間 ⇒ RREF 唯一。
//   [T-Rank] Rank–Nullity：rank(A) + dim ker(A) = #cols。
//   [T-SNF]  Smith 對角化的整除鏈 d_1 | d_2 | ...
//   [T-Solve] Ax=b 可解 ⟺ rank(A) = rank(A|b)。
//   [A-Rel]  整數關係精確性：輸出關係在容差內精確零化輸入。
// ============================================================================

///| /// 素數 p 上的有限域 F_p = Z/pZ。

///| ///

///| /// **實作限制 [Inv-Word]**：本函式庫的 `Int` 為 32 位元，所有乘法在約化前

///| /// 先做單次相乘，故必須 p <= 46337（p^2 < 2^31）。此不變量由 `test

///|
/// /// "field arithmetic"` 與 `safe_prime_bound` 共同守護。
pub struct Field {
  p : Int32
}

///|
/// /// 字長安全上界：p <= 46337 保證 p*p 不溢能 31 位元號號數。
pub fn safe_prime_bound() -> Int32 {
  46337
}

///|
/// /// 建立 F_p（呼叫端保證 p 為素數且 p <= safe_prime_bound()）。
pub fn mk_field(p : Int32) -> Field {
  Field::{ p, }
}

///|
/// /// 模約化到 [0,p)。
pub fn fld_norm(f : Field, x : Int32) -> Int32 {
  let r = x % f.p
  if r < 0 {
    r + f.p
  } else {
    r
  }
}

///|
pub fn fld_add(f : Field, a : Int32, b : Int32) -> Int32 {
  fld_norm(f, a + b)
}

///|
pub fn fld_sub(f : Field, a : Int32, b : Int32) -> Int32 {
  fld_norm(f, a - b)
}

///|
pub fn fld_mul(f : Field, a : Int32, b : Int32) -> Int32 {
  fld_norm(f, a * b)
}

///|
pub fn fld_neg(f : Field, a : Int32) -> Int32 {
  fld_norm(f, 0 - a)
}

///|
/// /// 乘法逆元（費馬小定理）；inv(0) := 0 作為保護。
pub fn fld_inv(f : Field, a : Int32) -> Int32 {
  let x = fld_norm(f, a)
  if x == 0 {
    0
  } else {
    mod_pow(x, f.p - 2, f.p)
  }
}

///|
pub fn fld_div(f : Field, a : Int32, b : Int32) -> Int32 {
  fld_mul(f, a, fld_inv(f, b))
}

///|
/// /// 試除法素性判定。
pub fn is_prime(n : Int32) -> Bool {
  if n < 2 {
    false
  } else if n % 2 == 0 {
    n == 2
  } else {
    let mut d = 3
    let mut ok = true
    while d * d <= n {
      if n % d == 0 {
        ok = false
        break
      }
      d = d + 2
    }
    ok
  }
}

///|
/// /// 列出不超過 n 的素數。
pub fn primes_up_to(n : Int32) -> Array[Int32] {
  let out : Array[Int32] = []
  for i = 2; i <= n; i = i + 1 {
    if is_prime(i) {
      out.push(i)
    }
  }
  out
}

///|
/// /// 快速冪 a^e mod m（e ≥ 0, m ≥ 2）。
pub fn mod_pow(a : Int32, e : Int32, m : Int32) -> Int32 {
  if m == 1 {
    return 0
  }
  let mut base = a % m
  if base < 0 {
    base = base + m
  }
  let mut acc = 1
  let mut ee = e
  while ee > 0 {
    if ee % 2 == 1 {
      acc = acc * base % m
    }
    base = base * base % m
    ee = ee / 2
  }
  acc
}

///|
/// /// 正的最大公因數。
pub fn igcd(a : Int32, b : Int32) -> Int32 {
  let mut x = if a < 0 { 0 - a } else { a }
  let mut y = if b < 0 { 0 - b } else { b }
  while y != 0 {
    let t = x % y
    x = y
    y = t
  }
  x
}

// ---------------------------------------------------------------------------
// 整數矩陣：消元引擎的統一載體
// ---------------------------------------------------------------------------

///|
/// /// 稠密整數矩陣，列優先展平。
pub struct Mat {
  rows : Int32
  cols : Int32
  data : Array[Int32]
}

///|
pub fn mat_make(rows : Int32, cols : Int32, init : Int32) -> Mat {
  let n = if rows <= 0 || cols <= 0 { 0 } else { rows * cols }
  Mat::{ rows, cols, data: Array::make(n, init), }
}

///|
/// /// 以回呼填充的矩陣構造子（index 為列優先）。
pub fn mat_build(
  rows : Int32,
  cols : Int32,
  f : (Int32, Int32) -> Int32,
) -> Mat {
  let data : Array[Int32] = Array::make(rows * cols, 0)
  for i = 0; i < rows; i = i + 1 {
    for j = 0; j < cols; j = j + 1 {
      data[i * cols + j] = f(i, j)
    }
  }
  Mat::{ rows, cols, data, }
}

///|
pub fn mat_from_rows(rows : Array[Array[Int32]]) -> Mat {
  let nr = rows.length()
  let nc = if nr == 0 { 0 } else { rows[0].length() }
  let m = mat_make(nr, nc, 0)
  for i = 0; i < nr; i = i + 1 {
    for j = 0; j < nc; j = j + 1 {
      m.data[i * nc + j] = rows[i][j]
    }
  }
  m
}

///|
pub fn mat_identity(n : Int32) -> Mat {
  mat_build(n, n, (i, j) => if i == j { 1 } else { 0 })
}

///|
pub fn mat_get(m : Mat, i : Int32, j : Int32) -> Int32 {
  m.data[i * m.cols + j]
}

///|
/// [D-MatRow] 取第 i 行（拷貝）。
pub fn mat_row(m : Mat, i : Int32) -> Array[Int32] {
  Array::makei(m.cols, j => m.data[i * m.cols + j])
}

///|
/// [D-MatRows] 全部行（拷貝）。
pub fn mat_rows(m : Mat) -> Array[Array[Int32]] {
  Array::makei(m.rows, i => mat_row(m, i))
}

///|
/// [D-MatVec] 矩陣-向量乘積（mod p，逐項取模避免溢出）。
pub fn mat_mul_vec(m : Mat, v : Array[Int32], p : Int32) -> Array[Int32] {
  Array::makei(m.rows, i => {
    let mut s = 0
    let mut j = 0
    while j < m.cols {
      s = (s + m.data[i * m.cols + j] % p * (v[j] % p)) % p
      j = j + 1
    }
    (s % p + p) % p
  })
}

///|
/// [D-VecScale] 逐分量乘純量（mod p，每步經 fld_mul 約化，故 p ≤ safe_prime_bound 時不溢出）。
pub fn vec_scale(a : Array[Int32], c : Int32, p : Int32) -> Array[Int32] {
  let f = mk_field(p)
  Array::makei(a.length(), i => fld_mul(f, a[i], c))
}

///|
/// [D-VecDot] 內積（mod p）。逐步 fld_add/fld_mul，避免 p 接近上界時的 32 位元溢出。
pub fn vec_dot(a : Array[Int32], b : Array[Int32], p : Int32) -> Int32 {
  let f = mk_field(p)
  let mut s = 0
  let mut i = 0
  while i < a.length() {
    s = fld_add(f, s, fld_mul(f, a[i], b[i]))
    i = i + 1
  }
  s
}

///|
/// [D-MatZero] 全零矩陣判定。
pub fn mat_is_zero(m : Mat) -> Bool {
  m.data.all(x => x == 0)
}

///|
pub fn mat_copy(m : Mat) -> Mat {
  Mat::{ rows: m.rows, cols: m.cols, data: m.data.copy(), }
}

///|
/// /// [A-Elm] 前置正規化：模 p 逐項約化（不改變 F_p 上的行空間）。
pub fn mat_mod(m : Mat, p : Int32) -> Mat {
  mat_build(m.rows, m.cols, (i, j) => {
    let v = m.data[i * m.cols + j] % p
    if v < 0 {
      v + p
    } else {
      v
    }
  })
}

///|
pub fn mat_transpose(m : Mat) -> Mat {
  mat_build(m.cols, m.rows, (i, j) => m.data[j * m.cols + i])
}

///|
/// /// 矩陣乘法；p > 0 時逐項模約化。
pub fn mat_mul(a : Mat, b : Mat, p : Int32) -> Mat {
  let n = a.cols
  if n != b.rows {
    return mat_make(a.rows, b.cols, 0)
  }
  let out = mat_make(a.rows, b.cols, 0)
  for i = 0; i < a.rows; i = i + 1 {
    for k = 0; k < n; k = k + 1 {
      let aik = a.data[i * n + k]
      if aik != 0 {
        for j = 0; j < b.cols; j = j + 1 {
          let cur = out.data[i * b.cols + j]
          let v = cur + aik * b.data[k * b.cols + j]
          out.data[i * b.cols + j] = if p > 0 {
            let r = v % p
            if r < 0 {
              r + p
            } else {
              r
            }
          } else {
            v
          }
        }
      }
    }
  }
  out
}

///|
/// [D-MatAdd] 逐分量相加（mod p）。
pub fn mat_add(a : Mat, b : Mat, p : Int32) -> Mat {
  let f = mk_field(p)
  mat_build(a.rows, a.cols, (i, j) => {
    fld_add(f, mat_get(a, i, j), mat_get(b, i, j))
  })
}

///|
/// [D-MatScale] 逐分量乘純量（mod p）。
pub fn mat_scale(a : Mat, c : Int32, p : Int32) -> Mat {
  let f = mk_field(p)
  mat_build(a.rows, a.cols, (i, j) => fld_mul(f, mat_get(a, i, j), c))
}

///|
/// [D-MatEqMod] 模 p 逐元相等（差約化為 0）。
pub fn mat_eq_mod(a : Mat, b : Mat, p : Int32) -> Bool {
  if a.rows != b.rows || a.cols != b.cols {
    false
  } else {
    let f = mk_field(p)
    let mut i = 0
    let mut ok = true
    while i < a.rows && ok {
      let mut j = 0
      while j < a.cols && ok {
        if fld_sub(f, mat_get(a, i, j), mat_get(b, i, j)) != 0 {
          ok = false
        }
        j = j + 1
      }
      i = i + 1
    }
    ok
  }
}
// ---------------------------------------------------------------------------
// [D-Elm] 演算法 Elim：Gauss–Jordan 消元 over F_p
// ---------------------------------------------------------------------------

///|
/// /// 消元輸出：RREF、秩、主元行索引。
pub struct Gauss {
  rref : Mat
  rank : Int32
  pivots : Array[Int32]
}

///|
pub fn gauss_jordan(m : Mat, f : Field) -> Gauss {
  let a = mat_mod(m, f.p)
  let mut r = 0
  let pivots : Array[Int32] = []
  for c = 0; c < a.cols; c = c + 1 {
    if r >= a.rows {
      break
    }
    let mut pr = -1
    for i = r; i < a.rows; i = i + 1 {
      if a.data[i * a.cols + c] != 0 {
        pr = i
        break
      }
    }
    if pr < 0 {
      continue
    }
    if pr != r {
      for j = 0; j < a.cols; j = j + 1 {
        let t = a.data[r * a.cols + j]
        a.data[r * a.cols + j] = a.data[pr * a.cols + j]
        a.data[pr * a.cols + j] = t
      }
    }
    let inv = fld_inv(f, a.data[r * a.cols + c])
    for j = 0; j < a.cols; j = j + 1 {
      a.data[r * a.cols + j] = fld_mul(f, a.data[r * a.cols + j], inv)
    }
    for i = 0; i < a.rows; i = i + 1 {
      if i != r {
        let factor = a.data[i * a.cols + c]
        if factor != 0 {
          for j = 0; j < a.cols; j = j + 1 {
            let v = a.data[i * a.cols + j] - factor * a.data[r * a.cols + j]
            a.data[i * a.cols + j] = fld_norm(f, v)
          }
        }
      }
    }
    pivots.push(c)
    r = r + 1
  }
  Gauss::{ rref: a, rank: r, pivots, }
}

///|
pub fn rank_mod(m : Mat, f : Field) -> Int32 {
  gauss_jordan(m, f).rank
}

///|
/// /// [T-Rank] 零空間基底（以列向量陣列回傳）。
pub fn nullspace_basis(m : Mat, f : Field) -> Array[Array[Int32]] {
  let g = gauss_jordan(m, f)
  let n = m.cols
  let is_pivot : Array[Bool] = Array::make(n, false)
  for c in g.pivots {
    is_pivot[c] = true
  }
  let out : Array[Array[Int32]] = []
  for j = 0; j < n; j = j + 1 {
    if !is_pivot[j] {
      let v : Array[Int32] = Array::make(n, 0)
      v[j] = 1
      let mut r = 0
      for c in g.pivots {
        v[c] = fld_neg(f, g.rref.data[r * n + j])
        r = r + 1
      }
      out.push(v)
    }
  }
  out
}

///|
/// /// [T-Solve] 解 A x = b（F_p 上）；無解回傳 None。
pub fn solve_linear(a : Mat, b : Array[Int32], f : Field) -> Array[Int32]? {
  let m = a.cols
  let aug = mat_build(a.rows, m + 1, (i, j) => {
    if j < m {
      a.data[i * m + j]
    } else {
      b[i]
    }
  })
  let g = gauss_jordan(aug, f)
  // 若某主元落在增廣欄 ⇒ 出現 0 = 1 ⇒ 無解
  let inconsistent = g.pivots.any(c => c == m)
  if inconsistent {
    return None
  }
  let x : Array[Int32] = Array::make(m, 0)
  for r = 0; r < g.rank; r = r + 1 {
    x[g.pivots[r]] = g.rref.data[r * (m + 1) + m]
  }
  Some(x)
}

// ---------------------------------------------------------------------------
// [D-Det] 行列式（消元法 + 換行符號）
// ---------------------------------------------------------------------------

///|
pub fn det_mod(a : Mat, f : Field) -> Int32 {
  if a.rows != a.cols {
    return 0
  }
  let m = mat_mod(a, f.p)
  let n = m.cols
  let mut acc = 1
  for i = 0; i < n; i = i + 1 {
    let mut pr = -1
    for r = i; r < n; r = r + 1 {
      if m.data[r * n + i] != 0 {
        pr = r
        break
      }
    }
    if pr < 0 {
      return 0
    }
    if pr != i {
      for j = 0; j < n; j = j + 1 {
        let t = m.data[i * n + j]
        m.data[i * n + j] = m.data[pr * n + j]
        m.data[pr * n + j] = t
      }
      acc = fld_neg(f, acc)
    }
    let piv = m.data[i * n + i]
    acc = fld_mul(f, acc, piv)
    let inv = fld_inv(f, piv)
    for r = i + 1; r < n; r = r + 1 {
      let factor = fld_mul(f, m.data[r * n + i], inv)
      if factor != 0 {
        for j = i; j < n; j = j + 1 {
          let v = m.data[r * n + j] - factor * m.data[i * n + j]
          m.data[r * n + j] = fld_norm(f, v)
        }
      }
    }
  }
  acc
}

// ---------------------------------------------------------------------------
// [D-SNF] Smith 正規形：有限生成阿貝爾群的 presentation → 結構
//         （扭曲 K_0、上同調群計算都走這條路）
// ---------------------------------------------------------------------------

///|
/// /// Smith 對角線（非負、整除鏈 [T-SNF]；0 表示自由生成元）。
pub fn smith_diagonal(m : Mat) -> Array[Int32] {
  let a = mat_copy(m)
  let nr = a.rows
  let nc = a.cols
  let n = if nr < nc { nr } else { nc }
  let diag : Array[Int32] = Array::make(n, 0)
  for k = 0; k < n; k = k + 1 {
    let mut again = true
    while again {
      again = false
      let mut pi = -1
      let mut pj = -1
      let mut best = 0
      for i = k; i < nr; i = i + 1 {
        for j = k; j < nc; j = j + 1 {
          let v = a.data[i * nc + j]
          let av = if v < 0 { 0 - v } else { v }
          if av != 0 && (pi < 0 || av < best) {
            pi = i
            pj = j
            best = av
          }
        }
      }
      if pi < 0 {
        break
      }
      if pi != k {
        for j = 0; j < nc; j = j + 1 {
          let t = a.data[k * nc + j]
          a.data[k * nc + j] = a.data[pi * nc + j]
          a.data[pi * nc + j] = t
        }
      }
      if pj != k {
        for i = 0; i < nr; i = i + 1 {
          let t = a.data[i * nc + k]
          a.data[i * nc + k] = a.data[i * nc + pj]
          a.data[i * nc + pj] = t
        }
      }
      for i = k + 1; i < nr; i = i + 1 {
        if a.data[i * nc + k] != 0 {
          let pv = a.data[k * nc + k]
          let q = a.data[i * nc + k] / pv
          for j = k; j < nc; j = j + 1 {
            a.data[i * nc + j] = a.data[i * nc + j] - q * a.data[k * nc + j]
          }
          if a.data[i * nc + k] != 0 {
            again = true
          }
        }
      }
      for j = k + 1; j < nc; j = j + 1 {
        if a.data[k * nc + j] != 0 {
          let pv = a.data[k * nc + k]
          let q = a.data[k * nc + j] / pv
          // 注意：必須先快照第 k 欄（第 k 欄本身是更新的目標之一）
          let col : Array[Int32] = Array::make(nr, 0)
          for i = k; i < nr; i = i + 1 {
            col[i] = a.data[i * nc + k]
          }
          for i = k; i < nr; i = i + 1 {
            a.data[i * nc + j] = a.data[i * nc + j] - q * col[i]
          }
          if a.data[k * nc + j] != 0 {
            again = true
          }
        }
      }
      let mut still_nonzero = false
      for i = k + 1; i < nr; i = i + 1 {
        if a.data[i * nc + k] != 0 {
          still_nonzero = true
        }
      }
      for j = k + 1; j < nc; j = j + 1 {
        if a.data[k * nc + j] != 0 {
          still_nonzero = true
        }
      }
      if still_nonzero {
        again = true
      }
    }
    let d = a.data[k * nc + k]
    diag[k] = if d < 0 { 0 - d } else { d }
  }
  // 把 0 推到末尾，再逐對做 (gcd, lcm) 正規化直到整除鏈成立 [T-SNF]
  let nz : Array[Int32] = []
  for d in diag {
    if d != 0 {
      nz.push(d)
    }
  }
  let zc = diag.length() - nz.length()
  let m2 = nz.length()
  let mut go = m2 > 1
  while go {
    go = false
    for i = 0; i + 1 < m2; i = i + 1 {
      let x = nz[i]
      let y = nz[i + 1]
      if x == 0 {
        nz[i] = y
        nz[i + 1] = 0
        go = true
      } else if y != 0 && y % x != 0 {
        let g = igcd(x, y)
        nz[i] = g
        nz[i + 1] = x / g * y
        go = true
      }
    }
  }
  for _ in 0..<zc {
    nz.push(0)
  }
  nz
}

///|
/// /// 有限生成阿貝爾群 Z^r ⊕ ⊕_i Z/d_i。
pub struct AbGroup {
  free_rank : Int32
  torsion : Array[Int32]
}

///| /// **演算法 AbPresent**：列 = 關係、行 = 生成元。

///|
/// /// 自由秩 = 生成元數 − rank_Z/ZN(關係矩陣)；扭部分 = 非 1 的初等因子。
pub fn ab_from_presentation(relations : Mat) -> AbGroup {
  let diag = smith_diagonal(relations)
  let torsion : Array[Int32] = []
  let mut pivots = 0
  for d in diag {
    if d != 0 {
      pivots = pivots + 1
      if d != 1 {
        torsion.push(d)
      }
    }
  }
  let free_rank = relations.cols - pivots
  AbGroup::{ free_rank, torsion, }
}

///|
/// /// 群階；無限（free_rank > 0）回傳 -1。
pub fn ab_order(g : AbGroup) -> Int32 {
  if g.free_rank > 0 {
    return -1
  }
  let mut o = 1
  for d in g.torsion {
    o = o * d
  }
  o
}

///|
/// /// 群的展示字串。
pub fn ab_show(g : AbGroup) -> String {
  let mut s = if g.free_rank == 0 {
    ""
  } else if g.free_rank == 1 {
    "Z"
  } else {
    "Z^" + g.free_rank.to_string()
  }
  if g.free_rank > 0 && g.torsion.length() > 0 {
    s = s + " (+) "
  }
  let mut first = true
  for d in g.torsion {
    if !first {
      s = s + " (+) "
    }
    s = s + "Z/" + d.to_string()
    first = false
  }
  if s == "" {
    "0"
  } else {
    s
  }
}

// ---------------------------------------------------------------------------
// [D-IntRel] 精確整數關係搜尋（「自動導出定理」的核心演算法）
// ---------------------------------------------------------------------------

///|
/// /// 關係 c·x = 0（整數係數，scale 為實數量化倍數，tol 為絕對容差）。
pub struct IntRelation {
  coeffs : Array[Int32]
  residual : Double
  height : Int32
}

///| /// **演算法 IntRel**：meet-in-the-middle 完備搜尋 ||c||_inf <= H 的非零整數關係。

///| ///

///| /// 命題 [P-IntRel]（可決定性）：給定量化尺度 scale，任何高度 <= H 的整數關係

///| /// 都會被找到，且輸出前以浮點殘差 |c·x| <= tol 複核 —— 這是「精密邏輯推算」

///|
/// /// 的離散化身：先在有限格點上找到候選，再對原始資料回驗。
pub fn integer_relation(
  xs : Array[Double],
  hmax : Int32,
  scale : Double,
  tol : Double,
) -> IntRelation? {
  let n = xs.length()
  if n < 2 {
    return None
  }
  let h = if hmax < 1 { 1 } else { hmax }
  // 將 x 量化為整數：q_i ≈ scale * x_i，關係 c·q = 0 近似 c·x = 0
  let q : Array[Int32] = xs.map(x => (x * scale).round().to_int())
  let half = n / 2
  let m1 = half
  let m2 = n - half
  let base = 2 * h + 1
  let total1 = @algebra.int_pow(base, m1)
  let total2 = @algebra.int_pow(base, m2)
  // 前半段：sum -> 最小高度的係數向量
  let table : @hashmap.HashMap[String, Array[Int32]] = HashMap([])
  for t = 0; t < total1; t = t + 1 {
    let mut acc = 0
    let mut code = t
    let cs : Array[Int32] = Array::make(m1, 0)
    for i = 0; i < m1; i = i + 1 {
      let digit = code % base - h
      code = code / base
      cs[i] = digit
      acc = acc + digit * q[i]
    }
    let key = acc.to_string()
    let hh = max_abs(cs)
    match table.get(key) {
      None => table.set(key, cs)
      Some(prev) => if hh < max_abs(prev) { table.set(key, cs) }
    }
  }
  let mut best : IntRelation? = None
  for t = 0; t < total2; t = t + 1 {
    let mut acc = 0
    let mut code = t
    let cs : Array[Int32] = Array::make(m2, 0)
    for i = 0; i < m2; i = i + 1 {
      let digit = code % base - h
      code = code / base
      cs[i] = digit
      acc = acc + digit * q[half + i]
    }
    let key = (0 - acc).to_string()
    match table.get(key) {
      None => continue
      Some(front) => {
        let full = front.copy()
        full.push_iter(cs.iter())
        let hh = max_abs(full)
        if hh == 0 || hh > h {
          continue
        }
        let mut resid = 0.0
        for i = 0; i < n; i = i + 1 {
          resid = resid + full[i].to_double() * xs[i]
        }
        if resid.abs() <= tol {
          let cand = IntRelation::{ coeffs: full, residual: resid, height: hh, }
          match best {
            None => best = Some(cand)
            Some(b) => if hh < b.height { best = Some(cand) }
          }
        }
      }
    }
  }
  best
}

///| /// 序列不變量偵測：找出一組常數的整數線性組合（跨所有時刻 t）。

///|
/// /// 這是「演化後仍作用的恆定關係」的搜尋器：對每個 t 找關係，再取交集。
pub fn find_stable_relations(
  series : Array[Array[Double]],
  hmax : Int32,
  scale : Double,
  tol : Double,
) -> Array[IntRelation] {
  if series.length() == 0 {
    return []
  }
  let dim = series[0].length()
  let found : Array[IntRelation] = []
  for t = 0; t < series.length(); t = t + 1 {
    match integer_relation(series[t], hmax, scale, tol) {
      None => ()
      Some(r) => {
        // 必須在「所有」時刻都成立才算恆定關係
        let mut holds_all = true
        for s = 0; s < series.length(); s = s + 1 {
          if s == t {
            continue
          }
          let mut acc = 0.0
          for i = 0; i < dim; i = i + 1 {
            acc = acc + r.coeffs[i].to_double() * series[s][i]
          }
          if acc.abs() > tol {
            holds_all = false
            break
          }
        }
        if holds_all && !found.any(x => x.coeffs == r.coeffs) {
          found.push(r)
        }
      }
    }
  }
  found
}

///|
pub fn max_abs(xs : Array[Int32]) -> Int32 {
  let mut m = 0
  for x in xs {
    let a = if x < 0 { 0 - x } else { x }
    if a > m {
      m = a
    }
  }
  m
}

// ---------------------------------------------------------------------------
// 決定性偽隨機源（可重現的抽樣；有限模型上的隨機窮舉用）
// ---------------------------------------------------------------------------

///|
/// /// xorshift64*
pub struct Rng {
  mut state : Int64
}

///|
pub fn rng_seed(s : Int32) -> Rng {
  let v = s.to_int64() * 6364136223846793005L + 1442695040888963407L
  let st = if v == 0L { 88172645463325252L } else { v }
  Rng::{ state: st, }
}

///|
/// /// 回傳 [0, 2^31) 內的非負偽隨機數。
pub fn rng_next(r : Rng) -> Int32 {
  let mut x = r.state
  x = x ^ (x >> 12)
  x = x ^ (x << 25)
  x = x ^ (x >> 27)
  r.state = x
  let y = x * 2685821657736338717L
  let u = (y >> 33).to_int()
  u & 0x7fffffff
}

///|
pub fn rng_below(r : Rng, n : Int32) -> Int32 {
  if n <= 0 {
    0
  } else {
    rng_next(r) % n
  }
}
