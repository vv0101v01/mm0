// ============================================================================
// @tensorlab/tensor —— 張量積、矩陣化（matricization）與秩的消元界
// ----------------------------------------------------------------------------
// [D-Tensor] 張量 = 有限阿貝爾群上的多線性資料 + 標量域作用。
// [Ax-Tens]  張量積的萬用性質（universal property）以「 flattening 同構」的
//            形式具體實作：Multilin(A,B;C) ≅ Hom(A ⊗ B, C)。
//
// 本檔定理／推論：
//   [P-Flat]   rank_⊗(T) ≥ max_k rank(flatten_k(T))          （消元下界）
//   [T-Strassen] 2×2×2：hyperdet ≠ 0 ⟺ T 有恰好 2 個秩-1 分解之唯一性判準
//   [P-Subadd] rank(S+T) ≤ rank(S) + rank(T)
//   [P-TensRank] rank(A⊗B) = rank(A)·rank(B)（對角化表示，F_p 上可窮舉驗證）
//   [D-RankDec]  有限域上低秩分解的完備搜尋（枚舉 rank-1 張量）
// ============================================================================

///|
/// /// 有限域上的 3 階張量（維度 d0×d1×d2，列優先展平）。
pub struct Tensor3 {
  dim0 : Int32
  dim1 : Int32
  dim2 : Int32
  field : Int32
  data : Array[Int32]
}

///|
pub fn t3_make(d0 : Int32, d1 : Int32, d2 : Int32, p : Int32) -> Tensor3 {
  Tensor3::{
    dim0: d0,
    dim1: d1,
    dim2: d2,
    field: p,
    data: Array::make(d0 * d1 * d2, 0),
  }
}

///|
pub fn t3_of(
  d0 : Int32,
  d1 : Int32,
  d2 : Int32,
  p : Int32,
  f : (Int32, Int32, Int32) -> Int32,
) -> Tensor3 {
  let t = t3_make(d0, d1, d2, p)
  for i = 0; i < d0; i = i + 1 {
    for j = 0; j < d1; j = j + 1 {
      for k = 0; k < d2; k = k + 1 {
        let v = f(i, j, k)
        let r = v % p
        t.data[(i * d1 + j) * d2 + k] = if r < 0 { r + p } else { r }
      }
    }
  }
  t
}

///|
pub fn t3_get(t : Tensor3, i : Int32, j : Int32, k : Int32) -> Int32 {
  t.data[(i * t.dim1 + j) * t.dim2 + k]
}

///|
/// /// [D-Flatten] 沿 mode-k 展平為矩陣（消元引擎的入口）。
pub fn t3_flatten(t : Tensor3, mode : Int32) -> @core.Mat {
  let d0 = t.dim0
  let d1 = t.dim1
  let d2 = t.dim2
  match mode {
    0 =>
      @core.mat_build(d0, d1 * d2, (i, jj) => {
        let j = jj / d2
        let k = jj % d2
        t.data[(i * d1 + j) * d2 + k]
      })
    1 =>
      @core.mat_build(d1, d0 * d2, (j, ii) => {
        let i = ii / d2
        let k = ii % d2
        t.data[(i * d1 + j) * d2 + k]
      })
    _ =>
      @core.mat_build(d2, d0 * d1, (k, ii) => {
        let i = ii / d1
        let j = ii % d1
        t.data[(i * d1 + j) * d2 + k]
      })
  }
}

///|
/// /// **演算法 TensAdd**：逐點加法（保持標量域）。
pub fn t3_add(a : Tensor3, b : Tensor3) -> Tensor3 {
  let out = t3_make(a.dim0, a.dim1, a.dim2, a.field)
  for i = 0; i < out.data.length(); i = i + 1 {
    let v = a.data[i] + b.data[i]
    out.data[i] = v % a.field
  }
  out
}

///|
/// /// **演算法 TensScalar**：標量乘法。
pub fn t3_smul(c : Int32, a : Tensor3) -> Tensor3 {
  let out = t3_make(a.dim0, a.dim1, a.dim2, a.field)
  for i = 0; i < out.data.length(); i = i + 1 {
    out.data[i] = c * a.data[i] % a.field
  }
  out
}

///|
/// /// 秩-1（單純）張量 u⊗v⊗w。
pub fn t3_simple(
  u : Array[Int32],
  v : Array[Int32],
  w : Array[Int32],
  p : Int32,
) -> Tensor3 {
  let d0 = u.length()
  let d1 = v.length()
  let d2 = w.length()
  t3_of(d0, d1, d2, p, (i, j, k) => u[i] * v[j] * w[k])
}

///| /// **演算法 Kronecker**（A⊗B 為矩陣的張量積 = 4 維块的 2 維排列）。

///|
/// /// 回傳 (dim0,dim1)×(dim2,dim3) 展開成矩陣，維度 (a.rows*b.rows)×(a.cols*b.cols)。
pub fn kron_mat(a : @core.Mat, b : @core.Mat, p : Int32) -> @core.Mat {
  @core.mat_build(a.rows * b.rows, a.cols * b.cols, (i, j) => {
    let ai = i / b.rows
    let bi = i % b.rows
    let aj = j / b.cols
    let bj = j % b.cols
    let av = a.data[ai * a.cols + aj]
    let bv = b.data[bi * b.cols + bj]
    av * bv % p
  })
}

///|
/// /// [P-Flat] 張量秩的消元下界：max_k rank(flatten_k)。
pub fn flattening_lower_bound(t : Tensor3) -> Int32 {
  let f = @core.mk_field(t.field)
  let mut best = 0
  for mode = 0; mode < 3; mode = mode + 1 {
    let r = @core.rank_mod(t3_flatten(t, mode), f)
    if r > best {
      best = r
    }
  }
  best
}

///|
/// [D-ProjScale] 射影比較：若存在 λ ≠ 0 使 b = λ·a 則回傳 λ，否則回傳 0。
///   λ 由**首個非零座標**決定（用座標 0 會把 a[0] = 0 的情況算成 λ = 0，
///   那正是本函式前一版把分解見證算錯的原因）。
fn proj_scale(a : Array[Int32], b : Array[Int32], p : Int32) -> Int32 {
  let f = @core.mk_field(p)
  let mut i0 = -1
  let mut i = 0
  while i < a.length() {
    if @core.fld_norm(f, a[i]) != 0 && i0 < 0 {
      i0 = i
    }
    i = i + 1
  }
  if i0 < 0 || @core.fld_norm(f, b[i0]) == 0 {
    return 0
  }
  let lam = @core.fld_div(f, b[i0], a[i0])
  let mut k = 0
  while k < a.length() {
    if @core.fld_sub(f, b[k], @core.fld_mul(f, lam, a[k])) != 0 {
      return 0
    }
    k = k + 1
  }
  lam
}

///|
/// [D-Decomp] 秩-1 分解搜索（**唯一**的秩引擎）：回傳 [(Rank1Table.list 的索引, 係數)]，
///   使 Σ 係數·list[i] = t。索引非遞減 ⇒ 只枚舉組合（消去 r! 個排列）。
///   *完整性*：係數可為 1..p−1（不只 +1），故 r 項能表示「秩 ≤ r 的任意張量」；
///   葉節點改用 O(1) 查表判秩-1，故代價為 (p−1)·|list| 的分支而非逐元素重算。
///   （舊版 `sum_search` 只允許係數 1 且用逐元素相等判秩-1，會把 2·(u⊗v⊗w) 誤判成秩 2。）
pub fn decompose(
  t : Tensor3,
  tab : Rank1Table,
  rmax : Int32,
) -> Array[(Int32, Int32)]? {
  if t.data.all(x => x == 0) {
    return Some([])
  }
  let p = t.field
  let f = @core.mk_field(p)
  let mut r = 1
  while r <= rmax {
    let acc : Array[(Int32, Int32)] = []
    if decompose_search(tab, f, p, t.data.copy(), r, 0, acc) {
      return Some(acc.copy())
    }
    r = r + 1
  }
  None
}

///|
/// decompose 的遞迴核心：remain 能否用 r 個（索引 ≥ start 的）秩-1 項表示。
fn decompose_search(
  tab : Rank1Table,
  f : @core.Field,
  p : Int32,
  remain : Array[Int32],
  r : Int32,
  start : Int32,
  acc : Array[(Int32, Int32)],
) -> Bool {
  if remain.all(x => x == 0) {
    return true
  }
  if r == 0 {
    return false
  }
  if r == 1 {
    let norm = remain.map(x => @core.fld_norm(f, x))
    if !tab.flags[vec_code(norm, p)] {
      return false
    }
    let mut i = 0
    while i < tab.list.length() {
      let lam = proj_scale(tab.list[i], norm, p)
      if lam != 0 {
        acc.push((i, lam))
        return true
      }
      i = i + 1
    }
    return false
  }
  let mut i = start
  while i < tab.list.length() {
    let a = tab.list[i]
    let mut k = 1
    while k < p {
      let next : Array[Int32] = Array::make(remain.length(), 0)
      let mut j = 0
      while j < remain.length() {
        next[j] = @core.fld_sub(f, remain[j], @core.fld_mul(f, k, a[j]))
        j = j + 1
      }
      acc.push((i, k))
      if decompose_search(tab, f, p, next, r - 1, i, acc) {
        return true
      }
      let _ = acc.pop()
      k = k + 1
    }
    i = i + 1
  }
  false
}

///|
/// [D-Rank] 張量秩 = 最短秩-1 分解的項數（rmax 以內的完備判定）。
pub fn tensor_rank(t : Tensor3, tab : Rank1Table, rmax : Int32) -> Int32? {
  match decompose(t, tab, rmax) {
    Some(terms) => Some(terms.length())
    None => None
  }
}

///|
/// [P-Subadd] 秩的次加性 rank(A+B) ≤ rank A + rank B（有限樣本，與秩引擎同一實作）。
pub fn check_subadditivity(
  samples : Array[(Tensor3, Tensor3)],
  tab : Rank1Table,
) -> Bool {
  let mut ok = true
  for pair in samples {
    let (s, t) = pair
    match (tensor_rank(s, tab, 3), tensor_rank(t, tab, 3)) {
      (Some(rs), Some(rt)) => {
        let sum = t3_add(s, t)
        match tensor_rank(sum, tab, 3) {
          Some(rsm) => if rsm > rs + rt { ok = false }
          None => ok = false
        }
      }
      _ => ok = false
    }
  }
  ok
}

// ---------------------------------------------------------------------------
// [T-Strassen] 2×2×2 Cayley hyperdeterminant 與分解唯一性
// ---------------------------------------------------------------------------

///| /// Cayley hyperdeterminant（12 項公式）：

///| ///   Det = Σ_4 (d_i⁺ d_i⁻)² − 2·Σ_6 (rectangle) + 4·Σ_2 (tetrahedron)。

///|
/// /// 以「立方體 4 條空間對角線／6 個矩形面對／2 個正四面體」的組合描述。
pub fn hyperdet222(t : Tensor3) -> Int32 {
  // 四個因子相乘可達 p⁴，故內部一律用 Int64；p ≤ safe_prime_bound()=46337 時
  // 逐步 red() 約化，中間值不超過 46337²，絕對不會溢出。
  let p64 = t.field.to_int64()
  let g = fn(i : Int32, j : Int32, k : Int32) -> Int64 {
    t3_get(t, i, j, k).to_int64()
  }
  let red = fn(x : Int64) -> Int64 {
    let r = x % p64
    if r < 0L {
      r + p64
    } else {
      r
    }
  }
  let mul = fn(a : Int64, b : Int64) -> Int64 { red(a * b) }
  let mono4 = fn(a : Int64, b : Int64, c : Int64, d : Int64) -> Int64 {
    mul(mul(mul(a, b), c), d)
  }
  let sq = fn(x : Int64) -> Int64 { mul(x, x) }
  // 4 條空間對角線（互補頂點對）
  let dg = red(
    sq(mul(g(0, 0, 0), g(1, 1, 1))) +
    sq(mul(g(0, 0, 1), g(1, 1, 0))) +
    sq(mul(g(0, 1, 0), g(1, 0, 1))) +
    sq(mul(g(0, 1, 1), g(1, 0, 0))),
  )
  // 6 個「矩形對」（每條對角線選兩個）
  let rc = red(
    mono4(g(0, 0, 0), g(0, 0, 1), g(1, 1, 0), g(1, 1, 1)) +
    mono4(g(0, 0, 0), g(0, 1, 0), g(1, 0, 1), g(1, 1, 1)) +
    mono4(g(0, 0, 0), g(0, 1, 1), g(1, 0, 0), g(1, 1, 1)) +
    mono4(g(0, 0, 1), g(0, 1, 0), g(1, 0, 1), g(1, 1, 0)) +
    mono4(g(0, 0, 1), g(0, 1, 1), g(1, 0, 0), g(1, 1, 0)) +
    mono4(g(0, 1, 0), g(0, 1, 1), g(1, 0, 0), g(1, 0, 1)),
  )
  // 2 個正四面體（偶／奇權重頂點集）
  let tet = red(
    mono4(g(0, 0, 0), g(0, 1, 1), g(1, 0, 1), g(1, 1, 0)) +
    mono4(g(0, 0, 1), g(0, 1, 0), g(1, 0, 0), g(1, 1, 1)),
  )
  red(dg - 2L * rc + 4L * tet).to_int()
}

///| /// **命題 [P-Shear]**：Det 在每個因子的 elementary shear（det = 1）下不變。

///|
/// /// 回傳「所有 6 個剪切生成元作用下 Det 值是否全部相同」。
pub fn check_shear_invariance(t : Tensor3) -> Bool {
  let base = hyperdet222(t)
  let p = t.field
  let f = @core.mk_field(p)
  let mut ok = true
  for mode = 0; mode < 3; mode = mode + 1 {
    for dir = 0; dir < 2; dir = dir + 1 {
      let s = t3_make(2, 2, 2, p)
      for i = 0; i < 2; i = i + 1 {
        for j = 0; j < 2; j = j + 1 {
          for k = 0; k < 2; k = k + 1 {
            let idx = i * 4 + j * 2 + k
            let bit = match mode {
              0 => i
              1 => j
              _ => k
            }
            let partner_idx = match mode {
              0 => (1 - i) * 4 + j * 2 + k
              1 => i * 4 + (1 - j) * 2 + k
              _ => i * 4 + j * 2 + (1 - k)
            }
            let keep = t3_get(t, i, j, k)
            let other = t.data[partner_idx]
            s.data[idx] = if (dir == 0 && bit == 0) || (dir == 1 && bit == 1) {
              @core.fld_add(f, keep, other)
            } else {
              keep
            }
          }
        }
      }
      if hyperdet222(s) != base {
        ok = false
      }
    }
  }
  ok
}

///|
/// /// 秩-1 張量的布爾表（索引 = 以 p 為基數的展平編碼），供分解計數使用。
pub struct Rank1Table {
  dim : Int32
  field : Int32
  flags : Array[Bool]
  list : Array[Array[Int32]]
}

///|
/// /// **演算法 Rank1Enum**：列出全部非零秩-1 張量並建表。
pub fn rank1_table(d : Int32, p : Int32) -> Rank1Table {
  let fld = @core.mk_field(p)
  let vs = nonzero_vectors_all(d, p)
  let m = vs.length()
  let size = @algebra.int_pow(p, d * d * d)
  let flags : Array[Bool] = Array::make(size, false)
  let list : Array[Array[Int32]] = []
  for a = 0; a < m; a = a + 1 {
    for b = 0; b < m; b = b + 1 {
      for c = 0; c < m; c = c + 1 {
        let flat : Array[Int32] = Array::make(d * d * d, 0)
        for i = 0; i < d; i = i + 1 {
          for j = 0; j < d; j = j + 1 {
            for k = 0; k < d; k = k + 1 {
              // 三個因子相乘可達 p³ ⇒ 必須逐步約化（p ≥ 1291 時直接相乘會溢出 Int32）
              flat[(i * d + j) * d + k] = @core.fld_mul(
                fld,
                @core.fld_mul(fld, vs[a][i], vs[b][j]),
                vs[c][k],
              )
            }
          }
        }
        if flat.any(x => x != 0) {
          let code = vec_code(flat, p)
          if !flags[code] {
            flags[code] = true
            list.push(flat)
          }
        }
      }
    }
  }
  Rank1Table::{ dim: d, field: p, flags, list, }
}

///|
/// /// 把平展向量編碼為 [0, p^n) 的整數（基 p 表示）。
pub fn vec_code(v : Array[Int32], p : Int32) -> Int32 {
  let mut acc = 0
  for i = 0; i < v.length(); i = i + 1 {
    acc = acc + v[i] * @algebra.int_pow(p, i)
  }
  acc
}

///|
/// /// 所有非零向量（不做射影歸約——因為標量倍也是不同秩-1 項）。
pub fn nonzero_vectors_all(d : Int32, p : Int32) -> Array[Array[Int32]] {
  let total = @algebra.int_pow(p, d)
  let out : Array[Array[Int32]] = []
  for code = 1; code < total; code = code + 1 {
    let v : Array[Int32] = Array::make(d, 0)
    let mut c = code
    for i = 0; i < d; i = i + 1 {
      v[i] = c % p
      c = c / p
    }
    out.push(v)
  }
  out
}

///|
/// /// T 是否為秩-1：三個展平矩陣的秩都 ≤ 1（標量不變、消元可判定）。
pub fn is_rank1(t : Tensor3) -> Bool {
  if !t.data.any(x => x != 0) {
    return false
  }
  let f = @core.mk_field(t.field)
  let mut ok = true
  for mode = 0; mode < 3; mode = mode + 1 {
    if @core.rank_mod(t3_flatten(t, mode), f) > 1 {
      ok = false
    }
  }
  ok
}

///|
/// /// 有序分解計數：#{ A 秩-1非零 : T − A 亦秩-1非零 }。
pub fn rank2_ordered_pairs(t : Tensor3, tab : Rank1Table) -> Int32 {
  let p = t.field
  let mut cnt = 0
  for i = 0; i < tab.list.length(); i = i + 1 {
    let a = tab.list[i]
    let b : Array[Int32] = Array::make(a.length(), 0)
    for j = 0; j < a.length(); j = j + 1 {
      b[j] = @core.fld_norm(@core.mk_field(p), t.data[j] - a[j])
    }
    let code_b = vec_code(b, p)
    if tab.flags[code_b] && !b.all(x => x == 0) {
      let mut equal = true
      for j = 0; j < a.length(); j = j + 1 {
        if (a[j] + b[j]) % p != t.data[j] {
          equal = false
        }
      }
      if equal {
        cnt = cnt + 1
      }
    }
  }
  cnt
}

///|
/// /// 無序分解數 = 有序計數 / 2（[L-Pair]：A + B 與 B + A 成對出現）。
pub fn rank2_decomposition_count(t : Tensor3, tab : Rank1Table) -> Int32 {
  rank2_ordered_pairs(t, tab) / 2
}

///| /// [T-Strassen] 分類子：回傳 (rank ∈ {0,1,2,3+}, 分解數, hyperdet)。

///| /// 定理 [T-Strassen-F3]：在 F_3 上對全部 3^8 個 2×2×2 張量，

///| ///   rank = 2 ⟺ (hyperdet ≠ 0 ∧ 分解數 = 1) ∨ (hyperdet = 0 ∧ 分解數 ≥ 3)

///|
/// /// 亦即「Det ≠ 0 ⟺ 秩 2 且分解唯一」，並允許有限域特有的 rank 3 & Det ≠ 0 現象。
pub fn classify222(t : Tensor3, tab : Rank1Table) -> (Int32, Int32, Int32) {
  let is_zero = t.data.all(x => x == 0)
  let d = hyperdet222(t)
  if is_zero {
    return (0, 0, 0)
  }
  if is_rank1(t) {
    return (1, 0, d)
  }
  let cnt = rank2_decomposition_count(t, tab)
  if cnt > 0 {
    (2, cnt, d)
  } else {
    (3, 0, d)
  }
}

// ---------------------------------------------------------------------------
// 張量範疇的複合：[Ax-Tens] 的計算版本（張量積 = 分塊矩陣的 Kronecker）
// ---------------------------------------------------------------------------

///| /// **命題 [P-KronRank]**：rank(A⊗B) = rank(A)·rank(B)。

///|
/// /// 這裡給出可執行驗證（在給定素數下做高斯消元比較）。
pub fn check_kronecker_rank_identity(
  a : @core.Mat,
  b : @core.Mat,
  p : Int32,
) -> Bool {
  let f = @core.mk_field(p)
  let k = kron_mat(a, b, p)
  @core.rank_mod(k, f) == @core.rank_mod(a, f) * @core.rank_mod(b, f)
}

///| /// **推論 [C-FlattenKron]**：flattening 界在張量積下相乘，

///|
/// /// 故「消元 + 張量積」給出可複合的下界：lb(A⊗B) = lb(A)·lb(B)。
pub fn flattening_bound_of_product(
  a : @core.Mat,
  b : @core.Mat,
  p : Int32,
) -> Int32 {
  let f = @core.mk_field(p)
  @core.rank_mod(a, f) * @core.rank_mod(b, f)
}
