///| score —— 超化核心（super core）：Grassmann 環、超矩陣、Berezinian。

///|

///| 本套件把 tensorlab 的消元引擎 `core` 超化：

///|  * `[S-D-Gr]` 純奇 Grassmann 環 Λ(θ₁..θ_k) over F_p —— 「展平對稱性」的引擎：

///|    反對稱（外代數）= 奇生成元的超交換多項式（對稱代數），

///|    一套乘法同時實現 Λ 與 Sym（Koszul 號規則）[S-T-FlatSym]；

///|  * `[S-D-SMat]` (m|n) 超矩陣 over F_p：方塊 a b c d，

///|    齊次元素 = 偶（b=c=0）/ 奇（a=d=0），即 gl(m|n) 的齊次部分；

///|  * `[S-D-st]` 超轉置、`[S-D-str]` 超跡、`[S-D-sbr]` 超交換子；

///|  * `[S-D-SMatG]` Grassmann 係數的齊次偶超矩陣（GL(m|n) 的 Λ-點）

///|    與 `[S-D-Ber]` Berezinian（超行列式）。

///|

///| 全部運算精確（F_p 消元 / Λ 環的整係數）；隨機實驗用 @core.Rng 固定種子。

///| ---------------------------------------------------------------- Grassmann

///| 純奇 Grassmann 環：k 個奇生成元 θ₁..θ_k，元素 = 長度 2^k 的 F_p 係數向量，

///|
/// 索引 = 生成元的位元遮罩（基底單項 θ_S，S ⊆ {0..k−1}）。
pub struct Gr {
  k : Int32
  p : Int32
}

///|
/// 新環。
pub fn gr_mk(k : Int32, p : Int32) -> Gr {
  Gr::{ k, p, }
}

///|
/// 環大小（維度 2^k）。
pub fn gr_size(g : Gr) -> Int32 {
  1 << g.k
}

///|
/// 零元素。
pub fn gr_zero(g : Gr) -> Array[Int32] {
  Array::make(gr_size(g), 0)
}

///|
/// 單位元素（常數 1）。
pub fn gr_one(g : Gr) -> Array[Int32] {
  let e = gr_zero(g)
  e[0] = 1
  e
}

///|
/// 單項 θ_i。
pub fn gr_gen(g : Gr, i : Int32) -> Array[Int32] {
  let e = gr_zero(g)
  e[1 << i] = 1
  e
}

///|
/// 位元計數。
fn popcount(x : Int32) -> Int32 {
  let mut v = x
  let mut c = 0
  while v != 0 {
    c = c + (v & 1)
    v = @algebra.int_lsr(v, 1)
  }
  c
}

///|
/// Koszul 號：θ_S θ_T（S∩T=∅，生成元全奇）= (−1)^{#{(a,b)∈S×T: b<a}} θ_{S∪T}。
fn ksign(s : Int32, t : Int32, k : Int32) -> Int32 {
  let mut sg = 1
  for a = 0; a < k; a = a + 1 {
    if ((s >> a) & 1) == 1 {
      for b = 0; b < a; b = b + 1 {
        if ((t >> b) & 1) == 1 {
          sg = -sg
        }
      }
    }
  }
  sg
}

///|
/// Λ 乘法（超交換：奇單項反對稱、平方為零）。
pub fn gr_mul(g : Gr, x : Array[Int32], y : Array[Int32]) -> Array[Int32] {
  let out = gr_zero(g)
  let sz = gr_size(g)
  for i = 0; i < sz; i = i + 1 {
    if x[i] == 0 {
      continue
    }
    for j = 0; j < sz; j = j + 1 {
      if y[j] == 0 {
        continue
      }
      if (i & j) != 0 {
        continue // 奇生成元平方為零
      }
      let coeff = (x[i] * y[j] % g.p * ksign(i, j, g.k) % g.p + g.p) % g.p
      let idx = i | j
      out[idx] = (out[idx] + coeff) % g.p
    }
  }
  out
}

///|
/// 純量乘。
pub fn gr_scale(g : Gr, x : Array[Int32], c : Int32) -> Array[Int32] {
  let out = gr_zero(g)
  for i = 0; i < gr_size(g); i = i + 1 {
    out[i] = x[i] % g.p * ((c % g.p + g.p) % g.p) % g.p
  }
  out
}

///|
/// 加法。
pub fn gr_add(g : Gr, x : Array[Int32], y : Array[Int32]) -> Array[Int32] {
  let out = gr_zero(g)
  for i = 0; i < gr_size(g); i = i + 1 {
    out[i] = ((x[i] + y[i]) % g.p + g.p) % g.p
  }
  out
}

///|
/// 相等。
pub fn gr_eq(x : Array[Int32], y : Array[Int32]) -> Bool {
  if x.length() != y.length() {
    return false
  }
  for i = 0; i < x.length(); i = i + 1 {
    if x[i] != y[i] {
      return false
    }
  }
  true
}

///|
/// 偶么正文（unit ⟺ body ≠ 0）。`gr_is_unit` 是偶子環求逆的前提。
pub fn gr_is_unit(g : Gr, x : Array[Int32]) -> Bool {
  x[0] % g.p != 0
}

///|
/// 偶么正元素的逆：x = b + n（n 在增廣理想），x⁻¹ = b⁻¹·Σ_{j}(−n/b)^j。
pub fn gr_inv(g : Gr, x : Array[Int32]) -> Array[Int32] {
  let b = x[0]
  let binv = @core.mod_pow(b, g.p - 2, g.p)
  // n = x - b（僅非 body 部位非零）
  let n = gr_zero(g)
  for i = 1; i < gr_size(g); i = i + 1 {
    n[i] = x[i]
  }
  // term_j = (−n·binv)^j；累加 e = Σ term_j
  let mut e = gr_one(g)
  let mut term = gr_one(g)
  let negn = gr_scale(g, n, (g.p - binv) % g.p) // −n/b
  for j = 1; j <= g.k; j = j + 1 {
    term = gr_mul(g, term, negn)
    e = gr_add(g, e, term)
  }
  gr_scale(g, e, binv)
}

// ------------------------------------------------- 偶子環上的矩陣運算 ----
// 偶子環 Λ⁰ 是交換環（么正局部環）；其上做高斯消元（選 unit 主元）。

///|
/// 偶元素方陣（r×r）乘法。
pub fn even_mat_mul(
  g : Gr,
  a : Array[Array[Array[Int32]]],
  b : Array[Array[Array[Int32]]],
) -> Array[Array[Array[Int32]]] {
  let r = a.length()
  let inner = a[0].length()
  let c2 = b[0].length()
  let out : Array[Array[Array[Int32]]] = []
  for i = 0; i < r; i = i + 1 {
    let row : Array[Array[Int32]] = []
    for j = 0; j < c2; j = j + 1 {
      let mut acc = gr_zero(g)
      for t = 0; t < inner; t = t + 1 {
        acc = gr_add(g, acc, gr_mul(g, a[i][t], b[t][j]))
      }
      let _ = row.push(acc)
    }
    let _ = out.push(row)
  }
  out
}

///|
/// 偶元素矩陣加/減（sign = ±1）。
fn even_mat_add(
  g : Gr,
  a : Array[Array[Array[Int32]]],
  b : Array[Array[Array[Int32]]],
  sign : Int32,
) -> Array[Array[Array[Int32]]] {
  let r = a.length()
  let c2 = a[0].length()
  let out : Array[Array[Array[Int32]]] = []
  for i = 0; i < r; i = i + 1 {
    let row : Array[Array[Int32]] = []
    for j = 0; j < c2; j = j + 1 {
      let _ = row.push(gr_add(g, a[i][j], gr_scale(g, b[i][j], sign)))
    }
    let _ = out.push(row)
  }
  out
}

///|
/// 偶元素方陣行列式：帶 unit 主元選取的高斯消去，det = ±主元乘積。
pub fn even_det(g : Gr, a : Array[Array[Array[Int32]]]) -> Array[Int32] {
  let n = a.length()
  // 複製
  let m : Array[Array[Array[Int32]]] = []
  for i = 0; i < n; i = i + 1 {
    let row : Array[Array[Int32]] = []
    for j = 0; j < n; j = j + 1 {
      let _ = row.push(a[i][j])
    }
    let _ = m.push(row)
  }
  let mut det = gr_one(g)
  let mut sign = 1
  for col = 0; col < n; col = col + 1 {
    // 找 unit 主元
    let mut piv = -1
    for i = col; i < n; i = i + 1 {
      if gr_is_unit(g, m[i][col]) {
        piv = i
        break
      }
    }
    if piv < 0 {
      return gr_zero(g) // 奇異
    }
    if piv != col {
      let tmp = m[piv]
      m[piv] = m[col]
      m[col] = tmp
      sign = -sign
    }
    let pv = m[col][col]
    det = gr_mul(g, det, pv)
    let pvinv = gr_inv(g, pv)
    for i = col + 1; i < n; i = i + 1 {
      if !gr_eq(m[i][col], gr_zero(g)) {
        let f = gr_mul(g, m[i][col], pvinv)
        for j = col; j < n; j = j + 1 {
          m[i][j] = gr_add(
            g,
            m[i][j],
            gr_scale(g, gr_mul(g, f, m[col][j]), g.p - 1),
          )
        }
      }
    }
  }
  if sign < 0 {
    det = gr_scale(g, det, g.p - 1)
  }
  det
}

///|
/// 偶元素方陣逆（Gauss–Jordan；主元須 unit，否則回傳 None）。
pub fn even_mat_inv(
  g : Gr,
  a : Array[Array[Array[Int32]]],
) -> Array[Array[Array[Int32]]]? {
  let n = a.length()
  // 增廣 [a | I]
  let m : Array[Array[Array[Int32]]] = []
  for i = 0; i < n; i = i + 1 {
    let row : Array[Array[Int32]] = []
    for j = 0; j < n; j = j + 1 {
      let _ = row.push(a[i][j])
    }
    for j = 0; j < n; j = j + 1 {
      let _ = row.push(if i == j { gr_one(g) } else { gr_zero(g) })
    }
    let _ = m.push(row)
  }
  for col = 0; col < n; col = col + 1 {
    let mut piv = -1
    for i = col; i < n; i = i + 1 {
      if gr_is_unit(g, m[i][col]) {
        piv = i
        break
      }
    }
    if piv < 0 {
      return None
    }
    if piv != col {
      let tmp = m[piv]
      m[piv] = m[col]
      m[col] = tmp
    }
    let pvinv = gr_inv(g, m[col][col])
    for j = 0; j < 2 * n; j = j + 1 {
      m[col][j] = gr_mul(g, m[col][j], pvinv)
    }
    for i = 0; i < n; i = i + 1 {
      if i != col && !gr_eq(m[i][col], gr_zero(g)) {
        let f = m[i][col]
        for j = 0; j < 2 * n; j = j + 1 {
          m[i][j] = gr_add(
            g,
            m[i][j],
            gr_scale(g, gr_mul(g, f, m[col][j]), g.p - 1),
          )
        }
      }
    }
  }
  let out : Array[Array[Array[Int32]]] = []
  for i = 0; i < n; i = i + 1 {
    let row : Array[Array[Int32]] = []
    for j = n; j < 2 * n; j = j + 1 {
      let _ = row.push(m[i][j])
    }
    let _ = out.push(row)
  }
  Some(out)
}

///| --------------------------------------------------------- (m|n) 超矩陣 over F_p

///| 方塊佈局：a (m×m 偶→偶)、b (m×n 偶→奇)、c (n×m 奇→偶)、d (n×n 奇→奇)。

///|
/// 齊次性：偶矩陣 b=c=0；奇矩陣 a=d=0。全陣 = (m+n)×(m+n)。
pub struct SMat {
  m : Int32
  n : Int32
  p : Int32
  a : @core.Mat
  b : @core.Mat
  c : @core.Mat
  d : @core.Mat
}

///|
/// 展開為普通 (m+n)×(m+n) 矩陣。
pub fn smat_full(x : SMat) -> @core.Mat {
  let s = x.m + x.n
  let out = @core.mat_make(s, s, 0)
  for i = 0; i < x.m; i = i + 1 {
    for j = 0; j < x.m; j = j + 1 {
      out.data[i * s + j] = x.a.data[i * x.m + j]
    }
    for j = 0; j < x.n; j = j + 1 {
      out.data[i * s + x.m + j] = x.b.data[i * x.n + j]
    }
  }
  for i = 0; i < x.n; i = i + 1 {
    for j = 0; j < x.m; j = j + 1 {
      out.data[(x.m + i) * s + j] = x.c.data[i * x.m + j]
    }
    for j = 0; j < x.n; j = j + 1 {
      out.data[(x.m + i) * s + x.m + j] = x.d.data[i * x.n + j]
    }
  }
  out
}

///|
/// 從普通 (m+n)×(m+n) 方陣拆方塊。
pub fn smat_from_full(m : Int32, n : Int32, p : Int32, f : @core.Mat) -> SMat {
  let s = m + n
  let a = @core.mat_make(m, m, 0)
  let b = @core.mat_make(m, n, 0)
  let c = @core.mat_make(n, m, 0)
  let d = @core.mat_make(n, n, 0)
  for i = 0; i < m; i = i + 1 {
    for j = 0; j < m; j = j + 1 {
      a.data[i * m + j] = f.data[i * s + j]
    }
    for j = 0; j < n; j = j + 1 {
      b.data[i * n + j] = f.data[i * s + m + j]
    }
  }
  for i = 0; i < n; i = i + 1 {
    for j = 0; j < m; j = j + 1 {
      c.data[i * m + j] = f.data[(m + i) * s + j]
    }
    for j = 0; j < n; j = j + 1 {
      d.data[i * n + j] = f.data[(m + i) * s + m + j]
    }
  }
  SMat::{ m, n, p, a, b, c, d, }
}

///|
/// 齊次隨機超矩陣：parity = 0（偶：b=c=0）/ 1（奇：a=d=0）。
pub fn smat_random(
  r : @core.Rng,
  m : Int32,
  n : Int32,
  p : Int32,
  parity : Int32,
) -> SMat {
  let s = m + n
  let f = @core.mat_make(s, s, 0)
  for i = 0; i < s; i = i + 1 {
    for j = 0; j < s; j = j + 1 {
      let same = (i < m && j < m) || (i >= m && j >= m) // 對角方塊
      let want = if parity == 0 { same } else { !same }
      if want {
        f.data[i * s + j] = @core.rng_below(r, p)
      }
    }
  }
  smat_from_full(m, n, p, f)
}

///|
/// 超矩陣乘法（經全陣；F_p 上與方塊乘法一致）。
pub fn smat_mul(x : SMat, y : SMat) -> SMat {
  smat_from_full(x.m, x.n, x.p, @core.mat_mul(smat_full(x), smat_full(y), x.p))
}

///|
/// 加法。
pub fn smat_add(x : SMat, y : SMat) -> SMat {
  smat_from_full(x.m, x.n, x.p, @core.mat_add(smat_full(x), smat_full(y), x.p))
}

///|
/// 純量乘。
pub fn smat_scale(x : SMat, c : Int32) -> SMat {
  smat_from_full(x.m, x.n, x.p, @core.mat_scale(smat_full(x), c, x.p))
}

///| [S-D-st] 超轉置：st [[A,B],[C,D]] = [[Aᵀ, −Cᵀ],[Bᵀ, Dᵀ]]。

///|
/// 號規由 [S-T-st] 的計算釘死：滿足 (MN)^st = (−1)^{|M||N|} N^st M^st。
pub fn smat_st(x : SMat) -> SMat {
  let p = x.p
  let at = @core.mat_transpose(x.a)
  let bt = @core.mat_transpose(x.b)
  let ct = @core.mat_transpose(x.c)
  let dt = @core.mat_transpose(x.d)
  let nct = @core.mat_scale(ct, p - 1, p)
  SMat::{ m: x.m, n: x.n, p, a: at, b: nct, c: bt, d: dt, }
}

///|
/// [S-D-str] 超跡：str M = tr A − tr D。
pub fn smat_str(x : SMat) -> Int32 {
  let mut ta = 0
  for i = 0; i < x.m; i = i + 1 {
    ta = ta + x.a.data[i * x.m + i]
  }
  let mut td = 0
  for i = 0; i < x.n; i = i + 1 {
    td = td + x.d.data[i * x.n + i]
  }
  ((ta - td) % x.p + x.p) % x.p
}

///|
/// [S-D-sbr] 超交換子：[X,Y]_s = XY − (−1)^{|X||Y|} YX（齊次輸入）。
pub fn smat_sbr(x : SMat, y : SMat, px : Int32, py : Int32) -> SMat {
  let xy = smat_mul(x, y)
  let yx = smat_mul(y, x)
  if px * py % 2 == 1 {
    smat_add(xy, yx)
  } else {
    smat_from_full(
      x.m,
      x.n,
      x.p,
      @core.mat_add(
        smat_full(xy),
        @core.mat_scale(smat_full(yx), x.p - 1, x.p),
        x.p,
      ),
    )
  }
}

///| -------------------------------------------- Grassmann 係數偶超矩陣 (GL(m|n))

///|
/// 齊次「偶」超矩陣：a、d 方塊 = 偶 Λ 元素；b、c 方塊 = 奇 Λ 元素。
pub struct SMatG {
  m : Int32
  n : Int32
  g : Gr
  a : Array[Array[Array[Int32]]] // m×m 偶
  b : Array[Array[Array[Int32]]] // m×n 奇
  c : Array[Array[Array[Int32]]] // n×m 奇
  d : Array[Array[Array[Int32]]] // n×n 偶
}

///|
/// 由方塊構造（黑箱測試/實驗用）。
pub fn smatg_of(
  m : Int32,
  n : Int32,
  g : Gr,
  a : Array[Array[Array[Int32]]],
  b : Array[Array[Array[Int32]]],
  c : Array[Array[Array[Int32]]],
  d : Array[Array[Array[Int32]]],
) -> SMatG {
  SMatG::{ m, n, g, a, b, c, d, }
}

///|
/// 把 b、c 方塊零化（分塊對角化）——Ber(diag) 實驗用。
pub fn smatg_diagonalize(x : SMatG) -> SMatG {
  let z1 : Array[Array[Array[Int32]]] = []
  for i = 0; i < x.m; i = i + 1 {
    let row : Array[Array[Int32]] = []
    for j = 0; j < x.n; j = j + 1 {
      let _ = row.push(gr_zero(x.g))
    }
    let _ = z1.push(row)
  }
  let z2 : Array[Array[Array[Int32]]] = []
  for i = 0; i < x.n; i = i + 1 {
    let row : Array[Array[Int32]] = []
    for j = 0; j < x.m; j = j + 1 {
      let _ = row.push(gr_zero(x.g))
    }
    let _ = z2.push(row)
  }
  SMatG::{ m: x.m, n: x.n, g: x.g, a: x.a, b: z1, c: z2, d: x.d, }
}

///| 純量型偶超矩陣 I + ε·s：a = (1+εs)·I_m、d = (1+εs)·I_n、b = c = 0。

///|
/// [S-T-BerExp1] 用：Ber(I+ε·s) = 1 + ε·s·(m−n)。
pub fn smatg_scalar_eps(
  g : Gr,
  m : Int32,
  n : Int32,
  eps : Array[Int32],
  s : Int32,
) -> SMatG {
  fn eye_eps(dim : Int32) -> Array[Array[Array[Int32]]] {
    let out : Array[Array[Array[Int32]]] = []
    for i = 0; i < dim; i = i + 1 {
      let row : Array[Array[Int32]] = []
      for j = 0; j < dim; j = j + 1 {
        let e = if i == j {
          gr_add(g, gr_one(g), gr_scale(g, eps, s))
        } else {
          gr_zero(g)
        }
        let _ = row.push(e)
      }
      let _ = out.push(row)
    }
    out
  }
  let zb : Array[Array[Array[Int32]]] = []
  for i = 0; i < m; i = i + 1 {
    let row : Array[Array[Int32]] = []
    for j = 0; j < n; j = j + 1 {
      let _ = row.push(gr_zero(g))
    }
    let _ = zb.push(row)
  }
  let zc : Array[Array[Array[Int32]]] = []
  for i = 0; i < n; i = i + 1 {
    let row : Array[Array[Int32]] = []
    for j = 0; j < m; j = j + 1 {
      let _ = row.push(gr_zero(g))
    }
    let _ = zc.push(row)
  }
  SMatG::{ m, n, g, a: eye_eps(m), b: zb, c: zc, d: eye_eps(n), }
}

///|
/// 隨機可逆偶超矩陣：a、d 的 body 隨機可逆，b、c 隨機奇元素。
pub fn smatg_random(r : @core.Rng, g : Gr, m : Int32, n : Int32) -> SMatG {
  let sz = gr_size(g)
  fn rand_even(r : @core.Rng, g : Gr, sz : Int32) -> Array[Int32] {
    let e = gr_zero(g)
    e[0] = 1 + @core.rng_below(r, g.p - 1) // body 非零（unit）
    for i = 1; i < sz; i = i + 1 {
      if popcount(i) % 2 == 0 {
        e[i] = @core.rng_below(r, g.p)
      }
    }
    e
  }
  fn rand_odd(r : @core.Rng, g : Gr, sz : Int32) -> Array[Int32] {
    let e = gr_zero(g)
    for i = 1; i < sz; i = i + 1 {
      if popcount(i) % 2 == 1 {
        e[i] = @core.rng_below(r, g.p)
      }
    }
    e
  }
  let a : Array[Array[Array[Int32]]] = []
  for i = 0; i < m; i = i + 1 {
    let row : Array[Array[Int32]] = []
    for j = 0; j < m; j = j + 1 {
      let _ = row.push(rand_even(r, g, sz))
    }
    let _ = a.push(row)
  }
  let b : Array[Array[Array[Int32]]] = []
  for i = 0; i < m; i = i + 1 {
    let row : Array[Array[Int32]] = []
    for j = 0; j < n; j = j + 1 {
      let _ = row.push(rand_odd(r, g, sz))
    }
    let _ = b.push(row)
  }
  let c : Array[Array[Array[Int32]]] = []
  for i = 0; i < n; i = i + 1 {
    let row : Array[Array[Int32]] = []
    for j = 0; j < m; j = j + 1 {
      let _ = row.push(rand_odd(r, g, sz))
    }
    let _ = c.push(row)
  }
  let d : Array[Array[Array[Int32]]] = []
  for i = 0; i < n; i = i + 1 {
    let row : Array[Array[Int32]] = []
    for j = 0; j < n; j = j + 1 {
      let _ = row.push(rand_even(r, g, sz))
    }
    let _ = d.push(row)
  }
  SMatG::{ m, n, g, a, b, c, d, }
}

///|
/// Grassmann 超矩陣乘法（方塊乘法，Λ 係數）。
pub fn smatg_mul(x : SMatG, y : SMatG) -> SMatG {
  let g = x.g
  let a = even_mat_add(
    g,
    even_mat_mul(g, x.a, y.a),
    even_mat_mul(g, x.b, y.c),
    1,
  )
  let b = even_mat_add(
    g,
    even_mat_mul(g, x.a, y.b),
    even_mat_mul(g, x.b, y.d),
    1,
  )
  let c = even_mat_add(
    g,
    even_mat_mul(g, x.c, y.a),
    even_mat_mul(g, x.d, y.c),
    1,
  )
  let d = even_mat_add(
    g,
    even_mat_mul(g, x.c, y.b),
    even_mat_mul(g, x.d, y.d),
    1,
  )
  SMatG::{ m: x.m, n: x.n, g, a, b, c, d, }
}

///| [S-D-Ber] Berezinian：Ber M = det(A − B·D⁻¹·C) · det(D)⁻¹

///|
/// （D 可逆時；A − BD⁻¹C 的元素：奇·偶⁻¹·奇 = 偶 ✓）。
pub fn smatg_ber(x : SMatG) -> Array[Int32]? {
  let g = x.g
  let dinv = even_mat_inv(g, x.d)
  if dinv is None {
    return None
  }
  if dinv is Some(di) {
    let bd = even_mat_mul(g, x.b, di)
    let bdc = even_mat_mul(g, bd, x.c)
    let schur = even_mat_add(g, x.a, bdc, g.p - 1) // A − B D⁻¹ C
    let detS = even_det(g, schur)
    let detD = even_det(g, x.d)
    if gr_is_unit(g, detD) {
      Some(gr_mul(g, detS, gr_inv(g, detD)))
    } else {
      None
    }
  } else {
    None
  }
}

///|
/// [S-D-strG] Grassmann 超矩陣的超跡：str M = tr(A) − tr(D)（Λ 偶元素之差）。
pub fn smatg_str(x : SMatG) -> Array[Int32] {
  let g = x.g
  let m = x.m
  let n = x.n
  let mut ta = gr_zero(g)
  for i = 0; i < m; i = i + 1 {
    ta = gr_add(g, ta, x.a[i][i])
  }
  let mut td = gr_zero(g)
  for i = 0; i < n; i = i + 1 {
    td = gr_add(g, td, x.d[i][i])
  }
  gr_add(g, ta, gr_scale(g, td, g.p - 1))
}

///| Berezinian（A-branch 對照版）：Ber' M = det(A) · det(D − C A⁻¹ B)⁻¹。

///|
/// [S-T-BerBranch]：兩個 Schur 分支在 Λ 係數下給出相同的 Ber。
pub fn smatg_ber_abranch(x : SMatG) -> Array[Int32]? {
  let g = x.g
  let ainv = even_mat_inv(g, x.a)
  if ainv is None {
    return None
  }
  if ainv is Some(ai) {
    let ca = even_mat_mul(g, x.c, ai)
    let cab = even_mat_mul(g, ca, x.b)
    let schur = even_mat_add(g, x.d, cab, g.p - 1) // D − C A⁻¹ B
    let detD = even_det(g, schur)
    let detA = even_det(g, x.a)
    if gr_is_unit(g, detD) {
      Some(gr_mul(g, detA, gr_inv(g, detD)))
    } else {
      None
    }
  } else {
    None
  }
}

///| ---------------------------------------------------- 展平對稱性：維度定理

///| [S-T-FlatSym] 的組合部分：m 個偶 + n 個奇生成元的次數 d 單項式個數，

///|
/// 以暴力遞迴枚舉（even 指數任意、odd 至多取一次）。
pub fn count_monomials(m : Int32, n : Int32, d : Int32) -> Int32 {
  // 遞迴：先配偶生成元指數，再配奇子集
  fn rec_even(mi : Int32, rem : Int32, odd_left : Int32, acc : Int32) -> Int32 {
    if mi == m {
      // 奇部分：選大小 ≤ rem 的子集使總次數 = rem ⟹ 恰選大小 rem 的子集（若 rem ≤ n）
      if rem <= odd_left {
        return acc * @algebra.int_binom(odd_left, rem)
      }
      return 0
    }
    let mut total = 0
    let mut e = 0
    while e <= rem {
      total = total + rec_even(mi + 1, rem - e, odd_left, acc)
      e = e + 1
    }
    total
  }
  rec_even(0, d, n, 1)
}

///|
/// 二項係數（Int64 內部運算；範圍內精確）。
///|
/// 32 位元邏輯右移（經 UInt 避免 Int 的算術移位）。
