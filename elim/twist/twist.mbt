///| ## twist —— 扭曲 K-理論（群上同調、twisted group algebra、gauge 不變量）

///|

///| 全部計算都是有限線性代數：上鏈空間是 F_ℓ 上的向量空間，δ 是矩陣，

///| H²(G, Z/ℓ) = ker δ² / im δ¹ 由消元（rank）算出；twisted group algebra

///| 的中心由另一組消元算出，並與 bicharacter 的 radical 比對。
// ===================== 群與上鏈 =====================

///|
/// [D-Grp] G = ∏ Z/n_i 的資料（各階皆 ≥ 2）。
pub struct Grp {
  orders : Array[Int32]
}

///|
/// [D-GrpMk] 群構造子：grp([n1, n2, ...]) = Z/n1 × Z/n2 × …。
pub fn grp(orders : Array[Int32]) -> Grp {
  Grp::{ orders, }
}

///|
/// [D-Zero] 零元素（全 0 向量）。
pub fn grp_zero(g : Grp) -> Array[Int32] {
  Array::makei(g.orders.length(), _ => 0)
}

///|
/// [D-Code] 混合進位碼：code(a) = Σ_i a_i · ∏_{j<i} n_j ∈ [0, |G|)。零元素 ⟺ code = 0。
pub fn grp_code(g : Grp, a : Array[Int32]) -> Int32 {
  let n = g.orders.length()
  let mut code = 0
  let mut mult = 1
  let mut i = 0
  while i < n {
    code = code + a[i] * mult
    mult = mult * g.orders[i]
    i = i + 1
  }
  code
}

///|
/// [D-Decode] 碼 → 元素。
pub fn grp_of_code(g : Grp, code : Int32) -> Array[Int32] {
  let n = g.orders.length()
  let out = Array::makei(n, _ => 0)
  let mut r = code
  let mut i = 0
  while i < n {
    out[i] = r % g.orders[i]
    r = r / g.orders[i]
    i = i + 1
  }
  out
}

///|
/// [Ax-Grp] 群加法（逐分量 mod n_i）。
pub fn grp_add(g : Grp, a : Array[Int32], b : Array[Int32]) -> Array[Int32] {
  let n = g.orders.length()
  let out = Array::makei(n, _ => 0)
  let mut i = 0
  while i < n {
    out[i] = (a[i] + b[i]) % g.orders[i]
    i = i + 1
  }
  out
}

///|
pub fn grp_neg(g : Grp, a : Array[Int32]) -> Array[Int32] {
  let n = g.orders.length()
  Array::makei(n, i => (g.orders[i] - a[i]) % g.orders[i])
}

///|
/// [D-Order] |G|。
pub fn grp_order(g : Grp) -> Int32 {
  let mut m = 1
  for n in g.orders {
    m = m * n
  }
  m
}

///|
/// [Ax-GrpAxiom] 驗算群公理：結合律、單位元、反元素、交換律（逐元素枚舉）。
pub fn check_group_axioms(g : Grp) -> Bool {
  let n = grp_order(g)
  let z = grp_zero(g)
  let mut a = 0
  while a < n {
    let mut b = 0
    while b < n {
      let mut c = 0
      while c < n {
        let av = grp_of_code(g, a)
        let bv = grp_of_code(g, b)
        let cv = grp_of_code(g, c)
        let l = grp_add(g, grp_add(g, av, bv), cv)
        let r = grp_add(g, av, grp_add(g, bv, cv))
        if grp_code(g, l) != grp_code(g, r) {
          return false
        }
        if grp_code(g, grp_add(g, av, bv)) != grp_code(g, grp_add(g, bv, av)) {
          return false
        }
        c = c + 1
      }
      if grp_code(g, grp_add(g, grp_of_code(g, a), z)) != a {
        return false
      }
      if grp_code(
          g,
          grp_add(g, grp_of_code(g, a), grp_neg(g, grp_of_code(g, a))),
        ) !=
        0 {
        return false
      }
      b = b + 1
    }
    a = a + 1
  }
  true
}

// ---- 上鏈（扁平表，索引 code(a)*|G| + code(b)，值在 Z/ℓ）----

///|
fn co_get(n : Int32, w : Array[Int32], ac : Int32, bc : Int32) -> Int32 {
  w[ac * n + bc]
}

///|
fn co_set(
  n : Int32,
  w : Array[Int32],
  ac : Int32,
  bc : Int32,
  v : Int32,
  ell : Int32,
) -> Unit {
  w[ac * n + bc] = (v % ell + ell) % ell
}

///|
/// [D-VarIdx] 歸一化座標索引；-1 代表該位置被歸一化固定為 0。
pub fn var_index(g : Grp, ac : Int32, bc : Int32) -> Int32 {
  let n = grp_order(g)
  if ac == 0 || bc == 0 {
    -1
  } else {
    (ac - 1) * (n - 1) + (bc - 1)
  }
}

///|
/// [D-VarCount] 歸一化 2-上鏈的自由維數 = (|G|-1)²。
pub fn var_count(g : Grp) -> Int32 {
  let n = grp_order(g)
  (n - 1) * (n - 1)
}

///|
/// [Ax-Cochain] 由自由座標向量展開成完整上鏈表（長度 |G|²）。
pub fn cochain_expand(g : Grp, vec : Array[Int32], ell : Int32) -> Array[Int32] {
  let n = grp_order(g)
  let w = Array::make(n * n, 0)
  let n1 = n - 1
  let mut i = 1
  while i < n {
    let mut j = 1
    while j < n {
      co_set(n, w, i, j, vec[(i - 1) * n1 + (j - 1)], ell)
      j = j + 1
    }
    i = i + 1
  }
  w
}

// ===================== δ 矩陣：消元引擎的直接應用 =====================

///|
/// [D-D2] δ² : C² → C³ 的矩陣（F_ℓ 係數）。列 = 三元組 (a,b,c)，
///   (δω)(a,b,c) = ω(b,c) - ω(a+b,c) + ω(a,b+c) - ω(a,b)；零列被省略（同秩）。
pub fn d2_matrix(g : Grp, ell : Int32) -> @core.Mat {
  let n = grp_order(g)
  let nv = var_count(g)
  let rows_arr : Array[Array[Int32]] = []
  let mut a = 0
  while a < n {
    let mut b = 0
    while b < n {
      let mut c = 0
      while c < n {
        let row = Array::make(nv, 0)
        let av = grp_of_code(g, a)
        let bv = grp_of_code(g, b)
        let cv = grp_of_code(g, c)
        let ab = grp_code(g, grp_add(g, av, bv))
        let bc = grp_code(g, grp_add(g, bv, cv))
        let terms : Array[(Int32, Int32, Int32)] = [
          (b, c, 1),
          (ab, c, -1),
          (a, bc, 1),
          (a, b, -1),
        ]
        for (x, y, sgn) in terms {
          let v = var_index(g, x, y)
          if v >= 0 {
            row[v] = ((row[v] + sgn) % ell + ell) % ell
          }
        }
        if !row.all(x => x == 0) {
          let _ = rows_arr.push(row)
        }
        c = c + 1
      }
      b = b + 1
    }
    a = a + 1
  }
  @core.mat_from_rows(rows_arr)
}

///|
/// [D-D1] δ¹ : C¹ → C² 的矩陣（F_ℓ 係數）。列 = C¹ 的基向量 μ_x（x 非零），
///   (δμ)(a,b) = μ(a) + μ(b) - μ(a+b)。
pub fn d1_matrix(g : Grp, ell : Int32) -> @core.Mat {
  let n = grp_order(g)
  let nv = var_count(g)
  let rows_arr : Array[Array[Int32]] = []
  let mut x = 1
  while x < n {
    let row = Array::make(nv, 0)
    let mut a = 1
    while a < n {
      let mut b = 1
      while b < n {
        let ab = grp_code(g, grp_add(g, grp_of_code(g, a), grp_of_code(g, b)))
        let mut v = 0
        if a == x {
          v = v + 1
        }
        if b == x {
          v = v + 1
        }
        if ab == x {
          v = v - 1
        }
        row[(a - 1) * (n - 1) + (b - 1)] = (v % ell + ell) % ell
        b = b + 1
      }
      a = a + 1
    }
    let _ = rows_arr.push(row)
    x = x + 1
  }
  @core.mat_from_rows(rows_arr)
}

///|
/// [T-H2-Rank] dim Z² = (|G|-1)² - rank δ²，dim B² = rank δ¹，
///   dim H² = dim Z² - dim B²；並驗證鏈條件 δ²∘δ¹ = 0。
pub fn h2_compute(g : Grp, ell : Int32) -> (Int32, Int32, Int32, Bool) {
  let d2 = d2_matrix(g, ell)
  let d1 = d1_matrix(g, ell)
  let nv = var_count(g)
  let fld = @core.mk_field(ell)
  let dim_z2 = nv - @core.gauss_jordan(d2, fld).rank
  let dim_b2 = @core.gauss_jordan(d1, fld).rank
  let prod = @core.mat_mul(d2, @core.mat_transpose(d1), ell)
  let chain_ok = @core.mat_is_zero(prod)
  (dim_z2, dim_b2, dim_z2 - dim_b2, chain_ok)
}

///|
/// [T-H2-Elem] 驗證 G = (Z/ℓ)^k 時 dim H²(G, Z/ℓ) = k(k+1)/2。
pub fn h2_dim(g : Grp, ell : Int32) -> Int32 {
  let (_, _, h, _) = h2_compute(g, ell)
  h
}

///|
/// [D-H1] dim H¹(G, Z/ℓ) = (|G|-1) - rank δ¹。
pub fn h1_dim(g : Grp, ell : Int32) -> Int32 {
  let d1 = d1_matrix(g, ell)
  let fld = @core.mk_field(ell)
  let n = grp_order(g)
  n - 1 - @core.gauss_jordan(d1, fld).rank
}

// ===================== ω-twisted group algebra =====================

///|
/// [D-Omega] 指數形式的 2-cocycle ω : G×G → Z/ℓ，實現於 F_p（ζ = ℓ 次本原根）：
///   e_a·e_b = ζ^{ω(a,b)} e_{a+b}。
pub struct Omega {
  g : Grp
  ell : Int32
  field : Int32
  zeta : Int32
  w : Array[Int32]
}

///|
/// [D-Root] 在 F_p^× 中找 ℓ 次本原單位根（需 ℓ | p-1）；無解回傳 -1。
pub fn primitive_root(ell : Int32, p : Int32) -> Int32 {
  let mut g = 2
  while g < p {
    let mut ok = @core.mod_pow(g, ell, p) == 1
    let mut j = 1
    while j < ell {
      if @core.mod_pow(g, j, p) == 1 {
        ok = false
      }
      j = j + 1
    }
    if ok {
      return g
    }
    g = g + 1
  }
  -1
}

///|
/// [D-MkOmega] 由座標向量構造 cocycle（假定已屬 Z²；用 omega_is_cocycle 驗）。
pub fn mk_omega(g : Grp, ell : Int32, p : Int32, vec : Array[Int32]) -> Omega {
  let z = primitive_root(ell, p)
  Omega::{ g, ell, field: p, zeta: z, w: cochain_expand(g, vec, ell), }
}

///|
pub fn omega_get(o : Omega, ac : Int32, bc : Int32) -> Int32 {
  co_get(grp_order(o.g), o.w, ac, bc)
}

///|
/// [Ax-Omega] 結合律 ⟺ cocycle 條件：直接逐三元組驗證。
pub fn omega_is_cocycle(o : Omega) -> Bool {
  let g = o.g
  let n = grp_order(g)
  let mut a = 0
  while a < n {
    let mut b = 0
    while b < n {
      let mut c = 0
      while c < n {
        let av = grp_of_code(g, a)
        let bv = grp_of_code(g, b)
        let cv = grp_of_code(g, c)
        let bc = grp_code(g, grp_add(g, bv, cv))
        let ab = grp_code(g, grp_add(g, av, bv))
        let lhs = (omega_get(o, b, c) + omega_get(o, a, bc)) % o.ell
        let rhs = (omega_get(o, ab, c) + omega_get(o, a, b)) % o.ell
        if ((lhs - rhs) % o.ell + o.ell) % o.ell != 0 {
          return false
        }
        c = c + 1
      }
      b = b + 1
    }
    a = a + 1
  }
  true
}

///|
/// [D-Rad] rad(b_ω) = { a : ∀b, ω(a,b) ≡ ω(b,a) (mod ℓ) }。
pub fn omega_radical(o : Omega) -> Array[Int32] {
  let n = grp_order(o.g)
  let out : Array[Int32] = []
  let mut a = 0
  while a < n {
    let mut ok = true
    let mut b = 0
    while b < n {
      if omega_get(o, a, b) != omega_get(o, b, a) {
        ok = false
      }
      b = b + 1
    }
    if ok {
      let _ = out.push(a)
    }
    a = a + 1
  }
  out
}

///|
pub fn omega_radical_size(o : Omega) -> Int32 {
  omega_radical(o).length()
}

///|
/// [D-CtrMat] 中心的線性系統：x = Σ_a x_a e_a 為中心元素 ⟺ 對所有 (b,c)：
///   x_{c-b} · (ζ^{ω(c-b,b)} - ζ^{ω(b,c-b)}) = 0。
pub fn center_matrix(o : Omega) -> @core.Mat {
  let g = o.g
  let n = grp_order(g)
  let p = o.field
  let rows_arr : Array[Array[Int32]] = []
  let mut b = 0
  while b < n {
    let mut c = 0
    while c < n {
      let row = Array::make(n, 0)
      let a = grp_code(
        g,
        grp_add(g, grp_of_code(g, c), grp_neg(g, grp_of_code(g, b))),
      )
      let s1 = omega_get(o, a, b)
      let s2 = omega_get(o, b, a)
      if s1 != s2 {
        let v = (
            @core.mod_pow(o.zeta, s1, p) - @core.mod_pow(o.zeta, s2, p) + p
          ) %
          p
        row[a] = v
      }
      let _ = rows_arr.push(row)
      c = c + 1
    }
    b = b + 1
  }
  @core.mat_from_rows(rows_arr)
}

///|
/// [T-TwCenter] dim Z(F_p^ω[G]) = |rad(b_ω)|（左側由消元算出，右側由定義枚舉算出）。
pub fn center_dim(o : Omega) -> Int32 {
  let m = center_matrix(o)
  let fld = @core.mk_field(o.field)
  let n = grp_order(o.g)
  n - @core.gauss_jordan(m, fld).rank
}

///|
/// [D-TwSq] d² = |G| / |rad(b_ω)|：既約 ω-射影表示的維數平方。
pub fn tw_irrep_dim_sq(o : Omega) -> Int32 {
  let n = grp_order(o.g)
  let r = omega_radical_size(o)
  n / r
}

///|
/// [D-Sq] 完全平方數判定。
pub fn is_perfect_square(m : Int32) -> Bool {
  if m < 0 {
    false
  } else {
    let mut d = 0
    let mut found = false
    while !found && d * d <= m {
      if d * d == m {
        found = true
      }
      d = d + 1
    }
    found
  }
}

///|
/// [D-TwK0] K₀^ω(G) := R^ω(G) ≅ Z^{#既約 ω-表示} = Z^{dim Z(A^ω)}；回傳秩。
pub fn tw_k0_rank(o : Omega) -> Int32 {
  center_dim(o)
}

// ===================== gauge（coboundary）流 =====================

///|
/// [D-Gauge] gauge 變換：ω ⟼ ω + δμ，(δμ)(a,b) = μ(a) + μ(b) - μ(a+b)。
pub fn omega_gauge(o : Omega, mu : Array[Int32]) -> Array[Int32] {
  let g = o.g
  let n = grp_order(g)
  let w = o.w.copy()
  let mut a = 0
  while a < n {
    let mut b = 0
    while b < n {
      let ab = grp_code(g, grp_add(g, grp_of_code(g, a), grp_of_code(g, b)))
      let dv = ((mu[a] + mu[b] - mu[ab]) % o.ell + o.ell) % o.ell
      co_set(n, w, a, b, co_get(n, o.w, a, b) + dv, o.ell)
      b = b + 1
    }
    a = a + 1
  }
  w
}

///|
pub fn omega_with_w(o : Omega, w : Array[Int32]) -> Omega {
  Omega::{ g: o.g, ell: o.ell, field: o.field, zeta: o.zeta, w, }
}

///|
/// [T-Tw-Gauge] gauge 不變性：回傳 (rad、dim Z、K₀ 秩皆不變, φ_μ 是代數同構)。
pub fn check_gauge_invariance(o : Omega, mu : Array[Int32]) -> (Bool, Bool) {
  let g = o.g
  let n = grp_order(g)
  let o2 = omega_with_w(o, omega_gauge(o, mu))
  let inv = omega_radical_size(o) == omega_radical_size(o2) &&
    center_dim(o) == center_dim(o2) &&
    tw_k0_rank(o) == tw_k0_rank(o2)
  let p = o.field
  let mut ok = true
  let mut a = 0
  while a < n {
    let mut b = 0
    while b < n {
      let ab = grp_code(g, grp_add(g, grp_of_code(g, a), grp_of_code(g, b)))
      let l = ((omega_get(o2, a, b) - mu[a] - mu[b]) % o.ell + o.ell) % o.ell
      let r = ((omega_get(o, a, b) - mu[ab]) % o.ell + o.ell) % o.ell
      if @core.mod_pow(o.zeta, l, p) != @core.mod_pow(o.zeta, r, p) {
        ok = false
      }
      b = b + 1
    }
    a = a + 1
  }
  (inv, ok)
}

///|
/// [D-H2Class] 兩 cocycle 同coboundary 類 ⟺ 差在 im δ¹。以消元判定
///   （把差向量加到 d1 的列上，秩不變 ⟺ 差屬於像空間）。
pub fn cohomologous(
  g : Grp,
  ell : Int32,
  u : Array[Int32],
  v : Array[Int32],
) -> Bool {
  let d1 = d1_matrix(g, ell)
  let diff : Array[Int32] = Array::makei(u.length(), i => {
    ((u[i] - v[i]) % ell + ell) % ell
  })
  let rows = @core.mat_rows(d1)
  let _ = rows.push(diff)
  let augmented = @core.mat_from_rows(rows)
  let fld = @core.mk_field(ell)
  @core.gauss_jordan(d1, fld).rank == @core.gauss_jordan(augmented, fld).rank
}

// ===================== 斜對稱部分與偶數秩定理 =====================

///|
/// [D-Skew] 由 ω 的指數表構造 bicharacter 矩陣 M[a,b] = ω(a,b) - ω(b,a) (mod ℓ)。
///   對 G = (Z/ℓ)^k，b_ω 是 F_ℓ-双線型，故 M 是斜對稱矩陣。
pub fn skew_matrix(o : Omega) -> @core.Mat {
  let g = o.g
  let n = grp_order(g)
  let ell = o.ell
  let rows : Array[Array[Int32]] = Array::makei(n, i => {
    Array::makei(n, j => {
      ((omega_get(o, i, j) - omega_get(o, j, i)) % ell + ell) % ell
    })
  })
  @core.mat_from_rows(rows)
}

///|
/// [T-Tw-Rank] 對 G = (Z/ℓ)^k：rank M 為偶數，且 |rad(b_ω)| = ℓ^{k - rank M}。
///   回傳 (秩為偶數, radical 尺寸公式成立)。
pub fn check_skew_rank_formula(o : Omega) -> (Bool, Bool) {
  let m = skew_matrix(o)
  let fld = @core.mk_field(o.ell)
  let k = o.g.orders.length()
  let ell = o.ell
  let r = @core.rank_mod(m, fld)
  let mut pw = 1
  let mut i = 0
  while i < k - r {
    pw = pw * ell
    i = i + 1
  }
  (r % 2 == 0, omega_radical_size(o) == pw)
}
