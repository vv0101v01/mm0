///| ## gauge —— 拉蒙零模（Clifford 代數）與格點規範場（線叢）

///|

///| 兩部分共用同一套「twisted group algebra」語言：

///|  * 拉蒙（Ramond）零模代數 = Cl_d，其生成元由 Jordan–Wigner 構造在 F_p 上具體實現，

///|    且精確地是 (Z/2)^d 帶有 bilinear cocycle ω(a,b)=Σ_{i>j} a_i b_j 的 twisted group algebra；

///|  * 格點規範場 = torus 上以 Z/ℓ 為結構群的線叢，規範變換 = Cech 1-coboundary，

///|    平坦模空間 = H¹(T², Z/ℓ)。

///| 所有判定都以有限枚舉 + `@core` 消元驗證。
// ===================== A. 拉蒙零模 / Clifford =====================

///|
/// [D-Pauli] Pauli 矩陣（F_p，p 為奇素數；i = √-1 需存在以構造 Y）。
pub fn pauli_x() -> @core.Mat {
  @core.mat_from_rows([[0, 1], [1, 0]])
}

///|
pub fn pauli_z(p : Int32) -> @core.Mat {
  @core.mat_from_rows([[1, 0], [0, p - 1]])
}

///|
/// [D-PauliY] Y = i·X·Z，其中 i² = -1；F_p 中 i 存在 ⟺ p ≡ 1 (mod 4)。
pub fn pauli_y(p : Int32) -> Int32? {
  let mut i = 1
  while i < p {
    if i * i % p == p - 1 {
      return Some(i)
    }
    i = i + 1
  }
  None
}

///|
/// [D-PauliStr] 字串积 ⊗_q P_{ops[q]}，P_0=I, P_1=X, P_2=Y, P_3=Z。
pub fn pauli_string(ops : Array[Int32], p : Int32) -> @core.Mat {
  let iu = match pauli_y(p) {
    Some(v) => v
    None => 0
  }
  let mut acc = @core.mat_build(1, 1, (_a, _b) => 1 % p)
  for o in ops {
    let piece = if o == 1 {
      pauli_x()
    } else if o == 2 {
      @core.mat_build(2, 2, (a, b) => {
        if a == 0 && b == 1 {
          (p - iu) % p
        } else if a == 1 && b == 0 {
          iu % p
        } else {
          0
        }
      })
    } else if o == 3 {
      pauli_z(p)
    } else {
      @core.mat_build(2, 2, (a, b) => if a == b { 1 % p } else { 0 })
    }
    acc = @tensor.kron_mat(acc, piece, p)
  }
  acc
}

///|
/// [D-Gamma] Jordan–Wigner：m = ⌊d/2⌋ 個 qubit，2^m 維。
///   γ_{2j} = Z^{⊗j}⊗X⊗I^{⊗(m-1-j)}, γ_{2j+1} = Z^{⊗j}⊗Y⊗I^{⊗(m-1-j)}；
///   d 為奇數時再加 γ_{d-1} = Z^{⊗m}（體積元素，與所有 γ 反對易）。
pub fn gamma_mats(d : Int32, p : Int32) -> Array[@core.Mat] {
  let m = d / 2
  let out : Array[@core.Mat] = []
  let mut j = 0
  while 2 * j + 1 < d {
    let ops_x = Array::makei(m, q => {
      if q < j {
        3
      } else if q == j {
        1
      } else {
        0
      }
    })
    let ops_y = Array::makei(m, q => {
      if q < j {
        3
      } else if q == j {
        2
      } else {
        0
      }
    })
    let _ = out.push(pauli_string(ops_x, p))
    let _ = out.push(pauli_string(ops_y, p))
    j = j + 1
  }
  if 2 * m < d {
    let ops_z = Array::make(m, 3)
    let _ = out.push(pauli_string(ops_z, p))
  }
  out
}

///|
/// [T-Cliff] Clifford 關係：{γ_a, γ_b} = 2δ_{ab}·I（在 char ≠ 2 的 F_p 中）。
pub fn check_clifford(d : Int32, p : Int32) -> Bool {
  let gs = gamma_mats(d, p)
  let m = gs.length()
  let sz = @algebra.int_pow(2, d / 2)
  let idn = @core.mat_identity(sz)
  let mut ok = m == d
  let mut a = 0
  while a < m {
    let mut b = 0
    while b < m {
      let ab = @core.mat_mul(gs[a], gs[b], p)
      let ba = @core.mat_mul(gs[b], gs[a], p)
      let lhs = @core.mat_add(ab, ba, p)
      let rhs = if a == b {
        @core.mat_scale(idn, 2 % p, p)
      } else {
        @core.mat_scale(idn, 0, p)
      }
      if !@core.mat_eq_mod(lhs, rhs, p) {
        ok = false
      }
      b = b + 1
    }
    a = a + 1
  }
  ok
}

///|
/// [D-SpinorDim] 既約旋量維數 = 2^{⌊d/2⌋}（複雜 Clifford 代數）。
pub fn spinor_dim(d : Int32) -> Int32 {
  @algebra.int_pow(2, d / 2)
}

///|
/// [D-CliffOmega] Cl_d 對應的 cocycle：ω(a,b) = Σ_{i>j} a_i b_j (mod 2)，
///   其中 a,b ∈ (Z/2)^d 是占據數向量。返回 twist 包所用的座標向量。
pub fn clifford_cocycle_vec(d : Int32) -> Array[Int32] {
  let g = @twist.grp(Array::makei(d, _ => 2))
  let n = @twist.grp_order(g)
  let nv = @twist.var_count(g)
  Array::makei(nv, t => {
    let ac = t / (n - 1) + 1
    let bc = t % (n - 1) + 1
    let av = @twist.grp_of_code(g, ac)
    let bv = @twist.grp_of_code(g, bc)
    let mut s = 0
    let mut i = 0
    while i < d {
      let mut j = 0
      while j < i {
        s = (s + av[i] * bv[j]) % 2
        j = j + 1
      }
      i = i + 1
    }
    s
  })
}

///|
/// [D-Rho] ρ(e_a) = γ_{i_1}γ_{i_2}…（i_1<i_2<… 為 a 的支撑）；ρ(0)=I。
pub fn rho(
  gs : Array[@core.Mat],
  code : Int32,
  d : Int32,
  p : Int32,
) -> @core.Mat {
  let sz = @algebra.int_pow(2, d / 2)
  let g = @twist.grp(Array::makei(d, _ => 2))
  let av = @twist.grp_of_code(g, code)
  let mut acc = @core.mat_identity(sz)
  let mut i = 0
  while i < d {
    if av[i] == 1 {
      acc = @core.mat_mul(acc, gs[i], p)
    }
    i = i + 1
  }
  acc
}

///|
/// [T-Cliff-Twist] ρ 是 twisted group algebra 的同態：
///   ρ(a)ρ(b) = (−1)^{ω(a,b)} ρ(a+b)，並因此給出 Cl_d 的 2^{⌊d/2⌋} 維表示。
pub fn check_clifford_is_twisted(d : Int32, p : Int32) -> Bool {
  let gs = gamma_mats(d, p)
  let g = @twist.grp(Array::makei(d, _ => 2))
  let n = @twist.grp_order(g)
  let vec = clifford_cocycle_vec(d)
  let nv = @twist.var_count(g)
  let omega = (ac : Int32, bc : Int32) => {
    let v = @twist.var_index(g, ac, bc)
    if v < 0 {
      0
    } else {
      vec[v]
    }
  }
  let mut ok = gs.length() == d && @twist.var_count(g) == nv
  let mut a = 0
  while a < n {
    let mut b = 0
    while b < n {
      let ab = @twist.grp_code(
        g,
        @twist.grp_add(g, @twist.grp_of_code(g, a), @twist.grp_of_code(g, b)),
      )
      let lhs = @core.mat_mul(rho(gs, a, d, p), rho(gs, b, d, p), p)
      let sgn = omega(a, b)
      let rhs0 = rho(gs, ab, d, p)
      let rhs = if sgn % 2 == 0 {
        rhs0
      } else {
        @core.mat_scale(rhs0, p - 1, p)
      }
      if !@core.mat_eq_mod(lhs, rhs, p) {
        ok = false
      }
      b = b + 1
    }
    a = a + 1
  }
  ok
}

///|
/// [T-Cliff-Center] 由 twist 包的中心計算得 Cl_d 的中心維數：
///   d 偶 → 1（Cl_d ≅ Mat_{2^{d/2}}，單純）；d 奇 → 2（Cl_d ≅ Mat⊕Mat）。
///   同時校驗 |rad(b_ω)| = 中心維數，且 d_旋量² = |G|/|rad|。
pub fn check_clifford_center(d : Int32, p : Int32) -> (Bool, Bool) {
  let g = @twist.grp(Array::makei(d, _ => 2))
  let vec = clifford_cocycle_vec(d)
  let o = @twist.mk_omega(g, 2, p, vec)
  let cd = @twist.center_dim(o)
  let expect = if d % 2 == 0 { 1 } else { 2 }
  let n = @twist.grp_order(g)
  let dsq = n / cd
  (
    cd == expect,
    @twist.is_perfect_square(dsq) && dsq == @algebra.int_pow(spinor_dim(d), 2),
  )
}

///|
/// [T-Cliff-Chi] 手徵算子 γ_* = ρ(1^d)：γ_*² = (−1)^{d(d-1)/2}·I；
///   d 偶時與所有 γ_a 反對易（手徵分解存在），d 奇時與所有 γ_a 交換（中心）。
pub fn check_chirality(d : Int32, p : Int32) -> Bool {
  if d == 0 {
    return true
  }
  let gs = gamma_mats(d, p)
  let g = @twist.grp(Array::makei(d, _ => 2))
  let allones = @twist.grp_code(g, Array::makei(d, _ => 1))
  let chi = rho(gs, allones, d, p)
  let sz = @algebra.int_pow(2, d / 2)
  let idn = @core.mat_identity(sz)
  let e = d * (d - 1) / 2
  let chi2 = @core.mat_mul(chi, chi, p)
  let sq_ok = if e % 2 == 0 {
    @core.mat_eq_mod(chi2, idn, p)
  } else {
    @core.mat_eq_mod(chi2, @core.mat_scale(idn, (p - 1) % p, p), p)
  }
  let mut comm_ok = true
  let mut a = 0
  while a < gs.length() {
    let l = @core.mat_mul(chi, gs[a], p)
    let r = @core.mat_mul(gs[a], chi, p)
    let good = if d % 2 == 0 {
      @core.mat_eq_mod(l, @core.mat_scale(r, p - 1, p), p)
    } else {
      @core.mat_eq_mod(l, r, p)
    }
    if !good {
      comm_ok = false
    }
    a = a + 1
  }
  sq_ok && comm_ok
}

///|
/// [T-Cliff-Kron] Bott 週期性的代數核心：由 Cl_d 的表示經 ⊗ Mat₂ 構造 Cl_{d+2} 的表示：
///   γ'_a = γ_a ⊗ Z（a<d... 取 a ≤ d-1）, γ'_d = I ⊗ X, γ'_{d+1} = I ⊗ Y。
pub fn check_bott_periodicity(d : Int32, p : Int32) -> Bool {
  let gs = gamma_mats(d, p)
  let m = gs.length()
  let sz = @algebra.int_pow(2, d / 2)
  let idn = @core.mat_identity(sz)
  let zs = pauli_z(p)
  let xs = pauli_x()
  let iu = match pauli_y(p) {
    Some(v) => v
    None => 0
  }
  let ys = @core.mat_build(2, 2, (a, b) => {
    let v = if a == 0 && b == 1 {
      p - iu
    } else if a == 1 && b == 0 {
      iu
    } else {
      0
    }
    v % p
  })
  let new : Array[@core.Mat] = []
  for gm in gs {
    let _ = new.push(@tensor.kron_mat(gm, zs, p))
  }
  let _ = new.push(@tensor.kron_mat(idn, xs, p))
  let _ = new.push(@tensor.kron_mat(idn, ys, p))
  let d2 = d + 2
  let sz2 = @algebra.int_pow(2, d2 / 2)
  let idn2 = @core.mat_identity(sz2)
  let mut ok = new.length() == m + 2
  let mut a = 0
  while a < new.length() {
    let mut b = 0
    while b < new.length() {
      let lhs = @core.mat_add(
        @core.mat_mul(new[a], new[b], p),
        @core.mat_mul(new[b], new[a], p),
        p,
      )
      let rhs = if a == b {
        @core.mat_scale(idn2, 2 % p, p)
      } else {
        @core.mat_scale(idn2, 0, p)
      }
      if !@core.mat_eq_mod(lhs, rhs, p) {
        ok = false
      }
      b = b + 1
    }
    a = a + 1
  }
  ok
}

///|
/// [D-EvenCtr] Cl_d 的偶子代數 Cl_d^even 的中心維數（以消元計算）：
///   基 = {e_a : |a| 偶}，x 中心 ⟺ ∀ 偶 b, ∀ 偶 c: x_{c-b}(ζ^{ω(c-b,b)}-ζ^{ω(b,c-b)}) = 0。
/// [T-Cliff-Even] 結果 = 2（d 偶，手徵分解 S=S⁺⊕S⁻）；= 1（d 奇，無手徵）。
pub fn even_center_dim(d : Int32, p : Int32) -> Int32 {
  let g = @twist.grp(Array::makei(d, _ => 2))
  let n = @twist.grp_order(g)
  let vec = clifford_cocycle_vec(d)
  let omega = (ac : Int32, bc : Int32) => {
    let v = @twist.var_index(g, ac, bc)
    if v < 0 {
      0
    } else {
      vec[v]
    }
  }
  let evens : Array[Int32] = []
  let mut a = 0
  while a < n {
    let av = @twist.grp_of_code(g, a)
    let mut w = 0
    for x in av {
      w = w + x
    }
    if w % 2 == 0 {
      let _ = evens.push(a)
    }
    a = a + 1
  }
  let ne = evens.length()
  let pos : Array[Int32] = Array::make(n, -1)
  let mut i = 0
  while i < ne {
    pos[evens[i]] = i
    i = i + 1
  }
  let rows : Array[Array[Int32]] = []
  let mut bi = 0
  while bi < ne {
    let b = evens[bi]
    let mut ci = 0
    while ci < ne {
      let c = evens[ci]
      let row = Array::make(ne, 0)
      let aa = @twist.grp_code(
        g,
        @twist.grp_add(
          g,
          @twist.grp_of_code(g, c),
          @twist.grp_neg(g, @twist.grp_of_code(g, b)),
        ),
      )
      let s1 = omega(aa, b)
      let s2 = omega(b, aa)
      if s1 != s2 {
        let v = (1 - (p - 1) + p) % p
        row[pos[aa]] = v
      }
      let _ = rows.push(row)
      ci = ci + 1
    }
    bi = bi + 1
  }
  let m = @core.mat_from_rows(rows)
  let fld = @core.mk_field(p)
  ne - @core.gauss_jordan(m, fld).rank
}

// ===================== B. 格點規範場（torus 上的 Z/ℓ 線叢） =====================

///|
/// [D-Lattice] 2n² 條有向邊：每點 (x,y) 有向右與向上兩條；週期邊界 = torus。
pub struct Lattice {
  n : Int32
  ell : Int32
}

///|
pub fn mk_lattice(n : Int32, ell : Int32) -> Lattice {
  Lattice::{ n, ell, }
}

///|
pub fn lat_sites(l : Lattice) -> Int32 {
  l.n * l.n
}

///|
pub fn lat_edges(l : Lattice) -> Int32 {
  2 * l.n * l.n
}

///|
/// [D-Edge] 第 e 條邊：e = 2·(x·n+y) + 0（向右）或 1（向上）。回傳 (起點, 終點)。
pub fn edge_ends(l : Lattice, e : Int32) -> (Int32, Int32) {
  let n = l.n
  let site = e / 2
  let x = site / n
  let y = site % n
  let to = if e % 2 == 0 { (x + 1) % n * n + y } else { x * n + (y + 1) % n }
  (site, to)
}

///|
/// [Ax-Gauge] 規範場 u : edges → Z/ℓ（平移子群 μ_ℓ 的指數表示）。
pub fn gauge_transform(
  l : Lattice,
  u : Array[Int32],
  lam : Array[Int32],
) -> Array[Int32] {
  let ell = l.ell
  Array::makei(u.length(), e => {
    let (from, to) = edge_ends(l, e)
    ((u[e] + lam[from] - lam[to]) % ell + ell) % ell
  })
}

///|
/// [D-Curv] plaquette 曲率：F(x,y) = U_right(x,y) + U_up(x+1,y) - U_right(x,y+1) - U_up(x,y)。
pub fn curvature(l : Lattice, u : Array[Int32]) -> Array[Int32] {
  let n = l.n
  let ell = l.ell
  Array::makei(n * n, i => {
    let x = i / n
    let y = i % n
    let r0 = u[2 * (x * n + y)]
    let u1 = u[2 * ((x + 1) % n * n + y) + 1]
    let r1 = u[2 * (x * n + (y + 1) % n)]
    let u0 = u[2 * (x * n + y) + 1]
    ((r0 + u1 - r1 - u0) % ell + ell) % ell
  })
}

///|
/// [T-Gauge-Inv] 曲率在規範變換下不變（Abel 情形）。
pub fn check_curvature_invariant(
  l : Lattice,
  u : Array[Int32],
  lam : Array[Int32],
) -> Bool {
  let f1 = curvature(l, u)
  let f2 = curvature(l, gauge_transform(l, u, lam))
  let mut ok = true
  let mut i = 0
  while i < f1.length() {
    if f1[i] != f2[i] {
      ok = false
    }
    i = i + 1
  }
  ok
}

///|
/// [T-Gauge-Bianchi] Abelian Bianchi 恆等式：Σ_p F(p) ≡ 0（mod ℓ），對任意規範場。
pub fn check_bianchi(l : Lattice, u : Array[Int32]) -> Bool {
  let f = curvature(l, u)
  let mut s = 0
  for x in f {
    s = (s + x) % l.ell
  }
  s % l.ell == 0
}

///|
/// [D-Hol] 兩個非可縮循環的 holonomy：
///   hx = Σ_x U(right(x,0))（沿 x 繞一圈）、hy = Σ_y U(up(0,y))（沿 y 繞一圈）。
pub fn holonomies(l : Lattice, u : Array[Int32]) -> (Int32, Int32) {
  let n = l.n
  let ell = l.ell
  let mut hx = 0
  let mut x = 0
  while x < n {
    hx = (hx + u[2 * (x * n + 0)]) % ell
    x = x + 1
  }
  let mut hy = 0
  let mut y = 0
  while y < n {
    hy = (hy + u[2 * (0 * n + y) + 1]) % ell
    y = y + 1
  }
  (hx, hy)
}

///|
/// [T-Gauge-Hol] holonomy 是規範不變量。
pub fn check_holonomy_invariant(
  l : Lattice,
  u : Array[Int32],
  lam : Array[Int32],
) -> Bool {
  let (a1, b1) = holonomies(l, u)
  let (a2, b2) = holonomies(l, gauge_transform(l, u, lam))
  a1 == a2 && b1 == b2
}

///|
/// [D-IsFlat] 平坦 ⟺ 所有 plaquette 曲率為 0。
pub fn is_flat(l : Lattice, u : Array[Int32]) -> Bool {
  curvature(l, u).all(x => x == 0)
}

///|
/// [D-CodeField] 把規範場編碼成整數（供軌道去重使用）。
pub fn code_of(l : Lattice, u : Array[Int32]) -> Int32 {
  let mut c = 0
  let mut i = 0
  while i < u.length() {
    c = c * l.ell + u[i]
    i = i + 1
  }
  c
}

///|
/// [D-Canon] 規範 orbits 的典範代表：取所有規範變換後編碼的最小值。
pub fn canonical_code(l : Lattice, u : Array[Int32]) -> Int32 {
  let ns = lat_sites(l)
  let nk = @algebra.int_pow(l.ell, ns)
  let mut best = -1
  let mut k = 0
  while k < nk {
    let lam = Array::makei(ns, i => k / @algebra.int_pow(l.ell, i) % l.ell)
    let v = code_of(l, gauge_transform(l, u, lam))
    if best < 0 || v < best {
      best = v
    }
    k = k + 1
  }
  best
}

///|
/// [T-Gauge-Moduli] 枚舉全部規範場，得 (平坦場數, 平坦軌道數)；
///   理論預測：平坦場 = ℓ^{2n²-(n²-1)} = ℓ^{n²+1}，軌道數 = |H¹(T²,Z/ℓ)| = ℓ²。
pub fn flat_moduli(l : Lattice) -> (Int32, Int32) {
  let ne = lat_edges(l)
  let total = @algebra.int_pow(l.ell, ne)
  let reps : Array[Int32] = []
  let mut nflat = 0
  let mut k = 0
  while k < total {
    let u = Array::makei(ne, i => k / @algebra.int_pow(l.ell, i) % l.ell)
    if is_flat(l, u) {
      nflat = nflat + 1
      let c = canonical_code(l, u)
      if !reps.any(x => x == c) {
        let _ = reps.push(c)
      }
    }
    k = k + 1
  }
  (nflat, reps.length())
}

///|
/// [T-Gauge-Moduli-Bij] 平坦場之間：同軌道 ⟺ 同 holonomy（回傳是否雙射且計數相符）。
pub fn check_moduli_bijective(l : Lattice) -> (Bool, Int32) {
  let ne = lat_edges(l)
  let total = @algebra.int_pow(l.ell, ne)
  let pairs : Array[(Int32, Int32, Int32)] = []
  let mut k = 0
  let mut ok = true
  while k < total {
    let u = Array::makei(ne, i => k / @algebra.int_pow(l.ell, i) % l.ell)
    if is_flat(l, u) {
      let (hx, hy) = holonomies(l, u)
      let key = hx * l.ell + hy
      let c = canonical_code(l, u)
      // 同 key 必須同 c；同 c 必須同 key
      for (_, c2, key2) in pairs {
        if (key == key2) != (c == c2) {
          ok = false
        }
      }
      let _ = pairs.push((0, c, key))
    }
    k = k + 1
  }
  let distinct = {
    let out : Array[Int32] = []
    for (_, _, key) in pairs {
      if !out.any(x => x == key) {
        let _ = out.push(key)
      }
    }
    out.length()
  }
  (ok, distinct)
}
