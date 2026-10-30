///| gauge 的驗證測試：Clifford/拉蒙零模的具體 F_p 表示、

///| 與 (Z/2)^d 的 twisted group algebra 的等同、中心/手徵/Bott 結構，

///|
/// 以及 torus 格點上 Z/ℓ 線叢的平坦模空間計數。
test "[T-Cliff] Jordan-Wigner γ 矩陣滿足 Clifford 關係，維數 = 2^⌊d/2⌋" {
  for d in [1, 2, 3, 4, 5, 6] {
    let gs = @gauge.gamma_mats(d, 5)
    assert_eq(gs.length(), d)
    let sz = @core.mat_rows(gs[0]).length()
    assert_eq(sz, @gauge.spinor_dim(d))
    assert_eq(@gauge.check_clifford(d, 5), true)
  }
}

///|
test "[T-Cliff-Twist] Cl_d = (Z/2)^d 的 twisted group algebra（ρ(a)ρ(b)=(-1)^ω ρ(a+b)）" {
  for d in [2, 3, 4, 5] {
    assert_eq(@gauge.check_clifford_is_twisted(d, 5), true)
  }
}

///|
test "[T-Cliff-Center] Cl_d 中心：d 偶 → dim 1（單純 Mat_{2^{d/2}}）；d 奇 → dim 2（Mat⊕Mat）" {
  for d in [1, 2, 3, 4, 5] {
    let (cd_ok, sq_ok) = @gauge.check_clifford_center(d, 5)
    assert_eq(cd_ok, true)
    assert_eq(sq_ok, true)
  }
}

///|
test "[T-Cliff-Chi] 手徵算子：γ_*² = (-1)^{d(d-1)/2}，d 偶反對易 / d 奇交換" {
  for d in [1, 2, 3, 4, 5, 6] {
    assert_eq(@gauge.check_chirality(d, 5), true)
  }
}

///|
test "[T-Cliff-Kron] Bott 2-週期：Cl_d ⊗ Mat₂ 的生成元滿足 Cl_{d+2} 關係" {
  for d in [0, 1, 2, 3, 4] {
    assert_eq(@gauge.check_bott_periodicity(d, 5), true)
  }
}

///|
test "[T-Cliff-Even] 偶子代數中心維數：d 偶 → 2（S=S⁺⊕S⁻），d 奇 → 1" {
  for d in [2, 3, 4, 5, 6] {
    let expect = if d % 2 == 0 { 2 } else { 1 }
    assert_eq(@gauge.even_center_dim(d, 5), expect)
  }
}

///|
test "[T-Gauge-Inv][T-Gauge-Bianchi] 曲率規範不變、Abelian Bianchi 恆等式" {
  let lat = @gauge.mk_lattice(3, 2)
  let rng = @core.rng_seed(4242)
  let ne = @gauge.lat_edges(lat)
  let ns = @gauge.lat_sites(lat)
  let mut rep = 0
  while rep < 12 {
    let u = Array::makei(ne, _ => @core.rng_below(rng, 2))
    let lam = Array::makei(ns, _ => @core.rng_below(rng, 2))
    assert_eq(@gauge.check_curvature_invariant(lat, u, lam), true)
    assert_eq(@gauge.check_holonomy_invariant(lat, u, lam), true)
    assert_eq(@gauge.check_bianchi(lat, u), true)
    rep = rep + 1
  }
}

///|
test "[T-Gauge-Moduli] 平坦線叢模空間 = H¹(T²,Z/ℓ)：軌道數 = ℓ²，平坦場數 = ℓ^{n²+1}" {
  // n = 2：完整枚舉
  let l2 = @gauge.mk_lattice(2, 2)
  let (f2, o2) = @gauge.flat_moduli(l2)
  assert_eq(f2, 32)
  assert_eq(o2, 4)
  let l3 = @gauge.mk_lattice(2, 3)
  let (f3, o3) = @gauge.flat_moduli(l3)
  assert_eq(f3, 243)
  assert_eq(o3, 9)
  // 軌道大小 = ℓ^{n²-1}（規範群核 = 常數函數）
  let flat_zero = Array::make(@gauge.lat_edges(l2), 0)
  let seen : Array[Int32] = []
  let mut k = 0
  while k < 16 {
    let lam = Array::makei(4, i => (k >> i) % 2)
    let v = @gauge.code_of(l2, @gauge.gauge_transform(l2, flat_zero, lam))
    if !seen.any(x => x == v) {
      let _ = seen.push(v)
    }
    k = k + 1
  }
  assert_eq(seen.length(), 8)
}

///|
test "[T-Gauge-Moduli-Bij] 平坦場：同軌道 ⟺ 同 holonomy，且 holonomy 給出全部 ℓ² 類" {
  let l2 = @gauge.mk_lattice(2, 2)
  let (bij2, n2) = @gauge.check_moduli_bijective(l2)
  assert_eq(bij2, true)
  assert_eq(n2, 4)
  let l3 = @gauge.mk_lattice(2, 3)
  let (bij3, n3) = @gauge.check_moduli_bijective(l3)
  assert_eq(bij3, true)
  assert_eq(n3, 9)
}
