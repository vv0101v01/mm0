///|
/// twist 的驗證測試：全部以有限枚舉 / 消元對照理論預測值。
test "[T-H2-Elem] dim H²((Z/ℓ)^k, Z/ℓ) = k(k+1)/2, δ²δ¹=0" {
  let cases : Array[(Int32, Int32)] = [(1, 2), (2, 2), (3, 2), (1, 3), (2, 3)]
  for (k, ell) in cases {
    let g = @twist.grp(Array::makei(k, _ => ell))
    assert_eq(@twist.check_group_axioms(g), true)
    let mut exp_order = 1
    for _i in 0..<k {
      exp_order = exp_order * ell
    }
    assert_eq(@twist.grp_order(g), exp_order)
    let (z2, b2, h2, chain_ok) = @twist.h2_compute(g, ell)
    assert_eq(chain_ok, true)
    assert_eq(z2 >= b2, true)
    assert_eq(h2, k * (k + 1) / 2)
  }
}

///|
test "[T-H2-Cyc] 循環群 G = Z/ℓ：dim H¹ = dim H² = 1（ℓ | |G|）" {
  for ell in [2, 3, 5] {
    let g = @twist.grp([ell])
    assert_eq(@twist.h1_dim(g, ell), 1)
    assert_eq(@twist.h2_dim(g, ell), 1)
  }
  // Z/9 與 Z/4：p-部分仍在，故 H¹ = H² = 1
  let g9 = @twist.grp([9])
  assert_eq(@twist.h1_dim(g9, 3), 1)
  assert_eq(@twist.h2_dim(g9, 3), 1)
  let g4 = @twist.grp([4])
  assert_eq(@twist.h1_dim(g4, 2), 1)
  assert_eq(@twist.h2_dim(g4, 2), 1)
  // 素數 ℓ ∤ |G| 時上同調消失
  let g3 = @twist.grp([3])
  assert_eq(@twist.h2_dim(g3, 2), 0)
}

///|
test "[T-H2-Kunn] Künneth：dim H²(G₁×G₂) = Σ_{i+j=2} dim H^i(G₁)·dim H^j(G₂)" {
  let pairs : Array[(Array[Int32], Array[Int32], Int32)] = [
    ([2], [2], 2),
    ([4], [2], 2),
    ([3], [3], 3),
    ([2], [2, 2], 2),
    ([3], [9], 3),
  ]
  for (o1, o2, ell) in pairs {
    let a = @twist.grp(o1)
    let b = @twist.grp(o2)
    let combined : Array[Int32] = o1.copy()
    for x in o2 {
      let _ = combined.push(x)
    }
    let h0a = 1
    let h1a = @twist.h1_dim(a, ell)
    let h2a = @twist.h2_dim(a, ell)
    let h0b = 1
    let h1b = @twist.h1_dim(b, ell)
    let h2b = @twist.h2_dim(b, ell)
    let pred = h0a * h2b + h1a * h1b + h2a * h0b
    let prod = @twist.grp(combined)
    let got = @twist.h2_dim(prod, ell)
    assert_eq(got, pred)
  }
}

///|
test "[T-TwCenter][T-Tw-Square] 全部 cocycle：dim Z(A^ω)=|rad|、|G|/|rad| 為平方數" {
  let g = @twist.grp([2, 2])
  let ell = 2
  let p = 5
  let nv = @twist.var_count(g)
  assert_eq(nv, 9)
  let mut ncocycles = 0
  let mut idx = 0
  let cocs : Array[Array[Int32]] = []
  while idx < 1 << nv {
    let vec = Array::makei(nv, i => (idx >> i) % 2)
    let o = @twist.mk_omega(g, ell, p, vec)
    if @twist.omega_is_cocycle(o) {
      ncocycles = ncocycles + 1
      let _ = cocs.push(vec)
      let rad = @twist.omega_radical_size(o)
      assert_eq(@twist.center_dim(o), rad)
      assert_eq(@twist.tw_k0_rank(o), rad)
      let dsq = @twist.tw_irrep_dim_sq(o)
      assert_eq(dsq * rad, @twist.grp_order(g))
      assert_eq(@twist.is_perfect_square(dsq), true)
      let (even_rank, rad_formula) = @twist.check_skew_rank_formula(o)
      assert_eq(even_rank, true)
      assert_eq(rad_formula, true)
    }
    idx = idx + 1
  }
  // |Z²| = ℓ^{dim Z²} = 2^4 = 16
  assert_eq(ncocycles, 16)
}

///|
test "[T-Tw-Gauge] coboundary 流保持 rad、K₀ 秩，並給出代數同構" {
  let g = @twist.grp([2, 2])
  let ell = 2
  let p = 5
  let nv = @twist.var_count(g)
  let n = @twist.grp_order(g)
  let mut idx = 0
  let mut seen = 0
  while idx < 1 << nv {
    let vec = Array::makei(nv, i => (idx >> i) % 2)
    let o = @twist.mk_omega(g, ell, p, vec)
    if @twist.omega_is_cocycle(o) {
      seen = seen + 1
      // 所有歸一化 1-上鏈 μ（μ(0)=0）
      let mut midx = 0
      while midx < 1 << (n - 1) {
        let mu = Array::makei(n, i => {
          if i == 0 {
            0
          } else {
            (midx >> (i - 1)) % 2
          }
        })
        let (inv, iso) = @twist.check_gauge_invariance(o, mu)
        assert_eq(inv, true)
        assert_eq(iso, true)
        midx = midx + 1
      }
    }
    idx = idx + 1
  }
  assert_eq(seen, 16)
}

///|
test "[T-H2-Quot] coboundary 類數 = ℓ^{dim H²}（此處 2³ = 8）" {
  let g = @twist.grp([2, 2])
  let ell = 2
  let p = 5
  let nv = @twist.var_count(g)
  let cocs : Array[Array[Int32]] = []
  let mut idx = 0
  while idx < 1 << nv {
    let vec = Array::makei(nv, i => (idx >> i) % 2)
    let o = @twist.mk_omega(g, ell, p, vec)
    if @twist.omega_is_cocycle(o) {
      let _ = cocs.push(vec)
    }
    idx = idx + 1
  }
  // 貪心分堆（等價關係由 cohomologous 判定）
  let assigned = Array::make(cocs.length(), -1)
  let mut nclasses = 0
  let mut i = 0
  while i < cocs.length() {
    if assigned[i] < 0 {
      assigned[i] = nclasses
      let mut j = i + 1
      while j < cocs.length() {
        if assigned[j] < 0 && @twist.cohomologous(g, ell, cocs[i], cocs[j]) {
          assigned[j] = nclasses
        }
        j = j + 1
      }
      nclasses = nclasses + 1
    }
    i = i + 1
  }
  assert_eq(nclasses, 1 << @twist.h2_dim(g, ell))
  // 每類大小 = |B²| = ℓ^{dim B²} = 2
  let counts = Array::make(nclasses, 0)
  for c in assigned {
    counts[c] = counts[c] + 1
  }
  for c in counts {
    assert_eq(c, 2)
  }
}

///|
test "[D-TwK0] 平凡 twist 給 representation ring：K₀ = Z^{|G|}；非退化 twist 給 Z" {
  let g = @twist.grp([2, 2])
  let nv = @twist.var_count(g)
  let zero_omega = @twist.mk_omega(g, 2, 5, Array::make(nv, 0))
  assert_eq(@twist.tw_k0_rank(zero_omega), 4)
  assert_eq(@twist.tw_irrep_dim_sq(zero_omega), 1)
  // 双線型 cocycle ω(a,b) = a_0·b_1 (mod 2)：給出非退化 bicharacter
  let n = @twist.grp_order(g)
  let vec = Array::makei(nv, t => {
    let ac = t / (n - 1) + 1
    let bc = t % (n - 1) + 1
    let av = [0, 0]
    let _ = av
    let a0 = @twist.grp_of_code(g, ac)[0]
    let b1 = @twist.grp_of_code(g, bc)[1]
    a0 * b1 % 2
  })
  let o = @twist.mk_omega(g, 2, 5, vec)
  assert_eq(@twist.omega_is_cocycle(o), true)
  assert_eq(@twist.omega_radical_size(o), 1)
  assert_eq(@twist.tw_k0_rank(o), 1)
  assert_eq(@twist.tw_irrep_dim_sq(o), 4)
  // 一個 2 維 ω-射影表示存在性（由 d²=4 ⟹ d=2）的等價條件：
  // A^ω 為 Mat_2(F_5)，中樞僅純量
  assert_eq(@twist.center_dim(o), 1)
}
