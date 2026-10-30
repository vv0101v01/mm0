///| ## 係數環契約測試
///

///| 這 12 條斷言就是「係數環」主軸的可驗收形式。

///| 任何一條失敗，代表兩件事之一：UCT 的實作錯了，或某個環的消元引擎退化。

///|
test "coefficient ring: Q makes torsion vanish, Z/F_p make it visible" {
  let cx = cw_rp2()
  let hz = homology_z(cx)
  assert_eq(ab_show(hz.groups[1]), "Z/2")
  let hq = homology_q(cx)
  assert_eq(ab_show(hq.groups[1]), "0")
  let h2 = homology_fp(cx, 2)
  assert_eq(h2.groups[1].free, 1)
  let h3 = homology_fp(cx, 3)
  assert_eq(h3.groups[1].free, 0)
}

///|
/// 撓率階為奇數的情形（單純複形做不到，必須用 CW）。
test "Moore space M(Z/3,1): torsion of order 3 visible only over Z and F_3" {
  let cx = moore_space(3)
  assert_eq(ab_show(homology_z(cx).groups[1]), "Z/3")
  assert_eq(ab_show(homology_q(cx).groups[1]), "0")
  assert_eq(homology_fp(cx, 3).groups[1].free, 1)
  assert_eq(homology_fp(cx, 2).groups[1].free, 0)
  assert_eq(homology_fp(cx, 5).groups[1].free, 0)
}

///|
/// UCT 交叉驗證：模 p 消元 vs SNF+UCT，全部模型、四個素數。
test "universal coefficient theorem agrees with direct mod-p elimination" {
  for m in models() {
    for p in [2, 3, 5, 7] {
      let c = uct_check(m.1, p)
      assert_true(c.ok)
    }
  }
}

///|
/// 三個獨立秩路徑（Q / Z / F_p）在同一矩陣上的一致性。
test "rank over Q equals rank over Z on every boundary matrix" {
  for m in models() {
    assert_true(rank_paths_agree(m.1))
    assert_true(cc_chain_ok(m.1))
  }
}

///|
/// Bockstein 抓到 2-撓率：`β(2-胞腔) = 1-胞腔`。
test "Bockstein detects the 2-torsion of RP^2" {
  let cx = cw_rp2()
  let beta = bockstein_of_cycle(cx, 2, 2, [1])
  assert_eq(beta[0], 1)
  assert_true(bockstein_nontrivial(cx, 2, 2, [1]))
  let r = bockstein_report(cx, 2, 2)
  assert_eq(r.dim_cycles_with_beta, 1)
}

///|
/// Bockstein 抓到 3-撓率。
test "Bockstein detects the 3-torsion of M(Z/3,1)" {
  let cx = moore_space(3)
  let beta = bockstein_of_cycle(cx, 3, 2, [1])
  assert_eq(beta[0], 1)
  assert_eq(bockstein_report(cx, 3, 2).dim_cycles_with_beta, 1)
}

///|
/// 無撓率空間上 Bockstein 應為零。
test "Bockstein vanishes on S^2 and T^2" {
  assert_eq(bockstein_report(simplex_cc(s2()), 2, 2).dim_cycles_with_beta, 0)
  assert_eq(bockstein_report(simplex_cc(torus()), 2, 2).dim_cycles_with_beta, 0)
}

///|
/// CW 與單純模型給出同一個同調（兩個獨立來源的一致性）。
test "CW model and simplicial model of RP^2 agree" {
  let a = homology_z(cw_rp2())
  let b = homology_z(simplex_cc(rp2()))
  for k = 0; k < a.groups.length(); k = k + 1 {
    assert_true(ab_eq(a.groups[k], b.groups[k]))
  }
}

///|
/// 同調不能區分 T² 與 S¹∨S¹∨S²。
test "T^2 and S1vS1vS2 have isomorphic homology" {
  let a = homology_z(simplex_cc(torus()))
  let b = homology_z(simplex_cc(wedge()))
  assert_true(ab_eq(a.groups[1], b.groups[1]))
  assert_true(ab_eq(a.groups[2], b.groups[2]))
}

///|
/// 但杯積可以：T² 有非零 1∪1，楔和全為零。
test "cup product separates T^2 from the wedge" {
  let t = cup_scan(torus(), "T^2")
  let w = cup_scan(wedge(), "wedge")
  assert_true(t.nonzero_cup > 0)
  assert_eq(w.nonzero_cup, 0)
}

///|
/// 杯積的閉性：餘圈之積仍是餘圈。
test "cup of two cocycles is a cocycle" {
  let sx = torus()
  let z1 = nullspace_f2(sx, 1)
  assert_true(z1.length() > 0)
  let c = cup_f2(sx, 1, z1[0], 1, z1[0])
  assert_true(is_cocycle_f2(sx, 2, c))
}

///|
/// 分裂表：x²−2 的三種行為在三個素數上各出現一次。
test "splitting kind of x^2-2 depends on the coefficient ring" {
  assert_true(
    match quadratic_kind(2, 2) {
      Ramified => true
      _ => false
    },
  )
  assert_true(
    match quadratic_kind(2, 7) {
      Split => true
      _ => false
    },
  )
  assert_true(
    match quadratic_kind(2, 5) {
      Inert => true
      _ => false
    },
  )
  // x²−2 在 ℚ 上不可約
  let f = @algebra.qpoly_normalize([
    @algebra.rat_int(-2),
    @algebra.rat_int(0),
    @algebra.rat_int(1),
  ])
  assert_true(@algebra.qpoly_is_irreducible(f))
}

///|
/// 二次互反判據與 Euler 判準、暴力枚舉三方一致。
test "Euler criterion, brute force and reciprocity agree" {
  for p in [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47] {
    assert_true(qr_rule_agrees(2, p))
    assert_true(qr_rule_agrees(-1, p))
  }
}

///|
/// `ℤ/4` 不是域：同調在 `ℤ/4` 上的結構必須由 UCT 給出，不能當成向量空間數維。
test "Z/4 coefficients are computed by UCT, not by rank" {
  let cx = cw_rp2()
  let h = homology_zm(cx, 4)
  // H_1(Z/4) = (H_1 ⊗ Z/4) ⊕ Tor(H_0, Z/4) = Z/2
  assert_eq(ab_show(h.groups[1]), "Z/2")
  assert_false(coeff_is_field(CZm(4)))
  assert_true(coeff_is_field(CFp(7)))
}
