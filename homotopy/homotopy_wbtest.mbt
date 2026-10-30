///| ## `homotopy` 套件的驗收測試（Hopf／Adem／Cayley–Dickson／Postnikov）

///| Gysin 上同調與 CW 同調逐維 UCT 一致；`d = ±1` 上 `π₁ = 0`，`|d| = 2` 上 `π₁ = ℤ/2`。
test "hopf: Gysin and CW homology agree, pi1 tracks the Euler class" {
  for d in [0 - 1, 0, 1, 2, 3, 5] {
    let r = hopf_row(d)
    assert_true(r.uct_agrees)
  }
  assert_true(@coeff.ab_eq(hopf_row(0 - 1).pi1, @coeff.ab_make(0, [])))
  assert_true(@coeff.ab_eq(hopf_row(1).pi1, @coeff.ab_make(0, [])))
  assert_true(@coeff.ab_eq(hopf_row(2).pi1, @coeff.ab_make(0, [2])))
  assert_true(@coeff.ab_eq(hopf_row(3).pi1, @coeff.ab_make(0, [3])))
}

///| 一次阻礙「通過 ⟺ n 是 2 的冪」，在 `n = 2..128` 上全等。
test "steenrod: primary obstruction vanishes exactly at powers of two" {
  for n = 2; n <= 128; n = n + 1 {
    assert_eq(primary_obstruction(n) is None, is_pow2(n))
  }
  assert_true(is_pow2(1))
  assert_false(is_pow2(96))
}

///| `C(n,k) mod 2` 的 Lucas 判據。
test "steenrod: binomial parity by Lucas" {
  assert_eq(binom_mod2(4, 2), 0)
  assert_eq(binom_mod2(3, 1), 1)
  assert_eq(binom_mod2(7, 7), 1)
  assert_eq(binom_mod2(5, 2), 0)
}

///| 範數乘性在 `ℝ,ℂ,ℍ,𝕆` 成立，在 `S(16)` 失敗且有零因子。
test "cayley-dickson: norm multiplicative through the octonions only" {
  for k in [0, 1, 2, 3] {
    assert_true(norm_check(cd_alg(k)).0)
  }
  assert_false(norm_check(cd_alg(4)).0)
  assert_true(zero_divisor(cd_alg(4)) is Some(_))
}

///| `H⁵(K(ℤ,3);F₂)` 一維 ⇒ `k₄ = Sq²ι₃ ≠ 0`；奇質數下第一個操作度數 `≥ 7`。
test "postnikov: H^5(K(Z,3);F_2) is spanned by Sq^2 iota" {
  assert_eq(h5_generators().length(), 1)
  let dims = poly_dims(serre_generators(3, 9), 3, 9)
  assert_eq(dims[3], 1)
  assert_eq(dims[4], 0)
  assert_eq(dims[5], 1)
  assert_eq(dims[9], 2)
  assert_eq(odd_p_first_degree(3), 7)
  assert_eq(odd_p_first_degree(5), 11)
}

///| 容許性與超越數。
test "postnikov: admissible monomials and excess" {
  assert_true(admissible([4, 2]))
  assert_true(admissible([2, 1]))
  assert_false(admissible([2, 3]))
  assert_eq(excess([2, 1]), 1)
  assert_eq(excess([4, 2]), 2)
  assert_eq(deg_of([4, 2]), 6)
}

///| 撓率精確地分開 `L(7,1)` 與 `L(7,2)`（同調分不出來），且與代數判據 `±q^{±1}` 一致。
test "torsion: Reidemeister torsion separates lens spaces" {
  assert_false(torsion_same(7, 1, 2))
  assert_true(torsion_same(7, 1, 6))
  assert_true(torsion_same(7, 2, 4))
  assert_true(torsion_same(7, 3, 5))
  assert_true(torsion_same(7, 3, 4))
  for p in [5, 7, 11, 13] {
    let r = torsion_row(p)
    assert_true(r.agrees)
  }
}

///| `ℚ(ζ_p)` 的算術：`ζ^p = 1`、`(ζ−1)(1+ζ+…+ζ^{p−2})` 之類的恆等式要精確成立。
test "cyclotomic: arithmetic in Q(zeta_p) is exact" {
  let p = 7
  // Σ_{k=0}^{p−1} ζ^k = 0
  let mut acc = cyc_const(p, 1)
  for k = 1; k < p; k = k + 1 {
    acc = cyc_add(acc, cyc_pow_zeta(p, k))
  }
  assert_true(cyc_is_zero(acc))
  // ζ^2 · ζ^{p−3} = ζ^{p−1}
  assert_true(cyc_eq(cyc_mul(cyc_pow_zeta(7, 2), cyc_pow_zeta(7, 4)), cyc_pow_zeta(7, 6)))
  // (ζ − 1)(ζ − 1) ≠ 0
  let d = cyc_sub(cyc_pow_zeta(p, 1), cyc_const(p, 1))
  assert_false(cyc_is_zero(cyc_mul(d, d)))
  // 單位群：ζ·b 與 b 單位相關
  assert_true(unit_related(cyc_pow_zeta(p, 1), cyc_const(p, 1)))
}

// ───────────────────────── 第八輪：Morse 指標流的區間化 ─────────────────────────

///| §7-3 殘餘：`S²` 的報告要給出 `β = 1/0/1`、臨界胞腔 `1/0/1`，四條檢查全過。
test "morse: sphere report" {
  let faces : Array[Array[Int32]] = [[0, 1, 2], [0, 1, 3], [0, 2, 3], [1, 2, 3]]
  let r = morse_report("S²", faces)
  assert_eq(r.betti[0], 1)
  assert_eq(r.betti[1], 0)
  assert_eq(r.betti[2], 1)
  assert_eq(r.critical[0], 1)
  assert_eq(r.critical[1], 0)
  assert_eq(r.critical[2], 1)
  assert_true(r.monotone)
  assert_true(r.jumps_ok)
  assert_true(r.euler_ok)
  assert_true(r.euler_values_ok)
  assert_true(r.morses_ok)
}

///| 環面：`β = 1/2/1`，三個維度都有本質區間。
test "morse: torus report" {
  let r = morse_report("T²", mc_torus_faces())
  assert_eq(r.cells, 42)
  assert_eq(r.betti[0], 1)
  assert_eq(r.betti[1], 2)
  assert_eq(r.betti[2], 1)
  assert_true(r.jumps_ok)
  assert_true(r.euler_ok)
  assert_true(r.euler_values_ok)
}

///| `ℝP²`：`ℚ` 係數下 `β = 1/0/0`（撓率在有理同調裡看不到）。
test "morse: projective plane over Q" {
  let r = morse_report("ℝP²", mc_rp2_faces())
  assert_eq(r.betti[0], 1)
  assert_eq(r.betti[1], 0)
  assert_eq(r.betti[2], 0)
  assert_true(r.euler_values_ok)
}

///| 單調性原則本身：每一條區間都必須 `birth ≤ death`（這就是 §7-3 缺的那條不等式）。
test "morse: every bar is monotone" {
  let cells = filt_from_faces(mc_wedge_faces())
  for b in morse_bars(cells) {
    match b.death {
      None => ()
      Some(d) => assert_true(@algebra.rat_cmp_exact(b.birth, d) <= 0)
    }
  }
}

///| 每一步恰有一個維度變動 ±1：直接對 `beta_by_index` 逐 k 檢查。
test "morse: one dimension changes per cell" {
  let cells = filt_from_faces(mc_torus_faces())
  let bars = morse_bars(cells)
  let mut prev0 = 0
  let mut prev1 = 0
  let mut prev2 = 0
  for k = 0; k < cells.length(); k = k + 1 {
    let b0 = beta_by_index(bars, 0, k)
    let b1 = beta_by_index(bars, 1, k)
    let b2 = beta_by_index(bars, 2, k)
    let mut changed = 0
    if b0 != prev0 {
      changed = changed + 1
    }
    if b1 != prev1 {
      changed = changed + 1
    }
    if b2 != prev2 {
      changed = changed + 1
    }
    assert_eq(changed, 1)
    prev0 = b0
    prev1 = b1
    prev2 = b2
  }
}
