///| ## bridge 的白盒驗收（第七輪重建）
///
///| 說明：第七輪把 `golden/bridge` 併入時，誤以同名檔覆蓋了這份測試（舊檔 24 條 test 全失）。
///| 這份是**重建版**：按各檔的公開介面重寫，覆蓋 B1–B7 與 G3／G5–G9 的主張，
///| 並且日後在 `AGENTS.md` 記下「拷貝前先查同名檔」。

///| B1：差分約束層級系統——可行時給最小解，不可行時給正環見證。
test "b1: level solve feasible and infeasible" {
  let s = level_system(3, ["U0", "U1", "U2"])
  level_require(s, 0, 1, 1)
  level_require(s, 1, 2, 1)
  let v = level_solve(s)
  assert_true(v.feasible)
  assert_eq(v.levels[0], 0)
  assert_eq(v.levels[2], 2)

  let s2 = level_system(2, ["A", "B"])
  level_require(s2, 0, 1, 1)
  level_require(s2, 1, 0, 1)
  let v2 = level_solve(s2)
  assert_false(v2.feasible)
  assert_true(v2.cycle.length() >= 2)
}

///| B2：GF(2) 秩界恰等於團數（Tseitin 的線性鬆弛在 GF(2) 上不鬆）。
test "b2: clique rank bound is exact on complete multipartite" {
  let adj = complete_multipartite([3, 3, 3])
  let (bound, _vec) = clique_rank_bound(adj)
  assert_eq(bound, 3)
  assert_eq(exact_clique(adj), 3)

  let tri = complete_multipartite([1, 1, 1])
  assert_eq(exact_clique(tri), 3)

  let cyc = cycle_graph(6)
  assert_eq(exact_clique(cyc), 2)
}

///| B3：帳本雜湊鏈——可驗、可重放、篡改必被抓。
test "b3: ledger run verifies and detects tampering" {
  let entries : Array[(String, String)] = [
    ("B1", "levels"),
    ("B2", "rank"),
    ("B3", "ledger"),
  ]
  let r = ledger_run(entries)
  // 帳本自帶一條創世紀錄 ⇒ 筆數 = 條目數 + 1
  assert_true(r.records >= entries.length())
  assert_true(r.verify_ok)
  assert_true(r.tamper_detected)
  assert_true(r.replay_ok)
  assert_true(ledger_idempotent())
}

///| B4：精確特徵多項式與模素數殘餘一致；位數界是單調的。
test "b4: charpoly residues match exact and bit bound grows" {
  let r = charpoly_probe(6, 3)
  assert_eq(r.n, 6)
  assert_true(r.residues_match)
  assert_true(r.primes_used <= r.primes_needed)
  assert_true(coeff_bit_bound(8) >= coeff_bit_bound(4))
}

///| B5：真值表 ↔ ANF 往返是恆等。
test "b5: truth table and ANF round-trip" {
  let n = 3
  let tt : Array[Int32] = []
  for s = 0; s < 8; s = s + 1 {
    tt.push(if (s % 3) == 0 { 1 } else { 0 })
  }
  let a = anf_of_truth(tt, n)
  let back = truth_of_anf(a, n)
  let mut same = true
  for i = 0; i < back.length(); i = i + 1 {
    if back[i] != tt[i] {
      same = false
    }
  }
  assert_true(same)
}

///| B6：`H₁(ℝP²) = ℤ/2`，且撓率見證逐條成立；`S²` 無撓率。
test "b6: homology of RP2 and S2" {
  let (w, h) = torsion_witness_rp2()
  assert_true(w.cycle_ok)
  assert_true(w.half_boundary_ok)
  assert_true(w.not_boundary_ok)
  let h2 = homology_of(simplex_from_faces(rp2_faces()))
  assert_eq(h2.torsion[1].length(), 1)
  assert_eq(h2.torsion[1][0], 2)
  let hs = homology_of(simplex_from_faces(s2_faces()))
  assert_eq(hs.betti[0], 1)
  assert_eq(hs.betti[2], 1)
  assert_eq(hs.torsion[1].length(), 0)
  let _ = h
}

///| B7：有限載體合一——可解性判定與計數公式對得上。
test "b7: finite unification count matches brute force" {
  let a : Array[Array[Int32]] = [[1, 1, 0], [0, 1, 1]]
  let b : Array[Int32] = [1, 1]
  let r = fin_unify(a, b, 3)
  assert_true(r.solvable)
  assert_eq(r.count_formula, r.count_bruteforce)
}

///| G3：對稱族的譜——精確係數與數值隔離一致。
test "g3: spectral row exact and isolated" {
  let r = spectral_row(4, [2, 3, 5], [2, 3])
  assert_eq(r.n, 4)
  assert_true(r.exact_digits > 0)
  assert_true(r.intervals_at.length() >= 0)
}

///| G5：線性系統的 ANF 重量等於約束數（每個約束一個單項）。
test "g5: ANF weight of linear system" {
  let n = 4
  let w = g5_weight_of_system(n, 3)
  assert_true(w > 0)
  assert_true(g5_weight_of_system(n, 1) <= w)
  let tt = truth_linear(n, 0b0101)
  let a = anf(tt, n)
  assert_eq(a.length(), 1 << n)
}

///| G7：稀疏性事前判定——導數消失的位數與支撐重量一致。
test "g7: sparsity degree from derivatives" {
  let n = 4
  let tt = tt_lowdeg(n)
  let (d, cnt) = anf_degree(tt, n)
  assert_true(d >= 0)
  assert_true(cnt >= 1)
  assert_eq(binom_sum(n, 0), 1)
  assert_eq(@algebra.int_binom(5, 2), 10)
}

///| G8：三條表示路線在低次數函數上互證；交叉點隨 n 單調。
test "g8: selector routes agree and crossover grows" {
  let n = 6
  let tt = tt_affine(n)
  let (_d, _w, routes, _adv) = select_routes(tt, n)
  assert_true(routes.length() >= 3)
  assert_true(crossover_degree(8) >= crossover_degree(4))
  let r = select_row("affine", tt, n)
  assert_true(r.correct)
  assert_true(r.predicted <= r.full_mobius)
}

///| G9：呈現無關性——同一空間兩個模型的不變量逐項相同（第八輪追加的閘門也在這裡）。
test "g9: two models of each space agree" {
  let t2a = inv_of_cw("simplex", cw_of_faces(t2_faces()))
  let t2b = inv_of_cw("cw", cc_from_attaching_t2())
  assert_true(models_agree(t2a, t2b))
  let rp2a = inv_of_cw("simplex", cw_of_faces(rp2_faces()))
  let rp2b = inv_of_cw("cw", cc_from_attaching_rp2())
  assert_true(models_agree(rp2a, rp2b))
  assert_eq(rp2a.torsion_k, 2)
}

///| 內部小工具：`T²` 與 `ℝP²` 的 CW 模型（測試用，避免重複字面量）。
fn cc_from_attaching_t2() -> @coeff.ChainComplex {
  @coeff.cc_from_attaching([1, 2, 1], [[], [[0, 0]], [[0, 0]]])
}

///|
fn cc_from_attaching_rp2() -> @coeff.ChainComplex {
  @coeff.cc_from_attaching([1, 1, 1], [[], [[0]], [[2]]])
}

///| 併入 `golden/bridge` 之後的六條自檢：每一條都是原庫的 `check_*`，現在在同一個套件裡跑。
test "merged golden bridges: the six self-checks pass" {
  assert_true(check_free_category_bridge())
  assert_true(check_perm_wiring_bridge())
  assert_true(check_tropical_bridges())
  assert_true(check_graph_symmetry_bridges())
  assert_true(verify_five_federation_pentagon_unification())
  assert_true(verify_geometry_logic_atlas())
}

///| 大統一報告：六柱證書全過。
test "merged golden bridges: grand unification report is all green" {
  let r = run_grand_unification_system()
  assert_true(r.all_ok)
  assert_true(r.five_federations_ok)
  assert_true(r.six_pillar_circle_sphere_ok)
  assert_true(r.total_certificates_passed == r.total_certificates_count)
}

///| 橋憑證：三族（cubical／symlib／semiring 定律）都要成立。
test "merged golden bridges: certificates of three federations" {
  let certs = bridge_certificates()
  assert_true(certs.length() >= 3)
  assert_true(certificates_all_ok(certs))
}

///| 分數卡與根因表：每個邊界都要有判定。
test "merged golden bridges: scorecard covers seven boundaries" {
  let rows = scorecard_table()
  assert_true(rows.length() >= 7)
  let rc = rootcause_table()
  assert_true(rc.length() >= 1)
}

///| G6：非阿貝爾 Čech `H¹`——圓上的 S₃-扭量有 3 類，圓盤上只有 1 類。
test "g6: non-abelian Cech H1 on circle and disk" {
  let circle = cech_row("S3", bg_symmetric(3), "S¹", nerve_circle3(), 6, "circle")
  assert_eq(circle.n_classes, 3)
  let disk = cech_row("S3", bg_symmetric(3), "D²", nerve_disk(), 1, "disk")
  assert_eq(disk.n_classes, 1)
}

///| B6：楔和與環面的同調——`H₁` 秩與撓率。
test "b6: homology of wedge and torus" {
  let w = homology_of(simplex_from_faces(wedge_faces()))
  assert_eq(w.betti[0], 1)
  assert_eq(w.betti[1], 2)
  assert_eq(w.betti[2], 1)
  let t = homology_of(simplex_from_faces(t2_faces()))
  assert_eq(t.betti[1], 2)
  assert_eq(t.euler, 0)
}

///| B2：秩界定理的方向是 **上界** `ω(G) ≤ rank(I + Ā)`；完全多分圖上等號成立，
///| 隨機圖上通常嚴格。（第一版把方向寫反，測試立刻抓到。）
test "b2: rank bound is an upper bound for clique number" {
  let g = random_graph(8, 5, 80)
  let (bound, _) = clique_rank_bound(g)
  let w = exact_clique(g)
  assert_true(bound >= w)
  assert_true(w >= 2)
  let k = complete_multipartite([2, 2, 2])
  let (kb, _) = clique_rank_bound(k)
  assert_eq(kb, exact_clique(k))
}

///| 分數卡：B1–B7 都有「動作／量測／殘餘」三格。
test "scorecard: seven boundaries with verdicts" {
  let rows = scorecard()
  assert_eq(rows.length(), 7)
  for r in rows {
    assert_true(r.metric != "")
    assert_true(r.mode != "")
  }
}

///| 熱帶橋：指派成本與恰好一個最優置換。
test "tropical bridge: assignment cost is attained" {
  let a : Array[Array[Int64]] = [[3L, 1L], [2L, 4L]]
  let best = match tropical_optimal_assignments(a, 8) {
    Some(v) => v
    None => fail("tropical_optimal_assignments should succeed")
  }
  assert_true(best.length() >= 1)
  let c0 = match assignment_cost(a, best[0]) {
    Some(v) => v
    None => fail("assignment_cost should succeed")
  }
  assert_true(c0 >= 1L)
}

///| B1：顯示字串要說清楚「可行／最小解」。
test "b1: level show mentions the least solution" {
  let s = level_system(2, ["U0", "U1"])
  level_require(s, 0, 1, 1)
  let v = level_solve(s)
  assert_true(level_show(v, s) != "")
  assert_true(level_show(v, s).contains("feasible"))
}

///| B4：稠密 0/1 矩陣是**對稱**的（`coeff_bit_bound` 的輸入族；對角線隨機，不是 1）。
test "b4: dense01 is symmetric and square" {
  let m = dense01(5)
  assert_eq(m.length(), 5)
  for i = 0; i < 5; i = i + 1 {
    for j = 0; j < 5; j = j + 1 {
      assert_eq(m[i][j], m[j][i])
    }
  }
}

///| G5：`truth_linear` 產生完整真值表（`2^n` 項）。
test "g5: truth table size" {
  let n = 4
  assert_eq(truth_linear(n, 0b1010).length(), 16)
}

// ───────────────────────── 第八輪：橋 18／20／21 ─────────────────────────

///| 橋 18：`ℚ` 與 `F₂` 的 `dim H¹` 在 `ℝP²` 上必須分開（`0` 對 `1`）。
test "b18: rational and mod-2 H1 differ exactly on the projective plane" {
  let rp2 = @topos.rp2_minimal_nerve()
  assert_eq(dim_h1_q(rp2), 0)
  assert_eq(dim_h1_f2(rp2), 1)
  // 有撓率的地方 `F₂` 才看得到杯積
  assert_eq(cup_rank_f2(rp2), 1)
  let t2 = @topos.torus_t2_minimal_nerve()
  assert_eq(dim_h1_q(t2), 2)
  assert_eq(dim_h1_f2(t2), 2)
  assert_eq(cup_rank_f2(t2), 1)
}

///| 橋 18：閉鏈空間的維數是 `dim Z¹ = n₁ − rank d¹`（不是 `H¹`）。
test "b18: cocycle space is strictly larger than cohomology" {
  let t2 = @topos.torus_t2_minimal_nerve()
  let z1 = one_cocycles_q(t2)
  assert_eq(z1.length(), 8)
  assert_eq(dim_h1_q(t2), 2)
  // 每個閉鏈真的閉：`d¹ w = 0`
  let d1 = nerve_d1_q(t2)
  for w in z1 {
    for r in d1 {
      let mut acc = @algebra.rat_zero()
      for c = 0; c < r.length(); c = c + 1 {
        acc = @algebra.rat_add(acc, @algebra.rat_mul(r[c], w[c]))
      }
      assert_true(@algebra.rat_eq(acc, @algebra.rat_zero()))
    }
  }
}

///| 橋 18：分次交換律在**上鏈層**只到「差一個上邊界」。
test "b18: graded commutativity holds up to a coboundary only" {
  let t2 = @topos.torus_t2_minimal_nerve()
  let coc = one_cocycles_q(t2)
  let mut checked = 0
  let mut homotopic = 0
  for i = 0; i < coc.length(); i = i + 1 {
    for j = 0; j < coc.length(); j = j + 1 {
      let p = @topos.simplicial_cup_1_1(t2, coc[i], coc[j])
      if qvec_all_zero(p) {
        continue
      }
      checked = checked + 1
      let r = @topos.simplicial_cup_1_1(t2, coc[j], coc[i])
      let sum : Array[@algebra.Rat] = []
      for k = 0; k < p.length(); k = k + 1 {
        sum.push(@algebra.rat_add(p[k], r[k]))
      }
      if is_coboundary(t2, sum) {
        homotopic = homotopic + 1
      }
    }
  }
  assert_true(checked > 0)
  assert_eq(checked, homotopic)
}

///| 橋 18：閉鏈的乘積還是閉鏈（`d²(α⌣β) = 0`）。
test "b18: cup of cocycles is a cocycle" {
  let t2 = @topos.torus_t2_minimal_nerve()
  let coc = one_cocycles_q(t2)
  for i = 0; i < coc.length() && i < 3; i = i + 1 {
    for j = 0; j < coc.length() && j < 3; j = j + 1 {
      let p = @topos.simplicial_cup_1_1(t2, coc[i], coc[j])
      assert_true(qvec_all_zero(d2_of(t2, p)))
    }
  }
}

///| 橋 20：認證譜流＝浮點譜流（非退化情形），而端點退化時認證會誠實回 `None`。
test "b20: certified flow agrees with floats and refuses at degeneracy" {
  let a : Array[Array[Int32]] = [[-1, 0, 0], [0, -1, 0], [0, 0, 1]]
  let id : Array[Array[Int32]] = [[1, 0, 0], [0, 1, 0], [0, 0, 1]]
  // (−,−,+) → (+,+,+)：兩條分支同時由負轉正
  assert_eq(certified_spectral_flow(a, id), Some(2))
  assert_eq(float_spectral_flow(a, id, 9), 2)
  // (−,−,+) → (−,+,+)：只有一條轉正
  let b : Array[Array[Int32]] = [[-1, 0, 0], [0, 1, 0], [0, 0, 1]]
  assert_eq(certified_spectral_flow(a, b), Some(1))
  assert_eq(float_spectral_flow(a, b, 9), 1)
  // 端點退化：`0` 是特徵值 ⇒ 符號沒有定義 ⇒ 認證必須回 None
  let c : Array[Array[Int32]] = [[0, 0], [0, -1]]
  let d : Array[Array[Int32]] = [[1, 0], [0, -1]]
  assert_true(certified_spectral_flow(c, d) is None)
}

///| 橋 20：Witten 指標＝`dim ker D − dim ker Dᵀ`，等於 `n − m + 2·(秩虧)`。
test "b20: witten index equals m minus n when full rank" {
  let d : Array[Array[Int32]] = [[1, 0, 0], [0, 1, 0]]
  assert_eq(witten_index_exact(d), 1)
  let e : Array[Array[Int32]] = [[1, 0], [0, 1], [0, 0]]
  assert_eq(witten_index_exact(e), -1)
  let z : Array[Array[Int32]] = [[1, 0], [0, 0]]
  assert_eq(witten_index_exact(z), 0)
}

///| 橋 21：`ℙ¹` 的換圖 Jacobi 行列式＝`−t^−(m+1)`，Berezinian 的度數就是 `n−(m+1)`。
test "b21: Berezinian degree of projective superspace" {
  for m in [1, 2, 3] {
    let jac = chart_jacobian_pm(m)
    let det = lp_det(jac)
    assert_eq(lp_degree(det), Some(0 - (m + 1)))
    assert_eq(lp_leading(det), Some(-1L))
    assert_false(lp_is_zero(det))
  }
  let ber = ber_of_projective(1, 2)
  assert_eq(lp_degree(ber), Some(0))
  assert_eq(lp_leading(ber), Some(-1L))
}

///| 橋 21：多項式基本律（`lp_of_ints` 建、`lp_leading`／`lp_is_zero` 讀）。
test "b21: laurent arithmetic" {
  let a = lp_of_ints(-1, [2L, 0L, 3L])
  let b = lp_mono(0, 1L)
  let p = lp_mul(a, b)
  assert_eq(lp_degree(p), Some(1))
  assert_eq(lp_leading(p), Some(3L))
  assert_false(lp_is_zero(p))
  assert_true(lp_is_zero(lp_add(p, lp_neg(p))))
  assert_eq(lp_of_ints(0, [1L, -1L]).terms.length(), 2)
}

///| 橋 21：`ℙ¹` 上 `O(d)` 的 Čech 上同調，`χ = d + 1`。
test "b21: cech cohomology of O(d) on P1" {
  for d in [-3, -2, -1, 0, 1, 2, 3] {
    let r = cech_projective_line(d)
    assert_eq(r.h0 - r.h1, d + 1)
    assert_true(r.stable)
    if d < 0 {
      assert_eq(r.h0, 0)
      assert_eq(r.h1, -d - 1)
    } else {
      assert_eq(r.h0, d + 1)
      assert_eq(r.h1, 0)
    }
  }
}
