///| ## B1′（方案 B）的驗收：序數層級代數與嚴格 Lift

///| 序數加法的吸收律與非交換性：這兩條在 `Int32` 上根本寫不出來。
test "level algebra: ordinal laws" {
  let w = ord_omega()
  assert_true(ord_eq(ord_add(ord_one(), w), w))          // 1 + ω = ω
  assert_false(ord_eq(ord_add(w, ord_one()), w))          // ω + 1 ≠ ω
  assert_true(ord_lt(w, ord_add(w, ord_one())))           // ω < ω + 1
  assert_true(ord_lt(ord_times(w, 5), ord_omega_pow(2)))  // ω·5 < ω²
  assert_true(ord_eq(ord_add(ord_times(w, 3), w), ord_times(w, 4))) // ω·3 + ω = ω·4
  assert_eq(ord_show(ord_omega_pow(3)), "w^3")
  assert_eq(ord_show(ord_omega_pow(4)), "w^4")
  assert_true(ord_eq(ord_sup(ord_omega_pow(3), w), ord_omega_pow(3)))
  assert_true(ord_eq(ord_sup(w, ord_finite(9)), w))
}

///| 正規形、良基秩與高度：`ω²·3 + ω + 5` 必須是正規的且秩有限。
test "level algebra: normal form and well-foundedness witness" {
  let o = ord_add(ord_times(ord_omega_pow(2), 3), ord_add(ord_omega(), ord_finite(5)))
  assert_true(ord_is_normal(o))
  assert_eq(ord_rank(o), 3)
  assert_eq(ord_height(o), 3)
  assert_false(ord_is_finite(o))
  assert_eq(ord_to_int(ord_finite(7)), 7)
  assert_eq(ord_to_int(ord_omega()), -1)
  assert_eq(ord_show(o), "w^2*3 + w + 5")
}

///| 嚴格 `Lift` 五條全過；累積模型在 E1／E2 上失敗（這正是 strict 的內容）。
test "level algebra: strict lift passes, cumulative fails" {
  assert_true(lift_strict_all())
  let checks = lift_checks()
  assert_eq(checks.length(), 5)
  assert_true(checks[0].strict_ok)
  assert_false(checks[0].cumulative_ok)
  assert_true(checks[1].strict_ok)
  assert_false(checks[1].cumulative_ok)
  assert_true(checks[2].strict_ok)
  assert_true(checks[2].cumulative_ok)
}

///| 序數層級系統：有限約束不可行、極限約束可行且最小解是 `ω`。
test "level algebra: ordinal level solving" {
  let s1 = ord_system(2, ["A", "B"])
  ord_require(s1, 0, 1, ord_one())
  ord_require(s1, 1, 0, ord_one())
  assert_false(ord_solve(s1).feasible)

  let s2 = ord_system(3, ["U_n", "U_w", "T"])
  ord_seed(s2, 0, ord_finite(0))
  ord_require(s2, 0, 1, ord_one())
  ord_seed(s2, 1, ord_omega())
  ord_require(s2, 1, 2, ord_one())
  let v = ord_solve(s2)
  assert_true(v.feasible)
  assert_true(ord_eq(v.levels[1], ord_omega()))
  assert_true(ord_eq(v.levels[2], ord_add(ord_omega(), ord_one())))
}

///| 呈現無關性的閘門：真登記通過；單模型與不一致的登記都會被擋。
test "invariance gate: rejects single-model and disagreeing entries" {
  let (ok, _msg) = invariance_gate(registered_invariants())
  assert_true(ok)

  let one = inv_entry("single")
  inv_add(one, inv_of_cw("simplex", cw_of_faces(t2_faces())))
  let (ok1, msg1) = invariance_gate([one])
  assert_false(ok1)
  assert_true(msg1 != "")

  let bad = inv_entry("bad")
  inv_add(bad, inv_of_cw("RP²", cw_of_faces(rp2_faces())))
  inv_add(bad, inv_of_cw("T²", @coeff.cc_from_attaching([1, 2, 1], [[], [[0, 0]], [[0, 0]]])))
  let (ok2, _msg2) = invariance_gate([bad])
  assert_false(ok2)
}
