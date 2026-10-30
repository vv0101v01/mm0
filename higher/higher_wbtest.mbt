///| ## `higher` 套件的驗收測試（Kan／∞-groupoid）

///| Kan 條件：圓與 `Nerve(ℤ/3)` 是 Kan，`Δ²` 不是（缺 8 個角）。
test "kan: circle and group nerves are Kan, Delta^2 is not" {
  assert_true(kan_dim2(sset_circle()).0)
  assert_true(kan_dim2(sset_rp2_min()).0)
  assert_true(kan_dim2(sset_nerve_group(3, [0, 1, 2, 1, 2, 0, 2, 0, 1], 0)).0)
  assert_false(kan_dim2(sset_delta2()).0)
  assert_eq(missing_horns(sset_delta2()).length(), 8)
}

///| ∞-groupoid：`reuse` 補角改變同倫型，`fresh`（pushout）不改變。
test "infinity: reuse filling is not a weak equivalence, fresh filling is" {
  let r = inf_row("S1vS1", sset_wedge2())
  assert_false(r.pi1_same)
  assert_true(fresh_pi1_same("S1vS1", sset_wedge2(), 1))
  let c = inf_row("S1", sset_circle())
  assert_true(c.pi1_same)
  assert_eq(c.missing_before, 0)
}

///| 相干塔不會在有限維停下：`fresh` 補一輪後仍缺大量角。
test "infinity: coherence tower does not terminate in dimension 2" {
  let (done, added) = kan_complete(sset_wedge2(), true, 1)
  assert_true(added > 0)
  assert_eq(kan_dim2(done).0, false)
  assert_true(kan_dim2(done).1 > 0)
}
