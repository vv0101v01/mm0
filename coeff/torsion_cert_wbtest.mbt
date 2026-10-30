///| ## 撓率證書的驗收（backlog §7-5）

///| `ℝP²`、`L(7)`、`M(ℤ/5,1)` 的證書必須自動找到且逐條通過。
test "torsion certificate: found and verified on standard complexes" {
  for (cells, bounds, k) in [
    ([1, 1, 1], [[], [[0]], [[2]]], 2),
    ([1, 1, 1], [[], [[0]], [[7]]], 7),
    ([1, 1, 1], [[], [[0]], [[5]]], 5),
  ] {
    let certs = torsion_certificates(cells, bounds, 12)
    assert_eq(certs.length(), 1)
    assert_eq(certs[0].k, k)
    assert_true(cert_verified(certs[0]))
  }
}

///| 兩個撓率生成元：`Z/2 ⊕ Z/3` 必須給出 `k = 2`（最小者），且鏈是 `(1,0)`。
test "torsion certificate: two generators, smallest k wins" {
  let cells : Array[Int32] = [1, 1, 2]
  let bounds : Array[Array[Array[Int32]]] = [[], [[0]], [[2, 3]]]
  let certs = torsion_certificates(cells, bounds, 12)
  assert_eq(certs.length(), 1)
  assert_eq(certs[0].k, 2)
  assert_true(cert_verified(certs[0]))
}

///| 自由空間（`S²`）沒有證書；`vec` 工具的基本性質。
test "torsion certificate: free complex yields none" {
  assert_eq(torsion_certificates([1, 0, 1], [[], [[0]], []], 12).length(), 0)
  assert_true(@algebra.int_vec_is_zero([0, 0]))
  assert_false(@algebra.int_vec_is_zero([0, 1]))
  assert_true(vec_eq(@algebra.int_vec_scale([1, 2], 3), [3, 6]))
  assert_eq(@algebra.int_mat_vec([[2, 3]], [1, 1]), [5])
}
