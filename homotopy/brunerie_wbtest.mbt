///| ## B6 殘餘（Brunerie）的驗收

///| Moore 空間 `M(ℤ/d,2)` 的 `H₂` 必須等於 `ℤ/d`，且與 `coker(×d)` 一致。
test "brunerie: Moore dictionary is exact" {
  for d in [0, 1, 2, 3, 4, 7] {
    let r = moore_row(d)
    assert_true(r.agrees)
  }
  assert_eq(moore_row(0).h2, "Z")
  assert_eq(moore_row(1).h2, "0")
  assert_eq(moore_row(2).h2, "Z/2")
  assert_eq(moore_row(7).h2, "Z/7")
}

///| `β = 2` ⇒ `π₄(S³) = ℤ/2`；而 `β = 4` 會給 `ℤ/4`（兩者可判別）。
test "brunerie: beta pins pi4" {
  assert_eq(whitehead_hopf(), 2)
  assert_eq(group_of_d(whitehead_hopf()), "Z/2")
  assert_eq(group_of_d(4), "Z/4")
  assert_true(group_of_d(2) != group_of_d(4))
  let cert = pi4_certificate()
  assert_eq(cert.length(), 5)
  assert_true(cert[0].computed == false)
  assert_true(cert[1].computed)
}
