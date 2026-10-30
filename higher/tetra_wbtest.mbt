///| ## 3-截斷（tetra）的驗收

///| 三角面數：`S² = ∂Δ³` 應有 4 個三角形；`S³ = ∂Δ⁴` 應有 10 個三角形、5 個四面體。
test "tetra: truncation sizes" {
  let s2 = sset_trunc_s2()
  let s3 = sset_trunc_s3()
  assert_eq(s2.simplices[2].length(), 4)
  assert_eq(s3.simplices[1].length(), 10)
  assert_eq(s3.simplices[2].length(), 10)
  assert_eq(s3.simplices[3].length(), 5)
}

///| 角填充的維度記帳：`S³` 在 3-截斷上無缺 3-角，但有 5 個缺 4-角。
test "tetra: S3 fills all 3-horns but misses 4-horns" {
  let s3 = sset_trunc_s3()
  assert_eq(horns_missing_count(s3, 3), 0)
  assert_eq(horns_missing_count(s3, 4), 5)
  let s2 = sset_trunc_s2()
  assert_eq(horns_missing_count(s2, 3), 4)
  assert_eq(horns_missing_count(s2, 2), 0)
  let d3 = sset_trunc_d3()
  assert_eq(horns_missing_count(d3, 2), 0)
  assert_eq(horns_missing_count(d3, 3), 0)
}
