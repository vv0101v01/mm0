///|
test "field arithmetic / Fermat inverse" {
  for p in [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47] {
    let f = @core.mk_field(p)
    for a = 1; a < p; a = a + 1 {
      assert_eq(@core.fld_mul(f, a, @core.fld_inv(f, a)) == 1, true)
    }
    assert_eq(@core.is_prime(p), true)
  }
}

///|
test "gauss-jordan / rank-nullity [T-Rank]" {
  let f = @core.mk_field(7)
  let m = @core.mat_from_rows([[1, 2, 3, 4], [2, 4, 6, 8], [1, 0, 1, 0]])
  let g = @core.gauss_jordan(m, f)
  assert_eq(g.rank == 2, true)
  // rank + nullity = #cols
  let ns = @core.nullspace_basis(m, f)
  assert_eq(g.rank + ns.length() == 4, true)
  // 零空間向量的確被 A 消滅
  for v in ns {
    for i = 0; i < m.rows; i = i + 1 {
      let mut acc = 0
      for j = 0; j < 4; j = j + 1 {
        acc = @core.fld_add(
          f,
          acc,
          @core.fld_mul(f, @core.mat_get(m, i, j), v[j]),
        )
      }
      assert_eq(acc == 0, true)
    }
  }
}

///|
test "solve consistency [T-Solve]" {
  let f = @core.mk_field(11)
  let a = @core.mat_from_rows([[1, 2], [3, 4]])
  let b = [5, 6]
  match @core.solve_linear(a, b, f) {
    None => assert_eq(false, true)
    Some(x) => {
      assert_eq(
        @core.fld_add(f, @core.fld_mul(f, 1, x[0]), @core.fld_mul(f, 2, x[1])) ==
        5,
        true,
      )
      assert_eq(
        @core.fld_add(f, @core.fld_mul(f, 3, x[0]), @core.fld_mul(f, 4, x[1])) ==
        6,
        true,
      )
    }
  }
  let a2 = @core.mat_from_rows([[1, 2], [2, 4]])
  let b2 = [1, 1]
  assert_eq(@core.solve_linear(a2, b2, f) == None, true)
}

///|
test "det via elimination matches expansion" {
  let f = @core.mk_field(13)
  let a = @core.mat_from_rows([[1, 2, 3], [4, 5, 6], [7, 8, 10]])
  // 1*(50-48) - 2*(40-42) + 3*(32-35) = 2 + 4 - 9 = -3 = 10
  assert_eq(@core.det_mod(a, f) == 10, true)
  let i3 = @core.mat_identity(3)
  assert_eq(@core.det_mod(i3, f) == 1, true)
}

///|
test "smith normal form divisibility chain [T-SNF]" {
  let m = @core.mat_from_rows([[2, 4, 4], [-6, 6, 12], [10, -4, -16]])
  let d = @core.smith_diagonal(m)
  assert_eq(d == [2, 6, 12], true)
  for i = 0; i + 1 < d.length(); i = i + 1 {
    if d[i] != 0 {
      assert_eq(d[i + 1] % d[i] == 0, true)
    }
  }
}

///|
test "abelian group presentation" {
  // Z^2 / <(2,0),(0,3)> = Z/2 (+) Z/3
  let rel = @core.mat_from_rows([[2, 0], [0, 3]])
  let g = @core.ab_from_presentation(rel)
  assert_eq(g.free_rank == 0, true)
  // Smith 不變因子（CRT 標準形）：Z/2 (+) Z/3 ≅ Z/6
  assert_eq(g.torsion == [6], true)
  assert_eq(@core.ab_order(g) == 6, true)
  // 更大例子：Z^3 / <(6,0,0),(0,10,0),(0,15,0)> 之階 = 6*gcd(10,15)*lcm? 直接對拍 Smith
  // d1=gcd(6,10,15)=1, d2=gcd(60,90,150)=30, det=900 => SNF=[1,30,30]
  let g3 = @core.ab_from_presentation(
    @core.mat_from_rows([[6, 0, 0], [0, 10, 0], [0, 0, 15]]),
  )
  assert_eq(@core.ab_order(g3), 900)
  assert_eq(g3.torsion == [30, 30], true)
  // 階不足 3 的例子（第 2、3 欄成比例）=> 出現自由部分
  let g4 = @core.ab_from_presentation(
    @core.mat_from_rows([[6, 0, 0], [0, 10, 0], [0, 15, 0]]),
  )
  assert_eq(g4.free_rank, 1)
  assert_eq(@core.ab_order(g4), -1)
  // 無關係 => Z^3
  let g2 = @core.ab_from_presentation(@core.mat_make(0, 3, 0))
  assert_eq(g2.free_rank == 3, true)
  assert_eq(@core.ab_show(g2) == "Z^3", true)
}

///|
test "integer relation finder (meet in the middle)" {
  // x = (1, 1, -phi) 其中 phi 為黃金比例：1 + 1 - 2*phi? 用 sqrt2 例子
  let s2 = 2.0.sqrt()
  let xs = [1.0, s2, 2.0 + s2]
  // (2, -1, ... ) 2 + s2 - (2+s2) = 0 => c = (1,1,-1)
  match @core.integer_relation(xs, 3, 1024.0, 0.0000001) {
    None => assert_eq(false, true)
    Some(r) => assert_eq(r.residual.abs() < 0.0000001, true)
  }
}

///|
test "stable relation detection across evolution" {
  // 三列不變量 (a_t, b_t, c_t) 其中 c_t = 2a_t - b_t 恆定成立
  let series = [[1.0, 3.0, -1.0], [2.0, 5.0, -1.0], [7.0, 11.0, 3.0]]
  let rs = @core.find_stable_relations(series, 3, 512.0, 0.000000001)
  assert_eq(rs.length() >= 1, true)
  let ok = rs.any(r => {
    // 2a - b - c = 0  <=>  coeffs 比例 (2,-1,-1)
    let c = r.coeffs
    c[0] * -1 == c[1] * 2 && c[0] * -1 == c[2] * 2
  })
  assert_eq(ok, true)
}

///|
test "SNF preserves determinant up to sign (unit transforms)" {
  let mats = [
    @core.mat_from_rows([[2, 0, 0], [0, 10, 0], [0, 0, 15]]),
    @core.mat_from_rows([[2, 4, 4], [-6, 6, 12], [10, -4, -16]]),
    @core.mat_from_rows([[4, 0, 0], [0, 6, 0], [0, 0, 9]]),
  ]
  for m in mats {
    let d = @core.smith_diagonal(m)
    let f = @core.mk_field(10007)
    let mut prod = 1
    for x in d {
      prod = @core.fld_mul(f, prod, x % 10007)
    }
    let det = @core.det_mod(m, f)
    let neg_det = @core.fld_neg(f, det)
    assert_eq(prod == det || prod == neg_det, true)
    // 整除鏈 [T-SNF]
    for i = 0; i + 1 < d.length(); i = i + 1 {
      if d[i] != 0 {
        assert_eq(d[i + 1] % d[i] == 0, true)
      }
    }
  }
}

///|
test "deterministic rng" {
  let r = @core.rng_seed(42)
  let a = @core.rng_next(r)
  let r2 = @core.rng_seed(42)
  assert_eq(a == @core.rng_next(r2), true)
  assert_eq(a >= 0, true)
}
