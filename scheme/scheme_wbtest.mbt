///|
test "scheme Eisenbud Theorem 20.8 pure-dimensional smoothness vs mixed-dim guard" {
  let t = mpoly_var(2, 0)
  let e = mpoly_var(2, 1)
  let e2_minus_e = mpoly_sub(mpoly_pow(e, 2), e)
  let t_one_minus_e = mpoly_mul(t, mpoly_sub(mpoly_int(2, 1), e))
  let two_lines = affine_scheme(coord_ring_new(2, [e2_minus_e]))
  let line_plus_pt = affine_scheme(
    coord_ring_new(2, [e2_minus_e, t_one_minus_e]),
  )
  assert_true(affine_is_smooth(two_lines))
  assert_true(!affine_is_smooth(line_plus_pt))
}

///|
test "scheme dualizing complexes, Gröbner motive h(P^1), and dual numbers F_p[ε]" {
  let x0 = mpoly_var(3, 0)
  let x1 = mpoly_var(3, 1)
  let x2 = mpoly_var(3, 2)
  let elliptic = mpoly_add(
    mpoly_sub(mpoly_mul(mpoly_pow(x1, 2), x2), mpoly_pow(x0, 3)),
    mpoly_mul(x0, mpoly_pow(x2, 2)),
  )
  let dc = plane_curve_dualizing_complex(elliptic)
  assert_true(dc.serre_duality_holds)
  assert_eq(dc.canonical_twist, 0)
  assert_eq(dc.arithmetic_genus, 1)
  assert_true(verify_motivic_p1_categorification(7))

  let (dual5, aug5) = fcomm_dual_numbers(5)
  assert_eq(dual5.size, 25)
  assert_true(finite_ring_hom_is_valid(aug5))
  // ε corresponds to 0 + 1*5 = 5, so ε^2 == 0 in F_5[ε]/(ε^2).
  assert_eq(dual5.mul_table[5 * 25 + 5], 0)
}
