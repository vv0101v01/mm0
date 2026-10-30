///|
test "exact algebra LLL, Van Hoeij, and complex Rouché algebraic closure" {
  assert_true(check_lll_lattice_and_van_hoeij_factor())
  assert_true(check_complex_algebraic_closure_rouche())
}

///|
test "large-prime F_p polynomial arithmetic overflow regression (p > 46349)" {
  // 46351^2 > 2^31 - 1 overflows 32-bit signed Int without Int64 modular widening.
  let p = 46351
  assert_eq(mod_mul_scalar(46350, 46350, p), 1)
  assert_eq(int_mod_inv(46350, p), 46350)
  // (x - 1)^2 = (x + 46350)^2 = x^2 + 46349 x + 1 (mod 46351)
  let lin = [46350, 1]
  assert_eq(mod_mul(p, lin, lin), [1, 46349, 1])
  let (q, r) = mod_divmod(p, [1, 46349, 1], lin)
  assert_eq(q, lin)
  assert_eq(r, [0])
  // Distinct-degree buckets for x^2 + 1 at p = 46351 (46351 ≡ 3 mod 4 => irreducible of degree 2).
  let ddf = mod_distinct_degrees([1N, 0N, 1N], p)
  assert_eq(ddf, Some([2]))
}

///|
test "certified QPoly factorization with negative irreducibility control" {
  // x^4 + 4 = (x^2 - 2x + 2)(x^2 + 2x + 2) over Q (Sophie Germain identity).
  let f = qpoly_normalize([
    rat_int(4),
    rat_zero(),
    rat_zero(),
    rat_zero(),
    rat_one(),
  ])
  assert_true(!qpoly_is_irreducible(f))
  let cert = qpoly_factor_certified(f)
  assert_true(qpoly_factor_certificate_check(f, cert))
  assert_eq(cert.factors.length(), 2)
  // x^4 + 1 (8th cyclotomic polynomial) is irreducible over Q despite splitting mod every prime!
  let cyc8 = qpoly_normalize([
    rat_one(),
    rat_zero(),
    rat_zero(),
    rat_zero(),
    rat_one(),
  ])
  assert_true(qpoly_is_irreducible(cyc8))
}
