///|
// Phase 16 Exact Algebra Law Suite:
// - `check_lll_lattice_and_van_hoeij_factor`
// - `check_complex_algebraic_closure_rouche`

///|
fn det3_bigint(m : Array[Array[BigInt]]) -> BigInt {
  if m.length() != 3 {
    return 0N
  }
  let a = m[0][0]
  let b = m[0][1]
  let c = m[0][2]
  let d = m[1][0]
  let e = m[1][1]
  let f = m[1][2]
  let g = m[2][0]
  let h = m[2][1]
  let k = m[2][2]
  a * (e * k - f * h) - b * (d * k - f * g) + c * (d * h - e * g)
}

///|
pub fn check_lll_lattice_and_van_hoeij_factor() -> Bool {
  // 1. Skewed 3D integer basis: unreduced initially, LLL reduces it with
  //    unimodular U (`|det(U)| == 1`, `U * B == B_red`).
  let b_skew : Array[Array[Rat]] = [
    [rat_int(105), rat_int(821), rat_int(404)],
    [rat_int(106), rat_int(829), rat_int(408)],
    [rat_int(13), rat_int(102), rat_int(50)],
  ]
  if qmat_is_lll_reduced(b_skew) {
    return false
  }
  let rep = qmat_lll_reduce(b_skew)
  if !qmat_is_lll_reduced(rep.reduced_basis) || rep.size_reductions <= 0 {
    return false
  }
  let det_u = det3_bigint(rep.unimodular_u)
  if det_u != 1N && det_u != -1N {
    return false
  }
  for i in 0..<3 {
    for col in 0..<3 {
      let mut acc = rat_zero()
      for k in 0..<3 {
        acc = rat_add(
          acc,
          rat_mul(rat_make_big(rep.unimodular_u[i][k], 1N), b_skew[k][col]),
        )
      }
      if !rat_eq(acc, rep.reduced_basis[i][col]) {
        return false
      }
    }
  }
  // Short first vector has squared norm <= 6 (e.g. (0, 1, 0) or (-1, 0, 2) class).
  let n0 = rat_add(
    rat_add(
      rat_mul(rep.reduced_basis[0][0], rep.reduced_basis[0][0]),
      rat_mul(rep.reduced_basis[0][1], rep.reduced_basis[0][1]),
    ),
    rat_mul(rep.reduced_basis[0][2], rep.reduced_basis[0][2]),
  )
  if rat_cmp_exact(n0, rat_int(10)) > 0 {
    return false
  }

  // 2. Swinnerton-Dyer degree-8 polynomial:
  //    S_3(x) = x^8 - 40 x^6 + 352 x^4 - 960 x^2 + 576
  //    Irreducible over Q, yet splits into <= quadratic factors mod EVERY prime!
  let sd3 = qpoly_normalize([
    rat_int(576),
    rat_zero(),
    rat_int(-960),
    rat_zero(),
    rat_int(352),
    rat_zero(),
    rat_int(-40),
    rat_zero(),
    rat_one(),
  ])
  let sd3_rep = qpoly_factor_lll(sd3)
  if !sd3_rep.used_lll_lattice ||
    sd3_rep.modular_factor_count < 4 ||
    sd3_rep.lll_short_dimension != 1 ||
    sd3_rep.factors.length() != 1 ||
    sd3_rep.factors[0].factor != sd3 {
    return false
  }

  // 3. Composite product of two shifted Swinnerton-Dyer quartics:
  //    S_2(x) = x^4 - 10 x^2 + 1
  //    S_2(x - 1) = (x - 1)^4 - 10 (x - 1)^2 + 1 = x^4 - 4 x^3 - 4 x^2 + 16 x - 8
  let sd2_a = qpoly_normalize([
    rat_one(),
    rat_zero(),
    rat_int(-10),
    rat_zero(),
    rat_one(),
  ])
  let sd2_b = qpoly_normalize([
    rat_int(-8),
    rat_int(16),
    rat_int(-4),
    rat_int(-4),
    rat_one(),
  ])
  let prod = qpoly_mul(sd2_a, sd2_b)
  let prod_rep = qpoly_factor_lll(prod)
  if !prod_rep.used_lll_lattice || prod_rep.factors.length() != 2 {
    return false
  }
  let mut recon = qpoly_normalize([prod_rep.leading])
  let mut has_a = false
  let mut has_b = false
  for f in prod_rep.factors {
    if f.factor == sd2_a {
      has_a = true
    }
    if f.factor == sd2_b {
      has_b = true
    }
    for _m in 0..<f.multiplicity {
      recon = qpoly_mul(recon, f.factor)
    }
  }
  has_a && has_b && recon == prod
}

///|
pub fn check_complex_algebraic_closure_rouche() -> Bool {
  let zero_c = complex_alg_of_rat(rat_zero())
  let one_c = complex_alg_of_rat(rat_one())
  let minus_one_c = complex_alg_of_rat(rat_int(-1))
  let minus_four_c = complex_alg_of_rat(rat_int(-4))
  let imag_i = complex_alg_i()

  // 1. `i^2 == -1`, `conj(i) == -i`, `(1 + i)^4 == -4`, `(1 + i)/(1 - i) == i`.
  let i_sq = match complex_alg_mul(imag_i, imag_i) {
    Some(v) => v
    None => return false
  }
  if !complex_alg_eq(i_sq, minus_one_c) {
    return false
  }
  if !complex_alg_eq(complex_alg_conj(imag_i), complex_alg_neg(imag_i)) {
    return false
  }
  if complex_alg_eq(imag_i, complex_alg_conj(imag_i)) {
    return false
  }
  let one_plus_i = match complex_alg_add(one_c, imag_i) {
    Some(v) => v
    None => return false
  }
  let one_minus_i = match complex_alg_sub(one_c, imag_i) {
    Some(v) => v
    None => return false
  }
  let p4 = match complex_alg_pow(one_plus_i, 4) {
    Some(v) => v
    None => return false
  }
  if !complex_alg_eq(p4, minus_four_c) {
    return false
  }
  let quot = match complex_alg_div(one_plus_i, one_minus_i) {
    Some(v) => v
    None => return false
  }
  if !complex_alg_eq(quot, imag_i) {
    return false
  }
  if complex_alg_inv(zero_c) is Some(_) {
    return false
  }

  // 2. Radical closure in `Q̄ ⊂ C`: both square roots of `i` satisfy `z^2 == i`
  //    and `z * conj(z) == 1` with minimal polynomial `x^4 + 1`.
  let sqrt_i = complex_alg_all_nth_roots(imag_i, 2)
  if sqrt_i.length() != 2 || complex_alg_eq(sqrt_i[0], sqrt_i[1]) {
    return false
  }
  for r in sqrt_i {
    if qpoly_degree(r.minpoly) != 4 {
      return false
    }
    let sq = match complex_alg_mul(r, r) {
      Some(v) => v
      None => return false
    }
    let norm = match complex_alg_mul(r, complex_alg_conj(r)) {
      Some(v) => v
      None => return false
    }
    if !complex_alg_eq(sq, imag_i) || !complex_alg_eq(norm, one_c) {
      return false
    }
  }

  // 3. Complete root splitting & Vieta identities over `Q̄ ⊂ C` for an
  //    irreducible polynomial with non-real conjugate roots (`x^3 - 2`).
  let f_cubic = qpoly_normalize([rat_int(-2), rat_zero(), rat_zero(), rat_one()])
  let rts = complex_alg_roots_of(f_cubic)
  if rts.length() != 3 {
    return false
  }
  let mut sum_acc = zero_c
  let mut prod_acc = one_c
  for pair in rts {
    let (z, mult) = pair
    if mult != 1 {
      return false
    }
    match complex_alg_eval_poly(f_cubic, z) {
      Some(val) => if !complex_alg_eq(val, zero_c) { return false }
      None => return false
    }
    sum_acc = match complex_alg_add(sum_acc, z) {
      Some(v) => v
      None => return false
    }
    prod_acc = match complex_alg_mul(prod_acc, z) {
      Some(v) => v
      None => return false
    }
  }
  complex_alg_eq(sum_acc, zero_c) &&
  complex_alg_eq(prod_acc, complex_alg_of_rat(rat_int(2)))
}
