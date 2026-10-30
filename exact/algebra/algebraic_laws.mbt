///|
fn qpoly_reconstruct_squarefree(factors : Array[QPolyFactor]) -> QPoly {
  let mut acc = qpoly_one()
  for i in 0..<factors.length() {
    acc = qpoly_mul(acc, qpoly_pow(factors[i].factor, factors[i].multiplicity))
  }
  acc
}

///|
fn check_qpoly_algebra() -> Bool {
  let x = qpoly_x()
  let p = qpoly_mul(
    qpoly_pow(qpoly_sub(x, qpoly_int(1)), 2),
    qpoly_mul(
      qpoly_pow(qpoly_sub(x, qpoly_int(2)), 3),
      qpoly_add(qpoly_mul(x, x), qpoly_int(1)),
    ),
  )
  let factors = qpoly_squarefree_factorization(p)
  let ext = qpoly_extgcd(
    qpoly_pow(qpoly_sub(x, qpoly_int(2)), 2),
    qpoly_sub(x, qpoly_int(3)),
  )
  let roots = qpoly_rational_roots(p)
  factors.length() == 3 &&
  qpoly_eq(qpoly_reconstruct_squarefree(factors), qpoly_monic(p)) &&
  !qpoly_is_squarefree(p) &&
  qpoly_is_squarefree(qpoly_squarefree_part(p)) &&
  qpoly_is_one(ext.g) &&
  qpoly_eq(
    qpoly_add(
      qpoly_mul(ext.s, qpoly_pow(qpoly_sub(x, qpoly_int(2)), 2)),
      qpoly_mul(ext.t, qpoly_sub(x, qpoly_int(3))),
    ),
    qpoly_one(),
  ) &&
  roots.length() == 2 &&
  qpoly_root_multiplicity(p, rat_int(1)) == 2 &&
  qpoly_root_multiplicity(p, rat_int(2)) == 3 &&
  qpoly_eq(
    qpoly_factor_rational_roots(p).residual,
    qpoly_add(qpoly_mul(x, x), qpoly_int(1)),
  )
}

///|
fn rat_vec_is(v : QVec, expected : Array[Int32]) -> Bool {
  if v.length() != expected.length() {
    return false
  }
  for i in 0..<v.length() {
    if !rat_eq(v[i], rat_int(expected[i])) {
      return false
    }
  }
  true
}

///|
fn check_rational_Jordan() -> Bool {
  // A 3-block at 2, blocks 2 and 1 at -1, conjugated by a shear so
  // the test matrix is not already in Jordan form.
  let j0 = qmat_from_int_rows([
    [2, 1, 0, 0, 0, 0],
    [0, 2, 1, 0, 0, 0],
    [0, 0, 2, 0, 0, 0],
    [0, 0, 0, -1, 1, 0],
    [0, 0, 0, 0, -1, 0],
    [0, 0, 0, 0, 0, -1],
  ])
  let shear = qmat_identity(6)
  shear.rows[0][3] = rat_int(2)
  shear.rows[1][4] = rat_int(-1)
  shear.rows[2][5] = rat_int(3)
  match qmat_inverse(shear) {
    Some(inv) => {
      let a = qmat_mul(qmat_mul(shear, j0), inv)
      let g2 = qmat_generalized_eigenspace(a, rat_int(2))
      let gm = qmat_generalized_eigenspace(a, rat_int(-1))
      let decomposition = match qmat_Jordan_decomposition_auto(a) {
        Some(dec) =>
          qmat_eq(qmat_mul(a, dec.p), qmat_mul(dec.p, dec.j)) &&
          qmat_rank(dec.p) == 6
        None => false
      }
      let expected_minpoly = qpoly_mul(
        qpoly_pow(qpoly_root_factor(rat_int(2)), 3),
        qpoly_pow(qpoly_root_factor(rat_int(-1)), 2),
      )
      g2.algebraic_multiplicity == 3 &&
      g2.geometric_multiplicity == 1 &&
      g2.index == 3 &&
      g2.block_sizes == [3] &&
      g2.basis.length() == 3 &&
      gm.algebraic_multiplicity == 3 &&
      gm.geometric_multiplicity == 2 &&
      gm.block_sizes == [2, 1] &&
      decomposition &&
      !qmat_is_diagonalizable_rational(a) &&
      qpoly_eq(qmat_minimal_polynomial(a), expected_minpoly) &&
      qmat_is_zero(qmat_poly_eval(qmat_minimal_polynomial(a), a)) &&
      qmat_is_zero(qmat_poly_eval(qmat_charpoly(a), a))
    }
    None => false
  }
}

///|
fn check_generalized_projectors() -> Bool {
  let a = qmat_from_int_rows([[2, 1, 0], [0, 2, 0], [0, 0, 3]])
  let repeated = match qmat_generalized_projector(a, rat_int(2)) {
    Some(pp) => {
      let expected = qmat_from_int_rows([[1, 0, 0], [0, 1, 0], [0, 0, 0]])
      qmat_eq(pp.projector, expected) &&
      qmat_eq(qmat_mul(pp.projector, pp.projector), pp.projector) &&
      qmat_eq(qmat_add(pp.projector, pp.complement), qmat_identity(3)) &&
      qmat_eq(qmat_mul(a, pp.projector), qmat_mul(pp.projector, a)) &&
      qmat_is_zero(
        qmat_mul(
          qmat_pow(qmat_sub(a, qmat_scalar(rat_int(2), 3)), 2),
          pp.projector,
        ),
      ) &&
      qmat_rank(pp.projector) == 2 &&
      qmat_column_basis(pp.projector).length() == 2
    }
    None => false
  }
  // An irreducible quadratic primary component (rotation block):
  let b = qmat_from_int_rows([[0, -1, 0], [1, 0, 0], [0, 0, 2]])
  let x2p1 = qpoly_normalize([rat_one(), rat_zero(), rat_one()])
  let primary = match qmat_primary_projector(b, x2p1) {
    Some(pp) =>
      qmat_eq(
        pp.projector,
        qmat_from_int_rows([[1, 0, 0], [0, 1, 0], [0, 0, 0]]),
      ) &&
      qmat_primary_subspace_basis(b, x2p1).length() == 2
    None => false
  }
  // Repeated eigenvalue of a diagonalizable (Hermitian) matrix: the
  // generalized projector is the ordinary spectral projector.
  let h = qmat_from_int_rows([[2, 0, 0], [0, 2, 0], [0, 0, 3]])
  let hermitian = match qmat_generalized_projector(h, rat_int(2)) {
    Some(pp) =>
      qmat_eq(
        pp.projector,
        qmat_from_int_rows([[1, 0, 0], [0, 1, 0], [0, 0, 0]]),
      ) &&
      qmat_diagonalizable_at(h, rat_int(2)) &&
      qmat_is_diagonalizable_rational(h)
    None => false
  }
  repeated && primary && hermitian
}

///|
fn check_quadratic_numbers() -> Bool {
  let sqrt2 = quad_sqrt_int(2)
  let one_plus = quad_add(quad_one(), sqrt2)
  let inverse_ok = match quad_inv(one_plus) {
    Some(inv) =>
      quad_eq(quad_mul(one_plus, inv), quad_one()) &&
      quad_eq(inv, quad_make(rat_int(-1), rat_one(), 2))
    None => false
  }
  let denested = match
    quad_denested_sqrt(quad_make(rat_int(5), rat_int(2), 6)) {
    Some((u, v)) => quad_eq(u, quad_sqrt_int(3)) && quad_eq(v, quad_sqrt_int(2))
    None => false
  }
  quad_eq(quad_sqrt_int(12), quad_make(rat_zero(), rat_int(2), 3)) &&
  quad_eq(quad_sqrt_rat(rat_make(9, 4)), quad_rat(rat_make(3, 2))) &&
  quad_eq(quad_sqrt_int(-4), quad_make(rat_zero(), rat_int(2), -1)) &&
  quad_eq(quad_mul(one_plus, one_plus), quad_make(rat_int(3), rat_int(2), 2)) &&
  rat_eq(quad_norm(one_plus), rat_int(-1)) &&
  rat_eq(quad_trace(one_plus), rat_int(2)) &&
  inverse_ok &&
  denested
}

///|
fn check_algebraic_numbers() -> Bool {
  let sqrt2_mod = qpoly_normalize([rat_int(-2), rat_zero(), rat_one()])
  let t = alg_generator(sqrt2_mod)
  let one_plus = alg_add(alg_one(sqrt2_mod), t)
  let squared = alg_mul(one_plus, one_plus)
  let inverse_ok = match alg_inv(one_plus) {
    Some(inv) => alg_eq(alg_mul(one_plus, inv), alg_one(sqrt2_mod))
    None => false
  }
  let minpoly = alg_minimal_polynomial(one_plus)
  let expected_minpoly = qpoly_normalize([rat_int(-1), rat_int(-2), rat_one()])
  let cube_mod = qpoly_normalize([
    rat_int(-2),
    rat_zero(),
    rat_zero(),
    rat_one(),
  ])
  let c = alg_generator(cube_mod)
  let cube_inverse = match alg_inv(c) {
    Some(inv) => alg_eq(inv, alg_scale_rat(rat_make(1, 2), alg_pow(c, 2)))
    None => false
  }
  rat_vec_is(alg_coeffs(squared), [3, 2]) &&
  alg_eq(alg_pow(t, 2), alg_int(sqrt2_mod, 2)) &&
  rat_eq(alg_norm(one_plus), rat_int(-1)) &&
  rat_eq(alg_trace(one_plus), rat_int(2)) &&
  inverse_ok &&
  qpoly_eq(minpoly, expected_minpoly) &&
  alg_is_zero(alg_eval_qpoly(minpoly, one_plus)) &&
  qpoly_eq(alg_rebase_to_minimal(one_plus).modulus, expected_minpoly) &&
  qpoly_irreducible_upto3(cube_mod) &&
  alg_eq(alg_pow(c, 3), alg_int(cube_mod, 2)) &&
  cube_inverse &&
  alg_eq(alg_sqrt_rat(rat_int(2)), alg_of_quad(quad_sqrt_int(2)))
}

///|
fn check_algebraic_Jordan() -> Bool {
  let sqrt2_mod = qpoly_normalize([rat_int(-2), rat_zero(), rat_one()])
  let t = alg_generator(sqrt2_mod)
  let a = algmat_zero(sqrt2_mod, 2)
  a.rows[0][0] = t
  a.rows[0][1] = alg_one(sqrt2_mod)
  a.rows[1][1] = t
  let generalized = algmat_generalized_eigenspace(a, t)
  let decomposition_sqrt2 = match algmat_Jordan_decomposition(a, [t]) {
    Some(dec) =>
      algmat_eq(algmat_mul(a, dec.p), algmat_mul(dec.p, dec.j)) &&
      dec.block_sizes == [[2]]
    None => false
  }
  let i_mod = qpoly_normalize([rat_one(), rat_zero(), rat_one()])
  let i = alg_generator(i_mod)
  let rotation = algmat_from_qmat(qmat_from_int_rows([[0, -1], [1, 0]]), i_mod)
  let eigenspace = algmat_generalized_eigenspace(rotation, i)
  let eigenvector_ok = eigenspace.basis.length() == 1 &&
    ({
      let v = eigenspace.basis[0]
      let av = algmat_vec(rotation, v)
      let iv : AlgVec = []
      for k in 0..<v.length() {
        iv.push(alg_mul(i, v[k]))
      }
      av.length() == iv.length() && alg_eq(av[0], iv[0]) && alg_eq(av[1], iv[1])
    })
  let decomposition_i = match
    algmat_Jordan_decomposition(rotation, [i, alg_neg(i)]) {
    Some(dec) =>
      algmat_eq(algmat_mul(rotation, dec.p), algmat_mul(dec.p, dec.j)) &&
      dec.block_sizes == [[1], [1]]
    None => false
  }
  generalized.algebraic_multiplicity == 2 &&
  generalized.geometric_multiplicity == 1 &&
  generalized.block_sizes == [2] &&
  generalized.basis.length() == 2 &&
  decomposition_sqrt2 &&
  eigenspace.algebraic_multiplicity == 1 &&
  eigenvector_ok &&
  decomposition_i
}

///|
pub fn check_algebraic_extensions_and_Jordan() -> Bool {
  check_qpoly_algebra() &&
  check_rational_Jordan() &&
  check_generalized_projectors() &&
  check_quadratic_numbers() &&
  check_algebraic_numbers() &&
  check_algebraic_Jordan()
}
