///|
test "topos Möbius Z/2Z stack descent contrast and nerve homotopy" {
  let (pre_fib, pre_diag) = build_circle_z2_torsor_stack(false)
  let (stk_fib, stk_diag) = build_circle_z2_torsor_stack(true)
  // Trivial-only prestack fails effective descent for the twisted Möbius cocycle;
  // full groupoid stack including Möbius satisfies effective descent.
  assert_true(!verify_stack_effective_descent(pre_fib, pre_diag))
  assert_true(verify_stack_effective_descent(stk_fib, stk_diag))
  let ht_s1 = compute_nerve_homotopy_type(boundary_simplex_nerve(2))
  let ht_s2 = compute_nerve_homotopy_type(boundary_simplex_nerve(3))
  assert_eq(ht_s1.pi1_free_rank, 1)
  assert_eq(ht_s1.betti_numbers, [1, 1, 0, 0])
  assert_eq(ht_s2.betti_numbers, [1, 0, 1, 0])
}

///|
test "topos sheafification universal property and geometric DNF soundness" {
  let s1_poset = cat_circle_open_poset()
  let s1_site = site_new(s1_poset, topology_from_coverage(s1_poset, [(0, [])]))
  let (two_psh, _, _) = presheaf_coproduct(
    presheaf_terminal(s1_poset),
    presheaf_terminal(s1_poset),
  )
  let sh = sheafify(s1_site, two_psh)
  assert_true(!is_sheaf(s1_site, two_psh))
  assert_true(
    verify_sheafification_universal_property(s1_site, two_psh, sh.sheaf),
  )

  let sierp = @sym.cat_arrow()
  let sierp_site = site_new(sierp, topology_trivial(sierp))
  let model : SheafStructure = {
    carrier: presheaf_constant_raw(sierp, 2),
    pred_arities: [0, 1, 1],
    relations: [[[[]], []], [[[0]], []], [[[1]], [[1]]]],
  }
  let f : GeoFormula = GAnd(
    GPred(0, []),
    GExists(GOr([GPred(1, [0]), GPred(2, [0])])),
  )
  assert_true(verify_geometric_normal_form_soundness(sierp_site, model, 0, f))
}
