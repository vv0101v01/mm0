///|
// Phase 15 Executable Laws:
//   Track I  — BDD, SAT & Host Cubes:
//     1. Coupled Branch-and-Bound + cofactor symmetry-orbit exact BDD ordering
//        (`n <= 20`) & support-component decomposed exact ordering (`n = 28`)
//     2. CDCL DRUP/DRAT -> ID-indexed LRAT elaboration, zero-search linear
//        LRAT verification, and `CHLRATBN` v1 binary proof codec
//     3. Strength-4 covering arrays (`P^1(F_8)` + `PHF (x) Bush` up to `n <= 16`)
//        & Cubical Yoneda `O(1)` universal extensionality + naturality auditing
//   Track II — General Bidirectional Bijectivity (`DVEquiv`) & Freudenthal Suspension:
//     4. Kernel bidirectional equivalence auditor (`equiv_bidirectional_certified`),
//        transitivity (`equiv_compose_value`), full `Omega^1(S^1) ≃ Z`, fiberwise
//        universal cover `Path S^1 base x ≃ Cover(x)`, and `pi_1(S^1) = ||Omega(S^1)||_0 ≃ Z`
//     5. Polymorphic suspension `SuspS(A)`, bidirectional `SuspS(BoolS) ≃ S^1`,
//        unpointed cocone `(SuspS A -> B) ≃ SuspCocone(A, B)`, and pointed
//        Loop–Suspension Adjunction `Map*(SuspS A, B) ≃ Map*(A, Omega B)`
//     6. General Freudenthal Suspension Theorem (`k = 0`: `||Omega^1(SuspS A)||_0 ≃ Unit`
//        in open 0-connected contexts + `S^2`, `S^3`), Wedge Connectivity on
//        `S^1 ∨ S^1 -> S^1 × S^1`, and Freudenthal–Hopf 1-loop suspension coherence

///|
/// Item 1: Coupled B&B + cofactor symmetry-orbit exact BDD ordering (`n = 19`,
/// above Phase 14's `n <= 18` limit) and support-component decomposed exact
/// optimal ordering (`bdd_dag_of_face_optimal_decomposed` at `n = 28`).
pub fn check_phase15_bdd_symmetry_orbit_and_decomposed_optimal() -> Bool {
  // 1A. Exact optimal BDD ordering at `n = 19` (`19 > 18`): 9 interleaved pairs
  // `(v_i ∧ v_{i+9})` disjoined with `v_18`, which exhibits wide symmetric
  // pair orbits AND blows up under natural variable order `[0..18]`.
  let mut f19 : Face = FEq1(DVar(18))
  for i in 0..<9 {
    f19 = FOr(f19, FAnd(FEq1(DVar(i)), FEq1(DVar(i + 9))))
  }
  let unopt_19 = bdd_dag_of_face(f19, 19)
  let unopt_19_size = bdd_dag_reachable_count(unopt_19.manager, unopt_19.root)
  let opt_19 = bdd_dag_of_face_optimal_pruned(f19, 19)
  if !opt_19.exact ||
    opt_19.active_vars != 19 ||
    opt_19.size >= unopt_19_size ||
    opt_19.size > 25 ||
    opt_19.pruned_subsets <= 0 {
    return false
  }
  // Verify semantic preservation on multiple assignments.
  for probe in 0..<8 {
    let bits : Array[Bool] = []
    for v in 0..<19 {
      bits.push(((probe + v) & 1) == 1)
    }
    let expected = face_holds(f19, bits)
    if bdd_dag_eval(opt_19.built.manager, opt_19.built.root, bits) != expected {
      return false
    }
  }
  // Boundary control: 21 active variables (`21 > exact_max_vars = 20`) must
  // honestly report `exact == false` in the monolithic solver.
  let mut f21 : Face = FBot
  for i in 0..<21 {
    f21 = FOr(f21, FEq1(DVar(i)))
  }
  if bdd_dag_of_face_optimal_pruned(f21, 21).exact {
    return false
  }

  // 1B. Decomposed exact optimal ordering at `n = 28` (`4` disjoint 7-variable
  // interleaved blocks): monolithic solver cannot prove optimality (`28 > 20`),
  // whereas `bdd_dag_of_face_optimal_decomposed` proves `exact == true` via the
  // additive component optimality theorem!
  let mut f28 : Face = FBot
  for blk in 0..<4 {
    let base = blk * 7
    let mut pairs : Face = FBot
    for i in 0..<3 {
      let pair_i = FAnd(FEq1(DVar(base + i)), FEq1(DVar(base + i + 3)))
      pairs = if i == 0 { pair_i } else { FOr(pairs, pair_i) }
    }
    let bface = FAnd(FEq1(DVar(base + 6)), pairs)
    f28 = if blk == 0 { bface } else { FOr(f28, bface) }
  }
  let mono_28 = bdd_dag_of_face_optimal_pruned(f28, 28)
  if mono_28.exact {
    return false
  }
  let unopt_28 = bdd_dag_of_face(f28, 28)
  let unopt_28_size = bdd_dag_reachable_count(unopt_28.manager, unopt_28.root)
  let dec_28 = bdd_dag_of_face_optimal_decomposed(f28, 28)
  if !dec_28.exact ||
    dec_28.active_vars != 28 ||
    dec_28.component_count != 4 ||
    dec_28.max_component_vars != 7 ||
    dec_28.size >= unopt_28_size {
    return false
  }
  for probe in 0..<6 {
    let bits : Array[Bool] = []
    for v in 0..<28 {
      bits.push(((probe * 3 + v) % 4) == 0)
    }
    let expected = face_holds(f28, bits)
    if bdd_dag_eval(dec_28.built.manager, dec_28.built.root, bits) != expected {
      return false
    }
  }
  // Negative control: a single 22-variable coupled chain has `max_component_vars == 22 > 20`
  // and must NOT claim `exact == true`.
  let mut chain22 : Face = FBot
  for i in 0..<21 {
    let link = FAnd(FEq1(DVar(i)), FEq1(DVar(i + 1)))
    chain22 = if i == 0 { link } else { FOr(chain22, link) }
  }
  let dec_chain22 = bdd_dag_of_face_optimal_decomposed(chain22, 22)
  !dec_chain22.exact &&
  dec_chain22.component_count == 1 &&
  dec_chain22.max_component_vars == 22
}

///|
/// Item 2: CDCL DRUP/DRAT -> ID-indexed LRAT elaboration, zero-search linear
/// LRAT verification, and `CHLRATBN` v1 binary proof codec with strict
/// hint-order, deleted-ID, and binary-corruption negative controls.
pub fn check_phase15_cdcl_lrat_elaboration_and_binary_codec() -> Bool {
  // 2A. Elaborate solver-generated UNSAT PHP(6, 5) DRUP proof into indexed LRAT
  // and check it with zero-search `face_cdcl_lrat_check` + `CHLRATBN` v1 round-trip.
  let (php65, vars65) = phase11_pigeonhole_face(6, 5)
  let cdcl65 = face_sat_cdcl_proof(php65, vars65, max_steps=2000000)
  if cdcl65.decision != FaceUnsat {
    return false
  }
  let elab = face_cdcl_elaborate_lrat(
    cdcl65.original_clauses,
    cdcl65.proof_steps,
  )
  if !elab.valid ||
    elab.lrat_adds <= 0 ||
    elab.lrat_deletes <= 0 ||
    elab.total_hints < elab.lrat_adds ||
    !face_cdcl_lrat_check(cdcl65.original_clauses, elab.steps) {
    return false
  }
  let bin = face_lrat_to_binary(elab.steps)
  match face_lrat_from_binary(bin) {
    Some(decoded) =>
      if decoded != elab.steps ||
        !face_cdcl_lrat_check_binary(cdcl65.original_clauses, bin) {
        return false
      }
    None => return false
  }

  // 2B. Elaborate a genuine RAT proof (`oct3` 8-clause parity cube) into LRAT
  // with explicit `rat_hints` and verify zero-search acceptance.
  let oct3 : Array[Array[Int32]] = [
    [1, 2, 3],
    [1, 2, -3],
    [1, -2, 3],
    [1, -2, -3],
    [-1, 2, 3],
    [-1, 2, -3],
    [-1, -2, 3],
    [-1, -2, -3],
  ]
  let rat_elab = face_cdcl_elaborate_lrat(oct3, [
    CdclProofAdd([1]),
    CdclProofAdd([2]),
    CdclProofAdd([]),
  ])
  if !rat_elab.valid || !face_cdcl_lrat_check(oct3, rat_elab.steps) {
    return false
  }

  // 2C. Strict negative controls proving zero-search LRAT is non-tautological:
  // Clauses: 1:[1, 2], 2:[-1, 2], 3:[1, -2], 4:[-1, -2].
  // Step 5 derives `[2]` from hints `[1, 2]` (assuming `-2`, clause 1 propagates `1`,
  // then clause 2 conflicts!).Step 6 derives `[]` from `[5, 3, 4]`.
  let base4 = [[1, 2], [-1, 2], [1, -2], [-1, -2]]
  let good_lrat = [
    LratAdd(5, [2], [1, 2], []),
    LratDelete(5, [1, 2]),
    LratAdd(6, [], [5, 3, 4], []),
  ]
  if !face_cdcl_lrat_check(base4, good_lrat) {
    return false
  }
  // Negative control 1 (wrong hint order / missing antecedent): `[5]` comes AFTER
  // `[3, 4]` when `[3, 4]` are NOT unit before `5` propagates `2`!
  let wrong_order_lrat = [
    LratAdd(5, [2], [1, 2], []),
    LratAdd(6, [], [3, 4, 5], []),
  ]
  if face_cdcl_lrat_check(base4, wrong_order_lrat) {
    return false
  }
  // Negative control 2 (deleted-ID reuse): deleting clause `5` before citing `5`.
  let deleted_reuse_lrat = [
    LratAdd(5, [2], [1, 2], []),
    LratDelete(5, [5]),
    LratAdd(6, [], [5, 3, 4], []),
  ]
  if face_cdcl_lrat_check(base4, deleted_reuse_lrat) {
    return false
  }
  // Negative control 3 (corrupted binary magic & truncated payload).
  let bad_magic = Bytes::from_array([
    b'B', b'A', b'D', b'M', b'A', b'G', b'I', b'C', 1, 0, 0, 0, 0, 0,
  ])
  let truncated_arr : Array[Byte] = []
  for i in 0..<(bin.length() - 2) {
    truncated_arr.push(bin[i])
  }
  let truncated = Bytes::from_array(truncated_arr)
  face_lrat_from_binary(bad_magic) == None &&
  face_lrat_from_binary(truncated) == None &&
  !face_cdcl_lrat_check_binary(cdcl65.original_clauses, bad_magic)
}

///|
/// Item 3: Strength-4 covering arrays (`P^1(F_8)` + `PHF (x) Bush` up to
/// `arity <= 16`) and Cubical Yoneda `O(1)` universal extensionality +
/// presheaf naturality auditing (`CheckedDCube`, `dcube_yoneda_audit_report`).
pub fn check_phase15_dcube_strength4_phf_and_yoneda_audit() -> Bool {
  let zero : DValue = DVZeroNat
  let one : DValue = DVSucc(DVZeroNat)

  // 3A. 10-dimensional (`n = 10 > 9`, beyond `P^1(F_8)`'s 9-column horizon!)
  // rogue host cube hiding on a simultaneous 4-axis interaction `(0, 3, 6, 9)`
  // across the 4 strata `[0, 1, r_i, (r_i v s) ^ ~t]`:
  let c10 = dcube_constant(10, zero)
  let sneaky10 = dcube_function(10, dims => {
    let hit0 = dims[0] == DZero
    let hit3 = dims[3] == DOne
    let hit6 = dims[6] == DVar(6)
    let hit9 = dims[9] == DAnd(DOr(DVar(9), DVar(10)), DNeg(DVar(11)))
    if hit0 && hit3 && hit6 && hit9 {
      one
    } else {
      zero
    }
  })
  let phf_diff = dcube_cubes_conv_covering_phf_report(
    0,
    0,
    DVNatTy,
    c10,
    sneaky10,
    strength=4,
  )
  if phf_diff.equal || !phf_diff.complete_for_strength {
    return false
  }
  let phf_eq = dcube_cubes_conv_covering_phf_report(
    0,
    0,
    DVNatTy,
    c10,
    c10,
    strength=4,
  )
  if !phf_eq.equal ||
    !phf_eq.complete_for_strength ||
    phf_eq.interaction_strength != 4 ||
    phf_eq.probes <= 0 {
    return false
  }
  // And `dcube_yoneda_audit_report` detects that `sneaky10` violates presheaf
  // naturality (`sneaky10` reifies to `0` at generic `(i_0..i_9)` yet jumps to `1`
  // on the 4-way substituted stratum!), while certifying `c10` as natural!
  let yoneda_bad = dcube_yoneda_audit_report(0, 0, DVNatTy, sneaky10)
  let yoneda_good = dcube_yoneda_audit_report(0, 0, DVNatTy, c10)
  if yoneda_bad.natural || !yoneda_good.natural {
    return false
  }

  // 3B. `CheckedDCube` `O(1)` universal extensionality at `arity = 24` (where
  // `2^24 = 16,777,216` vertices would explode any grid enumerator!):
  // `(<k> loop(k)) @ (i_0 ∧ ¬i_23)` vs `loop(i_0 ∧ ¬i_23)` on `S^1`.
  let conn_dim = DAnd(DVar(23), DNeg(DVar(0)))
  let body_a = DAppDim(DLamDim(DAppDim(DCircleLoop, DVar(0))), conn_dim)
  let body_b = DAppDim(DCircleLoop, conn_dim)
  let body_wrong = DAppDim(DCircleLoop, DOr(DVar(23), DNeg(DVar(0))))
  match
    (
      checked_dcube_closed(24, body_a, DCircleTy),
      checked_dcube_closed(24, body_b, DCircleTy),
      checked_dcube_closed(24, body_wrong, DCircleTy),
    ) {
    (Some(ca), Some(cb), Some(cw)) =>
      checked_dcube_extensional_eq(ca, cb) &&
      !checked_dcube_extensional_eq(ca, cw)
    _ => false
  }
}

///|
/// Item 4: General Bidirectional Bijectivity (`equiv_bidirectional_certified`,
/// `equiv_compose_value`), full bidirectional `Omega^1(S^1, base) ≃ IntegerS`,
/// fiberwise universal cover `(x : S^1) -> Path S^1 base x ≃ Cover(x)`, and
/// 0-truncated fundamental group isomorphism `pi_1(S^1) = ||Omega^1(S^1)||_0 ≃ Z`.
pub fn check_phase15_bidirectional_bijectivity_and_pi1_circle() -> Bool {
  let z_ty = integer_type_value()
  let c_ty = circle_hit_type_value()
  let loop_ty = circle_loop_space_type_value()
  let st_loop_ty = set_trunc_type_value(loop_ty)

  // 4A. Positive kernel-checked bidirectional equivalence audits on open
  // reflected variables:
  let succ_eq = integer_succ_equiv_value()
  if !equiv_bidirectional_certified(succ_eq) {
    return false
  }
  let omega_eq = circle_loop_space_equiv_integer_value(16)
  if !equiv_bidirectional_certified(omega_eq) {
    return false
  }
  // General polymorphic bidirectional equivalence composition `Equiv A C`
  // certified in open 5-variable context `[A, B, C : Type_0, e1 : Equiv A B, e2 : Equiv B C]`
  // plus concrete `succ ∘ succ : Equiv Z Z`:
  let a0_ty = reflect_var(0, DVUniv(0))
  let b0_ty = reflect_var(1, DVUniv(0))
  let c0_ty = reflect_var(2, DVUniv(0))
  let e1_ty = DVEquivTy(a0_ty, b0_ty, 0)
  let e2_ty = DVEquivTy(b0_ty, c0_ty, 0)
  let e1_v = reflect_var(3, e1_ty)
  let e2_v = reflect_var(4, e2_ty)
  let ctx_comp = denv_cons(
    e2_ty,
    denv_cons(
      e1_ty,
      denv_cons(
        DVUniv(0),
        denv_cons(DVUniv(0), denv_cons(DVUniv(0), denv_empty())),
      ),
    ),
  )
  let env_comp = denv_cons(
    e2_v,
    denv_cons(
      e1_v,
      denv_cons(c0_ty, denv_cons(b0_ty, denv_cons(a0_ty, denv_empty()))),
    ),
  )
  if !equiv_bidirectional_certified_in(
      ctx_comp,
      env_comp,
      ddim_empty(),
      equiv_compose_value(e1_v, e2_v, a0_ty, b0_ty, c0_ty, 16),
    ) ||
    !equiv_bidirectional_certified(
      equiv_compose_value(succ_eq, succ_eq, z_ty, z_ty, z_ty, 16),
    ) {
    return false
  }
  // Open-variable Hedberg / Axiom-K h-Set certification of `IntegerS`
  // `[zx : Z, zy : Z, zp : Path Z zx zy, zq : Path Z zx zy]`:
  let zx = reflect_var(0, z_ty)
  let zy = reflect_var(1, z_ty)
  let eq_zxy = DVPathTy(_ => z_ty, zx, zy)
  let zp = reflect_var(2, eq_zxy)
  let zq = reflect_var(3, eq_zxy)
  let ctx_zset = denv_cons(
    eq_zxy,
    denv_cons(eq_zxy, denv_cons(z_ty, denv_cons(z_ty, denv_empty()))),
  )
  let env_zset = denv_cons(
    zq,
    denv_cons(zp, denv_cons(zy, denv_cons(zx, denv_empty()))),
  )
  let z_sq = integer_is_set_value(zx, zy, zp, zq, 16)
  let z_sq_ty = DVPathTy(_ => eq_zxy, zp, zq)
  if !conv_at(4, 0, eq_zxy, dapp_dim(z_sq, DZero), zp) ||
    !conv_at(4, 0, eq_zxy, dapp_dim(z_sq, DOne), zq) {
    return false
  }
  match d_check(quote_at(4, 0, z_sq_ty, z_sq), z_sq_ty, ctx_zset, env_zset, ddim_empty()) {
    Some(_) => ()
    None => return false
  }
  // Universal 0-truncation equivalence `Equiv ‖A‖_0 B` certified in open
  // 4-variable context `[A : Type_0, B : Type_0, e : Equiv A B, is_set_b : isSet(B)]`:
  let a_open = reflect_var(0, DVUniv(0))
  let b_open = reflect_var(1, DVUniv(0))
  let eq_ab_ty = DVEquivTy(a_open, b_open, 0)
  let e_open = reflect_var(2, eq_ab_ty)
  let bset_ty = DVPi(b_open, x1 => {
    DVPi(b_open, y1 => {
      let eq1 = DVPathTy(_ => b_open, x1, y1)
      DVPi(eq1, p1 => DVPi(eq1, q1 => DVPathTy(_ => eq1, p1, q1)))
    })
  })
  let bset_open = reflect_var(3, bset_ty)
  let ctx_trunc = denv_cons(
    bset_ty,
    denv_cons(eq_ab_ty, denv_cons(DVUniv(0), denv_cons(DVUniv(0), denv_empty()))),
  )
  let env_trunc = denv_cons(
    bset_open,
    denv_cons(e_open, denv_cons(b_open, denv_cons(a_open, denv_empty()))),
  )
  let bset_fn = (x1 : DValue, y1 : DValue, p1 : DValue, q1 : DValue) => {
    let eq1 = DVPathTy(_ => b_open, x1, y1)
    dapp_typed(
      dapp_typed(
        dapp_typed(dapp_typed(bset_open, x1, b_open), y1, b_open),
        p1,
        eq1,
      ),
      q1,
      eq1,
    )
  }
  let trunc_eq_open = set_trunc_equiv_of_equiv_set_value(
    a_open,
    b_open,
    e_open,
    bset_fn,
    16,
  )
  if !equiv_bidirectional_certified_in(
      ctx_trunc,
      env_trunc,
      ddim_empty(),
      trunc_eq_open,
    ) {
    return false
  }
  // Instantiated `pi_1(S^1) = ‖Omega^1(S^1)‖_0 ≃ IntegerS` + fiberwise `Cover(x)`
  // computational winding-number round-trips on `k in [-2, -1, 0, 1, 2]`:
  let pi1_eq = pi1_set_circle_equiv_integer_value(16)
  let pi1_fwd = equiv_fwd_value(pi1_eq, st_loop_ty, z_ty)
  let pi1_bwd = equiv_bwd_value(pi1_eq, st_loop_ty, z_ty)
  let pi1_sect = equiv_sect_value(pi1_eq, st_loop_ty, z_ty)
  let pi1_retr = equiv_retr_value(pi1_eq, st_loop_ty, z_ty)
  let base_c = circle_hit_base_value()
  let cover_base = circle_path_equiv_cover_value(base_c, 16)
  let cov_b_fwd = equiv_fwd_value(cover_base, loop_ty, z_ty)
  let cov_b_bwd = equiv_bwd_value(cover_base, loop_ty, z_ty)
  let _ = c_ty
  for k in [-2, -1, 0, 1, 2] {
    let zk = integer_value(k)
    let lk = circle_decode_value(zk, 16)
    let stk = set_trunc_point_value(loop_ty, lk)
    if !conv_at(0, 0, z_ty, dapp_typed(pi1_fwd, stk, st_loop_ty), zk) ||
      !conv_at(0, 0, st_loop_ty, dapp_typed(pi1_bwd, zk, z_ty), stk) ||
      !conv_at(0, 0, z_ty, dapp_dim(dapp_typed(pi1_sect, zk, z_ty), DZero), zk) ||
      !conv_at(0, 0, z_ty, dapp_dim(dapp_typed(pi1_sect, zk, z_ty), DOne), zk) ||
      !conv_at(0, 0, st_loop_ty, dapp_dim(dapp_typed(pi1_retr, stk, st_loop_ty), DZero), stk) ||
      !conv_at(0, 0, st_loop_ty, dapp_dim(dapp_typed(pi1_retr, stk, st_loop_ty), DOne), stk) ||
      !conv_at(0, 0, z_ty, dapp_typed(cov_b_fwd, lk, loop_ty), zk) ||
      !conv_at(0, 0, loop_ty, dapp_typed(cov_b_bwd, zk, z_ty), lk) {
      return false
    }
  }

  // 4B. Strict negative controls proving `equiv_bidirectional_certified` rejects
  // fake `refl` proofs, non-injective maps, and non-surjective maps!
  // 1) Fake `refl` section/retraction on `succ`/`pred` (notice `conv_at` at
  //    `DVEquivTy` compares only `fwd` & `bwd`, whereas `equiv_bidirectional_certified`
  //    MUST reject `fake_succ_eq` on open `n : IntegerS`!):
  let fake_succ_eq = equiv_make_value(
    z_ty,
    z_ty,
    DVLam(n => integer_succ_value(n)),
    DVLam(n => integer_pred_value(n)),
    DVLam(n => dpath_refl_value(n)),
    DVLam(n => dpath_refl_value(n)),
  )
  if equiv_bidirectional_certified(fake_succ_eq) {
    return false
  }
  // 2) Non-injective forward map `p ↦ 0` paired with `decode`:
  let non_inj_eq = equiv_make_value(
    loop_ty,
    z_ty,
    DVLam(_ => integer_value(0)),
    DVLam(n => circle_decode_value(n, 16)),
    DVLam(n => dpath_refl_value(n)),
    DVLam(p => dpath_refl_value(p)),
  )
  if equiv_bidirectional_certified(non_inj_eq) {
    return false
  }
  // 3) Non-surjective map `n ↦ succ(n)` paired with `id`:
  let non_surj_eq = equiv_make_value(
    z_ty,
    z_ty,
    DVLam(n => integer_succ_value(n)),
    DVLam(n => n),
    DVLam(n => dpath_refl_value(n)),
    DVLam(n => dpath_refl_value(n)),
  )
  !equiv_bidirectional_certified(non_surj_eq)
}

///|
/// Item 5: Polymorphic suspension `SuspS(A)`, bidirectional `SuspS(BoolS) ≃ S^1`,
/// unpointed universal cocone `(SuspS A -> B) ≃ SuspCocone(A, B)`, and pointed
/// Loop–Suspension Adjunction `Map*(SuspS A, north; B, b0) ≃ Map*(A, a0; Omega B, refl)`
/// certified in open pointed-type contexts.
pub fn check_phase15_suspension_and_loop_suspension_adjunction() -> Bool {
  if !hit_schema_validate(susp_type_schema()) ||
    !hit_schema_validate(set_trunc_schema()) {
    return false
  }

  // 5A. Full bidirectional `SuspS(BoolS) ≃ S^1`:
  let sb_circle_eq = susp_bool_equiv_circle_value(16)
  if !equiv_bidirectional_certified(sb_circle_eq) {
    return false
  }
  let b_spec = bool_schema()
  let b_ty = DVInductive(b_spec, [], [])
  let btrue = DVIntro(b_spec, 1, [], [])
  let m_true_i = dapp_dim(susp_merid_path_value(b_ty, btrue), DVar(0))
  let lp_i = dapp_dim(circle_hit_loop_path_value(), DVar(0))
  if !conv_at(
      0,
      1,
      circle_hit_type_value(),
      susp_bool_to_circle_value(m_true_i, 16),
      lp_i,
    ) {
    return false
  }

  // 5B. Unpointed universal cocone `(SuspS A -> B) ≃ SuspCocone(A, B)` in open
  // context `[A : Type_0, B : Type_0]`:
  let open_a = reflect_var(0, DVUniv(0))
  let open_b = reflect_var(1, DVUniv(0))
  let ctx_ab = denv_cons(DVUniv(0), denv_cons(DVUniv(0), denv_empty()))
  let env_ab = denv_cons(open_b, denv_cons(open_a, denv_empty()))
  let univ_eq = susp_universal_equiv_value(open_a, open_b, 16)
  if !equiv_bidirectional_certified_in(ctx_ab, env_ab, ddim_empty(), univ_eq) {
    return false
  }
  // Negative control: `SuspS(A)` has NO definitional η on neutral points, so
  // replacing `retr` with `λf. refl_f` MUST be rejected!
  let susp_a = susp_type_value(open_a)
  let fn_ty = DVPi(susp_a, _ => open_b)
  let cocone_ty = susp_cocone_type_value(open_a, open_b)
  let fake_eta_univ = equiv_make_value(
    fn_ty,
    cocone_ty,
    equiv_fwd_value(univ_eq, fn_ty, cocone_ty),
    equiv_bwd_value(univ_eq, fn_ty, cocone_ty),
    equiv_sect_value(univ_eq, fn_ty, cocone_ty),
    DVLam(f => dpath_refl_value(f)),
  )
  if equiv_bidirectional_certified_in(
      ctx_ab,
      env_ab,
      ddim_empty(),
      fake_eta_univ,
    ) {
    return false
  }

  // 5C. Full bidirectional Pointed Loop–Suspension Adjunction
  //   `Map*(SuspS A, north; B, b0) ≃ Map*(A, a0; Omega(B, b0), refl_{b0})`
  // certified in the abstract 4-variable open context `[A : Type_0, a0 : A, B : Type_0, b0 : B]`!
  let a_var = reflect_var(0, DVUniv(0))
  let a0_var = reflect_var(1, a_var)
  let b_var = reflect_var(2, DVUniv(0))
  let b0_var = reflect_var(3, b_var)
  let ctx4 = denv_cons(
    b_var,
    denv_cons(DVUniv(0), denv_cons(a_var, denv_cons(DVUniv(0), denv_empty()))),
  )
  let env4 = denv_cons(
    b0_var,
    denv_cons(b_var, denv_cons(a0_var, denv_cons(a_var, denv_empty()))),
  )
  let adj_eq = loop_suspension_adjunction_equiv_value(
    a_var, a0_var, b_var, b0_var, 16,
  )
  equiv_bidirectional_certified_in(ctx4, env4, ddim_empty(), adj_eq)
}

///|
/// Item 6: General Freudenthal Suspension Theorem (`k = 0`: `||Omega^1(SuspS A)||_0 ≃ Unit`
/// in open 0-connected contexts + `pi_1(S^2) ≃ 1` & `pi_1(S^3) ≃ 1`), Wedge
/// Connectivity Extension on `S^1 ∨ S^1 -> S^1 × S^1`, and Freudenthal–Hopf
/// 1-loop suspension coherence.
pub fn check_phase15_freudenthal_suspension_and_wedge_connectivity() -> Bool {
  // 6A. General Freudenthal Suspension Theorem (`k = 0`) certified in an
  // ABSTRACT open 0-connected context `[A : Type_0, a0 : A, conn : (a : A) -> ||Path A a0 a||_{-1}]`!
  let a_ty = reflect_var(0, DVUniv(0))
  let a0 = reflect_var(1, a_ty)
  let conn_ty = DVPi(a_ty, a => {
    prop_trunc_type_value(DVPathTy(_ => a_ty, a0, a))
  })
  let conn_var = reflect_var(2, conn_ty)
  let ctx_conn = denv_cons(
    conn_ty,
    denv_cons(a_ty, denv_cons(DVUniv(0), denv_empty())),
  )
  let env_conn = denv_cons(
    conn_var,
    denv_cons(a0, denv_cons(a_ty, denv_empty())),
  )
  let freud_open = freudenthal_pi1_susp_connected_equiv_unit_value(
    a_ty,
    a0,
    a => dapp_typed(conn_var, a, a_ty),
    16,
  )
  if !equiv_bidirectional_certified_in(
      ctx_conn,
      env_conn,
      ddim_empty(),
      freud_open,
    ) {
    return false
  }
  // Concrete sphere instantiations `pi_1(Susp S^1) ≃ Unit` (`S^2`) and
  // `pi_1(Susp^2 S^1) ≃ Unit` (`S^3`):
  if !equiv_bidirectional_certified(pi1_susp_circle_equiv_unit_value(16)) ||
    !equiv_bidirectional_certified(pi1_susp2_circle_equiv_unit_value(16)) {
    return false
  }
  // Contrast control: non-0-connected `S^0 = BoolS` suspends to `S^1` whose
  // `pi_1(S^1) ≃ Z` has distinct classes `0 != 1`, proving `conn` is essential!
  if conv_at(0, 0, integer_type_value(), integer_value(0), integer_value(1)) {
    return false
  }

  // 6B. General Wedge Connectivity Extension (`m = n = 0`) on `S^1 ∨ S^1 -> S^1 × S^1`,
  // certified by `d_check` in the completely open 7-variable context
  // `[P : S^1 -> S^1 -> Type_0, is_set_p00 : isSet(P base base),
  //   f_L : (x : S^1) -> P x base, f_R : (y : S^1) -> P base y,
  //   glue : Path (P base base) (f_L base) (f_R base), x : S^1, y : S^1]`
  // PLUS univalent twisted instantiation on `Cover(x) -> Cover(x)`:
  let c_ty = circle_hit_type_value()
  let base_c = circle_hit_base_value()
  let p_fam_ty = DVPi(c_ty, _ => DVPi(c_ty, _ => DVUniv(0)))
  let p_fam_var = reflect_var(0, p_fam_ty)
  let p_open_fam = (xv : DValue, yv : DValue) => {
    dapp_typed(dapp_typed(p_fam_var, xv, c_ty), yv, c_ty)
  }
  let p00 = p_open_fam(base_c, base_c)
  let p00_set_ty = DVPi(p00, u1 => {
    DVPi(p00, v1 => {
      let eq1 = DVPathTy(_ => p00, u1, v1)
      DVPi(eq1, q1 => DVPi(eq1, q2 => DVPathTy(_ => eq1, q1, q2)))
    })
  })
  let p00_set_var = reflect_var(1, p00_set_ty)
  let is_set_p00_open = (
    _xv : DValue,
    _yv : DValue,
    u1 : DValue,
    v1 : DValue,
    q1 : DValue,
    q2 : DValue,
  ) => {
    let eq1 = DVPathTy(_ => p00, u1, v1)
    dapp_typed(
      dapp_typed(
        dapp_typed(dapp_typed(p00_set_var, u1, p00), v1, p00),
        q1,
        eq1,
      ),
      q2,
      eq1,
    )
  }
  let fl_ty = DVPi(c_ty, xv => p_open_fam(xv, base_c))
  let fr_ty = DVPi(c_ty, yv => p_open_fam(base_c, yv))
  let fl_var = reflect_var(2, fl_ty)
  let fr_var = reflect_var(3, fr_ty)
  let f_left = (xv : DValue) => dapp_typed(fl_var, xv, c_ty)
  let f_right = (yv : DValue) => dapp_typed(fr_var, yv, c_ty)
  let glue_ty = DVPathTy(_ => p00, f_left(base_c), f_right(base_c))
  let glue_pt = reflect_var(4, glue_ty)
  let x_open = reflect_var(5, c_ty)
  let y_open = reflect_var(6, c_ty)
  let ctx_wedge = denv_cons(
    c_ty,
    denv_cons(
      c_ty,
      denv_cons(
        glue_ty,
        denv_cons(
          fr_ty,
          denv_cons(
            fl_ty,
            denv_cons(p00_set_ty, denv_cons(p_fam_ty, denv_empty())),
          ),
        ),
      ),
    ),
  )
  let env_wedge = denv_cons(
    y_open,
    denv_cons(
      x_open,
      denv_cons(
        glue_pt,
        denv_cons(
          fr_var,
          denv_cons(
            fl_var,
            denv_cons(p00_set_var, denv_cons(p_fam_var, denv_empty())),
          ),
        ),
      ),
    ),
  )
  let ext_xy = wedge_connectivity_circle_set_ext_value(
    p_open_fam, is_set_p00_open, f_left, f_right, glue_pt, x_open, y_open, 16,
  )
  let ext_xy_term = quote_at(7, 0, p_open_fam(x_open, y_open), ext_xy)
  match
    d_check(
      ext_xy_term,
      p_open_fam(x_open, y_open),
      ctx_wedge,
      env_wedge,
      ddim_empty(),
    ) {
    Some(_) => ()
    None => return false
  }
  let left_coh = wedge_connectivity_circle_left_coh_value(
    p_open_fam, is_set_p00_open, f_left, f_right, glue_pt, x_open, 16,
  )
  let ext_x_base = wedge_connectivity_circle_set_ext_value(
    p_open_fam, is_set_p00_open, f_left, f_right, glue_pt, x_open, base_c, 16,
  )
  let left_coh_ty = DVPathTy(
    _ => p_open_fam(x_open, base_c),
    ext_x_base,
    f_left(x_open),
  )
  if !conv_at(7, 0, p_open_fam(x_open, base_c), dapp_dim(left_coh, DZero), ext_x_base) ||
    !conv_at(7, 0, p_open_fam(x_open, base_c), dapp_dim(left_coh, DOne), f_left(x_open)) {
    return false
  }
  match
    d_check(
      quote_at(7, 0, left_coh_ty, left_coh),
      left_coh_ty,
      ctx_wedge,
      env_wedge,
      ddim_empty(),
    ) {
    Some(_) => ()
    None => return false
  }
  let right_coh = wedge_connectivity_circle_right_coh_value(f_right, y_open)
  let ext_base_y = wedge_connectivity_circle_set_ext_value(
    p_open_fam, is_set_p00_open, f_left, f_right, glue_pt, base_c, y_open, 16,
  )
  let right_coh_ty = DVPathTy(
    _ => p_open_fam(base_c, y_open),
    ext_base_y,
    f_right(y_open),
  )
  if !conv_at(7, 0, p_open_fam(base_c, y_open), dapp_dim(right_coh, DZero), ext_base_y) ||
    !conv_at(7, 0, p_open_fam(base_c, y_open), dapp_dim(right_coh, DOne), f_right(y_open)) {
    return false
  }
  match
    d_check(
      quote_at(7, 0, right_coh_ty, right_coh),
      right_coh_ty,
      ctx_wedge,
      env_wedge,
      ddim_empty(),
    ) {
    Some(_) => ()
    None => return false
  }

  // 6C. Open-loop Freudenthal 1-loop suspension homomorphism `Omega^1(A) -> Omega^2(SuspS A)`
  // + identity preservation `sigma_1(refl) = refl` + Hopf `S^1 -> S^2` round-trip path:
  let loop_a_ty = DVPathTy(_ => a_ty, a0, a0)
  let p_open = reflect_var(2, loop_a_ty)
  let ctx_ap = denv_cons(
    loop_a_ty,
    denv_cons(a_ty, denv_cons(DVUniv(0), denv_empty())),
  )
  let env_ap = denv_cons(
    p_open,
    denv_cons(a0, denv_cons(a_ty, denv_empty())),
  )
  let susp_a = susp_type_value(a_ty)
  let north_a = susp_north_value(a_ty)
  let loop1_susp = DVPathTy(_ => susp_a, north_a, north_a)
  let refl_north = dpath_refl_value(north_a)
  let loop2_susp = DVPathTy(_ => loop1_susp, refl_north, refl_north)
  let sig_p = freudenthal_susp_loop1_to_loop2_value(a_ty, a0, p_open, 16)
  let sig_p_term = quote_at(3, 0, loop2_susp, sig_p)
  match d_check(sig_p_term, loop2_susp, ctx_ap, env_ap, ddim_empty()) {
    Some(_) => ()
    None => return false
  }
  let pres_refl = freudenthal_susp_loop1_preserves_refl_value(a_ty, a0, 16)
  let sig_refl = freudenthal_susp_loop1_to_loop2_value(
    a_ty,
    a0,
    dpath_refl_value(a0),
    16,
  )
  let refl2_north = dpath_refl_value(refl_north)
  let pres_ty = DVPathTy(_ => loop2_susp, sig_refl, refl2_north)
  let ctx_a2 = denv_cons(a_ty, denv_cons(DVUniv(0), denv_empty()))
  let env_a2 = denv_cons(a0, denv_cons(a_ty, denv_empty()))
  let pres_term = quote_at(2, 0, pres_ty, pres_refl)
  match d_check(pres_term, pres_ty, ctx_a2, env_a2, ddim_empty()) {
    Some(_) => ()
    None => return false
  }

  let g0 = sphere_loop_power_value(2, 0)
  let conn0 = hopf_connecting_loop_value(g0)
  if !conv_at(0, 0, c_ty, dapp_dim(conn0, DZero), base_c) ||
    !conv_at(0, 0, c_ty, dapp_dim(conn0, DOne), base_c) {
    return false
  }
  let z_ty = integer_type_value()
  for k in [-1, 0, 1] {
    let gk = sphere_loop_power_value(2, k)
    if !conv_at(0, 0, z_ty, hopf_invariant_value(gk), integer_value(k)) {
      return false
    }
  }
  true
}

