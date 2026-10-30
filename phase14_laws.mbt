///|
/// Phase 14 (`§1.17`) executable law suite covering all 7 boundary items
/// from Section 4 of `SPEC.md` / `SPEC.en.md`.

///|
/// Item 1A: Portable positivity witnesses (`DPositivityWitness`) and
/// independent verification (`dpositivity_witness_verify`).
pub fn check_phase14_positivity_witness_certificates() -> Bool {
  // Unary covariant operator `F(X) = Bool -> (X * Unit)` at variable `DTVar(0)` in scope 1:
  let cov_def = DLam(DUniv(0), DPi(DBoolTy, DSigma(DTVar(0), DUnitTy)))
  let cov_decl = match
    dpositivity_declaration(DTVar(0), 1, strict_args=[0], scope=1) {
    Some(d) => d
    None => return false
  }
  let cov_wit = dpositivity_witness(cov_decl, cov_def)
  if !dpositivity_witness_verify(cov_wit) {
    return false
  }
  // Certified strict positivity check of `F(SelfX)` using `cov_wit`:
  let self_probe = DInductive(dinductive_spec("SelfX", 0, [], [], []), [])
  if !dterm_family_strictly_positive_certified(
      DApp(DTVar(0), self_probe),
      "SelfX",
      [cov_wit],
      scope=1,
    ) {
    return false
  }
  // Tampered witness (claiming `strict_args=[0]` for negative `X -> Bool`) MUST fail
  // both `dpositivity_witness_verify` and `dterm_family_strictly_positive_certified`!
  let neg_def = DLam(DUniv(0), DPi(DTVar(0), DBoolTy))
  let bad_cov_wit = dpositivity_witness(cov_decl, neg_def)
  if dpositivity_witness_verify(bad_cov_wit) ||
    dterm_family_strictly_positive_certified(
      DApp(DTVar(0), self_probe),
      "SelfX",
      [bad_cov_wit],
      scope=1,
    ) {
    return false
  }
  // Binary operator `G(X, Y) = (X -> Bool) -> Y`: arg 1 is strictly positive,
  // arg 0 is at double-negative (merely positive, non-strict) polarity!
  let bin_def = DLam(
    DUniv(0),
    DLam(DUniv(0), DPi(DPi(DTVar(1), DBoolTy), DTVar(0))),
  )
  let bin_decl_good = match
    dpositivity_declaration(
      DTVar(0),
      2,
      strict_args=[1],
      positive_args=[0],
      scope=1,
    ) {
    Some(d) => d
    None => return false
  }
  if !dpositivity_witness_verify(dpositivity_witness(bin_decl_good, bin_def)) {
    return false
  }
  // Falsely claiming arg 0 is STRICTLY positive must be rejected!
  let bin_decl_bad = match
    dpositivity_declaration(DTVar(0), 2, strict_args=[0, 1], scope=1) {
    Some(d) => d
    None => return false
  }
  !dpositivity_witness_verify(dpositivity_witness(bin_decl_bad, bin_def))
}

///|
/// Item 1B: Joint `Σ`-tuple simultaneous inductive-recursive compilation
/// supporting cyclic mutual recursion, `DFunctorSum`, and small/dependent
/// codomains (`simultaneous_ir_compile_joint_block`).
pub fn check_phase14_joint_simultaneous_ir_mutual() -> Bool {
  let idx : Array[DTerm] = []
  let idf = dfunctor_identity(idx)
  // Base inductive with a binary coproduct (`DFunctorSum`) recursive constructor:
  // `zero : Code`, `step : (Code + Code) -> Code`
  let base = dinductive_spec("ParitySumCode", 1, [], [], [
    dconstructor_spec("zero", []),
    dconstructor_spec("step", [darg_nested("branch", dfunctor_sum(idf, idf))]),
  ])
  if !inductive_schema_validate(base) {
    return false
  }
  // Cyclic mutual recursion between two small (`Bool`-valued) functions:
  //   isEven(zero) = true
  //   isEven(step(true, x)) = isOdd(x)     (inl flips parity!)
  //   isEven(step(false, x)) = isEven(x)   (inr preserves parity!)
  //   isOdd(zero) = false
  //   isOdd(step(true, x)) = isEven(x)
  //   isOdd(step(false, x)) = isOdd(x)
  // In `step` case context: `branch` = DTVar(2), `ih_even` = DTVar(1), `ih_odd` = DTVar(0),
  // where `ih_even, ih_odd : DBoolElim(DUniv(1), DBoolTy, DBoolTy, DFst(branch))`.
  let ih_fib0 = DBoolElim(DUniv(1), DBoolTy, DBoolTy, DTVar(0))
  let ih_fib1 = DBoolElim(DUniv(1), DBoolTy, DBoolTy, DTVar(1))
  let step_motive = DPi(ih_fib0, DPi(ih_fib1, DBoolTy))
  let even_step = DApp(
    DApp(
      DBoolElim(
        step_motive,
        DLam(DBoolTy, DLam(DBoolTy, DTVar(0))), // tag == true -> ih_odd
        DLam(DBoolTy, DLam(DBoolTy, DTVar(1))), // tag == false -> ih_even
        DFst(DTVar(2)),
      ),
      DTVar(1),
    ),
    DTVar(0),
  )
  let odd_step = DApp(
    DApp(
      DBoolElim(
        step_motive,
        DLam(DBoolTy, DLam(DBoolTy, DTVar(1))), // tag == true -> ih_even
        DLam(DBoolTy, DLam(DBoolTy, DTVar(0))), // tag == false -> ih_odd
        DFst(DTVar(2)),
      ),
      DTVar(1),
    ),
    DTVar(0),
  )
  let fn_even = dsimultaneous_function("isEven", DBoolTy, [
    DBoolLit(true),
    even_step,
  ])
  let fn_odd = dsimultaneous_function("isOdd", DBoolTy, [
    DBoolLit(false),
    odd_step,
  ])
  let spec = dsimultaneous_ir_spec(base, [fn_even, fn_odd])
  if !simultaneous_ir_validate(spec) {
    return false
  }
  if simultaneous_ir_compile_eliminator(spec, 0) != None {
    return false
  }
  let joint = simultaneous_ir_compile_joint_block(spec)
  let even_term = match joint[0] {
    Some(t) => t
    None => return false
  }
  let odd_term = match joint[1] {
    Some(t) => t
    None => return false
  }
  let expected_ty = match simultaneous_ir_general_eliminator_type(spec, 0) {
    Some(ty) => ty
    None => return false
  }
  if !dep_check_closed(even_term, expected_ty) ||
    !dep_check_closed(odd_term, expected_ty) {
    return false
  }
  let z0 = schema_intro_term(base, 0, [], [])
  let s1 = schema_intro_term(base, 1, [], [DPair(DBoolLit(true), z0)]) // odd
  let s2 = schema_intro_term(base, 1, [], [DPair(DBoolLit(true), s1)]) // even
  let s3 = schema_intro_term(base, 1, [], [DPair(DBoolLit(false), s1)]) // odd
  dep_nf_closed(DApp(even_term, z0), DBoolTy) == Some(DBoolLit(true)) &&
  dep_nf_closed(DApp(odd_term, z0), DBoolTy) == Some(DBoolLit(false)) &&
  dep_nf_closed(DApp(even_term, s1), DBoolTy) == Some(DBoolLit(false)) &&
  dep_nf_closed(DApp(odd_term, s1), DBoolTy) == Some(DBoolLit(true)) &&
  dep_nf_closed(DApp(even_term, s2), DBoolTy) == Some(DBoolLit(true)) &&
  dep_nf_closed(DApp(odd_term, s2), DBoolTy) == Some(DBoolLit(false)) &&
  dep_nf_closed(DApp(even_term, s3), DBoolTy) == Some(DBoolLit(false)) &&
  dep_nf_closed(DApp(odd_term, s3), DBoolTy) == Some(DBoolLit(true))
}

///|
/// Item 2A: Order-independent enumeration of ALL maximum compatible `DSystem`
/// sub-systems (`dsystem_repair_all_maxima`) and general finite closed-inhabitant
/// case-split conversion (`conv_terms_finite_case_split_report`).
pub fn check_phase14_dsystem_all_maxima_and_finite_case_split() -> Bool {
  let line = (_ : Dim) => DVNatTy
  let p1 = (d : Dim) => {
    if dim_eq_sem(d, DZero) {
      dv_nat_lit(0)
    } else {
      dv_nat_lit(1)
    }
  }
  let p2 = (d : Dim) => {
    if dim_eq_sem(d, DZero) {
      dv_nat_lit(0)
    } else {
      dv_nat_lit(2)
    }
  }
  // 4-branch system with two disjoint maximum cliques of size 2:
  // `{i0=0 ↦ p1, i0=1 ↦ p1}` and `{i1=0 ↦ p2, i1=1 ↦ p2}`.
  let sys = DSystem::{
    branches: [
      tube_branch(FEq0(DVar(0)), p1),
      tube_branch(FEq0(DVar(1)), p2),
      tube_branch(FEq1(DVar(0)), p1),
      tube_branch(FEq1(DVar(1)), p2),
    ],
  }
  let all_max = dsystem_repair_all_maxima(0, 2, line, sys, dv_nat_lit(0), [])
  if !all_max.exact ||
    !all_max.all_compatible ||
    all_max.max_branch_count != 2 ||
    all_max.total_maximum_count != 2 ||
    all_max.systems.length() != 2 {
    return false
  }
  let sys_rev = DSystem::{
    branches: [
      sys.branches[3],
      sys.branches[2],
      sys.branches[1],
      sys.branches[0],
    ],
  }
  let all_max_rev = dsystem_repair_all_maxima(
    0,
    2,
    line,
    sys_rev,
    dv_nat_lit(0),
    [],
  )
  if !all_max_rev.exact ||
    all_max_rev.total_maximum_count != 2 ||
    all_max_rev.max_branch_count != 2 {
    return false
  }

  // Finite closed-inhabitant case split over a 3-element inductive `Fin3`:
  let fin3 = dinductive_spec("Fin3", 0, [], [], [
    dconstructor_spec("c0", []),
    dconstructor_spec("c1", []),
    dconstructor_spec("c2", []),
  ])
  let fin3_ty = DInductive(fin3, [])
  let fin3_val : DValue = DVInductive(fin3, [], [])
  match cs_finite_closed_inhabitants(fin3_val) {
    Some(xs) => if xs.length() != 3 { return false }
    None => return false
  }
  if cs_finite_closed_inhabitants(DVNatTy) != None {
    return false
  }
  let n1 = DSucc(DNatZero)
  let n2 = DSucc(n1)
  let lhs = DInductiveElim(
    fin3,
    DLam(fin3_ty, DNatTy),
    [n1, n1, n1],
    [],
    [],
    DTVar(0),
  )
  if conv_terms_plain([fin3_ty], DNatTy, lhs, n1) {
    return false
  }
  let split_ok = conv_terms_finite_case_split_report([fin3_ty], DNatTy, lhs, n1)
  if !split_ok.holds || split_ok.split_nodes != 1 || split_ok.probes != 4 {
    return false
  }
  let lhs_bad = DInductiveElim(
    fin3,
    DLam(fin3_ty, DNatTy),
    [n1, n2, n1],
    [],
    [],
    DTVar(0),
  )
  !conv_terms_finite_case_split_report([fin3_ty], DNatTy, lhs_bad, n1).holds
}

///|
/// Item 2B: Semantic circle winding normalization (`circle_sem_coord_norm`) and
/// decoupled per-coordinate `T^2` torus composition (`comp_torus_value`).
pub fn check_phase14_decoupled_torus_and_semantic_circle_norm() -> Bool {
  // Semantic circle coordinate normalization on primitive `DVCirclePoint(d)`:
  // `DAnd(k, DZero)` simplifies to winding `0` and `DVCirclePoint(k)` has winding `+1`!
  let loop0 = circle_sem_coord_norm(DOne)
  let loop1 = circle_sem_coord_norm(DVar(0))
  if !dim_eq_sem(loop0, DZero) || !dim_eq_sem(loop1, DVar(0)) {
    return false
  }
  // Decoupled `T^2` composition: face `i0 = 0` traverses `(t ∧ i1, 0)` with cap
  // `(i1, 0)` while face `i1 = 0` traverses `(0, t ∧ i0)` with cap `(0, i0)`.
  // At overlap `(i0=0, i1=0)` both equal `(0, 0)`, and the two torus coordinates
  // require distinct face-selection orders!
  let tbase : DValue = DVTorusPoint(DZero, DZero)
  let tline = (_ : Dim) => DVTorusTy
  let br_a = tube_branch(FEq0(DVar(0)), t => {
    torus_point(dim_simplify(DAnd(t, DVar(1))), DZero)
  })
  let br_b = tube_branch(FEq0(DVar(1)), t => {
    torus_point(DZero, dim_simplify(DAnd(t, DVar(0))))
  })
  let branches = dsystem_of([br_a, br_b])
  let res = comp_value(tline, branches, tbase, 2)
  conv_at_under_face(
    0,
    2,
    FEq0(DVar(0)),
    DVTorusTy,
    res,
    torus_point(DVar(1), DZero),
  ) &&
  conv_at_under_face(
    0,
    2,
    FEq0(DVar(1)),
    DVTorusTy,
    res,
    torus_point(DZero, DVar(0)),
  )
}

///|
/// Item 3: Incremental DAG delta (`CHDAGDLT` v1) and unified cross-format
/// shared-DAG module+schema bundle (`CHSHRBUN` v1).
pub fn check_phase14_incremental_dag_delta_and_shared_bundle() -> Bool {
  let table = dterm_intern_table_new()
  let base_term = DPi(DNatTy, DPi(DBoolTy, DSigma(DTVar(1), DTVar(0))))
  ignore(dterm_intern_id(table, base_term))
  let base_count = dterm_intern_table_size(table)
  if base_count < 4 {
    return false
  }
  let base_snap = dterm_intern_table_snapshot(table)
  let dest_table = dterm_intern_table_new()
  if dterm_dag_import(dest_table, base_snap) == None ||
    dterm_intern_table_size(dest_table) != base_count {
    return false
  }
  let derived = DPair(DLam(base_term, DTVar(0)), base_term)
  let delta = match dterm_dag_delta_compute(table, base_count, [derived]) {
    Some(d) => d
    None => return false
  }
  let full_snap = dterm_dag_snapshot(table, [derived])
  if delta.delta_nodes.length() >= full_snap.nodes.length() ||
    delta.delta_nodes.length() == 0 {
    return false
  }
  let delta_bytes = match dterm_dag_delta_to_binary(delta) {
    Some(b) => b
    None => return false
  }
  let imp = match dterm_dag_delta_import_binary(dest_table, delta_bytes) {
    Some(r) => r
    None => return false
  }
  if imp.root_ids.length() != 1 || dest_table.terms[imp.root_ids[0]] != derived {
    return false
  }
  if dterm_dag_delta_import_binary(dterm_intern_table_new(), delta_bytes) !=
    None {
    return false
  }

  let m1 = match module_compile(module_env_new(), bool_ops_module(), []) {
    Some(c) => c
    None => return false
  }
  let reg = schema_registry_new()
  ignore(schema_registry_register_inductive(reg, nat_schema()))
  ignore(schema_registry_register_hit(reg, circle_schema()))
  let reg_snap = schema_registry_snapshot(reg)
  let bundle = SharedDagBundle::{ modules: [m1, m1], registry: reg_snap, }
  let bun_bytes = shared_dag_bundle_to_binary(bundle)
  let load = shared_dag_bundle_load_binary_report(bun_bytes)
  match load.bundle {
    Some(back) =>
      load.status == ModuleBinaryOk &&
      back.modules.length() == 2 &&
      back.modules[0] == m1 &&
      back.registry.inductive_specs.length() == 1 &&
      back.registry.hit_specs.length() == 1 &&
      load.reused_dag_nodes > 0
    None => false
  }
}

///|
/// Item 4A: Berlekamp–Zassenhaus `p`-adic Hensel lifting factorization over
/// `Q[x]` and portable `QPolyFactorCertificate` verification.
pub fn check_phase14_qpoly_hensel_factor_and_certificates() -> Bool {
  check_qpoly_hensel_factor_and_certificates()
}

///|
/// Item 4B: General `n`-th real algebraic radicals (`RealAlgRadical`) and
/// rank-6 (64-dimensional) multiquadratic towers.
pub fn check_phase14_algebraic_radicals_and_rank6_multiquad() -> Bool {
  check_algebraic_radicals_and_rank6_multiquad()
}

///|
/// Item 4C: Hermitian Jacobi block deflation (`jacobi_block_deflated_eigen`)
/// and exact higher-multiplicity certification (`jacobi_block_deflated_certified`).
pub fn check_phase14_jacobi_block_deflation_and_multiplicity() -> Bool {
  check_jacobi_block_deflation_and_multiplicity()
}

///|
/// Item 5A: Branch-and-bound lower-bound pruned BDD variable ordering beyond
/// `n = 16` (`bdd_dag_of_face_optimal_pruned`) and CDCL `DRAT` checking +
/// backward `DRUP` trimming (`face_cdcl_drat_check`, `face_cdcl_drup_trim`).
pub fn check_phase14_bdd_bnb_and_cdcl_drat() -> Bool {
  // 1. Interleaved 18-variable face (`n = 18 > 16`): natural order `[0..17]`
  // explodes to > 500 nodes while `bdd_dag_of_face_optimal_pruned` compresses it!
  let mut f18 : Face = FBot
  for i in 0..<9 {
    f18 = FOr(f18, FAnd(FEq1(DVar(i)), FEq1(DVar(i + 9))))
  }
  let unopt_18 = bdd_dag_of_face(f18, 18)
  let unopt_size = bdd_dag_reachable_count(unopt_18.manager, unopt_18.root)
  let opt_18 = bdd_dag_of_face_optimal_pruned(f18, 18)
  if opt_18.active_vars != 18 || opt_18.size >= unopt_size || opt_18.size > 30 {
    return false
  }
  let mut f6 : Face = FBot
  for i in 0..<3 {
    f6 = FOr(f6, FAnd(FEq1(DVar(i)), FEq1(DVar(i + 3))))
  }
  let exact6 = bdd_dag_of_face_optimal(f6, 6)
  let bnb6 = bdd_dag_of_face_optimal_pruned(f6, 6)
  if !bnb6.exact || bnb6.size != exact6.size || bnb6.pruned_subsets <= 0 {
    return false
  }

  // 2. Genuine RAT (non-RUP) symmetry-breaking step on all 8 3-clauses of `{1,2,3}`:
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
  let drat_steps = [CdclProofAdd([1]), CdclProofAdd([2]), CdclProofAdd([])]
  // `[1]` is NOT RUP (since every clause has width 3), so `face_cdcl_drup_check`
  // MUST reject `drat_steps`, while `face_cdcl_drat_check` accepts it via RAT!
  if face_cdcl_drup_check(oct3, drat_steps) ||
    !face_cdcl_drat_check(oct3, drat_steps) {
    return false
  }
  // Unsound non-RAT step `[1]` on `[[1, 2], [-1, 3], [-1, -3]]` MUST fail DRAT!
  if face_cdcl_drat_check([[1, 2], [-1, 3], [-1, -3]], [
      CdclProofAdd([1]),
      CdclProofAdd([]),
    ]) {
    return false
  }
  // Backward DRUP trimming removes unused redundant learned clauses:
  let noisy_rup = [
    CdclProofAdd([1, 2]),
    CdclProofAdd([1, -2]),
    CdclProofAdd([1]),
    CdclProofAdd([]),
  ]
  let base_unsat = [[1, 2], [1, -2], [-1, 2], [-1, -2]]
  let trim_rep = face_cdcl_drup_trim(base_unsat, noisy_rup)
  trim_rep.valid &&
  trim_rep.trimmed_steps < trim_rep.original_steps &&
  face_cdcl_drup_check(base_unsat, trim_rep.steps)
}

///|
/// Item 5B: Projective-line `P^1(F_8)` strength-3 covering-array probing for
/// high-dimensional host cubes (`dcube_cubes_conv_covering_report`).
pub fn check_phase14_dcube_orthogonal_array_covering() -> Bool {
  let zero : DValue = DVZeroNat
  let one : DValue = DVSucc(DVZeroNat)
  let c0 = dcube_constant(5, zero)
  // 5D cube differing ONLY on a simultaneous 3-axis interaction `(0, 2, 4)`
  // over `dcube_deep_axis_pool` (`ambient_dlevel = 0, n = 5` -> `shared_s = i0, shared_t = i5`)!
  let sneaky5 = dcube_function(5, dims => {
    let hit0 = dims[0] == DOr(DVar(0), DNeg(DVar(5)))
    let hit2 = dims[2] == DNeg(DAnd(DVar(2), DVar(5)))
    let hit4 = dims[4] == DAnd(DVar(4), DVar(0))
    if hit0 && hit2 && hit4 {
      one
    } else {
      zero
    }
  })
  let diff_rep = dcube_cubes_conv_covering_report(
    0,
    0,
    DVNatTy,
    c0,
    sneaky5,
    strength=3,
  )
  if diff_rep.equal {
    return false
  }
  let eq_rep = dcube_cubes_conv_covering_report(
    0,
    0,
    DVNatTy,
    c0,
    c0,
    strength=3,
  )
  eq_rep.equal &&
  eq_rep.complete_for_strength &&
  eq_rep.interaction_strength == 3 &&
  eq_rep.probes > 0
}

///|
/// Item 6A: Eckmann–Hilton commutativity 3-cell on `Omega^2(S^2)` and Mac Lane
/// pentagon 4-cell coherence on composable paths.
pub fn check_phase14_eckmann_hilton_and_pentagon_coherence() -> Bool {
  let s2 = sphere_type_value(2)
  let north = sphere_north_value(2)
  let om1_ty = loop_space_type_value(s2, north, 1)
  let om2_ty = loop_space_type_value(s2, north, 2)
  let refl1 = iterated_refl_value(north, 1)
  let alpha = sphere_loop_power_value(2, 1)
  let beta = sphere_loop_power_value(2, -1)
  let eh = dpath_eckmann_hilton3_value(s2, north, alpha, beta, 4)
  let ab = dpath_trans_value(om1_ty, alpha, beta, 4)
  let ba = dpath_trans_value(om1_ty, beta, alpha, 4)
  if !conv_at(0, 0, om2_ty, dapp_dim(eh, DZero), ab) {
    return false
  }
  if !conv_at(0, 0, om2_ty, dapp_dim(eh, DOne), ba) {
    return false
  }
  let eh_mid = dapp_dim(eh, DVar(0))
  if !conv_at(0, 1, om1_ty, dapp_dim(eh_mid, DZero), refl1) ||
    !conv_at(0, 1, om1_ty, dapp_dim(eh_mid, DOne), refl1) {
    return false
  }

  let s1 = circle_hit_type_value()
  let b = circle_hit_base_value()
  let lp = circle_hit_loop_path_value()
  let lpi = dpath_sym_value(lp)
  let top3 = dpath_pentagon_top3_value(s1, b, lp, lpi, lp, lp, 2)
  let bot3 = dpath_pentagon_bot3_value(s1, b, lp, lpi, lp, lp, 2)
  let pent4 = dpath_pentagon4_value(s1, b, lp, lpi, lp, lp, 2)
  let pq = dpath_trans_value(s1, lp, lpi, 2)
  let pqr = dpath_trans_value(s1, pq, lp, 2)
  let lhs = dpath_trans_value(s1, pqr, lp, 2)
  let rs = dpath_trans_value(s1, lp, lp, 2)
  let qrs = dpath_trans_value(s1, lpi, rs, 2)
  let rhs = dpath_trans_value(s1, lp, qrs, 2)
  let assoc_ty : DValue = DVPathTy(_ => DVPathTy(_ => s1, b, b), lhs, rhs)
  let p4_0 = conv_at(0, 0, assoc_ty, dapp_dim(pent4, DZero), top3)
  let p4_1 = conv_at(0, 0, assoc_ty, dapp_dim(pent4, DOne), bot3)
  p4_0 && p4_1
}

///|
/// Item 6B: Internal `(n : IntegerS) -> encode(decode(n)) = n` section family
/// (including symbolic neutral `n`) and Brunerie's univalent Hopf fibration
/// `Hopf : S^2 -> Type_0` + synthetic Hopf invariant `Omega^2(S^2) -> IntegerS`.
pub fn check_phase14_internal_circle_sect_and_hopf_invariant() -> Bool {
  let z = integer_type_value()
  for k in [-2, -1, 0, 1, 2] {
    let nk = integer_value(k)
    let sect_k = circle_encode_decode_sect_value(nk, 2)
    let lhs_k = circle_encode_value(circle_decode_value(nk, 2), 2)
    if !conv_at(0, 0, z, dapp_dim(sect_k, DZero), lhs_k) ||
      !conv_at(0, 0, z, dapp_dim(sect_k, DOne), nk) {
      return false
    }
  }
  let sym_n : DValue = DVNeutral(DNVar(0))
  let sect_sym = circle_encode_decode_sect_value(sym_n, 2)
  let sym_lhs = circle_encode_value(circle_decode_value(sym_n, 2), 2)
  let s0 = conv_at(1, 0, z, dapp_dim(sect_sym, DZero), sym_lhs)
  let s1_ok = conv_at(1, 0, z, dapp_dim(sect_sym, DOne), sym_n)
  if !s0 || !s1_ok {
    return false
  }

  let s1 = circle_hit_type_value()
  if !conv_at(0, 0, DVUniv(0), hopf_family_value(sphere2_north_value()), s1) {
    return false
  }
  let g0 = sphere_loop_power_value(2, 0)
  let g1 = sphere_loop_power_value(2, 1)
  let gm1 = sphere_loop_power_value(2, -1)
  let g2 = sphere_loop_power_value(2, 2)
  let h0 = hopf_invariant_value(g0)
  let h1 = hopf_invariant_value(g1)
  let hm1 = hopf_invariant_value(gm1)
  let h2 = hopf_invariant_value(g2)
  let pos_orient = conv_at(0, 0, z, h1, integer_value(1)) &&
    conv_at(0, 0, z, hm1, integer_value(-1)) &&
    conv_at(0, 0, z, h2, integer_value(2))
  let neg_orient = conv_at(0, 0, z, h1, integer_value(-1)) &&
    conv_at(0, 0, z, hm1, integer_value(1)) &&
    conv_at(0, 0, z, h2, integer_value(-2))
  conv_at(0, 0, z, h0, integer_value(0)) && (pos_orient || neg_orient)
}

///|
/// Item 7A: Cross-constraint Huet backtracking (`hou_solve_constraints_backtracking`)
/// and bounded complete normal-form unifier enumeration (`hou_enumerate_unifiers`).
pub fn check_phase14_hou_backtracking_and_enumeration() -> Bool {
  let ca = UApp(UConst("c"), UConst("a"))
  let cb = UApp(UConst("c"), UConst("b"))
  let eq1 = HouConstraint::{ lhs: UMeta(0, [ca, ca]), rhs: ca, depth: 0, }
  let eq2 = HouConstraint::{ lhs: UMeta(0, [ca, cb]), rhs: cb, depth: 0, }

  let u_old = unifier_new()
  ignore(hou_fresh_meta(u_old, 0))
  if hou_solve_constraints([eq1, eq2], u_old).status == HouSolved {
    return false
  }

  let u_bt = unifier_new()
  ignore(hou_fresh_meta(u_bt, 0))
  let rep_bt = hou_solve_constraints_backtracking(
    [eq1, eq2],
    u_bt,
    max_projection_args=0,
  )
  if rep_bt.status != HouSolved ||
    hou_semantic_optimize(UMeta(0, [ca, cb]), u_bt) != cb ||
    hou_semantic_optimize(UMeta(0, [cb, ca]), u_bt) != ca {
    return false
  }

  let u_enum = unifier_new()
  ignore(hou_fresh_meta(u_enum, 0))
  let enum_rep = hou_enumerate_unifiers(
    [eq1],
    u_enum,
    max_depth=2,
    max_projection_args=0,
  )
  if !enum_rep.search_exhausted || enum_rep.solutions.length() < 3 {
    return false
  }

  let u_unsat = unifier_new()
  ignore(hou_fresh_meta(u_unsat, 0))
  let bad1 = HouConstraint::{ lhs: UMeta(0, [ca]), rhs: ca, depth: 0, }
  let bad2 = HouConstraint::{ lhs: UMeta(0, [ca]), rhs: cb, depth: 0, }
  let unsat_enum = hou_enumerate_unifiers(
    [bad1, bad2],
    u_unsat,
    max_depth=2,
    max_projection_args=0,
  )
  unsat_enum.search_exhausted && unsat_enum.solutions.length() == 0
}

///|
/// Item 7B: Forward-compatible TLV module envelope (`CHMODENV` v1), keyed-MAC
/// optimistic CAS commits (`artifact_repository_put_cas_authenticated`), and
/// producer-attested incremental sync (`artifact_repository_sync_incremental`).
pub fn check_phase14_tlv_envelope_cas_and_incremental_sync() -> Bool {
  let cm = match module_compile(module_env_new(), bool_ops_module(), []) {
    Some(m) => m
    None => return false
  }
  let sec_known = ModuleTlvSection::{
    tag: 10,
    critical: false,
    payload: [1, 2, 3],
  }
  let sec_opt = ModuleTlvSection::{ tag: 99, critical: false, payload: [4, 5], }
  let env_ok_bytes = match
    compiled_module_envelope_to_binary(cm, [sec_known, sec_opt]) {
    Some(b) => b
    None => return false
  }
  let env_loaded = compiled_module_envelope_load_binary(env_ok_bytes, [10])
  if env_loaded.status != ModuleBinaryOk ||
    env_loaded.module_ != Some(cm) ||
    env_loaded.recognized_sections != [sec_known] ||
    env_loaded.skipped_noncritical_tags != [99] {
    return false
  }
  let sec_crit = ModuleTlvSection::{ tag: 77, critical: true, payload: [9], }
  let env_crit_bytes = match
    compiled_module_envelope_to_binary(cm, [sec_crit]) {
    Some(b) => b
    None => return false
  }
  if compiled_module_envelope_load_binary(env_crit_bytes, [10]).status !=
    ModuleBinaryUnsupportedVersion {
    return false
  }

  let key = ArtifactAuthKey::{
    key_id: "build-cluster-k1",
    secret_a: 0x13579bdf,
    secret_b: 0x2468ace0,
  }
  let wrong_key = ArtifactAuthKey::{
    key_id: "build-cluster-k1",
    secret_a: 0x13579bde,
    secret_b: 0x2468ace0,
  }
  let src_store = artifact_memory_byte_store_new()
  let src = artifact_repository_new(src_store)
  let mod_bytes = compiled_module_to_binary(cm)
  if artifact_repository_put_cas_authenticated(
      src,
      "compiled-module",
      "BoolOps",
      mod_bytes,
      3,
      (0, 0),
      key,
    ) !=
    ArtifactCasCommitted {
    return false
  }
  let head1 = match artifact_repository_chain_head(src) {
    Some(h) => h
    None => return false
  }
  if artifact_repository_put_cas_authenticated(
      src,
      "docs",
      "stale",
      [1, 2],
      1,
      (0, 0),
      key,
    ) !=
    ArtifactCasConflict {
    return false
  }
  if artifact_repository_verify_authenticated(src, wrong_key) ||
    artifact_repository_put_cas_authenticated(
      src,
      "docs",
      "badkey",
      [1],
      1,
      head1,
      wrong_key,
    ) !=
    ArtifactCasAuthFailed {
    return false
  }
  if artifact_repository_put_cas_authenticated(
      src,
      "docs",
      "temp",
      [7, 8, 9],
      1,
      head1,
      key,
    ) !=
    ArtifactCasCommitted {
    return false
  }
  let tgt_store = artifact_memory_byte_store_new()
  let tgt = artifact_repository_new(tgt_store)
  let sync1 = artifact_repository_sync_incremental(src, tgt, key, trusted_producers=[
    compiled_module_producer_default(),
  ])
  if !sync1.ok ||
    sync1.transferred_blobs != 2 ||
    sync1.skipped_existing_blobs != 0 {
    return false
  }
  let untrusted_tgt = artifact_repository_new(artifact_memory_byte_store_new())
  if artifact_repository_sync_incremental(src, untrusted_tgt, key, trusted_producers=[
      "other-untrusted-compiler",
    ]).ok {
    return false
  }
  if !artifact_repository_remove(src, "docs", "temp") ||
    !artifact_repository_seal_authenticated(src, key) {
    return false
  }
  let head3 = match artifact_repository_chain_head(src) {
    Some(h) => h
    None => return false
  }
  if artifact_repository_put_cas_authenticated(
      src,
      "docs",
      "final",
      [42, 43],
      1,
      head3,
      key,
    ) !=
    ArtifactCasCommitted {
    return false
  }
  let sync2 = artifact_repository_sync_incremental(src, tgt, key, trusted_producers=[
    compiled_module_producer_default(),
  ])
  sync2.ok &&
  sync2.skipped_existing_blobs == 1 &&
  sync2.transferred_blobs == 1 &&
  sync2.tombstones_applied == 1 &&
  artifact_repository_verify_authenticated(tgt, key) &&
  artifact_repository_get(tgt, "docs", "temp") == None &&
  artifact_repository_get(tgt, "docs", "final") == Some([42, 43])
}
