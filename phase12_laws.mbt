// ---------------------------------------------------------------------------
// Phase 12 law checks backing the theorem registry.
// ---------------------------------------------------------------------------

///|
fn phase12_pair_face(n : Int32) -> Face {
  let half = n / 2
  let mut out = FAnd(FEq1(DVar(0)), FEq1(DVar(half)))
  for i in 1..<half {
    out = FOr(out, FAnd(FEq1(DVar(i)), FEq1(DVar(i + half))))
  }
  out
}

///|
fn phase12_bdd_semantics_ok(f : Face, built : BddDagFace, n : Int32) -> Bool {
  for mask in 0..<(1 << n) {
    let env : Array[Bool] = []
    for i in 0..<n {
      let bit = (mask >> i) & 1
      env.push(bit == 1)
    }
    if bdd_dag_eval(built.manager, built.root, env) != face_holds(f, env) {
      return false
    }
  }
  true
}

///|
/// Subset-DP optimal BDD ordering agrees with factorial search on
/// small cases, remains exact at ten variables without trying all
/// permutations, and reports its cap honestly.
pub fn check_bdd_optimal_order_dp() -> Bool {
  for n in [2, 4, 6] {
    let f = phase12_pair_face(n)
    let brute = bdd_dag_of_face_optimal(f, n)
    let dp = bdd_dag_of_face_optimal_dp(f, n)
    if !dp.exact {
      return false
    }
    if dp.size != brute.size {
      return false
    }
    if !phase12_bdd_semantics_ok(f, dp.built, n) {
      return false
    }
  }
  let mixed = FOr(
    FAnd(FEq1(DVar(0)), FEq0(DVar(1))),
    FAnd(FEq1(DVar(1)), FOr(FEq0(DVar(2)), FEq1(DVar(3)))),
  )
  let brute = bdd_dag_of_face_optimal(mixed, 4)
  let dp = bdd_dag_of_face_optimal_dp(mixed, 4)
  if dp.size != brute.size {
    return false
  }
  let f10 = phase12_pair_face(10)
  let dp10 = bdd_dag_of_face_optimal(f10, 10, exact_max_vars=10)
  if !dp10.exact {
    return false
  }
  if dp10.tried != 5120 {
    return false
  }
  if !phase12_bdd_semantics_ok(f10, dp10.built, 10) {
    return false
  }
  let over_cap = bdd_dag_of_face_optimal_dp(FTop, 17)
  if over_cap.exact {
    return false
  }
  true
}

///|
/// CDCL UNSAT results carry RUP-checkable proofs; learned-clause
/// database reduction engages on a larger pigeonhole instance
/// without changing the recorded proof semantics.
pub fn check_cdcl_proof_and_reduction() -> Bool {
  if !face_cdcl_proof_check([[1], [-1]], [[]]) {
    return false
  }
  if face_cdcl_proof_check([[-1]], [[]]) {
    return false
  }
  let (php, pvars) = phase11_pigeonhole_face(6, 5)
  let result = face_sat_cdcl_proof(php, pvars, max_steps=2000000)
  if result.decision != FaceUnsat {
    return false
  }
  if result.stats.learned <= 0 {
    return false
  }
  if result.proof_clauses.length() != result.stats.learned + 1 {
    return false
  }
  if !face_cdcl_proof_check(result.original_clauses, result.proof_clauses) {
    return false
  }
  // Removing the final empty clause, or inserting a clause that
  // is not a RUP consequence, must invalidate the audit.
  let truncated : Array[Array[Int32]] = []
  for i in 0..<(result.proof_clauses.length() - 1) {
    truncated.push(result.proof_clauses[i])
  }
  if face_cdcl_proof_check(result.original_clauses, truncated) {
    return false
  }
  let bogus : Array[Array[Int32]] = []
  for i in 0..<result.proof_clauses.length() {
    bogus.push(result.proof_clauses[i])
    if i == 0 {
      bogus.push([1000000])
    }
  }
  if face_cdcl_proof_check(result.original_clauses, bogus) {
    return false
  }
  // SAT runs return no UNSAT proof.
  let (php_sat, svars) = phase11_pigeonhole_face(5, 5)
  let sat_result = face_sat_cdcl_proof(php_sat, svars, max_steps=2000000)
  match sat_result.decision {
    FaceSat(_) => ()
    _ => return false
  }
  if sat_result.proof_clauses.length() != 0 {
    return false
  }
  // Database reduction triggers on PHP(7,6); checking only the
  // report here keeps this acceptance from paying for a second
  // full proof audit on the larger instance.
  let (php76, vars76) = phase11_pigeonhole_face(7, 6)
  let report = face_sat_cdcl_report(php76, vars76, max_steps=5000000)
  if report.decision != FaceUnsat {
    return false
  }
  report.stats.deleted > 0
}

///|
fn phase12_shape_host(name : String, inner : DInductiveSpec) -> DInductiveSpec {
  dinductive_spec(name, 0, [], [], [
    dconstructor_spec("base", []),
    dconstructor_spec("node", [
      darg_nested(
        "stored",
        dfunctor_family(inner, params=[dfunctor_param_self()]),
      ),
    ]),
  ])
}

///|
/// Same-spec self-family recursion (Bush), parameter shapes
/// traversable by the IH gatherer (lists and dependent pairs of
/// stored elements), and precise validation of parameter terms
/// depending on a `Self` parameter.
pub fn check_self_family_and_gather_shapes() -> Bool {
  // --- Bush: `Bush A` storing a `Bush (Bush A)` tail.
  let bush = dinductive_spec(
    "BushS",
    0,
    [dtelescope_entry("A", DUniv(0))],
    [],
    [
      dconstructor_spec("nil", []),
      dconstructor_spec("cons", [
        darg_external("head", DTVar(0)),
        darg_nested(
          "tail",
          dfunctor_self_family(params=[dfunctor_param_self()]),
        ),
      ]),
    ],
  )
  if !inductive_schema_validate(bush) {
    return false
  }
  let registry = schema_registry_new()
  ignore(schema_registry_register_inductive(registry, bush))
  if !schema_registry_binary_roundtrip_ok(registry) {
    return false
  }
  let b0 : DValue = DVInductive(bush, [DVBoolTy], [])
  let b1 : DValue = DVInductive(bush, [b0], [])
  if !conv_ty(
      0,
      0,
      inductive_arg_type(bush, bush.constructors[1].args[1], [DVBoolTy], [
        DVBool(true),
      ]),
      b1,
    ) {
    return false
  }
  let nil1 : DValue = DVIntro(bush, 0, [b0], [])
  let nil2 : DValue = DVIntro(bush, 0, [b1], [])
  let headbush : DValue = DVIntro(bush, 1, [DVBoolTy], [DVBool(false), nil1])
  let tail : DValue = DVIntro(bush, 1, [b0], [headbush, nil2])
  let tree : DValue = DVIntro(bush, 1, [DVBoolTy], [DVBool(true), tail])
  let leaf_count = eval_inductive_elim(
    bush,
    (_, _) => DVNatTy,
    [
      dv_nat_lit(0),
      DVLam(_ => {
        DVLam(_ => {
          DVLam(bundle => {
            dv_nat_plus(dv_nat_lit(1), dv_sum_bundle_leaves(bundle))
          })
        })
      }),
    ],
    [DVBoolTy],
    [],
    tree,
    0,
  )
  if !dv_is_nat(leaf_count, 2) {
    return false
  }
  // A parameter used in a function domain cannot be the target
  // of a `Self` self-family argument.
  let bad_self = dinductive_spec(
    "BadSelfBushS",
    0,
    [dtelescope_entry("A", DUniv(0))],
    [],
    [
      dconstructor_spec("mk", [
        darg_nested("fnarg", dfunctor_pi(DTVar(0), dfunctor_identity([]))),
        darg_nested(
          "tail",
          dfunctor_self_family(params=[dfunctor_param_self()]),
        ),
      ]),
    ],
  )
  if inductive_schema_validate(bad_self) {
    return false
  }
  // --- Gather through List and Sigma parameter shapes.
  let many = dinductive_spec(
    "ManyStoreS",
    0,
    [dtelescope_entry("A", DUniv(0))],
    [],
    [dconstructor_spec("wrap", [darg_external("items", DListTy(DTVar(0)))])],
  )
  let many_host = phase12_shape_host("ManyHostS", many)
  if !inductive_schema_validate(many_host) {
    return false
  }
  let count_cases : Array[DValue] = [
    dv_nat_lit(1),
    DVLam(_ => {
      DVLam(bundle => dv_nat_plus(dv_nat_lit(1), dv_sum_bundle_leaves(bundle)))
    }),
  ]
  let many_ty : DValue = DVInductive(many_host, [], [])
  let many_base : DValue = DVIntro(many_host, 0, [], [])
  let many_node : DValue = DVIntro(many_host, 1, [], [
    DVIntro(many, 0, [many_ty], [DVCons(many_base, DVCons(many_base, DVNil))]),
  ])
  if !dv_is_nat(
      eval_inductive_elim(
        many_host,
        (_, _) => DVNatTy,
        count_cases,
        [],
        [],
        many_node,
        0,
      ),
      3,
    ) {
    return false
  }
  let pair_inner = dinductive_spec(
    "PairStoreS",
    0,
    [dtelescope_entry("A", DUniv(0))],
    [],
    [
      dconstructor_spec("wrap", [
        darg_external("pair", DSigma(DTVar(0), DTVar(1))),
      ]),
    ],
  )
  let pair_host = phase12_shape_host("PairHostS", pair_inner)
  if !inductive_schema_validate(pair_host) {
    return false
  }
  let pair_ty : DValue = DVInductive(pair_host, [], [])
  let pair_base : DValue = DVIntro(pair_host, 0, [], [])
  let pair_node : DValue = DVIntro(pair_host, 1, [], [
    DVIntro(pair_inner, 0, [pair_ty], [DVPair(pair_base, pair_base)]),
  ])
  if !dv_is_nat(
      eval_inductive_elim(
        pair_host,
        (_, _) => DVNatTy,
        count_cases,
        [],
        [],
        pair_node,
        0,
      ),
      3,
    ) {
    return false
  }
  // --- A later family parameter whose type is an earlier
  // `Self` parameter is checked at the real host type.
  let dep_inner = dinductive_spec(
    "DepStoreS",
    0,
    [dtelescope_entry("A", DUniv(0)), dtelescope_entry("x", DTVar(0))],
    [],
    [
      dconstructor_spec("empty", []),
      dconstructor_spec("stored", [darg_external("elt", DTVar(1))]),
    ],
  )
  let dep_host = dinductive_spec("DepHostS", 0, [], [], [
    dconstructor_spec("base", []),
    dconstructor_spec("node", [
      darg_recursive("seed"),
      darg_nested(
        "stored",
        dfunctor_family(dep_inner, params=[
          dfunctor_param_self(),
          dfunctor_param_term(DTVar(0)),
        ]),
      ),
    ]),
  ])
  if !inductive_schema_validate(dep_host) {
    return false
  }
  let dep_host_wrong = dinductive_spec("DepHostWrongS", 0, [], [], [
    dconstructor_spec("base", []),
    dconstructor_spec("node", [
      darg_recursive("seed"),
      darg_nested(
        "stored",
        dfunctor_family(dep_inner, params=[
          dfunctor_param_self(),
          dfunctor_param_term(DUnitLit),
        ]),
      ),
    ]),
  ])
  if inductive_schema_validate(dep_host_wrong) {
    return false
  }
  let dep_ty : DValue = DVInductive(dep_host, [], [])
  let dep_base : DValue = DVIntro(dep_host, 0, [], [])
  let dep_node : DValue = DVIntro(dep_host, 1, [], [
    dep_base,
    DVIntro(dep_inner, 1, [dep_ty, dep_base], [dep_base]),
  ])
  let dep_count = eval_inductive_elim(
    dep_host,
    (_, _) => DVNatTy,
    [
      dv_nat_lit(1),
      DVLam(_ => {
        DVLam(seed_ih => {
          DVLam(_ => {
            DVLam(bundle => {
              dv_nat_plus(
                dv_nat_lit(1),
                dv_nat_plus(seed_ih, dv_sum_bundle_leaves(bundle)),
              )
            })
          })
        })
      }),
    ],
    [],
    [],
    dep_node,
    0,
  )
  dv_is_nat(dep_count, 3)
}

///|
/// The certified Miller-pattern unifier returns principal
/// substitutions (including flex-flex intersection and same-head
/// pruning), explicit residuals under a principal partial
/// substitution for non-pattern spines, and transactional
/// no-unifier verdicts.
pub fn check_hou_pattern_mgu_and_residuals() -> Bool {
  let u = unifier_new()
  let f = hou_fresh_meta(u, 2)
  let rhs = UPair(UVar(0), UConst("c"))
  let report = hou_unify_mgu(f, rhs, 2, u)
  if report.status != HouMguPrincipal || report.substitution.length() != 1 {
    return false
  }
  if hou_semantic_optimize(f, u) != rhs {
    return false
  }
  // Flex-flex intersection over the shared spine variable.
  let u2 = unifier_new()
  ignore(hou_fresh_meta(u2, 0))
  ignore(hou_fresh_meta(u2, 0))
  let flex = hou_unify_mgu(
    UMeta(0, [UVar(2), UVar(1)]),
    UMeta(1, [UVar(1), UVar(0)]),
    3,
    u2,
  )
  if flex.status != HouMguPrincipal {
    return false
  }
  if hou_semantic_optimize(UMeta(0, [UVar(2), UVar(1)]), u2) !=
    hou_semantic_optimize(UMeta(1, [UVar(1), UVar(0)]), u2) {
    return false
  }
  // Same-head pruning: swapped spines share no fixed position.
  let u3 = unifier_new()
  ignore(hou_fresh_meta(u3, 0))
  let same = hou_unify_mgu(
    UMeta(0, [UVar(1), UVar(0)]),
    UMeta(0, [UVar(0), UVar(1)]),
    2,
    u3,
  )
  if same.status != HouMguPrincipal {
    return false
  }
  if hou_semantic_optimize(UMeta(0, [UVar(1), UVar(0)]), u3) !=
    hou_semantic_optimize(UMeta(0, [UVar(0), UVar(1)]), u3) {
    return false
  }
  // A repeated-variable spine has no single MGU; the pattern
  // component still solves principally and the repeated
  // component comes back as the residual, whose subsequent
  // (specific) solution completes the original problem.
  let u4 = unifier_new()
  ignore(hou_fresh_meta(u4, 0))
  ignore(hou_fresh_meta(u4, 0))
  let original_lhs = UPair(UMeta(0, [UVar(0)]), UMeta(1, [UVar(0), UVar(0)]))
  let original_rhs = UPair(UConst("c"), UPair(UVar(0), UConst("c")))
  let partial = hou_unify_mgu(original_lhs, original_rhs, 1, u4)
  if partial.status != HouMguResidual ||
    partial.residual.length() != 1 ||
    partial.substitution.length() != 1 {
    return false
  }
  let residual = partial.residual[0]
  if !hou_unify(residual.lhs, residual.rhs, residual.depth, u4) {
    return false
  }
  if hou_semantic_optimize(original_lhs, u4) !=
    hou_semantic_optimize(original_rhs, u4) {
    return false
  }
  // Definitive failures restore the unifier.
  let u5 = unifier_new()
  ignore(hou_fresh_meta(u5, 0))
  let scope = hou_unify_mgu(UMeta(0, [UVar(1)]), UVar(0), 2, u5)
  if scope.status != HouMguNoUnifier || u5.solved_count != 0 {
    return false
  }
  let clash = hou_unify_mgu(
    UPair(UConst("a"), UConst("b")),
    USucc(UNatZero),
    0,
    u5,
  )
  clash.status == HouMguNoUnifier
}

///|
/// Agreement walks split only on dimensions occurring in the
/// quoted terms, and repair can supplement a system from a
/// candidate pool under the full compatibility audit.
pub fn check_dsystem_structural_agreement_and_supplementation() -> Bool {
  if dterm_dim_vars(DAppDim(DCircleLoop, DAnd(DVar(3), DNeg(DVar(1))))) !=
    [1, 3] {
    return false
  }
  let var_bdd = bdd_of_face(FAnd(FEq1(DVar(0)), FEq0(DVar(1))), 2)
  if bdd_tree_cofactor(var_bdd, 0, true) != BddNode(1, BddOne, BddZero) {
    return false
  }
  if bdd_tree_cofactor(var_bdd, 0, false) != BddZero {
    return false
  }
  // The same endpoint agreement as the Phase 11 law, now in a
  // twelve-dimensional ambient context whose extra dimensions
  // occur nowhere in the values: the walk splits only on the
  // one relevant dimension.
  let a = circle_point(DVar(0))
  let b = DVCirclePoint(DZero)
  let agreement = face_agreement_face(0, 12, FTop, DVCircleTy, a, b)
  if agreement == FTop || agreement == FBot {
    return false
  }
  if !face_holds(agreement, [false]) || !face_holds(agreement, [true]) {
    return false
  }
  let region = face_agreement_region(0, 12, FTop, DVCircleTy, a, b)
  if region != BddNode(0, BddOne, BddZero) {
    return false
  }
  // Supplementation: one original branch is dropped, one is
  // kept, one candidate fills the other endpoint face, and two
  // candidates are rejected (base disagreement and pairwise
  // incompatibility respectively).
  let line = (_ : Dim) => DVNatTy
  let zero_path = (_ : Dim) => DVZeroNat
  let system = dsystem_of([
    tube_branch(FTop, _ => dv_nat_lit(1)),
    tube_branch(FEq0(DVar(0)), zero_path),
  ])
  let candidates : Array[DTubeBranch] = [
    tube_branch(FEq1(DVar(0)), zero_path),
    tube_branch(FTop, _ => dv_nat_lit(1)),
    tube_branch(FEq1(DVar(0)), j => {
      if dim_is_zero(j) {
        DVZeroNat
      } else {
        dv_nat_lit(1)
      }
    }),
  ]
  let repaired = dsystem_repair_with_candidates(
    0,
    1,
    line,
    system,
    DVZeroNat,
    candidates,
  )
  if !repaired.compatible {
    return false
  }
  if repaired.system.branches.length() != 2 {
    return false
  }
  if repaired.added_branches != 1 || repaired.rejected_candidates != 2 {
    return false
  }
  if repaired.repaired_branches < 1 {
    return false
  }
  dsystem_compatible_with_base(0, 1, line, repaired.system, DVZeroNat)
}

///|
/// Phase 12: shared DAG term codec, version negotiation, and
/// the durable artifact repository.  A registry snapshot whose
/// constructors repeat one large external type is strictly
/// smaller under the v3-codec registry layout than under the
/// v2-codec layout, and both parse back exactly.  A module with
/// a tag-8 family functor negotiates to v2 for a v1+v2 peer, is
/// refused for a v1-only peer, and uses v3 for a v3 peer.  The
/// repository round-trips a compiled module and a registry
/// snapshot, refuses a corrupted blob, repairs it on re-put,
/// and rebuilds a destroyed index from commit manifests.
pub fn check_artifact_repository_and_dag_codec() -> Bool {
  if compiled_module_binary_version_policy() !=
    BinaryVersionPolicy::{
      current: 3,
      supported: [1, 2, 3],
      oldest_writable: 1,
    } ||
    schema_registry_binary_version_policy() !=
    BinaryVersionPolicy::{ current: 2, supported: [1, 2], oldest_writable: 1, } ||
    compiled_module_binary_negotiate_version([1, 2]) != 2 ||
    compiled_module_binary_negotiate_version([9]) != -1 {
    return false
  }
  // DAG codec: one large type repeated across constructors.
  let big = DPi(DNatTy, DPi(DNatTy, DPi(DNatTy, DNatTy)))
  let ctors : Array[DConstructorSpec] = []
  for i in 0..<8 {
    ctors.push(
      dconstructor_spec("c" + i.to_string(), [darg_external("f", big)]),
    )
  }
  let dag_spec = dinductive_spec("DagShareS", 0, [], [], ctors)
  let dag_registry = schema_registry_new()
  ignore(schema_registry_register_inductive(dag_registry, dag_spec))
  let dag_snapshot = schema_registry_snapshot(dag_registry)
  let plain = match
    schema_registry_snapshot_to_binary_version(dag_snapshot, 1) {
    Some(v) => v
    None => return false
  }
  let shared = match
    schema_registry_snapshot_to_binary_version(dag_snapshot, 2) {
    Some(v) => v
    None => return false
  }
  if shared.length() >= plain.length() ||
    schema_registry_binary_version_of(shared) != 2 ||
    schema_registry_binary_version_of(plain) != 1 {
    return false
  }
  match schema_registry_snapshot_from_binary(shared) {
    Some(back) =>
      if back.inductive_specs != dag_snapshot.inductive_specs {
        return false
      }
    None => return false
  }
  // Negotiation against a tag-8 family module.
  let rose = dinductive_spec(
    "NegRoseS",
    0,
    [dtelescope_entry("A", DUniv(0))],
    [],
    [
      dconstructor_spec("leaf", [darg_external("label", DTVar(0))]),
      dconstructor_spec("node", [
        darg_nested(
          "children",
          dfunctor_family(list_schema(), params=[dfunctor_param_self()]),
        ),
      ]),
    ],
  )
  let rose_module = module_def("Demo.NegRose", decls=[
    module_decl("RoseBool", DUniv(0), DInductive(rose, [DBoolTy])),
  ])
  let rose_compiled = match module_compile(module_env_new(), rose_module, []) {
    Some(v) => v
    None => return false
  }
  if compiled_module_to_binary_for_peer(rose_compiled, [1]) != None {
    return false
  }
  match compiled_module_to_binary_for_peer(rose_compiled, [1, 2]) {
    Some(bytes) =>
      if compiled_module_binary_version_of(bytes) != 2 {
        return false
      }
    None => return false
  }
  match compiled_module_to_binary_for_peer(rose_compiled, [2, 3]) {
    Some(bytes) =>
      if compiled_module_binary_version_of(bytes) != 3 {
        return false
      }
    None => return false
  }
  // Repository behaviour over the in-memory byte store.
  let compiled = match module_compile(module_env_new(), bool_ops_module(), []) {
    Some(v) => v
    None => return false
  }
  let store = artifact_memory_byte_store_new()
  let repo = artifact_repository_new(store)
  let module_record = match
    artifact_repository_put_compiled_module(repo, compiled) {
    Some(v) => v
    None => return false
  }
  if module_record.format_version != 3 {
    return false
  }
  match artifact_repository_get_compiled_module(repo, compiled.module_path) {
    Some(back) => if back != compiled { return false }
    None => return false
  }
  match artifact_repository_put_registry_snapshot(repo, "dag", dag_snapshot) {
    Some(_) => ()
    None => return false
  }
  match artifact_repository_get_registry_snapshot(repo, "dag") {
    Some(back) =>
      if back.inductive_specs != dag_snapshot.inductive_specs {
        return false
      }
    None => return false
  }
  if artifact_repository_stats(repo).records != 2 ||
    !artifact_repository_verify_all(repo) {
    return false
  }
  // A corrupted blob is refused, then repaired by re-putting.
  let blob = match (store.read)(module_record.blob_key) {
    Some(v) => v
    None => return false
  }
  blob[blob.length() - 1] = (blob[blob.length() - 1] + 1) & 255
  ignore((store.write)(module_record.blob_key, blob))
  if artifact_repository_get_compiled_module(repo, compiled.module_path) != None {
    return false
  }
  match artifact_repository_put_compiled_module(repo, compiled) {
    Some(_) => ()
    None => return false
  }
  match artifact_repository_get_compiled_module(repo, compiled.module_path) {
    Some(back) => if back != compiled { return false }
    None => return false
  }
  // A destroyed index is rebuilt from the commit manifests.
  ignore((store.write)("artifacts/index.bin", [1, 2, 3]))
  if artifact_repository_get_compiled_module(repo, compiled.module_path) != None ||
    artifact_repository_recover(repo) != 2 {
    return false
  }
  match artifact_repository_get_compiled_module(repo, compiled.module_path) {
    Some(back) => if back != compiled { return false }
    None => return false
  }
  if !artifact_repository_remove(repo, artifact_kind_schema_registry(), "dag") ||
    artifact_repository_stats(repo).records != 1 {
    return false
  }
  match artifact_repository_get_registry_snapshot(repo, "dag") {
    Some(_) => return false
    None => ()
  }
  artifact_repository_verify_all(repo)
}

///|
/// Phase 12: positivity declarations for opaque neutral
/// operators.  Without a declaration, an occurrence of the
/// family under an opaque operator application is unknown;
/// with a declaration for the operator it is strictly positive,
/// including under a binder (de Bruijn shifting), while a
/// negative (domain) position stays negative.  Parameter-use
/// certification through an operator parameter `F` is strict
/// only with the declaration.  Lambda operators get verified
/// declarations, and a negative lambda is refused.
pub fn check_positivity_declarations() -> Bool {
  let target_spec = dinductive_spec("DeclTargetS", 0, [], [], [
    dconstructor_spec("mk", []),
  ])
  let target = DInductive(target_spec, [])
  let decl = match
    dpositivity_declaration(DTVar(0), 1, strict_args=[0], scope=1) {
    Some(v) => v
    None => return false
  }
  let applied = DApp(DTVar(0), target)
  let plain = dterm_family_positivity(applied, "DeclTargetS")
  if plain.strictly_positive || !plain.unknown {
    return false
  }
  if !dterm_family_strictly_positive_declared(
      applied,
      "DeclTargetS",
      [decl],
      scope=1,
    ) {
    return false
  }
  // Under one binder the operator variable is DTVar(1).
  let under_binder = DPi(DNatTy, DApp(DTVar(1), target))
  if !dterm_family_strictly_positive_declared(
      under_binder,
      "DeclTargetS",
      [decl],
      scope=1,
    ) {
    return false
  }
  // The same application in a domain is negative.
  let negative = DPi(applied, DNatTy)
  let neg_report = dterm_family_positivity_declared(
    negative,
    "DeclTargetS",
    [decl],
    scope=1,
  )
  if neg_report.strictly_positive || !neg_report.negative_polarity {
    return false
  }
  // A position not declared does not become positive.
  let empty_decl = match dpositivity_declaration(DTVar(0), 1, scope=1) {
    Some(v) => v
    None => return false
  }
  if dterm_family_strictly_positive_declared(
      applied,
      "DeclTargetS",
      [empty_decl],
      scope=1,
    ) {
    return false
  }
  // Shape checking: overlapping positions are refused.
  if dpositivity_declaration(
      DTVar(0),
      1,
      strict_args=[0],
      positive_args=[0],
      scope=1,
    ) !=
    None {
    return false
  }
  // Parameter use through an operator parameter F : Type→Type.
  let op_spec = dinductive_spec(
    "OpParamS",
    0,
    [
      dtelescope_entry("F", DPi(DUniv(0), DUniv(0))),
      dtelescope_entry("A", DUniv(0)),
    ],
    [],
    [dconstructor_spec("wrap", [darg_external("x", DApp(DTVar(1), DTVar(0)))])],
  )
  if inductive_parameter_positivity(op_spec, 1).strictly_positive {
    return false
  }
  let f_decl = match
    dpositivity_declaration(DTVar(1), 1, strict_args=[0], scope=2) {
    Some(v) => v
    None => return false
  }
  let certified = inductive_parameter_positivity_declared(op_spec, 1, [f_decl])
  if !certified.strictly_positive || !certified.occurs || certified.unknown {
    return false
  }
  // Verified declarations for literal lambda operators.
  let list_op = DLam(DUniv(0), DListTy(DTVar(0)))
  match dpositivity_declaration_from_lambda(list_op, 1) {
    Some(d) => if d.strict_args != [0] || d.positive_args != [] { return false }
    None => return false
  }
  let const_op = DLam(DUniv(0), DNatTy)
  match dpositivity_declaration_from_lambda(const_op, 1) {
    Some(d) => if d.strict_args != [0] { return false }
    None => return false
  }
  let negative_op = DLam(DUniv(0), DPi(DTVar(0), DNatTy))
  if dpositivity_declaration_from_lambda(negative_op, 1) != None {
    return false
  }
  // A binary operator strict in its second argument only:
  // λX. λY. (X → Nat) × List Y  is refused (first is negative),
  // while λX. λY. List X × Y certifies both positions.
  let mixed_op = DLam(
    DUniv(0),
    DLam(DUniv(0), DSigma(DListTy(DTVar(1)), DTVar(0))),
  )
  match dpositivity_declaration_from_lambda(mixed_op, 2) {
    Some(d) => if d.strict_args != [0, 1] { return false }
    None => return false
  }
  true
}

///|
/// Phase 12: simultaneous IR compilation to eliminators over
/// the base family.  A universe function whose cases mention
/// an earlier function's hypotheses compiles to a closed
/// eliminator term (the decode route still refuses it, since a
/// nested decode over a different renamed copy would be
/// ill-typed); cyclic interdependence is refused;
/// function-valued recursive arguments substitute under a
/// lambda.  Compiled terms are typechecked against their
/// advertised Pi types and normalised on concrete codes.
pub fn check_simultaneous_ir_eliminator_compilation() -> Bool {
  // The eliminator motive is predicative, so the code family
  // lives one universe above the interpreted types.
  let base = dinductive_spec(
    "CodeSU",
    1,
    [],
    [],
    code_interpretation_ir(false).base.constructors,
  )
  // With two functions the binary case context is
  // a, El a, El2 a, b, El b, El2 b.
  let el = dsimultaneous_function("El", DUniv(0), [
    DNatTy,
    DBoolTy,
    DSigma(DTVar(4), DTVar(2)),
    DPi(DTVar(4), DTVar(2)),
  ])
  let el2 = dsimultaneous_function("El2", DUniv(0), [
    DBoolTy,
    DNatTy,
    DSigma(DTVar(4), DTVar(2)),
    DPi(DTVar(4), DTVar(2)),
  ])
  let spec = dsimultaneous_ir_spec(base, [el, el2])
  if !simultaneous_ir_validate(spec) ||
    !simultaneous_ir_uses_other_hypotheses(spec, 1) ||
    simultaneous_ir_compile_decode(spec, 1) != None {
    return false
  }
  let block = simultaneous_ir_compile_eliminator_block(spec)
  let el_term = match block[0] {
    Some(v) => v
    None => return false
  }
  let el2_term = match block[1] {
    Some(v) => v
    None => return false
  }
  match simultaneous_ir_eliminator_type(spec, 1) {
    Some(ty) => if !dep_check_closed(el2_term, ty) { return false }
    None => return false
  }
  ignore(el_term)
  let cnat_t = schema_intro_term(base, 0, [], [])
  let cbool_t = schema_intro_term(base, 1, [], [])
  let code_t = schema_intro_term(base, 3, [], [
    cnat_t,
    schema_intro_term(base, 2, [], [cbool_t, cnat_t]),
  ])
  // El2(carrow(cnat, cpair(cbool, cnat)))
  //   = Pi(El(cnat), Sigma(El(cbool), El(cnat)))
  //   = Nat -> Bool x Nat.
  if dep_nf_closed(DApp(el2_term, code_t), DUniv(0)) !=
    Some(DPi(DNatTy, DSigma(DBoolTy, DNatTy))) {
    return false
  }
  // And El itself through the same route.
  if dep_nf_closed(DApp(el_term, code_t), DUniv(0)) !=
    Some(DPi(DNatTy, DSigma(DBoolTy, DNatTy))) {
    return false
  }
  // Cyclic interdependence compiles on neither route.
  let cyc_a = dsimultaneous_function("A", DUniv(0), [
    DNatTy,
    DBoolTy,
    DSigma(DTVar(3), DTVar(1)),
    DPi(DTVar(3), DTVar(1)),
  ])
  let cyc_b = dsimultaneous_function("B", DUniv(0), [
    DBoolTy,
    DNatTy,
    DSigma(DTVar(4), DTVar(2)),
    DPi(DTVar(4), DTVar(2)),
  ])
  let cyclic = dsimultaneous_ir_spec(base, [cyc_a, cyc_b])
  if !simultaneous_ir_validate(cyclic) {
    return false
  }
  let cyc_block = simultaneous_ir_compile_eliminator_block(cyclic)
  if cyc_block[0] != None || cyc_block[1] != None {
    return false
  }
  // Function-valued recursive arguments.
  let fn_base = dinductive_spec("FnCodeSU", 1, [], [], [
    dconstructor_spec("leaf", []),
    dconstructor_spec("node", [darg_function("branch", DBoolTy)]),
  ])
  let fn_el = dsimultaneous_function("El", DUniv(0), [
    DNatTy,
    DPi(DBoolTy, DApp(DTVar(2), DTVar(0))),
  ])
  let fn_el2 = dsimultaneous_function("El2", DUniv(0), [
    DBoolTy,
    DPi(DBoolTy, DApp(DTVar(2), DTVar(0))),
  ])
  let fn_spec = dsimultaneous_ir_spec(fn_base, [fn_el, fn_el2])
  if !simultaneous_ir_validate(fn_spec) {
    return false
  }
  let fn_term = match simultaneous_ir_compile_eliminator(fn_spec, 1) {
    Some(v) => v
    None => return false
  }
  let leaf_t = schema_intro_term(fn_base, 0, [], [])
  let node_t = schema_intro_term(fn_base, 1, [], [DLam(DBoolTy, leaf_t)])
  // El2(node (lambda _. leaf)) = Bool -> El(leaf) = Bool -> Nat.
  dep_nf_closed(DApp(fn_term, node_t), DUniv(0)) == Some(DPi(DBoolTy, DNatTy))
}

///|
/// Phase 12: case-split conversion on discrete Bool variables,
/// and path-valued composition for the circle and torus.
/// `if x then 0 else 0` is not plainly convertible to `0` for
/// a neutral Bool `x`, but is after splitting; a genuinely
/// x-dependent term still refuses; nested splits and dependent
/// motive types are substituted along; Nat variables are never
/// split.  Composition in a Path type over S¹/T² whose right
/// endpoint traverses the loop now computes the loop itself
/// as cap (the branch coordinate is read generically so a
/// traversed coordinate 1 is not normalised to the base 0).
pub fn check_case_split_conversion_and_path_comp() -> Bool {
  let nat_motive = DLam(DBoolTy, DNatTy)
  let ctx = [DBoolTy]
  let ite0 = DBoolElim(nat_motive, DNatZero, DNatZero, DTVar(0))
  if conv_terms_plain(ctx, DNatTy, ite0, DNatZero) ||
    !conv_terms_case_split(ctx, DNatTy, ite0, DNatZero) {
    return false
  }
  let ite01 = DBoolElim(nat_motive, DNatZero, DSucc(DNatZero), DTVar(0))
  if conv_terms_case_split(ctx, DNatTy, ite01, DNatZero) {
    return false
  }
  // Two Bool variables, split recursively.
  let ctx2 = [DBoolTy, DBoolTy]
  let inner = DBoolElim(nat_motive, DNatZero, DNatZero, DTVar(0))
  let nested = DBoolElim(nat_motive, inner, DNatZero, DTVar(1))
  if conv_terms_plain(ctx2, DNatTy, nested, DNatZero) ||
    !conv_terms_case_split(ctx2, DNatTy, nested, DNatZero) {
    return false
  }
  // Dependent type: T(x) = if x then Nat else Bool, with two
  // different fillers for the false branch that agree only
  // after splitting.
  let type_motive = DLam(DBoolTy, DUniv(0))
  let dep_ty = DBoolElim(type_motive, DNatTy, DBoolTy, DTVar(0))
  let filler_a = DBoolElim(
    DLam(DBoolTy, DBoolElim(type_motive, DNatTy, DBoolTy, DTVar(0))),
    DNatZero,
    DBoolLit(true),
    DTVar(0),
  )
  let bool_motive = DLam(DBoolTy, DBoolTy)
  let filler_b = DBoolElim(
    DLam(DBoolTy, DBoolElim(type_motive, DNatTy, DBoolTy, DTVar(0))),
    DNatZero,
    DBoolElim(bool_motive, DBoolLit(true), DBoolLit(true), DTVar(0)),
    DTVar(0),
  )
  if conv_terms_plain(ctx, dep_ty, filler_a, filler_b) ||
    !conv_terms_case_split(ctx, dep_ty, filler_a, filler_b) {
    return false
  }
  // A Nat variable is never split.
  let nat_ctx = [DNatTy]
  let stuck_nat = DNatElim(
    DLam(DNatTy, DNatTy),
    DNatZero,
    DLam(DNatTy, DLam(DNatTy, DNatZero)),
    DTVar(0),
  )
  if conv_terms_case_split(nat_ctx, DNatTy, stuck_nat, DNatZero) {
    return false
  }
  // Path-valued composition over the torus: the right
  // endpoint of the path type traverses loopA, the tube
  // supplies the truncated loop, and the cap is loopA.
  let torus_base = DVTorusPoint(DZero, DZero)
  let torus_line = (j : Dim) => {
    DVPathTy(_ => DVTorusTy, torus_base, torus_point(j, DZero))
  }
  let torus_system = dsystem_of([
    tube_branch(FEq1(DVar(0)), (j : Dim) => {
      DVPathLam(k => torus_point(dim_simplify(DAnd(k, j)), DZero))
    }),
  ])
  let torus_cap = comp_value(
    torus_line,
    torus_system,
    DVPathLam(_ => torus_base),
    1,
  )
  let torus_cap_ty : DValue = DVPathTy(
    _ => DVTorusTy,
    torus_base,
    torus_point(DOne, DZero),
  )
  if !conv_at(
      0,
      1,
      torus_cap_ty,
      torus_cap,
      DVPathLam(k => torus_point(k, DZero)),
    ) {
    return false
  }
  // The same for the circle, and in the torus' second
  // coordinate.
  let circle_base = DVCirclePoint(DZero)
  let circle_line = (j : Dim) => {
    DVPathTy(_ => DVCircleTy, circle_base, circle_point(j))
  }
  let circle_system = dsystem_of([
    tube_branch(FEq1(DVar(0)), (j : Dim) => {
      DVPathLam(k => circle_point(dim_simplify(DAnd(k, j))))
    }),
  ])
  let circle_cap = comp_value(
    circle_line,
    circle_system,
    DVPathLam(_ => circle_base),
    1,
  )
  let circle_cap_ty : DValue = DVPathTy(
    _ => DVCircleTy,
    circle_base,
    circle_point(DOne),
  )
  if !conv_at(0, 1, circle_cap_ty, circle_cap, DVPathLam(k => circle_point(k))) {
    return false
  }
  let torus_b_line = (j : Dim) => {
    DVPathTy(_ => DVTorusTy, torus_base, torus_point(DZero, j))
  }
  let torus_b_system = dsystem_of([
    tube_branch(FEq1(DVar(0)), (j : Dim) => {
      DVPathLam(k => torus_point(DZero, dim_simplify(DAnd(k, j))))
    }),
  ])
  let torus_b_cap = comp_value(
    torus_b_line,
    torus_b_system,
    DVPathLam(_ => torus_base),
    1,
  )
  let torus_b_ty : DValue = DVPathTy(
    _ => DVTorusTy,
    torus_base,
    torus_point(DZero, DOne),
  )
  conv_at(0, 1, torus_b_ty, torus_b_cap, DVPathLam(k => torus_point(DZero, k)))
}

///|
/// Phase 12: stratified extensionality for host cube
/// functions.  Cubes that agree at a generic interior point
/// but differ on an endpoint stratum, on a diagonal, or on a
/// connection stratum are separated by the stratified probe
/// tiers; genuinely equal cubes pass; an open box whose faces
/// agree on generic edge interiors but disagree at an edge
/// endpoint passes plain validation and fails stratified
/// validation, while a constant box fills under the
/// stratified verified path.
pub fn check_dcube_stratified_extensionality() -> Bool {
  let zero : DValue = DVZeroNat
  let one : DValue = DVSucc(DVZeroNat)
  let const0 = dcube_constant(2, zero)
  let endpoint_sneaky = dcube_function(2, dims => {
    match dims[0] {
      DZero => one
      _ => zero
    }
  })
  if !dcube_cubes_conv(0, 0, DVNatTy, const0, endpoint_sneaky) {
    return false
  }
  let report = dcube_cubes_conv_stratified_report(
    0,
    0,
    DVNatTy,
    const0,
    endpoint_sneaky,
  )
  if report.equal || !report.complete || report.probes < 1 {
    return false
  }
  let diagonal_sneaky = dcube_function(2, dims => {
    if dims[0] == dims[1] {
      one
    } else {
      zero
    }
  })
  if !dcube_cubes_conv(0, 0, DVNatTy, const0, diagonal_sneaky) ||
    dcube_cubes_conv_stratified(0, 0, DVNatTy, const0, diagonal_sneaky) {
    return false
  }
  let connection_sneaky = dcube_function(2, dims => {
    match dims[0] {
      DAnd(_, _) => one
      _ => zero
    }
  })
  if !dcube_cubes_conv(0, 0, DVNatTy, const0, connection_sneaky) ||
    dcube_cubes_conv_stratified(0, 0, DVNatTy, const0, connection_sneaky) {
    return false
  }
  // Positive control: commutativity of the connection is
  // invisible to no tier.
  let meet_a = dcube_function(2, dims => {
    circle_point(dim_simplify(DAnd(dims[0], dims[1])))
  })
  let meet_b = dcube_function(2, dims => {
    circle_point(dim_simplify(DAnd(dims[1], dims[0])))
  })
  let meet_report = dcube_cubes_conv_stratified_report(
    0,
    0,
    DVCircleTy,
    meet_a,
    meet_b,
  )
  // All four tiers run to completion on an equal pair:
  // 3^2 + 4^2 + 4^2 + 8^2 probes.
  if !meet_report.equal || meet_report.probes != 105 {
    return false
  }
  // Box level: in arity 3, one face disagrees with its
  // neighbours only at a corner of the shared edge.
  let face_const = dcube_constant(2, zero)
  let corner_sneaky = dcube_function(2, dims => {
    match (dims[0], dims[1]) {
      (DZero, DZero) => one
      _ => zero
    }
  })
  let mk_box = (axis1_lo : DCubeFunction) => {
    dcube_open_box(DVNatTy, 3, 0, [
      dcube_box_face(0, false, face_const),
      dcube_box_face(0, true, face_const),
      dcube_box_face(1, false, axis1_lo),
      dcube_box_face(1, true, face_const),
      dcube_box_face(2, false, face_const),
    ])
  }
  let bad_box = mk_box(corner_sneaky)
  if !dcube_box_validate(bad_box, 0).overlaps_ok {
    return false
  }
  let bad_report = dcube_box_validate_stratified(bad_box, 0)
  if bad_report.overlaps_ok || bad_report.failed_overlaps < 1 {
    return false
  }
  match dcube_box_fill_verified_stratified(bad_box, 0) {
    Some(_) => return false
    None => ()
  }
  let good_box = mk_box(face_const)
  match dcube_box_fill_verified_stratified(good_box, 0) {
    Some(filler) => dcube_filler_faces_ok_stratified(good_box, filler, 0)
    None => false
  }
}

///|
/// Phase 12: unit laws of loop composition as explicit
/// 3-cells on sphere representatives (the representative
/// calculus' first higher groupoid structure), and the Hopf
/// identities in exact rational arithmetic.  The left unit
/// 3-cell rotates the top edge of the transitivity square
/// onto its right edge in two connection phases; the right
/// unit slides through its square.  On `S^2` and `S^3`
/// generator representatives both cells have the advertised
/// faces and stay inside the iterated loop space at a
/// generic parameter.  This is representative-level
/// structure: associativity/interchange 3-cells and an
/// internal Hopf map remain outside.
pub fn check_loop_unit_3cells_and_hopf_exact() -> Bool {
  if !check_hopf_exact_rational() {
    return false
  }
  let cases : Array[(Int32, Int32)] = [(2, 1), (2, 2), (2, -1), (3, 1)]
  for c in 0..<cases.length() {
    let (dim, n) = cases[c]
    let space_ty = loop_space_type_value(
      sphere_type_value(dim),
      sphere_north_value(dim),
      dim - 1,
    )
    let loop_ty = loop_space_type_value(
      sphere_type_value(dim),
      sphere_north_value(dim),
      dim,
    )
    let r = iterated_refl_value(sphere_north_value(dim), dim - 1)
    let r_dim = iterated_refl_value(sphere_north_value(dim), dim)
    let alpha = sphere_loop_power_value(dim, n)
    let left_cell = dpath_left_unit3_value(space_ty, r, alpha, 6)
    let left_lhs = sphere_loop_compose_value(dim, r_dim, alpha, 6)
    if !conv_at(0, 1, loop_ty, dapp_dim(left_cell, DZero), left_lhs) ||
      !conv_at(0, 1, loop_ty, dapp_dim(left_cell, DOne), alpha) {
      return false
    }
    let left_mid = dapp_dim(left_cell, DVar(0))
    if !conv_at(0, 1, space_ty, dapp_dim(left_mid, DZero), r) ||
      !conv_at(0, 1, space_ty, dapp_dim(left_mid, DOne), r) {
      return false
    }
    let right_cell = dpath_right_unit3_value(space_ty, r, alpha, 6)
    let right_lhs = sphere_loop_compose_value(dim, alpha, r_dim, 6)
    if !conv_at(0, 1, loop_ty, dapp_dim(right_cell, DZero), right_lhs) ||
      !conv_at(0, 1, loop_ty, dapp_dim(right_cell, DOne), alpha) {
      return false
    }
    let right_mid = dapp_dim(right_cell, DVar(0))
    if !conv_at(0, 1, space_ty, dapp_dim(right_mid, DZero), r) ||
      !conv_at(0, 1, space_ty, dapp_dim(right_mid, DOne), r) {
      return false
    }
  }
  true
}
