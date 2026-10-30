///|
/// Phase 13: strict positivity at self-family positions via a
/// least-fixpoint over the host spec's own parameter reports.
/// Bush's stored parameter is now certified strictly positive
/// (it was `unknown` through the self-application); a phantom
/// self-nested parameter stays absent; negativity introduced
/// one self-application deep propagates; and a two-parameter
/// swap family certifies both parameters through the mutual
/// fixpoint.
pub fn check_self_family_positivity_fixpoint() -> Bool {
  // Bush A: head : A, tail : Bush (Bush A).
  let bush = dinductive_spec(
    "BushP",
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
  let bush_report = inductive_parameter_positivity(bush, 0)
  if !bush_report.occurs ||
    !bush_report.strictly_positive ||
    bush_report.unknown ||
    bush_report.negative_polarity {
    return false
  }
  // Phantom: the only constructor steps to Phantom (Phantom A)
  // and never stores an A.
  let phantom = dinductive_spec(
    "PhantomP",
    0,
    [dtelescope_entry("A", DUniv(0))],
    [],
    [
      dconstructor_spec("step", [
        darg_nested(
          "next",
          dfunctor_self_family(params=[dfunctor_param_self()]),
        ),
      ]),
    ],
  )
  if inductive_parameter_positivity(phantom, 0).occurs {
    return false
  }
  // Negative one level down: Step stores NegSelf (A -> Nat),
  // whose Base stores the function.
  let neg_self = dinductive_spec(
    "NegSelfP",
    0,
    [dtelescope_entry("A", DUniv(0))],
    [],
    [
      dconstructor_spec("base", [darg_external("val", DTVar(0))]),
      dconstructor_spec("step", [
        darg_nested(
          "next",
          dfunctor_self_family(params=[
            dfunctor_param_term(DPi(DTVar(0), DNatTy)),
          ]),
        ),
      ]),
    ],
  )
  let neg_report = inductive_parameter_positivity(neg_self, 0)
  if !neg_report.occurs ||
    neg_report.strictly_positive ||
    !neg_report.negative_polarity ||
    neg_report.unknown {
    return false
  }
  // Two parameters, swapped at every self-application; only A
  // is ever stored directly, so B is positive only through one
  // swap.
  let swap = dinductive_spec(
    "SwapP",
    0,
    [dtelescope_entry("A", DUniv(0)), dtelescope_entry("B", DUniv(0))],
    [],
    [
      dconstructor_spec("leaf", [darg_external("val", DTVar(1))]),
      dconstructor_spec("step", [
        darg_nested(
          "next",
          dfunctor_self_family(params=[
            dfunctor_param_term(DTVar(0)),
            dfunctor_param_term(DTVar(1)),
          ]),
        ),
      ]),
    ],
  )
  let ra = inductive_parameter_positivity(swap, 0)
  let rb = inductive_parameter_positivity(swap, 1)
  ra.occurs &&
  ra.strictly_positive &&
  !ra.unknown &&
  rb.occurs &&
  rb.strictly_positive &&
  !rb.unknown &&
  !rb.negative_polarity
}

///|
/// Phase 13: foreign induction hypotheses at *nested*
/// constructor arguments in the simultaneous-IR eliminator
/// route.  The base family has product-, function- and
/// product-of-list-nested recursive arguments; the second
/// function's cases read the first function's hypotheses out
/// of the functor bundles, which the compiler now rebuilds by
/// a term-level functorial map of the foreign compiled
/// eliminator.  Compiled results agree with the simultaneous
/// semantics on closed trees.
pub fn check_simultaneous_ir_nested_foreign() -> Bool {
  let idx : Array[DTerm] = []
  let idf = dfunctor_identity(idx)
  let base = dinductive_spec("TreeSU", 1, [], [], [
    dconstructor_spec("leaf", []),
    dconstructor_spec("nodeP", [darg_nested("pair", dfunctor_product(idf, idf))]),
    dconstructor_spec("nodeF", [
      darg_nested("branch", dfunctor_pi(DBoolTy, idf)),
    ]),
    dconstructor_spec("nodePL", [
      darg_nested("headkids", dfunctor_product(idf, dfunctor_list(idf))),
    ]),
  ])
  // Case context per nested constructor (no parameters):
  // value, El-IH bundle, El2-IH bundle; de Bruijn 2, 1, 0.
  let el = dsimultaneous_function("ElT", DUniv(0), [
    DBoolTy,
    DSigma(DFst(DTVar(1)), DSnd(DTVar(2))),
    DPi(DBoolTy, DApp(DTVar(2), DTVar(0))),
    DFst(DTVar(1)),
  ])
  let el2 = dsimultaneous_function("El2T", DUniv(0), [
    DUnitTy,
    DFst(DTVar(1)),
    DApp(DTVar(1), DBoolLit(true)),
    DFst(DTVar(1)),
  ])
  let spec = dsimultaneous_ir_spec(base, [el, el2])
  if !simultaneous_ir_validate(spec) ||
    !simultaneous_ir_uses_other_hypotheses(spec, 1) {
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
  let leaf_t = schema_intro_term(base, 0, [], [])
  let p_t = schema_intro_term(base, 1, [], [DPair(leaf_t, leaf_t)])
  if dep_nf_closed(DApp(el_term, p_t), DUniv(0)) !=
    Some(DSigma(DBoolTy, DBoolTy)) {
    return false
  }
  if dep_nf_closed(DApp(el2_term, p_t), DUniv(0)) != Some(DBoolTy) {
    return false
  }
  let f_t = schema_intro_term(base, 2, [], [DLam(DBoolTy, leaf_t)])
  if dep_nf_closed(DApp(el_term, f_t), DUniv(0)) != Some(DPi(DBoolTy, DBoolTy)) {
    return false
  }
  if dep_nf_closed(DApp(el2_term, f_t), DUniv(0)) != Some(DBoolTy) {
    return false
  }
  let kids = DCons(leaf_t, DCons(leaf_t, DNil))
  let pl_t = schema_intro_term(base, 3, [], [DPair(leaf_t, kids)])
  dep_nf_closed(DApp(el2_term, pl_t), DUniv(0)) == Some(DBoolTy) &&
  dep_nf_closed(DApp(el_term, pl_t), DUniv(0)) == Some(DBoolTy)
}

///|
fn parity_faces(k : Int32) -> (Face, Face) {
  // (even, odd) parity faces over dimension levels [0, k),
  // where the proposition for level l is `FEq1(DVar(l))`.
  if k <= 0 {
    return (FTop, FBot)
  }
  let (even, odd) = parity_faces(k - 1)
  let zero = FEq0(DVar(k - 1))
  let one = FEq1(DVar(k - 1))
  (FOr(FAnd(even, zero), FAnd(odd, one)), FOr(FAnd(even, one), FAnd(odd, zero)))
}

///|
/// Phase 13: face-relative conversion descends only the
/// dimensions the quoted values mention.  On a face that
/// conjoins `(i9 = 0)` with an 8-variable parity condition
/// (a face BDD with hundreds of satisfying paths), the loop
/// on `i9` converts to the base point with a handful of
/// probes; with `i9` left free -- including its interior --
/// conversion correctly fails.
pub fn check_conv_under_face_relevant_descent() -> Bool {
  let (even, _odd) = parity_faces(8)
  let face = FAnd(FEq0(DVar(9)), even)
  let a : DValue = DVCirclePoint(DVar(9))
  let b : DValue = DVCirclePoint(DZero)
  let report = conv_at_under_face_report(0, 10, face, DVCircleTy, a, b)
  if !report.holds || report.nodes_visited > 12 {
    return false
  }
  let free_report = conv_at_under_face_report(0, 10, even, DVCircleTy, a, b)
  if free_report.holds {
    return false
  }
  // Each endpoint face separately converts; the endpoint
  // disjunction itself collapses to top at the BDD level (as
  // documented for the Boolean machinery), so its agreeing
  // part is witnessed by the exact Face-valued agreement
  // region instead.
  conv_at_under_face(0, 10, FEq0(DVar(9)), DVCircleTy, a, b) &&
  conv_at_under_face(0, 10, FEq1(DVar(9)), DVCircleTy, a, b) &&
  face_agreement_face(
    0,
    10,
    FOr(FEq0(DVar(9)), FEq1(DVar(9))),
    DVCircleTy,
    a,
    b,
  ) !=
  FBot
}

///|
fn from_zero_path(v : Int32) -> (Dim) -> DValue {
  d => if dim_eq_sem(d, DZero) { dv_nat_lit(0) } else { dv_nat_lit(v) }
}

///|
/// Phase 13: maximum compatible completion.  Five branches
/// whose conflict graph has the order-greedy maximal system
/// {b0, b4} of size 2 but the maximum {b1, b2, b3} of size 3.
/// The exact completion finds the maximum, certifies it, and
/// stays compatible; with a zero node budget it reports
/// `exact = false` yet never returns less than the greedy
/// incumbent.
pub fn check_dsystem_maximum_completion() -> Bool {
  let line = (_ : Dim) => DVNatTy
  let system = DSystem::{
    branches: [
      tube_branch(FOr(FEq0(DVar(0)), FEq1(DVar(0))), from_zero_path(1)),
      tube_branch(FEq0(DVar(0)), from_zero_path(2)),
      tube_branch(FEq1(DVar(0)), from_zero_path(2)),
      tube_branch(FEq0(DVar(1)), from_zero_path(2)),
      tube_branch(FEq1(DVar(1)), from_zero_path(1)),
    ],
  }
  let base = dv_nat_lit(0)
  let greedy = dsystem_repair_with_candidates(0, 2, line, system, base, [])
  if greedy.system.branches.length() != 2 || !greedy.compatible {
    return false
  }
  let maximum = dsystem_repair_maximum(0, 2, line, system, base, [])
  if !maximum.exact ||
    !maximum.compatible ||
    maximum.system.branches.length() != 3 {
    return false
  }
  let starved = dsystem_repair_maximum(
    0,
    2,
    line,
    system,
    base,
    [],
    node_budget=0,
  )
  !starved.exact &&
  starved.compatible &&
  starved.system.branches.length() >= greedy.system.branches.length()
}

///|
/// Phase 13: square-valued composition over the primitive
/// Circle and Torus computes *verified* caps.  The De Morgan
/// coordinate selection previously computed a cap point for
/// path-valued boxes whose face variable also traverses the
/// coordinates -- and that point's restrictions were wrong
/// (a traversed loop became a tent, since endpoint
/// identification is not a congruence of the dimension
/// algebra).  Composition now tries several candidate
/// coordinates (iterated selection in both orders, undamped
/// and damped joins of the branch caps) and returns the
/// first whose restriction to every branch face is that
/// branch's cap; boxes with no verifying dimension
/// coordinate (there are such: edge restrictions can agree
/// only as points, 0 ~ 1, not as expressions) stay formal
/// `DNComp` neutrals.  Here: the cap of the square whose
/// tube is the loop computes to a point and converts to the
/// loop on the tube face.
pub fn check_circle_torus_square_comp() -> Bool {
  let base_pt : DValue = DVCirclePoint(DZero)
  let path_ty : DValue = DVPathTy(_ => DVCircleTy, base_pt, base_pt)
  let line = (_ : Dim) => path_ty
  let refl_p : DValue = DVPathLam(_ => base_pt)
  let loop_p : DValue = DVPathLam(k => circle_point(k))
  let branches = dsystem_of([tube_branch(FEq1(DVar(0)), _ => loop_p)])
  let result = comp_value(line, branches, refl_p, 1)
  match force_value(result) {
    DVPathLam(_) => ()
    _ => return false
  }
  if !conv_at(0, 1, DVCircleTy, dapp_dim(result, DZero), base_pt) ||
    !conv_at(0, 1, DVCircleTy, dapp_dim(result, DOne), base_pt) {
    return false
  }
  // The generic interior computes to a point (previously a
  // tent point with wrong restrictions), and the square
  // converts to the loop on the tube face.
  match force_value(dapp_dim(result, DVar(1))) {
    DVCirclePoint(_) => ()
    _ => return false
  }
  if !conv_at_under_face(0, 2, FEq1(DVar(0)), path_ty, result, loop_p) {
    return false
  }
  // Torus analogue, with the loop in the first coordinate.
  let tbase : DValue = DVTorusPoint(DZero, DZero)
  let tpath_ty : DValue = DVPathTy(_ => DVTorusTy, tbase, tbase)
  let tline = (_ : Dim) => tpath_ty
  let trefl : DValue = DVPathLam(_ => tbase)
  let tloop : DValue = DVPathLam(k => torus_point(k, DZero))
  let tbranches = dsystem_of([tube_branch(FEq1(DVar(0)), _ => tloop)])
  let tresult = comp_value(tline, tbranches, trefl, 1)
  match force_value(tresult) {
    DVPathLam(_) => ()
    _ => return false
  }
  if !conv_at(0, 1, DVTorusTy, dapp_dim(tresult, DZero), tbase) ||
    !conv_at(0, 1, DVTorusTy, dapp_dim(tresult, DOne), tbase) {
    return false
  }
  match force_value(dapp_dim(tresult, DVar(1))) {
    DVTorusPoint(_, _) => ()
    _ => return false
  }
  conv_at_under_face(0, 2, FEq1(DVar(0)), tpath_ty, tresult, tloop)
}

///|
/// Phase 13: Bool case-split conversion is guided by the
/// quoted normal-form difference.  With three Bool hypotheses
/// where both sides share a genuinely dependent subterm on
/// the *first* variable and differ only through the *last*,
/// the difference variables are exactly the last variable,
/// and the search splits once -- not once per mentioned
/// variable in declaration order.  A mismatched pair still
/// refuses.
pub fn check_difference_guided_case_split() -> Bool {
  let nat_motive = DNatTy
  let n1 = DSucc(DNatZero)
  let n2 = DSucc(n1)
  let n3 = DSucc(n2)
  let ctx = [DBoolTy, DBoolTy, DBoolTy]
  let sigma_ty = DSigma(DNatTy, DNatTy)
  // Level 0 is DTVar(2), level 2 is DTVar(0) in this scope.
  let shared = DBoolElim(nat_motive, n2, n3, DTVar(2))
  let differing = DBoolElim(nat_motive, n1, n1, DTVar(0))
  let lhs = DPair(shared, differing)
  let rhs = DPair(shared, n1)
  if conv_terms_plain(ctx, sigma_ty, lhs, rhs) {
    return false
  }
  if conv_difference_variables(ctx, sigma_ty, lhs, rhs) != [2] {
    return false
  }
  let report = conv_terms_case_split_report(ctx, sigma_ty, lhs, rhs)
  if !report.holds || report.root_difference_variables != 1 {
    return false
  }
  if report.split_nodes != 1 {
    return false
  }
  let bad_rhs = DPair(shared, DNatZero)
  !conv_terms_case_split_report(ctx, sigma_ty, lhs, bad_rhs).holds
}

///|
/// Phase 13: the in-process `DTerm` interner and its byte
/// backend share one DAG.  A reachable intern graph exports as
/// local shells plus child-id edges, survives `CHDAGBIN`
/// round-trip exactly, and imports node-by-node into fresh and
/// pre-populated tables (the second import adds nothing).
/// Invalid forward-edge snapshots are rejected before the
/// destination changes, and the artifact repository can put a
/// live table's DAG and get it back into another live table.
pub fn check_interned_dag_byte_sharing() -> Bool {
  let arrow = DPi(DNatTy, DNatTy)
  let pair_ty = DSigma(arrow, arrow)
  let big = DSigma(pair_ty, DPi(pair_ty, pair_ty))
  let elim = DInductiveElim(
    nat_schema(),
    DLam(DNatTy, DNatTy),
    [DNatZero, DLam(DNatTy, DLam(DNatTy, DTVar(0)))],
    [],
    [],
    DSucc(DNatZero),
  )
  let partial = DPartial([
    { face: FEq1(DVar(0)), body: DNatZero, },
    { face: FTop, body: arrow, },
  ])
  let roots = [big, elim, partial]
  let source = dterm_intern_table_new()
  let snapshot = dterm_dag_snapshot(source, roots)
  if !dterm_dag_snapshot_validate(snapshot) || snapshot.roots.length() != 3 {
    return false
  }
  if dterm_intern_lookup_id(source, big) != snapshot.roots[0] ||
    dterm_intern_lookup_id(source, elim) != snapshot.roots[1] ||
    dterm_intern_lookup_id(source, partial) != snapshot.roots[2] {
    return false
  }
  let tree_total = dterm_tree_node_count(big) +
    dterm_tree_node_count(elim) +
    dterm_tree_node_count(partial)
  if snapshot.nodes.length() >= tree_total ||
    snapshot.nodes.length() != dterm_intern_table_size(source) {
    return false
  }
  let bytes = match dterm_dag_snapshot_to_binary(snapshot) {
    Some(value) => value
    None => return false
  }
  if dterm_dag_binary_version_of(bytes) != 1 ||
    dterm_dag_binary_version_policy() !=
    BinaryVersionPolicy::{ current: 1, supported: [1], oldest_writable: 1, } {
    return false
  }
  match dterm_dag_snapshot_from_binary(bytes) {
    Some(back) => if back != snapshot { return false }
    None => return false
  }
  // Fresh destination: every node is added once.
  let fresh = dterm_intern_table_new()
  let first = match dterm_dag_import_binary(fresh, bytes) {
    Some(value) => value
    None => return false
  }
  if first.added_nodes != snapshot.nodes.length() || first.reused_nodes != 0 {
    return false
  }
  if dterm_intern_table_term(fresh, first.root_ids[0]) != Some(big) ||
    dterm_intern_table_term(fresh, first.root_ids[1]) != Some(elim) ||
    dterm_intern_table_term(fresh, first.root_ids[2]) != Some(partial) {
    return false
  }
  // Re-import into the same destination is pure reuse.
  let second = match dterm_dag_import(fresh, snapshot) {
    Some(value) => value
    None => return false
  }
  if second.added_nodes != 0 ||
    second.reused_nodes != snapshot.nodes.length() ||
    second.root_ids != first.root_ids {
    return false
  }
  // A destination that already shares a subterm reuses it.
  let overlap = dterm_intern_table_new()
  ignore(dterm_intern(overlap, arrow))
  let overlap_before = dterm_intern_table_size(overlap)
  let overlapped = match dterm_dag_import_binary(overlap, bytes) {
    Some(value) => value
    None => return false
  }
  if overlapped.reused_nodes < overlap_before ||
    dterm_intern_table_term(overlap, overlapped.root_ids[0]) != Some(big) ||
    dterm_intern_id(overlap, big).1 != overlapped.root_ids[0] {
    return false
  }
  // Forward edges are invalid and change nothing.
  let bad_snapshot : DTermDagSnapshot = {
    nodes: [
      DTermDagNode::{
        shell: DPi(DTVar(1000000), DTVar(1000001)),
        children: [0, 0],
      },
    ],
    roots: [0],
  }
  let guarded = dterm_intern_table_new()
  ignore(dterm_intern(guarded, DNatTy))
  let guarded_size = dterm_intern_table_size(guarded)
  if dterm_dag_snapshot_validate(bad_snapshot) ||
    dterm_dag_snapshot_to_binary(bad_snapshot) != None ||
    dterm_dag_import(guarded, bad_snapshot) != None ||
    dterm_intern_table_size(guarded) != guarded_size {
    return false
  }
  // Header-level corruption is reported precisely.
  let bad_magic : Array[Int32] = []
  for i in 0..<bytes.length() {
    bad_magic.push(bytes[i])
  }
  bad_magic[0] = 88
  if dterm_dag_snapshot_load_binary_report(bad_magic).status !=
    ModuleBinaryBadMagic ||
    dterm_dag_snapshot_load_binary_report([1, 2, 3]).status !=
    ModuleBinaryTruncated {
    return false
  }
  let bad_checksum : Array[Int32] = []
  for i in 0..<bytes.length() {
    bad_checksum.push(bytes[i])
  }
  let last = bad_checksum.length() - 1
  bad_checksum[last] = (bad_checksum[last] + 1) & 255
  if dterm_dag_snapshot_load_binary_report(bad_checksum).status !=
    ModuleBinaryChecksumMismatch {
    return false
  }
  // Repository round-trip between two live intern tables.
  let store = artifact_memory_byte_store_new()
  let repo = artifact_repository_new(store)
  let record = match
    artifact_repository_put_dterm_dag_terms(repo, "shared", source, roots) {
    Some(value) => value
    None => return false
  }
  if record.kind != artifact_kind_dterm_dag() || record.format_version != 1 {
    return false
  }
  match artifact_repository_get_dterm_dag_snapshot(repo, "shared") {
    Some(back) => if back != snapshot { return false }
    None => return false
  }
  let destination = dterm_intern_table_new()
  ignore(dterm_intern(destination, arrow))
  let imported = match
    artifact_repository_get_dterm_dag_into(repo, "shared", destination) {
    Some(value) => value
    None => return false
  }
  if dterm_intern_table_term(destination, imported.root_ids[0]) != Some(big) ||
    dterm_intern_table_term(destination, imported.root_ids[1]) != Some(elim) {
    return false
  }
  let imported_again = match
    artifact_repository_get_dterm_dag_into(repo, "shared", destination) {
    Some(value) => value
    None => return false
  }
  if imported_again.added_nodes != 0 ||
    imported_again.root_ids != imported.root_ids {
    return false
  }
  artifact_repository_verify_all(repo) &&
  artifact_repository_remove(repo, artifact_kind_dterm_dag(), "shared") &&
  artifact_repository_get_dterm_dag_snapshot(repo, "shared") == None
}

///|
/// Phase 13: subset-DP BDD ordering beyond the old twelve-variable
/// ceiling.  Cofactor sets are generated incrementally by
/// restriction, so a fourteen-variable pair function is optimized
/// exactly, agrees semantically on every assignment, is no larger
/// than the heuristic build, and the raised sixteen-variable cap
/// is still reported honestly at seventeen variables.
pub fn check_bdd_optimal_order_dp_extended() -> Bool {
  let f14 = phase12_pair_face(14)
  let dp14 = bdd_dag_of_face_optimal_dp(f14, 14)
  if !dp14.exact || dp14.tried != 114688 {
    return false
  }
  if dp14.order.length() != 14 {
    return false
  }
  for i in 0..<14 {
    let mut occurrences = 0
    for j in 0..<dp14.order.length() {
      if dp14.order[j] == i {
        occurrences = occurrences + 1
      }
    }
    if occurrences != 1 {
      return false
    }
  }
  if !phase12_bdd_semantics_ok(f14, dp14.built, 14) {
    return false
  }
  let heuristic = bdd_dag_of_face_optimized(f14, 14)
  if dp14.size > heuristic.reachable {
    return false
  }
  let routed = bdd_dag_of_face_optimal(f14, 14, exact_max_vars=16)
  if !routed.exact || routed.size != dp14.size {
    return false
  }
  let at_cap = bdd_dag_of_face_optimal_dp(FTop, 16)
  if !at_cap.exact {
    return false
  }
  let over_cap = bdd_dag_of_face_optimal_dp(FTop, 17)
  !over_cap.exact
}

///|
fn phase13_cdcl_step_counts(steps : Array[FaceCdclProofStep]) -> (Int32, Int32) {
  let mut adds = 0
  let mut deletes = 0
  for i in 0..<steps.length() {
    match steps[i] {
      CdclProofAdd(_) => adds = adds + 1
      CdclProofDelete(_) => deletes = deletes + 1
    }
  }
  (adds, deletes)
}

///|
/// Phase 13: CDCL DRUP proofs with explicit deletion steps.  The
/// checker audits additions against the evolving active database,
/// accepts deletion up to literal-set identity, rejects absent or
/// premature deletions and proofs that try to use a deleted
/// clause, and validates solver-generated proofs whose deletion
/// steps exactly account for learned-clause database reduction.
pub fn check_cdcl_drup_proof_with_deletions() -> Bool {
  let original = [[1], [-1, 2], [-2]]
  if !face_cdcl_drup_check(original, [
      CdclProofAdd([2, 1]),
      CdclProofDelete([1, 2]),
      CdclProofAdd([]),
    ]) {
    return false
  }
  if face_cdcl_drup_check(original, [CdclProofDelete([3]), CdclProofAdd([])]) {
    return false
  }
  if face_cdcl_drup_check(original, [
      CdclProofDelete([2, 1]),
      CdclProofAdd([2, 1]),
      CdclProofAdd([]),
    ]) {
    return false
  }
  if face_cdcl_drup_check([[1]], [CdclProofAdd([2]), CdclProofAdd([])]) {
    return false
  }
  let xor_clauses = [[1, 2], [-1, 2], [1, -2], [-1, -2]]
  if face_cdcl_drup_check(xor_clauses, [
      CdclProofAdd([2]),
      CdclProofDelete([2]),
      CdclProofAdd([]),
    ]) {
    return false
  }
  let (php65, vars65) = phase11_pigeonhole_face(6, 5)
  let result65 = face_sat_cdcl_proof(php65, vars65, max_steps=2000000)
  if result65.decision != FaceUnsat {
    return false
  }
  let (adds65, deletes65) = phase13_cdcl_step_counts(result65.proof_steps)
  if adds65 != result65.stats.learned + 1 || deletes65 != result65.stats.deleted {
    return false
  }
  if !face_cdcl_drup_check(result65.original_clauses, result65.proof_steps) {
    return false
  }
  let (php76, vars76) = phase11_pigeonhole_face(7, 6)
  let result76 = face_sat_cdcl_proof(php76, vars76, max_steps=5000000)
  if result76.decision != FaceUnsat || result76.stats.deleted <= 0 {
    return false
  }
  let (adds76, deletes76) = phase13_cdcl_step_counts(result76.proof_steps)
  adds76 == result76.stats.learned + 1 &&
  deletes76 == result76.stats.deleted &&
  deletes76 > 0 &&
  face_cdcl_drup_check(result76.original_clauses, result76.proof_steps)
}

///|
/// Phase 13: Tier D of stratified host-cube extensionality.
/// Cubes hiding only on a negated connection or a nested
/// axis-specific connection pass the old tiers' expression shapes
/// but are separated by Tier D; an equal pair runs all 105
/// two-dimensional probes, and arity five honestly reports the
/// skipped oversized Tier D as incomplete.
pub fn check_dcube_stratified_tier_d() -> Bool {
  let zero : DValue = DVZeroNat
  let one : DValue = DVSucc(DVZeroNat)
  let const0 = dcube_constant(2, zero)
  let negated_connection = dcube_function(2, dims => {
    match dims[0] {
      DNeg(DAnd(_, _)) => one
      _ => zero
    }
  })
  if !dcube_cubes_conv(0, 0, DVNatTy, const0, negated_connection) ||
    dcube_cubes_conv_stratified(0, 0, DVNatTy, const0, negated_connection) {
    return false
  }
  let nested_connection = dcube_function(2, dims => {
    match dims[1] {
      DAnd(DOr(_, _), DNeg(_)) => one
      _ => zero
    }
  })
  if !dcube_cubes_conv(0, 0, DVNatTy, const0, nested_connection) ||
    dcube_cubes_conv_stratified(0, 0, DVNatTy, const0, nested_connection) {
    return false
  }
  let meet_a = dcube_function(2, dims => {
    circle_point(dim_simplify(DAnd(dims[0], dims[1])))
  })
  let meet_b = dcube_function(2, dims => {
    circle_point(dim_simplify(DAnd(dims[1], dims[0])))
  })
  let report = dcube_cubes_conv_stratified_report(
    0,
    0,
    DVCircleTy,
    meet_a,
    meet_b,
  )
  if !report.equal || !report.complete || report.probes != 105 {
    return false
  }
  let const5_a = dcube_constant(5, zero)
  let const5_b = dcube_constant(5, zero)
  let report5 = dcube_cubes_conv_stratified_report(
    0,
    0,
    DVNatTy,
    const5_a,
    const5_b,
  )
  report5.equal && !report5.complete && report5.probes == 2291
}

///|
fn phase13_loop3_faces_ok(
  dim : Int32,
  cell : DValue,
  lhs : DValue,
  rhs : DValue,
) -> Bool {
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
  if !conv_at(0, 1, loop_ty, dapp_dim(cell, DZero), lhs) {
    return false
  }
  if !conv_at(0, 1, loop_ty, dapp_dim(cell, DOne), rhs) {
    return false
  }
  let mid = dapp_dim(cell, DVar(0))
  conv_at(0, 1, space_ty, dapp_dim(mid, DZero), r) &&
  conv_at(0, 1, space_ty, dapp_dim(mid, DOne), r)
}

///|
/// Phase 13: inverse, associativity and symmetry-of-composite
/// laws as explicit 3-cells on sphere representatives, and the
/// resulting classification of closed representative expressions
/// by degree.  Right/left inverse and associativity cells have
/// the advertised faces on `S^2` and `S^3`; every tested closed
/// expression is joined by its recursively assembled
/// normalization cell to the canonical word of the same degree.
pub fn check_loop_inverse_assoc_and_classification() -> Bool {
  for n in [-5, -2, -1, 0, 1, 2, 5] {
    if sphere_loop_expr_degree(sphere_loop_canonical_expr(n)) != n {
      return false
    }
  }
  let mixed = SphereLoopCompose(
    SphereLoopInverse(SphereLoopGenerator),
    SphereLoopCompose(SphereLoopGenerator, SphereLoopGenerator),
  )
  if sphere_loop_expr_normal_form(mixed) != sphere_loop_canonical_expr(1) ||
    !sphere_loop_expr_same_class(mixed, sphere_loop_canonical_expr(1)) ||
    sphere_loop_expr_same_class(mixed, sphere_loop_canonical_expr(2)) {
    return false
  }
  // Inverse laws.
  let inverse_cases : Array[(Int32, Int32)] = [(2, 1), (2, -1), (3, 1)]
  for c in 0..<inverse_cases.length() {
    let (dim, n) = inverse_cases[c]
    let space_ty = loop_space_type_value(
      sphere_type_value(dim),
      sphere_north_value(dim),
      dim - 1,
    )
    let r = iterated_refl_value(sphere_north_value(dim), dim - 1)
    let r_dim = iterated_refl_value(sphere_north_value(dim), dim)
    let alpha = sphere_loop_power_value(dim, n)
    let alpha_inv = dpath_sym_value(alpha)
    let right = dpath_right_inverse3_value(space_ty, r, alpha, 6)
    if !phase13_loop3_faces_ok(
        dim,
        right,
        sphere_loop_compose_value(dim, alpha, alpha_inv, 6),
        r_dim,
      ) {
      return false
    }
    let left = dpath_left_inverse3_value(space_ty, r, alpha, 6)
    if !phase13_loop3_faces_ok(
        dim,
        left,
        sphere_loop_compose_value(dim, alpha_inv, alpha, 6),
        r_dim,
      ) {
      return false
    }
  }
  // Associativity and symmetry of a composite.
  let assoc_cases : Array[(Int32, Int32, Int32, Int32)] = [
    (2, 1, -1, 2),
    (3, 1, 1, -1),
  ]
  for c in 0..<assoc_cases.length() {
    let (dim, a_deg, b_deg, c_deg) = assoc_cases[c]
    let space_ty = loop_space_type_value(
      sphere_type_value(dim),
      sphere_north_value(dim),
      dim - 1,
    )
    let r = iterated_refl_value(sphere_north_value(dim), dim - 1)
    let a = sphere_loop_power_value(dim, a_deg)
    let b = sphere_loop_power_value(dim, b_deg)
    let gamma = sphere_loop_power_value(dim, c_deg)
    let cell = dpath_assoc3_value(space_ty, r, a, b, gamma, 6)
    let lhs = sphere_loop_compose_value(
      dim,
      sphere_loop_compose_value(dim, a, b, 6),
      gamma,
      6,
    )
    let rhs = sphere_loop_compose_value(
      dim,
      a,
      sphere_loop_compose_value(dim, b, gamma, 6),
      6,
    )
    if !phase13_loop3_faces_ok(dim, cell, lhs, rhs) {
      return false
    }
  }
  let sym_space = loop_space_type_value(
    sphere_type_value(2),
    sphere_north_value(2),
    1,
  )
  let sym_r = iterated_refl_value(sphere_north_value(2), 1)
  let sym_a = sphere_loop_power_value(2, 1)
  let sym_b = sphere_loop_power_value(2, 2)
  let sym_cell = dpath_sym_compose3_value(sym_space, sym_r, sym_a, sym_b, 6)
  if !phase13_loop3_faces_ok(
      2,
      sym_cell,
      dpath_sym_value(sphere_loop_compose_value(2, sym_a, sym_b, 6)),
      sphere_loop_compose_value(
        2,
        dpath_sym_value(sym_b),
        dpath_sym_value(sym_a),
        6,
      ),
    ) {
    return false
  }
  // Normalization cells classify closed representative words by
  // degree, including inverse-of-composite and total cancellation.
  let gg = SphereLoopCompose(SphereLoopGenerator, SphereLoopGenerator)
  let expressions : Array[SphereLoopExpr] = [
    SphereLoopInverse(gg),
    mixed,
    SphereLoopCompose(gg, SphereLoopInverse(gg)),
  ]
  for i in 0..<expressions.length() {
    let expr = expressions[i]
    let cell = sphere_loop_expr_normalize3_value(2, expr)
    if !phase13_loop3_faces_ok(
        2,
        cell,
        sphere_loop_expr_value(2, expr),
        sphere_loop_canonical_value(2, sphere_loop_expr_degree(expr)),
      ) {
      return false
    }
  }
  let cell3 = sphere_loop_expr_normalize3_value(3, mixed)
  phase13_loop3_faces_ok(
    3,
    cell3,
    sphere_loop_expr_value(3, mixed),
    sphere_loop_canonical_value(3, 1),
  )
}

///|
/// Phase 13: residual HOU constraints are solvable as a set.
/// The MGU engine first leaves a rigid-spine equation residual;
/// the residual solver then solves exactly those returned
/// constraints, solves a two-constraint rigid/repeated set,
/// takes no search rounds on a principal problem, restores the
/// input on a definitive clash after a partial principal
/// assignment, and reports budget exhaustion without assigning
/// the blocked meta.
pub fn check_hou_residual_solver() -> Bool {
  let gx = UApp(UConst("g"), UVar(1))
  let sy = USucc(UVar(0))
  let rigid_lhs = UMeta(0, [gx, sy])
  let rigid_rhs = UPair(gx, sy)
  let u0 = unifier_new()
  ignore(hou_fresh_meta(u0, 0))
  let mgu = hou_unify_mgu(rigid_lhs, rigid_rhs, 2, u0)
  if mgu.status != HouMguResidual || mgu.residual.length() == 0 {
    return false
  }
  let from_residual = hou_solve_constraints(mgu.residual, u0, depth_cap=3)
  if from_residual.status != HouSolved ||
    from_residual.search_rounds == 0 ||
    from_residual.residual.length() != 0 ||
    hou_semantic_optimize(rigid_lhs, u0) != rigid_rhs {
    return false
  }
  // A residual set mixing a rigid spine and a repeated spine.
  let u1 = unifier_new()
  ignore(hou_fresh_meta(u1, 0))
  ignore(hou_fresh_meta(u1, 0))
  let c1 = HouConstraint::{ lhs: rigid_lhs, rhs: rigid_rhs, depth: 2, }
  let c2 = HouConstraint::{
    lhs: UMeta(1, [UVar(1), UVar(1)]),
    rhs: UPair(USucc(UVar(1)), UVar(1)),
    depth: 2,
  }
  let set_report = hou_solve_constraints([c1, c2], u1, depth_cap=3)
  if set_report.status != HouSolved ||
    set_report.initial_constraints != 2 ||
    set_report.solved_constraints != 2 ||
    hou_semantic_optimize(c1.lhs, u1) != c1.rhs ||
    hou_semantic_optimize(c2.lhs, u1) != c2.rhs {
    return false
  }
  // Principal fragment: no guessing is needed.
  let u2 = unifier_new()
  ignore(hou_fresh_meta(u2, 0))
  let principal = hou_unify_residual(
    UMeta(0, [UVar(1), UVar(0)]),
    UPair(UVar(1), UVar(0)),
    2,
    u2,
  )
  if principal.status != HouSolved || principal.search_rounds != 0 {
    return false
  }
  // A clash after a principal assignment restores the input.
  let u3 = unifier_new()
  ignore(hou_fresh_meta(u3, 0))
  let clash = hou_solve_constraints(
    [
      HouConstraint::{ lhs: UMeta(0, []), rhs: UBoolLit(true), depth: 0, },
      HouConstraint::{ lhs: UBoolLit(true), rhs: UBoolLit(false), depth: 0, },
    ],
    u3,
  )
  if clash.status != HouNoUnifier || u3.metas.length() != 1 {
    return false
  }
  match u3.metas[0].solution {
    Some(_) => return false
    None => ()
  }
  // Budget exhaustion is explicit and assigns nothing unsound.
  let u4 = unifier_new()
  ignore(hou_fresh_meta(u4, 0))
  let budget = hou_unify_residual(
    rigid_lhs,
    rigid_rhs,
    2,
    u4,
    max_nodes_per_round=1,
    depth_cap=1,
  )
  if budget.status != HouBudgetExceeded || budget.residual.length() == 0 {
    return false
  }
  match u4.metas[0].solution {
    Some(_) => false
    None => true
  }
}

///|
/// Phase 13: artifact manifests form an append-only integrity
/// chain.  Put/overwrite/remove are replayed to the live index,
/// an expected head anchors chained reads, a destroyed index is
/// recovered by chain replay (respecting tombstones), replaying
/// an old chain or tampering with an entry/blob is rejected,
/// and a legacy index is bootstrapped on its next put.
pub fn check_artifact_manifest_integrity_chain() -> Bool {
  let store = artifact_memory_byte_store_new()
  let repo = artifact_repository_new(store)
  ignore(artifact_repository_put(repo, "docs", "a", [1, 2, 3]))
  ignore(artifact_repository_put(repo, "docs", "b", [1, 2, 3]))
  ignore(artifact_repository_put(repo, "docs", "a", [9, 8]))
  let before_remove = artifact_repository_chain_report(repo)
  if !before_remove.valid ||
    before_remove.entries != 3 ||
    before_remove.live_records != 2 {
    return false
  }
  let old_head = artifact_repository_chain_head(repo)
  if !artifact_repository_remove(repo, "docs", "b") {
    return false
  }
  let report = artifact_repository_chain_report(repo)
  if !report.valid || report.entries != 4 || report.live_records != 1 {
    return false
  }
  match old_head {
    Some(head) =>
      if artifact_repository_chain_report(repo, expected_head=Some(head)).valid {
        return false
      }
    None => return false
  }
  let head = (report.head_a, report.head_b)
  if artifact_repository_get_chained(
      repo,
      "docs",
      "a",
      expected_head=Some(head),
    ) !=
    Some([9, 8]) {
    return false
  }
  // Destroying the index does not lose the latest state: chain
  // replay restores `a` but not the tombstoned `b`.
  ignore((store.write)("artifacts/index.bin", [0]))
  if artifact_repository_get(repo, "docs", "a") != None {
    return false
  }
  if artifact_repository_recover_chained(repo, expected_head=Some(head)) != 1 ||
    artifact_repository_get(repo, "docs", "a") != Some([9, 8]) ||
    artifact_repository_get(repo, "docs", "b") != None {
    return false
  }
  // Replaying an older chain against the latest index/head is
  // detected.
  let store2 = artifact_memory_byte_store_new()
  let repo2 = artifact_repository_new(store2)
  ignore(artifact_repository_put(repo2, "docs", "a", [4, 5, 6]))
  let old_chain = match (store2.read)("artifacts/chain.bin") {
    Some(v) => v
    None => return false
  }
  ignore(artifact_repository_put(repo2, "docs", "a", [7, 7]))
  let latest_head = match artifact_repository_chain_head(repo2) {
    Some(v) => v
    None => return false
  }
  ignore((store2.write)("artifacts/chain.bin", old_chain))
  if artifact_repository_chain_report(repo2).valid ||
    artifact_repository_recover_chained(repo2, expected_head=Some(latest_head)) !=
    -1 {
    return false
  }
  // Entry-level tampering (a record hash changed without
  // recomputing its entry digest) breaks the link check.
  let store3 = artifact_memory_byte_store_new()
  let repo3 = artifact_repository_new(store3)
  ignore(artifact_repository_put(repo3, "docs", "x", [1, 1, 1]))
  let entries = match artifact_repository_chain_entries(repo3) {
    Some(v) => v
    None => return false
  }
  let first = entries[0]
  let bad_record = ArtifactRecord::{
    kind: first.record.kind,
    name: first.record.name,
    blob_key: first.record.blob_key,
    byte_length: first.record.byte_length,
    hash_a: first.record.hash_a + 1,
    hash_b: first.record.hash_b,
    format_version: first.record.format_version,
  }
  entries[0] = ArtifactChainEntry::{
    sequence: first.sequence,
    removed: first.removed,
    record: bad_record,
    previous_a: first.previous_a,
    previous_b: first.previous_b,
    entry_a: first.entry_a,
    entry_b: first.entry_b,
  }
  if !artifact_chain_save(repo3, entries) ||
    artifact_repository_chain_report(repo3).valid {
    return false
  }
  // Blob tampering is caught against the chained record.
  let store4 = artifact_memory_byte_store_new()
  let repo4 = artifact_repository_new(store4)
  ignore(artifact_repository_put(repo4, "docs", "x", [1, 1, 1]))
  let record4 = match artifact_repository_record(repo4, "docs", "x") {
    Some(v) => v
    None => return false
  }
  ignore((store4.write)(record4.blob_key, [2, 1, 1]))
  if artifact_repository_chain_report(repo4).valid ||
    artifact_repository_get_chained(repo4, "docs", "x") != None {
    return false
  }
  // Legacy bootstrap: with the chain absent, the next put first
  // chains the indexed records, then appends itself.
  let store5 = artifact_memory_byte_store_new()
  let repo5 = artifact_repository_new(store5)
  ignore(artifact_repository_put(repo5, "docs", "a", [1]))
  ignore(artifact_repository_put(repo5, "docs", "b", [2]))
  ignore((store5.remove)("artifacts/chain.bin"))
  ignore(artifact_repository_put(repo5, "docs", "c", [3]))
  let migrated = artifact_repository_chain_report(repo5)
  migrated.valid && migrated.entries == 3 && migrated.live_records == 3
}
