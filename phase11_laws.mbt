// ---------------------------------------------------------------------------
// Phase 11 law checks backing the theorem registry.  Each function is
// the library-level form of the corresponding white-box test in
// `phase11_wbtest.mbt` / `face_sat_watched_wbtest.mbt`.
// ---------------------------------------------------------------------------

///|
fn phase11_copy_bytes(bytes : Array[Int32]) -> Array[Int32] {
  let out : Array[Int32] = []
  for i in 0..<bytes.length() {
    out.push(bytes[i])
  }
  out
}

///|
fn phase11_truncate_bytes(bytes : Array[Int32], keep : Int32) -> Array[Int32] {
  let out : Array[Int32] = []
  for i in 0..<keep {
    out.push(bytes[i])
  }
  out
}

///|
/// The schema registry persists to bytes and back: round trips are
/// exact, corruption/truncation/bad magic are rejected, and a
/// restored registry still validates fresh registrations.
pub fn check_schema_registry_byte_persistence() -> Bool {
  let registry = schema_registry_new()
  ignore(schema_registry_register_inductive(registry, nat_schema()))
  ignore(schema_registry_register_inductive(registry, list_schema()))
  ignore(schema_registry_register_inductive(registry, vec_schema()))
  ignore(schema_registry_register_hit(registry, circle_schema()))
  ignore(schema_registry_register_hit(registry, torus_schema()))
  if !schema_registry_binary_roundtrip_ok(registry) {
    return false
  }
  let bytes = schema_registry_to_binary(registry)
  let report = schema_registry_snapshot_load_binary_report(bytes)
  if report.status != ModuleBinaryOk {
    return false
  }
  let corrupted = phase11_copy_bytes(bytes)
  corrupted[bytes.length() - 1] = (corrupted[bytes.length() - 1] + 1) % 256
  if !(match schema_registry_snapshot_from_binary(corrupted) {
      Some(_) => false
      None => true
    }) {
    return false
  }
  let truncated = phase11_truncate_bytes(bytes, bytes.length() - 3)
  if !(match schema_registry_snapshot_from_binary(truncated) {
      Some(_) => false
      None => true
    }) {
    return false
  }
  let bad_magic = phase11_copy_bytes(bytes)
  bad_magic[0] = 88
  if schema_registry_snapshot_load_binary_report(bad_magic).status !=
    ModuleBinaryBadMagic {
    return false
  }
  match schema_registry_from_binary(bytes) {
    Some(restored) =>
      schema_registry_register_inductive(restored, nat_schema()).valid
    None => false
  }
}

///|
/// Global DTerm hash-consing: interning shares equal subterms,
/// preserves terms and cache keys exactly, rebuild inverts children
/// on compound shapes, and interned terms check and normalise
/// identically.
pub fn check_dterm_hash_consing() -> Bool {
  let arrow = DPi(DNatTy, DNatTy)
  let pair_ty = DSigma(arrow, arrow)
  let big = DSigma(pair_ty, DPi(pair_ty, pair_ty))
  let table = dterm_intern_table_new()
  let interned = dterm_intern(table, big)
  if interned != big {
    return false
  }
  if dterm_cache_key(interned) != dterm_cache_key(big) {
    return false
  }
  let tree = dterm_tree_node_count(big)
  let distinct = dterm_intern_table_size(table)
  if !(distinct < tree) {
    return false
  }
  if distinct != dterm_distinct_subterm_count(big) {
    return false
  }
  let arrow2 = DPi(DNatTy, DNatTy)
  let pair2 = DSigma(arrow2, arrow2)
  let big2 = DSigma(pair2, DPi(pair2, pair2))
  let (_, id1) = dterm_intern_id(table, big)
  let (_, id2) = dterm_intern_id(table, big2)
  if id1 != id2 {
    return false
  }
  if dterm_intern_table_size(table) != distinct {
    return false
  }
  let partial = DPartial([
    { face: FEq1(DVar(0)), body: DNatZero, },
    { face: FTop, body: DNatZero, },
  ])
  if dterm_rebuild(partial, dterm_children(partial)) != partial {
    return false
  }
  let elim = DInductiveElim(
    nat_schema(),
    DLam(DNatTy, DNatTy),
    [DNatZero, DLam(DNatTy, DLam(DNatTy, DTVar(0)))],
    [],
    [],
    DSucc(DNatZero),
  )
  if dterm_rebuild(elim, dterm_children(elim)) != elim {
    return false
  }
  if dterm_intern(table, elim) != elim {
    return false
  }
  let term = DApp(DLam(DNatTy, DSucc(DTVar(0))), DSucc(DNatZero))
  let interned_term = dterm_intern(table, term)
  if !dep_check_closed(term, DNatTy) {
    return false
  }
  if !dep_check_closed(interned_term, DNatTy) {
    return false
  }
  if dep_nf_closed(interned_term, DNatTy) != dep_nf_closed(term, DNatTy) {
    return false
  }
  dep_nf_closed(term, DNatTy) == Some(DSucc(DSucc(DNatZero)))
}

///|
/// The Face-valued agreement region keeps both interval endpoints
/// (where the BDD region necessarily drops the `1` endpoint), and
/// exact repair keeps the endpoint-disjunction face while removing
/// nothing at the vertex level.
pub fn check_face_agreement_and_exact_repair() -> Bool {
  let a = circle_point(DVar(0))
  let b = DVCirclePoint(DZero)
  let agreement = face_agreement_face(0, 1, FTop, DVCircleTy, a, b)
  if agreement == FTop {
    return false
  }
  if agreement == FBot {
    return false
  }
  if !face_holds(agreement, [false]) {
    return false
  }
  if !face_holds(agreement, [true]) {
    return false
  }
  if bdd_of_face(agreement, 1) != BddOne {
    return false
  }
  if !face_agreement_face_sound(0, 1, FTop, agreement, DVCircleTy, a, b) {
    return false
  }
  let region = face_agreement_region(0, 1, FTop, DVCircleTy, a, b)
  if region == BddOne {
    return false
  }
  if region != BddNode(0, BddOne, BddZero) {
    return false
  }
  if face_agreement_face(0, 1, FTop, DVNatTy, DVZeroNat, DVZeroNat) != FTop {
    return false
  }
  if face_agreement_face(0, 1, FTop, DVNatTy, DVZeroNat, dv_nat_lit(1)) != FBot {
    return false
  }
  let system = dsystem_of([tube_branch(FTop, _ => circle_point(DVar(0)))])
  let base = DVCirclePoint(DZero)
  let line = (_ : Dim) => DVCircleTy
  let exact = dsystem_repair_to_base_exact(0, 1, line, system, base)
  if exact.system.branches.length() != 1 {
    return false
  }
  let kept_face = exact.system.branches[0].face
  if kept_face == FTop {
    return false
  }
  if !face_holds(kept_face, [false]) {
    return false
  }
  if !face_holds(kept_face, [true]) {
    return false
  }
  if exact.base_removed_region != BddZero {
    return false
  }
  let bdd_repair = dsystem_repair_to_base(0, 1, line, system, base)
  if bdd_repair.system.branches.length() != 1 {
    return false
  }
  let bdd_face = bdd_repair.system.branches[0].face
  if !face_holds(bdd_face, [false]) {
    return false
  }
  !face_holds(bdd_face, [true])
}

///|
/// Open boxes over host-opaque cubes validate, fill and cap on
/// compatible boundaries; incompatible and incomplete boxes are
/// rejected with witnesses.
pub fn check_dcube_open_box_filler() -> Bool {
  let loop_cube = dcube_of_path(d => circle_point(d))
  let const_base = dcube_of_path(_ => DVCirclePoint(DZero))
  let box = dcube_open_box(DVCircleTy, 2, 0, [
    dcube_box_face(0, false, loop_cube),
    dcube_box_face(0, true, loop_cube),
    dcube_box_face(1, false, const_base),
  ])
  let report = dcube_box_validate(box, 0)
  if !report.complete {
    return false
  }
  if !report.overlaps_ok {
    return false
  }
  match dcube_box_fill_verified(box, 0) {
    Some(filler) => if !dcube_filler_faces_ok(box, filler, 0) { return false }
    None => return false
  }
  match dcube_box_cap(box) {
    Some(cap) => {
      if !conv_at(
          0,
          0,
          DVCircleTy,
          dcube_at(cap, [DZero]),
          DVCirclePoint(DZero),
        ) {
        return false
      }
      if !conv_at(0, 0, DVCircleTy, dcube_at(cap, [DOne]), DVCirclePoint(DZero)) {
        return false
      }
    }
    None => return false
  }
  let one_path = dcube_of_path(_ => dv_nat_lit(1))
  let zero_path = dcube_of_path(_ => DVZeroNat)
  let bad_box = dcube_open_box(DVNatTy, 2, 0, [
    dcube_box_face(0, false, one_path),
    dcube_box_face(0, true, one_path),
    dcube_box_face(1, false, zero_path),
  ])
  let bad_report = dcube_box_validate(bad_box, 0)
  if !bad_report.complete {
    return false
  }
  if bad_report.overlaps_ok {
    return false
  }
  if bad_report.failed_overlaps < 1 {
    return false
  }
  if !(match dcube_box_fill_verified(bad_box, 0) {
      Some(_) => false
      None => true
    }) {
    return false
  }
  let zero_square = dcube_constant(2, DVZeroNat)
  let cube3 = dcube_open_box(DVNatTy, 3, 0, [
    dcube_box_face(0, false, zero_square),
    dcube_box_face(0, true, zero_square),
    dcube_box_face(1, false, zero_square),
    dcube_box_face(1, true, zero_square),
    dcube_box_face(2, false, zero_square),
  ])
  match dcube_box_fill_verified(cube3, 0) {
    Some(filler) =>
      if !dv_is_nat(dcube_at(filler, [DZero, DZero, DZero]), 0) {
        return false
      }
    None => return false
  }
  let open_box = dcube_open_box(DVNatTy, 2, 0, [
    dcube_box_face(1, false, zero_path),
  ])
  if dcube_box_complete(open_box) {
    return false
  }
  match dcube_box_fill(open_box) {
    Some(_) => false
    None => true
  }
}

///|
/// Composition in the primitive circle and torus computes on
/// point-valued tubes (De Morgan selection), while non-point tubes
/// stay formal.
pub fn check_circle_torus_point_comp() -> Bool {
  let circle_line = (_ : Dim) => DVCircleTy
  let base_pt = DVCirclePoint(DZero)
  let system = dsystem_of([
    tube_branch(FEq1(DVar(0)), (j : Dim) => {
      circle_point(dim_simplify(DAnd(j, DVar(0))))
    }),
  ])
  let cap = comp_value(circle_line, system, base_pt, 1)
  if !(match force_value(cap) {
      DVCirclePoint(_) => true
      _ => false
    }) {
    return false
  }
  if !conv_at(0, 1, DVCircleTy, cap, circle_point(DVar(0))) {
    return false
  }
  let filler = hfill_value(DVCircleTy, system, base_pt, 1)
  if !conv_at(0, 1, DVCircleTy, filler(DZero), base_pt) {
    return false
  }
  if !(match force_value(filler(DVar(1))) {
      DVCirclePoint(_) => true
      _ => false
    }) {
    return false
  }
  let torus_line = (_ : Dim) => DVTorusTy
  let torus_system = dsystem_of([
    tube_branch(FEq1(DVar(0)), (j : Dim) => {
      torus_point(dim_simplify(DAnd(j, DVar(0))), DZero)
    }),
  ])
  let torus_cap = comp_value(
    torus_line,
    torus_system,
    DVTorusPoint(DZero, DZero),
    1,
  )
  if !(match force_value(torus_cap) {
      DVTorusPoint(_, _) => true
      _ => false
    }) {
    return false
  }
  if !conv_at(0, 1, DVTorusTy, torus_cap, torus_point(DVar(0), DZero)) {
    return false
  }
  let stuck_system = dsystem_of([
    tube_branch(FEq1(DVar(0)), _ => DVNeutral(DNVar(0))),
  ])
  let stuck = comp_value(circle_line, stuck_system, base_pt, 1)
  if !(match force_value(stuck) {
      DVNeutral(DNComp(_, _, _)) => true
      _ => false
    }) {
    return false
  }
  let base_system = dsystem_of([tube_branch(FEq0(DVar(0)), _ => base_pt)])
  if !conv_at(
      0,
      1,
      DVCircleTy,
      comp_value(circle_line, base_system, base_pt, 1),
      base_pt,
    ) {
    return false
  }
  if !dim_eq_sem(dim_of_face(FEq0(DVar(0))), DNeg(DVar(0))) {
    return false
  }
  dim_eq_sem(
    dim_of_face(FAnd(FEq1(DVar(0)), FEq0(DVar(1)))),
    DAnd(DVar(0), DNeg(DVar(1))),
  )
}

///|
/// Exact optimal BDD variable ordering (all permutations up to the
/// variable cap) beats blocked orders and sifting, preserves
/// semantics, and reports non-exactness honestly above the cap.
pub fn check_bdd_optimal_order_exact() -> Bool {
  let pair = (a : Int32, b : Int32) => FAnd(FEq1(DVar(a)), FEq1(DVar(b)))
  let f = FOr(pair(0, 3), FOr(pair(1, 4), pair(2, 5)))
  let opt = bdd_dag_of_face_optimal(f, 6)
  if !opt.exact {
    return false
  }
  if opt.tried != 720 {
    return false
  }
  let blocked_manager = bdd_manager_with_order([0, 1, 2, 3, 4, 5], 6)
  let blocked_root = bdd_dag_build_face(blocked_manager, f)
  let blocked_size = bdd_dag_reachable_count(blocked_manager, blocked_root)
  if !(opt.size < blocked_size) {
    return false
  }
  let sifted = bdd_dag_of_face_optimized(f, 6)
  if sifted.reachable < opt.size {
    return false
  }
  for mask in 0..<64 {
    let env : Array[Bool] = []
    for i in 0..<6 {
      let bit = (mask >> i) & 1
      env.push(bit == 1)
    }
    if bdd_dag_eval(opt.built.manager, opt.built.root, env) !=
      face_holds(f, env) {
      return false
    }
  }
  let big = bdd_dag_of_face_optimal(f, 6, exact_max_vars=4)
  !big.exact
}

///|
/// The family (`DFunctorFamily`) functor node persists through the
/// registry bytes and the v2 module format, and the legacy v1
/// writer refuses it.
pub fn check_family_functor_persistence() -> Bool {
  let rose = dinductive_spec(
    "FamRoseTreeS",
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
  let registry = schema_registry_new()
  ignore(schema_registry_register_inductive(registry, rose))
  if !schema_registry_binary_roundtrip_ok(registry) {
    return false
  }
  let module_ = module_def("Demo.FamRose", decls=[
    module_decl("RoseBool", DUniv(0), DInductive(rose, [DBoolTy])),
  ])
  let compiled = match module_compile(module_env_new(), module_, []) {
    Some(v) => v
    None => return false
  }
  let bytes = compiled_module_to_binary(compiled)
  if compiled_module_binary_version_of(bytes) != 3 {
    return false
  }
  match compiled_module_load_binary(bytes) {
    Some(back) => if back != compiled { return false }
    None => return false
  }
  compiled_module_to_binary_v1(compiled) == None
}

///|
fn phase11_random_face(seed0 : Int32, n : Int32) -> Face {
  let mut seed = seed0
  let next = () => {
    seed = (seed * 1103515245 + 12345) & 2147483647
    seed
  }
  let literal = () => {
    let v = next() % n
    if next() % 2 == 0 {
      FEq1(DVar(v))
    } else {
      FEq0(DVar(v))
    }
  }
  let mut out = literal()
  for _i in 0..<18 {
    let clause = FOr(literal(), FOr(literal(), literal()))
    out = if next() % 5 == 0 { FOr(out, clause) } else { FAnd(out, clause) }
  }
  out
}

///|
fn phase11_pigeonhole_face(pigeons : Int32, holes : Int32) -> (Face, Int32) {
  let lit = (index : Int32, positive : Bool) => {
    if positive {
      FEq1(DVar(index))
    } else {
      FEq0(DVar(index))
    }
  }
  let mut out : Face = FTop
  let mut started = false
  let conjoin = (clause : Face) => {
    out = if started { FAnd(out, clause) } else { clause }
    started = true
  }
  for pigeon in 0..<pigeons {
    let mut clause = lit(pigeon * holes, true)
    for h in 1..<holes {
      clause = FOr(clause, lit(pigeon * holes + h, true))
    }
    conjoin(clause)
  }
  for h in 0..<holes {
    for p1 in 0..<pigeons {
      for p2 in (p1 + 1)..<pigeons {
        conjoin(FOr(lit(p1 * holes + h, false), lit(p2 * holes + h, false)))
      }
    }
  }
  (out, pigeons * holes)
}

///|
/// CDCL with 1-UIP clause learning agrees with brute force on
/// generated faces, uses the standard Luby restart sequence, and
/// engages learning on pigeonhole instances.
pub fn check_cdcl_clause_learning() -> Bool {
  let expected_Luby = [1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8]
  for i in 0..<expected_Luby.length() {
    if cdcl_Luby(i) != expected_Luby[i] {
      return false
    }
  }
  let n = 7
  for seed in 1..<80 {
    let f = phase11_random_face(seed * 7919, n)
    let mut brute_sat = false
    for mask in 0..<pow2(n) {
      if face_holds(f, assignment_of_mask(mask, n)) {
        brute_sat = true
      }
    }
    match face_sat_cdcl(f, n, max_steps=100000) {
      FaceSat(env) => if !(brute_sat && face_holds(f, env)) { return false }
      FaceUnsat => if brute_sat { return false }
      FaceSearchBudgetExceeded => return false
    }
    let g = phase11_random_face(seed * 104729 + 17, n)
    let mut brute_eq = true
    for mask in 0..<pow2(n) {
      let env = assignment_of_mask(mask, n)
      if face_holds(f, env) != face_holds(g, env) {
        brute_eq = false
      }
    }
    match face_eq_cdcl(f, g, n, max_steps=100000) {
      FaceDecided(eq) => if eq != brute_eq { return false }
      FaceBudgetExceeded => return false
    }
  }
  let (php, pvars) = phase11_pigeonhole_face(6, 5)
  let cdcl = face_sat_cdcl_report(php, pvars, max_steps=2000000)
  if cdcl.decision != FaceUnsat {
    return false
  }
  if cdcl.stats.learned <= 0 {
    return false
  }
  if cdcl.stats.conflicts <= 0 {
    return false
  }
  let (php_sat, svars) = phase11_pigeonhole_face(5, 5)
  match face_sat_cdcl(php_sat, svars, max_steps=2000000) {
    FaceSat(env) => face_holds(php_sat, env)
    _ => false
  }
}
