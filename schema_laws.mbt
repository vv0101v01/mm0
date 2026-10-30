// Behavioural laws for generated inductive schemas and semantic systems.

///|
pub fn check_schema_validation() -> Bool {
  let examples = schema_examples()
  for i in 0..<examples.length() {
    if !inductive_schema_validate(examples[i]) {
      return false
    }
  }
  // A same-named family in an external (negative/ambient) argument is
  // rejected by the strict-positivity scan.
  let bad_base = dinductive_spec("BadS", 0, [], [], [])
  let bad = dinductive_spec("BadS", 0, [], [], [
    dconstructor_spec("mk", [
      darg_external("x", DPi(schema_type_term(bad_base, []), DBoolTy)),
    ]),
  ])
  if inductive_schema_validate(bad) {
    return false
  }
  // A parameter telescope entry that is not a type is also rejected
  // (rather than silently elaborating to Unit).
  let bad_telescope = dinductive_spec(
    "BadTelescopeS",
    0,
    [dtelescope_entry("x", DPair(DBoolTy, DBoolTy))],
    [],
    [dconstructor_spec("mk", [])],
  )
  !inductive_schema_validate(bad_telescope)
}

///|
pub fn check_schema_nat_add() -> Bool {
  let spec = nat_schema()
  let nat_s = schema_type_term(spec, [])
  let motive = DLam(nat_s, DPi(nat_s, nat_s))
  let zero_case = DLam(nat_s, DTVar(0))
  let succ_case = DLam(
    nat_s,
    DLam(
      DPi(nat_s, nat_s),
      DLam(nat_s, schema_intro_term(spec, 1, [], [DApp(DTVar(1), DTVar(0))])),
    ),
  )
  let add = DLam(
    nat_s,
    DLam(
      nat_s,
      DApp(
        schema_elim_term(spec, motive, [zero_case, succ_case], [], [], DTVar(1)),
        DTVar(0),
      ),
    ),
  )
  let sum = DApp(DApp(add, nat_schema_lit(2)), nat_schema_lit(1))
  if dep_nf_closed(sum, nat_s) != Some(nat_schema_lit(3)) {
    return false
  }
  true
}

///|
pub fn check_schema_nat_neutral_quote() -> Bool {
  let spec = nat_schema()
  // The generated eliminator is stuck, and quoted, on a neutral.
  let stuck = eval_inductive_elim(
    spec,
    (_, _) => nat_s_value(),
    [integer_nat_value(0), DVLam(_ => DVLam(x => x))],
    [],
    [],
    DVNeutral(DNVar(0)),
    0,
  )
  if !conv_at(1, 0, nat_s_value(), stuck, stuck) {
    return false
  }
  match quote_at(1, 0, nat_s_value(), stuck) {
    DInductiveElim(_, _, _, _, _, DTVar(0)) => true
    _ => false
  }
}

///|
fn nat_s_value() -> DValue {
  DVInductive(nat_schema(), [], [])
}

///|
pub fn check_schema_list() -> Bool {
  // ListS Bool: generated length by dependent elimination.
  let list_spec = list_schema()
  let list_bool = schema_type_term(list_spec, [DBoolTy])
  let nil = schema_intro_term(list_spec, 0, [DBoolTy], [])
  let cons = (x : DTerm, xs : DTerm) => {
    schema_intro_term(list_spec, 1, [DBoolTy], [x, xs])
  }
  let xs = cons(DBoolLit(true), cons(DBoolLit(false), nil))
  let length = schema_elim_term(
    list_spec,
    DLam(list_bool, DNatTy),
    [DNatZero, DLam(DBoolTy, DLam(list_bool, DLam(DNatTy, DSucc(DTVar(0)))))],
    [DBoolTy],
    [],
    xs,
  )
  if dep_nf_closed(length, DNatTy) != Some(d_nat_lit(2)) {
    return false
  }
  true
}

///|
pub fn check_schema_tree() -> Bool {
  // TreeS Bool: semantic leaf count.
  let tree_spec = tree_schema()
  let leaf : DValue = DVIntro(tree_spec, 0, [DVBoolTy], [DVBool(true)])
  let tree : DValue = DVIntro(tree_spec, 1, [DVBoolTy], [leaf, leaf])
  let leaves = eval_inductive_elim(
    tree_spec,
    (_, _) => DVNatTy,
    [
      DVLam(_ => dv_nat_lit(1)),
      DVLam(_ => DVLam(l => DVLam(_ => DVLam(r => dv_nat_plus(l, r))))),
    ],
    [DVBoolTy],
    [],
    tree,
    0,
  )
  if !dv_is_nat(leaves, 2) {
    return false
  }
  true
}

///|
pub fn check_schema_w() -> Bool {
  // WS: the function-recursive argument generates a Pi induction
  // hypothesis, but a case that returns the label need not force any
  // branch of a neutral branching function.
  let w_spec = w_schema()
  let branching : DValue = DVLam(_ => DVBoolTy)
  let w_params : Array[DValue] = [DVBoolTy, branching]
  let branches : DValue = DVLam(_ => DVNeutral(DNVar(0)))
  let node : DValue = DVIntro(w_spec, 0, w_params, [DVBool(true), branches])
  let label = eval_inductive_elim(
    w_spec,
    (_, _) => DVBoolTy,
    [DVLam(x => DVLam(_ => DVLam(_ => x)))],
    w_params,
    [],
    node,
    0,
  )
  if !dv_is_bool_dep(label, true) {
    return false
  }
  match inductive_case_type(w_spec, (_, _) => DVBoolTy, w_params, 0) {
    DVPi(_, fam) =>
      match fam(DVBool(true)) {
        DVPi(_, fam2) =>
          match fam2(branches) {
            DVPi(DVPi(_, _), _) => true
            _ => false
          }
        _ => false
      }
    _ => false
  }
}

///|
fn dv_nat_plus(a : DValue, b : DValue) -> DValue {
  match force_value(a) {
    DVZeroNat => b
    DVSucc(n) => DVSucc(dv_nat_plus(n, b))
    _ => DVZeroNat
  }
}

///|
pub fn check_schema_indexed() -> Bool {
  let vec_spec = vec_schema()
  let vec_bool = (n : DTerm) => schema_type_term(vec_spec, [DBoolTy, n])
  let nil = schema_intro_term(vec_spec, 0, [DBoolTy], [])
  let one = schema_intro_term(vec_spec, 1, [DBoolTy], [
    DBoolLit(true),
    DNatZero,
    nil,
  ])
  let two = schema_intro_term(vec_spec, 1, [DBoolTy], [
    DBoolLit(false),
    d_nat_lit(1),
    one,
  ])
  if !dep_check_closed(two, vec_bool(d_nat_lit(2))) ||
    dep_check_closed(two, vec_bool(d_nat_lit(1))) {
    return false
  }
  let motive = DLam(DNatTy, DLam(vec_bool(DTVar(0)), DNatTy))
  let cons_case = DLam(
    DBoolTy,
    DLam(DNatTy, DLam(vec_bool(DTVar(0)), DLam(DNatTy, DSucc(DTVar(2))))),
  )
  let length = schema_elim_term(
    vec_spec,
    motive,
    [DNatZero, cons_case],
    [DBoolTy],
    [d_nat_lit(2)],
    two,
  )
  if dep_nf_closed(length, DNatTy) != Some(d_nat_lit(2)) {
    return false
  }
  // FinS: fsucc(fzero) inhabits Fin 2 but not Fin 1.
  let fin_spec = fin_schema()
  let fin = (n : DTerm) => schema_type_term(fin_spec, [n])
  let fz = schema_intro_term(fin_spec, 0, [], [DNatZero])
  let fs = schema_intro_term(fin_spec, 1, [], [d_nat_lit(1), fz])
  dep_check_closed(fs, fin(d_nat_lit(2))) &&
  !dep_check_closed(fs, fin(d_nat_lit(1)))
}

///|
pub fn check_generated_inductive_schemas() -> Bool {
  check_schema_validation() &&
  check_schema_nat_add() &&
  check_schema_nat_neutral_quote() &&
  check_schema_list() &&
  check_schema_tree() &&
  check_schema_w() &&
  check_schema_indexed() &&
  check_schema_inductive_comp() &&
  check_schema_vec_comp()
}

///|
pub fn check_schema_inductive_comp() -> Bool {
  let one = integer_nat_value(1)
  let composed = hcomp_value(
    nat_s_value(),
    dsystem_singleton(FEq0(DVar(0)), _ => one),
    one,
    1,
  )
  if !conv_at(0, 1, nat_s_value(), composed, one) {
    return false
  }
  match
    hcomp_value(
      nat_s_value(),
      dsystem_singleton(FEq0(DVar(0)), _ => integer_nat_value(0)),
      one,
      1,
    ) {
    DVNeutral(DNHComp(_, _, _)) => ()
    _ => return false
  }
  // ListS: cons composition recurses into the tail.
  let list_spec = list_schema()
  let xs : DValue = DVIntro(list_spec, 1, [DVBoolTy], [
    DVBool(true),
    DVIntro(list_spec, 0, [DVBoolTy], []),
  ])
  let list_ty : DValue = DVInductive(list_spec, [DVBoolTy], [])
  let list_out = hcomp_value(
    list_ty,
    dsystem_singleton(FEq0(DVar(0)), _ => xs),
    xs,
    1,
  )
  conv_at(0, 1, list_ty, list_out, xs)
}

///|
pub fn check_hit_schema_validation() -> Bool {
  let examples = hit_schema_examples()
  for i in 0..<examples.length() {
    if !hit_schema_validate(examples[i]) {
      return false
    }
  }
  let broken = dhit_spec("BrokenS", 0, [], [], [
    dhit_cell_spec("loop", 1, [], [dhit_face(0, [], [])]),
  ])
  !hit_schema_validate(broken)
}

///|
pub fn check_hit_schema_circle_segment() -> Bool {
  let circle = circle_schema()
  let circle_ty = DHitType(circle, [])
  let base = hit_intro_term(circle, 0, [], [], [])
  let loop0 = hit_intro_term(circle, 1, [], [], [DZero])
  if dep_nf_closed(loop0, circle_ty) != Some(base) {
    return false
  }
  // Eliminating the generated loop into Bool under a dimension binder.
  let loop_path = DLamDim(hit_intro_term(circle, 1, [], [], [DVar(0)]))
  let _ = loop_path
  let elim_loop = DLamDim(
    hit_elim_term(
      circle,
      DLam(circle_ty, DBoolTy),
      [DBoolLit(true), DLamDim(DBoolLit(true))],
      [],
      [],
      hit_intro_term(circle, 1, [], [], [DVar(0)]),
    ),
  )
  let path_bool = DPath(DBoolTy, DBoolLit(true), DBoolLit(true))
  if dep_nf_closed(elim_loop, path_bool) != Some(DLamDim(DBoolLit(true))) {
    return false
  }
  // A segment has distinct endpoints.  Use the identity eliminator:
  // eliminating into Bool with distinct endpoint values would be a
  // nonconstant Bool path, which correctly does not typecheck.
  let segment = segment_schema()
  let segment_ty = DHitType(segment, [])
  let left = hit_intro_term(segment, 0, [], [], [])
  let right = hit_intro_term(segment, 1, [], [], [])
  if dep_nf_closed(hit_intro_term(segment, 2, [], [], [DZero]), segment_ty) !=
    Some(left) ||
    dep_nf_closed(hit_intro_term(segment, 2, [], [], [DOne]), segment_ty) !=
    Some(right) {
    return false
  }
  let elim_segment = DLamDim(
    hit_elim_term(
      segment,
      DLam(segment_ty, segment_ty),
      [left, right, DLamDim(hit_intro_term(segment, 2, [], [], [DVar(0)]))],
      [],
      [],
      hit_intro_term(segment, 2, [], [], [DVar(0)]),
    ),
  )
  dep_nf_closed(elim_segment, DPath(segment_ty, left, right)) ==
  Some(DLamDim(hit_intro_term(segment, 2, [], [], [DVar(0)])))
}

///|
pub fn check_hit_schema_torus_comp() -> Bool {
  let torus = torus_schema()
  let stuck = eval_hit_elim(
    torus,
    (_, _) => DVBoolTy,
    [
      DVBool(true),
      DVPathLam(_ => DVBool(true)),
      DVPathLam(_ => DVBool(true)),
      DVPathLam(_ => DVPathLam(_ => DVBool(true))),
    ],
    [],
    [],
    DVNeutral(DNVar(0)),
    0,
  )
  if !conv_at(1, 0, DVBoolTy, stuck, stuck) {
    return false
  }
  match quote_at(1, 0, DVBoolTy, stuck) {
    DHitElim(_, _, _, _, _, DTVar(0)) => ()
    _ => return false
  }
  let torus_ty : DValue = DVHitType(torus, [], [])
  let square : DValue = DVHitCell(torus, 3, [], [], [DVar(0), DVar(1)])
  let out = eval_hit_elim(
    torus,
    (_, _) => DVBoolTy,
    [
      DVBool(true),
      DVPathLam(_ => DVBool(true)),
      DVPathLam(_ => DVBool(true)),
      DVPathLam(_ => DVPathLam(_ => DVBool(true))),
    ],
    [],
    [],
    square,
    2,
  )
  if !dv_is_bool_dep(out, true) {
    return false
  }
  // HIT composition computes for a constant cell/dimension system and
  // stays formal for a genuinely moving loop system.
  let loop_point : DValue = DVHitCell(torus, 1, [], [], [DVar(0)])
  let same = hcomp_value(
    torus_ty,
    dsystem_singleton(FEq0(DVar(1)), _ => loop_point),
    loop_point,
    2,
  )
  if !conv_at(0, 2, torus_ty, same, loop_point) {
    return false
  }
  match
    hcomp_value(
      torus_ty,
      dsystem_singleton(FEq1(DVar(0)), _ => loop_point),
      DVHitCell(torus, 0, [], [], []),
      1,
    ) {
    DVNeutral(DNHComp(_, _, _)) => true
    _ => false
  }
}

///|
pub fn check_generated_hit_schemas() -> Bool {
  check_hit_schema_validation() &&
  check_hit_schema_circle_segment() &&
  check_hit_schema_torus_comp() &&
  check_hit_endpoint_conversion() &&
  check_hit_schema_arguments()
}

///|
pub fn check_hit_endpoint_conversion() -> Bool {
  let circle = circle_schema()
  let ty : DValue = DVHitType(circle, [], [])
  let endpoint : DValue = DVHitCell(circle, 1, [], [], [DZero])
  let base : DValue = DVHitCell(circle, 0, [], [], [])
  conv_at(0, 0, ty, endpoint, base) &&
  quote_at(0, 0, ty, endpoint) == hit_intro_term(circle, 0, [], [], [])
}

///|
pub fn check_schema_vec_comp() -> Bool {
  let spec = vec_schema()
  let nil : DValue = DVIntro(spec, 0, [DVBoolTy], [])
  let one : DValue = DVIntro(spec, 1, [DVBoolTy], [DVBool(true), DVZeroNat, nil])
  let ty : DValue = DVInductive(spec, [DVBoolTy], [dv_nat_lit(1)])
  let out = hcomp_value(ty, dsystem_singleton(FEq0(DVar(0)), _ => one), one, 1)
  conv_at(0, 1, ty, out, one)
}

///|
pub fn check_hit_schema_arguments() -> Bool {
  // A labelled loop: both faces must instantiate the point cell with
  // the *same* label carried by the path cell.
  let spec = dhit_spec("LabelledLoopS", 0, [], [], [
    dhit_cell_spec("point", 0, [darg_external("label", DBoolTy)], []),
    dhit_cell_spec("loop", 1, [darg_external("label", DBoolTy)], [
      dhit_face(0, [DTVar(0)], []),
      dhit_face(0, [DTVar(0)], []),
    ]),
  ])
  if !hit_schema_validate(spec) {
    return false
  }
  let ty = DHitType(spec, [])
  let point = hit_intro_term(spec, 0, [], [DBoolLit(true)], [])
  if dep_nf_closed(hit_intro_term(spec, 1, [], [DBoolLit(true)], [DOne]), ty) !=
    Some(point) {
    return false
  }
  let elim_loop = DLamDim(
    hit_elim_term(
      spec,
      DLam(ty, DBoolTy),
      [DLam(DBoolTy, DTVar(0)), DLam(DBoolTy, DLamDim(DTVar(0)))],
      [],
      [],
      hit_intro_term(spec, 1, [], [DBoolLit(true)], [DVar(0)]),
    ),
  )
  if dep_nf_closed(elim_loop, DPath(DBoolTy, DBoolLit(true), DBoolLit(true))) !=
    Some(DLamDim(DBoolLit(true))) {
    return false
  }
  // An indexed labelled loop: face result indices must agree.
  let indexed = dhit_spec(
    "IndexedLoopS",
    0,
    [],
    [dtelescope_entry("index", DNatTy)],
    [
      dhit_cell_spec("point", 0, [darg_external("index", DNatTy)], [], result_index=[
        DTVar(0),
      ]),
      dhit_cell_spec(
        "loop",
        1,
        [darg_external("index", DNatTy)],
        [dhit_face(0, [DTVar(0)], []), dhit_face(0, [DTVar(0)], [])],
        result_index=[DTVar(0)],
      ),
    ],
  )
  if !hit_schema_validate(indexed) {
    return false
  }
  let indexed_ty = DHitType(indexed, [d_nat_lit(1)])
  let indexed_point = hit_intro_term(indexed, 0, [], [d_nat_lit(1)], [])
  dep_nf_closed(
    hit_intro_term(indexed, 1, [], [d_nat_lit(1)], [DZero]),
    indexed_ty,
  ) ==
  Some(indexed_point) &&
  !dep_check_closed(indexed_point, DHitType(indexed, [d_nat_lit(2)]))
}
