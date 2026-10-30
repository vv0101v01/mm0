// Behavioural laws for persistent environments, lazy semantic values,
// memoized lines/families, canonical DSystems and multi-branch Glue.

///|
pub fn check_persistent_env_lazy_cache() -> Bool {
  let env = denv_extend([DVBool(true), dv_nat_lit(2)], denv_empty())
  if denv_len(env) != 2 {
    return false
  }
  let env_values = denv_to_array(env)
  if env_values.length() != 2 || !dv_is_nat(env_values[0], 2) {
    return false
  }
  let denv_dims = ddim_from_array([DZero, DOne])
  if ddim_to_array(denv_dims) != [DZero, DOne] ||
    ddim_at(denv_dims, 1) != Some(DOne) {
    return false
  }
  match (denv_at(env, 0), denv_at(env, 1), denv_at(denv_tail(env), 0)) {
    (Some(x), Some(y), Some(z)) =>
      if !dv_is_nat(x, 2) ||
        !dv_is_bool_dep(y, true) ||
        !dv_is_bool_dep(z, true) {
        return false
      }
    _ => return false
  }
  // A thunk is forced at most once; an unused function argument is
  // not forced at all.
  let thunk = lazy_value(() => DVBool(true))
  if lazy_force_count(thunk) != 0 || lazy_is_forced(thunk) {
    return false
  }
  let _ = force_value(thunk)
  let _ = force_value(thunk)
  if lazy_force_count(thunk) != 1 || !lazy_is_forced(thunk) {
    return false
  }
  let unused_arg = lazy_value(() => DVBool(false))
  let answer = dapp_typed(DVLam(_ => DVBool(true)), unused_arg, DVBoolTy)
  if !dv_is_bool_dep(answer, true) || lazy_force_count(unused_arg) != 0 {
    return false
  }
  // Memoized dimension lines and families are extensionally stable
  // under repeated and syntactically different equal arguments.
  let line = memo_dim_line(d => {
    match dim_simplify(d) {
      DOne => DVNatTy
      _ => DVBoolTy
    }
  })
  if !conv_ty(0, 0, line(DAnd(DOne, DOne)), DVNatTy) ||
    !conv_ty(0, 0, line(DZero), DVBoolTy) {
    return false
  }
  let fam = memo_family(
    x => if dv_is_bool_dep(x, true) { DVNatTy } else { DVBoolTy },
    DVBoolTy,
    0,
    0,
  )
  conv_ty(0, 0, fam(DVBool(true)), DVNatTy) &&
  conv_ty(0, 0, fam(DVBool(true)), DVNatTy) &&
  conv_ty(0, 0, fam(DVBool(false)), DVBoolTy)
}

///|
pub fn check_dsystem_canonical_partial_nf() -> Bool {
  let system = dsystem_of([
    tube_branch(FEq0(DVar(0)), _ => dv_nat_lit(1)),
    tube_branch(FBot, _ => dv_nat_lit(0)),
    tube_branch(FEq1(DVar(0)), _ => dv_nat_lit(1)),
    tube_branch(FEq0(DVar(0)), _ => dv_nat_lit(0)),
  ])
  let canon = dsystem_canonical(0, 1, _ => DVNatTy, system)
  if canon.branches.length() != 2 {
    return false
  }
  let recanon = dsystem_canonical(0, 1, _ => DVNatTy, canon)
  if recanon.branches.length() != 2 ||
    !face_is_top_sem(dsystem_domain_face(canon)) {
    return false
  }
  // Neutral comp conversion sees through merging/reordering.
  let formal_a : DValue = DVNeutral(DNComp(_ => DVNatTy, system, dv_nat_lit(0)))
  let formal_b : DValue = DVNeutral(
    DNComp(
      _ => DVNatTy,
      dsystem_of([
        tube_branch(FEq0(DVar(0)), _ => dv_nat_lit(0)),
        tube_branch(FTop, _ => dv_nat_lit(1)),
      ]),
      dv_nat_lit(0),
    ),
  )
  if !conv_at(0, 1, DVNatTy, formal_a, formal_b) {
    return false
  }
  // First-match effective regions: x=0 and x=1 already cover the cube,
  // so the later top branch is semantically invisible and the two
  // zero branches merge into one BDD class.
  let partial = partial_of([
    dface_value(FEq0(DVar(0)), dv_nat_lit(0)),
    dface_value(FEq1(DVar(0)), dv_nat_lit(0)),
    dface_value(FTop, dv_nat_lit(1)),
  ])
  let nf = partial_normal_form(0, 1, DVNatTy, partial)
  if nf.classes.length() != 1 || nf.undefined != BddZero {
    return false
  }
  let empty_nf = partial_normal_form(0, 1, DVNatTy, partial_empty())
  if empty_nf.classes.length() != 0 || empty_nf.undefined != BddOne {
    return false
  }
  let singleton = partial_singleton(FEq0(DVar(0)), dv_nat_lit(0))
  if partial_domain_bdd(singleton, 1) != bdd_of_face(FEq0(DVar(0)), 1) {
    return false
  }
  let sampled = tube_system_nf_at(0, 1, _ => DVNatTy, canon, DZero)
  if sampled.classes.length() == 0 {
    return false
  }
  let reordered = partial_of([
    dface_value(FEq1(DVar(0)), dv_nat_lit(0)),
    dface_value(FEq0(DVar(0)), dv_nat_lit(0)),
  ])
  partial_eq_at(0, 1, DVNatTy, partial, reordered)
}

///|
pub fn check_multibranch_glue_partial() -> Bool {
  // AST level: a two-branch Glue type and a matching DPartial value.
  // The second branch body is an identity Glue line, so the two type
  // paths have the same Bool cap but are not convertible generically;
  // canonicalisation therefore rightly keeps both branches.
  let glue_line = DHComp(DUniv(0), [d_tube(FEq1(DVar(0)), DBoolTy)], DBoolTy)
  let glue_ty = DHComp(
    DUniv(0),
    [d_tube(FEq0(DVar(0)), DBoolTy), d_tube(FEq1(DVar(0)), glue_line)],
    DBoolTy,
  )
  let good = DPair(
    DPartial([
      d_face_term(FEq0(DVar(0)), DBoolLit(true)),
      d_face_term(FEq1(DVar(0)), DBoolLit(true)),
    ]),
    DBoolLit(true),
  )
  let bad = DPair(
    DPartial([
      d_face_term(FEq0(DVar(0)), DBoolLit(true)),
      d_face_term(FEq1(DVar(0)), DBoolLit(false)),
    ]),
    DBoolLit(true),
  )
  if !dep_check_closed(good, glue_ty) || dep_check_closed(bad, glue_ty) {
    return false
  }
  // Semantic level: DVGlue retains both branches and quotes the
  // partial component as DPartial rather than dropping branch two.
  let glue_value : DValue = DVGlue(
    dsystem_of([
      tube_branch(FEq0(DVar(0)), _ => DVBoolTy),
      tube_branch(FEq1(DVar(0)), _ => DVBoolTy),
    ]),
    DVBoolTy,
    0,
  )
  match as_glue(glue_value) {
    Some(g) => if g.system.branches.length() != 2 { return false }
    None => return false
  }
  let stored : DValue = DVPair(
    DVPartial(
      partial_of([
        dface_value(FEq0(DVar(0)), DVBool(true)),
        dface_value(FEq1(DVar(0)), DVBool(true)),
      ]),
    ),
    DVBool(true),
  )
  match quote_at(0, 1, glue_value, stored) {
    DPair(DPartial(branches), DBoolLit(true)) => branches.length() == 2
    _ => false
  }
}

///|
pub fn check_phase5_semantic_systems() -> Bool {
  check_persistent_env_lazy_cache() &&
  check_dsystem_canonical_partial_nf() &&
  check_dsystem_compatibility() &&
  check_dsystem_first_match_nf() &&
  check_dsystem_repair_phase9() &&
  check_multibranch_glue_partial()
}
