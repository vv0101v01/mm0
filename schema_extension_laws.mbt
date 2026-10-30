///|
// Behavioural laws for the extended schema language: structural
// positivity, nested functors, mutual families, induction-recursion,
// constructor constraints, universe schemes, quotients, and HITs of
// dimension greater than two.

///|
pub fn check_structural_positivity() -> Bool {
  let probe = dinductive_spec("ProbeS", 0, [], [], [])
  let target = schema_type_term(probe, [])
  let negative = dterm_family_positivity(DPi(target, DNatTy), "ProbeS")
  if !negative.occurs ||
    negative.strictly_positive ||
    !negative.negative_polarity {
    return false
  }
  let function_positive = dterm_family_positivity(DPi(DNatTy, target), "ProbeS")
  if !function_positive.strictly_positive {
    return false
  }
  // Beta aliases are unfolded before classification.
  let alias_term = DApp(DLam(DUniv(0), DListTy(DTVar(0))), target)
  if !dterm_family_positivity(alias_term, "ProbeS").strictly_positive {
    return false
  }
  // Occurrences through the certified positive parameter of ListS
  // are strict; the same occurrence in a Pi domain is not.
  let indirect = schema_type_term(list_schema(), [target])
  if !dterm_family_positivity(indirect, "ProbeS").strictly_positive ||
    dterm_family_positivity(DPi(indirect, DNatTy), "ProbeS").strictly_positive {
    return false
  }
  let list_param = inductive_parameter_positivity(list_schema(), 0)
  if !list_param.occurs || !list_param.strictly_positive {
    return false
  }
  // An external argument may not smuggle the family through ListS:
  // schema validation uses structural occurrence, not a name scan.
  let bad_placeholder = dinductive_spec("IndirectBadS", 0, [], [], [])
  let bad = dinductive_spec("IndirectBadS", 0, [], [], [
    dconstructor_spec("mk", [
      darg_external(
        "xs",
        schema_type_term(list_schema(), [schema_type_term(bad_placeholder, [])]),
      ),
    ]),
  ])
  !inductive_schema_validate(bad)
}

///|
fn dv_sum_all_nat(v : DValue) -> DValue {
  match force_value(v) {
    DVPair(x, rest) => dv_nat_plus(x, dv_sum_all_nat(rest))
    _ => DVZeroNat
  }
}

///|
pub fn check_nested_rose_tree() -> Bool {
  let spec = rose_tree_schema()
  if !inductive_schema_validate(spec) {
    return false
  }
  let leaf : DValue = DVIntro(spec, 0, [DVBoolTy], [DVBool(true)])
  let children : DValue = DVCons(leaf, DVCons(leaf, DVNil))
  let tree : DValue = DVIntro(spec, 1, [DVBoolTy], [children])
  let leaves = eval_inductive_elim(
    spec,
    (_, _) => DVNatTy,
    [DVLam(_ => dv_nat_lit(1)), DVLam(_ => DVLam(all => dv_sum_all_nat(all)))],
    [DVBoolTy],
    [],
    tree,
    0,
  )
  if !dv_is_nat(leaves, 2) {
    return false
  }
  // The nested argument type is a genuine List of the family.
  let family : DValue = DVInductive(spec, [DVBoolTy], [])
  conv_ty(
    0,
    0,
    inductive_arg_type(spec, spec.constructors[1].args[0], [DVBoolTy], []),
    DVListTy(family),
  )
}

///|
pub fn check_container_functor_tree() -> Bool {
  let spec = container_tree_schema()
  if !inductive_schema_validate(spec) {
    return false
  }
  let positions : DValue = DVLam(_ => DVBoolTy)
  let params : Array[DValue] = [DVBoolTy, positions]
  let leaf : DValue = DVIntro(spec, 0, params, [])
  let children : DValue = DVPair(DVBool(false), DVLam(_ => leaf))
  let tree : DValue = DVIntro(spec, 1, params, [children])
  let leaves = eval_inductive_elim(
    spec,
    (_, _) => DVNatTy,
    [
      dv_nat_lit(1),
      DVLam(_ => {
        DVLam(ih => {
          dv_nat_plus(
            dapp_typed(ih, DVBool(true), DVBoolTy),
            dapp_typed(ih, DVBool(false), DVBoolTy),
          )
        })
      }),
    ],
    params,
    [],
    tree,
    0,
  )
  if !dv_is_nat(leaves, 2) {
    return false
  }
  let family : DValue = DVInductive(spec, params, [])
  conv_ty(
    0,
    0,
    inductive_arg_type(spec, spec.constructors[1].args[0], params, []),
    DVSigma(DVBoolTy, _ => DVPi(DVBoolTy, _ => family)),
  )
}

///|
pub fn check_constructor_constraints() -> Bool {
  let spec = equal_nat_pair_schema()
  if !inductive_schema_validate(spec) {
    return false
  }
  let ty = schema_type_term(spec, [])
  let good = schema_intro_term(spec, 0, [], [d_nat_lit(2), d_nat_lit(2)])
  let bad = schema_intro_term(spec, 0, [], [d_nat_lit(0), d_nat_lit(1)])
  if !dep_check_closed(good, ty) || dep_check_closed(bad, ty) {
    return false
  }
  let pair_value : DValue = DVIntro(spec, 0, [], [dv_nat_lit(2), dv_nat_lit(2)])
  let first = eval_inductive_elim(
    spec,
    (_, _) => DVNatTy,
    [DVLam(x => DVLam(_ => DVLam(_proof => x)))],
    [],
    [],
    pair_value,
    0,
  )
  if !dv_is_nat(first, 2) {
    return false
  }
  // The generated case has a third, Path-typed argument.
  match inductive_case_type(spec, (_, _) => DVNatTy, [], 0) {
    DVPi(_, after_x) =>
      match after_x(DVZeroNat) {
        DVPi(_, after_y) =>
          match after_y(DVZeroNat) {
            DVPi(DVPathTy(_, _, _), _) => true
            _ => false
          }
        _ => false
      }
    _ => false
  }
}

///|
pub fn check_tarski_induction_recursion() -> Bool {
  let spec = tarski_universe_schema()
  if !inductive_schema_validate(spec) {
    return false
  }
  let nat_code : DValue = DVIntro(spec, 0, [], [])
  let pi_code : DValue = DVIntro(spec, 2, [], [nat_code, DVLam(_ => nat_code)])
  let decoded = eval_inductive_decode(spec, [], [], pi_code, 0)
  if !conv_ty(0, 0, decoded, DVPi(DVNatTy, _ => DVNatTy)) {
    return false
  }
  // The same computation is available as syntax.
  let nat_term = schema_intro_term(spec, 0, [], [])
  let pi_term = schema_intro_term(spec, 2, [], [
    nat_term,
    DLam(decode_term(spec, [], [], nat_term), nat_term),
  ])
  if !dep_check_closed(pi_term, schema_type_term(spec, [])) {
    return false
  }
  if dep_nf_closed(decode_term(spec, [], [], pi_term), DUniv(0)) !=
    Some(DPi(DNatTy, DNatTy)) {
    return false
  }
  // A neutral code has a neutral decoded type, quoted back to the
  // decode former.
  let neutral_decoded = eval_inductive_decode(
    spec,
    [],
    [],
    DVNeutral(DNVar(0)),
    0,
  )
  match quote_ty(1, 0, neutral_decoded) {
    DDecode(_, _, _, DTVar(0)) => true
    _ => false
  }
}

///|
pub fn check_mutual_inductives() -> Bool {
  let eo = match even_odd_family() {
    Some(f) => f
    None => return false
  }
  let even0 = mutual_intro_value(eo, 0, 0, [], [])
  let odd1 = mutual_intro_value(eo, 1, 0, [], [DVZeroNat, even0])
  let even2 = mutual_intro_value(eo, 0, 1, [], [dv_nat_lit(1), odd1])
  let even2_term = mutual_intro_term(eo, 0, 1, [], [
    d_nat_lit(1),
    mutual_intro_term(eo, 1, 0, [], [
      DNatZero,
      mutual_intro_term(eo, 0, 0, [], []),
    ]),
  ])
  if !dep_check_closed(even2_term, mutual_type_term(eo, 0, [d_nat_lit(2)])) ||
    dep_check_closed(even2_term, mutual_type_term(eo, 0, [d_nat_lit(1)])) {
    return false
  }
  let length = eval_mutual_elim(
    eo,
    [(_, _) => DVNatTy, (_, _) => DVNatTy],
    [
      [DVZeroNat, DVLam(_ => DVLam(_ => DVLam(ih => DVSucc(ih))))],
      [DVLam(_ => DVLam(_ => DVLam(ih => DVSucc(ih))))],
    ],
    [],
    0,
    [dv_nat_lit(2)],
    even2,
    0,
  )
  if !dv_is_nat(length, 2) {
    return false
  }
  // Tree/Forest: mutual recursion through two unindexed components.
  let tf = match tree_forest_family() {
    Some(f) => f
    None => return false
  }
  let nil_forest = mutual_intro_value(tf, 1, 0, [DVBoolTy], [])
  let subtree = mutual_intro_value(tf, 0, 0, [DVBoolTy], [
    DVBool(true),
    nil_forest,
  ])
  let forest = mutual_intro_value(tf, 1, 1, [DVBoolTy], [subtree, nil_forest])
  let root = mutual_intro_value(tf, 0, 0, [DVBoolTy], [DVBool(false), forest])
  let nodes = eval_mutual_elim(
    tf,
    [(_, _) => DVNatTy, (_, _) => DVNatTy],
    [
      [DVLam(_ => DVLam(_ => DVLam(ih => DVSucc(ih))))],
      [
        DVZeroNat,
        DVLam(_ => {
          DVLam(head => DVLam(_ => DVLam(tail => dv_nat_plus(head, tail))))
        }),
      ],
    ],
    [DVBoolTy],
    0,
    [],
    root,
    0,
  )
  dv_is_nat(nodes, 2)
}

///|
pub fn check_universe_schemes() -> Bool {
  let list2 = match
    instantiate_inductive_level_scheme(list_level_scheme(), [2]) {
    Some(spec) => spec
    None => return false
  }
  if list2.level != 2 || list2.params[0].ty != DUniv(2) {
    return false
  }
  if instantiate_inductive_level_scheme(list_level_scheme(), []) != None {
    return false
  }
  match instantiate_hit_level_scheme(circle_level_scheme(), [1]) {
    Some(spec) => spec.level == 1 && hit_schema_validate(spec)
    None => false
  }
}

///|
pub fn check_quotient_schema() -> Bool {
  let spec = quotient_schema()
  if !hit_schema_validate(spec) {
    return false
  }
  let relation : DValue = DVLam(_ => DVLam(_ => DVUnitTy))
  let params : Array[DValue] = [DVBoolTy, relation]
  let ty : DValue = DVHitType(spec, params, [])
  let point_true : DValue = DVHitCell(spec, 0, params, [DVBool(true)], [])
  let point_false : DValue = DVHitCell(spec, 0, params, [DVBool(false)], [])
  let eq0 = hit_cell_value(
    spec,
    1,
    params,
    [DVBool(true), DVBool(false), DVUnit],
    [DZero],
  )
  let eq1 = hit_cell_value(
    spec,
    1,
    params,
    [DVBool(true), DVBool(false), DVUnit],
    [DOne],
  )
  if !conv_at(0, 0, ty, eq0, point_true) || !conv_at(0, 0, ty, eq1, point_false) {
    return false
  }
  // The constant Nat-valued eliminator sends a quotient path to refl.
  let param_terms = [DBoolTy, DLam(DBoolTy, DLam(DBoolTy, DUnitTy))]
  let ty_term = DHitType(spec, param_terms)
  let elim_eq = DLamDim(
    hit_elim_term(
      spec,
      DLam(ty_term, DNatTy),
      [
        DLam(DBoolTy, DNatZero),
        DLam(DBoolTy, DLam(DBoolTy, DLam(DUnitTy, DLamDim(DNatZero)))),
      ],
      param_terms,
      [],
      quotient_eq_term(
        param_terms,
        DBoolLit(true),
        DBoolLit(false),
        DUnitLit,
        DVar(0),
      ),
    ),
  )
  dep_nf_closed(elim_eq, DPath(DNatTy, DNatZero, DNatZero)) ==
  Some(DLamDim(DNatZero))
}

///|
pub fn check_cube3_and_moving_hit_comp() -> Bool {
  let cube = cube3_schema()
  if !hit_schema_validate(cube) {
    return false
  }
  let ty : DValue = DVHitType(cube, [], [])
  let face = hit_cell_value(cube, 3, [], [], [DZero, DVar(0), DVar(1)])
  let square : DValue = DVHitCell(cube, 2, [], [], [DVar(0), DVar(1)])
  if !conv_at(0, 2, ty, face, square) {
    return false
  }
  let point : DValue = DVHitCell(cube, 3, [], [], [DVar(0), DVar(1), DVar(2)])
  let identity = eval_hit_elim(
    cube,
    (_, _) => ty,
    [
      DVHitCell(cube, 0, [], [], []),
      DVPathLam(d => hit_cell_value(cube, 1, [], [], [d])),
      DVPathLam(a => DVPathLam(b => hit_cell_value(cube, 2, [], [], [a, b]))),
      DVPathLam(a => {
        DVPathLam(b => {
          DVPathLam(c => hit_cell_value(cube, 3, [], [], [a, b, c]))
        })
      }),
    ],
    [],
    [],
    point,
    3,
  )
  if !conv_at(0, 3, ty, identity, point) {
    return false
  }
  // A composition may move the dimension of a fixed loop cell: the
  // tube `loop (i ∨ j)` ends at the base point.
  let circle = circle_schema()
  let circle_ty : DValue = DVHitType(circle, [], [])
  let base_loop : DValue = DVHitCell(circle, 1, [], [], [DVar(0)])
  let moved = hcomp_value(
    circle_ty,
    dsystem_singleton(FEq0(DVar(1)), j => {
      DVHitCell(circle, 1, [], [], [DOr(DVar(0), j)])
    }),
    base_loop,
    2,
  )
  conv_at(0, 2, circle_ty, moved, DVHitCell(circle, 0, [], [], []))
}

///|
pub fn check_schema_extensions() -> Bool {
  check_structural_positivity() &&
  check_family_nested_functors() &&
  check_nested_rose_tree() &&
  check_container_functor_tree() &&
  check_constructor_constraints() &&
  check_tarski_induction_recursion() &&
  check_mutual_inductives() &&
  check_universe_schemes() &&
  check_quotient_schema() &&
  check_cube3_and_moving_hit_comp()
}

///|
/// Sum the Nat leaves of a family-gather IH bundle (nested
/// pairs, one slot per constructor argument, unit-terminated).
fn dv_sum_bundle_leaves(v : DValue) -> DValue {
  match force_value(v) {
    DVPair(a, b) =>
      dv_nat_plus(dv_sum_bundle_leaves(a), dv_sum_bundle_leaves(b))
    DVZeroNat => DVZeroNat
    DVSucc(_) => v
    _ => DVZeroNat
  }
}

///|
/// Phase 11: recursion nested through *declared* families.
/// Rose trees whose children form a `ListS` (a declared family,
/// not the primitive list functor), and binary trees whose
/// branching is a `VecS _ 2`; in both cases the eliminator's
/// induction hypotheses for the children are produced by the
/// inner family's own eliminator.  Validation rejects a `Self`
/// instantiation at a parameter used in a function domain or in
/// a non-leaf constant position.
pub fn check_family_nested_functors() -> Bool {
  // Rose trees through the declared List family.
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
  if !inductive_schema_validate(rose) {
    return false
  }
  let leaf : DValue = DVIntro(rose, 0, [DVBoolTy], [DVBool(true)])
  let kids : DValue = DVIntro(
    list_schema(),
    1,
    [DVInductive(rose, [DVBoolTy], [])],
    [
      leaf,
      DVIntro(list_schema(), 1, [DVInductive(rose, [DVBoolTy], [])], [
        leaf,
        DVIntro(list_schema(), 0, [DVInductive(rose, [DVBoolTy], [])], []),
      ]),
    ],
  )
  let tree : DValue = DVIntro(rose, 1, [DVBoolTy], [kids])
  // The node argument type is the declared List family applied
  // to the rose family itself.
  if !conv_ty(
      0,
      0,
      inductive_arg_type(rose, rose.constructors[1].args[0], [DVBoolTy], []),
      DVInductive(list_schema(), [DVInductive(rose, [DVBoolTy], [])], []),
    ) {
    return false
  }
  // The IH bundle type for the children, computed by ListS's
  // eliminator into the universe: per cons cell a Sigma slot for
  // the head's motive and one for the tail's bundle.
  let bundle_ty = positive_functor_ih_type(
    dfunctor_family(list_schema(), params=[dfunctor_param_self()]),
    [DVBoolTy],
    [],
    _ => DVInductive(rose, [DVBoolTy], []),
    (_, _) => DVNatTy,
    kids,
  )
  let tail_bundle_ty : DValue = DVSigma(DVNatTy, _ => {
    DVSigma(DVUnitTy, _ => DVUnitTy)
  })
  if !conv_ty(
      0,
      0,
      bundle_ty,
      DVSigma(DVNatTy, _ => DVSigma(tail_bundle_ty, _ => DVUnitTy)),
    ) {
    return false
  }
  // Counting leaves: the node case receives the IH bundle
  // gathered by ListS's eliminator.
  let leaves = eval_inductive_elim(
    rose,
    (_, _) => DVNatTy,
    [
      DVLam(_ => dv_nat_lit(1)),
      DVLam(_ => DVLam(all => dv_sum_bundle_leaves(all))),
    ],
    [DVBoolTy],
    [],
    tree,
    0,
  )
  if !dv_is_nat(leaves, 2) {
    return false
  }
  // Binary branching through the declared Vec family at length 2.
  let vtree = dinductive_spec(
    "FamVecTreeS",
    0,
    [dtelescope_entry("A", DUniv(0))],
    [],
    [
      dconstructor_spec("leaf", [darg_external("label", DTVar(0))]),
      dconstructor_spec("node", [
        darg_nested(
          "children",
          dfunctor_family(vec_schema(), params=[dfunctor_param_self()], index=[
            DSucc(DSucc(DNatZero)),
          ]),
        ),
      ]),
    ],
  )
  if !inductive_schema_validate(vtree) {
    return false
  }
  let vleaf : DValue = DVIntro(vtree, 0, [DVBoolTy], [DVBool(false)])
  let vfam : DValue = DVInductive(vtree, [DVBoolTy], [])
  let vkids : DValue = DVIntro(vec_schema(), 1, [vfam], [
    vleaf,
    dv_nat_lit(1),
    DVIntro(vec_schema(), 1, [vfam], [
      vleaf,
      dv_nat_lit(0),
      DVIntro(vec_schema(), 0, [vfam], []),
    ]),
  ])
  let vtree_val : DValue = DVIntro(vtree, 1, [DVBoolTy], [vkids])
  let vleaves = eval_inductive_elim(
    vtree,
    (_, _) => DVNatTy,
    [
      DVLam(_ => dv_nat_lit(1)),
      DVLam(_ => DVLam(all => dv_sum_bundle_leaves(all))),
    ],
    [DVBoolTy],
    [],
    vtree_val,
    0,
  )
  if !dv_is_nat(vleaves, 2) {
    return false
  }
  // A parameter used in a function domain cannot take `Self`.
  let bad_inner = dinductive_spec(
    "FamBadInnerS",
    0,
    [dtelescope_entry("A", DUniv(0))],
    [],
    [
      dconstructor_spec("mk", [
        darg_nested("fnarg", dfunctor_pi(DTVar(0), dfunctor_identity([]))),
      ]),
    ],
  )
  let bad_host = dinductive_spec("FamBadHostS", 0, [], [], [
    dconstructor_spec("mk", [
      darg_nested(
        "inner",
        dfunctor_family(bad_inner, params=[dfunctor_param_self()]),
      ),
    ]),
  ])
  if inductive_schema_validate(bad_host) {
    return false
  }
  // A parameter stored in a function *domain* inside a constant
  // term cannot take `Self`.  (A codomain occurrence became
  // gatherable in Phase 12; the domain position remains
  // negative and untraversable.)
  let bad_inner2 = dinductive_spec(
    "FamBadInner2S",
    0,
    [dtelescope_entry("A", DUniv(0))],
    [],
    [dconstructor_spec("mk", [darg_external("wrapped", DPi(DTVar(0), DNatTy))])],
  )
  let bad_host2 = dinductive_spec("FamBadHost2S", 0, [], [], [
    dconstructor_spec("mk", [
      darg_nested(
        "inner",
        dfunctor_family(bad_inner2, params=[dfunctor_param_self()]),
      ),
    ]),
  ])
  !inductive_schema_validate(bad_host2)
}
