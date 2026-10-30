///|
// Propositional truncation as a generated HIT, enabled by argument
// faces (`dhit_arg_face`): the squash constructor takes two
// arbitrary elements of the truncation and its endpoints are those
// arguments themselves.
//
//   ‖A‖ ::= point (a : A) | squash (x y : ‖A‖) : x ⇝ y
//
// The eliminator is the generated HIT eliminator; mapping out of
// ‖A‖ into a family requires a squash case, which for a
// proposition-valued (or constant-unit) motive is supplied by
// reflexivity/unit paths.  The universal property at the level of
// points is definitional: every two elements are joined by the
// squash path constructor.

///|
pub fn prop_trunc_schema_at(level : Int32) -> DHitSpec {
  dhit_spec("PropTruncS", level, [dtelescope_entry("A", DUniv(level))], [], [
    dhit_cell_spec("point", 0, [darg_external("value", DTVar(0))], []),
    dhit_cell_spec("squash", 1, [darg_recursive("x"), darg_recursive("y")], [
      dhit_arg_face(DTVar(1)),
      dhit_arg_face(DTVar(0)),
    ]),
  ])
}

///|
pub fn prop_trunc_schema() -> DHitSpec {
  prop_trunc_schema_at(0)
}

///|
pub fn trunc_type_term(a : DTerm) -> DTerm {
  DHitType(prop_trunc_schema(), [a])
}

///|
pub fn trunc_point_term(a : DTerm, value : DTerm) -> DTerm {
  hit_intro_term(prop_trunc_schema(), 0, [a], [value], [])
}

///|
/// The squash path constructor at a dimension.
pub fn trunc_squash_term(a : DTerm, x : DTerm, y : DTerm, dim : Dim) -> DTerm {
  hit_intro_term(prop_trunc_schema(), 1, [a], [x, y], [dim])
}

///|
/// The squash as a path term `x = y` in `‖A‖`.
pub fn trunc_squash_path_term(a : DTerm, x : DTerm, y : DTerm) -> DTerm {
  DLamDim(trunc_squash_term(a, x, y, DVar(0)))
}

///|
/// Recursion into Unit: every truncated type maps to the unit type,
/// with the squash case given by the constant unit path.  This is
/// the simplest instance of the universal property whose squash
/// case type-checks definitionally.
pub fn trunc_rec_unit_term(scrut : DTerm) -> DTerm {
  let spec = prop_trunc_schema()
  DHitElim(
    spec,
    DLam(DHitType(spec, [DBoolTy]), DUnitTy),
    [
      DLam(DBoolTy, DUnitLit),
      DLam(
        DHitType(spec, [DBoolTy]),
        DLam(
          DUnitTy,
          DLam(DHitType(spec, [DBoolTy]), DLam(DUnitTy, DLamDim(DUnitLit))),
        ),
      ),
    ],
    [DBoolTy],
    [],
    scrut,
  )
}

///|
pub fn check_propositional_truncation() -> Bool {
  let spec = prop_trunc_schema()
  if !hit_schema_validate(spec) {
    return false
  }
  let trunc_bool = trunc_type_term(DBoolTy)
  let t = trunc_point_term(DBoolTy, DBoolLit(true))
  let f = trunc_point_term(DBoolTy, DBoolLit(false))
  // Points inhabit the truncation.
  if !dep_check_closed(t, trunc_bool) || !dep_check_closed(f, trunc_bool) {
    return false
  }
  // Squash joins arbitrary points: the path type-checks and its
  // normal form has the advertised endpoints.
  let path_ty = DPath(trunc_bool, t, f)
  let squash_path = trunc_squash_path_term(DBoolTy, t, f)
  if !dep_check_closed(squash_path, path_ty) {
    return false
  }
  // Semantic endpoint computation through argument faces.
  let ty_value = DVHitType(spec, [DVBoolTy], [])
  let t_val = hit_cell_value(spec, 0, [DVBoolTy], [DVBool(true)], [])
  let f_val = hit_cell_value(spec, 0, [DVBoolTy], [DVBool(false)], [])
  let at0 = hit_cell_value(spec, 1, [DVBoolTy], [t_val, f_val], [DZero])
  let at1 = hit_cell_value(spec, 1, [DVBoolTy], [t_val, f_val], [DOne])
  if !conv_at(0, 0, ty_value, at0, t_val) ||
    !conv_at(0, 0, ty_value, at1, f_val) {
    return false
  }
  // Squash also joins non-point elements (its arguments are
  // arbitrary truncation elements): squash between a squash point
  // at a generic dimension and a point type-checks.
  let mid = trunc_squash_term(DBoolTy, t, f, DVar(0))
  let denv = ddim_from_array([DVar(0)])
  let joined = match d_check(mid, ty_value, denv_empty(), denv_empty(), denv) {
    Some(v) =>
      conv_at(
        0,
        1,
        ty_value,
        hit_cell_value(spec, 1, [DVBoolTy], [v, t_val], [DZero]),
        v,
      )
    None => false
  }
  joined &&
  // Recursion into Unit on a point computes.
  dep_nf_closed(trunc_rec_unit_term(t), DUnitTy) == Some(DUnitLit)
}

///|
pub fn prop_trunc_type_value(a_ty : DValue) -> DValue {
  DVHitType(prop_trunc_schema(), [a_ty], [])
}

///|
pub fn prop_trunc_point_value(a_ty : DValue, value : DValue) -> DValue {
  hit_cell_value(prop_trunc_schema(), 0, [a_ty], [value], [])
}

///|
pub fn prop_trunc_squash_path_value(
  a_ty : DValue,
  x : DValue,
  y : DValue,
) -> DValue {
  DVPathLam(i => hit_cell_value(prop_trunc_schema(), 1, [a_ty], [x, y], [i]))
}

///|
/// Dependent elimination of propositional truncation `‖A‖₋₁` into any
/// h-Proposition family `M : ‖A‖₋₁ -> Type` equipped with
/// `is_prop_motive : (z : ‖A‖₋₁, u v : M z) -> Path (M z) u v`.
pub fn prop_trunc_elim_prop_value(
  a_ty : DValue,
  motive_fam : (DValue) -> DValue,
  is_prop_motive : (DValue, DValue, DValue) -> DValue,
  point_branch : (DValue) -> DValue,
  scrut : DValue,
  dlevel : Int32,
) -> DValue {
  let spec = prop_trunc_schema()
  let point_case = DVLam(a => point_branch(a))
  let squash_case = DVLam(x => {
    DVLam(ih_x => {
      DVLam(y => {
        DVLam(ih_y => {
          let line = memo_dim_line(i => {
            motive_fam(hit_cell_value(spec, 1, [a_ty], [x, y], [i]))
          })
          let transported = transport_value(line, ih_x, dlevel + 2)
          let eq = is_prop_motive(y, transported, ih_y)
          dpathp_of_transport_eq_value(line, ih_x, ih_y, eq, dlevel + 2)
        })
      })
    })
  })
  eval_hit_elim(
    spec,
    (_, z) => motive_fam(z),
    [point_case, squash_case],
    [a_ty],
    [],
    scrut,
    dlevel,
  )
}

// ---------------------------------------------------------------------------
// Hub-and-spoke 0-truncation (Set truncation `‖A‖₀`)
// ---------------------------------------------------------------------------

///|
/// Hub-and-spoke 0-truncation (`‖A‖₀`, HoTT §6.7 / Lumsdaine–Shulman):
///   `point (a : A) : ‖A‖₀`
///   `hub (f : S¹ -> ‖A‖₀) : ‖A‖₀`
///   `spoke (f : S¹ -> ‖A‖₀, t : S¹) : f(t) = hub(f)`
/// Every cell has dimension `<= 1` and strictly positive `DArgFunction`
/// recursion over `S¹`, passing `hit_schema_validate` without higher-path
/// schema axioms while forcing every self-loop in `‖A‖₀` to contract.
pub fn set_trunc_schema_at(level : Int32) -> DHitSpec {
  let c_ty = DHitType(circle_schema(), [])
  dhit_spec("SetTruncS", level, [dtelescope_entry("A", DUniv(level))], [], [
    dhit_cell_spec("point", 0, [darg_external("value", DTVar(0))], []),
    dhit_cell_spec("hub", 0, [darg_function("circle_map", c_ty)], []),
    dhit_cell_spec(
      "spoke",
      1,
      [darg_function("circle_map", c_ty), darg_external("t", c_ty)],
      [dhit_arg_face(DApp(DTVar(1), DTVar(0))), dhit_face(1, [DTVar(1)], [])],
    ),
  ])
}

///|
pub fn set_trunc_schema() -> DHitSpec {
  set_trunc_schema_at(0)
}

///|
pub fn set_trunc_type_term(a : DTerm) -> DTerm {
  DHitType(set_trunc_schema(), [a])
}

///|
pub fn set_trunc_point_term(a : DTerm, value : DTerm) -> DTerm {
  hit_intro_term(set_trunc_schema(), 0, [a], [value], [])
}

///|
pub fn set_trunc_type_value(a_ty : DValue) -> DValue {
  DVHitType(set_trunc_schema(), [a_ty], [])
}

///|
pub fn set_trunc_point_value(a_ty : DValue, value : DValue) -> DValue {
  hit_cell_value(set_trunc_schema(), 0, [a_ty], [value], [])
}

///|
pub fn set_trunc_hub_value(a_ty : DValue, circle_map : DValue) -> DValue {
  hit_cell_value(set_trunc_schema(), 1, [a_ty], [circle_map], [])
}

///|
pub fn set_trunc_spoke_path_value(
  a_ty : DValue,
  circle_map : DValue,
  t : DValue,
) -> DValue {
  let spec = set_trunc_schema()
  DVPathLam(i => hit_cell_value(spec, 2, [a_ty], [circle_map, t], [i]))
}

///|
/// Every based loop `loop_x : Path ‖A‖₀ x x` in the hub-and-spoke set
/// truncation contracts to `refl_x`, proved on arbitrary open/neutral `x`
/// and `loop_x` via the 4-face Kan square around `spoke(f, loop(j))` and
/// `spoke(f, base)`.
pub fn set_trunc_loop_trivial_value(
  a_ty : DValue,
  x : DValue,
  loop_x : DValue,
  dlevel : Int32,
) -> DValue {
  let spec = set_trunc_schema()
  let st_ty = set_trunc_type_value(a_ty)
  let c_spec = circle_schema()
  let base = DVHitCell(c_spec, 0, [], [], [])
  let f = DVLam(t => {
    eval_hit_elim(c_spec, (_, _) => st_ty, [x, loop_x], [], [], t, dlevel)
  })
  let sb = (u : Dim) => hit_cell_value(spec, 2, [a_ty], [f, base], [u])
  DVPathLam(r => {
    DVPathLam(j => {
      let loop_j = hit_cell_value(c_spec, 1, [], [], [j])
      let base_cap = hit_cell_value(spec, 2, [a_ty], [f, loop_j], [r])
      let sys = dsystem_of([
        tube_branch(face_simplify(FEq0(r)), _ => dapp_dim(loop_x, j)),
        tube_branch(face_simplify(FEq1(r)), k => sb(dim_simplify(DNeg(k)))),
        tube_branch(face_simplify(FEq0(j)), k => {
          sb(dim_simplify(DAnd(r, DNeg(k))))
        }),
        tube_branch(face_simplify(FEq1(j)), k => {
          sb(dim_simplify(DAnd(r, DNeg(k))))
        }),
      ])
      hcomp_value(st_ty, sys, base_cap, dlevel + 3)
    })
  })
}

///|
/// Set-hood (`isSet`) of `‖A‖₀`: for arbitrary open/neutral `x, y : ‖A‖₀`
/// and `p, q : Path ‖A‖₀ x y`, constructs `Path (Path ‖A‖₀ x y) p q` by
/// singleton contraction on `(y, q)` + `set_trunc_loop_trivial_value`.
pub fn set_trunc_is_set_value(
  a_ty : DValue,
  x : DValue,
  y : DValue,
  p : DValue,
  q : DValue,
  dlevel : Int32,
) -> DValue {
  let st_ty = set_trunc_type_value(a_ty)
  let fam = (y1 : DValue, q1 : DValue) => {
    let p_ty = DVPathTy(_ => st_ty, x, y1)
    DVPi(p_ty, p1 => DVPathTy(_ => p_ty, p1, q1))
  }
  let refl_case = DVLam(p0 => {
    set_trunc_loop_trivial_value(a_ty, x, p0, dlevel + 2)
  })
  let fn_at_q = dj_singleton_elim_value(fam, refl_case, q, dlevel + 1)
  dapp_typed(fn_at_q, p, DVPathTy(_ => st_ty, x, y))
}

///|
/// Non-dependent recursion out of `‖A‖₀` into any h-Set `(B, is_set_b)`.
pub fn set_trunc_rec_set_value(
  a_ty : DValue,
  b_ty : DValue,
  is_set_b : (DValue, DValue, DValue, DValue) -> DValue,
  point_branch : (DValue) -> DValue,
  scrut : DValue,
  dlevel : Int32,
) -> DValue {
  let spec = set_trunc_schema()
  match force_value(scrut) {
    DVHitCell(s, 0, _, args, _) if s == spec && args.length() == 1 =>
      return point_branch(args[0])
    _ => ()
  }
  let c_spec = circle_schema()
  let c_ty = DVHitType(c_spec, [], [])
  let base = DVHitCell(c_spec, 0, [], [], [])
  let point_case = DVLam(a => point_branch(a))
  let hub_case = DVLam(_f => DVLam(ih => dapp_typed(ih, base, c_ty)))
  let spoke_case = DVLam(_f => {
    DVLam(ih => {
      let hub_val = dapp_typed(ih, base, c_ty)
      DVLam(t => {
        let mot_t = (pt : DValue) => {
          DVPathTy(_ => b_ty, dapp_typed(ih, pt, c_ty), hub_val)
        }
        let base_p = dpath_refl_value(hub_val)
        let loop_line = memo_dim_line(j => {
          mot_t(hit_cell_value(c_spec, 1, [], [], [j]))
        })
        let tr_base_p = transport_value(loop_line, base_p, dlevel + 2)
        let loop_eq = is_set_b(hub_val, hub_val, tr_base_p, base_p)
        let loop_p = dpathp_of_transport_eq_value(
          loop_line, base_p, base_p, loop_eq, dlevel + 2,
        )
        eval_hit_elim(
          c_spec,
          (_, pt) => mot_t(pt),
          [base_p, loop_p],
          [],
          [],
          t,
          dlevel + 2,
        )
      })
    })
  })
  eval_hit_elim(
    spec,
    (_, _) => b_ty,
    [point_case, hub_case, spoke_case],
    [a_ty],
    [],
    scrut,
    dlevel,
  )
}

///|
/// Full dependent elimination of `‖A‖₀` into any h-Set family
/// `motive_fam : ‖A‖₀ -> Type` equipped with `is_set_motive`.
pub fn set_trunc_elim_set_value(
  a_ty : DValue,
  motive_fam : (DValue) -> DValue,
  is_set_motive : (DValue, DValue, DValue, DValue, DValue) -> DValue,
  point_branch : (DValue) -> DValue,
  scrut : DValue,
  dlevel : Int32,
) -> DValue {
  let spec = set_trunc_schema()
  let c_spec = circle_schema()
  let c_ty = DVHitType(c_spec, [], [])
  let base = DVHitCell(c_spec, 0, [], [], [])
  let point_case = DVLam(a => point_branch(a))
  let hub_case = DVLam(f => {
    DVLam(ih => {
      subst_value(
        z => motive_fam(z),
        set_trunc_spoke_path_value(a_ty, f, base),
        dapp_typed(ih, base, c_ty),
        dlevel + 2,
      )
    })
  })
  let spoke_case = DVLam(f => {
    DVLam(ih => {
      let hub_pt = set_trunc_hub_value(a_ty, f)
      let ih_base = dapp_typed(ih, base, c_ty)
      let hub_val = subst_value(
        z => motive_fam(z),
        set_trunc_spoke_path_value(a_ty, f, base),
        ih_base,
        dlevel + 2,
      )
      DVLam(t => {
        let spoke_line_at = (pt : DValue) => {
          memo_dim_line(i => {
            motive_fam(hit_cell_value(spec, 2, [a_ty], [f, pt], [i]))
          })
        }
        let mot_t = (pt : DValue) => {
          DVPathTy(spoke_line_at(pt), dapp_typed(ih, pt, c_ty), hub_val)
        }
        let base_spoke = subst_pathp_value(
          z => motive_fam(z),
          set_trunc_spoke_path_value(a_ty, f, base),
          ih_base,
          dlevel + 2,
        )
        let loop_line = memo_dim_line(j => {
          mot_t(hit_cell_value(c_spec, 1, [], [], [j]))
        })
        let tr_spoke = transport_value(loop_line, base_spoke, dlevel + 3)
        let loop_eq = dpathp_eq_in_set_family_value(
          spoke_line_at(base),
          ih_base,
          hub_val,
          tr_spoke,
          base_spoke,
          (a, b, p1, p2) => is_set_motive(hub_pt, a, b, p1, p2),
          dlevel + 4,
        )
        let loop_p = dpathp_of_transport_eq_value(
          loop_line, base_spoke, base_spoke, loop_eq, dlevel + 4,
        )
        eval_hit_elim(
          c_spec,
          (_, pt) => mot_t(pt),
          [base_spoke, loop_p],
          [],
          [],
          t,
          dlevel + 4,
        )
      })
    })
  })
  eval_hit_elim(
    spec,
    (_, z) => motive_fam(z),
    [point_case, hub_case, spoke_case],
    [a_ty],
    [],
    scrut,
    dlevel,
  )
}

///|
/// Dependent elimination of `‖A‖₀` into an h-Proposition family
/// `motive_fam : ‖A‖₀ -> Type` equipped with `is_prop_motive`
/// (`(z : ‖A‖₀) -> (u v : motive_fam(z)) -> Path (motive_fam(z)) u v`).
/// Since every fiber `motive_fam(hub(f))` is already an h-Proposition, the
/// `spoke(f, t)` path lifts directly from `is_prop_motive(hub(f), ...)`
/// without inner `S^1` elimination or `dprop_is_set` duplication.
pub fn set_trunc_elim_prop_value(
  a_ty : DValue,
  motive_fam : (DValue) -> DValue,
  is_prop_motive : (DValue, DValue, DValue, Int32) -> DValue,
  point_branch : (DValue) -> DValue,
  scrut : DValue,
  dlevel : Int32,
) -> DValue {
  let spec = set_trunc_schema()
  match force_value(scrut) {
    DVHitCell(s, 0, _, args, _) if s == spec && args.length() == 1 =>
      return point_branch(args[0])
    _ => ()
  }
  let c_spec = circle_schema()
  let c_ty = DVHitType(c_spec, [], [])
  let base = DVHitCell(c_spec, 0, [], [], [])
  let point_case = DVLam(a => point_branch(a))
  let hub_case = DVLam(f => {
    DVLam(ih => {
      subst_value(
        z => motive_fam(z),
        set_trunc_spoke_path_value(a_ty, f, base),
        dapp_typed(ih, base, c_ty),
        dlevel + 2,
      )
    })
  })
  let spoke_case = DVLam(f => {
    DVLam(ih => {
      let hub_pt = set_trunc_hub_value(a_ty, f)
      let hub_val = subst_value(
        z => motive_fam(z),
        set_trunc_spoke_path_value(a_ty, f, base),
        dapp_typed(ih, base, c_ty),
        dlevel + 2,
      )
      DVLam(t => {
        let ih_t = dapp_typed(ih, t, c_ty)
        let s_line = memo_dim_line(i => {
          motive_fam(hit_cell_value(spec, 2, [a_ty], [f, t], [i]))
        })
        let tr_t = transport_value(s_line, ih_t, dlevel + 6)
        let eq = is_prop_motive(hub_pt, tr_t, hub_val, dlevel + 12)
        dpathp_of_transport_eq_value(s_line, ih_t, hub_val, eq, dlevel + 24)
      })
    })
  })
  eval_hit_elim(
    spec,
    (_, z) => motive_fam(z),
    [point_case, hub_case, spoke_case],
    [a_ty],
    [],
    scrut,
    dlevel + 28,
  )
}

///|
/// Universal 0-truncation equivalence theorem for arbitrary h-Sets:
/// given any equivalence `e : Equiv A B` and an h-Set witness `is_set_b` on `B`,
/// constructs the full bidirectional equivalence `Equiv ‖A‖₀ B` by universal
/// recursion `set_trunc_rec_set_value` (`|a|₀ ↦ e.fwd(a)`) and propositional
/// path elimination `set_trunc_elim_prop_value` (`b ↦ |e.bwd(b)|₀`).
pub fn set_trunc_equiv_of_equiv_set_value(
  a_ty : DValue,
  b_ty : DValue,
  e : DValue,
  is_set_b : (DValue, DValue, DValue, DValue) -> DValue,
  dlevel : Int32,
) -> DValue {
  let st_a_ty = set_trunc_type_value(a_ty)
  let e_fwd = equiv_fwd_value(e, a_ty, b_ty)
  let e_bwd = equiv_bwd_value(e, a_ty, b_ty)
  let e_sect = equiv_sect_value(e, a_ty, b_ty)
  let e_retr = equiv_retr_value(e, a_ty, b_ty)
  let fwd_one = (w : DValue) => {
    set_trunc_rec_set_value(
      a_ty,
      b_ty,
      is_set_b,
      a => dapp_typed(e_fwd, a, a_ty),
      w,
      dlevel + 2,
    )
  }
  let bwd_one = (b : DValue) => {
    set_trunc_point_value(a_ty, dapp_typed(e_bwd, b, b_ty))
  }
  let point_fn = DVLam(a => set_trunc_point_value(a_ty, a))
  let retr_one = (w : DValue) => {
    let mot = (z : DValue) => DVPathTy(_ => st_a_ty, bwd_one(fwd_one(z)), z)
    set_trunc_elim_prop_value(
      a_ty,
      mot,
      (z, q1, q2, dl) => {
        set_trunc_is_set_value(a_ty, bwd_one(fwd_one(z)), z, q1, q2, dl)
      },
      a => dpath_cong_value(point_fn, a_ty, dapp_typed(e_retr, a, a_ty)),
      w,
      dlevel + 10,
    )
  }
  equiv_make_value(
    st_a_ty,
    b_ty,
    DVLam(w => fwd_one(w)),
    DVLam(b => bwd_one(b)),
    DVLam(b => dapp_typed(e_sect, b, b_ty)),
    DVLam(w => retr_one(w)),
  )
}
