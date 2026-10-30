///|
// Type-directed Kan operations for the dependent AST.
//
// This file gives the computational content of the cubical term
// constructors DCoe / DComp / DHComp / DHFill.  A line is a semantic
// Dim -> DValue type function (usually the evaluation of a line body
// under a fresh dimension), and a tube is a finite list of face-
// guarded paths over that line.  comp dispatches on the shape of the
// line sampled at a fresh generic dimension:
//
//   Pi      : contravariant on the domain; the argument travels along
//             the reversed domain fill before codomain composition.
//   Sigma   : compose the first component, take its fill, then compose
//             the second component over that fill.
//   PathP   : compose at each point of the path dimension, adding the
//             two endpoint branches of the moving path type.
//   Universe: hcomp produces a Glue type; coe along a constant
//   universe line is the identity on types.
//   Glue    : compose in the base and partial types, then correct the
//             base component by the hcomp path from the partial fill
//             (the same Kan-5 repair as the finite Glue layer).
//   Data    : Bool/Unit/Nat/List recurse on matching constructors.
//   HITs    : all-base systems over Circle/Torus reduce to the base
//             point; nontrivial compositions remain as formal hcomp
//             points (the standard stuck HIT compositions).
//   Neutral : stuck compositions are kept as DNComp neutrals.
//
// fill is the usual restriction of comp to an initial segment
// (j <= r); coe between arbitrary endpoints is reduced to fills and
// segment compositions.  hcomp is comp along a constant line and
// hfill is its filler.

// ---------------------------------------------------------------------------
// Semantic dimension / face predicates
// ---------------------------------------------------------------------------

///|
pub fn dim_vars_of(r : Dim) -> Array[Int32] {
  match r {
    DVar(i) => [i]
    DNeg(a) => dim_vars_of(a)
    DAnd(a, b) => {
      let out = dim_vars_of(a)
      let bs = dim_vars_of(b)
      for i in 0..<bs.length() {
        out.push(bs[i])
      }
      out
    }
    DOr(a, b) => {
      let out = dim_vars_of(a)
      let bs = dim_vars_of(b)
      for i in 0..<bs.length() {
        out.push(bs[i])
      }
      out
    }
    _ => []
  }
}

///|
pub fn dim_nvars_sem(r : Dim) -> Int32 {
  let vars = dim_vars_of(r)
  let mut n = 0
  for i in 0..<vars.length() {
    if vars[i] + 1 > n {
      n = vars[i] + 1
    }
  }
  n
}

///|
pub fn dim_eq_sem(r : Dim, s : Dim) -> Bool {
  let n1 = dim_nvars_sem(r)
  let n2 = dim_nvars_sem(s)
  let n = if n1 > n2 { n1 } else { n2 }
  face_eq_mod(FEq0(r), FEq0(s), n)
}

///|
pub fn face_nvars_sem(f : Face) -> Int32 {
  let vars = face_vars(f)
  let mut n = 0
  for i in 0..<vars.length() {
    if vars[i] + 1 > n {
      n = vars[i] + 1
    }
  }
  n
}

///|
pub fn face_is_top_sem(f : Face) -> Bool {
  face_le(FTop, f, face_nvars_sem(f))
}

///|
pub fn face_is_bot_sem(f : Face) -> Bool {
  face_le(f, FBot, face_nvars_sem(f))
}

///|
pub fn face_is_sat_sem(f : Face) -> Bool {
  !face_is_bot_sem(f)
}

///|
fn dim_is_zero(r : Dim) -> Bool {
  dim_eq_sem(r, DZero)
}

///|
fn dim_is_one(r : Dim) -> Bool {
  dim_eq_sem(r, DOne)
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

///|
fn dim_barycenter_tag(r : Dim) -> Int32 {
  match r {
    DZero => 0
    DOne => 2
    DVar(_) => 1
    DNeg(a) => 2 - dim_barycenter_tag(a)
    DAnd(a, b) => {
      let ta = dim_barycenter_tag(a)
      let tb = dim_barycenter_tag(b)
      if ta < tb {
        ta
      } else {
        tb
      }
    }
    DOr(a, b) => {
      let ta = dim_barycenter_tag(a)
      let tb = dim_barycenter_tag(b)
      if ta > tb {
        ta
      } else {
        tb
      }
    }
  }
}

///|
/// Exact decision for `φ = 1_𝔽` in the CCHM De Morgan face lattice `𝔽`
/// (interior barycenter `(1/2, ..., 1/2)` evaluation), distinguishing the
/// full cube `1_𝔽` from proper boundary disjunctions such as `(i = 0) ∨ (i = 1)`.
pub fn face_is_cubical_top(f : Face) -> Bool {
  match f {
    FTop => true
    FBot => false
    FEq0(r) => dim_barycenter_tag(r) == 0
    FEq1(r) => dim_barycenter_tag(r) == 2
    FAnd(a, b) => face_is_cubical_top(a) && face_is_cubical_top(b)
    FOr(a, b) => face_is_cubical_top(a) || face_is_cubical_top(b)
  }
}

///|
fn top_branch(system : DSystem) -> DTubeBranch? {
  for i in 0..<system.branches.length() {
    if face_is_cubical_top(system.branches[i].face) {
      return Some(system.branches[i])
    }
  }
  None
}

///|
pub fn map_branches(
  branches : DSystem,
  f : ((Dim) -> DValue) -> (Dim) -> DValue,
) -> DSystem {
  dsystem_map(branches, f)
}

///|
fn line_pi_at(line : (Dim) -> DValue, d : Dim) -> DFamilyParts {
  match as_pi(line(d)) {
    Some(p) => p
    None => DFamilyParts::{ dom: DVUnitTy, fam: _ => DVUnitTy, }
  }
}

///|
fn line_sigma_at(line : (Dim) -> DValue, d : Dim) -> DFamilyParts {
  match as_sigma(line(d)) {
    Some(p) => p
    None => DFamilyParts::{ dom: DVUnitTy, fam: _ => DVUnitTy, }
  }
}

///|
fn path_at(line : (Dim) -> DValue, d : Dim) -> DPathParts {
  match as_path(line(d)) {
    Some(p) => p
    None => DPathParts::{ line: _ => DVUnitTy, left: DVUnit, right: DVUnit, }
  }
}

///|
fn glue_at(line : (Dim) -> DValue, d : Dim) -> DGlueParts {
  let ty = line(d)
  match as_glue(ty) {
    Some(g) => g
    None =>
      DGlueParts::{
        system: dsystem_empty(),
        face: FBot,
        line: _ => ty,
        base: ty,
        level: 0,
      }
  }
}

///|
fn list_elem_at(line : (Dim) -> DValue, d : Dim) -> DValue {
  match as_list_elem(line(d)) {
    Some(a) => a
    None => DVUnitTy
  }
}

// ---------------------------------------------------------------------------
// fill / coe (defined from comp)
// ---------------------------------------------------------------------------

///|
pub fn fill_value(
  line : (Dim) -> DValue,
  branches : DSystem,
  base : DValue,
  dlevel : Int32,
) -> (Dim) -> DValue {
  r => {
    if dim_is_zero(r) {
      base
    } else {
      let subline = (j : Dim) => line(dim_simplify(DAnd(j, r)))
      let mapped = map_branches(branches, p => {
        (j : Dim) => p(dim_simplify(DAnd(j, r)))
      })
      mapped.branches.push(tube_branch(face_simplify(FEq0(r)), _ => base))
      comp_value(subline, mapped, base, dlevel + 1)
    }
  }
}

///|
pub fn hfill_value(
  ty : DValue,
  branches : DSystem,
  base : DValue,
  dlevel : Int32,
) -> (Dim) -> DValue {
  r => {
    if dim_is_zero(r) {
      base
    } else {
      let mapped = map_branches(branches, p => {
        (j : Dim) => p(dim_simplify(DAnd(j, r)))
      })
      mapped.branches.push(tube_branch(face_simplify(FEq0(r)), _ => base))
      hcomp_value(ty, mapped, base, dlevel + 1)
    }
  }
}

///|
pub fn coe_value(
  line : (Dim) -> DValue,
  r : Dim,
  s : Dim,
  v : DValue,
  dlevel : Int32,
) -> DValue {
  if dim_eq_sem(r, s) {
    v
  } else if dim_is_zero(r) && dim_is_one(s) {
    comp_value(line, dsystem_empty(), v, dlevel)
  } else if dim_is_one(r) && dim_is_zero(s) {
    comp_value(j => line(DNeg(j)), dsystem_empty(), v, dlevel)
  } else if dim_is_zero(r) {
    fill_value(line, dsystem_empty(), v, dlevel)(s)
  } else if dim_is_one(s) {
    comp_value(j => line(DOr(r, j)), dsystem_empty(), v, dlevel)
  } else if dim_is_one(r) {
    comp_value(j => line(DOr(s, DNeg(j))), dsystem_empty(), v, dlevel)
  } else if dim_is_zero(s) {
    coe_value(j => line(DNeg(j)), DNeg(r), DOne, v, dlevel)
  } else {
    let mid = coe_value(line, r, DOne, v, dlevel)
    coe_value(line, DOne, s, mid, dlevel)
  }
}

// ---------------------------------------------------------------------------
// comp: the type-directed recursion
// ---------------------------------------------------------------------------

///|
pub fn comp_value(
  line : (Dim) -> DValue,
  branches0 : DSystem,
  base : DValue,
  dlevel : Int32,
) -> DValue {
  let branches = dsystem_of(branches0.branches)
  match top_branch(branches) {
    Some(br) => return (br.path)(DOne)
    None => ()
  }
  let generic = DVar(dlevel)
  match force_value(line(generic)) {
    DVPi(_, _) => comp_pi_value(line, branches, base, dlevel)
    DVSigma(_, _) => comp_sigma_value(line, branches, base, dlevel)
    DVPathTy(_, _, _) => comp_path_value(line, branches, base, dlevel)
    DVUniv(_) => comp_univ_value(line, branches, base, dlevel)
    DVGlue(_, _, _) => comp_glue_value(line, branches, base, dlevel)
    DVEquivTy(_, _, _) => comp_equiv_value(line, branches, base, dlevel)
    DVGlueEquiv(_, _, _) => comp_glue_equiv_value(line, branches, base, dlevel)
    DVInductive(_, _, _) => comp_inductive_value(line, branches, base, dlevel)
    DVHitType(_, _, _) => comp_hit_value(line, branches, base, dlevel)
    DVBoolTy => comp_bool_value(line, branches, base, dlevel)
    DVUnitTy => DVUnit
    DVNatTy => comp_nat_value(line, branches, base, dlevel)
    DVListTy(_) => comp_list_value(line, branches, base, dlevel)
    DVCircleTy => comp_circle_value(line, branches, base, dlevel)
    DVTorusTy => comp_torus_value(line, branches, base, dlevel)
    _ => DVNeutral(DNComp(line, branches, base))
  }
}

///|
pub fn hcomp_value(
  ty : DValue,
  branches0 : DSystem,
  base : DValue,
  dlevel : Int32,
) -> DValue {
  let branches = dsystem_of(branches0.branches)
  match top_branch(branches) {
    Some(br) => return (br.path)(DOne)
    None => ()
  }
  match force_value(ty) {
    DVUnitTy => DVUnit
    _ if branches.branches.length() == 0 => base
    DVPi(dom, fam) =>
      DVLam(y => {
        let b_branches = map_branches(branches, p => {
          (j : Dim) => dapp_typed(p(j), y, dom)
        })
        hcomp_value(fam(y), b_branches, dapp_typed(base, y, dom), dlevel)
      })
    DVSigma(dom, fam) => {
      let fst_branches = map_branches(branches, p => {
        (j : Dim) => dfst_typed(p(j), fam)
      })
      let a_fill = hfill_value(dom, fst_branches, dfst_typed(base, fam), dlevel)
      let b_line = (j : Dim) => fam(a_fill(j))
      let snd_branches = map_branches(branches, p => {
        (j : Dim) => dsnd_typed(p(j), dom, fam)
      })
      DVPair(
        a_fill(DOne),
        comp_value(b_line, snd_branches, dsnd_typed(base, dom, fam), dlevel),
      )
    }
    DVPathTy(pline, left, right) =>
      DVPathLam(k => {
        let mapped = map_branches(branches, p => (j : Dim) => dapp_dim(p(j), k))
        mapped.branches.push(tube_branch(face_simplify(FEq0(k)), _ => left))
        mapped.branches.push(tube_branch(face_simplify(FEq1(k)), _ => right))
        hcomp_value(pline(k), mapped, dapp_dim(base, k), dlevel + 1)
      })
    _ =>
      match comp_value(_ => ty, branches, base, dlevel) {
        DVNeutral(DNComp(_, bs, b)) => DVNeutral(DNHComp(ty, bs, b))
        other => other
      }
  }
}

///|
pub fn comp_pi_value(
  line : (Dim) -> DValue,
  branches : DSystem,
  base : DValue,
  dlevel : Int32,
) -> DValue {
  DVLam(y => {
    let a_line = (j : Dim) => line_pi_at(line, j).dom
    let rev_fill = fill_value(j => a_line(DNeg(j)), dsystem_empty(), y, dlevel)
    let x_path = (j : Dim) => rev_fill(dim_simplify(DNeg(j)))
    let b_line = (j : Dim) => (line_pi_at(line, j).fam)(x_path(j))
    let out_bs : Array[DTubeBranch] = []
    for br in branches.branches {
      let bface = br.face
      let bp = br.path
      out_bs.push(
        tube_branch(bface, (j : Dim) => {
          let dom_j = a_line(j)
          let xj = glue_equiv_restrict_arg_under_face(bface, dom_j, x_path(j))
          dapp_typed(bp(j), xj, dom_j)
        }),
      )
    }
    let b_branches = dsystem_of(out_bs)
    comp_value(
      b_line,
      b_branches,
      dapp_typed(base, x_path(DZero), a_line(DZero)),
      dlevel,
    )
  })
}

///|
pub fn comp_sigma_value(
  line : (Dim) -> DValue,
  branches : DSystem,
  base : DValue,
  dlevel : Int32,
) -> DValue {
  let a_line = (j : Dim) => line_sigma_at(line, j).dom
  let fam_at = (j : Dim) => line_sigma_at(line, j).fam
  let fst_branches = map_branches(branches, p => {
    (j : Dim) => dfst_typed(p(j), fam_at(j))
  })
  let a_fill = fill_value(
    a_line,
    fst_branches,
    dfst_typed(base, fam_at(DZero)),
    dlevel,
  )
  let b_line = (j : Dim) => fam_at(j)(a_fill(j))
  let snd_branches = map_branches(branches, p => {
    (j : Dim) => dsnd_typed(p(j), a_line(j), fam_at(j))
  })
  DVPair(
    a_fill(DOne),
    comp_value(
      b_line,
      snd_branches,
      dsnd_typed(base, a_line(DZero), fam_at(DZero)),
      dlevel,
    ),
  )
}

///|
pub fn comp_path_value(
  line : (Dim) -> DValue,
  branches : DSystem,
  base : DValue,
  dlevel : Int32,
) -> DValue {
  DVPathLam(k => {
    let a_line = (j : Dim) => (path_at(line, j).line)(k)
    let mapped = map_branches(branches, p => (j : Dim) => dapp_dim(p(j), k))
    mapped.branches.push(
      tube_branch(face_simplify(FEq0(k)), j => path_at(line, j).left),
    )
    mapped.branches.push(
      tube_branch(face_simplify(FEq1(k)), j => path_at(line, j).right),
    )
    comp_value(a_line, mapped, dapp_dim(base, k), dlevel + 1)
  })
}

///|
/// hcomp in a universe.  The resulting semantic Glue retains the
/// entire partial type system; elements carry matching partial values.
pub fn comp_univ_value(
  line : (Dim) -> DValue,
  branches : DSystem,
  base : DValue,
  _dlevel : Int32,
) -> DValue {
  if branches.branches.length() == 0 {
    base
  } else {
    let lvl = match as_univ_level(line(DOne)) {
      Some(l) => l
      None => 0
    }
    DVGlue(branches, base, lvl)
  }
}

///|
/// Endpoint Glue structure of a line whose endpoint type may
/// have reduced away its (generic, path-based) Glue form -- the
/// analogue of `glue_equiv_endpoint_parts` for `DVGlue`.  This
/// arises for universe-valued eliminators over composite
/// points: the generic point is a `comp_univ_value` Glue while
/// the endpoints are plain types.  Branch faces are specialised
/// at the endpoint but bottom branches are retained, preserving
/// the branch-index alignment used by `comp_glue_value`.
fn glue_endpoint_parts(
  line : (Dim) -> DValue,
  d : Dim,
  dlevel : Int32,
) -> DGlueParts {
  let parts = glue_at(line, d)
  if parts.system.branches.length() > 0 {
    return parts
  }
  let generic = glue_at(line, DVar(dlevel))
  if generic.system.branches.length() == 0 {
    return parts
  }
  if dim_is_zero(d) || dim_is_one(d) {
    let val = dim_is_one(d)
    let bs : Array[DTubeBranch] = []
    for b in generic.system.branches {
      bs.push(
        tube_branch(face_simplify(face_subst(b.face, dlevel, val)), b.path),
      )
    }
    let system = DSystem::{ branches: bs, }
    DGlueParts::{
      system,
      face: dsystem_domain_face(system),
      line: generic.line,
      base: parts.base,
      level: generic.level,
    }
  } else {
    generic
  }
}

///|
fn glue_branch_path_at(
  line : (Dim) -> DValue,
  j : Dim,
  idx : Int32,
  dlevel : Int32,
) -> (Dim) -> DValue {
  let g = glue_at(line, j)
  if idx >= 0 && idx < g.system.branches.length() {
    return g.system.branches[idx].path
  }
  // At a collapsed endpoint the branch path survives only in
  // the generic Glue structure.
  let generic = glue_at(line, DVar(dlevel))
  if idx >= 0 && idx < generic.system.branches.length() {
    generic.system.branches[idx].path
  } else {
    _ => g.base
  }
}

///|
fn glue_branch_cap_line(
  line : (Dim) -> DValue,
  idx : Int32,
  dlevel : Int32,
) -> (Dim) -> DValue {
  (j : Dim) => glue_branch_path_at(line, j, idx, dlevel)(DOne)
}

///|
fn glue_partial_at(
  line : (Dim) -> DValue,
  j : Dim,
  packed : DValue,
  idx : Int32,
) -> DValue {
  let g = glue_at(line, j)
  let values = glue_partial_values(g, dfst_typed(packed, _ => g.base))
  if idx >= 0 && idx < values.length() {
    values[idx]
  } else {
    DVUnit
  }
}

///|
/// Pack an endpoint value into Glue pair form when the Glue face is
/// decided there (an unglued value under bot, a partial value under
/// top).  Generic Glue values are already pairs.  Multi-branch systems
/// pack one partial value for every type branch.
fn glue_pack_at(
  line : (Dim) -> DValue,
  d : Dim,
  v : DValue,
  dlevel : Int32,
) -> DValue {
  match force_value(v) {
    DVPair(_, _) => v
    _ => {
      let g = glue_at(line, d)
      if g.system.branches.length() == 0 {
        // The endpoint Glue may have collapsed to its base type (for
        // example hcompU at a decided face).  Probe the generic point
        // of the line so the base value is still packed against the
        // partial system used by the composition algorithm.
        let generic = glue_at(line, DVar(dlevel))
        if generic.system.branches.length() == 0 {
          v
        } else {
          let values : Array[DValue] = []
          for i in 0..<generic.system.branches.length() {
            values.push(
              coe_value(generic.system.branches[i].path, DZero, DOne, v, dlevel),
            )
          }
          DVPair(glue_store_partial(generic, values), v)
        }
      } else if face_is_bot_sem(g.face) {
        let values : Array[DValue] = []
        for i in 0..<g.system.branches.length() {
          values.push(
            coe_value(g.system.branches[i].path, DZero, DOne, v, dlevel),
          )
        }
        DVPair(glue_store_partial(g, values), v)
      } else if face_is_top_sem(g.face) {
        let values = glue_partial_values(g, v)
        let first = if values.length() > 0 { values[0] } else { DVUnit }
        DVPair(v, coe_value(g.line, DOne, DZero, first, dlevel))
      } else {
        v
      }
    }
  }
}

///|
pub fn comp_glue_value(
  line : (Dim) -> DValue,
  branches : DSystem,
  base : DValue,
  dlevel : Int32,
) -> DValue {
  let a_line = (j : Dim) => glue_at(line, j).base
  let packed_base = glue_pack_at(line, DZero, base, dlevel)
  let src = glue_endpoint_parts(line, DZero, dlevel)
  let tgt = glue_endpoint_parts(line, DOne, dlevel)
  let first_cap = glue_branch_cap_line(line, 0, dlevel)
  let snd_branches = map_branches(branches, p => {
    (j : Dim) => {
      dsnd_typed(glue_pack_at(line, j, p(j), dlevel), first_cap(j), _ => {
        a_line(j)
      })
    }
  })
  let base0 = dsnd_typed(packed_base, first_cap(DZero), _ => a_line(DZero))
  let a_raw = comp_value(a_line, snd_branches, base0, dlevel)
  let count = tgt.system.branches.length()
  let partial0 = glue_partial_values(
    src,
    dfst_typed(packed_base, _ => a_line(DZero)),
  )
  let fills : Array[(Dim) -> DValue] = []
  let t_outs : Array[DValue] = []
  for idx in 0..<count {
    let t_line = glue_branch_cap_line(line, idx, dlevel)
    let t_branches = map_branches(branches, p => {
      (j : Dim) => {
        glue_partial_at(line, j, glue_pack_at(line, j, p(j), dlevel), idx)
      }
    })
    let t_base = if idx < partial0.length() {
      partial0[idx]
    } else {
      coe_value(
        glue_branch_path_at(line, DZero, idx, dlevel),
        DZero,
        DOne,
        base0,
        dlevel,
      )
    }
    let t_fill = fill_value(t_line, t_branches, t_base, dlevel)
    fills.push(t_fill)
    // A branch whose face is bottom at the source carries no
    // source partial value to fill from; its target value is
    // the one compatible with the composed base value, obtained
    // by coercing along the branch path (as for a branch absent
    // at the source altogether).
    let src_active = idx < src.system.branches.length() &&
      !face_is_bot_sem(src.system.branches[idx].face)
    if !src_active {
      t_outs.push(
        coe_value(
          glue_branch_path_at(line, DOne, idx, dlevel),
          DZero,
          DOne,
          a_raw,
          dlevel,
        ),
      )
    } else {
      t_outs.push(t_fill(DOne))
    }
  }
  let a_out = if count == 0 {
    a_raw
  } else {
    let correction_branches : Array[DTubeBranch] = []
    for idx in 0..<count {
      let face = tgt.system.branches[idx].face
      let t_fill = fills[idx]
      let correction = (k : Dim) => {
        let down = coe_value(
          glue_branch_path_at(line, k, idx, dlevel),
          DOne,
          DZero,
          t_fill(k),
          dlevel,
        )
        coe_value(a_line, k, DOne, down, dlevel)
      }
      correction_branches.push(tube_branch(face, correction))
    }
    hcomp_value(a_line(DOne), dsystem_of(correction_branches), a_raw, dlevel)
  }
  if count == 0 || face_is_bot_sem(tgt.face) {
    a_out
  } else {
    // A top branch at the target collapses the Glue type to
    // that branch's partial type, for any branch count.
    let mut top = -1
    for idx in 0..<count {
      if face_is_top_sem(tgt.system.branches[idx].face) {
        top = idx
      }
    }
    if top >= 0 && top < t_outs.length() {
      t_outs[top]
    } else {
      DVPair(glue_store_partial(tgt, t_outs), a_out)
    }
  }
}

///|
/// hcomp in a universe, named explicitly: a partial type over a base
/// type composes to the Glue type.
pub fn hcomp_univ_value(
  level : Int32,
  branches : DSystem,
  base_ty : DValue,
  dlevel : Int32,
) -> DValue {
  hcomp_value(DVUniv(level), branches, base_ty, dlevel)
}

// ---------------------------------------------------------------------------
// Data-type compositions (constructor recursion)
// ---------------------------------------------------------------------------

///|
/// Recognize the canonical Bool forced by a stuck discrete
/// composition.  Only cap values are unfolded: a well-typed tube
/// in Bool cannot leave the constructor determined by its cap on
/// its prescribed face, and nested `hcomp`/`comp` neutrals arising
/// from open-box pasting therefore still have a Boolean normal
/// form when the base and every tube cap agree.
fn bool_cap_value(v : DValue, depth : Int32) -> Bool? {
  if depth <= 0 {
    return None
  }
  match force_value(v) {
    DVBool(b) => Some(b)
    DVNeutral(DNComp(_, branches, base)) =>
      match top_branch(branches) {
        Some(br) => bool_cap_value((br.path)(DOne), depth - 1)
        None =>
          match bool_cap_value(base, depth - 1) {
            Some(bb) => {
              let mut ok = true
              for i in 0..<branches.branches.length() {
                if bool_cap_value((branches.branches[i].path)(DOne), depth - 1) !=
                  Some(bb) {
                  ok = false
                }
              }
              if ok {
                Some(bb)
              } else {
                None
              }
            }
            None => None
          }
      }
    DVNeutral(DNHComp(_, branches, base)) =>
      match top_branch(branches) {
        Some(br) => bool_cap_value((br.path)(DOne), depth - 1)
        None =>
          match bool_cap_value(base, depth - 1) {
            Some(bb) => {
              let mut ok = true
              for i in 0..<branches.branches.length() {
                if bool_cap_value((branches.branches[i].path)(DOne), depth - 1) !=
                  Some(bb) {
                  ok = false
                }
              }
              if ok {
                Some(bb)
              } else {
                None
              }
            }
            None => None
          }
      }
    _ => None
  }
}

///|
pub fn comp_bool_value(
  line : (Dim) -> DValue,
  branches : DSystem,
  base : DValue,
  dlevel : Int32,
) -> DValue {
  ignore(dlevel)
  if branches.branches.length() == 0 {
    return base
  }
  match bool_cap_value(base, 32) {
    Some(bb) => {
      let mut ok = true
      for i in 0..<branches.branches.length() {
        if bool_cap_value((branches.branches[i].path)(DOne), 32) != Some(bb) {
          ok = false
        }
      }
      if ok {
        DVBool(bb)
      } else {
        DVNeutral(DNComp(line, branches, base))
      }
    }
    None => DVNeutral(DNComp(line, branches, base))
  }
}

///|
fn pred_of(v : DValue) -> DValue? {
  match force_value(v) {
    DVSucc(n) => Some(n)
    _ => None
  }
}

///|
fn pred_or_zero(v : DValue) -> DValue {
  match pred_of(v) {
    Some(n) => n
    None => DVZeroNat
  }
}

///|
fn head_or_unit(v : DValue) -> DValue {
  match cons_head(v) {
    Some(h) => h
    None => DVUnit
  }
}

///|
fn tail_or_nil(v : DValue) -> DValue {
  match cons_tail(v) {
    Some(t) => t
    None => DVNil
  }
}

///|
pub fn comp_nat_value(
  line : (Dim) -> DValue,
  branches : DSystem,
  base : DValue,
  dlevel : Int32,
) -> DValue {
  if branches.branches.length() == 0 {
    return base
  }
  match force_value(base) {
    DVZeroNat => {
      let mut ok = true
      for i in 0..<branches.branches.length() {
        match force_value((branches.branches[i].path)(DVar(dlevel))) {
          DVZeroNat => ()
          _ => ok = false
        }
      }
      if ok {
        DVZeroNat
      } else {
        DVNeutral(DNComp(line, branches, base))
      }
    }
    DVSucc(n) => {
      let mut ok = true
      for i in 0..<branches.branches.length() {
        match pred_of((branches.branches[i].path)(DVar(dlevel))) {
          Some(_) => ()
          None => ok = false
        }
      }
      if ok {
        let pred_branches = map_branches(branches, p => {
          (j : Dim) => pred_or_zero(p(j))
        })
        DVSucc(comp_value(line, pred_branches, n, dlevel))
      } else {
        DVNeutral(DNComp(line, branches, base))
      }
    }
    _ => DVNeutral(DNComp(line, branches, base))
  }
}

///|
fn cons_head(v : DValue) -> DValue? {
  match force_value(v) {
    DVCons(x, _) => Some(x)
    _ => None
  }
}

///|
fn cons_tail(v : DValue) -> DValue? {
  match force_value(v) {
    DVCons(_, xs) => Some(xs)
    _ => None
  }
}

///|
pub fn comp_list_value(
  line : (Dim) -> DValue,
  branches : DSystem,
  base : DValue,
  dlevel : Int32,
) -> DValue {
  if branches.branches.length() == 0 {
    return base
  }
  match force_value(base) {
    DVNil => {
      let mut ok = true
      for i in 0..<branches.branches.length() {
        match force_value((branches.branches[i].path)(DVar(dlevel))) {
          DVNil => ()
          _ => ok = false
        }
      }
      if ok {
        DVNil
      } else {
        DVNeutral(DNComp(line, branches, base))
      }
    }
    DVCons(x, xs) => {
      let mut ok = true
      for i in 0..<branches.branches.length() {
        match cons_head((branches.branches[i].path)(DVar(dlevel))) {
          Some(_) => ()
          None => ok = false
        }
      }
      if ok {
        let elem_line = (j : Dim) => list_elem_at(line, j)
        let head_branches = map_branches(branches, p => {
          (j : Dim) => head_or_unit(p(j))
        })
        let tail_branches = map_branches(branches, p => {
          (j : Dim) => tail_or_nil(p(j))
        })
        DVCons(
          comp_value(elem_line, head_branches, x, dlevel),
          comp_value(line, tail_branches, xs, dlevel),
        )
      } else {
        DVNeutral(DNComp(line, branches, base))
      }
    }
    _ => DVNeutral(DNComp(line, branches, base))
  }
}

// ---------------------------------------------------------------------------
// HIT compositions: point-valued boxes compose by De Morgan selection
// ---------------------------------------------------------------------------

///|
/// The characteristic dimension of a face: a `Dim` that is `1`
/// exactly where the face holds (vertex semantics).  `(r = 0)`
/// has characteristic `~r`, `(r = 1)` has `r`, and the face
/// connectives map to the De Morgan connectives.
pub fn dim_of_face(f : Face) -> Dim {
  match f {
    FTop => DOne
    FBot => DZero
    FEq0(r) => DNeg(r)
    FEq1(r) => r
    FAnd(a, b) => DAnd(dim_of_face(a), dim_of_face(b))
    FOr(a, b) => DOr(dim_of_face(a), dim_of_face(b))
  }
}

///|
fn is_circle_base(v : DValue) -> Bool {
  match force_value(v) {
    DVCirclePoint(r) => dim_is_zero(r) || dim_is_one(r)
    _ => false
  }
}

///|
/// Candidate cap coordinates for point-valued composition,
/// in preference order.  The first is the iterated De Morgan
/// selection (the kernel's traditional filler); the others
/// are rewritings that exploit endpoint identification
/// differently -- e.g. an undamped join of the branch caps,
/// which keeps a traversed loop's coordinate where iterated
/// selection through an endpoint face would replace it by a
/// tent.  Callers must verify the chosen candidate against
/// every branch cap on its face (`circle_coord_agrees_on_face`);
/// unverified candidates are never returned.
fn circle_coord_candidates(
  base_coord : Dim,
  deltas : Array[Dim],
  caps : Array[Dim],
) -> Array[Dim] {
  let out : Array[Dim] = []
  let n = caps.length()
  // 1. Iterated selection, branch order.
  let mut c1 = base_coord
  for i in 0..<n {
    c1 = dim_simplify(DOr(DAnd(deltas[i], caps[i]), DAnd(DNeg(deltas[i]), c1)))
  }
  out.push(c1)
  // 2. Iterated selection, reverse order.
  let mut c2 = base_coord
  for i in 0..<n {
    let j = n - 1 - i
    c2 = dim_simplify(DOr(DAnd(deltas[j], caps[j]), DAnd(DNeg(deltas[j]), c2)))
  }
  out.push(c2)
  // 3. Undamped join of caps, base damped by all complements.
  let mut join : Dim = DZero
  let mut none : Dim = DOne
  for i in 0..<n {
    join = DOr(join, caps[i])
    none = DAnd(none, DNeg(deltas[i]))
  }
  out.push(dim_simplify(DOr(join, DAnd(none, base_coord))))
  // 4. One-shot damped selection.
  let mut damped : Dim = DZero
  for i in 0..<n {
    damped = DOr(damped, DAnd(deltas[i], caps[i]))
  }
  out.push(dim_simplify(DOr(damped, DAnd(none, base_coord))))
  // 5. Damped join over the base.
  out.push(dim_simplify(DOr(base_coord, damped)))
  // 6. Active non-base loop selection: base-valued branches (`0` or `1`)
  //    identify `0 ~ 1` in `S^1`, so damping only non-base branches avoids
  //    turning higher-cube endpoint tubes into tents while covering-lifted
  //    variants lift up to 4 base-point caps from `0` to `1`.
  let mut active_damped : Dim = DZero
  let mut active_none : Dim = DOne
  let base_indices : Array[Int32] = []
  for i in 0..<n {
    if dim_is_zero(caps[i]) || dim_is_one(caps[i]) {
      base_indices.push(i)
    } else {
      active_damped = DOr(active_damped, DAnd(deltas[i], caps[i]))
      active_none = DAnd(active_none, DNeg(deltas[i]))
    }
  }
  out.push(dim_simplify(DOr(active_damped, DAnd(active_none, base_coord))))
  if base_indices.length() > 0 && base_indices.length() <= 4 {
    let mask_count = 1 << base_indices.length()
    for mask in 1..<mask_count {
      let mut lifted = base_coord
      for i in 0..<n {
        let mut cap_i = caps[i]
        for bi in 0..<base_indices.length() {
          if base_indices[bi] == i && (mask & (1 << bi)) != 0 {
            cap_i = DOne
          }
        }
        lifted = dim_simplify(
          DOr(DAnd(deltas[i], cap_i), DAnd(DNeg(deltas[i]), lifted)),
        )
      }
      out.push(lifted)
    }
  }
  out
}

///|
fn circle_sem_coord_norm(r : Dim) -> Dim {
  let s = dim_simplify(r)
  if dim_is_zero(s) || dim_is_one(s) {
    DZero
  } else {
    circle_dim_of(circle_point(s))
  }
}

///|
/// Does the coordinate expression `coord` restrict to the
/// coordinate `q` on every satisfying cube of `face`, as
/// circle points (endpoint coordinates identified)?  Checked
/// by substituting each cube's assigned dimensions and
/// comparing endpoint-normalised coordinates with vertex
/// semantics (including semantically constant `1` expressions
/// such as `¬i ∨ i`).  Returns false (do not trust the selection)
/// when the face has more cubes than the audit budget.
fn circle_coord_agrees_on_face(coord : Dim, face : Face, q : Dim) -> Bool {
  let mut n = face_nvars_sem(face)
  let nc = dim_nvars_sem(coord)
  if nc > n {
    n = nc
  }
  let nq = dim_nvars_sem(q)
  if nq > n {
    n = nq
  }
  let cubes = bdd_satisfying_cubes(bdd_of_face(face, n), n)
  if cubes.length() > 256 {
    return false
  }
  for c in 0..<cubes.length() {
    let cube = cubes[c]
    let mut rc = coord
    let mut rq = q
    for v in 0..<cube.length() {
      if cube[v] == 0 {
        rc = dim_subst(rc, v, false)
        rq = dim_subst(rq, v, false)
      } else if cube[v] == 1 {
        rc = dim_subst(rc, v, true)
        rq = dim_subst(rq, v, true)
      }
    }
    let nc2 = circle_sem_coord_norm(rc)
    let nq2 = circle_sem_coord_norm(rq)
    if !dim_eq_sem(nc2, nq2) {
      return false
    }
  }
  true
}

///|
/// Composition in the circle.  Boxes whose base and tubes are all
/// the base point reduce to the base point.  More generally, if
/// the base and every tube are *point-valued* (at a generic
/// dimension and at the cap), the cap is computed coordinatewise
/// by iterated De Morgan selection
///
///   c := coord(base);
///   c := (delta_i and coord(path_i(1))) or (~delta_i and c)
///
/// where `delta_i` is the characteristic dimension of branch
/// `i`'s face.  Circle-point conversion in this kernel is
/// vertex-semantic equality of coordinates (after `circle_point`
/// endpoint normalisation), and pairwise compatibility of the
/// system makes the branch coordinates agree on overlaps in
/// exactly that sense, so the selected coordinate restricts to
/// each branch's cap coordinate on its face.  Boxes that are not
/// point-valued remain formal `DNComp` neutrals.
pub fn comp_circle_value(
  line : (Dim) -> DValue,
  branches : DSystem,
  base : DValue,
  dlevel : Int32,
) -> DValue {
  if branches.branches.length() == 0 {
    return base
  }
  let mut ok = is_circle_base(base)
  for i in 0..<branches.branches.length() {
    if !is_circle_base((branches.branches[i].path)(DVar(dlevel))) {
      ok = false
    }
  }
  if ok {
    return DVCirclePoint(DZero)
  }
  let base_coord = match force_value(base) {
    DVCirclePoint(_) => circle_dim_of(circle_point(circle_dim_of(base)))
    _ => return DVNeutral(DNComp(line, branches, base))
  }
  let faces : Array[Face] = []
  let caps : Array[Dim] = []
  for i in 0..<branches.branches.length() {
    let br = branches.branches[i]
    let generic = (br.path)(DVar(dlevel))
    let cap = (br.path)(DOne)
    match (force_value(generic), force_value(cap)) {
      (DVCirclePoint(_), DVCirclePoint(_)) => {
        // The branch cap coordinate, read from the generic
        // branch value by substituting the composition
        // direction to 1 *in the coordinate expression*.  This
        // preserves a coordinate of 1 (a traversed loop), which
        // reading the evaluated cap would normalise to the
        // base point 0 -- losing exactly the winding that
        // path-valued composition must keep.  The substituted
        // coordinate is used only when it denotes the same
        // point as the evaluated cap.
        let q_cap = circle_dim_of(circle_point(circle_dim_of(cap)))
        let q_sub = dim_simplify(
          dim_subst(circle_dim_of(generic), dlevel, true),
        )
        let q = if dim_eq_sem(circle_dim_of(circle_point(q_sub)), q_cap) {
          q_sub
        } else {
          q_cap
        }
        faces.push(br.face)
        caps.push(q)
      }
      _ => return DVNeutral(DNComp(line, branches, base))
    }
  }
  // De Morgan selection through a face whose variable also
  // traverses the coordinates can damage the interior of
  // another branch's restriction, because endpoint
  // identification (coordinate 1 is the base point) is not a
  // congruence of the dimension algebra: selecting a base cap
  // over an endpoint face of a path-valued box replaces a
  // traversed loop by a tent.  Try the candidate coordinates
  // in order and return the first that verifies against
  // every branch cap on its face; boxes with no verifying
  // candidate stay formal `DNComp` rather than computing to
  // a point whose restrictions are wrong.
  let deltas : Array[Dim] = []
  for i in 0..<faces.length() {
    deltas.push(dim_of_face(faces[i]))
  }
  let candidates = circle_coord_candidates(base_coord, deltas, caps)
  for ci in 0..<candidates.length() {
    let coord = candidates[ci]
    let mut verified = true
    for i in 0..<faces.length() {
      if !circle_coord_agrees_on_face(coord, faces[i], caps[i]) {
        verified = false
      }
    }
    if verified {
      return circle_point(coord)
    }
  }
  let minterm_cands = circle_cube_minterm_candidates(faces, caps)
  for ci in 0..<minterm_cands.length() {
    let coord = minterm_cands[ci]
    let mut verified = true
    for i in 0..<faces.length() {
      if !circle_coord_agrees_on_face(coord, faces[i], caps[i]) {
        verified = false
      }
    }
    if verified {
      return circle_point(coord)
    }
  }
  DVNeutral(DNComp(line, branches, base))
}

///|
fn is_torus_base(v : DValue) -> Bool {
  match force_value(v) {
    DVTorusPoint(a, b) =>
      (dim_is_zero(a) || dim_is_one(a)) && (dim_is_zero(b) || dim_is_one(b))
    _ => false
  }
}

///|
fn torus_coord_pair(v : DValue) -> (Dim, Dim) {
  let (a, b) = torus_dims_of(v)
  torus_dims_of(torus_point(a, b))
}

///|
/// Composition in the torus: the circle's De Morgan selection
/// applied to both coordinates (see `comp_circle_value`).
pub fn comp_torus_value(
  line : (Dim) -> DValue,
  branches : DSystem,
  base : DValue,
  dlevel : Int32,
) -> DValue {
  if branches.branches.length() == 0 {
    return base
  }
  let mut ok = is_torus_base(base)
  for i in 0..<branches.branches.length() {
    if !is_torus_base((branches.branches[i].path)(DVar(dlevel))) {
      ok = false
    }
  }
  if ok {
    return DVTorusPoint(DZero, DZero)
  }
  let start = match force_value(base) {
    DVTorusPoint(_, _) => torus_coord_pair(base)
    _ => return DVNeutral(DNComp(line, branches, base))
  }
  let faces : Array[Face] = []
  let caps_a : Array[Dim] = []
  let caps_b : Array[Dim] = []
  for i in 0..<branches.branches.length() {
    let br = branches.branches[i]
    let generic = (br.path)(DVar(dlevel))
    let cap = (br.path)(DOne)
    match (force_value(generic), force_value(cap)) {
      (DVTorusPoint(_, _), DVTorusPoint(_, _)) => {
        // Generic-coordinate substitution, as in
        // `comp_circle_value`: keep a traversed loop's
        // coordinate 1 instead of the normalised base 0.
        let (qa_cap, qb_cap) = torus_coord_pair(cap)
        let (ga, gb) = torus_dims_of(generic)
        let qa_sub = dim_simplify(dim_subst(ga, dlevel, true))
        let qb_sub = dim_simplify(dim_subst(gb, dlevel, true))
        let (na, nb) = torus_dims_of(torus_point(qa_sub, qb_sub))
        let (qa, qb) = if dim_eq_sem(na, qa_cap) && dim_eq_sem(nb, qb_cap) {
          (qa_sub, qb_sub)
        } else {
          (qa_cap, qb_cap)
        }
        faces.push(br.face)
        caps_a.push(qa)
        caps_b.push(qb)
      }
      _ => return DVNeutral(DNComp(line, branches, base))
    }
  }
  // Candidate search and restriction verification, as in
  // `comp_circle_value` (endpoint identification applies
  // coordinatewise; both coordinates use the same candidate).
  let deltas : Array[Dim] = []
  for i in 0..<faces.length() {
    deltas.push(dim_of_face(faces[i]))
  }
  let cands_a = circle_coord_candidates(start.0, deltas, caps_a)
  let cands_b = circle_coord_candidates(start.1, deltas, caps_b)
  let mut chosen_a : Dim? = None
  for ca in 0..<cands_a.length() {
    let mut ok_a = true
    for i in 0..<faces.length() {
      if !circle_coord_agrees_on_face(cands_a[ca], faces[i], caps_a[i]) {
        ok_a = false
        break
      }
    }
    if ok_a {
      chosen_a = Some(cands_a[ca])
      break
    }
  }
  if chosen_a == None {
    let mc_a = circle_cube_minterm_candidates(faces, caps_a)
    for ca in 0..<mc_a.length() {
      let mut ok_a = true
      for i in 0..<faces.length() {
        if !circle_coord_agrees_on_face(mc_a[ca], faces[i], caps_a[i]) {
          ok_a = false
          break
        }
      }
      if ok_a {
        chosen_a = Some(mc_a[ca])
        break
      }
    }
  }
  let mut chosen_b : Dim? = None
  for cb in 0..<cands_b.length() {
    let mut ok_b = true
    for i in 0..<faces.length() {
      if !circle_coord_agrees_on_face(cands_b[cb], faces[i], caps_b[i]) {
        ok_b = false
        break
      }
    }
    if ok_b {
      chosen_b = Some(cands_b[cb])
      break
    }
  }
  if chosen_b == None {
    let mc_b = circle_cube_minterm_candidates(faces, caps_b)
    for cb in 0..<mc_b.length() {
      let mut ok_b = true
      for i in 0..<faces.length() {
        if !circle_coord_agrees_on_face(mc_b[cb], faces[i], caps_b[i]) {
          ok_b = false
          break
        }
      }
      if ok_b {
        chosen_b = Some(mc_b[cb])
        break
      }
    }
  }
  match (chosen_a, chosen_b) {
    (Some(ca), Some(cb)) => torus_point(ca, cb)
    _ => DVNeutral(DNComp(line, branches, base))
  }
}

// ---------------------------------------------------------------------------
// Phase 16: Cube-Minterm De Morgan Synthesis + Winding-Cocycle Obstruction &
// Endpoint-Glued (`0 ~ 1`) Square Cap Synthesis on `Circle` and `Torus`
// ---------------------------------------------------------------------------

///|
/// Synthesize additional De Morgan coordinate candidates from the satisfying
/// cube decomposition of `faces`: each non-base branch contributes a cube-
/// guarded minterm `cube_dim ∧ cap_i`, while base-valued cubes (`0 ~ 1`) may
/// either remain `0` or lift to `1` on corners forced to `1` by an overlapping
/// non-base branch.
fn circle_cube_minterm_candidates(
  faces : Array[Face],
  caps : Array[Dim],
) -> Array[Dim] {
  let out : Array[Dim] = []
  let mut nvars = 0
  for i in 0..<faces.length() {
    let nf = face_nvars_sem(faces[i])
    if nf > nvars {
      nvars = nf
    }
    let nc = dim_nvars_sem(caps[i])
    if nc > nvars {
      nvars = nc
    }
  }
  if nvars <= 0 || nvars > 5 {
    return out
  }
  let mut active_dnf : Dim = DZero
  let base_cubes : Array[Dim] = []
  for i in 0..<faces.length() {
    let cubes = bdd_satisfying_cubes(bdd_of_face(faces[i], nvars), nvars)
    if cubes.length() > 32 {
      return out
    }
    let is_base = dim_is_zero(caps[i]) || dim_is_one(caps[i])
    for c in 0..<cubes.length() {
      let cube = cubes[c]
      let mut cube_dim : Dim = DOne
      for v in 0..<cube.length() {
        if cube[v] == 0 {
          cube_dim = DAnd(cube_dim, DNeg(DVar(v)))
        } else if cube[v] == 1 {
          cube_dim = DAnd(cube_dim, DVar(v))
        }
      }
      if is_base {
        base_cubes.push(dim_simplify(cube_dim))
      } else {
        active_dnf = DOr(active_dnf, DAnd(cube_dim, caps[i]))
      }
    }
  }
  let simplified_active = dim_simplify(active_dnf)
  out.push(simplified_active)
  if base_cubes.length() > 0 && base_cubes.length() <= 5 {
    let mask_lim = 1 << base_cubes.length()
    for mask in 1..<mask_lim {
      let mut lifted = simplified_active
      for bi in 0..<base_cubes.length() {
        if (mask & (1 << bi)) != 0 {
          lifted = DOr(lifted, base_cubes[bi])
        }
      }
      out.push(dim_simplify(lifted))
    }
  }
  out
}

///|
/// Exact signed integer winding number of a 1D path `p : I -> Circle` whose
/// endpoints lie at the base point `0 ~ 1`. Supports elementary De Morgan
/// coordinates (`0`, `1`, `i`, `~i`) as well as iterated `DNComp` / `hcomp`
/// path concatenations and reversals.
pub fn circle_path_winding_int(
  path_fn : (Dim) -> DValue,
  dlevel~ : Int32 = 16,
) -> Int32? {
  let d = DVar(dlevel)
  circle_val_winding_wrt(path_fn(d), dlevel)
}

///|
fn circle_val_winding_wrt(v0 : DValue, var_id : Int32) -> Int32? {
  match force_value(v0) {
    DVCirclePoint(r) => {
      let r0 = dim_simplify(dim_subst(r, var_id, false))
      let r1 = dim_simplify(dim_subst(r, var_id, true))
      let b0 = if dim_is_zero(r0) {
        0
      } else if dim_is_one(r0) {
        1
      } else {
        return None
      }
      let b1 = if dim_is_zero(r1) {
        0
      } else if dim_is_one(r1) {
        1
      } else {
        return None
      }
      Some(b1 - b0)
    }
    DVNeutral(DNComp(_line, sys, base)) => {
      // By homotopy invariance along the box parameter `k : 0 -> 1`, the net
      // winding along `var_id : 0 -> 1` of the cap equals `winding(base)` plus
      // `winding(tube_{var_id=1})` minus `winding(tube_{var_id=0})`.
      let w_base = match circle_val_winding_wrt(base, var_id) {
        Some(w) => w
        None => return None
      }
      let mut w_at_0 = 0
      let mut w_at_1 = 0
      let k_id = var_id + 97
      for b in 0..<sys.branches.length() {
        let br = sys.branches[b]
        let f_at_0 = face_simplify(face_subst(br.face, var_id, false))
        let f_at_1 = face_simplify(face_subst(br.face, var_id, true))
        if f_at_0 == FTop {
          match
            circle_val_winding_wrt(
              dim_subst_in_circle_branch(br.path, var_id, false, k_id),
              k_id,
            ) {
            Some(dw) => w_at_0 = dw
            None => return None
          }
        }
        if f_at_1 == FTop {
          match
            circle_val_winding_wrt(
              dim_subst_in_circle_branch(br.path, var_id, true, k_id),
              k_id,
            ) {
            Some(dw) => w_at_1 = dw
            None => return None
          }
        }
      }
      Some(w_base + w_at_1 - w_at_0)
    }
    _ => None
  }
}

///|
fn dim_subst_in_circle_branch(
  path : (Dim) -> DValue,
  var_id : Int32,
  bit : Bool,
  k_id : Int32,
) -> DValue {
  match force_value(path(DVar(k_id))) {
    DVCirclePoint(r) => circle_point(dim_subst(r, var_id, bit))
    other => other
  }
}

///|
pub struct CircleSquareWindingReport {
  filler : DValue?
  corners_compatible : Bool
  winding_j0 : Int32
  winding_j1 : Int32
  winding_i0 : Int32
  winding_i1 : Int32
  net_boundary_winding : Int32
  used_hspace_glue : Bool
}

///|
fn elementary_signed_coord(w : Int32, d : Dim) -> Dim? {
  if w == 0 {
    Some(DZero)
  } else if w == 1 {
    Some(d)
  } else if w == -1 {
    Some(DNeg(d))
  } else {
    None
  }
}

///|
/// Canonical 2-cell square filler `(i, j) ↦ Circle` for an elementary signed
/// winding pair `(w_i, w_j) ∈ {-1, 0, 1}²` with boundary:
/// - `j = 0` and `j = 1`: `i ↦ circle_point(u(i))` (winding `w_i`)
/// - `i = 0` and `i = 1`: `j ↦ circle_point(v(j))` (winding `w_j`)
/// When `w_i != 0` and `w_j != 0`, corners agree ONLY via `0 ~ 1` so no single
/// `DVCirclePoint(r)` exists; the H-space `hcomp` retraction over
/// `circle_point(u(i) ∨ v(j))` restricts definitionally to all four faces!
fn circle_hspace_biloop_at(
  w_i : Int32,
  w_j : Int32,
  di : Dim,
  dj : Dim,
  dlevel : Int32,
) -> DValue? {
  if w_i == 0 {
    return match elementary_signed_coord(w_j, dj) {
      Some(v) => Some(circle_point(v))
      None => None
    }
  }
  if w_j == 0 {
    return match elementary_signed_coord(w_i, di) {
      Some(u) => Some(circle_point(u))
      None => None
    }
  }
  let (u, f_u0, f_u1) = if w_i == 1 {
    (di, FEq0(di), FEq1(di))
  } else if w_i == -1 {
    (DNeg(di), FEq1(di), FEq0(di))
  } else {
    return None
  }
  let (v, f_v0, f_v1) = if w_j == 1 {
    (dj, FEq0(dj), FEq1(dj))
  } else if w_j == -1 {
    (DNeg(dj), FEq1(dj), FEq0(dj))
  } else {
    return None
  }
  let sys = dsystem_of([
    tube_branch(f_u0, _k => circle_point(v)),
    tube_branch(f_u1, k => circle_point(DAnd(v, k))),
    tube_branch(f_v0, _k => circle_point(u)),
    tube_branch(f_v1, k => circle_point(DAnd(u, k))),
  ])
  Some(hcomp_value(DVCircleTy, sys, circle_point(DOr(u, v)), dlevel))
}

///|
/// Decide the 2-cocycle winding obstruction `δw = w(j=0) + w(i=1) - w(j=1) - w(i=0)`
/// of a 2D open boundary `(f_i0, f_i1, f_j0, f_j1)` in `Circle`, and synthesize
/// a face-verified 2-path filler `DVPathLam(i => DVPathLam(j => ...))` whenever
/// corners match (`0 ~ 1`) and either a De Morgan cap or an H-space `0 ~ 1`
/// glued square cap exists.
pub fn circle_square_glued_cap(
  f_i0 : (Dim) -> DValue,
  f_i1 : (Dim) -> DValue,
  f_j0 : (Dim) -> DValue,
  f_j1 : (Dim) -> DValue,
  level~ : Int32 = 0,
  dlevel~ : Int32 = 16,
) -> CircleSquareWindingReport {
  let c00 = conv_at(level, dlevel, DVCircleTy, f_i0(DZero), f_j0(DZero))
  let c01 = conv_at(level, dlevel, DVCircleTy, f_i0(DOne), f_j1(DZero))
  let c10 = conv_at(level, dlevel, DVCircleTy, f_i1(DZero), f_j0(DOne))
  let c11 = conv_at(level, dlevel, DVCircleTy, f_i1(DOne), f_j1(DOne))
  let corners_ok = c00 && c01 && c10 && c11
  let wi0 = match circle_path_winding_int(f_i0, dlevel~) {
    Some(w) => w
    None => 0
  }
  let wi1 = match circle_path_winding_int(f_i1, dlevel~) {
    Some(w) => w
    None => 0
  }
  let wj0 = match circle_path_winding_int(f_j0, dlevel~) {
    Some(w) => w
    None => 0
  }
  let wj1 = match circle_path_winding_int(f_j1, dlevel~) {
    Some(w) => w
    None => 0
  }
  let net = wj0 + wi1 - wj1 - wi0
  if !corners_ok || net != 0 {
    return CircleSquareWindingReport::{
      filler: None,
      corners_compatible: corners_ok,
      winding_j0: wj0,
      winding_j1: wj1,
      winding_i0: wi0,
      winding_i1: wi1,
      net_boundary_winding: net,
      used_hspace_glue: false,
    }
  }
  let verify_sq = (sq : DValue) => {
    let di = DVar(dlevel)
    let dj = DVar(dlevel + 1)
    conv_at(
      level,
      dlevel + 2,
      DVCircleTy,
      dapp_dim(dapp_dim(sq, DZero), dj),
      f_i0(dj),
    ) &&
    conv_at(
      level,
      dlevel + 2,
      DVCircleTy,
      dapp_dim(dapp_dim(sq, DOne), dj),
      f_i1(dj),
    ) &&
    conv_at(
      level,
      dlevel + 2,
      DVCircleTy,
      dapp_dim(dapp_dim(sq, di), DZero),
      f_j0(di),
    ) &&
    conv_at(
      level,
      dlevel + 2,
      DVCircleTy,
      dapp_dim(dapp_dim(sq, di), DOne),
      f_j1(di),
    )
  }
  // 1. Try direct single-coordinate De Morgan `comp_circle_value` first.
  let di_probe = DVar(dlevel)
  let dj_probe = DVar(dlevel + 1)
  let direct_sys = dsystem_of([
    tube_branch(FEq0(di_probe), _k => f_i0(dj_probe)),
    tube_branch(FEq1(di_probe), _k => f_i1(dj_probe)),
    tube_branch(FEq0(dj_probe), _k => f_j0(di_probe)),
    tube_branch(FEq1(dj_probe), _k => f_j1(di_probe)),
  ])
  let direct_pt = comp_circle_value(
    _ => DVCircleTy,
    direct_sys,
    DVCirclePoint(DZero),
    dlevel + 2,
  )
  match force_value(direct_pt) {
    DVCirclePoint(_) => {
      let sq = DVPathLam(i => {
        DVPathLam(j => {
          let sys_ij = dsystem_of([
            tube_branch(FEq0(i), _k => f_i0(j)),
            tube_branch(FEq1(i), _k => f_i1(j)),
            tube_branch(FEq0(j), _k => f_j0(i)),
            tube_branch(FEq1(j), _k => f_j1(i)),
          ])
          comp_circle_value(
            _ => DVCircleTy,
            sys_ij,
            DVCirclePoint(DZero),
            dlevel + 2,
          )
        })
      })
      if verify_sq(sq) {
        return CircleSquareWindingReport::{
          filler: Some(sq),
          corners_compatible: true,
          winding_j0: wj0,
          winding_j1: wj1,
          winding_i0: wi0,
          winding_i1: wi1,
          net_boundary_winding: 0,
          used_hspace_glue: false,
        }
      }
    }
    _ => ()
  }
  // 2. Endpoint-glued H-space `rotLoop` synthesis (`wj0 == wj1` and `wi0 == wi1`).
  if wj0 == wj1 && wi0 == wi1 {
    match circle_hspace_biloop_at(wj0, wi0, di_probe, dj_probe, dlevel + 2) {
      Some(_) => {
        let sq = DVPathLam(i => {
          DVPathLam(j => {
            match circle_hspace_biloop_at(wj0, wi0, i, j, dlevel + 2) {
              Some(v) => v
              None => DVCirclePoint(DZero)
            }
          })
        })
        if verify_sq(sq) {
          return CircleSquareWindingReport::{
            filler: Some(sq),
            corners_compatible: true,
            winding_j0: wj0,
            winding_j1: wj1,
            winding_i0: wi0,
            winding_i1: wi1,
            net_boundary_winding: 0,
            used_hspace_glue: true,
          }
        }
      }
      None => ()
    }
  }
  CircleSquareWindingReport::{
    filler: None,
    corners_compatible: true,
    winding_j0: wj0,
    winding_j1: wj1,
    winding_i0: wi0,
    winding_i1: wi1,
    net_boundary_winding: 0,
    used_hspace_glue: false,
  }
}

///|
/// Coordinatewise endpoint-glued 2-square synthesis on `Torus = S^1 x S^1`:
/// decomposes a 2D boundary `(f_i0, f_i1, f_j0, f_j1)` into its two circle
/// projections, checks both 2-cocycle winding obstructions `(net_a, net_b)`,
/// and pairs their H-space / De Morgan fillers into a `DVTorusTy` 2-path.
pub fn torus_square_glued_cap(
  f_i0 : (Dim) -> DValue,
  f_i1 : (Dim) -> DValue,
  f_j0 : (Dim) -> DValue,
  f_j1 : (Dim) -> DValue,
  level~ : Int32 = 0,
  dlevel~ : Int32 = 16,
) -> (DValue?, Int32, Int32) {
  let proj_a = (f : (Dim) -> DValue) => {
    (d : Dim) => {
      let (a, _b) = torus_dims_of(force_value(f(d)))
      circle_point(a)
    }
  }
  let proj_b = (f : (Dim) -> DValue) => {
    (d : Dim) => {
      let (_a, b) = torus_dims_of(force_value(f(d)))
      circle_point(b)
    }
  }
  let rep_a = circle_square_glued_cap(
    proj_a(f_i0),
    proj_a(f_i1),
    proj_a(f_j0),
    proj_a(f_j1),
    level~,
    dlevel~,
  )
  let rep_b = circle_square_glued_cap(
    proj_b(f_i0),
    proj_b(f_i1),
    proj_b(f_j0),
    proj_b(f_j1),
    level~,
    dlevel~,
  )
  match (rep_a.filler, rep_b.filler) {
    (Some(sq_a), Some(sq_b)) => {
      // Combine `sq_a(i, j) : Circle` and `sq_b(i, j) : Circle` into `Torus`
      // via circle elimination (`eval_circle_elim`).
      let embed_pair = (ca : DValue, cb : DValue) => {
        eval_circle_elim(
          _ => DVTorusTy,
          eval_circle_elim(
            _ => DVTorusTy,
            DVTorusPoint(DZero, DZero),
            DVPathLam(b => torus_point(DZero, b)),
            cb,
            dlevel + 4,
          ),
          DVPathLam(a => {
            eval_circle_elim(
              _ => DVTorusTy,
              torus_point(a, DZero),
              DVPathLam(b => torus_point(a, b)),
              cb,
              dlevel + 4,
            )
          }),
          ca,
          dlevel + 4,
        )
      }
      let sq = DVPathLam(i => {
        DVPathLam(j => {
          embed_pair(dapp_dim(dapp_dim(sq_a, i), j), dapp_dim(dapp_dim(sq_b, i), j))
        })
      })
      (Some(sq), rep_a.net_boundary_winding, rep_b.net_boundary_winding)
    }
    _ => (None, rep_a.net_boundary_winding, rep_b.net_boundary_winding)
  }
}
