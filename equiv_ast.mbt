///|
// First-class equivalences in the dependent cubical AST, Glue types
// presented by equivalences, and univalence.
//
// `DVEquiv` stores the two types, both functions, and the section
// and retraction Path-valued functions.  A `DVGlueEquiv` is the
// primitive semantic Glue type whose branches carry those
// equivalences directly; its composition uses equivFun/equivInv
// rather than first turning an equivalence into a type line.  The
// ua line of `e : A ≃ B` is the Glue family over B with the single
// branch `(i = 0) ↦ (A, e)`, so `coe` along ua computes by Glue
// composition to equivFun in one direction and equivInv in the
// other.

///|
pub struct DEquivTypeParts {
  src : DValue
  dst : DValue
  level : Int32
}

///|
pub fn as_equiv_type(v : DValue) -> DEquivTypeParts? {
  match force_value(v) {
    DVEquivTy(src, dst, level) => Some(DEquivTypeParts::{ src, dst, level, })
    _ => None
  }
}

///|
pub struct DEquivParts {
  src : DValue
  dst : DValue
  fwd : DValue
  bwd : DValue
  sect : DValue
  retr : DValue
}

///|
fn unwrap_equiv_neutral(n : DNeutral) -> DNeutral {
  match n {
    DNEquivAnn(inner, _, _) => unwrap_equiv_neutral(inner)
    other => other
  }
}

///|
pub fn equiv_fwd_value(e : DValue, src : DValue, dst : DValue) -> DValue {
  match force_value(e) {
    DVEquiv(_, _, f, _, _, _) => f
    DVNeutral(n) => {
      let inner = unwrap_equiv_neutral(n)
      DVLam(x => DVNeutral(DNApp(DNEquivFwd(inner, src, dst), x, src)))
    }
    _ => DVLam(_ => DVUnit)
  }
}

///|
pub fn equiv_bwd_value(e : DValue, src : DValue, dst : DValue) -> DValue {
  match force_value(e) {
    DVEquiv(_, _, _, g, _, _) => g
    DVNeutral(n) => {
      let inner = unwrap_equiv_neutral(n)
      DVLam(y => DVNeutral(DNApp(DNEquivBwd(inner, src, dst), y, dst)))
    }
    _ => DVLam(_ => DVUnit)
  }
}

///|
pub fn equiv_sect_value(e : DValue, src : DValue, dst : DValue) -> DValue {
  match force_value(e) {
    DVEquiv(_, _, _, _, s, _) => s
    DVNeutral(n) => {
      let inner = unwrap_equiv_neutral(n)
      DVLam(y => DVNeutral(DNApp(DNEquivSect(inner, src, dst), y, dst)))
    }
    _ => DVLam(_ => DVPathLam(_ => DVUnit))
  }
}

///|
pub fn equiv_retr_value(e : DValue, src : DValue, dst : DValue) -> DValue {
  match force_value(e) {
    DVEquiv(_, _, _, _, _, r) => r
    DVNeutral(n) => {
      let inner = unwrap_equiv_neutral(n)
      DVLam(x => DVNeutral(DNApp(DNEquivRetr(inner, src, dst), x, src)))
    }
    _ => DVLam(_ => DVPathLam(_ => DVUnit))
  }
}

///|
pub fn equiv_parts(e : DValue, src : DValue, dst : DValue) -> DEquivParts {
  match force_value(e) {
    DVEquiv(s, t, f, g, sect, retr) =>
      DEquivParts::{ src: s, dst: t, fwd: f, bwd: g, sect, retr, }
    _ =>
      DEquivParts::{
        src,
        dst,
        fwd: equiv_fwd_value(e, src, dst),
        bwd: equiv_bwd_value(e, src, dst),
        sect: equiv_sect_value(e, src, dst),
        retr: equiv_retr_value(e, src, dst),
      }
  }
}

///|
/// equivFun e x.
pub fn equiv_fun_value(
  e : DValue,
  src : DValue,
  dst : DValue,
  x : DValue,
) -> DValue {
  dapp_typed(equiv_fwd_value(e, src, dst), x, src)
}

///|
/// equivInv e y.
pub fn equiv_inv_fun_value(
  e : DValue,
  src : DValue,
  dst : DValue,
  y : DValue,
) -> DValue {
  dapp_typed(equiv_bwd_value(e, src, dst), y, dst)
}

///|
pub fn equiv_sect_type(
  src : DValue,
  dst : DValue,
  fwd : DValue,
  bwd : DValue,
) -> DValue {
  DVPi(dst, y => {
    DVPathTy(_ => dst, dapp_typed(fwd, dapp_typed(bwd, y, dst), src), y)
  })
}

///|
pub fn equiv_retr_type(
  src : DValue,
  dst : DValue,
  fwd : DValue,
  bwd : DValue,
) -> DValue {
  DVPi(src, x => {
    DVPathTy(_ => src, dapp_typed(bwd, dapp_typed(fwd, x, src), dst), x)
  })
}

///|
pub fn equiv_id_value(ty : DValue) -> DValue {
  DVEquiv(
    ty,
    ty,
    DVLam(x => x),
    DVLam(x => x),
    DVLam(x => DVPathLam(_ => x)),
    DVLam(x => DVPathLam(_ => x)),
  )
}

///|
pub fn equiv_inv_value(e : DValue, src : DValue, dst : DValue) -> DValue {
  let p = equiv_parts(e, src, dst)
  DVEquiv(p.dst, p.src, p.bwd, p.fwd, p.retr, p.sect)
}

///|
/// Build an equivalence value from its six components.
pub fn equiv_make_value(
  src : DValue,
  dst : DValue,
  fwd : DValue,
  bwd : DValue,
  sect : DValue,
  retr : DValue,
) -> DValue {
  DVEquiv(src, dst, fwd, bwd, sect, retr)
}

// ---------------------------------------------------------------------------
// Glue by equivalence: parts, packing, collapse
// ---------------------------------------------------------------------------

///|
pub fn glue_equiv_domain_face(branches : Array[DEquivBranchValue]) -> Face {
  let mut face = FBot
  for i in 0..<branches.length() {
    face = face_simplify(FOr(face, branches[i].face))
  }
  face
}

///|
pub fn as_glue_equiv(v : DValue) -> DGlueEquivParts? {
  match force_value(v) {
    DVGlueEquiv(branches, base, level) =>
      Some(DGlueEquivParts::{
        branches,
        face: glue_equiv_domain_face(branches),
        base,
        level,
      })
    _ => None
  }
}

///|
pub fn glue_equiv_top_index(parts : DGlueEquivParts) -> Int32 {
  for i in 0..<parts.branches.length() {
    if face_is_top_sem(parts.branches[i].face) {
      return i
    }
  }
  -1
}

///|
/// A Glue-by-equivalence type with a top branch is its partial type;
/// with bottom domain it is its base type.
pub fn glue_equiv_collapse(v : DValue) -> DValue {
  match as_glue_equiv(v) {
    Some(parts) => {
      let top = glue_equiv_top_index(parts)
      if top >= 0 {
        parts.branches[top].ty
      } else if face_is_bot_sem(parts.face) {
        parts.base
      } else {
        v
      }
    }
    None => v
  }
}

///|
fn glue_equiv_stored_values(
  parts : DGlueEquivParts,
  stored : DValue,
) -> Array[DValue] {
  let out : Array[DValue] = []
  match force_value(stored) {
    DVPartial(p) =>
      for i in 0..<parts.branches.length() {
        let wanted = parts.branches[i].face
        let mut found : DValue = DVUnit
        let mut ok = false
        for k in 0..<p.branches.length() {
          if same_face_sem(wanted, p.branches[k].face) {
            found = p.branches[k].value
            ok = true
            break
          }
        }
        if !ok && i < p.branches.length() {
          found = p.branches[i].value
        }
        out.push(found)
      }
    raw =>
      for _i in 0..<parts.branches.length() {
        out.push(raw)
      }
  }
  out
}

///|
pub fn glue_equiv_base_of(parts : DGlueEquivParts, v : DValue) -> DValue {
  let fv = force_value(v)
  match fv {
    DVPair(_, _) => {
      let first_ty = if parts.branches.length() > 0 {
        parts.branches[0].ty
      } else {
        DVUnitTy
      }
      dsnd_typed(fv, first_ty, _ => parts.base)
    }
    _ => {
      let top = glue_equiv_top_index(parts)
      if top >= 0 {
        let branch = parts.branches[top]
        equiv_fun_value(branch.equiv, branch.ty, parts.base, fv)
      } else if face_is_bot_sem(parts.face) {
        fv
      } else {
        match fv {
          DVNeutral(neu) => DVNeutral(DNUnglueEquiv(neu, parts))
          _ => fv
        }
      }
    }
  }
}

///|
pub fn glue_equiv_partial_values(
  parts : DGlueEquivParts,
  v : DValue,
) -> Array[DValue] {
  let fv = force_value(v)
  match fv {
    DVPair(first, _) => glue_equiv_stored_values(parts, first)
    _ => {
      let top = glue_equiv_top_index(parts)
      let base = glue_equiv_base_of(parts, fv)
      let out : Array[DValue] = []
      for i in 0..<parts.branches.length() {
        let branch = parts.branches[i]
        out.push(
          if i == top {
            fv
          } else {
            equiv_inv_fun_value(branch.equiv, branch.ty, parts.base, base)
          },
        )
      }
      out
    }
  }
}

///|
pub fn glue_equiv_store_partial(
  parts : DGlueEquivParts,
  values : Array[DValue],
) -> DValue {
  if values.length() == 0 {
    DVUnit
  } else if parts.branches.length() <= 1 {
    values[0]
  } else {
    let branches : Array[DFaceValue] = []
    for i in 0..<parts.branches.length() {
      let value = if i < values.length() { values[i] } else { DVUnit }
      branches.push(dface_value(parts.branches[i].face, value))
    }
    DVPartial(partial_of(branches))
  }
}

///|
/// The ua type line at one dimension: Glue over `dst` with the
/// branch `(d = 0) ↦ (src, e)`.
pub fn ua_type_at(
  e : DValue,
  src : DValue,
  dst : DValue,
  level : Int32,
  d : Dim,
) -> DValue {
  DVGlueEquiv([dequiv_branch_value(face_simplify(FEq0(d)), src, e)], dst, level)
}

///|
pub fn ua_line_value(
  e : DValue,
  src : DValue,
  dst : DValue,
  level : Int32,
) -> (Dim) -> DValue {
  (d : Dim) => ua_type_at(e, src, dst, level, d)
}

///|
pub fn ua_value(
  e : DValue,
  src : DValue,
  dst : DValue,
  level : Int32,
) -> DValue {
  DVPathLam(ua_line_value(e, src, dst, level))
}

// ---------------------------------------------------------------------------
// Evaluation and elaboration
// ---------------------------------------------------------------------------

///|
pub fn eval_mk_equiv_term(
  a : DTerm,
  b : DTerm,
  f : DTerm,
  g : DTerm,
  sect : DTerm,
  retr : DTerm,
  env : DEnv,
  denv : DDimEnv,
) -> DValue {
  DVEquiv(
    deval_dim(a, env, denv),
    deval_dim(b, env, denv),
    lazy_deval(f, env, denv),
    lazy_deval(g, env, denv),
    lazy_deval(sect, env, denv),
    lazy_deval(retr, env, denv),
  )
}

///|
pub fn eval_glue_equiv_term(
  base : DTerm,
  branches : Array[DEquivBranch],
  env : DEnv,
  denv : DDimEnv,
) -> DValue {
  let base_value = deval_dim(base, env, denv)
  let out : Array[DEquivBranchValue] = []
  for i in 0..<branches.length() {
    out.push(
      dequiv_branch_value(
        face_eval_env(branches[i].face, denv),
        deval_dim(branches[i].ty, env, denv),
        lazy_deval(branches[i].equiv, env, denv),
      ),
    )
  }
  DVGlueEquiv(out, base_value, 0)
}

///|
pub fn eval_unglue_equiv_term(
  term : DTerm,
  base : DTerm,
  branches : Array[DEquivBranch],
  env : DEnv,
  denv : DDimEnv,
) -> DValue {
  let glue_val = eval_glue_equiv_term(base, branches, env, denv)
  match as_glue_equiv(glue_val) {
    Some(parts) => glue_equiv_base_of(parts, deval_dim(term, env, denv))
    None => deval_dim(term, env, denv)
  }
}

///|
fn equiv_types_of_value(e : DValue) -> (DValue, DValue) {
  match force_value(e) {
    DVEquiv(src, dst, _, _, _, _) => (src, dst)
    DVNeutral(DNEquivAnn(_, src, dst)) => (src, dst)
    _ => (DVUnitTy, DVUnitTy)
  }
}

///|
pub fn eval_ua_term(e : DTerm, env : DEnv, denv : DDimEnv) -> DValue {
  let value = deval_dim(e, env, denv)
  let (src, dst) = equiv_types_of_value(value)
  ua_value(value, src, dst, 0)
}

///|
pub fn infer_equiv_ty(
  a : DTerm,
  b : DTerm,
  ctx : DEnv,
  env : DEnv,
  denv : DDimEnv,
) -> DInfer? {
  match (d_as_type(a, ctx, env, denv), d_as_type(b, ctx, env, denv)) {
    (Some(at), Some(bt)) => {
      let level = if at.level > bt.level { at.level } else { bt.level }
      Some(DInfer::{
        value: DVEquivTy(at.value, bt.value, level),
        ty: DVUniv(level),
      })
    }
    _ => None
  }
}

///|
pub fn infer_mk_equiv(
  a : DTerm,
  b : DTerm,
  f : DTerm,
  g : DTerm,
  sect : DTerm,
  retr : DTerm,
  ctx : DEnv,
  env : DEnv,
  denv : DDimEnv,
) -> DInfer? {
  match (d_as_type(a, ctx, env, denv), d_as_type(b, ctx, env, denv)) {
    (Some(at), Some(bt)) => {
      let src = at.value
      let dst = bt.value
      let level = if at.level > bt.level { at.level } else { bt.level }
      match
        (
          d_check(f, DVPi(src, _ => dst), ctx, env, denv),
          d_check(g, DVPi(dst, _ => src), ctx, env, denv),
        ) {
        (Some(fv), Some(gv)) =>
          match
            (
              d_check(sect, equiv_sect_type(src, dst, fv, gv), ctx, env, denv),
              d_check(retr, equiv_retr_type(src, dst, fv, gv), ctx, env, denv),
            ) {
            (Some(sv), Some(rv)) =>
              Some(DInfer::{
                value: DVEquiv(src, dst, fv, gv, sv, rv),
                ty: DVEquivTy(src, dst, level),
              })
            _ => None
          }
        _ => None
      }
    }
    _ => None
  }
}

///|
/// Projections are numbered 0=fwd, 1=bwd, 2=sect, 3=retr.
pub fn infer_equiv_projection(
  projection : Int32,
  e : DTerm,
  ctx : DEnv,
  env : DEnv,
  denv : DDimEnv,
) -> DInfer? {
  match d_infer(e, ctx, env, denv) {
    Some(inferred) =>
      match as_equiv_type(inferred.ty) {
        Some(parts) => {
          let value = inferred.value
          if projection == 0 {
            Some(DInfer::{
              value: equiv_fwd_value(value, parts.src, parts.dst),
              ty: DVPi(parts.src, _ => parts.dst),
            })
          } else if projection == 1 {
            Some(DInfer::{
              value: equiv_bwd_value(value, parts.src, parts.dst),
              ty: DVPi(parts.dst, _ => parts.src),
            })
          } else if projection == 2 {
            Some(DInfer::{
              value: equiv_sect_value(value, parts.src, parts.dst),
              ty: equiv_sect_type(
                parts.src,
                parts.dst,
                equiv_fwd_value(value, parts.src, parts.dst),
                equiv_bwd_value(value, parts.src, parts.dst),
              ),
            })
          } else if projection == 3 {
            Some(DInfer::{
              value: equiv_retr_value(value, parts.src, parts.dst),
              ty: equiv_retr_type(
                parts.src,
                parts.dst,
                equiv_fwd_value(value, parts.src, parts.dst),
                equiv_bwd_value(value, parts.src, parts.dst),
              ),
            })
          } else {
            None
          }
        }
        None => None
      }
    None => None
  }
}

///|
pub fn infer_glue_equiv(
  base : DTerm,
  branches : Array[DEquivBranch],
  ctx : DEnv,
  env : DEnv,
  denv : DDimEnv,
) -> DInfer? {
  match d_as_type(base, ctx, env, denv) {
    Some(bt) => {
      let mut level = bt.level
      let out : Array[DEquivBranchValue] = []
      for i in 0..<branches.length() {
        match d_as_type(branches[i].ty, ctx, env, denv) {
          Some(tt) => {
            if tt.level > level {
              level = tt.level
            }
            match
              d_check(
                branches[i].equiv,
                DVEquivTy(tt.value, bt.value, level),
                ctx,
                env,
                denv,
              ) {
              Some(ev) =>
                out.push(
                  dequiv_branch_value(
                    face_eval_env(branches[i].face, denv),
                    tt.value,
                    ev,
                  ),
                )
              None => return None
            }
          }
          None => return None
        }
      }
      Some(DInfer::{
        value: DVGlueEquiv(out, bt.value, level),
        ty: DVUniv(level),
      })
    }
    None => None
  }
}

///|
pub fn infer_unglue_equiv(
  term : DTerm,
  base : DTerm,
  branches : Array[DEquivBranch],
  ctx : DEnv,
  env : DEnv,
  denv : DDimEnv,
) -> DInfer? {
  match infer_glue_equiv(base, branches, ctx, env, denv) {
    Some(gi) =>
      match as_glue_equiv(gi.value) {
        Some(parts) =>
          match d_check(term, gi.value, ctx, env, denv) {
            Some(tv) =>
              Some(DInfer::{
                value: glue_equiv_base_of(parts, tv),
                ty: parts.base,
              })
            None => None
          }
        None => None
      }
    None => None
  }
}

///|
pub fn infer_ua(e : DTerm, ctx : DEnv, env : DEnv, denv : DDimEnv) -> DInfer? {
  match d_infer(e, ctx, env, denv) {
    Some(inferred) =>
      match as_equiv_type(inferred.ty) {
        Some(parts) =>
          Some(DInfer::{
            value: ua_value(inferred.value, parts.src, parts.dst, parts.level),
            ty: DVPathTy(_ => DVUniv(parts.level), parts.src, parts.dst),
          })
        None => None
      }
    None => None
  }
}

///|
/// Check the partial component of a Glue-by-equivalence pair.
pub fn d_check_glue_equiv_partial(
  a : DTerm,
  parts : DGlueEquivParts,
  ctx : DEnv,
  env : DEnv,
  denv : DDimEnv,
) -> Array[DValue]? {
  let values : Array[DValue] = []
  match a {
    DPartial(supplied) =>
      for i in 0..<parts.branches.length() {
        let branch = parts.branches[i]
        let mut body : DTerm = DUnitLit
        let mut found = false
        for k in 0..<supplied.length() {
          if same_face_sem(branch.face, face_eval_env(supplied[k].face, denv)) {
            body = supplied[k].body
            found = true
            break
          }
        }
        if !found {
          return None
        }
        match d_check(body, branch.ty, ctx, env, denv) {
          Some(v) => values.push(v)
          None => return None
        }
      }
    _ =>
      for i in 0..<parts.branches.length() {
        match d_check(a, parts.branches[i].ty, ctx, env, denv) {
          Some(v) => values.push(v)
          None => return None
        }
      }
  }
  Some(values)
}

// ---------------------------------------------------------------------------
// Conversion and quoting support
// ---------------------------------------------------------------------------

///|
fn glue_equiv_normalize(
  level : Int32,
  dlevel : Int32,
  base : DValue,
  branches : Array[DEquivBranchValue],
) -> Array[DEquivBranchValue] {
  let faces : Array[Face] = []
  let tys : Array[DValue] = []
  let equivs : Array[DValue] = []
  for i in 0..<branches.length() {
    let branch = branches[i]
    if face_is_bot_sem(branch.face) {
      continue
    }
    let mut merged = false
    for k in 0..<tys.length() {
      if conv_ty(level, dlevel, tys[k], branch.ty) &&
        conv_at(
          level,
          dlevel,
          DVEquivTy(tys[k], base, 0),
          equivs[k],
          branch.equiv,
        ) {
        faces[k] = face_simplify(FOr(faces[k], branch.face))
        merged = true
        break
      }
    }
    if !merged {
      faces.push(face_simplify(branch.face))
      tys.push(branch.ty)
      equivs.push(branch.equiv)
    }
  }
  let body_keys : Array[String] = []
  let face_keys : Array[String] = []
  for i in 0..<tys.length() {
    body_keys.push(
      dterm_cache_key(quote_ty(level, dlevel, tys[i])) +
      dterm_cache_key(
        quote_at(level, dlevel, DVEquivTy(tys[i], base, 0), equivs[i]),
      ),
    )
    face_keys.push(
      Repr(bdd_of_face(faces[i], face_nvars_sem(faces[i]))).to_string(),
    )
  }
  for _pass in 0..<tys.length() {
    for j in 0..<(tys.length() - 1) {
      let swap = body_keys[j + 1] < body_keys[j] ||
        (body_keys[j + 1] == body_keys[j] && face_keys[j + 1] < face_keys[j])
      if swap {
        let tmp_face = faces[j]
        faces[j] = faces[j + 1]
        faces[j + 1] = tmp_face
        let tmp_ty = tys[j]
        tys[j] = tys[j + 1]
        tys[j + 1] = tmp_ty
        let tmp_equiv = equivs[j]
        equivs[j] = equivs[j + 1]
        equivs[j + 1] = tmp_equiv
        let tmp_body = body_keys[j]
        body_keys[j] = body_keys[j + 1]
        body_keys[j + 1] = tmp_body
        let tmp_key = face_keys[j]
        face_keys[j] = face_keys[j + 1]
        face_keys[j + 1] = tmp_key
      }
    }
  }
  let out : Array[DEquivBranchValue] = []
  for i in 0..<tys.length() {
    out.push(dequiv_branch_value(faces[i], tys[i], equivs[i]))
  }
  out
}

///|
pub fn glue_equiv_systems_conv(
  level : Int32,
  dlevel : Int32,
  base : DValue,
  a : Array[DEquivBranchValue],
  b : Array[DEquivBranchValue],
) -> Bool {
  let na = glue_equiv_normalize(level, dlevel, base, a)
  let nb = glue_equiv_normalize(level, dlevel, base, b)
  if na.length() != nb.length() {
    return false
  }
  for i in 0..<na.length() {
    if !same_face_sem(na[i].face, nb[i].face) ||
      !conv_ty(level, dlevel, na[i].ty, nb[i].ty) ||
      !conv_at(
        level,
        dlevel,
        DVEquivTy(na[i].ty, base, 0),
        na[i].equiv,
        nb[i].equiv,
      ) {
      return false
    }
  }
  true
}

///|
pub fn quote_glue_equiv_type(
  level : Int32,
  dlevel : Int32,
  parts : DGlueEquivParts,
) -> DTerm {
  let branches : Array[DEquivBranch] = []
  for i in 0..<parts.branches.length() {
    let branch = parts.branches[i]
    branches.push(
      d_equiv_branch(
        face_quote(branch.face, dlevel),
        quote_ty(level, dlevel, branch.ty),
        quote_at(
          level,
          dlevel,
          DVEquivTy(branch.ty, parts.base, parts.level),
          branch.equiv,
        ),
      ),
    )
  }
  DGlueEquiv(quote_ty(level, dlevel, parts.base), branches)
}

///|
pub fn quote_unglue_equiv_neutral(
  level : Int32,
  dlevel : Int32,
  inner : DNeutral,
  parts : DGlueEquivParts,
) -> DTerm {
  let glue_ty = DVGlueEquiv(parts.branches, parts.base, parts.level)
  let inner_term = quote_dneutral(level, dlevel, inner, glue_ty)
  match quote_glue_equiv_type(level, dlevel, parts) {
    DGlueEquiv(base_t, branches_t) => DUnglueEquiv(inner_term, base_t, branches_t)
    _ => inner_term
  }
}

///|
/// The AST type former for equivalences.
pub fn equiv_type_term(a : DTerm, b : DTerm) -> DTerm {
  DEquivTy(a, b)
}

///|
pub fn mk_equiv_term(
  a : DTerm,
  b : DTerm,
  f : DTerm,
  g : DTerm,
  sect : DTerm,
  retr : DTerm,
) -> DTerm {
  DMkEquiv(a, b, f, g, sect, retr)
}

///|
pub fn glue_equiv_term(base : DTerm, branches : Array[DEquivBranch]) -> DTerm {
  DGlueEquiv(base, branches)
}

///|
pub fn ua_term(e : DTerm) -> DTerm {
  DUa(e)
}

// ---------------------------------------------------------------------------
// Kan composition for equivalences and Glue by equivalence
// ---------------------------------------------------------------------------

///|
fn glue_equiv_at(line : (Dim) -> DValue, d : Dim) -> DGlueEquivParts {
  match as_glue_equiv(line(d)) {
    Some(parts) => parts
    None =>
      DGlueEquivParts::{ branches: [], face: FBot, base: line(d), level: 0, }
  }
}

///|
fn glue_equiv_pack_with(parts : DGlueEquivParts, v : DValue) -> DValue {
  match force_value(v) {
    DVPair(_, _) => v
    _ =>
      if parts.branches.length() == 0 {
        v
      } else {
        DVPair(
          glue_equiv_store_partial(parts, glue_equiv_partial_values(parts, v)),
          glue_equiv_base_of(parts, v),
        )
      }
  }
}

///|
/// Endpoint Glue structure of a line whose endpoint type may have
/// reduced away its Glue form (e.g. a universe-valued HIT eliminator
/// whose point case is a plain type while its path case is a `ua`
/// line).  When the endpoint itself carries no branches but the
/// generic point does, the endpoint structure is the generic one
/// with every branch face specialised at the endpoint: this is the
/// Glue structure the line has at that endpoint before reduction.
/// Lines whose endpoints are already Glue-shaped (term-level Glue
/// and `ua` lines) are returned unchanged.
fn glue_equiv_endpoint_parts(
  line : (Dim) -> DValue,
  d : Dim,
  dlevel : Int32,
) -> DGlueEquivParts {
  let parts = glue_equiv_at(line, d)
  if parts.branches.length() > 0 {
    return parts
  }
  let generic = glue_equiv_at(line, DVar(dlevel))
  if generic.branches.length() == 0 {
    return parts
  }
  if dim_is_zero(d) || dim_is_one(d) {
    let val = dim_is_one(d)
    let bs : Array[DEquivBranchValue] = []
    for b in generic.branches {
      bs.push(
        dequiv_branch_value(
          face_simplify(face_subst(b.face, dlevel, val)),
          b.ty,
          b.equiv,
        ),
      )
    }
    DGlueEquivParts::{
      branches: bs,
      face: glue_equiv_domain_face(bs),
      base: parts.base,
      level: generic.level,
    }
  } else {
    generic
  }
}

///|
fn glue_equiv_pack_at(
  line : (Dim) -> DValue,
  d : Dim,
  v : DValue,
  dlevel : Int32,
) -> DValue {
  match force_value(v) {
    DVPair(_, _) => v
    _ => glue_equiv_pack_with(glue_equiv_endpoint_parts(line, d, dlevel), v)
  }
}

///|
fn glue_equiv_branch_at(
  line : (Dim) -> DValue,
  d : Dim,
  idx : Int32,
) -> DEquivBranchValue {
  let parts = glue_equiv_at(line, d)
  if idx >= 0 && idx < parts.branches.length() {
    parts.branches[idx]
  } else {
    dequiv_branch_value(FBot, parts.base, equiv_id_value(parts.base))
  }
}

///|
fn glue_equiv_partial_at(
  line : (Dim) -> DValue,
  d : Dim,
  packed : DValue,
  idx : Int32,
) -> DValue {
  let parts = glue_equiv_at(line, d)
  let values = glue_equiv_partial_values(parts, packed)
  if idx >= 0 && idx < values.length() {
    values[idx]
  } else {
    DVUnit
  }
}

///|
/// Composition in a Glue-by-equivalence type.  This is the usual
/// Glue composition, with equivInv packing partial components and
/// equivFun supplying the correction path in the base.
pub fn comp_glue_equiv_value(
  line : (Dim) -> DValue,
  branches : DSystem,
  base : DValue,
  dlevel : Int32,
) -> DValue {
  let a_line = (j : Dim) => glue_equiv_at(line, j).base
  let generic = glue_equiv_at(line, DVar(dlevel))
  let first_ty = if generic.branches.length() > 0 {
    generic.branches[0].ty
  } else {
    DVUnitTy
  }
  let packed_base = glue_equiv_pack_at(line, DZero, base, dlevel)
  let src = glue_equiv_endpoint_parts(line, DZero, dlevel)
  let tgt = glue_equiv_endpoint_parts(line, DOne, dlevel)
  let snd_branches = map_branches(branches, p => {
    (j : Dim) => {
      dsnd_typed(glue_equiv_pack_at(line, j, p(j), dlevel), first_ty, _ => {
        a_line(j)
      })
    }
  })
  let base0 = dsnd_typed(packed_base, first_ty, _ => a_line(DZero))
  let a_raw = comp_value(a_line, snd_branches, base0, dlevel)
  let count = tgt.branches.length()
  if count == 0 {
    return a_raw
  }
  let partial0 = glue_equiv_partial_values(src, packed_base)
  let fills : Array[(Dim) -> DValue] = []
  let t_outs : Array[DValue] = []
  for idx in 0..<count {
    let t_line = (j : Dim) => glue_equiv_branch_at(line, j, idx).ty
    let t_branches = map_branches(branches, p => {
      (j : Dim) => {
        glue_equiv_partial_at(
          line,
          j,
          glue_equiv_pack_at(line, j, p(j), dlevel),
          idx,
        )
      }
    })
    let t_base = if idx < partial0.length() {
      partial0[idx]
    } else {
      let branch = glue_equiv_branch_at(line, DZero, idx)
      equiv_inv_fun_value(branch.equiv, branch.ty, a_line(DZero), base0)
    }
    let t_fill = fill_value(t_line, t_branches, t_base, dlevel)
    fills.push(t_fill)
    if idx >= src.branches.length() {
      let branch = glue_equiv_branch_at(line, DOne, idx)
      t_outs.push(
        equiv_inv_fun_value(branch.equiv, branch.ty, a_line(DOne), a_raw),
      )
    } else {
      t_outs.push(t_fill(DOne))
    }
  }
  let correction_branches : Array[DTubeBranch] = []
  for idx in 0..<count {
    let t_fill = fills[idx]
    let correction = (k : Dim) => {
      let branch = glue_equiv_branch_at(line, k, idx)
      let down = equiv_fun_value(branch.equiv, branch.ty, a_line(k), t_fill(k))
      coe_value(a_line, k, DOne, down, dlevel)
    }
    correction_branches.push(tube_branch(tgt.branches[idx].face, correction))
  }
  let a_out = hcomp_value(
    a_line(DOne),
    dsystem_of(correction_branches),
    a_raw,
    dlevel,
  )
  if face_is_bot_sem(tgt.face) {
    a_out
  } else {
    let top = glue_equiv_top_index(tgt)
    if top >= 0 && top < t_outs.length() {
      t_outs[top]
    } else {
      DVPair(glue_equiv_store_partial(tgt, t_outs), a_out)
    }
  }
}

///|
/// Under a tube branch face `face`, unwrap a `DVPair(partial, base_out)` of a
/// `DVGlueEquiv` domain whenever every cubical subcube of `face` selects a
/// single partial branch (yielding that partial component) or falsifies the
/// entire Glue extent (yielding the base component).
pub fn glue_equiv_restrict_arg_under_face(
  face : Face,
  dom : DValue,
  x : DValue,
) -> DValue {
  match (as_glue_equiv(dom), force_value(x)) {
    (Some(parts), DVPair(_, a_out)) => {
      if parts.branches.length() == 0 {
        return x
      }
      let mut dl : Int32 = 0
      for v in face_vars(face) {
        if v + 1 > dl {
          dl = v + 1
        }
      }
      for v in face_vars(parts.face) {
        if v + 1 > dl {
          dl = v + 1
        }
      }
      let cubes = cubical_face_subcubes(face, dl)
      if cubes.length() == 0 {
        return x
      }
      let mut all_bot = true
      for cube in cubes {
        let mut f_sub = parts.face
        for v in 0..<cube.length() {
          if cube[v] == 0 {
            f_sub = face_subst(f_sub, v, false)
          } else if cube[v] == 1 {
            f_sub = face_subst(f_sub, v, true)
          }
        }
        if !face_is_bot_sem(face_simplify(f_sub)) {
          all_bot = false
        }
      }
      if all_bot {
        return a_out
      }
      let pvals = glue_equiv_partial_values(parts, x)
      for idx in 0..<parts.branches.length() {
        let bface = parts.branches[idx].face
        let mut all_top = true
        for cube in cubes {
          let mut f_sub = bface
          for v in 0..<cube.length() {
            if cube[v] == 0 {
              f_sub = face_subst(f_sub, v, false)
            } else if cube[v] == 1 {
              f_sub = face_subst(f_sub, v, true)
            }
          }
          if !face_is_top_sem(face_simplify(f_sub)) {
            all_top = false
          }
        }
        if all_top && idx < pvals.length() {
          return pvals[idx]
        }
      }
      x
    }
    _ => x
  }
}

///|
fn equiv_type_at(line : (Dim) -> DValue, d : Dim) -> DEquivTypeParts {
  match as_equiv_type(line(d)) {
    Some(parts) => parts
    None => DEquivTypeParts::{ src: DVUnitTy, dst: DVUnitTy, level: 0, }
  }
}

///|
/// Composition of equivalences along a line of equivalence types:
/// compose both functions as Π-types, take their fills, and compose
/// the section and retraction proofs in the resulting Path families.
pub fn comp_equiv_value(
  line : (Dim) -> DValue,
  branches : DSystem,
  base : DValue,
  dlevel : Int32,
) -> DValue {
  let src_line = (j : Dim) => equiv_type_at(line, j).src
  let dst_line = (j : Dim) => equiv_type_at(line, j).dst
  let fwd_line = (j : Dim) => DVPi(src_line(j), _ => dst_line(j))
  let bwd_line = (j : Dim) => DVPi(dst_line(j), _ => src_line(j))
  let fwd_branches = map_branches(branches, p => {
    (j : Dim) => equiv_fwd_value(p(j), src_line(j), dst_line(j))
  })
  let bwd_branches = map_branches(branches, p => {
    (j : Dim) => equiv_bwd_value(p(j), src_line(j), dst_line(j))
  })
  let fwd_fill = fill_value(
    fwd_line,
    fwd_branches,
    equiv_fwd_value(base, src_line(DZero), dst_line(DZero)),
    dlevel,
  )
  let bwd_fill = fill_value(
    bwd_line,
    bwd_branches,
    equiv_bwd_value(base, src_line(DZero), dst_line(DZero)),
    dlevel,
  )
  let sect_line = (j : Dim) => {
    equiv_sect_type(src_line(j), dst_line(j), fwd_fill(j), bwd_fill(j))
  }
  let retr_line = (j : Dim) => {
    equiv_retr_type(src_line(j), dst_line(j), fwd_fill(j), bwd_fill(j))
  }
  let sect_branches = map_branches(branches, p => {
    (j : Dim) => equiv_sect_value(p(j), src_line(j), dst_line(j))
  })
  let retr_branches = map_branches(branches, p => {
    (j : Dim) => equiv_retr_value(p(j), src_line(j), dst_line(j))
  })
  let sect = comp_value(
    sect_line,
    sect_branches,
    equiv_sect_value(base, src_line(DZero), dst_line(DZero)),
    dlevel,
  )
  let retr = comp_value(
    retr_line,
    retr_branches,
    equiv_retr_value(base, src_line(DZero), dst_line(DZero)),
    dlevel,
  )
  DVEquiv(
    src_line(DOne),
    dst_line(DOne),
    fwd_fill(DOne),
    bwd_fill(DOne),
    sect,
    retr,
  )
}

///|
/// Boolean negation as an AST function.
pub fn bool_not_term() -> DTerm {
  DLam(DBoolTy, DBoolElim(DBoolTy, DBoolLit(false), DBoolLit(true), DTVar(0)))
}

///|
fn bool_not_not_proof_term() -> DTerm {
  // Dependent Bool elimination into the motive
  // `fun y => Path Bool (not (not y)) y`; both cases are refl.
  let not_x = DBoolElim(DBoolTy, DBoolLit(false), DBoolLit(true), DTVar(0))
  let not_not_x = DBoolElim(DBoolTy, DBoolLit(false), DBoolLit(true), not_x)
  let motive = DPath(DBoolTy, not_not_x, DTVar(0))
  DLam(
    DBoolTy,
    DBoolElim(
      motive,
      DLamDim(DBoolLit(true)),
      DLamDim(DBoolLit(false)),
      DTVar(0),
    ),
  )
}

///|
/// The negation equivalence `Bool ≃ Bool` as one closed AST term.
pub fn bool_not_equiv_term() -> DTerm {
  DMkEquiv(
    DBoolTy,
    DBoolTy,
    bool_not_term(),
    bool_not_term(),
    bool_not_not_proof_term(),
    bool_not_not_proof_term(),
  )
}

