///|
// Checked, substitutable semantic type lines.
//
// A raw semantic type line is a host function `Dim -> DValue`; such a
// function could in principle inspect dimension syntax in a way that
// does not respect dimension substitution.  A `DCheckedTypeLine`
// instead stores a DTerm body, checked as a type under one fresh
// dimension binder, together with the persistent environments in
// which that body is to be read.  Evaluating the stored body at a
// dimension is exactly dimension substitution, so every checked line
// is natural by construction.  The semantic function is memoized on
// simplified dimensions.
//
// The body follows the same dimension convention as the line argument
// of `DCoe`/`DComp`: `DVar(0)` is the line dimension and ambient
// dimensions are shifted by one.  A constant line stores an ambient
// type term instead and ignores the line dimension.

///|
pub struct DCheckedTypeLine {
  body : DTerm
  ctx : DEnv
  env : DEnv
  denv : DDimEnv
  level : Int32
  constant : Bool
  line : (Dim) -> DValue
}

///|
/// Validate `body` as a type under one fresh dimension and package it
/// as a substitutable type line.  The body is checked at a generic
/// dimension and at both endpoints.
pub fn checked_type_line(
  body : DTerm,
  ctx : DEnv,
  env : DEnv,
  denv : DDimEnv,
) -> DCheckedTypeLine? {
  let fresh = fresh_dim(denv)
  match d_as_type(body, ctx, env, ddim_cons(fresh, denv)) {
    Some(tv) => {
      let at_zero = d_as_type(body, ctx, env, ddim_cons(DZero, denv))
      let at_one = d_as_type(body, ctx, env, ddim_cons(DOne, denv))
      match (at_zero, at_one) {
        (Some(z), Some(o)) => {
          let mut level = tv.level
          if z.level > level {
            level = z.level
          }
          if o.level > level {
            level = o.level
          }
          Some(DCheckedTypeLine::{
            body,
            ctx,
            env,
            denv,
            level,
            constant: false,
            line: memo_dim_line(d => dtype_of_line(body, ctx, env, denv, d)),
          })
        }
        _ => None
      }
    }
    None => None
  }
}

///|
pub fn checked_type_line_closed(body : DTerm) -> DCheckedTypeLine? {
  checked_type_line(body, denv_empty(), denv_empty(), ddim_empty())
}

///|
/// A checked constant type line from an ambient type term.
pub fn checked_constant_type_line(
  ty : DTerm,
  ctx : DEnv,
  env : DEnv,
  denv : DDimEnv,
) -> DCheckedTypeLine? {
  match d_as_type(ty, ctx, env, denv) {
    Some(tv) =>
      Some(DCheckedTypeLine::{
        body: ty,
        ctx,
        env,
        denv,
        level: tv.level,
        constant: true,
        line: _ => tv.value,
      })
    None => None
  }
}

///|
pub fn checked_constant_type_line_closed(ty : DTerm) -> DCheckedTypeLine? {
  checked_constant_type_line(ty, denv_empty(), denv_empty(), ddim_empty())
}

///|
/// The checked line underlying a PathP type term.
pub fn checked_line_of_pathp_term(
  t : DTerm,
  ctx : DEnv,
  env : DEnv,
  denv : DDimEnv,
) -> DCheckedTypeLine? {
  match t {
    DPathP(line, _, _) => checked_type_line(line, ctx, env, denv)
    DPath(a, _, _) => checked_constant_type_line(a, ctx, env, denv)
    _ => None
  }
}

///|
/// The ua line of an equivalence term, as a checked line.  The
/// equivalence term is read with ambient dimensions shifted by the
/// line binder, exactly as in a `DCoe` line body; closed equivalence
/// terms need no adjustment.
pub fn checked_ua_line(
  equiv : DTerm,
  ctx : DEnv,
  env : DEnv,
  denv : DDimEnv,
) -> DCheckedTypeLine? {
  checked_type_line(DAppDim(DUa(equiv), DVar(0)), ctx, env, denv)
}

///|
pub fn checked_line_at(line : DCheckedTypeLine, d : Dim) -> DValue {
  (line.line)(d)
}

///|
pub fn checked_line_fn(line : DCheckedTypeLine) -> (Dim) -> DValue {
  line.line
}

///|
pub fn checked_line_body(line : DCheckedTypeLine) -> DTerm {
  line.body
}

///|
pub fn checked_line_level(line : DCheckedTypeLine) -> Int32 {
  line.level
}

///|
pub fn checked_line_is_constant(line : DCheckedTypeLine) -> Bool {
  line.constant
}

///|
pub fn checked_line_endpoints(line : DCheckedTypeLine) -> (DValue, DValue) {
  ((line.line)(DZero), (line.line)(DOne))
}

///|
/// Pointwise conversion of checked lines at a generic dimension and
/// at both endpoints.
pub fn checked_line_conv(
  level : Int32,
  dlevel : Int32,
  a : DCheckedTypeLine,
  b : DCheckedTypeLine,
) -> Bool {
  let fresh = DVar(dlevel)
  conv_ty(level, dlevel + 1, (a.line)(fresh), (b.line)(fresh)) &&
  conv_ty(level, dlevel, (a.line)(DZero), (b.line)(DZero)) &&
  conv_ty(level, dlevel, (a.line)(DOne), (b.line)(DOne))
}

///|
/// Quote the body of a checked line under its dimension binder (or
/// the ambient body of a constant line).
pub fn checked_line_quote_body(
  level : Int32,
  dlevel : Int32,
  line : DCheckedTypeLine,
) -> DTerm {
  if line.constant {
    quote_ty(level, dlevel, (line.line)(DZero))
  } else {
    quote_ty(level, dlevel + 1, (line.line)(DVar(dlevel)))
  }
}

///|
/// The PathP type over a checked line.
pub fn checked_pathp_type(
  line : DCheckedTypeLine,
  left : DValue,
  right : DValue,
) -> DValue {
  DVPathTy(line.line, left, right)
}

///|
pub fn checked_coe_value(
  line : DCheckedTypeLine,
  r : Dim,
  s : Dim,
  v : DValue,
  dlevel : Int32,
) -> DValue {
  coe_value(line.line, r, s, v, dlevel)
}

///|
pub fn checked_comp_value(
  line : DCheckedTypeLine,
  branches : DSystem,
  base : DValue,
  dlevel : Int32,
) -> DValue {
  comp_value(line.line, branches, base, dlevel)
}

///|
pub fn checked_fill_value(
  line : DCheckedTypeLine,
  branches : DSystem,
  base : DValue,
  dlevel : Int32,
) -> (Dim) -> DValue {
  fill_value(line.line, branches, base, dlevel)
}

///|
/// Pack a raw semantic line only after reifying and rechecking it at
/// a generic dimension.  The quoted body is read in the empty
/// context, so this succeeds precisely for lines whose generic fibre
/// quotes to a closed, well-formed type line that also validates at
/// the endpoints; the endpoints of the result are then required to
/// be convertible to the raw line's endpoints.
pub fn checked_line_reify_closed(raw : (Dim) -> DValue) -> DCheckedTypeLine? {
  let body = quote_ty(0, 1, raw(DVar(0)))
  match checked_type_line_closed(body) {
    Some(line) =>
      if conv_ty(0, 0, (line.line)(DZero), raw(DZero)) &&
        conv_ty(0, 0, (line.line)(DOne), raw(DOne)) &&
        conv_ty(0, 1, (line.line)(DVar(0)), raw(DVar(0))) {
        Some(line)
      } else {
        None
      }
    None => None
  }
}

///|
/// Apply a dimension substitution to a semantic value at a known
/// type, by quoting and re-evaluating in the substituted dimension
/// environment.  `subst[k]` is the image of the semantic dimension
/// level `k` (missing entries are the identity).  Returns the
/// substituted type and value.  Host closures inside the value are
/// handled by the quote/re-evaluate round trip, so the result
/// respects substitution by construction.
pub fn dvalue_subst_dims(
  level : Int32,
  dlevel : Int32,
  ty : DValue,
  v : DValue,
  subst : Array[Dim],
) -> (DValue, DValue) {
  let ty_term = quote_ty(level, dlevel, ty)
  let v_term = quote_at(level, dlevel, ty, v)
  let denv_values : Array[Dim] = []
  for i in 0..<dlevel {
    let lvl = dlevel - 1 - i
    denv_values.push(
      if lvl >= 0 && lvl < subst.length() {
        subst[lvl]
      } else {
        DVar(lvl)
      },
    )
  }
  let denv = ddim_from_array(denv_values)
  let term_env = fresh_term_env(level)
  (deval_dim(ty_term, term_env, denv), deval_dim(v_term, term_env, denv))
}

///|
/// Reparameterize a closed checked line by a dimension expression
/// in its line variable (`DVar(0)`), reifying the result as a
/// checked line again.
pub fn checked_line_reparam_closed(
  line : DCheckedTypeLine,
  expr : Dim,
) -> DCheckedTypeLine? {
  checked_line_reify_closed(d => (line.line)(hit_dim_substitute(expr, 0, d)))
}

///|
pub fn check_semantic_dimension_substitution() -> Bool {
  // Substituting `0` for the circle's dimension collapses a loop
  // point to the base point; substituting `¬i` reverses it.
  let loop_point : DValue = DVCirclePoint(DVar(0))
  let (ty0, at_zero) = dvalue_subst_dims(0, 1, DVCircleTy, loop_point, [DZero])
  if !conv_ty(0, 1, ty0, DVCircleTy) ||
    !conv_at(0, 1, DVCircleTy, at_zero, DVCirclePoint(DZero)) {
    return false
  }
  let (_, reversed) = dvalue_subst_dims(0, 1, DVCircleTy, loop_point, [
    DNeg(DVar(0)),
  ])
  if !conv_at(0, 1, DVCircleTy, reversed, DVCirclePoint(DNeg(DVar(0)))) {
    return false
  }
  // A constant checked line reparameterizes to a constant line.
  match checked_constant_type_line_closed(DBoolTy) {
    Some(line) =>
      match checked_line_reparam_closed(line, DNeg(DVar(0))) {
        Some(reparam) =>
          checked_line_is_constant(reparam) ||
          conv_ty(0, 0, checked_line_at(reparam, DZero), DVBoolTy)
        None => false
      }
    None => false
  }
}
