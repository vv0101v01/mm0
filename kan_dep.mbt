///|
// Kan structure for the dependent fragment, pushed through every
// type former of the project.
//
// A fibrant *line of types* is a structure DLine with
//   at(i)              the type (a DValue) at dimension i,
//   coe(r, s, v)       heterogeneous transport along the line,
//   fill(tube, base)   the Kan filler as a path over the line; comp is
//                      its value at 1.  `tube` is a one-face partial
//                      path (Some) or absent (None); base is at 0.
//
// The constructors are the standard cubical recursion:
//   * Bool / Unit / Type_i are constant discrete lines (coe = id);
//   * Pi: coe is contravariant in the domain —
//       (coe f)(y) = coe_B( f(coe_A(s,r,y)) )
//     where B is taken along the argument path j ↦ coe_A(s,j,y);
//   * Sigma: coe transports the first component, then the second along
//     the line B over the resulting first-component path;
//   * fill/comp recurse the same way (Pi pointwise over a transported
//     argument path; Sigma along the first component's filler path).
//
// Dependent families are therefore presented as
//   B : (path in A) → DLine,
// which is exactly the data Kan composition for dependent types needs.
// Non-dependent lines, the simply-typed fragment (LTy) and the finite
// universe (Ty) embed through constant families; a ua-equivalence gives
// a non-constant line `dline_of_upath`.  The remaining project types
// already carry Kan structures elsewhere and are registered together in
// `check_kan_all_types`: eigenspaces/subspace lines (cube.mbt,
// glue_comp.mbt) and finite/vector Glue types (glue_comp.mbt).

///|
pub struct DLine {
  at : (Double) -> DValue
  coe_fn : (Double, Double, DValue) -> DValue
  fill_fn : (((Double) -> DValue)?, DValue) -> (Double) -> DValue
}

///|
pub fn dline_at(l : DLine, i : Double) -> DValue {
  (l.at)(i)
}

///|
/// coe with the reflexivity law normalised: coe(r,r) is the identity
/// *definitionally* (the wrapper returns the value untouched).
pub fn dcoe(l : DLine, r : Double, s : Double, v : DValue) -> DValue {
  if r == s {
    v
  } else {
    (l.coe_fn)(r, s, v)
  }
}

///|
pub fn dfill(
  l : DLine,
  tube : ((Double) -> DValue)?,
  base : DValue,
) -> (Double) -> DValue {
  (l.fill_fn)(tube, base)
}

///|
/// Heterogeneous composition from 0 to 1: the cap of the filler.
pub fn dcomp(l : DLine, tube : ((Double) -> DValue)?, base : DValue) -> DValue {
  dfill(l, tube, base)(1.0)
}

///|
fn const_fill(
  tube : ((Double) -> DValue)?,
  base : DValue,
) -> (Double) -> DValue {
  match tube {
    Some(p) => p
    None => _j => base
  }
}

///|
/// Constant line on a discrete (or already validated) type.
pub fn dline_const(ty : DValue) -> DLine {
  DLine::{
    at: _i => ty,
    coe_fn: (_r, _s, v) => v,
    fill_fn: (tube, base) => const_fill(tube, base),
  }
}

///|
pub fn dline_bool() -> DLine {
  dline_const(DVBoolTy)
}

///|
pub fn dline_unit() -> DLine {
  dline_const(DVUnitTy)
}

///|
pub fn dline_univ(level : Int32) -> DLine {
  dline_const(DVUniv(level))
}

///|
/// The argument path through `a` starting from x at dimension `from_i`.
pub fn path_from(a : DLine, from_i : Double, x : DValue) -> (Double) -> DValue {
  j => dcoe(a, from_i, j, x)
}

// ---------------------------------------------------------------------------
// Pi lines
// ---------------------------------------------------------------------------

///|
fn pi_fiber_ty(
  a : DLine,
  bfam : ((Double) -> DValue) -> DLine,
  i : Double,
  x : DValue,
) -> DValue {
  dline_at(bfam(path_from(a, i, x)), i)
}

///|
fn pi_at(a : DLine, bfam : ((Double) -> DValue) -> DLine, i : Double) -> DValue {
  DVPi(dline_at(a, i), x => pi_fiber_ty(a, bfam, i, x))
}

///|
fn pi_coe_apply(
  a : DLine,
  bfam : ((Double) -> DValue) -> DLine,
  r : Double,
  s : Double,
  f : DValue,
  y : DValue,
) -> DValue {
  let xpath = path_from(a, s, y) // xpath(r) = coe_A(s,r,y), xpath(s) = y
  dcoe(bfam(xpath), r, s, dapp_typed(f, xpath(r), dline_at(a, r)))
}

///|
fn pi_coe(
  a : DLine,
  bfam : ((Double) -> DValue) -> DLine,
  r : Double,
  s : Double,
  f : DValue,
) -> DValue {
  DVLam(y => pi_coe_apply(a, bfam, r, s, f, y))
}

///|
fn pi_fill_apply(
  a : DLine,
  bfam : ((Double) -> DValue) -> DLine,
  tube : ((Double) -> DValue)?,
  base : DValue,
  j : Double,
  y : DValue,
) -> DValue {
  let xpath = path_from(a, j, y)
  let bline = bfam(xpath)
  let btube = match tube {
    Some(p) => Some(k => dapp_typed(p(k), xpath(k), dline_at(a, k)))
    None => None
  }
  let bbase = dapp_typed(base, xpath(0.0), dline_at(a, 0.0))
  dfill(bline, btube, bbase)(j)
}

///|
fn pi_fill(
  a : DLine,
  bfam : ((Double) -> DValue) -> DLine,
  tube : ((Double) -> DValue)?,
  base : DValue,
) -> (Double) -> DValue {
  j => DVLam(y => pi_fill_apply(a, bfam, tube, base, j, y))
}

///|
pub fn dline_pi(a : DLine, bfam : ((Double) -> DValue) -> DLine) -> DLine {
  DLine::{
    at: i => pi_at(a, bfam, i),
    coe_fn: (r, s, f) => pi_coe(a, bfam, r, s, f),
    fill_fn: (tube, base) => pi_fill(a, bfam, tube, base),
  }
}

///|
pub fn dline_pi_constfam(a : DLine, b : DLine) -> DLine {
  dline_pi(a, _path => b)
}

// ---------------------------------------------------------------------------
// Sigma lines
// ---------------------------------------------------------------------------

///|
fn sigma_fam_at(
  a : DLine,
  bfam : ((Double) -> DValue) -> DLine,
  i : Double,
) -> (DValue) -> DValue {
  x => pi_fiber_ty(a, bfam, i, x)
}

///|
fn sigma_at(
  a : DLine,
  bfam : ((Double) -> DValue) -> DLine,
  i : Double,
) -> DValue {
  DVSigma(dline_at(a, i), x => pi_fiber_ty(a, bfam, i, x))
}

///|
fn sigma_coe(
  a : DLine,
  bfam : ((Double) -> DValue) -> DLine,
  r : Double,
  s : Double,
  p : DValue,
) -> DValue {
  let fst_val = dfst_typed(p, sigma_fam_at(a, bfam, r))
  let xpath = path_from(a, r, fst_val)
  DVPair(
    xpath(s),
    dcoe(
      bfam(xpath),
      r,
      s,
      dsnd_typed(p, dline_at(a, r), sigma_fam_at(a, bfam, r)),
    ),
  )
}

///|
fn tube_fst(
  a : DLine,
  bfam : ((Double) -> DValue) -> DLine,
  tube : ((Double) -> DValue)?,
) -> ((Double) -> DValue)? {
  match tube {
    Some(p) => Some(k => dfst_typed(p(k), sigma_fam_at(a, bfam, k)))
    None => None
  }
}

///|
fn tube_snd(
  a : DLine,
  bfam : ((Double) -> DValue) -> DLine,
  tube : ((Double) -> DValue)?,
) -> ((Double) -> DValue)? {
  match tube {
    Some(p) =>
      Some(k => dsnd_typed(p(k), dline_at(a, k), sigma_fam_at(a, bfam, k)))
    None => None
  }
}

///|
fn sigma_fill(
  a : DLine,
  bfam : ((Double) -> DValue) -> DLine,
  tube : ((Double) -> DValue)?,
  base : DValue,
) -> (Double) -> DValue {
  let a_fill = dfill(
    a,
    tube_fst(a, bfam, tube),
    dfst_typed(base, sigma_fam_at(a, bfam, 0.0)),
  )
  let b_fill = dfill(
    bfam(a_fill),
    tube_snd(a, bfam, tube),
    dsnd_typed(base, dline_at(a, 0.0), sigma_fam_at(a, bfam, 0.0)),
  )
  j => DVPair(a_fill(j), b_fill(j))
}

///|
pub fn dline_sigma(a : DLine, bfam : ((Double) -> DValue) -> DLine) -> DLine {
  DLine::{
    at: i => sigma_at(a, bfam, i),
    coe_fn: (r, s, p) => sigma_coe(a, bfam, r, s, p),
    fill_fn: (tube, base) => sigma_fill(a, bfam, tube, base),
  }
}

///|
pub fn dline_sigma_constfam(a : DLine, b : DLine) -> DLine {
  dline_sigma(a, _path => b)
}

// ---------------------------------------------------------------------------
// Non-constant lines from equivalences; embeddings of LTy and Ty
// ---------------------------------------------------------------------------

///|
fn maps_at(src : DValue, dst : DValue, i : Double) -> DValue {
  if i < 1.0 {
    src
  } else {
    dst
  }
}

///|
fn maps_coe(
  fwd : (DValue) -> DValue,
  bwd : (DValue) -> DValue,
  r : Double,
  s : Double,
  v : DValue,
) -> DValue {
  if r < 1.0 && s >= 1.0 {
    fwd(v)
  } else if r >= 1.0 && s < 1.0 {
    bwd(v)
  } else {
    v
  }
}

///|
fn maps_fill(
  fwd : (DValue) -> DValue,
  bwd : (DValue) -> DValue,
  tube : ((Double) -> DValue)?,
  base : DValue,
) -> (Double) -> DValue {
  match tube {
    Some(p) => p
    None => j => maps_coe(fwd, bwd, 0.0, j, base)
  }
}

///|
/// The type line underlying a (semantic) equivalence, presented in
/// endpoint form: src on [0,1), dst at 1; coe crosses by fwd/bwd.
/// This is the line whose associated path is ua of the equivalence.
pub fn dline_from_maps(
  src : DValue,
  dst : DValue,
  fwd : (DValue) -> DValue,
  bwd : (DValue) -> DValue,
) -> DLine {
  DLine::{
    at: i => maps_at(src, dst, i),
    coe_fn: (r, s, v) => maps_coe(fwd, bwd, r, s, v),
    fill_fn: (tube, base) => maps_fill(fwd, bwd, tube, base),
  }
}

///|
pub fn dbool_not(v : DValue) -> DValue {
  match force_value(v) {
    DVBool(b) => DVBool(!b)
    other => other
  }
}

///|
pub fn dline_bool_not_ua() -> DLine {
  dline_from_maps(DVBoolTy, DVBoolTy, dbool_not, dbool_not)
}

///|
pub fn dline_of_lty(ty : LTy) -> DLine {
  match ty {
    LBool => dline_bool()
    LUnit => dline_unit()
    LProd(a, b) => dline_sigma_constfam(dline_of_lty(a), dline_of_lty(b))
    LFun(a, b) => dline_pi_constfam(dline_of_lty(a), dline_of_lty(b))
  }
}

///|
pub fn dvalue_of_ty(ty : Ty) -> DValue {
  match ty {
    TyBool => DVBoolTy
    TyUnit => DVUnitTy
    TyProd(a, b) => DVSigma(dvalue_of_ty(a), _ => dvalue_of_ty(b))
  }
}

///|
pub fn dline_of_ty(ty : Ty) -> DLine {
  match ty {
    TyBool => dline_bool()
    TyUnit => dline_unit()
    TyProd(a, b) => dline_sigma_constfam(dline_of_ty(a), dline_of_ty(b))
  }
}

///|
pub fn pval_to_dvalue(v : PVal) -> DValue {
  match v {
    PVUnit => DVUnit
    PVBool(b) => DVBool(b)
    PVPair(a, b) => DVPair(pval_to_dvalue(a), pval_to_dvalue(b))
  }
}

///|
pub fn dvalue_to_pval(v : DValue) -> PVal {
  match force_value(v) {
    DVUnit => PVUnit
    DVBool(b) => PVBool(b)
    DVPair(a, b) => PVPair(dvalue_to_pval(a), dvalue_to_pval(b))
    _ => PVUnit
  }
}

///|
/// A finite ua-path as a dependent type line.
pub fn dline_of_upath(p : UPath) -> DLine {
  dline_from_maps(
    dvalue_of_ty(p.equiv.src),
    dvalue_of_ty(p.equiv.dst),
    v => pval_to_dvalue(coe_upath(p, 0, 1, dvalue_to_pval(v))),
    v => pval_to_dvalue(coe_upath(p, 1, 0, dvalue_to_pval(v))),
  )
}

// ---------------------------------------------------------------------------
// Kan laws on examples, and the all-types registry
// ---------------------------------------------------------------------------

///|
fn dv_is_bool(v : DValue, expected : Bool) -> Bool {
  match force_value(v) {
    DVBool(b) => b == expected
    _ => false
  }
}

///|
pub fn check_kan_coe_pi_sigma() -> Bool {
  // coe along Pi over the ua(not) domain line twists the identity to not.
  let pi_line = dline_pi_constfam(dline_bool_not_ua(), dline_bool())
  let id_fun = DVLam(x => x)
  let transported = dcoe(pi_line, 0.0, 1.0, id_fun)
  if !dv_is_bool(dapp_typed(transported, DVBool(true), DVBoolTy), false) {
    return false
  }
  if !dv_is_bool(dapp_typed(transported, DVBool(false), DVBoolTy), true) {
    return false
  }
  // and transporting back restores it.
  let back = dcoe(pi_line, 1.0, 0.0, transported)
  if !dv_is_bool(dapp_typed(back, DVBool(true), DVBoolTy), true) {
    return false
  }
  // comp with no tube is coe.
  let comped = dcomp(pi_line, None, id_fun)
  if !dv_is_bool(dapp_typed(comped, DVBool(false), DVBoolTy), true) {
    return false
  }
  // Sigma over the same domain line twists the first component only.
  let sig_line = dline_sigma_constfam(dline_bool_not_ua(), dline_bool())
  let pair = DVPair(DVBool(true), DVBool(false))
  let moved = dcoe(sig_line, 0.0, 1.0, pair)
  conv_at(
    0,
    0,
    dline_at(sig_line, 1.0),
    moved,
    DVPair(DVBool(false), DVBool(false)),
  )
}

///|
fn fam_if_true(path : (Double) -> DValue) -> DLine {
  match force_value(path(0.0)) {
    DVBool(true) => dline_bool_not_ua()
    _ => dline_bool()
  }
}

///|
pub fn check_kan_coe_dependent() -> Bool {
  // Dependent Sigma: the second line depends on the first component's path.
  let dep_sig = dline_sigma(dline_bool(), fam_if_true)
  let p1 = dcoe(dep_sig, 0.0, 1.0, DVPair(DVBool(true), DVBool(true)))
  let p2 = dcoe(dep_sig, 0.0, 1.0, DVPair(DVBool(false), DVBool(true)))
  if !conv_at(
      0,
      0,
      dline_at(dep_sig, 1.0),
      p1,
      DVPair(DVBool(true), DVBool(false)),
    ) {
    return false
  }
  if !conv_at(
      0,
      0,
      dline_at(dep_sig, 1.0),
      p2,
      DVPair(DVBool(false), DVBool(true)),
    ) {
    return false
  }
  // Dependent Pi: codomain line selected by the transported argument path.
  let dep_pi = dline_pi(dline_bool(), fam_if_true)
  let f = dcoe(dep_pi, 0.0, 1.0, DVLam(x => x))
  dv_is_bool(dapp_typed(f, DVBool(true), DVBoolTy), false) &&
  dv_is_bool(dapp_typed(f, DVBool(false), DVBoolTy), false)
}

///|
pub fn check_kan_comp_tube() -> Bool {
  // With a prescribed tube, comp returns its cap (Sigma, then Pi pointwise).
  let sig_line = dline_sigma_constfam(dline_bool(), dline_bool())
  let tube : ((Double) -> DValue)? = Some(_j => {
    DVPair(DVBool(true), DVBool(false))
  })
  let cap = dcomp(sig_line, tube, DVPair(DVBool(true), DVBool(false)))
  if !conv_at(
      0,
      0,
      dline_at(sig_line, 1.0),
      cap,
      DVPair(DVBool(true), DVBool(false)),
    ) {
    return false
  }
  let pi_line = dline_pi_constfam(dline_bool(), dline_bool())
  let tube_f : ((Double) -> DValue)? = Some(_j => DVLam(x => dbool_not(x)))
  let cap_f = dcomp(pi_line, tube_f, DVLam(x => dbool_not(x)))
  dv_is_bool(dapp_typed(cap_f, DVBool(true), DVBoolTy), false)
}

///|
pub fn check_kan_embeddings() -> Bool {
  // Simply-typed and finite types land on the right dependent types,
  // with (constant) coe the identity; universes are constant lines.
  let lty = LFun(LProd(LBool, LUnit), LBool)
  if quote_ty(0, 0, dline_at(dline_of_lty(lty), 0.0)) != lty_to_dterm(lty) {
    return false
  }
  let fty = TyProd(TyBool, TyUnit)
  let v = DVPair(DVBool(true), DVUnit)
  if !conv_at(0, 0, dvalue_of_ty(fty), dcoe(dline_of_ty(fty), 0.0, 1.0, v), v) {
    return false
  }
  if quote_ty(0, 0, dcoe(dline_univ(0), 0.0, 1.0, DVBoolTy)) != DBoolTy {
    return false
  }
  // A finite ua line transports by the underlying wiring (swap).
  let ua_line = dline_of_upath(iso_to_path(iso_swap(TyBool, TyUnit)))
  let moved = dcoe(ua_line, 0.0, 1.0, DVPair(DVBool(true), DVUnit))
  dvalue_to_pval(moved) == PVPair(PVUnit, PVBool(true))
}

///|
pub fn check_kan_dep_all() -> Bool {
  check_kan_coe_pi_sigma() &&
  check_kan_coe_dependent() &&
  check_kan_comp_tube() &&
  check_kan_embeddings() &&
  check_dline_dimension_substitution()
}

// ---------------------------------------------------------------------------
// Dimension substitution for DLines
// ---------------------------------------------------------------------------

///|
/// Substitute a dimension expression into a raw `DLine`: the line
/// `i ↦ L(φ i)` where `φ(i) = eval_dim(expr, [i])` (`DVar(0)` is
/// the substituted variable).  The Kan operations are transported
/// along `φ`: coercion in the substituted line is coercion in `L`
/// between the substituted endpoints, and the filler is the
/// coercion path (a supplied tube, being already a path over the
/// substituted line, is its own filler, matching `const_fill`).
pub fn dline_subst(l : DLine, expr : Dim) -> DLine {
  let phi = (i : Double) => eval_dim(expr, [i])
  DLine::{
    at: i => dline_at(l, phi(i)),
    coe_fn: (r, s, v) => dcoe(l, phi(r), phi(s), v),
    fill_fn: (tube, base) => {
      match tube {
        Some(p) => p
        None => j => dcoe(l, phi(0.0), phi(j), base)
      }
    },
  }
}

///|
/// The reversed line `i ↦ L(1 - i)`.
pub fn dline_rev(l : DLine) -> DLine {
  dline_subst(l, DNeg(DVar(0)))
}

///|
pub fn check_dline_dimension_substitution() -> Bool {
  let ua_line = dline_bool_not_ua()
  // Reversing the ua(not) line transports by the inverse (not is
  // its own inverse): coe in the reversed line from 0 to 1 is coe
  // in the original from 1 to 0.
  let rev = dline_rev(ua_line)
  if !dv_is_bool(dcoe(rev, 0.0, 1.0, DVBool(true)), false) ||
    !dv_is_bool(dcoe(rev, 1.0, 0.0, DVBool(true)), false) {
    return false
  }
  // Substitution by `i ∧ 0` collapses the line to its left fibre:
  // coercion is then the identity.  (The constant-zero expression
  // is `DAnd(DVar(0), DZero)`.)
  let collapsed = dline_subst(ua_line, DAnd(DVar(0), DZero))
  if !dv_is_bool(dcoe(collapsed, 0.0, 1.0, DVBool(true)), true) {
    return false
  }
  // Double reversal is the original line (pointwise at endpoints).
  let twice = dline_rev(rev)
  dv_is_bool(dcoe(twice, 0.0, 1.0, DVBool(true)), false) &&
  dv_is_bool(dcomp(twice, None, DVBool(false)), true)
}
