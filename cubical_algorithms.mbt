///|
// High-level cubical algorithms over the dependent kernel.
//
// The kernel already provides the primitive Kan operations
// (`coe_value`, `comp_value`, `fill_value`, `hcomp_value`).  This
// component packages the operations that cubical developments use
// every day -- transport, dependent paths over a transport filler,
// path symmetry/congruence/transitivity by an explicit hcomp square,
// function extensionality, and substitution along a path -- as one
// coherent semantic API, together with closed-term builders for the
// same operations.  Nothing in the kernel depends back on this file:
// it is an upper layer in `architecture.json`.
//
// Semantic paths are `DVPathLam` values.  The transitivity square is
// the standard one: for `p : x = y` and `q : y = z`, the square
// `S(i,j)` fills, in direction `j`, the open box whose base at `j=0`
// is `p(i)`, whose `i=0` side is constant `x`, and whose `i=1` side
// is `q(j)`.  Then `i ↦ S(i,1)` is a path `x = z`.

// ---------------------------------------------------------------------------
// Transport and Kan boxes
// ---------------------------------------------------------------------------

///|
/// Transport (coe 0→1) along a semantic type line.
pub fn transport_value(
  line : (Dim) -> DValue,
  v : DValue,
  dlevel : Int32,
) -> DValue {
  coe_value(line, DZero, DOne, v, dlevel)
}

///|
/// Backwards transport (coe 1→0) along a semantic type line.
pub fn transport_back_value(
  line : (Dim) -> DValue,
  v : DValue,
  dlevel : Int32,
) -> DValue {
  coe_value(line, DOne, DZero, v, dlevel)
}

///|
/// Transport along a checked (substitutable) type line.
pub fn transport_checked_line_value(
  line : DCheckedTypeLine,
  v : DValue,
  dlevel : Int32,
) -> DValue {
  checked_coe_value(line, DZero, DOne, v, dlevel)
}

///|
/// The transport filler: a dependent path from `v` to its transport.
pub fn transport_filler_value(
  line : (Dim) -> DValue,
  v : DValue,
  dlevel : Int32,
) -> (Dim) -> DValue {
  fill_value(line, dsystem_empty(), v, dlevel)
}

///|
/// The transport filler as a `PathP` value over the line.
pub fn transport_pathp_value(
  line : (Dim) -> DValue,
  v : DValue,
  dlevel : Int32,
) -> DValue {
  DVPathLam(transport_filler_value(line, v, dlevel))
}

///|
/// An open Kan box: a type line, a tube system and a base cap.
pub struct KanBox {
  line : (Dim) -> DValue
  system : DSystem
  base : DValue
  dlevel : Int32
}

///|
pub fn kan_box(
  line : (Dim) -> DValue,
  system : DSystem,
  base : DValue,
  dlevel : Int32,
) -> KanBox {
  KanBox::{ line, system, base, dlevel, }
}

///|
/// The filler of an open box, as a function of the composition
/// direction: at 0 it is the base, at 1 the composition, and on each
/// tube face it agrees with that tube.
pub fn kan_box_fill(box : KanBox) -> (Dim) -> DValue {
  fill_value(box.line, box.system, box.base, box.dlevel)
}

///|
/// The composition (cap) of an open box.
pub fn kan_box_comp(box : KanBox) -> DValue {
  comp_value(box.line, box.system, box.base, box.dlevel)
}

///|
/// The filler of an open box as a `PathP` value over its line.
pub fn kan_box_pathp(box : KanBox) -> DValue {
  DVPathLam(kan_box_fill(box))
}

// ---------------------------------------------------------------------------
// Path algebra on semantic values
// ---------------------------------------------------------------------------

///|
/// The point of a semantic path at a dimension.
pub fn dpath_at_value(p : DValue, d : Dim) -> DValue {
  dapp_dim(p, d)
}

///|
/// Reflexivity: the constant path.
pub fn dpath_refl_value(v : DValue) -> DValue {
  DVPathLam(_ => v)
}

///|
/// Symmetry by dimension reversal.
pub fn dpath_sym_value(p : DValue) -> DValue {
  DVPathLam(d => dapp_dim(p, DNeg(d)))
}

///|
/// The suffix of a path starting at `r`: `j ↦ p(r ∨ j)`, a path from
/// `p(r)` to `p(1)`.
pub fn dpath_segment_value(p : DValue, r : Dim) -> DValue {
  DVPathLam(j => dapp_dim(p, DOr(r, j)))
}

///|
/// The prefix of a path ending at `r`: `j ↦ p(r ∧ j)`, a path from
/// `p(0)` to `p(r)`.
pub fn dpath_prefix_value(p : DValue, r : Dim) -> DValue {
  DVPathLam(j => dapp_dim(p, DAnd(r, j)))
}

///|
/// The transitivity square of `p : x = y` and `q : y = z`, as a
/// nested path value `S(i,j)`.
pub fn dpath_trans_square_value(
  ty : DValue,
  p : DValue,
  q : DValue,
  dlevel : Int32,
) -> DValue {
  DVPathLam(i => {
    DVPathLam(j => {
      let branches = dsystem_of([
        tube_branch(face_simplify(FEq0(i)), _ => dapp_dim(p, DZero)),
        tube_branch(face_simplify(FEq1(i)), k => dapp_dim(q, k)),
      ])
      hfill_value(ty, branches, dapp_dim(p, i), dlevel + 1)(j)
    })
  })
}

///|
/// Transitivity of paths: the top edge `i ↦ S(i,1)` of the
/// transitivity square.
pub fn dpath_trans_value(
  ty : DValue,
  p : DValue,
  q : DValue,
  dlevel : Int32,
) -> DValue {
  let square = dpath_trans_square_value(ty, p, q, dlevel)
  DVPathLam(i => dapp_dim(dapp_dim(square, i), DOne))
}

///|
/// Congruence (`ap`): apply a function pointwise to a path.
pub fn dpath_cong_value(f : DValue, dom : DValue, p : DValue) -> DValue {
  DVPathLam(d => dapp_typed(f, dapp_dim(p, d), dom))
}

///|
/// Function extensionality: from a pointwise path-valued function to
/// a path of functions.
pub fn dpath_funext_value(pointwise : DValue, dom : DValue) -> DValue {
  DVPathLam(d => DVLam(x => dapp_dim(dapp_typed(pointwise, x, dom), d)))
}

///|
/// Substitution/transport in a dependent family along a path in the
/// base type: `subst B p v = coe^{j.B(p j)} v`.
pub fn subst_value(
  fam : (DValue) -> DValue,
  p : DValue,
  v : DValue,
  dlevel : Int32,
) -> DValue {
  transport_value(memo_dim_line(j => fam(dapp_dim(p, j))), v, dlevel)
}

///|
/// The dependent path over `p` whose far endpoint is `subst B p v`.
pub fn subst_pathp_value(
  fam : (DValue) -> DValue,
  p : DValue,
  v : DValue,
  dlevel : Int32,
) -> DValue {
  transport_pathp_value(j => fam(dapp_dim(p, j)), v, dlevel)
}

// ---------------------------------------------------------------------------
// Closed-term builders
//
// These build DTerms.  The arguments must be closed with respect to
// ambient dimension variables (the builders place them under fresh
// dimension binders; term variables are in a separate space and are
// unaffected).
// ---------------------------------------------------------------------------

///|
/// `transport` of a closed term along a line body.
pub fn dtransport_term(line_body : DTerm, x : DTerm) -> DTerm {
  DCoe(line_body, DZero, DOne, x)
}

///|
/// Backwards `transport` of a closed term along a line body.
pub fn dtransport_back_term(line_body : DTerm, x : DTerm) -> DTerm {
  DCoe(line_body, DOne, DZero, x)
}

///|
pub fn dpath_refl_term(x : DTerm) -> DTerm {
  DLamDim(x)
}

///|
pub fn dpath_sym_term(p : DTerm) -> DTerm {
  DLamDim(DAppDim(p, DNeg(DVar(0))))
}

///|
pub fn dpath_cong_term(f : DTerm, p : DTerm) -> DTerm {
  DLamDim(DApp(f, DAppDim(p, DVar(0))))
}

///|
/// Function extensionality as a closed term: from
/// `pointwise : (x:A) -> Path B (f x) (g x)` build a path
/// `f = g` in `A -> B` (at the constant family `B`).
pub fn dfunext_term(dom : DTerm, pointwise : DTerm) -> DTerm {
  DLamDim(DLam(dom, DAppDim(DApp(pointwise, DTVar(0)), DVar(0))))
}

///|
/// Transitivity of closed paths by the hcomp square.  Under the
/// outer `<i>` binder, `DHComp` composes in a fresh direction `j`:
/// tube bodies therefore see `j` as `DVar(0)`.
pub fn dpath_trans_term(ty : DTerm, p : DTerm, q : DTerm) -> DTerm {
  DLamDim(
    DHComp(
      ty,
      [
        d_tube(FEq0(DVar(0)), DAppDim(p, DZero)),
        d_tube(FEq1(DVar(0)), DAppDim(q, DVar(0))),
      ],
      DAppDim(p, DVar(0)),
    ),
  )
}

// ---------------------------------------------------------------------------
// Behavioural laws
// ---------------------------------------------------------------------------

///|
// Shared test helper (also used by equiv_laws/univalence law checks).
fn cubical_bool_is(v : DValue, expected : Bool) -> Bool {
  conv_at(0, 0, DVBoolTy, v, DVBool(expected))
}

///|
fn check_transport_algorithms() -> Bool {
  let e = deval_dim(bool_not_equiv_term(), denv_empty(), ddim_empty())
  let line = ua_line_value(e, DVBoolTy, DVBoolTy, 0)
  let filler = transport_filler_value(line, DVBool(true), 0)
  let box = kan_box(line, dsystem_empty(), DVBool(true), 0)
  cubical_bool_is(transport_value(line, DVBool(true), 0), false) &&
  cubical_bool_is(transport_back_value(line, DVBool(true), 0), false) &&
  cubical_bool_is(filler(DZero), true) &&
  cubical_bool_is(filler(DOne), false) &&
  cubical_bool_is(kan_box_comp(box), false) &&
  cubical_bool_is(dapp_dim(kan_box_pathp(box), DOne), false) &&
  cubical_bool_is(
    subst_value(_ => DVBoolTy, dpath_refl_value(DVBool(true)), DVBool(true), 0),
    true,
  )
}

///|
fn check_path_algebra_algorithms() -> Bool {
  // The circle loop is a genuinely nonconstant path.
  let loop_path : DValue = DVPathLam(d => circle_point(d))
  let base = circle_point(DZero)
  let sym_ok = conv_at(
      0,
      0,
      DVCircleTy,
      dapp_dim(dpath_sym_value(loop_path), DZero),
      base,
    ) &&
    conv_at(0, 0, DVCircleTy, dapp_dim(dpath_sym_value(loop_path), DOne), base)
  let trans = dpath_trans_value(DVCircleTy, loop_path, loop_path, 0)
  let trans_ok = conv_at(0, 0, DVCircleTy, dapp_dim(trans, DZero), base) &&
    conv_at(0, 0, DVCircleTy, dapp_dim(trans, DOne), base)
  let cong = dpath_cong_value(DVLam(x => x), DVCircleTy, loop_path)
  let cong_ok = conv_at(
    0,
    1,
    DVCircleTy,
    dapp_dim(cong, DVar(0)),
    dapp_dim(loop_path, DVar(0)),
  )
  let pointwise : DValue = DVLam(x => dpath_refl_value(x))
  let funext_path = dpath_funext_value(pointwise, DVCircleTy)
  let funext_ok = conv_at(
    0,
    0,
    DVCircleTy,
    dapp_typed(dapp_dim(funext_path, DOne), base, DVCircleTy),
    base,
  )
  let segment_ok = conv_at(
      0,
      0,
      DVCircleTy,
      dapp_dim(dpath_segment_value(loop_path, DZero), DOne),
      base,
    ) &&
    conv_at(
      0,
      0,
      DVCircleTy,
      dapp_dim(dpath_prefix_value(loop_path, DOne), DOne),
      base,
    )
  sym_ok && trans_ok && cong_ok && funext_ok && segment_ok
}

///|
fn check_cubical_term_builders() -> Bool {
  let path_ty = DPath(DCircleTy, DCircleBase, DCircleBase)
  let trans = dpath_trans_term(DCircleTy, DCircleLoop, DCircleLoop)
  if !dep_check_closed(trans, path_ty) {
    return false
  }
  let sym = dpath_sym_term(DCircleLoop)
  if !dep_check_closed(sym, path_ty) {
    return false
  }
  let cong = dpath_cong_term(DLam(DCircleTy, DTVar(0)), DCircleLoop)
  if !dep_check_closed(cong, path_ty) {
    return false
  }
  let id_fun = DLam(DCircleTy, DTVar(0))
  let pointwise = DLam(DCircleTy, DLamDim(DTVar(0)))
  let fun_path_ty = DPath(DPi(DCircleTy, DCircleTy), id_fun, id_fun)
  if !dep_check_closed(dfunext_term(DCircleTy, pointwise), fun_path_ty) {
    return false
  }
  let ua_line = DAppDim(DUa(bool_not_equiv_term()), DVar(0))
  dep_nf_closed(dtransport_term(ua_line, DBoolLit(true)), DBoolTy) ==
  Some(DBoolLit(false)) &&
  dep_nf_closed(dtransport_back_term(ua_line, DBoolLit(true)), DBoolTy) ==
  Some(DBoolLit(false))
}

///|
pub fn check_cubical_algorithms() -> Bool {
  check_transport_algorithms() &&
  check_path_algebra_algorithms() &&
  check_cubical_term_builders()
}

///|
/// Left unit as a 3-cell: for `alpha : Path(space, r, r)`, a
/// path in `Path(space, r, r)` from `refl(r) ⬝ alpha` to
/// `alpha`.  The transitivity square `S` of `(refl, alpha)`
/// has top edge `refl ⬝ alpha`, right edge `alpha`, and left
/// and bottom edges constant at `r`; the 3-cell rotates the
/// top edge onto the right edge in two connection phases --
/// first `S(i, i ∨ ¬t)` (top edge to diagonal, start point
/// sliding down the constant left edge), then `S(i ∨ t, i)`
/// (diagonal to right edge, start point sliding along the
/// constant bottom edge) -- so both endpoints stay at `r`
/// throughout.
pub fn dpath_left_unit3_value(
  space_ty : DValue,
  r : DValue,
  alpha : DValue,
  dlevel : Int32,
) -> DValue {
  let square = dpath_trans_square_value(
    space_ty,
    dpath_refl_value(r),
    alpha,
    dlevel,
  )
  let phase1 : DValue = DVPathLam(t => {
    DVPathLam(i => dapp_dim(dapp_dim(square, i), dim_simplify(DOr(i, DNeg(t)))))
  })
  let phase2 : DValue = DVPathLam(t => {
    DVPathLam(i => dapp_dim(dapp_dim(square, dim_simplify(DOr(i, t))), i))
  })
  dpath_trans_value(DVPathTy(_ => space_ty, r, r), phase1, phase2, dlevel)
}

///|
/// Right unit as a 3-cell: a path from `alpha ⬝ refl(r)` to
/// `alpha`, by sliding vertically through the transitivity
/// square of `(alpha, refl)`, whose bottom edge is `alpha`
/// and whose left and right edges are constant at `r`.
pub fn dpath_right_unit3_value(
  space_ty : DValue,
  r : DValue,
  alpha : DValue,
  dlevel : Int32,
) -> DValue {
  let square = dpath_trans_square_value(
    space_ty,
    alpha,
    dpath_refl_value(r),
    dlevel,
  )
  DVPathLam(t => DVPathLam(i => dapp_dim(dapp_dim(square, i), DNeg(t))))
}

///|
/// Right inverse as a 3-cell: for a loop `alpha` at `r`, a path
/// in `Path(space, r, r)` from `alpha ⬝ sym(alpha)` to
/// `refl(r)`.  This is the loop case of the corner-turning
/// cancellation square `dpath_trans_sym_cancel_value`.
pub fn dpath_right_inverse3_value(
  space_ty : DValue,
  r : DValue,
  alpha : DValue,
  dlevel : Int32,
) -> DValue {
  dpath_trans_sym_cancel_value(space_ty, alpha, r, dlevel)
}

///|
/// Left inverse as a 3-cell: a path from `sym(alpha) ⬝ alpha`
/// to `refl(r)`.  It is the right-inverse cell of `sym(alpha)`;
/// the resulting second factor is `sym(sym(alpha))`, whose
/// points are those of `alpha` because dimension application
/// simplifies double negation.
pub fn dpath_left_inverse3_value(
  space_ty : DValue,
  r : DValue,
  alpha : DValue,
  dlevel : Int32,
) -> DValue {
  dpath_right_inverse3_value(space_ty, r, dpath_sym_value(alpha), dlevel)
}

///|
/// The triple-composition square obtained by vertically stacking
/// the transitivity squares of `(p, q)` and `(p ⬝ q, s)`.
/// Vertical stacking is pointwise path transitivity in the
/// square's second coordinate.  Its bottom edge is `p`, its
/// right edge is the standard composite `q ⬝ s`, its left edge
/// is constant at the common start point, and its top edge is
/// `(p ⬝ q) ⬝ s`.
pub fn dpath_triple_square_value(
  space_ty : DValue,
  p : DValue,
  q : DValue,
  s : DValue,
  dlevel : Int32,
) -> DValue {
  let first = dpath_trans_square_value(space_ty, p, q, dlevel)
  let second = dpath_trans_square_value(
    space_ty,
    dpath_trans_value(space_ty, p, q, dlevel),
    s,
    dlevel,
  )
  DVPathLam(i => {
    dpath_trans_value(
      space_ty,
      DVPathLam(j => dapp_dim(dapp_dim(first, i), j)),
      DVPathLam(j => dapp_dim(dapp_dim(second, i), j)),
      dlevel + 2,
    )
  })
}

///|
/// Associativity as a 3-cell for loops: a path in
/// `Path(space, r, r)` from `(alpha ⬝ beta) ⬝ gamma` to
/// `alpha ⬝ (beta ⬝ gamma)`.  The triple square above and the
/// ordinary transitivity square of `(alpha, beta ⬝ gamma)` have
/// the same bottom, left and right edges.  For each point
/// `(t, i)` of the associativity square, an `hcomp` in the
/// squares' vertical direction fills the box whose `t=0` and
/// `t=1` faces are those two squares; its cap is therefore the
/// required path between their top edges, with both endpoints
/// fixed at `r`.
pub fn dpath_assoc3_value(
  space_ty : DValue,
  r : DValue,
  alpha : DValue,
  beta : DValue,
  gamma : DValue,
  dlevel : Int32,
) -> DValue {
  let alpha_beta = dpath_trans_value(space_ty, alpha, beta, dlevel)
  let beta_gamma = dpath_trans_value(space_ty, beta, gamma, dlevel)
  let s_ab = dpath_trans_square_value(space_ty, alpha, beta, dlevel)
  let s_bg = dpath_trans_square_value(space_ty, beta, gamma, dlevel)
  let s_ab_g = dpath_trans_square_value(space_ty, alpha_beta, gamma, dlevel + 2)
  let s_a_bg = dpath_trans_square_value(space_ty, alpha, beta_gamma, dlevel + 2)
  let end_pt = dapp_dim(gamma, DOne)
  let right_face = (t : Dim, k : Dim) => {
    let u = dim_simplify(DOr(DNeg(t), k))
    let r_base = dapp_dim(dapp_dim(s_bg, u), k)
    let r_sys = dsystem_of([
      tube_branch(face_simplify(FEq0(t)), _ => dapp_dim(gamma, k)),
      tube_branch(face_simplify(FEq1(t)), w => {
        dapp_dim(dapp_dim(s_bg, k), dim_simplify(DOr(k, w)))
      }),
      tube_branch(face_simplify(FEq0(k)), _ => {
        dapp_dim(beta, dim_simplify(DNeg(t)))
      }),
      tube_branch(face_simplify(FEq1(k)), _ => end_pt),
    ])
    hcomp_value(space_ty, r_sys, r_base, dlevel + 4)
  }
  DVPathLam(t => {
    DVPathLam(i => {
      let base_ti = dapp_dim(dapp_dim(s_ab, i), dim_simplify(DNeg(t)))
      let branches = dsystem_of([
        tube_branch(face_simplify(FEq0(t)), k => {
          dapp_dim(dapp_dim(s_ab_g, i), k)
        }),
        tube_branch(face_simplify(FEq1(t)), k => {
          dapp_dim(dapp_dim(s_a_bg, i), k)
        }),
        tube_branch(face_simplify(FEq0(i)), _ => r),
        tube_branch(face_simplify(FEq1(i)), k => right_face(t, k)),
      ])
      hcomp_value(space_ty, branches, base_ti, dlevel + 6)
    })
  })
}

///|
fn dloop3_trans(
  space_ty : DValue,
  r : DValue,
  first : DValue,
  second : DValue,
  dlevel : Int32,
) -> DValue {
  dpath_trans_value(DVPathTy(_ => space_ty, r, r), first, second, dlevel)
}

///|
fn dloop3_whisker_left(
  space_ty : DValue,
  alpha : DValue,
  cell : DValue,
  dlevel : Int32,
) -> DValue {
  DVPathLam(t => dpath_trans_value(space_ty, alpha, dapp_dim(cell, t), dlevel))
}

///|
fn dloop3_whisker_right(
  space_ty : DValue,
  cell : DValue,
  beta : DValue,
  dlevel : Int32,
) -> DValue {
  DVPathLam(t => dpath_trans_value(space_ty, dapp_dim(cell, t), beta, dlevel))
}

///|
/// Symmetry of a composite loop, as a 3-cell from
/// `sym(alpha ⬝ beta)` to `sym(beta) ⬝ sym(alpha)`.  The
/// proof is the standard uniqueness-of-inverses argument made
/// from the unit, inverse and associativity cells above: first
/// cancel `(alpha ⬝ beta) ⬝ (sym(beta) ⬝ sym(alpha))` by
/// reassociating and cancelling `beta` and then `alpha`, then
/// conjugate that cancellation by `sym(alpha ⬝ beta)`.
pub fn dpath_sym_compose3_value(
  space_ty : DValue,
  r : DValue,
  alpha : DValue,
  beta : DValue,
  dlevel : Int32,
) -> DValue {
  let alpha_inv = dpath_sym_value(alpha)
  let beta_inv = dpath_sym_value(beta)
  let reversed = dpath_trans_value(space_ty, beta_inv, alpha_inv, dlevel)
  let composite = dpath_trans_value(space_ty, alpha, beta, dlevel)
  // (alpha beta) reversed -> alpha (beta reversed)
  let cancel1 = dpath_assoc3_value(space_ty, r, alpha, beta, reversed, dlevel)
  // beta (beta^-1 alpha^-1) -> (beta beta^-1) alpha^-1
  let cancel2_inner = dpath_sym_value(
    dpath_assoc3_value(space_ty, r, beta, beta_inv, alpha_inv, dlevel),
  )
  let cancel2 = dloop3_whisker_left(space_ty, alpha, cancel2_inner, dlevel)
  // (beta beta^-1) alpha^-1 -> refl alpha^-1
  let cancel3_inner = dloop3_whisker_right(
    space_ty,
    dpath_right_inverse3_value(space_ty, r, beta, dlevel),
    alpha_inv,
    dlevel,
  )
  let cancel3 = dloop3_whisker_left(space_ty, alpha, cancel3_inner, dlevel)
  // refl alpha^-1 -> alpha^-1, under the left factor alpha.
  let cancel4 = dloop3_whisker_left(
    space_ty,
    alpha,
    dpath_left_unit3_value(space_ty, r, alpha_inv, dlevel),
    dlevel,
  )
  let cancel5 = dpath_right_inverse3_value(space_ty, r, alpha, dlevel)
  let mut cancellation = dloop3_trans(space_ty, r, cancel1, cancel2, dlevel)
  cancellation = dloop3_trans(space_ty, r, cancellation, cancel3, dlevel)
  cancellation = dloop3_trans(space_ty, r, cancellation, cancel4, dlevel)
  cancellation = dloop3_trans(space_ty, r, cancellation, cancel5, dlevel)
  let composite_inv = dpath_sym_value(composite)
  // composite^-1 -> composite^-1 refl
  let uniq1 = dpath_sym_value(
    dpath_right_unit3_value(space_ty, r, composite_inv, dlevel),
  )
  // composite^-1 refl -> composite^-1 (composite reversed)
  let uniq2 = dloop3_whisker_left(
    space_ty,
    composite_inv,
    dpath_sym_value(cancellation),
    dlevel,
  )
  // composite^-1 (composite reversed) -> (composite^-1 composite) reversed
  let uniq3 = dpath_sym_value(
    dpath_assoc3_value(space_ty, r, composite_inv, composite, reversed, dlevel),
  )
  // (composite^-1 composite) reversed -> refl reversed
  let uniq4 = dloop3_whisker_right(
    space_ty,
    dpath_left_inverse3_value(space_ty, r, composite, dlevel),
    reversed,
    dlevel,
  )
  let uniq5 = dpath_left_unit3_value(space_ty, r, reversed, dlevel)
  let mut result = dloop3_trans(space_ty, r, uniq1, uniq2, dlevel)
  result = dloop3_trans(space_ty, r, result, uniq3, dlevel)
  result = dloop3_trans(space_ty, r, result, uniq4, dlevel)
  dloop3_trans(space_ty, r, result, uniq5, dlevel)
}

// ---------------------------------------------------------------------------
// Phase 14: Fundamental square boundary 3-cell, unit triangle coherence,
// Eckmann-Hilton 3-cell on Omega^2, and Mac Lane's pentagon 4-cell.
// ---------------------------------------------------------------------------

///|
/// Fundamental square-boundary 3-cell: for any 2-dimensional path
/// `sq : I -> I -> space_ty` with corners `x00 = sq(0,0)` and
/// `x11 = sq(1,1)`, bottom `b0(u) = sq(u,0)`, right `r1(v) = sq(1,v)`,
/// left `l0(v) = sq(0,v)`, and top `t1(u) = sq(u,1)`, constructs an
/// explicit path in `Path(space_ty, x00, x11)` from `b0 ⬝ r1` to
/// `l0 ⬝ t1` via the diagonal `u ↦ sq(u, u)`.
pub fn dpath_square_boundary3_value(
  space_ty : DValue,
  sq : DValue,
  dlevel : Int32,
) -> DValue {
  let sq_at = (u : Dim, v : Dim) => dapp_dim(dapp_dim(sq, u), v)
  let x00 = sq_at(DZero, DZero)
  let x11 = sq_at(DOne, DOne)
  let b0 : DValue = DVPathLam(u => sq_at(u, DZero))
  let r1 : DValue = DVPathLam(v => sq_at(DOne, v))
  let l0 : DValue = DVPathLam(v => sq_at(DZero, v))
  let t1 : DValue = DVPathLam(u => sq_at(u, DOne))
  let s1 = dpath_trans_square_value(space_ty, b0, r1, dlevel)
  let s2 = dpath_trans_square_value(space_ty, l0, t1, dlevel)
  // Step 1: `(b0 ⬝ r1)` to `diag` via lower-right connection `sq(u, u ∧ v)`.
  let to_diag : DValue = DVPathLam(t => {
    DVPathLam(u => {
      let branches = dsystem_of([
        tube_branch(face_simplify(FEq0(t)), v => dapp_dim(dapp_dim(s1, u), v)),
        tube_branch(face_simplify(FEq1(t)), v => {
          sq_at(u, dim_simplify(DAnd(u, v)))
        }),
        tube_branch(face_simplify(FEq0(u)), _ => x00),
        tube_branch(face_simplify(FEq1(u)), v => dapp_dim(r1, v)),
      ])
      hcomp_value(space_ty, branches, dapp_dim(b0, u), dlevel + 4)
    })
  })
  // Step 2: `diag` to `(l0 ⬝ t1)` via upper-left connection `sq(u ∧ v, u)`.
  let from_diag : DValue = DVPathLam(t => {
    DVPathLam(u => {
      let branches = dsystem_of([
        tube_branch(face_simplify(FEq0(t)), v => {
          sq_at(dim_simplify(DAnd(u, v)), u)
        }),
        tube_branch(face_simplify(FEq1(t)), v => dapp_dim(dapp_dim(s2, u), v)),
        tube_branch(face_simplify(FEq0(u)), _ => x00),
        tube_branch(face_simplify(FEq1(u)), v => dapp_dim(t1, v)),
      ])
      hcomp_value(space_ty, branches, dapp_dim(l0, u), dlevel + 4)
    })
  })
  dpath_trans_value(
    DVPathTy(_ => space_ty, x00, x11),
    to_diag,
    from_diag,
    dlevel + 6,
  )
}

///|
/// HoTT unit coherence (`left_unit(refl_b) = right_unit(refl_b)`):
/// for any `b : ty`, constructs a 4-cell in
/// `Path(Path(Path(ty, b, b), refl_b ⬝ refl_b, refl_b), left_unit(refl_b), right_unit(refl_b))`.
pub fn dpath_lr_unit_coherence4_value(
  ty : DValue,
  b : DValue,
  dlevel : Int32,
) -> DValue {
  let e = dpath_refl_value(b)
  let loop1_ty = DVPathTy(_ => ty, b, b)
  let ee = dpath_trans_value(ty, e, e, dlevel)
  let unit_path_ty = DVPathTy(_ => loop1_ty, ee, e)
  let sq = dpath_trans_square_value(ty, e, e, dlevel)
  let sq_at = (u : Dim, v : Dim) => dapp_dim(dapp_dim(sq, u), v)
  let diag : DValue = DVPathLam(i => sq_at(i, i))
  let phase1 : DValue = DVPathLam(t => {
    DVPathLam(i => sq_at(i, dim_simplify(DOr(i, DNeg(t)))))
  })
  let step_b1 : DValue = DVPathLam(t => {
    DVPathLam(i => sq_at(i, dim_simplify(DAnd(i, DNeg(t)))))
  })
  // `phase2` (`S(i ∨ t, i)`) -> `S(i ∨ t, i ∧ ¬t)` -> `step_b1` (`S(i, i ∧ ¬t)`).
  let p2_to_mid : DValue = DVPathLam(s => {
    DVPathLam(t => {
      DVPathLam(i => {
        sq_at(dim_simplify(DOr(i, t)), dim_simplify(DAnd(i, DNeg(DAnd(s, t)))))
      })
    })
  })
  let mid_to_b1 : DValue = DVPathLam(s => {
    DVPathLam(t => {
      DVPathLam(i => {
        sq_at(
          dim_simplify(DOr(i, DAnd(t, DNeg(s)))),
          dim_simplify(DAnd(i, DNeg(t))),
        )
      })
    })
  })
  let p2_to_b1 = dpath_trans_value(
    DVPathTy(_ => loop1_ty, diag, e),
    p2_to_mid,
    mid_to_b1,
    dlevel + 4,
  )
  let whisker_p1 : DValue = DVPathLam(s => {
    dpath_trans_value(loop1_ty, phase1, dapp_dim(p2_to_b1, s), dlevel)
  })
  // Connect `phase1 ⬝ step_b1` to `right_unit(e)` (`t ↦ i ↦ S(i, ¬t)`)
  // using the comparison square `K(t, u)(i) = S(i, ¬t ∨ (i ∧ ¬u))`.
  let trans_p1_b1 = dpath_trans_square_value(loop1_ty, phase1, step_b1, dlevel)
  let to_right : DValue = DVPathLam(s => {
    DVPathLam(t => {
      let branches = dsystem_of([
        tube_branch(face_simplify(FEq0(s)), u => {
          dapp_dim(dapp_dim(trans_p1_b1, t), u)
        }),
        tube_branch(face_simplify(FEq1(s)), u => {
          DVPathLam(i => sq_at(i, dim_simplify(DOr(DNeg(t), DAnd(i, DNeg(u))))))
        }),
        tube_branch(face_simplify(FEq0(t)), _ => ee),
        tube_branch(face_simplify(FEq1(t)), u => dapp_dim(step_b1, u)),
      ])
      hcomp_value(loop1_ty, branches, dapp_dim(phase1, t), dlevel + 6)
    })
  })
  dpath_trans_value(unit_path_ty, whisker_p1, to_right, dlevel + 6)
}

///|
/// Eckmann-Hilton commutativity 3-cell on `Omega^2(ty, b)`: for any
/// two 2-loops `alpha, beta : Path(Path(ty, b, b), refl_b, refl_b)`,
/// builds a 3-cell in `Path(Omega^2(ty, b), alpha ⬝ beta, beta ⬝ alpha)`
/// with zero assumptions on `ty` or `b`.
pub fn dpath_eckmann_hilton3_value(
  ty : DValue,
  b : DValue,
  alpha : DValue,
  beta : DValue,
  dlevel : Int32,
) -> DValue {
  let e = dpath_refl_value(b)
  let y_ty = DVPathTy(_ => ty, b, b)
  let c0 = dpath_right_unit3_value(ty, b, e, dlevel) // ee = e in y_ty
  let lr_coh = dpath_lr_unit_coherence4_value(ty, b, dlevel) // l0 = c0

  // Torus-like bifunctor square `G(u, v) = alpha(u) ⬝ beta(v)` in `y_ty`.
  let g_sq : DValue = DVPathLam(u => {
    DVPathLam(v => {
      dpath_trans_value(ty, dapp_dim(alpha, u), dapp_dim(beta, v), dlevel)
    })
  })
  let a_loop : DValue = DVPathLam(u => {
    dpath_trans_value(ty, dapp_dim(alpha, u), e, dlevel)
  })
  let b_loop : DValue = DVPathLam(v => {
    dpath_trans_value(ty, e, dapp_dim(beta, v), dlevel)
  })
  // In `Omega(y_ty, ee)`: `a_loop ⬝ b_loop = b_loop ⬝ a_loop`.
  let raw_comm = dpath_square_boundary3_value(y_ty, g_sq, dlevel)
  // Transport `Omega(y_ty, ee)` along `c0 : ee = e` into `Omega(y_ty, e) = Omega^2(ty, b)`.
  let conj_by_c0 = (loop_ee : DValue) => {
    subst_value(pt => DVPathTy(_ => y_ty, pt, pt), c0, loop_ee, dlevel + 4)
  }
  let comm_conj = DVPathLam(t => conj_by_c0(dapp_dim(raw_comm, t)))

  // Connect `conj_by_c0(a_loop)` to `alpha`: naturality of `right_unit` gives
  // a dependent path over `u ↦ Path(y_ty, c0(u), c0(u))` from `a_loop` to `alpha`,
  // so `transport` along `u ↦ Path(y_ty, c0(u), c0(u))` takes `a_loop` to `alpha`!
  let a_dep_line : DValue = DVPathLam(s => {
    DVPathLam(u => {
      dapp_dim(dpath_right_unit3_value(ty, b, dapp_dim(alpha, u), dlevel), s)
    })
  })
  // And for `b_loop`: `s ↦ u ↦ left_unit(beta(u))(s)` has endpoints `l0(s)` at `u=0,1`,
  // corrected to `c0(s)` via `lr_coh`!
  let b_dep_raw : DValue = DVPathLam(s => {
    DVPathLam(u => {
      let base_pt = dapp_dim(
        dpath_left_unit3_value(ty, b, dapp_dim(beta, u), dlevel),
        s,
      )
      let branches = dsystem_of([
        tube_branch(face_simplify(FEq0(u)), w => {
          dapp_dim(dapp_dim(lr_coh, w), s)
        }),
        tube_branch(face_simplify(FEq1(u)), w => {
          dapp_dim(dapp_dim(lr_coh, w), s)
        }),
        tube_branch(face_simplify(FEq0(s)), _ => dapp_dim(b_loop, u)),
        tube_branch(face_simplify(FEq1(s)), _ => dapp_dim(beta, u)),
      ])
      hcomp_value(y_ty, branches, base_pt, dlevel + 6)
    })
  })
  // `subst` from `s = 0` (`ee`) to `s = 1` (`e`) along a `PathP (s => Path(y_ty, c0 s, c0 s)) X Y`
  // equals `Y` via `transport_filler` comparison!
  let dep_to_subst_eq = (x_ee : DValue, dep_p : DValue) => {
    let fam = (s : Dim) => {
      let pt = dapp_dim(c0, s)
      DVPathTy(_ => y_ty, pt, pt)
    }
    let tf = transport_filler_value(fam, x_ee, dlevel + 4)
    DVPathLam(w => {
      let branches = dsystem_of([
        tube_branch(face_simplify(FEq0(w)), s => tf(s)),
        tube_branch(face_simplify(FEq1(w)), s => dapp_dim(dep_p, s)),
      ])
      comp_value(fam, branches, x_ee, dlevel + 6)
    })
  }
  let eq_a = dep_to_subst_eq(a_loop, a_dep_line) // conj_by_c0(a_loop) = alpha
  let eq_b = dep_to_subst_eq(b_loop, b_dep_raw) // conj_by_c0(b_loop) = beta

  // Functoriality of `subst` over loop composition:
  // `conj_by_c0(p ⬝ q) = conj_by_c0(p) ⬝ conj_by_c0(q)`.
  let subst_comp_eq = (p_ee : DValue, q_ee : DValue) => {
    let fam = (s : Dim) => {
      let pt = dapp_dim(c0, s)
      DVPathTy(_ => y_ty, pt, pt)
    }
    let pf = transport_filler_value(fam, p_ee, dlevel + 4)
    let qf = transport_filler_value(fam, q_ee, dlevel + 4)
    let pq_f = transport_filler_value(
      fam,
      dpath_trans_value(y_ty, p_ee, q_ee, dlevel),
      dlevel + 4,
    )
    DVPathLam(w => {
      let branches = dsystem_of([
        tube_branch(face_simplify(FEq0(w)), s => pq_f(s)),
        tube_branch(face_simplify(FEq1(w)), s => {
          let pt = dapp_dim(c0, s)
          dpath_trans_value(y_ty, pf(s), qf(s), dlevel + 4)
          |> v => {
            ignore(pt)
            v
          }
        }),
      ])
      comp_value(
        fam,
        branches,
        dpath_trans_value(y_ty, p_ee, q_ee, dlevel),
        dlevel + 8,
      )
    })
  }

  let lhs_step1 = dpath_sym_value(subst_comp_eq(a_loop, b_loop)) // conj(a)·conj(b) -> conj(a·b)
  let lhs_step0 : DValue = DVPathLam(w => {
    dpath_trans_value(
      y_ty,
      dapp_dim(dpath_sym_value(eq_a), w),
      dapp_dim(dpath_sym_value(eq_b), w),
      dlevel,
    )
  }) // α·β -> conj(a)·conj(b)
  let rhs_step1 = subst_comp_eq(b_loop, a_loop) // conj(b·a) -> conj(b)·conj(a)
  let rhs_step2 : DValue = DVPathLam(w => {
    dpath_trans_value(y_ty, dapp_dim(eq_b, w), dapp_dim(eq_a, w), dlevel)
  }) // conj(b)·conj(a) -> β·α

  let mut out = dloop3_trans(y_ty, e, lhs_step0, lhs_step1, dlevel + 4)
  out = dloop3_trans(y_ty, e, out, comm_conj, dlevel + 4)
  out = dloop3_trans(y_ty, e, out, rhs_step1, dlevel + 4)
  dloop3_trans(y_ty, e, out, rhs_step2, dlevel + 4)
}

///|
/// Associativity 3-cell for arbitrary composable paths
/// `p : x0 = x1`, `q : x1 = x2`, `u : x2 = x3`: a path in
/// `Path(space_ty, x0, x3)` from `(p ⬝ q) ⬝ u` to `p ⬝ (q ⬝ u)`.
pub fn dpath_assoc_path3_value(
  space_ty : DValue,
  p : DValue,
  q : DValue,
  u : DValue,
  dlevel : Int32,
) -> DValue {
  let x0 = dapp_dim(p, DZero)
  let qu = dpath_trans_value(space_ty, q, u, dlevel)
  let left_square = dpath_triple_square_value(space_ty, p, q, u, dlevel)
  let right_square = dpath_trans_square_value(space_ty, p, qu, dlevel)
  DVPathLam(t => {
    DVPathLam(i => {
      let branches = dsystem_of([
        tube_branch(face_simplify(FEq0(t)), j => {
          dapp_dim(dapp_dim(left_square, i), j)
        }),
        tube_branch(face_simplify(FEq1(t)), j => {
          dapp_dim(dapp_dim(right_square, i), j)
        }),
        tube_branch(face_simplify(FEq0(i)), _ => x0),
        tube_branch(face_simplify(FEq1(i)), j => dapp_dim(qu, j)),
      ])
      hcomp_value(space_ty, branches, dapp_dim(p, i), dlevel + 6)
    })
  })
}

///|
/// Top 2-step route of Mac Lane's pentagon for arbitrary composable
/// paths `p : x0 = x1`, `q : x1 = x2`, `u : x2 = x3`, `v : x3 = x4`.
pub fn dpath_pentagon_path_top3_value(
  space_ty : DValue,
  p : DValue,
  q : DValue,
  u : DValue,
  v : DValue,
  dlevel : Int32,
) -> DValue {
  let x0 = dapp_dim(p, DZero)
  let x4 = dapp_dim(v, DOne)
  let pq = dpath_trans_value(space_ty, p, q, dlevel)
  let uv = dpath_trans_value(space_ty, u, v, dlevel)
  let step1 = dpath_assoc_path3_value(space_ty, pq, u, v, dlevel)
  let step2 = dpath_assoc_path3_value(space_ty, p, q, uv, dlevel)
  dpath_trans_value(DVPathTy(_ => space_ty, x0, x4), step1, step2, dlevel + 2)
}

///|
/// Bottom 3-step route of Mac Lane's pentagon for arbitrary composable
/// paths `p : x0 = x1`, `q : x1 = x2`, `u : x2 = x3`, `v : x3 = x4`.
pub fn dpath_pentagon_path_bot3_value(
  space_ty : DValue,
  p : DValue,
  q : DValue,
  u : DValue,
  v : DValue,
  dlevel : Int32,
) -> DValue {
  let x0 = dapp_dim(p, DZero)
  let x4 = dapp_dim(v, DOne)
  let path_ty = DVPathTy(_ => space_ty, x0, x4)
  let qu = dpath_trans_value(space_ty, q, u, dlevel)
  let assoc_pqu = dpath_assoc_path3_value(space_ty, p, q, u, dlevel)
  let step1 : DValue = DVPathLam(t => {
    dpath_trans_value(space_ty, dapp_dim(assoc_pqu, t), v, dlevel)
  })
  let step2 = dpath_assoc_path3_value(space_ty, p, qu, v, dlevel)
  let assoc_quv = dpath_assoc_path3_value(space_ty, q, u, v, dlevel)
  let step3 : DValue = DVPathLam(t => {
    dpath_trans_value(space_ty, p, dapp_dim(assoc_quv, t), dlevel)
  })
  let first = dpath_trans_value(path_ty, step1, step2, dlevel + 2)
  dpath_trans_value(path_ty, first, step3, dlevel + 2)
}

///|
/// Top 2-step route of Mac Lane's pentagon on loops at `r`.
pub fn dpath_pentagon_top3_value(
  space_ty : DValue,
  r : DValue,
  alpha : DValue,
  beta : DValue,
  gamma : DValue,
  delta : DValue,
  dlevel : Int32,
) -> DValue {
  ignore(r)
  dpath_pentagon_path_top3_value(space_ty, alpha, beta, gamma, delta, dlevel)
}

///|
/// Bottom 3-step route of Mac Lane's pentagon on loops at `r`.
pub fn dpath_pentagon_bot3_value(
  space_ty : DValue,
  r : DValue,
  alpha : DValue,
  beta : DValue,
  gamma : DValue,
  delta : DValue,
  dlevel : Int32,
) -> DValue {
  ignore(r)
  dpath_pentagon_path_bot3_value(space_ty, alpha, beta, gamma, delta, dlevel)
}

///|
/// Mac Lane's pentagon coherence 4-cell: for any space `space_ty` whose
/// constant Kan boxes normalize on `r` (all concrete types, spheres,
/// circles, tori, functions, pairs, universes) and any four composable
/// loops `alpha, beta, gamma, delta : Omega(space_ty, r)`, constructs
/// an explicit 4-cell in
/// `Path(Path(Omega(space_ty, r), ((alpha ⬝ beta) ⬝ gamma) ⬝ delta, alpha ⬝ (beta ⬝ (gamma ⬝ delta))), pentagon_top, pentagon_bot)`
/// by 4-stage cubical singleton contraction (`coe` over path prefixes).
pub fn dpath_pentagon4_value(
  space_ty : DValue,
  r : DValue,
  alpha : DValue,
  beta : DValue,
  gamma : DValue,
  delta : DValue,
  dlevel : Int32,
) -> DValue {
  let pent_type = (p : DValue, q : DValue, u : DValue, v : DValue) => {
    let x0 = dapp_dim(p, DZero)
    let x4 = dapp_dim(v, DOne)
    let path1_ty = DVPathTy(_ => space_ty, x0, x4)
    let pqu = dpath_trans_value(
      space_ty,
      dpath_trans_value(space_ty, p, q, dlevel),
      u,
      dlevel,
    )
    let lhs = dpath_trans_value(space_ty, pqu, v, dlevel)
    let quv = dpath_trans_value(
      space_ty,
      q,
      dpath_trans_value(space_ty, u, v, dlevel),
      dlevel,
    )
    let rhs = dpath_trans_value(space_ty, p, quv, dlevel)
    let path2_ty = DVPathTy(_ => path1_ty, lhs, rhs)
    let top3 = dpath_pentagon_path_top3_value(space_ty, p, q, u, v, dlevel)
    let bot3 = dpath_pentagon_path_bot3_value(space_ty, p, q, u, v, dlevel)
    DVPathTy(_ => path2_ty, top3, bot3)
  }
  let refl_r = dpath_refl_value(r)
  let base_cell = dpath_refl_value(
    dpath_pentagon_path_top3_value(
      space_ty, refl_r, refl_r, refl_r, refl_r, dlevel,
    ),
  )
  // Stage 1: contract `alpha` from `refl_r` to `alpha` (`w1 : 0 -> 1`).
  let cell1 = transport_value(
    w1 => {
      let p1 = dpath_prefix_value(alpha, w1)
      let x1 = dapp_dim(alpha, w1)
      let rx1 = dpath_refl_value(x1)
      pent_type(p1, rx1, rx1, rx1)
    },
    base_cell,
    dlevel + 4,
  )
  // Stage 2: contract `beta` from `refl_r` to `beta` (`w2 : 0 -> 1`).
  let cell2 = transport_value(
    w2 => {
      let q2 = dpath_prefix_value(beta, w2)
      let x2 = dapp_dim(beta, w2)
      let rx2 = dpath_refl_value(x2)
      pent_type(alpha, q2, rx2, rx2)
    },
    cell1,
    dlevel + 4,
  )
  // Stage 3: contract `gamma` from `refl_r` to `gamma` (`w3 : 0 -> 1`).
  let cell3 = transport_value(
    w3 => {
      let u3 = dpath_prefix_value(gamma, w3)
      let x3 = dapp_dim(gamma, w3)
      let rx3 = dpath_refl_value(x3)
      pent_type(alpha, beta, u3, rx3)
    },
    cell2,
    dlevel + 4,
  )
  // Stage 4: contract `delta` from `refl_r` to `delta` (`w4 : 0 -> 1`).
  transport_value(
    w4 => {
      let v4 = dpath_prefix_value(delta, w4)
      pent_type(alpha, beta, gamma, v4)
    },
    cell3,
    dlevel + 4,
  )
}

///|
/// Lift a homogeneous equality `eq_in_line1 : Path (line(1)) (transport line v0) v1`
/// to a dependent path `PathP (i => line(i)) v0 v1` with definitionally exact
/// endpoints `v0` at `0` and `v1` at `1`.
pub fn dpathp_of_transport_eq_value(
  line : (Dim) -> DValue,
  v0 : DValue,
  _v1 : DValue,
  eq_in_line1 : DValue,
  dlevel : Int32,
) -> DValue {
  let mline = memo_dim_line(line)
  let filler = transport_filler_value(mline, v0, dlevel)
  DVPathLam(i => {
    let sys = dsystem_of([
      tube_branch(face_simplify(FEq0(i)), _ => v0),
      tube_branch(face_simplify(FEq1(i)), j => dapp_dim(eq_in_line1, j)),
    ])
    hcomp_value(mline(i), sys, filler(i), dlevel + 2)
  })
}

///|
/// Project a dependent path `p : PathP (i => line(i)) v0 v1` to a homogeneous
/// path `Path (line(1)) (transport line v0) v1`.
pub fn dpath_of_pathp_value(
  line : (Dim) -> DValue,
  p : DValue,
  dlevel : Int32,
) -> DValue {
  let mline = memo_dim_line(line)
  let v0 = dapp_dim(p, DZero)
  let filler = transport_filler_value(mline, v0, dlevel)
  DVPathLam(j => {
    let sys = dsystem_of([
      tube_branch(face_simplify(FEq0(j)), i => filler(i)),
      tube_branch(face_simplify(FEq1(j)), i => dapp_dim(p, i)),
    ])
    comp_value(mline, sys, v0, dlevel + 2)
  })
}

///|
/// Dependent path equality in a family whose right endpoint fiber `line(1)`
/// is an h-Set: given `p1, p2 : PathP (i => line(i)) u0 u1` and a witness
/// `is_set_line1 : (a b : line(1)) -> (alpha beta : Path (line(1)) a b) -> Path (...) alpha beta`,
/// constructs `Path (PathP (i => line(i)) u0 u1) p1 p2` with definitionally
/// exact boundaries `p1`, `p2`, `u0`, and `u1`.
pub fn dpathp_eq_in_set_family_value(
  line : (Dim) -> DValue,
  u0 : DValue,
  u1 : DValue,
  p1 : DValue,
  p2 : DValue,
  is_set_line1 : (DValue, DValue, DValue, DValue) -> DValue,
  dlevel : Int32,
) -> DValue {
  let mline = memo_dim_line(line)
  let open_fill = (r : Dim, i : Dim) => {
    let sys = dsystem_of([
      tube_branch(face_simplify(FEq0(r)), k => dapp_dim(p1, k)),
      tube_branch(face_simplify(FEq1(r)), k => dapp_dim(p2, k)),
    ])
    fill_value(mline, sys, u0, dlevel + 2)(i)
  }
  let top_cap = DVPathLam(r => open_fill(r, DOne))
  let lid = is_set_line1(u1, u1, top_cap, dpath_refl_value(u1))
  DVPathLam(r => {
    DVPathLam(i => {
      let sys = dsystem_of([
        tube_branch(face_simplify(FEq0(r)), _ => dapp_dim(p1, i)),
        tube_branch(face_simplify(FEq1(r)), _ => dapp_dim(p2, i)),
        tube_branch(face_simplify(FEq0(i)), _ => u0),
        tube_branch(face_simplify(FEq1(i)), j => dapp_dim(dapp_dim(lid, j), r)),
      ])
      hcomp_value(mline(i), sys, open_fill(r, i), dlevel + 4)
    })
  })
}

///|
/// Cubical Paulin-Mohring `J` (based singleton contraction): given
/// `motive : (y : A, p : Path A a0 y) -> Type`, `refl_case : motive(a0, refl a0)`,
/// and `p : Path A a0 y`, transports `refl_case` along `w => (p(w), p_{<= w})`.
pub fn dj_singleton_elim_value(
  motive : (DValue, DValue) -> DValue,
  refl_case : DValue,
  p : DValue,
  dlevel : Int32,
) -> DValue {
  transport_value(
    memo_dim_line(w => motive(dapp_dim(p, w), dpath_prefix_value(p, w))),
    refl_case,
    dlevel,
  )
}

///|
/// HoTT Lemma 3.3.4 (every h-Proposition is an h-Set): given `is_prop : (u v : P) -> Path P u v`
/// and `p, q : Path P x y`, constructs `Path (Path P x y) p q` with exact
/// endpoints `p` and `q` by factoring through `canon(y) = sym(is_prop x x) . is_prop x y`.
pub fn dprop_is_set_value(
  p_ty : DValue,
  is_prop : (DValue, DValue) -> DValue,
  x : DValue,
  y : DValue,
  p : DValue,
  q : DValue,
  dlevel : Int32,
) -> DValue {
  let canon = (target : DValue) => {
    dpath_trans_value(
      p_ty,
      dpath_sym_value(is_prop(x, x)),
      is_prop(x, target),
      dlevel,
    )
  }
  let base_cancel = dpath_left_inverse3_value(
    p_ty,
    x,
    is_prop(x, x),
    dlevel + 1,
  )
  let canon_to_path = (r : DValue) => {
    dj_singleton_elim_value(
      (y1, r1) => {
        let eq_ty = DVPathTy(_ => p_ty, x, y1)
        DVPathTy(_ => eq_ty, canon(y1), r1)
      },
      base_cancel,
      r,
      dlevel + 3,
    )
  }
  let path_ty = DVPathTy(_ => p_ty, x, y)
  dpath_trans_value(
    path_ty,
    dpath_sym_value(canon_to_path(p)),
    canon_to_path(q),
    dlevel + 4,
  )
}

// ===========================================================================
// Phase 16 (Track 5): Open-Context Dependent Path / Sigma-Path / Fibration
// Loop Equivalences, Transport Functoriality, and 5D Stasheff Associahedron K5
// ===========================================================================

///|
/// Transport along a reflexive path `subst(fam, refl(x), u) = u` in `fam(x)`.
pub fn subst_refl_eq_value(
  fam : (DValue) -> DValue,
  x : DValue,
  u : DValue,
  dlevel : Int32,
) -> DValue {
  let fx = fam(x)
  let line : (Dim) -> DValue = _ => fx
  let filler = transport_filler_value(line, u, dlevel + 1)
  DVPathLam(i => filler(DNeg(i)))
}

///|
/// General open-context functoriality of `subst` over path concatenation:
/// for arbitrary `fam : A -> Type`, `p : Path A x y`, `q : Path A y z`, and
/// `u0 : fam(x)`, constructs
///   `Path (fam z) (subst fam (p ⬝ q) u0) (subst fam q (subst fam p u0))`
/// with definitionally exact endpoints via cubical Paulin-Mohring `J` on `q`.
pub fn subst_trans_eq_value(
  fam : (DValue) -> DValue,
  a_ty : DValue,
  p : DValue,
  q : DValue,
  u0 : DValue,
  dlevel : Int32,
) -> DValue {
  let y0 = dapp_dim(p, DOne)
  let motive = (z1 : DValue, q1 : DValue) => {
    let pq1 = dpath_trans_value(a_ty, p, q1, dlevel)
    let lhs = subst_value(fam, pq1, u0, dlevel + 1)
    let rhs = subst_value(
      fam,
      q1,
      subst_value(fam, p, u0, dlevel + 1),
      dlevel + 2,
    )
    DVPathTy(_ => fam(z1), lhs, rhs)
  }
  let ru_p = dpath_right_unit3_value(a_ty, y0, p, dlevel)
  let sp = subst_value(fam, p, u0, dlevel + 1)
  let step1 : DValue = DVPathLam(t => {
    subst_value(fam, dapp_dim(ru_p, t), u0, dlevel + 1)
  })
  let step2 = dpath_sym_value(subst_refl_eq_value(fam, y0, sp, dlevel + 2))
  let refl_case = dpath_trans_value(fam(y0), step1, step2, dlevel + 3)
  dj_singleton_elim_value(motive, refl_case, q, dlevel + 5)
}

///|
/// First-class bidirectional equivalence between heterogeneous dependent paths
/// and homogeneous transported paths in an open context:
///   `Equiv (PathP (i => line i) v0 v1) (Path (line 1) (transport line v0) v1)`.
/// Constructed by `pathToEquiv` along the 1-parameter path-type family
/// `s ↦ PathP (i => line(i ∨ s)) (transport_filler line v0 s) v1`, whose
/// `s = 0` and `s = 1` fibers are definitionally `PathP line v0 v1` and
/// `Path (line 1) (transport line v0) v1`.
pub fn pathp_equiv_transport_eq_value(
  line : (Dim) -> DValue,
  v0 : DValue,
  v1 : DValue,
  dlevel : Int32,
  level~ : Int32 = 0,
) -> DValue {
  let mline = memo_dim_line(line)
  let filler = transport_filler_value(mline, v0, dlevel)
  let src = DVPathTy(mline, v0, v1)
  let tr_v0 = transport_value(mline, v0, dlevel)
  let dst = DVPathTy(_ => mline(DOne), tr_v0, v1)
  let type_line = memo_dim_line(s => {
    DVPathTy(i => mline(dim_simplify(DOr(i, s))), filler(s), v1)
  })
  path_to_equiv_value(type_line, src, dst, level, dlevel + 2)
}

///|
/// First-class bidirectional equivalence characterizing identity in any
/// dependent pair type `Σ (x : A), P(x)`:
///   `Equiv (Path (Σ A P) u v) (Σ (p : Path A (fst u) (fst v)), PathP (i => P (p i)) (snd u) (snd v))`.
/// Because the kernel enforces judgmental surjective-pairing `η` on `DVSigma`
/// and `DVPathTy`, both round-trip homotopies reduce definitionally to `refl`.
pub fn sigma_path_equiv_value(
  a_ty : DValue,
  p_fam : (DValue) -> DValue,
  u : DValue,
  v : DValue,
  _dlevel : Int32,
) -> DValue {
  let sig_ty = DVSigma(a_ty, p_fam)
  let src = DVPathTy(_ => sig_ty, u, v)
  let u1 = dfst_typed(u, p_fam)
  let v1 = dfst_typed(v, p_fam)
  let u2 = dsnd_typed(u, a_ty, p_fam)
  let v2 = dsnd_typed(v, a_ty, p_fam)
  let base_path_ty = DVPathTy(_ => a_ty, u1, v1)
  let dep_fam = (p : DValue) => DVPathTy(i => p_fam(dapp_dim(p, i)), u2, v2)
  let dst = DVSigma(base_path_ty, dep_fam)
  let fwd = DVLam(q => {
    DVPair(
      DVPathLam(i => dfst_typed(dapp_dim(q, i), p_fam)),
      DVPathLam(i => dsnd_typed(dapp_dim(q, i), a_ty, p_fam)),
    )
  })
  let bwd = DVLam(pr => {
    let p = dfst_typed(pr, dep_fam)
    let r = dsnd_typed(pr, base_path_ty, dep_fam)
    DVPathLam(i => DVPair(dapp_dim(p, i), dapp_dim(r, i)))
  })
  equiv_make_value(
    src,
    dst,
    fwd,
    bwd,
    DVLam(pr => dpath_refl_value(pr)),
    DVLam(q => dpath_refl_value(q)),
  )
}

///|
/// Fiberwise congruence of `DVSigma` in the second component:
/// given `fiber_eq : (x : A) -> Equiv (P x) (Q x)`, constructs
///   `Equiv (Σ (x : A), P x) (Σ (x : A), Q x)`.
pub fn sigma_cong_snd_equiv_value(
  a_ty : DValue,
  p_fam : (DValue) -> DValue,
  q_fam : (DValue) -> DValue,
  fiber_eq : (DValue) -> DValue,
) -> DValue {
  let src = DVSigma(a_ty, p_fam)
  let dst = DVSigma(a_ty, q_fam)
  let fwd = DVLam(w => {
    let x = dfst_typed(w, p_fam)
    let y = dsnd_typed(w, a_ty, p_fam)
    DVPair(x, equiv_fun_value(fiber_eq(x), p_fam(x), q_fam(x), y))
  })
  let bwd = DVLam(w => {
    let x = dfst_typed(w, q_fam)
    let z = dsnd_typed(w, a_ty, q_fam)
    DVPair(x, equiv_inv_fun_value(fiber_eq(x), p_fam(x), q_fam(x), z))
  })
  let sect = DVLam(w => {
    let x = dfst_typed(w, q_fam)
    let z = dsnd_typed(w, a_ty, q_fam)
    let s = dapp_typed(
      equiv_sect_value(fiber_eq(x), p_fam(x), q_fam(x)),
      z,
      q_fam(x),
    )
    DVPathLam(i => DVPair(x, dapp_dim(s, i)))
  })
  let retr = DVLam(w => {
    let x = dfst_typed(w, p_fam)
    let y = dsnd_typed(w, a_ty, p_fam)
    let r = dapp_typed(
      equiv_retr_value(fiber_eq(x), p_fam(x), q_fam(x)),
      y,
      p_fam(x),
    )
    DVPathLam(i => DVPair(x, dapp_dim(r, i)))
  })
  equiv_make_value(src, dst, fwd, bwd, sect, retr)
}

///|
/// Homogeneous transport characterization of `Σ`-paths in an open context:
///   `Equiv (Path (Σ A P) u v) (Σ (p : Path A (fst u) (fst v)), Path (P (fst v)) (subst P p (snd u)) (snd v))`.
pub fn sigma_path_equiv_subst_value(
  a_ty : DValue,
  p_fam : (DValue) -> DValue,
  u : DValue,
  v : DValue,
  dlevel : Int32,
  level~ : Int32 = 0,
) -> DValue {
  let sig_ty = DVSigma(a_ty, p_fam)
  let u1 = dfst_typed(u, p_fam)
  let v1 = dfst_typed(v, p_fam)
  let u2 = dsnd_typed(u, a_ty, p_fam)
  let v2 = dsnd_typed(v, a_ty, p_fam)
  let base_path_ty = DVPathTy(_ => a_ty, u1, v1)
  let dep_fam = (p : DValue) => DVPathTy(i => p_fam(dapp_dim(p, i)), u2, v2)
  let subst_fam = (p : DValue) => {
    DVPathTy(_ => p_fam(v1), subst_value(p_fam, p, u2, dlevel), v2)
  }
  let fiber_eq_at = (p : DValue) => {
    pathp_equiv_transport_eq_value(
      i => p_fam(dapp_dim(p, i)),
      u2,
      v2,
      dlevel,
      level~,
    )
  }
  let src_ty = DVPathTy(_ => sig_ty, u, v)
  let dst_ty = DVSigma(base_path_ty, subst_fam)
  let fwd = DVLam(q => {
    let p = DVPathLam(i => dfst_typed(dapp_dim(q, i), p_fam))
    let r_dep = DVPathLam(i => dsnd_typed(dapp_dim(q, i), a_ty, p_fam))
    let feq = fiber_eq_at(p)
    DVPair(p, equiv_fun_value(feq, dep_fam(p), subst_fam(p), r_dep))
  })
  let bwd = DVLam(pr => {
    let p = dfst_typed(pr, subst_fam)
    let r_hom = dsnd_typed(pr, base_path_ty, subst_fam)
    let feq = fiber_eq_at(p)
    let r_dep = equiv_inv_fun_value(feq, dep_fam(p), subst_fam(p), r_hom)
    DVPathLam(i => DVPair(dapp_dim(p, i), dapp_dim(r_dep, i)))
  })
  let sect = DVLam(pr => {
    let p = dfst_typed(pr, subst_fam)
    let r_hom = dsnd_typed(pr, base_path_ty, subst_fam)
    let feq = fiber_eq_at(p)
    let s = dapp_typed(
      equiv_sect_value(feq, dep_fam(p), subst_fam(p)),
      r_hom,
      subst_fam(p),
    )
    DVPathLam(k => DVPair(p, dapp_dim(s, k)))
  })
  let retr = DVLam(q => {
    let p = DVPathLam(i => dfst_typed(dapp_dim(q, i), p_fam))
    let r_dep = DVPathLam(i => dsnd_typed(dapp_dim(q, i), a_ty, p_fam))
    let feq = fiber_eq_at(p)
    let r = dapp_typed(
      equiv_retr_value(feq, dep_fam(p), subst_fam(p)),
      r_dep,
      dep_fam(p),
    )
    DVPathLam(k => {
      DVPathLam(i => DVPair(dapp_dim(p, i), dapp_dim(dapp_dim(r, k), i)))
    })
  })
  equiv_make_value(src_ty, dst_ty, fwd, bwd, sect, retr)
}

///|
/// General fibration fiber-sequence loop-space classification in an open context:
/// for any base `B`, family `P : B -> Type`, basepoint `b0 : B`, and fiber
/// basepoint `e0 : P(b0)`, constructs the bidirectional equivalence
///   `Equiv (Ω¹(Σ B P, (b0, e0))) (Σ (p : Ω¹(B, b0)), Path (P b0) (subst P p e0) e0)`.
pub fn fibration_loop_equiv_fiber_path_value(
  b_ty : DValue,
  p_fam : (DValue) -> DValue,
  b0 : DValue,
  e0 : DValue,
  dlevel : Int32,
  level~ : Int32 = 0,
) -> DValue {
  let total_pt = DVPair(b0, e0)
  sigma_path_equiv_subst_value(b_ty, p_fam, total_pt, total_pt, dlevel, level~)
}

///|
/// Split 5-fold parenthesization `(p ⬝ q) ⬝ ((u ⬝ v) ⬝ w)` (source vertex of
/// the `K_5` naturality facet commuting left `(p, q, _)` and right `(u, v, w)`
/// associators).
pub fn dpath_k5_lhs1_value(
  space_ty : DValue,
  p : DValue,
  q : DValue,
  u : DValue,
  v : DValue,
  w : DValue,
  dlevel : Int32,
) -> DValue {
  let pq = dpath_trans_value(space_ty, p, q, dlevel)
  let uv = dpath_trans_value(space_ty, u, v, dlevel)
  let uvw = dpath_trans_value(space_ty, uv, w, dlevel)
  dpath_trans_value(space_ty, pq, uvw, dlevel)
}

///|
/// Rightmost 5-fold path parenthesization `p ⬝ (q ⬝ (u ⬝ (v ⬝ w)))`.
pub fn dpath_k5_rhs1_value(
  space_ty : DValue,
  p : DValue,
  q : DValue,
  u : DValue,
  v : DValue,
  w : DValue,
  dlevel : Int32,
) -> DValue {
  let vw = dpath_trans_value(space_ty, v, w, dlevel)
  let uvw = dpath_trans_value(space_ty, u, vw, dlevel)
  let quvw = dpath_trans_value(space_ty, q, uvw, dlevel)
  dpath_trans_value(space_ty, p, quvw, dlevel)
}

///|
fn dpath_k5_interchange_square_value(
  space_ty : DValue,
  p : DValue,
  q : DValue,
  u : DValue,
  v : DValue,
  w : DValue,
  dlevel : Int32,
) -> DValue {
  let assoc_uvw = dpath_assoc_path3_value(space_ty, u, v, w, dlevel)
  DVPathLam(
    memo_dim_line(a => {
      DVPathLam(
        memo_dim_line(b => {
          let uvw_b = dapp_dim(assoc_uvw, b)
          dapp_dim(dpath_assoc_path3_value(space_ty, p, q, uvw_b, dlevel), a)
        }),
      )
    }),
  )
}

///|
/// Outer 2-edge walk of the `K_5` interchange facet:
/// `assoc(p, q, (u ⬝ v) ⬝ w) ⬝ (p ⬝ (q ⬝ assoc(u, v, w)))`.
pub fn dpath_k5_route_outer3_value(
  space_ty : DValue,
  p : DValue,
  q : DValue,
  u : DValue,
  v : DValue,
  w : DValue,
  dlevel : Int32,
) -> DValue {
  let x0 = dapp_dim(p, DZero)
  let x5 = dapp_dim(w, DOne)
  let path1_ty = DVPathTy(_ => space_ty, x0, x5)
  let sq = dpath_k5_interchange_square_value(space_ty, p, q, u, v, w, dlevel)
  let b0 : DValue = DVPathLam(a => dapp_dim(dapp_dim(sq, a), DZero))
  let r1 : DValue = DVPathLam(b => dapp_dim(dapp_dim(sq, DOne), b))
  dpath_trans_value(path1_ty, b0, r1, dlevel + 2)
}

///|
/// Inner 2-edge walk of the `K_5` interchange facet:
/// `((p ⬝ q) ⬝ assoc(u, v, w)) ⬝ assoc(p, q, u ⬝ (v ⬝ w))`.
pub fn dpath_k5_route_inner3_value(
  space_ty : DValue,
  p : DValue,
  q : DValue,
  u : DValue,
  v : DValue,
  w : DValue,
  dlevel : Int32,
) -> DValue {
  let x0 = dapp_dim(p, DZero)
  let x5 = dapp_dim(w, DOne)
  let path1_ty = DVPathTy(_ => space_ty, x0, x5)
  let sq = dpath_k5_interchange_square_value(space_ty, p, q, u, v, w, dlevel)
  let l0 : DValue = DVPathLam(b => dapp_dim(dapp_dim(sq, DZero), b))
  let t1 : DValue = DVPathLam(a => dapp_dim(dapp_dim(sq, a), DOne))
  dpath_trans_value(path1_ty, l0, t1, dlevel + 2)
}

///|
fn dpath_singleton5_transport_value(
  fam5 : (DValue, DValue, DValue, DValue, DValue) -> DValue,
  base_cell : DValue,
  p : DValue,
  q : DValue,
  u : DValue,
  v : DValue,
  w : DValue,
  dlevel : Int32,
) -> DValue {
  let c1 = transport_value(
    memo_dim_line(w1 => {
      let p1 = dpath_prefix_value(p, w1)
      let rx = dpath_refl_value(dapp_dim(p, w1))
      fam5(p1, rx, rx, rx, rx)
    }),
    base_cell,
    dlevel + 4,
  )
  let c2 = transport_value(
    memo_dim_line(w2 => {
      let q2 = dpath_prefix_value(q, w2)
      let rx = dpath_refl_value(dapp_dim(q, w2))
      fam5(p, q2, rx, rx, rx)
    }),
    c1,
    dlevel + 4,
  )
  let c3 = transport_value(
    memo_dim_line(w3 => {
      let u3 = dpath_prefix_value(u, w3)
      let rx = dpath_refl_value(dapp_dim(u, w3))
      fam5(p, q, u3, rx, rx)
    }),
    c2,
    dlevel + 4,
  )
  let c4 = transport_value(
    memo_dim_line(w4 => {
      let v4 = dpath_prefix_value(v, w4)
      let rx = dpath_refl_value(dapp_dim(v, w4))
      fam5(p, q, u, v4, rx)
    }),
    c3,
    dlevel + 4,
  )
  transport_value(
    memo_dim_line(w5 => fam5(p, q, u, v, dpath_prefix_value(w, w5))),
    c4,
    dlevel + 4,
  )
}

///|
/// Northern O(1) 4-cell filler of Stasheff's `K_5` interchange square between
/// `route_outer3` and `route_inner3` (horizontal-first diagonal filler).
pub fn dpath_k5_hemi_north4_value(
  space_ty : DValue,
  _r : DValue,
  p : DValue,
  q : DValue,
  u : DValue,
  v : DValue,
  w : DValue,
  dlevel : Int32,
) -> DValue {
  let path1_ty = DVPathTy(_ => space_ty, dapp_dim(p, DZero), dapp_dim(w, DOne))
  let sq = dpath_k5_interchange_square_value(space_ty, p, q, u, v, w, dlevel)
  dpath_square_boundary3_value(path1_ty, sq, dlevel + 2)
}

///|
/// Southern O(1) 4-cell filler of Stasheff's `K_5` interchange square between
/// `route_outer3` and `route_inner3` (inverted transposed-square filler).
pub fn dpath_k5_hemi_south4_value(
  space_ty : DValue,
  _r : DValue,
  p : DValue,
  q : DValue,
  u : DValue,
  v : DValue,
  w : DValue,
  dlevel : Int32,
) -> DValue {
  let path1_ty = DVPathTy(_ => space_ty, dapp_dim(p, DZero), dapp_dim(w, DOne))
  let sq = dpath_k5_interchange_square_value(space_ty, p, q, u, v, w, dlevel)
  let sq_tr : DValue = DVPathLam(
    memo_dim_line(b => DVPathLam(memo_dim_line(a => dapp_dim(dapp_dim(sq, a), b)))),
  )
  dpath_sym_value(dpath_square_boundary3_value(path1_ty, sq_tr, dlevel + 2))
}

///|
/// Stasheff's 5-dimensional associahedron `K_5` coherence 5-cell (`I^5 -> space_ty`):
/// for any constant-normalizing Kan space `space_ty` and any 5 composable paths
/// `(p, q, u, v, w)` based at `r`, constructs an explicit 5-cell filling the
/// 3-sphere boundary between `dpath_k5_hemi_north4_value` and
/// `dpath_k5_hemi_south4_value` by 5-stage cubical singleton contraction.
pub fn dpath_associahedron_k5_cell5_value(
  space_ty : DValue,
  r : DValue,
  p : DValue,
  q : DValue,
  u : DValue,
  v : DValue,
  w : DValue,
  dlevel : Int32,
) -> DValue {
  let rr = dpath_refl_value(r)
  let base5 = dpath_refl_value(
    dpath_k5_hemi_north4_value(space_ty, r, rr, rr, rr, rr, rr, dlevel),
  )
  dpath_singleton5_transport_value(
    (p1, q1, u1, v1, w1) => {
      let path1_ty = DVPathTy(_ => space_ty, dapp_dim(p1, DZero), dapp_dim(w1, DOne))
      let lhs = dpath_k5_lhs1_value(space_ty, p1, q1, u1, v1, w1, dlevel)
      let rhs = dpath_k5_rhs1_value(space_ty, p1, q1, u1, v1, w1, dlevel)
      let path2_ty = DVPathTy(_ => path1_ty, lhs, rhs)
      let out3 = dpath_k5_route_outer3_value(space_ty, p1, q1, u1, v1, w1, dlevel)
      let inn3 = dpath_k5_route_inner3_value(space_ty, p1, q1, u1, v1, w1, dlevel)
      let path3_ty = DVPathTy(_ => path2_ty, out3, inn3)
      DVPathTy(
        _ => path3_ty,
        dpath_k5_hemi_north4_value(space_ty, r, p1, q1, u1, v1, w1, dlevel),
        dpath_k5_hemi_south4_value(space_ty, r, p1, q1, u1, v1, w1, dlevel),
      )
    },
    base5,
    p,
    q,
    u,
    v,
    w,
    dlevel + 4,
  )
}
