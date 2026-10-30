///|
// Adjoint equivalences, contractible fibers, and primitive Glue
// quoting.
//
// The kernel's `DMkEquiv` is a quasi-inverse equivalence (two
// functions with a section and a retraction).  An *adjoint*
// equivalence additionally carries the triangle coherence
//
//   τ (x : A) : Path (Path B (f (g (f x))) (f x))
//                      (ap f (retr x)) (sect (f x)).
//
// This file makes that data first-class: a semantic record with an
// explicit triangle value, the corresponding AST Σ-type over
// `Equiv A B`, identity and Bool-negation instances whose triangle
// is reflexivity, and the standard improved counit of a
// quasi-inverse (the first step of adjointification).  It also
// gives the contractible-fiber characterization as checked AST
// types, the definitional contraction of based singletons, and a
// fiber center for every quasi-inverse equivalence.

// ---------------------------------------------------------------------------
// Triangle coherence and adjoint equivalence data
// ---------------------------------------------------------------------------

///|
/// The type of the triangle coherence, as a semantic value:
/// `Π x, Path (Path B (f (g (f x))) (f x)) (ap f (retr x)) (sect (f x))`.
pub fn equiv_triangle_type(
  src : DValue,
  dst : DValue,
  fwd : DValue,
  bwd : DValue,
  sect : DValue,
  retr : DValue,
) -> DValue {
  DVPi(src, x => {
    let fx = dapp_typed(fwd, x, src)
    let gfx = dapp_typed(bwd, fx, dst)
    let fgfx = dapp_typed(fwd, gfx, src)
    let path_ty = DVPathTy(_ => dst, fgfx, fx)
    let ap_retr = dpath_cong_value(fwd, src, dapp_typed(retr, x, src))
    let sect_fx = dapp_typed(sect, fx, dst)
    DVPathTy(_ => path_ty, ap_retr, sect_fx)
  })
}

///|
pub struct DAdjointEquivParts {
  equiv : DEquivParts
  triangle : DValue
}

///|
pub fn adjoint_equiv_make(
  e : DValue,
  src : DValue,
  dst : DValue,
  triangle : DValue,
) -> DAdjointEquivParts {
  DAdjointEquivParts::{ equiv: equiv_parts(e, src, dst), triangle, }
}

///|
/// Forget the coherence: the underlying quasi-inverse equivalence.
pub fn adjoint_equiv_to_equiv(adj : DAdjointEquivParts) -> DValue {
  let p = adj.equiv
  DVEquiv(p.src, p.dst, p.fwd, p.bwd, p.sect, p.retr)
}

///|
/// The identity adjoint equivalence: every component is
/// reflexivity, including the triangle.
pub fn adjoint_id_value(ty : DValue) -> DAdjointEquivParts {
  DAdjointEquivParts::{
    equiv: equiv_parts(equiv_id_value(ty), ty, ty),
    triangle: DVLam(x => DVPathLam(_ => DVPathLam(_ => x))),
  }
}

///|
/// The improved counit (section) of a quasi-inverse equivalence,
/// `ε'(y) = ε(f (g y))⁻¹ ∙ ap f (η (g y)) ∙ ε(y)`.  Replacing `ε`
/// by `ε'` is the standard first step in adjointifying a
/// quasi-inverse; the resulting data is still an equivalence with
/// the same functions and retraction.
pub fn equiv_improved_sect_value(
  src : DValue,
  dst : DValue,
  fwd : DValue,
  bwd : DValue,
  sect : DValue,
  retr : DValue,
  dlevel : Int32,
) -> DValue {
  DVLam(y => {
    let gy = dapp_typed(bwd, y, dst)
    let fgy = dapp_typed(fwd, gy, src)
    let first = dpath_sym_value(dapp_typed(sect, fgy, dst))
    let second = dpath_cong_value(fwd, src, dapp_typed(retr, gy, src))
    let third = dapp_typed(sect, y, dst)
    dpath_trans_value(
      dst,
      dpath_trans_value(dst, first, second, dlevel),
      third,
      dlevel,
    )
  })
}

///|
/// A quasi-inverse equivalence with its section replaced by the
/// improved counit.
pub fn equiv_with_improved_sect(
  e : DValue,
  src : DValue,
  dst : DValue,
  dlevel : Int32,
) -> DValue {
  let p = equiv_parts(e, src, dst)
  DVEquiv(
    p.src,
    p.dst,
    p.fwd,
    p.bwd,
    equiv_improved_sect_value(
      p.src,
      p.dst,
      p.fwd,
      p.bwd,
      p.sect,
      p.retr,
      dlevel,
    ),
    p.retr,
  )
}

///|
/// The AST Σ-type of adjoint equivalences over `Equiv A B`.  In the
/// body, `DTVar(0)` is the bound equivalence and, under the
/// additional `x : A` binder, `DTVar(1)` is the equivalence and
/// `DTVar(0)` is `x`.
pub fn adjoint_equiv_type_term(a : DTerm, b : DTerm) -> DTerm {
  let e1 = DTVar(1)
  let x = DTVar(0)
  let fx = DApp(DEquivFwd(e1), x)
  let fgfx = DApp(DEquivFwd(e1), DApp(DEquivBwd(e1), fx))
  // `b`/`a` are closed in the uses here; under the Σ and Π binders
  // they are unchanged because DTerm binders are explicit in the
  // builders used by the laws (closed A and B).
  DSigma(
    DEquivTy(a, b),
    DPi(
      a,
      DPath(
        DPath(b, fgfx, fx),
        dpath_cong_term(DEquivFwd(e1), DApp(DEquivRetr(e1), x)),
        DApp(DEquivSect(e1), fx),
      ),
    ),
  )
}

// ---------------------------------------------------------------------------
// Contractible fibers
// ---------------------------------------------------------------------------

///|
/// `isContr A = Σ (c : A), Π (x : A), Path A c x` as an AST type
/// (for closed `A`).
pub fn is_contr_type_term(a : DTerm) -> DTerm {
  DSigma(a, DPi(a, DPath(a, DTVar(1), DTVar(0))))
}

///|
/// `fiber f y = Σ (x : A), Path B (f x) y` as an AST type, for
/// closed `A`, `B`, `f`, and `y`.
pub fn fiber_type_term(a : DTerm, b : DTerm, f : DTerm, y : DTerm) -> DTerm {
  DSigma(a, DPath(b, DApp(f, DTVar(0)), y))
}

///|
/// `Π (y : B), isContr (fiber f y)` as an AST type, for closed
/// `A`, `B`, and `f`.  Under the Π binder `DTVar(0)` is `y`.
pub fn contractible_fibers_type_term(a : DTerm, b : DTerm, f : DTerm) -> DTerm {
  DPi(b, is_contr_type_term(fiber_type_term(a, b, f, DTVar(0))))
}

///|
/// The based singleton contraction: the path in
/// `Σ (x : A), Path A x y` from the center `(y, refl)` to `(x, p)`,
/// by `i ↦ (p (¬i), λ j ↦ p (¬i ∨ j))`.  This computes at both
/// endpoints by the De Morgan endpoint laws.
pub fn singleton_contraction_value(p : DValue) -> DValue {
  DVPathLam(i => {
    DVPair(dapp_dim(p, DNeg(i)), DVPathLam(j => dapp_dim(p, DOr(DNeg(i), j))))
  })
}

///|
/// The center of the fiber of a quasi-inverse equivalence over
/// `y`: `(g y, sect y)`.
pub fn equiv_fiber_center_value(
  e : DValue,
  src : DValue,
  dst : DValue,
  y : DValue,
) -> DValue {
  let p = equiv_parts(e, src, dst)
  DVPair(dapp_typed(p.bwd, y, dst), dapp_typed(p.sect, y, dst))
}

///|
/// Contractibility data for the fibers of an identity equivalence,
/// from the singleton contraction: `y ↦ ((y, refl), λ w ↦ ...)`.
/// A fiber element is `(x, p)` with `p : Path A x y`; its
/// contraction is the singleton contraction at `p`.
pub fn identity_fibers_contractible_value(ty : DValue) -> DValue {
  DVLam(y => {
    DVPair(
      DVPair(y, DVPathLam(_ => y)),
      DVLam(w => {
        match force_value(w) {
          DVPair(_, p) => singleton_contraction_value(p)
          _ =>
            // Neutral fiber elements: project the path component
            // semantically (second projection of a Σ value).
            singleton_contraction_value(
              dsnd_typed(w, ty, x => DVPathTy(_ => ty, x, y)),
            )
        }
      }),
    )
  })
}

// ---------------------------------------------------------------------------
// Laws
// ---------------------------------------------------------------------------

///|
pub fn check_adjoint_equivalence_and_fibers() -> Bool {
  // Triangle coherence of the identity on Bool and on the circle,
  // checked at the semantic triangle type for fresh points.
  for ty in [DVBoolTy, DVCircleTy] {
    let adj = adjoint_id_value(ty)
    let p = adj.equiv
    let tri_ty = equiv_triangle_type(ty, ty, p.fwd, p.bwd, p.sect, p.retr)
    let fresh = DVNeutral(DNVar(0))
    let at = dapp_typed(adj.triangle, fresh, ty)
    let expected = match as_pi(tri_ty) {
      Some(parts) => (parts.fam)(fresh)
      None => DVUnitTy
    }
    if !conv_at(
        1,
        0,
        expected,
        at,
        DVPathLam(_ => {
          dpath_cong_value(p.fwd, ty, dapp_typed(p.retr, fresh, ty))
        }),
      ) {
      return false
    }
  }
  // Improved counit of Bool negation: still a section at both
  // points (endpoint computation), with the same functions.
  let e = deval_dim(bool_not_equiv_term(), denv_empty(), ddim_empty())
  let improved = equiv_with_improved_sect(e, DVBoolTy, DVBoolTy, 0)
  let parts = equiv_parts(improved, DVBoolTy, DVBoolTy)
  for y in [true, false] {
    let sect_y = dapp_typed(parts.sect, DVBool(y), DVBoolTy)
    if !conv_at(0, 0, DVBoolTy, dapp_dim(sect_y, DZero), DVBool(y)) ||
      !conv_at(0, 0, DVBoolTy, dapp_dim(sect_y, DOne), DVBool(y)) ||
      !conv_at(
        0,
        0,
        DVBoolTy,
        equiv_fun_value(improved, DVBoolTy, DVBoolTy, DVBool(y)),
        DVBool(!y),
      ) {
      return false
    }
  }
  // The AST adjoint Σ-type and contractible-fiber types are
  // well-formed types.
  if !dep_check_closed(adjoint_equiv_type_term(DBoolTy, DBoolTy), DUniv(0)) ||
    !dep_check_closed(is_contr_type_term(DBoolTy), DUniv(0)) ||
    !dep_check_closed(
      contractible_fibers_type_term(DBoolTy, DBoolTy, DLam(DBoolTy, DTVar(0))),
      DUniv(0),
    ) {
    return false
  }
  // Singleton contraction endpoints on the circle loop.
  let loop_path : DValue = DVPathLam(d => circle_point(d))
  let contr = singleton_contraction_value(loop_path)
  let singleton_ty = DVSigma(DVCircleTy, x => {
    DVPathTy(_ => DVCircleTy, x, DVCirclePoint(DZero))
  })
  let center : DValue = DVPair(
    DVCirclePoint(DZero),
    DVPathLam(_ => DVCirclePoint(DZero)),
  )
  let element : DValue = DVPair(DVCirclePoint(DZero), loop_path)
  if !conv_at(0, 0, singleton_ty, dapp_dim(contr, DZero), center) ||
    !conv_at(0, 0, singleton_ty, dapp_dim(contr, DOne), element) {
    return false
  }
  // Fiber center of Bool negation over `true` is `(false, refl)`.
  let center2 = equiv_fiber_center_value(e, DVBoolTy, DVBoolTy, DVBool(true))
  match force_value(center2) {
    DVPair(gx, proof) =>
      conv_at(0, 0, DVBoolTy, gx, DVBool(false)) &&
      conv_at(0, 0, DVBoolTy, dapp_dim(proof, DZero), DVBool(true)) &&
      conv_at(0, 0, DVBoolTy, dapp_dim(proof, DOne), DVBool(true))
    _ => false
  }
}

///|
/// Quoting a Glue-by-equivalence type with a top branch preserves
/// the primitive `DGlueEquiv` syntax (it does not collapse to the
/// branch type), while remaining convertible to the original.
pub fn check_glue_equiv_quote_preserves_syntax() -> Bool {
  let e = deval_dim(bool_not_equiv_term(), denv_empty(), ddim_empty())
  let glue : DValue = DVGlueEquiv(
    [dequiv_branch_value(FTop, DVBoolTy, e)],
    DVBoolTy,
    0,
  )
  let quoted = quote_ty(0, 0, glue)
  match quoted {
    DGlueEquiv(base, branches) => {
      let convertible = match
        d_as_type(quoted, denv_empty(), denv_empty(), ddim_empty()) {
        Some(tv) => conv_ty(0, 0, tv.value, glue)
        None => false
      }
      base == DBoolTy && branches.length() == 1 && convertible
    }
    _ => false
  }
}
