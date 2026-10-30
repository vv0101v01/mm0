///|
// Computational univalence.
//
// Two levels are implemented.
//
// 1. The finite universe of `pathp_glue.mbt`: a universe path is
//    represented by its wiring equivalence, so `ua` and
//    `pathToEquiv` are inverse by wiring equality, and transport is
//    decided symbolically (never by enumerating the cube on the
//    decision path).
//
// 2. The dependent cubical AST: for a semantic type line `L`,
//    `path_to_equiv_value` builds the transport equivalence
//    (coe 0→1, coe 1→0, and round-trip paths built from fillers).
//    `ua_value` is the Glue line of an equivalence.  The computation
//    rule `uaβ` is an explicit path obtained by ungluing the
//    transport filler.  From `uaβ` we build the retraction homotopy
//    `pathToEquiv (ua e) = e` in the equivalence type, and from a
//    two-dimensional Glue square the section homotopy
//    `ua (pathToEquiv p) = p` in the universe.  Together they form
//    `univalence_equiv_value : DVEquiv (Equiv A B) (Path U A B)` in
//    the semantic domain, where equivalence conversion is the
//    kernel's (the two functions; proof components are
//    propositional, exactly as `conv_at` treats `DVEquivTy`).
//
// At the term level, `path_to_equiv_term` builds a closed
// `DMkEquiv` from a line body, with fill/coe proof terms, and
// `path_to_equiv_map_term` / `ua_map_term` are the two maps of the
// univalence equivalence as closed terms.

// ---------------------------------------------------------------------------
// Finite universe
// ---------------------------------------------------------------------------

///|
/// The equivalence underlying a finite universe path.
pub fn upath_to_equiv(p : UPath) -> Equiv {
  p.equiv
}

///|
pub fn upath_refl(ty : Ty) -> UPath {
  ua(equiv_id(ty))
}

///|
pub fn upath_sym(p : UPath) -> UPath {
  ua(equiv_inv(p.equiv))
}

///|
/// Transitivity of finite universe paths, when the middle types
/// agree.  Composition order follows `equiv_comp`: first `p`, then
/// `q`.
pub fn upath_trans(p : UPath, q : UPath) -> UPath? {
  if p.equiv.dst == q.equiv.src {
    Some(ua(equiv_comp(p.equiv, q.equiv)))
  } else {
    None
  }
}

///|
/// Transport in the finite universe along a universe path.
pub fn finite_transport(p : UPath, x : PVal) -> PVal {
  coe_upath(p, 0, 1, x)
}

///|
/// Decidable univalence in the finite universe on a repertoire of
/// equivalences: both round-trips are wiring identities and
/// transport computes in both directions.
pub fn check_finite_univalence() -> Bool {
  let es = [
    equiv_id(TyBool),
    equiv_bool_not(),
    equiv_swap(TyBool, TyUnit),
    equiv_prod(equiv_bool_not(), equiv_swap(TyBool, TyUnit)),
    equiv_comp(equiv_bool_not(), equiv_bool_not()),
  ]
  for i in 0..<es.length() {
    let e = es[i]
    let p = ua(e)
    if !equiv_wf(e) ||
      !equiv_ext_eq(upath_to_equiv(p), e) ||
      !upath_eq(ua(upath_to_equiv(p)), p) ||
      !coe_computes(p) {
      return false
    }
  }
  let sym_ok = match
    upath_trans(ua(equiv_bool_not()), upath_sym(ua(equiv_bool_not()))) {
    Some(p) => upath_eq(p, upath_refl(TyBool))
    None => false
  }
  sym_ok &&
  finite_transport(ua(equiv_bool_not()), PVBool(true)) == PVBool(false) &&
  finite_transport(ua(equiv_swap(TyBool, TyUnit)), PVPair(PVBool(true), PVUnit)) ==
  PVPair(PVUnit, PVBool(true))
}

///|
/// Collapse nested Glue endpoint representations.  A checked ua
/// line's endpoint is itself a `DVGlueEquiv` whose top branch is the
/// endpoint type; one collapse step can therefore return another
/// Glue value.  Universe-path endpoints are stored fully collapsed.
fn collapse_glue_type_value(v : DValue) -> DValue {
  let mut current = v
  for _i in 0..<16 {
    let next = glue_equiv_collapse(current)
    current = next
    match as_glue_equiv(current) {
      Some(_) => continue
      None => break
    }
  }
  current
}

// ---------------------------------------------------------------------------
// Transport equivalences of semantic type lines
// ---------------------------------------------------------------------------

///|
/// The round-trip path `coe 1→0 (coe 0→1 x) = x` in `line(0)`,
/// built from the transport filler:
/// `i ↦ coe (¬i → 0) (fill (¬i))`.
pub fn transport_roundtrip_path_value(
  line : (Dim) -> DValue,
  x : DValue,
  dlevel : Int32,
) -> DValue {
  let filler = transport_filler_value(line, x, dlevel + 1)
  DVPathLam(i => {
    let flipped = DNeg(i)
    coe_value(line, flipped, DZero, filler(flipped), dlevel + 1)
  })
}

///|
/// `pathToEquiv`: the transport equivalence of a type line.
pub fn path_to_equiv_value(
  line : (Dim) -> DValue,
  src : DValue,
  dst : DValue,
  _level : Int32,
  dlevel : Int32,
) -> DValue {
  let rev = (j : Dim) => line(DNeg(j))
  DVEquiv(
    src,
    dst,
    DVLam(x => transport_value(line, x, dlevel)),
    DVLam(y => transport_value(rev, y, dlevel)),
    DVLam(y => transport_roundtrip_path_value(rev, y, dlevel)),
    DVLam(x => transport_roundtrip_path_value(line, x, dlevel)),
  )
}

///|
/// `ua` as a semantic value (the Glue line), named for this layer.
pub fn equiv_to_universe_path_value(
  e : DValue,
  src : DValue,
  dst : DValue,
  level : Int32,
) -> DValue {
  ua_value(e, src, dst, level)
}

///|
/// Transport along `ua(e)`.
pub fn ua_transport_value(
  e : DValue,
  src : DValue,
  dst : DValue,
  level : Int32,
  x : DValue,
  dlevel : Int32,
) -> DValue {
  transport_value(ua_line_value(e, src, dst, level), x, dlevel)
}

///|
/// `uaβ`: the path in `dst` from `equivFun e x` to
/// `transport (ua e) x`, obtained by ungluing the transport filler
/// over the Glue line.
pub fn ua_beta_path_value(
  e : DValue,
  src : DValue,
  dst : DValue,
  level : Int32,
  x : DValue,
  dlevel : Int32,
) -> DValue {
  let line = ua_line_value(e, src, dst, level)
  let filler = transport_filler_value(line, x, dlevel + 1)
  DVPathLam(i => {
    match as_glue_equiv(line(i)) {
      Some(parts) => glue_equiv_base_of(parts, filler(i))
      None => filler(i)
    }
  })
}

///|
/// The backwards `uaβ`: the path in `src` from `equivInv e y` to
/// `transportBack (ua e) y`, obtained by taking the partial (src)
/// component of the reverse transport filler.
pub fn ua_beta_back_path_value(
  e : DValue,
  src : DValue,
  dst : DValue,
  level : Int32,
  y : DValue,
  dlevel : Int32,
) -> DValue {
  let line = ua_line_value(e, src, dst, level)
  let rev = (j : Dim) => line(DNeg(j))
  let filler = transport_filler_value(rev, y, dlevel + 1)
  DVPathLam(i => {
    match as_glue_equiv(rev(i)) {
      Some(parts) => {
        let partials = glue_equiv_partial_values(parts, filler(i))
        if partials.length() > 0 {
          partials[0]
        } else {
          filler(i)
        }
      }
      None => filler(i)
    }
  })
}

// ---------------------------------------------------------------------------
// The two homotopies
// ---------------------------------------------------------------------------

///|
/// Retraction homotopy `pathToEquiv (ua e) = e` in `Equiv src dst`.
/// The two functions are interpolated by the `uaβ` homotopies; the
/// section/retraction field at stage `i` is assembled by path
/// congruence, segments of those homotopies, and the original proof.
pub fn univalence_retr_path_value(
  e : DValue,
  src : DValue,
  dst : DValue,
  level : Int32,
  dlevel : Int32,
) -> DValue {
  let parts = equiv_parts(e, src, dst)
  DVPathLam(i => {
    let fwd_i : DValue = DVLam(x => {
      dapp_dim(
        dpath_sym_value(ua_beta_path_value(e, src, dst, level, x, dlevel + 1)),
        i,
      )
    })
    let bwd_i : DValue = DVLam(y => {
      dapp_dim(
        dpath_sym_value(
          ua_beta_back_path_value(e, src, dst, level, y, dlevel + 1),
        ),
        i,
      )
    })
    let sect_i : DValue = DVLam(y => {
      let back_homotopy = dpath_sym_value(
        ua_beta_back_path_value(e, src, dst, level, y, dlevel + 1),
      )
      let step1 = dpath_cong_value(
        fwd_i,
        src,
        dpath_segment_value(back_homotopy, i),
      )
      let gy = dapp_typed(parts.bwd, y, dst)
      let fwd_homotopy = dpath_sym_value(
        ua_beta_path_value(e, src, dst, level, gy, dlevel + 1),
      )
      let step2 = dpath_segment_value(fwd_homotopy, i)
      let step3 = dapp_typed(parts.sect, y, dst)
      dpath_trans_value(
        dst,
        dpath_trans_value(dst, step1, step2, dlevel + 2),
        step3,
        dlevel + 2,
      )
    })
    let retr_i : DValue = DVLam(x => {
      let fwd_homotopy = dpath_sym_value(
        ua_beta_path_value(e, src, dst, level, x, dlevel + 1),
      )
      let step1 = dpath_cong_value(
        bwd_i,
        dst,
        dpath_segment_value(fwd_homotopy, i),
      )
      let fx = dapp_typed(parts.fwd, x, src)
      let back_homotopy = dpath_sym_value(
        ua_beta_back_path_value(e, src, dst, level, fx, dlevel + 1),
      )
      let step2 = dpath_segment_value(back_homotopy, i)
      let step3 = dapp_typed(parts.retr, x, src)
      dpath_trans_value(
        src,
        dpath_trans_value(src, step1, step2, dlevel + 2),
        step3,
        dlevel + 2,
      )
    })
    DVEquiv(src, dst, fwd_i, bwd_i, sect_i, retr_i)
  })
}

///|
/// The Glue square witnessing `ua (pathToEquiv L) = L`: at `i=0` it
/// is the ua line of the transport equivalence, at `i=1` it is `L`,
/// and its `j=0`/`j=1` edges are constantly `src`/`dst`.  The
/// interior is the Glue type over `dst` with the `j=0` branch
/// `(src, pathToEquiv L)` and the `i=1 ∨ j=1` branch
/// `(L(j), segment equivalence L(j) ≃ dst)`.
pub fn univalence_sect_square_value(
  line : (Dim) -> DValue,
  src : DValue,
  dst : DValue,
  level : Int32,
  dlevel : Int32,
) -> DValue {
  let g = path_to_equiv_value(line, src, dst, level, dlevel + 1)
  DVPathLam(i => {
    DVPathLam(j => {
      if dim_is_zero(i) {
        ua_type_at(g, src, dst, level, j)
      } else if dim_is_one(i) {
        line(j)
      } else if dim_is_zero(j) {
        collapse_glue_type_value(src)
      } else if dim_is_one(j) {
        collapse_glue_type_value(dst)
      } else {
        let segment_equiv = if dim_is_one(j) {
          equiv_id_value(dst)
        } else {
          path_to_equiv_value(
            k => line(DOr(j, k)),
            line(j),
            dst,
            level,
            dlevel + 2,
          )
        }
        DVGlueEquiv(
          [
            dequiv_branch_value(face_simplify(FEq0(j)), src, g),
            dequiv_branch_value(
              face_simplify(FOr(FEq1(i), FEq1(j))),
              line(j),
              segment_equiv,
            ),
          ],
          dst,
          level,
        )
      }
    })
  })
}

///|
/// Computational univalence as a semantic equivalence value:
/// `(Equiv A B) ≃ Path (Type level) A B`.
pub fn univalence_equiv_value(
  src : DValue,
  dst : DValue,
  level : Int32,
  dlevel : Int32,
) -> DValue {
  let equiv_ty = DVEquivTy(src, dst, level)
  let path_ty = DVPathTy(_ => DVUniv(level), src, dst)
  DVEquiv(
    equiv_ty,
    path_ty,
    DVLam(e => ua_value(e, src, dst, level)),
    DVLam(p => {
      path_to_equiv_value(j => dapp_dim(p, j), src, dst, level, dlevel + 1)
    }),
    DVLam(p => {
      univalence_sect_square_value(
        j => dapp_dim(p, j),
        src,
        dst,
        level,
        dlevel + 1,
      )
    }),
    DVLam(e => univalence_retr_path_value(e, src, dst, level, dlevel + 1)),
  )
}

// ---------------------------------------------------------------------------
// Checked universe paths
// ---------------------------------------------------------------------------

///|
/// A universe path presented by a checked type line.
pub struct UniversePath {
  line : DCheckedTypeLine
  src : DValue
  dst : DValue
  level : Int32
}

///|
pub fn universe_path_of_checked_line(line : DCheckedTypeLine) -> UniversePath {
  let (src, dst) = checked_line_endpoints(line)
  UniversePath::{
    line,
    src: collapse_glue_type_value(src),
    dst: collapse_glue_type_value(dst),
    level: checked_line_level(line),
  }
}

///|
/// The checked ua line of a closed equivalence term, as a universe
/// path.
pub fn universe_path_of_ua_term_closed(equiv : DTerm) -> UniversePath? {
  match checked_ua_line(equiv, denv_empty(), denv_empty(), ddim_empty()) {
    Some(line) => Some(universe_path_of_checked_line(line))
    None => None
  }
}

///|
/// The path value in the universe.
pub fn universe_path_path_value(p : UniversePath) -> DValue {
  DVPathLam(checked_line_fn(p.line))
}

///|
/// The transport equivalence of a checked universe path.
pub fn universe_path_to_equiv_value(p : UniversePath, dlevel : Int32) -> DValue {
  path_to_equiv_value(checked_line_fn(p.line), p.src, p.dst, p.level, dlevel)
}

///|
/// The ua normal form of a universe path: `ua(pathToEquiv p)`.
pub fn universe_path_normal_form(p : UniversePath, dlevel : Int32) -> DValue {
  ua_value(universe_path_to_equiv_value(p, dlevel), p.src, p.dst, p.level)
}

///|
/// Two universe paths are univalence-equal when their endpoints and
/// transport equivalences are convertible.
pub fn universe_path_transport_conv(
  a : UniversePath,
  b : UniversePath,
  dlevel : Int32,
) -> Bool {
  conv_ty(0, dlevel, a.src, b.src) &&
  conv_ty(0, dlevel, a.dst, b.dst) &&
  conv_at(
    0,
    dlevel,
    DVEquivTy(a.src, a.dst, a.level),
    universe_path_to_equiv_value(a, dlevel),
    universe_path_to_equiv_value(b, dlevel),
  )
}

// ---------------------------------------------------------------------------
// Term-level pathToEquiv and the two univalence maps
// ---------------------------------------------------------------------------

///|
/// Build the transport equivalence of a line body as a `DMkEquiv`
/// term.  `line_body` is a type under one dimension binder
/// (`DVar(0)`), in the ambient term context; it is shifted under
/// each lambda of the equivalence.  The round-trip proofs are the
/// fill/coe composites described at the value level.
pub fn path_to_equiv_term(line_body : DTerm, src : DTerm, dst : DTerm) -> DTerm {
  let line = dterm_shift(line_body, 0, 1)
  let fwd = DLam(src, DCoe(line, DZero, DOne, DTVar(0)))
  let bwd = DLam(dst, DCoe(line, DOne, DZero, DTVar(0)))
  // sect y : Path dst (fwd (bwd y)) y =
  //   <i> coe (i→1) (coe (1→i) y)
  let sect = DLam(
    dst,
    DLamDim(DCoe(line, DVar(0), DOne, DCoe(line, DOne, DVar(0), DTVar(0)))),
  )
  // retr x : Path src (bwd (fwd x)) x =
  //   <i> coe (¬i→0) (coe (0→¬i) x)
  let retr = DLam(
    src,
    DLamDim(
      DCoe(
        line,
        DNeg(DVar(0)),
        DZero,
        DCoe(line, DZero, DNeg(DVar(0)), DTVar(0)),
      ),
    ),
  )
  DMkEquiv(src, dst, fwd, bwd, sect, retr)
}

///|
/// The forward univalence map as a closed term:
/// `Equiv A B -> Path (Type 0) A B`.
pub fn ua_map_term(src : DTerm, dst : DTerm) -> DTerm {
  DLam(DEquivTy(src, dst), DUa(DTVar(0)))
}

///|
/// The backward univalence map as a closed term:
/// `Path (Type 0) A B -> Equiv A B`, by applying
/// `path_to_equiv_term` to the line `j ↦ p @ j` under the binder.
pub fn path_to_equiv_map_term(src : DTerm, dst : DTerm) -> DTerm {
  DLam(
    DPath(DUniv(0), src, dst),
    path_to_equiv_term(DAppDim(DTVar(0), DVar(0)), src, dst),
  )
}

// ---------------------------------------------------------------------------
// Behavioural laws
// ---------------------------------------------------------------------------

///|
fn check_univalence_semantic() -> Bool {
  let e = deval_dim(bool_not_equiv_term(), denv_empty(), ddim_empty())
  let equiv_ty = DVEquivTy(DVBoolTy, DVBoolTy, 0)
  let line = ua_line_value(e, DVBoolTy, DVBoolTy, 0)
  let back = path_to_equiv_value(line, DVBoolTy, DVBoolTy, 0, 0)
  if !conv_at(0, 0, equiv_ty, back, e) {
    return false
  }
  let beta = ua_beta_path_value(e, DVBoolTy, DVBoolTy, 0, DVBool(true), 0)
  let beta_back = ua_beta_back_path_value(
    e,
    DVBoolTy,
    DVBoolTy,
    0,
    DVBool(false),
    0,
  )
  if !cubical_bool_is(dapp_dim(beta, DZero), false) ||
    !cubical_bool_is(dapp_dim(beta, DOne), false) ||
    !cubical_bool_is(dapp_dim(beta_back, DZero), true) ||
    !cubical_bool_is(dapp_dim(beta_back, DOne), true) {
    return false
  }
  let retr = univalence_retr_path_value(e, DVBoolTy, DVBoolTy, 0, 0)
  if !conv_at(0, 0, equiv_ty, dapp_dim(retr, DZero), back) ||
    !conv_at(0, 0, equiv_ty, dapp_dim(retr, DOne), e) {
    return false
  }
  // The sect square over the constant Bool line and over ua(not).
  let lines : Array[(Dim) -> DValue] = [_ => DVBoolTy, line]
  for idx in 0..<lines.length() {
    let l = lines[idx]
    let g = path_to_equiv_value(l, DVBoolTy, DVBoolTy, 0, 0)
    let square = univalence_sect_square_value(l, DVBoolTy, DVBoolTy, 0, 0)
    let at_zero = dapp_dim(square, DZero)
    let at_one = dapp_dim(square, DOne)
    if !conv_ty(
        0,
        1,
        dapp_dim(at_zero, DVar(0)),
        ua_type_at(g, DVBoolTy, DVBoolTy, 0, DVar(0)),
      ) ||
      !conv_ty(0, 1, dapp_dim(at_one, DVar(0)), l(DVar(0))) ||
      !conv_ty(0, 1, dapp_dim(dapp_dim(square, DVar(0)), DZero), DVBoolTy) ||
      !conv_ty(0, 1, dapp_dim(dapp_dim(square, DVar(0)), DOne), DVBoolTy) {
      return false
    }
  }
  let univ = univalence_equiv_value(DVBoolTy, DVBoolTy, 0, 0)
  let univ_parts = equiv_parts(
    univ,
    equiv_ty,
    DVPathTy(_ => DVUniv(0), DVBoolTy, DVBoolTy),
  )
  let roundtrip = dapp_typed(
    univ_parts.bwd,
    dapp_typed(univ_parts.fwd, e, equiv_ty),
    DVPathTy(_ => DVUniv(0), DVBoolTy, DVBoolTy),
  )
  conv_at(0, 0, equiv_ty, roundtrip, e)
}

///|
fn check_univalence_terms() -> Bool {
  let ua_line = DAppDim(DUa(bool_not_equiv_term()), DVar(0))
  let from_ua = path_to_equiv_term(ua_line, DBoolTy, DBoolTy)
  if !dep_check_closed(from_ua, DEquivTy(DBoolTy, DBoolTy)) {
    return false
  }
  if dep_nf_closed(DApp(DEquivFwd(from_ua), DBoolLit(true)), DBoolTy) !=
    Some(DBoolLit(false)) ||
    dep_nf_closed(DApp(DEquivBwd(from_ua), DBoolLit(false)), DBoolTy) !=
    Some(DBoolLit(true)) {
    return false
  }
  let refl_equiv = path_to_equiv_term(DBoolTy, DBoolTy, DBoolTy)
  if !dep_check_closed(refl_equiv, DEquivTy(DBoolTy, DBoolTy)) ||
    dep_nf_closed(DApp(DEquivFwd(refl_equiv), DBoolLit(true)), DBoolTy) !=
    Some(DBoolLit(true)) {
    return false
  }
  let ua_map_ty = DPi(
    DEquivTy(DBoolTy, DBoolTy),
    DPath(DUniv(0), DBoolTy, DBoolTy),
  )
  let back_map_ty = DPi(
    DPath(DUniv(0), DBoolTy, DBoolTy),
    DEquivTy(DBoolTy, DBoolTy),
  )
  dep_check_closed(ua_map_term(DBoolTy, DBoolTy), ua_map_ty) &&
  dep_check_closed(path_to_equiv_map_term(DBoolTy, DBoolTy), back_map_ty)
}

///|
fn check_universe_paths() -> Bool {
  match universe_path_of_ua_term_closed(bool_not_equiv_term()) {
    Some(p) => {
      let e = deval_dim(bool_not_equiv_term(), denv_empty(), ddim_empty())
      conv_at(
        0,
        0,
        DVEquivTy(DVBoolTy, DVBoolTy, 0),
        universe_path_to_equiv_value(p, 0),
        e,
      ) &&
      universe_path_transport_conv(p, p, 0) &&
      conv_ty(0, 0, dapp_dim(universe_path_normal_form(p, 0), DZero), DVBoolTy)
    }
    None => false
  }
}

///|
pub fn check_univalence() -> Bool {
  check_finite_univalence() &&
  check_univalence_semantic() &&
  check_univalence_terms() &&
  check_universe_paths()
}

///|
/// General composition of bidirectional equivalences `(e1 : Equiv A B)` and
/// `(e2 : Equiv B C)` into `Equiv A C`, synthesizing the composite section
/// `ap f2 (sect_1 (g2 z)) ⬝ sect_2 z` and composite retraction
/// `ap g1 (retr_2 (f1 x)) ⬝ retr_1 x` uniformly over concrete or open/neutral
/// equivalences `e1, e2`.
pub fn equiv_compose_value(
  e1 : DValue,
  e2 : DValue,
  a_ty : DValue,
  b_ty : DValue,
  c_ty : DValue,
  dlevel : Int32,
) -> DValue {
  let f1 = equiv_fwd_value(e1, a_ty, b_ty)
  let g1 = equiv_bwd_value(e1, a_ty, b_ty)
  let s1 = equiv_sect_value(e1, a_ty, b_ty)
  let r1 = equiv_retr_value(e1, a_ty, b_ty)
  let f2 = equiv_fwd_value(e2, b_ty, c_ty)
  let g2 = equiv_bwd_value(e2, b_ty, c_ty)
  let s2 = equiv_sect_value(e2, b_ty, c_ty)
  let r2 = equiv_retr_value(e2, b_ty, c_ty)
  let fwd = DVLam(x => dapp_typed(f2, dapp_typed(f1, x, a_ty), b_ty))
  let bwd = DVLam(z => dapp_typed(g1, dapp_typed(g2, z, c_ty), b_ty))
  let sect = DVLam(z => {
    let g2z = dapp_typed(g2, z, c_ty)
    let step1 = dpath_cong_value(f2, b_ty, dapp_typed(s1, g2z, b_ty))
    let step2 = dapp_typed(s2, z, c_ty)
    dpath_trans_value(c_ty, step1, step2, dlevel)
  })
  let retr = DVLam(x => {
    let f1x = dapp_typed(f1, x, a_ty)
    let step1 = dpath_cong_value(g1, b_ty, dapp_typed(r2, f1x, b_ty))
    let step2 = dapp_typed(r1, x, a_ty)
    dpath_trans_value(a_ty, step1, step2, dlevel)
  })
  equiv_make_value(a_ty, c_ty, fwd, bwd, sect, retr)
}

///|
/// Kernel-checked bidirectional equivalence certificate: verifies `e` for
/// general bidirectional bijectivity (split surjection `sect` + split
/// injection `retr`) on fresh open reflected variables `x : src` and
/// `y : dst` in ambient context `(ctx, env, denv)`.
pub fn equiv_bidirectional_certified_in(
  ctx : DEnv,
  env : DEnv,
  denv : DDimEnv,
  e : DValue,
) -> Bool {
  let level = denv_len(ctx)
  let dlevel = ddim_len(denv)
  match force_value(e) {
    DVEquiv(src, dst, fwd, bwd, sect, retr) => {
      let x = reflect_var(level, src)
      let y = reflect_var(level, dst)
      let ctx_x = denv_cons(src, ctx)
      let env_x = denv_cons(x, env)
      let ctx_y = denv_cons(dst, ctx)
      let env_y = denv_cons(y, env)

      let fx = dapp_typed(fwd, x, src)
      let gy = dapp_typed(bwd, y, dst)
      let fx_term = quote_at(level + 1, dlevel, dst, fx)
      let gy_term = quote_at(level + 1, dlevel, src, gy)
      match
        (
          d_check(fx_term, dst, ctx_x, env_x, denv),
          d_check(gy_term, src, ctx_y, env_y, denv),
        ) {
        (Some(_), Some(_)) => ()
        _ => return false
      }

      let sy = dapp_typed(sect, y, dst)
      let f_gy = dapp_typed(fwd, gy, src)
      if !conv_at(level + 1, dlevel, dst, dapp_dim(sy, DZero), f_gy) ||
        !conv_at(level + 1, dlevel, dst, dapp_dim(sy, DOne), y) {
        return false
      }
      let fresh_d = DVar(dlevel)
      let denv_d = ddim_cons(fresh_d, denv)
      let sy_i_term = quote_at(level + 1, dlevel + 1, dst, dapp_dim(sy, fresh_d))
      match d_check(sy_i_term, dst, ctx_y, env_y, denv_d) {
        Some(_) => ()
        None => return false
      }

      let rx = dapp_typed(retr, x, src)
      let g_fx = dapp_typed(bwd, fx, dst)
      if !conv_at(level + 1, dlevel, src, dapp_dim(rx, DZero), g_fx) ||
        !conv_at(level + 1, dlevel, src, dapp_dim(rx, DOne), x) {
        return false
      }
      let rx_i_term = quote_at(level + 1, dlevel + 1, src, dapp_dim(rx, fresh_d))
      match d_check(rx_i_term, src, ctx_x, env_x, denv_d) {
        Some(_) => true
        None => false
      }
    }
    _ => false
  }
}

///|
pub fn equiv_bidirectional_certified(e : DValue) -> Bool {
  equiv_bidirectional_certified_in(denv_empty(), denv_empty(), ddim_empty(), e)
}

