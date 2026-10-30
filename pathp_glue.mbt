///|
// ua, coe, PathP, Glue and J in a finite universe.
//
// The universe here consists of finite types built from Bool and Unit by
// products.  Finiteness is a feature: equivalences can be verified on
// *all* elements, so the theorems below are decided, not sampled.
//
//   Iso A B  --iso_to_equiv-->  A ≃ B  --ua-->  Path U A B
// and coe along that path computes:
//   coe^{ua e} 0 1  = equivFun e,   coe^{p} r r = id,
// by the definition of `coe_upath` (compare the term-level version in
// nbe.mbt, where the same equations hold definitionally by NbE).
// In this set-level finite model a bi-invertible map is an equivalence,
// so iso_to_equiv needs no extra coherence data.
//
// PathP over a ua-line, products of paths and the exchange law
//   swap ∘ (e₁ × e₂) = (e₂ × e₁) ∘ swap
// are checked on all elements; Glue is implemented with its formation,
// introduction, unglue and face-restriction rules and the soundness
// equation  φ ⊢ equivFun(partial) = unglue.  J is implemented for the
// discrete fragment via coe over a constant line: J(refl) computes by
// the same code path as J(p) for any well-formed (hence constant) p.

///|
pub enum Ty {
  TyBool
  TyUnit
  TyProd(Ty, Ty)
} derive(Debug, Eq)

///|
/// Cross-package constructor for the Bool finite type.  The enum itself
/// stays non-`pub(all)`; these three functions are the deliberate
/// construction boundary for integration packages such as `bridge/`.
pub fn ty_bool() -> Ty {
  TyBool
}

///|
/// Cross-package constructor for the Unit finite type.
pub fn ty_unit() -> Ty {
  TyUnit
}

///|
/// Cross-package constructor for finite product types.
pub fn ty_prod(a : Ty, b : Ty) -> Ty {
  TyProd(a, b)
}

///|
pub extend PVal with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend PVal with Eq::{not_equal, equal}

///|
pub extend Ty with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend Ty with Eq::{not_equal, equal}

///|
pub enum PVal {
  PVUnit
  PVBool(Bool)
  PVPair(PVal, PVal)
} derive(Debug, Eq)

///|
/// All elements of a finite type.
pub fn elems_of(ty : Ty) -> Array[PVal] {
  match ty {
    TyBool => [PVBool(false), PVBool(true)]
    TyUnit => [PVUnit]
    TyProd(a, b) => {
      let out : Array[PVal] = []
      let xs = elems_of(a)
      let ys = elems_of(b)
      for i in 0..<xs.length() {
        for j in 0..<ys.length() {
          out.push(PVPair(xs[i], ys[j]))
        }
      }
      out
    }
  }
}

///|
pub fn in_ty(v : PVal, ty : Ty) -> Bool {
  match (v, ty) {
    (PVUnit, TyUnit) => true
    (PVBool(_), TyBool) => true
    (PVPair(a, b), TyProd(x, y)) => in_ty(a, x) && in_ty(b, y)
    _ => false
  }
}

///|
pub fn pval_fst(v : PVal) -> PVal {
  match v {
    PVPair(a, _) => a
    _ => PVUnit
  }
}

///|
pub fn pval_snd(v : PVal) -> PVal {
  match v {
    PVPair(_, b) => b
    _ => PVUnit
  }
}

///|
pub fn pval_not(v : PVal) -> PVal {
  match v {
    PVBool(b) => PVBool(!b)
    other => other
  }
}

///|
pub fn pval_swap(v : PVal) -> PVal {
  match v {
    PVPair(a, b) => PVPair(b, a)
    other => other
  }
}

// ---------------------------------------------------------------------------
// Iso, Equiv, ua
// ---------------------------------------------------------------------------

///|
pub struct Iso {
  src : Ty
  dst : Ty
  to_fn : (PVal) -> PVal
  from_fn : (PVal) -> PVal
  wiring : Wiring // canonical form; to_fn/from_fn are its evaluation
}

///|
pub struct Equiv {
  src : Ty
  dst : Ty
  fwd : (PVal) -> PVal
  bwd : (PVal) -> PVal
  wiring : Wiring // canonical form; fwd/bwd are its evaluation
}

///|
/// A path in the universe obtained from an equivalence (ua).
pub struct UPath {
  equiv : Equiv
}

///|
pub fn iso_of_wiring(w : Wiring) -> Iso {
  let winv = wiring_inv(w)
  Iso::{
    src: w.src,
    dst: w.dst,
    to_fn: v => wiring_apply(w, v),
    from_fn: v => wiring_apply(winv, v),
    wiring: w,
  }
}

///|
pub fn equiv_of_wiring(w : Wiring) -> Equiv {
  let winv = wiring_inv(w)
  Equiv::{
    src: w.src,
    dst: w.dst,
    fwd: v => wiring_apply(w, v),
    bwd: v => wiring_apply(winv, v),
    wiring: w,
  }
}

///|
pub fn iso_swap(a : Ty, b : Ty) -> Iso {
  iso_of_wiring(wiring_swap(a, b))
}

///|
pub fn iso_bool_not() -> Iso {
  iso_of_wiring(wiring_not())
}

///|
/// Isomorphism laws by enumerating all elements: the *oracle*, kept for
/// differential testing of the symbolic decision below.
pub fn iso_wf_extensional(i : Iso) -> Bool {
  let xs = elems_of(i.src)
  for k in 0..<xs.length() {
    let x = xs[k]
    if !in_ty((i.to_fn)(x), i.dst) || (i.from_fn)((i.to_fn)(x)) != x {
      return false
    }
  }
  let ys = elems_of(i.dst)
  for k in 0..<ys.length() {
    let y = ys[k]
    if !in_ty((i.from_fn)(y), i.src) || (i.to_fn)((i.from_fn)(y)) != y {
      return false
    }
  }
  true
}

///|
/// Isomorphism laws, decided symbolically: the wiring is a signed
/// permutation between the stated types.
pub fn iso_wf(i : Iso) -> Bool {
  i.wiring.src == i.src && i.wiring.dst == i.dst && wiring_wf(i.wiring)
}

///|
/// In this finite set-level universe, a bi-invertible map is an equivalence.
pub fn iso_to_equiv(i : Iso) -> Equiv {
  Equiv::{
    src: i.src,
    dst: i.dst,
    fwd: i.to_fn,
    bwd: i.from_fn,
    wiring: i.wiring,
  }
}

///|
pub fn equiv_id(ty : Ty) -> Equiv {
  equiv_of_wiring(wiring_id(ty))
}

///|
pub fn equiv_swap(a : Ty, b : Ty) -> Equiv {
  iso_to_equiv(iso_swap(a, b))
}

///|
pub fn equiv_bool_not() -> Equiv {
  iso_to_equiv(iso_bool_not())
}

///|
/// Product of equivalences: (e₁ × e₂) : A×C ≃ B×D.
pub fn equiv_prod(e1 : Equiv, e2 : Equiv) -> Equiv {
  equiv_of_wiring(wiring_prod(e1.wiring, e2.wiring))
}

///|
pub fn equiv_comp(e1 : Equiv, e2 : Equiv) -> Equiv {
  equiv_of_wiring(wiring_comp(e1.wiring, e2.wiring))
}

///|
pub fn equiv_inv(e : Equiv) -> Equiv {
  equiv_of_wiring(wiring_inv(e.wiring))
}

///|
/// Equivalence laws, decided symbolically on the wiring normal form.
pub fn equiv_wf(e : Equiv) -> Bool {
  e.wiring.src == e.src && e.wiring.dst == e.dst && wiring_wf(e.wiring)
}

///|
/// Equivalence laws by enumeration (oracle for differential testing).
pub fn equiv_wf_extensional(e : Equiv) -> Bool {
  iso_wf_extensional(Iso::{
    src: e.src,
    dst: e.dst,
    to_fn: e.fwd,
    from_fn: e.bwd,
    wiring: e.wiring,
  })
}

///|
/// Extensional equality by enumeration (oracle for differential testing).
pub fn equiv_ext_eq_oracle(e1 : Equiv, e2 : Equiv) -> Bool {
  if e1.src != e2.src || e1.dst != e2.dst {
    return false
  }
  let xs = elems_of(e1.src)
  for k in 0..<xs.length() {
    if (e1.fwd)(xs[k]) != (e2.fwd)(xs[k]) {
      return false
    }
  }
  let ys = elems_of(e1.dst)
  for k in 0..<ys.length() {
    if (e1.bwd)(ys[k]) != (e2.bwd)(ys[k]) {
      return false
    }
  }
  true
}

///|
/// Equality of equivalences, decided by canonical-form (wiring) equality.
/// (For this fragment it coincides with extensional equality, as the
/// oracle-based differential tests confirm — hence the name is kept.)
pub fn equiv_ext_eq(e1 : Equiv, e2 : Equiv) -> Bool {
  wiring_eq(e1.wiring, e2.wiring)
}

///|
/// ua: from an equivalence, a path (equality) of types.  Isomorphism *is*
/// equality in the universe, with computational transport below.
pub fn ua(e : Equiv) -> UPath {
  UPath::{ equiv: e, }
}

///|
pub fn iso_to_path(i : Iso) -> UPath {
  ua(iso_to_equiv(i))
}

///|
pub fn upath_left(p : UPath) -> Ty {
  p.equiv.src
}

///|
pub fn upath_right(p : UPath) -> Ty {
  p.equiv.dst
}

///|
/// coe along a universe path between endpoints r, s ∈ {0,1}.
/// The computation rules are the definition:
///   coe r r x = x,  coe 0 1 x = equivFun e x,  coe 1 0 y = equivInv e y.
pub fn coe_upath(p : UPath, r : Int32, s : Int32, x : PVal) -> PVal {
  if r == s {
    x
  } else if r == 0 {
    (p.equiv.fwd)(x)
  } else {
    (p.equiv.bwd)(x)
  }
}

///|
/// Transport along ua(e) is equivFun e (by definition of coe_upath),
/// transport in the identity direction is the identity, and forth-and-back
/// transport is the identity: decided symbolically as wiring identities.
pub fn coe_computes(p : UPath) -> Bool {
  // Symbolic form of the statement: coe 0 1 is equivFun *by the definition
  // of coe_upath*, coe r r is id by the same definition, and the
  // forth-and-back round-trip is the wiring identity w ; w⁻¹ = id.
  let w = p.equiv.wiring
  wiring_wf(w) &&
  wiring_eq(wiring_comp(w, wiring_inv(w)), wiring_id(p.equiv.src)) &&
  wiring_eq(wiring_comp(wiring_inv(w), w), wiring_id(p.equiv.dst))
}

///|
/// Paths in this universe are equal when their transports agree everywhere.
pub fn upath_eq(p : UPath, q : UPath) -> Bool {
  equiv_ext_eq(p.equiv, q.equiv)
}

///|
/// PathP / ua product-exchange (積交換) square:
///   swap ∘ (e₁ × e₂)  =  (e₂ × e₁) ∘ swap
/// as equivalences, hence their ua-paths are equal.
pub fn swap_naturality(e1 : Equiv, e2 : Equiv) -> Bool {
  let lhs = equiv_comp(equiv_prod(e1, e2), equiv_swap(e1.dst, e2.dst))
  let rhs = equiv_comp(equiv_swap(e1.src, e2.src), equiv_prod(e2, e1))
  equiv_wf(lhs) && equiv_wf(rhs) && upath_eq(ua(lhs), ua(rhs))
}

// ---------------------------------------------------------------------------
// PathP over a universe line, and discrete paths with J
// ---------------------------------------------------------------------------

///|
/// An element of PathP over a ua-line: endpoints at the two types and a
/// pointwise representation (in this discrete model, at0 before 1, at1 at 1
/// for canonical elements; arbitrary representatives are judged by their
/// endpoint behaviour).
pub struct PathPVal {
  line : UPath
  at0 : PVal
  at1 : PVal
  point : (Double) -> PVal
}

///|
fn pathp_point_formula(a : PVal, b : PVal, t : Double) -> PVal {
  if t >= 1.0 {
    b
  } else {
    a
  }
}

///|
/// The canonical PathP element over ua(e) out of x: its far endpoint is
/// coe (transport) of x.
pub fn pathp_canonical(line : UPath, x : PVal) -> PathPVal {
  let y = coe_upath(line, 0, 1, x)
  PathPVal::{ line, at0: x, at1: y, point: t => pathp_point_formula(x, y, t), }
}

///|
pub fn pathp_wf(pp : PathPVal) -> Bool {
  in_ty(pp.at0, upath_left(pp.line)) &&
  in_ty(pp.at1, upath_right(pp.line)) &&
  (pp.point)(0.0) == pp.at0 &&
  (pp.point)(1.0) == pp.at1
}

///|
fn pair_point_formula(
  f : (Double) -> PVal,
  g : (Double) -> PVal,
  t : Double,
) -> PVal {
  PVPair(f(t), g(t))
}

///|
/// Pairing PathP elements over the product line.
pub fn pathp_prod(a : PathPVal, b : PathPVal) -> PathPVal {
  PathPVal::{
    line: ua(equiv_prod(a.line.equiv, b.line.equiv)),
    at0: PVPair(a.at0, b.at0),
    at1: PVPair(a.at1, b.at1),
    point: t => pair_point_formula(a.point, b.point, t),
  }
}

///|
fn fst_point(f : (Double) -> PVal, t : Double) -> PVal {
  pval_fst(f(t))
}

///|
fn snd_point(f : (Double) -> PVal, t : Double) -> PVal {
  pval_snd(f(t))
}

///|
/// First projection of a PathP over a product line, given the first factor
/// equivalence of that line.
pub fn pathp_fst(pp : PathPVal, e1 : Equiv) -> PathPVal {
  PathPVal::{
    line: ua(e1),
    at0: pval_fst(pp.at0),
    at1: pval_fst(pp.at1),
    point: t => fst_point(pp.point, t),
  }
}

///|
pub fn pathp_snd(pp : PathPVal, e2 : Equiv) -> PathPVal {
  PathPVal::{
    line: ua(e2),
    at0: pval_snd(pp.at0),
    at1: pval_snd(pp.at1),
    point: t => snd_point(pp.point, t),
  }
}

///|
/// PathP-over-product exchange is a round-trip: pairing the projections of
/// a PathP over a product line recovers its endpoints, its points, and its
/// line (PathP (A×B) ≅ PathP A × PathP B for product lines).
pub fn pathp_prod_exchange_roundtrip(
  pp : PathPVal,
  e1 : Equiv,
  e2 : Equiv,
) -> Bool {
  let rebuilt = pathp_prod(pathp_fst(pp, e1), pathp_snd(pp, e2))
  if rebuilt.at0 != pp.at0 || rebuilt.at1 != pp.at1 {
    return false
  }
  let samples = disc_samples()
  for s in 0..<samples.length() {
    if (rebuilt.point)(samples[s]) != (pp.point)(samples[s]) {
      return false
    }
  }
  upath_eq(rebuilt.line, pp.line) && pathp_wf(rebuilt)
}

///|
pub fn disc_samples() -> Array[Double] {
  [0.0, 0.25, 0.5, 0.75, 1.0]
}

///|
/// A path in a discrete finite type: in this model well-formed paths are
/// constant, so endpoints coincide.
pub struct DiscPath {
  ty : Ty
  lo : PVal
  hi : PVal
  point : (Double) -> PVal
}

///|
pub fn refl_path(ty : Ty, a : PVal) -> DiscPath {
  DiscPath::{ ty, lo: a, hi: a, point: _t => a, }
}

///|
pub fn disc_path_wf(p : DiscPath) -> Bool {
  if (p.point)(0.0) != p.lo || (p.point)(1.0) != p.hi {
    return false
  }
  let samples = disc_samples()
  for s in 0..<samples.length() {
    if (p.point)(samples[s]) != p.lo || !in_ty((p.point)(samples[s]), p.ty) {
      return false
    }
  }
  true
}

///|
fn sym_point(f : (Double) -> PVal, t : Double) -> PVal {
  f(1.0 - t)
}

///|
pub fn disc_path_sym(p : DiscPath) -> DiscPath {
  DiscPath::{ ty: p.ty, lo: p.hi, hi: p.lo, point: t => sym_point(p.point, t), }
}

///|
/// A type family (motive) over PVal.
pub struct Family {
  fiber : (PVal) -> Ty
}

///|
/// J for the discrete fragment, via coe: along a well-formed path the
/// fiber line λi. fiber(p i) is constant, so coe over it is the identity —
/// the *same* code path computes J(p) and J(refl), which is the J
/// computation rule.  Returns None for ill-formed input instead of
/// assuming it away.
pub fn j_elim_disc(fam : Family, d : PVal, p : DiscPath) -> PVal? {
  if !disc_path_wf(p) {
    return None
  }
  if !in_ty(d, (fam.fiber)(p.lo)) {
    return None
  }
  // lo == hi and the line is constant, so fiber(lo) == fiber(hi) and
  // coe over a constant line is the identity function.
  if (fam.fiber)(p.lo) == (fam.fiber)(p.hi) {
    Some(d)
  } else {
    None
  }
}

///|
/// J computation + round-trip: J(refl, d) = d, and J along p then along
/// sym p returns d.
pub fn j_roundtrip(fam : Family, d : PVal, p : DiscPath) -> Bool {
  match j_elim_disc(fam, d, refl_path(p.ty, p.lo)) {
    Some(v) => if v != d { return false }
    None => return false
  }
  match j_elim_disc(fam, d, p) {
    Some(mid) =>
      match j_elim_disc(fam, mid, disc_path_sym(p)) {
        Some(back) => back == d
        None => false
      }
    None => false
  }
}

// ---------------------------------------------------------------------------
// Glue
// ---------------------------------------------------------------------------

///|
/// Glue [ φ ↦ (T, e : T ≃ A) ] A.
pub struct GlueData {
  base_ty : Ty // A
  partial_ty : Ty // T
  equiv : Equiv // T ≃ A
  face : Face // φ
}

///|
pub struct GlueElem {
  partial : PVal
  base : PVal
}

///|
/// Well-formedness of a Glue element: typing, and the compatibility
/// condition that on φ the partial element maps to the base element:
/// φ ⊢ equivFun partial = base.
pub fn glue_wf(g : GlueData, e : GlueElem, nvars : Int32) -> Bool {
  if !in_ty(e.partial, g.partial_ty) || !in_ty(e.base, g.base_ty) {
    return false
  }
  // Values are assignment-independent, so the condition over all env with
  // φ holding collapses to: if φ is satisfiable (BDD decision), the pair
  // must be compatible.
  !face_sat(g.face, nvars) || (g.equiv.fwd)(e.partial) == e.base
}

///|
/// glue: introduction, accepting exactly the compatible pairs.
pub fn make_glue(
  g : GlueData,
  partial : PVal,
  base : PVal,
  nvars : Int32,
) -> GlueElem? {
  let e = GlueElem::{ partial, base, }
  if glue_wf(g, e, nvars) {
    Some(e)
  } else {
    None
  }
}

///|
/// unglue: the underlying element of A.
pub fn unglue(e : GlueElem) -> PVal {
  e.base
}

///|
/// Restriction to an endpoint assignment: on φ, recover the partial part.
pub fn glue_restrict(g : GlueData, e : GlueElem, env : Array[Bool]) -> PVal? {
  if face_holds(g.face, env) {
    Some(e.partial)
  } else {
    None
  }
}

///|
/// Canonical element from a base element: glue (equivInv a) a.
/// This is coe from A into the Glue type along the trivial line.
pub fn glue_from_base(g : GlueData, a : PVal) -> GlueElem {
  GlueElem::{ partial: (g.equiv.bwd)(a), base: a, }
}

///|
/// Glue soundness/reliability (可靠性): for every endpoint assignment
/// satisfying φ, unglue agrees with equivFun of the restriction; the
/// canonical element is well-formed whenever e is, unglues back to its
/// base, and restricts to equivInv of the base on φ.  These are the β/face
/// computation rules of Glue, decided by enumeration.
pub fn glue_sound(g : GlueData, e : GlueElem, nvars : Int32) -> Bool {
  if !glue_wf(g, e, nvars) || !equiv_wf(g.equiv) {
    return false
  }
  // Restriction agreement, on a BDD witness for φ if one exists (values
  // are assignment-independent, so one witness represents all of φ).
  let restrict_ok = match face_witness(g.face, nvars) {
    Some(env) =>
      match glue_restrict(g, e, env) {
        Some(t) => (g.equiv.fwd)(t) == unglue(e)
        None => false
      }
    None => true
  }
  if !restrict_ok {
    return false
  }
  // The canonical element glue_from_base(a) is well-formed for *every* a:
  // symbolically this is the section identity w⁻¹ ; w = id on A, plus a
  // concrete instance at e.base.  unglue(glue_from_base(a)) = a holds by
  // definition (it is the base field).
  let w = g.equiv.wiring
  wiring_eq(wiring_comp(wiring_inv(w), w), wiring_id(g.base_ty)) &&
  glue_wf(g, glue_from_base(g, e.base), nvars) &&
  unglue(glue_from_base(g, e.base)) == e.base
}
