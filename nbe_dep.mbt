///|
// Dependent NbE with Pi, Sigma, universes, Path types, data types,
// higher inductive types, and cubical Kan term constructors.
//
// One AST (DTerm) for terms and types.  Semantics is dependent NbE with
// two contexts: term variables (de Bruijn indices into env) and
// dimension variables (de Bruijn indices into denv, whose entries are
// symbolic Dim expressions at *level*).  Pi/Sigma families and PathP
// lines are semantic closures over persistent, shared environments;
// conversion and quoting are directed by
// semantic types and use eta for Pi/Sigma/Unit/Path.  Universes are
// cumulative: Type_i : Type_{i+1}, Pi/Sigma at max level.
//
// Cubical content:
//   * PathP A a b with A a line body, <i> e path abstraction and
//     e @ r dimension application; Path is the constant-line case.
//   * Kan term constructors DCoe / DComp / DHComp / DHFill.  Their
//     evaluation is the type-directed comp/coe/fill recursion of
//     kan_ast.mbt (Pi contravariant, Sigma along the first fill,
//     PathP with endpoint branches, data by constructor recursion,
//     HITs by point constructors or formal hcomp points, Universe by
//     Glue).  DHComp in a universe evaluates to a semantic Glue type.
//   * Data: Nat and List with dependent eliminators.
//   * HITs: Circle (base, loop) with dependent eliminator, and Torus
//     in the square presentation (points are (i,j) modulo edge
//     identifications; loopA/loopB/square are its faces) with a
//     dependent square eliminator.  Eliminators commute with formal
//     Kan compositions by composing in the motive.
//   * Evaluation infrastructure: environments are persistent cons lists
//     (extension is O(1) and shares the tail); selected subvalues are
//     DVThunk cells forced at most once; dimension lines and elaborated
//     type families can be wrapped in semantic memoizers.

///|
/// One branch of a composition system in the AST: a tube body under
/// the composition dimension, guarded by an ambient face.
pub struct DTubeTerm {
  face : Face
  body : DTerm
} derive(Debug, Eq)

///|
pub extend DTubeTerm with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend DTubeTerm with Eq::{not_equal, equal}

///|
pub fn d_tube(face : Face, body : DTerm) -> DTubeTerm {
  DTubeTerm::{ face, body, }
}

///|
/// One branch of a partial *element* in the AST.  Unlike a tube body,
/// this body is an ordinary term in the ambient dimension context.
pub struct DFaceTerm {
  face : Face
  body : DTerm
} derive(Debug, Eq)

///|
pub extend DFaceTerm with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend DFaceTerm with Eq::{not_equal, equal}

///|
pub fn d_face_term(face : Face, body : DTerm) -> DFaceTerm {
  DFaceTerm::{ face, body, }
}

///|
/// One branch of a Glue type presented directly by an equivalence
/// `partial ≃ base`, guarded by a face.
pub struct DEquivBranch {
  face : Face
  ty : DTerm
  equiv : DTerm
} derive(Debug, Eq)

///|
pub extend DEquivBranch with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend DEquivBranch with Eq::{not_equal, equal}

///|
pub fn d_equiv_branch(face : Face, ty : DTerm, equiv : DTerm) -> DEquivBranch {
  DEquivBranch::{ face, ty, equiv, }
}

///|
pub enum DTerm {
  DTVar(Int32)
  DUniv(Int32) // Type_i
  DUnivLevel(DLevelExpr) // Type at a level expression; instantiate before core checking
  DBoolTy
  DUnitTy
  DPi(DTerm, DTerm) // binder in the second component
  DSigma(DTerm, DTerm)
  DLam(DTerm, DTerm) // annotated domain, body
  DApp(DTerm, DTerm)
  DPair(DTerm, DTerm)
  DFst(DTerm)
  DSnd(DTerm)
  DBoolLit(Bool)
  DBoolElim(DTerm, DTerm, DTerm, DTerm) // motive, true case, false case, scrutinee
  DUnitLit
  DAnn(DTerm, DTerm)
  DPartial(Array[DFaceTerm]) // partial element by face branches
  // Cubical dimension / path syntax.  A type *line* is a DTerm body
  // under one dimension binder; tube bodies likewise.
  DPathP(DTerm, DTerm, DTerm) // line body, lhs, rhs
  DPath(DTerm, DTerm, DTerm) // constant line
  DLamDim(DTerm) // <i> body
  DAppDim(DTerm, Dim)
  // Kan operations as term constructors.
  DCoe(DTerm, Dim, Dim, DTerm) // line body, from, to, value
  DComp(DTerm, Array[DTubeTerm], DTerm) // line body, tube system, base
  DHComp(DTerm, Array[DTubeTerm], DTerm) // type, tube system, base
  DHFill(DTerm, Array[DTubeTerm], DTerm, Dim) // filler at the given dimension
  // Data types.
  DNatTy
  DNatZero
  DSucc(DTerm)
  DNatElim(DTerm, DTerm, DTerm, DTerm) // motive, zero, succ, scrutinee
  DListTy(DTerm)
  DNil
  DCons(DTerm, DTerm)
  DListElim(DTerm, DTerm, DTerm, DTerm) // motive, nil, cons, scrutinee
  // Higher inductive types.
  DCircleTy
  DCircleBase
  DCircleLoop // loop : Path Circle base base
  DCircleElim(DTerm, DTerm, DTerm, DTerm) // motive, base, loop, scrutinee
  DTorusTy
  DTorusBase
  DTorusLoopA
  DTorusLoopB
  DTorusSquare // the commuting square 2-cell
  DTorusElim(DTerm, DTerm, DTerm) // motive, dependent square, scrutinee
  DInductive(DInductiveSpec, Array[DTerm]) // generated type; params then indices
  DIntro(DInductiveSpec, Int32, Array[DTerm], Array[DTerm]) // spec, constructor, params, args
  DInductiveElim(
    DInductiveSpec,
    DTerm,
    Array[DTerm],
    Array[DTerm],
    Array[DTerm],
    DTerm
  )
  DHitType(DHitSpec, Array[DTerm]) // generated HIT; params then indices
  DHitIntro(DHitSpec, Int32, Array[DTerm], Array[DTerm], Array[Dim])
  DHitElim(DHitSpec, DTerm, Array[DTerm], Array[DTerm], Array[DTerm], DTerm)
  DDecode(DInductiveSpec, Array[DTerm], Array[DTerm], DTerm) // spec, params, indices, code
  // First-class equivalences and Glue presented by equivalences.
  DEquivTy(DTerm, DTerm) // A ≃ B
  DMkEquiv(DTerm, DTerm, DTerm, DTerm, DTerm, DTerm) // A, B, fwd, bwd, sect, retr
  DEquivFwd(DTerm)
  DEquivBwd(DTerm)
  DEquivSect(DTerm)
  DEquivRetr(DTerm)
  DGlueEquiv(DTerm, Array[DEquivBranch]) // base type, equiv branches
  DUnglueEquiv(DTerm, DTerm, Array[DEquivBranch]) // glue term, base type, equiv branches
  DUa(DTerm) // an equivalence as a path in the universe
} derive(Debug, Eq)

///|
pub extend DTerm with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend DTerm with Eq::{not_equal, equal}

///|
pub enum DNeutral {
  DNVar(Int32) // level
  DNApp(DNeutral, DValue, DValue) // argument value, argument type
  DNFst(DNeutral, (DValue) -> DValue) // sibling family B
  DNSnd(DNeutral, DValue, (DValue) -> DValue) // first type A, family B
  DNAppDim(DNeutral, Dim)
  DNBoolElim((DValue) -> DValue, DValue, DValue, DNeutral)
  DNNatElim((DValue) -> DValue, DValue, DValue, DNeutral)
  DNListElim(DValue, (DValue) -> DValue, DValue, DValue, DNeutral)
  DNCircleElim((DValue) -> DValue, DValue, DValue, DNeutral)
  DNTorusElim((DValue) -> DValue, (Dim, Dim) -> DValue, DNeutral)
  DNInductiveElim(
    DInductiveSpec,
    (Array[DValue], DValue) -> DValue,
    Array[DValue],
    Array[DValue],
    Array[DValue],
    DNeutral
  )
  DNHitElim(
    DHitSpec,
    (Array[DValue], DValue) -> DValue,
    Array[DValue],
    Array[DValue],
    Array[DValue],
    DNeutral
  )
  DNDecode(DInductiveSpec, Array[DValue], Array[DValue], DNeutral)
  DNEquivFwd(DNeutral, DValue, DValue)
  DNEquivBwd(DNeutral, DValue, DValue)
  DNEquivSect(DNeutral, DValue, DValue)
  DNEquivRetr(DNeutral, DValue, DValue)
  DNEquivAnn(DNeutral, DValue, DValue)
  DNUnglueEquiv(DNeutral, DGlueEquivParts)
  DNComp((Dim) -> DValue, DSystem, DValue)
  DNHComp(DValue, DSystem, DValue)
}

///|
/// A call-by-need semantic cell.  The computation runs at most once;
/// later forces reuse the stored value.  `force_count` is observable
/// instrumentation for the cache/laziness laws.
pub struct DThunk {
  mut forced : DValue?
  compute : () -> DValue
  mut force_count : Int32
}

///|
/// One face-guarded semantic path.  A finite array of these is always
/// packaged as a DSystem below; raw arrays are not used as systems.
pub struct DTubeBranch {
  face : Face
  path : (Dim) -> DValue
}

///|
pub fn tube_branch(face : Face, path : (Dim) -> DValue) -> DTubeBranch {
  DTubeBranch::{ face, path, }
}

///|
/// Semantic composition system.  Smart constructors drop bottom
/// branches and simplify faces; `dsystem_canonical` additionally
/// merges convertible bodies and sorts by quoted body.
pub struct DSystem {
  branches : Array[DTubeBranch]
}

///|
/// One face-guarded semantic value (a partial element branch).
pub struct DFaceValue {
  face : Face
  value : DValue
}

///|
pub fn dface_value(face : Face, value : DValue) -> DFaceValue {
  DFaceValue::{ face, value, }
}

///|
/// A partial semantic value.  Used for multi-branch Glue components
/// and as the value-level counterpart of a composition system.
pub struct DPartialValue {
  branches : Array[DFaceValue]
}

///|
/// One class of the symbolic normal form of a partial value: a BDD
/// region on which the value is constant (up to conversion).
pub struct DSystemClass {
  region : Bdd
  value : DValue
}

///|
pub struct DSystemNF {
  classes : Array[DSystemClass]
  undefined : Bdd
}

///|
/// One semantic Glue branch presented by an equivalence.  `equiv`
/// is a value of `ty ≃ base` for the ambient Glue base type.
pub struct DEquivBranchValue {
  face : Face
  ty : DValue
  equiv : DValue
}

///|
pub fn dequiv_branch_value(
  face : Face,
  ty : DValue,
  equiv : DValue,
) -> DEquivBranchValue {
  DEquivBranchValue::{ face, ty, equiv, }
}

///|
pub struct DGlueEquivParts {
  branches : Array[DEquivBranchValue]
  face : Face
  base : DValue
  level : Int32
}

///|
pub enum DValue {
  DVUniv(Int32)
  DVBoolTy
  DVUnitTy
  DVPi(DValue, (DValue) -> DValue)
  DVSigma(DValue, (DValue) -> DValue)
  DVLam((DValue) -> DValue)
  DVPair(DValue, DValue)
  DVBool(Bool)
  DVUnit
  DVPathTy((Dim) -> DValue, DValue, DValue)
  DVPathLam((Dim) -> DValue)
  DVNatTy
  DVZeroNat
  DVSucc(DValue)
  DVListTy(DValue)
  DVNil
  DVCons(DValue, DValue)
  DVCircleTy
  DVCirclePoint(Dim) // loop at this dimension; endpoints are base
  DVTorusTy
  DVTorusPoint(Dim, Dim) // square point; opposite edges identified
  DVInductive(DInductiveSpec, Array[DValue], Array[DValue])
  DVIntro(DInductiveSpec, Int32, Array[DValue], Array[DValue])
  DVHitType(DHitSpec, Array[DValue], Array[DValue])
  DVHitCell(DHitSpec, Int32, Array[DValue], Array[DValue], Array[Dim])
  DVGlue(DSystem, DValue, Int32) // partial type system, base type, level
  DVEquivTy(DValue, DValue, Int32) // src, dst, universe level
  DVEquiv(DValue, DValue, DValue, DValue, DValue, DValue) // src, dst, fwd, bwd, sect, retr
  DVGlueEquiv(Array[DEquivBranchValue], DValue, Int32) // equiv branches, base, level
  DVPartial(DPartialValue)
  DVThunk(DThunk)
  DVNeutral(DNeutral)
}

///|
pub struct DInfer {
  value : DValue
  ty : DValue
}

///|
pub struct DTypeVal {
  value : DValue
  level : Int32
}

///|
pub struct DFamilyParts {
  dom : DValue
  fam : (DValue) -> DValue
}

///|
pub struct DPathParts {
  line : (Dim) -> DValue
  left : DValue
  right : DValue
}

///|
pub struct DGlueParts {
  system : DSystem
  face : Face // join of the system faces
  line : (Dim) -> DValue // representative line (exact for a singleton system)
  base : DValue
  level : Int32
}

// ---------------------------------------------------------------------------
// Contexts, dimensions, smart constructors
// ---------------------------------------------------------------------------

///|
/// Persistent term/type environment.  Index 0 is the head (most recent
/// binder).  Extending an environment allocates one node and shares the
/// entire tail, rather than copying an array.
pub enum DEnv {
  DEnvNil
  DEnvCons(DValue, DEnv, Int32) // head, shared tail, length
}

///|
/// Persistent dimension environment, with the same sharing discipline.
pub enum DDimEnv {
  DDimEnvNil
  DDimEnvCons(Dim, DDimEnv, Int32)
}

///|
pub fn denv_empty() -> DEnv {
  DEnvNil
}

///|
pub fn denv_cons(v : DValue, env : DEnv) -> DEnv {
  DEnvCons(v, env, denv_len(env) + 1)
}

///|
pub fn denv_len(env : DEnv) -> Int32 {
  match env {
    DEnvNil => 0
    DEnvCons(_, _, n) => n
  }
}

///|
pub fn denv_at(env : DEnv, i : Int32) -> DValue? {
  if i < 0 {
    return None
  }
  let mut cur = env
  let mut k = i
  while true {
    match cur {
      DEnvNil => return None
      DEnvCons(v, tail, _) =>
        if k == 0 {
          return Some(v)
        } else {
          cur = tail
          k = k - 1
        }
    }
  }
  None
}

///|
pub fn denv_tail(env : DEnv) -> DEnv {
  match env {
    DEnvNil => DEnvNil
    DEnvCons(_, tail, _) => tail
  }
}

///|
/// Build a persistent environment from values in de Bruijn order
/// (element 0 becomes index 0).
pub fn denv_from_array(values : Array[DValue]) -> DEnv {
  let mut out = denv_empty()
  let mut i = values.length() - 1
  while i >= 0 {
    out = denv_cons(values[i], out)
    i = i - 1
  }
  out
}

///|
pub fn denv_to_array(env : DEnv) -> Array[DValue] {
  let out : Array[DValue] = []
  let mut cur = env
  while true {
    match cur {
      DEnvNil => break
      DEnvCons(v, tail, _) => {
        out.push(v)
        cur = tail
      }
    }
  }
  out
}

///|
/// Cons a sequence of values in declaration order.  After this
/// operation the last supplied value is de Bruijn index 0, matching a
/// telescope whose binders were introduced left-to-right.
pub fn denv_extend(values : Array[DValue], env : DEnv) -> DEnv {
  let mut out = env
  for i in 0..<values.length() {
    out = denv_cons(values[i], out)
  }
  out
}

///|
pub fn ddim_empty() -> DDimEnv {
  DDimEnvNil
}

///|
pub fn ddim_cons(d : Dim, denv : DDimEnv) -> DDimEnv {
  DDimEnvCons(d, denv, ddim_len(denv) + 1)
}

///|
pub fn ddim_len(denv : DDimEnv) -> Int32 {
  match denv {
    DDimEnvNil => 0
    DDimEnvCons(_, _, n) => n
  }
}

///|
pub fn ddim_at(denv : DDimEnv, i : Int32) -> Dim? {
  if i < 0 {
    return None
  }
  let mut cur = denv
  let mut k = i
  while true {
    match cur {
      DDimEnvNil => return None
      DDimEnvCons(v, tail, _) =>
        if k == 0 {
          return Some(v)
        } else {
          cur = tail
          k = k - 1
        }
    }
  }
  None
}

///|
pub fn ddim_from_array(values : Array[Dim]) -> DDimEnv {
  let mut out = ddim_empty()
  let mut i = values.length() - 1
  while i >= 0 {
    out = ddim_cons(values[i], out)
    i = i - 1
  }
  out
}

///|
pub fn ddim_to_array(denv : DDimEnv) -> Array[Dim] {
  let out : Array[Dim] = []
  let mut cur = denv
  while true {
    match cur {
      DDimEnvNil => break
      DDimEnvCons(v, tail, _) => {
        out.push(v)
        cur = tail
      }
    }
  }
  out
}

///|
pub fn ddim_extend(values : Array[Dim], denv : DDimEnv) -> DDimEnv {
  let mut out = denv
  for i in 0..<values.length() {
    out = ddim_cons(values[i], out)
  }
  out
}

///|
pub fn fresh_dim(denv : DDimEnv) -> Dim {
  DVar(ddim_len(denv))
}

///|
pub fn eval_dim_expr(r : Dim, denv : DDimEnv) -> Dim {
  match r {
    DVar(i) =>
      match ddim_at(denv, i) {
        Some(x) => x
        None => r
      }
    DNeg(a) => dim_simplify(DNeg(eval_dim_expr(a, denv)))
    DAnd(a, b) =>
      dim_simplify(DAnd(eval_dim_expr(a, denv), eval_dim_expr(b, denv)))
    DOr(a, b) =>
      dim_simplify(DOr(eval_dim_expr(a, denv), eval_dim_expr(b, denv)))
    other => other
  }
}

///|
pub fn dim_quote(r : Dim, dlevel : Int32) -> Dim {
  match r {
    DVar(l) => if l < dlevel { DVar(dlevel - 1 - l) } else { DVar(l) }
    DNeg(a) => DNeg(dim_quote(a, dlevel))
    DAnd(a, b) => DAnd(dim_quote(a, dlevel), dim_quote(b, dlevel))
    DOr(a, b) => DOr(dim_quote(a, dlevel), dim_quote(b, dlevel))
    other => other
  }
}

///|
pub fn face_eval_env(f : Face, denv : DDimEnv) -> Face {
  match f {
    FEq0(r) => face_simplify(FEq0(eval_dim_expr(r, denv)))
    FEq1(r) => face_simplify(FEq1(eval_dim_expr(r, denv)))
    FAnd(a, b) =>
      face_simplify(FAnd(face_eval_env(a, denv), face_eval_env(b, denv)))
    FOr(a, b) =>
      face_simplify(FOr(face_eval_env(a, denv), face_eval_env(b, denv)))
    other => other
  }
}

///|
pub fn face_quote(f : Face, dlevel : Int32) -> Face {
  match f {
    FEq0(r) => FEq0(dim_quote(r, dlevel))
    FEq1(r) => FEq1(dim_quote(r, dlevel))
    FAnd(a, b) => FAnd(face_quote(a, dlevel), face_quote(b, dlevel))
    FOr(a, b) => FOr(face_quote(a, dlevel), face_quote(b, dlevel))
    other => other
  }
}

///|
fn dv_unwrap(v : DValue?) -> DValue {
  match v {
    Some(x) => x
    None => DVUnit
  }
}

///|
fn dinfer_value(r : DInfer?) -> DValue {
  match r {
    Some(x) => x.value
    None => DVUnit
  }
}

///|
fn dinfer_ty(r : DInfer?) -> DValue {
  match r {
    Some(x) => x.ty
    None => DVUnitTy
  }
}

///|
pub fn lazy_value(compute : () -> DValue) -> DValue {
  DVThunk(DThunk::{ forced: None, compute, force_count: 0, })
}

///|
pub fn force_value(v : DValue) -> DValue {
  match v {
    DVThunk(cell) =>
      match cell.forced {
        Some(x) => force_value(x)
        None => {
          cell.force_count = cell.force_count + 1
          let out = force_value((cell.compute)())
          cell.forced = Some(out)
          out
        }
      }
    other => other
  }
}

///|
pub fn lazy_is_forced(v : DValue) -> Bool {
  match v {
    DVThunk(cell) =>
      match cell.forced {
        Some(_) => true
        None => false
      }
    _ => true
  }
}

///|
pub fn lazy_force_count(v : DValue) -> Int32 {
  match v {
    DVThunk(cell) => cell.force_count
    _ => 0
  }
}

///|
let dind_spec_key_registry : Array[DInductiveSpec] = []

///|
let dhit_spec_key_registry : Array[DHitSpec] = []

///|
fn dind_spec_key_id(spec : DInductiveSpec) -> Int {
  for i in 0..<dind_spec_key_registry.length() {
    let entry = dind_spec_key_registry[i]
    if entry.name == spec.name &&
      entry.constructors.length() == spec.constructors.length() &&
      entry == spec {
      return i
    }
  }
  let id = dind_spec_key_registry.length()
  dind_spec_key_registry.push(spec)
  id
}

///|
fn dhit_spec_key_id(spec : DHitSpec) -> Int {
  for i in 0..<dhit_spec_key_registry.length() {
    let entry = dhit_spec_key_registry[i]
    if entry.name == spec.name && entry == spec {
      return i
    }
  }
  let id = dhit_spec_key_registry.length()
  dhit_spec_key_registry.push(spec)
  id
}

///|
fn dim_write_key(buf : StringBuilder, r : Dim) -> Unit {
  match r {
    DZero => buf.write_char('0')
    DOne => buf.write_char('1')
    DVar(v) => {
      buf.write_char('v')
      buf.write_string(v.to_string())
      buf.write_char(';')
    }
    DNeg(x) => {
      buf.write_char('~')
      dim_write_key(buf, x)
    }
    DAnd(a, b) => {
      buf.write_char('&')
      dim_write_key(buf, a)
      dim_write_key(buf, b)
    }
    DOr(a, b) => {
      buf.write_char('|')
      dim_write_key(buf, a)
      dim_write_key(buf, b)
    }
  }
}

///|
fn face_write_key(buf : StringBuilder, f : Face) -> Unit {
  match f {
    FTop => buf.write_char('T')
    FBot => buf.write_char('F')
    FEq0(r) => {
      buf.write_char('z')
      dim_write_key(buf, r)
    }
    FEq1(r) => {
      buf.write_char('o')
      dim_write_key(buf, r)
    }
    FAnd(a, b) => {
      buf.write_char('a')
      face_write_key(buf, a)
      face_write_key(buf, b)
    }
    FOr(a, b) => {
      buf.write_char('r')
      face_write_key(buf, a)
      face_write_key(buf, b)
    }
  }
}

///|
fn dlevel_write_key(buf : StringBuilder, lv : DLevelExpr) -> Unit {
  match lv {
    DLevelConst(k) => {
      buf.write_char('c')
      buf.write_string(k.to_string())
      buf.write_char(';')
    }
    DLevelVar(v) => {
      buf.write_char('v')
      buf.write_string(v.to_string())
      buf.write_char(';')
    }
    DLevelSucc(e) => {
      buf.write_char('s')
      dlevel_write_key(buf, e)
    }
    DLevelMax(a, b) => {
      buf.write_char('m')
      dlevel_write_key(buf, a)
      dlevel_write_key(buf, b)
    }
  }
}

///|
fn dterm_array_write_key(buf : StringBuilder, ts : Array[DTerm]) -> Unit {
  buf.write_char('[')
  buf.write_string(ts.length().to_string())
  buf.write_char(':')
  for t in ts {
    dterm_write_key(buf, t)
  }
  buf.write_char(']')
}

///|
fn dtube_array_write_key(buf : StringBuilder, ts : Array[DTubeTerm]) -> Unit {
  buf.write_char('[')
  buf.write_string(ts.length().to_string())
  buf.write_char(':')
  for tb in ts {
    face_write_key(buf, tb.face)
    dterm_write_key(buf, tb.body)
  }
  buf.write_char(']')
}

///|
fn dequiv_branches_write_key(
  buf : StringBuilder,
  bs : Array[DEquivBranch],
) -> Unit {
  buf.write_char('[')
  buf.write_string(bs.length().to_string())
  buf.write_char(':')
  for b in bs {
    face_write_key(buf, b.face)
    dterm_write_key(buf, b.ty)
    dterm_write_key(buf, b.equiv)
  }
  buf.write_char(']')
}

///|
fn dterm_write_key(buf : StringBuilder, t : DTerm) -> Unit {
  match t {
    DTVar(i) => {
      buf.write_string("V")
      buf.write_string(i.to_string())
      buf.write_char(';')
    }
    DUniv(k) => {
      buf.write_string("U")
      buf.write_string(k.to_string())
      buf.write_char(';')
    }
    DUnivLevel(lv) => {
      buf.write_string("UL")
      dlevel_write_key(buf, lv)
    }
    DBoolTy => buf.write_string("BT;")
    DUnitTy => buf.write_string("UT;")
    DPi(a, b) => {
      buf.write_string("Pi")
      dterm_write_key(buf, a)
      dterm_write_key(buf, b)
    }
    DSigma(a, b) => {
      buf.write_string("Sg")
      dterm_write_key(buf, a)
      dterm_write_key(buf, b)
    }
    DLam(a, b) => {
      buf.write_string("Lm")
      dterm_write_key(buf, a)
      dterm_write_key(buf, b)
    }
    DApp(f, x) => {
      buf.write_string("Ap")
      dterm_write_key(buf, f)
      dterm_write_key(buf, x)
    }
    DPair(a, b) => {
      buf.write_string("Pr")
      dterm_write_key(buf, a)
      dterm_write_key(buf, b)
    }
    DFst(p) => {
      buf.write_string("F1")
      dterm_write_key(buf, p)
    }
    DSnd(p) => {
      buf.write_string("F2")
      dterm_write_key(buf, p)
    }
    DBoolLit(b) => buf.write_string(if b { "B1;" } else { "B0;" })
    DBoolElim(m, t1, t0, s) => {
      buf.write_string("BE")
      dterm_write_key(buf, m)
      dterm_write_key(buf, t1)
      dterm_write_key(buf, t0)
      dterm_write_key(buf, s)
    }
    DUnitLit => buf.write_string("u0;")
    DAnn(e, ty) => {
      buf.write_string("An")
      dterm_write_key(buf, e)
      dterm_write_key(buf, ty)
    }
    DPartial(fs) => {
      buf.write_string("Pt[")
      buf.write_string(fs.length().to_string())
      buf.write_char(':')
      for ft in fs {
        face_write_key(buf, ft.face)
        dterm_write_key(buf, ft.body)
      }
      buf.write_char(']')
    }
    DPathP(l, a, b) => {
      buf.write_string("PP")
      dterm_write_key(buf, l)
      dterm_write_key(buf, a)
      dterm_write_key(buf, b)
    }
    DPath(ty, a, b) => {
      buf.write_string("Pa")
      dterm_write_key(buf, ty)
      dterm_write_key(buf, a)
      dterm_write_key(buf, b)
    }
    DLamDim(b) => {
      buf.write_string("LD")
      dterm_write_key(buf, b)
    }
    DAppDim(p, r) => {
      buf.write_string("AD")
      dterm_write_key(buf, p)
      dim_write_key(buf, r)
    }
    DCoe(l, r0, r1, v) => {
      buf.write_string("Co")
      dterm_write_key(buf, l)
      dim_write_key(buf, r0)
      dim_write_key(buf, r1)
      dterm_write_key(buf, v)
    }
    DComp(l, ts, b) => {
      buf.write_string("Cp")
      dterm_write_key(buf, l)
      dtube_array_write_key(buf, ts)
      dterm_write_key(buf, b)
    }
    DHComp(ty, ts, b) => {
      buf.write_string("HC")
      dterm_write_key(buf, ty)
      dtube_array_write_key(buf, ts)
      dterm_write_key(buf, b)
    }
    DHFill(ty, ts, b, r) => {
      buf.write_string("HF")
      dterm_write_key(buf, ty)
      dtube_array_write_key(buf, ts)
      dterm_write_key(buf, b)
      dim_write_key(buf, r)
    }
    DNatTy => buf.write_string("NT;")
    DNatZero => buf.write_string("NZ;")
    DSucc(n) => {
      buf.write_string("NS")
      dterm_write_key(buf, n)
    }
    DNatElim(m, z, s, n) => {
      buf.write_string("NE")
      dterm_write_key(buf, m)
      dterm_write_key(buf, z)
      dterm_write_key(buf, s)
      dterm_write_key(buf, n)
    }
    DListTy(a) => {
      buf.write_string("LT")
      dterm_write_key(buf, a)
    }
    DNil => buf.write_string("LN;")
    DCons(h, tl) => {
      buf.write_string("LC")
      dterm_write_key(buf, h)
      dterm_write_key(buf, tl)
    }
    DListElim(m, n, c, l) => {
      buf.write_string("LE")
      dterm_write_key(buf, m)
      dterm_write_key(buf, n)
      dterm_write_key(buf, c)
      dterm_write_key(buf, l)
    }
    DCircleTy => buf.write_string("S1;")
    DCircleBase => buf.write_string("Sb;")
    DCircleLoop => buf.write_string("Sl;")
    DCircleElim(m, b, l, x) => {
      buf.write_string("SE")
      dterm_write_key(buf, m)
      dterm_write_key(buf, b)
      dterm_write_key(buf, l)
      dterm_write_key(buf, x)
    }
    DTorusTy => buf.write_string("T2;")
    DTorusBase => buf.write_string("Tb;")
    DTorusLoopA => buf.write_string("Ta;")
    DTorusLoopB => buf.write_string("Tc;")
    DTorusSquare => buf.write_string("Tq;")
    DTorusElim(m, q, x) => {
      buf.write_string("TE")
      dterm_write_key(buf, m)
      dterm_write_key(buf, q)
      dterm_write_key(buf, x)
    }
    DInductive(spec, args) => {
      buf.write_string("IT")
      buf.write_string(dind_spec_key_id(spec).to_string())
      buf.write_char(';')
      dterm_array_write_key(buf, args)
    }
    DIntro(spec, c, ps, args) => {
      buf.write_string("II")
      buf.write_string(dind_spec_key_id(spec).to_string())
      buf.write_char(',')
      buf.write_string(c.to_string())
      buf.write_char(';')
      dterm_array_write_key(buf, ps)
      dterm_array_write_key(buf, args)
    }
    DInductiveElim(spec, m, ps, bs, ix, sc) => {
      buf.write_string("IE")
      buf.write_string(dind_spec_key_id(spec).to_string())
      buf.write_char(';')
      dterm_write_key(buf, m)
      dterm_array_write_key(buf, ps)
      dterm_array_write_key(buf, bs)
      dterm_array_write_key(buf, ix)
      dterm_write_key(buf, sc)
    }
    DHitType(spec, args) => {
      buf.write_string("HT")
      buf.write_string(dhit_spec_key_id(spec).to_string())
      buf.write_char(';')
      dterm_array_write_key(buf, args)
    }
    DHitIntro(spec, c, ps, args, ds) => {
      buf.write_string("HI")
      buf.write_string(dhit_spec_key_id(spec).to_string())
      buf.write_char(',')
      buf.write_string(c.to_string())
      buf.write_char(';')
      dterm_array_write_key(buf, ps)
      dterm_array_write_key(buf, args)
      buf.write_char('[')
      buf.write_string(ds.length().to_string())
      buf.write_char(':')
      for d in ds {
        dim_write_key(buf, d)
      }
      buf.write_char(']')
    }
    DHitElim(spec, m, ps, bs, ix, sc) => {
      buf.write_string("HE")
      buf.write_string(dhit_spec_key_id(spec).to_string())
      buf.write_char(';')
      dterm_write_key(buf, m)
      dterm_array_write_key(buf, ps)
      dterm_array_write_key(buf, bs)
      dterm_array_write_key(buf, ix)
      dterm_write_key(buf, sc)
    }
    DDecode(spec, ps, ix, code) => {
      buf.write_string("DC")
      buf.write_string(dind_spec_key_id(spec).to_string())
      buf.write_char(';')
      dterm_array_write_key(buf, ps)
      dterm_array_write_key(buf, ix)
      dterm_write_key(buf, code)
    }
    DEquivTy(a, b) => {
      buf.write_string("ET")
      dterm_write_key(buf, a)
      dterm_write_key(buf, b)
    }
    DMkEquiv(a, b, f, g, s, r) => {
      buf.write_string("ME")
      dterm_write_key(buf, a)
      dterm_write_key(buf, b)
      dterm_write_key(buf, f)
      dterm_write_key(buf, g)
      dterm_write_key(buf, s)
      dterm_write_key(buf, r)
    }
    DEquivFwd(e) => {
      buf.write_string("Ef")
      dterm_write_key(buf, e)
    }
    DEquivBwd(e) => {
      buf.write_string("Eb")
      dterm_write_key(buf, e)
    }
    DEquivSect(e) => {
      buf.write_string("Es")
      dterm_write_key(buf, e)
    }
    DEquivRetr(e) => {
      buf.write_string("Er")
      dterm_write_key(buf, e)
    }
    DGlueEquiv(b, bs) => {
      buf.write_string("GE")
      dterm_write_key(buf, b)
      dequiv_branches_write_key(buf, bs)
    }
    DUnglueEquiv(g, b, bs) => {
      buf.write_string("UG")
      dterm_write_key(buf, g)
      dterm_write_key(buf, b)
      dequiv_branches_write_key(buf, bs)
    }
    DUa(e) => {
      buf.write_string("Ua")
      dterm_write_key(buf, e)
    }
  }
}

///|
/// Stable injective cache keys.  DTerm keys use a compact prefix-free
/// structural encoding with interned schema IDs; dimension keys first pass
/// through the De Morgan simplifier.
pub fn dterm_cache_key(t : DTerm) -> String {
  let buf = StringBuilder()
  dterm_write_key(buf, t)
  buf.to_string()
}

///|
pub fn dim_cache_key(r : Dim) -> String {
  let buf = StringBuilder()
  dim_write_key(buf, dim_simplify(r))
  buf.to_string()
}

///|
/// Memoize a semantic dimension line.  Dimensions that simplify to the
/// same expression share one computed semantic type.
pub fn memo_dim_line(f : (Dim) -> DValue) -> (Dim) -> DValue {
  let cache : Array[(String, DValue)] = []
  d => {
    let key = dim_cache_key(d)
    for i in 0..<cache.length() {
      if cache[i].0 == key {
        return cache[i].1
      }
    }
    let out = f(dim_simplify(d))
    cache.push((key, out))
    out
  }
}

///|
/// Memoize a dependent semantic family by the quoted normal form of its
/// argument.  This is semantic (conversion-stable for values quoted by
/// this NbE), rather than pointer-keyed.
pub fn memo_family(
  f : (DValue) -> DValue,
  dom : DValue,
  level : Int32,
  dlevel : Int32,
) -> (DValue) -> DValue {
  let cache : Array[(String, DValue)] = []
  arg => {
    let key = dterm_cache_key(quote_at(level, dlevel, dom, arg))
    for i in 0..<cache.length() {
      if cache[i].0 == key {
        return cache[i].1
      }
    }
    let out = f(arg)
    cache.push((key, out))
    out
  }
}

///|
pub fn dapp_typed(f : DValue, arg : DValue, arg_ty : DValue) -> DValue {
  match force_value(f) {
    DVLam(g) => g(arg)
    DVNeutral(n) => {
      let real_arg_ty = match force_value(arg_ty) {
        DVUnitTy =>
          match neutral_inferred_type(n) {
            Some(fty) =>
              match as_pi(fty) {
                Some(parts) => parts.dom
                None => arg_ty
              }
            None => arg_ty
          }
        _ => arg_ty
      }
      DVNeutral(DNApp(n, arg, real_arg_ty))
    }
    _ => DVUnit
  }
}

///|
pub fn dfst_typed(v : DValue, fam : (DValue) -> DValue) -> DValue {
  match force_value(v) {
    DVPair(a, _) => a
    DVNeutral(n) => {
      let real_fam = match neutral_inferred_type(n) {
        Some(sty) =>
          match as_sigma(sty) {
            Some(parts) => parts.fam
            None => fam
          }
        None => fam
      }
      DVNeutral(DNFst(n, real_fam))
    }
    _ => DVUnit
  }
}

///|
pub fn dsnd_typed(
  v : DValue,
  fst_ty : DValue,
  fam : (DValue) -> DValue,
) -> DValue {
  match force_value(v) {
    DVPair(_, b) => b
    DVNeutral(n) => {
      let (real_fst_ty, real_fam) = match force_value(fst_ty) {
        DVUnitTy =>
          match neutral_inferred_type(n) {
            Some(sty) =>
              match as_sigma(sty) {
                Some(parts) => (parts.dom, parts.fam)
                None => (fst_ty, fam)
              }
            None => (fst_ty, fam)
          }
        _ => (fst_ty, fam)
      }
      DVNeutral(DNSnd(n, real_fst_ty, real_fam))
    }
    _ => DVUnit
  }
}

///|

///|
/// Endpoint reduction for paths obtained from a neutral
/// equivalence's section/retraction projections: `(sect e y) @ 0`
/// is `equivFun e (equivInv e y)`, `(sect e y) @ 1` is `y`, and
/// dually for the retraction.  Without this rule, a path built by
/// congruence from an abstract equivalence (for example the
/// triangle coherence of an adjoint equivalence) cannot be checked
/// against its stated endpoint type.
fn neutral_inferred_type(neu : DNeutral) -> DValue? {
  match neu {
    DNBoolElim(motive, _, _, scrut) => Some(motive(DVNeutral(scrut)))
    DNNatElim(motive, _, _, scrut) => Some(motive(DVNeutral(scrut)))
    DNListElim(_, motive, _, _, scrut) => Some(motive(DVNeutral(scrut)))
    DNCircleElim(motive, _, _, scrut) => Some(motive(DVNeutral(scrut)))
    DNTorusElim(motive, _, scrut) => Some(motive(DVNeutral(scrut)))
    DNInductiveElim(_, motive, _, _, indices, scrut) =>
      Some(motive(indices, DVNeutral(scrut)))
    DNHitElim(_, motive, _, _, indices, scrut) =>
      Some(motive(indices, DVNeutral(scrut)))
    DNDecode(spec, params, indices, _) =>
      Some(DVInductive(spec, params, indices))
    DNComp(line, _, _) => Some(line(DOne))
    DNHComp(ty, _, _) => Some(ty)
    DNApp(inner, arg, _) =>
      match neutral_inferred_type(inner) {
        Some(fty) =>
          match as_pi(fty) {
            Some(parts) => Some((parts.fam)(arg))
            None => None
          }
        None => None
      }
    DNFst(inner, _) =>
      match neutral_inferred_type(inner) {
        Some(sty) =>
          match as_sigma(sty) {
            Some(parts) => Some(parts.dom)
            None => None
          }
        None => None
      }
    DNSnd(inner, _, _) =>
      match neutral_inferred_type(inner) {
        Some(sty) =>
          match as_sigma(sty) {
            Some(parts) =>
              Some((parts.fam)(dfst_typed(DVNeutral(inner), parts.fam)))
            None => None
          }
        None => None
      }
    DNAppDim(inner, s) =>
      match neutral_inferred_type(inner) {
        Some(pty) =>
          match as_path(pty) {
            Some(parts) => Some((parts.line)(s))
            None => None
          }
        None => None
      }
    DNEquivFwd(_, src, dst) => Some(DVPi(src, _ => dst))
    DNEquivBwd(_, src, dst) => Some(DVPi(dst, _ => src))
    DNUnglueEquiv(_, parts) => Some(parts.base)
    _ => None
  }
}

///|
fn neutral_equiv_path_endpoint(n : DNeutral, r : Dim) -> DValue? {
  match n {
    DNApp(DNEquivSect(e, src, dst), y, _) =>
      if dim_is_zero(r) {
        Some(
          DVNeutral(
            DNApp(
              DNEquivFwd(e, src, dst),
              DVNeutral(DNApp(DNEquivBwd(e, src, dst), y, dst)),
              src,
            ),
          ),
        )
      } else if dim_is_one(r) {
        Some(y)
      } else {
        None
      }
    DNApp(DNEquivRetr(e, src, dst), x, _) =>
      if dim_is_zero(r) {
        Some(
          DVNeutral(
            DNApp(
              DNEquivBwd(e, src, dst),
              DVNeutral(DNApp(DNEquivFwd(e, src, dst), x, src)),
              dst,
            ),
          ),
        )
      } else if dim_is_one(r) {
        Some(x)
      } else {
        None
      }
    other =>
      if dim_is_zero(r) || dim_is_one(r) {
        match neutral_inferred_type(other) {
          Some(ty) =>
            match as_path(ty) {
              Some(parts) =>
                Some(if dim_is_zero(r) { parts.left } else { parts.right })
              None => None
            }
          None => None
        }
      } else {
        None
      }
  }
}

///|
/// Type-directed CCHM reflection of a neutral expression `neu` at semantic
/// type `ty`: path variables reduce judgementally to `left` / `right` at
/// dimension endpoints `0` / `1` (recursively across iterated path spaces),
/// function variables η-reflect with typed domain applications, and
/// dependent-pair variables reflect both projections so path components
/// of pointed structures inherit judgemental boundary computation.
pub fn reflect_neutral_at_type(neu : DNeutral, ty : DValue) -> DValue {
  match force_value(ty) {
    DVPathTy(line, left, right) =>
      DVPathLam(r => {
        let rs = dim_simplify(r)
        if dim_is_zero(rs) {
          left
        } else if dim_is_one(rs) {
          right
        } else {
          reflect_neutral_at_type(DNAppDim(neu, rs), line(rs))
        }
      })
    DVPi(dom, fam) =>
      DVLam(arg => {
        let a = force_value(arg)
        reflect_neutral_at_type(DNApp(neu, a, dom), fam(a))
      })
    DVSigma(dom, fam) => {
      let fst_v = reflect_neutral_at_type(DNFst(neu, fam), dom)
      DVPair(fst_v, reflect_neutral_at_type(DNSnd(neu, dom, fam), fam(fst_v)))
    }
    DVEquivTy(src, dst, _) => DVNeutral(DNEquivAnn(neu, src, dst))
    _ => DVNeutral(neu)
  }
}

///|
pub fn reflect_var(level : Int32, ty : DValue) -> DValue {
  reflect_neutral_at_type(DNVar(level), ty)
}

///|
pub fn dapp_dim(v : DValue, r : Dim) -> DValue {
  match force_value(v) {
    DVPathLam(f) => f(dim_simplify(r))
    DVNeutral(n) =>
      match neutral_equiv_path_endpoint(n, dim_simplify(r)) {
        Some(endpoint) => endpoint
        None => DVNeutral(DNAppDim(n, dim_simplify(r)))
      }
    _ => DVUnit
  }
}

///|
pub fn circle_point(r : Dim) -> DValue {
  match dim_simplify(r) {
    DZero | DOne => DVCirclePoint(DZero)
    x => DVCirclePoint(x)
  }
}

///|
pub fn circle_dim_of(v : DValue) -> Dim {
  match force_value(v) {
    DVCirclePoint(x) => x
    _ => DZero
  }
}

///|
pub fn torus_dims_of(v : DValue) -> (Dim, Dim) {
  match force_value(v) {
    DVTorusPoint(x, y) => (x, y)
    _ => (DZero, DZero)
  }
}

///|
pub fn torus_point(a : Dim, b : Dim) -> DValue {
  let na = match dim_simplify(a) {
    DOne => DZero
    x => x
  }
  let nb = match dim_simplify(b) {
    DOne => DZero
    x => x
  }
  DVTorusPoint(na, nb)
}

///|
pub fn as_pi(v : DValue) -> DFamilyParts? {
  match force_value(v) {
    DVPi(a, fam) => Some(DFamilyParts::{ dom: a, fam, })
    _ => None
  }
}

///|
pub fn as_sigma(v : DValue) -> DFamilyParts? {
  match force_value(v) {
    DVSigma(a, fam) => Some(DFamilyParts::{ dom: a, fam, })
    _ => None
  }
}

///|
pub fn as_path(v : DValue) -> DPathParts? {
  match force_value(v) {
    DVPathTy(line, l, r) => Some(DPathParts::{ line, left: l, right: r, })
    _ => None
  }
}

///|
pub fn as_glue(v : DValue) -> DGlueParts? {
  match force_value(v) {
    DVGlue(system, base, level) =>
      Some(DGlueParts::{
        system,
        face: dsystem_domain_face(system),
        line: dsystem_first_path(system, base),
        base,
        level,
      })
    _ => None
  }
}

///|
pub fn as_univ_level(v : DValue) -> Int32? {
  match force_value(v) {
    DVUniv(l) => Some(l)
    _ => None
  }
}

///|
pub fn as_list_elem(v : DValue) -> DValue? {
  match force_value(v) {
    DVListTy(a) => Some(a)
    _ => None
  }
}

// ---------------------------------------------------------------------------
// Semantic systems: canonical merging, sorting, and partial values
// ---------------------------------------------------------------------------

///|
pub fn dsystem_empty() -> DSystem {
  DSystem::{ branches: [], }
}

///|
/// Package branches as a system, dropping bottom faces and simplifying
/// the remaining face expressions.  Value merging is separate because
/// it is type-directed (see `dsystem_canonical`).
pub fn dsystem_of(branches : Array[DTubeBranch]) -> DSystem {
  let out : Array[DTubeBranch] = []
  for i in 0..<branches.length() {
    let br = branches[i]
    if !face_is_bot_sem(br.face) {
      out.push(tube_branch(face_simplify(br.face), br.path))
    }
  }
  DSystem::{ branches: out, }
}

///|
pub fn dsystem_singleton(face : Face, path : (Dim) -> DValue) -> DSystem {
  dsystem_of([tube_branch(face, path)])
}

///|
pub fn dsystem_map(
  system : DSystem,
  f : ((Dim) -> DValue) -> (Dim) -> DValue,
) -> DSystem {
  let out : Array[DTubeBranch] = []
  for i in 0..<system.branches.length() {
    let br = system.branches[i]
    out.push(tube_branch(br.face, f(br.path)))
  }
  DSystem::{ branches: out, }
}

///|
pub fn dsystem_domain_face(system : DSystem) -> Face {
  let mut face = FBot
  for i in 0..<system.branches.length() {
    face = face_simplify(FOr(face, system.branches[i].face))
  }
  face
}

///|
pub fn dsystem_first_path(
  system : DSystem,
  fallback : DValue,
) -> (Dim) -> DValue {
  if system.branches.length() == 0 {
    _ => fallback
  } else {
    system.branches[0].path
  }
}

///|
fn tube_paths_conv(
  level : Int32,
  dlevel : Int32,
  line : (Dim) -> DValue,
  p : (Dim) -> DValue,
  q : (Dim) -> DValue,
) -> Bool {
  let fresh = DVar(dlevel)
  conv_at(level, dlevel, line(DOne), p(DOne), q(DOne)) &&
  conv_at(level, dlevel, line(DZero), p(DZero), q(DZero)) &&
  conv_at(level, dlevel + 1, line(fresh), p(fresh), q(fresh))
}

///|
fn dterm_conv_plausible(a : DTerm, b : DTerm) -> Bool {
  match (a, b) {
    (DPartial(_), _)
    | (_, DPartial(_))
    | (DGlueEquiv(_, _), _)
    | (_, DGlueEquiv(_, _))
    | (DHComp(DUniv(_), _, _), _)
    | (_, DHComp(DUniv(_), _, _)) => true
    (DTVar(x), DTVar(y)) => x == y
    (DUnitLit, DUnitLit) => true
    (DBoolLit(x), DBoolLit(y)) => x == y
    (DLam(_, b1), DLam(_, b2)) => dterm_conv_plausible(b1, b2)
    (DApp(f1, a1), DApp(f2, a2)) =>
      dterm_conv_plausible(f1, f2) && dterm_conv_plausible(a1, a2)
    (DPair(a1, b1), DPair(a2, b2)) =>
      dterm_conv_plausible(a1, a2) && dterm_conv_plausible(b1, b2)
    (DFst(p1), DFst(p2)) => dterm_conv_plausible(p1, p2)
    (DSnd(p1), DSnd(p2)) => dterm_conv_plausible(p1, p2)
    (DUnglueEquiv(g1, _, _), DUnglueEquiv(g2, _, _)) =>
      dterm_conv_plausible(g1, g2)
    (DLamDim(b1), DLamDim(b2)) => dterm_conv_plausible(b1, b2)
    (DAppDim(DCircleLoop, _), DCircleBase)
    | (DCircleBase, DAppDim(DCircleLoop, _)) => true
    (DTorusBase, _)
    | (_, DTorusBase)
    | (DAppDim(DTorusLoopA, _), _)
    | (_, DAppDim(DTorusLoopA, _))
    | (DAppDim(DTorusLoopB, _), _)
    | (_, DAppDim(DTorusLoopB, _))
    | (DAppDim(DAppDim(DTorusSquare, _), _), _)
    | (_, DAppDim(DAppDim(DTorusSquare, _), _)) => true
    (DAppDim(f1, _), DAppDim(f2, _)) => dterm_conv_plausible(f1, f2)
    (DNatZero, DNatZero) => true
    (DSucc(x), DSucc(y)) => dterm_conv_plausible(x, y)
    (DNil, DNil) => true
    (DCons(x1, xs1), DCons(x2, xs2)) =>
      dterm_conv_plausible(x1, x2) && dterm_conv_plausible(xs1, xs2)
    (DCircleBase, DCircleBase) => true
    (DComp(_, br1, base1), DComp(_, br2, base2)) =>
      br1.length() == br2.length() && dterm_conv_plausible(base1, base2)
    (DHComp(_, br1, base1), DHComp(_, br2, base2)) =>
      br1.length() == br2.length() && dterm_conv_plausible(base1, base2)
    (DIntro(s1, c1, _, a1), DIntro(s2, c2, _, a2)) => {
      if s1 != s2 || c1 != c2 || a1.length() != a2.length() {
        return false
      }
      for idx in 0..<a1.length() {
        if !dterm_conv_plausible(a1[idx], a2[idx]) {
          return false
        }
      }
      true
    }
    (DHitIntro(s1, c1, _, a1, d1), DHitIntro(s2, c2, _, a2, d2)) => {
      if s1 != s2 ||
        c1 != c2 ||
        a1.length() != a2.length() ||
        d1.length() != d2.length() {
        return false
      }
      for idx in 0..<a1.length() {
        if !dterm_conv_plausible(a1[idx], a2[idx]) {
          return false
        }
      }
      true
    }
    (DInductiveElim(s1, _, _, _, _, n1), DInductiveElim(s2, _, _, _, _, n2)) =>
      s1 == s2 && dterm_conv_plausible(n1, n2)
    (DHitElim(s1, _, _, _, _, n1), DHitElim(s2, _, _, _, _, n2)) =>
      s1 == s2 && dterm_conv_plausible(n1, n2)
    (DBoolElim(_, _, _, n1), DBoolElim(_, _, _, n2))
    | (DNatElim(_, _, _, n1), DNatElim(_, _, _, n2))
    | (DListElim(_, _, _, n1), DListElim(_, _, _, n2))
    | (DCircleElim(_, _, _, n1), DCircleElim(_, _, _, n2))
    | (DTorusElim(_, _, n1), DTorusElim(_, _, n2)) =>
      dterm_conv_plausible(n1, n2)
    (DDecode(s1, _, _, n1), DDecode(s2, _, _, n2)) =>
      s1 == s2 && dterm_conv_plausible(n1, n2)
    (DEquivFwd(x), DEquivFwd(y))
    | (DEquivBwd(x), DEquivBwd(y))
    | (DEquivSect(x), DEquivSect(y))
    | (DEquivRetr(x), DEquivRetr(y)) => dterm_conv_plausible(x, y)
    (DUniv(_), DUniv(_))
    | (DBoolTy, DBoolTy)
    | (DUnitTy, DUnitTy)
    | (DPi(_, _), DPi(_, _))
    | (DSigma(_, _), DSigma(_, _))
    | (DPathP(_, _, _), DPathP(_, _, _))
    | (DPath(_, _, _), DPath(_, _, _))
    | (DNatTy, DNatTy)
    | (DListTy(_), DListTy(_))
    | (DCircleTy, DCircleTy)
    | (DTorusTy, DTorusTy)
    | (DEquivTy(_, _), DEquivTy(_, _))
    | (DMkEquiv(_, _, _, _, _, _), DMkEquiv(_, _, _, _, _, _)) => true
    (DInductive(s1, _), DInductive(s2, _)) => s1 == s2
    (DHitType(s1, _), DHitType(s2, _)) => s1 == s2
    _ => false
  }
}

///|
fn dsystem_face_key(br : DTubeBranch) -> String {
  // Use the BDD, not face syntax, so semantically equal faces have the
  // same tie-breaking key.
  Repr(bdd_of_face(face_simplify(br.face), face_nvars_sem(br.face))).to_string()
}

///|
fn dsystem_canonical_quoted(
  level : Int32,
  dlevel : Int32,
  line : (Dim) -> DValue,
  system : DSystem,
) -> (DSystem, Array[DTerm]) {
  let fresh = DVar(dlevel)
  let line_fresh = line(fresh)
  let faces : Array[Face] = []
  let paths : Array[(Dim) -> DValue] = []
  let quoted : Array[DTerm] = []
  let keys : Array[String] = []
  for i in 0..<system.branches.length() {
    let br = system.branches[i]
    if face_is_bot_sem(br.face) {
      continue
    }
    let q_i = quote_at(level, dlevel + 1, line_fresh, (br.path)(fresh))
    let key_i = dterm_cache_key(q_i)
    let mut merged = false
    for k in 0..<paths.length() {
      let same = if keys[k] == key_i {
        conv_at(level, dlevel, line(DOne), paths[k](DOne), (br.path)(DOne)) &&
        conv_at(level, dlevel, line(DZero), paths[k](DZero), (br.path)(DZero))
      } else if dterm_conv_plausible(quoted[k], q_i) {
        tube_paths_conv(level, dlevel, line, paths[k], br.path)
      } else {
        false
      }
      if same {
        faces[k] = face_simplify(FOr(faces[k], br.face))
        merged = true
        break
      }
    }
    if !merged {
      faces.push(face_simplify(br.face))
      paths.push(br.path)
      quoted.push(q_i)
      keys.push(key_i)
    }
  }
  let out : Array[DTubeBranch] = []
  let face_keys : Array[String] = []
  for i in 0..<paths.length() {
    let br = tube_branch(faces[i], paths[i])
    out.push(br)
    face_keys.push(dsystem_face_key(br))
  }
  // Sort lexicographically by (body, face).  Comparing a concatenated
  // key would let total string length interfere with the primary key.
  for _pass in 0..<out.length() {
    for j in 0..<(out.length() - 1) {
      let swap = keys[j + 1] < keys[j] ||
        (keys[j + 1] == keys[j] && face_keys[j + 1] < face_keys[j])
      if swap {
        let tmp_branch = out[j]
        out[j] = out[j + 1]
        out[j + 1] = tmp_branch
        let tmp_q = quoted[j]
        quoted[j] = quoted[j + 1]
        quoted[j + 1] = tmp_q
        let tmp_body = keys[j]
        keys[j] = keys[j + 1]
        keys[j + 1] = tmp_body
        let tmp_face = face_keys[j]
        face_keys[j] = face_keys[j + 1]
        face_keys[j + 1] = tmp_face
      }
    }
  }
  (DSystem::{ branches: out, }, quoted)
}

///|
/// Canonical form of a composition system along a type line: bottom
/// branches vanish, branches with convertible bodies are merged by
/// joining their faces, and classes are sorted by quoted body.
pub fn dsystem_canonical(
  level : Int32,
  dlevel : Int32,
  line : (Dim) -> DValue,
  system : DSystem,
) -> DSystem {
  let (canon, _) = dsystem_canonical_quoted(level, dlevel, line, system)
  canon
}

///|
pub fn partial_empty() -> DPartialValue {
  DPartialValue::{ branches: [], }
}

///|
pub fn partial_of(branches : Array[DFaceValue]) -> DPartialValue {
  let out : Array[DFaceValue] = []
  for i in 0..<branches.length() {
    let br = branches[i]
    if !face_is_bot_sem(br.face) {
      out.push(dface_value(face_simplify(br.face), br.value))
    }
  }
  DPartialValue::{ branches: out, }
}

///|
pub fn partial_singleton(face : Face, value : DValue) -> DPartialValue {
  partial_of([dface_value(face, value)])
}

///|
fn partial_nvars(partial : DPartialValue, dlevel : Int32) -> Int32 {
  let mut n = dlevel
  for i in 0..<partial.branches.length() {
    let m = face_nvars_sem(partial.branches[i].face)
    if m > n {
      n = m
    }
  }
  n
}

///|
/// Symbolic normal form of a partial value at a type.  Effective
/// regions are computed with BDDs under first-match semantics, equal
/// values are merged, and classes are sorted by quoted value.  This is
/// the dependent analogue of `system_normal_form` for vectors.
pub fn partial_normal_form(
  level : Int32,
  dlevel : Int32,
  ty : DValue,
  partial0 : DPartialValue,
) -> DSystemNF {
  let partial = partial_of(partial0.branches)
  let nvars = partial_nvars(partial, dlevel)
  let regions : Array[Bdd] = []
  let values : Array[DValue] = []
  let mut covered = BddZero
  for i in 0..<partial.branches.length() {
    let br = partial.branches[i]
    let region_all = bdd_of_face(br.face, nvars)
    let effective = bdd_and(region_all, bdd_not(covered))
    covered = bdd_or(covered, region_all)
    if effective == BddZero {
      continue
    }
    let mut merged = false
    for k in 0..<values.length() {
      if conv_at(level, dlevel, ty, values[k], br.value) {
        regions[k] = bdd_or(regions[k], effective)
        merged = true
        break
      }
    }
    if !merged {
      regions.push(effective)
      values.push(br.value)
    }
  }
  let keys : Array[String] = []
  for i in 0..<values.length() {
    keys.push(dterm_cache_key(quote_at(level, dlevel, ty, values[i])))
  }
  for _pass in 0..<values.length() {
    for j in 0..<(values.length() - 1) {
      if keys[j + 1] < keys[j] {
        let tmp_region = regions[j]
        regions[j] = regions[j + 1]
        regions[j + 1] = tmp_region
        let tmp_value = values[j]
        values[j] = values[j + 1]
        values[j + 1] = tmp_value
        let tmp_key = keys[j]
        keys[j] = keys[j + 1]
        keys[j + 1] = tmp_key
      }
    }
  }
  let classes : Array[DSystemClass] = []
  for i in 0..<values.length() {
    classes.push(DSystemClass::{ region: regions[i], value: values[i], })
  }
  DSystemNF::{ classes, undefined: bdd_not(covered), }
}

///|
pub fn partial_eq_at(
  level : Int32,
  dlevel : Int32,
  ty : DValue,
  a : DPartialValue,
  b : DPartialValue,
) -> Bool {
  let na = partial_normal_form(level, dlevel, ty, a)
  let nb = partial_normal_form(level, dlevel, ty, b)
  if na.undefined != nb.undefined || na.classes.length() != nb.classes.length() {
    return false
  }
  for i in 0..<na.classes.length() {
    if na.classes[i].region != nb.classes[i].region ||
      !conv_at(level, dlevel, ty, na.classes[i].value, nb.classes[i].value) {
      return false
    }
  }
  true
}

///|
pub fn partial_domain_bdd(partial : DPartialValue, dlevel : Int32) -> Bdd {
  let nvars = partial_nvars(partial, dlevel)
  let mut covered = BddZero
  for i in 0..<partial.branches.length() {
    covered = bdd_or(covered, bdd_of_face(partial.branches[i].face, nvars))
  }
  covered
}

///|
/// The normal form of a tube system sampled at one dimension.
pub fn tube_system_nf_at(
  level : Int32,
  dlevel : Int32,
  line : (Dim) -> DValue,
  system : DSystem,
  at : Dim,
) -> DSystemNF {
  let branches : Array[DFaceValue] = []
  for i in 0..<system.branches.length() {
    let br = system.branches[i]
    branches.push(dface_value(br.face, (br.path)(at)))
  }
  partial_normal_form(level, dlevel, line(at), partial_of(branches))
}

///|
fn same_face_sem(a : Face, b : Face) -> Bool {
  let na = face_nvars_sem(a)
  let nb = face_nvars_sem(b)
  let n = if na > nb { na } else { nb }
  face_eq_mod(a, b, n)
}

///|
/// Align a stored Glue partial component with a Glue type system.
/// A raw value is replicated over the branches; a DVPartial is matched
/// by semantic face equality (falling back to position when arities agree).
pub fn glue_partial_values(
  parts : DGlueParts,
  stored : DValue,
) -> Array[DValue] {
  let out : Array[DValue] = []
  match force_value(stored) {
    DVPartial(p) =>
      for i in 0..<parts.system.branches.length() {
        let wanted = parts.system.branches[i].face
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
      for _i in 0..<parts.system.branches.length() {
        out.push(raw)
      }
  }
  out
}

///|
/// Store branch-aligned partial values.  Singleton systems keep the
/// historical raw-pair representation; larger systems use DVPartial.
pub fn glue_store_partial(parts : DGlueParts, values : Array[DValue]) -> DValue {
  if values.length() == 0 {
    DVUnit
  } else if parts.system.branches.length() <= 1 {
    values[0]
  } else {
    let branches : Array[DFaceValue] = []
    for i in 0..<parts.system.branches.length() {
      let v = if i < values.length() { values[i] } else { DVUnit }
      branches.push(dface_value(parts.system.branches[i].face, v))
    }
    DVPartial(partial_of(branches))
  }
}

// ---------------------------------------------------------------------------
// Plain evaluation with dimension environment
// ---------------------------------------------------------------------------

///|
pub fn eval_tube_terms(
  tubes : Array[DTubeTerm],
  env : DEnv,
  denv : DDimEnv,
) -> DSystem {
  let out : Array[DTubeBranch] = []
  for i in 0..<tubes.length() {
    let tube = tubes[i]
    out.push(
      tube_branch(face_eval_env(tube.face, denv), d => {
        deval_dim(tube.body, env, ddim_cons(d, denv))
      }),
    )
  }
  dsystem_of(out)
}

///|
/// A suspended plain evaluation.  Used for constructor fields and
/// eliminator branches that need not be evaluated until demanded.
pub fn lazy_deval(t : DTerm, env : DEnv, denv : DDimEnv) -> DValue {
  lazy_value(() => deval_dim(t, env, denv))
}

///|
pub fn deval_dim(t : DTerm, env : DEnv, denv : DDimEnv) -> DValue {
  match t {
    DTVar(i) =>
      match denv_at(env, i) {
        Some(v) => v
        None => DVNeutral(DNVar(0))
      }
    DUniv(l) => DVUniv(l)
    DUnivLevel(_) => DVUniv(-1) // uninstantiated level template; checked entries reject it
    DBoolTy => DVBoolTy
    DUnitTy => DVUnitTy
    DPi(a, b) => {
      let dom = deval_dim(a, env, denv)
      DVPi(
        dom,
        memo_family(
          arg => deval_dim(b, denv_cons(arg, env), denv),
          dom,
          denv_len(env),
          ddim_len(denv),
        ),
      )
    }
    DSigma(a, b) => {
      let dom = deval_dim(a, env, denv)
      DVSigma(
        dom,
        memo_family(
          arg => deval_dim(b, denv_cons(arg, env), denv),
          dom,
          denv_len(env),
          ddim_len(denv),
        ),
      )
    }
    DLam(_, body) => DVLam(arg => deval_dim(body, denv_cons(arg, env), denv))
    DApp(f, a) =>
      dapp_typed(deval_dim(f, env, denv), lazy_deval(a, env, denv), DVUnitTy)
    DPair(a, b) => DVPair(lazy_deval(a, env, denv), lazy_deval(b, env, denv))
    DFst(a) => dfst_typed(deval_dim(a, env, denv), _ => DVUnitTy)
    DSnd(a) => dsnd_typed(deval_dim(a, env, denv), DVUnitTy, _ => DVUnitTy)
    DBoolLit(b) => DVBool(b)
    DBoolElim(motive, tt, ff, scrut) =>
      eval_bool_elim(
        x => deval_dim(motive, denv_cons(x, env), denv),
        lazy_deval(tt, env, denv),
        lazy_deval(ff, env, denv),
        deval_dim(scrut, env, denv),
        ddim_len(denv),
      )
    DUnitLit => DVUnit
    DAnn(inner, _) => deval_dim(inner, env, denv)
    DPartial(branches) => {
      let out : Array[DFaceValue] = []
      for i in 0..<branches.length() {
        let br = branches[i]
        out.push(
          dface_value(
            face_eval_env(br.face, denv),
            lazy_deval(br.body, env, denv),
          ),
        )
      }
      DVPartial(partial_of(out))
    }
    DPathP(line, l, r) =>
      DVPathTy(
        memo_dim_line(d => deval_dim(line, env, ddim_cons(d, denv))),
        lazy_deval(l, env, denv),
        deval_dim(r, env, denv),
      )
    DPath(a, l, r) => {
      let av = deval_dim(a, env, denv)
      DVPathTy(_ => av, deval_dim(l, env, denv), deval_dim(r, env, denv))
    }
    DLamDim(body) => DVPathLam(d => deval_dim(body, env, ddim_cons(d, denv)))
    DAppDim(p, r) => dapp_dim(deval_dim(p, env, denv), eval_dim_expr(r, denv))
    DCoe(line, r, s, v) =>
      coe_value(
        memo_dim_line(d => deval_dim(line, env, ddim_cons(d, denv))),
        eval_dim_expr(r, denv),
        eval_dim_expr(s, denv),
        deval_dim(v, env, denv),
        ddim_len(denv),
      )
    DComp(line, tubes, base) =>
      comp_value(
        memo_dim_line(d => deval_dim(line, env, ddim_cons(d, denv))),
        eval_tube_terms(tubes, env, denv),
        deval_dim(base, env, denv),
        ddim_len(denv),
      )
    DHComp(a, tubes, base) =>
      hcomp_value(
        deval_dim(a, env, denv),
        eval_tube_terms(tubes, env, denv),
        deval_dim(base, env, denv),
        ddim_len(denv),
      )
    DHFill(a, tubes, base, r) =>
      hfill_value(
        deval_dim(a, env, denv),
        eval_tube_terms(tubes, env, denv),
        deval_dim(base, env, denv),
        ddim_len(denv),
      )(eval_dim_expr(r, denv))
    DNatTy => DVNatTy
    DNatZero => DVZeroNat
    DSucc(n) => DVSucc(lazy_deval(n, env, denv))
    DNatElim(motive, z, s, scrut) =>
      eval_nat_elim(
        x => deval_dim(motive, denv_cons(x, env), denv),
        lazy_deval(z, env, denv),
        lazy_deval(s, env, denv),
        deval_dim(scrut, env, denv),
        ddim_len(denv),
      )
    DListTy(a) => DVListTy(deval_dim(a, env, denv))
    DNil => DVNil
    DCons(x, xs) => DVCons(lazy_deval(x, env, denv), lazy_deval(xs, env, denv))
    DListElim(motive, z, s, scrut) =>
      eval_list_elim(
        DVUnitTy,
        x => deval_dim(motive, denv_cons(x, env), denv),
        lazy_deval(z, env, denv),
        lazy_deval(s, env, denv),
        deval_dim(scrut, env, denv),
        ddim_len(denv),
      )
    DCircleTy => DVCircleTy
    DCircleBase => DVCirclePoint(DZero)
    DCircleLoop => DVPathLam(d => circle_point(d))
    DCircleElim(motive, b, l, scrut) =>
      eval_circle_elim(
        x => deval_dim(motive, denv_cons(x, env), denv),
        lazy_deval(b, env, denv),
        lazy_deval(l, env, denv),
        deval_dim(scrut, env, denv),
        ddim_len(denv),
      )
    DTorusTy => DVTorusTy
    DTorusBase => DVTorusPoint(DZero, DZero)
    DTorusLoopA => DVPathLam(d => torus_point(d, DZero))
    DTorusLoopB => DVPathLam(d => torus_point(DZero, d))
    DTorusSquare => DVPathLam(a => DVPathLam(b => torus_point(a, b)))
    DInductive(spec, args) => eval_inductive_type_term(spec, args, env, denv)
    DIntro(spec, ctor, params, args) =>
      eval_intro_term(spec, ctor, params, args, env, denv)
    DInductiveElim(spec, motive, cases, params, indices, scrut) =>
      eval_inductive_elim_term(
        spec, motive, cases, params, indices, scrut, env, denv,
      )
    DHitType(spec, args) => eval_hit_type_term(spec, args, env, denv)
    DHitIntro(spec, cell, params, args, dims) =>
      eval_hit_intro_term(spec, cell, params, args, dims, env, denv)
    DHitElim(spec, motive, cases, params, indices, scrut) =>
      eval_hit_elim_term(spec, motive, cases, params, indices, scrut, env, denv)
    DDecode(spec, params, indices, code) =>
      eval_decode_term(spec, params, indices, code, env, denv)
    DEquivTy(a, b) =>
      DVEquivTy(deval_dim(a, env, denv), deval_dim(b, env, denv), 0)
    DMkEquiv(a, b, f, g, sect, retr) =>
      eval_mk_equiv_term(a, b, f, g, sect, retr, env, denv)
    DEquivFwd(e) => {
      let value = deval_dim(e, env, denv)
      let (src, dst) = equiv_types_of_value(value)
      equiv_fwd_value(value, src, dst)
    }
    DEquivBwd(e) => {
      let value = deval_dim(e, env, denv)
      let (src, dst) = equiv_types_of_value(value)
      equiv_bwd_value(value, src, dst)
    }
    DEquivSect(e) => {
      let value = deval_dim(e, env, denv)
      let (src, dst) = equiv_types_of_value(value)
      equiv_sect_value(value, src, dst)
    }
    DEquivRetr(e) => {
      let value = deval_dim(e, env, denv)
      let (src, dst) = equiv_types_of_value(value)
      equiv_retr_value(value, src, dst)
    }
    DGlueEquiv(base, branches) =>
      eval_glue_equiv_term(base, branches, env, denv)
    DUnglueEquiv(term, base, branches) =>
      eval_unglue_equiv_term(term, base, branches, env, denv)
    DUa(e) => eval_ua_term(e, env, denv)
    DTorusElim(motive, square, scrut) =>
      eval_torus_elim(
        x => deval_dim(motive, denv_cons(x, env), denv),
        (a, b) => deval_dim(square, env, ddim_cons(b, ddim_cons(a, denv))),
        deval_dim(scrut, env, denv),
        ddim_len(denv),
      )
  }
}

///|
pub fn deval(t : DTerm, env : Array[DValue]) -> DValue {
  deval_dim(t, denv_from_array(env), ddim_empty())
}

// ---------------------------------------------------------------------------
// Eliminator computation (including commutation with formal compositions)
// ---------------------------------------------------------------------------

///|
fn elim_over_comp(
  line : (Dim) -> DValue,
  branches : DSystem,
  base : DValue,
  motive : (DValue) -> DValue,
  elim : (DValue) -> DValue,
  dlevel : Int32,
) -> DValue {
  let scrut_fill = fill_value(line, branches, base, dlevel)
  let mapped = dsystem_map(branches, p => d => elim(p(d)))
  comp_value(d => motive(scrut_fill(d)), mapped, elim(base), dlevel)
}

///|
pub fn eval_bool_elim(
  motive : (DValue) -> DValue,
  tt : DValue,
  ff : DValue,
  scrut : DValue,
  dlevel : Int32,
) -> DValue {
  match force_value(scrut) {
    DVBool(true) => tt
    DVBool(false) => ff
    DVNeutral(DNComp(line, branches, base)) =>
      elim_over_comp(
        line,
        branches,
        base,
        motive,
        v => eval_bool_elim(motive, tt, ff, v, dlevel),
        dlevel,
      )
    DVNeutral(DNHComp(ty, branches, base)) =>
      elim_over_comp(
        _ => ty,
        branches,
        base,
        motive,
        v => eval_bool_elim(motive, tt, ff, v, dlevel),
        dlevel,
      )
    DVNeutral(n) => DVNeutral(DNBoolElim(motive, tt, ff, n))
    _ => DVUnit
  }
}

///|
pub fn eval_nat_elim(
  motive : (DValue) -> DValue,
  z : DValue,
  s : DValue,
  scrut : DValue,
  dlevel : Int32,
) -> DValue {
  match force_value(scrut) {
    DVZeroNat => z
    DVSucc(n) =>
      dapp_typed(
        dapp_typed(s, n, DVNatTy),
        eval_nat_elim(motive, z, s, n, dlevel),
        motive(n),
      )
    DVNeutral(DNComp(line, branches, base)) =>
      elim_over_comp(
        line,
        branches,
        base,
        motive,
        v => eval_nat_elim(motive, z, s, v, dlevel),
        dlevel,
      )
    DVNeutral(DNHComp(ty, branches, base)) =>
      elim_over_comp(
        _ => ty,
        branches,
        base,
        motive,
        v => eval_nat_elim(motive, z, s, v, dlevel),
        dlevel,
      )
    DVNeutral(n) => DVNeutral(DNNatElim(motive, z, s, n))
    _ => DVUnit
  }
}

///|
pub fn eval_list_elim(
  elem_ty : DValue,
  motive : (DValue) -> DValue,
  z : DValue,
  s : DValue,
  scrut : DValue,
  dlevel : Int32,
) -> DValue {
  match force_value(scrut) {
    DVNil => z
    DVCons(x, xs) => {
      let ih = eval_list_elim(elem_ty, motive, z, s, xs, dlevel)
      let step1 = dapp_typed(s, x, elem_ty)
      let step2 = dapp_typed(step1, xs, DVListTy(elem_ty))
      dapp_typed(step2, ih, motive(xs))
    }
    DVNeutral(DNComp(line, branches, base)) =>
      elim_over_comp(
        line,
        branches,
        base,
        motive,
        v => eval_list_elim(elem_ty, motive, z, s, v, dlevel),
        dlevel,
      )
    DVNeutral(DNHComp(ty, branches, base)) =>
      elim_over_comp(
        _ => ty,
        branches,
        base,
        motive,
        v => eval_list_elim(elem_ty, motive, z, s, v, dlevel),
        dlevel,
      )
    DVNeutral(n) => DVNeutral(DNListElim(elem_ty, motive, z, s, n))
    _ => DVUnit
  }
}

///|
pub fn eval_circle_elim(
  motive : (DValue) -> DValue,
  b : DValue,
  l : DValue,
  scrut : DValue,
  dlevel : Int32,
) -> DValue {
  match force_value(scrut) {
    DVCirclePoint(r) =>
      match dim_simplify(r) {
        DZero | DOne => b
        x => dapp_dim(l, x)
      }
    DVNeutral(DNComp(line, branches, base)) =>
      elim_over_comp(
        line,
        branches,
        base,
        motive,
        v => eval_circle_elim(motive, b, l, v, dlevel),
        dlevel,
      )
    DVNeutral(DNHComp(ty, branches, base)) =>
      elim_over_comp(
        _ => ty,
        branches,
        base,
        motive,
        v => eval_circle_elim(motive, b, l, v, dlevel),
        dlevel,
      )
    DVNeutral(n) => DVNeutral(DNCircleElim(motive, b, l, n))
    _ => DVUnit
  }
}

///|
pub fn eval_torus_elim(
  motive : (DValue) -> DValue,
  square : (Dim, Dim) -> DValue,
  scrut : DValue,
  dlevel : Int32,
) -> DValue {
  match force_value(scrut) {
    DVTorusPoint(a, b) => square(a, b)
    DVNeutral(DNComp(line, branches, base)) =>
      elim_over_comp(
        line,
        branches,
        base,
        motive,
        v => eval_torus_elim(motive, square, v, dlevel),
        dlevel,
      )
    DVNeutral(DNHComp(ty, branches, base)) =>
      elim_over_comp(
        _ => ty,
        branches,
        base,
        motive,
        v => eval_torus_elim(motive, square, v, dlevel),
        dlevel,
      )
    DVNeutral(n) => DVNeutral(DNTorusElim(motive, square, n))
    _ => DVUnit
  }
}

// ---------------------------------------------------------------------------
// Bidirectional elaboration
// ---------------------------------------------------------------------------

///|
pub fn d_as_type(
  t : DTerm,
  ctx : DEnv,
  env : DEnv,
  denv : DDimEnv,
) -> DTypeVal? {
  match d_infer(t, ctx, env, denv) {
    Some(r) =>
      match as_univ_level(r.ty) {
        Some(l) => Some(DTypeVal::{ value: r.value, level: l, })
        None => None
      }
    None => None
  }
}

///|
fn dtype_of_fam(
  b : DTerm,
  ctx : DEnv,
  env : DEnv,
  denv : DDimEnv,
  dom : DValue,
  arg : DValue,
) -> DValue {
  match d_as_type(b, denv_cons(dom, ctx), denv_cons(arg, env), denv) {
    Some(tv) => tv.value
    None => DVUnitTy
  }
}

///|
fn dim_subst_assignment(d : Dim, asgn : Array[Int32]) -> Dim {
  match d {
    DZero => DZero
    DOne => DOne
    DVar(v) =>
      if v >= 0 && v < asgn.length() {
        if asgn[v] == 0 {
          DZero
        } else if asgn[v] == 1 {
          DOne
        } else {
          DVar(v)
        }
      } else {
        DVar(v)
      }
    DNeg(a) => dim_simplify(DNeg(dim_subst_assignment(a, asgn)))
    DAnd(a, b) =>
      dim_simplify(
        DAnd(dim_subst_assignment(a, asgn), dim_subst_assignment(b, asgn)),
      )
    DOr(a, b) =>
      dim_simplify(
        DOr(dim_subst_assignment(a, asgn), dim_subst_assignment(b, asgn)),
      )
  }
}

///|
fn d_check_tube_under_face(
  body : DTerm,
  sem_face : Face,
  line_fn : (Dim) -> DValue,
  ctx : DEnv,
  env : DEnv,
  denv : DDimEnv,
) -> Bool {
  let dl = ddim_len(denv)
  let fresh = DVar(dl)
  if !(d_check(body, line_fn(fresh), ctx, env, ddim_cons(fresh, denv)) is None) {
    return true
  }
  if face_is_bot_sem(sem_face) {
    return true
  }
  let face_vars = face_nvars_sem(sem_face)
  let sub_dl = if dl > face_vars { dl } else { face_vars }
  let subcubes = cubical_face_subcubes(sem_face, sub_dl)
  if subcubes.length() == 0 {
    return false
  }
  let level = denv_len(ctx)
  let fresh_sub = DVar(sub_dl)
  let line_term = quote_ty(level, sub_dl + 1, line_fn(fresh_sub))
  let orig_dims = ddim_to_array(denv)
  for s in 0..<subcubes.length() {
    let asgn = subcubes[s]
    let sub_dim_env = cube_dim_env(asgn)
    let mut ctx_sub = denv_empty()
    let mut env_sub = denv_empty()
    for lvl in 0..<level {
      let orig_ty = match denv_at(ctx, level - 1 - lvl) {
        Some(t) => t
        None => DVUnitTy
      }
      let ty_term = quote_ty(lvl, sub_dl, orig_ty)
      let sub_ty = deval_dim(ty_term, env_sub, sub_dim_env)
      let sub_var = reflect_var(lvl, sub_ty)
      let sub_val = match denv_at(env, level - 1 - lvl) {
        Some(orig_v) => {
          let v_term = quote_at(lvl + 1, sub_dl, orig_ty, orig_v)
          deval_dim(v_term, denv_cons(sub_var, env_sub), sub_dim_env)
        }
        None => sub_var
      }
      ctx_sub = denv_cons(sub_ty, ctx_sub)
      env_sub = denv_cons(sub_val, env_sub)
    }
    let sub_dims : Array[Dim] = []
    for k in 0..<orig_dims.length() {
      sub_dims.push(dim_subst_assignment(orig_dims[k], asgn))
    }
    let denv_sub = ddim_from_array(sub_dims)
    let expected_sub = deval_dim(
      line_term,
      env_sub,
      ddim_cons(fresh_sub, sub_dim_env),
    )
    if d_check(
        body,
        expected_sub,
        ctx_sub,
        env_sub,
        ddim_cons(fresh_sub, denv_sub),
      )
      is None {
      return false
    }
  }
  true
}

///|
fn d_checked_branches(
  tubes : Array[DTubeTerm],
  line_fn : (Dim) -> DValue,
  ctx : DEnv,
  env : DEnv,
  denv : DDimEnv,
) -> DSystem? {
  let out : Array[DTubeBranch] = []
  for i in 0..<tubes.length() {
    let tube = tubes[i]
    let sem_face = face_eval_env(tube.face, denv)
    if d_check_tube_under_face(tube.body, sem_face, line_fn, ctx, env, denv) {
      out.push(
        tube_branch(sem_face, d => deval_dim(tube.body, env, ddim_cons(d, denv))),
      )
    } else {
      return None
    }
  }
  Some(
    dsystem_canonical(denv_len(ctx), ddim_len(denv), line_fn, dsystem_of(out)),
  )
}

///|
fn d_system_compat(
  env : DEnv,
  branches : DSystem,
  line_fn : (Dim) -> DValue,
  base : DValue,
  level : Int32,
  dlevel : Int32,
) -> Bool {
  // Face-relative compatibility (dsystem_compat.mbt): branches need
  // only agree on their actual overlaps, and with the base on their
  // own faces, evaluated in the typed reflected environment `env`.
  dsystem_compatible_with_base_in(env, level, dlevel, line_fn, branches, base)
}

///|
pub fn d_infer(t : DTerm, ctx : DEnv, env : DEnv, denv : DDimEnv) -> DInfer? {
  match t {
    DTVar(i) =>
      match (denv_at(env, i), denv_at(ctx, i)) {
        (Some(v), Some(ty)) => Some(DInfer::{ value: v, ty, })
        _ => None
      }
    DUniv(l) =>
      if l >= 0 {
        Some(DInfer::{ value: DVUniv(l), ty: DVUniv(l + 1), })
      } else {
        None
      }
    DUnivLevel(_) => None // instantiate level variables before core checking
    DBoolTy => Some(DInfer::{ value: DVBoolTy, ty: DVUniv(0), })
    DUnitTy => Some(DInfer::{ value: DVUnitTy, ty: DVUniv(0), })
    DPi(a, b) | DSigma(a, b) =>
      match d_as_type(a, ctx, env, denv) {
        Some(at) => {
          let fresh = reflect_var(denv_len(ctx), at.value)
          match
            d_as_type(b, denv_cons(at.value, ctx), denv_cons(fresh, env), denv) {
            Some(bt) => {
              let fam = memo_family(
                arg => dtype_of_fam(b, ctx, env, denv, at.value, arg),
                at.value,
                denv_len(ctx),
                ddim_len(denv),
              )
              let value = match t {
                DPi(_, _) => DVPi(at.value, fam)
                _ => DVSigma(at.value, fam)
              }
              let lvl = if at.level > bt.level { at.level } else { bt.level }
              Some(DInfer::{ value, ty: DVUniv(lvl), })
            }
            None => None
          }
        }
        None => None
      }
    DLam(dom, body) =>
      match d_as_type(dom, ctx, env, denv) {
        Some(at) => {
          let fresh = reflect_var(denv_len(ctx), at.value)
          match
            d_infer(body, denv_cons(at.value, ctx), denv_cons(fresh, env), denv) {
            Some(_) =>
              Some(DInfer::{
                value: DVLam(arg => {
                  dinfer_value(
                    d_infer(
                      body,
                      denv_cons(at.value, ctx),
                      denv_cons(arg, env),
                      denv,
                    ),
                  )
                }),
                ty: DVPi(at.value, arg => {
                  dinfer_ty(
                    d_infer(
                      body,
                      denv_cons(at.value, ctx),
                      denv_cons(arg, env),
                      denv,
                    ),
                  )
                }),
              })
            None => None
          }
        }
        None => None
      }
    DApp(f, a) =>
      match d_infer(f, ctx, env, denv) {
        Some(fr) =>
          match as_pi(fr.ty) {
            Some(parts) =>
              match d_check(a, parts.dom, ctx, env, denv) {
                Some(av) =>
                  Some(DInfer::{
                    value: dapp_typed(fr.value, av, parts.dom),
                    ty: (parts.fam)(av),
                  })
                None => None
              }
            None => None
          }
        None => None
      }
    DFst(a) =>
      match d_infer(a, ctx, env, denv) {
        Some(pr) =>
          match as_sigma(pr.ty) {
            Some(parts) =>
              Some(DInfer::{
                value: dfst_typed(pr.value, parts.fam),
                ty: parts.dom,
              })
            None =>
              match as_glue(pr.ty) {
                Some(g) =>
                  if g.system.branches.length() <= 1 {
                    Some(DInfer::{
                      value: dfst_typed(pr.value, _ => g.base),
                      ty: (g.line)(DOne),
                    })
                  } else {
                    None
                  }
                None => None
              }
          }
        None => None
      }
    DSnd(a) =>
      match d_infer(a, ctx, env, denv) {
        Some(pr) =>
          match as_sigma(pr.ty) {
            Some(parts) => {
              let fst_val = dfst_typed(pr.value, parts.fam)
              Some(DInfer::{
                value: dsnd_typed(pr.value, parts.dom, parts.fam),
                ty: (parts.fam)(fst_val),
              })
            }
            None =>
              match as_glue(pr.ty) {
                Some(g) =>
                  Some(DInfer::{
                    value: dsnd_typed(pr.value, (g.line)(DOne), _ => g.base),
                    ty: g.base,
                  })
                None => None
              }
          }
        None => None
      }
    DBoolElim(motive, tt, ff, scrut) =>
      match d_check(scrut, DVBoolTy, ctx, env, denv) {
        Some(sv) => {
          let fam = x => dtype_of_fam(motive, ctx, env, denv, DVBoolTy, x)
          match
            (
              d_check(tt, fam(DVBool(true)), ctx, env, denv),
              d_check(ff, fam(DVBool(false)), ctx, env, denv),
            ) {
            (Some(tv), Some(fv)) =>
              Some(DInfer::{
                value: eval_bool_elim(fam, tv, fv, sv, ddim_len(denv)),
                ty: fam(sv),
              })
            _ => None
          }
        }
        None => None
      }
    DBoolLit(b) => Some(DInfer::{ value: DVBool(b), ty: DVBoolTy, })
    DUnitLit => Some(DInfer::{ value: DVUnit, ty: DVUnitTy, })
    DAnn(inner, ty_term) =>
      match d_as_type(ty_term, ctx, env, denv) {
        Some(tv) =>
          match d_check(inner, tv.value, ctx, env, denv) {
            Some(v) => Some(DInfer::{ value: v, ty: tv.value, })
            None => None
          }
        None => None
      }
    DPathP(line, l, r) => {
      let fresh_dim = fresh_dim(denv)
      match d_as_type(line, ctx, env, ddim_cons(fresh_dim, denv)) {
        Some(lt) => {
          let line_fn = memo_dim_line(d => {
            dtype_of_line(line, ctx, env, denv, d)
          })
          match
            (
              d_check(l, line_fn(DZero), ctx, env, denv),
              d_check(r, line_fn(DOne), ctx, env, denv),
            ) {
            (Some(lv), Some(rv)) =>
              Some(DInfer::{
                value: DVPathTy(line_fn, lv, rv),
                ty: DVUniv(lt.level),
              })
            _ => None
          }
        }
        None => None
      }
    }
    DPath(a, l, r) =>
      match d_as_type(a, ctx, env, denv) {
        Some(at) =>
          match
            (
              d_check(l, at.value, ctx, env, denv),
              d_check(r, at.value, ctx, env, denv),
            ) {
            (Some(lv), Some(rv)) =>
              Some(DInfer::{
                value: DVPathTy(_ => at.value, lv, rv),
                ty: DVUniv(at.level),
              })
            _ => None
          }
        None => None
      }
    DLamDim(body) => {
      let fresh = fresh_dim(denv)
      match d_infer(body, ctx, env, ddim_cons(fresh, denv)) {
        Some(_) => {
          let line_fn = d => {
            dinfer_ty(d_infer(body, ctx, env, ddim_cons(d, denv)))
          }
          let lv = dinfer_value(d_infer(body, ctx, env, ddim_cons(DZero, denv)))
          let rv = dinfer_value(d_infer(body, ctx, env, ddim_cons(DOne, denv)))
          Some(DInfer::{
            value: DVPathLam(d => {
              dinfer_value(d_infer(body, ctx, env, ddim_cons(d, denv)))
            }),
            ty: DVPathTy(line_fn, lv, rv),
          })
        }
        None => None
      }
    }
    DAppDim(p, r) =>
      match d_infer(p, ctx, env, denv) {
        Some(pr) =>
          match as_path(pr.ty) {
            Some(parts) => {
              let rd = eval_dim_expr(r, denv)
              Some(DInfer::{
                value: dapp_dim(pr.value, rd),
                ty: (parts.line)(rd),
              })
            }
            None => None
          }
        None => None
      }
    DCoe(line, r, s, v) => {
      let line_fn = memo_dim_line(d => dtype_of_line(line, ctx, env, denv, d))
      let rd = eval_dim_expr(r, denv)
      let sd = eval_dim_expr(s, denv)
      match d_check(v, line_fn(rd), ctx, env, denv) {
        Some(vv) =>
          Some(DInfer::{
            value: coe_value(line_fn, rd, sd, vv, ddim_len(denv)),
            ty: line_fn(sd),
          })
        None => None
      }
    }
    DComp(line, tubes, base) => {
      let line_fn = memo_dim_line(d => dtype_of_line(line, ctx, env, denv, d))
      match d_checked_branches(tubes, line_fn, ctx, env, denv) {
        Some(branches) =>
          match d_check(base, line_fn(DZero), ctx, env, denv) {
            Some(bv) =>
              if d_system_compat(
                  env,
                  branches,
                  line_fn,
                  bv,
                  denv_len(ctx),
                  ddim_len(denv),
                ) {
                Some(DInfer::{
                  value: comp_value(line_fn, branches, bv, ddim_len(denv)),
                  ty: line_fn(DOne),
                })
              } else {
                None
              }
            None => None
          }
        None => None
      }
    }
    DHComp(a, tubes, base) | DHFill(a, tubes, base, _) =>
      match d_as_type(a, ctx, env, denv) {
        Some(at) =>
          match d_checked_branches(tubes, _ => at.value, ctx, env, denv) {
            Some(branches) =>
              match d_check(base, at.value, ctx, env, denv) {
                Some(bv) =>
                  if d_system_compat(
                      env,
                      branches,
                      _ => at.value,
                      bv,
                      denv_len(ctx),
                      ddim_len(denv),
                    ) {
                    let value = match t {
                      DHFill(_, _, _, r) =>
                        hfill_value(at.value, branches, bv, ddim_len(denv))(
                          eval_dim_expr(r, denv),
                        )
                      _ => hcomp_value(at.value, branches, bv, ddim_len(denv))
                    }
                    Some(DInfer::{ value, ty: at.value, })
                  } else {
                    None
                  }
                None => None
              }
            None => None
          }
        None => None
      }
    DNatTy => Some(DInfer::{ value: DVNatTy, ty: DVUniv(0), })
    DNatZero => Some(DInfer::{ value: DVZeroNat, ty: DVNatTy, })
    DSucc(n) =>
      match d_check(n, DVNatTy, ctx, env, denv) {
        Some(v) => Some(DInfer::{ value: DVSucc(v), ty: DVNatTy, })
        None => None
      }
    DNatElim(motive, z, s, scrut) =>
      match d_check(scrut, DVNatTy, ctx, env, denv) {
        Some(sv) => {
          let fam = x => dtype_of_fam(motive, ctx, env, denv, DVNatTy, x)
          let step_ty = DVPi(DVNatTy, n => DVPi(fam(n), _ => fam(DVSucc(n))))
          match
            (
              d_check(z, fam(DVZeroNat), ctx, env, denv),
              d_check(s, step_ty, ctx, env, denv),
            ) {
            (Some(zv), Some(sv2)) =>
              Some(DInfer::{
                value: eval_nat_elim(fam, zv, sv2, sv, ddim_len(denv)),
                ty: fam(sv),
              })
            _ => None
          }
        }
        None => None
      }
    DListTy(a) =>
      match d_as_type(a, ctx, env, denv) {
        Some(at) =>
          Some(DInfer::{ value: DVListTy(at.value), ty: DVUniv(at.level), })
        None => None
      }
    DCons(x, xs) =>
      match d_infer(xs, ctx, env, denv) {
        Some(xsr) =>
          match as_list_elem(xsr.ty) {
            Some(elem) =>
              match d_check(x, elem, ctx, env, denv) {
                Some(xv) =>
                  Some(DInfer::{
                    value: DVCons(xv, xsr.value),
                    ty: DVListTy(elem),
                  })
                None => None
              }
            None => None
          }
        None => None
      }
    DListElim(motive, z, s, scrut) =>
      match d_infer(scrut, ctx, env, denv) {
        Some(sr) =>
          match as_list_elem(sr.ty) {
            Some(elem) => {
              let list_ty = DVListTy(elem)
              let fam = x => dtype_of_fam(motive, ctx, env, denv, list_ty, x)
              let step_ty = DVPi(elem, x => {
                DVPi(list_ty, xs => DVPi(fam(xs), _ => fam(DVCons(x, xs))))
              })
              match
                (
                  d_check(z, fam(DVNil), ctx, env, denv),
                  d_check(s, step_ty, ctx, env, denv),
                ) {
                (Some(zv), Some(sv)) =>
                  Some(DInfer::{
                    value: eval_list_elim(
                      elem,
                      fam,
                      zv,
                      sv,
                      sr.value,
                      ddim_len(denv),
                    ),
                    ty: fam(sr.value),
                  })
                _ => None
              }
            }
            None => None
          }
        None => None
      }
    DCircleTy => Some(DInfer::{ value: DVCircleTy, ty: DVUniv(0), })
    DCircleBase =>
      Some(DInfer::{ value: DVCirclePoint(DZero), ty: DVCircleTy, })
    DCircleLoop =>
      Some(DInfer::{
        value: DVPathLam(d => circle_point(d)),
        ty: DVPathTy(
          _ => DVCircleTy,
          DVCirclePoint(DZero),
          DVCirclePoint(DZero),
        ),
      })
    DCircleElim(motive, b, l, scrut) =>
      match d_check(scrut, DVCircleTy, ctx, env, denv) {
        Some(sv) => {
          let fam = x => dtype_of_fam(motive, ctx, env, denv, DVCircleTy, x)
          match d_check(b, fam(DVCirclePoint(DZero)), ctx, env, denv) {
            Some(bv) => {
              let loop_ty = DVPathTy(d => fam(circle_point(d)), bv, bv)
              match d_check(l, loop_ty, ctx, env, denv) {
                Some(lv) =>
                  Some(DInfer::{
                    value: eval_circle_elim(fam, bv, lv, sv, ddim_len(denv)),
                    ty: fam(sv),
                  })
                None => None
              }
            }
            None => None
          }
        }
        None => None
      }
    DTorusTy => Some(DInfer::{ value: DVTorusTy, ty: DVUniv(0), })
    DTorusBase =>
      Some(DInfer::{ value: DVTorusPoint(DZero, DZero), ty: DVTorusTy, })
    DTorusLoopA =>
      Some(DInfer::{
        value: DVPathLam(d => torus_point(d, DZero)),
        ty: DVPathTy(
          _ => DVTorusTy,
          DVTorusPoint(DZero, DZero),
          DVTorusPoint(DZero, DZero),
        ),
      })
    DTorusLoopB =>
      Some(DInfer::{
        value: DVPathLam(d => torus_point(DZero, d)),
        ty: DVPathTy(
          _ => DVTorusTy,
          DVTorusPoint(DZero, DZero),
          DVTorusPoint(DZero, DZero),
        ),
      })
    DTorusSquare => {
      let loop_b : DValue = DVPathLam(d => torus_point(DZero, d))
      Some(DInfer::{
        value: DVPathLam(a => DVPathLam(b => torus_point(a, b))),
        ty: DVPathTy(
          a => {
            DVPathTy(
              _ => DVTorusTy,
              torus_point(a, DZero),
              torus_point(a, DZero),
            )
          },
          loop_b,
          loop_b,
        ),
      })
    }
    DTorusElim(motive, square, scrut) =>
      match d_check(scrut, DVTorusTy, ctx, env, denv) {
        Some(sv) => {
          let fam = x => dtype_of_fam(motive, ctx, env, denv, DVTorusTy, x)
          let fi = fresh_dim(denv)
          let fj = DVar(ddim_len(denv) + 1)
          match
            d_check(
              square,
              fam(torus_point(fi, fj)),
              ctx,
              env,
              ddim_cons(fj, ddim_cons(fi, denv)),
            ) {
            Some(_) => {
              let sq = (a : Dim, b : Dim) => {
                dv_unwrap(
                  d_check(
                    square,
                    fam(torus_point(a, b)),
                    ctx,
                    env,
                    ddim_cons(b, ddim_cons(a, denv)),
                  ),
                )
              }
              Some(DInfer::{
                value: eval_torus_elim(fam, sq, sv, ddim_len(denv)),
                ty: fam(sv),
              })
            }
            None => None
          }
        }
        None => None
      }
    DInductive(spec, args) => infer_inductive_type(spec, args, ctx, env, denv)
    DIntro(spec, ctor, params, args) =>
      infer_intro(spec, ctor, params, args, ctx, env, denv)
    DInductiveElim(spec, motive, cases, params, indices, scrut) =>
      infer_inductive_elim(
        spec, motive, cases, params, indices, scrut, ctx, env, denv,
      )
    DHitType(spec, args) => infer_hit_type(spec, args, ctx, env, denv)
    DHitIntro(spec, cell, params, args, dims) =>
      infer_hit_intro(spec, cell, params, args, dims, ctx, env, denv)
    DHitElim(spec, motive, cases, params, indices, scrut) =>
      infer_hit_elim(
        spec, motive, cases, params, indices, scrut, ctx, env, denv,
      )
    DDecode(spec, params, indices, code) =>
      infer_decode(spec, params, indices, code, ctx, env, denv)
    DEquivTy(a, b) => infer_equiv_ty(a, b, ctx, env, denv)
    DMkEquiv(a, b, f, g, sect, retr) =>
      infer_mk_equiv(a, b, f, g, sect, retr, ctx, env, denv)
    DEquivFwd(e) => infer_equiv_projection(0, e, ctx, env, denv)
    DEquivBwd(e) => infer_equiv_projection(1, e, ctx, env, denv)
    DEquivSect(e) => infer_equiv_projection(2, e, ctx, env, denv)
    DEquivRetr(e) => infer_equiv_projection(3, e, ctx, env, denv)
    DGlueEquiv(base, branches) =>
      infer_glue_equiv(base, branches, ctx, env, denv)
    DUnglueEquiv(term, base, branches) =>
      infer_unglue_equiv(term, base, branches, ctx, env, denv)
    DUa(e) => infer_ua(e, ctx, env, denv)
    DPair(_, _) | DNil | DPartial(_) => None // introduction forms are check-only
  }
}

///|
fn dtype_of_line(
  line : DTerm,
  ctx : DEnv,
  env : DEnv,
  denv : DDimEnv,
  d : Dim,
) -> DValue {
  match d_as_type(line, ctx, env, ddim_cons(d, denv)) {
    Some(tv) => tv.value
    None => DVUnitTy
  }
}

///|
fn d_check_glue_partial(
  a : DTerm,
  g : DGlueParts,
  ctx : DEnv,
  env : DEnv,
  denv : DDimEnv,
) -> Array[DValue]? {
  let values : Array[DValue] = []
  match a {
    DPartial(supplied) =>
      for i in 0..<g.system.branches.length() {
        let type_branch = g.system.branches[i]
        let mut body : DTerm = DUnitLit
        let mut found = false
        for k in 0..<supplied.length() {
          if same_face_sem(
              type_branch.face,
              face_eval_env(supplied[k].face, denv),
            ) {
            body = supplied[k].body
            found = true
            break
          }
        }
        if !found {
          return None
        }
        match d_check(body, (type_branch.path)(DOne), ctx, env, denv) {
          Some(v) => values.push(v)
          None => return None
        }
      }
    _ =>
      for i in 0..<g.system.branches.length() {
        let type_branch = g.system.branches[i]
        match d_check(a, (type_branch.path)(DOne), ctx, env, denv) {
          Some(v) => values.push(v)
          None => return None
        }
      }
  }
  Some(values)
}

///|
pub fn d_check(
  t : DTerm,
  expected0 : DValue,
  ctx : DEnv,
  env : DEnv,
  denv : DDimEnv,
) -> DValue? {
  // A Glue-by-equivalence type with a top branch is checked as the
  // corresponding partial type; with bottom domain it is the base.
  let expected = glue_equiv_collapse(expected0)
  match t {
    DLam(dom, body) =>
      match as_pi(expected) {
        Some(parts) =>
          match d_as_type(dom, ctx, env, denv) {
            Some(at) =>
              if conv_ty(denv_len(ctx), ddim_len(denv), at.value, parts.dom) {
                let fresh_x = reflect_var(denv_len(ctx), at.value)
                match
                  d_check(
                    body,
                    (parts.fam)(fresh_x),
                    denv_cons(at.value, ctx),
                    denv_cons(fresh_x, env),
                    denv,
                  ) {
                  Some(_) =>
                    Some(
                      DVLam(arg => deval_dim(body, denv_cons(arg, env), denv)),
                    )
                  None => None
                }
              } else {
                None
              }
            None => None
          }
        None => None
      }
    DPair(a, b) =>
      match as_sigma(expected) {
        Some(parts) =>
          match d_check(a, parts.dom, ctx, env, denv) {
            Some(av) =>
              match d_check(b, (parts.fam)(av), ctx, env, denv) {
                Some(bv) => Some(DVPair(av, bv))
                None => None
              }
            None => None
          }
        None =>
          match as_glue(expected) {
            Some(g) =>
              match
                (
                  d_check_glue_partial(a, g, ctx, env, denv),
                  d_check(b, g.base, ctx, env, denv),
                ) {
                (Some(partial_values), Some(bv)) => {
                  let mut ok = true
                  for i in 0..<partial_values.length() {
                    let branch = g.system.branches[i]
                    let fwd = coe_value(
                      branch.path,
                      DOne,
                      DZero,
                      partial_values[i],
                      ddim_len(denv),
                    )
                    if face_is_sat_sem(branch.face) &&
                      !conv_at(denv_len(ctx), ddim_len(denv), g.base, fwd, bv) {
                      ok = false
                    }
                  }
                  if ok {
                    Some(DVPair(glue_store_partial(g, partial_values), bv))
                  } else {
                    None
                  }
                }
                _ => None
              }
            None =>
              match as_glue_equiv(expected) {
                Some(g) =>
                  match
                    (
                      d_check_glue_equiv_partial(a, g, ctx, env, denv),
                      d_check(b, g.base, ctx, env, denv),
                    ) {
                    (Some(partial_values), Some(bv)) => {
                      let mut ok = true
                      for i in 0..<partial_values.length() {
                        let branch = g.branches[i]
                        let fwd = equiv_fun_value(
                          branch.equiv,
                          branch.ty,
                          g.base,
                          partial_values[i],
                        )
                        if !conv_at_under_face(
                            denv_len(ctx),
                            ddim_len(denv),
                            branch.face,
                            g.base,
                            fwd,
                            bv,
                          ) {
                          ok = false
                        }
                      }
                      if ok {
                        Some(
                          DVPair(
                            glue_equiv_store_partial(g, partial_values),
                            bv,
                          ),
                        )
                      } else {
                        None
                      }
                    }
                    _ => None
                  }
                None => None
              }
          }
      }
    DLamDim(body) =>
      match as_path(expected) {
        Some(parts) => {
          let fd = fresh_dim(denv)
          match d_check(body, (parts.line)(fd), ctx, env, ddim_cons(fd, denv)) {
            Some(_) => {
              let path_val = DVPathLam(d => {
                deval_dim(body, env, ddim_cons(d, denv))
              })
              let at0 = dapp_dim(path_val, DZero)
              let at1 = dapp_dim(path_val, DOne)
              if conv_at(
                  denv_len(ctx),
                  ddim_len(denv),
                  (parts.line)(DZero),
                  at0,
                  parts.left,
                ) &&
                conv_at(
                  denv_len(ctx),
                  ddim_len(denv),
                  (parts.line)(DOne),
                  at1,
                  parts.right,
                ) {
                Some(path_val)
              } else {
                None
              }
            }
            None => None
          }
        }
        None => None
      }
    DBoolLit(b) =>
      match force_value(expected) {
        DVBoolTy => Some(DVBool(b))
        _ => None
      }
    DUnitLit =>
      match force_value(expected) {
        DVUnitTy => Some(DVUnit)
        _ => None
      }
    DNatZero =>
      match force_value(expected) {
        DVNatTy => Some(DVZeroNat)
        _ => None
      }
    DNil =>
      match as_list_elem(expected) {
        Some(_) => Some(DVNil)
        None => None
      }
    DCons(x, xs) =>
      match as_list_elem(expected) {
        Some(elem) =>
          match
            (
              d_check(x, elem, ctx, env, denv),
              d_check(xs, expected, ctx, env, denv),
            ) {
            (Some(xv), Some(xsv)) => Some(DVCons(xv, xsv))
            _ => None
          }
        None => None
      }
    _ =>
      match d_infer(t, ctx, env, denv) {
        Some(r) => {
          let cumulative = match
            (as_univ_level(r.ty), as_univ_level(expected)) {
            (Some(a), Some(b)) => a <= b
            _ => false
          }
          if cumulative ||
            conv_ty(denv_len(ctx), ddim_len(denv), r.ty, expected) {
            Some(r.value)
          } else {
            None
          }
        }
        None => None
      }
  }
}

// ---------------------------------------------------------------------------
// Conversion and quoting (with dimension levels)
// ---------------------------------------------------------------------------

///|
fn glue_type_systems_conv(
  level : Int32,
  dlevel : Int32,
  a : DSystem,
  b : DSystem,
) -> Bool {
  let univ_line = (_ : Dim) => DVUniv(0)
  let ca = dsystem_canonical(level, dlevel, univ_line, a)
  let cb = dsystem_canonical(level, dlevel, univ_line, b)
  if ca.branches.length() != cb.branches.length() {
    return false
  }
  for i in 0..<ca.branches.length() {
    if !same_face_sem(ca.branches[i].face, cb.branches[i].face) ||
      !tube_paths_conv(
        level,
        dlevel,
        univ_line,
        ca.branches[i].path,
        cb.branches[i].path,
      ) {
      return false
    }
  }
  true
}

///|
pub fn conv_neutral(
  level : Int32,
  dlevel : Int32,
  a : DNeutral,
  b : DNeutral,
) -> Bool {
  match (a, b) {
    (DNVar(x), DNVar(y)) => x == y
    (DNApp(f, arg, arg_ty), DNApp(g, arg2, _)) =>
      conv_neutral(level, dlevel, f, g) &&
      conv_at(level, dlevel, arg_ty, arg, arg2)
    (DNFst(x, _), DNFst(y, _)) => conv_neutral(level, dlevel, x, y)
    (DNSnd(x, _, _), DNSnd(y, _, _)) => conv_neutral(level, dlevel, x, y)
    (DNAppDim(x, r), DNAppDim(y, s)) =>
      conv_neutral(level, dlevel, x, y) && dim_simplify(r) == dim_simplify(s)
    (DNBoolElim(m1, tt1, ff1, n1), DNBoolElim(m2, tt2, ff2, n2)) =>
      conv_neutral(level, dlevel, n1, n2) &&
      conv_ty(
        level + 1,
        dlevel,
        m1(DVNeutral(DNVar(level))),
        m2(DVNeutral(DNVar(level))),
      ) &&
      conv_at(level, dlevel, m1(DVBool(true)), tt1, tt2) &&
      conv_at(level, dlevel, m1(DVBool(false)), ff1, ff2)
    (DNNatElim(m1, z1, s1, n1), DNNatElim(m2, z2, s2, n2)) =>
      conv_neutral(level, dlevel, n1, n2) &&
      conv_ty(
        level + 1,
        dlevel,
        m1(DVNeutral(DNVar(level))),
        m2(DVNeutral(DNVar(level))),
      ) &&
      conv_at(level, dlevel, m1(DVZeroNat), z1, z2) &&
      conv_at(
        level,
        dlevel,
        DVPi(DVNatTy, n => DVPi(m1(n), _ => m1(DVSucc(n)))),
        s1,
        s2,
      )
    (DNListElim(e1, m1, z1, s1, n1), DNListElim(e2, m2, z2, s2, n2)) =>
      conv_ty(level, dlevel, e1, e2) &&
      conv_neutral(level, dlevel, n1, n2) &&
      conv_ty(
        level + 1,
        dlevel,
        m1(DVNeutral(DNVar(level))),
        m2(DVNeutral(DNVar(level))),
      ) &&
      conv_at(level, dlevel, m1(DVNil), z1, z2) &&
      conv_at(
        level,
        dlevel,
        DVPi(e1, x => {
          DVPi(DVListTy(e1), xs => DVPi(m1(xs), _ => m1(DVCons(x, xs))))
        }),
        s1,
        s2,
      )
    (DNCircleElim(m1, b1, l1, n1), DNCircleElim(m2, b2, l2, n2)) =>
      conv_neutral(level, dlevel, n1, n2) &&
      conv_ty(
        level + 1,
        dlevel,
        m1(DVNeutral(DNVar(level))),
        m2(DVNeutral(DNVar(level))),
      ) &&
      conv_at(level, dlevel, m1(DVCirclePoint(DZero)), b1, b2) &&
      conv_at(level, dlevel, DVPathTy(d => m1(circle_point(d)), b1, b1), l1, l2)
    (DNTorusElim(m1, q1, n1), DNTorusElim(m2, q2, n2)) => {
      let fi = DVar(dlevel)
      let fj = DVar(dlevel + 1)
      conv_neutral(level, dlevel, n1, n2) &&
      conv_ty(
        level + 1,
        dlevel,
        m1(DVNeutral(DNVar(level))),
        m2(DVNeutral(DNVar(level))),
      ) &&
      conv_at(
        level,
        dlevel + 2,
        m1(torus_point(fi, fj)),
        q1(fi, fj),
        q2(fi, fj),
      )
    }
    (DNHComp(t1, branches1, base1), DNHComp(t2, branches2, base2)) => {
      let line = (_ : Dim) => t1
      let sys1 = dsystem_canonical(level, dlevel, line, branches1)
      let sys2 = dsystem_canonical(level, dlevel, line, branches2)
      let mut ok = conv_ty(level, dlevel, t1, t2) &&
        conv_at(level, dlevel, t1, base1, base2) &&
        sys1.branches.length() == sys2.branches.length()
      for i in 0..<sys1.branches.length() {
        if i < sys2.branches.length() &&
          (
            !same_face_sem(sys1.branches[i].face, sys2.branches[i].face) ||
            !tube_paths_conv(
              level,
              dlevel,
              line,
              sys1.branches[i].path,
              sys2.branches[i].path,
            )
          ) {
          ok = false
        }
      }
      ok
    }
    (
      DNInductiveElim(s1, m1, c1, p1, i1, n1),
      DNInductiveElim(s2, m2, c2, p2, i2, n2),
    ) =>
      conv_inductive_elim_neutral(
        level, dlevel, s1, m1, c1, p1, i1, n1, s2, m2, c2, p2, i2, n2,
      )
    (DNHitElim(s1, m1, c1, p1, i1, n1), DNHitElim(s2, m2, c2, p2, i2, n2)) =>
      conv_hit_elim_neutral(
        level, dlevel, s1, m1, c1, p1, i1, n1, s2, m2, c2, p2, i2, n2,
      )
    (DNDecode(s1, p1, i1, n1), DNDecode(s2, p2, i2, n2)) =>
      conv_decode_neutral(level, dlevel, s1, p1, i1, n1, s2, p2, i2, n2)
    (DNEquivFwd(x, _, _), DNEquivFwd(y, _, _)) =>
      conv_neutral(level, dlevel, x, y)
    (DNEquivBwd(x, _, _), DNEquivBwd(y, _, _)) =>
      conv_neutral(level, dlevel, x, y)
    (DNEquivSect(x, _, _), DNEquivSect(y, _, _)) =>
      conv_neutral(level, dlevel, x, y)
    (DNEquivRetr(x, _, _), DNEquivRetr(y, _, _)) =>
      conv_neutral(level, dlevel, x, y)
    (DNEquivAnn(x, _, _), y) => conv_neutral(level, dlevel, x, y)
    (x, DNEquivAnn(y, _, _)) => conv_neutral(level, dlevel, x, y)
    (DNUnglueEquiv(x, _), DNUnglueEquiv(y, _)) =>
      conv_neutral(level, dlevel, x, y)
    (DNComp(line, branches, base), DNComp(line2, branches2, base2)) => {
      let sys1 = dsystem_canonical(level, dlevel, line, branches)
      let sys2 = dsystem_canonical(level, dlevel, line2, branches2)
      let mut ok = conv_ty(
          level,
          dlevel + 1,
          line(DVar(dlevel)),
          line2(DVar(dlevel)),
        ) &&
        conv_at(level, dlevel, line(DZero), base, base2) &&
        sys1.branches.length() == sys2.branches.length()
      for i in 0..<sys1.branches.length() {
        if i < sys2.branches.length() &&
          (
            !same_face_sem(sys1.branches[i].face, sys2.branches[i].face) ||
            !tube_paths_conv(
              level,
              dlevel,
              line,
              sys1.branches[i].path,
              sys2.branches[i].path,
            )
          ) {
          ok = false
        }
      }
      ok
    }
    _ => false
  }
}

///|
pub fn conv_at(
  level : Int32,
  dlevel : Int32,
  ty : DValue,
  a : DValue,
  b : DValue,
) -> Bool {
  let ty = force_value(ty)
  let a = force_value(a)
  let b = force_value(b)
  match (a, b) {
    (DVPartial(x), DVPartial(y)) =>
      return partial_eq_at(level, dlevel, ty, x, y)
    _ => ()
  }
  match ty {
    DVUniv(_) => conv_ty(level, dlevel, a, b)
    DVBoolTy =>
      match (a, b) {
        (DVBool(x), DVBool(y)) => x == y
        (DVNeutral(x), DVNeutral(y)) => conv_neutral(level, dlevel, x, y)
        _ => false
      }
    DVUnitTy => true
    DVPi(dom, fam) => {
      let fresh = reflect_var(level, dom)
      conv_at(
        level + 1,
        dlevel,
        fam(fresh),
        dapp_typed(a, fresh, dom),
        dapp_typed(b, fresh, dom),
      )
    }
    DVSigma(dom, fam) => {
      let fa = dfst_typed(a, fam)
      conv_at(level, dlevel, dom, fa, dfst_typed(b, fam)) &&
      conv_at(
        level,
        dlevel,
        fam(fa),
        dsnd_typed(a, dom, fam),
        dsnd_typed(b, dom, fam),
      )
    }
    DVPathTy(line, _, _) => {
      let fresh = DVar(dlevel)
      conv_at(
        level,
        dlevel + 1,
        line(fresh),
        dapp_dim(a, fresh),
        dapp_dim(b, fresh),
      )
    }
    DVNatTy =>
      match (a, b) {
        (DVZeroNat, DVZeroNat) => true
        (DVSucc(x), DVSucc(y)) => conv_at(level, dlevel, ty, x, y)
        (DVNeutral(x), DVNeutral(y)) => conv_neutral(level, dlevel, x, y)
        _ => false
      }
    DVListTy(elem) =>
      match (a, b) {
        (DVNil, DVNil) => true
        (DVCons(x, xs), DVCons(y, ys)) =>
          conv_at(level, dlevel, elem, x, y) &&
          conv_at(level, dlevel, ty, xs, ys)
        (DVNeutral(x), DVNeutral(y)) => conv_neutral(level, dlevel, x, y)
        _ => false
      }
    DVInductive(spec, params, _) =>
      conv_intro_at(level, dlevel, spec, params, a, b)
    DVHitType(spec, params, _) =>
      conv_hit_cell_at(level, dlevel, spec, params, a, b)
    DVCircleTy =>
      match (a, b) {
        (DVCirclePoint(r), DVCirclePoint(s)) => {
          let rr = circle_dim_of(circle_point(r))
          let ss = circle_dim_of(circle_point(s))
          dim_eq_sem(rr, ss)
        }
        (DVNeutral(x), DVNeutral(y)) => conv_neutral(level, dlevel, x, y)
        _ => false
      }
    DVTorusTy =>
      match (a, b) {
        (DVTorusPoint(r1, r2), DVTorusPoint(s1, s2)) => {
          let (ra, rb) = torus_dims_of(torus_point(r1, r2))
          let (sa, sb) = torus_dims_of(torus_point(s1, s2))
          dim_eq_sem(ra, sa) && dim_eq_sem(rb, sb)
        }
        (DVNeutral(x), DVNeutral(y)) => conv_neutral(level, dlevel, x, y)
        _ => false
      }
    DVEquivTy(src, dst, _) =>
      match (a, b) {
        (DVNeutral(x), DVNeutral(y)) => conv_neutral(level, dlevel, x, y)
        // isEquiv data is propositional: conversion compares the
        // two functions, not the chosen section/retraction proofs.
        _ => {
          let pa = equiv_parts(a, src, dst)
          let pb = equiv_parts(b, src, dst)
          let a_ok = match a {
            DVEquiv(_, _, _, _, _, _) | DVNeutral(_) => true
            _ => false
          }
          let b_ok = match b {
            DVEquiv(_, _, _, _, _, _) | DVNeutral(_) => true
            _ => false
          }
          a_ok &&
          b_ok &&
          conv_at(level, dlevel, DVPi(src, _ => dst), pa.fwd, pb.fwd) &&
          conv_at(level, dlevel, DVPi(dst, _ => src), pa.bwd, pb.bwd)
        }
      }
    DVGlueEquiv(branches, base, lvl) =>
      match (a, b) {
        (DVNeutral(x), DVNeutral(y)) => conv_neutral(level, dlevel, x, y)
        _ => {
          let parts = DGlueEquivParts::{
            branches,
            face: glue_equiv_domain_face(branches),
            base,
            level: lvl,
          }
          let partial_a = glue_equiv_partial_values(parts, a)
          let partial_b = glue_equiv_partial_values(parts, b)
          let mut ok = partial_a.length() == partial_b.length()
          for i in 0..<partial_a.length() {
            if i < partial_b.length() &&
              !conv_at(
                level,
                dlevel,
                branches[i].ty,
                partial_a[i],
                partial_b[i],
              ) {
              ok = false
            }
          }
          ok &&
          conv_at(
            level,
            dlevel,
            base,
            glue_equiv_base_of(parts, a),
            glue_equiv_base_of(parts, b),
          )
        }
      }
    DVGlue(system, base, _) => {
      let parts = DGlueParts::{
        system,
        face: dsystem_domain_face(system),
        line: dsystem_first_path(system, base),
        base,
        level: 0,
      }
      let pa = dfst_typed(a, _ => base)
      let pb = dfst_typed(b, _ => base)
      let partial_a = glue_partial_values(parts, pa)
      let partial_b = glue_partial_values(parts, pb)
      let mut ok = partial_a.length() == partial_b.length()
      for i in 0..<partial_a.length() {
        if i < partial_b.length() &&
          !conv_at(
            level,
            dlevel,
            (system.branches[i].path)(DOne),
            partial_a[i],
            partial_b[i],
          ) {
          ok = false
        }
      }
      let first_ty = (parts.line)(DOne)
      ok &&
      conv_at(
        level,
        dlevel,
        base,
        dsnd_typed(a, first_ty, _ => base),
        dsnd_typed(b, first_ty, _ => base),
      )
    }
    DVNeutral(_) =>
      match (a, b) {
        (DVNeutral(x), DVNeutral(y)) => conv_neutral(level, dlevel, x, y)
        (DVBool(x), DVBool(y)) => x == y
        (DVUnit, DVUnit) => true
        (DVZeroNat, DVZeroNat) => true
        (DVSucc(x), DVSucc(y)) => conv_at(level, dlevel, DVNatTy, x, y)
        (DVCirclePoint(_), DVCirclePoint(_)) =>
          conv_at(level, dlevel, DVCircleTy, a, b)
        (DVTorusPoint(_, _), DVTorusPoint(_, _)) =>
          conv_at(level, dlevel, DVTorusTy, a, b)
        (DVIntro(s1, c1, p1, args1), DVIntro(s2, c2, _, _)) =>
          if s1 == s2 && c1 >= 0 && c1 < s1.constructors.length() && c2 >= 0 {
            conv_at(
              level,
              dlevel,
              DVInductive(
                s1,
                p1,
                inductive_result_indices(s1.constructors[c1], p1, args1),
              ),
              a,
              b,
            )
          } else {
            false
          }
        (DVHitCell(s1, c1, p1, args1, _), DVHitCell(s2, _, _, _, _)) =>
          if s1 == s2 && c1 >= 0 && c1 < s1.cells.length() {
            conv_at(
              level,
              dlevel,
              DVHitType(s1, p1, hit_cell_result_indices(s1, c1, p1, args1)),
              a,
              b,
            )
          } else {
            false
          }
        (DVEquiv(src, dst, _, _, _, _), DVEquiv(_, _, _, _, _, _)) =>
          conv_at(level, dlevel, DVEquivTy(src, dst, 0), a, b)
        _ => false
      }
    _ => false
  }
}

///|
pub fn conv_ty(level : Int32, dlevel : Int32, a : DValue, b : DValue) -> Bool {
  let a = force_value(a)
  let b = force_value(b)
  match (a, b) {
    (DVUniv(x), DVUniv(y)) => x == y
    (DVBoolTy, DVBoolTy) => true
    (DVUnitTy, DVUnitTy) => true
    (DVPi(a1, f1), DVPi(a2, f2)) => {
      let fresh = reflect_var(level, a1)
      conv_ty(level, dlevel, a1, a2) &&
      conv_ty(level + 1, dlevel, f1(fresh), f2(fresh))
    }
    (DVSigma(a1, f1), DVSigma(a2, f2)) => {
      let fresh = reflect_var(level, a1)
      conv_ty(level, dlevel, a1, a2) &&
      conv_ty(level + 1, dlevel, f1(fresh), f2(fresh))
    }
    (DVPathTy(l1, x1, y1), DVPathTy(l2, x2, y2)) => {
      let fresh = DVar(dlevel)
      conv_ty(level, dlevel + 1, l1(fresh), l2(fresh)) &&
      conv_at(level, dlevel, l1(DZero), x1, x2) &&
      conv_at(level, dlevel, l1(DOne), y1, y2)
    }
    (DVNatTy, DVNatTy) => true
    (DVListTy(x), DVListTy(y)) => conv_ty(level, dlevel, x, y)
    (DVInductive(s1, p1, i1), DVInductive(s2, p2, i2)) =>
      conv_inductive_type(level, dlevel, s1, p1, i1, s2, p2, i2)
    (DVHitType(s1, p1, i1), DVHitType(s2, p2, i2)) =>
      conv_hit_type(level, dlevel, s1, p1, i1, s2, p2, i2)
    (DVCircleTy, DVCircleTy) => true
    (DVTorusTy, DVTorusTy) => true
    (DVEquivTy(a1, b1, _), DVEquivTy(a2, b2, _)) =>
      conv_ty(level, dlevel, a1, a2) && conv_ty(level, dlevel, b1, b2)
    (DVGlueEquiv(br1, b1, _), DVGlueEquiv(br2, b2, _)) =>
      match (glue_equiv_collapse(a), glue_equiv_collapse(b)) {
        (DVGlueEquiv(_, _, _), DVGlueEquiv(_, _, _)) =>
          conv_ty(level, dlevel, b1, b2) &&
          glue_equiv_systems_conv(level, dlevel, b1, br1, br2)
        (x, y) => conv_ty(level, dlevel, x, y)
      }
    (DVGlueEquiv(_, _, _), _) =>
      match glue_equiv_collapse(a) {
        DVGlueEquiv(_, _, _) => false
        x => conv_ty(level, dlevel, x, b)
      }
    (_, DVGlueEquiv(_, _, _)) =>
      match glue_equiv_collapse(b) {
        DVGlueEquiv(_, _, _) => false
        y => conv_ty(level, dlevel, a, y)
      }
    (DVGlue(s1, b1, _), DVGlue(s2, b2, _)) =>
      conv_ty(level, dlevel, b1, b2) &&
      glue_type_systems_conv(level, dlevel, s1, s2)
    (DVNeutral(x), DVNeutral(y)) => conv_neutral(level, dlevel, x, y)
    _ => false
  }
}

///|
pub fn quote_tube_branches(
  level : Int32,
  dlevel : Int32,
  line : (Dim) -> DValue,
  branches0 : DSystem,
) -> Array[DTubeTerm] {
  let (branches, quoted) = dsystem_canonical_quoted(
    level, dlevel, line, branches0,
  )
  let out : Array[DTubeTerm] = []
  for i in 0..<branches.branches.length() {
    let br = branches.branches[i]
    out.push(d_tube(face_quote(br.face, dlevel), quoted[i]))
  }
  out
}

///|
pub fn quote_dneutral(
  level : Int32,
  dlevel : Int32,
  n : DNeutral,
  ty : DValue,
) -> DTerm {
  match n {
    DNVar(l) => DTVar(level - 1 - l)
    DNApp(f, arg, arg_ty) =>
      DApp(
        quote_dneutral(level, dlevel, f, DVPi(arg_ty, _ => ty)),
        quote_at(level, dlevel, arg_ty, arg),
      )
    DNFst(inner, fam) =>
      DFst(quote_dneutral(level, dlevel, inner, DVSigma(ty, fam)))
    DNSnd(inner, fst_ty, fam) =>
      DSnd(quote_dneutral(level, dlevel, inner, DVSigma(fst_ty, fam)))
    DNAppDim(inner, r) => {
      let path_ty = DVPathTy(_ => ty, DVUnit, DVUnit)
      DAppDim(
        quote_dneutral(level, dlevel, inner, path_ty),
        dim_quote(r, dlevel),
      )
    }
    DNBoolElim(motive, tt, ff, scrut) => {
      let mot_body = quote_ty(
        level + 1,
        dlevel,
        motive(DVNeutral(DNVar(level))),
      )
      DBoolElim(
        mot_body,
        quote_at(level, dlevel, motive(DVBool(true)), tt),
        quote_at(level, dlevel, motive(DVBool(false)), ff),
        quote_dneutral(level, dlevel, scrut, DVBoolTy),
      )
    }
    DNNatElim(motive, z, s, scrut) => {
      let mot_body = quote_ty(
        level + 1,
        dlevel,
        motive(DVNeutral(DNVar(level))),
      )
      let step_ty = DVPi(DVNatTy, n => DVPi(motive(n), _ => motive(DVSucc(n))))
      DNatElim(
        mot_body,
        quote_at(level, dlevel, motive(DVZeroNat), z),
        quote_at(level, dlevel, step_ty, s),
        quote_dneutral(level, dlevel, scrut, DVNatTy),
      )
    }
    DNListElim(elem, motive, z, s, scrut) => {
      let list_ty = DVListTy(elem)
      let mot_body = quote_ty(
        level + 1,
        dlevel,
        motive(DVNeutral(DNVar(level))),
      )
      let step_ty = DVPi(elem, x => {
        DVPi(list_ty, xs => DVPi(motive(xs), _ => motive(DVCons(x, xs))))
      })
      DListElim(
        mot_body,
        quote_at(level, dlevel, motive(DVNil), z),
        quote_at(level, dlevel, step_ty, s),
        quote_dneutral(level, dlevel, scrut, list_ty),
      )
    }
    DNCircleElim(motive, b, l, scrut) => {
      let mot_body = quote_ty(
        level + 1,
        dlevel,
        motive(DVNeutral(DNVar(level))),
      )
      let base_pt = DVCirclePoint(DZero)
      let loop_ty = DVPathTy(d => motive(circle_point(d)), b, b)
      DCircleElim(
        mot_body,
        quote_at(level, dlevel, motive(base_pt), b),
        quote_at(level, dlevel, loop_ty, l),
        quote_dneutral(level, dlevel, scrut, DVCircleTy),
      )
    }
    DNTorusElim(motive, square, scrut) => {
      let mot_body = quote_ty(
        level + 1,
        dlevel,
        motive(DVNeutral(DNVar(level))),
      )
      let fi = DVar(dlevel)
      let fj = DVar(dlevel + 1)
      let sq_body = quote_at(
        level,
        dlevel + 2,
        motive(torus_point(fi, fj)),
        square(fi, fj),
      )
      DTorusElim(
        mot_body,
        sq_body,
        quote_dneutral(level, dlevel, scrut, DVTorusTy),
      )
    }
    DNInductiveElim(spec, motive, cases, params, indices, scrut) =>
      quote_inductive_elim_neutral(
        level, dlevel, spec, motive, cases, params, indices, scrut,
      )
    DNHitElim(spec, motive, cases, params, indices, scrut) =>
      quote_hit_elim_neutral(
        level, dlevel, spec, motive, cases, params, indices, scrut,
      )
    DNDecode(spec, params, indices, code) =>
      quote_decode_neutral(level, dlevel, spec, params, indices, code)
    DNEquivFwd(inner, src, dst) =>
      DEquivFwd(quote_dneutral(level, dlevel, inner, DVEquivTy(src, dst, 0)))
    DNEquivBwd(inner, src, dst) =>
      DEquivBwd(quote_dneutral(level, dlevel, inner, DVEquivTy(src, dst, 0)))
    DNEquivSect(inner, src, dst) =>
      DEquivSect(quote_dneutral(level, dlevel, inner, DVEquivTy(src, dst, 0)))
    DNEquivRetr(inner, src, dst) =>
      DEquivRetr(quote_dneutral(level, dlevel, inner, DVEquivTy(src, dst, 0)))
    DNEquivAnn(inner, _, _) => quote_dneutral(level, dlevel, inner, ty)
    DNUnglueEquiv(inner, parts) =>
      quote_unglue_equiv_neutral(level, dlevel, inner, parts)
    DNComp(line, branches, base) => {
      let line_body = quote_ty(level, dlevel + 1, line(DVar(dlevel)))
      let base_term = quote_at(level, dlevel, line(DZero), base)
      if branches.branches.length() == 0 {
        DCoe(line_body, DZero, DOne, base_term)
      } else {
        DComp(
          line_body,
          quote_tube_branches(level, dlevel, line, branches),
          base_term,
        )
      }
    }
    DNHComp(hty, branches, base) => {
      let base_term = quote_at(level, dlevel, hty, base)
      if branches.branches.length() == 0 {
        base_term
      } else {
        DHComp(
          quote_ty(level, dlevel, hty),
          quote_tube_branches(level, dlevel, _ => hty, branches),
          base_term,
        )
      }
    }
  }
}

///|
pub fn quote_ty(level : Int32, dlevel : Int32, ty : DValue) -> DTerm {
  match force_value(ty) {
    DVUniv(l) => DUniv(l)
    DVBoolTy => DBoolTy
    DVUnitTy => DUnitTy
    DVPi(a, fam) =>
      DPi(
        quote_ty(level, dlevel, a),
        quote_ty(level + 1, dlevel, fam(reflect_var(level, a))),
      )
    DVSigma(a, fam) =>
      DSigma(
        quote_ty(level, dlevel, a),
        quote_ty(level + 1, dlevel, fam(reflect_var(level, a))),
      )
    DVPathTy(line, l, r) =>
      DPathP(
        quote_ty(level, dlevel + 1, line(DVar(dlevel))),
        quote_at(level, dlevel, line(DZero), l),
        quote_at(level, dlevel, line(DOne), r),
      )
    DVNatTy => DNatTy
    DVListTy(a) => DListTy(quote_ty(level, dlevel, a))
    DVInductive(spec, params, indices) =>
      quote_inductive_type(level, dlevel, spec, params, indices)
    DVHitType(spec, params, indices) =>
      quote_hit_type(level, dlevel, spec, params, indices)
    DVCircleTy => DCircleTy
    DVTorusTy => DTorusTy
    DVEquivTy(a, b, _) =>
      DEquivTy(quote_ty(level, dlevel, a), quote_ty(level, dlevel, b))
    DVGlueEquiv(branches, base, lvl) =>
      // Quoting preserves the primitive Glue-by-equivalence syntax
      // even when the type is convertible to a branch or the base
      // (top/bottom collapse is a conversion, not a quote rule).
      quote_glue_equiv_type(level, dlevel, DGlueEquivParts::{
        branches,
        face: glue_equiv_domain_face(branches),
        base,
        level: lvl,
      })
    DVGlue(system, base, lvl) =>
      DHComp(
        DUniv(lvl),
        quote_tube_branches(level, dlevel, _ => DVUniv(lvl), system),
        quote_ty(level, dlevel, base),
      )
    DVNeutral(n) => quote_dneutral(level, dlevel, n, DVUniv(0))
    _ => DUnitTy
  }
}

///|
pub fn quote_at(
  level : Int32,
  dlevel : Int32,
  ty : DValue,
  v : DValue,
) -> DTerm {
  let ty = force_value(ty)
  let v = force_value(v)
  match v {
    DVPartial(p) => {
      let out : Array[DFaceTerm] = []
      for i in 0..<p.branches.length() {
        let br = p.branches[i]
        out.push(
          d_face_term(
            face_quote(br.face, dlevel),
            quote_at(level, dlevel, ty, br.value),
          ),
        )
      }
      return DPartial(out)
    }
    _ => ()
  }
  match ty {
    DVUniv(_) => quote_ty(level, dlevel, v)
    DVBoolTy =>
      match v {
        DVBool(b) => DBoolLit(b)
        DVNeutral(n) => quote_dneutral(level, dlevel, n, ty)
        _ => DUnitLit
      }
    DVUnitTy => DUnitLit
    DVPi(dom, fam) => {
      let fresh = reflect_var(level, dom)
      DLam(
        quote_ty(level, dlevel, dom),
        quote_at(level + 1, dlevel, fam(fresh), dapp_typed(v, fresh, dom)),
      )
    }
    DVSigma(dom, fam) => {
      let fst_val = dfst_typed(v, fam)
      DPair(
        quote_at(level, dlevel, dom, fst_val),
        quote_at(level, dlevel, fam(fst_val), dsnd_typed(v, dom, fam)),
      )
    }
    DVPathTy(line, _, _) => {
      let fresh = DVar(dlevel)
      DLamDim(quote_at(level, dlevel + 1, line(fresh), dapp_dim(v, fresh)))
    }
    DVNatTy =>
      match v {
        DVZeroNat => DNatZero
        DVSucc(n) => DSucc(quote_at(level, dlevel, ty, n))
        DVNeutral(n) => quote_dneutral(level, dlevel, n, ty)
        _ => DNatZero
      }
    DVListTy(elem) =>
      match v {
        DVNil => DNil
        DVCons(x, xs) =>
          DCons(
            quote_at(level, dlevel, elem, x),
            quote_at(level, dlevel, ty, xs),
          )
        DVNeutral(n) => quote_dneutral(level, dlevel, n, ty)
        _ => DNil
      }
    DVInductive(spec, params, _) =>
      quote_intro_at(level, dlevel, spec, params, ty, v)
    DVHitType(spec, params, _) =>
      quote_hit_cell_at(level, dlevel, spec, params, ty, v)
    DVCircleTy =>
      match v {
        DVCirclePoint(r) =>
          match circle_point(r) {
            DVCirclePoint(DZero) => DCircleBase
            _ => DAppDim(DCircleLoop, dim_quote(r, dlevel))
          }
        DVNeutral(n) => quote_dneutral(level, dlevel, n, ty)
        _ => DCircleBase
      }
    DVTorusTy =>
      match v {
        DVTorusPoint(a, b) =>
          match torus_point(a, b) {
            DVTorusPoint(DZero, DZero) => DTorusBase
            _ =>
              DAppDim(
                DAppDim(DTorusSquare, dim_quote(a, dlevel)),
                dim_quote(b, dlevel),
              )
          }
        DVNeutral(n) => quote_dneutral(level, dlevel, n, ty)
        _ => DTorusBase
      }
    DVEquivTy(src, dst, _) =>
      match v {
        DVEquiv(_, _, f, g, sect, retr) =>
          DMkEquiv(
            quote_ty(level, dlevel, src),
            quote_ty(level, dlevel, dst),
            quote_at(level, dlevel, DVPi(src, _ => dst), f),
            quote_at(level, dlevel, DVPi(dst, _ => src), g),
            quote_at(level, dlevel, equiv_sect_type(src, dst, f, g), sect),
            quote_at(level, dlevel, equiv_retr_type(src, dst, f, g), retr),
          )
        DVNeutral(n) => quote_dneutral(level, dlevel, n, ty)
        _ => DUnitLit
      }
    DVGlueEquiv(branches, base, lvl) => {
      let parts = DGlueEquivParts::{
        branches,
        face: glue_equiv_domain_face(branches),
        base,
        level: lvl,
      }
      let top = glue_equiv_top_index(parts)
      if top >= 0 {
        let values = glue_equiv_partial_values(parts, v)
        quote_at(level, dlevel, branches[top].ty, values[top])
      } else if face_is_bot_sem(parts.face) {
        quote_at(level, dlevel, base, glue_equiv_base_of(parts, v))
      } else {
        match force_value(v) {
          DVNeutral(n) => quote_dneutral(level, dlevel, n, ty)
          _ => {
            let values = glue_equiv_partial_values(parts, v)
            let base_term = quote_at(
              level,
              dlevel,
              base,
              glue_equiv_base_of(parts, v),
            )
            if branches.length() <= 1 {
              let partial = if values.length() > 0 { values[0] } else { DVUnit }
              let partial_ty = if branches.length() > 0 {
                branches[0].ty
              } else {
                DVUnitTy
              }
              DPair(quote_at(level, dlevel, partial_ty, partial), base_term)
            } else {
              let face_terms : Array[DFaceTerm] = []
              for i in 0..<branches.length() {
                let value = if i < values.length() { values[i] } else { DVUnit }
                face_terms.push(
                  d_face_term(
                    face_quote(branches[i].face, dlevel),
                    quote_at(level, dlevel, branches[i].ty, value),
                  ),
                )
              }
              DPair(DPartial(face_terms), base_term)
            }
          }
        }
      }
    }
    DVGlue(system, base, _) => {
      let parts = DGlueParts::{
        system,
        face: dsystem_domain_face(system),
        line: dsystem_first_path(system, base),
        base,
        level: 0,
      }
      let stored = dfst_typed(v, _ => base)
      let base_term = quote_at(
        level,
        dlevel,
        base,
        dsnd_typed(v, (parts.line)(DOne), _ => base),
      )
      if system.branches.length() <= 1 {
        DPair(quote_at(level, dlevel, (parts.line)(DOne), stored), base_term)
      } else {
        let values = glue_partial_values(parts, stored)
        let branches : Array[DFaceTerm] = []
        for i in 0..<system.branches.length() {
          let br = system.branches[i]
          let value = if i < values.length() { values[i] } else { DVUnit }
          branches.push(
            d_face_term(
              face_quote(br.face, dlevel),
              quote_at(level, dlevel, (br.path)(DOne), value),
            ),
          )
        }
        DPair(DPartial(branches), base_term)
      }
    }
    DVNeutral(_) =>
      match v {
        DVNeutral(n) => quote_dneutral(level, dlevel, n, ty)
        DVBool(b) => DBoolLit(b)
        DVZeroNat | DVSucc(_) => quote_at(level, dlevel, DVNatTy, v)
        DVCirclePoint(_) => quote_at(level, dlevel, DVCircleTy, v)
        DVTorusPoint(_, _) => quote_at(level, dlevel, DVTorusTy, v)
        DVIntro(spec, c, params, args) =>
          if c >= 0 && c < spec.constructors.length() {
            quote_intro_at(
              level,
              dlevel,
              spec,
              params,
              DVInductive(
                spec,
                params,
                inductive_result_indices(spec.constructors[c], params, args),
              ),
              v,
            )
          } else {
            DUnitLit
          }
        DVHitCell(spec, c, params, args, _) =>
          quote_hit_cell_at(
            level,
            dlevel,
            spec,
            params,
            DVHitType(
              spec,
              params,
              hit_cell_result_indices(spec, c, params, args),
            ),
            v,
          )
        DVEquiv(src, dst, _, _, _, _) =>
          quote_at(level, dlevel, DVEquivTy(src, dst, 0), v)
        _ => DUnitLit
      }
    _ => DUnitLit
  }
}

// ---------------------------------------------------------------------------
// Closed-term API and embedding
// ---------------------------------------------------------------------------

///|
pub fn dep_type_val_of(ty_term : DTerm) -> DTypeVal? {
  d_as_type(ty_term, denv_empty(), denv_empty(), ddim_empty())
}

///|
pub fn dep_check_closed(t : DTerm, ty_term : DTerm) -> Bool {
  match dep_type_val_of(ty_term) {
    Some(tv) =>
      match d_check(t, tv.value, denv_empty(), denv_empty(), ddim_empty()) {
        Some(_) => true
        None => false
      }
    None => false
  }
}

///|
pub fn dep_nf_closed(t : DTerm, ty_term : DTerm) -> DTerm? {
  match dep_type_val_of(ty_term) {
    Some(tv) =>
      match d_check(t, tv.value, denv_empty(), denv_empty(), ddim_empty()) {
        Some(v) => Some(quote_at(0, 0, tv.value, v))
        None => None
      }
    None => None
  }
}

///|
pub fn dep_type_of_closed(t : DTerm) -> DTerm? {
  match d_infer(t, denv_empty(), denv_empty(), ddim_empty()) {
    Some(r) => Some(quote_ty(0, 0, r.ty))
    None => None
  }
}

///|
pub fn dep_def_eq_closed(t : DTerm, u : DTerm, ty_term : DTerm) -> Bool {
  match (dep_nf_closed(t, ty_term), dep_nf_closed(u, ty_term)) {
    (Some(a), Some(b)) => a == b
    _ => false
  }
}

///|
/// Simply-typed embedding: functions become Pi, products become Sigma.
pub fn lty_to_dterm(ty : LTy) -> DTerm {
  match ty {
    LBool => DBoolTy
    LUnit => DUnitTy
    LProd(a, b) => DSigma(lty_to_dterm(a), lty_to_dterm(b))
    LFun(a, b) => DPi(lty_to_dterm(a), lty_to_dterm(b))
  }
}

// ---------------------------------------------------------------------------
// Laws / examples
// ---------------------------------------------------------------------------

///|
pub fn dep_id_type() -> DTerm {
  DPi(DUniv(0), DPi(DTVar(0), DTVar(1)))
}

///|
pub fn dep_id_term() -> DTerm {
  DLam(DUniv(0), DLam(DTVar(0), DTVar(0)))
}

///|
pub fn check_dep_universe() -> Bool {
  dep_type_of_closed(DUniv(0)) == Some(DUniv(1)) &&
  !dep_check_closed(DUniv(0), DUniv(0)) &&
  dep_check_closed(DBoolTy, DUniv(1)) &&
  dep_type_of_closed(DPi(DUniv(0), DTVar(0))) == Some(DUniv(1)) &&
  dep_type_of_closed(DSigma(DUniv(0), DTVar(0))) == Some(DUniv(1)) &&
  dep_type_of_closed(lty_to_dterm(LFun(LBool, LProd(LBool, LUnit)))) ==
  Some(DUniv(0))
}

///|
pub fn check_dep_pi() -> Bool {
  let applied = DApp(DApp(dep_id_term(), DBoolTy), DBoolLit(true))
  if !dep_check_closed(dep_id_term(), dep_id_type()) {
    return false
  }
  if dep_type_of_closed(applied) != Some(DBoolTy) {
    return false
  }
  if dep_nf_closed(applied, DBoolTy) != Some(DBoolLit(true)) {
    return false
  }
  let pi_bb = DPi(DBoolTy, DBoolTy)
  let outer = DPi(pi_bb, pi_bb)
  let plain = DLam(pi_bb, DTVar(0))
  let eta = DLam(pi_bb, DLam(DBoolTy, DApp(DTVar(1), DTVar(0))))
  dep_def_eq_closed(plain, eta, outer)
}

///|
pub fn check_dep_sigma() -> Bool {
  let sig_ty = DSigma(DUniv(0), DTVar(0))
  let pair = DPair(DBoolTy, DBoolLit(true))
  let ann_pair = DAnn(pair, sig_ty)
  if !dep_check_closed(pair, sig_ty) {
    return false
  }
  if dep_type_of_closed(DSnd(ann_pair)) != Some(DBoolTy) {
    return false
  }
  if dep_nf_closed(DSnd(ann_pair), DBoolTy) != Some(DBoolLit(true)) {
    return false
  }
  if dep_nf_closed(DFst(ann_pair), DUniv(0)) != Some(DBoolTy) {
    return false
  }
  if dep_check_closed(DPair(DBoolTy, DUnitLit), sig_ty) {
    return false
  }
  let sig_bu = DSigma(DBoolTy, DUnitTy)
  let outer = DPi(sig_bu, sig_bu)
  let plain = DLam(sig_bu, DTVar(0))
  let eta = DLam(sig_bu, DPair(DFst(DTVar(0)), DSnd(DTVar(0))))
  dep_def_eq_closed(plain, eta, outer)
}

///|
pub fn check_dep_all() -> Bool {
  check_dep_universe() && check_dep_pi() && check_dep_sigma()
}
