// Generic inductive-family and higher-inductive-type schema generation.
//
// The concrete Bool/Nat/List/Circle/Torus fragment remains in
// nbe_dep.mbt for backwards compatibility.  This file adds a reusable
// schema language: a finite description of parameters, indices,
// strictly positive constructor arguments, and (for HITs) cells with
// face expressions.  The checker, evaluator, conversion, quoting and
// Kan operations for those descriptions are generated generically.
//
// Telescope and constructor-argument types are ordinary DTerm's.  Their
// DTVar indices refer to schema-local binders in order: parameters,
// then earlier entries/arguments, with DTVar(0) the innermost binder.
// Constructor arguments are classified as external, directly recursive,
// or a function into a recursive occurrence.  External types and
// function domains are rejected if they mention the generated family,
// which gives the usual strict-positivity fragment.
//
// HIT face expressions name a target cell, instantiate its arguments,
// and instantiate its dimensions.  Dimension variables in those
// expressions use DVar(0) for the last dimension of the source cell,
// matching DDimEnv.  Cells of dimension 0, 1 and 2 are supported.

// ---------------------------------------------------------------------------
// Schema descriptors
// ---------------------------------------------------------------------------

///|
pub enum DArgKind {
  DArgExternal
  DArgRecursive
  DArgFunction
  DArgNested
  DArgDecoded
  DArgDecodedFunction
} derive(Debug, Eq)

///|
pub extend DArgKind with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend DArgKind with Eq::{not_equal, equal}

///|
/// One argument instantiating a parameter of a family applied by
/// `DFunctorFamily`: an ordinary term, or the family being
/// declared itself at the given index terms.
pub enum DFunctorParamArg {
  DFunctorParamTerm(DTerm)
  DFunctorParamSelf(Array[DTerm])
} derive(Debug, Eq)

///|
pub extend DFunctorParamArg with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend DFunctorParamArg with Eq::{not_equal, equal}

///|
/// A strictly positive type-functor descriptor.  `DFunctorIdentity`
/// is one recursive occurrence at the displayed family indices;
/// constants and the domains of `DFunctorPi` must be external.  The
/// other nodes are finite products, finite sums (encoded by a Bool
/// tag), lists, and functions from an external domain.  Every node is
/// positive by construction, and the generator synthesizes both its
/// semantic type and its induction-hypothesis functor.
pub enum DPositiveFunctor {
  DFunctorIdentity(Array[DTerm])
  DFunctorConst(DTerm)
  DFunctorProduct(DPositiveFunctor, DPositiveFunctor)
  DFunctorSum(DPositiveFunctor, DPositiveFunctor)
  DFunctorList(DPositiveFunctor)
  DFunctorPi(DTerm, DPositiveFunctor)
  // Dependent polynomial/container node: shape type, a position-type
  // body under one shape binder, and recursive family indices under
  // shape and position binders.  It denotes
  // `Sigma (s : Shape), Positions s -> X (index s p)`.
  DFunctorContainer(DTerm, DTerm, Array[DTerm])
  // Dependent pair of positive functors: the second is read under
  // one binder for a value of the first.  This records dependent
  // Sigma type operators that are not dependent containers whose
  // second component is a single recursive leaf.
  DFunctorSigma(DPositiveFunctor, DPositiveFunctor)
  // Application of another declared inductive family.  The second
  // component instantiates the inner family's parameters: an entry
  // is either an ordinary term over the ambient telescope, or the
  // family currently being declared at the given index terms --
  // which is how recursion through the other family (rose trees
  // through a declared List family, fixed-length branching through
  // a declared Vec family) is expressed.  The third component is
  // the inner family's index vector.  Induction hypotheses for the
  // recursive occurrences reached through this node are produced
  // by eliminating the inner value with the inner family's own
  // eliminator; see `family_gather_type` in schema_functor.mbt.
  DFunctorFamily(DInductiveSpec, Array[DFunctorParamArg], Array[DTerm])
  // Application of the very family being declared, at a possibly
  // different parameter instantiation.  The target spec cannot
  // be carried by value (a finite immutable declaration cannot
  // contain itself), so it is named implicitly: the generator
  // resolves it to the enclosing declaration.  This is the node
  // for non-uniform recursion such as Bush (`Bush (Bush A)`
  // inside `Bush A`, written with a `Self` parameter argument).
  // Parameter and index arguments have the same meaning as in
  // `DFunctorFamily`.
  DFunctorSelfFamily(Array[DFunctorParamArg], Array[DTerm])
} derive(Debug, Eq)

///|
pub extend DPositiveFunctor with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend DPositiveFunctor with Eq::{not_equal, equal}

///|
pub fn dfunctor_identity(index : Array[DTerm]) -> DPositiveFunctor {
  DFunctorIdentity(index)
}

///|
pub fn dfunctor_const(ty : DTerm) -> DPositiveFunctor {
  DFunctorConst(ty)
}

///|
pub fn dfunctor_product(
  a : DPositiveFunctor,
  b : DPositiveFunctor,
) -> DPositiveFunctor {
  DFunctorProduct(a, b)
}

///|
pub fn dfunctor_sum(
  a : DPositiveFunctor,
  b : DPositiveFunctor,
) -> DPositiveFunctor {
  DFunctorSum(a, b)
}

///|
pub fn dfunctor_list(inner : DPositiveFunctor) -> DPositiveFunctor {
  DFunctorList(inner)
}

///|
pub fn dfunctor_pi(dom : DTerm, inner : DPositiveFunctor) -> DPositiveFunctor {
  DFunctorPi(dom, inner)
}

// A dependent polynomial (container) functor.  `positions` is checked
// with the selected shape appended to the local schema context;

///|
/// `index` is checked after appending that shape and one position.
pub fn dfunctor_container(
  shape : DTerm,
  positions : DTerm,
  index~ : Array[DTerm] = [],
) -> DPositiveFunctor {
  DFunctorContainer(shape, positions, index)
}

///|
pub fn dfunctor_sigma(
  first : DPositiveFunctor,
  second : DPositiveFunctor,
) -> DPositiveFunctor {
  DFunctorSigma(first, second)
}

///|
pub fn dfunctor_param_term(term : DTerm) -> DFunctorParamArg {
  DFunctorParamTerm(term)
}

///|
pub fn dfunctor_param_self(index~ : Array[DTerm] = []) -> DFunctorParamArg {
  DFunctorParamSelf(index)
}

///|
/// The positive functor denoting the previously declared family
/// `spec` at the given parameter instantiation and indices.
pub fn dfunctor_family(
  spec : DInductiveSpec,
  params~ : Array[DFunctorParamArg] = [],
  index~ : Array[DTerm] = [],
) -> DPositiveFunctor {
  DFunctorFamily(spec, params, index)
}

///|
/// The positive functor denoting the family being declared
/// itself at the given parameter instantiation and indices
/// (non-uniform / Bush-style recursion).
pub fn dfunctor_self_family(
  params~ : Array[DFunctorParamArg] = [],
  index~ : Array[DTerm] = [],
) -> DPositiveFunctor {
  DFunctorSelfFamily(params, index)
}

///|
/// A propositional equality constraint on constructor/cell data.
/// All three terms are read in the context of the family parameters
/// followed by the constructor arguments.  An introduction is
/// accepted only when `lhs` and `rhs` are convertible at `ty`; the
/// generated eliminator case receives the corresponding Path proof.
pub struct DConstructorConstraint {
  ty : DTerm
  lhs : DTerm
  rhs : DTerm
} derive(Debug, Eq)

///|
pub extend DConstructorConstraint with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend DConstructorConstraint with Eq::{not_equal, equal}

///|
pub fn dconstructor_constraint(
  ty : DTerm,
  lhs : DTerm,
  rhs : DTerm,
) -> DConstructorConstraint {
  DConstructorConstraint::{ ty, lhs, rhs, }
}

///|
pub struct DTelescopeEntry {
  name : String
  ty : DTerm
} derive(Debug, Eq)

///|
pub extend DTelescopeEntry with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend DTelescopeEntry with Eq::{not_equal, equal}

///|
pub fn dtelescope_entry(name : String, ty : DTerm) -> DTelescopeEntry {
  DTelescopeEntry::{ name, ty, }
}

///|
/// One constructor/cell argument.  For DArgExternal, `ty` is its type.
/// For DArgRecursive, `index` gives the family indices and `ty` is
/// unused.  For DArgFunction, `ty` is the domain and `index` terms are
/// checked under one additional domain binder.
pub struct DConstructorArg {
  name : String
  kind : DArgKind
  ty : DTerm
  index : Array[DTerm]
  nested : DPositiveFunctor
  target : Int32
} derive(Debug, Eq)

///|
pub extend DConstructorArg with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend DConstructorArg with Eq::{not_equal, equal}

///|
pub fn darg_external(name : String, ty : DTerm) -> DConstructorArg {
  DConstructorArg::{
    name,
    kind: DArgExternal,
    ty,
    index: [],
    nested: DFunctorIdentity([]),
    target: -1,
  }
}

///|
pub fn darg_recursive(
  name : String,
  index~ : Array[DTerm] = [],
) -> DConstructorArg {
  DConstructorArg::{
    name,
    kind: DArgRecursive,
    ty: DUnitTy,
    index,
    nested: DFunctorIdentity([]),
    target: -1,
  }
}

///|
pub fn darg_function(
  name : String,
  dom : DTerm,
  index~ : Array[DTerm] = [],
) -> DConstructorArg {
  DConstructorArg::{
    name,
    kind: DArgFunction,
    ty: dom,
    index,
    nested: DFunctorIdentity([]),
    target: -1,
  }
}

///|
/// A nested recursive argument `F (family ...)` for a strictly
/// positive functor descriptor `F`.
pub fn darg_nested(
  name : String,
  functor : DPositiveFunctor,
) -> DConstructorArg {
  DConstructorArg::{
    name,
    kind: DArgNested,
    ty: DUnitTy,
    index: [],
    nested: functor,
    target: -1,
  }
}

///|
/// An element of `decode` applied to an earlier recursive code
/// argument (induction-recursion).  `source` is the zero-based
/// position of that earlier argument.
pub fn darg_decoded(name : String, source : Int32) -> DConstructorArg {
  DConstructorArg::{
    name,
    kind: DArgDecoded,
    ty: DUnitTy,
    index: [],
    nested: DFunctorIdentity([]),
    target: source,
  }
}

///|
/// A function from `decode` of an earlier recursive code argument
/// into the code family itself, as in the Π-code of a Tarski
/// universe.  `index` is checked under the decoded domain binder.
pub fn darg_decoded_function(
  name : String,
  source : Int32,
  index~ : Array[DTerm] = [],
) -> DConstructorArg {
  DConstructorArg::{
    name,
    kind: DArgDecodedFunction,
    ty: DUnitTy,
    index,
    nested: DFunctorIdentity([]),
    target: source,
  }
}

///|
/// A recursive occurrence in another component of a mutual block.
/// Such arguments are meaningful only before compilation with
/// `compile_mutual_inductive`.
pub fn darg_mutual(
  name : String,
  component : Int32,
  index : Array[DTerm],
) -> DConstructorArg {
  DConstructorArg::{
    name,
    kind: DArgRecursive,
    ty: DUnitTy,
    index,
    nested: DFunctorIdentity([]),
    target: component,
  }
}

///|
/// A function into another component of a mutual block.
pub fn darg_mutual_function(
  name : String,
  component : Int32,
  dom : DTerm,
  index~ : Array[DTerm] = [],
) -> DConstructorArg {
  DConstructorArg::{
    name,
    kind: DArgFunction,
    ty: dom,
    index,
    nested: DFunctorIdentity([]),
    target: component,
  }
}

///|
pub struct DConstructorSpec {
  name : String
  args : Array[DConstructorArg]
  result_index : Array[DTerm]
  constraints : Array[DConstructorConstraint]
} derive(Debug, Eq)

///|
pub extend DConstructorSpec with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend DConstructorSpec with Eq::{not_equal, equal}

///|
pub fn dconstructor_spec(
  name : String,
  args : Array[DConstructorArg],
  result_index~ : Array[DTerm] = [],
  constraints~ : Array[DConstructorConstraint] = [],
) -> DConstructorSpec {
  DConstructorSpec::{ name, args, result_index, constraints, }
}

///|
pub fn dconstructor_spec_constrained(
  name : String,
  args : Array[DConstructorArg],
  constraints : Array[DConstructorConstraint],
  result_index~ : Array[DTerm] = [],
) -> DConstructorSpec {
  dconstructor_spec(name, args, result_index~, constraints~)
}

///|
pub struct DInductiveSpec {
  name : String
  level : Int32
  params : Array[DTelescopeEntry]
  indices : Array[DTelescopeEntry]
  constructors : Array[DConstructorSpec]
  decode_cases : Array[DTerm]
  decode_level : Int32
} derive(Debug, Eq)

///|
pub extend DInductiveSpec with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend DInductiveSpec with Eq::{not_equal, equal}

///|
pub fn dinductive_spec(
  name : String,
  level : Int32,
  params : Array[DTelescopeEntry],
  indices : Array[DTelescopeEntry],
  constructors : Array[DConstructorSpec],
) -> DInductiveSpec {
  DInductiveSpec::{
    name,
    level,
    params,
    indices,
    constructors,
    decode_cases: [],
    decode_level: 0,
  }
}

///|
/// An induction-recursive declaration.  The inductive family is the
/// type of codes; `decode_cases[i]` is a type-valued term in the
/// context of parameters, constructor arguments, their recursive
/// decode hypotheses, and constraint proofs.  It defines the
/// simultaneously recursive decoding function into
/// `Type[decode_level]`.
pub fn dinductive_recursive_spec(
  name : String,
  level : Int32,
  params : Array[DTelescopeEntry],
  indices : Array[DTelescopeEntry],
  constructors : Array[DConstructorSpec],
  decode_cases : Array[DTerm],
  decode_level~ : Int32 = 0,
) -> DInductiveSpec {
  DInductiveSpec::{
    name,
    level,
    params,
    indices,
    constructors,
    decode_cases,
    decode_level,
  }
}

///|
/// Instantiate another cell as one face of a HIT cell.
pub struct DHitFaceExpr {
  cell : Int32
  args : Array[DTerm]
  dims : Array[Dim]
} derive(Debug, Eq)

///|
pub extend DHitFaceExpr with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend DHitFaceExpr with Eq::{not_equal, equal}

///|
pub fn dhit_face(
  cell : Int32,
  args : Array[DTerm],
  dims : Array[Dim],
) -> DHitFaceExpr {
  DHitFaceExpr::{ cell, args, dims, }
}

///|
/// A face given directly by a term in the context of the cell's
/// parameters and arguments, rather than by a cell application.
/// This is represented by `cell = -1` with the single face term in
/// `args`.  It is what makes constructors like the squash of a
/// propositional truncation expressible: their endpoints are the
/// recursive arguments themselves.
pub fn dhit_arg_face(term : DTerm) -> DHitFaceExpr {
  DHitFaceExpr::{ cell: -1, args: [term], dims: [], }
}

///|
/// A HIT cell.  `faces` has length `2 * dim_count`, ordered
/// (dim 0 at 0, dim 0 at 1, dim 1 at 0, dim 1 at 1).
pub struct DHitCellSpec {
  name : String
  dim_count : Int32
  args : Array[DConstructorArg]
  result_index : Array[DTerm]
  faces : Array[DHitFaceExpr]
  constraints : Array[DConstructorConstraint]
} derive(Debug, Eq)

///|
pub extend DHitCellSpec with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend DHitCellSpec with Eq::{not_equal, equal}

///|
pub fn dhit_cell_spec(
  name : String,
  dim_count : Int32,
  args : Array[DConstructorArg],
  faces : Array[DHitFaceExpr],
  result_index~ : Array[DTerm] = [],
  constraints~ : Array[DConstructorConstraint] = [],
) -> DHitCellSpec {
  DHitCellSpec::{ name, dim_count, args, result_index, faces, constraints, }
}

///|
pub struct DHitSpec {
  name : String
  level : Int32
  params : Array[DTelescopeEntry]
  indices : Array[DTelescopeEntry]
  cells : Array[DHitCellSpec]
} derive(Debug, Eq)

///|
pub extend DHitSpec with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend DHitSpec with Eq::{not_equal, equal}

///|
pub fn dhit_spec(
  name : String,
  level : Int32,
  params : Array[DTelescopeEntry],
  indices : Array[DTelescopeEntry],
  cells : Array[DHitCellSpec],
) -> DHitSpec {
  DHitSpec::{ name, level, params, indices, cells, }
}

// ---------------------------------------------------------------------------
// Telescope utilities
// ---------------------------------------------------------------------------

///|
pub fn schema_concat_values(
  a : Array[DValue],
  b : Array[DValue],
) -> Array[DValue] {
  let out : Array[DValue] = []
  for i in 0..<a.length() {
    out.push(a[i])
  }
  for i in 0..<b.length() {
    out.push(b[i])
  }
  out
}

///|
fn schema_env(values : Array[DValue]) -> DEnv {
  // Schema arrays are in declaration order; denv_extend makes the last
  // (innermost) declaration de Bruijn index 0.
  denv_extend(values, denv_empty())
}

///|
fn schema_dim_env(dims : Array[Dim]) -> DDimEnv {
  ddim_extend(dims, ddim_empty())
}

///|
fn schema_eval_under(
  t : DTerm,
  values : Array[DValue],
  dims : Array[Dim],
) -> DValue {
  deval_dim(t, schema_env(values), schema_dim_env(dims))
}

///|
fn schema_term_mentions_family(t : DTerm, name : String) -> Bool {
  // Structural occurrence analysis (see schema_positivity.mbt): it
  // follows binders, beta-reduces aliases, and traverses indirect
  // occurrences through other generated families.
  dterm_family_occurs(t, name)
}

///|
/// Types of telescope entries at concrete earlier values.  Prefix
/// types/values describe binders already in scope.
pub fn telescope_type_values(
  entries : Array[DTelescopeEntry],
  prefix_types : Array[DValue],
  prefix_values : Array[DValue],
  values : Array[DValue],
) -> Array[DValue] {
  let out : Array[DValue] = []
  let prior : Array[DValue] = []
  for i in 0..<entries.length() {
    let all_values = schema_concat_values(prefix_values, prior)
    let all_types = schema_concat_values(prefix_types, out)
    let ty = match
      d_as_type(
        entries[i].ty,
        schema_env(all_types),
        schema_env(all_values),
        ddim_empty(),
      ) {
      Some(tv) => tv.value
      None => DVUnitTy
    }
    out.push(ty)
    if i < values.length() {
      prior.push(values[i])
    } else {
      prior.push(DVUnit)
    }
  }
  out
}

///|
/// Elaborate only the next type of a telescope from the types and
/// values already obtained for earlier entries.  Stepwise callers use
/// this instead of recomputing the whole telescope at every entry.
pub fn telescope_next_type(
  entries : Array[DTelescopeEntry],
  prefix_types : Array[DValue],
  prefix_values : Array[DValue],
  prior_types : Array[DValue],
  prior_values : Array[DValue],
) -> DValue {
  let i = prior_values.length()
  if i < 0 || i >= entries.length() {
    return DVUnitTy
  }
  let all_types = schema_concat_values(prefix_types, prior_types)
  let all_values = schema_concat_values(prefix_values, prior_values)
  match
    d_as_type(
      entries[i].ty,
      schema_env(all_types),
      schema_env(all_values),
      ddim_empty(),
    ) {
    Some(tv) => tv.value
    None => DVUnitTy
  }
}

///|
/// Check terms against a telescope in an ambient checker context.
/// The telescope types themselves are closed over the supplied prefix.
pub fn check_telescope_terms(
  entries : Array[DTelescopeEntry],
  terms : Array[DTerm],
  prefix_types : Array[DValue],
  prefix_values : Array[DValue],
  ctx : DEnv,
  env : DEnv,
  denv : DDimEnv,
) -> Array[DValue]? {
  if entries.length() != terms.length() {
    return None
  }
  let values : Array[DValue] = []
  let prior_types : Array[DValue] = []
  for i in 0..<entries.length() {
    let ty = telescope_next_type(
      entries, prefix_types, prefix_values, prior_types, values,
    )
    prior_types.push(ty)
    match d_check(terms[i], ty, ctx, env, denv) {
      Some(v) => values.push(v)
      None => return None
    }
  }
  Some(values)
}

///|
fn telescope_elaborates(
  entries : Array[DTelescopeEntry],
  prefix_types : Array[DValue],
  prefix_values : Array[DValue],
  values : Array[DValue],
) -> Bool {
  let types : Array[DValue] = []
  let prior : Array[DValue] = []
  for i in 0..<entries.length() {
    let all_types = schema_concat_values(prefix_types, types)
    let all_values = schema_concat_values(prefix_values, prior)
    match
      d_as_type(
        entries[i].ty,
        schema_env(all_types),
        schema_env(all_values),
        ddim_empty(),
      ) {
      Some(tv) => types.push(tv.value)
      None => return false
    }
    if i < values.length() {
      prior.push(values[i])
    } else {
      prior.push(DVUnit)
    }
  }
  true
}

///|
fn schema_fresh_values(n : Int32, start : Int32) -> Array[DValue] {
  let out : Array[DValue] = []
  for i in 0..<n {
    out.push(DVNeutral(DNVar(start + i)))
  }
  out
}

///|
fn schema_check_index_terms(
  indices : Array[DTelescopeEntry],
  params : Array[DTelescopeEntry],
  prefix_types : Array[DValue],
  prefix_values : Array[DValue],
  terms : Array[DTerm],
) -> Bool {
  // prefix_types includes the parameter types followed by any local
  // argument/domain types.  Recover parameter values/types from the
  // front of the prefix.
  if terms.length() != indices.length() {
    return false
  }
  let param_types : Array[DValue] = []
  let param_values : Array[DValue] = []
  for i in 0..<params.length() {
    if i < prefix_types.length() && i < prefix_values.length() {
      param_types.push(prefix_types[i])
      param_values.push(prefix_values[i])
    }
  }
  // Index telescope types are evaluated stepwise at the checked index
  // values themselves, while index terms may use the whole prefix.
  let checked : Array[DValue] = []
  let prior_types : Array[DValue] = []
  let ctx = schema_env(prefix_types)
  let env = schema_env(prefix_values)
  for i in 0..<indices.length() {
    let ty = telescope_next_type(
      indices, param_types, param_values, prior_types, checked,
    )
    prior_types.push(ty)
    match d_check(terms[i], ty, ctx, env, ddim_empty()) {
      Some(v) => checked.push(v)
      None => return false
    }
  }
  true
}

///|
/// The host family type at evaluated `Self` indices, for use
/// during declaration validation: host parameter values are the
/// first `params.length()` entries of the validation prefix.
fn schema_validation_self_type(
  self_type : (Array[DValue], Array[DValue]) -> DValue,
  params : Array[DTelescopeEntry],
  prefix_values : Array[DValue],
  js : Array[DTerm],
) -> DValue {
  let host_params : Array[DValue] = []
  for h in 0..<params.length() {
    if h < prefix_values.length() {
      host_params.push(prefix_values[h])
    }
  }
  let self_indices : Array[DValue] = []
  for h in 0..<js.length() {
    self_indices.push(schema_eval_under(js[h], prefix_values, []))
  }
  self_type(host_params, self_indices)
}

///|
fn schema_arg_type_for_validation(
  arg : DConstructorArg,
  prior_specs : Array[DConstructorArg],
  decode_available : Bool,
  family_name : String,
  params : Array[DTelescopeEntry],
  indices : Array[DTelescopeEntry],
  prefix_types : Array[DValue],
  prefix_values : Array[DValue],
  self_type : (Array[DValue], Array[DValue]) -> DValue,
) -> DValue? {
  match arg.kind {
    DArgExternal => {
      if schema_term_mentions_family(arg.ty, family_name) {
        return None
      }
      match
        d_as_type(
          arg.ty,
          schema_env(prefix_types),
          schema_env(prefix_values),
          ddim_empty(),
        ) {
        Some(tv) => Some(tv.value)
        None => None
      }
    }
    DArgRecursive =>
      if arg.target == -1 &&
        schema_check_index_terms(
          indices,
          params,
          prefix_types,
          prefix_values,
          arg.index,
        ) {
        // The real host type, not a placeholder: later argument,
        // result-index and constraint types may depend on this
        // recursive element (notably a `DFunctorFamily` parameter
        // whose type is an earlier `Self` parameter).
        Some(
          schema_validation_self_type(
            self_type,
            params,
            prefix_values,
            arg.index,
          ),
        )
      } else {
        None
      }
    DArgFunction => {
      if arg.target != -1 || schema_term_mentions_family(arg.ty, family_name) {
        return None
      }
      match
        d_as_type(
          arg.ty,
          schema_env(prefix_types),
          schema_env(prefix_values),
          ddim_empty(),
        ) {
        Some(tv) => {
          let dom_types = schema_concat_values(prefix_types, [tv.value])
          let dom_values = schema_concat_values(prefix_values, [
            DVNeutral(DNVar(9000 + prefix_values.length())),
          ])
          if schema_check_index_terms(
              indices,
              params,
              dom_types,
              dom_values,
              arg.index,
            ) {
            let saved_values = schema_concat_values([], prefix_values)
            Some(
              DVPi(tv.value, a => {
                schema_validation_self_type(
                  self_type,
                  params,
                  schema_concat_values(saved_values, [a]),
                  arg.index,
                )
              }),
            )
          } else {
            None
          }
        }
        None => None
      }
    }
    DArgNested =>
      if arg.target == -1 {
        positive_functor_validate(
          arg.nested,
          family_name,
          params,
          indices,
          prefix_types,
          prefix_values,
          self_type,
        )
      } else {
        None
      }
    DArgDecoded =>
      if decode_available &&
        arg.target >= 0 &&
        arg.target < prior_specs.length() &&
        prior_specs[arg.target].kind == DArgRecursive &&
        prior_specs[arg.target].target == -1 {
        // The decoded type itself is available semantically once the
        // code argument is present; validation only needs a
        // placeholder in the prefix telescope.
        Some(DVUnitTy)
      } else {
        None
      }
    DArgDecodedFunction => {
      if !decode_available ||
        arg.target < 0 ||
        arg.target >= prior_specs.length() ||
        prior_specs[arg.target].kind != DArgRecursive ||
        prior_specs[arg.target].target != -1 {
        return None
      }
      let dom_types = schema_concat_values(prefix_types, [DVUnitTy])
      let dom_values = schema_concat_values(prefix_values, [
        DVNeutral(DNVar(9050 + prefix_values.length())),
      ])
      if schema_check_index_terms(
          indices,
          params,
          dom_types,
          dom_values,
          arg.index,
        ) {
        Some(DVPi(DVUnitTy, _ => DVUnitTy))
      } else {
        None
      }
    }
  }
}

///|
fn schema_validate_args(
  family_name : String,
  params : Array[DTelescopeEntry],
  indices : Array[DTelescopeEntry],
  args : Array[DConstructorArg],
  result_index : Array[DTerm],
  constraints : Array[DConstructorConstraint],
  decode_available : Bool,
  self_type : (Array[DValue], Array[DValue]) -> DValue,
) -> Bool {
  let param_values = schema_fresh_values(params.length(), 8000)
  if !telescope_elaborates(params, [], [], param_values) {
    return false
  }
  let param_types = telescope_type_values(params, [], [], param_values)
  let index_values = schema_fresh_values(indices.length(), 8050)
  if !telescope_elaborates(indices, param_types, param_values, index_values) {
    return false
  }
  let prefix_types = schema_concat_values([], param_types)
  let prefix_values = schema_concat_values([], param_values)
  for i in 0..<args.length() {
    match
      schema_arg_type_for_validation(
        args[i],
        schema_arg_spec_prefix(args, i),
        decode_available,
        family_name,
        params,
        indices,
        prefix_types,
        prefix_values,
        self_type,
      ) {
      Some(ty) => {
        prefix_types.push(ty)
        prefix_values.push(DVNeutral(DNVar(8100 + i)))
      }
      None => return false
    }
  }
  if !schema_check_index_terms(
      indices, params, prefix_types, prefix_values, result_index,
    ) {
    return false
  }
  for i in 0..<constraints.length() {
    let c = constraints[i]
    match
      d_as_type(
        c.ty,
        schema_env(prefix_types),
        schema_env(prefix_values),
        ddim_empty(),
      ) {
      Some(tv) =>
        match
          (
            d_check(
              c.lhs,
              tv.value,
              schema_env(prefix_types),
              schema_env(prefix_values),
              ddim_empty(),
            ),
            d_check(
              c.rhs,
              tv.value,
              schema_env(prefix_types),
              schema_env(prefix_values),
              ddim_empty(),
            ),
          ) {
          (Some(_), Some(_)) => ()
          _ => return false
        }
      None => return false
    }
  }
  true
}

///|
fn schema_names_unique(names : Array[String]) -> Bool {
  for i in 0..<names.length() {
    if names[i].length() == 0 {
      return false
    }
    for j in (i + 1)..<names.length() {
      if names[i] == names[j] {
        return false
      }
    }
  }
  true
}

///|
fn inductive_schema_validate_uncached(spec : DInductiveSpec) -> Bool {
  let ctor_names : Array[String] = []
  for i in 0..<spec.constructors.length() {
    ctor_names.push(spec.constructors[i].name)
  }
  if spec.name.length() == 0 || !schema_names_unique(ctor_names) {
    return false
  }
  if schema_telescope_family_occurs(spec.params, spec.name) ||
    schema_telescope_family_occurs(spec.indices, spec.name) {
    return false
  }
  // Parameter and index telescopes must elaborate at fresh values.
  let pv = schema_fresh_values(spec.params.length(), 8200)
  if !telescope_elaborates(spec.params, [], [], pv) {
    return false
  }
  let pt = telescope_type_values(spec.params, [], [], pv)
  let iv = schema_fresh_values(spec.indices.length(), 8300)
  if !telescope_elaborates(spec.indices, pt, pv, iv) {
    return false
  }
  for i in 0..<spec.constructors.length() {
    let c = spec.constructors[i]
    if !schema_validate_args(
        spec.name,
        spec.params,
        spec.indices,
        c.args,
        c.result_index,
        c.constraints,
        spec.decode_cases.length() == spec.constructors.length() &&
        spec.decode_cases.length() > 0,
        (ps, js) => DVInductive(spec, ps, js),
      ) {
      return false
    }
  }
  inductive_decode_cases_validate(spec)
}

///|
pub fn quote_inductive_elim_neutral(
  level : Int32,
  dlevel : Int32,
  spec : DInductiveSpec,
  motive : (Array[DValue], DValue) -> DValue,
  cases : Array[DValue],
  params : Array[DValue],
  indices : Array[DValue],
  scrut : DNeutral,
) -> DTerm {
  let param_terms = quote_telescope_values(
    level,
    dlevel,
    spec.params,
    [],
    [],
    params,
  )
  let index_terms = quote_telescope_values(
    level,
    dlevel,
    spec.indices,
    inductive_param_types(spec, params),
    params,
    indices,
  )
  let case_terms : Array[DTerm] = []
  for i in 0..<cases.length() {
    case_terms.push(
      quote_at(
        level,
        dlevel,
        inductive_case_type(spec, motive, params, i),
        cases[i],
      ),
    )
  }
  DInductiveElim(
    spec,
    quote_schema_motive(
      level,
      dlevel,
      spec.indices,
      inductive_param_types(spec, params),
      params,
      idx => DVInductive(spec, params, idx),
      motive,
    ),
    case_terms,
    param_terms,
    index_terms,
    quote_dneutral(level, dlevel, scrut, DVInductive(spec, params, indices)),
  )
}

///|
pub fn quote_hit_elim_neutral(
  level : Int32,
  dlevel : Int32,
  spec : DHitSpec,
  motive : (Array[DValue], DValue) -> DValue,
  cases : Array[DValue],
  params : Array[DValue],
  indices : Array[DValue],
  scrut : DNeutral,
) -> DTerm {
  let param_terms = quote_telescope_values(
    level,
    dlevel,
    spec.params,
    [],
    [],
    params,
  )
  let index_terms = quote_telescope_values(
    level,
    dlevel,
    spec.indices,
    hit_param_types(spec, params),
    params,
    indices,
  )
  let case_terms : Array[DTerm] = []
  for i in 0..<cases.length() {
    case_terms.push(
      quote_at(
        level,
        dlevel,
        hit_case_type(spec, motive, cases, params, i, dlevel),
        cases[i],
      ),
    )
  }
  DHitElim(
    spec,
    quote_schema_motive(
      level,
      dlevel,
      spec.indices,
      hit_param_types(spec, params),
      params,
      idx => DVHitType(spec, params, idx),
      motive,
    ),
    case_terms,
    param_terms,
    index_terms,
    quote_dneutral(level, dlevel, scrut, DVHitType(spec, params, indices)),
  )
}

///|
pub fn conv_inductive_elim_neutral(
  level : Int32,
  dlevel : Int32,
  s1 : DInductiveSpec,
  m1 : (Array[DValue], DValue) -> DValue,
  c1 : Array[DValue],
  p1 : Array[DValue],
  i1 : Array[DValue],
  n1 : DNeutral,
  s2 : DInductiveSpec,
  m2 : (Array[DValue], DValue) -> DValue,
  c2 : Array[DValue],
  p2 : Array[DValue],
  i2 : Array[DValue],
  n2 : DNeutral,
) -> Bool {
  if s1 != s2 || c1.length() != c2.length() {
    return false
  }
  if !conv_telescope_values(level, dlevel, s1.params, [], [], p1, p2) ||
    !conv_telescope_values(
      level,
      dlevel,
      s1.indices,
      inductive_param_types(s1, p1),
      p1,
      i1,
      i2,
    ) ||
    !schema_motives_conv(
      level,
      dlevel,
      s1.indices,
      inductive_param_types(s1, p1),
      p1,
      idx => DVInductive(s1, p1, idx),
      m1,
      m2,
    ) ||
    !conv_neutral(level, dlevel, n1, n2) {
    return false
  }
  for i in 0..<c1.length() {
    if !conv_at(level, dlevel, inductive_case_type(s1, m1, p1, i), c1[i], c2[i]) {
      return false
    }
  }
  true
}

///|
pub fn conv_hit_elim_neutral(
  level : Int32,
  dlevel : Int32,
  s1 : DHitSpec,
  m1 : (Array[DValue], DValue) -> DValue,
  c1 : Array[DValue],
  p1 : Array[DValue],
  i1 : Array[DValue],
  n1 : DNeutral,
  s2 : DHitSpec,
  m2 : (Array[DValue], DValue) -> DValue,
  c2 : Array[DValue],
  p2 : Array[DValue],
  i2 : Array[DValue],
  n2 : DNeutral,
) -> Bool {
  if s1 != s2 || c1.length() != c2.length() {
    return false
  }
  if !conv_telescope_values(level, dlevel, s1.params, [], [], p1, p2) ||
    !conv_telescope_values(
      level,
      dlevel,
      s1.indices,
      hit_param_types(s1, p1),
      p1,
      i1,
      i2,
    ) ||
    !schema_motives_conv(
      level,
      dlevel,
      s1.indices,
      hit_param_types(s1, p1),
      p1,
      idx => DVHitType(s1, p1, idx),
      m1,
      m2,
    ) ||
    !conv_neutral(level, dlevel, n1, n2) {
    return false
  }
  for i in 0..<c1.length() {
    if !conv_at(
        level,
        dlevel,
        hit_case_type(s1, m1, c1, p1, i, dlevel),
        c1[i],
        c2[i],
      ) {
      return false
    }
  }
  true
}

///|
fn schema_split_terms(
  terms : Array[DTerm],
  n : Int32,
) -> (Array[DTerm], Array[DTerm]) {
  let a : Array[DTerm] = []
  let b : Array[DTerm] = []
  for i in 0..<terms.length() {
    if i < n {
      a.push(terms[i])
    } else {
      b.push(terms[i])
    }
  }
  (a, b)
}

// ---------------------------------------------------------------------------
// Generated inductive families: semantics and elaboration
// ---------------------------------------------------------------------------

///|
pub fn inductive_param_types(
  spec : DInductiveSpec,
  params : Array[DValue],
) -> Array[DValue] {
  inductive_param_types_cached(default_schema_registry, spec, params)
}

///|
pub fn inductive_index_types(
  spec : DInductiveSpec,
  params : Array[DValue],
  indices : Array[DValue],
) -> Array[DValue] {
  inductive_index_types_cached(default_schema_registry, spec, params, indices)
}

///|
pub fn hit_param_types(
  spec : DHitSpec,
  params : Array[DValue],
) -> Array[DValue] {
  hit_param_types_cached(default_schema_registry, spec, params)
}

///|
pub fn hit_index_types(
  spec : DHitSpec,
  params : Array[DValue],
  indices : Array[DValue],
) -> Array[DValue] {
  hit_index_types_cached(default_schema_registry, spec, params, indices)
}

///|
fn schema_eval_index_terms(
  params : Array[DValue],
  prior : Array[DValue],
  terms : Array[DTerm],
) -> Array[DValue] {
  let values = schema_concat_values(params, prior)
  let out : Array[DValue] = []
  for i in 0..<terms.length() {
    out.push(schema_eval_under(terms[i], values, []))
  }
  out
}

///|
/// The semantic type of one generated constructor argument.  The
/// `family` function is supplied by the inductive or HIT generator.
pub fn schema_arg_type(
  arg : DConstructorArg,
  params : Array[DValue],
  prior : Array[DValue],
  family : (Array[DValue]) -> DValue,
) -> DValue {
  schema_arg_type_full(arg, [], params, prior, family, (_, _) => DVUnitTy)
}

///|
pub fn inductive_arg_type(
  spec : DInductiveSpec,
  arg : DConstructorArg,
  params : Array[DValue],
  prior : Array[DValue],
) -> DValue {
  inductive_arg_type_full(spec, arg, [], params, prior)
}

///|
pub fn inductive_result_indices(
  ctor : DConstructorSpec,
  params : Array[DValue],
  args : Array[DValue],
) -> Array[DValue] {
  schema_eval_index_terms(params, args, ctor.result_index)
}

///|
fn schema_apply_motive(
  motive_value : DValue,
  index_types : Array[DValue],
  family : DValue,
  indices : Array[DValue],
  scrut : DValue,
) -> DValue {
  let mut cur = motive_value
  for i in 0..<indices.length() {
    let ty = if i < index_types.length() { index_types[i] } else { DVUnitTy }
    cur = dapp_typed(cur, indices[i], ty)
  }
  dapp_typed(cur, scrut, family)
}

///|
fn inductive_motive_from_value(
  spec : DInductiveSpec,
  params : Array[DValue],
  motive_value : DValue,
) -> (Array[DValue], DValue) -> DValue {
  (indices : Array[DValue], scrut : DValue) => {
    schema_apply_motive(
      motive_value,
      inductive_index_types(spec, params, indices),
      DVInductive(spec, params, indices),
      indices,
      scrut,
    )
  }
}

///|
fn schema_motive_type_loop(
  entries : Array[DTelescopeEntry],
  pos : Int32,
  param_types : Array[DValue],
  params : Array[DValue],
  prior : Array[DValue],
  prior_types : Array[DValue],
  family : (Array[DValue]) -> DValue,
  level : Int32,
) -> DValue {
  if pos >= entries.length() {
    DVPi(family(prior), _ => DVUniv(level))
  } else {
    let ty = telescope_next_type(
      entries, param_types, params, prior_types, prior,
    )
    DVPi(ty, x => {
      schema_motive_type_loop(
        entries,
        pos + 1,
        param_types,
        params,
        schema_concat_values(prior, [x]),
        schema_concat_values(prior_types, [ty]),
        family,
        level,
      )
    })
  }
}

///|
fn peel_motive_univ_level(
  ty : DValue,
  arity : Int32,
  level : Int32,
) -> Int32? {
  if arity <= 0 {
    as_univ_level(ty)
  } else {
    match as_pi(ty) {
      Some(parts) =>
        peel_motive_univ_level(
          (parts.fam)(reflect_var(level, parts.dom)),
          arity - 1,
          level + 1,
        )
      None => None
    }
  }
}

///|
fn check_schema_motive(
  motive_term : DTerm,
  entries : Array[DTelescopeEntry],
  param_types : Array[DValue],
  params : Array[DValue],
  family : (Array[DValue]) -> DValue,
  default_level : Int32,
  ctx : DEnv,
  env : DEnv,
  denv : DDimEnv,
) -> DValue? {
  let chosen_level = match d_infer(motive_term, ctx, env, denv) {
    Some(inf) =>
      match
        peel_motive_univ_level(inf.ty, entries.length() + 1, denv_len(ctx)) {
        Some(lvl) => lvl
        None => default_level
      }
    None => default_level
  }
  let mot_ty = schema_motive_type_loop(
    entries, 0, param_types, params, [], [], family, chosen_level,
  )
  d_check(motive_term, mot_ty, ctx, env, denv)
}

///|
pub fn inductive_motive_type(
  spec : DInductiveSpec,
  params : Array[DValue],
) -> DValue {
  schema_motive_type_loop(
    spec.indices,
    0,
    inductive_param_types(spec, params),
    params,
    [],
    [],
    idx => DVInductive(spec, params, idx),
    spec.level,
  )
}

///|
fn inductive_case_type_loop(
  spec : DInductiveSpec,
  motive : (Array[DValue], DValue) -> DValue,
  params : Array[DValue],
  ctor_index : Int32,
  ctor : DConstructorSpec,
  pos : Int32,
  prior : Array[DValue],
) -> DValue {
  if pos >= ctor.args.length() {
    let result = inductive_result_indices(ctor, params, prior)
    schema_constraints_pi(
      ctor.constraints,
      params,
      prior,
      motive(result, DVIntro(spec, ctor_index, params, prior)),
    )
  } else {
    let arg = ctor.args[pos]
    let arg_ty = inductive_arg_type_full(
      spec,
      arg,
      schema_arg_spec_prefix(ctor.args, pos),
      params,
      prior,
    )
    DVPi(arg_ty, x => {
      let next = schema_concat_values(prior, [x])
      match arg.kind {
        DArgExternal =>
          inductive_case_type_loop(
            spec,
            motive,
            params,
            ctor_index,
            ctor,
            pos + 1,
            next,
          )
        DArgRecursive => {
          let idx = schema_eval_index_terms(params, prior, arg.index)
          DVPi(motive(idx, x), _ => {
            inductive_case_type_loop(
              spec,
              motive,
              params,
              ctor_index,
              ctor,
              pos + 1,
              next,
            )
          })
        }
        DArgFunction => {
          let dom = schema_eval_under(
            arg.ty,
            schema_concat_values(params, prior),
            [],
          )
          let ih_ty = DVPi(dom, a => {
            let idx = schema_eval_index_terms(
              params,
              schema_concat_values(prior, [a]),
              arg.index,
            )
            motive(idx, dapp_typed(x, a, dom))
          })
          DVPi(ih_ty, _ => {
            inductive_case_type_loop(
              spec,
              motive,
              params,
              ctor_index,
              ctor,
              pos + 1,
              next,
            )
          })
        }
        DArgNested => {
          let ih_ty = positive_functor_ih_type(
            arg.nested,
            params,
            prior,
            idx => DVInductive(spec, params, idx),
            motive,
            x,
          )
          DVPi(ih_ty, _ => {
            inductive_case_type_loop(
              spec,
              motive,
              params,
              ctor_index,
              ctor,
              pos + 1,
              next,
            )
          })
        }
        DArgDecoded =>
          inductive_case_type_loop(
            spec,
            motive,
            params,
            ctor_index,
            ctor,
            pos + 1,
            next,
          )
        DArgDecodedFunction => {
          let prior_specs = schema_arg_spec_prefix(ctor.args, pos)
          let dom = eval_inductive_decode(
            spec,
            params,
            schema_source_indices(arg, prior_specs, params, prior),
            schema_source_value(arg, prior),
            0,
          )
          let ih_ty = DVPi(dom, a => {
            let idx = schema_eval_index_terms(
              params,
              schema_concat_values(prior, [a]),
              arg.index,
            )
            motive(idx, dapp_typed(x, a, dom))
          })
          DVPi(ih_ty, _ => {
            inductive_case_type_loop(
              spec,
              motive,
              params,
              ctor_index,
              ctor,
              pos + 1,
              next,
            )
          })
        }
      }
    })
  }
}

///|
pub fn inductive_case_type(
  spec : DInductiveSpec,
  motive : (Array[DValue], DValue) -> DValue,
  params : Array[DValue],
  ctor_index : Int32,
) -> DValue {
  if ctor_index < 0 || ctor_index >= spec.constructors.length() {
    DVUnitTy
  } else {
    inductive_case_type_loop(
      spec,
      motive,
      params,
      ctor_index,
      spec.constructors[ctor_index],
      0,
      [],
    )
  }
}

///|
fn inductive_family_parts(
  ty : DValue,
  params : Array[DValue],
  indices : Array[DValue],
) -> (Array[DValue], Array[DValue]) {
  match force_value(ty) {
    DVInductive(_, p, i) => (p, i)
    _ => (params, indices)
  }
}

///|
/// Generated dependent elimination for an inductive schema.
pub fn eval_inductive_elim(
  spec : DInductiveSpec,
  motive : (Array[DValue], DValue) -> DValue,
  cases : Array[DValue],
  params : Array[DValue],
  indices : Array[DValue],
  scrut : DValue,
  dlevel : Int32,
) -> DValue {
  match force_value(scrut) {
    DVIntro(spec2, ctor_index, params2, args) =>
      if spec2 != spec ||
        ctor_index < 0 ||
        ctor_index >= cases.length() ||
        ctor_index >= spec.constructors.length() {
        DVUnit
      } else {
        schema_apply_case(
          spec.constructors[ctor_index].args,
          spec.constructors[ctor_index].constraints,
          cases[ctor_index],
          params2,
          args,
          motive,
          idx => DVInductive(spec, params2, idx),
          (idx, x) => {
            eval_inductive_elim(spec, motive, cases, params2, idx, x, dlevel)
          },
          (idx, x) => eval_inductive_decode(spec, params2, idx, x, dlevel),
        )
      }
    DVNeutral(n) =>
      DVNeutral(DNInductiveElim(spec, motive, cases, params, indices, n))
    _ => DVUnit
  }
}

///|
pub fn eval_inductive_type_term(
  spec : DInductiveSpec,
  args : Array[DTerm],
  env : DEnv,
  denv : DDimEnv,
) -> DValue {
  let (param_terms, index_terms) = schema_split_terms(
    args,
    spec.params.length(),
  )
  let params : Array[DValue] = []
  for i in 0..<param_terms.length() {
    params.push(lazy_deval(param_terms[i], env, denv))
  }
  let indices : Array[DValue] = []
  for i in 0..<index_terms.length() {
    indices.push(lazy_deval(index_terms[i], env, denv))
  }
  DVInductive(spec, params, indices)
}

///|
pub fn eval_intro_term(
  spec : DInductiveSpec,
  ctor_index : Int32,
  param_terms : Array[DTerm],
  arg_terms : Array[DTerm],
  env : DEnv,
  denv : DDimEnv,
) -> DValue {
  let params : Array[DValue] = []
  for i in 0..<param_terms.length() {
    params.push(lazy_deval(param_terms[i], env, denv))
  }
  let args : Array[DValue] = []
  for i in 0..<arg_terms.length() {
    args.push(lazy_deval(arg_terms[i], env, denv))
  }
  DVIntro(spec, ctor_index, params, args)
}

///|
pub fn eval_inductive_elim_term(
  spec : DInductiveSpec,
  motive : DTerm,
  case_terms : Array[DTerm],
  param_terms : Array[DTerm],
  index_terms : Array[DTerm],
  scrut : DTerm,
  env : DEnv,
  denv : DDimEnv,
) -> DValue {
  let params : Array[DValue] = []
  for i in 0..<param_terms.length() {
    params.push(deval_dim(param_terms[i], env, denv))
  }
  let indices : Array[DValue] = []
  for i in 0..<index_terms.length() {
    indices.push(deval_dim(index_terms[i], env, denv))
  }
  let cases : Array[DValue] = []
  for i in 0..<case_terms.length() {
    cases.push(lazy_deval(case_terms[i], env, denv))
  }
  let motive_value = deval_dim(motive, env, denv)
  eval_inductive_elim(
    spec,
    inductive_motive_from_value(spec, params, motive_value),
    cases,
    params,
    indices,
    deval_dim(scrut, env, denv),
    ddim_len(denv),
  )
}

///|
pub fn infer_inductive_type(
  spec : DInductiveSpec,
  args : Array[DTerm],
  ctx : DEnv,
  env : DEnv,
  denv : DDimEnv,
) -> DInfer? {
  if !inductive_schema_validate(spec) ||
    args.length() != spec.params.length() + spec.indices.length() {
    return None
  }
  let (param_terms, index_terms) = schema_split_terms(
    args,
    spec.params.length(),
  )
  match
    check_telescope_terms(spec.params, param_terms, [], [], ctx, env, denv) {
    Some(params) =>
      match
        check_telescope_terms(
          spec.indices,
          index_terms,
          inductive_param_types(spec, params),
          params,
          ctx,
          env,
          denv,
        ) {
        Some(indices) =>
          Some(DInfer::{
            value: DVInductive(spec, params, indices),
            ty: DVUniv(spec.level),
          })
        None => None
      }
    None => None
  }
}

///|
pub fn infer_intro(
  spec : DInductiveSpec,
  ctor_index : Int32,
  param_terms : Array[DTerm],
  arg_terms : Array[DTerm],
  ctx : DEnv,
  env : DEnv,
  denv : DDimEnv,
) -> DInfer? {
  if !inductive_schema_validate(spec) ||
    ctor_index < 0 ||
    ctor_index >= spec.constructors.length() {
    return None
  }
  let ctor = spec.constructors[ctor_index]
  if arg_terms.length() != ctor.args.length() {
    return None
  }
  match
    check_telescope_terms(spec.params, param_terms, [], [], ctx, env, denv) {
    Some(params) => {
      let args : Array[DValue] = []
      for i in 0..<arg_terms.length() {
        let expected = inductive_arg_type_full(
          spec,
          ctor.args[i],
          schema_arg_spec_prefix(ctor.args, i),
          params,
          args,
        )
        match d_check(arg_terms[i], expected, ctx, env, denv) {
          Some(v) => args.push(v)
          None => return None
        }
      }
      if !schema_constraints_hold(
          denv_len(ctx),
          ddim_len(denv),
          ctor.constraints,
          params,
          args,
        ) {
        return None
      }
      Some(DInfer::{
        value: DVIntro(spec, ctor_index, params, args),
        ty: DVInductive(
          spec,
          params,
          inductive_result_indices(ctor, params, args),
        ),
      })
    }
    None => None
  }
}

///|
pub fn infer_inductive_elim(
  spec : DInductiveSpec,
  motive_term : DTerm,
  case_terms : Array[DTerm],
  param_terms : Array[DTerm],
  index_terms : Array[DTerm],
  scrut : DTerm,
  ctx : DEnv,
  env : DEnv,
  denv : DDimEnv,
) -> DInfer? {
  if !inductive_schema_validate(spec) ||
    case_terms.length() != spec.constructors.length() {
    return None
  }
  match
    check_telescope_terms(spec.params, param_terms, [], [], ctx, env, denv) {
    Some(params) =>
      match
        check_telescope_terms(
          spec.indices,
          index_terms,
          inductive_param_types(spec, params),
          params,
          ctx,
          env,
          denv,
        ) {
        Some(indices) => {
          let target = DVInductive(spec, params, indices)
          let param_types = inductive_param_types(spec, params)
          match
            (
              check_schema_motive(
                motive_term,
                spec.indices,
                param_types,
                params,
                idx => DVInductive(spec, params, idx),
                spec.level,
                ctx,
                env,
                denv,
              ),
              d_check(scrut, target, ctx, env, denv),
            ) {
            (Some(motive_value), Some(scrut_value)) => {
              let motive = inductive_motive_from_value(
                spec, params, motive_value,
              )
              let cases : Array[DValue] = []
              for i in 0..<case_terms.length() {
                match
                  d_check(
                    case_terms[i],
                    inductive_case_type(spec, motive, params, i),
                    ctx,
                    env,
                    denv,
                  ) {
                  Some(v) => cases.push(v)
                  None => return None
                }
              }
              Some(DInfer::{
                value: eval_inductive_elim(
                  spec,
                  motive,
                  cases,
                  params,
                  indices,
                  scrut_value,
                  ddim_len(denv),
                ),
                ty: motive(indices, scrut_value),
              })
            }
            _ => None
          }
        }
        None => None
      }
    None => None
  }
}

///|
pub fn eval_hit_type_term(
  spec : DHitSpec,
  args : Array[DTerm],
  env : DEnv,
  denv : DDimEnv,
) -> DValue {
  let (param_terms, index_terms) = schema_split_terms(
    args,
    spec.params.length(),
  )
  let params : Array[DValue] = []
  for i in 0..<param_terms.length() {
    params.push(lazy_deval(param_terms[i], env, denv))
  }
  let indices : Array[DValue] = []
  for i in 0..<index_terms.length() {
    indices.push(lazy_deval(index_terms[i], env, denv))
  }
  DVHitType(spec, params, indices)
}

///|
pub fn eval_hit_intro_term(
  spec : DHitSpec,
  cell : Int32,
  param_terms : Array[DTerm],
  arg_terms : Array[DTerm],
  dim_terms : Array[Dim],
  env : DEnv,
  denv : DDimEnv,
) -> DValue {
  let params : Array[DValue] = []
  for i in 0..<param_terms.length() {
    params.push(lazy_deval(param_terms[i], env, denv))
  }
  let args : Array[DValue] = []
  for i in 0..<arg_terms.length() {
    args.push(lazy_deval(arg_terms[i], env, denv))
  }
  let dims : Array[Dim] = []
  for i in 0..<dim_terms.length() {
    dims.push(eval_dim_expr(dim_terms[i], denv))
  }
  hit_cell_value(spec, cell, params, args, dims)
}

///|
pub fn eval_hit_elim_term(
  spec : DHitSpec,
  motive : DTerm,
  case_terms : Array[DTerm],
  param_terms : Array[DTerm],
  index_terms : Array[DTerm],
  scrut : DTerm,
  env : DEnv,
  denv : DDimEnv,
) -> DValue {
  let params : Array[DValue] = []
  for i in 0..<param_terms.length() {
    params.push(deval_dim(param_terms[i], env, denv))
  }
  let indices : Array[DValue] = []
  for i in 0..<index_terms.length() {
    indices.push(deval_dim(index_terms[i], env, denv))
  }
  let cases : Array[DValue] = []
  for i in 0..<case_terms.length() {
    cases.push(lazy_deval(case_terms[i], env, denv))
  }
  eval_hit_elim(
    spec,
    hit_motive_from_value(spec, params, deval_dim(motive, env, denv)),
    cases,
    params,
    indices,
    deval_dim(scrut, env, denv),
    ddim_len(denv),
  )
}

///|
pub fn infer_hit_type(
  spec : DHitSpec,
  args : Array[DTerm],
  ctx : DEnv,
  env : DEnv,
  denv : DDimEnv,
) -> DInfer? {
  if !hit_schema_validate(spec) ||
    args.length() != spec.params.length() + spec.indices.length() {
    return None
  }
  let (param_terms, index_terms) = schema_split_terms(
    args,
    spec.params.length(),
  )
  match
    check_telescope_terms(spec.params, param_terms, [], [], ctx, env, denv) {
    Some(params) =>
      match
        check_telescope_terms(
          spec.indices,
          index_terms,
          hit_param_types(spec, params),
          params,
          ctx,
          env,
          denv,
        ) {
        Some(indices) =>
          Some(DInfer::{
            value: DVHitType(spec, params, indices),
            ty: DVUniv(spec.level),
          })
        None => None
      }
    None => None
  }
}

///|
pub fn infer_hit_intro(
  spec : DHitSpec,
  cell_index : Int32,
  param_terms : Array[DTerm],
  arg_terms : Array[DTerm],
  dim_terms : Array[Dim],
  ctx : DEnv,
  env : DEnv,
  denv : DDimEnv,
) -> DInfer? {
  if !hit_schema_validate(spec) ||
    cell_index < 0 ||
    cell_index >= spec.cells.length() {
    return None
  }
  let cell = spec.cells[cell_index]
  if arg_terms.length() != cell.args.length() ||
    dim_terms.length() != cell.dim_count {
    return None
  }
  match
    check_telescope_terms(spec.params, param_terms, [], [], ctx, env, denv) {
    Some(params) => {
      let args : Array[DValue] = []
      for i in 0..<arg_terms.length() {
        match
          d_check(
            arg_terms[i],
            hit_arg_type(spec, cell.args[i], params, args),
            ctx,
            env,
            denv,
          ) {
          Some(v) => args.push(v)
          None => return None
        }
      }
      if !schema_constraints_hold(
          denv_len(ctx),
          ddim_len(denv),
          cell.constraints,
          params,
          args,
        ) {
        return None
      }
      let dims : Array[Dim] = []
      for i in 0..<dim_terms.length() {
        dims.push(eval_dim_expr(dim_terms[i], denv))
      }
      Some(DInfer::{
        value: hit_cell_value(spec, cell_index, params, args, dims),
        ty: DVHitType(
          spec,
          params,
          hit_cell_result_indices(spec, cell_index, params, args),
        ),
      })
    }
    None => None
  }
}

///|
pub fn infer_hit_elim(
  spec : DHitSpec,
  motive_term : DTerm,
  case_terms : Array[DTerm],
  param_terms : Array[DTerm],
  index_terms : Array[DTerm],
  scrut : DTerm,
  ctx : DEnv,
  env : DEnv,
  denv : DDimEnv,
) -> DInfer? {
  if !hit_schema_validate(spec) || case_terms.length() != spec.cells.length() {
    return None
  }
  match
    check_telescope_terms(spec.params, param_terms, [], [], ctx, env, denv) {
    Some(params) =>
      match
        check_telescope_terms(
          spec.indices,
          index_terms,
          hit_param_types(spec, params),
          params,
          ctx,
          env,
          denv,
        ) {
        Some(indices) => {
          let target = DVHitType(spec, params, indices)
          let param_types = hit_param_types(spec, params)
          match
            (
              check_schema_motive(
                motive_term,
                spec.indices,
                param_types,
                params,
                idx => DVHitType(spec, params, idx),
                spec.level,
                ctx,
                env,
                denv,
              ),
              d_check(scrut, target, ctx, env, denv),
            ) {
            (Some(motive_value), Some(scrut_value)) => {
              let motive = hit_motive_from_value(spec, params, motive_value)
              // Raw case closures instantiate the PathP endpoints in
              // generated case types; checked values replace them as
              // elaboration proceeds.
              let cases : Array[DValue] = []
              for i in 0..<case_terms.length() {
                cases.push(deval_dim(case_terms[i], env, denv))
              }
              for i in 0..<case_terms.length() {
                match
                  d_check(
                    case_terms[i],
                    hit_case_type(
                      spec,
                      motive,
                      cases,
                      params,
                      i,
                      ddim_len(denv),
                    ),
                    ctx,
                    env,
                    denv,
                  ) {
                  Some(v) => cases[i] = v
                  None => return None
                }
              }
              Some(DInfer::{
                value: eval_hit_elim(
                  spec,
                  motive,
                  cases,
                  params,
                  indices,
                  scrut_value,
                  ddim_len(denv),
                ),
                ty: motive(indices, scrut_value),
              })
            }
            _ => None
          }
        }
        None => None
      }
    None => None
  }
}

// ---------------------------------------------------------------------------
// Generic conversion and quoting for schema telescopes/arguments
// ---------------------------------------------------------------------------

///|
pub fn conv_telescope_values(
  level : Int32,
  dlevel : Int32,
  entries : Array[DTelescopeEntry],
  prefix_types : Array[DValue],
  prefix_values : Array[DValue],
  a : Array[DValue],
  b : Array[DValue],
) -> Bool {
  if a.length() != b.length() || a.length() != entries.length() {
    return false
  }
  let prior : Array[DValue] = []
  let prior_types : Array[DValue] = []
  for i in 0..<a.length() {
    let ty = telescope_next_type(
      entries, prefix_types, prefix_values, prior_types, prior,
    )
    prior_types.push(ty)
    if !conv_at(level, dlevel, ty, a[i], b[i]) {
      return false
    }
    prior.push(a[i])
  }
  true
}

///|
pub fn quote_telescope_values(
  level : Int32,
  dlevel : Int32,
  entries : Array[DTelescopeEntry],
  prefix_types : Array[DValue],
  prefix_values : Array[DValue],
  values : Array[DValue],
) -> Array[DTerm] {
  let out : Array[DTerm] = []
  let prior : Array[DValue] = []
  let prior_types : Array[DValue] = []
  for i in 0..<values.length() {
    let ty = if i < entries.length() {
      telescope_next_type(
        entries, prefix_types, prefix_values, prior_types, prior,
      )
    } else {
      DVUnitTy
    }
    prior_types.push(ty)
    out.push(quote_at(level, dlevel, ty, values[i]))
    prior.push(values[i])
  }
  out
}

///|
pub fn conv_schema_args(
  level : Int32,
  dlevel : Int32,
  args : Array[DConstructorArg],
  params : Array[DValue],
  family : (Array[DValue]) -> DValue,
  a : Array[DValue],
  b : Array[DValue],
) -> Bool {
  if a.length() != b.length() || a.length() != args.length() {
    return false
  }
  let prior : Array[DValue] = []
  for i in 0..<a.length() {
    let ty = schema_arg_type(args[i], params, prior, family)
    if !conv_at(level, dlevel, ty, a[i], b[i]) {
      return false
    }
    prior.push(a[i])
  }
  true
}

///|
pub fn quote_schema_args(
  level : Int32,
  dlevel : Int32,
  args : Array[DConstructorArg],
  params : Array[DValue],
  family : (Array[DValue]) -> DValue,
  values : Array[DValue],
) -> Array[DTerm] {
  let out : Array[DTerm] = []
  let prior : Array[DValue] = []
  for i in 0..<values.length() {
    let ty = if i < args.length() {
      schema_arg_type(args[i], params, prior, family)
    } else {
      DVUnitTy
    }
    out.push(quote_at(level, dlevel, ty, values[i]))
    prior.push(values[i])
  }
  out
}

///|
fn schema_motives_conv_loop(
  level : Int32,
  dlevel : Int32,
  current : Int32,
  entries : Array[DTelescopeEntry],
  pos : Int32,
  param_types : Array[DValue],
  params : Array[DValue],
  prior : Array[DValue],
  family : (Array[DValue]) -> DValue,
  m1 : (Array[DValue], DValue) -> DValue,
  m2 : (Array[DValue], DValue) -> DValue,
) -> Bool {
  if pos >= entries.length() {
    let scrut = DVNeutral(DNVar(current))
    conv_ty(current + 1, dlevel, m1(prior, scrut), m2(prior, scrut))
  } else {
    let _ = family
    let fresh = DVNeutral(DNVar(current))
    schema_motives_conv_loop(
      level,
      dlevel,
      current + 1,
      entries,
      pos + 1,
      param_types,
      params,
      schema_concat_values(prior, [fresh]),
      family,
      m1,
      m2,
    )
  }
}

///|
pub fn schema_motives_conv(
  level : Int32,
  dlevel : Int32,
  entries : Array[DTelescopeEntry],
  param_types : Array[DValue],
  params : Array[DValue],
  family : (Array[DValue]) -> DValue,
  m1 : (Array[DValue], DValue) -> DValue,
  m2 : (Array[DValue], DValue) -> DValue,
) -> Bool {
  schema_motives_conv_loop(
    level,
    dlevel,
    level,
    entries,
    0,
    param_types,
    params,
    [],
    family,
    m1,
    m2,
  )
}

///|
fn quote_schema_motive_loop(
  level : Int32,
  dlevel : Int32,
  entries : Array[DTelescopeEntry],
  pos : Int32,
  param_types : Array[DValue],
  params : Array[DValue],
  prior : Array[DValue],
  prior_types : Array[DValue],
  family : (Array[DValue]) -> DValue,
  motive : (Array[DValue], DValue) -> DValue,
) -> DTerm {
  if pos >= entries.length() {
    DLam(
      quote_ty(level, dlevel, family(prior)),
      quote_ty(level + 1, dlevel, motive(prior, DVNeutral(DNVar(level)))),
    )
  } else {
    let ty = telescope_next_type(
      entries, param_types, params, prior_types, prior,
    )
    DLam(
      quote_ty(level, dlevel, ty),
      quote_schema_motive_loop(
        level + 1,
        dlevel,
        entries,
        pos + 1,
        param_types,
        params,
        schema_concat_values(prior, [DVNeutral(DNVar(level))]),
        schema_concat_values(prior_types, [ty]),
        family,
        motive,
      ),
    )
  }
}

///|
pub fn quote_schema_motive(
  level : Int32,
  dlevel : Int32,
  entries : Array[DTelescopeEntry],
  param_types : Array[DValue],
  params : Array[DValue],
  family : (Array[DValue]) -> DValue,
  motive : (Array[DValue], DValue) -> DValue,
) -> DTerm {
  quote_schema_motive_loop(
    level,
    dlevel,
    entries,
    0,
    param_types,
    params,
    [],
    [],
    family,
    motive,
  )
}

///|
pub fn conv_inductive_type(
  level : Int32,
  dlevel : Int32,
  s1 : DInductiveSpec,
  p1 : Array[DValue],
  i1 : Array[DValue],
  s2 : DInductiveSpec,
  p2 : Array[DValue],
  i2 : Array[DValue],
) -> Bool {
  s1 == s2 &&
  conv_telescope_values(level, dlevel, s1.params, [], [], p1, p2) &&
  conv_telescope_values(
    level,
    dlevel,
    s1.indices,
    inductive_param_types(s1, p1),
    p1,
    i1,
    i2,
  )
}

///|
pub fn conv_intro_at(
  level : Int32,
  dlevel : Int32,
  spec : DInductiveSpec,
  params : Array[DValue],
  a : DValue,
  b : DValue,
) -> Bool {
  match (force_value(a), force_value(b)) {
    (DVIntro(s1, c1, p1, args1), DVIntro(s2, c2, p2, args2)) =>
      s1 == spec &&
      s2 == spec &&
      c1 == c2 &&
      c1 >= 0 &&
      c1 < spec.constructors.length() &&
      conv_telescope_values(level, dlevel, spec.params, [], [], p1, p2) &&
      conv_schema_args_full(
        level,
        dlevel,
        spec.constructors[c1].args,
        params,
        idx => DVInductive(spec, params, idx),
        (idx, code) => eval_inductive_decode(spec, params, idx, code, dlevel),
        args1,
        args2,
      )
    (DVNeutral(x), DVNeutral(y)) => conv_neutral(level, dlevel, x, y)
    _ => false
  }
}

///|
pub fn quote_inductive_type(
  level : Int32,
  dlevel : Int32,
  spec : DInductiveSpec,
  params : Array[DValue],
  indices : Array[DValue],
) -> DTerm {
  let param_terms = quote_telescope_values(
    level,
    dlevel,
    spec.params,
    [],
    [],
    params,
  )
  let index_terms = quote_telescope_values(
    level,
    dlevel,
    spec.indices,
    inductive_param_types(spec, params),
    params,
    indices,
  )
  let all : Array[DTerm] = []
  for i in 0..<param_terms.length() {
    all.push(param_terms[i])
  }
  for i in 0..<index_terms.length() {
    all.push(index_terms[i])
  }
  DInductive(spec, all)
}

///|
pub fn quote_intro_at(
  level : Int32,
  dlevel : Int32,
  spec : DInductiveSpec,
  params : Array[DValue],
  ty : DValue,
  v : DValue,
) -> DTerm {
  match force_value(v) {
    DVIntro(_, ctor, intro_params, args) =>
      if ctor < 0 || ctor >= spec.constructors.length() {
        DUnitLit
      } else {
        DIntro(
          spec,
          ctor,
          quote_telescope_values(
            level,
            dlevel,
            spec.params,
            [],
            [],
            intro_params,
          ),
          quote_schema_args_full(
            level,
            dlevel,
            spec.constructors[ctor].args,
            params,
            idx => DVInductive(spec, params, idx),
            (idx, code) => {
              eval_inductive_decode(spec, params, idx, code, dlevel)
            },
            args,
          ),
        )
      }
    DVNeutral(n) => quote_dneutral(level, dlevel, n, ty)
    _ => DUnitLit
  }
}

///|
pub fn hit_arg_type(
  spec : DHitSpec,
  arg : DConstructorArg,
  params : Array[DValue],
  prior : Array[DValue],
) -> DValue {
  schema_arg_type(arg, params, prior, idx => DVHitType(spec, params, idx))
}

///|
pub fn hit_result_indices(
  cell : DHitCellSpec,
  params : Array[DValue],
  args : Array[DValue],
) -> Array[DValue] {
  schema_eval_index_terms(params, args, cell.result_index)
}

///|
pub fn conv_hit_type(
  level : Int32,
  dlevel : Int32,
  s1 : DHitSpec,
  p1 : Array[DValue],
  i1 : Array[DValue],
  s2 : DHitSpec,
  p2 : Array[DValue],
  i2 : Array[DValue],
) -> Bool {
  s1 == s2 &&
  conv_telescope_values(level, dlevel, s1.params, [], [], p1, p2) &&
  conv_telescope_values(
    level,
    dlevel,
    s1.indices,
    hit_param_types(s1, p1),
    p1,
    i1,
    i2,
  )
}

///|
pub fn conv_hit_cell_at(
  level : Int32,
  dlevel : Int32,
  spec : DHitSpec,
  params : Array[DValue],
  a : DValue,
  b : DValue,
) -> Bool {
  match (hit_normalized(a), hit_normalized(b)) {
    (DVHitCell(s1, c1, p1, args1, dims1), DVHitCell(s2, c2, p2, args2, dims2)) => {
      let mut ok = s1 == spec &&
        s2 == spec &&
        c1 == c2 &&
        c1 >= 0 &&
        c1 < spec.cells.length() &&
        dims1.length() == dims2.length() &&
        conv_telescope_values(level, dlevel, spec.params, [], [], p1, p2)
      for i in 0..<dims1.length() {
        if i >= dims2.length() || !dim_eq_sem(dims1[i], dims2[i]) {
          ok = false
        }
      }
      ok &&
      conv_schema_args(
        level,
        dlevel,
        spec.cells[c1].args,
        params,
        idx => DVHitType(spec, params, idx),
        args1,
        args2,
      )
    }
    (DVNeutral(x), DVNeutral(y)) => conv_neutral(level, dlevel, x, y)
    _ => false
  }
}

///|
pub fn quote_hit_type(
  level : Int32,
  dlevel : Int32,
  spec : DHitSpec,
  params : Array[DValue],
  indices : Array[DValue],
) -> DTerm {
  let param_terms = quote_telescope_values(
    level,
    dlevel,
    spec.params,
    [],
    [],
    params,
  )
  let index_terms = quote_telescope_values(
    level,
    dlevel,
    spec.indices,
    hit_param_types(spec, params),
    params,
    indices,
  )
  let all : Array[DTerm] = []
  for i in 0..<param_terms.length() {
    all.push(param_terms[i])
  }
  for i in 0..<index_terms.length() {
    all.push(index_terms[i])
  }
  DHitType(spec, all)
}

///|
pub fn quote_hit_cell_at(
  level : Int32,
  dlevel : Int32,
  spec : DHitSpec,
  params : Array[DValue],
  ty : DValue,
  v : DValue,
) -> DTerm {
  match hit_normalized(v) {
    DVHitCell(_, cell, cell_params, args, dims) =>
      if cell < 0 || cell >= spec.cells.length() {
        DUnitLit
      } else {
        let quoted_dims : Array[Dim] = []
        for i in 0..<dims.length() {
          quoted_dims.push(dim_quote(dims[i], dlevel))
        }
        DHitIntro(
          spec,
          cell,
          quote_telescope_values(
            level,
            dlevel,
            spec.params,
            [],
            [],
            cell_params,
          ),
          quote_schema_args(
            level,
            dlevel,
            spec.cells[cell].args,
            params,
            idx => DVHitType(spec, params, idx),
            args,
          ),
          quoted_dims,
        )
      }
    DVNeutral(n) => quote_dneutral(level, dlevel, n, ty)
    _ => DUnitLit
  }
}

// ---------------------------------------------------------------------------
// Canonical generated schemas and term builders
// ---------------------------------------------------------------------------

///|
pub fn schema_type_term(spec : DInductiveSpec, args : Array[DTerm]) -> DTerm {
  DInductive(spec, args)
}

///|
pub fn schema_intro_term(
  spec : DInductiveSpec,
  ctor : Int32,
  params : Array[DTerm],
  args : Array[DTerm],
) -> DTerm {
  DIntro(spec, ctor, params, args)
}

///|
pub fn schema_elim_term(
  spec : DInductiveSpec,
  motive : DTerm,
  cases : Array[DTerm],
  params : Array[DTerm],
  indices : Array[DTerm],
  scrut : DTerm,
) -> DTerm {
  DInductiveElim(spec, motive, cases, params, indices, scrut)
}

///|
pub fn nat_schema() -> DInductiveSpec {
  dinductive_spec("NatS", 0, [], [], [
    dconstructor_spec("zero", []),
    dconstructor_spec("succ", [darg_recursive("pred")]),
  ])
}

///|
pub fn bool_schema() -> DInductiveSpec {
  dinductive_spec("BoolS", 0, [], [], [
    dconstructor_spec("false", []),
    dconstructor_spec("true", []),
  ])
}

///|
pub fn list_schema() -> DInductiveSpec {
  dinductive_spec("ListS", 0, [dtelescope_entry("A", DUniv(0))], [], [
    dconstructor_spec("nil", []),
    dconstructor_spec("cons", [
      darg_external("head", DTVar(0)),
      darg_recursive("tail"),
    ]),
  ])
}

///|
pub fn vec_schema() -> DInductiveSpec {
  dinductive_spec(
    "VecS",
    0,
    [dtelescope_entry("A", DUniv(0))],
    [dtelescope_entry("length", DNatTy)],
    [
      dconstructor_spec("nil", [], result_index=[DNatZero]),
      dconstructor_spec(
        "cons",
        [
          darg_external("head", DTVar(0)),
          darg_external("tail_length", DNatTy),
          darg_recursive("tail", index=[DTVar(0)]),
        ],
        result_index=[DSucc(DTVar(1))],
      ),
    ],
  )
}

///|
pub fn fin_schema() -> DInductiveSpec {
  dinductive_spec("FinS", 0, [], [dtelescope_entry("bound", DNatTy)], [
    dconstructor_spec("fzero", [darg_external("pred_bound", DNatTy)], result_index=[
      DSucc(DTVar(0)),
    ]),
    dconstructor_spec(
      "fsucc",
      [
        darg_external("pred_bound", DNatTy),
        darg_recursive("value", index=[DTVar(0)]),
      ],
      result_index=[DSucc(DTVar(1))],
    ),
  ])
}

///|
pub fn tree_schema() -> DInductiveSpec {
  dinductive_spec("TreeS", 0, [dtelescope_entry("A", DUniv(0))], [], [
    dconstructor_spec("leaf", [darg_external("label", DTVar(0))]),
    dconstructor_spec("node", [darg_recursive("left"), darg_recursive("right")]),
  ])
}

///|
pub fn w_schema() -> DInductiveSpec {
  dinductive_spec(
    "WS",
    0,
    [
      dtelescope_entry("A", DUniv(0)),
      dtelescope_entry("B", DPi(DTVar(0), DUniv(0))),
    ],
    [],
    [
      dconstructor_spec("sup", [
        darg_external("label", DTVar(1)),
        darg_function("branches", DApp(DTVar(1), DTVar(0))),
      ]),
    ],
  )
}

///|
pub fn nat_schema_lit(n : Int32) -> DTerm {
  let spec = nat_schema()
  let mut out = schema_intro_term(spec, 0, [], [])
  for _i in 0..<n {
    out = schema_intro_term(spec, 1, [], [out])
  }
  out
}

///|
pub fn schema_examples() -> Array[DInductiveSpec] {
  [
    nat_schema(),
    bool_schema(),
    list_schema(),
    vec_schema(),
    fin_schema(),
    tree_schema(),
    w_schema(),
  ]
}

// ---------------------------------------------------------------------------
// Generated Kan composition over constructor/cell arguments
// ---------------------------------------------------------------------------

///|
fn comp_schema_arg_branches(
  branches : DSystem,
  pos : Int32,
  arg_value : (Int32, Dim, Int32) -> DValue,
) -> DSystem {
  let out : Array[DTubeBranch] = []
  for slot in 0..<branches.branches.length() {
    let br = branches.branches[slot]
    out.push(tube_branch(br.face, j => arg_value(slot, j, pos)))
  }
  DSystem::{ branches: out, }
}

///|
fn comp_schema_args_loop(
  args : Array[DConstructorArg],
  pos : Int32,
  params_line : (Dim) -> Array[DValue],
  family : (Array[DValue], Array[DValue]) -> DValue,
  decode : (Array[DValue], Array[DValue], DValue) -> DValue,
  branches : DSystem,
  arg_value : (Int32, Dim, Int32) -> DValue,
  fills : Array[(Dim) -> DValue],
  out : Array[DValue],
  dlevel : Int32,
) -> Array[DValue] {
  if pos >= args.length() {
    out
  } else {
    let arg = args[pos]
    let prior_fills : Array[(Dim) -> DValue] = []
    for k in 0..<fills.length() {
      prior_fills.push(fills[k])
    }
    let type_line = (j : Dim) => {
      let prior : Array[DValue] = []
      for k in 0..<prior_fills.length() {
        prior.push(prior_fills[k](j))
      }
      let params_j = params_line(j)
      schema_arg_type_full(
        arg,
        schema_arg_spec_prefix(args, pos),
        params_j,
        prior,
        idx => family(params_j, idx),
        (idx, code) => decode(params_j, idx, code),
      )
    }
    let fill = fill_value(
      type_line,
      comp_schema_arg_branches(branches, pos, arg_value),
      arg_value(-1, DZero, pos),
      dlevel,
    )
    let target = fill(DOne)
    fills.push(fill)
    out.push(target)
    comp_schema_args_loop(
      args,
      pos + 1,
      params_line,
      family,
      decode,
      branches,
      arg_value,
      fills,
      out,
      dlevel,
    )
  }
}

///|
/// Compose constructor/cell arguments one at a time.  The type of
/// each later argument is evaluated along fillers of earlier
/// arguments, exactly as in the Sigma composition rule.
pub fn comp_schema_args(
  args : Array[DConstructorArg],
  params_line : (Dim) -> Array[DValue],
  family : (Array[DValue], Array[DValue]) -> DValue,
  branches : DSystem,
  arg_value : (Int32, Dim, Int32) -> DValue,
  dlevel : Int32,
) -> Array[DValue] {
  comp_schema_args_loop(
    args,
    0,
    params_line,
    family,
    (_, _, _) => DVUnitTy,
    branches,
    arg_value,
    [],
    [],
    dlevel,
  )
}

///|
/// Decode-aware form of `comp_schema_args`, used for
/// induction-recursive families.
pub fn comp_schema_args_decoded(
  args : Array[DConstructorArg],
  params_line : (Dim) -> Array[DValue],
  family : (Array[DValue], Array[DValue]) -> DValue,
  decode : (Array[DValue], Array[DValue], DValue) -> DValue,
  branches : DSystem,
  arg_value : (Int32, Dim, Int32) -> DValue,
  dlevel : Int32,
) -> Array[DValue] {
  comp_schema_args_loop(
    args,
    0,
    params_line,
    family,
    decode,
    branches,
    arg_value,
    [],
    [],
    dlevel,
  )
}

///|
fn intro_args_of(v : DValue) -> Array[DValue]? {
  match force_value(v) {
    DVIntro(_, _, _, args) => Some(args)
    _ => None
  }
}

///|
pub fn comp_inductive_value(
  line : (Dim) -> DValue,
  branches : DSystem,
  base : DValue,
  dlevel : Int32,
) -> DValue {
  match force_value(line(DVar(dlevel))) {
    DVInductive(spec, _params, _indices) => {
      if spec.params.length() == 0 &&
        spec.indices.length() == 0 &&
        branches.branches.length() == 0 {
        return base
      }
      let mut ctor = -1
      let mut base_args : Array[DValue] = []
      let mut ok = true
      match force_value(base) {
        DVIntro(s, c, _, args) =>
          if s == spec && c >= 0 && c < spec.constructors.length() {
            ctor = c
            base_args = args
          } else {
            ok = false
          }
        _ => ok = false
      }
      if ok {
        for i in 0..<branches.branches.length() {
          match force_value((branches.branches[i].path)(DVar(dlevel))) {
            DVIntro(s, c, _, _) => if s != spec || c != ctor { ok = false }
            _ => ok = false
          }
        }
      }
      if !ok {
        DVNeutral(DNComp(line, branches, base))
      } else {
        let params_line = (j : Dim) => {
          let (p, _) = inductive_family_parts(line(j), _params, _indices)
          p
        }
        let arg_value = (slot : Int32, j : Dim, pos : Int32) => {
          let args = if slot < 0 {
            base_args
          } else {
            match intro_args_of((branches.branches[slot].path)(j)) {
              Some(xs) => xs
              None => []
            }
          }
          if pos >= 0 && pos < args.length() {
            args[pos]
          } else {
            DVUnit
          }
        }
        let composed = comp_schema_args_decoded(
          spec.constructors[ctor].args,
          params_line,
          (p, idx) => DVInductive(spec, p, idx),
          (p, idx, code) => eval_inductive_decode(spec, p, idx, code, dlevel),
          branches,
          arg_value,
          dlevel,
        )
        if schema_constraints_hold(
            10000,
            dlevel,
            spec.constructors[ctor].constraints,
            params_line(DOne),
            composed,
          ) {
          DVIntro(spec, ctor, params_line(DOne), composed)
        } else {
          // A propositional constructor constraint is not in general
          // preserved by an arbitrary filler; the formal composition
          // is then the correct stuck normal form.
          DVNeutral(DNComp(line, branches, base))
        }
      }
    }
    _ => DVNeutral(DNComp(line, branches, base))
  }
}

///|
fn hit_dim_substitute(d : Dim, variable : Int32, replacement : Dim) -> Dim {
  match d {
    DVar(i) => if i == variable { replacement } else { d }
    DNeg(a) => dim_simplify(DNeg(hit_dim_substitute(a, variable, replacement)))
    DAnd(a, b) =>
      dim_simplify(
        DAnd(
          hit_dim_substitute(a, variable, replacement),
          hit_dim_substitute(b, variable, replacement),
        ),
      )
    DOr(a, b) =>
      dim_simplify(
        DOr(
          hit_dim_substitute(a, variable, replacement),
          hit_dim_substitute(b, variable, replacement),
        ),
      )
    other => other
  }
}

///|
fn hit_dims_substitute(
  dims : Array[Dim],
  variable : Int32,
  replacement : Dim,
) -> Array[Dim] {
  let out : Array[Dim] = []
  for i in 0..<dims.length() {
    out.push(hit_dim_substitute(dims[i], variable, replacement))
  }
  out
}

///|
fn hit_raw_cell_args_of(v : DValue, cell_index : Int32) -> Array[DValue] {
  match force_value(v) {
    DVHitCell(_, c, _, args, _) =>
      if c == cell_index {
        args
      } else {
        hit_cell_args_of(v)
      }
    _ => hit_cell_args_of(v)
  }
}

///|
pub fn comp_hit_value(
  line : (Dim) -> DValue,
  branches : DSystem,
  base : DValue,
  dlevel : Int32,
) -> DValue {
  match force_value(line(DVar(dlevel))) {
    DVHitType(spec, fallback_params, fallback_indices) => {
      let mut cell_index = -1
      let mut base_dims : Array[Dim] = []
      let mut target_dims : Array[Dim] = []
      let mut base_args : Array[DValue] = []
      let mut ok = true
      match hit_normalized(base) {
        DVHitCell(s, c, _, args, dims) =>
          if s == spec && c >= 0 && c < spec.cells.length() {
            cell_index = c
            base_args = args
            base_dims = dims
            target_dims = dims
          } else {
            ok = false
          }
        _ => ok = false
      }
      // Moving-dimension lift: the normalized base may be a face of
      // the common raw cell carried by the tube.  If that cell at
      // the composition origin is convertible to the base, compose
      // in the higher cell and let `hit_cell_value` take the target
      // face at the end.  This computes compositions that traverse
      // from a face into a cell interior when the tube itself
      // supplies that cell uniformly.
      if branches.branches.length() > 0 {
        match force_value((branches.branches[0].path)(DVar(dlevel))) {
          DVHitCell(s, candidate, _, _, _) =>
            if s == spec && candidate != cell_index {
              match force_value((branches.branches[0].path)(DZero)) {
                DVHitCell(s0, c0, p0, args0, dims0) =>
                  if s0 == spec && c0 == candidate {
                    let candidate_base = hit_cell_value(
                      spec, candidate, p0, args0, dims0,
                    )
                    if conv_at(10000, dlevel, line(DZero), candidate_base, base) {
                      cell_index = candidate
                      base_args = args0
                      base_dims = dims0
                      target_dims = dims0
                      ok = true
                    }
                  }
                _ => ()
              }
            }
          _ => ()
        }
      }
      if ok {
        // The tube may move inside one fixed cell.  Read the cell
        // dimensions at the generic composition point; substituting
        // the composition variable by 0 and 1 gives the required
        // base and target dimensions.  All branches must determine
        // the same target dimensions.  Compositions that genuinely
        // traverse between different cells remain formal HIT points.
        for i in 0..<branches.branches.length() {
          let branch_raw = force_value(
            (branches.branches[i].path)(DVar(dlevel)),
          )
          let branch_value = match branch_raw {
            DVHitCell(_, c, _, _, _) =>
              if c == cell_index {
                branch_raw
              } else {
                hit_normalized(branch_raw)
              }
            _ => hit_normalized(branch_raw)
          }
          match branch_value {
            DVHitCell(s, c, _, _, dims) =>
              if s != spec || c != cell_index {
                ok = false
              } else {
                let at_zero = hit_dims_substitute(dims, dlevel, DZero)
                let at_one = hit_dims_substitute(dims, dlevel, DOne)
                if !hit_dims_eq(at_zero, base_dims) {
                  ok = false
                } else if i == 0 {
                  target_dims = at_one
                } else if !hit_dims_eq(at_one, target_dims) {
                  ok = false
                }
              }
            _ => ok = false
          }
        }
      }
      if !ok {
        DVNeutral(DNComp(line, branches, base))
      } else {
        let params_line = (j : Dim) => {
          let (p, _) = hit_family_parts(
            line(j),
            fallback_params,
            fallback_indices,
          )
          p
        }
        let arg_value = (slot : Int32, j : Dim, pos : Int32) => {
          let args = if slot < 0 {
            base_args
          } else {
            hit_raw_cell_args_of((branches.branches[slot].path)(j), cell_index)
          }
          if pos >= 0 && pos < args.length() {
            args[pos]
          } else {
            DVUnit
          }
        }
        let composed = comp_schema_args(
          spec.cells[cell_index].args,
          params_line,
          (p, idx) => DVHitType(spec, p, idx),
          branches,
          arg_value,
          dlevel,
        )
        if schema_constraints_hold(
            10000,
            dlevel,
            spec.cells[cell_index].constraints,
            params_line(DOne),
            composed,
          ) {
          hit_cell_value(
            spec,
            cell_index,
            params_line(DOne),
            composed,
            target_dims,
          )
        } else {
          DVNeutral(DNComp(line, branches, base))
        }
      }
    }
    _ => DVNeutral(DNComp(line, branches, base))
  }
}

// ---------------------------------------------------------------------------
// Generated higher inductive types
// ---------------------------------------------------------------------------

///|
pub fn hit_motive_type(spec : DHitSpec, params : Array[DValue]) -> DValue {
  schema_motive_type_loop(
    spec.indices,
    0,
    hit_param_types(spec, params),
    params,
    [],
    [],
    idx => DVHitType(spec, params, idx),
    spec.level,
  )
}

///|
fn hit_motive_from_value(
  spec : DHitSpec,
  params : Array[DValue],
  motive_value : DValue,
) -> (Array[DValue], DValue) -> DValue {
  (indices : Array[DValue], scrut : DValue) => {
    schema_apply_motive(
      motive_value,
      hit_index_types(spec, params, indices),
      DVHitType(spec, params, indices),
      indices,
      scrut,
    )
  }
}

///|
pub fn hit_cell_result_indices(
  spec : DHitSpec,
  cell_index : Int32,
  params : Array[DValue],
  args : Array[DValue],
) -> Array[DValue] {
  if cell_index < 0 || cell_index >= spec.cells.length() {
    []
  } else {
    hit_result_indices(spec.cells[cell_index], params, args)
  }
}

///|
fn hit_scrut_result_indices(
  spec : DHitSpec,
  fallback : Array[DValue],
  scrut : DValue,
) -> Array[DValue] {
  match force_value(scrut) {
    DVHitCell(_, cell, p, args, _) =>
      hit_cell_result_indices(spec, cell, p, args)
    _ => fallback
  }
}

///|
fn hit_face_instantiate(
  spec : DHitSpec,
  params : Array[DValue],
  args : Array[DValue],
  dims : Array[Dim],
  face : DHitFaceExpr,
) -> DValue {
  let values = schema_concat_values(params, args)
  let term_env = schema_env(values)
  let dim_env = schema_dim_env(dims)
  if face.cell < 0 {
    if face.args.length() == 1 {
      return deval_dim(face.args[0], term_env, dim_env)
    } else {
      return DVUnit
    }
  }
  let face_args : Array[DValue] = []
  for i in 0..<face.args.length() {
    face_args.push(deval_dim(face.args[i], term_env, dim_env))
  }
  let face_dims : Array[Dim] = []
  for i in 0..<face.dims.length() {
    face_dims.push(eval_dim_expr(face.dims[i], dim_env))
  }
  hit_cell_value(spec, face.cell, params, face_args, face_dims)
}

///|
/// The smart constructor for a generated HIT cell.  If any dimension
/// is an endpoint, the corresponding face expression is instantiated
/// (recursively), giving the usual point/path/square reductions.
pub fn hit_cell_value(
  spec : DHitSpec,
  cell_index : Int32,
  params : Array[DValue],
  args : Array[DValue],
  dims0 : Array[Dim],
) -> DValue {
  if cell_index < 0 || cell_index >= spec.cells.length() {
    return DVUnit
  }
  let cell = spec.cells[cell_index]
  let dims : Array[Dim] = []
  for i in 0..<cell.dim_count {
    if i < dims0.length() {
      dims.push(dim_simplify(dims0[i]))
    } else {
      dims.push(DZero)
    }
  }
  for i in 0..<dims.length() {
    let end = if dim_is_zero(dims[i]) {
      0
    } else if dim_is_one(dims[i]) {
      1
    } else {
      -1
    }
    if end >= 0 {
      let face_index = 2 * i + end
      if face_index < cell.faces.length() {
        return hit_face_instantiate(
          spec,
          params,
          args,
          dims,
          cell.faces[face_index],
        )
      }
    }
  }
  DVHitCell(spec, cell_index, params, args, dims)
}

///|
fn hit_reduce_dimension(
  spec : DHitSpec,
  cell_index : Int32,
  params : Array[DValue],
  args : Array[DValue],
  dims : Array[Dim],
  dim_index : Int32,
) -> DValue {
  if cell_index < 0 ||
    cell_index >= spec.cells.length() ||
    dim_index < 0 ||
    dim_index >= dims.length() {
    return hit_cell_value(spec, cell_index, params, args, dims)
  }
  let cell = spec.cells[cell_index]
  let end = if dim_is_zero(dims[dim_index]) {
    0
  } else if dim_is_one(dims[dim_index]) {
    1
  } else {
    -1
  }
  if end < 0 {
    hit_cell_value(spec, cell_index, params, args, dims)
  } else {
    let face_index = 2 * dim_index + end
    if face_index < cell.faces.length() {
      hit_face_instantiate(spec, params, args, dims, cell.faces[face_index])
    } else {
      DVUnit
    }
  }
}

///|
fn schema_apply_case(
  argspecs : Array[DConstructorArg],
  constraints : Array[DConstructorConstraint],
  case_value : DValue,
  params : Array[DValue],
  args : Array[DValue],
  motive : (Array[DValue], DValue) -> DValue,
  family : (Array[DValue]) -> DValue,
  elim : (Array[DValue], DValue) -> DValue,
  decode : (Array[DValue], DValue) -> DValue,
) -> DValue {
  let mut cur = case_value
  let prior : Array[DValue] = []
  for i in 0..<args.length() {
    if i >= argspecs.length() {
      break
    }
    let arg_spec = argspecs[i]
    let arg = args[i]
    let arg_ty = schema_arg_type_full(
      arg_spec,
      schema_arg_spec_prefix(argspecs, i),
      params,
      prior,
      family,
      decode,
    )
    cur = dapp_typed(cur, arg, arg_ty)
    match arg_spec.kind {
      DArgExternal | DArgDecoded => ()
      DArgRecursive => {
        let idx = schema_eval_index_terms(params, prior, arg_spec.index)
        cur = dapp_typed(cur, elim(idx, arg), motive(idx, arg))
      }
      DArgFunction => {
        let dom = schema_eval_under(
          arg_spec.ty,
          schema_concat_values(params, prior),
          [],
        )
        let prior_copy = schema_concat_values([], prior)
        let ih : DValue = DVLam(a => {
          let idx = schema_eval_index_terms(
            params,
            schema_concat_values(prior_copy, [a]),
            arg_spec.index,
          )
          elim(idx, dapp_typed(arg, a, dom))
        })
        let ih_ty = DVPi(dom, a => {
          let idx = schema_eval_index_terms(
            params,
            schema_concat_values(prior, [a]),
            arg_spec.index,
          )
          motive(idx, dapp_typed(arg, a, dom))
        })
        cur = dapp_typed(cur, ih, ih_ty)
      }
      DArgNested => {
        let ih = positive_functor_map(
          arg_spec.nested,
          params,
          prior,
          family,
          motive,
          elim,
          arg,
        )
        let ih_ty = positive_functor_ih_type(
          arg_spec.nested,
          params,
          prior,
          family,
          motive,
          arg,
        )
        cur = dapp_typed(cur, ih, ih_ty)
      }
      DArgDecodedFunction => {
        let prior_specs = schema_arg_spec_prefix(argspecs, i)
        let dom = decode(
          schema_source_indices(arg_spec, prior_specs, params, prior),
          schema_source_value(arg_spec, prior),
        )
        let prior_copy = schema_concat_values([], prior)
        let ih : DValue = DVLam(a => {
          let idx = schema_eval_index_terms(
            params,
            schema_concat_values(prior_copy, [a]),
            arg_spec.index,
          )
          elim(idx, dapp_typed(arg, a, dom))
        })
        let ih_ty = DVPi(dom, a => {
          let idx = schema_eval_index_terms(
            params,
            schema_concat_values(prior, [a]),
            arg_spec.index,
          )
          motive(idx, dapp_typed(arg, a, dom))
        })
        cur = dapp_typed(cur, ih, ih_ty)
      }
    }
    prior.push(arg)
  }
  schema_apply_constraint_proofs(cur, constraints, params, args)
}

///|
fn hit_family_parts(
  ty : DValue,
  params : Array[DValue],
  indices : Array[DValue],
) -> (Array[DValue], Array[DValue]) {
  match force_value(ty) {
    DVHitType(_, p, i) => (p, i)
    _ => (params, indices)
  }
}

///|
/// Generated dependent elimination for a HIT schema.  A k-dimensional
/// cell case is a nested PathP value; elimination applies it to the
/// cell dimensions after supplying constructor arguments and IHs.
pub fn eval_hit_elim(
  spec : DHitSpec,
  motive : (Array[DValue], DValue) -> DValue,
  cases : Array[DValue],
  params : Array[DValue],
  indices : Array[DValue],
  scrut0 : DValue,
  dlevel : Int32,
) -> DValue {
  let scrut = match force_value(scrut0) {
    DVHitCell(s, cell, p, args, dims) => hit_cell_value(s, cell, p, args, dims)
    other => other
  }
  match scrut {
    DVHitCell(spec2, cell_index, params2, args, dims) =>
      if spec2 != spec ||
        cell_index < 0 ||
        cell_index >= spec.cells.length() ||
        cell_index >= cases.length() {
        DVUnit
      } else {
        let cell = spec.cells[cell_index]
        let mut cur = schema_apply_case(
          cell.args,
          cell.constraints,
          cases[cell_index],
          params2,
          args,
          motive,
          idx => DVHitType(spec, params2, idx),
          (idx, x) => {
            eval_hit_elim(spec, motive, cases, params2, idx, x, dlevel)
          },
          (_, _) => DVUnitTy,
        )
        for i in 0..<dims.length() {
          cur = dapp_dim(cur, dims[i])
        }
        cur
      }
    DVNeutral(DNComp(line, branches, base)) => {
      let scrut_fill = fill_value(line, branches, base, dlevel)
      let mapped = dsystem_map(branches, p => {
        (d : Dim) => {
          let (p_d, i_d) = hit_family_parts(line(d), params, indices)
          eval_hit_elim(spec, motive, cases, p_d, i_d, p(d), dlevel)
        }
      })
      let (p0, i0) = hit_family_parts(line(DZero), params, indices)
      comp_value(
        d => {
          let (_, i_d) = hit_family_parts(line(d), params, indices)
          motive(i_d, scrut_fill(d))
        },
        mapped,
        eval_hit_elim(spec, motive, cases, p0, i0, base, dlevel),
        dlevel,
      )
    }
    DVNeutral(DNHComp(ty, branches, base)) => {
      let (p_ty, i_ty) = hit_family_parts(ty, params, indices)
      let mapped = dsystem_map(branches, p => {
        (d : Dim) => {
          eval_hit_elim(spec, motive, cases, p_ty, i_ty, p(d), dlevel)
        }
      })
      hcomp_value(
        motive(i_ty, scrut),
        mapped,
        eval_hit_elim(spec, motive, cases, p_ty, i_ty, base, dlevel),
        dlevel,
      )
    }
    DVNeutral(n) =>
      DVNeutral(DNHitElim(spec, motive, cases, params, indices, n))
    _ => DVUnit
  }
}

///|
fn schema_concat_opt_ih(ihs : Array[DValue?], v : DValue?) -> Array[DValue?] {
  let out : Array[DValue?] = []
  for i in 0..<ihs.length() {
    out.push(ihs[i])
  }
  out.push(v)
  out
}

///|
fn hit_endpoint_value(
  spec : DHitSpec,
  motive : (Array[DValue], DValue) -> DValue,
  cases : Array[DValue],
  params : Array[DValue],
  cell_index : Int32,
  args : Array[DValue],
  prior_ihs : Array[DValue?],
  face_dim : Int32,
  face_end : Int32,
  fixed_dims : Array[Dim],
  dlevel : Int32,
) -> DValue {
  let cell = spec.cells[cell_index]
  if fixed_dims.length() < cell.dim_count {
    DVPathLam(d => {
      hit_endpoint_value(
        spec,
        motive,
        cases,
        params,
        cell_index,
        args,
        prior_ihs,
        face_dim,
        face_end,
        schema_concat_dims(fixed_dims, d),
        dlevel,
      )
    })
  } else {
    let face_index = 2 * face_dim + face_end
    if face_index >= 0 && face_index < cell.faces.length() {
      let face = cell.faces[face_index]
      let total = params.length() + args.length()
      if face.cell < 0 && face.args.length() == 1 {
        match face.args[0] {
          DTVar(v_idx) => {
            let arg_pos = total - 1 - v_idx - params.length()
            if arg_pos >= 0 &&
              arg_pos < prior_ihs.length() &&
              arg_pos < cell.args.length() {
              match (cell.args[arg_pos].kind, prior_ihs[arg_pos]) {
                (DArgRecursive, Some(ih_x)) => return ih_x
                _ => ()
              }
            }
          }
          DApp(DTVar(f_idx), arg_term) => {
            let f_pos = total - 1 - f_idx - params.length()
            if f_pos >= 0 &&
              f_pos < prior_ihs.length() &&
              f_pos < cell.args.length() {
              match (cell.args[f_pos].kind, prior_ihs[f_pos]) {
                (DArgFunction, Some(ih_f)) => {
                  let values = schema_concat_values(params, args)
                  let a_val = deval_dim(
                    arg_term,
                    schema_env(values),
                    schema_dim_env(fixed_dims),
                  )
                  let dom = schema_eval_under(
                    cell.args[f_pos].ty,
                    schema_concat_values(
                      params,
                      schema_value_prefix(args, f_pos),
                    ),
                    [],
                  )
                  return dapp_typed(ih_f, a_val, dom)
                }
                _ => ()
              }
            }
          }
          _ => ()
        }
      } else if face.cell >= 0 &&
        face.cell < spec.cells.length() &&
        face.cell < cases.length() &&
        face.args.length() == 1 {
        let target_cell = spec.cells[face.cell]
        if target_cell.dim_count == 0 &&
          target_cell.args.length() == 1 &&
          target_cell.constraints.length() == 0 {
          match face.args[0] {
            DTVar(f_idx) => {
              let f_pos = total - 1 - f_idx - params.length()
              if f_pos >= 0 && f_pos < prior_ihs.length() {
                match (target_cell.args[0].kind, prior_ihs[f_pos]) {
                  (DArgFunction, Some(ih_f)) => {
                    let fn_arg_ty = hit_arg_type(
                      spec,
                      target_cell.args[0],
                      params,
                      [],
                    )
                    let dom = schema_eval_under(
                      target_cell.args[0].ty,
                      params,
                      [],
                    )
                    let ih_ty = DVPi(dom, a => {
                      let idx = schema_eval_index_terms(
                        params,
                        [a],
                        target_cell.args[0].index,
                      )
                      motive(idx, dapp_typed(args[f_pos], a, dom))
                    })
                    return dapp_typed(
                      dapp_typed(cases[face.cell], args[f_pos], fn_arg_ty),
                      ih_f,
                      ih_ty,
                    )
                  }
                  _ => ()
                }
              }
            }
            _ => ()
          }
        }
      }
    }
    let scrut = if face_index >= 0 && face_index < cell.faces.length() {
      hit_face_instantiate(
        spec,
        params,
        args,
        fixed_dims,
        cell.faces[face_index],
      )
    } else {
      DVUnit
    }
    let fallback = hit_cell_result_indices(spec, cell_index, params, args)
    let idx = hit_scrut_result_indices(spec, fallback, scrut)
    eval_hit_elim(spec, motive, cases, params, idx, scrut, dlevel)
  }
}

///|
fn schema_concat_dims(dims : Array[Dim], d : Dim) -> Array[Dim] {
  let out : Array[Dim] = []
  for i in 0..<dims.length() {
    out.push(dims[i])
  }
  out.push(d)
  out
}

///|
fn hit_path_type_loop(
  spec : DHitSpec,
  motive : (Array[DValue], DValue) -> DValue,
  cases : Array[DValue],
  params : Array[DValue],
  cell_index : Int32,
  args : Array[DValue],
  prior_ihs : Array[DValue?],
  fixed_dims : Array[Dim],
  dlevel : Int32,
) -> DValue {
  let cell = spec.cells[cell_index]
  if fixed_dims.length() >= cell.dim_count {
    motive(
      hit_cell_result_indices(spec, cell_index, params, args),
      hit_cell_value(spec, cell_index, params, args, fixed_dims),
    )
  } else {
    let dim_index = fixed_dims.length()
    DVPathTy(
      d => {
        hit_path_type_loop(
          spec,
          motive,
          cases,
          params,
          cell_index,
          args,
          prior_ihs,
          schema_concat_dims(fixed_dims, d),
          dlevel,
        )
      },
      hit_endpoint_value(
        spec,
        motive,
        cases,
        params,
        cell_index,
        args,
        prior_ihs,
        dim_index,
        0,
        schema_concat_dims(fixed_dims, DZero),
        dlevel,
      ),
      hit_endpoint_value(
        spec,
        motive,
        cases,
        params,
        cell_index,
        args,
        prior_ihs,
        dim_index,
        1,
        schema_concat_dims(fixed_dims, DOne),
        dlevel,
      ),
    )
  }
}

///|
fn hit_case_type_loop(
  spec : DHitSpec,
  motive : (Array[DValue], DValue) -> DValue,
  cases : Array[DValue],
  params : Array[DValue],
  cell_index : Int32,
  cell : DHitCellSpec,
  pos : Int32,
  prior : Array[DValue],
  prior_ihs : Array[DValue?],
  dlevel : Int32,
) -> DValue {
  if pos >= cell.args.length() {
    schema_constraints_pi(
      cell.constraints,
      params,
      prior,
      hit_path_type_loop(
        spec,
        motive,
        cases,
        params,
        cell_index,
        prior,
        prior_ihs,
        [],
        dlevel,
      ),
    )
  } else {
    let arg = cell.args[pos]
    let arg_ty = hit_arg_type(spec, arg, params, prior)
    DVPi(arg_ty, x => {
      let next = schema_concat_values(prior, [x])
      match arg.kind {
        DArgExternal =>
          hit_case_type_loop(
            spec,
            motive,
            cases,
            params,
            cell_index,
            cell,
            pos + 1,
            next,
            schema_concat_opt_ih(prior_ihs, None),
            dlevel,
          )
        DArgRecursive => {
          let idx = schema_eval_index_terms(params, prior, arg.index)
          DVPi(motive(idx, x), ih_x => {
            hit_case_type_loop(
              spec,
              motive,
              cases,
              params,
              cell_index,
              cell,
              pos + 1,
              next,
              schema_concat_opt_ih(prior_ihs, Some(ih_x)),
              dlevel,
            )
          })
        }
        DArgFunction => {
          let dom = schema_eval_under(
            arg.ty,
            schema_concat_values(params, prior),
            [],
          )
          let ih_ty = DVPi(dom, a => {
            let idx = schema_eval_index_terms(
              params,
              schema_concat_values(prior, [a]),
              arg.index,
            )
            motive(idx, dapp_typed(x, a, dom))
          })
          DVPi(ih_ty, ih_f => {
            hit_case_type_loop(
              spec,
              motive,
              cases,
              params,
              cell_index,
              cell,
              pos + 1,
              next,
              schema_concat_opt_ih(prior_ihs, Some(ih_f)),
              dlevel,
            )
          })
        }
        DArgNested => {
          let ih_ty = positive_functor_ih_type(
            arg.nested,
            params,
            prior,
            idx => DVHitType(spec, params, idx),
            motive,
            x,
          )
          DVPi(ih_ty, _ => {
            hit_case_type_loop(
              spec,
              motive,
              cases,
              params,
              cell_index,
              cell,
              pos + 1,
              next,
              schema_concat_opt_ih(prior_ihs, None),
              dlevel,
            )
          })
        }
        DArgDecoded | DArgDecodedFunction =>
          // Rejected by HIT validation: HIT specs have no decode.
          hit_case_type_loop(
            spec,
            motive,
            cases,
            params,
            cell_index,
            cell,
            pos + 1,
            next,
            schema_concat_opt_ih(prior_ihs, None),
            dlevel,
          )
      }
    })
  }
}

///|
pub fn hit_case_type(
  spec : DHitSpec,
  motive : (Array[DValue], DValue) -> DValue,
  cases : Array[DValue],
  params : Array[DValue],
  cell_index : Int32,
  dlevel : Int32,
) -> DValue {
  if cell_index < 0 || cell_index >= spec.cells.length() {
    DVUnitTy
  } else {
    hit_case_type_loop(
      spec,
      motive,
      cases,
      params,
      cell_index,
      spec.cells[cell_index],
      0,
      [],
      [],
      dlevel,
    )
  }
}

///|
fn schema_dim_nvars(d : Dim) -> Int32 {
  match d {
    DVar(i) => i + 1
    DNeg(x) => schema_dim_nvars(x)
    DAnd(x, y) => {
      let a = schema_dim_nvars(x)
      let b = schema_dim_nvars(y)
      if a > b {
        a
      } else {
        b
      }
    }
    DOr(x, y) => {
      let a = schema_dim_nvars(x)
      let b = schema_dim_nvars(y)
      if a > b {
        a
      } else {
        b
      }
    }
    _ => 0
  }
}

///|
fn hit_validate_face(
  spec : DHitSpec,
  source_index : Int32,
  face : DHitFaceExpr,
) -> Bool {
  let source = spec.cells[source_index]
  if face.cell >= spec.cells.length() {
    return false
  }
  let param_values = schema_fresh_values(spec.params.length(), 8000)
  let param_types = hit_param_types(spec, param_values)
  let source_values = schema_fresh_values(source.args.length(), 8100)
  let source_types : Array[DValue] = []
  let prior_source : Array[DValue] = []
  for i in 0..<source.args.length() {
    source_types.push(
      hit_arg_type(spec, source.args[i], param_values, prior_source),
    )
    prior_source.push(source_values[i])
  }
  let local_types = schema_concat_values(param_types, source_types)
  let local_values = schema_concat_values(param_values, source_values)
  if face.cell < 0 {
    if face.args.length() != 1 || face.dims.length() != 0 {
      return false
    }
    let fresh_dims : Array[Dim] = []
    for i in 0..<source.dim_count {
      fresh_dims.push(DVar(9200 + i))
    }
    let expected = DVHitType(
      spec,
      param_values,
      hit_result_indices(source, param_values, source_values),
    )
    return match
      d_check(
        face.args[0],
        expected,
        schema_env(local_types),
        schema_env(local_values),
        schema_dim_env(fresh_dims),
      ) {
      Some(_) => true
      None => false
    }
  }
  let target = spec.cells[face.cell]
  if face.args.length() != target.args.length() ||
    face.dims.length() != target.dim_count {
    return false
  }
  for i in 0..<face.dims.length() {
    if schema_dim_nvars(face.dims[i]) > source.dim_count {
      return false
    }
  }
  let fresh_dims : Array[Dim] = []
  for i in 0..<source.dim_count {
    fresh_dims.push(DVar(9200 + i))
  }
  let target_values : Array[DValue] = []
  for i in 0..<face.args.length() {
    let expected = hit_arg_type(
      spec,
      target.args[i],
      param_values,
      target_values,
    )
    match
      d_check(
        face.args[i],
        expected,
        schema_env(local_types),
        schema_env(local_values),
        schema_dim_env(fresh_dims),
      ) {
      Some(v) => target_values.push(v)
      None => return false
    }
  }
  let source_result = hit_result_indices(source, param_values, source_values)
  let target_result = hit_result_indices(target, param_values, target_values)
  conv_telescope_values(
    10000,
    10000,
    spec.indices,
    param_types,
    param_values,
    source_result,
    target_result,
  ) &&
  schema_constraints_hold(
    10000,
    10000,
    target.constraints,
    param_values,
    target_values,
  )
}

///|
fn hit_schema_validate_uncached(spec : DHitSpec) -> Bool {
  let names : Array[String] = []
  for i in 0..<spec.cells.length() {
    names.push(spec.cells[i].name)
  }
  if spec.name.length() == 0 || !schema_names_unique(names) {
    return false
  }
  if schema_telescope_family_occurs(spec.params, spec.name) ||
    schema_telescope_family_occurs(spec.indices, spec.name) {
    return false
  }
  for i in 0..<spec.cells.length() {
    let cell = spec.cells[i]
    if cell.dim_count < 0 ||
      cell.faces.length() != 2 * cell.dim_count ||
      !schema_validate_args(
        spec.name,
        spec.params,
        spec.indices,
        cell.args,
        cell.result_index,
        cell.constraints,
        false,
        (ps, js) => DVHitType(spec, ps, js),
      ) {
      return false
    }
    for k in 0..<cell.faces.length() {
      if !hit_validate_face(spec, i, cell.faces[k]) {
        return false
      }
    }
    // Corner compatibility in every dimension: for every pair of
    // dimensions, reducing either one first gives convertible
    // results.  The remaining dimensions stay generic, so this is a
    // pairwise local-confluence check rather than an enumeration of
    // all 2^n corners.
    if cell.dim_count >= 2 {
      let param_values = schema_fresh_values(spec.params.length(), 8400)
      let arg_values = schema_fresh_values(cell.args.length(), 8500)
      let result = hit_result_indices(cell, param_values, arg_values)
      let ends = [DZero, DOne]
      for first in 0..<cell.dim_count {
        for second in (first + 1)..<cell.dim_count {
          for a in 0..<2 {
            for b in 0..<2 {
              let dims : Array[Dim] = []
              for k in 0..<cell.dim_count {
                dims.push(DVar(9300 + k))
              }
              dims[first] = ends[a]
              dims[second] = ends[b]
              let x = hit_reduce_dimension(
                spec, i, param_values, arg_values, dims, first,
              )
              let y = hit_reduce_dimension(
                spec, i, param_values, arg_values, dims, second,
              )
              if !conv_at(10000, 0, DVHitType(spec, param_values, result), x, y) {
                return false
              }
            }
          }
        }
      }
    }
  }
  true
}

///|
fn hit_normalized(v : DValue) -> DValue {
  match force_value(v) {
    DVHitCell(s, cell, p, args, dims) => hit_cell_value(s, cell, p, args, dims)
    other => other
  }
}

///|
fn hit_cell_args_of(v : DValue) -> Array[DValue] {
  match hit_normalized(v) {
    DVHitCell(_, _, _, args, _) => args
    _ => []
  }
}

///|
fn hit_dims_eq(a : Array[Dim], b : Array[Dim]) -> Bool {
  if a.length() != b.length() {
    return false
  }
  for i in 0..<a.length() {
    if !dim_eq_sem(a[i], b[i]) {
      return false
    }
  }
  true
}

// ---------------------------------------------------------------------------
// Canonical generated HIT schemas and term builders
// ---------------------------------------------------------------------------

///|
pub fn hit_type_term(spec : DHitSpec, args : Array[DTerm]) -> DTerm {
  DHitType(spec, args)
}

///|
pub fn hit_intro_term(
  spec : DHitSpec,
  cell : Int32,
  params : Array[DTerm],
  args : Array[DTerm],
  dims : Array[Dim],
) -> DTerm {
  DHitIntro(spec, cell, params, args, dims)
}

///|
pub fn hit_elim_term(
  spec : DHitSpec,
  motive : DTerm,
  cases : Array[DTerm],
  params : Array[DTerm],
  indices : Array[DTerm],
  scrut : DTerm,
) -> DTerm {
  DHitElim(spec, motive, cases, params, indices, scrut)
}

///|
pub fn circle_schema() -> DHitSpec {
  dhit_spec("CircleS", 0, [], [], [
    dhit_cell_spec("base", 0, [], []),
    dhit_cell_spec("loop", 1, [], [dhit_face(0, [], []), dhit_face(0, [], [])]),
  ])
}

///|
pub fn segment_schema() -> DHitSpec {
  dhit_spec("SegmentS", 0, [], [], [
    dhit_cell_spec("left", 0, [], []),
    dhit_cell_spec("right", 0, [], []),
    dhit_cell_spec("segment", 1, [], [
      dhit_face(0, [], []),
      dhit_face(1, [], []),
    ]),
  ])
}

///|
pub fn torus_schema() -> DHitSpec {
  dhit_spec("TorusS", 0, [], [], [
    dhit_cell_spec("base", 0, [], []),
    dhit_cell_spec("loop_a", 1, [], [dhit_face(0, [], []), dhit_face(0, [], [])]),
    dhit_cell_spec("loop_b", 1, [], [dhit_face(0, [], []), dhit_face(0, [], [])]),
    dhit_cell_spec("square", 2, [], [
      dhit_face(2, [], [DVar(0)]),
      dhit_face(2, [], [DVar(0)]),
      dhit_face(1, [], [DVar(1)]),
      dhit_face(1, [], [DVar(1)]),
    ]),
  ])
}

///|
pub fn hit_schema_examples() -> Array[DHitSpec] {
  [circle_schema(), segment_schema(), torus_schema()]
}
