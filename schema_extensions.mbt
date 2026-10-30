///|
// Higher-level schema declarations built from the core generators:
// mutual inductive families (compiled to one tagged indexed family),
// declaration-level universe schemes, quotient HITs, and canonical
// examples for nested recursion, induction-recursion, constraints,
// and cells of dimension three.

// ---------------------------------------------------------------------------
// Mutual inductive families
// ---------------------------------------------------------------------------

///|
/// A compiled mutual block.  Components must share parameter and
/// index telescopes; the compiled family has one additional Nat
/// index selecting the component.  Cross-recursive arguments in the
/// component declarations are rewritten to recursive occurrences of
/// the compiled family at the corresponding tag.
pub struct DMutualFamily {
  name : String
  components : Array[DInductiveSpec]
  combined : DInductiveSpec
  ctor_offsets : Array[Int32]
}

///|
fn mutual_nat_term_loop(n : Int32, acc : DTerm) -> DTerm {
  if n <= 0 {
    acc
  } else {
    mutual_nat_term_loop(n - 1, DSucc(acc))
  }
}

///|
pub fn mutual_nat_term(n : Int32) -> DTerm {
  mutual_nat_term_loop(n, DNatZero)
}

///|
pub fn mutual_nat_value(n : Int32) -> DValue {
  let mut out = DVZeroNat
  for _i in 0..<n {
    out = DVSucc(out)
  }
  out
}

///|
fn mutual_nat_of_value(v : DValue) -> Int32 {
  match force_value(v) {
    DVZeroNat => 0
    DVSucc(x) => 1 + mutual_nat_of_value(x)
    _ => 0
  }
}

///|
fn mutual_prepend_tag(tag : Int32, terms : Array[DTerm]) -> Array[DTerm] {
  let out = [mutual_nat_term(tag)]
  for i in 0..<terms.length() {
    out.push(terms[i])
  }
  out
}

///|
fn mutual_transform_functor(
  functor : DPositiveFunctor,
  tag : Int32,
) -> DPositiveFunctor {
  match functor {
    DFunctorIdentity(index) => DFunctorIdentity(mutual_prepend_tag(tag, index))
    DFunctorConst(ty) => DFunctorConst(ty)
    DFunctorProduct(a, b) =>
      DFunctorProduct(
        mutual_transform_functor(a, tag),
        mutual_transform_functor(b, tag),
      )
    DFunctorSum(a, b) =>
      DFunctorSum(
        mutual_transform_functor(a, tag),
        mutual_transform_functor(b, tag),
      )
    DFunctorList(inner) => DFunctorList(mutual_transform_functor(inner, tag))
    DFunctorPi(dom, inner) =>
      DFunctorPi(dom, mutual_transform_functor(inner, tag))
    DFunctorContainer(shape, positions, index) =>
      DFunctorContainer(shape, positions, mutual_prepend_tag(tag, index))
    DFunctorSigma(a, b) =>
      DFunctorSigma(
        mutual_transform_functor(a, tag),
        mutual_transform_functor(b, tag),
      )
    DFunctorFamily(spec, pargs, index) => {
      // The inner family's own indices are untouched; `Self`
      // arguments denote the joint family, so they take the tag.
      let out : Array[DFunctorParamArg] = []
      for i in 0..<pargs.length() {
        out.push(
          match pargs[i] {
            DFunctorParamTerm(t) => DFunctorParamTerm(t)
            DFunctorParamSelf(js) =>
              DFunctorParamSelf(mutual_prepend_tag(tag, js))
          },
        )
      }
      DFunctorFamily(spec, out, index)
    }
    DFunctorSelfFamily(pargs, index) => {
      // Components using self-family recursion are rejected by
      // the mutual positivity check before compilation; the
      // transform is still defined structurally (the node and
      // its `Self` arguments take the joint tag) so this
      // function stays total.
      let out : Array[DFunctorParamArg] = []
      for i in 0..<pargs.length() {
        out.push(
          match pargs[i] {
            DFunctorParamTerm(t) => DFunctorParamTerm(t)
            DFunctorParamSelf(js) =>
              DFunctorParamSelf(mutual_prepend_tag(tag, js))
          },
        )
      }
      DFunctorSelfFamily(out, mutual_prepend_tag(tag, index))
    }
  }
}

///|
fn mutual_transform_arg(
  arg : DConstructorArg,
  own : Int32,
  component_count : Int32,
) -> DConstructorArg? {
  let target = if arg.target == -1 { own } else { arg.target }
  if target < 0 || target >= component_count {
    return None
  }
  match arg.kind {
    DArgExternal => if arg.target == -1 { Some(arg) } else { None }
    DArgRecursive | DArgFunction =>
      Some(DConstructorArg::{
        name: arg.name,
        kind: arg.kind,
        ty: arg.ty,
        index: mutual_prepend_tag(target, arg.index),
        nested: arg.nested,
        target: -1,
      })
    DArgNested =>
      Some(DConstructorArg::{
        name: arg.name,
        kind: arg.kind,
        ty: arg.ty,
        index: [],
        nested: mutual_transform_functor(arg.nested, target),
        target: -1,
      })
    DArgDecoded | DArgDecodedFunction => None
  }
}

///|
/// Compile a mutual block to a single tagged inductive family.
/// Returns None for mismatched telescopes, invalid cross-references,
/// induction-recursive components, or if the compiled family fails
/// ordinary schema validation.
pub fn compile_mutual_inductive(
  name : String,
  components : Array[DInductiveSpec],
) -> DMutualFamily? {
  if name.length() == 0 || components.length() == 0 {
    return None
  }
  let first = components[0]
  let mut level = first.level
  for i in 0..<components.length() {
    let c = components[i]
    if c.name.length() == 0 ||
      c.decode_cases.length() != 0 ||
      c.params != first.params ||
      c.indices != first.indices {
      return None
    }
    if c.level > level {
      level = c.level
    }
    for j in (i + 1)..<components.length() {
      if c.name == components[j].name {
        return None
      }
    }
  }
  let indices = [dtelescope_entry("component", DNatTy)]
  for i in 0..<first.indices.length() {
    indices.push(
      dtelescope_entry(
        first.indices[i].name,
        dterm_shift(first.indices[i].ty, 0, 1),
      ),
    )
  }
  let ctors : Array[DConstructorSpec] = []
  let offsets : Array[Int32] = []
  for comp in 0..<components.length() {
    offsets.push(ctors.length())
    let component = components[comp]
    for k in 0..<component.constructors.length() {
      let ctor = component.constructors[k]
      let args : Array[DConstructorArg] = []
      for a in 0..<ctor.args.length() {
        match mutual_transform_arg(ctor.args[a], comp, components.length()) {
          Some(x) => args.push(x)
          None => return None
        }
      }
      ctors.push(DConstructorSpec::{
        name: component.name + "." + ctor.name,
        args,
        result_index: mutual_prepend_tag(comp, ctor.result_index),
        constraints: ctor.constraints,
      })
    }
  }
  let combined = dinductive_spec(name, level, first.params, indices, ctors)
  if inductive_schema_validate(combined) {
    Some(DMutualFamily::{ name, components, combined, ctor_offsets: offsets, })
  } else {
    None
  }
}

///|
pub fn mutual_ctor_index(
  family : DMutualFamily,
  component : Int32,
  ctor : Int32,
) -> Int32 {
  if component < 0 || component >= family.ctor_offsets.length() {
    -1
  } else {
    family.ctor_offsets[component] + ctor
  }
}

///|
/// The type of one component, as a tagged application of the
/// compiled family.  `args` are parameters followed by indices.
pub fn mutual_type_term(
  family : DMutualFamily,
  component : Int32,
  args : Array[DTerm],
) -> DTerm {
  let (params, indices) = schema_split_terms(
    args,
    family.combined.params.length(),
  )
  let all : Array[DTerm] = []
  for i in 0..<params.length() {
    all.push(params[i])
  }
  let tagged = mutual_prepend_tag(component, indices)
  for i in 0..<tagged.length() {
    all.push(tagged[i])
  }
  DInductive(family.combined, all)
}

///|
pub fn mutual_intro_term(
  family : DMutualFamily,
  component : Int32,
  ctor : Int32,
  params : Array[DTerm],
  args : Array[DTerm],
) -> DTerm {
  DIntro(
    family.combined,
    mutual_ctor_index(family, component, ctor),
    params,
    args,
  )
}

///|
/// Mutual elimination as a term, given a motive and cases for the
/// compiled family in flattened constructor order.
pub fn mutual_elim_term(
  family : DMutualFamily,
  motive : DTerm,
  cases : Array[DTerm],
  params : Array[DTerm],
  component : Int32,
  indices : Array[DTerm],
  scrut : DTerm,
) -> DTerm {
  DInductiveElim(
    family.combined,
    motive,
    cases,
    params,
    mutual_prepend_tag(component, indices),
    scrut,
  )
}

///|
pub fn mutual_type_value(
  family : DMutualFamily,
  component : Int32,
  params : Array[DValue],
  indices : Array[DValue],
) -> DValue {
  let all = [mutual_nat_value(component)]
  for i in 0..<indices.length() {
    all.push(indices[i])
  }
  DVInductive(family.combined, params, all)
}

///|
pub fn mutual_intro_value(
  family : DMutualFamily,
  component : Int32,
  ctor : Int32,
  params : Array[DValue],
  args : Array[DValue],
) -> DValue {
  DVIntro(
    family.combined,
    mutual_ctor_index(family, component, ctor),
    params,
    args,
  )
}

///|
fn mutual_tail_values(values : Array[DValue]) -> Array[DValue] {
  let out : Array[DValue] = []
  for i in 1..<values.length() {
    out.push(values[i])
  }
  out
}

///|
/// The motive of the compiled family obtained by dispatching on the
/// component tag.
pub fn mutual_motive_function(
  motives : Array[(Array[DValue], DValue) -> DValue],
) -> (Array[DValue], DValue) -> DValue {
  (indices, scrut) => {
    if indices.length() == 0 || motives.length() == 0 {
      DVUnitTy
    } else {
      let component = mutual_nat_of_value(indices[0])
      if component < 0 || component >= motives.length() {
        DVUnitTy
      } else {
        motives[component](mutual_tail_values(indices), scrut)
      }
    }
  }
}

///|
/// Semantic mutual dependent elimination.  `cases` are grouped by
/// component; induction hypotheses for cross-recursive arguments are
/// supplied at the corresponding component motive.
pub fn eval_mutual_elim(
  family : DMutualFamily,
  motives : Array[(Array[DValue], DValue) -> DValue],
  cases : Array[Array[DValue]],
  params : Array[DValue],
  component : Int32,
  indices : Array[DValue],
  scrut : DValue,
  dlevel : Int32,
) -> DValue {
  if motives.length() != family.components.length() ||
    cases.length() != family.components.length() {
    return DVUnit
  }
  let flat : Array[DValue] = []
  for i in 0..<cases.length() {
    if cases[i].length() != family.components[i].constructors.length() {
      return DVUnit
    }
    for j in 0..<cases[i].length() {
      flat.push(cases[i][j])
    }
  }
  let all_indices = [mutual_nat_value(component)]
  for i in 0..<indices.length() {
    all_indices.push(indices[i])
  }
  eval_inductive_elim(
    family.combined,
    mutual_motive_function(motives),
    flat,
    params,
    all_indices,
    scrut,
    dlevel,
  )
}

///|
pub fn even_odd_components() -> Array[DInductiveSpec] {
  let indices = [dtelescope_entry("n", DNatTy)]
  [
    dinductive_spec("EvenS", 0, [], indices, [
      dconstructor_spec("zero", [], result_index=[DNatZero]),
      dconstructor_spec(
        "succ_odd",
        [darg_external("pred", DNatTy), darg_mutual("odd", 1, [DTVar(0)])],
        result_index=[DSucc(DTVar(1))],
      ),
    ]),
    dinductive_spec("OddS", 0, [], indices, [
      dconstructor_spec(
        "succ_even",
        [darg_external("pred", DNatTy), darg_mutual("even", 0, [DTVar(0)])],
        result_index=[DSucc(DTVar(1))],
      ),
    ]),
  ]
}

///|
pub fn even_odd_family() -> DMutualFamily? {
  compile_mutual_inductive("EvenOddS", even_odd_components())
}

///|
pub fn tree_forest_components() -> Array[DInductiveSpec] {
  let params = [dtelescope_entry("A", DUniv(0))]
  [
    dinductive_spec("MutTreeS", 0, params, [], [
      dconstructor_spec("node", [
        darg_external("label", DTVar(0)),
        darg_mutual("children", 1, []),
      ]),
    ]),
    dinductive_spec("MutForestS", 0, params, [], [
      dconstructor_spec("nil", []),
      dconstructor_spec("cons", [
        darg_mutual("head", 0, []),
        darg_recursive("tail"),
      ]),
    ]),
  ]
}

///|
pub fn tree_forest_family() -> DMutualFamily? {
  compile_mutual_inductive("TreeForestS", tree_forest_components())
}

// ---------------------------------------------------------------------------
// Universe schemes
// ---------------------------------------------------------------------------

///|
/// Universe-level expressions for declaration-level schemes.
pub enum DLevelExpr {
  DLevelConst(Int32)
  DLevelVar(Int32)
  DLevelSucc(DLevelExpr)
  DLevelMax(DLevelExpr, DLevelExpr)
} derive(Debug, Eq)

///|
pub extend DLevelExpr with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend DLevelExpr with Eq::{not_equal, equal}

///|
pub fn dlevel_const(n : Int32) -> DLevelExpr {
  DLevelConst(n)
}

///|
pub fn dlevel_var(n : Int32) -> DLevelExpr {
  DLevelVar(n)
}

///|
pub fn dlevel_succ(e : DLevelExpr) -> DLevelExpr {
  DLevelSucc(e)
}

///|
pub fn dlevel_max(a : DLevelExpr, b : DLevelExpr) -> DLevelExpr {
  DLevelMax(a, b)
}

///|
pub fn dlevel_eval(expr : DLevelExpr, levels : Array[Int32]) -> Int32? {
  match expr {
    DLevelConst(n) => if n >= 0 { Some(n) } else { None }
    DLevelVar(i) =>
      if i >= 0 && i < levels.length() && levels[i] >= 0 {
        Some(levels[i])
      } else {
        None
      }
    DLevelSucc(e) =>
      match dlevel_eval(e, levels) {
        Some(n) => Some(n + 1)
        None => None
      }
    DLevelMax(a, b) =>
      match (dlevel_eval(a, levels), dlevel_eval(b, levels)) {
        (Some(x), Some(y)) => Some(if x > y { x } else { y })
        _ => None
      }
  }
}

///|
/// A universe-polymorphic inductive declaration scheme.  Each
/// instantiation is an ordinary monomorphic schema and is fully
/// revalidated; its displayed universe must equal `result_level`.
pub struct DInductiveLevelScheme {
  name : String
  level_arity : Int32
  result_level : DLevelExpr
  build : (Array[Int32]) -> DInductiveSpec
}

///|
pub fn dinductive_level_scheme(
  name : String,
  level_arity : Int32,
  result_level : DLevelExpr,
  build : (Array[Int32]) -> DInductiveSpec,
) -> DInductiveLevelScheme {
  DInductiveLevelScheme::{ name, level_arity, result_level, build, }
}

///|
pub fn instantiate_inductive_level_scheme(
  scheme : DInductiveLevelScheme,
  levels : Array[Int32],
) -> DInductiveSpec? {
  if levels.length() != scheme.level_arity {
    return None
  }
  match dlevel_eval(scheme.result_level, levels) {
    Some(expected) => {
      let spec = (scheme.build)(levels)
      if spec.name == scheme.name &&
        spec.level == expected &&
        inductive_schema_validate(spec) {
        Some(spec)
      } else {
        None
      }
    }
    None => None
  }
}

///|
/// A universe-polymorphic HIT declaration scheme.
pub struct DHitLevelScheme {
  name : String
  level_arity : Int32
  result_level : DLevelExpr
  build : (Array[Int32]) -> DHitSpec
}

///|
pub fn dhit_level_scheme(
  name : String,
  level_arity : Int32,
  result_level : DLevelExpr,
  build : (Array[Int32]) -> DHitSpec,
) -> DHitLevelScheme {
  DHitLevelScheme::{ name, level_arity, result_level, build, }
}

///|
pub fn instantiate_hit_level_scheme(
  scheme : DHitLevelScheme,
  levels : Array[Int32],
) -> DHitSpec? {
  if levels.length() != scheme.level_arity {
    return None
  }
  match dlevel_eval(scheme.result_level, levels) {
    Some(expected) => {
      let spec = (scheme.build)(levels)
      if spec.name == scheme.name &&
        spec.level == expected &&
        hit_schema_validate(spec) {
        Some(spec)
      } else {
        None
      }
    }
    None => None
  }
}

///|
pub fn list_level_scheme() -> DInductiveLevelScheme {
  dinductive_level_scheme("ListU", 1, DLevelVar(0), levels => {
    let l = levels[0]
    dinductive_spec("ListU", l, [dtelescope_entry("A", DUniv(l))], [], [
      dconstructor_spec("nil", []),
      dconstructor_spec("cons", [
        darg_external("head", DTVar(0)),
        darg_recursive("tail"),
      ]),
    ])
  })
}

///|
pub fn circle_level_scheme() -> DHitLevelScheme {
  dhit_level_scheme("CircleU", 1, DLevelVar(0), levels => {
    dhit_spec("CircleU", levels[0], [], [], [
      dhit_cell_spec("base", 0, [], []),
      dhit_cell_spec("loop", 1, [], [dhit_face(0, [], []), dhit_face(0, [], [])]),
    ])
  })
}

// ---------------------------------------------------------------------------
// Quotient HITs and canonical extended schemas
// ---------------------------------------------------------------------------

///|
/// The homotopy quotient of `A` by a relation family `R`: a point
/// constructor and a path constructor for every related pair.
pub fn quotient_schema() -> DHitSpec {
  dhit_spec(
    "QuotientS",
    0,
    [
      dtelescope_entry("A", DUniv(0)),
      dtelescope_entry("R", DPi(DTVar(0), DPi(DTVar(1), DUniv(0)))),
    ],
    [],
    [
      dhit_cell_spec("point", 0, [darg_external("value", DTVar(1))], []),
      dhit_cell_spec(
        "eq",
        1,
        [
          darg_external("x", DTVar(1)),
          darg_external("y", DTVar(2)),
          darg_external("related", DApp(DApp(DTVar(2), DTVar(1)), DTVar(0))),
        ],
        [dhit_face(0, [DTVar(2)], []), dhit_face(0, [DTVar(1)], [])],
      ),
    ],
  )
}

///|
pub fn quotient_point_term(params : Array[DTerm], value : DTerm) -> DTerm {
  hit_intro_term(quotient_schema(), 0, params, [value], [])
}

///|
pub fn quotient_eq_term(
  params : Array[DTerm],
  x : DTerm,
  y : DTerm,
  related : DTerm,
  dim : Dim,
) -> DTerm {
  hit_intro_term(quotient_schema(), 1, params, [x, y, related], [dim])
}

///|
/// Rose trees: recursion nested through the List functor.
pub fn rose_tree_schema() -> DInductiveSpec {
  dinductive_spec("RoseTreeS", 0, [dtelescope_entry("A", DUniv(0))], [], [
    dconstructor_spec("leaf", [darg_external("label", DTVar(0))]),
    dconstructor_spec("node", [
      darg_nested("children", dfunctor_list(dfunctor_identity([]))),
    ]),
  ])
}

///|
/// Trees whose recursive positions are an arbitrary dependent
/// polynomial/container supplied by two parameters: a shape type and
/// a position family over it.  A node stores
/// `Sigma (s : Shape), Positions s -> ContainerTree ...`.
pub fn container_tree_schema() -> DInductiveSpec {
  dinductive_spec(
    "ContainerTreeS",
    0,
    [
      dtelescope_entry("Shape", DUniv(0)),
      dtelescope_entry("Positions", DPi(DTVar(0), DUniv(0))),
    ],
    [],
    [
      dconstructor_spec("leaf", []),
      dconstructor_spec("node", [
        darg_nested(
          "children",
          dfunctor_container(DTVar(1), DApp(DTVar(1), DTVar(0))),
        ),
      ]),
    ],
  )
}

///|
/// A small Tarski universe declared by induction-recursion.  Its Π
/// code has type `(a : U) -> (decode a -> U) -> U`.
pub fn tarski_universe_schema() -> DInductiveSpec {
  dinductive_recursive_spec(
    "TarskiU",
    0,
    [],
    [],
    [
      dconstructor_spec("nat_code", []),
      dconstructor_spec("bool_code", []),
      dconstructor_spec("pi_code", [
        darg_recursive("domain_code"),
        darg_decoded_function("codomain_code", 0),
      ]),
    ],
    [
      DNatTy,
      DBoolTy,
      // Decode context, innermost first: B, b, A, a.  Under the Pi
      // binder x, B is DTVar(1).
      DPi(DTVar(2), DApp(DTVar(1), DTVar(0))),
    ],
  )
}

///|
/// Pairs of natural numbers constrained propositionally to be equal.
pub fn equal_nat_pair_schema() -> DInductiveSpec {
  dinductive_spec("EqualNatPairS", 0, [], [], [
    dconstructor_spec_constrained(
      "pair",
      [darg_external("x", DNatTy), darg_external("y", DNatTy)],
      [dconstructor_constraint(DNatTy, DTVar(1), DTVar(0))],
    ),
  ])
}

///|
/// A 3-dimensional cell: a cube whose six faces are squares, whose
/// twelve edges are loops, and whose corners are the base point.
pub fn cube3_schema() -> DHitSpec {
  dhit_spec("Cube3S", 0, [], [], [
    dhit_cell_spec("base", 0, [], []),
    dhit_cell_spec("loop", 1, [], [dhit_face(0, [], []), dhit_face(0, [], [])]),
    dhit_cell_spec("square", 2, [], [
      dhit_face(1, [], [DVar(0)]),
      dhit_face(1, [], [DVar(0)]),
      dhit_face(1, [], [DVar(1)]),
      dhit_face(1, [], [DVar(1)]),
    ]),
    dhit_cell_spec("cube", 3, [], [
      dhit_face(2, [], [DVar(1), DVar(0)]),
      dhit_face(2, [], [DVar(1), DVar(0)]),
      dhit_face(2, [], [DVar(2), DVar(0)]),
      dhit_face(2, [], [DVar(2), DVar(0)]),
      dhit_face(2, [], [DVar(2), DVar(1)]),
      dhit_face(2, [], [DVar(2), DVar(1)]),
    ]),
  ])
}
