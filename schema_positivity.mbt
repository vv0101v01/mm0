///|
// Structural strict-positivity analysis for generated families.
//
// This replaces the original Debug-string name scan.  The analysis
// walks type syntax with polarity and a strictness context,
// beta-reduces aliases (with fuel, so ill-typed self-applications
// cannot make validation loop), and understands indirect occurrences
// through previously generated families whose parameters have been
// certified positive by analysing their own constructor telescopes.
//
// A report distinguishes:
//   * no occurrence;
//   * a strictly positive occurrence;
//   * a merely positive-polarity but non-strict occurrence (for
//     example under a double negation); and
//   * negative or unknown occurrences.
//
// The schema validator remains sound in a deliberately simple way:
// external arguments and function domains must have *no* occurrence,
// while genuinely recursive occurrences are admitted only through
// the recursive/function/nested/decoded descriptors for which the
// generator knows how to synthesize induction hypotheses.

///|
pub struct DPositivityReport {
  occurs : Bool
  strictly_positive : Bool
  positive_polarity : Bool
  negative_polarity : Bool
  unknown : Bool
} derive(Debug, Eq)

///|
pub extend DPositivityReport with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend DPositivityReport with Eq::{not_equal, equal}

///|
pub fn dpositivity_report(
  occurs : Bool,
  strictly_positive : Bool,
  positive_polarity : Bool,
  negative_polarity : Bool,
  unknown : Bool,
) -> DPositivityReport {
  DPositivityReport::{
    occurs,
    strictly_positive,
    positive_polarity,
    negative_polarity,
    unknown,
  }
}

///|
fn positivity_absent() -> DPositivityReport {
  DPositivityReport::{
    occurs: false,
    strictly_positive: true,
    positive_polarity: false,
    negative_polarity: false,
    unknown: false,
  }
}

///|
fn positivity_occurrence(
  positive : Bool,
  strict_allowed : Bool,
) -> DPositivityReport {
  DPositivityReport::{
    occurs: true,
    strictly_positive: strict_allowed && positive,
    positive_polarity: positive,
    negative_polarity: !positive,
    unknown: false,
  }
}

///|
fn positivity_unknown() -> DPositivityReport {
  DPositivityReport::{
    occurs: true,
    strictly_positive: false,
    positive_polarity: false,
    negative_polarity: false,
    unknown: true,
  }
}

///|
fn positivity_combine(
  a : DPositivityReport,
  b : DPositivityReport,
) -> DPositivityReport {
  DPositivityReport::{
    occurs: a.occurs || b.occurs,
    strictly_positive: a.strictly_positive && b.strictly_positive,
    positive_polarity: a.positive_polarity || b.positive_polarity,
    negative_polarity: a.negative_polarity || b.negative_polarity,
    unknown: a.unknown || b.unknown,
  }
}

///|
fn positivity_flip(r : DPositivityReport) -> DPositivityReport {
  if r.occurs {
    DPositivityReport::{
      occurs: true,
      strictly_positive: false,
      positive_polarity: r.negative_polarity,
      negative_polarity: r.positive_polarity,
      unknown: r.unknown,
    }
  } else {
    r
  }
}

///|
fn positivity_mark_unknown(r : DPositivityReport) -> DPositivityReport {
  if r.occurs {
    DPositivityReport::{
      occurs: true,
      strictly_positive: false,
      positive_polarity: r.positive_polarity,
      negative_polarity: r.negative_polarity,
      unknown: true,
    }
  } else {
    r
  }
}

///|
fn positivity_non_strict(r : DPositivityReport) -> DPositivityReport {
  DPositivityReport::{
    occurs: r.occurs,
    strictly_positive: r.strictly_positive && !r.occurs,
    positive_polarity: r.positive_polarity,
    negative_polarity: r.negative_polarity,
    unknown: r.unknown,
  }
}

///|
fn positivity_of_children_term(
  t : DTerm,
  name : String,
  fuel : Int32,
) -> DPositivityReport {
  let children = dterm_children(t)
  let mut out = positivity_absent()
  for i in 0..<children.length() {
    out = positivity_combine(
      out,
      dterm_family_positivity_term(children[i], name, fuel),
    )
  }
  out
}

///|
fn dterm_family_positivity_term(
  t : DTerm,
  name : String,
  fuel : Int32,
) -> DPositivityReport {
  let self_report = match t {
    DInductive(spec, _) =>
      if spec.name == name {
        positivity_unknown()
      } else {
        positivity_absent()
      }
    DHitType(spec, _) =>
      if spec.name == name {
        positivity_unknown()
      } else {
        positivity_absent()
      }
    DDecode(spec, _, _, _) =>
      if spec.name == name {
        positivity_unknown()
      } else {
        positivity_absent()
      }
    _ => positivity_absent()
  }
  positivity_mark_unknown(
    positivity_combine(self_report, positivity_of_children_term(t, name, fuel)),
  )
}

///|
fn positivity_through_parameter(
  report : DPositivityReport,
  arg : DTerm,
  name : String,
  positive : Bool,
  strict_allowed : Bool,
  fuel : Int32,
) -> DPositivityReport {
  if report.strictly_positive &&
    report.occurs &&
    !report.unknown &&
    !report.negative_polarity {
    dterm_family_positivity_type(arg, name, positive, strict_allowed, fuel)
  } else if report.occurs &&
    report.positive_polarity &&
    !report.negative_polarity &&
    !report.unknown {
    positivity_non_strict(
      dterm_family_positivity_type(arg, name, positive, false, fuel),
    )
  } else if report.occurs &&
    report.negative_polarity &&
    !report.positive_polarity &&
    !report.unknown {
    positivity_non_strict(
      dterm_family_positivity_type(arg, name, !positive, false, fuel),
    )
  } else {
    dterm_family_positivity_term(arg, name, fuel)
  }
}

///|
fn dterm_family_positivity_type(
  t : DTerm,
  name : String,
  positive : Bool,
  strict_allowed : Bool,
  fuel : Int32,
) -> DPositivityReport {
  match t {
    DPi(a, b) =>
      positivity_combine(
        positivity_flip(
          dterm_family_positivity_type(a, name, positive, false, fuel),
        ),
        dterm_family_positivity_type(b, name, positive, strict_allowed, fuel),
      )
    DSigma(a, b) =>
      positivity_combine(
        dterm_family_positivity_type(a, name, positive, strict_allowed, fuel),
        dterm_family_positivity_type(b, name, positive, strict_allowed, fuel),
      )
    DListTy(a) =>
      dterm_family_positivity_type(a, name, positive, strict_allowed, fuel)
    DPathP(line, l, r) =>
      positivity_combine(
        dterm_family_positivity_type(line, name, positive, strict_allowed, fuel),
        positivity_combine(
          dterm_family_positivity_term(l, name, fuel),
          dterm_family_positivity_term(r, name, fuel),
        ),
      )
    DPath(a, l, r) =>
      positivity_combine(
        dterm_family_positivity_type(a, name, positive, strict_allowed, fuel),
        positivity_combine(
          dterm_family_positivity_term(l, name, fuel),
          dterm_family_positivity_term(r, name, fuel),
        ),
      )
    DInductive(spec, args) =>
      if spec.name == name {
        let mut out = positivity_occurrence(positive, strict_allowed)
        for i in 0..<args.length() {
          out = positivity_combine(
            out,
            dterm_family_positivity_term(args[i], name, fuel),
          )
        }
        out
      } else {
        let (params, indices) = schema_split_terms(args, spec.params.length())
        let mut out = positivity_absent()
        for i in 0..<params.length() {
          out = positivity_combine(
            out,
            positivity_through_parameter(
              inductive_parameter_positivity(spec, i),
              params[i],
              name,
              positive,
              strict_allowed,
              fuel,
            ),
          )
        }
        for i in 0..<indices.length() {
          out = positivity_combine(
            out,
            dterm_family_positivity_term(indices[i], name, fuel),
          )
        }
        out
      }
    DHitType(spec, args) =>
      if spec.name == name {
        let mut out = positivity_occurrence(positive, strict_allowed)
        for i in 0..<args.length() {
          out = positivity_combine(
            out,
            dterm_family_positivity_term(args[i], name, fuel),
          )
        }
        out
      } else {
        let (params, indices) = schema_split_terms(args, spec.params.length())
        let mut out = positivity_absent()
        for i in 0..<params.length() {
          out = positivity_combine(
            out,
            positivity_through_parameter(
              hit_parameter_positivity(spec, i),
              params[i],
              name,
              positive,
              strict_allowed,
              fuel,
            ),
          )
        }
        for i in 0..<indices.length() {
          out = positivity_combine(
            out,
            dterm_family_positivity_term(indices[i], name, fuel),
          )
        }
        out
      }
    DApp(DLam(_, body), arg) =>
      if fuel <= 0 {
        positivity_unknown()
      } else {
        dterm_family_positivity_type(
          dterm_substitute(body, 0, arg),
          name,
          positive,
          strict_allowed,
          fuel - 1,
        )
      }
    DLam(a, b) =>
      positivity_combine(
        positivity_flip(
          dterm_family_positivity_type(a, name, positive, false, fuel),
        ),
        dterm_family_positivity_type(b, name, positive, strict_allowed, fuel),
      )
    DAnn(x, y) =>
      positivity_combine(
        dterm_family_positivity_type(x, name, positive, strict_allowed, fuel),
        dterm_family_positivity_type(y, name, positive, strict_allowed, fuel),
      )
    DLamDim(body) =>
      dterm_family_positivity_type(body, name, positive, strict_allowed, fuel)
    DAppDim(x, _) =>
      dterm_family_positivity_type(x, name, positive, strict_allowed, fuel)
    DPartial(branches) => {
      let mut out = positivity_absent()
      for i in 0..<branches.length() {
        out = positivity_combine(
          out,
          dterm_family_positivity_type(
            branches[i].body,
            name,
            positive,
            strict_allowed,
            fuel,
          ),
        )
      }
      out
    }
    DCoe(line, _, _, v) =>
      positivity_combine(
        dterm_family_positivity_type(line, name, positive, strict_allowed, fuel),
        dterm_family_positivity_type(v, name, positive, strict_allowed, fuel),
      )
    DComp(line, tubes, base) | DHComp(line, tubes, base) => {
      let mut out = positivity_combine(
        dterm_family_positivity_type(line, name, positive, strict_allowed, fuel),
        dterm_family_positivity_type(base, name, positive, strict_allowed, fuel),
      )
      for i in 0..<tubes.length() {
        out = positivity_combine(
          out,
          dterm_family_positivity_type(
            tubes[i].body,
            name,
            positive,
            strict_allowed,
            fuel,
          ),
        )
      }
      out
    }
    DHFill(a, tubes, base, _) => {
      let mut out = positivity_combine(
        dterm_family_positivity_type(a, name, positive, strict_allowed, fuel),
        dterm_family_positivity_type(base, name, positive, strict_allowed, fuel),
      )
      for i in 0..<tubes.length() {
        out = positivity_combine(
          out,
          dterm_family_positivity_type(
            tubes[i].body,
            name,
            positive,
            strict_allowed,
            fuel,
          ),
        )
      }
      out
    }
    DDecode(spec, _, _, _) =>
      if spec.name == name {
        positivity_combine(
          positivity_unknown(),
          positivity_of_children_term(t, name, fuel),
        )
      } else {
        dterm_family_positivity_term(t, name, fuel)
      }
    _ => dterm_family_positivity_term(t, name, fuel)
  }
}

///|
/// Structural positivity report for a named generated family in a
/// type term.
pub fn dterm_family_positivity(t : DTerm, name : String) -> DPositivityReport {
  dterm_family_positivity_type(t, name, true, true, 64)
}

///|
pub fn dterm_family_occurs(t : DTerm, name : String) -> Bool {
  dterm_family_positivity(t, name).occurs
}

///|
pub fn dterm_family_strictly_positive(t : DTerm, name : String) -> Bool {
  let r = dterm_family_positivity(t, name)
  !r.occurs || (r.strictly_positive && !r.unknown && !r.negative_polarity)
}

///|
fn positivity_probe_name() -> String {
  "__PositivityProbe"
}

///|
fn positivity_probe_term() -> DTerm {
  DInductive(dinductive_spec(positivity_probe_name(), 0, [], [], []), [])
}

///|
fn positivity_substitute_param(
  t : DTerm,
  scope : Int32,
  param_index : Int32,
) -> DTerm {
  let variable = scope - 1 - param_index
  if variable < 0 {
    t
  } else {
    dterm_substitute(t, variable, positivity_probe_term())
  }
}

///|
fn positivity_param_in_type(
  t : DTerm,
  scope : Int32,
  param_index : Int32,
  strict_allowed : Bool,
) -> DPositivityReport {
  dterm_family_positivity_type(
    positivity_substitute_param(t, scope, param_index),
    positivity_probe_name(),
    true,
    strict_allowed,
    64,
  )
}

///|
fn positivity_param_in_term(
  t : DTerm,
  scope : Int32,
  param_index : Int32,
) -> DPositivityReport {
  dterm_family_positivity_term(
    positivity_substitute_param(t, scope, param_index),
    positivity_probe_name(),
    64,
  )
}

///|
fn positivity_param_in_terms(
  terms : Array[DTerm],
  scope : Int32,
  param_index : Int32,
) -> DPositivityReport {
  let mut out = positivity_absent()
  for i in 0..<terms.length() {
    out = positivity_combine(
      out,
      positivity_param_in_term(terms[i], scope, param_index),
    )
  }
  out
}

///|
fn positivity_param_in_functor(
  functor : DPositiveFunctor,
  scope : Int32,
  param_index : Int32,
  self_reports : Array[DPositivityReport],
) -> DPositivityReport {
  match functor {
    DFunctorIdentity(index) =>
      positivity_param_in_terms(index, scope, param_index)
    DFunctorConst(ty) => positivity_param_in_type(ty, scope, param_index, true)
    DFunctorProduct(a, b) | DFunctorSum(a, b) =>
      positivity_combine(
        positivity_param_in_functor(a, scope, param_index, self_reports),
        positivity_param_in_functor(b, scope, param_index, self_reports),
      )
    DFunctorList(inner) =>
      positivity_param_in_functor(inner, scope, param_index, self_reports)
    DFunctorPi(dom, inner) =>
      positivity_combine(
        positivity_non_strict(
          positivity_param_in_type(dom, scope, param_index, false),
        ),
        positivity_param_in_functor(inner, scope + 1, param_index, self_reports),
      )
    DFunctorContainer(shape, positions, index) =>
      positivity_combine(
        positivity_non_strict(
          positivity_param_in_type(shape, scope, param_index, false),
        ),
        positivity_combine(
          positivity_non_strict(
            positivity_param_in_type(positions, scope + 1, param_index, false),
          ),
          positivity_param_in_terms(index, scope + 2, param_index),
        ),
      )
    DFunctorSigma(a, b) =>
      positivity_combine(
        positivity_param_in_functor(a, scope, param_index, self_reports),
        positivity_param_in_functor(b, scope + 1, param_index, self_reports),
      )
    DFunctorFamily(spec, pargs, index) => {
      let mut out = positivity_param_in_terms(index, scope, param_index)
      for k in 0..<pargs.length() {
        out = positivity_combine(
          out,
          match pargs[k] {
            DFunctorParamTerm(t) =>
              positivity_compose_param(
                positivity_param_in_type(t, scope, param_index, true),
                inductive_parameter_positivity(spec, k),
              )
            DFunctorParamSelf(js) =>
              positivity_param_in_terms(js, scope, param_index)
          },
        )
      }
      out
    }
    DFunctorSelfFamily(pargs, index) => {
      // Parameter use through a self-application is a recursive
      // equation in the host's own reports.  `self_reports` is
      // the current least-fixpoint approximation of those
      // reports (see `positivity_reports_fixpoint`): slot `k`
      // composes the argument's parameter flow with the host's
      // own slot-`k` report, exactly as a cross-family slot
      // composes with the target family's report.  A `Self`
      // argument is the host family at the ambient parameters,
      // so the tracked parameter flows into it through its own
      // host slot.  Without a fixpoint context (empty
      // `self_reports`) self slots stay unknown.
      let slot_report = (k : Int32) => {
        if k >= 0 && k < self_reports.length() {
          self_reports[k]
        } else {
          positivity_unknown()
        }
      }
      let mut out = positivity_param_in_terms(index, scope, param_index)
      for k in 0..<pargs.length() {
        out = positivity_combine(
          out,
          match pargs[k] {
            DFunctorParamTerm(t) =>
              positivity_compose_param(
                positivity_param_in_type(t, scope, param_index, true),
                slot_report(k),
              )
            DFunctorParamSelf(js) =>
              positivity_compose_param(
                positivity_combine(
                  positivity_param_in_terms(js, scope, param_index),
                  slot_report(param_index),
                ),
                slot_report(k),
              )
          },
        )
      }
      out
    }
  }
}

///|
/// Polarities compose along a parameter instantiation: the outer
/// report describes the argument term, the inner report how the
/// applied family uses its parameter.  An unused parameter makes
/// the occurrence vanish.
fn positivity_compose_param(
  outer : DPositivityReport,
  inner : DPositivityReport,
) -> DPositivityReport {
  if !outer.occurs || !inner.occurs {
    positivity_absent()
  } else {
    DPositivityReport::{
      occurs: true,
      strictly_positive: outer.strictly_positive && inner.strictly_positive,
      positive_polarity: (outer.positive_polarity && inner.positive_polarity) ||
      (outer.negative_polarity && inner.negative_polarity),
      negative_polarity: (outer.positive_polarity && inner.negative_polarity) ||
      (outer.negative_polarity && inner.positive_polarity),
      unknown: outer.unknown || inner.unknown,
    }
  }
}

///|
fn positivity_param_in_arg(
  arg : DConstructorArg,
  scope : Int32,
  param_index : Int32,
  has_decode : Bool,
  self_reports : Array[DPositivityReport],
) -> DPositivityReport {
  match arg.kind {
    DArgExternal => positivity_param_in_type(arg.ty, scope, param_index, true)
    DArgRecursive => positivity_param_in_terms(arg.index, scope, param_index)
    DArgFunction =>
      positivity_combine(
        positivity_non_strict(
          positivity_param_in_type(arg.ty, scope, param_index, false),
        ),
        positivity_param_in_terms(arg.index, scope + 1, param_index),
      )
    DArgNested =>
      positivity_param_in_functor(arg.nested, scope, param_index, self_reports)
    DArgDecoded =>
      if has_decode {
        positivity_unknown()
      } else {
        positivity_absent()
      }
    DArgDecodedFunction =>
      positivity_combine(
        if has_decode {
          positivity_unknown()
        } else {
          positivity_absent()
        },
        positivity_param_in_terms(arg.index, scope + 1, param_index),
      )
  }
}

///|
fn positivity_param_in_telescope(
  entries : Array[DTelescopeEntry],
  start_scope : Int32,
  param_index : Int32,
) -> DPositivityReport {
  let mut out = positivity_absent()
  for i in 0..<entries.length() {
    out = positivity_combine(
      out,
      positivity_param_in_term(entries[i].ty, start_scope + i, param_index),
    )
  }
  out
}

///|
fn positivity_decode_case_scope(
  ctor : DConstructorSpec,
  params : Int32,
) -> Int32 {
  let mut scope = params
  for i in 0..<ctor.args.length() {
    scope = scope + 1
    match ctor.args[i].kind {
      DArgRecursive | DArgFunction | DArgNested | DArgDecodedFunction =>
        scope = scope + 1
      _ => ()
    }
  }
  scope + ctor.constraints.length()
}

///|
/// Least-fixpoint iteration for a vector of parameter reports.
/// Start from the bottom of the information order (absent
/// everywhere) and recompute until stable: the combinators
/// (`combine`, `compose_param`, `flip`, `non_strict`) are
/// monotone in that order -- occurrences and polarities only
/// accumulate, strictness only erodes -- so at most five bit
/// flips per parameter can occur.  The limit is the exact
/// occurrence report of the least (initial-algebra)
/// unfolding: occurrences in any finite unfolding appear at
/// some iterate, and strictness in the limit implies
/// strictness at every finite depth, which is what makes
/// certification from the fixpoint sound for non-uniform
/// (self-nested) families.  Failure to stabilize within the
/// cap (not expected for monotone combinators) falls back to
/// marking every report unknown.
fn positivity_reports_fixpoint(
  count : Int32,
  compute : (Int32, Array[DPositivityReport]) -> DPositivityReport,
) -> Array[DPositivityReport] {
  let mut reports : Array[DPositivityReport] = []
  for _i in 0..<count {
    reports.push(positivity_absent())
  }
  let mut rounds = 0
  while rounds <= 5 * count + 2 {
    let next : Array[DPositivityReport] = []
    let mut stable = true
    for k in 0..<count {
      let r = compute(k, reports)
      if r != reports[k] {
        stable = false
      }
      next.push(r)
    }
    reports = next
    if stable {
      return reports
    }
    rounds = rounds + 1
  }
  for k in 0..<count {
    reports[k] = positivity_mark_unknown(reports[k])
  }
  reports
}

///|
/// One fixpoint step of the parameter-positivity analysis for
/// an inductive spec.  `arg_walk` selects the plain or the
/// declared argument analysis and closes over the current
/// self-report approximation.
fn inductive_parameter_positivity_step(
  spec : DInductiveSpec,
  param_index : Int32,
  arg_walk : (DConstructorArg, Int32, Int32) -> DPositivityReport,
) -> DPositivityReport {
  let mut out = positivity_param_in_telescope(spec.params, 0, param_index)
  out = positivity_combine(
    out,
    positivity_param_in_telescope(
      spec.indices,
      spec.params.length(),
      param_index,
    ),
  )
  for c in 0..<spec.constructors.length() {
    let ctor = spec.constructors[c]
    for i in 0..<ctor.args.length() {
      out = positivity_combine(
        out,
        arg_walk(ctor.args[i], spec.params.length() + i, param_index),
      )
    }
    out = positivity_combine(
      out,
      positivity_param_in_terms(
        ctor.result_index,
        spec.params.length() + ctor.args.length(),
        param_index,
      ),
    )
    for i in 0..<ctor.constraints.length() {
      let scope = spec.params.length() + ctor.args.length()
      out = positivity_combine(
        out,
        positivity_param_in_term(ctor.constraints[i].ty, scope, param_index),
      )
      out = positivity_combine(
        out,
        positivity_param_in_term(ctor.constraints[i].lhs, scope, param_index),
      )
      out = positivity_combine(
        out,
        positivity_param_in_term(ctor.constraints[i].rhs, scope, param_index),
      )
    }
    if c < spec.decode_cases.length() {
      out = positivity_combine(
        out,
        positivity_param_in_term(
          spec.decode_cases[c],
          positivity_decode_case_scope(ctor, spec.params.length()),
          param_index,
        ),
      )
    }
  }
  out
}

///|
/// Certify how one parameter of a generated inductive family is
/// used by its constructors.  A strictly positive report is
/// what permits an indirect recursive occurrence through this
/// family in the structural positivity checker.  Self-nested
/// (`DFunctorSelfFamily`) uses are solved by the least-fixpoint
/// iteration in `positivity_reports_fixpoint`, so non-uniform
/// families such as Bush are certified strictly positive in
/// their stored parameter instead of unknown.
pub fn inductive_parameter_positivity(
  spec : DInductiveSpec,
  param_index : Int32,
) -> DPositivityReport {
  if param_index < 0 || param_index >= spec.params.length() {
    return positivity_absent()
  }
  let has_decode = spec.decode_cases.length() > 0
  let reports = positivity_reports_fixpoint(spec.params.length(), (k, self) => {
    inductive_parameter_positivity_step(spec, k, (arg, scope, pi) => {
      positivity_param_in_arg(arg, scope, pi, has_decode, self)
    })
  })
  reports[param_index]
}

///|
fn hit_parameter_positivity_step(
  spec : DHitSpec,
  param_index : Int32,
  self_reports : Array[DPositivityReport],
) -> DPositivityReport {
  let mut out = positivity_param_in_telescope(spec.params, 0, param_index)
  out = positivity_combine(
    out,
    positivity_param_in_telescope(
      spec.indices,
      spec.params.length(),
      param_index,
    ),
  )
  for c in 0..<spec.cells.length() {
    let cell = spec.cells[c]
    for i in 0..<cell.args.length() {
      out = positivity_combine(
        out,
        positivity_param_in_arg(
          cell.args[i],
          spec.params.length() + i,
          param_index,
          false,
          self_reports,
        ),
      )
    }
    let scope = spec.params.length() + cell.args.length()
    out = positivity_combine(
      out,
      positivity_param_in_terms(cell.result_index, scope, param_index),
    )
    for i in 0..<cell.constraints.length() {
      out = positivity_combine(
        out,
        positivity_param_in_term(cell.constraints[i].ty, scope, param_index),
      )
      out = positivity_combine(
        out,
        positivity_param_in_term(cell.constraints[i].lhs, scope, param_index),
      )
      out = positivity_combine(
        out,
        positivity_param_in_term(cell.constraints[i].rhs, scope, param_index),
      )
    }
    for f in 0..<cell.faces.length() {
      out = positivity_combine(
        out,
        positivity_param_in_terms(cell.faces[f].args, scope, param_index),
      )
    }
  }
  out
}

///|
/// Parameter-use certification for generated HITs, with the
/// same self-report fixpoint as the inductive analysis.
pub fn hit_parameter_positivity(
  spec : DHitSpec,
  param_index : Int32,
) -> DPositivityReport {
  if param_index < 0 || param_index >= spec.params.length() {
    return positivity_absent()
  }
  let reports = positivity_reports_fixpoint(spec.params.length(), (k, self) => {
    hit_parameter_positivity_step(spec, k, self)
  })
  reports[param_index]
}

///|
pub fn schema_telescope_family_occurs(
  entries : Array[DTelescopeEntry],
  name : String,
) -> Bool {
  for i in 0..<entries.length() {
    if dterm_family_occurs(entries[i].ty, name) {
      return true
    }
  }
  false
}

// ---------------------------------------------------------------------------
// Phase 12: positivity declarations for opaque neutral operators.
//
// An application whose head is a neutral operator (typically a
// variable of operator type, such as a spec parameter
// `F : Type -> Type`) is opaque to the structural analysis: any
// family occurrence inside its arguments is reported unknown.
// A `DPositivityDeclaration` lets the caller state which
// argument positions of one such operator are strictly positive
// or merely positive; the declared analysis then treats the
// operator like a known type former at those positions.
// Declarations are *trusted* at face value (shape-checked only),
// exactly like positivity pragmas in other systems: they move
// the proof obligation to the declaration site.  When the
// operator is a literal lambda, `dpositivity_declaration_from_lambda`
// discharges that obligation by running the ordinary structural
// analysis on its body.
//
// The declared walk tracks term-binder depth so a head declared
// at one scope (`scope` in the declaration) is recognised under
// binders and at other scopes by de Bruijn shifting.
// ---------------------------------------------------------------------------

///|
pub struct DPositivityDeclaration {
  head : DTerm
  arity : Int32
  strict_args : Array[Int32]
  positive_args : Array[Int32]
  scope : Int32
} derive(Debug, Eq)

///|
pub extend DPositivityDeclaration with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend DPositivityDeclaration with Eq::{not_equal, equal}

///|
fn positivity_int_contains(xs : Array[Int32], v : Int32) -> Bool {
  for i in 0..<xs.length() {
    if xs[i] == v {
      return true
    }
  }
  false
}

///|
/// Shape-checked declaration constructor: positive arity,
/// argument positions in range, no duplicates, and no position
/// declared both strictly positive and merely positive.
pub fn dpositivity_declaration(
  head : DTerm,
  arity : Int32,
  strict_args~ : Array[Int32] = [],
  positive_args~ : Array[Int32] = [],
  scope~ : Int32 = 0,
) -> DPositivityDeclaration? {
  if arity <= 0 || scope < 0 {
    return None
  }
  for i in 0..<strict_args.length() {
    let p = strict_args[i]
    if p < 0 || p >= arity || positivity_int_contains(positive_args, p) {
      return None
    }
    for j in (i + 1)..<strict_args.length() {
      if strict_args[j] == p {
        return None
      }
    }
  }
  for i in 0..<positive_args.length() {
    let p = positive_args[i]
    if p < 0 || p >= arity {
      return None
    }
    for j in (i + 1)..<positive_args.length() {
      if positive_args[j] == p {
        return None
      }
    }
  }
  Some(DPositivityDeclaration::{
    head,
    arity,
    strict_args,
    positive_args,
    scope,
  })
}

///|
/// Discharge a declaration for a literal lambda operator by
/// structural analysis of its body: each argument position is
/// probed with a fresh family and classified.  `None` when the
/// head is not an `arity`-fold lambda or some position is
/// negative or unknown.  Unused positions are vacuously strict.
pub fn dpositivity_declaration_from_lambda(
  head : DTerm,
  arity : Int32,
  scope~ : Int32 = 0,
) -> DPositivityDeclaration? {
  if arity <= 0 {
    return None
  }
  let mut body = head
  for _i in 0..<arity {
    body = match body {
      DLam(_, b) => b
      _ => return None
    }
  }
  let strict : Array[Int32] = []
  let positive : Array[Int32] = []
  for j in 0..<arity {
    let variable = arity - 1 - j
    let probed = dterm_substitute(body, variable, positivity_probe_term())
    let report = dterm_family_positivity(probed, positivity_probe_name())
    if report.negative_polarity || report.unknown {
      return None
    }
    if !report.occurs || report.strictly_positive {
      strict.push(j)
    } else if report.positive_polarity {
      positive.push(j)
    } else {
      return None
    }
  }
  dpositivity_declaration(
    head,
    arity,
    strict_args=strict,
    positive_args=positive,
    scope~,
  )
}

///|
fn positivity_app_spine(t : DTerm) -> (DTerm, Array[DTerm]) {
  let rev_args : Array[DTerm] = []
  let mut cur = t
  while true {
    match cur {
      DApp(f, a) => {
        rev_args.push(a)
        cur = f
      }
      _ => break
    }
  }
  let args : Array[DTerm] = []
  let mut i = rev_args.length() - 1
  while i >= 0 {
    args.push(rev_args[i])
    i = i - 1
  }
  (cur, args)
}

///|
fn positivity_through_parameter_decl(
  report : DPositivityReport,
  arg : DTerm,
  name : String,
  positive : Bool,
  strict_allowed : Bool,
  fuel : Int32,
  decls : Array[DPositivityDeclaration],
  scope : Int32,
  depth : Int32,
) -> DPositivityReport {
  if report.strictly_positive &&
    report.occurs &&
    !report.unknown &&
    !report.negative_polarity {
    dterm_family_positivity_type_decl(
      arg, name, positive, strict_allowed, fuel, decls, scope, depth,
    )
  } else if report.occurs &&
    report.positive_polarity &&
    !report.negative_polarity &&
    !report.unknown {
    positivity_non_strict(
      dterm_family_positivity_type_decl(
        arg, name, positive, false, fuel, decls, scope, depth,
      ),
    )
  } else if report.occurs &&
    report.negative_polarity &&
    !report.positive_polarity &&
    !report.unknown {
    positivity_non_strict(
      dterm_family_positivity_type_decl(
        arg,
        name,
        !positive,
        false,
        fuel,
        decls,
        scope,
        depth,
      ),
    )
  } else {
    dterm_family_positivity_term(arg, name, fuel)
  }
}

///|
fn dterm_family_positivity_type_decl(
  t : DTerm,
  name : String,
  positive : Bool,
  strict_allowed : Bool,
  fuel : Int32,
  decls : Array[DPositivityDeclaration],
  scope : Int32,
  depth : Int32,
) -> DPositivityReport {
  match t {
    DPi(a, b) =>
      positivity_combine(
        positivity_flip(
          dterm_family_positivity_type_decl(
            a, name, positive, false, fuel, decls, scope, depth,
          ),
        ),
        dterm_family_positivity_type_decl(
          b,
          name,
          positive,
          strict_allowed,
          fuel,
          decls,
          scope,
          depth + 1,
        ),
      )
    DSigma(a, b) =>
      positivity_combine(
        dterm_family_positivity_type_decl(
          a, name, positive, strict_allowed, fuel, decls, scope, depth,
        ),
        dterm_family_positivity_type_decl(
          b,
          name,
          positive,
          strict_allowed,
          fuel,
          decls,
          scope,
          depth + 1,
        ),
      )
    DListTy(a) =>
      dterm_family_positivity_type_decl(
        a, name, positive, strict_allowed, fuel, decls, scope, depth,
      )
    DPathP(line, l, r) =>
      positivity_combine(
        dterm_family_positivity_type_decl(
          line, name, positive, strict_allowed, fuel, decls, scope, depth,
        ),
        positivity_combine(
          dterm_family_positivity_term(l, name, fuel),
          dterm_family_positivity_term(r, name, fuel),
        ),
      )
    DPath(a, l, r) =>
      positivity_combine(
        dterm_family_positivity_type_decl(
          a, name, positive, strict_allowed, fuel, decls, scope, depth,
        ),
        positivity_combine(
          dterm_family_positivity_term(l, name, fuel),
          dterm_family_positivity_term(r, name, fuel),
        ),
      )
    DInductive(spec, args) =>
      if spec.name == name {
        let mut out = positivity_occurrence(positive, strict_allowed)
        for i in 0..<args.length() {
          out = positivity_combine(
            out,
            dterm_family_positivity_term(args[i], name, fuel),
          )
        }
        out
      } else {
        let (params, indices) = schema_split_terms(args, spec.params.length())
        let mut out = positivity_absent()
        for i in 0..<params.length() {
          out = positivity_combine(
            out,
            positivity_through_parameter_decl(
              inductive_parameter_positivity(spec, i),
              params[i],
              name,
              positive,
              strict_allowed,
              fuel,
              decls,
              scope,
              depth,
            ),
          )
        }
        for i in 0..<indices.length() {
          out = positivity_combine(
            out,
            dterm_family_positivity_term(indices[i], name, fuel),
          )
        }
        out
      }
    DHitType(spec, args) =>
      if spec.name == name {
        let mut out = positivity_occurrence(positive, strict_allowed)
        for i in 0..<args.length() {
          out = positivity_combine(
            out,
            dterm_family_positivity_term(args[i], name, fuel),
          )
        }
        out
      } else {
        let (params, indices) = schema_split_terms(args, spec.params.length())
        let mut out = positivity_absent()
        for i in 0..<params.length() {
          out = positivity_combine(
            out,
            positivity_through_parameter_decl(
              hit_parameter_positivity(spec, i),
              params[i],
              name,
              positive,
              strict_allowed,
              fuel,
              decls,
              scope,
              depth,
            ),
          )
        }
        for i in 0..<indices.length() {
          out = positivity_combine(
            out,
            dterm_family_positivity_term(indices[i], name, fuel),
          )
        }
        out
      }
    DApp(_, _) => {
      let (head, args) = positivity_app_spine(t)
      let mut declared : DPositivityDeclaration? = None
      for d in 0..<decls.length() {
        let decl = decls[d]
        if args.length() == decl.arity &&
          dterm_shift(decl.head, 0, scope - decl.scope + depth) == head {
          declared = Some(decl)
          break
        }
      }
      match declared {
        Some(decl) => {
          let mut out = positivity_absent()
          for i in 0..<args.length() {
            let part = if positivity_int_contains(decl.strict_args, i) {
              dterm_family_positivity_type_decl(
                args[i],
                name,
                positive,
                strict_allowed,
                fuel,
                decls,
                scope,
                depth,
              )
            } else if positivity_int_contains(decl.positive_args, i) {
              positivity_non_strict(
                dterm_family_positivity_type_decl(
                  args[i],
                  name,
                  positive,
                  false,
                  fuel,
                  decls,
                  scope,
                  depth,
                ),
              )
            } else {
              dterm_family_positivity_term(args[i], name, fuel)
            }
            out = positivity_combine(out, part)
          }
          out
        }
        None =>
          match t {
            DApp(DLam(_, body), arg) =>
              if fuel <= 0 {
                positivity_unknown()
              } else {
                dterm_family_positivity_type_decl(
                  dterm_substitute(body, 0, arg),
                  name,
                  positive,
                  strict_allowed,
                  fuel - 1,
                  decls,
                  scope,
                  depth,
                )
              }
            _ => dterm_family_positivity_term(t, name, fuel)
          }
      }
    }
    DLam(a, b) =>
      positivity_combine(
        positivity_flip(
          dterm_family_positivity_type_decl(
            a, name, positive, false, fuel, decls, scope, depth,
          ),
        ),
        dterm_family_positivity_type_decl(
          b,
          name,
          positive,
          strict_allowed,
          fuel,
          decls,
          scope,
          depth + 1,
        ),
      )
    DAnn(x, y) =>
      positivity_combine(
        dterm_family_positivity_type_decl(
          x, name, positive, strict_allowed, fuel, decls, scope, depth,
        ),
        dterm_family_positivity_type_decl(
          y, name, positive, strict_allowed, fuel, decls, scope, depth,
        ),
      )
    DLamDim(body) =>
      dterm_family_positivity_type_decl(
        body, name, positive, strict_allowed, fuel, decls, scope, depth,
      )
    DAppDim(x, _) =>
      dterm_family_positivity_type_decl(
        x, name, positive, strict_allowed, fuel, decls, scope, depth,
      )
    DPartial(branches) => {
      let mut out = positivity_absent()
      for i in 0..<branches.length() {
        out = positivity_combine(
          out,
          dterm_family_positivity_type_decl(
            branches[i].body,
            name,
            positive,
            strict_allowed,
            fuel,
            decls,
            scope,
            depth,
          ),
        )
      }
      out
    }
    DCoe(line, _, _, v) =>
      positivity_combine(
        dterm_family_positivity_type_decl(
          line, name, positive, strict_allowed, fuel, decls, scope, depth,
        ),
        dterm_family_positivity_type_decl(
          v, name, positive, strict_allowed, fuel, decls, scope, depth,
        ),
      )
    DComp(line, tubes, base) | DHComp(line, tubes, base) => {
      let mut out = positivity_combine(
        dterm_family_positivity_type_decl(
          line, name, positive, strict_allowed, fuel, decls, scope, depth,
        ),
        dterm_family_positivity_type_decl(
          base, name, positive, strict_allowed, fuel, decls, scope, depth,
        ),
      )
      for i in 0..<tubes.length() {
        out = positivity_combine(
          out,
          dterm_family_positivity_type_decl(
            tubes[i].body,
            name,
            positive,
            strict_allowed,
            fuel,
            decls,
            scope,
            depth,
          ),
        )
      }
      out
    }
    DHFill(a, tubes, base, _) => {
      let mut out = positivity_combine(
        dterm_family_positivity_type_decl(
          a, name, positive, strict_allowed, fuel, decls, scope, depth,
        ),
        dterm_family_positivity_type_decl(
          base, name, positive, strict_allowed, fuel, decls, scope, depth,
        ),
      )
      for i in 0..<tubes.length() {
        out = positivity_combine(
          out,
          dterm_family_positivity_type_decl(
            tubes[i].body,
            name,
            positive,
            strict_allowed,
            fuel,
            decls,
            scope,
            depth,
          ),
        )
      }
      out
    }
    DDecode(spec, _, _, _) =>
      if spec.name == name {
        positivity_combine(
          positivity_unknown(),
          positivity_of_children_term(t, name, fuel),
        )
      } else {
        dterm_family_positivity_term(t, name, fuel)
      }
    _ => dterm_family_positivity_term(t, name, fuel)
  }
}

///|
/// Structural positivity report under trusted declarations for
/// opaque neutral operators.  `scope` is the de Bruijn scope at
/// the top of `t` (the context the declaration heads are
/// shifted from their own declared scopes into).
pub fn dterm_family_positivity_declared(
  t : DTerm,
  name : String,
  decls : Array[DPositivityDeclaration],
  scope~ : Int32 = 0,
) -> DPositivityReport {
  dterm_family_positivity_type_decl(t, name, true, true, 64, decls, scope, 0)
}

///|
pub fn dterm_family_strictly_positive_declared(
  t : DTerm,
  name : String,
  decls : Array[DPositivityDeclaration],
  scope~ : Int32 = 0,
) -> Bool {
  let report = dterm_family_positivity_declared(t, name, decls, scope~)
  report.strictly_positive && !report.unknown && !report.negative_polarity
}

///|
fn positivity_param_in_type_declared(
  t : DTerm,
  scope : Int32,
  param_index : Int32,
  strict_allowed : Bool,
  decls : Array[DPositivityDeclaration],
) -> DPositivityReport {
  // Substituting the probe for the parameter variable also
  // renumbers every later variable down by one, so declaration
  // heads must undergo the same substitution (after shifting
  // them into this scope) and the walk runs at `scope - 1`.
  let variable = scope - 1 - param_index
  let adjusted : Array[DPositivityDeclaration] = []
  if variable >= 0 {
    for i in 0..<decls.length() {
      let d = decls[i]
      adjusted.push(DPositivityDeclaration::{
        head: positivity_substitute_param(
          dterm_shift(d.head, 0, scope - d.scope),
          scope,
          param_index,
        ),
        arity: d.arity,
        strict_args: d.strict_args,
        positive_args: d.positive_args,
        scope: scope - 1,
      })
    }
  }
  let (walk_decls, walk_scope) = if variable >= 0 {
    (adjusted, scope - 1)
  } else {
    (decls, scope)
  }
  dterm_family_positivity_type_decl(
    positivity_substitute_param(t, scope, param_index),
    positivity_probe_name(),
    true,
    strict_allowed,
    64,
    walk_decls,
    walk_scope,
    0,
  )
}

///|
fn positivity_param_in_arg_declared(
  arg : DConstructorArg,
  scope : Int32,
  param_index : Int32,
  has_decode : Bool,
  decls : Array[DPositivityDeclaration],
  self_reports : Array[DPositivityReport],
) -> DPositivityReport {
  match arg.kind {
    DArgExternal =>
      positivity_param_in_type_declared(arg.ty, scope, param_index, true, decls)
    DArgFunction => {
      // The domain enters the ordinary (undeclared) analysis
      // through the declared walk at non-strict polarity; the
      // result index terms stay on the plain term walk.
      let domain = positivity_param_in_type_declared(
        arg.ty,
        scope,
        param_index,
        false,
        decls,
      )
      positivity_combine(
        positivity_non_strict(domain),
        positivity_param_in_terms(arg.index, scope + 1, param_index),
      )
    }
    _ =>
      positivity_param_in_arg(arg, scope, param_index, has_decode, self_reports)
  }
}

///|
/// Parameter-use certification under positivity declarations.
/// Declaration heads are expressed in the spec's telescope
/// scopes (each declaration carries its own `scope`); external
/// and function-argument types are analysed with them, the
/// remaining positions reuse the undeclared analysis.
pub fn inductive_parameter_positivity_declared(
  spec : DInductiveSpec,
  param_index : Int32,
  decls : Array[DPositivityDeclaration],
) -> DPositivityReport {
  if param_index < 0 || param_index >= spec.params.length() {
    return positivity_absent()
  }
  let has_decode = spec.decode_cases.length() > 0
  let reports = positivity_reports_fixpoint(spec.params.length(), (k, self) => {
    inductive_parameter_positivity_step(spec, k, (arg, scope, pi) => {
      positivity_param_in_arg_declared(arg, scope, pi, has_decode, decls, self)
    })
  })
  reports[param_index]
}

///|
/// A machine-checkable positivity certificate pairing an operator
/// `declaration` with its explicit defining lambda/type term
/// `definition`.  Unlike an axiomatic `DPositivityDeclaration`, a
/// `DPositivityWitness` is verified by applying `definition` to fresh
/// probe families, beta-reducing, and auditing the structural
/// polarity of every parameter slot before trusting the declaration.
pub struct DPositivityWitness {
  declaration : DPositivityDeclaration
  definition : DTerm
} derive(Debug, Eq)

///|
pub extend DPositivityWitness with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend DPositivityWitness with Eq::{not_equal, equal}

///|
pub fn dpositivity_witness(
  declaration : DPositivityDeclaration,
  definition : DTerm,
) -> DPositivityWitness {
  DPositivityWitness::{ declaration, definition, }
}

///|
/// Verify that `witness.definition` justifies the strictness and
/// positivity flags claimed by `witness.declaration`:
/// - `arity > 0` and flag array lengths match `arity`;
/// - for every argument `k` (`0 <= k < arity`), instantiating argument
///   `k` with a fresh probe family while leaving all other arguments
///   as neutral parameters yields a structural positivity report free
///   of `unknown` occurrences, free of `negative_polarity` whenever
///   `strict_args[k]` or `positive_args[k]` is claimed, and strictly
///   positive whenever `strict_args[k]` is claimed.
pub fn dpositivity_witness_verify(
  witness : DPositivityWitness,
  ambient_decls~ : Array[DPositivityDeclaration] = [],
) -> Bool {
  let d = witness.declaration
  if d.arity <= 0 || d.scope < 0 {
    return false
  }
  for i in 0..<d.strict_args.length() {
    if d.strict_args[i] < 0 || d.strict_args[i] >= d.arity {
      return false
    }
  }
  for i in 0..<d.positive_args.length() {
    if d.positive_args[i] < 0 || d.positive_args[i] >= d.arity {
      return false
    }
  }
  let probe_term = positivity_probe_term()
  for k in 0..<d.arity {
    let claims_strict = d.strict_args.contains(k)
    let claims_pos = claims_strict || d.positive_args.contains(k)
    let mut applied = dterm_shift(witness.definition, 0, d.arity)
    for j in 0..<d.arity {
      let arg_term = if j == k { probe_term } else { DTVar(d.arity - 1 - j) }
      applied = match applied {
        DLam(_, body) => dterm_substitute(body, 0, arg_term)
        _ => DApp(applied, arg_term)
      }
    }
    let report = dterm_family_positivity_type_decl(
      applied,
      positivity_probe_name(),
      true,
      true,
      64,
      ambient_decls,
      d.scope + d.arity,
      0,
    )
    if report.unknown {
      return false
    }
    if claims_strict && (!report.strictly_positive || report.negative_polarity) {
      return false
    }
    if claims_pos && report.negative_polarity {
      return false
    }
  }
  true
}

///|
/// Certified strict-positivity check: sequentially verifies each
/// `DPositivityWitness` (allowing later witnesses to build on earlier
/// verified witnesses) and checks `t` only if *every* witness passes
/// `dpositivity_witness_verify`.
pub fn dterm_family_strictly_positive_certified(
  t : DTerm,
  name : String,
  witnesses : Array[DPositivityWitness],
  scope~ : Int32 = 0,
) -> Bool {
  let verified_decls : Array[DPositivityDeclaration] = []
  for i in 0..<witnesses.length() {
    if !dpositivity_witness_verify(witnesses[i], ambient_decls=verified_decls) {
      return false
    }
    verified_decls.push(witnesses[i].declaration)
  }
  dterm_family_strictly_positive_declared(t, name, verified_decls, scope~)
}

// ---------------------------------------------------------------------------
// Phase 16: Semantic functorial & container positivity certificates for
// opaque/axiomatic type operators without syntactic unfolding bodies
// ---------------------------------------------------------------------------

///|
/// Semantic evidence justifying positivity of an opaque unary type operator
/// `F : Type[univ_level] -> Type[univ_level]` bound at de Bruijn `level` in
/// an ambient context `ambient_ctx`:
/// - `DFunctorCovariantLaws(map_term, map_id_term, map_comp_term)` certifies
///   covariant (`positive_args = [0]`, non-strict) functoriality via kernel-
///   checked `map_F`, identity preservation, and composition preservation.
///   By Reynolds's theorem (`(X -> Bool) -> Bool` is a lawful covariant
///   functor yet non-strictly positive), covariance laws never grant
///   `strict_args`.
/// - `DFunctorContainerIso(shape_ty, position_fam, container_equiv)` certifies
///   Abbott–Altenkirch–Ghani strict positivity (`strict_args = [0]`) by
///   exhibiting `S : Type[univ_level]`, `P : S -> Type[univ_level]` (not
///   referencing `F`), and a natural family of equivalences
///   `Π (X : Type[univ_level]), Equiv (F X) (Σ (s : S), P s -> X)`.
pub enum DFunctorPositivityEvidence {
  DFunctorCovariantLaws(DTerm, DTerm, DTerm)
  DFunctorContainerIso(DTerm, DTerm, DTerm)
} derive(Debug, Eq)

///|
pub extend DFunctorPositivityEvidence with @moonbitlang/core/debug.Debug::{
  to_repr,
}

///|
pub extend DFunctorPositivityEvidence with Eq::{not_equal, equal}

///|
pub struct DFunctorialPositivityCert {
  level : Int32
  univ_level : Int32
  claim_strict : Bool
  evidence : DFunctorPositivityEvidence
} derive(Debug, Eq)

///|
pub extend DFunctorialPositivityCert with @moonbitlang/core/debug.Debug::{
  to_repr,
}

///|
pub extend DFunctorialPositivityCert with Eq::{not_equal, equal}

///|
pub fn dfunctorial_positivity_covariant_cert(
  level : Int32,
  univ_level : Int32,
  map_term : DTerm,
  map_id_term : DTerm,
  map_comp_term : DTerm,
) -> DFunctorialPositivityCert {
  DFunctorialPositivityCert::{
    level,
    univ_level,
    claim_strict: false,
    evidence: DFunctorCovariantLaws(map_term, map_id_term, map_comp_term),
  }
}

///|
pub fn dfunctorial_positivity_container_cert(
  level : Int32,
  univ_level : Int32,
  shape_ty : DTerm,
  position_fam : DTerm,
  container_equiv : DTerm,
) -> DFunctorialPositivityCert {
  DFunctorialPositivityCert::{
    level,
    univ_level,
    claim_strict: true,
    evidence: DFunctorContainerIso(shape_ty, position_fam, container_equiv),
  }
}

///|
fn dterm_uses_free_var(t : DTerm, target_idx : Int32) -> Bool {
  if target_idx < 0 {
    return false
  }
  let mut found = false
  ignore(
    dterm_map_vars_at(t, 0, (v, depth) => {
      if v == target_idx + depth {
        found = true
      }
      DTVar(v)
    }),
  )
  found
}

///|
/// Kernel-verify a semantic functorial positivity certificate against an
/// explicit ambient telescope `ambient_ctx` (ordered outer-to-inner).
/// Returns the justified `DPositivityDeclaration` when valid, or `None`.
pub fn dfunctorial_positivity_verify(
  ambient_ctx : Array[DTerm],
  cert : DFunctorialPositivityCert,
) -> DPositivityDeclaration? {
  let scope = ambient_ctx.length()
  if cert.level < 0 || cert.level >= scope || cert.univ_level < 0 {
    return None
  }
  // Check that `ambient_ctx` itself is a well-formed telescope and that the
  // target slot `cert.level` has operator type `Type[u] -> Type[u]`.
  let mut ctx = denv_empty()
  let mut env = denv_empty()
  for i in 0..<scope {
    match d_as_type(ambient_ctx[i], ctx, env, ddim_empty()) {
      Some(tv) => {
        let fresh = reflect_var(i, tv.value)
        ctx = denv_cons(tv.value, ctx)
        env = denv_cons(fresh, env)
      }
      None => return None
    }
  }
  let check_term_in_ctx = (tm : DTerm, expected_ty : DTerm) => {
    match d_as_type(expected_ty, ctx, env, ddim_empty()) {
      Some(tv) =>
        match d_check(tm, tv.value, ctx, env, ddim_empty()) {
          Some(_) => true
          None => false
        }
      None => false
    }
  }
  let u_term = DUniv(cert.univ_level)
  let op_expected_term = DPi(u_term, DUniv(cert.univ_level))
  let f_idx = scope - 1 - cert.level
  if !check_term_in_ctx(DTVar(f_idx), op_expected_term) {
    return None
  }
  match cert.evidence {
    DFunctorCovariantLaws(map_term, map_id_term, map_comp_term) => {
      if cert.claim_strict {
        return None
      }
      // `map_term : Π (A : Type_u) (B : Type_u) (f : A -> B) (x : F A), F B`
      // Under binders A (3), B (2), f (1), x (0): F is at `f_idx + 4` (or +2/+3).
      let map_ty = DPi(
        u_term,
        DPi(
          u_term,
          DPi(
            DPi(DTVar(1), DTVar(1)),
            DPi(DApp(DTVar(f_idx + 3), DTVar(2)), DApp(DTVar(f_idx + 4), DTVar(2))),
          ),
        ),
      )
      if !check_term_in_ctx(map_term, map_ty) {
        return None
      }
      // `map_id_term : Π (A : Type_u) (x : F A), Path (F A) (map A A (λa.a) x) x`
      let map_s2 = dterm_shift(map_term, 0, 2)
      let id_fn = DLam(DTVar(1), DTVar(0))
      let map_id_lhs = DApp(
        DApp(DApp(DApp(map_s2, DTVar(1)), DTVar(1)), id_fn),
        DTVar(0),
      )
      let fa_at_2 = DApp(DTVar(f_idx + 2), DTVar(1))
      let map_id_ty = DPi(
        u_term,
        DPi(
          DApp(DTVar(f_idx + 1), DTVar(0)),
          DPath(fa_at_2, map_id_lhs, DTVar(0)),
        ),
      )
      if !check_term_in_ctx(map_id_term, map_id_ty) {
        return None
      }
      // `map_comp_term : Π (A B C : Type_u) (g : B -> C) (f : A -> B) (x : F A),
      //   Path (F C) (map A C (λa. g (f a)) x) (map B C g (map A B f x))`
      // Under 6 binders: A=5, B=4, C=3, g=2, f=1, x=0; F is at `f_idx + 6`.
      let map_s6 = dterm_shift(map_term, 0, 6)
      let gf_fn = DLam(DTVar(5), DApp(DTVar(3), DApp(DTVar(2), DTVar(0))))
      let comp_lhs = DApp(
        DApp(DApp(DApp(map_s6, DTVar(5)), DTVar(3)), gf_fn),
        DTVar(0),
      )
      let inner_fx = DApp(
        DApp(DApp(DApp(map_s6, DTVar(5)), DTVar(4)), DTVar(1)),
        DTVar(0),
      )
      let comp_rhs = DApp(
        DApp(DApp(DApp(map_s6, DTVar(4)), DTVar(3)), DTVar(2)),
        inner_fx,
      )
      let fc_at_6 = DApp(DTVar(f_idx + 6), DTVar(3))
      let map_comp_ty = DPi(
        u_term,
        DPi(
          u_term,
          DPi(
            u_term,
            DPi(
              DPi(DTVar(1), DTVar(1)),
              DPi(
                DPi(DTVar(3), DTVar(3)),
                DPi(
                  DApp(DTVar(f_idx + 5), DTVar(4)),
                  DPath(fc_at_6, comp_lhs, comp_rhs),
                ),
              ),
            ),
          ),
        ),
      )
      if !check_term_in_ctx(map_comp_term, map_comp_ty) {
        return None
      }
      let empty_strict : Array[Int32] = []
      dpositivity_declaration(
        DTVar(f_idx),
        1,
        strict_args=empty_strict,
        positive_args=[0],
        scope~,
      )
    }
    DFunctorContainerIso(shape_ty, position_fam, container_equiv) => {
      // `shape_ty` and `position_fam` must not depend on the opaque operator `F`
      // itself; otherwise circular container witnesses could smuggle `F`.
      if dterm_uses_free_var(shape_ty, f_idx) ||
        dterm_uses_free_var(position_fam, f_idx) {
        return None
      }
      if !check_term_in_ctx(shape_ty, u_term) {
        return None
      }
      let pos_expected = DPi(shape_ty, dterm_shift(u_term, 0, 1))
      if !check_term_in_ctx(position_fam, pos_expected) {
        return None
      }
      // `container_equiv : Π (X : Type_u), Equiv (F X) (Σ (s : S), P s -> X)`
      // Under `X` (0): S is shifted by 1; under `X` (1) and `s` (0): P is shifted by 2.
      let shape_s1 = dterm_shift(shape_ty, 0, 1)
      let pos_s2 = dterm_shift(position_fam, 0, 2)
      let container_ext = DSigma(
        shape_s1,
        DPi(DApp(pos_s2, DTVar(0)), DTVar(2)),
      )
      let equiv_ty = DPi(
        u_term,
        DEquivTy(DApp(DTVar(f_idx + 1), DTVar(0)), container_ext),
      )
      if !check_term_in_ctx(container_equiv, equiv_ty) {
        return None
      }
      let strict_slots : Array[Int32] = if cert.claim_strict { [0] } else { [] }
      let pos_slots : Array[Int32] = if cert.claim_strict { [] } else { [0] }
      dpositivity_declaration(
        DTVar(f_idx),
        1,
        strict_args=strict_slots,
        positive_args=pos_slots,
        scope~,
      )
    }
  }
}

///|
/// Check strict positivity of `t` wrt family `name` in `ambient_ctx` using
/// kernel-verified semantic functorial/container certificates (`certs`) plus
/// optional syntactic unfolding witnesses (`witnesses`).
pub fn dterm_family_strictly_positive_functorial(
  ambient_ctx : Array[DTerm],
  t : DTerm,
  name : String,
  certs : Array[DFunctorialPositivityCert],
  witnesses~ : Array[DPositivityWitness] = [],
) -> Bool {
  let scope = ambient_ctx.length()
  let verified_decls : Array[DPositivityDeclaration] = []
  for i in 0..<certs.length() {
    match dfunctorial_positivity_verify(ambient_ctx, certs[i]) {
      Some(decl) => verified_decls.push(decl)
      None => return false
    }
  }
  for i in 0..<witnesses.length() {
    if witnesses[i].declaration.scope != scope ||
      !dpositivity_witness_verify(witnesses[i], ambient_decls=verified_decls) {
      return false
    }
    verified_decls.push(witnesses[i].declaration)
  }
  dterm_family_strictly_positive_declared(t, name, verified_decls, scope~)
}

