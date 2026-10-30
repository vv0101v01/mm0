///|
// Syntax, semantics, NbE, HOAS, and definitional equality of coe.
//
// Fragment: λ-calculus with products, booleans and unit, plus two
// *computational* constants standing for coercions:
//   TmCoeRefl    — coe along the reflexivity path in the universe
//   TmCoeUaSwap  — coe along ua(swap) : (A×B) = (B×A)
// Their semantics is given by evaluation rules (not axioms):
//   coe^{refl}      ≡ λx.x               (coe i i = id)
//   coe^{ua(swap)}  ≡ λp.(snd p, fst p)   (coe along ua e = equivFun e)
// Because the rules live in the evaluator, these equalities hold
// *definitionally*: NbE assigns both sides the same normal form.  This is
// the sense in which the model implements 同構即相等 with computational
// content: ua turns an isomorphism into an equality whose transport
// computes.
//
// Normalisation by Evaluation: eval maps syntax to a semantic domain of
// MoonBit functions (a higher-order semantics), quote reads values back
// as βπ-normal forms.  The 單值性 (single-valuedness / uniqueness) theorem
// for this fragment is the executable statement
//     nf(nf(t)) = nf(t)   and   t ≡βπ u  ⇒  nf(t) = nf(u),
// i.e. normal forms are unique representatives of definitional-equality
// classes, so definitional equality is decided by comparing normal forms.
//
// HOAS: HTm represents binders by MoonBit functions.  Interpreting first
// order terms into HTm (with smart constructors performing meta-level
// βπ-steps) and reifying back yields exactly the NbE normal form, and
// reifying then interpreting is stable: the HOAS / first-order syntax
// correspondence is an isomorphism modulo definitional equality, and a
// genuine equality on normal forms.

///|
pub enum Term {
  TmVar(Int32) // de Bruijn index
  TmLam(Term)
  TmApp(Term, Term)
  TmPair(Term, Term)
  TmFst(Term)
  TmSnd(Term)
  TmBool(Bool)
  TmUnit
  TmCoeRefl // coe along refl, as a function
  TmCoeUaSwap // coe along ua(swap), as a function
  TmAnn(Term, LTy) // type annotation (erased by evaluation; for typed NbE)
} derive(Debug, Eq)

///|
pub extend Term with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend Term with Eq::{not_equal, equal}

///|
pub enum Neutral {
  NeVar(Int32) // de Bruijn level
  NeApp(Neutral, Value)
  NeFst(Neutral)
  NeSnd(Neutral)
}

///|
pub enum Value {
  VUnit
  VBool(Bool)
  VPair(Value, Value)
  VClosure((Value) -> Value) // semantic function: HOAS domain
  VNeutral(Neutral)
}

///|
pub fn tm_id() -> Term {
  TmLam(TmVar(0))
}

///|
pub fn tm_const() -> Term {
  TmLam(TmLam(TmVar(1)))
}

///|
pub fn tm_swap() -> Term {
  TmLam(TmPair(TmSnd(TmVar(0)), TmFst(TmVar(0))))
}

///|
fn env_cons(v : Value, env : Array[Value]) -> Array[Value] {
  let out : Array[Value] = [v]
  for i in 0..<env.length() {
    out.push(env[i])
  }
  out
}

///|
pub fn vapp(f : Value, arg : Value) -> Value {
  match f {
    VClosure(g) => g(arg)
    VNeutral(n) => VNeutral(NeApp(n, arg))
    _ => VUnit // unreachable for well-typed inputs
  }
}

///|
pub fn vfst(v : Value) -> Value {
  match v {
    VPair(a, _) => a
    VNeutral(n) => VNeutral(NeFst(n))
    _ => VUnit
  }
}

///|
pub fn vsnd(v : Value) -> Value {
  match v {
    VPair(_, b) => b
    VNeutral(n) => VNeutral(NeSnd(n))
    _ => VUnit
  }
}

///|
/// Evaluation into the higher-order semantic domain.
pub fn eval(t : Term, env : Array[Value]) -> Value {
  match t {
    TmVar(i) =>
      if i >= 0 && i < env.length() {
        env[i]
      } else {
        VNeutral(NeVar(0))
      }
    TmLam(body) => VClosure(arg => eval(body, env_cons(arg, env)))
    TmApp(f, a) => vapp(eval(f, env), eval(a, env))
    TmPair(a, b) => VPair(eval(a, env), eval(b, env))
    TmFst(a) => vfst(eval(a, env))
    TmSnd(a) => vsnd(eval(a, env))
    TmBool(b) => VBool(b)
    TmUnit => VUnit
    // The coe computation rules are evaluation rules:
    TmCoeRefl => VClosure(x => x)
    TmCoeUaSwap => eval(tm_swap(), env)
    TmAnn(t, _) => eval(t, env)
  }
}

///|
pub fn quote_neutral(level : Int32, n : Neutral) -> Term {
  match n {
    NeVar(l) => TmVar(level - 1 - l)
    NeApp(f, a) => TmApp(quote_neutral(level, f), quote(level, a))
    NeFst(a) => TmFst(quote_neutral(level, a))
    NeSnd(a) => TmSnd(quote_neutral(level, a))
  }
}

///|
pub fn quote(level : Int32, v : Value) -> Term {
  match v {
    VUnit => TmUnit
    VBool(b) => TmBool(b)
    VPair(a, b) => TmPair(quote(level, a), quote(level, b))
    VClosure(g) => TmLam(quote(level + 1, g(VNeutral(NeVar(level)))))
    VNeutral(n) => quote_neutral(level, n)
  }
}

///|
fn fresh_env(nfree : Int32) -> Array[Value] {
  let env : Array[Value] = []
  for i in 0..<nfree {
    // de Bruijn index i corresponds to level nfree−1−i
    env.push(VNeutral(NeVar(nfree - 1 - i)))
  }
  env
}

///|
/// NbE normal form of a term with `nfree` free variables.
pub fn nf(t : Term, nfree : Int32) -> Term {
  quote(nfree, eval(t, fresh_env(nfree)))
}

///|
/// Definitional (βπ + coe) equality, decided by NbE.
pub fn def_eq(t : Term, u : Term, nfree : Int32) -> Bool {
  nf(t, nfree) == nf(u, nfree)
}

///|
/// Uniqueness / single-valuedness of normal forms on a set of samples:
/// normalising twice changes nothing, and every term is definitionally
/// equal to its normal form.
pub fn nbe_single_valued(terms : Array[Term], nfree : Int32) -> Bool {
  for i in 0..<terms.length() {
    let t = terms[i]
    let once = nf(t, nfree)
    if nf(once, nfree) != once {
      return false
    }
    if !def_eq(t, once, nfree) {
      return false
    }
  }
  true
}

///|
/// The coe computation rules hold definitionally:
/// coe along refl *is* the identity and coe along ua(swap) *is* swap,
/// as decided by normal-form equality (not merely up to a path).
pub fn coe_rules_definitional() -> Bool {
  def_eq(TmCoeRefl, tm_id(), 0) &&
  def_eq(TmCoeUaSwap, tm_swap(), 0) &&
  // ... hence on elements: coe^{ua swap} (true, ()) ≡ ((), true)
  def_eq(
    TmApp(TmCoeUaSwap, TmPair(TmBool(true), TmUnit)),
    TmPair(TmUnit, TmBool(true)),
    0,
  )
}

///|
/// Product commutativity is involutive on elements:
/// swap (swap p) ≡ p — shown here for a closed element, by NbE.
pub fn swap_involutive_on_element() -> Bool {
  let p = TmPair(TmBool(true), TmUnit)
  def_eq(TmApp(tm_swap(), TmApp(tm_swap(), p)), p, 0)
}

// ---------------------------------------------------------------------------
// HOAS: binders are MoonBit functions.
// ---------------------------------------------------------------------------

///|
pub enum HTm {
  HVar(Int32) // de Bruijn level
  HBool(Bool)
  HUnit
  HPair(HTm, HTm)
  HLam((HTm) -> HTm) // the binder is a host-language function
  HApp(HTm, HTm)
  HFst(HTm)
  HSnd(HTm)
}

///|
/// Smart application: meta-level β-step when the head is a HOAS lambda.
pub fn happ(f : HTm, a : HTm) -> HTm {
  match f {
    HLam(g) => g(a)
    _ => HApp(f, a)
  }
}

///|
pub fn hfst(v : HTm) -> HTm {
  match v {
    HPair(a, _) => a
    _ => HFst(v)
  }
}

///|
pub fn hsnd(v : HTm) -> HTm {
  match v {
    HPair(_, b) => b
    _ => HSnd(v)
  }
}

///|
fn henv_cons(v : HTm, env : Array[HTm]) -> Array[HTm] {
  let out : Array[HTm] = [v]
  for i in 0..<env.length() {
    out.push(env[i])
  }
  out
}

///|
/// Interpret first-order syntax in the HOAS domain.
pub fn term_to_hoas(t : Term, env : Array[HTm]) -> HTm {
  match t {
    TmVar(i) => if i >= 0 && i < env.length() { env[i] } else { HVar(0) }
    TmLam(body) => HLam(x => term_to_hoas(body, henv_cons(x, env)))
    TmApp(f, a) => happ(term_to_hoas(f, env), term_to_hoas(a, env))
    TmPair(a, b) => HPair(term_to_hoas(a, env), term_to_hoas(b, env))
    TmFst(a) => hfst(term_to_hoas(a, env))
    TmSnd(a) => hsnd(term_to_hoas(a, env))
    TmBool(b) => HBool(b)
    TmUnit => HUnit
    TmCoeRefl => HLam(x => x)
    TmCoeUaSwap => HLam(p => HPair(hsnd(p), hfst(p)))
    TmAnn(t, _) => term_to_hoas(t, env)
  }
}

///|
/// Reify HOAS back to first-order syntax at a given level.
pub fn hoas_to_term(level : Int32, h : HTm) -> Term {
  match h {
    HVar(l) => TmVar(level - 1 - l)
    HBool(b) => TmBool(b)
    HUnit => TmUnit
    HPair(a, b) => TmPair(hoas_to_term(level, a), hoas_to_term(level, b))
    HLam(g) => TmLam(hoas_to_term(level + 1, g(HVar(level))))
    HApp(f, a) => TmApp(hoas_to_term(level, f), hoas_to_term(level, a))
    HFst(a) => TmFst(hoas_to_term(level, a))
    HSnd(a) => TmSnd(hoas_to_term(level, a))
  }
}

///|
fn hoas_of_term(t : Term, nfree : Int32) -> HTm {
  let env : Array[HTm] = []
  for i in 0..<nfree {
    env.push(HVar(nfree - 1 - i))
  }
  term_to_hoas(t, env)
}

///|
/// HOAS isomorphism, one round-trip: interpreting a term in HOAS and
/// reifying gives precisely its NbE normal form.
pub fn hoas_roundtrip_term(t : Term, nfree : Int32) -> Bool {
  hoas_to_term(nfree, hoas_of_term(t, nfree)) == nf(t, nfree)
}

///|
/// HOAS isomorphism, other round-trip: reifying a HOAS term, reinterpreting
/// and reifying again is stable (equal to the normal form of the first
/// reification — the two syntaxes agree up to definitional equality and
/// literally on normal forms).
pub fn hoas_roundtrip_hoas(h : HTm, nfree : Int32) -> Bool {
  let first = hoas_to_term(nfree, h)
  let second = hoas_to_term(nfree, hoas_of_term(first, nfree))
  second == nf(first, nfree)
}

///|
pub fn hoas_swap_example() -> HTm {
  HLam(p => HPair(hsnd(p), hfst(p)))
}

///|
pub fn hoas_const_example() -> HTm {
  HLam(x => HLam(_y => x))
}
