///|
// The cubical interval and face (cofibration) formulas.
//
// The interval I is a De Morgan algebra: dimension expressions are built
// from 0, 1, variables, ¬ (1−x), ∧ (min), ∨ (max).  Semantically a
// dimension expression denotes a function Iⁿ → I; at the endpoints it
// denotes a boolean function, which is what face formulas test.
//
// A face formula φ (cofibration) is built from equations (r = 0), (r = 1)
// by ∧ and ∨.  Because the endpoint semantics is finite (2ⁿ assignments),
// satisfiability, entailment φ ≤ ψ and equality of faces are decidable by
// exhaustive enumeration.  The quotient of systems by face equality — and
// pruning of unsatisfiable / subsumed branches — rests on these decisions.

///|
pub enum Dim {
  DZero
  DOne
  DVar(Int32)
  DNeg(Dim)
  DAnd(Dim, Dim)
  DOr(Dim, Dim)
} derive(Debug, Eq)

///|
pub extend Face with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend Face with Eq::{not_equal, equal}

///|
pub extend Dim with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend Dim with Eq::{not_equal, equal}

///|
/// Shared tolerance for the floating semantic layers.  It lives in
/// the foundation component because interval laws use it too.
/// Cross-package Dim constructors.  The enums remain non-`pub(all)`;
/// these functions are the deliberate construction boundary.
pub fn dim_zero() -> Dim {
  DZero
}

///|
pub fn dim_one() -> Dim {
  DOne
}

///|
pub fn dim_var(i : Int32) -> Dim {
  DVar(i)
}

///|
pub fn dim_neg(a : Dim) -> Dim {
  DNeg(a)
}

///|
pub fn dim_and(a : Dim, b : Dim) -> Dim {
  DAnd(a, b)
}

///|
pub fn dim_or(a : Dim, b : Dim) -> Dim {
  DOr(a, b)
}

///|
pub let eps : Double = 0.000000001

///|
pub fn dmin(a : Double, b : Double) -> Double {
  if a < b {
    a
  } else {
    b
  }
}

///|
pub fn dmax(a : Double, b : Double) -> Double {
  if a > b {
    a
  } else {
    b
  }
}

///|
/// Interval semantics: env assigns each dimension variable a point of I.
pub fn eval_dim(r : Dim, env : Array[Double]) -> Double {
  match r {
    DZero => 0.0
    DOne => 1.0
    DVar(i) => if i >= 0 && i < env.length() { env[i] } else { 0.0 }
    DNeg(a) => 1.0 - eval_dim(a, env)
    DAnd(a, b) => dmin(eval_dim(a, env), eval_dim(b, env))
    DOr(a, b) => dmax(eval_dim(a, env), eval_dim(b, env))
  }
}

///|
/// Endpoint (boolean) semantics of a dimension expression.
pub fn eval_dim_bool(r : Dim, env : Array[Bool]) -> Bool {
  match r {
    DZero => false
    DOne => true
    DVar(i) => if i >= 0 && i < env.length() { env[i] } else { false }
    DNeg(a) => !eval_dim_bool(a, env)
    DAnd(a, b) => eval_dim_bool(a, env) && eval_dim_bool(b, env)
    DOr(a, b) => eval_dim_bool(a, env) || eval_dim_bool(b, env)
  }
}

///|
/// De Morgan / lattice laws of I hold definitionally in the semantics.
/// Spot-check the characteristic ones on sample points: ¬¬r = r,
/// r ∧ ¬r and r ∨ ¬r are the *non-boolean* middle values min(x,1−x) /
/// max(x,1−x), and De Morgan duality ¬(a∧b) = ¬a ∨ ¬b.
pub fn interval_laws_hold(samples : Array[Double]) -> Bool {
  for s in 0..<samples.length() {
    let x = samples[s]
    let env : Array[Double] = [x]
    let r = DVar(0)
    if (eval_dim(DNeg(DNeg(r)), env) - x).abs() >= eps {
      return false
    }
    let meet_self = eval_dim(DAnd(r, DNeg(r)), env)
    if (meet_self - dmin(x, 1.0 - x)).abs() >= eps {
      return false
    }
    let join_self = eval_dim(DOr(r, DNeg(r)), env)
    if (join_self - dmax(x, 1.0 - x)).abs() >= eps {
      return false
    }
    let lhs = eval_dim(DNeg(DAnd(r, DOne)), env)
    let rhs = eval_dim(DOr(DNeg(r), DNeg(DOne)), env)
    if (lhs - rhs).abs() >= eps {
      return false
    }
  }
  true
}

///|
pub enum Face {
  FTop
  FBot
  FEq0(Dim)
  FEq1(Dim)
  FAnd(Face, Face)
  FOr(Face, Face)
} derive(Debug, Eq)

///|
/// Does the face hold at this endpoint assignment?
/// Cross-package Face constructor: true.
pub fn face_top() -> Face {
  FTop
}

///|
/// Cross-package Face constructor: false.
pub fn face_bot() -> Face {
  FBot
}

///|
/// Cross-package Face constructor: dimension equals zero.
pub fn face_eq0(r : Dim) -> Face {
  FEq0(r)
}

///|
/// Cross-package Face constructor: dimension equals one.
pub fn face_eq1(r : Dim) -> Face {
  FEq1(r)
}

///|
/// Cross-package Face constructor: conjunction.
pub fn face_and(a : Face, b : Face) -> Face {
  FAnd(a, b)
}

///|
/// Cross-package Face constructor: disjunction.
pub fn face_or(a : Face, b : Face) -> Face {
  FOr(a, b)
}

///|
pub fn face_holds(f : Face, env : Array[Bool]) -> Bool {
  match f {
    FTop => true
    FBot => false
    FEq0(r) => !eval_dim_bool(r, env)
    FEq1(r) => eval_dim_bool(r, env)
    FAnd(a, b) => face_holds(a, env) && face_holds(b, env)
    FOr(a, b) => face_holds(a, env) || face_holds(b, env)
  }
}

///|
pub fn pow2(n : Int32) -> Int32 {
  let mut acc = 1
  for _i in 0..<n {
    acc = acc * 2
  }
  acc
}

///|
/// The `mask`-th endpoint assignment of `n` dimension variables.
pub fn assignment_of_mask(mask : Int32, n : Int32) -> Array[Bool] {
  let env : Array[Bool] = []
  for k in 0..<n {
    env.push(((mask >> k) & 1) == 1)
  }
  env
}

///|
/// Satisfiability of a face over n variables, decided symbolically (ROBDD ≠ ⊥; see bdd.mbt).
pub fn face_sat(f : Face, n : Int32) -> Bool {
  bdd_sat_face(f, n)
}

///|
pub fn face_unsat(f : Face, n : Int32) -> Bool {
  !face_sat(f, n)
}

///|
/// Entailment of faces: φ ≤ ψ iff every endpoint satisfying φ satisfies ψ.
pub fn face_le(f : Face, g : Face, n : Int32) -> Bool {
  bdd_face_le(f, g, n)
}

///|
/// Equality in the quotient of face formulas by semantic equivalence:
/// decided by structural equality of canonical ROBDDs (bdd.mbt).  Syntactically different formulas
/// (e.g. φ ∨ φ and φ) become *equal* here — the quotient that system
/// pruning and system equivalence are taken modulo.
pub fn face_eq_mod(f : Face, g : Face, n : Int32) -> Bool {
  bdd_face_eq(f, g, n)
}

///|
/// The face (i = 0) for the i-th dimension variable.
pub fn face_var0(i : Int32) -> Face {
  FEq0(DVar(i))
}

///|
/// The face (i = 1) for the i-th dimension variable.
pub fn face_var1(i : Int32) -> Face {
  FEq1(DVar(i))
}
