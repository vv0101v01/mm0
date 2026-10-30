///|
// Symbolic decision for face formulas via reduced ordered BDDs.
//
// The first version decided face satisfiability / entailment / equality
// by enumerating all 2ⁿ endpoint assignments.  This module replaces that
// with a symbolic normal form: every face formula compiles to a reduced
// ordered binary decision diagram (variables in increasing order, nodes
// with equal children eliminated).  Two faces are equal in the quotient
// iff their BDDs are *structurally identical* — the BDD is the canonical
// representative of the quotient class.  Satisfiability is "BDD ≠ ⊥",
// entailment is "bdd(f ∧ ¬g) = ⊥", and a satisfying assignment can be
// read off a root-to-⊤ path (witness), all without enumerating the cube.
//
// Categorically, faces modulo BDD equality form a bounded distributive
// lattice, i.e. a poset category with ∧ as product, ∨ as coproduct,
// ⊤ terminal and ⊥ initial; face_le is its (unique) morphism existence.
//
// The brute-force enumerator survives only in the whitebox tests, as an
// independent oracle that the symbolic decisions are differentially
// checked against; library decision paths never call it.

///|
pub enum Bdd {
  BddZero
  BddOne
  BddNode(Int32, Bdd, Bdd) // variable, low (x=0), high (x=1)
} derive(Debug, Eq)

///|
pub extend Bdd with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend Bdd with Eq::{not_equal, equal}

///|
fn bdd_node(vidx : Int32, lo : Bdd, hi : Bdd) -> Bdd {
  if lo == hi {
    lo // reduction rule: a test with equal outcomes is no test
  } else {
    BddNode(vidx, lo, hi)
  }
}

///|
pub fn contains_int(xs : Array[Int32], x : Int32) -> Bool {
  for i in 0..<xs.length() {
    if xs[i] == x {
      return true
    }
  }
  false
}

///|
fn dim_vars_into(r : Dim, acc : Array[Int32]) -> Unit {
  match r {
    DZero | DOne => ()
    DVar(i) => if !contains_int(acc, i) { acc.push(i) }
    DNeg(a) => dim_vars_into(a, acc)
    DAnd(a, b) => {
      dim_vars_into(a, acc)
      dim_vars_into(b, acc)
    }
    DOr(a, b) => {
      dim_vars_into(a, acc)
      dim_vars_into(b, acc)
    }
  }
}

///|
fn face_vars_into(f : Face, acc : Array[Int32]) -> Unit {
  match f {
    FTop | FBot => ()
    FEq0(r) | FEq1(r) => dim_vars_into(r, acc)
    FAnd(a, b) => {
      face_vars_into(a, acc)
      face_vars_into(b, acc)
    }
    FOr(a, b) => {
      face_vars_into(a, acc)
      face_vars_into(b, acc)
    }
  }
}

///|
/// Variables occurring in a face, sorted increasingly (the BDD order).
pub fn face_vars(f : Face) -> Array[Int32] {
  let acc : Array[Int32] = []
  face_vars_into(f, acc)
  @algebra.int_sort(acc)
}

///|
/// Constant simplification of dimension expressions (the endpoint
/// Boolean algebra): this rewriting is what prunes the BDD construction.
pub fn dim_simplify(r : Dim) -> Dim {
  match r {
    DNeg(a) =>
      match dim_simplify(a) {
        DZero => DOne
        DOne => DZero
        DNeg(x) => x
        x => DNeg(x)
      }
    DAnd(a, b) =>
      match (dim_simplify(a), dim_simplify(b)) {
        (DZero, _) | (_, DZero) => DZero
        (DOne, x) => x
        (x, DOne) => x
        (x, y) => if x == y { x } else { DAnd(x, y) }
      }
    DOr(a, b) =>
      match (dim_simplify(a), dim_simplify(b)) {
        (DOne, _) | (_, DOne) => DOne
        (DZero, x) => x
        (x, DZero) => x
        (x, y) => if x == y { x } else { DOr(x, y) }
      }
    other => other
  }
}

///|
pub fn dim_subst(r : Dim, vidx : Int32, val : Bool) -> Dim {
  match r {
    DVar(i) => if i == vidx { if val { DOne } else { DZero } } else { r }
    DNeg(a) => dim_simplify(DNeg(dim_subst(a, vidx, val)))
    DAnd(a, b) =>
      dim_simplify(DAnd(dim_subst(a, vidx, val), dim_subst(b, vidx, val)))
    DOr(a, b) =>
      dim_simplify(DOr(dim_subst(a, vidx, val), dim_subst(b, vidx, val)))
    other => other
  }
}

///|
pub fn face_simplify(f : Face) -> Face {
  match f {
    FEq0(r) =>
      match dim_simplify(r) {
        DZero => FTop
        DOne => FBot
        x => FEq0(x)
      }
    FEq1(r) =>
      match dim_simplify(r) {
        DZero => FBot
        DOne => FTop
        x => FEq1(x)
      }
    FAnd(a, b) =>
      match (face_simplify(a), face_simplify(b)) {
        (FBot, _) | (_, FBot) => FBot
        (FTop, x) => x
        (x, FTop) => x
        (x, y) => if x == y { x } else { FAnd(x, y) }
      }
    FOr(a, b) =>
      match (face_simplify(a), face_simplify(b)) {
        (FTop, _) | (_, FTop) => FTop
        (FBot, x) => x
        (x, FBot) => x
        (x, y) => if x == y { x } else { FOr(x, y) }
      }
    other => other
  }
}

///|
pub fn face_subst(f : Face, vidx : Int32, val : Bool) -> Face {
  match f {
    FEq0(r) => face_simplify(FEq0(dim_subst(r, vidx, val)))
    FEq1(r) => face_simplify(FEq1(dim_subst(r, vidx, val)))
    FAnd(a, b) =>
      face_simplify(FAnd(face_subst(a, vidx, val), face_subst(b, vidx, val)))
    FOr(a, b) =>
      face_simplify(FOr(face_subst(a, vidx, val), face_subst(b, vidx, val)))
    other => other
  }
}

///|
fn dim_bound(r : Dim, n : Int32) -> Dim {
  match r {
    DVar(i) => if i < 0 || i >= n { DZero } else { r }
    DNeg(a) => dim_simplify(DNeg(dim_bound(a, n)))
    DAnd(a, b) => dim_simplify(DAnd(dim_bound(a, n), dim_bound(b, n)))
    DOr(a, b) => dim_simplify(DOr(dim_bound(a, n), dim_bound(b, n)))
    other => other
  }
}

///|
/// Variable indices outside [0, n) denote 0, matching eval_dim_bool.
pub fn face_bound(f : Face, n : Int32) -> Face {
  match f {
    FEq0(r) => face_simplify(FEq0(dim_bound(r, n)))
    FEq1(r) => face_simplify(FEq1(dim_bound(r, n)))
    FAnd(a, b) => face_simplify(FAnd(face_bound(a, n), face_bound(b, n)))
    FOr(a, b) => face_simplify(FOr(face_bound(a, n), face_bound(b, n)))
    other => other
  }
}

///|
/// The canonical form of a face over variables [0, n): its ROBDD.
pub fn bdd_of_face(f : Face, n : Int32) -> Bdd {
  // Built in the interned DAG manager (bdd_dag.mbt), then expanded
  // once to the legacy tree type with shared subdiagrams shared.
  let manager = bdd_manager_new(n)
  let root = bdd_dag_build_face(manager, face_bound(f, n))
  bdd_tree_of_dag(manager, root)
}

///|
pub fn bdd_not(b : Bdd) -> Bdd {
  match b {
    BddZero => BddOne
    BddOne => BddZero
    BddNode(v, lo, hi) => bdd_node(v, bdd_not(lo), bdd_not(hi))
  }
}

///|
pub fn bdd_and(a : Bdd, b : Bdd) -> Bdd {
  match (a, b) {
    (BddZero, _) | (_, BddZero) => BddZero
    (BddOne, x) => x
    (x, BddOne) => x
    (BddNode(v, alo, ahi), BddNode(w, blo, bhi)) =>
      if v == w {
        bdd_node(v, bdd_and(alo, blo), bdd_and(ahi, bhi))
      } else if v < w {
        bdd_node(v, bdd_and(alo, b), bdd_and(ahi, b))
      } else {
        bdd_node(w, bdd_and(a, blo), bdd_and(a, bhi))
      }
  }
}

///|
pub fn bdd_or(a : Bdd, b : Bdd) -> Bdd {
  match (a, b) {
    (BddOne, _) | (_, BddOne) => BddOne
    (BddZero, x) => x
    (x, BddZero) => x
    (BddNode(v, alo, ahi), BddNode(w, blo, bhi)) =>
      if v == w {
        bdd_node(v, bdd_or(alo, blo), bdd_or(ahi, bhi))
      } else if v < w {
        bdd_node(v, bdd_or(alo, b), bdd_or(ahi, b))
      } else {
        bdd_node(w, bdd_or(a, blo), bdd_or(a, bhi))
      }
  }
}

///|
/// Cofactor by one variable assignment, preserving the ordered
/// reduced form.
pub fn bdd_tree_cofactor(b : Bdd, variable : Int32, value : Bool) -> Bdd {
  match b {
    BddZero | BddOne => b
    BddNode(v, lo, hi) =>
      if v == variable {
        if value {
          hi
        } else {
          lo
        }
      } else if v > variable {
        b
      } else {
        bdd_node(
          v,
          bdd_tree_cofactor(lo, variable, value),
          bdd_tree_cofactor(hi, variable, value),
        )
      }
  }
}

///|
/// Symbolic satisfiability.
pub fn bdd_sat_face(f : Face, n : Int32) -> Bool {
  bdd_dag_sat_face(f, n)
}

///|
/// Symbolic entailment: f ≤ g iff f ∧ ¬g is unsatisfiable.
pub fn bdd_face_le(f : Face, g : Face, n : Int32) -> Bool {
  bdd_dag_face_le(f, g, n)
}

///|
/// Symbolic quotient equality: identical canonical forms.
pub fn bdd_face_eq(f : Face, g : Face, n : Int32) -> Bool {
  bdd_dag_face_eq(f, g, n)
}

///|
/// A satisfying endpoint assignment read off the BDD, if one exists.
pub fn face_witness(f : Face, n : Int32) -> Array[Bool]? {
  let manager = bdd_manager_new(n)
  let root = bdd_dag_build_face(manager, f)
  bdd_dag_witness(manager, root)
}

///|
/// Canonical-form spot laws: duplicates and units vanish in the BDD,
/// De Morgan-shaped rewrites coincide, and witnesses satisfy the face.
pub fn check_bdd_canonical() -> Bool {
  let i0 = face_var0(0)
  let j1 = face_var1(1)
  let f = FOr(i0, j1)
  if bdd_of_face(FOr(f, f), 2) != bdd_of_face(f, 2) {
    return false
  }
  if bdd_of_face(FAnd(FTop, f), 2) != bdd_of_face(f, 2) {
    return false
  }
  if bdd_of_face(FAnd(i0, face_var1(0)), 2) != BddZero {
    return false
  }
  // (i=0) as a face is the constant-true under (¬i=1): FEq1(DNeg i) ≡ FEq0(i)
  if !bdd_face_eq(FEq1(DNeg(DVar(0))), i0, 2) {
    return false
  }
  match face_witness(FAnd(i0, j1), 2) {
    Some(env) => face_holds(FAnd(i0, j1), env) && !env[0] && env[1]
    None => false
  }
}
