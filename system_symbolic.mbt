///|
// Symbolic normal form of a system (partial element).
//
// First-match semantics gives each branch an *effective region*
//   effᵢ = φᵢ ∧ ¬(φ₁ ∨ … ∨ φᵢ₋₁),
// computed with BDD operations.  Grouping effective regions by value and
// sorting the classes lexicographically by value yields a canonical
// representative of the system's quotient class: a finite partition of
// the cube of endpoint assignments into BDD regions, each labelled by a
// vector, plus the undefined region.  Quotient equality of systems is
// equality of these partitions — decided symbolically, with no 2ⁿ scan.
//
// Categorically, a system is a morphism from a cofibration-indexed
// partial domain; the normal form is its decomposition as a coproduct
// (disjoint union over BDD regions) of constant maps, i.e. the image
// factorisation of the partial element in the slice over the face lattice.

///|
pub struct SymRegion {
  value : CVec
  mut region : Bdd
}

///|
pub struct SystemNF {
  classes : Array[SymRegion]
  undefined : Bdd
}

///|
pub fn vec_lex_lt(a : CVec, b : CVec) -> Bool {
  let n = if a.length() < b.length() { a.length() } else { b.length() }
  for i in 0..<n {
    if (a[i].re - b[i].re).abs() > eps {
      return a[i].re < b[i].re
    }
    if (a[i].im - b[i].im).abs() > eps {
      return a[i].im < b[i].im
    }
  }
  a.length() < b.length()
}

///|
/// The symbolic normal form: disjoint BDD regions per value.
pub fn system_normal_form(s : VecSystem, nvars : Int32) -> SystemNF {
  let classes : Array[SymRegion] = []
  let mut covered = BddZero
  for i in 0..<s.branches.length() {
    let bi = s.branches[i]
    let region_all = bdd_of_face(bi.face, nvars)
    let effective = bdd_and(region_all, bdd_not(covered))
    covered = bdd_or(covered, region_all)
    if effective == BddZero {
      continue
    }
    let mut merged = false
    for k in 0..<classes.length() {
      if vec_approx_eq(classes[k].value, bi.value) {
        classes[k].region = bdd_or(classes[k].region, effective)
        merged = true
      }
    }
    if !merged {
      classes.push(SymRegion::{ value: bi.value, region: effective, })
    }
  }
  // Canonical class order: lexicographic by value.
  for _pass in 0..<classes.length() {
    for j in 0..<(classes.length() - 1) {
      if vec_lex_lt(classes[j + 1].value, classes[j].value) {
        let tmp = classes[j]
        classes[j] = classes[j + 1]
        classes[j + 1] = tmp
      }
    }
  }
  SystemNF::{ classes, undefined: bdd_not(covered), }
}

///|
/// Symbolic quotient equality of systems, via normal forms.
pub fn system_eq_mod_sym(a : VecSystem, b : VecSystem, nvars : Int32) -> Bool {
  let na = system_normal_form(a, nvars)
  let nb = system_normal_form(b, nvars)
  if na.undefined != nb.undefined || na.classes.length() != nb.classes.length() {
    return false
  }
  for i in 0..<na.classes.length() {
    // classes are canonically ordered, so compare in lockstep
    if !vec_approx_eq(na.classes[i].value, nb.classes[i].value) ||
      na.classes[i].region != nb.classes[i].region {
      return false
    }
  }
  true
}

///|
/// The defined region of a system as a BDD (the union of its faces).
pub fn system_domain_bdd(s : VecSystem, nvars : Int32) -> Bdd {
  bdd_not(system_normal_form(s, nvars).undefined)
}
