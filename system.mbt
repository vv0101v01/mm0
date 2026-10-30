///|
// Systems (partial elements) over CVec, modulo the face quotient.
//
// A system [ φ₁ ↦ a₁, …, φₖ ↦ aₖ ] is a partial element: on the face φᵢ
// it is prescribed to be aᵢ.  It is *compatible* (well-formed) when
// prescriptions agree on overlaps:  on φᵢ ∧ φⱼ,  aᵢ = aⱼ.
//
// Two systems are equal in the quotient when they prescribe the same value
// at every endpoint assignment.  `prune_system` computes a smaller
// representative of the same quotient class by deleting
//   * branches whose face is unsatisfiable (never active), and
//   * branches subsumed by another branch with the same value
//     (φ ≤ ψ and same value ⇒ the φ-branch is redundant).
// Pruning is the syntactic counterpart of eigenspace pruning by P:
// it removes components that cannot be observed.
//
// Union of compatible systems is commutative in the quotient, and
// compatibility is preserved under quotient equality: replacing a system
// by its pruning never changes whether it extends compatibly.  These are
// the "商可交換性 / 相容性" (quotient commutativity / compatibility) laws.

///|
pub struct VecBranch {
  face : Face
  value : CVec
}

///|
pub struct VecSystem {
  branches : Array[VecBranch]
}

///|
pub fn system_of(branches : Array[VecBranch]) -> VecSystem {
  VecSystem::{ branches, }
}

///|
pub fn branch(face : Face, value : CVec) -> VecBranch {
  VecBranch::{ face, value, }
}

///|
/// The value prescribed at an endpoint assignment, if any branch is active.
/// For compatible systems the choice of active branch does not matter.
pub fn system_lookup(s : VecSystem, env : Array[Bool]) -> CVec? {
  for i in 0..<s.branches.length() {
    if face_holds(s.branches[i].face, env) {
      return Some(s.branches[i].value)
    }
  }
  None
}

///|
/// Compatibility: whenever two faces can hold simultaneously, the
/// prescribed values agree.
pub fn system_compatible(s : VecSystem, nvars : Int32) -> Bool {
  let k = s.branches.length()
  for i in 0..<k {
    for j in 0..<k {
      let overlap = FAnd(s.branches[i].face, s.branches[j].face)
      if face_sat(overlap, nvars) &&
        !vec_approx_eq(s.branches[i].value, s.branches[j].value) {
        return false
      }
    }
  }
  true
}

///|
/// Equality of systems in the quotient: equality of symbolic normal forms
/// (BDD region partitions; see system_symbolic.mbt).
pub fn system_eq_mod(a : VecSystem, b : VecSystem, nvars : Int32) -> Bool {
  system_eq_mod_sym(a, b, nvars)
}

///|
/// Prune a system: drop unsatisfiable branches and branches subsumed by a
/// different branch carrying the same value.  The result is equal to the
/// input in the quotient (checked by `pruning_respects_quotient`).
pub fn prune_system(s : VecSystem, nvars : Int32) -> VecSystem {
  let out : Array[VecBranch] = []
  let k = s.branches.length()
  for i in 0..<k {
    let bi = s.branches[i]
    if face_unsat(bi.face, nvars) {
      continue
    }
    let mut subsumed = false
    for j in 0..<k {
      if i == j {
        continue
      }
      let bj = s.branches[j]
      if vec_approx_eq(bi.value, bj.value) && face_le(bi.face, bj.face, nvars) {
        // Keep one representative among mutually subsuming duplicates:
        // drop i only in favour of a strictly larger face, or an equal
        // face with smaller index.
        let strictly_larger = !face_le(bj.face, bi.face, nvars)
        if strictly_larger || j < i {
          subsumed = true
        }
      }
    }
    if !subsumed {
      out.push(bi)
    }
  }
  VecSystem::{ branches: out, }
}

///|
/// Pruning respects the quotient and is idempotent: prune(s) ≡ s and
/// prune(prune(s)) ≡ prune(s) with no more branches than s.
pub fn pruning_respects_quotient(s : VecSystem, nvars : Int32) -> Bool {
  let pruned = prune_system(s, nvars)
  let pruned_twice = prune_system(pruned, nvars)
  system_eq_mod(pruned, s, nvars) &&
  system_eq_mod(pruned_twice, pruned, nvars) &&
  pruned.branches.length() <= s.branches.length()
}

///|
/// Union of two systems: concatenate the prescriptions.
pub fn system_union(a : VecSystem, b : VecSystem) -> VecSystem {
  let out : Array[VecBranch] = []
  for i in 0..<a.branches.length() {
    out.push(a.branches[i])
  }
  for j in 0..<b.branches.length() {
    out.push(b.branches[j])
  }
  VecSystem::{ branches: out, }
}

///|
/// Quotient commutativity of union: [a ∪ b] = [b ∪ a] as quotient classes,
/// and indeed already after pruning.
pub fn union_commutes_mod(a : VecSystem, b : VecSystem, nvars : Int32) -> Bool {
  system_eq_mod(system_union(a, b), system_union(b, a), nvars) &&
  system_eq_mod(
    prune_system(system_union(a, b), nvars),
    prune_system(system_union(b, a), nvars),
    nvars,
  )
}

///|
/// Compatibility is a quotient notion: if a is compatible and a ≡ a′ with
/// a′ compatible, then for every other system b, a ∪ b is compatible iff
/// a′ ∪ b is — provided the values a′ prescribes are drawn from those of a
/// (true in particular for a′ = prune(a)).
pub fn compatibility_respects_quotient(
  a : VecSystem,
  b : VecSystem,
  nvars : Int32,
) -> Bool {
  let ap = prune_system(a, nvars)
  let bp = prune_system(b, nvars)
  system_compatible(system_union(a, b), nvars) ==
  system_compatible(system_union(ap, bp), nvars)
}

///|
/// Extend a compatible system by a value prescribed on the top face, when
/// it agrees with everything already prescribed.  Returns None exactly
/// when the extension would be incompatible — the obstruction is checked,
/// not assumed.
pub fn system_extend_top(
  s : VecSystem,
  value : CVec,
  nvars : Int32,
) -> VecSystem? {
  let extended = system_union(s, system_of([branch(FTop, value)]))
  if system_compatible(extended, nvars) {
    Some(extended)
  } else {
    None
  }
}
