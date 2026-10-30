///|
// Topos Pillar — Layer 4: Geometric & Kripke–Joyal Logic, Joyal–Reyes
// Canonical Geometric Normal Form, Syntactic Sites & Classifying Toposes B(T),
// Grothendieck Category-of-Elements Categorification, and Beck–Chevalley
// Dependent Quantifiers (Σ_f ⊣ f* ⊣ Π_f).

///|
/// First-order / geometric formula in de Bruijn-indexed context `x_0, ..., x_{n-1}`:
/// `GExists(body)` and `GForall(body)` bind variable `x_n` inside `body`.
pub(all) enum GeoFormula {
  GTrue
  GFalse
  GPred(Int32, Array[Int32])
  GEq(Int32, Int32)
  GAnd(GeoFormula, GeoFormula)
  GOr(Array[GeoFormula])
  GExists(GeoFormula)
  GImplies(GeoFormula, GeoFormula)
  GForall(GeoFormula)
} derive(Debug, Eq)

///|
pub extend GeoFormula with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend GeoFormula with Eq::{not_equal, equal}

///|
/// Atomic constraint in canonical Geometric DNF.
pub(all) enum GeoAtom {
  AtomPred(Int32, Array[Int32])
  AtomEq(Int32, Int32)
} derive(Debug, Eq)

///|
pub extend GeoAtom with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend GeoAtom with Eq::{not_equal, equal}

///|
/// One clause `∃ y_0 ... y_{num_exists - 1}. ∧_{a ∈ atoms} a` in canonical
/// Geometric Disjunctive-Existential Normal Form.
pub(all) struct GeoConjClause {
  num_exists : Int32
  atoms : Array[GeoAtom]
} derive(Debug, Eq)

///|
pub extend GeoConjClause with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend GeoConjClause with Eq::{not_equal, equal}

///|
/// Canonical Joyal–Reyes Geometric Normal Form `∨_{c ∈ clauses} c`.
pub(all) struct GeoNormalForm {
  free_arity : Int32
  clauses : Array[GeoConjClause]
} derive(Debug, Eq)

///|
pub extend GeoNormalForm with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend GeoNormalForm with Eq::{not_equal, equal}

///|
/// Geometric sequent `premise ⊢_{x_0,...,x_{arity-1}} conclusion`.
pub(all) struct GeoSequent {
  arity : Int32
  premise : GeoFormula
  conclusion : GeoFormula
} derive(Debug, Eq)

///|
pub extend GeoSequent with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend GeoSequent with Eq::{not_equal, equal}

///|
/// First-order geometric theory `(num_preds, pred_arities, axioms)`.
pub(all) struct GeometricTheory {
  pred_arities : Array[Int32]
  axioms : Array[GeoSequent]
}

///|
/// Sheaf structure `M` interpreting a signature in `Sh(site)`:
/// `relations[r][u]` lists tuples in `M(u)^{arity(r)}` belonging to `R_M(u)`.
pub(all) struct SheafStructure {
  carrier : @sym.Presheaf
  pred_arities : Array[Int32]
  relations : Array[Array[Array[Array[Int32]]]]
}

///|
/// Propositional geometric sequent `∧_{p ∈ premise_atoms} p  ⊢  ∨_{branch ∈ branches} ∧_{q ∈ branch} q`.
pub(all) struct PropGeoAxiom {
  premise_atoms : Array[Int32]
  branches : Array[Array[Int32]]
} derive(Debug, Eq)

///|
pub extend PropGeoAxiom with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend PropGeoAxiom with Eq::{not_equal, equal}

///|
/// Propositional geometric theory over `num_props` atomic propositions.
pub(all) struct PropGeoTheory {
  num_props : Int32
  axioms : Array[PropGeoAxiom]
}

///|
/// Classifying Topos `B(T) = Sh(C_T, J_T)` of a propositional geometric theory,
/// bundled with the syntactic Horn-closed theories at each site object and the
/// universal generic model `generic_prop_sheaves[i] ↪ 1`.
pub(all) struct ClassifyingToposData {
  theory : PropGeoTheory
  site : Site
  obj_theories : Array[Array[Int32]]
  generic_prop_sheaves : Array[@sym.Presheaf]
}

///|
fn shift_var_above(v : Int32, cutoff : Int32, delta : Int32) -> Int32 {
  if v >= cutoff {
    v + delta
  } else {
    v
  }
}

///|
fn shift_atom(a : GeoAtom, cutoff : Int32, delta : Int32) -> GeoAtom {
  match a {
    AtomPred(p, args) => {
      let out = Array::make(args.length(), 0)
      for i in 0..<args.length() {
        out[i] = shift_var_above(args[i], cutoff, delta)
      }
      AtomPred(p, out)
    }
    AtomEq(x, y) =>
      AtomEq(
        shift_var_above(x, cutoff, delta),
        shift_var_above(y, cutoff, delta),
      )
  }
}

///|
fn atom_less(a : GeoAtom, b : GeoAtom) -> Bool {
  match (a, b) {
    (AtomEq(x1, y1), AtomEq(x2, y2)) => if x1 != x2 { x1 < x2 } else { y1 < y2 }
    (AtomEq(_, _), AtomPred(_, _)) => true
    (AtomPred(_, _), AtomEq(_, _)) => false
    (AtomPred(p1, args1), AtomPred(p2, args2)) => {
      if p1 != p2 {
        return p1 < p2
      }
      if args1.length() != args2.length() {
        return args1.length() < args2.length()
      }
      for i in 0..<args1.length() {
        if args1[i] != args2[i] {
          return args1[i] < args2[i]
        }
      }
      false
    }
  }
}

///|
fn canonicalize_atoms(atoms : Array[GeoAtom]) -> Array[GeoAtom] {
  let norm : Array[GeoAtom] = []
  for a in atoms {
    match a {
      AtomEq(x, y) =>
        if x == y {
          continue
        } else if x < y {
          norm.push(AtomEq(x, y))
        } else {
          norm.push(AtomEq(y, x))
        }
      AtomPred(p, args) => norm.push(AtomPred(p, args.copy()))
    }
  }
  let n = norm.length()
  for i in 0..<n {
    for j in (i + 1)..<n {
      if atom_less(norm[j], norm[i]) {
        let t = norm[i]
        norm[i] = norm[j]
        norm[j] = t
      }
    }
  }
  let out : Array[GeoAtom] = []
  for a in norm {
    if out.length() == 0 || out[out.length() - 1] != a {
      out.push(a)
    }
  }
  out
}

///|
fn clause_less(c1 : GeoConjClause, c2 : GeoConjClause) -> Bool {
  if c1.num_exists != c2.num_exists {
    return c1.num_exists < c2.num_exists
  }
  if c1.atoms.length() != c2.atoms.length() {
    return c1.atoms.length() < c2.atoms.length()
  }
  for i in 0..<c1.atoms.length() {
    if c1.atoms[i] != c2.atoms[i] {
      return atom_less(c1.atoms[i], c2.atoms[i])
    }
  }
  false
}

///|
fn sort_unique_clauses(cs : Array[GeoConjClause]) -> Array[GeoConjClause] {
  let tmp : Array[GeoConjClause] = []
  for c in cs {
    tmp.push({ num_exists: c.num_exists, atoms: canonicalize_atoms(c.atoms), })
  }
  let n = tmp.length()
  for i in 0..<n {
    for j in (i + 1)..<n {
      if clause_less(tmp[j], tmp[i]) {
        let t = tmp[i]
        tmp[i] = tmp[j]
        tmp[j] = t
      }
    }
  }
  let out : Array[GeoConjClause] = []
  for c in tmp {
    if out.length() == 0 || out[out.length() - 1] != c {
      out.push(c)
    }
  }
  out
}

///|
/// Transform any geometric formula (built from `⊤, ⊥, Pred, =, ∧, ∨, ∃`) into
/// its canonical Joyal–Reyes Geometric Disjunctive-Existential Normal Form
/// `∨_i ∃ y_i. ∧_j atom_{i,j}` via Frobenius reciprocity and distributivity!
pub fn geometric_normal_form(
  arity : Int32,
  formula : GeoFormula,
) -> GeoNormalForm {
  match formula {
    GTrue => { free_arity: arity, clauses: [{ num_exists: 0, atoms: [], }], }
    GFalse => { free_arity: arity, clauses: [], }
    GPred(p, args) =>
      {
        free_arity: arity,
        clauses: [
          { num_exists: 0, atoms: canonicalize_atoms([AtomPred(p, args)]), },
        ],
      }
    GEq(x, y) =>
      {
        free_arity: arity,
        clauses: [{ num_exists: 0, atoms: canonicalize_atoms([AtomEq(x, y)]), }],
      }
    GOr(disjuncts) => {
      let all_c : Array[GeoConjClause] = []
      for d in disjuncts {
        let nf = geometric_normal_form(arity, d)
        for c in nf.clauses {
          all_c.push(c)
        }
      }
      { free_arity: arity, clauses: sort_unique_clauses(all_c), }
    }
    GExists(body) => {
      // Inner NF has free_arity = arity + 1; variable `arity` becomes the
      // outermost existential, with inner existentials at `arity + 1 ..`.
      let inner = geometric_normal_form(arity + 1, body)
      let lifted : Array[GeoConjClause] = []
      for c in inner.clauses {
        lifted.push({ num_exists: c.num_exists + 1, atoms: c.atoms, })
      }
      { free_arity: arity, clauses: sort_unique_clauses(lifted), }
    }
    GAnd(left, right) => {
      // Frobenius product of `(∃^{q1} A1) ∧ (∃^{q2} A2)`:
      //   free vars are `0 ..< arity`;
      //   A1's bound vars stay at `arity ..< arity + q1`;
      //   A2's bound vars `arity + k` shift by `+q1` to `arity + q1 + k`!
      let nf1 = geometric_normal_form(arity, left)
      let nf2 = geometric_normal_form(arity, right)
      let combined : Array[GeoConjClause] = []
      for c1 in nf1.clauses {
        for c2 in nf2.clauses {
          let merged = c1.atoms.copy()
          for a2 in c2.atoms {
            merged.push(shift_atom(a2, arity, c1.num_exists))
          }
          combined.push({
            num_exists: c1.num_exists + c2.num_exists,
            atoms: canonicalize_atoms(merged),
          })
        }
      }
      { free_arity: arity, clauses: sort_unique_clauses(combined), }
    }
    GImplies(_, _) | GForall(_) =>
      abort("geometric_normal_form: formula outside geometric fragment")
  }
}

///|
/// Reify a `GeoNormalForm` back into a `GeoFormula`.
pub fn geo_normal_form_to_formula(nf : GeoNormalForm) -> GeoFormula {
  if nf.clauses.length() == 0 {
    return GFalse
  }
  let disj : Array[GeoFormula] = []
  for c in nf.clauses {
    let mut body : GeoFormula = GTrue
    if c.atoms.length() > 0 {
      fn atom_to_formula(a : GeoAtom) -> GeoFormula {
        match a {
          AtomPred(p, args) => GPred(p, args.copy())
          AtomEq(x, y) => GEq(x, y)
        }
      }
      body = atom_to_formula(c.atoms[0])
      for i in 1..<c.atoms.length() {
        body = GAnd(body, atom_to_formula(c.atoms[i]))
      }
    }
    for _ in 0..<c.num_exists {
      body = GExists(body)
    }
    disj.push(body)
  }
  if disj.length() == 1 {
    disj[0]
  } else {
    GOr(disj)
  }
}

///|
fn tuple_in_list(list : Array[Array[Int32]], needle : Array[Int32]) -> Bool {
  for tup in list {
    if tup == needle {
      return true
    }
  }
  false
}

///|
fn restrict_env(
  carrier : @sym.Presheaf,
  f : Int32,
  env : Array[Int32],
) -> Array[Int32] {
  let out = Array::make(env.length(), 0)
  for i in 0..<env.length() {
    out[i] = carrier.res[f][env[i]]
  }
  out
}

///|
/// Kripke–Joyal Forcing Semantics `u ⊩_J formula(env)` in `Sh(site)`:
///   - Local truth on `⊥` checks `∅_u ∈ J(u)`;
///   - Atomic predicates & equality check J-local satisfaction;
///   - `∨` and `∃` force via J-covering sieves (genuine sheaf semantics, NOT
///     naive classical pointwise disjunction/existence!);
///   - `=>` and `∀` quantify universally over all morphisms `f : v -> u`.
pub fn kripke_joyal_forces(
  site : Site,
  model : SheafStructure,
  u : Int32,
  env : Array[Int32],
  formula : GeoFormula,
) -> Bool {
  let c = site.cat
  match formula {
    GTrue => true
    GFalse => topology_covers(site.topology, sieve_empty(u))
    GEq(i, j) => {
      let arrows : Array[Int32] = []
      for f in 0..<c.nmor {
        if c.cod[f] == u {
          if model.carrier.res[f][env[i]] == model.carrier.res[f][env[j]] {
            arrows.push(f)
          }
        }
      }
      topology_covers(site.topology, { target: u, arrows, })
    }
    GPred(r, vars) => {
      let arrows : Array[Int32] = []
      for f in 0..<c.nmor {
        if c.cod[f] == u {
          let v = c.dom[f]
          let tup = Array::make(vars.length(), 0)
          for k in 0..<vars.length() {
            tup[k] = model.carrier.res[f][env[vars[k]]]
          }
          if tuple_in_list(model.relations[r][v], tup) {
            arrows.push(f)
          }
        }
      }
      topology_covers(site.topology, { target: u, arrows, })
    }
    GAnd(a, b) =>
      kripke_joyal_forces(site, model, u, env, a) &&
      kripke_joyal_forces(site, model, u, env, b)
    GOr(disj) => {
      let arrows : Array[Int32] = []
      for f in 0..<c.nmor {
        if c.cod[f] == u {
          let v = c.dom[f]
          let env_v = restrict_env(model.carrier, f, env)
          let mut any_ok = false
          for d in disj {
            if kripke_joyal_forces(site, model, v, env_v, d) {
              any_ok = true
              break
            }
          }
          if any_ok {
            arrows.push(f)
          }
        }
      }
      topology_covers(site.topology, { target: u, arrows, })
    }
    GExists(body) => {
      let arrows : Array[Int32] = []
      for f in 0..<c.nmor {
        if c.cod[f] == u {
          let v = c.dom[f]
          let env_v = restrict_env(model.carrier, f, env)
          let mut witness_ok = false
          for b in 0..<model.carrier.size[v] {
            let ext = env_v.copy()
            ext.push(b)
            if kripke_joyal_forces(site, model, v, ext, body) {
              witness_ok = true
              break
            }
          }
          if witness_ok {
            arrows.push(f)
          }
        }
      }
      topology_covers(site.topology, { target: u, arrows, })
    }
    GImplies(a, b) => {
      for f in 0..<c.nmor {
        if c.cod[f] == u {
          let v = c.dom[f]
          let env_v = restrict_env(model.carrier, f, env)
          if kripke_joyal_forces(site, model, v, env_v, a) &&
            !kripke_joyal_forces(site, model, v, env_v, b) {
            return false
          }
        }
      }
      true
    }
    GForall(body) => {
      for f in 0..<c.nmor {
        if c.cod[f] == u {
          let v = c.dom[f]
          let env_v = restrict_env(model.carrier, f, env)
          for b in 0..<model.carrier.size[v] {
            let ext = env_v.copy()
            ext.push(b)
            if !kripke_joyal_forces(site, model, v, ext, body) {
              return false
            }
          }
        }
      }
      true
    }
  }
}

///|
fn enumerate_tuples(n : Int32, arity : Int32) -> Array[Array[Int32]] {
  if arity == 0 {
    return [[]]
  }
  if n == 0 {
    return []
  }
  let sub = enumerate_tuples(n, arity - 1)
  let out : Array[Array[Int32]] = []
  for prefix in sub {
    for x in 0..<n {
      let next = prefix.copy()
      next.push(x)
      out.push(next)
    }
  }
  out
}

///|
/// Decide whether `model` satisfies the sequent `premise ⊢_{arity} conclusion`
/// across all objects `u` and environments `env ∈ M(u)^{arity}`.
pub fn model_satisfies_sequent(
  site : Site,
  model : SheafStructure,
  seq : GeoSequent,
) -> Bool {
  for u in 0..<site.cat.nobj {
    for env in enumerate_tuples(model.carrier.size[u], seq.arity) {
      if kripke_joyal_forces(site, model, u, env, seq.premise) &&
        !kripke_joyal_forces(site, model, u, env, seq.conclusion) {
        return false
      }
    }
  }
  true
}

///|
/// Decide whether `model` satisfies every axiom of `theory` in `Sh(site)`.
pub fn model_satisfies_theory(
  site : Site,
  model : SheafStructure,
  theory : GeometricTheory,
) -> Bool {
  for ax in theory.axioms {
    if !model_satisfies_sequent(site, model, ax) {
      return false
    }
  }
  true
}

///|
/// Verify semantic soundness of `geometric_normal_form`: `formula` and its
/// reified canonical Geometric DNF force the exact same tuples at every stage `u`.
pub fn verify_geometric_normal_form_soundness(
  site : Site,
  model : SheafStructure,
  arity : Int32,
  formula : GeoFormula,
) -> Bool {
  let nf = geometric_normal_form(arity, formula)
  let reified = geo_normal_form_to_formula(nf)
  // Idempotence of canonicalization: normalizing the reified NF yields the exact same NF!
  if geometric_normal_form(arity, reified) != nf {
    return false
  }
  for u in 0..<site.cat.nobj {
    for env in enumerate_tuples(model.carrier.size[u], arity) {
      if kripke_joyal_forces(site, model, u, env, formula) !=
        kripke_joyal_forces(site, model, u, env, reified) {
        return false
      }
    }
  }
  true
}

///|
/// Close a subset `seed` of propositions under all definite Horn axioms
/// (`premise ⊢ single_branch`) of `theory`.
fn horn_closure(theory : PropGeoTheory, seed : Array[Int32]) -> Array[Int32] {
  let present = Array::make(theory.num_props, false)
  for p in seed {
    if p >= 0 && p < theory.num_props {
      present[p] = true
    }
  }
  let mut changed = true
  while changed {
    changed = false
    for ax in theory.axioms {
      if ax.branches.length() != 1 {
        continue
      }
      let mut prem_ok = true
      for p in ax.premise_atoms {
        if !present[p] {
          prem_ok = false
          break
        }
      }
      if prem_ok {
        for q in ax.branches[0] {
          if !present[q] {
            present[q] = true
            changed = true
          }
        }
      }
    }
  }
  let out : Array[Int32] = []
  for i in 0..<theory.num_props {
    if present[i] {
      out.push(i)
    }
  }
  out
}

///|
fn int_subset(sub : Array[Int32], sup : Array[Int32]) -> Bool {
  for x in sub {
    if !sorted_contains(sup, x) {
      return false
    }
  }
  true
}

///|
/// Build the **Classifying Topos `B(T) = Sh(C_T, J_T)`** of a propositional
/// geometric theory `T`:
///   - `C_T`: poset category of Horn-closed theories `S ⊆ {0..n-1}`, with a
///     morphism `S2 -> S1` iff `S1 ⊆ S2` (`∧ S2` entails `∧ S1`);
///   - `J_T`: Grothendieck topology generated by all disjunctive/falsehood
///     sequents `∧ A ⊢ ∨_k ∧ B_k`;
///   - `generic_prop_sheaves[i]`: universal generic model interpreting `p_i` as
///     the sheafified subterminal object `a(y(cl({i}))) ↪ 1`!
pub fn build_propositional_classifying_topos(
  theory : PropGeoTheory,
) -> ClassifyingToposData {
  guard theory.num_props >= 0 && theory.num_props <= 10 else {
    abort("build_propositional_classifying_topos: num_props out of range")
  }
  let obj_theories : Array[Array[Int32]] = []
  let total = int_pow_i32(2, theory.num_props)
  for mask in 0..<total {
    let subset : Array[Int32] = []
    for i in 0..<theory.num_props {
      if ((mask >> i) & 1) == 1 {
        subset.push(i)
      }
    }
    if horn_closure(theory, subset) == subset {
      obj_theories.push(subset)
    }
  }
  let nobj = obj_theories.length()
  let arrows : Array[(Int32, Int32)] = []
  for u in 0..<nobj {
    for v in 0..<nobj {
      // Morphism u -> v in syntactic category iff theory(v) ⊆ theory(u).
      if int_subset(obj_theories[v], obj_theories[u]) {
        arrows.push((u, v))
      }
    }
  }
  let cat = @sym.cat_poset(nobj, arrows)
  // Generate Grothendieck coverage from non-Horn axioms (m == 0 or m >= 2,
  // and also m == 1 which is already iso/id in C_T).
  let seed_families : Array[(Int32, Array[Int32])] = []
  for u in 0..<nobj {
    let s_u = obj_theories[u]
    for ax in theory.axioms {
      if !int_subset(ax.premise_atoms, s_u) {
        continue
      }
      let fam : Array[Int32] = []
      for branch in ax.branches {
        let merged = s_u.copy()
        for q in branch {
          merged.push(q)
        }
        let closed = horn_closure(theory, merged)
        let mut v_idx = -1
        for k in 0..<nobj {
          if obj_theories[k] == closed {
            v_idx = k
            break
          }
        }
        guard v_idx >= 0 else {
          abort("build_propositional_classifying_topos: closed theory missing")
        }
        for m in 0..<cat.nmor {
          if cat.dom[m] == v_idx && cat.cod[m] == u {
            fam.push(m)
            break
          }
        }
      }
      seed_families.push((u, fam))
    }
  }
  let site = site_new(cat, topology_from_coverage(cat, seed_families))
  // Generic model: prop `i` is interpreted as the J_T-sheaf of the sieve
  // `{ v -> root | i ∈ obj_theories[v] }` on the terminal object `root` (`cl(∅)`),
  // which as a subterminal sheaf has section `{0}` at `u` iff `{i}` is J_T-locally
  // in `obj_theories[u]`!
  let mut root_obj = -1
  let empty_cl = horn_closure(theory, [])
  for u in 0..<nobj {
    if obj_theories[u] == empty_cl {
      root_obj = u
      break
    }
  }
  guard root_obj >= 0 else {
    abort("build_propositional_classifying_topos: root object missing")
  }
  let generic_prop_sheaves : Array[@sym.Presheaf] = []
  for i in 0..<theory.num_props {
    let gen_arrows : Array[Int32] = []
    for m in 0..<cat.nmor {
      if cat.cod[m] == root_obj && sorted_contains(obj_theories[cat.dom[m]], i) {
        gen_arrows.push(m)
      }
    }
    let s_i = sieve_j_closure(site, sieve_generate(cat, root_obj, gen_arrows))
    let (raw_i, _) = presheaf_of_sieve(cat, s_i)
    generic_prop_sheaves.push(sheafify(site, raw_i).sheaf)
  }
  { theory, site, obj_theories, generic_prop_sheaves, }
}

///|
/// Enumerate all classical Set-models `v ∈ {false, true}^{num_props}` of `theory`.
pub fn enumerate_set_models_prop(theory : PropGeoTheory) -> Array[Array[Bool]] {
  let out : Array[Array[Bool]] = []
  let total = int_pow_i32(2, theory.num_props)
  for mask in 0..<total {
    let model = Array::make(theory.num_props, false)
    for i in 0..<theory.num_props {
      model[i] = ((mask >> i) & 1) == 1
    }
    let mut ok = true
    for ax in theory.axioms {
      let mut prem = true
      for p in ax.premise_atoms {
        if !model[p] {
          prem = false
          break
        }
      }
      if prem {
        let mut concl = false
        for br in ax.branches {
          let mut br_ok = true
          for q in br {
            if !model[q] {
              br_ok = false
              break
            }
          }
          if br_ok {
            concl = true
            break
          }
        }
        if !concl {
          ok = false
          break
        }
      }
    }
    if ok {
      out.push(model)
    }
  }
  out
}

///|
/// Theorem (Hakim–Makkai–Reyes Universal Property of the Classifying Topos):
///   1. The universal generic model inside `B(T)` satisfies every sequent of `T`
///      under Kripke–Joyal forcing;
///   2. Pulling back the generic model along Diaconescu points `p : Set -> B(T)`
///      establishes an **exact bijection** `Pt(B(T)) ≅ Mod_Set(T)`!
pub fn verify_classifying_topos_universal_property(
  ct : ClassifyingToposData,
) -> Bool {
  let site = ct.site
  let c = site.cat
  let n = ct.theory.num_props
  // Build first-order SheafStructure over carrier `1` (0-ary predicates!).
  let term = presheaf_terminal(c)
  let arities = Array::make(n, 0)
  let relations : Array[Array[Array[Array[Int32]]]] = []
  for i in 0..<n {
    let rel_i : Array[Array[Array[Int32]]] = []
    for u in 0..<c.nobj {
      if ct.generic_prop_sheaves[i].size[u] > 0 {
        rel_i.push([[]])
      } else {
        rel_i.push([])
      }
    }
    relations.push(rel_i)
  }
  let generic_struct : SheafStructure = {
    carrier: term,
    pred_arities: arities,
    relations,
  }
  // Translate every PropGeoAxiom to a 0-ary GeoSequent and check Kripke–Joyal!
  for ax in ct.theory.axioms {
    let mut prem : GeoFormula = GTrue
    for p in ax.premise_atoms {
      prem = GAnd(prem, GPred(p, []))
    }
    let disj : Array[GeoFormula] = []
    for br in ax.branches {
      let mut conj : GeoFormula = GTrue
      for q in br {
        conj = GAnd(conj, GPred(q, []))
      }
      disj.push(conj)
    }
    let concl = if disj.length() == 0 { GFalse } else { GOr(disj) }
    if !model_satisfies_sequent(site, generic_struct, {
        arity: 0,
        premise: prem,
        conclusion: concl,
      }) {
      return false
    }
  }
  // Check exact bijection `Pt(B(T)) -> Mod_Set(T)` via `p |-> [|p*(U_i)| == 1]`.
  let pts = enumerate_canonical_points(site)
  let set_models = enumerate_set_models_prop(ct.theory)
  if pts.length() != set_models.length() {
    return false
  }
  let pulled_models : Array[Array[Bool]] = []
  for pt in pts {
    let m = Array::make(n, false)
    for i in 0..<n {
      let st = point_stalk_cardinality(pt, ct.generic_prop_sheaves[i])
      if st != 0 && st != 1 {
        return false
      }
      m[i] = st == 1
    }
    // Must be a valid Set-model and pairwise distinct across points!
    let mut in_models = false
    for sm in set_models {
      if sm == m {
        in_models = true
        break
      }
    }
    if !in_models {
      return false
    }
    for prev in pulled_models {
      if prev == m {
        return false
      }
    }
    pulled_models.push(m)
  }
  true
}

///|
/// Categorification 1 — Grothendieck Category of Elements `∫_C P`:
///   - Objects are pairs `(u ∈ C, x ∈ P(u))`;
///   - A morphism `(u, x) -> (v, y)` is a morphism `f : u -> v` in `C` such
///     that `P.res[f](y) == x`;
///   - Returns `(elements_cat, discrete_fibration_functor)`.
pub fn category_of_elements(
  p : @sym.Presheaf,
) -> (@sym.FinCat, @sym.FinFunctor) {
  let c = p.cat
  let objs : Array[(Int32, Int32)] = []
  let proj_obj : Array[Int32] = []
  for u in 0..<c.nobj {
    for x in 0..<p.size[u] {
      objs.push((u, x))
      proj_obj.push(u)
    }
  }
  let nobj = objs.length()
  let dom : Array[Int32] = []
  let cod : Array[Int32] = []
  let proj_mor : Array[Int32] = []
  let id = Array::make(nobj, -1)
  for i in 0..<nobj {
    let (u, x) = objs[i]
    for j in 0..<nobj {
      let (v, y) = objs[j]
      for f in 0..<c.nmor {
        if c.dom[f] == u && c.cod[f] == v && p.res[f][y] == x {
          let idx = dom.length()
          dom.push(i)
          cod.push(j)
          proj_mor.push(f)
          if i == j && f == c.id[u] {
            id[i] = idx
          }
        }
      }
    }
  }
  let nmor = dom.length()
  let comp = Array::make(nmor * nmor, -1)
  for a in 0..<nmor {
    for b in 0..<nmor {
      if cod[b] == dom[a] {
        let fg = c.comp[proj_mor[a] * c.nmor + proj_mor[b]]
        for k in 0..<nmor {
          if dom[k] == dom[b] && cod[k] == cod[a] && proj_mor[k] == fg {
            comp[a * nmor + b] = k
            break
          }
        }
      }
    }
  }
  let el_cat : @sym.FinCat = { nobj, nmor, dom, cod, id, comp, }
  let fib : @sym.FinFunctor = {
    src: el_cat,
    dst: c,
    obj: proj_obj,
    mor: proj_mor,
  }
  (el_cat, fib)
}

///|
/// Theorem (Fundamental Slice Categorification `PSh(C)/P ≃ PSh(∫_C P)`):
///   1. `∫_C P` is a valid category and `π_P : ∫_C P -> C` is a discrete fibration
///      (for every `f : u -> v` and every `(v, y)`, there is a UNIQUE lift `(u, x) -> (v, y)`);
///   2. Subobjects of `P` in `PSh(C)` (`Hom_PSh(P, Ω_C)`) are in exact bijection
///      with subobjects of `1` in `PSh(∫_C P)` (`Hom_PSh(1_{∫P}, Ω_{∫P})`),
///      and `π_P^*` induces a left-exact geometric morphism `PSh(∫_C P) -> PSh(C)`.
pub fn verify_elements_slice_categorification(p : @sym.Presheaf) -> Bool {
  let c = p.cat
  let (el_cat, fib) = category_of_elements(p)
  if !@sym.is_category(el_cat) || !@sym.is_fin_functor(fib) {
    return false
  }
  // Check discrete fibration unique-lifting property.
  for j in 0..<el_cat.nobj {
    let v = fib.obj[j]
    for f in 0..<c.nmor {
      if c.cod[f] == v {
        let mut lifts = 0
        for m in 0..<el_cat.nmor {
          if el_cat.cod[m] == j && fib.mor[m] == f {
            lifts = lifts + 1
          }
        }
        if lifts != 1 {
          return false
        }
      }
    }
  }
  let omega_c = subobject_classifier_presheaf(c).omega
  let omega_el = subobject_classifier_presheaf(el_cat)
  let sub_p = presheaf_hom_enumerate(p, omega_c, cap=4096).length()
  let sub_one_el = presheaf_hom_enumerate(
    omega_el.terminal,
    omega_el.omega,
    cap=4096,
  ).length()
  sub_p == sub_one_el
}

///|
/// Subpresheaf represented as componentwise sorted element masks `sub[u] ⊆ {0..P(u)-1}`
/// closed under restriction `x ∈ sub[v] ==> P.res[f][x] ∈ sub[u]`.
pub(all) struct Subpresheaf {
  ambient : @sym.Presheaf
  members : Array[Array[Int32]]
}

///|
/// Check whether `sub` is closed under all restrictions of `sub.ambient`.
pub fn is_valid_subpresheaf(sub : Subpresheaf) -> Bool {
  let p = sub.ambient
  let c = p.cat
  guard sub.members.length() == c.nobj else { return false }
  for u in 0..<c.nobj {
    if sort_unique_ints(sub.members[u]) != sub.members[u] {
      return false
    }
    for x in sub.members[u] {
      if x < 0 || x >= p.size[u] {
        return false
      }
    }
  }
  for f in 0..<c.nmor {
    let u = c.dom[f]
    let v = c.cod[f]
    for x in sub.members[v] {
      if !sorted_contains(sub.members[u], p.res[f][x]) {
        return false
      }
    }
  }
  true
}

///|
/// Pullback `f^*(B) ⊆ X` of `B ⊆ Y` along `f : X => Y`.
pub fn subpresheaf_pullback(
  x_psh : @sym.Presheaf,
  f_hom : PresheafHom,
  b_sub : Subpresheaf,
) -> Subpresheaf {
  let members : Array[Array[Int32]] = []
  for u in 0..<x_psh.cat.nobj {
    let mu : Array[Int32] = []
    for x in 0..<x_psh.size[u] {
      if sorted_contains(b_sub.members[u], f_hom.components[u][x]) {
        mu.push(x)
      }
    }
    members.push(mu)
  }
  { ambient: x_psh, members, }
}

///|
/// Existential image `Σ_f(A) ⊆ Y` (left adjoint to `f*`) along `f : X => Y`:
///   `y ∈ (Σ_f A)(u)  iff  ∃ x ∈ A(u), f_u(x) == y`.
pub fn subpresheaf_exists(
  y_psh : @sym.Presheaf,
  f_hom : PresheafHom,
  a_sub : Subpresheaf,
) -> Subpresheaf {
  let members : Array[Array[Int32]] = []
  for u in 0..<y_psh.cat.nobj {
    let mu : Array[Int32] = []
    for x in a_sub.members[u] {
      mu.push(f_hom.components[u][x])
    }
    members.push(sort_unique_ints(mu))
  }
  { ambient: y_psh, members, }
}

///|
/// Universal image `Π_f(A) ⊆ Y` (right adjoint to `f*`) along `f : X => Y`:
///   `y ∈ (Π_f A)(u)  iff  ∀ h : v -> u in C, ∀ x ∈ X(v), f_v(x) == Y(h)(y) ==> x ∈ A(v)`.
pub fn subpresheaf_forall(
  x_psh : @sym.Presheaf,
  y_psh : @sym.Presheaf,
  f_hom : PresheafHom,
  a_sub : Subpresheaf,
) -> Subpresheaf {
  let c = y_psh.cat
  let members : Array[Array[Int32]] = []
  for u in 0..<c.nobj {
    let mu : Array[Int32] = []
    for y in 0..<y_psh.size[u] {
      let mut all_ok = true
      for h in 0..<c.nmor {
        if c.cod[h] == u {
          let v = c.dom[h]
          let yh = y_psh.res[h][y]
          for x in 0..<x_psh.size[v] {
            if f_hom.components[v][x] == yh &&
              !sorted_contains(a_sub.members[v], x) {
              all_ok = false
              break
            }
          }
          if !all_ok {
            break
          }
        }
      }
      if all_ok {
        mu.push(y)
      }
    }
    members.push(mu)
  }
  { ambient: y_psh, members, }
}

///|
fn subpresheaf_le(a : Subpresheaf, b : Subpresheaf) -> Bool {
  for u in 0..<a.members.length() {
    if !int_subset(a.members[u], b.members[u]) {
      return false
    }
  }
  true
}

///|
/// Theorem (Categorified Dependent Quantifiers `Σ_f ⊣ f* ⊣ Π_f` & Beck–Chevalley):
/// Given `f : X => Z` and `g : Y => Z` with pullback `P = Y ×_Z X` (`p1 : P => Y`,
/// `p2 : P => X`), verifies:
///   1. Adjointness `Σ_f(A) <= B  <==>  A <= f*(B)` and `f*(B) <= A  <==>  B <= Π_f(A)`;
///   2. **Beck–Chevalley Law**: `Σ_{p1}(p2*(A)) == g*(Σ_f(A))` AND
///      `Π_{p1}(p2*(A)) == g*(Π_f(A))`!
pub fn verify_beck_chevalley_quantifiers(
  x_psh : @sym.Presheaf,
  y_psh : @sym.Presheaf,
  z_psh : @sym.Presheaf,
  f_hom : PresheafHom,
  g_hom : PresheafHom,
  a_sub : Subpresheaf,
  b_sub : Subpresheaf,
) -> Bool {
  guard is_valid_subpresheaf(a_sub) && is_valid_subpresheaf(b_sub) else {
    return false
  }
  let sig_a = subpresheaf_exists(z_psh, f_hom, a_sub)
  let pi_a = subpresheaf_forall(x_psh, z_psh, f_hom, a_sub)
  let fb = subpresheaf_pullback(x_psh, f_hom, b_sub)
  if !is_valid_subpresheaf(sig_a) ||
    !is_valid_subpresheaf(pi_a) ||
    !is_valid_subpresheaf(fb) {
    return false
  }
  if subpresheaf_le(sig_a, b_sub) != subpresheaf_le(a_sub, fb) {
    return false
  }
  if subpresheaf_le(fb, a_sub) != subpresheaf_le(b_sub, pi_a) {
    return false
  }
  let (pb, p1, p2) = presheaf_pullback(y_psh, x_psh, g_hom, f_hom)
  let p2_a = subpresheaf_pullback(pb, p2, a_sub)
  let lhs_exists = subpresheaf_exists(y_psh, p1, p2_a)
  let rhs_exists = subpresheaf_pullback(y_psh, g_hom, sig_a)
  let lhs_forall = subpresheaf_forall(pb, y_psh, p1, p2_a)
  let rhs_forall = subpresheaf_pullback(y_psh, g_hom, pi_a)
  lhs_exists.members == rhs_exists.members &&
  lhs_forall.members == rhs_forall.members
}
