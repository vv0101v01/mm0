///|
// Topos Pillar — Layer 1: General Sites, Sieves, Grothendieck Topologies,
// Multi-Morphism Presheaves, Limits/Colimits, and General Yoneda Lemma.
//
// Composition convention (shared with @sym.FinCat):
//   cat.comp[f * cat.nmor + g] = f ∘ g   (first g : W -> V, then f : V -> U)
//   defined iff cat.cod[g] == cat.dom[f].
// For a contravariant presheaf P : C^op -> FinSet:
//   P.res[f] : P(cod(f)) -> P(dom(f))
//   P.res[f ∘ g](x) = P.res[g](P.res[f](x)).

///|
/// A sieve S on an object `target` of `cat`: a canonical sorted list of
/// morphism indices `f` with `cod[f] == target`, closed under precomposition
/// `f ∈ S, cod[g] == dom[f]  ==>  f ∘ g ∈ S`.
pub(all) struct Sieve {
  target : Int32
  arrows : Array[Int32]
} derive(Debug, Eq)

///|
pub extend Sieve with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend Sieve with Eq::{not_equal, equal}

///|
/// Grothendieck topology J on a finite category: for each object `u`,
/// `covers[u]` holds the canonical sorted list of J-covering sieves on `u`.
pub(all) struct GrothendieckTopology {
  nobj : Int32
  covers : Array[Array[Sieve]]
} derive(Debug, Eq)

///|
pub extend GrothendieckTopology with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend GrothendieckTopology with Eq::{not_equal, equal}

///|
/// A Grothendieck site (C, J).
pub(all) struct Site {
  cat : @sym.FinCat
  topology : GrothendieckTopology
}

///|
/// A natural transformation α : dom_psh => cod_psh between presheaves on the
/// same category: `components[u][x]` is `α_u(x) ∈ cod_psh(u)`.
pub(all) struct PresheafHom {
  cat : @sym.FinCat
  dom_size : Array[Int32]
  cod_size : Array[Int32]
  components : Array[Array[Int32]]
}

///|
/// Object and morphism mapping of a slice category C / over_obj.
pub(all) struct SliceCategoryData {
  slice_cat : @sym.FinCat
  obj_arrow : Array[Int32]
  proj_obj : Array[Int32]
  proj_mor : Array[Int32]
}

///|
fn sort_unique_ints(xs : Array[Int32]) -> Array[Int32] {
  let tmp = xs.copy()
  let n = tmp.length()
  for i in 0..<n {
    for j in (i + 1)..<n {
      if tmp[j] < tmp[i] {
        let t = tmp[i]
        tmp[i] = tmp[j]
        tmp[j] = t
      }
    }
  }
  let out : Array[Int32] = []
  for x in tmp {
    if out.length() == 0 || out[out.length() - 1] != x {
      out.push(x)
    }
  }
  out
}

///|
fn sorted_contains(sorted : Array[Int32], x : Int32) -> Bool {
  let mut lo = 0
  let mut hi = sorted.length() - 1
  while lo <= hi {
    let mid = (lo + hi) / 2
    if sorted[mid] == x {
      return true
    } else if sorted[mid] < x {
      lo = mid + 1
    } else {
      hi = mid - 1
    }
  }
  false
}

///|
fn sieve_less(a : Sieve, b : Sieve) -> Bool {
  if a.target != b.target {
    return a.target < b.target
  }
  if a.arrows.length() != b.arrows.length() {
    return a.arrows.length() < b.arrows.length()
  }
  for i in 0..<a.arrows.length() {
    if a.arrows[i] != b.arrows[i] {
      return a.arrows[i] < b.arrows[i]
    }
  }
  false
}

///|
fn sort_unique_sieves(xs : Array[Sieve]) -> Array[Sieve] {
  let tmp = xs.copy()
  let n = tmp.length()
  for i in 0..<n {
    for j in (i + 1)..<n {
      if sieve_less(tmp[j], tmp[i]) {
        let t = tmp[i]
        tmp[i] = tmp[j]
        tmp[j] = t
      }
    }
  }
  let out : Array[Sieve] = []
  for s in tmp {
    if out.length() == 0 || out[out.length() - 1] != s {
      out.push(s)
    }
  }
  out
}

///|
/// Opposite category C^op: reverses domain/codomain and composition order.
pub fn cat_opposite(c : @sym.FinCat) -> @sym.FinCat {
  let comp = Array::make(c.nmor * c.nmor, -1)
  for f in 0..<c.nmor {
    for g in 0..<c.nmor {
      // In C^op, f ∘_op g = g ∘_C f (g : W ->_op V means g : V ->_C W).
      let gf = c.comp[g * c.nmor + f]
      if gf >= 0 {
        comp[f * c.nmor + g] = gf
      }
    }
  }
  {
    nobj: c.nobj,
    nmor: c.nmor,
    dom: c.cod.copy(),
    cod: c.dom.copy(),
    id: c.id.copy(),
    comp,
  }
}

///|
/// Check the right Ore condition on C: for every cospan f : V -> U and
/// g : W -> U, there exist W0 and a : W0 -> V, b : W0 -> W with f ∘ a = g ∘ b.
/// This is the exact necessary and sufficient condition for all non-empty
/// sieves on C to form a Grothendieck topology (the atomic topology).
pub fn cat_satisfies_right_ore(c : @sym.FinCat) -> Bool {
  guard @sym.is_category(c) else { return false }
  for f in 0..<c.nmor {
    for g in 0..<c.nmor {
      if c.cod[f] != c.cod[g] {
        continue
      }
      let mut ok = false
      for a in 0..<c.nmor {
        if c.cod[a] != c.dom[f] {
          continue
        }
        for b in 0..<c.nmor {
          if c.dom[b] == c.dom[a] &&
            c.cod[b] == c.dom[g] &&
            c.comp[f * c.nmor + a] == c.comp[g * c.nmor + b] &&
            c.comp[f * c.nmor + a] >= 0 {
            ok = true
            break
          }
        }
        if ok {
          break
        }
      }
      if !ok {
        return false
      }
    }
  }
  true
}

///|
/// Construct the slice category C / over_obj together with its forgetful
/// projection functor Π : C / over_obj -> C.
pub fn cat_slice(c : @sym.FinCat, over_obj : Int32) -> SliceCategoryData {
  guard over_obj >= 0 && over_obj < c.nobj else {
    abort("cat_slice: object out of range")
  }
  let obj_arrow : Array[Int32] = []
  let proj_obj : Array[Int32] = []
  for m in 0..<c.nmor {
    if c.cod[m] == over_obj {
      obj_arrow.push(m)
      proj_obj.push(c.dom[m])
    }
  }
  let nobj = obj_arrow.length()
  let dom : Array[Int32] = []
  let cod : Array[Int32] = []
  let proj_mor : Array[Int32] = []
  let id = Array::make(nobj, -1)
  for i in 0..<nobj {
    for j in 0..<nobj {
      let fi = obj_arrow[i]
      let fj = obj_arrow[j]
      for h in 0..<c.nmor {
        if c.dom[h] == c.dom[fi] &&
          c.cod[h] == c.dom[fj] &&
          c.comp[fj * c.nmor + h] == fi {
          let idx = dom.length()
          dom.push(i)
          cod.push(j)
          proj_mor.push(h)
          if i == j && h == c.id[c.dom[fi]] {
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
        let h_comp = c.comp[proj_mor[a] * c.nmor + proj_mor[b]]
        for k in 0..<nmor {
          if dom[k] == dom[b] && cod[k] == cod[a] && proj_mor[k] == h_comp {
            comp[a * nmor + b] = k
            break
          }
        }
      }
    }
  }
  {
    slice_cat: { nobj, nmor, dom, cod, id, comp, },
    obj_arrow,
    proj_obj,
    proj_mor,
  }
}

///|
/// Poset of non-empty opens in the 3-arc good cover of S^1:
///   objects 0,1,2 = pairwise intersections U01, U12, U20
///   objects 3,4,5 = arcs U0, U1, U2
///   object 6      = whole circle S^1 = U0 ∪ U1 ∪ U2.
pub fn cat_circle_open_poset() -> @sym.FinCat {
  @sym.cat_poset(7, [
    (0, 3),
    (0, 4),
    (1, 4),
    (1, 5),
    (2, 5),
    (2, 3),
    (3, 6),
    (4, 6),
    (5, 6),
  ])
}

///|
/// Empty sieve on `target`.
pub fn sieve_empty(target : Int32) -> Sieve {
  { target, arrows: [], }
}

///|
/// Maximal sieve M_target = { f ∈ Mor(C) | cod(f) == target }.
pub fn sieve_maximal(c : @sym.FinCat, target : Int32) -> Sieve {
  let arrows : Array[Int32] = []
  for m in 0..<c.nmor {
    if c.cod[m] == target {
      arrows.push(m)
    }
  }
  { target, arrows, }
}

///|
/// Generate the smallest sieve on `target` containing `generators` by closing
/// under precomposition `f ∘ g` for all composable `g`.
pub fn sieve_generate(
  c : @sym.FinCat,
  target : Int32,
  generators : Array[Int32],
) -> Sieve {
  let acc : Array[Int32] = []
  for f in generators {
    guard f >= 0 && f < c.nmor && c.cod[f] == target else {
      abort("sieve_generate: generator codomain mismatch")
    }
    for g in 0..<c.nmor {
      if c.cod[g] == c.dom[f] {
        let fg = c.comp[f * c.nmor + g]
        if fg >= 0 {
          acc.push(fg)
        }
      }
    }
  }
  { target, arrows: sort_unique_ints(acc), }
}

///|
/// Check whether `s` contains morphism index `m`.
pub fn sieve_contains(s : Sieve, m : Int32) -> Bool {
  sorted_contains(s.arrows, m)
}

///|
/// Verify right-ideal / sieve axioms on `c`.
pub fn sieve_is_valid(c : @sym.FinCat, s : Sieve) -> Bool {
  guard s.target >= 0 && s.target < c.nobj else { return false }
  let norm = sort_unique_ints(s.arrows)
  guard norm == s.arrows else { return false }
  for f in s.arrows {
    guard f >= 0 && f < c.nmor && c.cod[f] == s.target else { return false }
    for g in 0..<c.nmor {
      if c.cod[g] == c.dom[f] {
        let fg = c.comp[f * c.nmor + g]
        guard fg >= 0 && sieve_contains(s, fg) else { return false }
      }
    }
  }
  true
}

///|
/// Pullback sieve h*(S) = { g : W -> dom(h) | h ∘ g ∈ S } along h : V -> target.
pub fn sieve_pullback(c : @sym.FinCat, s : Sieve, h : Int32) -> Sieve {
  guard h >= 0 && h < c.nmor && c.cod[h] == s.target else {
    abort("sieve_pullback: arrow codomain mismatch")
  }
  let v = c.dom[h]
  let arrows : Array[Int32] = []
  for g in 0..<c.nmor {
    if c.cod[g] == v {
      let hg = c.comp[h * c.nmor + g]
      if hg >= 0 && sieve_contains(s, hg) {
        arrows.push(g)
      }
    }
  }
  { target: v, arrows, }
}

///|
/// Intersection S ∩ T of two sieves on the same target.
pub fn sieve_inter(s : Sieve, t : Sieve) -> Sieve {
  guard s.target == t.target else { abort("sieve_inter: target mismatch") }
  let arrows : Array[Int32] = []
  for f in s.arrows {
    if sieve_contains(t, f) {
      arrows.push(f)
    }
  }
  { target: s.target, arrows, }
}

///|
/// Union S ∪ T of two sieves on the same target.
pub fn sieve_union(s : Sieve, t : Sieve) -> Sieve {
  guard s.target == t.target else { abort("sieve_union: target mismatch") }
  let raw = s.arrows.copy()
  for f in t.arrows {
    raw.push(f)
  }
  { target: s.target, arrows: sort_unique_ints(raw), }
}

///|
/// Subset relation S ⊆ T between sieves on the same target.
pub fn sieve_subset(s : Sieve, t : Sieve) -> Bool {
  guard s.target == t.target else { return false }
  for f in s.arrows {
    if !sieve_contains(t, f) {
      return false
    }
  }
  true
}

///|
/// Heyting implication (S => T) on sieves at `target`:
///   f : V -> target belongs to (S => T)  iff  f*(S) ⊆ f*(T).
pub fn sieve_heyting_implies(c : @sym.FinCat, s : Sieve, t : Sieve) -> Sieve {
  guard s.target == t.target else {
    abort("sieve_heyting_implies: target mismatch")
  }
  let arrows : Array[Int32] = []
  for f in 0..<c.nmor {
    if c.cod[f] == s.target {
      let fs = sieve_pullback(c, s, f)
      let ft = sieve_pullback(c, t, f)
      if sieve_subset(fs, ft) {
        arrows.push(f)
      }
    }
  }
  { target: s.target, arrows, }
}

///|
/// Enumerate all sieves on `target` in `c` in canonical order.
pub fn all_sieves_on(c : @sym.FinCat, target : Int32) -> Array[Sieve] {
  let incoming : Array[Int32] = []
  for m in 0..<c.nmor {
    if c.cod[m] == target {
      incoming.push(m)
    }
  }
  // Precompute principal sieves generated by each single incoming arrow.
  let principal : Array[Sieve] = []
  for f in incoming {
    principal.push(sieve_generate(c, target, [f]))
  }
  // Close under finite unions starting from the empty sieve.
  let mut found : Array[Sieve] = [sieve_empty(target)]
  for p in principal {
    let next = found.copy()
    for s in found {
      next.push(sieve_union(s, p))
    }
    found = sort_unique_sieves(next)
  }
  found
}

///|
/// Check whether `s` is a J-covering sieve on `s.target`.
pub fn topology_covers(j : GrothendieckTopology, s : Sieve) -> Bool {
  guard s.target >= 0 && s.target < j.nobj else { return false }
  for cov in j.covers[s.target] {
    if cov == s {
      return true
    }
  }
  false
}

///|
/// Verify all three Grothendieck topology axioms on `(c, j)`:
///   1. Maximal sieve: M_u ∈ J(u) for every object u.
///   2. Stability: S ∈ J(u) and h : v -> u  ==>  h*(S) ∈ J(v).
///   3. Transitivity (local character): if S ∈ J(u) and R is any sieve on u
///      such that f*(R) ∈ J(dom(f)) for every f ∈ S, then R ∈ J(u).
pub fn topology_is_valid(c : @sym.FinCat, j : GrothendieckTopology) -> Bool {
  guard @sym.is_category(c) && j.nobj == c.nobj && j.covers.length() == c.nobj else {
    return false
  }
  for u in 0..<c.nobj {
    let norm = sort_unique_sieves(j.covers[u])
    guard norm == j.covers[u] else { return false }
    for s in j.covers[u] {
      guard s.target == u && sieve_is_valid(c, s) else { return false }
    }
    // Axiom 1: maximal sieve covers.
    guard topology_covers(j, sieve_maximal(c, u)) else { return false }
  }
  // Axiom 2: pullback stability.
  for u in 0..<c.nobj {
    for s in j.covers[u] {
      for h in 0..<c.nmor {
        if c.cod[h] == u {
          guard topology_covers(j, sieve_pullback(c, s, h)) else {
            return false
          }
        }
      }
    }
  }
  // Axiom 3: transitivity across all sieves R on each u.
  for u in 0..<c.nobj {
    let all_r = all_sieves_on(c, u)
    for s in j.covers[u] {
      for r in all_r {
        let mut locally_covers = true
        for f in s.arrows {
          if !topology_covers(j, sieve_pullback(c, r, f)) {
            locally_covers = false
            break
          }
        }
        if locally_covers && !topology_covers(j, r) {
          return false
        }
      }
    }
  }
  true
}

///|
/// Trivial (chaotic / presheaf) Grothendieck topology: only maximal sieves cover,
/// so Sh(C, J_triv) == PSh(C).
pub fn topology_trivial(c : @sym.FinCat) -> GrothendieckTopology {
  let covers : Array[Array[Sieve]] = []
  for u in 0..<c.nobj {
    covers.push([sieve_maximal(c, u)])
  }
  { nobj: c.nobj, covers, }
}

///|
/// Dense (¬¬ / double-negation) Grothendieck topology: a sieve S on u covers
/// iff for every h : v -> u, the pullback h*(S) is non-empty (equivalently
/// ¬¬S == M_u in Ω(u)). Its sheaf topos Sh_¬¬(C) is always Boolean!
pub fn topology_dense(c : @sym.FinCat) -> GrothendieckTopology {
  let covers : Array[Array[Sieve]] = []
  for u in 0..<c.nobj {
    let ku : Array[Sieve] = []
    for s in all_sieves_on(c, u) {
      let mut dense = true
      for h in 0..<c.nmor {
        if c.cod[h] == u && sieve_pullback(c, s, h).arrows.length() == 0 {
          dense = false
          break
        }
      }
      if dense {
        ku.push(s)
      }
    }
    covers.push(sort_unique_sieves(ku))
  }
  { nobj: c.nobj, covers, }
}

///|
/// Atomic Grothendieck topology (defined iff `c` satisfies the right Ore
/// condition): every non-empty sieve on u covers.
pub fn topology_atomic(c : @sym.FinCat) -> GrothendieckTopology? {
  if !cat_satisfies_right_ore(c) {
    return None
  }
  let covers : Array[Array[Sieve]] = []
  for u in 0..<c.nobj {
    let ku : Array[Sieve] = []
    for s in all_sieves_on(c, u) {
      if s.arrows.length() > 0 {
        ku.push(s)
      }
    }
    covers.push(sort_unique_sieves(ku))
  }
  Some({ nobj: c.nobj, covers, })
}

///|
/// Generate the smallest Grothendieck topology on `c` containing the given
/// seed covering families `(target, arrow_family)` by closing inductively under
/// maximal sieves, pullback stability, superset upward closure, and transitivity.
pub fn topology_from_coverage(
  c : @sym.FinCat,
  seed_families : Array[(Int32, Array[Int32])],
) -> GrothendieckTopology {
  let all_by_u : Array[Array[Sieve]] = []
  let covers : Array[Array[Sieve]] = []
  for u in 0..<c.nobj {
    all_by_u.push(all_sieves_on(c, u))
    covers.push([sieve_maximal(c, u)])
  }
  for pair in seed_families {
    let (u, gens) = pair
    let s = sieve_generate(c, u, gens)
    covers[u].push(s)
    covers[u] = sort_unique_sieves(covers[u])
  }
  let mut changed = true
  while changed {
    changed = false
    // Pullback closure.
    for u in 0..<c.nobj {
      let snapshot = covers[u].copy()
      for s in snapshot {
        for h in 0..<c.nmor {
          if c.cod[h] == u {
            let v = c.dom[h]
            let hs = sieve_pullback(c, s, h)
            let before = covers[v].length()
            covers[v].push(hs)
            covers[v] = sort_unique_sieves(covers[v])
            if covers[v].length() > before {
              changed = true
            }
          }
        }
      }
    }
    // Transitivity (which also implies superset closure).
    let cur : GrothendieckTopology = { nobj: c.nobj, covers: covers.copy(), }
    for u in 0..<c.nobj {
      for s in cur.covers[u] {
        for r in all_by_u[u] {
          if topology_covers(cur, r) {
            continue
          }
          let mut local_ok = true
          for f in s.arrows {
            if !topology_covers(cur, sieve_pullback(c, r, f)) {
              local_ok = false
              break
            }
          }
          if local_ok {
            covers[u].push(r)
            covers[u] = sort_unique_sieves(covers[u])
            changed = true
          }
        }
      }
    }
  }
  { nobj: c.nobj, covers, }
}

///|
/// Construct and validate a Site `(cat, topology)`.
pub fn site_new(cat : @sym.FinCat, topology : GrothendieckTopology) -> Site {
  guard topology_is_valid(cat, topology) else {
    abort("site_new: invalid Grothendieck topology")
  }
  { cat, topology, }
}

///|
/// Check whether `site` satisfies both category and Grothendieck topology laws.
pub fn site_is_valid(site : Site) -> Bool {
  topology_is_valid(site.cat, site.topology)
}

///|
/// Canonical open-cover site of S^1 on the 7-object circle poset:
///   - empty sieve does NOT cover any non-empty open;
///   - object 6 (S^1) is covered by {U0->S^1, U1->S^1, U2->S^1}.
pub fn site_circle_good_cover() -> Site {
  let c = cat_circle_open_poset()
  let gens : Array[Int32] = []
  for m in 0..<c.nmor {
    if c.cod[m] == 6 && (c.dom[m] == 3 || c.dom[m] == 4 || c.dom[m] == 5) {
      gens.push(m)
    }
  }
  site_new(c, topology_from_coverage(c, [(6, gens)]))
}

///|
/// Terminal presheaf `1` on `c` (`1(u) = {0}` for all `u`).
pub fn presheaf_terminal(c : @sym.FinCat) -> @sym.Presheaf {
  let size = Array::make(c.nobj, 1)
  let res : Array[Array[Int32]] = []
  for _ in 0..<c.nmor {
    res.push([0])
  }
  @sym.presheaf_new(c, size, res)
}

///|
/// Initial presheaf `0` on `c` (`0(u) = ∅` for all `u`).
pub fn presheaf_initial(c : @sym.FinCat) -> @sym.Presheaf {
  let size = Array::make(c.nobj, 0)
  let res : Array[Array[Int32]] = []
  for _ in 0..<c.nmor {
    res.push([])
  }
  @sym.presheaf_new(c, size, res)
}

///|
/// Constant presheaf Δ_raw(k) taking every object to `{0, ..., k - 1}` and
/// every restriction to the identity map (note: sheafification `sheafify`
/// turns this into the locally constant sheaf Δ(k) on any site!).
pub fn presheaf_constant_raw(c : @sym.FinCat, k : Int32) -> @sym.Presheaf {
  let size = Array::make(c.nobj, k)
  let id_k = Array::make(k, 0)
  for i in 0..<k {
    id_k[i] = i
  }
  let res : Array[Array[Int32]] = []
  for _ in 0..<c.nmor {
    res.push(id_k.copy())
  }
  @sym.presheaf_new(c, size, res)
}

///|
/// Representable presheaf `y(a) = Hom_C(-, a)` for ANY finite category `c`
/// (including non-thin groupoids BG and parallel-arrow categories!), together
/// with the morphism tables `hom_arrows[u][idx] = morphism_id`.
pub fn presheaf_representable_with_table(
  c : @sym.FinCat,
  a : Int32,
) -> (@sym.Presheaf, Array[Array[Int32]]) {
  guard a >= 0 && a < c.nobj else {
    abort("presheaf_representable_with_table: object out of range")
  }
  let hom_arrows : Array[Array[Int32]] = []
  let size = Array::make(c.nobj, 0)
  for u in 0..<c.nobj {
    let arr : Array[Int32] = []
    for m in 0..<c.nmor {
      if c.dom[m] == u && c.cod[m] == a {
        arr.push(m)
      }
    }
    size[u] = arr.length()
    hom_arrows.push(arr)
  }
  let res : Array[Array[Int32]] = []
  for f in 0..<c.nmor {
    // f : u -> v induces f* : Hom(v, a) -> Hom(u, a),  g |-> g ∘ f.
    let u = c.dom[f]
    let v = c.cod[f]
    let map_f = Array::make(size[v], 0)
    for idx_g in 0..<size[v] {
      let g = hom_arrows[v][idx_g]
      let gf = c.comp[g * c.nmor + f]
      let mut pos = -1
      for k in 0..<hom_arrows[u].length() {
        if hom_arrows[u][k] == gf {
          pos = k
          break
        }
      }
      guard pos >= 0 else { abort("presheaf_representable: composite missing") }
      map_f[idx_g] = pos
    }
    res.push(map_f)
  }
  (@sym.presheaf_new(c, size, res), hom_arrows)
}

///|
/// Representable presheaf `y(a) = Hom_C(-, a)`.
pub fn presheaf_representable(c : @sym.FinCat, a : Int32) -> @sym.Presheaf {
  let (p, _) = presheaf_representable_with_table(c, a)
  p
}

///|
/// Convert a Sieve `s` on `u` into its canonical subpresheaf `S ↪ y(u)`
/// together with its monomorphic inclusion `PresheafHom`.
pub fn presheaf_of_sieve(
  c : @sym.FinCat,
  s : Sieve,
) -> (@sym.Presheaf, PresheafHom) {
  let (yu, hom_arrows) = presheaf_representable_with_table(c, s.target)
  let sub_arrows : Array[Array[Int32]] = []
  let comps : Array[Array[Int32]] = []
  let size = Array::make(c.nobj, 0)
  for v in 0..<c.nobj {
    let sv : Array[Int32] = []
    let cv : Array[Int32] = []
    for idx in 0..<hom_arrows[v].length() {
      let m = hom_arrows[v][idx]
      if sieve_contains(s, m) {
        sv.push(m)
        cv.push(idx)
      }
    }
    size[v] = sv.length()
    sub_arrows.push(sv)
    comps.push(cv)
  }
  let res : Array[Array[Int32]] = []
  for f in 0..<c.nmor {
    let u = c.dom[f]
    let v = c.cod[f]
    let map_f = Array::make(size[v], 0)
    for i in 0..<size[v] {
      let y_idx = comps[v][i]
      let target_y = yu.res[f][y_idx]
      let target_m = hom_arrows[u][target_y]
      let mut pos = -1
      for k in 0..<sub_arrows[u].length() {
        if sub_arrows[u][k] == target_m {
          pos = k
          break
        }
      }
      guard pos >= 0 else { abort("presheaf_of_sieve: not closed under res") }
      map_f[i] = pos
    }
    res.push(map_f)
  }
  let p = @sym.presheaf_new(c, size, res)
  let mono : PresheafHom = {
    cat: c,
    dom_size: size,
    cod_size: yu.size,
    components: comps,
  }
  (p, mono)
}

///|
/// Binary product `P × Q` of presheaves (via `@sym.product_set`), with `π1, π2`.
pub fn presheaf_product(
  p : @sym.Presheaf,
  q : @sym.Presheaf,
) -> (@sym.Presheaf, PresheafHom, PresheafHom) {
  let c = p.cat
  let size = Array::make(c.nobj, 0)
  let pi1 : Array[Array[Int32]] = []
  let pi2 : Array[Array[Int32]] = []
  for u in 0..<c.nobj {
    let pairs = @sym.product_set(p.size[u], q.size[u])
    size[u] = pairs.length()
    let c1 : Array[Int32] = []
    let c2 : Array[Int32] = []
    for pair in pairs {
      let (x, y) = pair
      c1.push(x)
      c2.push(y)
    }
    pi1.push(c1)
    pi2.push(c2)
  }
  let res : Array[Array[Int32]] = []
  for f in 0..<c.nmor {
    let u = c.dom[f]
    let v = c.cod[f]
    let map_f = Array::make(size[v], 0)
    for x in 0..<p.size[v] {
      for y in 0..<q.size[v] {
        map_f[x * q.size[v] + y] = p.res[f][x] * q.size[u] + q.res[f][y]
      }
    }
    res.push(map_f)
  }
  (
    @sym.presheaf_new(c, size, res),
    { cat: c, dom_size: size, cod_size: p.size, components: pi1, },
    { cat: c, dom_size: size, cod_size: q.size, components: pi2, },
  )
}

///|
/// Binary coproduct `P + Q` (pointwise disjoint union) with injections `ι1, ι2`.
pub fn presheaf_coproduct(
  p : @sym.Presheaf,
  q : @sym.Presheaf,
) -> (@sym.Presheaf, PresheafHom, PresheafHom) {
  let c = p.cat
  let size = Array::make(c.nobj, 0)
  let in1 : Array[Array[Int32]] = []
  let in2 : Array[Array[Int32]] = []
  for u in 0..<c.nobj {
    size[u] = p.size[u] + q.size[u]
    let i1 = Array::make(p.size[u], 0)
    for x in 0..<p.size[u] {
      i1[x] = x
    }
    let i2 = Array::make(q.size[u], 0)
    for y in 0..<q.size[u] {
      i2[y] = p.size[u] + y
    }
    in1.push(i1)
    in2.push(i2)
  }
  let res : Array[Array[Int32]] = []
  for f in 0..<c.nmor {
    let u = c.dom[f]
    let v = c.cod[f]
    let map_f = Array::make(size[v], 0)
    for x in 0..<p.size[v] {
      map_f[x] = p.res[f][x]
    }
    for y in 0..<q.size[v] {
      map_f[p.size[v] + y] = p.size[u] + q.res[f][y]
    }
    res.push(map_f)
  }
  let coprod = @sym.presheaf_new(c, size, res)
  (
    coprod,
    { cat: c, dom_size: p.size, cod_size: size, components: in1, },
    { cat: c, dom_size: q.size, cod_size: size, components: in2, },
  )
}

///|
/// Categorical pullback `P ×_R Q` (delegating objectwise to `@sym.pullback_set`).
pub fn presheaf_pullback(
  p : @sym.Presheaf,
  q : @sym.Presheaf,
  alpha : PresheafHom,
  beta : PresheafHom,
) -> (@sym.Presheaf, PresheafHom, PresheafHom) {
  let c = p.cat
  let pairs_by_u : Array[Array[(Int32, Int32)]] = []
  let size = Array::make(c.nobj, 0)
  let p1 : Array[Array[Int32]] = []
  let p2 : Array[Array[Int32]] = []
  for u in 0..<c.nobj {
    let ps = @sym.pullback_set(
      @sym.FinMap::new(p.size[u], alpha.cod_size[u], alpha.components[u]),
      @sym.FinMap::new(q.size[u], beta.cod_size[u], beta.components[u]),
    )
    let c1 : Array[Int32] = []
    let c2 : Array[Int32] = []
    for pair in ps {
      let (x, y) = pair
      c1.push(x)
      c2.push(y)
    }
    size[u] = ps.length()
    pairs_by_u.push(ps)
    p1.push(c1)
    p2.push(c2)
  }
  let res : Array[Array[Int32]] = []
  for f in 0..<c.nmor {
    let u = c.dom[f]
    let v = c.cod[f]
    let map_f = Array::make(size[v], 0)
    for k in 0..<size[v] {
      let (x, y) = pairs_by_u[v][k]
      let target = (p.res[f][x], q.res[f][y])
      let mut pos = -1
      for idx in 0..<pairs_by_u[u].length() {
        if pairs_by_u[u][idx] == target {
          pos = idx
          break
        }
      }
      guard pos >= 0 else { abort("presheaf_pullback: naturality violated") }
      map_f[k] = pos
    }
    res.push(map_f)
  }
  (
    @sym.presheaf_new(c, size, res),
    { cat: c, dom_size: size, cod_size: p.size, components: p1, },
    { cat: c, dom_size: size, cod_size: q.size, components: p2, },
  )
}

///|
/// Equalizer `Eq(alpha, beta) ↪ P` (delegating objectwise to `@sym.equalizer_set`).
pub fn presheaf_equalizer(
  p : @sym.Presheaf,
  alpha : PresheafHom,
  beta : PresheafHom,
) -> (@sym.Presheaf, PresheafHom) {
  let c = p.cat
  let elems : Array[Array[Int32]] = []
  let size = Array::make(c.nobj, 0)
  for u in 0..<c.nobj {
    let eu = @sym.equalizer_set(
      @sym.FinMap::new(p.size[u], alpha.cod_size[u], alpha.components[u]),
      @sym.FinMap::new(p.size[u], beta.cod_size[u], beta.components[u]),
    )
    size[u] = eu.length()
    elems.push(eu)
  }
  let res : Array[Array[Int32]] = []
  for f in 0..<c.nmor {
    let u = c.dom[f]
    let v = c.cod[f]
    let map_f = Array::make(size[v], 0)
    for i in 0..<size[v] {
      let rx = p.res[f][elems[v][i]]
      let mut pos = -1
      for k in 0..<elems[u].length() {
        if elems[u][k] == rx {
          pos = k
          break
        }
      }
      guard pos >= 0 else { abort("presheaf_equalizer: naturality violated") }
      map_f[i] = pos
    }
    res.push(map_f)
  }
  (
    @sym.presheaf_new(c, size, res),
    { cat: c, dom_size: size, cod_size: p.size, components: elems, },
  )
}

///|
fn uf_new(n : Int32) -> Array[Int32] {
  let parent = Array::make(n, 0)
  for i in 0..<n {
    parent[i] = i
  }
  parent
}

///|
fn uf_find(par : Array[Int32], x0 : Int32) -> Int32 {
  let mut x = x0
  while par[x] != x {
    par[x] = par[par[x]]
    x = par[x]
  }
  x
}

///|
fn uf_union(par : Array[Int32], a : Int32, b : Int32) -> Unit {
  let ra = uf_find(par, a)
  let rb = uf_find(par, b)
  if ra < rb {
    par[rb] = ra
  } else if rb < ra {
    par[ra] = rb
  }
}

///|
/// Pointwise coequalizer `Q ->> Coeq(alpha, beta)` of `alpha, beta : P => Q`.
pub fn presheaf_coequalizer(
  p : @sym.Presheaf,
  q : @sym.Presheaf,
  alpha : PresheafHom,
  beta : PresheafHom,
) -> (@sym.Presheaf, PresheafHom) {
  let c = q.cat
  let quot_map : Array[Array[Int32]] = []
  let size = Array::make(c.nobj, 0)
  for u in 0..<c.nobj {
    let n = q.size[u]
    let parent = uf_new(n)
    for x in 0..<p.size[u] {
      uf_union(parent, alpha.components[u][x], beta.components[u][x])
    }
    let class_of = Array::make(n, -1)
    let mut cls = 0
    for y in 0..<n {
      let r = uf_find(parent, y)
      if class_of[r] < 0 {
        class_of[r] = cls
        cls = cls + 1
      }
      class_of[y] = class_of[r]
    }
    size[u] = cls
    quot_map.push(class_of)
  }
  let res : Array[Array[Int32]] = []
  for f in 0..<c.nmor {
    let u = c.dom[f]
    let v = c.cod[f]
    let map_f = Array::make(size[v], 0)
    for y in 0..<q.size[v] {
      let cv = quot_map[v][y]
      map_f[cv] = quot_map[u][q.res[f][y]]
    }
    res.push(map_f)
  }
  (
    @sym.presheaf_new(c, size, res),
    { cat: c, dom_size: q.size, cod_size: size, components: quot_map, },
  )
}

///|
/// Identity natural transformation `id_P : P => P`.
pub fn presheaf_hom_id(p : @sym.Presheaf) -> PresheafHom {
  let comps : Array[Array[Int32]] = []
  for u in 0..<p.cat.nobj {
    let arr = Array::make(p.size[u], 0)
    for x in 0..<p.size[u] {
      arr[x] = x
    }
    comps.push(arr)
  }
  {
    cat: p.cat,
    dom_size: p.size.copy(),
    cod_size: p.size.copy(),
    components: comps,
  }
}

///|
/// Composition `beta ∘ alpha : P => R` of `alpha : P => Q` and `beta : Q => R`.
pub fn presheaf_hom_compose(
  alpha : PresheafHom,
  beta : PresheafHom,
) -> PresheafHom {
  guard alpha.cod_size == beta.dom_size else {
    abort("presheaf_hom_compose: codomain/domain mismatch")
  }
  let comps : Array[Array[Int32]] = []
  for u in 0..<alpha.cat.nobj {
    let cu = Array::make(alpha.dom_size[u], 0)
    for x in 0..<alpha.dom_size[u] {
      cu[x] = beta.components[u][alpha.components[u][x]]
    }
    comps.push(cu)
  }
  {
    cat: alpha.cat,
    dom_size: alpha.dom_size.copy(),
    cod_size: beta.cod_size.copy(),
    components: comps,
  }
}

///|
/// Extensional equality of natural transformations `alpha == beta`.
pub fn presheaf_hom_eq(alpha : PresheafHom, beta : PresheafHom) -> Bool {
  alpha.dom_size == beta.dom_size &&
  alpha.cod_size == beta.cod_size &&
  alpha.components == beta.components
}

///|
/// Verify naturality of `alpha : p => q`:
///   for every f : u -> v and every x ∈ p(v), q.res[f](α_v(x)) == α_u(p.res[f](x)).
pub fn presheaf_hom_is_natural(
  p : @sym.Presheaf,
  q : @sym.Presheaf,
  alpha : PresheafHom,
) -> Bool {
  let c = p.cat
  guard alpha.components.length() == c.nobj &&
    alpha.dom_size == p.size &&
    alpha.cod_size == q.size else {
    return false
  }
  for u in 0..<c.nobj {
    guard alpha.components[u].length() == p.size[u] else { return false }
    for x in alpha.components[u] {
      guard x >= 0 && x < q.size[u] else { return false }
    }
  }
  for f in 0..<c.nmor {
    let u = c.dom[f]
    let v = c.cod[f]
    for x in 0..<p.size[v] {
      let lhs = q.res[f][alpha.components[v][x]]
      let rhs = alpha.components[u][p.res[f][x]]
      if lhs != rhs {
        return false
      }
    }
  }
  true
}

///|
/// Monomorphism check in PSh(C): delegates componentwise to `@sym.FinMap::is_mono`.
pub fn presheaf_hom_is_mono(alpha : PresheafHom) -> Bool {
  for u in 0..<alpha.cat.nobj {
    if !@sym.FinMap::new(
        alpha.dom_size[u],
        alpha.cod_size[u],
        alpha.components[u],
      ).is_mono() {
      return false
    }
  }
  true
}

///|
/// Epimorphism check in PSh(C): delegates componentwise to `@sym.FinMap::is_epi`.
pub fn presheaf_hom_is_epi_presheaf(alpha : PresheafHom) -> Bool {
  for u in 0..<alpha.cat.nobj {
    if !@sym.FinMap::new(
        alpha.dom_size[u],
        alpha.cod_size[u],
        alpha.components[u],
      ).is_epi() {
      return false
    }
  }
  true
}

///|
/// Isomorphism check in PSh(C) / Sh(C, J): delegates componentwise to `@sym.FinMap::is_iso`.
pub fn presheaf_hom_is_iso(alpha : PresheafHom) -> Bool {
  for u in 0..<alpha.cat.nobj {
    if !@sym.FinMap::new(
        alpha.dom_size[u],
        alpha.cod_size[u],
        alpha.components[u],
      ).is_iso() {
      return false
    }
  }
  true
}

///|
/// Enumerate all natural transformations `Hom_PSh(p, q)` using constraint
/// propagation along restriction morphisms (`α_u(p.res[f](x)) = q.res[f](α_v(x))`),
/// capped at `cap` morphisms.
pub fn presheaf_hom_enumerate(
  p : @sym.Presheaf,
  q : @sym.Presheaf,
  cap~ : Int32 = 4096,
) -> Array[PresheafHom] {
  let c = p.cat
  for u in 0..<c.nobj {
    if p.size[u] > 0 && q.size[u] == 0 {
      return []
    }
  }
  let vars : Array[(Int32, Int32)] = []
  let var_offset = Array::make(c.nobj, 0)
  for u in 0..<c.nobj {
    var_offset[u] = vars.length()
    for x in 0..<p.size[u] {
      vars.push((u, x))
    }
  }
  let nvars = vars.length()
  // Build forward & backward naturality constraint lists per variable.
  // Forward from (v, x): for f : u -> v, val(u, p.res[f][x]) == q.res[f][val(v, x)].
  let fwd_constraints : Array[Array[(Int32, Int32)]] = []
  let bwd_constraints : Array[Array[(Int32, Int32)]] = []
  for _ in 0..<nvars {
    fwd_constraints.push([])
    bwd_constraints.push([])
  }
  for f in 0..<c.nmor {
    let u = c.dom[f]
    let v = c.cod[f]
    for x in 0..<p.size[v] {
      let src_var = var_offset[v] + x
      let dst_var = var_offset[u] + p.res[f][x]
      if src_var != dst_var || f != c.id[v] {
        fwd_constraints[src_var].push((f, dst_var))
        bwd_constraints[dst_var].push((f, src_var))
      }
    }
  }
  let assign = Array::make(nvars, -1)
  let out : Array[PresheafHom] = []
  let trail : Array[Int32] = []
  fn propagate(from_var : Int32) -> Bool {
    let queue : Array[Int32] = [from_var]
    let mut head = 0
    while head < queue.length() {
      let cur = queue[head]
      head = head + 1
      let y_cur = assign[cur]
      for pair in fwd_constraints[cur] {
        let (f, dst) = pair
        let want = q.res[f][y_cur]
        if assign[dst] < 0 {
          assign[dst] = want
          trail.push(dst)
          queue.push(dst)
        } else if assign[dst] != want {
          return false
        }
      }
      for pair in bwd_constraints[cur] {
        let (f, src) = pair
        if assign[src] >= 0 && q.res[f][assign[src]] != y_cur {
          return false
        }
      }
    }
    true
  }
  fn search() -> Unit {
    if out.length() >= cap {
      return
    }
    // Pick first unassigned variable with highest forward out-degree.
    let mut best_v = -1
    let mut best_deg = -1
    for idx in 0..<nvars {
      if assign[idx] < 0 {
        let deg = fwd_constraints[idx].length()
        if deg > best_deg {
          best_deg = deg
          best_v = idx
        }
      }
    }
    if best_v < 0 {
      let comps : Array[Array[Int32]] = []
      for u in 0..<c.nobj {
        let cu = Array::make(p.size[u], 0)
        for x in 0..<p.size[u] {
          cu[x] = assign[var_offset[u] + x]
        }
        comps.push(cu)
      }
      out.push({
        cat: c,
        dom_size: p.size.copy(),
        cod_size: q.size.copy(),
        components: comps,
      })
      return
    }
    let (u, _) = vars[best_v]
    for val in 0..<q.size[u] {
      let mark = trail.length()
      assign[best_v] = val
      trail.push(best_v)
      if propagate(best_v) {
        search()
      }
      while trail.length() > mark {
        guard trail.pop() is Some(idx) else {
          abort("presheaf_hom_enumerate: empty trail")
        }
        assign[idx] = -1
      }
      if out.length() >= cap {
        return
      }
    }
  }
  search()
  out
}

///|
/// Decide whether two presheaves `p` and `q` on the same category are naturally
/// isomorphic (`∃ α : p => q` componentwise bijective).
pub fn presheaf_are_isomorphic(p : @sym.Presheaf, q : @sym.Presheaf) -> Bool {
  guard p.size == q.size else { return false }
  for alpha in presheaf_hom_enumerate(p, q, cap=2048) {
    if presheaf_hom_is_iso(alpha) {
      return true
    }
  }
  false
}

///|
/// General Yoneda forward bijection `p(a) -> Hom_PSh(y(a), p)`:
/// sends `elem ∈ p(a)` to `η_u(f : u -> a) = p.res[f](elem)`.
/// Works for ALL finite categories, including non-thin groupoids BG!
pub fn yoneda_elem_to_hom(
  p : @sym.Presheaf,
  a : Int32,
  elem : Int32,
) -> PresheafHom {
  let (ya, hom_arrows) = presheaf_representable_with_table(p.cat, a)
  guard elem >= 0 && elem < p.size[a] else {
    abort("yoneda_elem_to_hom: element out of range")
  }
  let comps : Array[Array[Int32]] = []
  for u in 0..<p.cat.nobj {
    let cu = Array::make(ya.size[u], 0)
    for k in 0..<ya.size[u] {
      let f = hom_arrows[u][k]
      cu[k] = p.res[f][elem]
    }
    comps.push(cu)
  }
  { cat: p.cat, dom_size: ya.size, cod_size: p.size.copy(), components: comps, }
}

///|
/// Theorem (General Multi-Morphism Yoneda Lemma):
/// Extends `@sym.yoneda_roundtrip` from thin categories to arbitrary finite
/// categories (including groupoids `BG` with parallel automorphisms), verifying
/// `p(a) ≅ Hom_PSh(y(a), p)` via evaluation at `id_a ∈ y(a)(a)`.
pub fn verify_general_yoneda_lemma(p : @sym.Presheaf) -> Bool {
  guard @sym.is_presheaf(p) else { return false }
  for a in 0..<p.cat.nobj {
    let (ya, hom_arrows) = presheaf_representable_with_table(p.cat, a)
    let id_a = p.cat.id[a]
    let mut id_pos = -1
    for k in 0..<hom_arrows[a].length() {
      if hom_arrows[a][k] == id_a {
        id_pos = k
        break
      }
    }
    if id_pos < 0 {
      return false
    }
    let homs = presheaf_hom_enumerate(ya, p, cap=4096)
    if homs.length() != p.size[a] {
      return false
    }
    for e in 0..<p.size[a] {
      let eta = yoneda_elem_to_hom(p, a, e)
      if !presheaf_hom_is_natural(ya, p, eta) || eta.components[a][id_pos] != e {
        return false
      }
    }
    for h in homs {
      let back = yoneda_elem_to_hom(p, a, h.components[a][id_pos])
      if !presheaf_hom_eq(h, back) {
        return false
      }
    }
  }
  true
}
