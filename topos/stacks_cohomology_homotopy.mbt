///|
// Topos Pillar — Layer 5: Groupoid Stacks & Effective Descent, Exact Rational
// Sheaf / Čech / Roos-Group Cohomology & Snake-Lemma Long Exact Sequences,
// and Simplicial Nerve Homotopy Types (π_0, π_1 Free Rank & Torsion, Betti).

///|
/// A finite groupoid: a category `cat` equipped with two-sided inverse arrows
/// `inv[m]` for every morphism `m`.
pub(all) struct FiniteGroupoid {
  cat : @sym.FinCat
  inv : Array[Int32]
}

///|
/// A cloven category fibered in groupoids `M : base^op -> Grpd`:
///   - `fibers[u]` is the fiber groupoid `M(u)` over `u ∈ base`;
///   - `pullbacks[f]` is the pullback functor `f^* : M(cod(f)) -> M(dom(f))`.
pub(all) struct GroupoidFibration {
  base : @sym.FinCat
  fibers : Array[FiniteGroupoid]
  pullbacks : Array[@sym.FinFunctor]
}

///|
/// Explicit overlap pullback diagram for a covering family `{ cover_arrows[i] : U_i -> target }`,
/// including pseudofunctorial cleavage coherence transitions
/// `cleavage_transitions[x][i * k + j] = θ_{f_i, p1}(x)^{-1} ∘ θ_{f_j, p2}(x)`
/// for each global object `x ∈ M(target)` (`empty` defaults to strict identity cleavage).
pub(all) struct CoverDescentDiagram {
  target : Int32
  cover_arrows : Array[Int32]
  overlap_obj : Array[Int32]
  proj1 : Array[Int32]
  proj2 : Array[Int32]
  triple_obj : Array[Int32]
  proj12 : Array[Int32]
  proj23 : Array[Int32]
  proj13 : Array[Int32]
  cleavage_transitions : Array[Array[Int32]]
}

///|
/// A descent datum `(x_i ∈ M(U_i), φ_{ij} : p2^*(x_j) -> p1^*(x_i) in M(U_{ij}))`.
pub(all) struct DescentDatum {
  local_objs : Array[Int32]
  transitions : Array[Int32]
} derive(Debug, Eq)

///|
pub extend DescentDatum with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend DescentDatum with Eq::{not_equal, equal}

///|
/// Rectangular exact rational matrix `nrows × ncols` for homological algebra.
pub(all) struct RectQMat {
  nrows : Int32
  ncols : Int32
  rows : Array[Array[@exactalg.Rat]]
} derive(Debug, Eq)

///|
pub extend RectQMat with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend RectQMat with Eq::{not_equal, equal}

///|
/// Exact rational cochain complex `C^0 ->^{d^0} C^1 ->^{d^1} ... -> C^m`.
pub(all) struct CochainComplexQ {
  dims : Array[Int32]
  differentials : Array[RectQMat]
}

///|
/// Presheaf of finite-dimensional Q-vector spaces on `cat`:
/// `res_mats[f]` has shape `dims[dom(f)] × dims[cod(f)]`.
pub(all) struct AbelianPresheafQ {
  cat : @sym.FinCat
  dims : Array[Int32]
  res_mats : Array[RectQMat]
}

///|
/// Abstract simplicial nerve up to dimension 3 (`vertices` = `0 ..< num_vertices`).
pub(all) struct SimplicialNerve {
  num_vertices : Int32
  edges : Array[(Int32, Int32)]
  triangles : Array[(Int32, Int32, Int32)]
  tetrahedra : Array[(Int32, Int32, Int32, Int32)]
}

///|
/// Extracted homotopy invariants of a site / cover nerve.
pub(all) struct HomotopyTypeSummary {
  pi0_components : Int32
  pi1_free_rank : Int32
  pi1_torsion_invariants : Array[Int32]
  betti_numbers : Array[Int32]
  euler_characteristic : Int32
} derive(Debug, Eq)

///|
pub extend HomotopyTypeSummary with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend HomotopyTypeSummary with Eq::{not_equal, equal}

///|
/// Verify groupoid laws on `g`.
pub fn is_valid_groupoid(g : FiniteGroupoid) -> Bool {
  let c = g.cat
  guard @sym.is_category(c) && g.inv.length() == c.nmor else { return false }
  for m in 0..<c.nmor {
    let im = g.inv[m]
    guard im >= 0 && im < c.nmor else { return false }
    guard c.dom[im] == c.cod[m] && c.cod[im] == c.dom[m] else { return false }
    guard c.comp[im * c.nmor + m] == c.id[c.dom[m]] &&
      c.comp[m * c.nmor + im] == c.id[c.cod[m]] else {
      return false
    }
  }
  true
}

///|
/// Convert any groupoid-shaped `FinCat` into a `FiniteGroupoid` by locating
/// unique inverses.
pub fn groupoid_of_fincat(c : @sym.FinCat) -> FiniteGroupoid? {
  if !@sym.is_category(c) {
    return None
  }
  let inv = Array::make(c.nmor, -1)
  for m in 0..<c.nmor {
    for k in 0..<c.nmor {
      if c.dom[k] == c.cod[m] &&
        c.cod[k] == c.dom[m] &&
        c.comp[k * c.nmor + m] == c.id[c.dom[m]] &&
        c.comp[m * c.nmor + k] == c.id[c.cod[m]] {
        inv[m] = k
        break
      }
    }
    if inv[m] < 0 {
      return None
    }
  }
  Some({ cat: c, inv, })
}

///|
/// Check the Grothendieck descent cocycle condition on `datum` over `diag`:
///   - `φ_{ij} : p2^*(x_j) -> p1^*(x_i)` in `M(U_{ij})`,
///   - `φ_{ii} == id` when `proj1 == proj2`,
///   - `p12^*(φ_{ij}) ∘ p23^*(φ_{jk}) == p13^*(φ_{ik})` on every non-empty `U_{ijk}`!
pub fn verify_descent_cocycle(
  fib : GroupoidFibration,
  diag : CoverDescentDiagram,
  datum : DescentDatum,
) -> Bool {
  let k = diag.cover_arrows.length()
  guard datum.local_objs.length() == k && datum.transitions.length() == k * k else {
    return false
  }
  for i in 0..<k {
    let ui = fib.base.dom[diag.cover_arrows[i]]
    if datum.local_objs[i] < 0 || datum.local_objs[i] >= fib.fibers[ui].cat.nobj {
      return false
    }
  }
  for i in 0..<k {
    for j in 0..<k {
      let uij = diag.overlap_obj[i * k + j]
      let p1 = diag.proj1[i * k + j]
      let p2 = diag.proj2[i * k + j]
      let g_ij = fib.fibers[uij].cat
      let phi_ij = datum.transitions[i * k + j]
      if phi_ij < 0 || phi_ij >= g_ij.nmor {
        return false
      }
      let want_dom = fib.pullbacks[p2].obj[datum.local_objs[j]]
      let want_cod = fib.pullbacks[p1].obj[datum.local_objs[i]]
      if g_ij.dom[phi_ij] != want_dom || g_ij.cod[phi_ij] != want_cod {
        return false
      }
      if i == j && p1 == p2 && phi_ij != g_ij.id[want_dom] {
        return false
      }
    }
  }
  for i in 0..<k {
    for j in 0..<k {
      for l in 0..<k {
        let idx3 = (i * k + j) * k + l
        let u_ijl = diag.triple_obj[idx3]
        if u_ijl < 0 {
          continue
        }
        let g3 = fib.fibers[u_ijl].cat
        let m12 = fib.pullbacks[diag.proj12[idx3]].mor[datum.transitions[i * k +
          j]]
        let m23 = fib.pullbacks[diag.proj23[idx3]].mor[datum.transitions[j * k +
          l]]
        let m13 = fib.pullbacks[diag.proj13[idx3]].mor[datum.transitions[i * k +
          l]]
        if g3.comp[m12 * g3.nmor + m23] != m13 {
          return false
        }
      }
    }
  }
  true
}

///|
/// Canonical descent datum induced by pulling back a global object `x ∈ M(target)`
/// along `diag.cover_arrows` together with its pseudofunctorial cleavage transitions.
pub fn canonical_descent_datum(
  fib : GroupoidFibration,
  diag : CoverDescentDiagram,
  global_obj : Int32,
) -> DescentDatum {
  let k = diag.cover_arrows.length()
  let local_objs = Array::make(k, 0)
  for i in 0..<k {
    local_objs[i] = fib.pullbacks[diag.cover_arrows[i]].obj[global_obj]
  }
  if global_obj >= 0 && global_obj < diag.cleavage_transitions.length() {
    return {
      local_objs,
      transitions: diag.cleavage_transitions[global_obj].copy(),
    }
  }
  let transitions = Array::make(k * k, 0)
  for i in 0..<k {
    for j in 0..<k {
      let uij = diag.overlap_obj[i * k + j]
      let p1 = diag.proj1[i * k + j]
      let pulled = fib.pullbacks[p1].obj[local_objs[i]]
      transitions[i * k + j] = fib.fibers[uij].cat.id[pulled]
    }
  }
  { local_objs, transitions, }
}

///|
/// Decide whether two descent data `d1, d2` over `diag` are isomorphic in the
/// descent category `Desc(diag, fib)`:
///   `∃ η_i : d1.x_i -> d2.x_i in M(U_i)` such that on every overlap `U_{ij}`,
///   `p1^*(η_i) ∘ d1.φ_{ij} == d2.φ_{ij} ∘ p2^*(η_j)`.
pub fn descent_data_isomorphic(
  fib : GroupoidFibration,
  diag : CoverDescentDiagram,
  d1 : DescentDatum,
  d2 : DescentDatum,
) -> Bool {
  let k = diag.cover_arrows.length()
  let candidates : Array[Array[Int32]] = []
  for i in 0..<k {
    let ui = fib.base.dom[diag.cover_arrows[i]]
    let gi = fib.fibers[ui].cat
    let arr : Array[Int32] = []
    for m in 0..<gi.nmor {
      if gi.dom[m] == d1.local_objs[i] && gi.cod[m] == d2.local_objs[i] {
        arr.push(m)
      }
    }
    if arr.length() == 0 {
      return false
    }
    candidates.push(arr)
  }
  let chosen = Array::make(k, 0)
  fn search(pos : Int32) -> Bool {
    if pos == k {
      for i in 0..<k {
        for j in 0..<k {
          let uij = diag.overlap_obj[i * k + j]
          let g_ij = fib.fibers[uij].cat
          let p1_eta_i = fib.pullbacks[diag.proj1[i * k + j]].mor[chosen[i]]
          let p2_eta_j = fib.pullbacks[diag.proj2[i * k + j]].mor[chosen[j]]
          let lhs = g_ij.comp[p1_eta_i * g_ij.nmor + d1.transitions[i * k + j]]
          let rhs = g_ij.comp[d2.transitions[i * k + j] * g_ij.nmor + p2_eta_j]
          if lhs != rhs {
            return false
          }
        }
      }
      return true
    }
    for m in candidates[pos] {
      chosen[pos] = m
      if search(pos + 1) {
        return true
      }
    }
    false
  }
  search(0)
}

///|
/// Enumerate all cocycle-valid descent data over `diag` (capped at `cap`) and
/// verify the **Stack Effective Descent Axiom**:
///   1. Every global object `x ∈ M(target)` has a valid canonical descent datum;
///   2. Prestack faithfulness/gluing on `Aut(x)` holds (`|Aut_M(target)(x)|`
///      matches the number of descent automorphisms of `can(x)`);
///   3. Every cocycle-valid descent datum is isomorphic in `Desc(diag, fib)` to
///      `canonical_descent_datum(x)` for a UNIQUE isomorphism class in `M(target)`!
pub fn verify_stack_effective_descent(
  fib : GroupoidFibration,
  diag : CoverDescentDiagram,
  cap~ : Int32 = 2048,
) -> Bool {
  let k = diag.cover_arrows.length()
  let g_target = fib.fibers[diag.target].cat
  // Collect global skeleton representatives of M(target).
  let global_reps : Array[Int32] = []
  for x in 0..<g_target.nobj {
    let mut iso_seen = false
    for r in global_reps {
      for m in 0..<g_target.nmor {
        if g_target.dom[m] == x && g_target.cod[m] == r {
          iso_seen = true
          break
        }
      }
      if iso_seen {
        break
      }
    }
    if !iso_seen {
      global_reps.push(x)
    }
  }
  // Check prestack automorphism sheaf condition on each global representative!
  for x in global_reps {
    let can_x = canonical_descent_datum(fib, diag, x)
    if !verify_descent_cocycle(fib, diag, can_x) {
      return false
    }
    let mut global_auts = 0
    for m in 0..<g_target.nmor {
      if g_target.dom[m] == x && g_target.cod[m] == x {
        global_auts = global_auts + 1
      }
    }
    // Count descent automorphisms (η_0, ..., η_{k-1}) of `can_x`.
    let local_auts : Array[Array[Int32]] = []
    for i in 0..<k {
      let ui = fib.base.dom[diag.cover_arrows[i]]
      let gi = fib.fibers[ui].cat
      let arr : Array[Int32] = []
      for m in 0..<gi.nmor {
        if gi.dom[m] == can_x.local_objs[i] && gi.cod[m] == can_x.local_objs[i] {
          arr.push(m)
        }
      }
      local_auts.push(arr)
    }
    let chosen = Array::make(k, 0)
    let mut desc_auts = 0
    fn count_auts(pos : Int32) -> Unit {
      if pos == k {
        let mut ok = true
        for i in 0..<k {
          for j in 0..<k {
            let uij = diag.overlap_obj[i * k + j]
            let g_ij = fib.fibers[uij].cat
            let lhs = g_ij.comp[fib.pullbacks[diag.proj1[i * k + j]].mor[chosen[i]] *
              g_ij.nmor +
              can_x.transitions[i * k + j]]
            let rhs = g_ij.comp[can_x.transitions[i * k + j] * g_ij.nmor +
              fib.pullbacks[diag.proj2[i * k + j]].mor[chosen[j]]]
            if lhs != rhs {
              ok = false
              break
            }
          }
          if !ok {
            break
          }
        }
        if ok {
          desc_auts = desc_auts + 1
        }
        return
      }
      for m in local_auts[pos] {
        chosen[pos] = m
        count_auts(pos + 1)
      }
    }
    count_auts(0)
    if global_auts != desc_auts {
      return false
    }
  }
  // Enumerate all cocycle-valid descent data and verify essential surjectivity +
  // full faithfulness on isomorphism classes!
  let valid_cocycles : Array[DescentDatum] = []
  let local_objs = Array::make(k, 0)
  let trans = Array::make(k * k, 0)
  fn enum_objs(i : Int32) -> Unit {
    if valid_cocycles.length() >= cap {
      return
    }
    if i == k {
      fn enum_trans(pos : Int32) -> Unit {
        if valid_cocycles.length() >= cap {
          return
        }
        if pos == k * k {
          let cand : DescentDatum = {
            local_objs: local_objs.copy(),
            transitions: trans.copy(),
          }
          if verify_descent_cocycle(fib, diag, cand) {
            valid_cocycles.push(cand)
          }
          return
        }
        let r = pos / k
        let c_idx = pos % k
        let uij = diag.overlap_obj[pos]
        let g_ij = fib.fibers[uij].cat
        let want_dom = fib.pullbacks[diag.proj2[pos]].obj[local_objs[c_idx]]
        let want_cod = fib.pullbacks[diag.proj1[pos]].obj[local_objs[r]]
        if r == c_idx && diag.proj1[pos] == diag.proj2[pos] {
          trans[pos] = g_ij.id[want_dom]
          enum_trans(pos + 1)
        } else {
          for m in 0..<g_ij.nmor {
            if g_ij.dom[m] == want_dom && g_ij.cod[m] == want_cod {
              trans[pos] = m
              enum_trans(pos + 1)
            }
          }
        }
      }
      enum_trans(0)
      return
    }
    let ui = fib.base.dom[diag.cover_arrows[i]]
    for x in 0..<fib.fibers[ui].cat.nobj {
      local_objs[i] = x
      enum_objs(i + 1)
    }
  }
  enum_objs(0)
  for d in valid_cocycles {
    let mut matches = 0
    for x in global_reps {
      if descent_data_isomorphic(
          fib,
          diag,
          d,
          canonical_descent_datum(fib, diag, x),
        ) {
        matches = matches + 1
      }
    }
    if matches != 1 {
      return false
    }
  }
  true
}

///|
/// Construct the classifying stack `B(Z/2Z)` of principal `Z/2Z`-bundles
/// (double covers) over the 3-arc circle poset `cat_circle_open_poset()`,
/// together with its `CoverDescentDiagram` over `S^1 = U0 ∪ U1 ∪ U2`.
/// When `include_mobius_bundle` is `true`, `M(S^1)` contains BOTH the trivial
/// double cover and the twisted Möbius/connected double cover (a genuine Stack!).
/// When `include_mobius_bundle` is `false`, `M(S^1)` contains ONLY the trivial
/// bundle — a Prestack whose `-1` holonomy cocycle fails effective descent!
pub fn build_circle_z2_torsor_stack(
  include_mobius_bundle : Bool,
) -> (GroupoidFibration, CoverDescentDiagram) {
  let base = cat_circle_open_poset()
  let z2_cat : @sym.FinCat = {
    nobj: 1,
    nmor: 2,
    dom: [0, 0],
    cod: [0, 0],
    id: [0],
    comp: [0, 1, 1, 0],
  }
  guard groupoid_of_fincat(z2_cat) is Some(z2_grpd) else {
    abort("circle_z2_torsor_stack: invalid Z/2Z groupoid")
  }
  // Two disjoint copies of BG = Z/2Z over S^1 when Mobius bundle is included:
  // objects 0 (trivial) and 1 (Mobius), each with {id, flip} automorphisms.
  let s1_grpd : FiniteGroupoid = if include_mobius_bundle {
    let s1_cat : @sym.FinCat = {
      nobj: 2,
      nmor: 4,
      dom: [0, 0, 1, 1],
      cod: [0, 0, 1, 1],
      id: [0, 2],
      comp: [0, 1, -1, -1, 1, 0, -1, -1, -1, -1, 2, 3, -1, -1, 3, 2],
    }
    guard groupoid_of_fincat(s1_cat) is Some(sg) else {
      abort("circle_z2_torsor_stack: invalid S^1 fiber groupoid")
    }
    sg
  } else {
    z2_grpd
  }
  let fibers : Array[FiniteGroupoid] = []
  for u in 0..<base.nobj {
    fibers.push(if u == 6 { s1_grpd } else { z2_grpd })
  }
  // Pseudofunctorial cleavage on the 3-arc open cover of S^1: local fibers over
  // contractible opens `u < 6` are `B(Z/2Z)`, while the twisted Möbius torsor
  // over `S^1` (`u = 6`) carries non-trivial `-1` cleavage transition holonomy
  // on `U_{02}` and `U_{20}`.
  let pullbacks : Array[@sym.FinFunctor] = []
  for m in 0..<base.nmor {
    let u = base.dom[m]
    let v = base.cod[m]
    if v == 6 && u < 6 && include_mobius_bundle {
      pullbacks.push({
        src: s1_grpd.cat,
        dst: z2_grpd.cat,
        obj: [0, 0],
        mor: [0, 1, 0, 1],
      })
    } else if v == 6 && u == 6 && include_mobius_bundle {
      pullbacks.push({
        src: s1_grpd.cat,
        dst: s1_grpd.cat,
        obj: [0, 1],
        mor: [0, 1, 2, 3],
      })
    } else {
      pullbacks.push({
        src: z2_grpd.cat,
        dst: z2_grpd.cat,
        obj: [0],
        mor: [0, 1],
      })
    }
  }
  // Find morphism indices in `base` for the 3-arc cover of 6.
  fn find_arrow(c : @sym.FinCat, a : Int32, b : Int32) -> Int32 {
    for m in 0..<c.nmor {
      if c.dom[m] == a && c.cod[m] == b {
        return m
      }
    }
    -1
  }
  let u_arcs = [3, 4, 5]
  let cover_arrows = [
    find_arrow(base, 3, 6),
    find_arrow(base, 4, 6),
    find_arrow(base, 5, 6),
  ]
  // Pairwise overlaps of [U0=3, U1=4, U2=5]:
  // (0,0)->3, (0,1)->0, (0,2)->2, (1,0)->0, (1,1)->4, (1,2)->1, (2,0)->2, (2,1)->1, (2,2)->5
  let overlap_obj = [3, 0, 2, 0, 4, 1, 2, 1, 5]
  let proj1 : Array[Int32] = []
  let proj2 : Array[Int32] = []
  for i in 0..<3 {
    for j in 0..<3 {
      let ov = overlap_obj[i * 3 + j]
      proj1.push(find_arrow(base, ov, u_arcs[i]))
      proj2.push(find_arrow(base, ov, u_arcs[j]))
    }
  }
  // Triple overlaps: only (i, i, i), (i, i, j), (i, j, i), (j, i, i) are non-empty;
  // (0, 1, 2) etc. have empty triple intersection (-1)!
  let triple_obj = Array::make(27, -1)
  let proj12 = Array::make(27, -1)
  let proj23 = Array::make(27, -1)
  let proj13 = Array::make(27, -1)
  for i in 0..<3 {
    for j in 0..<3 {
      for l in 0..<3 {
        let idx = (i * 3 + j) * 3 + l
        if i == j && j == l {
          let u_i = u_arcs[i]
          triple_obj[idx] = u_i
          proj12[idx] = find_arrow(base, u_i, u_i)
          proj23[idx] = find_arrow(base, u_i, u_i)
          proj13[idx] = find_arrow(base, u_i, u_i)
        } else if i == j {
          let ov = overlap_obj[j * 3 + l]
          triple_obj[idx] = ov
          proj12[idx] = find_arrow(base, ov, u_arcs[i])
          proj23[idx] = find_arrow(base, ov, ov)
          proj13[idx] = find_arrow(base, ov, ov)
        } else if j == l {
          let ov = overlap_obj[i * 3 + j]
          triple_obj[idx] = ov
          proj12[idx] = find_arrow(base, ov, ov)
          proj23[idx] = find_arrow(base, ov, u_arcs[j])
          proj13[idx] = find_arrow(base, ov, ov)
        } else if i == l {
          let ov = overlap_obj[i * 3 + j]
          triple_obj[idx] = ov
          proj12[idx] = find_arrow(base, ov, ov)
          proj23[idx] = find_arrow(base, ov, ov)
          proj13[idx] = find_arrow(base, ov, u_arcs[i])
        }
      }
    }
  }
  let cleavage_transitions : Array[Array[Int32]] = if include_mobius_bundle {
    // Object 0 (trivial cover): all +1 (morphism 0 in Z/2Z);
    // Object 1 (Mobius double cover): -1 (morphism 1 in Z/2Z) on U_{02} and U_{20}!
    [[0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 1, 0, 0]]
  } else {
    [[0, 0, 0, 0, 0, 0, 0, 0, 0]]
  }
  (
    { base, fibers, pullbacks, },
    {
      target: 6,
      cover_arrows,
      overlap_obj,
      proj1,
      proj2,
      triple_obj,
      proj12,
      proj23,
      proj13,
      cleavage_transitions,
    },
  )
}

///|
/// Construct the genuine twisted Möbius `Z/2Z`-torsor sheaf on `site_circle_good_cover()`:
/// locally isomorphic to `Z/2Z` of size 2 on every proper open `u < 6`, with a
/// swap monodromy on `U_{20} -> U_0`, and ZERO global sections on `S^1` (`u = 6`)!
pub fn circle_mobius_double_cover_sheaf() -> @sym.Presheaf {
  let c = cat_circle_open_poset()
  let size = [2, 2, 2, 2, 2, 2, 0]
  let res : Array[Array[Int32]] = []
  for m in 0..<c.nmor {
    let u = c.dom[m]
    let v = c.cod[m]
    if v == 6 {
      res.push([])
    } else if u == 2 && v == 3 {
      res.push([1, 0])
    } else {
      res.push([0, 1])
    }
  }
  @sym.presheaf_new(c, size, res)
}

///|
fn nerve_edge_index(nerve : SimplicialNerve, u : Int32, v : Int32) -> Int32 {
  for k in 0..<nerve.edges.length() {
    if nerve.edges[k] == (u, v) {
      return k
    }
  }
  abort("nerve_edge_index: missing boundary edge of simplex")
}

///|
fn nerve_tri_index(
  nerve : SimplicialNerve,
  u : Int32,
  v : Int32,
  w : Int32,
) -> Int32 {
  for k in 0..<nerve.triangles.length() {
    if nerve.triangles[k] == (u, v, w) {
      return k
    }
  }
  abort("nerve_tri_index: missing boundary triangle of simplex")
}

///|
/// General non-abelian Čech 1-cohomology `H^1(nerve, G)` of `G`-torsors over ANY
/// `SimplicialNerve` and ANY 1-object finite groupoid `group_cat = BG` (including
/// non-abelian groups such as `S_3`):
///   - `1`-cochains assign `g_e ∈ G` to each oriented edge `e = (u < v)` of `nerve`;
///   - `Z^1(nerve, G)` consists of assignments satisfying `g_{uv} · g_{vw} == g_{uw}`
///     on every 2-simplex `(u < v < w)` of `nerve`;
///   - Gauge coboundary action of `(h_0, ..., h_{n-1}) ∈ G^{num_vertices}` acts via
///     `g'_{uv} = h_u · g_{uv} · h_v^{-1}`.
/// Returns `(|Z^1(nerve, G)|, |H^1(nerve, G)|)`.
pub fn classify_group_torsor_cohomology(
  group_cat : @sym.FinCat,
  nerve : SimplicialNerve,
) -> (Int32, Int32) {
  let grpd = match groupoid_of_fincat(group_cat) {
    Some(g) => g
    None => abort("classify_group_torsor_cohomology: not a valid groupoid")
  }
  guard group_cat.nobj == 1 else {
    abort("classify_group_torsor_cohomology: expected 1-object groupoid BG")
  }
  let ng = group_cat.nmor
  let ne = nerve.edges.length()
  let nv = nerve.num_vertices
  let cocycles : Array[Array[Int32]] = []
  let cur = Array::make(ne, 0)
  fn enum_cocycles(pos : Int32) -> Unit {
    if pos == ne {
      for tri in nerve.triangles {
        let (u, v, w) = tri
        let g_uv = cur[nerve_edge_index(nerve, u, v)]
        let g_vw = cur[nerve_edge_index(nerve, v, w)]
        let g_uw = cur[nerve_edge_index(nerve, u, w)]
        if group_cat.comp[g_uv * ng + g_vw] != g_uw {
          return
        }
      }
      cocycles.push(cur.copy())
      return
    }
    for g in 0..<ng {
      cur[pos] = g
      enum_cocycles(pos + 1)
    }
  }
  enum_cocycles(0)
  // Partition `Z^1` under gauge equivalence `g'_{uv} = h_u · g_{uv} · h_v^{-1}`
  // (fixing `h_0 = id` on each connected component's root 0 to avoid redundant global inner automorphisms?
  // Wait: for non-abelian G, `h_0` acts by simultaneous conjugation on holonomies, so we MUST range over ALL `h ∈ G^nv`!).
  let visited = Array::make(cocycles.length(), false)
  let gauge = Array::make(nv, 0)
  let mut classes = 0
  for idx in 0..<cocycles.length() {
    if visited[idx] {
      continue
    }
    classes = classes + 1
    let base_c = cocycles[idx]
    fn sweep_gauge(v_pos : Int32) -> Unit {
      if v_pos == nv {
        let transformed = Array::make(ne, 0)
        for e_i in 0..<ne {
          let (u, v) = nerve.edges[e_i]
          let hu_g = group_cat.comp[gauge[u] * ng + base_c[e_i]]
          transformed[e_i] = group_cat.comp[hu_g * ng + grpd.inv[gauge[v]]]
        }
        for j in idx..<cocycles.length() {
          if !visited[j] && cocycles[j] == transformed {
            visited[j] = true
          }
        }
        return
      }
      for h in 0..<ng {
        gauge[v_pos] = h
        sweep_gauge(v_pos + 1)
      }
    }
    sweep_gauge(0)
  }
  (cocycles.length(), classes)
}

///|
/// Zero `nrows × ncols` exact rational matrix.
pub fn rect_qmat_zero(nrows : Int32, ncols : Int32) -> RectQMat {
  let rows : Array[Array[@exactalg.Rat]] = []
  for _ in 0..<nrows {
    rows.push(Array::make(ncols, @exactalg.rat_zero()))
  }
  { nrows, ncols, rows, }
}

///|
/// Identity `n × n` exact rational matrix.
pub fn rect_qmat_id(n : Int32) -> RectQMat {
  let m = rect_qmat_zero(n, n)
  for i in 0..<n {
    m.rows[i][i] = @exactalg.rat_one()
  }
  m
}

///|
/// Internal matrix helpers delegating directly to `@exactalg` (`algebra/qmat.mbt`).
fn rect_qmat_mul(a : RectQMat, b : RectQMat) -> RectQMat {
  guard a.ncols == b.nrows else { abort("rect_qmat_mul: dimension mismatch") }
  if a.nrows == 0 || b.ncols == 0 {
    return rect_qmat_zero(a.nrows, b.ncols)
  }
  if a.ncols == 0 {
    return rect_qmat_zero(a.nrows, b.ncols)
  }
  let prod = @exactalg.qmat_mul(
    @exactalg.qmat_from_rows(a.rows),
    @exactalg.qmat_from_rows(b.rows),
  )
  { nrows: a.nrows, ncols: b.ncols, rows: prod.rows, }
}

///|
fn rect_qmat_is_zero(a : RectQMat) -> Bool {
  for row in a.rows {
    if !@exactalg.qvec_is_zero(row) {
      return false
    }
  }
  true
}

///|
fn rect_qmat_rank(a : RectQMat) -> Int32 {
  if a.nrows == 0 || a.ncols == 0 {
    0
  } else {
    @exactalg.qrows_rank(a.rows, a.ncols)
  }
}

///|
fn rect_qmat_nullity(a : RectQMat) -> Int32 {
  a.ncols - rect_qmat_rank(a)
}

///|
fn rect_qmat_solve(
  a : RectQMat,
  rhs : Array[@exactalg.Rat],
) -> Array[@exactalg.Rat]? {
  guard rhs.length() == a.nrows else { abort("rect_qmat_solve: rhs length") }
  if a.ncols == 0 {
    return if @exactalg.qvec_is_zero(rhs) { Some([]) } else { None }
  }
  let aug : Array[Array[@exactalg.Rat]] = []
  for i in 0..<a.nrows {
    let row = a.rows[i].copy()
    row.push(rhs[i])
    aug.push(row)
  }
  let rref = @exactalg.qrows_rref(aug, a.ncols + 1)
  for p_col in rref.pivots {
    if p_col == a.ncols {
      return None
    }
  }
  let sol = @exactalg.qvec_zero(a.ncols)
  for r in 0..<rref.pivots.length() {
    sol[rref.pivots[r]] = rref.rows[r][a.ncols]
  }
  Some(sol)
}

///|
fn rect_qmat_vec(
  a : RectQMat,
  v : Array[@exactalg.Rat],
) -> Array[@exactalg.Rat] {
  guard v.length() == a.ncols else { abort("rect_qmat_vec: length mismatch") }
  @exactalg.qmat_vec(@exactalg.qmat_from_rows(a.rows), v)
}

///|
/// Verify cochain complex law `d^{k+1} ∘ d^k == 0` for all `k`.
pub fn cochain_complex_is_valid(cc : CochainComplexQ) -> Bool {
  guard cc.dims.length() == cc.differentials.length() + 1 else { return false }
  for k in 0..<cc.differentials.length() {
    let dk = cc.differentials[k]
    if dk.ncols != cc.dims[k] || dk.nrows != cc.dims[k + 1] {
      return false
    }
  }
  for k in 0..<(cc.differentials.length() - 1) {
    let comp = rect_qmat_mul(cc.differentials[k + 1], cc.differentials[k])
    if !rect_qmat_is_zero(comp) {
      return false
    }
  }
  true
}

///|
/// Compute exact cohomology dimensions `[dim H^0, dim H^1, ..., dim H^m]` of a
/// valid rational cochain complex `cc`.
pub fn cohomology_dimensions(cc : CochainComplexQ) -> Array[Int32] {
  guard cochain_complex_is_valid(cc) else {
    abort("cohomology_dimensions: d^{k+1} ∘ d^k != 0")
  }
  let m = cc.dims.length()
  let out = Array::make(m, 0)
  for k in 0..<m {
    let z_dim = if k < cc.differentials.length() {
      rect_qmat_nullity(cc.differentials[k])
    } else {
      cc.dims[k]
    }
    let b_dim = if k > 0 { rect_qmat_rank(cc.differentials[k - 1]) } else { 0 }
    out[k] = z_dim - b_dim
  }
  out
}

///|
/// Verify the **Euler–Poincaré Theorem**:
/// `Σ (-1)^k dim C^k == Σ (-1)^k dim H^k(C)`.
pub fn verify_euler_poincare(cc : CochainComplexQ) -> Bool {
  if !cochain_complex_is_valid(cc) {
    return false
  }
  let betti = cohomology_dimensions(cc)
  let mut lhs = 0
  let mut rhs = 0
  for k in 0..<cc.dims.length() {
    let sign = if k % 2 == 0 { 1 } else { -1 }
    lhs = lhs + sign * cc.dims[k]
    rhs = rhs + sign * betti[k]
  }
  lhs == rhs
}

///|
/// Constant Q-vector space presheaf `Q^d` on `cat`.
pub fn abelian_presheaf_constant_q(
  cat : @sym.FinCat,
  d : Int32,
) -> AbelianPresheafQ {
  let dims = Array::make(cat.nobj, d)
  let res_mats : Array[RectQMat] = []
  for _ in 0..<cat.nmor {
    res_mats.push(rect_qmat_id(d))
  }
  { cat, dims, res_mats, }
}

///|
/// Verify contravariant functoriality `R_{id} == I` and `R_{f ∘ g} == R_g * R_f`.
pub fn is_valid_abelian_presheaf(ap : AbelianPresheafQ) -> Bool {
  let c = ap.cat
  guard ap.dims.length() == c.nobj && ap.res_mats.length() == c.nmor else {
    return false
  }
  for u in 0..<c.nobj {
    if ap.res_mats[c.id[u]] != rect_qmat_id(ap.dims[u]) {
      return false
    }
  }
  for f in 0..<c.nmor {
    let rf = ap.res_mats[f]
    if rf.nrows != ap.dims[c.dom[f]] || rf.ncols != ap.dims[c.cod[f]] {
      return false
    }
    for g in 0..<c.nmor {
      let fg = c.comp[f * c.nmor + g]
      if fg >= 0 {
        if ap.res_mats[fg] != rect_qmat_mul(ap.res_mats[g], rf) {
          return false
        }
      }
    }
  }
  true
}

///|
/// Build the Roos / categorical nerve cosimplicial cochain complex
/// `C^0(cat, F) ->^{δ^0} C^1(cat, F) ->^{δ^1} C^2(cat, F)` computing the derived
/// global-section sheaf/presheaf cohomology `H^k(cat, F)` (including group
/// cohomology `H^k(G, V)` when `cat = BG`!):
///   - `C^0 = Π_{u_0} F(u_0)`
///   - `C^1 = Π_{f_1 : u_0 -> u_1} F(u_0)`,
///     `(δ^0 c)_{f_1} = F(f_1)(c_{u_1}) - c_{u_0}`
///   - `C^2 = Π_{u_0 ->^{f_1} u_1 ->^{f_2} u_2} F(u_0)`,
///     `(δ^1 c)_{(f_1, f_2)} = F(f_1)(c_{f_2}) - c_{f_2 ∘ f_1} + c_{f_1}`.
pub fn roos_site_cochain_complex(ap : AbelianPresheafQ) -> CochainComplexQ {
  let c = ap.cat
  // Offsets in C^0.
  let off0 = Array::make(c.nobj, 0)
  let mut dim0 = 0
  for u in 0..<c.nobj {
    off0[u] = dim0
    dim0 = dim0 + ap.dims[u]
  }
  // Offsets in C^1 indexed by morphism f_1.
  let off1 = Array::make(c.nmor, 0)
  let mut dim1 = 0
  for f1 in 0..<c.nmor {
    off1[f1] = dim1
    dim1 = dim1 + ap.dims[c.dom[f1]]
  }
  // 2-simplices: composable pairs (f_1 : u0 -> u1, f_2 : u1 -> u2).
  let pairs2 : Array[(Int32, Int32)] = []
  let off2 : Array[Int32] = []
  let mut dim2 = 0
  for f1 in 0..<c.nmor {
    for f2 in 0..<c.nmor {
      if c.cod[f1] == c.dom[f2] {
        pairs2.push((f1, f2))
        off2.push(dim2)
        dim2 = dim2 + ap.dims[c.dom[f1]]
      }
    }
  }
  let d0 = rect_qmat_zero(dim1, dim0)
  for f1 in 0..<c.nmor {
    let u0 = c.dom[f1]
    let u1 = c.cod[f1]
    let d_u0 = ap.dims[u0]
    let d_u1 = ap.dims[u1]
    let rf1 = ap.res_mats[f1]
    // + F(f1)(c_{u1})
    for r in 0..<d_u0 {
      for col in 0..<d_u1 {
        d0.rows[off1[f1] + r][off0[u1] + col] = @exactalg.rat_add(
          d0.rows[off1[f1] + r][off0[u1] + col],
          rf1.rows[r][col],
        )
      }
      // - c_{u0}
      d0.rows[off1[f1] + r][off0[u0] + r] = @exactalg.rat_sub(
        d0.rows[off1[f1] + r][off0[u0] + r],
        @exactalg.rat_one(),
      )
    }
  }
  let d1 = rect_qmat_zero(dim2, dim1)
  for idx in 0..<pairs2.length() {
    let (f1, f2) = pairs2[idx]
    let f21 = c.comp[f2 * c.nmor + f1]
    let u0 = c.dom[f1]
    let u1 = c.dom[f2]
    let d_u0 = ap.dims[u0]
    let d_u1 = ap.dims[u1]
    let rf1 = ap.res_mats[f1]
    // + F(f1)(c_{f2})
    for r in 0..<d_u0 {
      for col in 0..<d_u1 {
        d1.rows[off2[idx] + r][off1[f2] + col] = @exactalg.rat_add(
          d1.rows[off2[idx] + r][off1[f2] + col],
          rf1.rows[r][col],
        )
      }
      // - c_{f2 ∘ f1}
      d1.rows[off2[idx] + r][off1[f21] + r] = @exactalg.rat_sub(
        d1.rows[off2[idx] + r][off1[f21] + r],
        @exactalg.rat_one(),
      )
      // + c_{f1}
      d1.rows[off2[idx] + r][off1[f1] + r] = @exactalg.rat_add(
        d1.rows[off2[idx] + r][off1[f1] + r],
        @exactalg.rat_one(),
      )
    }
  }
  { dims: [dim0, dim1, dim2], differentials: [d0, d1], }
}

///|
/// Build the exact rational Čech / simplicial cochain complex
/// `C^0(N; Q) ->^{δ^0} C^1(N; Q) ->^{δ^1} C^2(N; Q) ->^{δ^2} C^3(N; Q)`
/// of an abstract `SimplicialNerve` (with canonical increasing vertex order on simplices).
pub fn nerve_constant_cochain_complex_q(
  nerve : SimplicialNerve,
) -> CochainComplexQ {
  let n0 = nerve.num_vertices
  let n1 = nerve.edges.length()
  let n2 = nerve.triangles.length()
  let n3 = nerve.tetrahedra.length()
  // (δ^0 f)(v0, v1) = f(v1) - f(v0)
  let d0 = rect_qmat_zero(n1, n0)
  for e in 0..<n1 {
    let (v0, v1) = nerve.edges[e]
    d0.rows[e][v1] = @exactalg.rat_one()
    d0.rows[e][v0] = @exactalg.rat_int(-1)
  }
  // (δ^1 c)(v0, v1, v2) = c(v1, v2) - c(v0, v2) + c(v0, v1)
  let d1 = rect_qmat_zero(n2, n1)
  for t in 0..<n2 {
    let (v0, v1, v2) = nerve.triangles[t]
    d1.rows[t][nerve_edge_index(nerve, v1, v2)] = @exactalg.rat_one()
    d1.rows[t][nerve_edge_index(nerve, v0, v2)] = @exactalg.rat_int(-1)
    d1.rows[t][nerve_edge_index(nerve, v0, v1)] = @exactalg.rat_one()
  }
  // (δ^2 c)(v0, v1, v2, v3) = c(v1,v2,v3) - c(v0,v2,v3) + c(v0,v1,v3) - c(v0,v1,v2)
  let d2 = rect_qmat_zero(n3, n2)
  for tet in 0..<n3 {
    let (v0, v1, v2, v3) = nerve.tetrahedra[tet]
    d2.rows[tet][nerve_tri_index(nerve, v1, v2, v3)] = @exactalg.rat_one()
    d2.rows[tet][nerve_tri_index(nerve, v0, v2, v3)] = @exactalg.rat_int(-1)
    d2.rows[tet][nerve_tri_index(nerve, v0, v1, v3)] = @exactalg.rat_one()
    d2.rows[tet][nerve_tri_index(nerve, v0, v1, v2)] = @exactalg.rat_int(-1)
  }
  { dims: [n0, n1, n2, n3], differentials: [d0, d1, d2], }
}

///|
/// Verify a Short Exact Sequence of cochain complexes
/// `0 -> A^• ->^{iota} B^• ->^{pi} C^• -> 0` and prove exactness of its induced
/// **Snake-Lemma Long Exact Sequence in Cohomology**
/// `0 -> H^0(A) -> H^0(B) -> H^0(C) ->^{∂^0} H^1(A) -> H^1(B) -> H^1(C) -> ...`
/// by explicitly constructing each connecting homomorphism `∂^k` via Gaussian
/// elimination diagram chase (`c ∈ Z^k(C)  <--π^k--  b ∈ B^k  --d_B^k-->  d_B(b) = ι^{k+1}(a)`).
pub fn verify_snake_lemma_cohomology_les(
  a_cc : CochainComplexQ,
  b_cc : CochainComplexQ,
  c_cc : CochainComplexQ,
  iota : Array[RectQMat],
  pi : Array[RectQMat],
) -> Bool {
  let m = a_cc.dims.length()
  guard cochain_complex_is_valid(a_cc) &&
    cochain_complex_is_valid(b_cc) &&
    cochain_complex_is_valid(c_cc) &&
    b_cc.dims.length() == m &&
    c_cc.dims.length() == m &&
    iota.length() == m &&
    pi.length() == m else {
    return false
  }
  // 1. Degreewise exactness of 0 -> A^k -> B^k -> C^k -> 0 and chain-map laws.
  for k in 0..<m {
    if iota[k].ncols != a_cc.dims[k] ||
      iota[k].nrows != b_cc.dims[k] ||
      pi[k].ncols != b_cc.dims[k] ||
      pi[k].nrows != c_cc.dims[k] {
      return false
    }
    if rect_qmat_rank(iota[k]) != a_cc.dims[k] ||
      rect_qmat_rank(pi[k]) != c_cc.dims[k] ||
      b_cc.dims[k] != a_cc.dims[k] + c_cc.dims[k] ||
      !rect_qmat_is_zero(rect_qmat_mul(pi[k], iota[k])) {
      return false
    }
    if k + 1 < m {
      if rect_qmat_mul(b_cc.differentials[k], iota[k]) !=
        rect_qmat_mul(iota[k + 1], a_cc.differentials[k]) {
        return false
      }
      if rect_qmat_mul(c_cc.differentials[k], pi[k]) !=
        rect_qmat_mul(pi[k + 1], b_cc.differentials[k]) {
        return false
      }
    }
  }
  // Helper: cocycle basis Z^k and coboundary basis B^k for any complex.
  fn cocycles_at(
    cc : CochainComplexQ,
    k : Int32,
  ) -> Array[Array[@exactalg.Rat]] {
    if cc.dims[k] == 0 {
      return []
    }
    if k < cc.differentials.length() {
      let dk = cc.differentials[k]
      if dk.nrows == 0 {
        return rect_qmat_id(cc.dims[k]).rows
      }
      @exactalg.qrows_nullspace(dk.rows, dk.ncols)
    } else {
      rect_qmat_id(cc.dims[k]).rows
    }
  }
  fn coboundaries_at(
    cc : CochainComplexQ,
    k : Int32,
  ) -> Array[Array[@exactalg.Rat]] {
    if k == 0 || cc.dims[k] == 0 || cc.dims[k - 1] == 0 {
      return []
    }
    let dm1 = cc.differentials[k - 1]
    // Columns of dm1 = rows of transpose!
    let cols : Array[Array[@exactalg.Rat]] = []
    for c_idx in 0..<dm1.ncols {
      let col = Array::make(dm1.nrows, @exactalg.rat_zero())
      for r in 0..<dm1.nrows {
        col[r] = dm1.rows[r][c_idx]
      }
      cols.push(col)
    }
    cols
  }
  // For a linear map `f : Z(X) -> Z(Y)` represented by `images` of `z_x` basis,
  // rank of induced map `H(X) -> H(Y)` equals `dim(im(f) + B(Y)) - dim(B(Y))`,
  // and nullity on `H(X)` equals `dim H(X) - rank_H(f)`!
  // In an exact sequence `H_prev ->^{f} H_mid ->^{g} H_next`, exactness at `H_mid`
  // holds iff `g ∘ f == 0` in cohomology (`im(f) ⊆ ker_H(g)`) AND
  // `rank_H(f) + rank_H(g) == dim H_mid`!
  let h_a = cohomology_dimensions(a_cc)
  let h_b = cohomology_dimensions(b_cc)
  let h_c = cohomology_dimensions(c_cc)
  let rank_iota_h = Array::make(m, 0)
  let rank_pi_h = Array::make(m, 0)
  let rank_delta_h = Array::make(if m > 0 { m - 1 } else { 0 }, 0)
  for k in 0..<m {
    let za = cocycles_at(a_cc, k)
    let zb = cocycles_at(b_cc, k)
    let zc = cocycles_at(c_cc, k)
    let bb = coboundaries_at(b_cc, k)
    let bc = coboundaries_at(c_cc, k)
    // Induced ι* : H^k(A) -> H^k(B)
    let im_iota = bb.copy()
    for v in za {
      im_iota.push(rect_qmat_vec(iota[k], v))
    }
    rank_iota_h[k] = @exactalg.qvec_rank(im_iota) - @exactalg.qvec_rank(bb)
    // Induced π* : H^k(B) -> H^k(C)
    let im_pi = bc.copy()
    for v in zb {
      im_pi.push(rect_qmat_vec(pi[k], v))
    }
    rank_pi_h[k] = @exactalg.qvec_rank(im_pi) - @exactalg.qvec_rank(bc)
    // Connecting homomorphism ∂^k : H^k(C) -> H^{k+1}(A) via Snake diagram chase!
    if k + 1 < m {
      let ba_next = coboundaries_at(a_cc, k + 1)
      let im_delta = ba_next.copy()
      for c_vec in zc {
        let b_lift = match rect_qmat_solve(pi[k], c_vec) {
          Some(sol) => sol
          None => return false
        }
        let db = rect_qmat_vec(b_cc.differentials[k], b_lift)
        let a_next = match rect_qmat_solve(iota[k + 1], db) {
          Some(sol) => sol
          None => return false
        }
        // Check `a_next` is genuinely a cocycle in `Z^{k+1}(A)`!
        if k + 1 < a_cc.differentials.length() {
          let da = rect_qmat_vec(a_cc.differentials[k + 1], a_next)
          if !@exactalg.qvec_is_zero(da) {
            return false
          }
        }
        im_delta.push(a_next)
      }
      rank_delta_h[k] = @exactalg.qvec_rank(im_delta) -
        @exactalg.qvec_rank(ba_next)
    }
  }
  // Verify exactness at EVERY node of the Long Exact Sequence!
  for k in 0..<m {
    // At H^k(A): incoming is ∂^{k-1} (or 0 when k == 0), outgoing is ι*^k.
    let in_a = if k == 0 { 0 } else { rank_delta_h[k - 1] }
    if in_a + rank_iota_h[k] != h_a[k] {
      return false
    }
    // At H^k(B): incoming is ι*^k, outgoing is π*^k.
    if rank_iota_h[k] + rank_pi_h[k] != h_b[k] {
      return false
    }
    // At H^k(C) (for k + 1 < m): incoming is π*^k, outgoing is ∂^k.
    if k + 1 < m {
      if rank_pi_h[k] + rank_delta_h[k] != h_c[k] {
        return false
      }
    } else if rank_pi_h[k] != h_c[k] {
      return false
    }
  }
  true
}

///|
/// Integer Smith-style invariant factor extraction for small integer boundary
/// matrices `∂_2 : Z^{|T|} -> Z^{|E|}` to detect abelianized `π_1` torsion
/// (e.g. `Z/2Z` on `RP^2`!).
fn integer_smith_torsion_factors(
  mat_in : Array[Array[Int32]],
  nrows : Int32,
  ncols : Int32,
) -> Array[Int32] {
  if nrows == 0 || ncols == 0 {
    return []
  }
  let m : Array[Array[Int32]] = []
  for r in 0..<nrows {
    m.push(mat_in[r].copy())
  }
  let mut r = 0
  let mut c = 0
  while r < nrows && c < ncols {
    // Find nonzero entry of smallest |val| in submatrix m[r.., c..].
    let mut changed = true
    while changed {
      changed = false
      let mut best_val = 0
      let mut br = -1
      let mut bc = -1
      for i in r..<nrows {
        for j in c..<ncols {
          let v = @exactalg.int_abs(m[i][j])
          if v > 0 && (br < 0 || v < best_val) {
            best_val = v
            br = i
            bc = j
          }
        }
      }
      if br < 0 {
        break
      }
      if br != r {
        let tmp = m[r]
        m[r] = m[br]
        m[br] = tmp
      }
      if bc != c {
        for i in 0..<nrows {
          let t = m[i][c]
          m[i][c] = m[i][bc]
          m[i][bc] = t
        }
      }
      if m[r][c] < 0 {
        for j in c..<ncols {
          m[r][j] = -m[r][j]
        }
      }
      let piv = m[r][c]
      // Eliminate column `c` below/above `r` and row `r` right of `c`.
      for i in (r + 1)..<nrows {
        if m[i][c] != 0 {
          let q = m[i][c] / piv
          for j in c..<ncols {
            m[i][j] = m[i][j] - q * m[r][j]
          }
          if m[i][c] != 0 {
            changed = true
          }
        }
      }
      for j in (c + 1)..<ncols {
        if m[r][j] != 0 {
          let q = m[r][j] / piv
          for i in r..<nrows {
            m[i][j] = m[i][j] - q * m[i][c]
          }
          if m[r][j] != 0 {
            changed = true
          }
        }
      }
      // Divisibility fixup if remainder submatrix has an entry not divisible by `piv`.
      if !changed {
        for i in (r + 1)..<nrows {
          for j in (c + 1)..<ncols {
            if m[i][j] % piv != 0 {
              for col in c..<ncols {
                m[r][col] = m[r][col] + m[i][col]
              }
              changed = true
              break
            }
          }
          if changed {
            break
          }
        }
      }
    }
    if m[r][c] == 0 {
      break
    }
    r = r + 1
    c = c + 1
  }
  let tors : Array[Int32] = []
  let diag_len = if nrows < ncols { nrows } else { ncols }
  for k in 0..<diag_len {
    let v = @exactalg.int_abs(m[k][k])
    if v > 1 {
      tors.push(v)
    }
  }
  tors
}

///|
/// Build the classifying nerve `B(C)` (up to dimension 3, of non-identity
/// composable chains for posets / acyclic categories) of a finite category `c`.
/// Computes a canonical Kahn topological ordering of the non-identity arrow DAG
/// so every non-identity morphism `u -> v` satisfies `rank[u] < rank[v]`
/// regardless of object numbering, preserving `B(C)` up to simplicial isomorphism!
pub fn classifying_nerve_of_poset(c : @sym.FinCat) -> SimplicialNerve {
  let n = c.nobj
  let adj = Array::make(n * n, false)
  let indeg = Array::make(n, 0)
  for m in 0..<c.nmor {
    let u = c.dom[m]
    let v = c.cod[m]
    if u != v && !adj[u * n + v] {
      adj[u * n + v] = true
      indeg[v] = indeg[v] + 1
    }
  }
  let placed = Array::make(n, false)
  let rank = Array::make(n, -1)
  for step in 0..<n {
    let mut pick = -1
    for u in 0..<n {
      if !placed[u] && indeg[u] == 0 {
        pick = u
        break
      }
    }
    guard pick >= 0 else {
      abort("classifying_nerve_of_poset: category has non-identity cycles")
    }
    placed[pick] = true
    rank[pick] = step
    for v in 0..<n {
      if adj[pick * n + v] {
        indeg[v] = indeg[v] - 1
      }
    }
  }
  let ranked_adj = Array::make(n * n, false)
  for u in 0..<n {
    for v in 0..<n {
      if adj[u * n + v] {
        ranked_adj[rank[u] * n + rank[v]] = true
      }
    }
  }
  let edges : Array[(Int32, Int32)] = []
  for i in 0..<n {
    for j in (i + 1)..<n {
      if ranked_adj[i * n + j] {
        edges.push((i, j))
      }
    }
  }
  let triangles : Array[(Int32, Int32, Int32)] = []
  for i in 0..<n {
    for j in (i + 1)..<n {
      if !ranked_adj[i * n + j] {
        continue
      }
      for k in (j + 1)..<n {
        if ranked_adj[j * n + k] && ranked_adj[i * n + k] {
          triangles.push((i, j, k))
        }
      }
    }
  }
  let tetrahedra : Array[(Int32, Int32, Int32, Int32)] = []
  for i in 0..<n {
    for j in (i + 1)..<n {
      if !ranked_adj[i * n + j] {
        continue
      }
      for k in (j + 1)..<n {
        if !ranked_adj[j * n + k] || !ranked_adj[i * n + k] {
          continue
        }
        for l in (k + 1)..<n {
          if ranked_adj[k * n + l] &&
            ranked_adj[j * n + l] &&
            ranked_adj[i * n + l] {
            tetrahedra.push((i, j, k, l))
          }
        }
      }
    }
  }
  { num_vertices: n, edges, triangles, tetrahedra, }
}

///|
/// Extract the **Homotopy Type Summary** (`π_0`, `π_1` free rank & torsion
/// invariant factors, rational Betti numbers `[b_0, b_1, b_2, b_3]`, and Euler
/// characteristic `χ`) of a `SimplicialNerve`!
pub fn compute_nerve_homotopy_type(
  nerve : SimplicialNerve,
) -> HomotopyTypeSummary {
  let cc = nerve_constant_cochain_complex_q(nerve)
  let betti = cohomology_dimensions(cc)
  // Connected components via shared Union-Find on edges.
  let n0 = nerve.num_vertices
  let parent = uf_new(n0)
  for e in nerve.edges {
    let (u, v) = e
    uf_union(parent, u, v)
  }
  let mut pi0 = 0
  for i in 0..<n0 {
    if uf_find(parent, i) == i {
      pi0 = pi0 + 1
    }
  }
  // Integer ∂_2 matrix (|edges| × |triangles|) for torsion invariant factors of H_1!
  let ne = nerve.edges.length()
  let nt = nerve.triangles.length()
  let d2_int : Array[Array[Int32]] = []
  for _ in 0..<ne {
    d2_int.push(Array::make(nt, 0))
  }
  for t in 0..<nt {
    let (v0, v1, v2) = nerve.triangles[t]
    for e_idx in 0..<ne {
      if nerve.edges[e_idx] == (v1, v2) {
        d2_int[e_idx][t] = d2_int[e_idx][t] + 1
      }
      if nerve.edges[e_idx] == (v0, v2) {
        d2_int[e_idx][t] = d2_int[e_idx][t] - 1
      }
      if nerve.edges[e_idx] == (v0, v1) {
        d2_int[e_idx][t] = d2_int[e_idx][t] + 1
      }
    }
  }
  let torsion = integer_smith_torsion_factors(d2_int, ne, nt)
  let euler = betti[0] - betti[1] + betti[2] - betti[3]
  {
    pi0_components: pi0,
    pi1_free_rank: betti[1],
    pi1_torsion_invariants: torsion,
    betti_numbers: betti,
    euler_characteristic: euler,
  }
}

///|
/// Boundary `∂Δ^{dim}` of the standard `dim`-simplex (`dim + 1` vertices, all
/// faces of dimension `< dim` present), giving the canonical good-cover Čech
/// nerve of the `(dim - 1)`-sphere `S^{dim - 1}`:
///   - `dim = 1` -> `S^0` (`b = [2, 0, 0, 0]`, `χ = 2`);
///   - `dim = 2` -> `S^1` (`b = [1, 1, 0, 0]`, `χ = 0`);
///   - `dim = 3` -> `S^2` (`b = [1, 0, 1, 0]`, `χ = 2`);
///   - `dim = 4` -> `S^3` (`b = [1, 0, 0, 1]`, `χ = 0`)!
pub fn boundary_simplex_nerve(dim : Int32) -> SimplicialNerve {
  guard dim >= 1 && dim <= 4 else {
    abort("boundary_simplex_nerve: supported for 1 <= dim <= 4")
  }
  let nv = dim + 1
  let edges : Array[(Int32, Int32)] = []
  let triangles : Array[(Int32, Int32, Int32)] = []
  let tetrahedra : Array[(Int32, Int32, Int32, Int32)] = []
  if dim >= 2 {
    for i in 0..<nv {
      for j in (i + 1)..<nv {
        edges.push((i, j))
      }
    }
  }
  if dim >= 3 {
    for i in 0..<nv {
      for j in (i + 1)..<nv {
        for k in (j + 1)..<nv {
          triangles.push((i, j, k))
        }
      }
    }
  }
  if dim >= 4 {
    for i in 0..<nv {
      for j in (i + 1)..<nv {
        for k in (j + 1)..<nv {
          for l in (k + 1)..<nv {
            tetrahedra.push((i, j, k, l))
          }
        }
      }
    }
  }
  { num_vertices: nv, edges, triangles, tetrahedra, }
}

///|
/// Classic 6-vertex, 15-edge, 10-triangle minimal simplicial triangulation of
/// the real projective plane `RP^2` (icosahedron quotient by antipodal action,
/// yielding `H_1(RP^2; Z) ≅ Z/2Z` torsion `[2]` while `H^*(RP^2; Q) ≅ Q[0]`!).
pub fn rp2_minimal_nerve() -> SimplicialNerve {
  let edges : Array[(Int32, Int32)] = []
  for i in 0..<6 {
    for j in (i + 1)..<6 {
      edges.push((i, j))
    }
  }
  {
    num_vertices: 6,
    edges,
    triangles: [
      (0, 1, 2),
      (0, 2, 3),
      (0, 3, 4),
      (0, 4, 5),
      (0, 1, 5),
      (1, 2, 4),
      (2, 3, 5),
      (1, 3, 4),
      (2, 4, 5),
      (1, 3, 5),
    ],
    tetrahedra: [],
  }
}
