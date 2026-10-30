///|
// Topos Pillar — Round 2 Structural Derivations (第 2 輪數學結構導出演算法與定理):
//   1. Right Kan Extension Presheaf `Ran_{u^{op}}` (`@sym.ran`) & Essential
//      Geometric Morphism Triple Adjunction (`Lan_{u^{op}} ⊣ u^* ⊣ Ran_{u^{op}}`)
//   2. Co-Heyting Subtopos Nucleus Calculus: Open `j_o(U)` & Closed `j_c(U)`
//      Lawvere–Tierney Modalities & Grothendieck–Johnstone Complementarity
//   3. Grothendieck–Verdier Comparison Lemma (Dense Subsite Morita Equivalence)
//   4. Diaconescu Internal `G`-Torsor Sheaves & Shear Isomorphism Theorem
//   5. Alexander–Whitney Simplicial Cup-Product DG-Algebra (`H^1 ⌣ H^1 -> H^2`,
//      distinguishing `T^2` from `S^1 ∨ S^1 ∨ S^2` at identical Betti numbers!)

///|
/// Report of Open/Closed Subtopos Nucleus Complementarity for a subterminal
/// truth value `U ↪ 1` (closed sieve on terminal / global section of `Ω`).
pub(all) struct SubtoposComplementReport {
  open_lt_valid : Bool
  closed_lt_valid : Bool
  meet_is_ambient : Bool
  join_is_inconsistent : Bool
  internal_lem_holds : Bool
  subtopos_boolean_complement_holds : Bool
} derive(Debug, Eq)

///|
pub extend SubtoposComplementReport with @moonbitlang/core/debug.Debug::{
  to_repr,
}

///|
pub extend SubtoposComplementReport with Eq::{not_equal, equal}

///|
/// Internal right `G`-torsor candidate in a Grothendieck sheaf topos `Sh(site)`:
///   - `carrier`: underlying presheaf `T` on `site.cat`;
///   - `group`: finite permutation group `G` (`elements` enumerate `G` in canonical order);
///   - `action`: natural automorphisms `ρ_g : T -> T` aligned with `group_elems[i]`,
///     satisfying right-action composition `ρ_{g1 * g2} == ρ_{g2} ∘ ρ_{g1}`!
pub(all) struct InternalGroupTorsor {
  site : Site
  carrier : @sym.Presheaf
  group_elems : Array[@sym.Perm]
  action : Array[PresheafHom]
}

// =============================================================================
// 1. Right Kan Extension `Ran_{u^{op}}` & Essential Geometric Morphisms
// =============================================================================

///|
/// Compute the **Right Kan Extension Presheaf** `(Ran_{phi^{op}} P)(d) = lim_{(d ↓ phi^{op})} P`
/// along `phi : C -> D` by delegating limit-cone enumeration directly to
/// `@sym.ran` on `cat_opposite`! Together with `inverse_image_presheaf` (`Lan_{phi^{op}}`)
/// and `direct_image_presheaf` (`phi^*`), this completes the **Essential Geometric
/// Morphism Triple Adjunction** `e_! ⊣ e^* ⊣ e_*` (`Lan_{phi^{op}} ⊣ phi^* ⊣ Ran_{phi^{op}}`).
pub fn right_kan_presheaf(
  phi : @sym.FinFunctor,
  p : @sym.Presheaf,
  cap~ : Int32 = 2048,
) -> @sym.Presheaf {
  guard @sym.is_fin_functor(phi) else {
    abort("right_kan_presheaf: invalid FinFunctor")
  }
  let c_op = cat_opposite(phi.src)
  let d_op = cat_opposite(phi.dst)
  let phi_op : @sym.FinFunctor = {
    src: c_op,
    dst: d_op,
    obj: phi.obj.copy(),
    mor: phi.mor.copy(),
  }
  let diag = @sym.diagram_new(c_op, p.size.copy(), p.res.copy())
  let r = @sym.ran(phi_op, diag, cap)
  // Reconstruct comma object lists `(c, m : d ->_{D^op} phi(c))` in `@sym.ran` order
  // so restriction along `m0 : d ->_{D^op} dp` pulls cones back by precomposition!
  let comma_objs_by_d : Array[Array[(Int32, Int32)]] = []
  for d in 0..<d_op.nobj {
    let cobjs : Array[(Int32, Int32)] = []
    for c in 0..<c_op.nobj {
      for m in 0..<d_op.nmor {
        if d_op.dom[m] == d && d_op.cod[m] == phi_op.obj[c] {
          cobjs.push((c, m))
        }
      }
    }
    comma_objs_by_d.push(cobjs)
  }
  let res : Array[Array[Int32]] = []
  for m0 in 0..<d_op.nmor {
    let d = d_op.dom[m0]
    let dp = d_op.cod[m0]
    let src_cobjs = comma_objs_by_d[d]
    let dst_cobjs = comma_objs_by_d[dp]
    // Precomposition `m ↦ m ∘_{D^op} m0` maps `(dp ↓ phi^op)` into `(d ↓ phi^op)`.
    let pull_idx = Array::make(dst_cobjs.length(), -1)
    for j in 0..<dst_cobjs.length() {
      let (c, m) = dst_cobjs[j]
      let comp_m = d_op.comp[m * d_op.nmor + m0]
      let mut hit = -1
      for i in 0..<src_cobjs.length() {
        if src_cobjs[i] == (c, comp_m) {
          hit = i
          break
        }
      }
      guard hit >= 0 else {
        abort("right_kan_presheaf: comma pullback index missing")
      }
      pull_idx[j] = hit
    }
    let map_m0 = Array::make(r.size[d], 0)
    for cone_i in 0..<r.size[d] {
      let src_cone = r.cones[d][cone_i]
      let dst_cone = Array::make(dst_cobjs.length(), 0)
      for j in 0..<dst_cobjs.length() {
        dst_cone[j] = src_cone[pull_idx[j]]
      }
      let mut target_idx = -1
      for k in 0..<r.size[dp] {
        if r.cones[dp][k] == dst_cone {
          target_idx = k
          break
        }
      }
      guard target_idx >= 0 else {
        abort("right_kan_presheaf: restricted cone not in limit")
      }
      map_m0[cone_i] = target_idx
    }
    res.push(map_m0)
  }
  @sym.presheaf_new(phi.dst, r.size, res)
}

///|
/// Verify the **Essential Geometric Morphism Triple Adjunction**
/// `e_! = Lan_{phi^{op}} ⊣ e^* = phi^* ⊣ e_* = Ran_{phi^{op}}` induced by
/// `phi : C -> D`:
///   1. `|Hom_{PSh(D)}(e_! P, Q)| == |Hom_{PSh(C)}(P, e^* Q)|` (left adjunction);
///   2. `|Hom_{PSh(C)}(e^* Q, P)| == |Hom_{PSh(D)}(Q, e_* P)|` (right adjunction);
///   3. `e_* (1_C) ≅ 1_D` (right adjoint always preserves terminal object!).
pub fn verify_essential_geometric_triple_adjunction(
  phi : @sym.FinFunctor,
  sample_p : @sym.Presheaf,
  sample_q : @sym.Presheaf,
) -> Bool {
  guard @sym.is_fin_functor(phi) else { return false }
  let e_shriek_p = inverse_image_presheaf(phi, sample_p)
  let e_star_q = direct_image_presheaf(phi, sample_q)
  let e_lower_p = right_kan_presheaf(phi, sample_p)
  if !@sym.is_presheaf(e_shriek_p) ||
    !@sym.is_presheaf(e_star_q) ||
    !@sym.is_presheaf(e_lower_p) {
    return false
  }
  let hom_shriek_l = presheaf_hom_enumerate(e_shriek_p, sample_q, cap=2048).length()
  let hom_shriek_r = presheaf_hom_enumerate(sample_p, e_star_q, cap=2048).length()
  if hom_shriek_l != hom_shriek_r {
    return false
  }
  let hom_ran_l = presheaf_hom_enumerate(e_star_q, sample_p, cap=2048).length()
  let hom_ran_r = presheaf_hom_enumerate(sample_q, e_lower_p, cap=2048).length()
  if hom_ran_l != hom_ran_r {
    return false
  }
  let term_c = presheaf_terminal(phi.src)
  let term_d = presheaf_terminal(phi.dst)
  presheaf_are_isomorphic(right_kan_presheaf(phi, term_c), term_d)
}

///|
/// Decide whether the essential geometric morphism `e : PSh(C) -> PSh(D)`
/// induced by `phi : C -> D` is **Connected** (`e^* : PSh(D) -> PSh(C)` full &
/// faithful, equivalently `e_!(1_C) ≅ 1_D`, i.e. every comma category `(phi ↓ d)`
/// in `C^op` has `π_0 == 1`)!
pub fn is_connected_essential_functor(phi : @sym.FinFunctor) -> Bool {
  guard @sym.is_fin_functor(phi) else { return false }
  let e_shriek_term = inverse_image_presheaf(phi, presheaf_terminal(phi.src))
  presheaf_are_isomorphic(e_shriek_term, presheaf_terminal(phi.dst))
}

// =============================================================================
// 2. Co-Heyting Subtopos Nucleus Calculus: Open & Closed Subtopos Complementarity
// =============================================================================

///|
/// Pointwise **Meet `J_1 ∧ J_2`** in the lattice of Grothendieck topologies on `cat`
/// (corresponding to the **Union `Sh_{J_1} ∪ Sh_{J_2}`** in the lattice of subtoposes!):
/// a sieve covers in `J_1 ∧ J_2` iff it covers in BOTH `J_1` and `J_2`.
pub fn topology_lattice_meet(
  cat : @sym.FinCat,
  j1 : GrothendieckTopology,
  j2 : GrothendieckTopology,
) -> GrothendieckTopology {
  let covers : Array[Array[Sieve]] = []
  for u in 0..<cat.nobj {
    let cu : Array[Sieve] = []
    for s in j1.covers[u] {
      if topology_covers(j2, s) {
        cu.push(s)
      }
    }
    covers.push(cu)
  }
  { nobj: cat.nobj, covers, }
}

///|
/// **Join `J_1 ∨ J_2`** in the lattice of Grothendieck topologies on `cat`
/// (smallest Grothendieck topology containing `J_1 ∪ J_2`, corresponding to the
/// **Intersection `Sh_{J_1} ∩ Sh_{J_2}`** of subtoposes!).
pub fn topology_lattice_join(
  cat : @sym.FinCat,
  j1 : GrothendieckTopology,
  j2 : GrothendieckTopology,
) -> GrothendieckTopology {
  let raw_cov : Array[(Int32, Array[Int32])] = []
  for u in 0..<cat.nobj {
    for s in j1.covers[u] {
      raw_cov.push((u, s.arrows.copy()))
    }
    for s in j2.covers[u] {
      raw_cov.push((u, s.arrows.copy()))
    }
  }
  topology_from_coverage(cat, raw_cov)
}

///|
fn subterminal_sieves(u_sub : @sym.Presheaf) -> Array[Sieve] {
  let cat = u_sub.cat
  let u_sieves : Array[Sieve] = []
  for v in 0..<cat.nobj {
    let arr : Array[Int32] = []
    for f in 0..<cat.nmor {
      if cat.cod[f] == v && u_sub.size[cat.dom[f]] == 1 {
        arr.push(f)
      }
    }
    u_sieves.push(sieve_generate(cat, v, arr))
  }
  u_sieves
}

///|
/// Construct the **Open Subtopos Lawvere–Tierney Operator** `j_{open(U)} : Ω -> Ω`
/// associated to a subterminal presheaf `u_sub ↪ 1` (`u_sub.size[v] ∈ {0, 1}`):
/// at stage `v`, `j_{open(U)}(S) = (U|_v ⇒ S)`, where `U|_v = { f : w -> v | u_sub.size[w] == 1 }`!
pub fn open_subtopos_lt_operator(
  u_sub : @sym.Presheaf,
) -> (SubobjectClassifierData, PresheafHom) {
  let cat = u_sub.cat
  let om = subobject_classifier_presheaf(cat)
  let u_sieves = subterminal_sieves(u_sub)
  let comps : Array[Array[Int32]] = []
  for v in 0..<cat.nobj {
    let sv = om.closed_sieves[v]
    let cv = Array::make(sv.length(), 0)
    for idx in 0..<sv.length() {
      let implied = sieve_heyting_implies(cat, u_sieves[v], sv[idx])
      let mut pos = -1
      for k in 0..<sv.length() {
        if sv[k] == implied {
          pos = k
          break
        }
      }
      guard pos >= 0 else {
        abort("open_subtopos_lt_operator: implied sieve missing")
      }
      cv[idx] = pos
    }
    comps.push(cv)
  }
  (
    om,
    {
      cat,
      dom_size: om.omega.size.copy(),
      cod_size: om.omega.size.copy(),
      components: comps,
    },
  )
}

///|
/// Construct the **Closed Subtopos Lawvere–Tierney Operator** `j_{closed(U)} : Ω -> Ω`
/// associated to a subterminal presheaf `u_sub ↪ 1`:
/// at stage `v`, `j_{closed(U)}(S) = U|_v ∪ S`!
pub fn closed_subtopos_lt_operator(
  u_sub : @sym.Presheaf,
) -> (SubobjectClassifierData, PresheafHom) {
  let cat = u_sub.cat
  let om = subobject_classifier_presheaf(cat)
  let u_sieves = subterminal_sieves(u_sub)
  let comps : Array[Array[Int32]] = []
  for v in 0..<cat.nobj {
    let sv = om.closed_sieves[v]
    let cv = Array::make(sv.length(), 0)
    for idx in 0..<sv.length() {
      let joined = sieve_union(u_sieves[v], sv[idx])
      let mut pos = -1
      for k in 0..<sv.length() {
        if sv[k] == joined {
          pos = k
          break
        }
      }
      guard pos >= 0 else {
        abort("closed_subtopos_lt_operator: union sieve missing")
      }
      cv[idx] = pos
    }
    comps.push(cv)
  }
  (
    om,
    {
      cat,
      dom_size: om.omega.size.copy(),
      cod_size: om.omega.size.copy(),
      components: comps,
    },
  )
}

///|
/// Verify **Grothendieck–Johnstone Open/Closed Subtopos Complementarity** for a
/// subterminal `u_sub ↪ 1` in `PSh(cat)`:
///   1. `j_{open(U)}` and `j_{closed(U)}` are valid Lawvere–Tierney modalities;
///   2. `J_{open(U)} ∧ J_{closed(U)} == J_trivial` (`Sh_o(U) ∪ Sh_c(U) = PSh(cat)`);
///   3. `J_{open(U)} ∨ J_{closed(U)} == J_inconsistent` (every empty sieve covers,
///      so `Sh_o(U) ∩ Sh_c(U) ≃ 1`);
///   4. Records whether internal Excluded Middle `U ∪ ¬U == ⊤` holds in `Ω` (on
///      intuitionistic sites such as Sierpinski, `internal_lem_holds == false`
///      EVEN WHILE `subtopos_boolean_complement_holds == true`!).
pub fn verify_open_closed_subtopos_complementarity(
  u_sub : @sym.Presheaf,
) -> SubtoposComplementReport {
  let cat = u_sub.cat
  let (om_o, j_open) = open_subtopos_lt_operator(u_sub)
  let (om_c, j_closed) = closed_subtopos_lt_operator(u_sub)
  let open_ok = is_lawvere_tierney_operator(om_o, j_open)
  let closed_ok = is_lawvere_tierney_operator(om_c, j_closed)
  let top_o = topology_of_lawvere_tierney(om_o, j_open)
  let top_c = topology_of_lawvere_tierney(om_c, j_closed)
  let meet_j = topology_lattice_meet(cat, top_o, top_c)
  let join_j = topology_lattice_join(cat, top_o, top_c)
  let meet_triv = meet_j == topology_trivial(cat)
  let mut join_inconsistent = topology_is_valid(cat, join_j)
  for v in 0..<cat.nobj {
    if !topology_covers(join_j, sieve_empty(v)) {
      join_inconsistent = false
    }
  }
  // Check whether `U|_v ∪ ¬(U|_v) == M_v` at every object `v` in `Ω`:
  let triv_site = site_new(cat, topology_trivial(cat))
  let u_sieves = subterminal_sieves(u_sub)
  let mut lem_internal = true
  for v in 0..<cat.nobj {
    let uv = u_sieves[v]
    let neg_uv = omega_j_neg(triv_site, uv)
    if sieve_union(uv, neg_uv) != sieve_maximal(cat, v) {
      lem_internal = false
    }
  }
  {
    open_lt_valid: open_ok,
    closed_lt_valid: closed_ok,
    meet_is_ambient: meet_triv,
    join_is_inconsistent: join_inconsistent,
    internal_lem_holds: lem_internal,
    subtopos_boolean_complement_holds: open_ok &&
    closed_ok &&
    meet_triv &&
    join_inconsistent,
  }
}

// =============================================================================
// 3. Grothendieck–Verdier Comparison Lemma (Site Morita Equivalence)
// =============================================================================

///|
/// Check whether `u : C -> D` is **Full, Faithful, and `J_D`-Dense** into `site_d = (D, J_D)`:
///   1. For all `c_1, c_2 ∈ C`, `u : Hom_C(c_1, c_2) -> Hom_D(u(c_1), u(c_2))` is bijective;
///   2. For every object `d ∈ D`, the sieve generated by `{ f : u(c) -> d | c ∈ C }` covers `d` in `J_D`!
/// When satisfied, derives and returns the **Induced Subsite Grothendieck Topology `J_C`**
/// (`S ∈ J_C(c) <=> <u(S)>_D ∈ J_D(u(c))`), otherwise returns `None`.
pub fn induced_dense_subsite_topology(
  u : @sym.FinFunctor,
  site_d : Site,
) -> GrothendieckTopology? {
  guard @sym.is_fin_functor(u) && site_is_valid(site_d) else { return None }
  let c = u.src
  let d = site_d.cat
  // 1. Check Full & Faithful:
  for c1 in 0..<c.nobj {
    for c2 in 0..<c.nobj {
      let c_mors : Array[Int32] = []
      for m in 0..<c.nmor {
        if c.dom[m] == c1 && c.cod[m] == c2 {
          c_mors.push(u.mor[m])
        }
      }
      let mut d_count = 0
      for md in 0..<d.nmor {
        if d.dom[md] == u.obj[c1] && d.cod[md] == u.obj[c2] {
          d_count = d_count + 1
        }
      }
      if c_mors.length() != d_count {
        return None
      }
      // Injectivity on Hom_C(c1, c2):
      for i in 0..<c_mors.length() {
        for j in (i + 1)..<c_mors.length() {
          if c_mors[i] == c_mors[j] {
            return None
          }
        }
      }
    }
  }
  // 2. Check J_D-Density of u(C) in D:
  for y in 0..<d.nobj {
    let from_c : Array[Int32] = []
    for x in 0..<c.nobj {
      for md in 0..<d.nmor {
        if d.dom[md] == u.obj[x] && d.cod[md] == y {
          from_c.push(md)
        }
      }
    }
    let gen = sieve_generate(d, y, from_c)
    if !topology_covers(site_d.topology, gen) {
      return None
    }
  }
  // 3. Derive Induced Topology J_C: S ∈ J_C(x) <=> <u(S)>_D ∈ J_D(u(x))!
  let covers : Array[Array[Sieve]] = []
  for x in 0..<c.nobj {
    let cx : Array[Sieve] = []
    for s in all_sieves_on(c, x) {
      let mapped : Array[Int32] = []
      for f in s.arrows {
        mapped.push(u.mor[f])
      }
      let gen_d = sieve_generate(d, u.obj[x], mapped)
      if topology_covers(site_d.topology, gen_d) {
        cx.push(s)
      }
    }
    covers.push(cx)
  }
  let jc : GrothendieckTopology = { nobj: c.nobj, covers, }
  if topology_is_valid(c, jc) {
    Some(jc)
  } else {
    None
  }
}

///|
/// Verify **Grothendieck's Comparison Lemma (`Sh(C, J_C) ≃ Sh(D, J_D)`)**:
///   1. `induced_dense_subsite_topology(u, site_d)` succeeds and yields a valid site `(C, J_C)`;
///   2. Restriction `u^* : Sh(D, J_D) -> Sh(C, J_C)` preserves sheaves (`is_sheaf(site_c, u^* F)`);
///   3. Inverse equivalence `a_{J_D} ∘ Lan_{u^{op}}` recovers `F` up to isomorphism
///      (`sheafify(site_d, inverse_image_presheaf(u, u^* F)).sheaf ≅ F`), AND
///      `|End_{Sh(D)}(F)| == |End_{Sh(C)}(u^* F)|`!
pub fn verify_grothendieck_comparison_lemma(
  u : @sym.FinFunctor,
  site_d : Site,
  sheaf_d : @sym.Presheaf,
) -> Bool {
  guard is_sheaf(site_d, sheaf_d) else { return false }
  let jc = match induced_dense_subsite_topology(u, site_d) {
    Some(j) => j
    None => return false
  }
  let site_c = site_new(u.src, jc)
  let res_c = direct_image_presheaf(u, sheaf_d)
  if !is_sheaf(site_c, res_c) {
    return false
  }
  let reconstructed = inverse_image_sheaf(site_d, u, res_c)
  if !presheaf_are_isomorphic(reconstructed, sheaf_d) {
    return false
  }
  let end_d = presheaf_hom_enumerate(sheaf_d, sheaf_d, cap=2048).length()
  let end_c = presheaf_hom_enumerate(res_c, res_c, cap=2048).length()
  end_d == end_c
}

// =============================================================================
// 4. Diaconescu Internal `G`-Torsors & Shear Isomorphism Theorem
// =============================================================================

///|
/// Decide whether `tors` is a genuine **Internal `G`-Torsor Sheaf** in `Sh(tors.site)`:
///   1. `tors.carrier` is a `J`-sheaf;
///   2. Every `ρ_g` is a natural transformation `T -> T`, `ρ_e == id_T`, and
///      right-action law `ρ_{g1 * g2} == ρ_{g2} ∘ ρ_{g1}` holds for all `g1, g2 ∈ G`;
///   3. **Local Inhabitedness (`T ->> 1` in `Sh(C, J)`)**: for every `u ∈ C`, the sieve
///      `{ f : v -> u | T(v) != ∅ }` belongs to `J(u)`;
///   4. **Free & Transitive Shear Isomorphism**: at every `u ∈ C`, the shear map
///      `T(u) × G -> T(u) × T(u)` sending `(t, g) ↦ (t, ρ_g(u)(t))` is a bijection
///      (delegated to `@sym.FinMap::is_iso`)!
pub fn is_internal_group_torsor_sheaf(tors : InternalGroupTorsor) -> Bool {
  let site = tors.site
  let c = site.cat
  let t_sh = tors.carrier
  let ng = tors.group_elems.length()
  guard ng >= 1 && tors.action.length() == ng else { return false }
  guard is_sheaf(site, t_sh) else { return false }
  // 1 & 2. Check naturality, identity, and right-action homomorphism law:
  for i in 0..<ng {
    if !presheaf_hom_is_natural(t_sh, t_sh, tors.action[i]) {
      return false
    }
    if tors.group_elems[i].is_identity() &&
      !presheaf_hom_eq(tors.action[i], presheaf_hom_id(t_sh)) {
      return false
    }
  }
  // Uniform group action quantifier (right OR left homomorphism uniformly across ALL pairs `(i, j)`):
  let mut all_right = true
  let mut all_left = true
  for i in 0..<ng {
    for j in 0..<ng {
      let prod_g = tors.group_elems[i].compose(tors.group_elems[j])
      let mut k_idx = -1
      for k in 0..<ng {
        if tors.group_elems[k].equal(prod_g) {
          k_idx = k
          break
        }
      }
      guard k_idx >= 0 else { return false }
      let comp_ij = presheaf_hom_compose(tors.action[j], tors.action[i])
      let comp_ji = presheaf_hom_compose(tors.action[i], tors.action[j])
      if !presheaf_hom_eq(tors.action[k_idx], comp_ij) {
        all_right = false
      }
      if !presheaf_hom_eq(tors.action[k_idx], comp_ji) {
        all_left = false
      }
    }
  }
  if !all_right && !all_left {
    return false
  }
  // 3. Local inhabitedness: `{ f : v -> u | T(v) > 0 } ∈ J(u)` for every `u ∈ C`.
  for u in 0..<c.nobj {
    let inhab : Array[Int32] = []
    for f in 0..<c.nmor {
      if c.cod[f] == u && t_sh.size[c.dom[f]] > 0 {
        inhab.push(f)
      }
    }
    let s_inhab = sieve_generate(c, u, inhab)
    if !topology_covers(site.topology, s_inhab) {
      return false
    }
  }
  // 4. Shear isomorphism `(t, g) ↦ (t, ρ_g(u)(t)) : T(u) × G -> T(u) × T(u)`:
  for u in 0..<c.nobj {
    let tu = t_sh.size[u]
    let dom_sz = tu * ng
    let cod_sz = tu * tu
    let img = Array::make(dom_sz, 0)
    for t_el in 0..<tu {
      for g_i in 0..<ng {
        let tg = tors.action[g_i].components[u][t_el]
        img[t_el * ng + g_i] = t_el * tu + tg
      }
    }
    if !@sym.FinMap::new(dom_sz, cod_sz, img).is_iso() {
      return false
    }
  }
  true
}

///|
/// Build the non-trivial **Möbius `Z/2Z`-Torsor** on `site_circle_good_cover()`
/// by equipping `circle_mobius_double_cover_sheaf()` with sheet-involution!
pub fn build_mobius_internal_z2_torsor() -> InternalGroupTorsor {
  let site = site_circle_good_cover()
  let sh = circle_mobius_double_cover_sheaf()
  let g_elems = @sym.PermGroup::symmetric(2).elements(4)
  let action : Array[PresheafHom] = []
  for g in g_elems {
    if g.is_identity() {
      action.push(presheaf_hom_id(sh))
    } else {
      let comps : Array[Array[Int32]] = []
      for u in 0..<site.cat.nobj {
        if sh.size[u] == 2 {
          comps.push([1, 0])
        } else {
          comps.push([])
        }
      }
      action.push({
        cat: site.cat,
        dom_size: sh.size.copy(),
        cod_size: sh.size.copy(),
        components: comps,
      })
    }
  }
  { site, carrier: sh, group_elems: g_elems, action, }
}

// =============================================================================
// 5. Alexander–Whitney Simplicial Cup-Product DG-Algebra (`H^1 ⌣ H^1 -> H^2`)
// =============================================================================

///|
/// Alexander–Whitney cup product `a ⌣ b ∈ C^2(nerve; Q)` of two 1-cochains
/// `a, b ∈ C^1(nerve; Q)` on `nerve`:
/// for each oriented 2-simplex `(v_0 < v_1 < v_2)` in `nerve.triangles`,
/// `(a ⌣ b)(v_0, v_1, v_2) = a(v_0, v_1) * b(v_1, v_2)`!
pub fn simplicial_cup_1_1(
  nerve : SimplicialNerve,
  a : Array[@exactalg.Rat],
  b : Array[@exactalg.Rat],
) -> Array[@exactalg.Rat] {
  let ne = nerve.edges.length()
  let nt = nerve.triangles.length()
  guard a.length() == ne && b.length() == ne else {
    abort("simplicial_cup_1_1: 1-cochain length mismatch")
  }
  let out = Array::make(nt, @exactalg.rat_zero())
  for t_i in 0..<nt {
    let (v0, v1, v2) = nerve.triangles[t_i]
    let e01 = nerve_edge_index(nerve, v0, v1)
    let e12 = nerve_edge_index(nerve, v1, v2)
    out[t_i] = @exactalg.rat_mul(a[e01], b[e12])
  }
  out
}

///|
/// Verify the **Graded Leibniz Rule** of the Alexander–Whitney DG-Algebra
/// `d^2(a ⌣ b) == (d^1 a) ⌣_21 b - a ⌣_12 (d^1 b)` on 3-simplices `(v_0 < v_1 < v_2 < v_3)`
/// AND on 2-simplices for a 0-cochain `f` and 1-cochain `a`:
/// `d^1(f ⌣ a) == (d^0 f) ⌣ a + f ⌣ (d^1 a)`!
pub fn verify_alexander_whitney_leibniz(
  nerve : SimplicialNerve,
  f0 : Array[@exactalg.Rat],
  a1 : Array[@exactalg.Rat],
) -> Bool {
  let nv = nerve.num_vertices
  let ne = nerve.edges.length()
  let nt = nerve.triangles.length()
  guard f0.length() == nv && a1.length() == ne else { return false }
  let cpx = nerve_constant_cochain_complex_q(nerve)
  // Compute `(f0 ⌣ a1)(u < v) = f0(u) * a1(u, v)` in C^1:
  let f_cup_a = Array::make(ne, @exactalg.rat_zero())
  for e_i in 0..<ne {
    let (u, _) = nerve.edges[e_i]
    f_cup_a[e_i] = @exactalg.rat_mul(f0[u], a1[e_i])
  }
  // LHS = d^1(f0 ⌣ a1) in C^2:
  let lhs = if nt == 0 || ne == 0 {
    Array::make(nt, @exactalg.rat_zero())
  } else {
    rect_qmat_vec(cpx.differentials[1], f_cup_a)
  }
  // RHS = (d^0 f0) ⌣ a1 + f0 ⌣ (d^1 a1):
  let df0 = if ne == 0 || nv == 0 {
    Array::make(ne, @exactalg.rat_zero())
  } else {
    rect_qmat_vec(cpx.differentials[0], f0)
  }
  let da1 = if nt == 0 || ne == 0 {
    Array::make(nt, @exactalg.rat_zero())
  } else {
    rect_qmat_vec(cpx.differentials[1], a1)
  }
  let df_cup_a = simplicial_cup_1_1(nerve, df0, a1)
  let rhs = Array::make(nt, @exactalg.rat_zero())
  for t_i in 0..<nt {
    let (v0, _, _) = nerve.triangles[t_i]
    rhs[t_i] = @exactalg.rat_add(
      df_cup_a[t_i],
      @exactalg.rat_mul(f0[v0], da1[t_i]),
    )
  }
  if lhs != rhs {
    return false
  }
  // Also verify Koszul-signed `d^2(a1 ⌣ a1) == (d^1 a1) ⌣ a1 - a1 ⌣ (d^1 a1)` on 3-simplices!
  let ntet = nerve.tetrahedra.length()
  if ntet > 0 {
    let a_cup_a = simplicial_cup_1_1(nerve, a1, a1)
    let lhs3 = rect_qmat_vec(cpx.differentials[2], a_cup_a)
    let rhs3 = Array::make(ntet, @exactalg.rat_zero())
    for tet_i in 0..<ntet {
      let (v0, v1, v2, v3) = nerve.tetrahedra[tet_i]
      let t012 = nerve_tri_index(nerve, v0, v1, v2)
      let t123 = nerve_tri_index(nerve, v1, v2, v3)
      let e01 = nerve_edge_index(nerve, v0, v1)
      let e23 = nerve_edge_index(nerve, v2, v3)
      rhs3[tet_i] = @exactalg.rat_sub(
        @exactalg.rat_mul(da1[t012], a1[e23]),
        @exactalg.rat_mul(a1[e01], da1[t123]),
      )
    }
    if lhs3 != rhs3 {
      return false
    }
  }
  true
}

///|
/// Compute the exact rational vector-space rank of the **Cup-Product Pairing**
/// `⌣ : H^1(nerve; Q) ⊗ H^1(nerve; Q) -> H^2(nerve; Q)`:
///   1. Computes `Z^1 = ker(d^1)` via `@exactalg.qrows_nullspace`;
///   2. Computes `Z^2 = ker(d^2)` and `B^2 = im(d^1)`;
///   3. Evaluates `z_i ⌣ z_j` for all pairs of 1-cocycles, verifies `z_i ⌣ z_j ∈ Z^2`
///      (cocycle closure!), and returns `dim((B^2 + span{z_i ⌣ z_j}) / B^2)`!
pub fn simplicial_cup_h1_h1_rank(nerve : SimplicialNerve) -> Int32 {
  let cpx = nerve_constant_cochain_complex_q(nerve)
  let n1 = cpx.dims[1]
  let n2 = cpx.dims[2]
  if n1 == 0 || n2 == 0 {
    return 0
  }
  let z1 = if cpx.differentials[1].nrows == 0 {
    rect_qmat_id(n1).rows
  } else {
    @exactalg.qrows_nullspace(cpx.differentials[1].rows, n1)
  }
  // B^2 = column space of d^1 = row space of (d^1)^T:
  let b2 : Array[Array[@exactalg.Rat]] = []
  for col in 0..<n1 {
    let img_col = Array::make(n2, @exactalg.rat_zero())
    for r in 0..<n2 {
      img_col[r] = cpx.differentials[1].rows[r][col]
    }
    if !@exactalg.qvec_is_zero(img_col) {
      b2.push(img_col)
    }
  }
  let span_with_cups = b2.copy()
  for i in 0..<z1.length() {
    for j in 0..<z1.length() {
      let cup_ij = simplicial_cup_1_1(nerve, z1[i], z1[j])
      // Verify `cup_ij ∈ Z^2 = ker(d^2)` whenever 3-simplices exist!
      if cpx.dims[3] > 0 {
        let d2_cup = rect_qmat_vec(cpx.differentials[2], cup_ij)
        guard @exactalg.qvec_is_zero(d2_cup) else {
          abort("simplicial_cup_h1_h1_rank: cup of 1-cocycles not a 2-cocycle")
        }
      }
      if !@exactalg.qvec_is_zero(cup_ij) {
        span_with_cups.push(cup_ij)
      }
    }
  }
  @exactalg.qvec_rank(span_with_cups) - @exactalg.qvec_rank(b2)
}

///|
/// Minimal 7-vertex Möbius–Császár triangulation of the **2-Torus `T^2`**
/// (`7` vertices, `21` edges, `14` triangles `{i, i+1, i+3}` and `{i, i+2, i+3}` mod 7):
///   - `b = [1, 2, 1, 0]`, `χ = 0`,
///   - **Non-trivial cup product `rank(H^1 ⌣ H^1 -> H^2) == 1`** (Poincaré duality!).
pub fn torus_t2_minimal_nerve() -> SimplicialNerve {
  let edges : Array[(Int32, Int32)] = []
  for u in 0..<7 {
    for v in (u + 1)..<7 {
      edges.push((u, v))
    }
  }
  fn sorted_tri(a : Int32, b : Int32, c : Int32) -> (Int32, Int32, Int32) {
    let arr = [a, b, c]
    if arr[0] > arr[1] {
      let t = arr[0]
      arr[0] = arr[1]
      arr[1] = t
    }
    if arr[1] > arr[2] {
      let t = arr[1]
      arr[1] = arr[2]
      arr[2] = t
    }
    if arr[0] > arr[1] {
      let t = arr[0]
      arr[0] = arr[1]
      arr[1] = t
    }
    (arr[0], arr[1], arr[2])
  }
  let raw_tris : Array[(Int32, Int32, Int32)] = []
  for i in 0..<7 {
    raw_tris.push(sorted_tri(i, (i + 1) % 7, (i + 3) % 7))
    raw_tris.push(sorted_tri(i, (i + 2) % 7, (i + 3) % 7))
  }
  // Sort triangles lexicographically for canonical `SimplicialNerve` order.
  for i in 0..<raw_tris.length() {
    for j in (i + 1)..<raw_tris.length() {
      if raw_tris[j] < raw_tris[i] {
        let tmp = raw_tris[i]
        raw_tris[i] = raw_tris[j]
        raw_tris[j] = tmp
      }
    }
  }
  { num_vertices: 7, edges, triangles: raw_tris, tetrahedra: [], }
}

///|
/// Wedge sum **`S^1 ∨ S^1 ∨ S^2`** (`∂Δ^3` on `{0,1,2,3}` wedged at vertex `0`
/// with two hollow triangles `{0,4,5}` and `{0,6,7}`):
///   - **Identical Betti numbers `b = [1, 2, 1, 0]` and `χ = 0` as `T^2`**,
///   - **Vanishing cup product `rank(H^1 ⌣ H^1 -> H^2) == 0`**!
pub fn wedge_s1_s1_s2_nerve() -> SimplicialNerve {
  {
    num_vertices: 8,
    edges: [
      (0, 1),
      (0, 2),
      (0, 3),
      (0, 4),
      (0, 5),
      (0, 6),
      (0, 7),
      (1, 2),
      (1, 3),
      (2, 3),
      (4, 5),
      (6, 7),
    ],
    triangles: [(0, 1, 2), (0, 1, 3), (0, 2, 3), (1, 2, 3)],
    tetrahedra: [],
  }
}
