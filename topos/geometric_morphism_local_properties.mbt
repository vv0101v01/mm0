///|
// Topos Pillar — Layer 3: Geometric Morphisms (f* ⊣ f_*), Diaconescu Points
// of a Topos, Local Toposes (Δ ⊣ Γ ⊣ Γ^!), Connected Toposes (Π_0 ⊣ Δ ⊣ Γ),
// Atomic Toposes (Atoms & Booleanity), and Compact / Coherent / Deligne
// Enough-Points Decision Procedures.

///|
/// A covariant functor `F : cat -> FinSet` representing a candidate flat
/// J-continuous functor (by Diaconescu's theorem, equivalent to a geometric
/// morphism / point `p : Set -> Sh(cat, J)`).
pub(all) struct FlatPointFunctor {
  cat : @sym.FinCat
  size : Array[Int32]
  map : Array[Array[Int32]]
}

///|
/// Diagnostic report of Local Topos analysis (`Δ ⊣ Γ ⊣ Γ^!`).
pub(all) struct LocalToposReport {
  is_local : Bool
  global_terminal_sections : Int32
  global_initial_sections : Int32
  preserves_coproducts : Bool
  preserves_coequalizers : Bool
  focal_point : FlatPointFunctor?
  triple_adjunction_holds : Bool
}

///|
/// Diagnostic report of Connected Topos analysis (`Π_0 ⊣ Δ ⊣ Γ`).
pub(all) struct ConnectedToposReport {
  is_connected : Bool
  clopen_subobjects_of_one : Int32
  connected_components : Int32
  delta_two_global_sections : Int32
}

///|
/// Diagnostic report of Atomic Topos analysis.
pub(all) struct AtomicToposReport {
  is_atomic : Bool
  is_boolean : Bool
  site_right_ore : Bool
  representable_atom_count : Int32
}

///|
/// Diagnostic report of Compact / Coherent / Spatial Topos analysis.
pub(all) struct CompactCoherentReport {
  is_compact : Bool
  is_coherent : Bool
  site_has_pullbacks : Bool
  terminal_irredundant_cover_degree : Int32
  max_minimal_cover_arity : Int32
  point_count : Int32
  has_enough_points : Bool
}

///|
/// Check whether `phi : site_c -> site_d` is cover-preserving: every covering
/// sieve `S ∈ J(u)` maps to arrows generating a covering sieve in `K(Phi(u))`.
pub fn is_cover_preserving_functor(
  site_c : Site,
  site_d : Site,
  phi : @sym.FinFunctor,
) -> Bool {
  guard @sym.is_fin_functor(phi) else { return false }
  for u in 0..<site_c.cat.nobj {
    for s in site_c.topology.covers[u] {
      let mapped : Array[Int32] = []
      for f in s.arrows {
        mapped.push(phi.mor[f])
      }
      let gen_d = sieve_generate(site_d.cat, phi.obj[u], mapped)
      if !topology_covers(site_d.topology, gen_d) {
        return false
      }
    }
  }
  true
}

///|
/// Direct image presheaf functor `(f_* Q)(u) = Q(Phi(u))` along `Phi : C -> D`.
pub fn direct_image_presheaf(
  phi : @sym.FinFunctor,
  q : @sym.Presheaf,
) -> @sym.Presheaf {
  let c = phi.src
  let size = Array::make(c.nobj, 0)
  for u in 0..<c.nobj {
    size[u] = q.size[phi.obj[u]]
  }
  let res : Array[Array[Int32]] = []
  for f in 0..<c.nmor {
    res.push(q.res[phi.mor[f]].copy())
  }
  @sym.presheaf_new(c, size, res)
}

///|
/// Inverse image presheaf functor `f^*_psh P = Lan_{Phi^op} P` on `D`,
/// delegating directly to `@sym.lan` and `@sym.lan_map` on `cat_opposite`!
pub fn inverse_image_presheaf(
  phi : @sym.FinFunctor,
  p : @sym.Presheaf,
) -> @sym.Presheaf {
  let c_op = cat_opposite(phi.src)
  let d_op = cat_opposite(phi.dst)
  let phi_op : @sym.FinFunctor = {
    src: c_op,
    dst: d_op,
    obj: phi.obj.copy(),
    mor: phi.mor.copy(),
  }
  let diag_op = @sym.diagram_new(c_op, p.size.copy(), p.res.copy())
  let lr = @sym.lan(phi_op, diag_op, 16384)
  let res : Array[Array[Int32]] = []
  for delta in 0..<phi.dst.nmor {
    let d1 = phi.dst.dom[delta]
    let d2 = phi.dst.cod[delta]
    // In `d_op`, `delta` has domain `d2` and codomain `d1`.
    match @sym.lan_map(lr, delta, d2, d1) {
      Some(m) => res.push(m)
      None => abort("inverse_image_presheaf: lan_map failed")
    }
  }
  @sym.presheaf_new(phi.dst, lr.size.copy(), res)
}

///|
/// Sheafified inverse image functor `f^*(P) = a_K(Lan_{Phi^op} P)` from
/// `Sh(site_c)` to `Sh(site_d)`.
pub fn inverse_image_sheaf(
  site_d : Site,
  phi : @sym.FinFunctor,
  p : @sym.Presheaf,
) -> @sym.Presheaf {
  sheafify(site_d, inverse_image_presheaf(phi, p)).sheaf
}

///|
/// Verify whether `phi : site_c -> site_d` induces a genuine Geometric Morphism
/// `f : Sh(site_d) -> Sh(site_c)`:
///   1. `f_*` carries K-sheaves to J-sheaves;
///   2. Adjunction `Hom_Sh(f^* P, Q) ≅ Hom_Sh(P, f_* Q)` holds on sample sheaves;
///   3. `f^*` is LEFT EXACT (`f^*(1) ≅ 1` and `f^*(P1 × P2) ≅ f^*(P1) × f^*(P2)`).
pub fn verify_geometric_morphism(
  site_c : Site,
  site_d : Site,
  phi : @sym.FinFunctor,
  sample_p1 : @sym.Presheaf,
  sample_p2 : @sym.Presheaf,
  sample_q : @sym.Presheaf,
) -> Bool {
  guard @sym.is_fin_functor(phi) &&
    is_sheaf(site_c, sample_p1) &&
    is_sheaf(site_c, sample_p2) &&
    is_sheaf(site_d, sample_q) else {
    return false
  }
  let f_lower_q = direct_image_presheaf(phi, sample_q)
  if !is_sheaf(site_c, f_lower_q) {
    return false
  }
  let f_upper_p1 = inverse_image_sheaf(site_d, phi, sample_p1)
  let f_upper_p2 = inverse_image_sheaf(site_d, phi, sample_p2)
  // Adjunction cardinality check: |Hom(f^* P1, Q)| == |Hom(P1, f_* Q)|.
  let lhs_homs = presheaf_hom_enumerate(f_upper_p1, sample_q, cap=4096)
  let rhs_homs = presheaf_hom_enumerate(sample_p1, f_lower_q, cap=4096)
  if lhs_homs.length() != rhs_homs.length() {
    return false
  }
  // Left exactness 1: f^*(1_C) ≅ 1_D.
  let term_c = presheaf_terminal(site_c.cat)
  let term_d = presheaf_terminal(site_d.cat)
  let f_upper_term = inverse_image_sheaf(site_d, phi, term_c)
  if !presheaf_are_isomorphic(f_upper_term, term_d) {
    return false
  }
  // Left exactness 2: f^*(P1 × P2) ≅ f^*(P1) × f^*(P2).
  let (prod_c, _, _) = presheaf_product(sample_p1, sample_p2)
  let f_upper_prod = inverse_image_sheaf(site_d, phi, prod_c)
  let (prod_d, _, _) = presheaf_product(f_upper_p1, f_upper_p2)
  presheaf_are_isomorphic(f_upper_prod, prod_d)
}

///|
/// Check whether `F : cat -> FinSet` is a valid covariant functor by viewing it
/// as a contravariant `@sym.Presheaf` on `cat_opposite(cat)`.
pub fn is_covariant_point_functor(fp : FlatPointFunctor) -> Bool {
  @sym.is_presheaf({ cat: cat_opposite(fp.cat), size: fp.size, res: fp.map, })
}

///|
/// Check whether `F : cat -> FinSet` is FLAT (its category of elements `∫ F`
/// is cofiltered: non-empty, pair-cone filtering, parallel-arrow equalizing).
pub fn is_flat_point_functor(fp : FlatPointFunctor) -> Bool {
  guard is_covariant_point_functor(fp) else { return false }
  let c = fp.cat
  // Axiom 1: non-empty total set of elements.
  let elems : Array[(Int32, Int32)] = []
  for u in 0..<c.nobj {
    for x in 0..<fp.size[u] {
      elems.push((u, x))
    }
  }
  if elems.length() == 0 {
    return false
  }
  // Axiom 2: for every (u, x) and (v, y), ∃ (w, z) and f:w->u, g:w->v
  // with F(f)(z) == x and F(g)(z) == y.
  for p1 in elems {
    let (u, x) = p1
    for p2 in elems {
      let (v, y) = p2
      let mut found = false
      for p3 in elems {
        let (w, z) = p3
        let mut hit_u = false
        let mut hit_v = false
        for f in 0..<c.nmor {
          if c.dom[f] == w && c.cod[f] == u && fp.map[f][z] == x {
            hit_u = true
            break
          }
        }
        if hit_u {
          for g in 0..<c.nmor {
            if c.dom[g] == w && c.cod[g] == v && fp.map[g][z] == y {
              hit_v = true
              break
            }
          }
        }
        if hit_u && hit_v {
          found = true
          break
        }
      }
      if !found {
        return false
      }
    }
  }
  // Axiom 3: for parallel f, g : u -> v and x ∈ F(u) with F(f)(x) == F(g)(x),
  // ∃ h : w -> u and z ∈ F(w) such that f ∘ h == g ∘ h and F(h)(z) == x.
  for f in 0..<c.nmor {
    for g in (f + 1)..<c.nmor {
      if c.dom[f] != c.dom[g] || c.cod[f] != c.cod[g] {
        continue
      }
      let u = c.dom[f]
      for x in 0..<fp.size[u] {
        if fp.map[f][x] != fp.map[g][x] {
          continue
        }
        let mut eq_found = false
        for h in 0..<c.nmor {
          if c.cod[h] == u && c.comp[f * c.nmor + h] == c.comp[g * c.nmor + h] {
            let w = c.dom[h]
            for z in 0..<fp.size[w] {
              if fp.map[h][z] == x {
                eq_found = true
                break
              }
            }
          }
          if eq_found {
            break
          }
        }
        if !eq_found {
          return false
        }
      }
    }
  }
  true
}

///|
/// Diaconescu's Criterion: `F : C -> FinSet` defines a point `p : Set -> Sh(C, J)`
/// iff `F` is flat AND J-continuous (`∀ S ∈ J(u), { F(f) : f ∈ S }` is jointly
/// surjective onto `F(u)`).
pub fn is_diaconescu_point(site : Site, fp : FlatPointFunctor) -> Bool {
  guard is_flat_point_functor(fp) else { return false }
  let c = site.cat
  for u in 0..<c.nobj {
    for s in site.topology.covers[u] {
      for x in 0..<fp.size[u] {
        let mut covered = false
        for f in s.arrows {
          let v = c.dom[f]
          for y in 0..<fp.size[v] {
            if fp.map[f][y] == x {
              covered = true
              break
            }
          }
          if covered {
            break
          }
        }
        if !covered {
          return false
        }
      }
    }
  }
  true
}

///|
/// Compute the stalk cardinality `|p^*(E)|` of a presheaf/sheaf `E` at a
/// Diaconescu point `fp`:
///   `p^*(E) = { (u, x ∈ F(u), s ∈ E(u)) } / ((u, F(h)(z), s) ~ (w, z, E(h)(s)))`.
pub fn point_stalk_cardinality(
  fp : FlatPointFunctor,
  e_psh : @sym.Presheaf,
) -> Int32 {
  let c = fp.cat
  let triples : Array[(Int32, Int32, Int32)] = []
  for u in 0..<c.nobj {
    for x in 0..<fp.size[u] {
      for s in 0..<e_psh.size[u] {
        triples.push((u, x, s))
      }
    }
  }
  let n = triples.length()
  if n == 0 {
    return 0
  }
  let parent = uf_new(n)
  for h in 0..<c.nmor {
    let w = c.dom[h]
    let u = c.cod[h]
    for z in 0..<fp.size[w] {
      let x = fp.map[h][z]
      for s in 0..<e_psh.size[u] {
        let lhs = (u, x, s)
        let rhs = (w, z, e_psh.res[h][s])
        let mut il = -1
        let mut ir = -1
        for k in 0..<n {
          if triples[k] == lhs {
            il = k
          }
          if triples[k] == rhs {
            ir = k
          }
        }
        if il >= 0 && ir >= 0 {
          uf_union(parent, il, ir)
        }
      }
    }
  }
  let mut count = 0
  for i in 0..<n {
    if uf_find(parent, i) == i {
      count = count + 1
    }
  }
  count
}

///|
fn int_pow_i32(base : Int32, exp : Int32) -> Int32 {
  let mut acc = 1
  for _ in 0..<exp {
    acc = acc * base
  }
  acc
}

///|
/// Construct the skyscraper / direct-image sheaf `p_*(S)` of a finite set of
/// cardinality `set_card` along a Diaconescu point `fp`:
///   `(p_* S)(u) = S^{F(u)}` with restriction `(p_* S)(h)(tup)[z] = tup[F(h)(z)]`.
pub fn point_skyscraper_sheaf(
  fp : FlatPointFunctor,
  set_card : Int32,
) -> @sym.Presheaf {
  let c = fp.cat
  let size = Array::make(c.nobj, 0)
  for u in 0..<c.nobj {
    size[u] = int_pow_i32(set_card, fp.size[u])
  }
  let res : Array[Array[Int32]] = []
  for h in 0..<c.nmor {
    let w = c.dom[h]
    let u = c.cod[h]
    let map_h = Array::make(size[u], 0)
    for code_u in 0..<size[u] {
      // Decode base-`set_card` digits at `u` of length `fp.size[u]`.
      let digits_u = Array::make(fp.size[u], 0)
      let mut tmp = code_u
      for idx in 0..<fp.size[u] {
        digits_u[idx] = tmp % set_card
        tmp = tmp / set_card
      }
      // Pull back along `fp.map[h] : F(w) -> F(u)` and re-encode at `w`.
      let mut code_w = 0
      let mut mult = 1
      for z in 0..<fp.size[w] {
        let d = digits_u[fp.map[h][z]]
        code_w = code_w + d * mult
        mult = mult * set_card
      }
      map_h[code_u] = code_w
    }
    res.push(map_h)
  }
  @sym.presheaf_new(c, size, res)
}

///|
/// Covariant representable point `Hom_C(a, -)` constructed directly as the
/// contravariant representable `presheaf_representable(cat_opposite(c), a)`.
pub fn covariant_representable_point(
  c : @sym.FinCat,
  a : Int32,
) -> FlatPointFunctor {
  let rep = presheaf_representable(cat_opposite(c), a)
  { cat: c, size: rep.size, map: rep.res, }
}

///|
/// Enumerate canonical Diaconescu points of `site`:
///   - All `{0, 1}`-valued J-continuous flat filters (completely prime filters
///     of poset/localic sites, when `nobj <= 12`);
///   - Plus all J-continuous covariant representables `Hom_C(a, -)` (which
///     capture groupoid torsor points such as the unique fiber functor of `BG`!).
pub fn enumerate_canonical_points(site : Site) -> Array[FlatPointFunctor] {
  let c = site.cat
  let out : Array[FlatPointFunctor] = []
  fn same_point_stalks(a : FlatPointFunctor, b : FlatPointFunctor) -> Bool {
    if a.size == b.size && a.map == b.map {
      return true
    }
    false
  }
  // 1. Subterminal / filter points F(u) ∈ {0, 1} for nobj <= 12.
  if c.nobj <= 12 {
    let total = int_pow_i32(2, c.nobj)
    for mask in 1..<total {
      let size = Array::make(c.nobj, 0)
      for u in 0..<c.nobj {
        size[u] = (mask >> u) & 1
      }
      // Valid covariant functor iff size[dom(m)] == 1 ==> size[cod(m)] == 1.
      let mut upward_closed = true
      let map : Array[Array[Int32]] = []
      for m in 0..<c.nmor {
        let u = c.dom[m]
        let v = c.cod[m]
        if size[u] == 1 && size[v] == 0 {
          upward_closed = false
          break
        }
        map.push(if size[u] == 1 { [0] } else { [] })
      }
      if upward_closed {
        let cand : FlatPointFunctor = { cat: c, size, map, }
        if is_diaconescu_point(site, cand) {
          out.push(cand)
        }
      }
    }
  }
  // 2. Covariant representables Hom_C(a, -).
  for a in 0..<c.nobj {
    let rep_pt = covariant_representable_point(c, a)
    if is_diaconescu_point(site, rep_pt) {
      let mut dup = false
      for existing in out {
        if same_point_stalks(existing, rep_pt) {
          dup = true
          break
        }
      }
      if !dup {
        out.push(rep_pt)
      }
    }
  }
  out
}

///|
/// Global sections cardinality `|Γ(E)| = |Hom_Sh(1, E)|`.
pub fn global_sections_count(site : Site, e_sheaf : @sym.Presheaf) -> Int32 {
  let term = presheaf_terminal(site.cat)
  presheaf_hom_enumerate(term, e_sheaf, cap=4096).length()
}

///|
/// Analyze whether `Sh(site)` is a **Local Topos** (`Δ ⊣ Γ ⊣ Γ^!`):
///   1. `|Γ(1)| == 1` and `|Γ(a(0))| == 0` (non-degenerate, connected terminal);
///   2. `Γ` preserves sheafified binary coproducts on generators `a(y(u))`;
///   3. `Γ` preserves sheafified coequalizers (testing e.g. universal/groupoid
///      quotients `a(y(u)) ->> 1` where non-local `BG` fails!);
///   4. Exhibits the focal Diaconescu point `c` whose stalk `c^*(E)` matches
///      `|Γ(E)|`, constructs `Γ^!(2) = c_*(2)`, and verifies the Triple
///      Adjunction `|Hom_Sh(E, Γ^!(2))| == 2^{|Γ(E)|}`!
pub fn analyze_local_topos(site : Site) -> LocalToposReport {
  let c = site.cat
  let term = presheaf_terminal(c)
  let init_sh = sheafify(site, presheaf_initial(c)).sheaf
  let g_one = global_sections_count(site, term)
  let g_zero = global_sections_count(site, init_sh)
  let gens : Array[@sym.Presheaf] = []
  for u in 0..<c.nobj {
    gens.push(sheafify(site, presheaf_representable(c, u)).sheaf)
  }
  // Check coproduct preservation of Γ on pairs of generators and `1 + 1`.
  let mut preserves_coproducts = g_zero == 0
  let (one_plus_one_raw, _, _) = presheaf_coproduct(term, term)
  let one_plus_one = sheafify(site, one_plus_one_raw).sheaf
  if global_sections_count(site, one_plus_one) != 2 * g_one {
    preserves_coproducts = false
  }
  for i in 0..<gens.length() {
    for j in i..<gens.length() {
      let (s_raw, _, _) = presheaf_coproduct(gens[i], gens[j])
      let s_sh = sheafify(site, s_raw).sheaf
      if global_sections_count(site, s_sh) !=
        global_sections_count(site, gens[i]) +
        global_sections_count(site, gens[j]) {
        preserves_coproducts = false
        break
      }
    }
    if !preserves_coproducts {
      break
    }
  }
  // Check coequalizer preservation on `E × E ==(π1, π2)==> E` for every non-empty
  // generator `E`: in PSh(C) its coequalizer is the image of E -> 1; if E is
  // globally supported (`a(coeq) ≅ 1`) while `Γ(E) == 0` (exact failure on BG!),
  // then Γ fails to preserve coequalizers!
  let mut preserves_coequalizers = true
  for g_sh in gens {
    let (prod_gg, pi1, pi2) = presheaf_product(g_sh, g_sh)
    let (coeq_raw, _) = presheaf_coequalizer(prod_gg, g_sh, pi1, pi2)
    let coeq_sh = sheafify(site, coeq_raw).sheaf
    let g_e = global_sections_count(site, g_sh)
    let g_coeq = global_sections_count(site, coeq_sh)
    // Coequalizer of all pairs on a set S has cardinality min(1, |S|).
    let expected_set_coeq = if g_e == 0 { 0 } else { 1 }
    if g_coeq != expected_set_coeq {
      preserves_coequalizers = false
      break
    }
  }
  // Search for the focal point c among Diaconescu points such that c^*(E) == Γ(E)
  // and `|Hom_Sh(E, c_*(2))| == 2^{|Γ(E)|}` on all generators and Ω_J.
  let omega_j = subobject_classifier_sheaf(site).omega
  let mut focal_point : FlatPointFunctor? = None
  let mut triple_adjunction_holds = false
  let pts = enumerate_canonical_points(site)
  for pt in pts {
    let mut matches_gamma = point_stalk_cardinality(pt, term) == g_one &&
      point_stalk_cardinality(pt, init_sh) == g_zero &&
      point_stalk_cardinality(pt, omega_j) ==
      global_sections_count(site, omega_j)
    if matches_gamma {
      for g_sh in gens {
        if point_stalk_cardinality(pt, g_sh) !=
          global_sections_count(site, g_sh) {
          matches_gamma = false
          break
        }
      }
    }
    if matches_gamma {
      let gamma_shriek_two = point_skyscraper_sheaf(pt, 2)
      if is_sheaf(site, gamma_shriek_two) {
        let mut adj_ok = true
        for g_sh in gens {
          let hom_cnt = presheaf_hom_enumerate(g_sh, gamma_shriek_two, cap=4096).length()
          let want = int_pow_i32(2, global_sections_count(site, g_sh))
          if hom_cnt != want {
            adj_ok = false
            break
          }
        }
        // Also check Δ(2) ⊣ Γ: |Hom_Sh(Δ(2), Ω_J)| == |Γ(Ω_J)|^2.
        let delta_two = sheafify(site, presheaf_constant_raw(c, 2)).sheaf
        let lhs_delta = presheaf_hom_enumerate(delta_two, omega_j, cap=4096).length()
        let g_omega = global_sections_count(site, omega_j)
        if lhs_delta != g_omega * g_omega {
          adj_ok = false
        }
        if adj_ok {
          focal_point = Some(pt)
          triple_adjunction_holds = true
          break
        }
      }
    }
  }
  let is_local = g_one == 1 &&
    g_zero == 0 &&
    preserves_coproducts &&
    preserves_coequalizers &&
    triple_adjunction_holds
  {
    is_local,
    global_terminal_sections: g_one,
    global_initial_sections: g_zero,
    preserves_coproducts,
    preserves_coequalizers,
    focal_point,
    triple_adjunction_holds,
  }
}

///|
/// Analyze whether `Sh(site)` is a **Connected Topos**:
///   `Sh(site)` is connected iff `Δ : Set -> Sh(site)` is fully faithful,
///   equivalently `|Γ(Δ(2))| == 2` and `1` has exactly `2` complemented
///   (clopen) subobjects (`⊥` and `⊤`).
pub fn analyze_connected_topos(site : Site) -> ConnectedToposReport {
  let omega_j = subobject_classifier_sheaf(site)
  let global_truths = presheaf_hom_enumerate(
    omega_j.terminal,
    omega_j.omega,
    cap=4096,
  )
  // A global truth element τ : 1 => Ω_J is clopen (complemented) iff there exists
  // τ' : 1 => Ω_J with τ_u ∩ τ'_u == cl_J(∅_u) and τ_u ∨_J τ'_u == M_u for all u.
  let mut clopen_count = 0
  for tau in global_truths {
    let mut has_comp = false
    for tau2 in global_truths {
      let mut ok = true
      for u in 0..<site.cat.nobj {
        let s1 = omega_j.closed_sieves[u][tau.components[u][0]]
        let s2 = omega_j.closed_sieves[u][tau2.components[u][0]]
        let bot_u = sieve_j_closure(site, sieve_empty(u))
        let top_u = sieve_maximal(site.cat, u)
        if sieve_inter(s1, s2) != bot_u || omega_j_join(site, s1, s2) != top_u {
          ok = false
          break
        }
      }
      if ok {
        has_comp = true
        break
      }
    }
    if has_comp {
      clopen_count = clopen_count + 1
    }
  }
  let mut components = 0
  let mut p = 1
  while p < clopen_count {
    p = p * 2
    components = components + 1
  }
  let delta_two = sheafify(site, presheaf_constant_raw(site.cat, 2)).sheaf
  let delta_two_global = global_sections_count(site, delta_two)
  {
    is_connected: clopen_count == 2 && delta_two_global == 2,
    clopen_subobjects_of_one: clopen_count,
    connected_components: components,
    delta_two_global_sections: delta_two_global,
  }
}

///|
/// Decide whether a J-sheaf `a_sheaf` is an **Atom** in `Sh(site)`:
/// non-initial (`¬(a_sheaf ≅ a(0))`) and has NO proper non-initial J-sheaf
/// subobjects (`|Sub_Sh(a_sheaf)| == 2`, tested via `|Hom_Sh(a_sheaf, Ω_J)| == 2`).
pub fn is_atom_sheaf(site : Site, a_sheaf : @sym.Presheaf) -> Bool {
  guard is_sheaf(site, a_sheaf) else { return false }
  let init_sh = sheafify(site, presheaf_initial(site.cat)).sheaf
  if presheaf_are_isomorphic(a_sheaf, init_sh) {
    return false
  }
  let omega_j = subobject_classifier_sheaf(site)
  presheaf_hom_enumerate(a_sheaf, omega_j.omega, cap=64).length() == 2
}

///|
/// Analyze whether `Sh(site)` is an **Atomic Topos**:
///   In an atomic topos, `Ω_J` is Boolean and every object splits into a
///   coproduct of atoms (in particular, for atomic sites, sheafified
///   representables of connected site components are atoms!).
pub fn analyze_atomic_topos(site : Site) -> AtomicToposReport {
  let boolean_ok = is_boolean_topos(site)
  let ore_ok = cat_satisfies_right_ore(site.cat)
  let init_sh = sheafify(site, presheaf_initial(site.cat)).sheaf
  let mut rep_atoms = 0
  let mut all_non_init_atomic_generated = true
  let omega_j = subobject_classifier_sheaf(site)
  for u in 0..<site.cat.nobj {
    let ay = sheafify(site, presheaf_representable(site.cat, u)).sheaf
    if presheaf_are_isomorphic(ay, init_sh) {
      continue
    }
    if is_atom_sheaf(site, ay) {
      rep_atoms = rep_atoms + 1
    } else {
      // Check if Sub_Sh(ay) is finite Boolean atomic (size 2^k with k >= 1).
      let sub_cnt = presheaf_hom_enumerate(ay, omega_j.omega, cap=512).length()
      let mut pow2 = 1
      while pow2 < sub_cnt {
        pow2 = pow2 * 2
      }
      if !boolean_ok || pow2 != sub_cnt {
        all_non_init_atomic_generated = false
      }
    }
  }
  {
    is_atomic: boolean_ok && all_non_init_atomic_generated && rep_atoms > 0,
    is_boolean: boolean_ok,
    site_right_ore: ore_ok,
    representable_atom_count: rep_atoms,
  }
}

///|
/// Minimal number of arrows in `s` whose generated sieve already covers `s.target`
/// in `site`.
fn minimal_cover_arity(site : Site, s : Sieve) -> Int32 {
  let u = s.target
  if topology_covers(site.topology, sieve_empty(u)) {
    return 0
  }
  for f in s.arrows {
    if topology_covers(site.topology, sieve_generate(site.cat, u, [f])) {
      return 1
    }
  }
  let n = s.arrows.length()
  for i in 0..<n {
    for j in (i + 1)..<n {
      if topology_covers(
          site.topology,
          sieve_generate(site.cat, u, [s.arrows[i], s.arrows[j]]),
        ) {
        return 2
      }
    }
  }
  for i in 0..<n {
    for j in (i + 1)..<n {
      for k in (j + 1)..<n {
        if topology_covers(
            site.topology,
            sieve_generate(site.cat, u, [s.arrows[i], s.arrows[j], s.arrows[k]]),
          ) {
          return 3
        }
      }
    }
  }
  n
}

///|
/// Check whether category `c` has categorical pullbacks for every cospan
/// `f : a -> d` and `g : b -> d` (universal cone `(p, p1 : p -> a, p2 : p -> b)`
/// with `f ∘ p1 == g ∘ p2` and unique factorization of every competing cone).
pub fn cat_has_pullbacks(c : @sym.FinCat) -> Bool {
  for f in 0..<c.nmor {
    for g in 0..<c.nmor {
      if c.cod[f] != c.cod[g] {
        continue
      }
      let a = c.dom[f]
      let b = c.dom[g]
      let mut pb_found = false
      for p in 0..<c.nobj {
        for p1 in 0..<c.nmor {
          if c.dom[p1] != p || c.cod[p1] != a {
            continue
          }
          for p2 in 0..<c.nmor {
            if c.dom[p2] != p || c.cod[p2] != b {
              continue
            }
            if c.comp[f * c.nmor + p1] != c.comp[g * c.nmor + p2] {
              continue
            }
            // Test universal property against all cones (w, q1, q2).
            let mut universal = true
            for w in 0..<c.nobj {
              for q1 in 0..<c.nmor {
                if c.dom[q1] != w || c.cod[q1] != a {
                  continue
                }
                for q2 in 0..<c.nmor {
                  if c.dom[q2] != w || c.cod[q2] != b {
                    continue
                  }
                  if c.comp[f * c.nmor + q1] != c.comp[g * c.nmor + q2] {
                    continue
                  }
                  let mut mediators = 0
                  for u_mor in 0..<c.nmor {
                    if c.dom[u_mor] == w &&
                      c.cod[u_mor] == p &&
                      c.comp[p1 * c.nmor + u_mor] == q1 &&
                      c.comp[p2 * c.nmor + u_mor] == q2 {
                      mediators = mediators + 1
                    }
                  }
                  if mediators != 1 {
                    universal = false
                    break
                  }
                }
                if !universal {
                  break
                }
              }
              if !universal {
                break
              }
            }
            if universal {
              pb_found = true
              break
            }
          }
          if pb_found {
            break
          }
        }
        if pb_found {
          break
        }
      }
      if !pb_found {
        return false
      }
    }
  }
  true
}

///|
/// Analyze **Compactness, Coherence, and Deligne's Enough-Points Property**
/// on `Sh(site)`:
///   - `site_has_pullbacks` verifies genuine categorical pullbacks in `site.cat`;
///   - `terminal_irredundant_cover_degree` computes the largest cardinality of an
///     irredundant cover of `1` in `Sub_Sh(1)` (0 iff degenerate `1 ≅ 0`);
///   - `is_compact` holds when `1` is non-degenerate (`1 ≇ 0`) and every open
///     cover of `1` reduces to a bounded irredundant finite subcover;
///   - `is_coherent` holds when `site.cat` has pullbacks (coherent site!) and
///     every covering sieve is finitely generated;
///   - `has_enough_points` tests Deligne spatiality across all `Ω_J(u)`.
pub fn analyze_compact_coherent_topos(site : Site) -> CompactCoherentReport {
  let c = site.cat
  let has_pb = cat_has_pullbacks(c)
  let mut max_arity = 0
  for u in 0..<c.nobj {
    for s in site.topology.covers[u] {
      let ar = minimal_cover_arity(site, s)
      if ar > max_arity {
        max_arity = ar
      }
    }
  }
  let omega_j = subobject_classifier_sheaf(site)
  // Compute Sub_Sh(1) = Hom_Sh(1, Ω_J) and find maximum size of an irredundant
  // family whose join in Sub_Sh(1) equals ⊤!
  let sub_one = presheaf_hom_enumerate(
    omega_j.terminal,
    omega_j.omega,
    cap=1024,
  )
  let init_sh = sheafify(site, presheaf_initial(c)).sheaf
  let non_degenerate = !presheaf_are_isomorphic(omega_j.terminal, init_sh)
  fn join_all_is_top(indices : Array[Int32]) -> Bool {
    for u in 0..<c.nobj {
      let mut acc = sieve_j_closure(site, sieve_empty(u))
      for idx in indices {
        let s = omega_j.closed_sieves[u][sub_one[idx].components[u][0]]
        acc = omega_j_join(site, acc, s)
      }
      if acc != sieve_maximal(c, u) {
        return false
      }
    }
    true
  }
  let mut irred_deg = if non_degenerate { 1 } else { 0 }
  let m_sub = sub_one.length()
  if non_degenerate && m_sub <= 12 {
    let limit_mask = int_pow_i32(2, m_sub)
    for mask in 1..<limit_mask {
      let chosen : Array[Int32] = []
      for i in 0..<m_sub {
        if ((mask >> i) & 1) == 1 {
          chosen.push(i)
        }
      }
      if chosen.length() > irred_deg && join_all_is_top(chosen) {
        let mut irredundant = true
        for skip in 0..<chosen.length() {
          let reduced : Array[Int32] = []
          for k in 0..<chosen.length() {
            if k != skip {
              reduced.push(chosen[k])
            }
          }
          if join_all_is_top(reduced) {
            irredundant = false
            break
          }
        }
        if irredundant {
          irred_deg = chosen.length()
        }
      }
    }
  }
  let pts = enumerate_canonical_points(site)
  let mut enough = true
  for u in 0..<c.nobj {
    let sieves = omega_j.closed_sieves[u]
    for i in 0..<sieves.length() {
      for j in (i + 1)..<sieves.length() {
        let s1 = sieves[i]
        let s2 = sieves[j]
        let (p1_raw, _) = presheaf_of_sieve(c, s1)
        let (p2_raw, _) = presheaf_of_sieve(c, s2)
        let sh1 = sheafify(site, p1_raw).sheaf
        let sh2 = sheafify(site, p2_raw).sheaf
        let mut separated = false
        for pt in pts {
          let (p_inter_raw, _) = presheaf_of_sieve(c, sieve_inter(s1, s2))
          let sh_inter = sheafify(site, p_inter_raw).sheaf
          let c1 = point_stalk_cardinality(pt, sh1)
          let c2 = point_stalk_cardinality(pt, sh2)
          let ci = point_stalk_cardinality(pt, sh_inter)
          if c1 != ci || c2 != ci {
            separated = true
            break
          }
        }
        if !separated {
          enough = false
          break
        }
      }
      if !enough {
        break
      }
    }
    if !enough {
      break
    }
  }
  {
    is_compact: non_degenerate && irred_deg >= 1,
    is_coherent: has_pb && max_arity <= c.nmor,
    site_has_pullbacks: has_pb,
    terminal_irredundant_cover_degree: irred_deg,
    max_minimal_cover_arity: max_arity,
    point_count: pts.length(),
    has_enough_points: enough,
  }
}
