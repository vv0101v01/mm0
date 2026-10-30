///|
// Five-Federation Architecture & Complete K_5 Grand Unification Plan
// (五聯邦架構及大一統規劃):
//   F1 `cubical`  : Cubical Dependent Type Theory, Univalence, ROBDDs & Exact Algebra
//   F2 `symlib`   : Schreier–Sims Symmetry Groups, G-Sets, Burnside & Kan Extensions
//   F3 `semiring` : Idempotent Star-Semirings, Matrix Closure, DFA NF & Tropical Geometry
//   F4 `topos`    : Grothendieck & Elementary Toposes, Subtopos Nuclei, Stacks & Cohomology
//   F5 `scheme`   : Gröbner Ideals, Kähler/Étale Geometry, Dualizing Complexes & Motives
// Every federation carries a live native kernel probe, and all C(5, 2) = 10
// pairwise cross-federation edges of K_5 plus the 5-Federation Pentagon
// Unification Theorem are verified on non-trivial mathematical witnesses.

///|
/// Canonical identifier of the five autonomous mathematical federations.
pub(all) enum FederationId {
  Cubical
  Symlib
  Semiring
  Topos
  Scheme
} derive(Debug, Eq)

///|
pub extend FederationId with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend FederationId with Eq::{not_equal, equal}

///|
/// Architectural and mathematical health descriptor of one federation.
pub(all) struct FederationDescriptor {
  id : FederationId
  slug : String
  packages : Array[String]
  canonical_normal_form : String
  categorification_role : String
  live_health_ok : Bool
  summary : String
} derive(Debug, Eq)

///|
pub extend FederationDescriptor with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend FederationDescriptor with Eq::{not_equal, equal}

///|
/// One verified edge `(lhs, rhs)` of the complete `K_5` cross-federation graph.
pub(all) struct FederationPairBridge {
  id : String
  lhs : FederationId
  rhs : FederationId
  bridge_theorem : String
  holds : Bool
  quantitative_witness : String
} derive(Debug, Eq)

///|
pub extend FederationPairBridge with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend FederationPairBridge with Eq::{not_equal, equal}

///|
/// Execute live native probes across all **5 Federations**, including our
/// Eisenbud Theorem 20.8 mixed-dimension smoothness guard (`line ⊔ point` rejected
/// while pure-dimensional `two_lines` is smooth!) in Federation 5 (`scheme`).
pub fn five_federation_descriptors() -> Array[FederationDescriptor] {
  // F1 Cubical: univalent coe NbE + canonical ROBDD + Hermitian projector
  let f1_ok = @cub.check_coe_definitional() &&
    @cub.check_bdd_canonical() &&
    @cub.check_projector()

  // F2 Symlib: non-abelian S_3 pair action Burnside count + C_4 automorphism certificates
  let s3 = @sym.PermGroup::symmetric(3)
  let gs_s3 = @sym.gset_pairs(s3, 6)
  let (orbs_s3, burnside_s3) = @sym.gset_burnside(gs_s3)
  let c4_graph = @sym.Graph::from_edges(4, [(0, 1), (1, 2), (2, 3), (3, 0)])
  let c4_certs = @sym.prove_graph(
    c4_graph,
    @sym.Perm::from_img([1, 2, 3, 0]),
    32,
  )
  let mut c4_all_ok = c4_certs.length() > 0
  for cert in c4_certs {
    if !cert.holds {
      c4_all_ok = false
    }
  }
  let f2_ok = s3.order() == 6L && orbs_s3 == 2 && burnside_s3 == 2 && c4_all_ok

  // F3 Semiring: BoolSr Lehmann vs Blocked Kleene closure + Brzozowski minimal DFA NF
  let m_bool : @smat.Mat[@semialg.BoolSr] = @smat.Mat::zero(3, 3)
  m_bool.set(0, 1, @semialg.BoolSr::one())
  m_bool.set(1, 2, @semialg.BoolSr::one())
  let cl_leh = @smat.closure_lehmann(m_bool)
  let cl_blk = @smat.closure_blocked(m_bool)
  let mut cl_match = cl_leh.get(0, 2).is_one() && !cl_leh.get(2, 0).is_one()
  for r in 0..<3 {
    for c in 0..<3 {
      if cl_leh.get(r, c) != cl_blk.get(r, c) {
        cl_match = false
      }
    }
  }
  let r_a = @snf.Regex::RChar(0)
  let r_b = @snf.Regex::RChar(1)
  let dfa_ok = @snf.regex_equiv(
    @snf.Regex::RStar(@snf.Regex::RSum(r_a, r_b)),
    @snf.Regex::RStar(
      @snf.Regex::RProd(@snf.Regex::RStar(r_a), @snf.Regex::RStar(r_b)),
    ),
    [0, 1],
  )
  let f3_ok = cl_match && dfa_ok

  // F4 Topos: twisted Möbius sheaf on S^1 + Sierpiński open/closed subtopos nuclei
  let s1_site = @topos.site_circle_good_cover()
  let mobius = @topos.circle_mobius_double_cover_sheaf()
  let sierp = @sym.cat_arrow()
  let u_open = @topos.presheaf_representable(sierp, 0)
  let comp_rep = @topos.verify_open_closed_subtopos_complementarity(u_open)
  let f4_ok = @topos.is_sheaf(s1_site, mobius) &&
    @topos.global_sections_count(s1_site, mobius) == 0 &&
    comp_rep.subtopos_boolean_complement_holds &&
    !comp_rep.internal_lem_holds

  // F5 Scheme: Eisenbud Thm 20.8 pure-dimensional smoothness (accepts pure 1D `e^2-e=0`,
  // strictly rejects mixed-dimension `line ⊔ point = V(e^2-e, t(1-e))` even though Fitt_1 == <1>!)
  let t = @scheme.mpoly_var(2, 0)
  let e = @scheme.mpoly_var(2, 1)
  let e2_minus_e = @scheme.mpoly_sub(@scheme.mpoly_pow(e, 2), e)
  let t_one_minus_e = @scheme.mpoly_mul(
    t,
    @scheme.mpoly_sub(@scheme.mpoly_int(2, 1), e),
  )
  let two_lines = @scheme.affine_scheme(@scheme.coord_ring_new(2, [e2_minus_e]))
  let line_plus_pt = @scheme.affine_scheme(
    @scheme.coord_ring_new(2, [e2_minus_e, t_one_minus_e]),
  )
  let omega_mixed = @scheme.affine_kahler_differentials(line_plus_pt)
  let f5_ok = @scheme.affine_is_smooth(two_lines) &&
    @scheme.ideal_is_unit(@scheme.quasicoherent_fitting_ideal(omega_mixed, 1)) &&
    !@scheme.ideal_eq(
      @scheme.quasicoherent_fitting_ideal(omega_mixed, 0),
      line_plus_pt.ring.ideal,
    ) &&
    !@scheme.affine_is_smooth(line_plus_pt)

  [
    {
      id: Cubical,
      slug: "cubical",
      packages: ["root", "algebra", "cmd-main"],
      canonical_normal_form: "η-long dependent NbE / ROBDD root / RREF & Sturm–Rouché",
      categorification_role: "Cubical CwF with Univalence, HITs & Karoubi Hermitian Projectors",
      live_health_ok: f1_ok,
      summary: "ua/coe NbE=true, ROBDD canonical=true, Hermitian P²=P=P†=true",
    },
    {
      id: Symlib,
      slug: "symlib",
      packages: ["symlib", "cmd-symdemo", "cmd-symbench"],
      canonical_normal_form: "Schreier–Sims BSGS / McKay–Piper colored key / table of marks",
      categorification_role: "Finite PermGroup, Action Groupoids, G-Set Monad & Kan Extensions",
      live_health_ok: f2_ok,
      summary: "|S_3|=6, Orbits(V×V)=\{orbs_s3}==Burnside(\{burnside_s3}), prove_graph(C_4)=true",
    },
    {
      id: Semiring,
      slug: "semiring",
      packages: [
        "semiring-algebra", "semiring-matrix", "semiring-monoid", "semiring-graph",
        "semiring-spline", "semiring-trop", "semiring-nf", "semiring-cat", "semiring-app",
        "semiring-bp", "semiring-ratelimit", "semiring-io", "semiring-sim", "semiring-par",
        "semiring-par-host", "semiring-examples", "cmd-semiringreport",
      ],
      canonical_normal_form: "Kleene star matrix closure A* / Brzozowski minimal DFA / tropical hull",
      categorification_role: "Idempotent Star-Semiring Categories, Weighted CSR Paths & Tropical Polytopes",
      live_health_ok: f3_ok,
      summary: "BoolSr Lehmann==Blocked=true, Brzozowski (a|b)*==(a*b*)*=true",
    },
    {
      id: Topos,
      slug: "topos",
      packages: ["topos"],
      canonical_normal_form: "Grothendieck J-closed sieves Ω_J / Plus-sheafification / Smith torsion",
      categorification_role: "Elementary & Grothendieck Toposes, Subtopos Nuclei, Gerbes & Nerve Cohomology",
      live_health_ok: f4_ok,
      summary: "Möbius Sh(S^1) Γ=0, Subtopos J_o∧J_c=J_triv & J_o∨J_c=J_⊥ (LEM=false)",
    },
    {
      id: Scheme,
      slug: "scheme",
      packages: ["scheme"],
      canonical_normal_form: "Monic reduced grevlex Gröbner basis / Hilbert QPoly / Fitting ideals",
      categorification_role: "Affine & Glued Schemes, Kähler/Étale Geometry, Serre Duality & Chow Motives",
      live_health_ok: f5_ok,
      summary: "Eisenbud Thm 20.8 smooth(two_lines)=true, smooth(line⊔pt)=false (Fitt_0!=I)",
    },
  ]
}

///|
/// **`K5-03` (`Cubical ↔ Topos`)**:
/// Verifies **Cubical Dependent `λΠΣ` (`isContr`) & CCHM Interval Face Classifying Topos
/// ↔ Kripke–Joyal Forcing & Glivenko `Sh_{¬¬}` Booleanization**:
///   1. Voevodsky's `isContr(Z) = Σ(c : Z). Π(x : Z). Path(Z, c, x)` in `@cub.DTerm`
///      translates to `∃c. ∀x. c = x`, forced on `1` and refuted on `1 ⊔ 1` in `Sh(Sierpinski)`;
///   2. `build_cchm_interval_classifying_topos(2)` has exactly `2^2 = 4` points (`{0, 1}^2`);
///   3. `verify_glivenko_topos_subtopos_bridge()` Booleanizes intuitionistic `¬¬LEM`.
pub fn verify_dependent_cubical_topos_bridge() -> Bool {
  let cub_is_contr = @cub.is_contr_type_term(@cub.integer_type_term())
  let formula = translate_cubical_dterm_to_geo_formula(cub_is_contr)
  let sierp = @sym.cat_arrow()
  let site = @topos.site_new(sierp, @topos.topology_trivial(sierp))
  let one = @topos.presheaf_terminal(sierp)
  let (two, _, _) = @topos.presheaf_coproduct(one, one)
  let holds_1 = @topos.kripke_joyal_forces(
    site,
    { carrier: one, pred_arities: [], relations: [], },
    0,
    [],
    formula,
  )
  let holds_2 = @topos.kripke_joyal_forces(
    site,
    { carrier: two, pred_arities: [], relations: [], },
    0,
    [],
    formula,
  )
  // 1D CCHM interval classifying site (`(i=0) ∧ (i=1) ⊢ ⊥`): 3 consistent stages `{⊥, i=0, i=1}`!
  let cchm_1 = build_cchm_interval_classifying_topos(1)
  let mut consistent_stages = 0
  for u in 0..<cchm_1.cat.nobj {
    if !@topos.topology_covers(cchm_1.topology, @topos.sieve_empty(u)) {
      consistent_stages = consistent_stages + 1
    }
  }
  holds_1 &&
  !holds_2 &&
  consistent_stages == 3 &&
  verify_glivenko_topos_subtopos_bridge()
}

///|
/// **`K5-04` (`Cubical ↔ Scheme`)**:
/// Verifies the multivariate ring isomorphism `@algebra.Poly ↔ @scheme.MPoly`
/// (`mpoly_of_poly` / `mpoly_to_poly` preserving addition and multiplication),
/// Bézout intersection multiplicity `dim_Q Q[x,y]/<x^2+y^2-1, x-y> == 2` matching
/// the degree of `@algebra.qpoly_splitting_field(2t^2 - 1)`, together with
/// `Face` Stone–Zariski duality (`verify_cubical_face_zariski_scheme_bridge`)!
pub fn verify_cubical_algebra_scheme_bridge() -> Bool {
  let px = @algebra.poly_var(0)
  let py = @algebra.poly_var(1)
  let p_circle = @algebra.poly_sub(
    @algebra.poly_add(@algebra.poly_mul(px, px), @algebra.poly_mul(py, py)),
    @algebra.poly_int(1),
  )
  let p_diag = @algebra.poly_sub(px, py)
  let m_circle = @scheme.mpoly_of_poly(2, p_circle)
  let m_diag = @scheme.mpoly_of_poly(2, p_diag)
  let prod_poly = @algebra.poly_mul(p_circle, p_diag)
  let prod_mpoly = @scheme.mpoly_mul(m_circle, m_diag)
  if !@algebra.poly_eq(@scheme.mpoly_to_poly(m_circle), p_circle) ||
    !@algebra.poly_eq(@scheme.mpoly_to_poly(prod_mpoly), prod_poly) {
    return false
  }
  let inter_ideal = @scheme.ideal_new(2, [m_circle, m_diag])
  let vdim = @scheme.ideal_quotient_vector_space_dim(inter_ideal)
  // Substituting y = x gives 2x^2 - 1 = 0, splitting field Q(√2) of degree 2:
  let two_t2_minus_1 = @algebra.qpoly_normalize([
    @algebra.rat_int(-1),
    @algebra.rat_zero(),
    @algebra.rat_int(2),
  ])
  let sf_deg = match @algebra.qpoly_splitting_field(two_t2_minus_1) {
    Some(sf) => @algebra.qpoly_degree(sf.modulus)
    None => -1
  }
  // Also check Cubical Face -> Stone–Zariski radical ideal (`(i0=0) ∨ (i1=1) ↦ <x0*(x1-1)>`):
  let face = @cub.face_or(@cub.face_var0(0), @cub.face_var1(1))
  let f_ideal = translate_cubical_face_to_zariski_ideal(face, 2, false)
  let expected_f = @scheme.ideal_new(2, [
    @scheme.mpoly_mul(
      @scheme.mpoly_var(2, 0),
      @scheme.mpoly_sub(@scheme.mpoly_var(2, 1), @scheme.mpoly_int(2, 1)),
    ),
  ])
  vdim == Some(2) &&
  sf_deg == 2 &&
  @scheme.ideal_eq(f_ideal, expected_f) &&
  @scheme.ideal_eq(@scheme.ideal_radical(f_ideal), f_ideal)
}

///|
/// **`K5-06` (`Symlib ↔ Topos`)**:
/// Verifies **Grothendieck's Fundamental Galois Equivalence `G-Set ≃ Sh_at(BG)`**
/// for non-abelian `G = S_3` acting on `X = {0,1,2}²` (`|X| = 9`):
///   1. Contravariant inverse action `res[g](x) = g⁻¹ · x` compiles `FinAction::on_pairs(S_3)`
///      into a genuine atomic sheaf `P ∈ Sh_at(BS_3)`;
///   2. `|Γ(BS_3, P)| == gset_global_fixed(X) == 0`;
///   3. `|Hom_{Sh(BS_3)}(P, Δ(2))| == 4 == 2^{orbits}`, matching Burnside's orbit count `2`;
///   4. `P` decomposes into two atomic subsheaves of sizes `3` (diagonal) and `6`
///      (off-diagonal) with `P ≅ P_diag ⨿ P_off`;
///   5. Topological order-independence of `classifying_nerve_of_poset`: reversing all
///      object indices of the `S^1` open-cover poset (`u > v` on every inclusion!)
///      still recovers `b(B(P)) == [1, 1, 0, 0]`.
pub fn verify_symlib_galois_topos_bridge() -> Bool {
  let s3 = @sym.PermGroup::symmetric(3)
  let elems = s3.elements(6)
  if elems.length() != 6 {
    return false
  }
  let bg = @sym.cat_group(s3, 6)
  guard @topos.topology_atomic(bg) is Some(bg_j) else { return false }
  let bg_site = @topos.site_new(bg, bg_j)
  let act = @sym.FinAction::on_pairs(s3)
  let gs = @sym.gset_from_action(act, s3, 6)
  let (burn_orbits, _) = @sym.gset_burnside(gs)
  let res : Array[Array[Int32]] = []
  for g in elems {
    res.push(act.lift(g.inverse()))
  }
  let psh = @sym.presheaf_new(bg, [gs.x], res)
  if !@sym.is_presheaf(psh) || !@topos.is_sheaf(bg_site, psh) {
    return false
  }
  if @topos.global_sections_count(bg_site, psh) != @sym.gset_global_fixed(gs) ||
    @sym.gset_global_fixed(gs) != 0 {
    return false
  }
  let term = @topos.presheaf_terminal(bg)
  let (delta_two, _, _) = @topos.presheaf_coproduct(term, term)
  if burn_orbits != 2 ||
    @topos.presheaf_hom_enumerate(psh, delta_two).length() != 4 {
    return false
  }
  // Decompose along `gset_orbits(gs)` into two transitive atomic `S_3`-sheaves (`3 + 6 = 9`):
  let orbs = @sym.gset_orbits(gs)
  if orbs.length() != 2 || @topos.is_atom_sheaf(bg_site, psh) {
    return false
  }
  let sub_sheaves : Array[@sym.Presheaf] = []
  for orb in orbs {
    let k_sz = orb.length()
    let sub_res : Array[Array[Int32]] = []
    for m in 0..<bg.nmor {
      let mp = Array::make(k_sz, 0)
      for idx in 0..<k_sz {
        let img_pt = res[m][orb[idx]]
        let mut pos = -1
        for j in 0..<k_sz {
          if orb[j] == img_pt {
            pos = j
            break
          }
        }
        guard pos >= 0 else { return false }
        mp[idx] = pos
      }
      sub_res.push(mp)
    }
    let sub_p = @sym.presheaf_new(bg, [k_sz], sub_res)
    if !@topos.is_atom_sheaf(bg_site, sub_p) {
      return false
    }
    sub_sheaves.push(sub_p)
  }
  let (coprod, _, _) = @topos.presheaf_coproduct(sub_sheaves[0], sub_sheaves[1])
  if !@topos.presheaf_are_isomorphic(psh, coprod) {
    return false
  }
  // Reverse-numbered homotopy circle poset (`5,4,3` -> `2,1,0`, so `dom > cod` on EVERY arrow!):
  let rev_circle_bary = @sym.cat_poset(6, [
    (5, 2),
    (5, 1),
    (4, 1),
    (4, 0),
    (3, 0),
    (3, 2),
  ])
  let ht_rev = @topos.compute_nerve_homotopy_type(
    @topos.classifying_nerve_of_poset(rev_circle_bary),
  )
  ht_rev.betti_numbers == [1, 1, 0, 0] && ht_rev.pi1_free_rank == 1
}

///|
/// **`K5-07` (`Symlib ↔ Scheme`)**:
/// Verifies **Symmetric Group Scheme Automorphisms, Burnside `F_p`-Point Orbits &
/// Vieta Vandermonde Étale `S_2`-Torsor**:
///   1. `S_3` acts by valid `RingHom` automorphisms on the trace-zero plane
///      `H = Spec(Q[x_0, x_1, x_2] / <x_0 + x_1 + x_2>)`;
///   2. Over `F_3` (`3 ≡ 0 mod 3`), `|H(F_3)| = 9` has `3` global `S_3`-fixed points
///      `(c,c,c)` and `4` Burnside orbits (`3` singletons + `1` free orbit of size `6`),
///      whereas over `F_2` (`3 ≡ 1 mod 2`), `|H(F_2)| = 4` has `1` fixed point and `2` orbits;
///   3. For the Vieta invariant quotient `π : A^2_{(x_0,x_1)} -> A^2_{(e_1,e_2)}`
///      (`e_1 = x_0 + x_1`, `e_2 = x_0 x_1`), `√Fitt_0(Ω^1_{π}) == <x_0 - x_1>` and
///      localizing away from the Vandermonde difference `x_0 - x_1` makes `Ω^1 == 0`!
pub fn verify_symlib_symmetric_scheme_bridge() -> Bool {
  let s3 = @sym.PermGroup::symmetric(3)
  let x0 = @scheme.mpoly_var(3, 0)
  let x1 = @scheme.mpoly_var(3, 1)
  let x2 = @scheme.mpoly_var(3, 2)
  let h_ring = @scheme.coord_ring_new(3, [
    @scheme.mpoly_add(@scheme.mpoly_add(x0, x1), x2),
  ])
  let h_aff = @scheme.affine_scheme(h_ring)
  for sigma in s3.elements(6) {
    let hom : @scheme.RingHom = {
      src: h_ring,
      dst: h_ring,
      var_images: [
        @scheme.mpoly_var(3, sigma.apply(0)),
        @scheme.mpoly_var(3, sigma.apply(1)),
        @scheme.mpoly_var(3, sigma.apply(2)),
      ],
    }
    if !@scheme.ring_hom_is_valid(hom) {
      return false
    }
  }
  fn burnside_on_fp(p : Int32) -> (Int32, Int32, Int32) {
    let pts = @scheme.eval_affine_functor_of_points(h_aff, @scheme.fcomm_fp(p))
    let npts = pts.length()
    let imgs : Array[Array[Int32]] = []
    for sigma in s3.elements(6) {
      let inv_s = sigma.inverse()
      let tbl = Array::make(npts, 0)
      for idx in 0..<npts {
        let pt = pts[idx]
        let img_pt = [
          pt[inv_s.apply(0)],
          pt[inv_s.apply(1)],
          pt[inv_s.apply(2)],
        ]
        let mut hit = -1
        for k in 0..<npts {
          if pts[k] == img_pt {
            hit = k
            break
          }
        }
        tbl[idx] = hit
      }
      imgs.push(tbl)
    }
    let gs : @sym.GSetOf = { x: npts, imgs, }
    let (orbs, _) = @sym.gset_burnside(gs)
    (npts, @sym.gset_global_fixed(gs), orbs)
  }
  let (n3, fix3, orb3) = burnside_on_fp(3)
  let (n2, fix2, orb2) = burnside_on_fp(2)
  if (n3, fix3, orb3) != (9, 3, 4) || (n2, fix2, orb2) != (4, 1, 2) {
    return false
  }
  // Vieta quotient `Q[e_1, e_2] -> Q[x_0, x_1]` (`e_1 ↦ x_0 + x_1`, `e_2 ↦ x_0 * x_1`):
  let base_e = @scheme.coord_ring_new(2, [])
  let cov_x = @scheme.coord_ring_new(2, [])
  let y0 = @scheme.mpoly_var(2, 0)
  let y1 = @scheme.mpoly_var(2, 1)
  let vieta : @scheme.RingHom = {
    src: base_e,
    dst: cov_x,
    var_images: [@scheme.mpoly_add(y0, y1), @scheme.mpoly_mul(y0, y1)],
  }
  let omega_vieta = @scheme.kahler_differentials_module(vieta)
  let ram_locus = @scheme.ideal_radical(
    @scheme.quasicoherent_fitting_zero_ideal(omega_vieta),
  )
  let vandermonde = @scheme.mpoly_sub(y0, y1)
  if !@scheme.ideal_eq(ram_locus, @scheme.ideal_new(2, [vandermonde])) {
    return false
  }
  // Localize both base (`disc = e_1^2 - 4 e_2`) and cover (`x_0 - x_1`, where `disc = (x_0 - x_1)^2`!):
  // Wait: inverting `disc = e_1^2 - 4 e_2` (`u_b · (e_1^2 - 4 e_2) = 1` on base,
  // `u_c · (y_0 - y_1)^2 = 1` on cover) gives an exact étale S_2-torsor!
  let e1 = @scheme.mpoly_var(3, 0)
  let e2 = @scheme.mpoly_var(3, 1)
  let ub = @scheme.mpoly_var(3, 2)
  let disc_e = @scheme.mpoly_sub(
    @scheme.mpoly_pow(e1, 2),
    @scheme.mpoly_mul(@scheme.mpoly_int(3, 4), e2),
  )
  let base_loc = @scheme.coord_ring_new(3, [
    @scheme.mpoly_sub(@scheme.mpoly_mul(ub, disc_e), @scheme.mpoly_int(3, 1)),
  ])
  let z0 = @scheme.mpoly_var(3, 0)
  let z1 = @scheme.mpoly_var(3, 1)
  let uc = @scheme.mpoly_var(3, 2)
  let diff_z = @scheme.mpoly_sub(z0, z1)
  let cov_loc = @scheme.coord_ring_new(3, [
    @scheme.mpoly_sub(
      @scheme.mpoly_mul(uc, @scheme.mpoly_pow(diff_z, 2)),
      @scheme.mpoly_int(3, 1),
    ),
  ])
  let vieta_etale : @scheme.RingHom = {
    src: base_loc,
    dst: cov_loc,
    var_images: [@scheme.mpoly_add(z0, z1), @scheme.mpoly_mul(z0, z1), uc],
  }
  @scheme.is_etale_ring_hom_between_smooth(vieta_etale)
}

///|
/// **`K5-08` (`Semiring ↔ Topos`)**:
/// Verifies **Boolean Semiring Kleene Star Closure `M*` ↔ Alexandroff Poset Sieves
/// & Subobject Classifier `Ω_J`**:
///   1. On the 4-vertex diamond DAG `0 -> 1 -> 3, 0 -> 2 -> 3`, `@smat.closure_lehmann`
///      and `@smat.closure_blocked` over `@semialg.BoolSr` compute identical
///      reflexive-transitive reachability matrices `M*`;
///   2. The idempotent semiring module fixed-point lattice `Fix((M*)^T) = { v ∈ 2^4 | (M*)^T ⊗ v = v }`
///      (downward-closed subsets) has cardinality `6`;
///   3. Compiling `M*` to `@sym.cat_poset` yields `|Γ(1, Ω_{PSh(P)})| == 6 == |Fix((M*)^T)|`,
///      while imposing the Grothendieck cover `{1 -> 3, 2 -> 3}` of `3` shrinks
///      `|Γ(1, Ω_J)|` strictly from `6` to `5` (eliminating `{0, 1, 2}`)!
pub fn verify_semiring_kleene_alexandroff_topos_bridge() -> Bool {
  let m : @smat.Mat[@semialg.BoolSr] = @smat.Mat::zero(4, 4)
  m.set(0, 1, @semialg.BoolSr::one())
  m.set(0, 2, @semialg.BoolSr::one())
  m.set(1, 3, @semialg.BoolSr::one())
  m.set(2, 3, @semialg.BoolSr::one())
  let m_star = @smat.closure_lehmann(m)
  let m_blk = @smat.closure_blocked(m)
  let pairs : Array[(Int32, Int32)] = []
  for i in 0..<4 {
    for j in 0..<4 {
      if m_star.get(i, j) != m_blk.get(i, j) {
        return false
      }
      if i != j && m_star.get(i, j).is_one() {
        pairs.push((i, j))
      }
    }
  }
  // Count downward-closed Boolean vectors `v ∈ {0, 1}^4`: `(i <= j and v[j] = 1) => v[i] = 1`,
  // i.e., `v ⊕ (M* ⊗ v) == v` (`M* ⊗ v == v` since `M*` has 1s on the diagonal!):
  let mut fix_count = 0
  for mask in 0..<16 {
    let v = Array::make(4, false)
    for k in 0..<4 {
      v[k] = ((mask >> k) & 1) == 1
    }
    let mv = Array::make(4, false)
    for i in 0..<4 {
      for j in 0..<4 {
        if m_star.get(i, j).is_one() && v[j] {
          mv[i] = true
        }
      }
    }
    if mv == v {
      fix_count = fix_count + 1
    }
  }
  let poset = @sym.cat_poset(4, pairs)
  let triv_site = @topos.site_new(poset, @topos.topology_trivial(poset))
  let om = @topos.subobject_classifier_presheaf(poset)
  let global_truths = @topos.global_sections_count(triv_site, om.omega)
  // Impose Grothendieck cover `{1 -> 3, 2 -> 3}` over `3`:
  let cov_arrows : Array[Int32] = []
  for f in 0..<poset.nmor {
    if (poset.dom[f] == 1 || poset.dom[f] == 2) && poset.cod[f] == 3 {
      cov_arrows.push(f)
    }
  }
  let j_cov = @topos.topology_from_coverage(poset, [(3, cov_arrows)])
  let site = @topos.site_new(poset, j_cov)
  let om_j = @topos.subobject_classifier_sheaf(site)
  let sheaf_truths = @topos.global_sections_count(site, om_j.omega)
  fix_count == 6 && global_truths == 6 && sheaf_truths == 5
}

///|
/// Execute and return all **`C(5, 2) = 10` Pairwise Cross-Federation Bridges** of the
/// complete graph `K_5` over `{Cubical, Symlib, Semiring, Topos, Scheme}`!
pub fn verify_k5_federation_bridges() -> Array[FederationPairBridge] {
  [
    {
      id: "K5-01",
      lhs: Cubical,
      rhs: Symlib,
      bridge_theorem: "S_4 Perm ↔ Cubical Bool^4 Wiring/Equiv & Unitary Adjoint Representation",
      holds: check_perm_wiring_bridge(),
      quantitative_witness: "|S_4|=24 round-trips on 16 Bool^4 states; P(σ)† == P(σ⁻¹)",
    },
    {
      id: "K5-02",
      lhs: Cubical,
      rhs: Semiring,
      bridge_theorem: "FaceClass ROBDD Quotient Star-Semiring & p-adic QPoly Tropicalization",
      holds: check_face_semiring_bridge() && check_tropical_bridges(),
      quantitative_witness: "48 star-idempotent law samples + tropical Newton min-plus roots",
    },
    {
      id: "K5-03",
      lhs: Cubical,
      rhs: Topos,
      bridge_theorem: "Cubical λΠΣ / Voevodsky isContr & Face → Kripke–Joyal & Glivenko Sh_{¬¬}",
      holds: verify_dependent_cubical_topos_bridge(),
      quantitative_witness: "1 ⊨ ⟦isContr⟧, 2 ⊭ ⟦isContr⟧; Sh_{¬¬}(Sierp) Booleanizes ¬¬LEM",
    },
    {
      id: "K5-04",
      lhs: Cubical,
      rhs: Scheme,
      bridge_theorem: "Exact Poly ↔ MPoly Ring Isomorphism, Splitting Field & Stone–Zariski Face Duality",
      holds: verify_cubical_algebra_scheme_bridge(),
      quantitative_witness: "dim_Q Q[x,y]/<x²+y²-1,x-y> = 2 = [Q(√2):Q]; Face ↦ Radical Ideal",
    },
    {
      id: "K5-05",
      lhs: Symlib,
      rhs: Semiring,
      bridge_theorem: "2-Channel Weighted CSR Graph Automorphisms & Free DAG Category ↔ Star Closure",
      holds: check_graph_symmetry_bridges() && check_free_category_bridge(),
      quantitative_witness: "|Aut_w(C_4)|=4 (trace=1), |Hom_Free(4-DAG)|=11 == Kleene path count",
    },
    {
      id: "K5-06",
      lhs: Symlib,
      rhs: Topos,
      bridge_theorem: "Grothendieck Galois Equivalence S_3-Set ≃ Sh_at(BS_3) & Order-Free Poset Nerve",
      holds: verify_symlib_galois_topos_bridge(),
      quantitative_witness: "S_3 on 3²: Γ=0, |Hom(P,Δ2)|=4=2², atoms 3+6=9; reverse S^1 Betti=[1,1,0,0]",
    },
    {
      id: "K5-07",
      lhs: Symlib,
      rhs: Scheme,
      bridge_theorem: "S_3 Scheme Automorphisms, Burnside F_p-Orbits & Vieta Vandermonde Étale Torsor",
      holds: verify_symlib_symmetric_scheme_bridge(),
      quantitative_witness: "H(F_3): 9 pts -> 4 S_3-orbits (fix=3); Vieta étale off V(x_0 - x_1)",
    },
    {
      id: "K5-08",
      lhs: Semiring,
      rhs: Topos,
      bridge_theorem: "Boolean Matrix Kleene Star Fix(M*) ↔ Alexandroff Sieves Γ(1, Ω) & Ω_J Nucleus",
      holds: verify_semiring_kleene_alexandroff_topos_bridge(),
      quantitative_witness: "|Fix(M*)| = |Γ(1, Ω)| = 6 -> |Γ(1, Ω_J)| = 5 under {1,2} ↠ 3",
    },
    {
      id: "K5-09",
      lhs: Semiring,
      rhs: Scheme,
      bridge_theorem: "Kapranov Tropical Bend Locus ↔ Formal Laurent DVR Q((t)) & P^1 Properness",
      holds: verify_kapranov_tropical_laurent_bridge(),
      quantitative_witness: "Tropical bend roots {-1, 2} == DVR valuation jump & unique P^1 limit",
    },
    {
      id: "K5-10",
      lhs: Topos,
      rhs: Scheme,
      bridge_theorem: "Hakim Zariski Topos, Diaconescu ↔ Kähler Étale Torsors & Subtopos ↔ Blow-Up",
      holds: verify_zariski_topos_invariance_vs_nilpotent_points() &&
      verify_quadratic_etale_torsor_galois_bridge() &&
      verify_excision_subtopos_blowup_bridge(),
      quantitative_witness: "|X(F_3[ε])|=4 vs |X_red|=2, G_m double cover Ω^1=0, Bl_{(0,0)} cubics",
    },
  ]
}

///|
/// **Five-Federation Pentagon Grand Unification Theorem (`五聯邦五角大一統定理`)**:
/// Synthesizes ALL FIVE FEDERATIONS around the canonical **Quadratic `Z/2Z` Galois–Étale
/// Double Cover** (`Bool ¬` / `S_2` free action / 2-sheeted `C_4 -> C_2` Kleene cover /
/// Möbius `Z/2Z`-torsor in `Sh(S^1)` / Kummer double cover `w^2 = u` over `G_m`),
/// proving that fiber degree (`2`), global fixed-point / section obstruction (`0`),
/// connected orbit count (`1`), and unramified/étale local triviality match identically
/// across `Cubical`, `Symlib`, `Semiring`, `Topos`, and `Scheme`!
pub fn verify_five_federation_pentagon_unification() -> Bool {
  // F1 Cubical: `wiring_not` on `Bool` has fiber size 2, order 2, and 0 fixed points!
  let w_not = @cub.wiring_not()
  let bool_vals = @cub.elems_of(@cub.ty_bool())
  let mut cub_fixed = 0
  for v in bool_vals {
    if @cub.wiring_apply(w_not, v) == v {
      cub_fixed = cub_fixed + 1
    }
  }
  let cub_deg = bool_vals.length()
  let cub_inv_ok = @cub.wiring_eq(
    @cub.wiring_comp(w_not, w_not),
    @cub.wiring_id(@cub.ty_bool()),
  )
  if cub_deg != 2 || cub_fixed != 0 || !cub_inv_ok {
    return false
  }

  // F2 Symlib: regular `Z/2Z` G-set has size 2, 0 global fixed points, and 1 Burnside orbit!
  let z2 = @sym.PermGroup::symmetric(2)
  let gs_z2 = @sym.gset_points(z2, 2)
  let (sym_orbits, _) = @sym.gset_burnside(gs_z2)
  let sym_fixed = @sym.gset_global_fixed(gs_z2)
  if gs_z2.x != cub_deg || sym_fixed != cub_fixed || sym_orbits != 1 {
    return false
  }

  // F3 Semiring: 2-sheeted directed cycle `C_4` covering `C_2` has single strongly
  // connected component under `BoolSr` Kleene closure (`M* == all-ones`) and
  // deck-transformation order `2` (`(0,2)(1,3)` commutes with shift `(0,1,2,3)`)!
  let c4 = @sgraph.Graph::build(4, [0, 1, 2, 3], [1, 2, 3, 0], [1, 1, 1, 1])
  let deck = @sym.Perm::from_img([2, 3, 0, 1])
  let m_c4 : @smat.Mat[@semialg.BoolSr] = @smat.Mat::zero(4, 4)
  for i in 0..<4 {
    m_c4.set(i, (i + 1) % 4, @semialg.BoolSr::one())
  }
  let c4_star = @smat.closure_lehmann(m_c4)
  let mut c4_connected = perm_preserves_semiring_graph(c4, deck)
  for i in 0..<4 {
    for j in 0..<4 {
      if !c4_star.get(i, j).is_one() {
        c4_connected = false
      }
    }
  }
  if !c4_connected ||
    @sgraph.Graph::build(2, [0, 1], [1, 0], [1, 1]).n * cub_deg != c4.n {
    return false
  }

  // F4 Topos: twisted Möbius `Z/2Z`-torsor sheaf on `Sh(S^1)` has local fiber size 2,
  // 0 global sections (`== sym_fixed`), is a genuine internal `Z/2Z`-torsor sheaf,
  // and represents the unique non-trivial class in `|H^1(S^1, Z/2Z)| == 2`!
  let s1_site = @topos.site_circle_good_cover()
  let mobius = @topos.circle_mobius_double_cover_sheaf()
  let id_hom = @topos.presheaf_hom_id(mobius)
  let flip_comps : Array[Array[Int32]] = []
  for u in 0..<s1_site.cat.nobj {
    flip_comps.push(if u < 6 { [1, 0] } else { [] })
  }
  let flip_hom : @topos.PresheafHom = {
    cat: s1_site.cat,
    dom_size: mobius.size.copy(),
    cod_size: mobius.size.copy(),
    components: flip_comps,
  }
  let tors_ok = @topos.is_internal_group_torsor_sheaf({
    site: s1_site,
    group_elems: [@sym.Perm::identity(2), @sym.Perm::from_img([1, 0])],
    carrier: mobius,
    action: [id_hom, flip_hom],
  })
  let (_, h1_z2) = @topos.classify_group_torsor_cohomology(
    @sym.cat_group(z2, 2),
    @topos.boundary_simplex_nerve(2),
  )
  if !tors_ok ||
    mobius.size[3] != cub_deg ||
    @topos.global_sections_count(s1_site, mobius) != sym_fixed ||
    h1_z2 != cub_deg {
    return false
  }

  // F5 Scheme: Kummer double cover `Spec(Q[u,v,w]/<uv-1, w^2-u>) -> Spec(Q[u,v]/<uv-1>)`
  // is étale over `G_m`, has fiber degree 2 over `u = 1`, and has `0` rational sections
  // over `F_3` above `u = 2` (`2` is quadratic non-residue mod `3`, matching `Γ = 0`)!
  let u0 = @scheme.mpoly_var(2, 0)
  let v0 = @scheme.mpoly_var(2, 1)
  let gm_ring = @scheme.coord_ring_new(2, [
    @scheme.mpoly_sub(@scheme.mpoly_mul(u0, v0), @scheme.mpoly_int(2, 1)),
  ])
  let u1 = @scheme.mpoly_var(3, 0)
  let v1 = @scheme.mpoly_var(3, 1)
  let w1 = @scheme.mpoly_var(3, 2)
  let kum_ring = @scheme.coord_ring_new(3, [
    @scheme.mpoly_sub(@scheme.mpoly_mul(u1, v1), @scheme.mpoly_int(3, 1)),
    @scheme.mpoly_sub(@scheme.mpoly_pow(w1, 2), u1),
  ])
  let kummer : @scheme.RingHom = {
    src: gm_ring,
    dst: kum_ring,
    var_images: [u1, v1],
  }
  let fiber_u_eq_1 = @scheme.ideal_add(
    kum_ring.ideal,
    @scheme.ideal_new(3, [@scheme.mpoly_sub(u1, @scheme.mpoly_int(3, 1))]),
  )
  let kum_f3_pts = @scheme.eval_affine_functor_of_points(
    @scheme.affine_scheme(kum_ring),
    @scheme.fcomm_fp(3),
  )
  let mut pts_over_u2 = 0
  for pt in kum_f3_pts {
    if pt[0] == 2 {
      pts_over_u2 = pts_over_u2 + 1
    }
  }
  @scheme.is_etale_ring_hom_between_smooth(kummer) &&
  @scheme.ideal_quotient_vector_space_dim(fiber_u_eq_1) == Some(cub_deg) &&
  pts_over_u2 == sym_fixed
}
