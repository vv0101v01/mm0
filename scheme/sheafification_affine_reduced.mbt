///|
// Scheme Pillar — Layer 2: Coordinate Algebras, Ring Homomorphisms, Zariski
// Localization & Structure Sheaf Sections O_{Spec(A)}(D(f)), Partition-of-Unity
// Algebraic Sheafification / Gluing, Quasi-Coherent Module Sheafification M~,
// and Reduced Schemes (Nilradical Witness & X_red Universal Property).

///|
/// Finitely presented commutative `Q`-algebra `A = Q[x_0, ..., x_{nvars-1}] / ideal`.
pub(all) struct CoordRing {
  nvars : Int32
  ideal : Ideal
} derive(Debug, Eq)

///|
pub extend CoordRing with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend CoordRing with Eq::{not_equal, equal}

///|
/// Commutative `Q`-algebra homomorphism `φ : src -> dst` specified by the images
/// `var_images[i] ∈ dst` of each generator `x_i` of `src` (contravariantly
/// defining an affine scheme morphism `Spec(dst) -> Spec(src)`!).
pub(all) struct RingHom {
  src : CoordRing
  dst : CoordRing
  var_images : Array[MPoly]
} derive(Debug, Eq)

///|
pub extend RingHom with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend RingHom with Eq::{not_equal, equal}

///|
/// A section `num / den_base^{exp}` of the structure sheaf `O_{Spec(A)}(D(den_base))`
/// (in the localized ring `A_{den_base}`).
pub(all) struct LocalizedSection {
  num : MPoly
  den_base : MPoly
  exp : Int32
} derive(Debug, Eq)

///|
pub extend LocalizedSection with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend LocalizedSection with Eq::{not_equal, equal}

///|
/// Finitely presented `A`-module `M = coker(A^{ ncols } ->^{rel_matrix} A^{ nrows })`
/// whose localization `M_f` models the quasi-coherent sheaf `M~(D(f))`.
pub(all) struct QuasiCoherentModule {
  ring : CoordRing
  nrows : Int32
  ncols : Int32
  rel_matrix : Array[Array[MPoly]]
}

///|
/// Affine scheme `Spec(ring)`.
pub(all) struct AffineScheme {
  ring : CoordRing
} derive(Debug, Eq)

///|
pub extend AffineScheme with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend AffineScheme with Eq::{not_equal, equal}

///|
/// Construct `CoordRing` `Q[x_0..x_{nvars-1}] / <gens>`.
pub fn coord_ring_new(nvars : Int32, gens : Array[MPoly]) -> CoordRing {
  { nvars, ideal: ideal_new(nvars, gens), }
}

///|
/// Canonical coset representative `nf_I(f)` in `ring`.
pub fn coord_ring_nf(ring : CoordRing, f : MPoly) -> MPoly {
  ideal_normal_form(ring.ideal, f)
}

///|
/// Equality of polynomial representatives in `ring` (`f - g ∈ ring.ideal`).
pub fn coord_ring_eq(ring : CoordRing, f : MPoly, g : MPoly) -> Bool {
  ideal_contains(ring.ideal, mpoly_sub(f, g))
}

///|
/// Verify well-definedness of `hom : src -> dst`: every generator `g ∈ src.ideal`
/// maps into `dst.ideal` (`g(var_images) ∈ dst.ideal`).
pub fn ring_hom_is_valid(hom : RingHom) -> Bool {
  guard hom.var_images.length() == hom.src.nvars else { return false }
  for img in hom.var_images {
    if img.nvars != hom.dst.nvars {
      return false
    }
  }
  for g in hom.src.ideal.rgb.gens {
    let mapped = mpoly_subst(g, hom.dst.nvars, hom.var_images)
    if !ideal_contains(hom.dst.ideal, mapped) {
      return false
    }
  }
  true
}

///|
/// Apply `hom` to an element `f ∈ hom.src` (returned in canonical normal form in `hom.dst`).
pub fn ring_hom_apply(hom : RingHom, f : MPoly) -> MPoly {
  coord_ring_nf(hom.dst, mpoly_subst(f, hom.dst.nvars, hom.var_images))
}

///|
/// Identity ring homomorphism `id_A : A -> A`.
pub fn ring_hom_id(ring : CoordRing) -> RingHom {
  let imgs : Array[MPoly] = []
  for i in 0..<ring.nvars {
    imgs.push(mpoly_var(ring.nvars, i))
  }
  { src: ring, dst: ring, var_images: imgs, }
}

///|
/// Composition `psi ∘ phi : A -> C` of `phi : A -> B` and `psi : B -> C`
/// (contravariantly `Spec(C) -> Spec(B) -> Spec(A)`).
pub fn ring_hom_compose(phi : RingHom, psi : RingHom) -> RingHom {
  guard phi.dst == psi.src else {
    abort("ring_hom_compose: intermediate ring mismatch")
  }
  let imgs : Array[MPoly] = []
  for i in 0..<phi.src.nvars {
    imgs.push(ring_hom_apply(psi, phi.var_images[i]))
  }
  { src: phi.src, dst: psi.dst, var_images: imgs, }
}

///|
/// Compute the exact algebraic kernel ideal `ker(hom) ⊆ Q[x_0..x_{src.nvars-1}]`
/// (presenting the **scheme-theoretic image closure** of `Spec(dst) -> Spec(src)`!)
/// by eliminating `y_0..y_{dst.nvars-1}` from `<dst.ideal(y), x_i - hom(x_i)(y)>`!
pub fn ring_hom_kernel(hom : RingHom) -> Ideal {
  let ny = hom.dst.nvars
  let nx = hom.src.nvars
  let total_n = ny + nx
  let gens : Array[MPoly] = []
  for g in hom.dst.ideal.rgb.gens {
    gens.push(mpoly_extend_vars(g, nx, false))
  }
  for i in 0..<nx {
    let xi = mpoly_var(total_n, ny + i)
    let phi_i = mpoly_extend_vars(hom.var_images[i], nx, false)
    gens.push(mpoly_sub(xi, phi_i))
  }
  ideal_eliminate_first_k(ideal_new(total_n, gens), ny)
}

///|
/// Decide whether `hom : src -> dst` is **surjective** as a `Q`-algebra homomorphism
/// (geometrically: `Spec(dst) -> Spec(src)` is a **Closed Immersion**!!):
/// holds iff every coordinate generator `y_j` of `dst` lies in the subalgebra
/// `im(hom) + dst.ideal`, decided by Gröbner elimination of `x` in
/// `<src.ideal(x), dst.ideal(y), x_i - hom(x_i)(y)>` with `Elim(nx)`?
/// Even better: in `Q[y_0..y_{ny-1}, x_0..x_{nx-1}]` with `Elim(ny)` (`y > x`),
/// `y_j ∈ Q[hom(x)] + dst.ideal` iff `nf_{Elim(ny)}(y_j)` contains ONLY `x`-variables!!
/// (Shannon–Sweedler Subalgebra Membership Theorem!)
pub fn ring_hom_is_surjective(hom : RingHom) -> Bool {
  guard ring_hom_is_valid(hom) else { return false }
  let ny = hom.dst.nvars
  let nx = hom.src.nvars
  if ny == 0 {
    return true
  }
  let total_n = ny + nx
  // Variables `0 ..< ny` are `y`; variables `ny ..< ny + nx` are `x`!
  let tag_gens : Array[MPoly] = []
  for g in hom.dst.ideal.rgb.gens {
    tag_gens.push(mpoly_extend_vars(g, nx, false))
  }
  for h in hom.src.ideal.rgb.gens {
    tag_gens.push(mpoly_extend_vars(h, ny, true))
  }
  for i in 0..<nx {
    let xi = mpoly_var(total_n, ny + i)
    let phi_i_in_y = mpoly_extend_vars(hom.var_images[i], nx, false)
    tag_gens.push(mpoly_sub(phi_i_in_y, xi))
  }
  let gb = reduced_groebner_basis(total_n, tag_gens, Elim(ny))
  for j in 0..<ny {
    let yj = mpoly_var(total_n, j)
    let rem = mpoly_reduce(yj, gb.gens, Elim(ny))
    for t in rem.terms {
      for v in 0..<ny {
        if t.exps[v] > 0 {
          return false
        }
      }
    }
  }
  true
}

///|
/// Exact equality of two sections `s1 = a1 / f^{e1}` and `s2 = a2 / f^{e2}`
/// in the localized structure sheaf `O_{Spec(ring)}(D(f)) = ring_f` (allowing
/// compatible denominators on `D(s1.den_base) == D(s2.den_base)`):
/// holds iff `a1 * g^{e2} - a2 * f^{e1} ∈ (ring.ideal : (f * g)^∞)`!
pub fn localized_section_eq(
  ring : CoordRing,
  s1 : LocalizedSection,
  s2 : LocalizedSection,
) -> Bool {
  let f = s1.den_base
  let g = s2.den_base
  // Verify same open set D(f) == D(g) in Spec(ring)!
  if !principal_open_subset(ring, f, g) || !principal_open_subset(ring, g, f) {
    return false
  }
  let lhs = mpoly_mul(s1.num, mpoly_pow(g, s2.exp))
  let rhs = mpoly_mul(s2.num, mpoly_pow(f, s1.exp))
  let diff = mpoly_sub(lhs, rhs)
  let sat = ideal_saturate(ring.ideal, mpoly_mul(f, g))
  ideal_contains(sat, diff)
}

///|
/// Decide Zariski open inclusion `D(sub_f) ⊆ D(sup_f)` in `Spec(ring)`:
/// holds by Hilbert's Nullstellensatz iff `sub_f ∈ √(ring.ideal + <sup_f>)`!
pub fn principal_open_subset(
  ring : CoordRing,
  sub_f : MPoly,
  sup_f : MPoly,
) -> Bool {
  let j = ideal_add(ring.ideal, ideal_new(ring.nvars, [sup_f]))
  ideal_radical_contains(j, sub_f)
}

///|
/// Enumerate all exponent vectors in `N^{nvars}` of total degree `<= max_deg`.
fn all_monomials_upto_deg(
  nvars : Int32,
  max_deg : Int32,
) -> Array[Array[Int32]] {
  let out : Array[Array[Int32]] = []
  let cur = Array::make(nvars, 0)
  fn build(pos : Int32, rem_deg : Int32) -> Unit {
    if pos == nvars {
      out.push(cur.copy())
      return
    }
    for e in 0..<(rem_deg + 1) {
      cur[pos] = e
      build(pos + 1, rem_deg - e)
    }
  }
  build(0, max_deg)
  out
}

///|
/// Solve the `ring`-linear relation `Σ_{i=0}^{r-1} c_i(x) * generators[i] ≡ target (mod ring.ideal)`
/// with `deg(c_i) <= max_deg` using Macaulay's canonical normal-form basis and
/// exact rational Gauss–Jordan elimination (`@exactalg.qrows_rref`)!
pub fn solve_ideal_linear_combination(
  ring : CoordRing,
  generators : Array[MPoly],
  target : MPoly,
  max_deg~ : Int32 = 4,
) -> Array[MPoly]? {
  let n = ring.nvars
  let target_nf = coord_ring_nf(ring, target)
  if mpoly_is_zero(target_nf) {
    let zeros : Array[MPoly] = []
    for _ in 0..<generators.length() {
      zeros.push(mpoly_zero(n))
    }
    return Some(zeros)
  }
  for deg_cap in 0..<(max_deg + 1) {
    let cand_mons = all_monomials_upto_deg(n, deg_cap)
    // Build column normal forms `col_nfs[col]` for each `(gen_idx, mon_idx)`.
    let col_nfs : Array[MPoly] = []
    let col_meta : Array[(Int32, Array[Int32])] = []
    let basis_exps : Array[Array[Int32]] = []
    fn record_exps(poly : MPoly) -> Unit {
      for t in poly.terms {
        let mut seen = false
        for e in basis_exps {
          if e == t.exps {
            seen = true
            break
          }
        }
        if !seen {
          basis_exps.push(t.exps.copy())
        }
      }
    }
    record_exps(target_nf)
    for g_idx in 0..<generators.length() {
      for m_exps in cand_mons {
        let mon_poly : MPoly = {
          nvars: n,
          terms: [{ coeff: @exactalg.rat_one(), exps: m_exps.copy(), }],
        }
        let nf = coord_ring_nf(ring, mpoly_mul(mon_poly, generators[g_idx]))
        record_exps(nf)
        col_nfs.push(nf)
        col_meta.push((g_idx, m_exps))
      }
    }
    let nrows = basis_exps.length()
    let ncols = col_nfs.length()
    if ncols == 0 {
      continue
    }
    let aug : Array[Array[@exactalg.Rat]] = []
    for r in 0..<nrows {
      let row = Array::make(ncols + 1, @exactalg.rat_zero())
      let row_e = basis_exps[r]
      for c in 0..<ncols {
        for t in col_nfs[c].terms {
          if t.exps == row_e {
            row[c] = t.coeff
            break
          }
        }
      }
      for t in target_nf.terms {
        if t.exps == row_e {
          row[ncols] = t.coeff
          break
        }
      }
      aug.push(row)
    }
    let rref = @exactalg.qrows_rref(aug, ncols + 1)
    let mut consistent = true
    for p_col in rref.pivots {
      if p_col == ncols {
        consistent = false
        break
      }
    }
    if consistent {
      let sol = Array::make(ncols, @exactalg.rat_zero())
      for r in 0..<rref.pivots.length() {
        sol[rref.pivots[r]] = rref.rows[r][ncols]
      }
      let coeffs : Array[Array[MTerm]] = []
      for _ in 0..<generators.length() {
        coeffs.push([])
      }
      for c in 0..<ncols {
        if !@exactalg.rat_is_zero(sol[c]) {
          let (g_idx, m_exps) = col_meta[c]
          coeffs[g_idx].push({ coeff: sol[c], exps: m_exps.copy(), })
        }
      }
      let out : Array[MPoly] = []
      for g_idx in 0..<generators.length() {
        out.push(mpoly_from_terms(n, coeffs[g_idx]))
      }
      return Some(out)
    }
  }
  None
}

///|
/// Restrict a structure-sheaf section `sec ∈ O(D(sec.den_base))` to a smaller
/// principal open `D(sub_h) ⊆ D(sec.den_base)`!
pub fn restrict_localized_section(
  ring : CoordRing,
  sec : LocalizedSection,
  sub_h : MPoly,
) -> LocalizedSection? {
  if !principal_open_subset(ring, sub_h, sec.den_base) {
    return None
  }
  if sec.exp == 0 {
    return Some({ num: coord_ring_nf(ring, sec.num), den_base: sub_h, exp: 0, })
  }
  // Find `m >= 1` and `c ∈ Q[x]` such that `c * sec.den_base ≡ sub_h^m (mod ring.ideal)`.
  for m in 1..<6 {
    let hm = mpoly_pow(sub_h, m)
    match solve_ideal_linear_combination(ring, [sec.den_base], hm, max_deg=4) {
      Some(cs) => {
        let c = cs[0]
        let new_num = coord_ring_nf(
          ring,
          mpoly_mul(sec.num, mpoly_pow(c, sec.exp)),
        )
        return Some({ num: new_num, den_base: sub_h, exp: m * sec.exp, })
      }
      None => ()
    }
  }
  None
}

///|
/// Verify whether `{ D(cover_fs[i]) }` is a valid Zariski open cover of `Spec(ring)`:
/// holds iff `1 ∈ √(ring.ideal + <cover_fs>)`!
pub fn is_zariski_open_cover(ring : CoordRing, cover_fs : Array[MPoly]) -> Bool {
  principal_open_subset(
    ring,
    mpoly_int(ring.nvars, 1),
    mpoly_int(ring.nvars, 0),
  ) ||
  ideal_radical_contains(
    ideal_add(ring.ideal, ideal_new(ring.nvars, cover_fs)),
    mpoly_int(ring.nvars, 1),
  )
}

///|
/// **Grothendieck's Structure Sheaf Gluing / Sheafification Algorithm on `Spec(ring)`**:
/// Given a Zariski open cover `{ D(f_i) }_{i=0}^{r-1}` of `Spec(ring)` and local
/// sections `s_i = a_i / f_i^{e_i} ∈ O(D(f_i))`:
///   1. Verifies `{ D(f_i) }` covers `Spec(ring)`;
///   2. Verifies pairwise overlap compatibility `(s_i)|_{D(f_i f_j)} == (s_j)|_{D(f_i f_j)}`;
///   3. Clears torsion powers `(f_i f_j)^N (a_i f_j^{e_j} - a_j f_i^{e_i}) ∈ ring.ideal`,
///      sets `M = max_i(e_i) + N`, solves the Partition of Unity
///      `Σ_i c_i * f_i^M ≡ 1 (mod ring.ideal)`, and constructs the UNIQUE global
///      section `s = Σ_i c_i * a_i * f_i^{M - e_i} ∈ A = O(Spec(ring))` whose
///      restriction to EVERY `D(f_i)` equals `s_i`!
pub fn glue_zariski_structure_sections(
  ring : CoordRing,
  cover_fs : Array[MPoly],
  sections : Array[LocalizedSection],
) -> MPoly? {
  let r = cover_fs.length()
  guard r == sections.length() && r > 0 else { return None }
  if !is_zariski_open_cover(ring, cover_fs) {
    return None
  }
  for i in 0..<r {
    if sections[i].den_base != cover_fs[i] {
      return None
    }
  }
  // Check overlap compatibility and find uniform annihilating exponent `n_ann`.
  let mut max_exp = 0
  for s in sections {
    if s.exp > max_exp {
      max_exp = s.exp
    }
  }
  let mut n_ann = 0
  for i in 0..<r {
    for j in (i + 1)..<r {
      let fij = mpoly_mul(cover_fs[i], cover_fs[j])
      let cross = mpoly_sub(
        mpoly_mul(sections[i].num, mpoly_pow(cover_fs[j], sections[j].exp)),
        mpoly_mul(sections[j].num, mpoly_pow(cover_fs[i], sections[i].exp)),
      )
      // Must lie in saturation `(I : fij^∞)`!
      let sat = ideal_saturate(ring.ideal, fij)
      if !ideal_contains(sat, cross) {
        return None
      }
      let mut found_pow = -1
      for k in 0..<6 {
        if ideal_contains(ring.ideal, mpoly_mul(mpoly_pow(fij, k), cross)) {
          found_pow = k
          break
        }
      }
      if found_pow < 0 {
        return None
      }
      if found_pow > n_ann {
        n_ann = found_pow
      }
    }
  }
  // Solve Partition of Unity `Σ_i c_i * f_i^m_pow ≡ 1 (mod ring.ideal)` for m_pow >= max_exp + n_ann.
  for extra in 0..<4 {
    let m_pow = max_exp + n_ann + extra
    let pow_fs : Array[MPoly] = []
    for i in 0..<r {
      pow_fs.push(mpoly_pow(cover_fs[i], m_pow))
    }
    match
      solve_ideal_linear_combination(
        ring,
        pow_fs,
        mpoly_int(ring.nvars, 1),
        max_deg=5,
      ) {
      Some(cs) => {
        let mut global_s = mpoly_zero(ring.nvars)
        for i in 0..<r {
          let lifted_i = mpoly_mul(
            sections[i].num,
            mpoly_pow(cover_fs[i], m_pow - sections[i].exp),
          )
          global_s = mpoly_add(global_s, mpoly_mul(cs[i], lifted_i))
        }
        let global_nf = coord_ring_nf(ring, global_s)
        // Double-check that global_nf restricts to sections[i] on every D(f_i)!
        let mut all_match = true
        for i in 0..<r {
          let global_as_sec : LocalizedSection = {
            num: global_nf,
            den_base: cover_fs[i],
            exp: 0,
          }
          if !localized_section_eq(ring, global_as_sec, sections[i]) {
            all_match = false
            break
          }
        }
        if all_match {
          return Some(global_nf)
        }
      }
      None => ()
    }
  }
  None
}

///|
/// Quasi-coherent module localization `M~(D(f)) = M_f`: localizes the coordinate
/// ring `A` to `A_f = Q[x, u] / <I_A, u * f - 1>` and pushes forward the
/// presentation matrix `rel_matrix` to `A_f`!
pub fn localize_quasicoherent_module(
  m : QuasiCoherentModule,
  f : MPoly,
) -> QuasiCoherentModule {
  let n = m.ring.nvars
  let u_var = mpoly_var(n + 1, n)
  let f_ext = mpoly_extend_vars(f, 1, false)
  let gens : Array[MPoly] = [
    mpoly_sub(mpoly_mul(u_var, f_ext), mpoly_int(n + 1, 1)),
  ]
  for g in m.ring.ideal.rgb.gens {
    gens.push(mpoly_extend_vars(g, 1, false))
  }
  let loc_ring = coord_ring_new(n + 1, gens)
  let loc_mat : Array[Array[MPoly]] = []
  for r in 0..<m.nrows {
    let row : Array[MPoly] = []
    for c in 0..<m.ncols {
      row.push(
        coord_ring_nf(loc_ring, mpoly_extend_vars(m.rel_matrix[r][c], 1, false)),
      )
    }
    loc_mat.push(row)
  }
  { ring: loc_ring, nrows: m.nrows, ncols: m.ncols, rel_matrix: loc_mat, }
}

///|
/// Construct `Spec(ring)`.
pub fn affine_scheme(ring : CoordRing) -> AffineScheme {
  { ring, }
}

///|
/// Search for an explicit nonzero **Nilpotent Witness** `w ∈ A` (`w ∉ I` and
/// `w^m ∈ I` for some `m >= 2`): returns `None` iff `Spec(ring)` is **Reduced**!
pub fn affine_nilpotent_witness(x : AffineScheme) -> MPoly? {
  let rad = ideal_radical(x.ring.ideal)
  for g in rad.rgb.gens {
    if !ideal_contains(x.ring.ideal, g) {
      return Some(coord_ring_nf(x.ring, g))
    }
  }
  None
}

///|
/// Decide whether `x = Spec(A)` is a **Reduced Scheme** (`√I_A == I_A`, i.e.,
/// `O_X` has no nonzero nilpotent elements!).
pub fn affine_is_reduced(x : AffineScheme) -> Bool {
  ideal_eq(ideal_radical(x.ring.ideal), x.ring.ideal)
}

///|
/// Construct the **Associated Reduced Scheme** `X_red = Spec(A / √I_A)` together
/// with its canonical closed immersion ring surjection `A ->> A / √I_A`
/// (`X_red ↪ X`)!
pub fn affine_reduction(x : AffineScheme) -> (AffineScheme, RingHom) {
  let rad = ideal_radical(x.ring.ideal)
  let red_ring : CoordRing = { nvars: x.ring.nvars, ideal: rad, }
  let imgs : Array[MPoly] = []
  for i in 0..<x.ring.nvars {
    imgs.push(coord_ring_nf(red_ring, mpoly_var(x.ring.nvars, i)))
  }
  ({ ring: red_ring, }, { src: x.ring, dst: red_ring, var_images: imgs, })
}

///|
/// Theorem (Universal Property of Reduced Scheme `X_red ↪ X`):
/// For ANY morphism `Spec(B) -> Spec(A)` (given by `phi : A -> B`) whose source
/// `Spec(B)` is reduced, `phi` annihilates `√I_A` and therefore factors UNIQUELY
/// through `A ->> A / √I_A` (`X_red ↪ X`)!
pub fn verify_affine_reduction_universal_property(
  x : AffineScheme,
  reduced_source : AffineScheme,
  phi : RingHom,
) -> Bool {
  guard affine_is_reduced(reduced_source) &&
    phi.src == x.ring &&
    phi.dst == reduced_source.ring &&
    ring_hom_is_valid(phi) else {
    return false
  }
  let (x_red, iota_hom) = affine_reduction(x)
  if !affine_is_reduced(x_red) || !ring_hom_is_surjective(iota_hom) {
    return false
  }
  let factored : RingHom = {
    src: x_red.ring,
    dst: reduced_source.ring,
    var_images: phi.var_images.copy(),
  }
  if !ring_hom_is_valid(factored) {
    return false
  }
  let composed = ring_hom_compose(iota_hom, factored)
  for i in 0..<x.ring.nvars {
    if !coord_ring_eq(
        reduced_source.ring,
        composed.var_images[i],
        phi.var_images[i],
      ) {
      return false
    }
  }
  true
}
