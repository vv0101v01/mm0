///|
// Scheme Pillar — Round 2 Structural Derivations (第 2 輪數學結構導出演算法與定理):
//   1. Module of Kähler Differentials `Ω^1_{B/A}` (`QuasiCoherentModule`),
//      Zeroth Fitting Ideals `Fitt_0`, Unramified / Étale Morphism Criteria,
//      Jacobian Singular Locus `Sing(X)` & Tjurina Singularity Number `τ(X)`
//   2. Macaulay–Taylor Graded Gröbner Hilbert Polynomial `P_X(t) ∈ Q[t]`,
//      Projective Dimension, Projective Degree `deg(X)` & Arithmetic Genus `p_a(X)`
//      (covering arbitrary-codimension subschemes such as the Twisted Cubic in `P^3`!)
//   3. Blow-Up Strict Transform `Bl_{(0,0)}(A^2)` via Gröbner Saturation &
//      One-Step Curve Desingularization (Nodal vs Cuspidal Exceptional Fibers)
//   4. Quadratic Galois Finite Fields `F_{p^2}` & Arithmetic Frobenius Zeta
//      Point-Counting Descent (`h_X(F_p)` vs `h_X(F_{p^2})`)

///|
/// Hilbert-polynomial geometric invariants of a projective subscheme
/// `X = V_+(homog_ideal) ⊆ P^n_Q`.
pub(all) struct ProjectiveHilbertReport {
  ambient_dim : Int32
  projective_dim : Int32
  degree : Int32
  arithmetic_genus : Int32
  hilbert_poly : @exactalg.QPoly
  matches_hilbert_function : Bool
}

///|
/// Report of blowing up an affine plane curve `V(f(x, y)) ⊆ A^2_Q` at `(0, 0)`.
pub(all) struct PlaneCurveBlowupReport {
  origin_was_singular : Bool
  strict_transform : Scheme
  strict_transform_is_smooth : Bool
  exceptional_fiber_length : Int32
  exceptional_fiber_is_reduced : Bool
}

// =============================================================================
// 1. Kähler Differentials `Ω^1_{B/A}`, Fitting Ideals, Smoothness & Étale Maps
// =============================================================================

///|
/// Exact determinant of a square `k × k` matrix over `MPoly` (`nvars` variables)
/// computed by Laplace cofactor recursion (used for Jacobian / Fitting minors).
fn mpoly_square_det(nvars : Int32, mat : Array[Array[MPoly]]) -> MPoly {
  let k = mat.length()
  if k == 0 {
    return mpoly_int(nvars, 1)
  }
  if k == 1 {
    return mat[0][0]
  }
  if k == 2 {
    return mpoly_sub(
      mpoly_mul(mat[0][0], mat[1][1]),
      mpoly_mul(mat[0][1], mat[1][0]),
    )
  }
  let mut acc = mpoly_zero(nvars)
  for col in 0..<k {
    let entry = mat[0][col]
    if mpoly_is_zero(entry) {
      continue
    }
    let sub : Array[Array[MPoly]] = []
    for r in 1..<k {
      let row : Array[MPoly] = []
      for c in 0..<k {
        if c != col {
          row.push(mat[r][c])
        }
      }
      sub.push(row)
    }
    let term = mpoly_mul(entry, mpoly_square_det(nvars, sub))
    acc = if col % 2 == 0 { mpoly_add(acc, term) } else { mpoly_sub(acc, term) }
  }
  acc
}

///|
/// Enumerate all `r × r` minors of an `nrows × ncols` `MPoly` matrix.
fn mpoly_matrix_minors(
  nvars : Int32,
  mat : Array[Array[MPoly]],
  nrows : Int32,
  ncols : Int32,
  r : Int32,
) -> Array[MPoly] {
  if r <= 0 {
    return [mpoly_int(nvars, 1)]
  }
  if r > nrows || r > ncols {
    return []
  }
  let out : Array[MPoly] = []
  let row_sel = Array::make(r, 0)
  let col_sel = Array::make(r, 0)
  fn choose_cols(c_pos : Int32, c_start : Int32) -> Unit {
    if c_pos == r {
      let sub : Array[Array[MPoly]] = []
      for i in 0..<r {
        let row : Array[MPoly] = []
        for j in 0..<r {
          row.push(mat[row_sel[i]][col_sel[j]])
        }
        sub.push(row)
      }
      let det = mpoly_square_det(nvars, sub)
      if !mpoly_is_zero(det) {
        out.push(det)
      }
      return
    }
    for c in c_start..<(ncols - (r - c_pos) + 1) {
      col_sel[c_pos] = c
      choose_cols(c_pos + 1, c + 1)
    }
  }
  fn choose_rows(r_pos : Int32, r_start : Int32) -> Unit {
    if r_pos == r {
      choose_cols(0, 0)
      return
    }
    for rw in r_start..<(nrows - (r - r_pos) + 1) {
      row_sel[r_pos] = rw
      choose_rows(r_pos + 1, rw + 1)
    }
  }
  choose_rows(0, 0)
  out
}

///|
/// Construct the **Relative Module of Kähler Differentials `Ω^1_{B/A}`** as an
/// explicit `QuasiCoherentModule` over `B = phi.dst` (`Spec(B) -> Spec(A)`):
///   `Ω^1_{B/A} = (⊕_{j=0}^{n-1} B · dy_j) / < dg_r (g_r ∈ I_B), d(phi(x_i)) (0 <= i < m) >`!
pub fn kahler_differentials_module(phi : RingHom) -> QuasiCoherentModule {
  guard ring_hom_is_valid(phi) else {
    abort("kahler_differentials_module: invalid RingHom")
  }
  let b = phi.dst
  let n = b.nvars
  // Collect all differential relation polynomials `h ∈ Q[y_0, ..., y_{n-1}]` whose `dh = 0`:
  let rel_polys : Array[MPoly] = []
  for g in b.ideal.rgb.gens {
    rel_polys.push(g)
  }
  for img in phi.var_images {
    rel_polys.push(img)
  }
  let ncols = rel_polys.length()
  let rel_matrix : Array[Array[MPoly]] = []
  for j in 0..<n {
    let row : Array[MPoly] = []
    for col in 0..<ncols {
      row.push(coord_ring_nf(b, mpoly_partial_deriv(rel_polys[col], j)))
    }
    rel_matrix.push(row)
  }
  { ring: b, nrows: n, ncols, rel_matrix, }
}

///|
/// Absolute Kähler differentials `Ω^1_{X / Spec(Q)}` of an affine `Q`-scheme `X`.
pub fn affine_kahler_differentials(aff : AffineScheme) -> QuasiCoherentModule {
  let q_ring = coord_ring_new(0, [])
  kahler_differentials_module({ src: q_ring, dst: aff.ring, var_images: [], })
}

///|
/// Compute the **`idx`-th Fitting Ideal `Fitt_idx(M) ⊆ Q[y_0, ..., y_{n-1}]`**
/// (lifted to the ambient polynomial ring by including `I_B`) of a finitely
/// presented `B`-module `M = coker(B^{ncols} ->^{rel_matrix} B^{nrows})`
/// (Eisenbud Definition 20.4):
///   - `idx < 0` => `I_B` (`0` in `B`);
///   - `idx >= nrows` => `<1>` (`B` itself);
///   - `0 <= idx < nrows` => generated by `I_B` together with all
///     `(nrows - idx) × (nrows - idx)` minors of `rel_matrix`.
pub fn quasicoherent_fitting_ideal(
  m : QuasiCoherentModule,
  idx : Int32,
) -> Ideal {
  let nvars = m.ring.nvars
  if ideal_is_unit(m.ring.ideal) {
    return m.ring.ideal
  }
  let minor_size = m.nrows - idx
  if minor_size <= 0 {
    return ideal_new(nvars, [mpoly_int(nvars, 1)])
  }
  let gens : Array[MPoly] = []
  for g in m.ring.ideal.rgb.gens {
    gens.push(g)
  }
  if minor_size <= m.nrows && minor_size <= m.ncols {
    for
      det in mpoly_matrix_minors(
        nvars,
        m.rel_matrix,
        m.nrows,
        m.ncols,
        minor_size,
      ) {
      gens.push(det)
    }
  }
  ideal_new(nvars, gens)
}

///|
/// Compute the **Zeroth Fitting Ideal `Fitt_0(M) ⊆ Q[y_0, ..., y_{n-1}]`**
/// of a finitely presented `B`-module `M`.
/// By Eisenbud Corollary 20.5, `Supp(M) = V(Fitt_0(M))`, and `M == 0 <=> Fitt_0(M) == <1>`!
pub fn quasicoherent_fitting_zero_ideal(m : QuasiCoherentModule) -> Ideal {
  quasicoherent_fitting_ideal(m, 0)
}

///|
/// Exact vanishing test `M == 0` for a finitely presented `QuasiCoherentModule`
/// via `1 ∈ Fitt_0(M)`!
pub fn quasicoherent_module_is_zero(m : QuasiCoherentModule) -> Bool {
  ideal_is_unit(quasicoherent_fitting_zero_ideal(m))
}

///|
/// Decide whether `phi : A -> B` (`Spec(B) -> Spec(A)`) is **Formally Unramified**
/// (finite type + `Ω^1_{B/A} == 0`, i.e. `Fitt_0(Ω^1_{B/A}) == <1>`)!
pub fn is_unramified_ring_hom(phi : RingHom) -> Bool {
  guard ring_hom_is_valid(phi) else { return false }
  quasicoherent_module_is_zero(kahler_differentials_module(phi))
}

///|
/// Compute the **Raw Jacobian Ideal `I + J_c(I) = Fitt_d(Ω^1_{X/Q})`** (preserving
/// scheme-theoretic multiplicity!) of an affine scheme `aff = Spec(Q[y_0..y_{n-1}]/I)`
/// of dimension `d = dim(aff)` and codimension `c = n - d`.
pub fn affine_jacobian_ideal(aff : AffineScheme) -> Ideal {
  if ideal_is_unit(aff.ring.ideal) {
    return aff.ring.ideal
  }
  let d = ideal_krull_dimension(aff.ring.ideal)
  quasicoherent_fitting_ideal(affine_kahler_differentials(aff), d)
}

///|
/// Radical **Singular Locus Ideal `I(Sing(X)) = √(I + J_c(I))`** of an equidimensional
/// affine `Q`-scheme `X`.
pub fn affine_singular_locus_ideal(aff : AffineScheme) -> Ideal {
  ideal_radical(affine_jacobian_ideal(aff))
}

///|
/// Decide **Pure-Dimensional Smoothness** over `Q` via **Eisenbud Proposition 20.6 &
/// Theorem 20.8**: `aff = Spec(B)` is smooth of pure dimension `d = dim(B)` iff `B == 0`
/// or `Ω^1_{B/Q}` is locally free of constant rank `d`, i.e.
///   `Fitt_d(Ω^1_{B/Q}) == <1>` AND `Fitt_{d-1}(Ω^1_{B/Q}) == I_B`
/// (rejecting both singular points AND mixed-dimension schemes like `line ⊔ point`!).
pub fn affine_is_smooth(aff : AffineScheme) -> Bool {
  if ideal_is_unit(aff.ring.ideal) {
    return true
  }
  let d = ideal_krull_dimension(aff.ring.ideal)
  let omega = affine_kahler_differentials(aff)
  ideal_is_unit(quasicoherent_fitting_ideal(omega, d)) &&
  ideal_eq(quasicoherent_fitting_ideal(omega, d - 1), aff.ring.ideal)
}

///|
/// Compute the **Global Tjurina Number `τ(X) = dim_Q Q[x] / (I + J_c(I))`** of an
/// affine scheme with isolated singularities (`Some(0)` if smooth, `Some(1)` for an
/// `A_1` node, `Some(2)` for an `A_2` cusp, `None` if `Sing(X)` has positive dimension)!
pub fn affine_tjurina_number(aff : AffineScheme) -> Int32? {
  let jac = affine_jacobian_ideal(aff)
  if ideal_is_unit(jac) {
    Some(0)
  } else {
    ideal_quotient_vector_space_dim(jac)
  }
}

///|
/// Decide whether `phi : A -> B` between smooth equidimensional affine `Q`-schemes
/// is **Étale** (smooth of relative dimension `0` + unramified: `dim(B) == dim(A)`
/// and `Ω^1_{B/A} == 0` — by Miracle Flatness / Jacobian criterion, an unramified
/// morphism between smooth schemes of equal dimension with `ker(phi) = 0` on
/// dominant components is flat and hence étale!).
pub fn is_etale_ring_hom_between_smooth(phi : RingHom) -> Bool {
  let src_aff = affine_scheme(phi.src)
  let dst_aff = affine_scheme(phi.dst)
  if ideal_is_unit(phi.dst.ideal) {
    return true
  }
  if !affine_is_smooth(src_aff) || !affine_is_smooth(dst_aff) {
    return false
  }
  if ideal_krull_dimension(phi.src.ideal) !=
    ideal_krull_dimension(phi.dst.ideal) {
    return false
  }
  is_unramified_ring_hom(phi)
}

// =============================================================================
// 2. Macaulay–Taylor Graded Gröbner Hilbert Polynomial `P_X(t) ∈ Q[t]`
// =============================================================================

///|
/// Symbolic binomial polynomial `C(t + shift, k) = Π_{j=1}^k (t + shift - k + j) / k! ∈ Q[t]`
/// represented as an exact `@exactalg.QPoly`.
fn binomial_qpoly(shift : Int32, k : Int32) -> @exactalg.QPoly {
  if k == 0 {
    return @exactalg.qpoly_one()
  }
  let mut acc = @exactalg.qpoly_one()
  for j in 1..<(k + 1) {
    // Factor `(1/j) * t + (shift - k + j)/j`:
    let c0 = @exactalg.rat_make(shift - k + j, j)
    let c1 = @exactalg.rat_make(1, j)
    let lin = @exactalg.qpoly_normalize([c0, c1])
    acc = @exactalg.qpoly_mul(acc, lin)
  }
  acc
}

///|
/// Count standard homogeneous monomials of exact total degree `deg` in
/// `S / in(homog_ideal)` directly, to cross-check `P_X(deg) == H_{S/I}(deg)`!
pub fn projective_hilbert_function(homog_ideal : Ideal, deg : Int32) -> Int32 {
  if deg < 0 || ideal_is_unit(homog_ideal) {
    return 0
  }
  let nvars = homog_ideal.nvars
  let lms : Array[Array[Int32]] = []
  for g in homog_ideal.rgb.gens {
    lms.push(mpoly_leading_term(g, homog_ideal.rgb.order).exps)
  }
  let cur = Array::make(nvars, 0)
  let mut count = 0
  fn walk(pos : Int32, rem : Int32) -> Unit {
    if pos == nvars - 1 {
      cur[pos] = rem
      let mut divisible = false
      for lm in lms {
        let mut div = true
        for v in 0..<nvars {
          if cur[v] < lm[v] {
            div = false
            break
          }
        }
        if div {
          divisible = true
          break
        }
      }
      if !divisible {
        count = count + 1
      }
      return
    }
    for e in 0..<(rem + 1) {
      cur[pos] = e
      walk(pos + 1, rem - e)
    }
  }
  walk(0, deg)
  count
}

///|
/// Derive the **Exact Symbolic Hilbert Polynomial `P_X(t) ∈ Q[t]`**, projective
/// dimension `dim(X)`, projective degree `deg(X) = d! · lc(P_X)`, and arithmetic
/// genus `p_a(X) = (-1)^d (P_X(0) - 1)` of `X = V_+(homog_ideal) ⊆ P^n_Q` directly
/// from the minimal initial ideal `in(homog_ideal.rgb)` via Macaulay's theorem and
/// LCM inclusion–exclusion over `@exactalg.QPoly`!
pub fn projective_hilbert_report(
  homog_ideal : Ideal,
) -> ProjectiveHilbertReport {
  let nvars = homog_ideal.nvars
  guard nvars >= 1 else {
    abort("projective_hilbert_report: expected nvars >= 1")
  }
  let n = nvars - 1
  if ideal_is_unit(homog_ideal) {
    return {
      ambient_dim: n,
      projective_dim: -1,
      degree: 0,
      arithmetic_genus: 0,
      hilbert_poly: @exactalg.qpoly_zero(),
      matches_hilbert_function: true,
    }
  }
  let lms : Array[Array[Int32]] = []
  let max_var_exp = Array::make(nvars, 0)
  for g in homog_ideal.rgb.gens {
    let e = mpoly_leading_term(g, homog_ideal.rgb.order).exps
    lms.push(e)
    for v in 0..<nvars {
      if e[v] > max_var_exp[v] {
        max_var_exp[v] = e[v]
      }
    }
  }
  let s = lms.length()
  let mut total_masks = 1
  for _ in 0..<s {
    total_masks = total_masks * 2
  }
  let mut poly = @exactalg.qpoly_zero()
  for mask in 0..<total_masks {
    let lcm_e = Array::make(nvars, 0)
    let mut pop = 0
    for i in 0..<s {
      if ((mask >> i) & 1) == 1 {
        pop = pop + 1
        for v in 0..<nvars {
          if lms[i][v] > lcm_e[v] {
            lcm_e[v] = lms[i][v]
          }
        }
      }
    }
    let mut deg_lcm = 0
    for v in 0..<nvars {
      deg_lcm = deg_lcm + lcm_e[v]
    }
    let term = binomial_qpoly(n - deg_lcm, n)
    poly = if pop % 2 == 0 {
      @exactalg.qpoly_add(poly, term)
    } else {
      @exactalg.qpoly_sub(poly, term)
    }
  }
  // Check agreement with `projective_hilbert_function` above the exact regularity bound `Σ max_var_exp[v]`:
  let mut reg_m = 0
  for v in 0..<nvars {
    reg_m = reg_m + max_var_exp[v]
  }
  let hf0 = projective_hilbert_function(homog_ideal, reg_m)
  let hf1 = projective_hilbert_function(homog_ideal, reg_m + 1)
  let pv0 = @exactalg.qpoly_eval(poly, @exactalg.rat_int(reg_m))
  let pv1 = @exactalg.qpoly_eval(poly, @exactalg.rat_int(reg_m + 1))
  let matches_hf = @exactalg.rat_eq(pv0, @exactalg.rat_int(hf0)) &&
    @exactalg.rat_eq(pv1, @exactalg.rat_int(hf1))
  let d = @exactalg.qpoly_degree(poly)
  if d < 0 {
    return {
      ambient_dim: n,
      projective_dim: -1,
      degree: 0,
      arithmetic_genus: 0,
      hilbert_poly: poly,
      matches_hilbert_function: matches_hf,
    }
  }
  let mut fact_d = 1
  for k in 2..<(d + 1) {
    fact_d = fact_d * k
  }
  let lc = @exactalg.qpoly_leading(poly)
  let deg_rat = @exactalg.rat_mul(lc, @exactalg.rat_int(fact_d))
  let deg_int = deg_rat.num.to_int()
  let p0 = @exactalg.qpoly_eval(poly, @exactalg.rat_zero())
  let p0_minus_1 = @exactalg.rat_sub(p0, @exactalg.rat_one()).num.to_int()
  let pa = if d % 2 == 0 { p0_minus_1 } else { -p0_minus_1 }
  {
    ambient_dim: n,
    projective_dim: d,
    degree: deg_int,
    arithmetic_genus: pa,
    hilbert_poly: poly,
    matches_hilbert_function: matches_hf,
  }
}

// =============================================================================
// 3. Blow-Up Strict Transform `Bl_{(0,0)}(A^2)` & Curve Desingularization
// =============================================================================

///|
/// Blow up an affine plane curve `C = V(f(x, y)) ⊆ A^2_Q` at the origin `(0, 0)`
/// inside `Bl_{(0,0)}(A^2) = W_0 ∪ W_1`:
///   - Chart `W_0 = Spec(Q[x, t])` (`y = x * t`, exceptional divisor `E : x = 0`):
///     strict transform ideal `I_0 = (<f(x, x * t)> : x^∞)` via `ideal_saturate`!
///   - Chart `W_1 = Spec(Q[s, y])` (`x = s * y`, exceptional divisor `E : y = 0`):
///     strict transform ideal `I_1 = (<f(s * y, y)> : y^∞)` via `ideal_saturate`!
///   - Glued along `W_{01} = Spec(Q[x, t, s] / <t * s - 1, I_0>)` (`y = x * t`),
///     returning the glued `Scheme`, Jacobian smoothness of the strict transform,
///     and length / reducedness of the exceptional fiber `C~ ∩ E`!
pub fn blowup_plane_curve_at_origin(f : MPoly) -> PlaneCurveBlowupReport {
  guard f.nvars == 2 && !mpoly_is_zero(f) else {
    abort("blowup_plane_curve_at_origin: expected nonzero 2-var polynomial")
  }
  let orig_aff = affine_scheme(coord_ring_new(2, [f]))
  let origin_sing = !affine_is_smooth(orig_aff)
  // Chart W_0: coords (x, t) = (var 0, var 1), subst (x, x * t)
  let x0 = mpoly_var(2, 0)
  let t0 = mpoly_var(2, 1)
  let total_w0 = mpoly_subst(f, 2, [x0, mpoly_mul(x0, t0)])
  let strict_i0 = ideal_saturate(ideal_new(2, [total_w0]), x0)
  let r0 = coord_ring_new(2, strict_i0.rgb.gens)
  // Chart W_1: coords (s, y) = (var 0, var 1), subst (s * y, y)
  let s1 = mpoly_var(2, 0)
  let y1 = mpoly_var(2, 1)
  let total_w1 = mpoly_subst(f, 2, [mpoly_mul(s1, y1), y1])
  let strict_i1 = ideal_saturate(ideal_new(2, [total_w1]), y1)
  let r1 = coord_ring_new(2, strict_i1.rgb.gens)
  // Overlap W_{01}: adjoin `s` = var 2 to W_0 with `t * s - 1 = 0`, mapping W_1's `(s, y) ↦ (s, x * t)`.
  let gens01 : Array[MPoly] = [
    mpoly_sub(mpoly_mul(mpoly_var(3, 1), mpoly_var(3, 2)), mpoly_int(3, 1)),
  ]
  for g in r0.ideal.rgb.gens {
    gens01.push(mpoly_extend_vars(g, 1, false))
  }
  let r01 = coord_ring_new(3, gens01)
  let id0 = ring_hom_id(r0)
  let id1 = ring_hom_id(r1)
  let hom0 : RingHom = {
    src: r0,
    dst: r01,
    var_images: [
      coord_ring_nf(r01, mpoly_var(3, 0)),
      coord_ring_nf(r01, mpoly_var(3, 1)),
    ],
  }
  let hom1 : RingHom = {
    src: r1,
    dst: r01,
    var_images: [
      coord_ring_nf(r01, mpoly_var(3, 2)),
      coord_ring_nf(r01, mpoly_mul(mpoly_var(3, 0), mpoly_var(3, 1))),
    ],
  }
  let strict_sch : Scheme = {
    charts: [affine_scheme(r0), affine_scheme(r1)],
    overlaps: [
      { is_empty: false, ring: r0, from_i: id0, from_j: id0, },
      { is_empty: false, ring: r01, from_i: hom0, from_j: hom1, },
      { is_empty: false, ring: r01, from_i: hom1, from_j: hom0, },
      { is_empty: false, ring: r1, from_i: id1, from_j: id1, },
    ],
  }
  let smooth_after = scheme_is_valid(strict_sch) &&
    affine_is_smooth(strict_sch.charts[0]) &&
    affine_is_smooth(strict_sch.charts[1])
  // Exceptional fiber `C~ ∩ E` on `E = P^1 = E_0 ∪ {[1:0]}`:
  // `len(C~ ∩ E) = dim_Q(O_{W_0}/<x>) + (dim_Q(O_{W_1}/<y>) - dim_Q((O_{W_1}/<y>)_s))`!
  let exc0_gens : Array[MPoly] = [x0]
  for g in r0.ideal.rgb.gens {
    exc0_gens.push(g)
  }
  let exc0_idl = ideal_new(2, exc0_gens)
  let len0 = match ideal_quotient_vector_space_dim(exc0_idl) {
    Some(d) => d
    None => 0
  }
  let exc1_gens : Array[MPoly] = [y1]
  for g in r1.ideal.rgb.gens {
    exc1_gens.push(g)
  }
  let exc1_idl = ideal_new(2, exc1_gens)
  let len1_all = match ideal_quotient_vector_space_dim(exc1_idl) {
    Some(d) => d
    None => 0
  }
  let exc1_loc_gens : Array[MPoly] = [
    mpoly_sub(mpoly_mul(mpoly_var(3, 2), mpoly_var(3, 0)), mpoly_int(3, 1)),
  ]
  for g in exc1_gens {
    exc1_loc_gens.push(mpoly_extend_vars(g, 1, false))
  }
  let len1_away_from_zero = match
    ideal_quotient_vector_space_dim(ideal_new(3, exc1_loc_gens)) {
    Some(d) => d
    None => 0
  }
  let exc_reduced = affine_is_reduced(
      affine_scheme(coord_ring_new(2, exc0_gens)),
    ) &&
    affine_is_reduced(affine_scheme(coord_ring_new(2, exc1_gens)))
  {
    origin_was_singular: origin_sing,
    strict_transform: strict_sch,
    strict_transform_is_smooth: smooth_after,
    exceptional_fiber_length: len0 + (len1_all - len1_away_from_zero),
    exceptional_fiber_is_reduced: exc_reduced,
  }
}

// =============================================================================
// 4. Galois Quadratic Field `F_{p^2}` & Arithmetic Frobenius Zeta Descent
// =============================================================================

///|
/// Construct the quadratic Galois field **`F_{p^2} = F_p[α] / <α^2 - c>`** (for
/// any odd prime `p >= 3`, automatically selecting the least quadratic non-residue
/// `c ∈ F_p^×`!) together with the canonical Frobenius-invariant subfield inclusion
/// `F_p ↪ F_{p^2}` (`a ↦ a + 0 · α`).
pub fn fcomm_fp2(p : Int32) -> (FiniteCommRing, FiniteRingHom) {
  guard p >= 3 && p % 2 == 1 else {
    abort("fcomm_fp2: expected odd prime p >= 3")
  }
  // Find least quadratic non-residue `c ∈ {1..p-1}`:
  let p64 = p.to_int64()
  let is_sq = Array::make(p, false)
  for a in 0..<p {
    let sq = (a.to_int64() * a.to_int64() % p64).to_int()
    is_sq[sq] = true
  }
  let mut c_nr = -1
  for c in 1..<p {
    if !is_sq[c] {
      c_nr = c
      break
    }
  }
  guard c_nr > 0 else { abort("fcomm_fp2: no non-residue found") }
  let sz = p * p
  let neg_t = Array::make(sz, 0)
  let add_t = Array::make(sz * sz, 0)
  let mul_t = Array::make(sz * sz, 0)
  let c64 = c_nr.to_int64()
  for i in 0..<sz {
    let a0 = i % p
    let a1 = i / p
    let na0 = (p - a0) % p
    let na1 = (p - a1) % p
    neg_t[i] = na1 * p + na0
    let a0_64 = a0.to_int64()
    let a1_64 = a1.to_int64()
    for j in 0..<sz {
      let b0 = j % p
      let b1 = j / p
      let s0 = (a0 + b0) % p
      let s1 = (a1 + b1) % p
      add_t[i * sz + j] = s1 * p + s0
      let b0_64 = b0.to_int64()
      let b1_64 = b1.to_int64()
      // (a0 + a1 α)(b0 + b1 α) = (a0 b0 + c_nr a1 b1) + (a0 b1 + a1 b0) α
      let m0 = ((a0_64 * b0_64 + c64 * (a1_64 * b1_64 % p64)) % p64).to_int()
      let m1 = ((a0_64 * b1_64 + a1_64 * b0_64) % p64).to_int()
      mul_t[i * sz + j] = m1 * p + m0
    }
  }
  let fp2 : FiniteCommRing = {
    size: sz,
    zero: 0,
    one: 1,
    neg_table: neg_t,
    add_table: add_t,
    mul_table: mul_t,
  }
  let fp = fcomm_fp(p)
  let emb_vals = Array::make(p, 0)
  for a in 0..<p {
    emb_vals[a] = a
  }
  (fp2, { src: fp, dst: fp2, values: emb_vals, })
}

///|
/// Verify **Hasse–Weil Zeta Rationality & Galois Component Frobenius Descent**
/// over `F_3 ⊂ F_9`:
///   1. `F_9 = fcomm_fp2(3)` is a genuine finite field (every nonzero element has
///      a multiplicative inverse) and `F_3 ↪ F_9` is a valid ring homomorphism;
///   2. Smooth real-pointless conic `C : X_0^2 + X_1^2 + X_2^2 = 0 ⊆ P^2` satisfies
///      Chevalley–Warning / Weil rationality `|C(F_3)| == 4 = 1 + 3` and
///      `|C(F_9)| == 10 = 1 + 3^2` (matching `P^1`);
///   3. Geometrically reducible Galois-conjugate line pair `Z : X_0^2 + X_1^2 = 0 ⊆ P^2`
///      has **ONLY ONE `F_3`-rational point `[0:0:1]` (`|Z(F_3)| == 1`)** because
///      `Frob_3` swaps the two lines `X_0 ± α X_1 = 0`, whereas over `F_9` both
///      components split and yield **`|Z(F_9)| == 2 * (9 + 1) - 1 = 19`**!
pub fn verify_weil_zeta_and_galois_frobenius_descent() -> Bool {
  let fp3 = fcomm_fp(3)
  let (fp9, emb) = fcomm_fp2(3)
  if !finite_ring_hom_is_valid(emb) {
    return false
  }
  // Verify every nonzero element of F_9 is a unit!
  for x in 1..<fp9.size {
    let mut has_inv = false
    for y in 1..<fp9.size {
      if fp9.mul_table[x * fp9.size + y] == fp9.one {
        has_inv = true
        break
      }
    }
    if !has_inv {
      return false
    }
  }
  let x0 = mpoly_var(3, 0)
  let x1 = mpoly_var(3, 1)
  let x2 = mpoly_var(3, 2)
  let conic = scheme_projective_subscheme(2, [
    mpoly_add(mpoly_add(mpoly_pow(x0, 2), mpoly_pow(x1, 2)), mpoly_pow(x2, 2)),
  ])
  let conj_lines = scheme_projective_subscheme(2, [
    mpoly_add(mpoly_pow(x0, 2), mpoly_pow(x1, 2)),
  ])
  let c_f3 = eval_scheme_functor_of_points(conic, fp3).length()
  let c_f9 = eval_scheme_functor_of_points(conic, fp9).length()
  let z_f3 = eval_scheme_functor_of_points(conj_lines, fp3).length()
  let z_f9 = eval_scheme_functor_of_points(conj_lines, fp9).length()
  c_f3 == 4 && c_f9 == 10 && z_f3 == 1 && z_f9 == 19
}
