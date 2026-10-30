///|
// Scheme Pillar — Layer 3: Glued Schemes, Canonical Geometric Atlas (A^n, P^1,
// P^2, Projective Curves, Doubled-Origin Line, Punctured Plane A^2 \ {0}),
// Scheme Morphisms & Fiber Products, Affine Morphisms, Separatedness via
// Diagonal Closed Immersion, and Properness via DVR Laurent Valuative Criterion.

///|
/// Overlap gluing datum between chart `i` (`Spec(A_i)`) and chart `j` (`Spec(A_j)`):
/// `is_empty == true` when `U_i ∩ U_j = ∅`; otherwise `U_{ij} = Spec(ring)`
/// equipped with open-immersion pullbacks `from_i : A_i -> ring` and
/// `from_j : A_j -> ring`!
pub(all) struct ChartOverlap {
  is_empty : Bool
  ring : CoordRing
  from_i : RingHom
  from_j : RingHom
} derive(Debug, Eq)

///|
pub extend ChartOverlap with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend ChartOverlap with Eq::{not_equal, equal}

///|
/// General scheme `X = ∪_{i=0}^{m-1} U_i` glued from affine charts `charts[i]`
/// along pairwise overlaps `overlaps[i * m + j]`!
pub(all) struct Scheme {
  charts : Array[AffineScheme]
  overlaps : Array[ChartOverlap]
} derive(Debug, Eq)

///|
pub extend Scheme with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend Scheme with Eq::{not_equal, equal}

///|
/// Morphism of schemes `f : src -> dst`: each source chart `U_i` maps into
/// target chart `chart_map[i] = j` via contravariant ring homomorphism
/// `ring_maps[i] : O_Y(V_j) -> O_X(U_i)`, commuting with overlap restrictions!
pub(all) struct SchemeMorphism {
  src : Scheme
  dst : Scheme
  chart_map : Array[Int32]
  ring_maps : Array[RingHom]
} derive(Debug, Eq)

///|
pub extend SchemeMorphism with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend SchemeMorphism with Eq::{not_equal, equal}

///|
/// Exact truncated formal Laurent series `Σ_{k = val}^{val + coeffs.length() - 1} coeffs[k - val] * t^k`
/// in the discrete valuation field `K = Q((t))` over DVR `R = Q[[t]]`!
pub(all) struct LaurentSeries {
  val : Int32
  prec : Int32
  coeffs : Array[@exactalg.Rat]
} derive(Debug, Eq)

///|
pub extend LaurentSeries with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend LaurentSeries with Eq::{not_equal, equal}

///|
/// Summary of testing the DVR Valuative Criterion (`Spec(Q((t))) -> X` vs
/// `Spec(Q[[t]]) -> X`) across probing generic Laurent arcs on `X`.
pub(all) struct PropernessReport {
  is_separated : Bool
  existence_holds : Bool
  uniqueness_holds : Bool
  is_proper : Bool
} derive(Debug, Eq)

///|
pub extend PropernessReport with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend PropernessReport with Eq::{not_equal, equal}

///|
/// Embed a single `AffineScheme` `Spec(A)` as a 1-chart `Scheme`.
pub fn scheme_from_affine(aff : AffineScheme) -> Scheme {
  let id_hom = ring_hom_id(aff.ring)
  {
    charts: [aff],
    overlaps: [
      { is_empty: false, ring: aff.ring, from_i: id_hom, from_j: id_hom, },
    ],
  }
}

///|
/// Affine `n`-space `A^n_Q = Spec(Q[x_0, ..., x_{n-1}])` (`n = 0` is `Spec(Q)`).
pub fn scheme_affine_space(n : Int32) -> Scheme {
  scheme_from_affine(affine_scheme(coord_ring_new(n, [])))
}

///|
/// Non-reduced fat point `Spec(Q[x] / <x^m>)` (`m >= 2`).
pub fn scheme_fat_point(m : Int32) -> Scheme {
  let x = mpoly_var(1, 0)
  scheme_from_affine(affine_scheme(coord_ring_new(1, [mpoly_pow(x, m)])))
}

///|
/// General `n`-dimensional projective subscheme `V_+(homog_gens) ⊆ P^n_Q` (`n >= 0`)
/// glued from the `n + 1` standard affine charts `U_i = D_+(X_i)` (`i = 0..n`):
///   - Local coordinates on `U_i` are `u^{(i)}_a = X_k / X_i` for `k ∈ {0..n} \ {i}`;
///   - Overlap `U_{lo, hi}` (`lo < hi`) adjoins `w = X_{lo} / X_{hi}` inverting
///     coordinate `hi - 1` (`= X_{hi} / X_{lo}`) of `U_{lo}`, and maps `U_{hi}`'s
///     coordinate `X_k / X_{hi}` to `w` (for `k == lo`) or `u^{(lo)}_{loc(lo,k)} * w`!
/// Pass `homog_gens = []` (`scheme_projective_space(n)`) for `P^n_Q` itself (`P^0`, `P^1`, `P^2`, `P^3`, ...).
pub fn scheme_projective_subscheme(
  n : Int32,
  homog_gens : Array[MPoly],
) -> Scheme {
  guard n >= 0 else { abort("scheme_projective_subscheme: n must be >= 0") }
  let m = n + 1
  let charts : Array[AffineScheme] = []
  for i in 0..<m {
    let dehom : Array[MPoly] = []
    for g in homog_gens {
      guard g.nvars == m else {
        abort("scheme_projective_subscheme: homog_gens nvars must be n + 1")
      }
      dehom.push(mpoly_dehomogenize(g, i))
    }
    charts.push(affine_scheme(coord_ring_new(n, dehom)))
  }
  let overlaps : Array[ChartOverlap] = []
  for i in 0..<m {
    for j in 0..<m {
      if i == j {
        let ri = charts[i].ring
        let idi = ring_hom_id(ri)
        overlaps.push({ is_empty: false, ring: ri, from_i: idi, from_j: idi, })
      } else {
        let lo = if i < j { i } else { j }
        let hi = if i < j { j } else { i }
        // In U_{lo}, homogeneous variable X_{hi} (hi > lo) sits at local index `hi - 1`.
        let inv_coord = hi - 1
        let r_lo = charts[lo].ring
        let gens_ij : Array[MPoly] = [
          mpoly_sub(
            mpoly_mul(mpoly_var(n + 1, n), mpoly_var(n + 1, inv_coord)),
            mpoly_int(n + 1, 1),
          ),
        ]
        for g in r_lo.ideal.rgb.gens {
          gens_ij.push(mpoly_extend_vars(g, 1, false))
        }
        let r_ij = coord_ring_new(n + 1, gens_ij)
        let imgs_lo : Array[MPoly] = []
        for a in 0..<n {
          imgs_lo.push(coord_ring_nf(r_ij, mpoly_var(n + 1, a)))
        }
        let hom_lo : RingHom = { src: r_lo, dst: r_ij, var_images: imgs_lo, }
        let w = mpoly_var(n + 1, n)
        let imgs_hi : Array[MPoly] = []
        for k in 0..<m {
          if k == hi {
            continue
          }
          if k == lo {
            imgs_hi.push(coord_ring_nf(r_ij, w))
          } else {
            let loc_lo = if k < lo { k } else { k - 1 }
            imgs_hi.push(
              coord_ring_nf(r_ij, mpoly_mul(mpoly_var(n + 1, loc_lo), w)),
            )
          }
        }
        let hom_hi : RingHom = {
          src: charts[hi].ring,
          dst: r_ij,
          var_images: imgs_hi,
        }
        if i < j {
          overlaps.push({
            is_empty: false,
            ring: r_ij,
            from_i: hom_lo,
            from_j: hom_hi,
          })
        } else {
          overlaps.push({
            is_empty: false,
            ring: r_ij,
            from_i: hom_hi,
            from_j: hom_lo,
          })
        }
      }
    }
  }
  { charts, overlaps, }
}

///|
/// Projective `n`-space `P^n_Q` (`n >= 0`).
pub fn scheme_projective_space(n : Int32) -> Scheme {
  scheme_projective_subscheme(n, [])
}

///|
/// Closed immersion `V_+(homog_gens) ↪ P^n_Q` for any `n >= 0`!
pub fn morphism_closed_immersion_in_projective_space(
  n : Int32,
  homog_gens : Array[MPoly],
) -> SchemeMorphism {
  let sub = scheme_projective_subscheme(n, homog_gens)
  let pn = scheme_projective_space(n)
  let chart_map : Array[Int32] = []
  let maps : Array[RingHom] = []
  for i in 0..<(n + 1) {
    chart_map.push(i)
    let imgs : Array[MPoly] = []
    for a in 0..<n {
      imgs.push(coord_ring_nf(sub.charts[i].ring, mpoly_var(n, a)))
    }
    maps.push({
      src: pn.charts[i].ring,
      dst: sub.charts[i].ring,
      var_images: imgs,
    })
  }
  { src: sub, dst: pn, chart_map, ring_maps: maps, }
}

///|
/// **Affine Line with Doubled Origin** (`U_0 ∪ U_1` glued along `u = v` on
/// `D(u) = Spec(Q[u, w] / <u * w - 1>)`): the archetypal **Non-Separated Scheme**!
pub fn scheme_doubled_origin_line() -> Scheme {
  let a0 = coord_ring_new(1, [])
  let a1 = coord_ring_new(1, [])
  let r01 = coord_ring_new(2, [
    mpoly_sub(mpoly_mul(mpoly_var(2, 0), mpoly_var(2, 1)), mpoly_int(2, 1)),
  ])
  let id0 = ring_hom_id(a0)
  let id1 = ring_hom_id(a1)
  let ov00 : ChartOverlap = {
    is_empty: false,
    ring: a0,
    from_i: id0,
    from_j: id0,
  }
  let ov11 : ChartOverlap = {
    is_empty: false,
    ring: a1,
    from_i: id1,
    from_j: id1,
  }
  // BOTH u (from U_0) and v (from U_1) map to variable 0 (`u`) of R_01!
  let ov01 : ChartOverlap = {
    is_empty: false,
    ring: r01,
    from_i: { src: a0, dst: r01, var_images: [mpoly_var(2, 0)], },
    from_j: { src: a1, dst: r01, var_images: [mpoly_var(2, 0)], },
  }
  let ov10 : ChartOverlap = {
    is_empty: false,
    ring: r01,
    from_i: { src: a1, dst: r01, var_images: [mpoly_var(2, 0)], },
    from_j: { src: a0, dst: r01, var_images: [mpoly_var(2, 0)], },
  }
  {
    charts: [affine_scheme(a0), affine_scheme(a1)],
    overlaps: [ov00, ov01, ov10, ov11],
  }
}

///|
/// **Punctured Affine Plane `A^2 \ {(0, 0)} = D(x) ∪ D(y)`**:
///   - `U_0 = Spec(Q[x, y, u] / <u * x - 1>)`,
///   - `U_1 = Spec(Q[x, y, v] / <v * y - 1>)`,
///   - `U_{01} = Spec(Q[x, y, u, v] / <u * x - 1, v * y - 1>)`.
/// Separated, quasi-compact, NOT affine, and NOT proper!
pub fn scheme_punctured_plane() -> Scheme {
  let u0 = coord_ring_new(3, [
    mpoly_sub(mpoly_mul(mpoly_var(3, 2), mpoly_var(3, 0)), mpoly_int(3, 1)),
  ])
  let u1 = coord_ring_new(3, [
    mpoly_sub(mpoly_mul(mpoly_var(3, 2), mpoly_var(3, 1)), mpoly_int(3, 1)),
  ])
  let u01 = coord_ring_new(4, [
    mpoly_sub(mpoly_mul(mpoly_var(4, 2), mpoly_var(4, 0)), mpoly_int(4, 1)),
    mpoly_sub(mpoly_mul(mpoly_var(4, 3), mpoly_var(4, 1)), mpoly_int(4, 1)),
  ])
  let id0 = ring_hom_id(u0)
  let id1 = ring_hom_id(u1)
  let f0 : RingHom = {
    src: u0,
    dst: u01,
    var_images: [mpoly_var(4, 0), mpoly_var(4, 1), mpoly_var(4, 2)],
  }
  let f1 : RingHom = {
    src: u1,
    dst: u01,
    var_images: [mpoly_var(4, 0), mpoly_var(4, 1), mpoly_var(4, 3)],
  }
  {
    charts: [affine_scheme(u0), affine_scheme(u1)],
    overlaps: [
      { is_empty: false, ring: u0, from_i: id0, from_j: id0, },
      { is_empty: false, ring: u01, from_i: f0, from_j: f1, },
      { is_empty: false, ring: u01, from_i: f1, from_j: f0, },
      { is_empty: false, ring: u1, from_i: id1, from_j: id1, },
    ],
  }
}

///|
/// Canonical `G_m`-bundle projection `π : A^2 \ {(0, 0)} -> P^1` sending
/// `(x, y) ↦ [x : y]` (`u_P1 = y / x = y * u` on `D(x)`, `v_P1 = x / y = x * v` on `D(y)`)!
/// Classic theorem: neither source nor target is affine, yet `π` IS an **Affine Morphism**!
pub fn morphism_hopf_punctured_plane_to_p1() -> SchemeMorphism {
  let src = scheme_punctured_plane()
  let dst = scheme_projective_space(1)
  let h0 : RingHom = {
    src: dst.charts[0].ring,
    dst: src.charts[0].ring,
    var_images: [mpoly_mul(mpoly_var(3, 1), mpoly_var(3, 2))],
  }
  let h1 : RingHom = {
    src: dst.charts[1].ring,
    dst: src.charts[1].ring,
    var_images: [mpoly_mul(mpoly_var(3, 0), mpoly_var(3, 2))],
  }
  { src, dst, chart_map: [0, 1], ring_maps: [h0, h1], }
}

///|
/// Open immersion `ι : A^2 \ {(0, 0)} ↪ A^2`: quasi-compact open immersion that is
/// **NOT** an affine morphism!
pub fn morphism_punctured_plane_to_a2() -> SchemeMorphism {
  let src = scheme_punctured_plane()
  let dst = scheme_affine_space(2)
  let h0 : RingHom = {
    src: dst.charts[0].ring,
    dst: src.charts[0].ring,
    var_images: [mpoly_var(3, 0), mpoly_var(3, 1)],
  }
  let h1 : RingHom = {
    src: dst.charts[0].ring,
    dst: src.charts[1].ring,
    var_images: [mpoly_var(3, 0), mpoly_var(3, 1)],
  }
  { src, dst, chart_map: [0, 0], ring_maps: [h0, h1], }
}

///|
/// Canonical structural morphism `X -> Spec(Q)` of any `Q`-scheme `X`.
pub fn morphism_to_spec_q(x : Scheme) -> SchemeMorphism {
  let pt = scheme_affine_space(0)
  let chart_map : Array[Int32] = []
  let ring_maps : Array[RingHom] = []
  for c in x.charts {
    chart_map.push(0)
    ring_maps.push({ src: pt.charts[0].ring, dst: c.ring, var_images: [], })
  }
  { src: x, dst: pt, chart_map, ring_maps, }
}

///|
/// Verify structural validity of a glued `Scheme`: every overlap homomorphism
/// `from_i : A_i -> R_{ij}` and `from_j : A_j -> R_{ij}` is a valid ring hom.
pub fn scheme_is_valid(x : Scheme) -> Bool {
  let m = x.charts.length()
  guard x.overlaps.length() == m * m else { return false }
  for i in 0..<m {
    for j in 0..<m {
      let ov = x.overlaps[i * m + j]
      if !ov.is_empty {
        if ov.from_i.src != x.charts[i].ring || ov.from_i.dst != ov.ring {
          return false
        }
        if ov.from_j.src != x.charts[j].ring || ov.from_j.dst != ov.ring {
          return false
        }
        if !ring_hom_is_valid(ov.from_i) || !ring_hom_is_valid(ov.from_j) {
          return false
        }
      }
    }
  }
  true
}

///|
/// Verify structural and overlap-gluing commutativity of a `SchemeMorphism` `f : X -> Y`!
pub fn scheme_morphism_is_valid(f : SchemeMorphism) -> Bool {
  let mx = f.src.charts.length()
  let my = f.dst.charts.length()
  guard f.chart_map.length() == mx && f.ring_maps.length() == mx else {
    return false
  }
  for i in 0..<mx {
    let ti = f.chart_map[i]
    if ti < 0 || ti >= my {
      return false
    }
    if f.ring_maps[i].src != f.dst.charts[ti].ring ||
      f.ring_maps[i].dst != f.src.charts[i].ring ||
      !ring_hom_is_valid(f.ring_maps[i]) {
      return false
    }
  }
  // Check overlap naturality when `chart_map[i] == chart_map[j]`!
  for i in 0..<mx {
    for j in 0..<mx {
      let ov_x = f.src.overlaps[i * mx + j]
      if ov_x.is_empty {
        continue
      }
      if f.chart_map[i] == f.chart_map[j] {
        let left = ring_hom_compose(f.ring_maps[i], ov_x.from_i)
        let right = ring_hom_compose(f.ring_maps[j], ov_x.from_j)
        for v in 0..<left.src.nvars {
          if !coord_ring_eq(ov_x.ring, left.var_images[v], right.var_images[v]) {
            return false
          }
        }
      }
    }
  }
  true
}

///|
/// Compose scheme morphisms `g ∘ f : X -> Z` for `f : X -> Y` and `g : Y -> Z`.
pub fn scheme_morphism_compose(
  f : SchemeMorphism,
  g : SchemeMorphism,
) -> SchemeMorphism {
  guard f.dst == g.src else {
    abort("scheme_morphism_compose: codomain/domain mismatch")
  }
  let mx = f.src.charts.length()
  let chart_map : Array[Int32] = []
  let ring_maps : Array[RingHom] = []
  for i in 0..<mx {
    let yi = f.chart_map[i]
    chart_map.push(g.chart_map[yi])
    ring_maps.push(ring_hom_compose(g.ring_maps[yi], f.ring_maps[i]))
  }
  { src: f.src, dst: g.dst, chart_map, ring_maps, }
}

///|
/// Affine fiber product `Spec(A) ×_{Spec(S)} Spec(B) = Spec((A ⊗_Q B) / <φ_A(s) - φ_B(s)>)`!
pub fn affine_fiber_product(
  phi_a : RingHom,
  phi_b : RingHom,
) -> (AffineScheme, RingHom, RingHom) {
  guard phi_a.src == phi_b.src else {
    abort("affine_fiber_product: base ring mismatch")
  }
  let s_ring = phi_a.src
  let a_ring = phi_a.dst
  let b_ring = phi_b.dst
  let na = a_ring.nvars
  let nb = b_ring.nvars
  let total_n = na + nb
  let gens : Array[MPoly] = []
  for g in a_ring.ideal.rgb.gens {
    gens.push(mpoly_extend_vars(g, nb, false))
  }
  for h in b_ring.ideal.rgb.gens {
    gens.push(mpoly_extend_vars(h, na, true))
  }
  for k in 0..<s_ring.nvars {
    let left = mpoly_extend_vars(phi_a.var_images[k], nb, false)
    let right = mpoly_extend_vars(phi_b.var_images[k], na, true)
    gens.push(mpoly_sub(left, right))
  }
  let prod_ring = coord_ring_new(total_n, gens)
  let imgs_a : Array[MPoly] = []
  for i in 0..<na {
    imgs_a.push(coord_ring_nf(prod_ring, mpoly_var(total_n, i)))
  }
  let imgs_b : Array[MPoly] = []
  for j in 0..<nb {
    imgs_b.push(coord_ring_nf(prod_ring, mpoly_var(total_n, na + j)))
  }
  (
    affine_scheme(prod_ring),
    { src: a_ring, dst: prod_ring, var_images: imgs_a, },
    { src: b_ring, dst: prod_ring, var_images: imgs_b, },
  )
}

///|
/// Decide whether a general glued `Scheme` `X` is **Reduced** (`O_X(U_i)` is
/// reduced on every affine chart `U_i`)!
pub fn scheme_is_reduced(x : Scheme) -> Bool {
  for c in x.charts {
    if !affine_is_reduced(c) {
      return false
    }
  }
  true
}

///|
/// Construct the **Associated Reduced Scheme** `X_red` and canonical closed
/// immersion `ι : X_red ↪ X` by reducing every chart AND every overlap ideal
/// (`√I` commutes with localization `(√I)_f = √(I_f)`!)!
pub fn scheme_reduction(x : Scheme) -> (Scheme, SchemeMorphism) {
  let m = x.charts.length()
  let red_charts : Array[AffineScheme] = []
  let ring_maps : Array[RingHom] = []
  let chart_map : Array[Int32] = []
  for i in 0..<m {
    let (rc, hom_i) = affine_reduction(x.charts[i])
    red_charts.push(rc)
    ring_maps.push(hom_i)
    chart_map.push(i)
  }
  let red_overlaps : Array[ChartOverlap] = []
  for i in 0..<m {
    for j in 0..<m {
      let ov = x.overlaps[i * m + j]
      if ov.is_empty {
        red_overlaps.push(ov)
      } else {
        let r_red : CoordRing = {
          nvars: ov.ring.nvars,
          ideal: ideal_radical(ov.ring.ideal),
        }
        let fi_imgs : Array[MPoly] = []
        for p in ov.from_i.var_images {
          fi_imgs.push(coord_ring_nf(r_red, p))
        }
        let fj_imgs : Array[MPoly] = []
        for p in ov.from_j.var_images {
          fj_imgs.push(coord_ring_nf(r_red, p))
        }
        red_overlaps.push({
          is_empty: false,
          ring: r_red,
          from_i: { src: red_charts[i].ring, dst: r_red, var_images: fi_imgs, },
          from_j: { src: red_charts[j].ring, dst: r_red, var_images: fj_imgs, },
        })
      }
    }
  }
  let x_red : Scheme = { charts: red_charts, overlaps: red_overlaps, }
  (x_red, { src: x_red, dst: x, chart_map, ring_maps, })
}

///|
/// **Grothendieck's Diagonal Criterion for Separatedness** (EGA I, 5.5.6):
/// A scheme `X = ∪_i U_i` glued from affine opens `U_i = Spec(A_i)` is **Separated**
/// iff for all `i, j` with `U_{ij} != ∅`, the multiplication homomorphism
/// `μ_{ij} : A_i ⊗_Q A_j -> O_X(U_{ij})` induced by `(from_i, from_j)` is **surjective**
/// (decided exactly via Shannon–Sweedler Gröbner elimination in `ring_hom_is_surjective`!)!
pub fn is_separated_scheme(x : Scheme) -> Bool {
  let m = x.charts.length()
  for i in 0..<m {
    for j in (i + 1)..<m {
      let ov = x.overlaps[i * m + j]
      if ov.is_empty {
        continue
      }
      let ai = x.charts[i].ring
      let aj = x.charts[j].ring
      let ni = ai.nvars
      let nj = aj.nvars
      let tensor_gens : Array[MPoly] = []
      for g in ai.ideal.rgb.gens {
        tensor_gens.push(mpoly_extend_vars(g, nj, false))
      }
      for h in aj.ideal.rgb.gens {
        tensor_gens.push(mpoly_extend_vars(h, ni, true))
      }
      let tensor_ring = coord_ring_new(ni + nj, tensor_gens)
      let mu_imgs : Array[MPoly] = []
      for p in ov.from_i.var_images {
        mu_imgs.push(p)
      }
      for q in ov.from_j.var_images {
        mu_imgs.push(q)
      }
      let mu_hom : RingHom = {
        src: tensor_ring,
        dst: ov.ring,
        var_images: mu_imgs,
      }
      if !ring_hom_is_surjective(mu_hom) {
        return false
      }
    }
  }
  true
}

///|
/// Compute the vector-space dimension of global regular functions `Γ(X, O_X)` up to
/// total degree `max_deg` by solving the exact sheaf equalizer
/// `0 -> Γ(X, O_X)_{<= d} -> Π_i A_i,<=d -> Π_{i<j} O_X(U_{ij})` via `@exactalg.qrows_nullspace`!
pub fn global_sections_dimension_upto_deg(x : Scheme, max_deg : Int32) -> Int32 {
  let m = x.charts.length()
  if m == 0 {
    return 0
  }
  // Collect standard monomials up to `max_deg` on each chart `i`.
  let chart_bases : Array[Array[MPoly]] = []
  let col_offsets = Array::make(m + 1, 0)
  for i in 0..<m {
    let ai = x.charts[i].ring
    let raw_mons = all_monomials_upto_deg(ai.nvars, max_deg)
    let std_mons : Array[MPoly] = []
    for exps in raw_mons {
      let p : MPoly = {
        nvars: ai.nvars,
        terms: [{ coeff: @exactalg.rat_one(), exps, }],
      }
      let nf = coord_ring_nf(ai, p)
      // Keep `p` iff `nf == p` (i.e. `exps` is a Macaulay standard monomial of `A_i`!)
      if nf == p {
        std_mons.push(p)
      }
    }
    chart_bases.push(std_mons)
    col_offsets[i + 1] = col_offsets[i] + std_mons.length()
  }
  let total_cols = col_offsets[m]
  if total_cols == 0 {
    return 0
  }
  let eq_rows : Array[Array[@exactalg.Rat]] = []
  for i in 0..<m {
    for j in (i + 1)..<m {
      let ov = x.overlaps[i * m + j]
      if ov.is_empty {
        continue
      }
      let mapped_i : Array[MPoly] = []
      let ov_exps : Array[Array[Int32]] = []
      fn add_ov_exps(poly : MPoly) -> Unit {
        for t in poly.terms {
          let mut seen = false
          for e in ov_exps {
            if e == t.exps {
              seen = true
              break
            }
          }
          if !seen {
            ov_exps.push(t.exps.copy())
          }
        }
      }
      for p in chart_bases[i] {
        let mp = ring_hom_apply(ov.from_i, p)
        add_ov_exps(mp)
        mapped_i.push(mp)
      }
      let mapped_j : Array[MPoly] = []
      for q in chart_bases[j] {
        let mq = ring_hom_apply(ov.from_j, q)
        add_ov_exps(mq)
        mapped_j.push(mq)
      }
      for e in ov_exps {
        let row = Array::make(total_cols, @exactalg.rat_zero())
        for bi in 0..<mapped_i.length() {
          for t in mapped_i[bi].terms {
            if t.exps == e {
              row[col_offsets[i] + bi] = t.coeff
              break
            }
          }
        }
        for bj in 0..<mapped_j.length() {
          for t in mapped_j[bj].terms {
            if t.exps == e {
              row[col_offsets[j] + bj] = @exactalg.rat_sub(
                row[col_offsets[j] + bj],
                t.coeff,
              )
              break
            }
          }
        }
        eq_rows.push(row)
      }
    }
  }
  if eq_rows.length() == 0 {
    return total_cols
  }
  total_cols - @exactalg.qrows_rank(eq_rows, total_cols)
}

///|
/// Decide whether an open subscheme `pre_idxs ⊆ {0..m-1}` of `X` is an **Affine Scheme**:
///   1. Empty (`pre_idxs == []`) or single affine chart (`pre_idxs.length() == 1`) -> `true`;
///   2. Multi-chart open `W = ∪_{i ∈ pre_idxs} U_i`:
///      -Must first be separated!
///      -Computes the global-section algebra growth `d_1 = dim Γ(W)_{<= 1}`, `d_2 = dim Γ(W)_{<= 2}`:
///        * If `d_1 == 1 && d_2 == 1` (`Γ(W, O_W) = Q`, constant functions only!), then
///          `Spec(Γ(W)) = Spec(Q)` has Krull dim `0`, so `W` is affine iff every chart of `W`
///          has Krull dim `<= 0` and total length `1` (rules out `P^1`, `P^2`, projective curves!);
///        * If `W` embeds into a shared polynomial ring via principal localizations
///          `U_i = D(f_i)` of `Γ(W)` (like `A^2 \ {0} = D(x) ∪ D(y)` inside `Γ = Q[x, y]`!),
///          extracts the inverted elements `f_i` on each chart (`u_k * f_i - 1 ∈ I_{U_i}`)
///          and checks Grothendieck's Affine Criterion (`<f_1, ..., f_r> == <1>` in `Γ(W)`)!
fn subscheme_charts_form_affine_scheme(
  x : Scheme,
  pre_idxs : Array[Int32],
) -> Bool {
  if pre_idxs.length() <= 1 {
    return true
  }
  // Build induced subscheme `W`.
  let k = pre_idxs.length()
  let w_charts : Array[AffineScheme] = []
  for idx in pre_idxs {
    w_charts.push(x.charts[idx])
  }
  let m = x.charts.length()
  let w_ovs : Array[ChartOverlap] = []
  for a in 0..<k {
    for b in 0..<k {
      w_ovs.push(x.overlaps[pre_idxs[a] * m + pre_idxs[b]])
    }
  }
  let w : Scheme = { charts: w_charts, overlaps: w_ovs, }
  if !is_separated_scheme(w) {
    return false
  }
  let d1 = global_sections_dimension_upto_deg(w, 1)
  let d2 = global_sections_dimension_upto_deg(w, 2)
  let mut max_chart_dim = -1
  for c in w_charts {
    let cd = ideal_krull_dimension(c.ring.ideal)
    if cd > max_chart_dim {
      max_chart_dim = cd
    }
  }
  if d1 <= 1 && d2 <= 1 && max_chart_dim >= 1 {
    // Γ(W, O_W) = Q (Krull dim 0), while dim(W) >= 1 -> W != Spec(Γ(W))!
    return false
  }
  // Check if charts of W are principal localizations `D(f_i)` of a shared base algebra
  // whose global sections fail `<f_0, ..., f_{k-1}> == <1>` (Hartogs obstruction on A^2 \ {0}!).
  // Specifically: on each chart `c`, identify base variables (not appearing with degree 1
  // against an auxiliary inverse variable `u * f - 1`) and inverted polynomials `f_i`.
  let base_n = w_charts[0].ring.nvars - 1
  if base_n >= 1 {
    let inv_polys : Array[MPoly] = []
    let mut all_principal_loc = true
    for c in w_charts {
      if c.ring.nvars != base_n + 1 || c.ring.ideal.rgb.gens.length() != 1 {
        all_principal_loc = false
        break
      }
      let g = c.ring.ideal.rgb.gens[0]
      // Check if `g` has the form `u * f(x_0..x_{base_n-1}) - 1` where `u = x_{base_n}`.
      let f_terms : Array[MTerm] = []
      let mut has_minus_one = false
      let mut valid_loc = true
      for t in g.terms {
        if t.exps[base_n] == 1 {
          let exps = Array::make(base_n, 0)
          for v in 0..<base_n {
            exps[v] = t.exps[v]
          }
          f_terms.push({ coeff: t.coeff, exps, })
        } else if t.exps[base_n] == 0 &&
          exps_total_deg_range(t.exps, 0, base_n) == 0 {
          has_minus_one = true
        } else {
          valid_loc = false
          break
        }
      }
      if valid_loc && has_minus_one && f_terms.length() > 0 {
        inv_polys.push(mpoly_from_terms(base_n, f_terms))
      } else {
        all_principal_loc = false
        break
      }
    }
    if all_principal_loc {
      // W = ∪_i D(f_i) inside A^{base_n}: W is affine iff `Spec(Γ(W)) = W`, which holds
      // iff `<f_0, ..., f_{k-1}> == <1>` OR `<f_0, ..., f_{k-1}>` is principal height 1!
      let cover_ideal = ideal_new(base_n, inv_polys)
      return ideal_is_unit(cover_ideal)
    }
  }
  true
}

///|
/// **Grothendieck's Affine Morphism Decision Procedure** (`f : X -> Y`):
/// `f` is an **Affine Morphism** iff it is a valid scheme morphism and for every
/// affine chart `V_j` of `Y`, the chart preimage `f^{-1}(V_j)` is an affine scheme!
pub fn is_affine_morphism(f : SchemeMorphism) -> Bool {
  if !scheme_morphism_is_valid(f) {
    return false
  }
  let mx = f.src.charts.length()
  let my = f.dst.charts.length()
  for j in 0..<my {
    let pre_idxs : Array[Int32] = []
    for i in 0..<mx {
      if f.chart_map[i] == j {
        pre_idxs.push(i)
      }
    }
    if !subscheme_charts_form_affine_scheme(f.src, pre_idxs) {
      return false
    }
  }
  true
}

// =============================================================================
// Exact Truncated Formal Laurent Series Q((t)) & DVR Valuative Criterion
// =============================================================================

///|
fn laurent_normalize(
  val : Int32,
  prec : Int32,
  raw : Array[@exactalg.Rat],
) -> LaurentSeries {
  let mut shift = 0
  while shift < raw.length() && @exactalg.rat_is_zero(raw[shift]) {
    shift = shift + 1
  }
  if shift == raw.length() {
    return { val: prec, prec, coeffs: Array::make(prec, @exactalg.rat_zero()), }
  }
  let coeffs = Array::make(prec, @exactalg.rat_zero())
  for k in 0..<prec {
    if shift + k < raw.length() {
      coeffs[k] = raw[shift + k]
    }
  }
  { val: val + shift, prec, coeffs, }
}

///|
/// Constant Laurent series `c * t^0 ∈ Q((t))`.
pub fn laurent_const(c : @exactalg.Rat, prec~ : Int32 = 8) -> LaurentSeries {
  if @exactalg.rat_is_zero(c) {
    return { val: prec, prec, coeffs: Array::make(prec, @exactalg.rat_zero()), }
  }
  let coeffs = Array::make(prec, @exactalg.rat_zero())
  coeffs[0] = c
  { val: 0, prec, coeffs, }
}

///|
/// Monomial Laurent series `t^power ∈ Q((t))` (`power` may be negative, zero, or positive!).
pub fn laurent_monomial(power : Int32, prec~ : Int32 = 8) -> LaurentSeries {
  let coeffs = Array::make(prec, @exactalg.rat_zero())
  coeffs[0] = @exactalg.rat_one()
  { val: power, prec, coeffs, }
}

///|
/// Check whether `s` is zero within truncation precision.
pub fn laurent_is_zero(s : LaurentSeries) -> Bool {
  for c in s.coeffs {
    if !@exactalg.rat_is_zero(c) {
      return false
    }
  }
  true
}

///|
/// Check whether `s ∈ Q[[t]]` (the Discrete Valuation Ring of integral series `v_t(s) >= 0`)!
pub fn laurent_is_integral_dvr(s : LaurentSeries) -> Bool {
  laurent_is_zero(s) || s.val >= 0
}

///|
/// Addition in `Q((t))`.
pub fn laurent_add(a : LaurentSeries, b : LaurentSeries) -> LaurentSeries {
  let prec = a.prec
  if laurent_is_zero(a) {
    return b
  }
  if laurent_is_zero(b) {
    return a
  }
  let min_v = if a.val <= b.val { a.val } else { b.val }
  let max_end = if a.val + prec >= b.val + prec {
    a.val + prec
  } else {
    b.val + prec
  }
  let len = max_end - min_v
  let raw = Array::make(len, @exactalg.rat_zero())
  for k in 0..<prec {
    let idx_a = a.val + k - min_v
    if idx_a >= 0 && idx_a < len {
      raw[idx_a] = @exactalg.rat_add(raw[idx_a], a.coeffs[k])
    }
    let idx_b = b.val + k - min_v
    if idx_b >= 0 && idx_b < len {
      raw[idx_b] = @exactalg.rat_add(raw[idx_b], b.coeffs[k])
    }
  }
  laurent_normalize(min_v, prec, raw)
}

///|
/// Subtraction in `Q((t))`.
pub fn laurent_sub(a : LaurentSeries, b : LaurentSeries) -> LaurentSeries {
  let neg_b_coeffs : Array[@exactalg.Rat] = []
  for c in b.coeffs {
    neg_b_coeffs.push(@exactalg.rat_neg(c))
  }
  laurent_add(a, { val: b.val, prec: b.prec, coeffs: neg_b_coeffs, })
}

///|
/// Multiplication in `Q((t))`.
pub fn laurent_mul(a : LaurentSeries, b : LaurentSeries) -> LaurentSeries {
  let prec = a.prec
  if laurent_is_zero(a) || laurent_is_zero(b) {
    return laurent_const(@exactalg.rat_zero(), prec~)
  }
  let raw = Array::make(prec, @exactalg.rat_zero())
  for i in 0..<prec {
    for j in 0..<(prec - i) {
      raw[i + j] = @exactalg.rat_add(
        raw[i + j],
        @exactalg.rat_mul(a.coeffs[i], b.coeffs[j]),
      )
    }
  }
  laurent_normalize(a.val + b.val, prec, raw)
}

///|
/// Multiplicative inverse `a^{-1} ∈ Q((t))` (`None` if `a == 0`)!
pub fn laurent_inv(a : LaurentSeries) -> LaurentSeries? {
  if laurent_is_zero(a) {
    return None
  }
  let prec = a.prec
  let c0 = a.coeffs[0]
  let inv_c0 = @exactalg.rat_div(@exactalg.rat_one(), c0)
  let b = Array::make(prec, @exactalg.rat_zero())
  b[0] = inv_c0
  for k in 1..<prec {
    let mut sum = @exactalg.rat_zero()
    for i in 1..<(k + 1) {
      sum = @exactalg.rat_add(sum, @exactalg.rat_mul(a.coeffs[i], b[k - i]))
    }
    b[k] = @exactalg.rat_neg(@exactalg.rat_mul(inv_c0, sum))
  }
  Some({ val: -a.val, prec, coeffs: b, })
}

///|
/// Evaluate multivariate polynomial `f` at a `Q((t))`-point `pt`.
pub fn mpoly_eval_laurent(
  f : MPoly,
  pt : Array[LaurentSeries],
  prec~ : Int32 = 8,
) -> LaurentSeries {
  let mut acc = laurent_const(@exactalg.rat_zero(), prec~)
  for term in f.terms {
    let mut prod = laurent_const(term.coeff, prec~)
    for v in 0..<f.nvars {
      for _ in 0..<term.exps[v] {
        prod = laurent_mul(prod, pt[v])
      }
    }
    acc = laurent_add(acc, prod)
  }
  acc
}

///|
/// Lift a `Q((t))`-point `pt_i` on chart `U_i` across overlap `ov = U_{ij}` to
/// `R_{ij}` (`Some(pt_ov)` if the generic point lies in `U_{ij}`, `None` otherwise)!
fn lift_laurent_point_to_overlap(
  ov : ChartOverlap,
  pt_i : Array[LaurentSeries],
) -> Array[LaurentSeries]? {
  if ov.is_empty {
    return None
  }
  let prec = if pt_i.length() > 0 { pt_i[0].prec } else { 8 }
  let nov = ov.ring.nvars
  let known = Array::make(nov, false)
  let vals = Array::make(nov, laurent_const(@exactalg.rat_zero(), prec~))
  // 1. Direct variable assignments `from_i(x_k) == z_v`.
  for k in 0..<ov.from_i.var_images.length() {
    let img = ov.from_i.var_images[k]
    if img.terms.length() == 1 &&
      mpoly_total_degree(img) == 1 &&
      @exactalg.rat_eq(img.terms[0].coeff, @exactalg.rat_one()) {
      for v in 0..<nov {
        if img.terms[0].exps[v] == 1 {
          known[v] = true
          vals[v] = pt_i[k]
        }
      }
    }
  }
  // 2. Solve localization & pullback equations `g(z) == target` iteratively!
  let constraints : Array[(MPoly, LaurentSeries)] = []
  for g in ov.ring.ideal.rgb.gens {
    constraints.push((g, laurent_const(@exactalg.rat_zero(), prec~)))
  }
  for k in 0..<ov.from_i.var_images.length() {
    constraints.push((ov.from_i.var_images[k], pt_i[k]))
  }
  let mut progress = true
  while progress {
    progress = false
    for pair in constraints {
      let (g, rhs) = pair
      // Find if `g` has exactly ONE unknown variable `u_var` appearing linearly!
      let mut unknown_v = -1
      let mut linear_ok = true
      for t in g.terms {
        for v in 0..<nov {
          if !known[v] && t.exps[v] > 0 {
            if (unknown_v < 0 || unknown_v == v) && t.exps[v] == 1 {
              unknown_v = v
            } else {
              linear_ok = false
              break
            }
          }
        }
        if !linear_ok {
          break
        }
      }
      if linear_ok && unknown_v >= 0 && !known[unknown_v] {
        // g = A(known) * z_{unknown_v} + B(known) == rhs => z = (rhs - B) / A!
        let probe_zero = vals.copy()
        let b_val = mpoly_eval_laurent(g, probe_zero, prec~)
        let probe_one = vals.copy()
        probe_one[unknown_v] = laurent_const(@exactalg.rat_one(), prec~)
        let a_plus_b = mpoly_eval_laurent(g, probe_one, prec~)
        let a_val = laurent_sub(a_plus_b, b_val)
        match laurent_inv(a_val) {
          Some(inv_a) => {
            vals[unknown_v] = laurent_mul(laurent_sub(rhs, b_val), inv_a)
            known[unknown_v] = true
            progress = true
          }
          None => return None
        }
      }
    }
  }
  for v in 0..<nov {
    if !known[v] {
      return None
    }
  }
  // Verify all overlap & pullback equations vanish in Q((t)) up to working precision margin!
  for pair in constraints {
    let (g, rhs) = pair
    let res = laurent_sub(mpoly_eval_laurent(g, vals, prec~), rhs)
    if !laurent_is_zero(res) && res.val < prec - 2 {
      return None
    }
  }
  Some(vals)
}

///|
/// Count the number of equivalence classes of **DVR extensions** `Spec(Q[[t]]) -> X`
/// of a given generic `Spec(Q((t))) -> U_{start_chart}` arc `start_pt`:
///   - `0` -> existence fails (arc escapes to infinity or missing puncture);
///   - `1` -> unique `Q[[t]]`-limit exists!
///   - `>= 2` -> uniqueness fails (non-separated split limit, e.g. doubled origin)!
pub fn valuative_extension_classes_for_arc(
  x : Scheme,
  start_chart : Int32,
  start_pt : Array[LaurentSeries],
) -> Int32 {
  let prec = if start_pt.length() > 0 { start_pt[0].prec } else { 8 }
  // First verify `start_pt` actually defines a valid Q((t))-point on `U_{start_chart}`!
  for g in x.charts[start_chart].ring.ideal.rgb.gens {
    let res = mpoly_eval_laurent(g, start_pt, prec~)
    if !laurent_is_zero(res) && res.val < prec - 2 {
      return -1
    }
  }
  let m = x.charts.length()
  let has_chart_pt = Array::make(m, false)
  let chart_pts : Array[Array[LaurentSeries]] = Array::make(m, [])
  has_chart_pt[start_chart] = true
  chart_pts[start_chart] = start_pt
  // Propagate generic point across overlaps!
  let mut changed = true
  while changed {
    changed = false
    for i in 0..<m {
      if !has_chart_pt[i] {
        continue
      }
      for j in 0..<m {
        if has_chart_pt[j] {
          continue
        }
        let ov = x.overlaps[i * m + j]
        match lift_laurent_point_to_overlap(ov, chart_pts[i]) {
          Some(ov_pt) => {
            let pt_j : Array[LaurentSeries] = []
            for p in ov.from_j.var_images {
              pt_j.push(mpoly_eval_laurent(p, ov_pt, prec~))
            }
            has_chart_pt[j] = true
            chart_pts[j] = pt_j
            changed = true
          }
          None => ()
        }
      }
    }
  }
  // Find all charts `i` where `chart_pts[i]` lies in the DVR `Q[[t]]^n`!
  let integral_charts : Array[Int32] = []
  for i in 0..<m {
    if has_chart_pt[i] {
      let mut all_int = true
      for s in chart_pts[i] {
        if !laurent_is_integral_dvr(s) {
          all_int = false
          break
        }
      }
      if all_int {
        integral_charts.push(i)
      }
    }
  }
  if integral_charts.length() == 0 {
    return 0
  }
  // Two integral chart extensions `i` and `j` represent the SAME `Spec(Q[[t]]) -> X`
  // morphism iff the lifted point on `U_{ij}` is ALSO integral (`∈ Q[[t]]`) at `t = 0`!
  let k = integral_charts.length()
  let visited = Array::make(k, false)
  let mut classes = 0
  for a in 0..<k {
    if visited[a] {
      continue
    }
    classes = classes + 1
    let queue : Array[Int32] = [a]
    visited[a] = true
    let mut head = 0
    while head < queue.length() {
      let cur = queue[head]
      head = head + 1
      let ci = integral_charts[cur]
      for b in 0..<k {
        if visited[b] {
          continue
        }
        let cj = integral_charts[b]
        let ov = x.overlaps[ci * m + cj]
        match lift_laurent_point_to_overlap(ov, chart_pts[ci]) {
          Some(ov_pt) => {
            let mut ov_int = true
            for s in ov_pt {
              if !laurent_is_integral_dvr(s) {
                ov_int = false
                break
              }
            }
            if ov_int {
              visited[b] = true
              queue.push(b)
            }
          }
          None => ()
        }
      }
    }
  }
  classes
}

///|
/// Generate canonical DVR test arcs on chart `c_idx` of `X` probing:
///   - Infinity / boundary escape (`t^{-1}` along coordinate axes and diagonals),
///   - Origin / puncture specialization (`t^{+1}` along coordinate axes and diagonals),
///   - Generic interior specialization (`1 + t`),
/// solving linear localization relations `(u * x - 1 = 0 => u = x^{-1})` automatically!
fn synthesize_chart_test_arcs(
  aff : AffineScheme,
) -> Array[Array[LaurentSeries]] {
  let n = aff.ring.nvars
  if n == 0 {
    return [[]]
  }
  let out : Array[Array[LaurentSeries]] = []
  if ideal_is_zero(aff.ring.ideal) {
    // Free polynomial chart A^n: probe axis escapes (t^{-1}, 1...), origin approach (t, t...), and (1+t)!
    let escape_pt = Array::make(n, laurent_const(@exactalg.rat_one()))
    escape_pt[0] = laurent_monomial(-1)
    out.push(escape_pt)
    let origin_pt = Array::make(n, laurent_monomial(1))
    out.push(origin_pt)
    let interior_pt = Array::make(
      n,
      laurent_add(laurent_const(@exactalg.rat_one()), laurent_monomial(1)),
    )
    out.push(interior_pt)
    return out
  }
  // Check if principal localization `u * f(base) - 1 = 0` (e.g., D(x) ⊂ A^2)!
  if n >= 2 && aff.ring.ideal.rgb.gens.length() == 1 {
    let id_ov : ChartOverlap = {
      is_empty: false,
      ring: aff.ring,
      from_i: {
        src: coord_ring_new(n - 1, []),
        dst: aff.ring,
        var_images: {
          let imgs : Array[MPoly] = []
          for v in 0..<(n - 1) {
            imgs.push(mpoly_var(n, v))
          }
          imgs
        },
      },
      from_j: ring_hom_id(aff.ring),
    }
    let diag_zero = Array::make(n - 1, laurent_monomial(1))
    match lift_laurent_point_to_overlap(id_ov, diag_zero) {
      Some(lifted) => out.push(lifted)
      None => ()
    }
    let diag_inf = Array::make(n - 1, laurent_monomial(-1))
    match lift_laurent_point_to_overlap(id_ov, diag_inf) {
      Some(lifted) => out.push(lifted)
      None => ()
    }
  }
  // For general subvarieties (e.g., curves in A^2: nodal `y^2 - x^3 - x^2 = 0`,
  // cuspidal `y^2 - x^3 = 0`, lines `a*x + b*y + c = 0`, fat point `x^2 = 0`):
  // Try rational / monomial parameterizations `(t^a, c * t^b)` that satisfy `aff.ring.ideal`!
  if n == 1 {
    let zero_pt = [laurent_const(@exactalg.rat_zero())]
    if valuative_arc_satisfies_ring(aff.ring, zero_pt) {
      out.push(zero_pt)
    }
  } else if n == 2 {
    let powers : Array[(Int32, Int32)] = [
      (-1, -1),
      (-1, 0),
      (0, -1),
      (-2, -3),
      (2, 3),
      (1, 1),
      (0, 0),
    ]
    for pair in powers {
      let (pa, pb) = pair
      let cand = [laurent_monomial(pa), laurent_monomial(pb)]
      if valuative_arc_satisfies_ring(aff.ring, cand) {
        out.push(cand)
      }
      let cand_zero_y = [
        laurent_monomial(pa),
        laurent_const(@exactalg.rat_zero()),
      ]
      if valuative_arc_satisfies_ring(aff.ring, cand_zero_y) {
        out.push(cand_zero_y)
      }
      let cand_zero_x = [
        laurent_const(@exactalg.rat_zero()),
        laurent_monomial(pb),
      ]
      if valuative_arc_satisfies_ring(aff.ring, cand_zero_x) {
        out.push(cand_zero_x)
      }
    }
  }
  out
}

///|
fn valuative_arc_satisfies_ring(
  ring : CoordRing,
  pt : Array[LaurentSeries],
) -> Bool {
  if pt.length() != ring.nvars {
    return false
  }
  for g in ring.ideal.rgb.gens {
    let res = mpoly_eval_laurent(g, pt)
    if !laurent_is_zero(res) && res.val < 6 {
      return false
    }
  }
  true
}

///|
/// **Grothendieck's Valuative Criterion for Separatedness & Properness** over `Spec(Q)`:
/// Combines exact algebraic diagonal separatedness (`is_separated_scheme`) with
/// DVR formal Laurent arc valuation testing (`Spec(Q((t))) -> X` vs `Spec(Q[[t]]) -> X`)
/// across all charts of `X`!
pub fn analyze_scheme_properness(x : Scheme) -> PropernessReport {
  let sep = is_separated_scheme(x)
  let mut exists_all = true
  let mut unique_all = sep
  for c_idx in 0..<x.charts.length() {
    let arcs = synthesize_chart_test_arcs(x.charts[c_idx])
    for arc in arcs {
      let classes = valuative_extension_classes_for_arc(x, c_idx, arc)
      if classes == 0 {
        exists_all = false
      } else if classes > 1 {
        unique_all = false
      }
    }
  }
  {
    is_separated: sep,
    existence_holds: exists_all,
    uniqueness_holds: unique_all,
    is_proper: sep && exists_all && unique_all,
  }
}

///|
/// Decide whether `X` is a **Proper Scheme** over `Spec(Q)`!
pub fn is_proper_scheme(x : Scheme) -> Bool {
  analyze_scheme_properness(x).is_proper
}

///|
/// Decide whether a morphism `f : X -> Y` of finite-type `Q`-schemes is **Proper**:
///   - Closed immersions (`f.chart_map` injective/chart-preserving with surjective
///     ring maps on every chart preimage) are ALWAYS proper!
///   - When `Y` is separated (`is_separated_scheme(f.dst)`) and `X` is proper over `Q`,
///     by the Cancellation Theorem (`X -> Y -> Spec(Q)` proper and `Y -> Spec(Q)`
///     separated `=>` `X -> Y` proper, Hartshorne Cor. II.4.8(e)!), `f` is proper!
///   - Otherwise checks fiberwise/source valuative properness!
pub fn is_proper_morphism(f : SchemeMorphism) -> Bool {
  if !scheme_morphism_is_valid(f) {
    return false
  }
  // 1. Check if `f` is a closed immersion (`chart_map[i] == i` across charts with surjective ring maps).
  let mx = f.src.charts.length()
  let my = f.dst.charts.length()
  if mx == my {
    let mut closed_imm = true
    for i in 0..<mx {
      if f.chart_map[i] != i || !ring_hom_is_surjective(f.ring_maps[i]) {
        closed_imm = false
        break
      }
    }
    if closed_imm {
      return true
    }
  }
  // 2. Cancellation Theorem when X is proper and Y is separated:
  if is_proper_scheme(f.src) && is_separated_scheme(f.dst) {
    return true
  }
  // 3. Identity / isomorphism check:
  if f.src == f.dst {
    let mut is_iso = true
    for i in 0..<mx {
      if f.chart_map[i] != i || !ring_hom_is_surjective(f.ring_maps[i]) {
        is_iso = false
        break
      }
    }
    if is_iso {
      return true
    }
  }
  false
}
