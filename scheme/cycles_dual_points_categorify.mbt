///|
// Scheme Pillar — Layer 4: Rational Equivalence & Chow Groups (Weil/Principal
// Divisors on P^1, Bézout's Intersection Multiplicity Theorem on P^2),
// Grothendieck–Serre Dualizing Complexes (ω_{P^1}^• = O(-2)[1], ω_{P^2}^• = O(-3)[2],
// and ω_C^• = O_C(d-3)[1] via Exact Čech Cohomology & Laurent Principal Parts),
// Functor of Points h_X(R) over Finite Local/Artinian Rings & Zariski Tangent
// Spaces, and Multi-Projective Gröbner Chow Correspondence Categorification h(P^1) = 1 ⊕ L.

///|
/// Closed prime divisor on `P^1_Q`: either the point at infinity `[0 : 1]`
/// or the Galois orbit cut out by a monic irreducible polynomial `p(u) ∈ Q[u]`
/// on `U_0 = Spec(Q[u])` (residue degree `[κ(P) : Q] = deg(p)`)!
pub(all) enum PrimeDivisorP1 {
  PointAtInfinity
  FiniteIrreducible(@exactalg.QPoly)
} derive(Debug, Eq)

///|
pub extend PrimeDivisorP1 with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend PrimeDivisorP1 with Eq::{not_equal, equal}

///|
/// Canonical Weil divisor `Σ_i mults[i] * [primes[i]]` on `P^1_Q`.
pub(all) struct WeilDivisorP1 {
  terms : Array[(PrimeDivisorP1, Int32)]
} derive(Debug, Eq)

///|
pub extend WeilDivisorP1 with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend WeilDivisorP1 with Eq::{not_equal, equal}

///|
/// Cohomology summary `(h^0, h^1, euler_characteristic)` of `O_{P^1}(n)`.
pub(all) struct P1LineBundleCohomology {
  twist : Int32
  h0 : Int32
  h1 : Int32
  chi : Int32
} derive(Debug, Eq)

///|
pub extend P1LineBundleCohomology with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend P1LineBundleCohomology with Eq::{not_equal, equal}

///|
/// Cohomology summary `(h^0, h^1, h^2, chi)` of `O_{P^2}(n)` computed from the
/// exact 3-chart Čech cochain complex `C^0 -> C^1 -> C^2` on `P^2_Q`.
pub(all) struct P2LineBundleCohomology {
  twist : Int32
  h0 : Int32
  h1 : Int32
  h2 : Int32
  chi : Int32
} derive(Debug, Eq)

///|
pub extend P2LineBundleCohomology with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend P2LineBundleCohomology with Eq::{not_equal, equal}

///|
/// Grothendieck–Serre Dualizing Complex report for a projective plane curve
/// `C = V_+(F) ⊆ P^2_Q` of degree `d >= 1`, where
/// `ω_C^• = RHom_{P^2}(O_C, ω_{P^2}^•) ≅ O_C(d - 3)[1]`!
pub(all) struct PlaneCurveDualizingReport {
  degree : Int32
  canonical_twist : Int32
  arithmetic_genus : Int32
  h0_oc : Int32
  h1_oc : Int32
  h0_omega : Int32
  h1_omega : Int32
  serre_duality_holds : Bool
} derive(Debug, Eq)

///|
pub extend PlaneCurveDualizingReport with @moonbitlang/core/debug.Debug::{
  to_repr,
}

///|
pub extend PlaneCurveDualizingReport with Eq::{not_equal, equal}

///|
/// Explicit finite commutative ring `(carrier = {0..size-1}, zero, one, +, *)`
/// used as a test algebra `R ∈ CommRing` for Grothendieck's **Functor of Points**
/// `h_X(R) = Hom_{Sch}(Spec(R), X)`!
pub(all) struct FiniteCommRing {
  size : Int32
  zero : Int32
  one : Int32
  neg_table : Array[Int32]
  add_table : Array[Int32]
  mul_table : Array[Int32]
} derive(Debug, Eq)

///|
pub extend FiniteCommRing with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend FiniteCommRing with Eq::{not_equal, equal}

///|
/// Morphism of finite commutative rings `φ : src -> dst` (`values.length() == src.size`).
pub(all) struct FiniteRingHom {
  src : FiniteCommRing
  dst : FiniteCommRing
  values : Array[Int32]
} derive(Debug, Eq)

///|
pub extend FiniteRingHom with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend FiniteRingHom with Eq::{not_equal, equal}

// =============================================================================
// 1. Rational Equivalence, Weil / Principal Divisors & Bézout's Theorem
// =============================================================================

///|
fn prime_divisor_cmp(a : PrimeDivisorP1, b : PrimeDivisorP1) -> Int32 {
  match (a, b) {
    (PointAtInfinity, PointAtInfinity) => 0
    (PointAtInfinity, FiniteIrreducible(_)) => -1
    (FiniteIrreducible(_), PointAtInfinity) => 1
    (FiniteIrreducible(pa), FiniteIrreducible(pb)) => {
      let da = @exactalg.qpoly_degree(pa)
      let db = @exactalg.qpoly_degree(pb)
      if da != db {
        return if da < db { -1 } else { 1 }
      }
      for k = da; k >= 0; k = k - 1 {
        let c = @exactalg.rat_cmp_exact(
          @exactalg.qpoly_coeff(pa, k),
          @exactalg.qpoly_coeff(pb, k),
        )
        if c != 0 {
          return c
        }
      }
      0
    }
  }
}

///|
/// Normalize a `WeilDivisorP1` by sorting prime divisors and combining multiplicities.
pub fn weil_divisor_p1_normalize(
  raw : Array[(PrimeDivisorP1, Int32)],
) -> WeilDivisorP1 {
  let non_zero : Array[(PrimeDivisorP1, Int32)] = []
  for pair in raw {
    if pair.1 != 0 {
      non_zero.push(pair)
    }
  }
  let m = non_zero.length()
  for i in 0..<m {
    for j in (i + 1)..<m {
      if prime_divisor_cmp(non_zero[j].0, non_zero[i].0) < 0 {
        let tmp = non_zero[i]
        non_zero[i] = non_zero[j]
        non_zero[j] = tmp
      }
    }
  }
  let merged : Array[(PrimeDivisorP1, Int32)] = []
  for pair in non_zero {
    if merged.length() > 0 && merged[merged.length() - 1].0 == pair.0 {
      guard merged.pop() is Some(prev) else {
        abort("weil_divisor_p1_normalize: empty merge stack")
      }
      let s = prev.1 + pair.1
      if s != 0 {
        merged.push((prev.0, s))
      }
    } else {
      merged.push(pair)
    }
  }
  { terms: merged, }
}

///|
/// Addition `D_1 + D_2` of Weil divisors on `P^1_Q`.
pub fn weil_divisor_p1_add(
  d1 : WeilDivisorP1,
  d2 : WeilDivisorP1,
) -> WeilDivisorP1 {
  let raw = d1.terms.copy()
  for t in d2.terms {
    raw.push(t)
  }
  weil_divisor_p1_normalize(raw)
}

///|
/// Subtraction `D_1 - D_2` of Weil divisors on `P^1_Q`.
pub fn weil_divisor_p1_sub(
  d1 : WeilDivisorP1,
  d2 : WeilDivisorP1,
) -> WeilDivisorP1 {
  let raw = d1.terms.copy()
  for t in d2.terms {
    raw.push((t.0, -t.1))
  }
  weil_divisor_p1_normalize(raw)
}

///|
/// Degree `deg(D) = Σ_P n_P * [κ(P) : Q]` of a Weil divisor on `P^1_Q`!
pub fn weil_divisor_p1_degree(d : WeilDivisorP1) -> Int32 {
  let mut total = 0
  for pair in d.terms {
    let res_deg = match pair.0 {
      PointAtInfinity => 1
      FiniteIrreducible(p) => @exactalg.qpoly_degree(p)
    }
    total = total + pair.1 * res_deg
  }
  total
}

///|
/// Compute the exact **Principal Divisor** `div(num / den)` on `P^1_Q` for any
/// nonzero rational function `r(u) = num(u) / den(u) ∈ Q(P^1)^×` via complete
/// rational polynomial factorization (`@exactalg.qpoly_factor_complete`)!
pub fn principal_divisor_p1(
  num : @exactalg.QPoly,
  den : @exactalg.QPoly,
) -> WeilDivisorP1 {
  guard !@exactalg.qpoly_is_zero(num) && !@exactalg.qpoly_is_zero(den) else {
    abort("principal_divisor_p1: rational function must be nonzero and finite")
  }
  let raw : Array[(PrimeDivisorP1, Int32)] = []
  let f_num = @exactalg.qpoly_factor_complete(num)
  for pair in f_num.factors {
    raw.push((FiniteIrreducible(pair.factor), pair.multiplicity))
  }
  let f_den = @exactalg.qpoly_factor_complete(den)
  for pair in f_den.factors {
    raw.push((FiniteIrreducible(pair.factor), -pair.multiplicity))
  }
  let ord_inf = @exactalg.qpoly_degree(den) - @exactalg.qpoly_degree(num)
  if ord_inf != 0 {
    raw.push((PointAtInfinity, ord_inf))
  }
  weil_divisor_p1_normalize(raw)
}

///|
fn qpoly_pow_int(p : @exactalg.QPoly, e : Int32) -> @exactalg.QPoly {
  let mut acc = @exactalg.qpoly_one()
  for _ in 0..<e {
    acc = @exactalg.qpoly_mul(acc, p)
  }
  acc
}

///|
/// Decide **Rational Equivalence** `D_1 ~_rat D_2` in `CH^1(P^1_Q)` AND construct
/// the explicit rational function witness `(num(u), den(u))` proving
/// `D_1 - D_2 == div(num / den)` whenever `deg(D_1) == deg(D_2)`!
pub fn rational_equivalence_witness_p1(
  d1 : WeilDivisorP1,
  d2 : WeilDivisorP1,
) -> (@exactalg.QPoly, @exactalg.QPoly)? {
  if weil_divisor_p1_degree(d1) != weil_divisor_p1_degree(d2) {
    return None
  }
  let diff = weil_divisor_p1_sub(d1, d2)
  let mut num = @exactalg.qpoly_one()
  let mut den = @exactalg.qpoly_one()
  for pair in diff.terms {
    match pair.0 {
      PointAtInfinity => ()
      FiniteIrreducible(p) =>
        if pair.1 > 0 {
          num = @exactalg.qpoly_mul(num, qpoly_pow_int(p, pair.1))
        } else if pair.1 < 0 {
          den = @exactalg.qpoly_mul(den, qpoly_pow_int(p, -pair.1))
        }
    }
  }
  // Certify `div(num / den) == D_1 - D_2` (including at PointAtInfinity automatically!).
  if principal_divisor_p1(num, den) == diff {
    Some((num, den))
  } else {
    None
  }
}

///|
/// Decide `D_1 ~_rat D_2` on `P^1_Q` (`CH^1(P^1_Q) ≅ Z`).
pub fn are_rationally_equivalent_p1(
  d1 : WeilDivisorP1,
  d2 : WeilDivisorP1,
) -> Bool {
  match rational_equivalence_witness_p1(d1, d2) {
    Some(_) => true
    None => false
  }
}

///|
/// **Bézout's Intersection Theorem on `P^2_Q`**:
/// Computes the exact scheme-theoretic intersection number `I(F, G)` of two
/// properly intersecting homogeneous polynomials `F(X_0, X_1, X_2)` and
/// `G(X_0, X_1, X_2)` across `P^2 = U_0 ⊔ (U_1 \ U_0) ⊔ {[0:0:1]}` using Artinian
/// Gröbner quotient dimensions and saturation away from previously counted charts!
/// Returns `None` if `V_+(F) ∩ V_+(G)` has positive Krull dimension (shared component).
pub fn bezout_intersection_number_p2(
  f_homog : MPoly,
  g_homog : MPoly,
) -> Int32? {
  guard f_homog.nvars == 3 && g_homog.nvars == 3 else { return None }
  // 1. Contribution on U_0 = {X_0 != 0}:
  let i0 = ideal_new(2, [
    mpoly_dehomogenize(f_homog, 0),
    mpoly_dehomogenize(g_homog, 0),
  ])
  let m0 = match ideal_quotient_vector_space_dim(i0) {
    Some(d) => d
    None => return None
  }
  // 2. Contribution on U_1 \ U_0 (coords c = X_0/X_1, d = X_2/X_1; isolate c == 0 via saturation!):
  let i1 = ideal_new(2, [
    mpoly_dehomogenize(f_homog, 1),
    mpoly_dehomogenize(g_homog, 1),
  ])
  let d1_all = match ideal_quotient_vector_space_dim(i1) {
    Some(d) => d
    None => return None
  }
  let i1_away = ideal_saturate(i1, mpoly_var(2, 0))
  let d1_away = match ideal_quotient_vector_space_dim(i1_away) {
    Some(d) => d
    None => return None
  }
  let m1 = d1_all - d1_away
  // 3. Contribution at [0 : 0 : 1] = U_2 \ (U_0 ∪ U_1) (coords e = X_0/X_2, f = X_1/X_2):
  let i2 = ideal_new(2, [
    mpoly_dehomogenize(f_homog, 2),
    mpoly_dehomogenize(g_homog, 2),
  ])
  let d2_all = match ideal_quotient_vector_space_dim(i2) {
    Some(d) => d
    None => return None
  }
  let i2_away = ideal_intersect(
    ideal_saturate(i2, mpoly_var(2, 0)),
    ideal_saturate(i2, mpoly_var(2, 1)),
  )
  let d2_away = match ideal_quotient_vector_space_dim(i2_away) {
    Some(d) => d
    None => return None
  }
  let m2 = d2_all - d2_away
  Some(m0 + m1 + m2)
}

///|
/// Verify **Bézout's Theorem** `I(F, G) == deg(F) * deg(G)` for two properly
/// intersecting homogeneous curves on `P^2_Q`!
pub fn verify_bezout_theorem_p2(f_homog : MPoly, g_homog : MPoly) -> Bool {
  let df = mpoly_total_degree(f_homog)
  let dg = mpoly_total_degree(g_homog)
  if df < 0 || dg < 0 {
    return false
  }
  match bezout_intersection_number_p2(f_homog, g_homog) {
    Some(inter) => inter == df * dg
    None => false
  }
}

// =============================================================================
// 2. Dual Complexes: Grothendieck–Serre Dualizing Complex & Boundary Dual Complex
// =============================================================================

///|
/// Compute the exact sheaf cohomology `(h^0(P^1, O(n)), h^1(P^1, O(n)), χ)` of
/// the twisted line bundle `O_{P^1}(n)` via the exact Čech cochain differential
/// `δ_n : O(n)(U_0) ⊕ O(n)(U_1) -> O(n)(U_{01})` (`(p_0(u), p_1(v)) ↦ p_0(u) - u^n p_1(u^{-1})`)
/// on the sufficient Laurent window `[n - N, N]` (`N = |n| + 3`) over `@exactalg.Rat`!
pub fn cech_cohomology_p1_line_bundle(twist : Int32) -> P1LineBundleCohomology {
  let abs_n = if twist >= 0 { twist } else { -twist }
  let cap = abs_n + 3
  let dim_c0 = 2 * (cap + 1)
  let min_exp = twist - cap
  let max_exp = cap
  let dim_c1 = max_exp - min_exp + 1
  let rows : Array[Array[@exactalg.Rat]] = []
  for r in 0..<dim_c1 {
    let exp_u = min_exp + r
    let row = Array::make(dim_c0, @exactalg.rat_zero())
    // Basis of O(n)(U_0): u^a for a ∈ [0..cap] -> +u^a
    if exp_u >= 0 && exp_u <= cap {
      row[exp_u] = @exactalg.rat_one()
    }
    // Basis of O(n)(U_1): v^b for b ∈ [0..cap] -> -u^{twist - b}, so b = twist - exp_u!
    let b = twist - exp_u
    if b >= 0 && b <= cap {
      row[cap + 1 + b] = @exactalg.rat_int(-1)
    }
    rows.push(row)
  }
  let rk = @exactalg.qrows_rank(rows, dim_c0)
  let h0 = dim_c0 - rk
  let h1 = dim_c1 - rk
  { twist, h0, h1, chi: h0 - h1, }
}

///|
/// **Grothendieck–Serre Duality & Riemann–Roch Theorem on `P^1_Q`**
/// with canonical **Dualizing Complex** `ω_{P^1}^• = Ω^1_{P^1}[1] ≅ O_{P^1}(-2)[1]`:
///   1. `h^1(P^1, ω_{P^1}) == 1` (canonical Grothendieck trace isomorphism);
///   2. `h^0(P^1, O(n)) == h^1(P^1, O(-2 - n))` and `h^1(P^1, O(n)) == h^0(P^1, O(-2 - n))`;
///   3. `χ(P^1, O(n)) = h^0 - h^1 == n + 1 = deg(O(n)) + 1 - g` (`g = 0`)!
pub fn verify_serre_duality_and_riemann_roch_p1(twist : Int32) -> Bool {
  let omega = cech_cohomology_p1_line_bundle(-2)
  if omega.h0 != 0 || omega.h1 != 1 {
    return false
  }
  let c_n = cech_cohomology_p1_line_bundle(twist)
  let c_dual = cech_cohomology_p1_line_bundle(-2 - twist)
  c_n.h0 == c_dual.h1 && c_n.h1 == c_dual.h0 && c_n.chi == twist + 1
}

///|
/// Compute the exact sheaf cohomology `(h^0, h^1, h^2, χ)` of `O_{P^2}(n)` by
/// assembling the explicit 3-chart Čech cochain matrices
/// `C^0 = ⊕_i O(n)(U_i) --d^0--> C^1 = ⊕_{i<j} O(n)(U_{ij}) --d^1--> C^2 = O(n)(U_{012})`
/// on homogeneous Laurent monomials `X_0^{e_0} X_1^{e_1} X_2^{e_2}` (`e_0 + e_1 + e_2 = n`,
/// `e_k >= -( |n| + 3 )`) and taking exact rational matrix ranks (`@exactalg.qrows_rank`)!
pub fn cech_cohomology_p2_line_bundle(twist : Int32) -> P2LineBundleCohomology {
  let abs_n = if twist >= 0 { twist } else { -twist }
  let lb = -(abs_n + 3)
  let ub = twist - 2 * lb
  // Collect all degree-`twist` Laurent weights `(e_0, e_1, e_2)` with `e_i >= lb`.
  let weights : Array[(Int32, Int32, Int32)] = []
  for e0 in lb..<(ub + 1) {
    for e1 in lb..<(ub + 1) {
      let e2 = twist - e0 - e1
      if e2 >= lb {
        weights.push((e0, e1, e2))
      }
    }
  }
  // Basis of C^0: (chart i ∈ {0,1,2}, weight idx) where e_j >= 0 for j != i.
  let c0_basis : Array[(Int32, Int32)] = []
  for w_idx in 0..<weights.length() {
    let (e0, e1, e2) = weights[w_idx]
    if e1 >= 0 && e2 >= 0 {
      c0_basis.push((0, w_idx))
    }
    if e0 >= 0 && e2 >= 0 {
      c0_basis.push((1, w_idx))
    }
    if e0 >= 0 && e1 >= 0 {
      c0_basis.push((2, w_idx))
    }
  }
  // Basis of C^1: (pair p ∈ {0=(0,1), 1=(0,2), 2=(1,2)}, weight idx) where remaining e_k >= 0.
  let c1_basis : Array[(Int32, Int32)] = []
  for w_idx in 0..<weights.length() {
    let (e0, e1, e2) = weights[w_idx]
    if e2 >= 0 {
      c1_basis.push((0, w_idx))
    }
    if e1 >= 0 {
      c1_basis.push((1, w_idx))
    }
    if e0 >= 0 {
      c1_basis.push((2, w_idx))
    }
  }
  let dim_c0 = c0_basis.length()
  let dim_c1 = c1_basis.length()
  let dim_c2 = weights.length()
  // Assemble d^0 : C^0 -> C^1 (`(s_0, s_1, s_2) ↦ (s_1 - s_0, s_2 - s_0, s_2 - s_1)`)
  // Wait: the Čech complex decomposes as a direct sum over torus weights `w_idx`,
  // OR we can assemble the block-diagonal global cochain matrix directly!
  // Let's assemble per-weight exact cochain matrices and sum exact ranks via `@exactalg.qrows_rank`
  // (mathematically identical to global rank of block-diagonal `d^0`, `d^1`, while remaining O(weights) instead of O(weights^3)!).
  let mut rk0 = 0
  let mut rk1 = 0
  for w_idx in 0..<weights.length() {
    let (e0, e1, e2) = weights[w_idx]
    let c0_charts : Array[Int32] = []
    if e1 >= 0 && e2 >= 0 {
      c0_charts.push(0)
    }
    if e0 >= 0 && e2 >= 0 {
      c0_charts.push(1)
    }
    if e0 >= 0 && e1 >= 0 {
      c0_charts.push(2)
    }
    let c1_pairs : Array[(Int32, Int32)] = []
    if e2 >= 0 {
      c1_pairs.push((0, 1))
    }
    if e1 >= 0 {
      c1_pairs.push((0, 2))
    }
    if e0 >= 0 {
      c1_pairs.push((1, 2))
    }
    if c1_pairs.length() > 0 && c0_charts.length() > 0 {
      let rows0 : Array[Array[@exactalg.Rat]] = []
      for pair in c1_pairs {
        let row = Array::make(c0_charts.length(), @exactalg.rat_zero())
        for col in 0..<c0_charts.length() {
          if c0_charts[col] == pair.1 {
            row[col] = @exactalg.rat_one()
          } else if c0_charts[col] == pair.0 {
            row[col] = @exactalg.rat_int(-1)
          }
        }
        rows0.push(row)
      }
      rk0 = rk0 + @exactalg.qrows_rank(rows0, c0_charts.length())
    }
    if c1_pairs.length() > 0 {
      let row1 = Array::make(c1_pairs.length(), @exactalg.rat_zero())
      for col in 0..<c1_pairs.length() {
        let p = c1_pairs[col]
        // d^1(t_{01}, t_{02}, t_{12}) = t_{12} - t_{02} + t_{01}
        if p == (1, 2) {
          row1[col] = @exactalg.rat_one()
        } else if p == (0, 2) {
          row1[col] = @exactalg.rat_int(-1)
        } else {
          row1[col] = @exactalg.rat_one()
        }
      }
      rk1 = rk1 + @exactalg.qrows_rank([row1], c1_pairs.length())
    }
  }
  let h0 = dim_c0 - rk0
  let h1 = dim_c1 - rk1 - rk0
  let h2 = dim_c2 - rk1
  { twist, h0, h1, h2, chi: h0 - h1 + h2, }
}

///|
/// **Grothendieck–Serre Duality on `P^2_Q`** with canonical **Dualizing Complex**
/// `ω_{P^2}^• = Ω^2_{P^2}[2] ≅ O_{P^2}(-3)[2]`:
///   1. `h^2(P^2, ω_{P^2}) == 1` (`1 / (X_0 X_1 X_2)` residue trace), `h^0 == h^1 == 0`;
///   2. `h^i(P^2, O(n)) == h^{2-i}(P^2, O(-3 - n))` for `i = 0, 1, 2`;
///   3. Hilbert polynomial `χ(P^2, O(n)) == (n + 1)(n + 2) / 2`!
pub fn verify_serre_duality_p2(twist : Int32) -> Bool {
  let omega = cech_cohomology_p2_line_bundle(-3)
  if omega.h0 != 0 || omega.h1 != 0 || omega.h2 != 1 {
    return false
  }
  let c_n = cech_cohomology_p2_line_bundle(twist)
  let c_dual = cech_cohomology_p2_line_bundle(-3 - twist)
  c_n.h0 == c_dual.h2 &&
  c_n.h1 == c_dual.h1 &&
  c_n.h2 == c_dual.h0 &&
  2 * c_n.chi == (twist + 1) * (twist + 2)
}

///|
/// Exact cohomology `(h^0(C, O_C(m)), h^1(C, O_C(m)))` of a twisted sheaf `O_C(m)`
/// on a projective plane curve `C = V_+(f_homog) ⊆ P^2_Q` of degree `d >= 1`,
/// computed from the Koszul exact sequence `0 -> O_{P^2}(m - d) --(* F)--> O_{P^2}(m) -> O_C(m) -> 0`
/// by assembling the **explicit polynomial multiplication matrix** `μ_0(F, m)` on `H^0`
/// and the **explicit Laurent principal-part multiplication matrix** `μ_2(F, m)` on
/// `H^2(P^2, O(·)) = span{ X_0^{e_0} X_1^{e_1} X_2^{e_2} | e_i <= -1 }`!
pub fn plane_curve_line_bundle_cohomology(
  f_homog : MPoly,
  twist : Int32,
) -> (Int32, Int32) {
  guard f_homog.nvars == 3 && !mpoly_is_zero(f_homog) else {
    abort(
      "plane_curve_line_bundle_cohomology: expected nonzero 3-var homogeneous F",
    )
  }
  let d = mpoly_total_degree(f_homog)
  guard d >= 1 else {
    abort("plane_curve_line_bundle_cohomology: degree must be >= 1")
  }
  // 1. H^0(C, O_C(m)) = coker( μ_0(F) : S_{m - d} -> S_m ) (since H^1(P^2, O(m - d)) = 0).
  fn poly_basis_deg(deg : Int32) -> Array[(Int32, Int32, Int32)] {
    let out : Array[(Int32, Int32, Int32)] = []
    if deg < 0 {
      return out
    }
    for e0 in 0..<(deg + 1) {
      for e1 in 0..<(deg - e0 + 1) {
        out.push((e0, e1, deg - e0 - e1))
      }
    }
    out
  }
  let s_prev = poly_basis_deg(twist - d)
  let s_cur = poly_basis_deg(twist)
  let rk_mu0 = if s_prev.length() == 0 || s_cur.length() == 0 {
    0
  } else {
    let rows0 : Array[Array[@exactalg.Rat]] = []
    for _ in 0..<s_cur.length() {
      rows0.push(Array::make(s_prev.length(), @exactalg.rat_zero()))
    }
    for col in 0..<s_prev.length() {
      let (a0, a1, a2) = s_prev[col]
      for t in f_homog.terms {
        let tgt = (a0 + t.exps[0], a1 + t.exps[1], a2 + t.exps[2])
        for r in 0..<s_cur.length() {
          if s_cur[r] == tgt {
            rows0[r][col] = @exactalg.rat_add(rows0[r][col], t.coeff)
            break
          }
        }
      }
    }
    @exactalg.qrows_rank(rows0, s_prev.length())
  }
  let h0_c = s_cur.length() - rk_mu0
  // 2. H^1(C, O_C(m)) = ker( μ_2(F) : H^2(P^2, O(m - d)) -> H^2(P^2, O(m)) )!
  fn h2_basis_deg(deg : Int32) -> Array[(Int32, Int32, Int32)] {
    let out : Array[(Int32, Int32, Int32)] = []
    if deg > -3 {
      return out
    }
    // e_0 <= -1, e_1 <= -1, e_2 = deg - e_0 - e_1 <= -1  <=>  deg + 2 <= e_0 <= -1
    for e0 in (deg + 2)..<0 {
      for e1 in (deg - e0 + 1)..<0 {
        let e2 = deg - e0 - e1
        if e2 <= -1 {
          out.push((e0, e1, e2))
        }
      }
    }
    out
  }
  let h2_prev = h2_basis_deg(twist - d)
  let h2_cur = h2_basis_deg(twist)
  let rk_mu2 = if h2_prev.length() == 0 || h2_cur.length() == 0 {
    0
  } else {
    let rows2 : Array[Array[@exactalg.Rat]] = []
    for _ in 0..<h2_cur.length() {
      rows2.push(Array::make(h2_prev.length(), @exactalg.rat_zero()))
    }
    for col in 0..<h2_prev.length() {
      let (e0, e1, e2) = h2_prev[col]
      for t in f_homog.terms {
        let tgt = (e0 + t.exps[0], e1 + t.exps[1], e2 + t.exps[2])
        if tgt.0 <= -1 && tgt.1 <= -1 && tgt.2 <= -1 {
          for r in 0..<h2_cur.length() {
            if h2_cur[r] == tgt {
              rows2[r][col] = @exactalg.rat_add(rows2[r][col], t.coeff)
              break
            }
          }
        }
      }
    }
    @exactalg.qrows_rank(rows2, h2_prev.length())
  }
  let h1_c = h2_prev.length() - rk_mu2
  (h0_c, h1_c)
}

///|
/// Compute and certify the **Grothendieck–Serre Dualizing Complex**
/// `ω_C^• = i^!(ω_{P^2}^•) = RHom_{P^2}(O_C, O_{P^2}(-3)[2]) ≅ O_C(d - 3)[1]`
/// of ANY plane curve `C = V_+(f_homog) ⊆ P^2_Q` (smooth OR singular Cohen–Macaulay!):
/// verifies Grothendieck–Serre duality `h^0(C, O_C(m)) == h^1(C, ω_C(-m))` and
/// Riemann–Roch `χ(C, O_C(m)) == d * m + 1 - p_a(C)` across twists `m ∈ [-2..d]`!
pub fn plane_curve_dualizing_complex(
  f_homog : MPoly,
) -> PlaneCurveDualizingReport {
  let d = mpoly_total_degree(f_homog)
  let can_twist = d - 3
  let (h0_oc, h1_oc) = plane_curve_line_bundle_cohomology(f_homog, 0)
  let (h0_omega, h1_omega) = plane_curve_line_bundle_cohomology(
    f_homog, can_twist,
  )
  let pa = h1_oc
  let mut ok = h0_oc == h1_omega &&
    h1_oc == h0_omega &&
    2 * pa == (d - 1) * (d - 2)
  for m in -2..<(d + 1) {
    let (h0_m, h1_m) = plane_curve_line_bundle_cohomology(f_homog, m)
    let (h0_dual, h1_dual) = plane_curve_line_bundle_cohomology(
      f_homog,
      can_twist - m,
    )
    if h0_m != h1_dual || h1_m != h0_dual || h0_m - h1_m != d * m + 1 - pa {
      ok = false
    }
  }
  {
    degree: d,
    canonical_twist: can_twist,
    arithmetic_genus: pa,
    h0_oc,
    h1_oc,
    h0_omega,
    h1_omega,
    serre_duality_holds: ok,
  }
}

// =============================================================================
// 3. Functor of Points h_X(R) = Hom_{Sch}(Spec(R), X) & Zariski Tangent Space
// =============================================================================

///|
/// Prime field `F_p = Z / pZ` as a `FiniteCommRing`.
pub fn fcomm_fp(p : Int32) -> FiniteCommRing {
  guard p >= 2 else { abort("fcomm_fp: p must be >= 2") }
  let neg_t = Array::make(p, 0)
  let add_t = Array::make(p * p, 0)
  let mul_t = Array::make(p * p, 0)
  for a in 0..<p {
    neg_t[a] = (p - a) % p
    for b in 0..<p {
      add_t[a * p + b] = (a + b) % p
      mul_t[a * p + b] = (a.to_int64() * b.to_int64() % p.to_int64()).to_int()
    }
  }
  {
    size: p,
    zero: 0,
    one: 1,
    neg_table: neg_t,
    add_table: add_t,
    mul_table: mul_t,
  }
}

///|
/// Ring of **Dual Numbers** `F_p[ε] / (ε^2)` (`size == p^2`, element `a + b * ε`
/// encoded as `a + b * p`) together with the canonical augmentation homomorphism
/// `π : F_p[ε]/(ε^2) ->> F_p` (`a + b * ε ↦ a`)!
pub fn fcomm_dual_numbers(p : Int32) -> (FiniteCommRing, FiniteRingHom) {
  let fp = fcomm_fp(p)
  let sz = p * p
  let neg_t = Array::make(sz, 0)
  let add_t = Array::make(sz * sz, 0)
  let mul_t = Array::make(sz * sz, 0)
  let proj_vals = Array::make(sz, 0)
  let p64 = p.to_int64()
  for x in 0..<sz {
    let a1 = x % p
    let b1 = x / p
    proj_vals[x] = a1
    neg_t[x] = (p - a1) % p + (p - b1) % p * p
    for y in 0..<sz {
      let a2 = y % p
      let b2 = y / p
      let sa = (a1 + a2) % p
      let sb = (b1 + b2) % p
      add_t[x * sz + y] = sa + sb * p
      let ma = (a1.to_int64() * a2.to_int64() % p64).to_int()
      let mb = ((a1.to_int64() * b2.to_int64() + b1.to_int64() * a2.to_int64()) %
      p64).to_int()
      mul_t[x * sz + y] = ma + mb * p
    }
  }
  let dual_ring : FiniteCommRing = {
    size: sz,
    zero: 0,
    one: 1,
    neg_table: neg_t,
    add_table: add_t,
    mul_table: mul_t,
  }
  (dual_ring, { src: dual_ring, dst: fp, values: proj_vals, })
}

///|
/// Direct product ring `R_1 × R_2` (`size == R_1.size * R_2.size`).
pub fn fcomm_product(
  r1 : FiniteCommRing,
  r2 : FiniteCommRing,
) -> FiniteCommRing {
  let s1 = r1.size
  let s2 = r2.size
  let sz = s1 * s2
  let neg_t = Array::make(sz, 0)
  let add_t = Array::make(sz * sz, 0)
  let mul_t = Array::make(sz * sz, 0)
  for x in 0..<sz {
    let a1 = x % s1
    let b1 = x / s1
    neg_t[x] = r1.neg_table[a1] + r2.neg_table[b1] * s1
    for y in 0..<sz {
      let a2 = y % s1
      let b2 = y / s1
      add_t[x * sz + y] = r1.add_table[a1 * s1 + a2] +
        r2.add_table[b1 * s2 + b2] * s1
      mul_t[x * sz + y] = r1.mul_table[a1 * s1 + a2] +
        r2.mul_table[b1 * s2 + b2] * s1
    }
  }
  {
    size: sz,
    zero: r1.zero + r2.zero * s1,
    one: r1.one + r2.one * s1,
    neg_table: neg_t,
    add_table: add_t,
    mul_table: mul_t,
  }
}

///|
/// Verify `hom : src -> dst` preserves `0, 1, +, *`.
pub fn finite_ring_hom_is_valid(hom : FiniteRingHom) -> Bool {
  let s = hom.src
  let d = hom.dst
  guard hom.values.length() == s.size else { return false }
  if hom.values[s.zero] != d.zero || hom.values[s.one] != d.one {
    return false
  }
  for a in 0..<s.size {
    for b in 0..<s.size {
      let lhs_add = hom.values[s.add_table[a * s.size + b]]
      let rhs_add = d.add_table[hom.values[a] * d.size + hom.values[b]]
      if lhs_add != rhs_add {
        return false
      }
      let lhs_mul = hom.values[s.mul_table[a * s.size + b]]
      let rhs_mul = d.mul_table[hom.values[a] * d.size + hom.values[b]]
      if lhs_mul != rhs_mul {
        return false
      }
    }
  }
  true
}

///|
fn fcomm_int_embed(r : FiniteCommRing, k_big : BigInt) -> Int32 {
  let mut k = k_big.to_int()
  let mut neg = false
  if k < 0 {
    neg = true
    k = -k
  }
  let mut acc = r.zero
  let mut base = r.one
  while k > 0 {
    if k % 2 == 1 {
      acc = r.add_table[acc * r.size + base]
    }
    k = k / 2
    if k > 0 {
      base = r.mul_table[base * r.size + base]
    }
  }
  if neg {
    r.neg_table[acc]
  } else {
    acc
  }
}

///|
fn fcomm_inv(r : FiniteCommRing, x : Int32) -> Int32? {
  for y in 0..<r.size {
    if r.mul_table[x * r.size + y] == r.one {
      return Some(y)
    }
  }
  None
}

///|
/// Evaluate a polynomial `f ∈ Q[x]` (whose coefficients have denominators invertible
/// in `r`) at a point `pt ∈ r^{nvars}`!
pub fn mpoly_eval_finite_ring(
  f : MPoly,
  r : FiniteCommRing,
  pt : Array[Int32],
) -> Int32? {
  let mut acc = r.zero
  for t in f.terms {
    let num_r = fcomm_int_embed(r, t.coeff.num)
    let den_r = fcomm_int_embed(r, t.coeff.den)
    let inv_den = match fcomm_inv(r, den_r) {
      Some(v) => v
      None => return None
    }
    let mut prod = r.mul_table[num_r * r.size + inv_den]
    for v in 0..<f.nvars {
      for _ in 0..<t.exps[v] {
        prod = r.mul_table[prod * r.size + pt[v]]
      }
    }
    acc = r.add_table[acc * r.size + prod]
  }
  Some(acc)
}

///|
/// Evaluate the **Affine Functor of Points** `h_{Spec(A)}(r) = Hom_{Ring}(A, r)`:
/// enumerates all `pt ∈ r^{nvars}` annihilating every generator of `aff.ring.ideal`!
pub fn eval_affine_functor_of_points(
  aff : AffineScheme,
  r : FiniteCommRing,
) -> Array[Array[Int32]] {
  let n = aff.ring.nvars
  let out : Array[Array[Int32]] = []
  let cur = Array::make(n, r.zero)
  fn search(pos : Int32) -> Unit {
    if pos == n {
      let mut ok = true
      for g in aff.ring.ideal.rgb.gens {
        match mpoly_eval_finite_ring(g, r, cur) {
          Some(v) =>
            if v != r.zero {
              ok = false
              break
            }
          None => {
            ok = false
            break
          }
        }
      }
      if ok {
        out.push(cur.copy())
      }
      return
    }
    for val in 0..<r.size {
      cur[pos] = val
      search(pos + 1)
    }
  }
  search(0)
  out
}

///|
fn eval_ring_hom_on_finite_point(
  hom : RingHom,
  r : FiniteCommRing,
  dst_pt : Array[Int32],
) -> Array[Int32]? {
  let out : Array[Int32] = []
  for img in hom.var_images {
    match mpoly_eval_finite_ring(img, r, dst_pt) {
      Some(v) => out.push(v)
      None => return None
    }
  }
  Some(out)
}

///|
/// Evaluate Grothendieck's **Glued Scheme Functor of Points** `h_X(r)` for a
/// local finite commutative ring `r` (`F_p`, `F_p[ε]/(ε^2)`, `F_p[t]/(t^k)`):
/// computes the exact coequalizer `(∐_i U_i(r)) / (∐_{i,j} U_{ij}(r))` across
/// all affine charts and overlaps of `X`, returning canonical `(chart_idx, pt)`
/// representatives of each equivalence class!
pub fn eval_scheme_functor_of_points(
  x : Scheme,
  r : FiniteCommRing,
) -> Array[(Int32, Array[Int32])] {
  let m = x.charts.length()
  let all_pts : Array[(Int32, Array[Int32])] = []
  for i in 0..<m {
    let c_pts = eval_affine_functor_of_points(x.charts[i], r)
    for pt in c_pts {
      all_pts.push((i, pt))
    }
  }
  let total = all_pts.length()
  if total == 0 {
    return []
  }
  let parent = Array::make(total, 0)
  for k in 0..<total {
    parent[k] = k
  }
  fn find_root(idx : Int32) -> Int32 {
    let mut cur = idx
    while parent[cur] != cur {
      parent[cur] = parent[parent[cur]]
      cur = parent[cur]
    }
    cur
  }
  for i in 0..<m {
    for j in (i + 1)..<m {
      let ov = x.overlaps[i * m + j]
      if ov.is_empty {
        continue
      }
      let ov_pts = eval_affine_functor_of_points(affine_scheme(ov.ring), r)
      for ov_pt in ov_pts {
        match
          (
            eval_ring_hom_on_finite_point(ov.from_i, r, ov_pt),
            eval_ring_hom_on_finite_point(ov.from_j, r, ov_pt),
          ) {
          (Some(pi), Some(pj)) => {
            let mut idx_i = -1
            let mut idx_j = -1
            for k in 0..<total {
              if all_pts[k].0 == i && all_pts[k].1 == pi {
                idx_i = k
              }
              if all_pts[k].0 == j && all_pts[k].1 == pj {
                idx_j = k
              }
            }
            if idx_i >= 0 && idx_j >= 0 {
              let ri = find_root(idx_i)
              let rj = find_root(idx_j)
              if ri != rj {
                if ri < rj {
                  parent[rj] = ri
                } else {
                  parent[ri] = rj
                }
              }
            }
          }
          _ => ()
        }
      }
    }
  }
  let reps : Array[(Int32, Array[Int32])] = []
  for k in 0..<total {
    if find_root(k) == k {
      reps.push(all_pts[k])
    }
  }
  reps
}

///|
/// Push forward an `r_1`-point of `aff` along a ring homomorphism `hom : r_1 -> r_2`
/// (`h_{Spec(A)}(hom) : h_{Spec(A)}(r_1) -> h_{Spec(A)}(r_2)`), verifying functoriality!
pub fn pushforward_affine_point(
  hom : FiniteRingHom,
  pt : Array[Int32],
) -> Array[Int32] {
  let out : Array[Int32] = []
  for v in pt {
    out.push(hom.values[v])
  }
  out
}

///|
/// Compute the exact **Zariski Tangent Dimension** `dim_{F_p} T_{base_pt}(aff)`
/// at an `F_p`-point `base_pt ∈ aff(F_p)` PURELY FUNCTORIALLY as `log_p` of the
/// fiber cardinality of `h_{aff}(F_p[ε]/(ε^2)) -> h_{aff}(F_p)` over `base_pt`!
pub fn zariski_tangent_dimension_fp(
  aff : AffineScheme,
  p : Int32,
  base_pt : Array[Int32],
) -> Int32 {
  let (dual_r, aug) = fcomm_dual_numbers(p)
  let dual_pts = eval_affine_functor_of_points(aff, dual_r)
  let mut fiber_card = 0
  for dpt in dual_pts {
    if pushforward_affine_point(aug, dpt) == base_pt {
      fiber_card = fiber_card + 1
    }
  }
  // Since T_{x_0} X is an F_p-vector space, `fiber_card == p^d`!
  let mut d = 0
  let mut cur = 1
  while cur < fiber_card {
    cur = cur * p
    d = d + 1
  }
  d
}

// =============================================================================
// 4. Categorification: Multi-Projective Gröbner Chow Correspondences & h(P^1) = 1 ⊕ L
// =============================================================================

///|
/// Extract the exact Chow bidegree `(d_1, d_2) ∈ CH^1(P^1 × P^1) ≅ Z[H_1] ⊕ Z[H_2]`
/// of a bihomogeneous algebraic 1-cycle `V_+(z) ⊆ P^1_X × P^1_Y` in 4 variables
/// `(X_0, X_1, Y_0, Y_1)`. Returns `None` if `z` is zero or not bihomogeneous!
pub fn p1_correspondence_bidegree(z : MPoly) -> (Int32, Int32)? {
  if z.nvars != 4 || mpoly_is_zero(z) {
    return None
  }
  let t0 = z.terms[0].exps
  let d1 = t0[0] + t0[1]
  let d2 = t0[2] + t0[3]
  for i in 1..<z.terms.length() {
    let e = z.terms[i].exps
    if e[0] + e[1] != d1 || e[2] + e[3] != d2 {
      return None
    }
  }
  Some((d1, d2))
}

///|
/// **Multi-Projective Gröbner Composition of Algebraic Correspondences on `P^1 × P^1`**:
/// Given bihomogeneous defining equations `z12(X_0, X_1, Y_0, Y_1)` on `P^1_X × P^1_Y`
/// and `z23(Y_0, Y_1, Z_0, Z_1)` on `P^1_Y × P^1_Z`:
///   1. Embeds `p_{12}^*(z12)` and `p_{23}^*(z23)` into `Q[Y_0, Y_1, X_0, X_1, Z_0, Z_1]`;
///   2. Saturates by the irrelevant ideal `<Y_0, Y_1>` (`(I : Y_0^∞) ∩ (I : Y_1^∞)`)
///      so base-locus artifacts at `Y = (0, 0)` vanish (yielding `<1>` when disjoint!);
///   3. Eliminates `(Y_0, Y_1)` via Buchberger `ideal_eliminate_first_k(..., 2)`;
///   4. Bihomogeneously saturates by `<X_0, X_1>` and `<Z_0, Z_1>` in `Q[X_0, X_1, Z_0, Z_1]`!
/// Returns the exact scheme-theoretic correspondence ideal `(p_{13})_*(p_{12}^* Z_{12} ∩ p_{23}^* Z_{23})`.
pub fn compose_p1_correspondences_groebner(z12 : MPoly, z23 : MPoly) -> Ideal {
  guard z12.nvars == 4 && z23.nvars == 4 else {
    abort(
      "compose_p1_correspondences_groebner: expected 4-var bihomogeneous polynomials",
    )
  }
  // Variable ordering in 6-space: (Y_0, Y_1, X_0, X_1, Z_0, Z_1) = (0, 1, 2, 3, 4, 5).
  let terms12 : Array[MTerm] = []
  for t in z12.terms {
    terms12.push({
      coeff: t.coeff,
      exps: [t.exps[2], t.exps[3], t.exps[0], t.exps[1], 0, 0],
    })
  }
  let terms23 : Array[MTerm] = []
  for t in z23.terms {
    terms23.push({
      coeff: t.coeff,
      exps: [t.exps[0], t.exps[1], 0, 0, t.exps[2], t.exps[3]],
    })
  }
  let i6 = ideal_new(6, [
    mpoly_from_terms(6, terms12),
    mpoly_from_terms(6, terms23),
  ])
  let sat_y = ideal_intersect(
    ideal_saturate(i6, mpoly_var(6, 0)),
    ideal_saturate(i6, mpoly_var(6, 1)),
  )
  let elim_xz = ideal_eliminate_first_k(sat_y, 2)
  let sat_x = ideal_intersect(
    ideal_saturate(elim_xz, mpoly_var(4, 0)),
    ideal_saturate(elim_xz, mpoly_var(4, 1)),
  )
  ideal_intersect(
    ideal_saturate(sat_x, mpoly_var(4, 2)),
    ideal_saturate(sat_x, mpoly_var(4, 3)),
  )
}

///|
/// Verify **Grothendieck Chow Motive Categorification `h(P^1) ≅ 1 ⊕ L`** via
/// genuine 6-variable Buchberger Gröbner correspondence composition on `P^1 × P^1`
/// (with zero matrix stubs!):
///   1. Transverse motive projectors `π_0 = V_+(X_0)` (`{[0:1]} × P^1`, bidegree `(1, 0)`)
///      and `π_2 = V_+(Y_1)` (`P^1 × {[1:0]}`, bidegree `(0, 1)`) satisfy:
///      - `π_0 ∘ π_0 == <X_0>` and `π_2 ∘ π_2 == <Z_1>` (idempotency);
///      - `π_0 ∘ π_2 == <1>` (empty intersection -> zero cycle orthogonality!);
///   2. Completeness `[Δ_{P^1}] == [π_0] + [π_2]` in `CH^1(P^1 × P^1)` (`(1, 1) = (1, 0) + (0, 1)`,
///      cut out by rational function `(X_0 Y_1 - X_1 Y_0) / (X_0 Y_1)`);
///   3. Diagonal `Δ = V_+(X_0 Y_1 - X_1 Y_0)` acts as identity on the squaring
///      morphism graph `Γ_sq = V_+(X_0^2 Y_1 - X_1^2 Y_0)` (`Δ ∘ Γ_sq == Γ_sq`),
///      involution `Γ_σ = V_+(X_0 Y_0 - X_1 Y_1)` satisfies `Γ_σ ∘ Γ_σ == Δ`, and
///      `Γ_sq ∘ Γ_sq == V_+(X_0^4 Z_1 - X_1^4 Z_0)` (bidegree `(4, 1)`)!
///   4. Decategorified Frobenius trace matches `|h_{P^1}(F_p)| == 1 + p`!
pub fn verify_motivic_p1_categorification(p : Int32) -> Bool {
  let x0 = mpoly_var(4, 0)
  let x1 = mpoly_var(4, 1)
  let y0 = mpoly_var(4, 2)
  let y1 = mpoly_var(4, 3)
  let pi0 = x0
  let pi2 = y1
  let delta = mpoly_sub(mpoly_mul(x0, y1), mpoly_mul(x1, y0))
  let gamma_sigma = mpoly_sub(mpoly_mul(x0, y0), mpoly_mul(x1, y1))
  let gamma_sq = mpoly_sub(
    mpoly_mul(mpoly_pow(x0, 2), y1),
    mpoly_mul(mpoly_pow(x1, 2), y0),
  )
  let gamma_fourth = mpoly_sub(
    mpoly_mul(mpoly_pow(x0, 4), y1),
    mpoly_mul(mpoly_pow(x1, 4), y0),
  )
  // 1. Check bidegree completeness [Δ] = (1, 1) = (1, 0) + (0, 1) = [π_0] + [π_2]:
  let (b_pi0, b_pi2, b_delta) = match
    (
      p1_correspondence_bidegree(pi0),
      p1_correspondence_bidegree(pi2),
      p1_correspondence_bidegree(delta),
    ) {
    (Some(a), Some(b), Some(c)) => (a, b, c)
    _ => return false
  }
  if b_pi0 != (1, 0) ||
    b_pi2 != (0, 1) ||
    b_delta != (b_pi0.0 + b_pi2.0, b_pi0.1 + b_pi2.1) {
    return false
  }
  // 2. Check idempotency and orthogonality via 6-var Gröbner saturation + elimination:
  if !ideal_eq(
      compose_p1_correspondences_groebner(pi0, pi0),
      ideal_new(4, [pi0]),
    ) {
    return false
  }
  if !ideal_eq(
      compose_p1_correspondences_groebner(pi2, pi2),
      ideal_new(4, [pi2]),
    ) {
    return false
  }
  // `compose(pi2, pi0)`: Z_12 = Y_1 (`P^1 × {[1:0]}`), Z_23 = Y_0 (`{[0:1]} × P^1`) -> `<Y_1, Y_0>` -> `<1>` (empty = 0 cycle)!
  if !ideal_is_unit(compose_p1_correspondences_groebner(pi2, pi0)) {
    return false
  }
  // 3. Check categorical identity Δ, involution Γ_σ^2 = Δ, and functoriality Γ_sq ∘ Γ_sq = Γ_{u -> u^4}:
  if !ideal_eq(
      compose_p1_correspondences_groebner(gamma_sq, delta),
      ideal_new(4, [gamma_sq]),
    ) {
    return false
  }
  if !ideal_eq(
      compose_p1_correspondences_groebner(gamma_sigma, gamma_sigma),
      ideal_new(4, [delta]),
    ) {
    return false
  }
  if !ideal_eq(
      compose_p1_correspondences_groebner(gamma_sq, gamma_sq),
      ideal_new(4, [gamma_fourth]),
    ) {
    return false
  }
  // 4. Decategorified Frobenius point count |P^1(F_p)| = 1 + p:
  let p1_pts = eval_scheme_functor_of_points(
    scheme_projective_space(1),
    fcomm_fp(p),
  )
  p1_pts.length() == 1 + p
}
