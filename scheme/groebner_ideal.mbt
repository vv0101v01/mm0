///|
// Scheme Pillar — Layer 1: Multivariate Commutative Polynomial Rings over Q,
// Monomial Orders (Lex, GRevLex, Elimination), Buchberger's Reduced Gröbner
// Basis (Canonical Form!), Elimination / Intersection / Quotient / Saturation,
// Rabinowitsch Hilbert Nullstellensatz, Radical Ideals, and Krull Dimension.

///|
/// Monomial term ordering on `Q[x_0, ..., x_{n-1}]`:
///   - `Lex`: pure lexicographic `x_0 > x_1 > ... > x_{n-1}`;
///   - `GRevLex`: graded reverse lexicographic (canonical default);
///   - `Elim(k)`: block elimination order eliminating the first `k` variables
///     `x_0, ..., x_{k-1}` over `x_k, ..., x_{n-1}` (each block GRevLex).
pub(all) enum MonomialOrder {
  Lex
  GRevLex
  Elim(Int32)
} derive(Debug, Eq)

///|
pub extend MonomialOrder with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend MonomialOrder with Eq::{not_equal, equal}

///|
/// A nonzero monomial term `coeff * x_0^{exps[0]} ... x_{n-1}^{exps[n-1]}`.
pub(all) struct MTerm {
  coeff : @exactalg.Rat
  exps : Array[Int32]
} derive(Debug, Eq)

///|
pub extend MTerm with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend MTerm with Eq::{not_equal, equal}

///|
/// Canonical sparse multivariate polynomial over `Q` in `nvars` variables,
/// stored sorted in strictly descending `GRevLex` order with nonzero coefficients.
pub(all) struct MPoly {
  nvars : Int32
  terms : Array[MTerm]
} derive(Debug, Eq)

///|
pub extend MPoly with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend MPoly with Eq::{not_equal, equal}

///|
/// Canonical Reduced Gröbner Basis of an ideal `I ⊆ Q[x_0, ..., x_{n-1}]`
/// with respect to `order`: every generator is monic, no term of `gens[i]` is
/// divisible by `LM(gens[j])` for `j != i`, and `LM(gens)` is sorted ascending.
/// Two ideals are equal iff their `ReducedGroebnerBasis` under the same `order`
/// are structurally equal (`==`)!
pub(all) struct ReducedGroebnerBasis {
  nvars : Int32
  order : MonomialOrder
  gens : Array[MPoly]
} derive(Debug, Eq)

///|
pub extend ReducedGroebnerBasis with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend ReducedGroebnerBasis with Eq::{not_equal, equal}

///|
/// Polynomial ideal `I ⊆ Q[x_0, ..., x_{n-1}]` presented by generators together
/// with its canonical `GRevLex` reduced Gröbner basis.
pub(all) struct Ideal {
  nvars : Int32
  rgb : ReducedGroebnerBasis
} derive(Debug, Eq)

///|
pub extend Ideal with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend Ideal with Eq::{not_equal, equal}

///|
fn exps_total_deg_range(exps : Array[Int32], lo : Int32, hi : Int32) -> Int32 {
  let mut s = 0
  for i in lo..<hi {
    s = s + exps[i]
  }
  s
}

///|
fn cmp_grevlex_range(
  a : Array[Int32],
  b : Array[Int32],
  lo : Int32,
  hi : Int32,
) -> Int32 {
  let da = exps_total_deg_range(a, lo, hi)
  let db = exps_total_deg_range(b, lo, hi)
  if da != db {
    return if da < db { -1 } else { 1 }
  }
  for i = hi - 1; i >= lo; i = i - 1 {
    if a[i] != b[i] {
      // In GRevLex, smaller last exponent wins!
      return if a[i] > b[i] { -1 } else { 1 }
    }
  }
  0
}

///|
/// Compare two exponent vectors `a, b` of the same length under `order`:
/// returns `-1` if `a < b`, `0` if `a == b`, `1` if `a > b`.
pub fn monomial_cmp(
  order : MonomialOrder,
  a : Array[Int32],
  b : Array[Int32],
) -> Int32 {
  let n = a.length()
  match order {
    Lex => {
      for i in 0..<n {
        if a[i] != b[i] {
          return if a[i] < b[i] { -1 } else { 1 }
        }
      }
      0
    }
    GRevLex => cmp_grevlex_range(a, b, 0, n)
    Elim(k) => {
      let split = if k < 0 { 0 } else if k > n { n } else { k }
      let c1 = cmp_grevlex_range(a, b, 0, split)
      if c1 != 0 {
        c1
      } else {
        cmp_grevlex_range(a, b, split, n)
      }
    }
  }
}

///|
fn exps_mul(a : Array[Int32], b : Array[Int32]) -> Array[Int32] {
  let out = Array::make(a.length(), 0)
  for i in 0..<a.length() {
    out[i] = a[i] + b[i]
  }
  out
}

///|
fn exps_divides(divisor : Array[Int32], target : Array[Int32]) -> Bool {
  for i in 0..<divisor.length() {
    if divisor[i] > target[i] {
      return false
    }
  }
  true
}

///|
fn exps_quot(target : Array[Int32], divisor : Array[Int32]) -> Array[Int32] {
  let out = Array::make(target.length(), 0)
  for i in 0..<target.length() {
    out[i] = target[i] - divisor[i]
  }
  out
}

///|
fn exps_lcm(a : Array[Int32], b : Array[Int32]) -> Array[Int32] {
  let out = Array::make(a.length(), 0)
  for i in 0..<a.length() {
    out[i] = if a[i] >= b[i] { a[i] } else { b[i] }
  }
  out
}

///|
fn exps_coprime(a : Array[Int32], b : Array[Int32]) -> Bool {
  for i in 0..<a.length() {
    if a[i] > 0 && b[i] > 0 {
      return false
    }
  }
  true
}

///|
/// Normalize a raw list of terms into canonical `MPoly` form (descending `GRevLex`,
/// like-monomials combined, zero coefficients dropped).
pub fn mpoly_from_terms(nvars : Int32, raw : Array[MTerm]) -> MPoly {
  let filtered : Array[MTerm] = []
  for t in raw {
    guard t.exps.length() == nvars else {
      abort("mpoly_from_terms: exponent length mismatch")
    }
    if !@exactalg.rat_is_zero(t.coeff) {
      filtered.push({ coeff: t.coeff, exps: t.exps.copy(), })
    }
  }
  let m = filtered.length()
  for i in 0..<m {
    for j in (i + 1)..<m {
      if monomial_cmp(GRevLex, filtered[j].exps, filtered[i].exps) > 0 {
        let tmp = filtered[i]
        filtered[i] = filtered[j]
        filtered[j] = tmp
      }
    }
  }
  let merged : Array[MTerm] = []
  for t in filtered {
    if merged.length() > 0 && merged[merged.length() - 1].exps == t.exps {
      guard merged.pop() is Some(last) else {
        abort("mpoly_normalize: empty merge stack")
      }
      let sum_c = @exactalg.rat_add(last.coeff, t.coeff)
      if !@exactalg.rat_is_zero(sum_c) {
        merged.push({ coeff: sum_c, exps: last.exps, })
      }
    } else {
      merged.push(t)
    }
  }
  { nvars, terms: merged, }
}

///|
/// Zero polynomial in `nvars` variables.
pub fn mpoly_zero(nvars : Int32) -> MPoly {
  { nvars, terms: [], }
}

///|
/// Constant rational polynomial `c` in `nvars` variables.
pub fn mpoly_const(nvars : Int32, c : @exactalg.Rat) -> MPoly {
  if @exactalg.rat_is_zero(c) {
    mpoly_zero(nvars)
  } else {
    { nvars, terms: [{ coeff: c, exps: Array::make(nvars, 0), }], }
  }
}

///|
/// Constant integer polynomial `k` in `nvars` variables.
pub fn mpoly_int(nvars : Int32, k : Int32) -> MPoly {
  mpoly_const(nvars, @exactalg.rat_int(k))
}

///|
/// Coordinate generator `x_idx` in `Q[x_0, ..., x_{nvars-1}]`.
pub fn mpoly_var(nvars : Int32, idx : Int32) -> MPoly {
  guard idx >= 0 && idx < nvars else { abort("mpoly_var: index out of range") }
  let exps = Array::make(nvars, 0)
  exps[idx] = 1
  { nvars, terms: [{ coeff: @exactalg.rat_one(), exps, }], }
}

///|
/// Check whether `f == 0`.
pub fn mpoly_is_zero(f : MPoly) -> Bool {
  f.terms.length() == 0
}

///|
/// Total degree of `f` (`-1` if `f == 0`).
pub fn mpoly_total_degree(f : MPoly) -> Int32 {
  if f.terms.length() == 0 {
    return -1
  }
  // Since `terms` is sorted descending in GRevLex, `terms[0]` achieves maximal total degree!
  exps_total_deg_range(f.terms[0].exps, 0, f.nvars)
}

///|
/// Addition `f + g`.
pub fn mpoly_add(f : MPoly, g : MPoly) -> MPoly {
  guard f.nvars == g.nvars else { abort("mpoly_add: nvars mismatch") }
  let raw = f.terms.copy()
  for t in g.terms {
    raw.push(t)
  }
  mpoly_from_terms(f.nvars, raw)
}

///|
/// Negation `-f`.
pub fn mpoly_neg(f : MPoly) -> MPoly {
  let out : Array[MTerm] = []
  for t in f.terms {
    out.push({ coeff: @exactalg.rat_neg(t.coeff), exps: t.exps.copy(), })
  }
  { nvars: f.nvars, terms: out, }
}

///|
/// Subtraction `f - g`.
pub fn mpoly_sub(f : MPoly, g : MPoly) -> MPoly {
  mpoly_add(f, mpoly_neg(g))
}

///|
/// Scalar multiplication `c * f`.
pub fn mpoly_scale(c : @exactalg.Rat, f : MPoly) -> MPoly {
  if @exactalg.rat_is_zero(c) {
    return mpoly_zero(f.nvars)
  }
  let out : Array[MTerm] = []
  for t in f.terms {
    out.push({ coeff: @exactalg.rat_mul(c, t.coeff), exps: t.exps.copy(), })
  }
  { nvars: f.nvars, terms: out, }
}

///|
/// Polynomial multiplication `f * g`.
pub fn mpoly_mul(f : MPoly, g : MPoly) -> MPoly {
  guard f.nvars == g.nvars else { abort("mpoly_mul: nvars mismatch") }
  if mpoly_is_zero(f) || mpoly_is_zero(g) {
    return mpoly_zero(f.nvars)
  }
  let raw : Array[MTerm] = []
  for tf in f.terms {
    for tg in g.terms {
      raw.push({
        coeff: @exactalg.rat_mul(tf.coeff, tg.coeff),
        exps: exps_mul(tf.exps, tg.exps),
      })
    }
  }
  mpoly_from_terms(f.nvars, raw)
}

///|
/// Non-negative integer power `f^exp`.
pub fn mpoly_pow(f : MPoly, exp : Int32) -> MPoly {
  guard exp >= 0 else { abort("mpoly_pow: negative exponent") }
  let mut acc = mpoly_int(f.nvars, 1)
  let mut base = f
  let mut e = exp
  while e > 0 {
    if e % 2 == 1 {
      acc = mpoly_mul(acc, base)
    }
    e = e / 2
    if e > 0 {
      base = mpoly_mul(base, base)
    }
  }
  acc
}

///|
/// Formal partial derivative `∂f / ∂x_{var_idx}`.
pub fn mpoly_partial_deriv(f : MPoly, var_idx : Int32) -> MPoly {
  let raw : Array[MTerm] = []
  for t in f.terms {
    let e = t.exps[var_idx]
    if e > 0 {
      let exps = t.exps.copy()
      exps[var_idx] = e - 1
      raw.push({
        coeff: @exactalg.rat_mul(t.coeff, @exactalg.rat_int(e)),
        exps,
      })
    }
  }
  mpoly_from_terms(f.nvars, raw)
}

///|
/// Evaluate `f` at a rational point `pt ∈ Q^{nvars}`.
pub fn mpoly_eval(f : MPoly, pt : Array[@exactalg.Rat]) -> @exactalg.Rat {
  guard pt.length() == f.nvars else { abort("mpoly_eval: point dimension") }
  let mut sum = @exactalg.rat_zero()
  for t in f.terms {
    let mut prod = t.coeff
    for i in 0..<f.nvars {
      for _ in 0..<t.exps[i] {
        prod = @exactalg.rat_mul(prod, pt[i])
      }
    }
    sum = @exactalg.rat_add(sum, prod)
  }
  sum
}

///|
/// Substitute `images[i] ∈ Q[y_0, ..., y_{target_nvars-1}]` for each `x_i` in `f`.
pub fn mpoly_subst(
  f : MPoly,
  target_nvars : Int32,
  images : Array[MPoly],
) -> MPoly {
  guard images.length() == f.nvars else { abort("mpoly_subst: arity mismatch") }
  let mut sum = mpoly_zero(target_nvars)
  for t in f.terms {
    let mut term_val = mpoly_const(target_nvars, t.coeff)
    for i in 0..<f.nvars {
      if t.exps[i] > 0 {
        term_val = mpoly_mul(term_val, mpoly_pow(images[i], t.exps[i]))
      }
    }
    sum = mpoly_add(sum, term_val)
  }
  sum
}

///|
/// Embed `f ∈ Q[x_0..x_{n-1}]` into `Q[x_0..x_{n + extra - 1}]` either by
/// appending `extra` trailing variables (`prepend == false`) or prepending
/// `extra` leading elimination variables (`prepend == true`).
pub fn mpoly_extend_vars(f : MPoly, extra : Int32, prepend : Bool) -> MPoly {
  let new_n = f.nvars + extra
  let raw : Array[MTerm] = []
  for t in f.terms {
    let exps = Array::make(new_n, 0)
    for i in 0..<f.nvars {
      if prepend {
        exps[extra + i] = t.exps[i]
      } else {
        exps[i] = t.exps[i]
      }
    }
    raw.push({ coeff: t.coeff, exps, })
  }
  mpoly_from_terms(new_n, raw)
}

///|
/// Dehomogenize a homogeneous polynomial `F(X_0, ..., X_n)` on affine chart
/// `U_{chart_idx} = { X_{chart_idx} != 0 }` by setting `X_{chart_idx} = 1`
/// and mapping remaining variables in order to `u_0, ..., u_{n-1}`.
pub fn mpoly_dehomogenize(f : MPoly, chart_idx : Int32) -> MPoly {
  let target_n = f.nvars - 1
  let imgs : Array[MPoly] = []
  let mut slot = 0
  for i in 0..<f.nvars {
    if i == chart_idx {
      imgs.push(mpoly_int(target_n, 1))
    } else {
      imgs.push(mpoly_var(target_n, slot))
      slot = slot + 1
    }
  }
  mpoly_subst(f, target_n, imgs)
}

///|
/// Find the leading term `LT_order(f)` of a nonzero polynomial `f` under `order`.
pub fn mpoly_leading_term(f : MPoly, order : MonomialOrder) -> MTerm {
  guard f.terms.length() > 0 else {
    abort("mpoly_leading_term: zero polynomial")
  }
  let mut best = f.terms[0]
  for i in 1..<f.terms.length() {
    if monomial_cmp(order, f.terms[i].exps, best.exps) > 0 {
      best = f.terms[i]
    }
  }
  best
}

///|
/// Make `f` monic with respect to `order` (`LC_order(f) = 1`).
pub fn mpoly_monic(f : MPoly, order : MonomialOrder) -> MPoly {
  if mpoly_is_zero(f) {
    return f
  }
  let lt = mpoly_leading_term(f, order)
  mpoly_scale(@exactalg.rat_div(@exactalg.rat_one(), lt.coeff), f)
}

///|
fn mpoly_mul_monomial(
  c : @exactalg.Rat,
  exps : Array[Int32],
  f : MPoly,
) -> MPoly {
  if @exactalg.rat_is_zero(c) || mpoly_is_zero(f) {
    return mpoly_zero(f.nvars)
  }
  let raw : Array[MTerm] = []
  for t in f.terms {
    raw.push({
      coeff: @exactalg.rat_mul(c, t.coeff),
      exps: exps_mul(exps, t.exps),
    })
  }
  mpoly_from_terms(f.nvars, raw)
}

///|
/// Multivariate division remainder (Canonical Normal Form `nf_G(f)`) of `f`
/// modulo `divisors` with respect to `order`: NO term of the returned remainder
/// is divisible by `LM_order(g)` for any nonzero `g ∈ divisors`!
pub fn mpoly_reduce(
  f : MPoly,
  divisors : Array[MPoly],
  order : MonomialOrder,
) -> MPoly {
  let active : Array[(MPoly, MTerm)] = []
  for g in divisors {
    if !mpoly_is_zero(g) {
      active.push((g, mpoly_leading_term(g, order)))
    }
  }
  let mut p = f
  let rem_terms : Array[MTerm] = []
  while !mpoly_is_zero(p) {
    let lt_p = mpoly_leading_term(p, order)
    let mut reduced = false
    for pair in active {
      let (g, lt_g) = pair
      if exps_divides(lt_g.exps, lt_p.exps) {
        let q_coeff = @exactalg.rat_div(lt_p.coeff, lt_g.coeff)
        let q_exps = exps_quot(lt_p.exps, lt_g.exps)
        p = mpoly_sub(p, mpoly_mul_monomial(q_coeff, q_exps, g))
        reduced = true
        break
      }
    }
    if !reduced {
      rem_terms.push(lt_p)
      p = mpoly_sub(p, mpoly_from_terms(f.nvars, [lt_p]))
    }
  }
  mpoly_from_terms(f.nvars, rem_terms)
}

///|
/// Buchberger's S-polynomial `S(f, g) = (lcm / LT(f)) * f - (lcm / LT(g)) * g`.
pub fn s_polynomial(f : MPoly, g : MPoly, order : MonomialOrder) -> MPoly {
  let ltf = mpoly_leading_term(f, order)
  let ltg = mpoly_leading_term(g, order)
  let lcm = exps_lcm(ltf.exps, ltg.exps)
  let left = mpoly_mul_monomial(
    @exactalg.rat_div(@exactalg.rat_one(), ltf.coeff),
    exps_quot(lcm, ltf.exps),
    f,
  )
  let right = mpoly_mul_monomial(
    @exactalg.rat_div(@exactalg.rat_one(), ltg.coeff),
    exps_quot(lcm, ltg.exps),
    g,
  )
  mpoly_sub(left, right)
}

///|
/// Compute the unique **Canonical Reduced Gröbner Basis** of `<gens>` in
/// `Q[x_0, ..., x_{nvars-1}]` with respect to `order` via Buchberger's algorithm
/// with coprime-LM pruning, minimal-LM filtering, full tail interreduction, and
/// ascending LM canonical sort!
pub fn reduced_groebner_basis(
  nvars : Int32,
  gens : Array[MPoly],
  order : MonomialOrder,
) -> ReducedGroebnerBasis {
  let basis : Array[MPoly] = []
  for g in gens {
    let m = mpoly_monic(g, order)
    if !mpoly_is_zero(m) {
      basis.push(m)
    }
  }
  let pairs : Array[(Int32, Int32)] = []
  for i in 0..<basis.length() {
    for j in (i + 1)..<basis.length() {
      pairs.push((i, j))
    }
  }
  let mut head = 0
  while head < pairs.length() {
    let (i, j) = pairs[head]
    head = head + 1
    let lti = mpoly_leading_term(basis[i], order)
    let ltj = mpoly_leading_term(basis[j], order)
    // Buchberger's First Criterion: coprime leading monomials reduce to 0 automatically!
    if exps_coprime(lti.exps, ltj.exps) {
      continue
    }
    let sp = s_polynomial(basis[i], basis[j], order)
    let rem = mpoly_reduce(sp, basis, order)
    if !mpoly_is_zero(rem) {
      let monic_rem = mpoly_monic(rem, order)
      if mpoly_total_degree(monic_rem) == 0 {
        // Unit ideal <1>: immediately collapses to `[1]`!
        return { nvars, order, gens: [mpoly_int(nvars, 1)], }
      }
      let new_idx = basis.length()
      basis.push(monic_rem)
      for k in 0..<new_idx {
        pairs.push((k, new_idx))
      }
    }
  }
  // 1. Minimal basis: drop any generator whose LM is divisible by another's LM
  //    (with tie-breaking by smaller index for equal LMs).
  let keep = Array::make(basis.length(), true)
  for i in 0..<basis.length() {
    if !keep[i] {
      continue
    }
    let lti = mpoly_leading_term(basis[i], order).exps
    for j in 0..<basis.length() {
      if i == j || !keep[j] {
        continue
      }
      let ltj = mpoly_leading_term(basis[j], order).exps
      if exps_divides(ltj, lti) {
        if ltj != lti || j < i {
          keep[i] = false
          break
        }
      }
    }
  }
  let minimal : Array[MPoly] = []
  for i in 0..<basis.length() {
    if keep[i] {
      minimal.push(basis[i])
    }
  }
  // 2. Interreduce tails so NO term of minimal[i] is divisible by LM(minimal[j]) for j != i.
  for i in 0..<minimal.length() {
    let others : Array[MPoly] = []
    for j in 0..<minimal.length() {
      if j != i {
        others.push(minimal[j])
      }
    }
    minimal[i] = mpoly_monic(mpoly_reduce(minimal[i], others, order), order)
  }
  // 3. Sort ascending by leading monomial under `order` for canonical uniqueness.
  let m = minimal.length()
  for i in 0..<m {
    for j in (i + 1)..<m {
      let lti = mpoly_leading_term(minimal[i], order).exps
      let ltj = mpoly_leading_term(minimal[j], order).exps
      if monomial_cmp(order, ltj, lti) < 0 {
        let tmp = minimal[i]
        minimal[i] = minimal[j]
        minimal[j] = tmp
      }
    }
  }
  { nvars, order, gens: minimal, }
}

///|
/// Construct an `Ideal` in `Q[x_0, ..., x_{nvars-1}]` presented by its canonical
/// `GRevLex` Reduced Gröbner Basis.
pub fn ideal_new(nvars : Int32, gens : Array[MPoly]) -> Ideal {
  { nvars, rgb: reduced_groebner_basis(nvars, gens, GRevLex), }
}

///|
/// Canonical normal form `nf_I(f)` of `f` modulo ideal `idl`.
pub fn ideal_normal_form(idl : Ideal, f : MPoly) -> MPoly {
  mpoly_reduce(f, idl.rgb.gens, GRevLex)
}

///|
/// Exact ideal membership test `f ∈ idl` (`nf_I(f) == 0`).
pub fn ideal_contains(idl : Ideal, f : MPoly) -> Bool {
  mpoly_is_zero(ideal_normal_form(idl, f))
}

///|
/// Check whether `idl == <1>` (defining the empty closed subscheme `∅`!).
pub fn ideal_is_unit(idl : Ideal) -> Bool {
  idl.rgb.gens.length() == 1 && mpoly_total_degree(idl.rgb.gens[0]) == 0
}

///|
/// Check whether `idl == <0>`.
pub fn ideal_is_zero(idl : Ideal) -> Bool {
  idl.rgb.gens.length() == 0
}

///|
/// Check `idl1 ⊆ idl2`.
pub fn ideal_subset(idl1 : Ideal, idl2 : Ideal) -> Bool {
  for g in idl1.rgb.gens {
    if !ideal_contains(idl2, g) {
      return false
    }
  }
  true
}

///|
/// Exact ideal equality `idl1 == idl2` (structural equality of canonical `GRevLex` RGB!).
pub fn ideal_eq(idl1 : Ideal, idl2 : Ideal) -> Bool {
  idl1 == idl2
}

///|
/// Sum of ideals `I + J` (corresponds geometrically to scheme-theoretic
/// intersection `V(I) ∩ V(J)`!).
pub fn ideal_add(i1 : Ideal, i2 : Ideal) -> Ideal {
  let gens = i1.rgb.gens.copy()
  for g in i2.rgb.gens {
    gens.push(g)
  }
  ideal_new(i1.nvars, gens)
}

///|
/// Product of ideals `I * J`.
pub fn ideal_mul(i1 : Ideal, i2 : Ideal) -> Ideal {
  let gens : Array[MPoly] = []
  for f in i1.rgb.gens {
    for g in i2.rgb.gens {
      gens.push(mpoly_mul(f, g))
    }
  }
  ideal_new(i1.nvars, gens)
}

///|
/// Elimination ideal `I ∩ Q[x_k, ..., x_{n-1}]` (returned as an ideal in the
/// remaining `n - k` variables!).
pub fn ideal_eliminate_first_k(idl : Ideal, k : Int32) -> Ideal {
  let rem_n = idl.nvars - k
  let elim_gb = reduced_groebner_basis(idl.nvars, idl.rgb.gens, Elim(k))
  let kept : Array[MPoly] = []
  for g in elim_gb.gens {
    let mut pure = true
    for t in g.terms {
      for v in 0..<k {
        if t.exps[v] > 0 {
          pure = false
          break
        }
      }
      if !pure {
        break
      }
    }
    if pure {
      let raw : Array[MTerm] = []
      for t in g.terms {
        let exps = Array::make(rem_n, 0)
        for v in 0..<rem_n {
          exps[v] = t.exps[k + v]
        }
        raw.push({ coeff: t.coeff, exps, })
      }
      kept.push(mpoly_from_terms(rem_n, raw))
    }
  }
  ideal_new(rem_n, kept)
}

///|
/// Intersection `I ∩ J = (t * I + (1 - t) * J) ∩ Q[x_0..x_{n-1}]`
/// (corresponds geometrically to scheme-theoretic union `V(I) ∪ V(J)`!).
pub fn ideal_intersect(i1 : Ideal, i2 : Ideal) -> Ideal {
  let n = i1.nvars
  let t_var = mpoly_var(n + 1, 0)
  let one_minus_t = mpoly_sub(mpoly_int(n + 1, 1), t_var)
  let gens : Array[MPoly] = []
  for f in i1.rgb.gens {
    gens.push(mpoly_mul(t_var, mpoly_extend_vars(f, 1, true)))
  }
  for g in i2.rgb.gens {
    gens.push(mpoly_mul(one_minus_t, mpoly_extend_vars(g, 1, true)))
  }
  ideal_eliminate_first_k(ideal_new(n + 1, gens), 1)
}

///|
/// Exact polynomial division `h / divisor` when `divisor` divides `h` in `Q[x]`.
pub fn mpoly_div_exact(h : MPoly, divisor : MPoly) -> MPoly? {
  if mpoly_is_zero(divisor) {
    return None
  }
  if mpoly_is_zero(h) {
    return Some(mpoly_zero(h.nvars))
  }
  let lt_d = mpoly_leading_term(divisor, GRevLex)
  let mut rem = h
  let q_terms : Array[MTerm] = []
  while !mpoly_is_zero(rem) {
    let lt_r = mpoly_leading_term(rem, GRevLex)
    if !exps_divides(lt_d.exps, lt_r.exps) {
      return None
    }
    let qc = @exactalg.rat_div(lt_r.coeff, lt_d.coeff)
    let qe = exps_quot(lt_r.exps, lt_d.exps)
    q_terms.push({ coeff: qc, exps: qe, })
    rem = mpoly_sub(rem, mpoly_mul_monomial(qc, qe, divisor))
  }
  Some(mpoly_from_terms(h.nvars, q_terms))
}

///|
/// Ideal colon `(I : <f>) = (I ∩ <f>) / f`.
pub fn ideal_quotient_poly(idl : Ideal, f : MPoly) -> Ideal {
  if mpoly_is_zero(f) {
    return ideal_new(idl.nvars, [mpoly_int(idl.nvars, 1)])
  }
  let inter = ideal_intersect(idl, ideal_new(idl.nvars, [f]))
  let gens : Array[MPoly] = []
  for h in inter.rgb.gens {
    match mpoly_div_exact(h, f) {
      Some(q) => gens.push(q)
      None =>
        abort("ideal_quotient_poly: generator of I ∩ <f> not divisible by f")
    }
  }
  ideal_new(idl.nvars, gens)
}

///|
/// Ideal colon `(I : J) = ∩_{g ∈ J} (I : <g>)`.
pub fn ideal_quotient(i1 : Ideal, i2 : Ideal) -> Ideal {
  if i2.rgb.gens.length() == 0 {
    return ideal_new(i1.nvars, [mpoly_int(i1.nvars, 1)])
  }
  let mut acc = ideal_quotient_poly(i1, i2.rgb.gens[0])
  for k in 1..<i2.rgb.gens.length() {
    acc = ideal_intersect(acc, ideal_quotient_poly(i1, i2.rgb.gens[k]))
  }
  acc
}

///|
/// Saturation `(I : f^∞) = (<I, 1 - t * f>) ∩ Q[x_0..x_{n-1}]` via Rabinowitsch
/// elimination variable `t`! Geometrically, this is the closure of `V(I) \ V(f)`
/// (and kernel of localization `A -> A_f`)!
pub fn ideal_saturate(idl : Ideal, f : MPoly) -> Ideal {
  let n = idl.nvars
  if mpoly_is_zero(f) {
    return ideal_new(n, [mpoly_int(n, 1)])
  }
  let t_var = mpoly_var(n + 1, 0)
  let f_ext = mpoly_extend_vars(f, 1, true)
  let rabinowitsch = mpoly_sub(mpoly_int(n + 1, 1), mpoly_mul(t_var, f_ext))
  let gens : Array[MPoly] = [rabinowitsch]
  for g in idl.rgb.gens {
    gens.push(mpoly_extend_vars(g, 1, true))
  }
  ideal_eliminate_first_k(ideal_new(n + 1, gens), 1)
}

///|
/// **Hilbert's Nullstellensatz (Rabinowitsch Trick)**:
/// Exact decision procedure for `f ∈ √I` (`∃ m >= 1, f^m ∈ I`):
/// holds iff `1 ∈ <I, 1 - t * f>` in `Q[t, x_0..x_{n-1}]`!
pub fn ideal_radical_contains(idl : Ideal, f : MPoly) -> Bool {
  let n = idl.nvars
  if mpoly_is_zero(f) {
    return true
  }
  let t_var = mpoly_var(n + 1, 0)
  let f_ext = mpoly_extend_vars(f, 1, true)
  let gens : Array[MPoly] = [
    mpoly_sub(mpoly_int(n + 1, 1), mpoly_mul(t_var, f_ext)),
  ]
  for g in idl.rgb.gens {
    gens.push(mpoly_extend_vars(g, 1, true))
  }
  ideal_is_unit(ideal_new(n + 1, gens))
}

///|
/// Convert a univariate `MPoly` (depending only on variable `var_idx`) to `@exactalg.QPoly`.
pub fn mpoly_to_qpoly_univariate(f : MPoly, var_idx : Int32) -> @exactalg.QPoly {
  if mpoly_is_zero(f) {
    return @exactalg.qpoly_zero()
  }
  let mut max_d = 0
  for t in f.terms {
    if t.exps[var_idx] > max_d {
      max_d = t.exps[var_idx]
    }
  }
  let coeffs = Array::make(max_d + 1, @exactalg.rat_zero())
  for t in f.terms {
    coeffs[t.exps[var_idx]] = @exactalg.rat_add(
      coeffs[t.exps[var_idx]],
      t.coeff,
    )
  }
  @exactalg.qpoly_normalize(coeffs)
}

///|
/// Embed a `@exactalg.QPoly` as a univariate `MPoly` in variable `var_idx` of `nvars`.
pub fn qpoly_to_mpoly_var(
  p : @exactalg.QPoly,
  nvars : Int32,
  var_idx : Int32,
) -> MPoly {
  let deg = @exactalg.qpoly_degree(p)
  if deg < 0 {
    return mpoly_zero(nvars)
  }
  let raw : Array[MTerm] = []
  for d in 0..<(deg + 1) {
    let c = @exactalg.qpoly_coeff(p, d)
    if !@exactalg.rat_is_zero(c) {
      let exps = Array::make(nvars, 0)
      exps[var_idx] = d
      raw.push({ coeff: c, exps, })
    }
  }
  mpoly_from_terms(nvars, raw)
}

///|
/// Convert `@exactalg.Poly` (`algebra/symalg.mbt`) into an `nvars`-variable `MPoly`
/// (padding/checking exponent width to `nvars`).
pub fn mpoly_of_poly(nvars : Int32, p : @exactalg.Poly) -> MPoly {
  let raw : Array[MTerm] = []
  for t in p.terms {
    let exps = Array::make(nvars, 0)
    for i in 0..<t.exps.length() {
      if i < nvars {
        exps[i] = t.exps[i]
      } else {
        guard t.exps[i] == 0 else {
          abort("mpoly_of_poly: variable index exceeds nvars")
        }
      }
    }
    raw.push({ coeff: t.coeff, exps, })
  }
  mpoly_from_terms(nvars, raw)
}

///|
/// Convert `MPoly` to `@exactalg.Poly` (`algebra/symalg.mbt`).
pub fn mpoly_to_poly(f : MPoly) -> @exactalg.Poly {
  let mut acc = @exactalg.poly_zero()
  for t in f.terms {
    let mut mon = @exactalg.poly_const(t.coeff)
    for v in 0..<f.nvars {
      for _ in 0..<t.exps[v] {
        mon = @exactalg.poly_mul(mon, @exactalg.poly_var(v))
      }
    }
    acc = @exactalg.poly_add(acc, mon)
  }
  acc
}

///|
/// Squarefree reduction of a single multivariate polynomial `f` by dividing out
/// `gcd(f, ∂f/∂x_i)` iteratively in univariate/principal projections and testing
/// exact root powers of monomials & factors.
fn mpoly_squarefree_reduction(f : MPoly) -> MPoly {
  if mpoly_is_zero(f) || mpoly_total_degree(f) <= 0 {
    return f
  }
  // Check if `f` only involves a single variable `v_only`.
  let mut v_only = -1
  let mut uni = true
  for t in f.terms {
    for v in 0..<f.nvars {
      if t.exps[v] > 0 {
        if v_only < 0 {
          v_only = v
        } else if v_only != v {
          uni = false
          break
        }
      }
    }
    if !uni {
      break
    }
  }
  if uni && v_only >= 0 {
    let qp = mpoly_to_qpoly_univariate(f, v_only)
    return qpoly_to_mpoly_var(
      @exactalg.qpoly_squarefree_part(qp),
      f.nvars,
      v_only,
    )
  }
  // For single-term monomial `x^{e_0} ...`, reduce every positive exponent to `1`!
  if f.terms.length() == 1 {
    let exps = Array::make(f.nvars, 0)
    for v in 0..<f.nvars {
      exps[v] = if f.terms[0].exps[v] > 0 { 1 } else { 0 }
    }
    return { nvars: f.nvars, terms: [{ coeff: @exactalg.rat_one(), exps, }], }
  }
  // Check if `f = h^k` for small `k >= 2` or shares common variable power `x_v^m`.
  let mut cur = mpoly_monic(f, GRevLex)
  for v in 0..<f.nvars {
    let mut min_e = cur.terms[0].exps[v]
    for t in cur.terms {
      if t.exps[v] < min_e {
        min_e = t.exps[v]
      }
    }
    if min_e >= 2 {
      let xv_extra = mpoly_pow(mpoly_var(f.nvars, v), min_e - 1)
      match mpoly_div_exact(cur, xv_extra) {
        Some(q) => cur = q
        None => ()
      }
    }
  }
  // Also test modulo ideal quotient `( <cur> : <∂cur / ∂x_v> )` to strip repeated
  // hypersurface factors `(h^m) / gcd(h^m, m h^{m-1} ∂h) = h`!!
  for v in 0..<f.nvars {
    let df = mpoly_partial_deriv(cur, v)
    if !mpoly_is_zero(df) {
      let rad_cand = ideal_quotient_poly(ideal_new(f.nvars, [cur]), df)
      if rad_cand.rgb.gens.length() == 1 {
        let g = rad_cand.rgb.gens[0]
        if mpoly_total_degree(g) > 0 &&
          mpoly_total_degree(g) < mpoly_total_degree(cur) &&
          ideal_radical_contains(ideal_new(f.nvars, [cur]), g) {
          cur = g
        }
      }
    }
  }
  cur
}

///|
/// Compute the **Radical Ideal `√I`** in `Q[x_0, ..., x_{n-1}]` using:
///   1. Seidenberg's Univariate Elimination Lemma: for each variable `x_v`,
///      eliminates all other variables to extract `I ∩ Q[x_v] = <g_v(x_v)>` and
///      adjoins `squarefree(g_v)` (exact over characteristic-0 perfect field `Q`
///      for ALL 0-dimensional ideals!!);
///   2. Hypersurface / Jacobian colon squarefree stripping `<f> : <∂f/∂x_v>` and
///      monomial-radical stripping on generators, iterated to fixed point and
///      certified by `ideal_radical_contains`!
pub fn ideal_radical(idl : Ideal) -> Ideal {
  if ideal_is_unit(idl) || ideal_is_zero(idl) {
    return idl
  }
  let n = idl.nvars
  let mut cur = idl
  // Step 1: Seidenberg univariate elimination along EVERY coordinate axis `v`!
  let extra_gens = cur.rgb.gens.copy()
  for v in 0..<n {
    // Reorder variables so `x_v` is LAST and eliminate first `n - 1` variables!
    if n == 1 {
      let qp = mpoly_to_qpoly_univariate(cur.rgb.gens[0], 0)
      extra_gens.push(
        qpoly_to_mpoly_var(@exactalg.qpoly_squarefree_part(qp), 1, 0),
      )
    } else {
      let imgs : Array[MPoly] = []
      let mut slot = 0
      for i in 0..<n {
        if i == v {
          imgs.push(mpoly_var(n, n - 1))
        } else {
          imgs.push(mpoly_var(n, slot))
          slot = slot + 1
        }
      }
      let swapped_gens : Array[MPoly] = []
      for g in cur.rgb.gens {
        swapped_gens.push(mpoly_subst(g, n, imgs))
      }
      let uni_ideal = ideal_eliminate_first_k(ideal_new(n, swapped_gens), n - 1)
      if uni_ideal.rgb.gens.length() == 1 {
        let qp = mpoly_to_qpoly_univariate(uni_ideal.rgb.gens[0], 0)
        let sf = @exactalg.qpoly_squarefree_part(qp)
        extra_gens.push(qpoly_to_mpoly_var(sf, n, v))
      }
    }
  }
  cur = ideal_new(n, extra_gens)
  // Step 2: Strip squarefree / Jacobian multiplicity factors on RGB generators
  // and search bounded-degree standard monomials for residual nilpotents when dim == 0
  // or small generator sets!
  let mut changed = true
  while changed {
    changed = false
    let next_gens = cur.rgb.gens.copy()
    for g in cur.rgb.gens {
      let sf_g = mpoly_squarefree_reduction(g)
      if !ideal_contains(cur, sf_g) && ideal_radical_contains(idl, sf_g) {
        next_gens.push(sf_g)
        changed = true
      }
    }
    // Check linear/monomial combinations `x_i` and `x_i * x_j` via Rabinowitsch!
    for i in 0..<n {
      let xi = mpoly_var(n, i)
      if !ideal_contains(cur, xi) && ideal_radical_contains(idl, xi) {
        next_gens.push(xi)
        changed = true
      }
      for j in i..<n {
        let xij = mpoly_mul(xi, mpoly_var(n, j))
        if !ideal_contains(cur, xij) && ideal_radical_contains(idl, xij) {
          next_gens.push(xij)
          changed = true
        }
      }
    }
    if changed {
      cur = ideal_new(n, next_gens)
    }
  }
  cur
}

///|
/// Compute the exact **Krull Dimension** of `Spec(Q[x_0..x_{n-1}] / I)`
/// (`-1` for the unit ideal `<1>` / empty scheme; otherwise the maximum size of
/// an independent subset `S ⊆ {0..n-1}` such that `LM(RGB(I)) ∩ Q[S] == ∅`!).
pub fn ideal_krull_dimension(idl : Ideal) -> Int32 {
  if ideal_is_unit(idl) {
    return -1
  }
  let n = idl.nvars
  let lms : Array[Array[Int32]] = []
  for g in idl.rgb.gens {
    lms.push(mpoly_leading_term(g, GRevLex).exps)
  }
  let mut total_masks = 1
  for _ in 0..<n {
    total_masks = total_masks * 2
  }
  let mut best = 0
  for mask in 0..<total_masks {
    let mut card = 0
    for i in 0..<n {
      if ((mask >> i) & 1) == 1 {
        card = card + 1
      }
    }
    if card <= best {
      continue
    }
    // Subset `mask` is independent iff NO leading monomial has support ⊆ `mask`!
    let mut indep = true
    for lm in lms {
      let mut supp_in_mask = true
      for i in 0..<n {
        if lm[i] > 0 && ((mask >> i) & 1) == 0 {
          supp_in_mask = false
          break
        }
      }
      if supp_in_mask {
        indep = false
        break
      }
    }
    if indep {
      best = card
    }
  }
  best
}

///|
/// Enumerate the canonical basis of **Standard Monomials** (exponent vectors not
/// divisible by any `LM(RGB(I))`) of a zero-dimensional quotient algebra
/// `Q[x_0..x_{n-1}] / I`; returns `None` if `dim(I) > 0`!
pub fn ideal_standard_monomials(idl : Ideal) -> Array[Array[Int32]]? {
  if ideal_is_unit(idl) {
    return Some([])
  }
  if ideal_krull_dimension(idl) > 0 {
    return None
  }
  let n = idl.nvars
  let lms : Array[Array[Int32]] = []
  for g in idl.rgb.gens {
    lms.push(mpoly_leading_term(g, GRevLex).exps)
  }
  // Since dim == 0, every variable `x_i` has a pure power `x_i^{b_i}` in `LM(RGB(I))`!
  let bounds = Array::make(n, 0)
  for i in 0..<n {
    let mut b_i = -1
    for lm in lms {
      let mut pure_i = lm[i] > 0
      for j in 0..<n {
        if j != i && lm[j] > 0 {
          pure_i = false
          break
        }
      }
      if pure_i && (b_i < 0 || lm[i] < b_i) {
        b_i = lm[i]
      }
    }
    if b_i < 0 {
      return None
    }
    bounds[i] = b_i
  }
  let out : Array[Array[Int32]] = []
  let cur = Array::make(n, 0)
  fn gen(pos : Int32) -> Unit {
    if pos == n {
      let mut divisible = false
      for lm in lms {
        if exps_divides(lm, cur) {
          divisible = true
          break
        }
      }
      if !divisible {
        out.push(cur.copy())
      }
      return
    }
    for e in 0..<bounds[pos] {
      cur[pos] = e
      gen(pos + 1)
    }
  }
  gen(0)
  Some(out)
}

///|
/// Exact `Q`-vector space dimension `dim_Q (Q[x_0..x_{n-1}] / I)` for a
/// 0-dimensional ideal (`0` if `I = <1>`, `None` if `Krull dim > 0`).
pub fn ideal_quotient_vector_space_dim(idl : Ideal) -> Int32? {
  match ideal_standard_monomials(idl) {
    Some(mons) => Some(mons.length())
    None => None
  }
}
