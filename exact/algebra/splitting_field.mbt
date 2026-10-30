///|
// Polynomials over a simple algebraic extension, factorization over
// that extension, and splitting fields.
//
// Factorization over `K = Q(alpha)` uses Trager's norm method: for a
// shift `s` whose norm polynomial `N(f(X - s*alpha))` is squarefree,
// irreducible rational factors of the norm pull back under
// `X |-> X + s*alpha` and gcd with `f` over K to the irreducible
// factors of `f`.  Splitting fields are built by repeatedly
// adjoining a root of a nonlinear K-factor and collapsing the
// resulting two-generator field to one primitive generator
// `theta = beta + c*alpha`; the old generator is recovered as the
// unique common root of its minimal polynomial and the transported
// defining equation for beta.  Every returned root can therefore be
// checked by exact evaluation in one `AlgNum` field.

///|
pub struct AlgPoly {
  modulus : QPoly
  coeffs : Array[AlgNum]
}

///|
pub struct AlgPolyFactor {
  factor : AlgPoly
  multiplicity : Int32
}

///|
pub struct SplittingRoot {
  value : AlgNum
  multiplicity : Int32
}

///|
pub struct SplittingField {
  modulus : QPoly
  roots : Array[SplittingRoot]
}

///|
fn algpoly_make(modulus : QPoly, coeffs : Array[AlgNum]) -> AlgPoly {
  let mut n = coeffs.length()
  while n > 1 && alg_is_zero(coeffs[n - 1]) {
    n = n - 1
  }
  let out : Array[AlgNum] = []
  if coeffs.length() == 0 {
    out.push(alg_zero(modulus))
  } else {
    for i in 0..<n {
      out.push(coeffs[i])
    }
  }
  AlgPoly::{ modulus, coeffs: out, }
}

///|
pub fn algpoly_zero(modulus : QPoly) -> AlgPoly {
  algpoly_make(modulus, [alg_zero(modulus)])
}

///|
pub fn algpoly_one(modulus : QPoly) -> AlgPoly {
  algpoly_make(modulus, [alg_one(modulus)])
}

///|
pub fn algpoly_from_qpoly(modulus : QPoly, p : QPoly) -> AlgPoly {
  let coeffs : Array[AlgNum] = []
  for i in 0..<p.coeffs.length() {
    coeffs.push(alg_rat(modulus, p.coeffs[i]))
  }
  algpoly_make(modulus, coeffs)
}

///|
pub fn algpoly_degree(p : AlgPoly) -> Int32 {
  if p.coeffs.length() == 1 && alg_is_zero(p.coeffs[0]) {
    -1
  } else {
    p.coeffs.length() - 1
  }
}

///|
pub fn algpoly_is_zero(p : AlgPoly) -> Bool {
  algpoly_degree(p) < 0
}

///|
fn algpoly_coeff(p : AlgPoly, i : Int32) -> AlgNum {
  if i < 0 || i >= p.coeffs.length() {
    alg_zero(p.modulus)
  } else {
    p.coeffs[i]
  }
}

///|
pub fn algpoly_add(a : AlgPoly, b : AlgPoly) -> AlgPoly {
  let n = if a.coeffs.length() > b.coeffs.length() {
    a.coeffs.length()
  } else {
    b.coeffs.length()
  }
  let out : Array[AlgNum] = []
  for i in 0..<n {
    out.push(alg_add(algpoly_coeff(a, i), algpoly_coeff(b, i)))
  }
  algpoly_make(a.modulus, out)
}

///|
pub fn algpoly_sub(a : AlgPoly, b : AlgPoly) -> AlgPoly {
  let n = if a.coeffs.length() > b.coeffs.length() {
    a.coeffs.length()
  } else {
    b.coeffs.length()
  }
  let out : Array[AlgNum] = []
  for i in 0..<n {
    out.push(alg_sub(algpoly_coeff(a, i), algpoly_coeff(b, i)))
  }
  algpoly_make(a.modulus, out)
}

///|
pub fn algpoly_mul(a : AlgPoly, b : AlgPoly) -> AlgPoly {
  if algpoly_is_zero(a) || algpoly_is_zero(b) {
    return algpoly_zero(a.modulus)
  }
  let out : Array[AlgNum] = []
  for _i in 0..<(a.coeffs.length() + b.coeffs.length() - 1) {
    out.push(alg_zero(a.modulus))
  }
  for i in 0..<a.coeffs.length() {
    for j in 0..<b.coeffs.length() {
      out[i + j] = alg_add(out[i + j], alg_mul(a.coeffs[i], b.coeffs[j]))
    }
  }
  algpoly_make(a.modulus, out)
}

///|
pub fn algpoly_scale(c : AlgNum, p : AlgPoly) -> AlgPoly {
  let out : Array[AlgNum] = []
  for i in 0..<p.coeffs.length() {
    out.push(alg_mul(c, p.coeffs[i]))
  }
  algpoly_make(p.modulus, out)
}

///|
pub fn algpoly_pow(p : AlgPoly, e : Int32) -> AlgPoly {
  let mut out = algpoly_one(p.modulus)
  for _i in 0..<e {
    out = algpoly_mul(out, p)
  }
  out
}

///|
pub fn algpoly_eq(a : AlgPoly, b : AlgPoly) -> Bool {
  qpoly_eq(a.modulus, b.modulus) && algpoly_is_zero(algpoly_sub(a, b))
}

///|
pub fn algpoly_monic(p : AlgPoly) -> AlgPoly {
  if algpoly_is_zero(p) {
    return p
  }
  match alg_inv(p.coeffs[p.coeffs.length() - 1]) {
    Some(inv) => algpoly_scale(inv, p)
    None => p
  }
}

///|
pub struct AlgPolyDiv {
  quotient : AlgPoly
  remainder : AlgPoly
}

///|
pub fn algpoly_divmod(a : AlgPoly, b : AlgPoly) -> AlgPolyDiv {
  if algpoly_is_zero(b) {
    return AlgPolyDiv::{
      quotient: algpoly_zero(a.modulus),
      remainder: algpoly_zero(a.modulus),
    }
  }
  let db = algpoly_degree(b)
  let qcoeffs : Array[AlgNum] = []
  let qlen = if algpoly_degree(a) >= db {
    algpoly_degree(a) - db + 1
  } else {
    1
  }
  for _i in 0..<qlen {
    qcoeffs.push(alg_zero(a.modulus))
  }
  let mut rem = a
  let lb = b.coeffs[b.coeffs.length() - 1]
  while !algpoly_is_zero(rem) && algpoly_degree(rem) >= db {
    let shift = algpoly_degree(rem) - db
    let coeff = match alg_div(rem.coeffs[rem.coeffs.length() - 1], lb) {
      Some(v) => v
      None => break
    }
    qcoeffs[shift] = coeff
    let sub : Array[AlgNum] = []
    for _i in 0..<shift {
      sub.push(alg_zero(a.modulus))
    }
    for i in 0..<b.coeffs.length() {
      sub.push(alg_mul(coeff, b.coeffs[i]))
    }
    rem = algpoly_sub(rem, algpoly_make(a.modulus, sub))
  }
  AlgPolyDiv::{ quotient: algpoly_make(a.modulus, qcoeffs), remainder: rem, }
}

///|
pub fn algpoly_mod(a : AlgPoly, b : AlgPoly) -> AlgPoly {
  algpoly_divmod(a, b).remainder
}

///|
pub fn algpoly_div_exact(a : AlgPoly, b : AlgPoly) -> AlgPoly {
  algpoly_divmod(a, b).quotient
}

///|
pub fn algpoly_gcd(a0 : AlgPoly, b0 : AlgPoly) -> AlgPoly {
  let mut a = a0
  let mut b = b0
  while !algpoly_is_zero(b) {
    let r = algpoly_mod(a, b)
    a = b
    b = r
  }
  algpoly_monic(a)
}

///|
pub fn algpoly_derivative(p : AlgPoly) -> AlgPoly {
  let out : Array[AlgNum] = []
  for i in 1..<p.coeffs.length() {
    out.push(alg_scale_rat(rat_int(i), p.coeffs[i]))
  }
  algpoly_make(p.modulus, out)
}

///|
pub fn algpoly_eval(p : AlgPoly, x : AlgNum) -> AlgNum {
  let mut acc = alg_zero(p.modulus)
  for i = p.coeffs.length() - 1; i >= 0; i = i - 1 {
    acc = alg_add(alg_mul(acc, x), p.coeffs[i])
  }
  acc
}

///|
pub fn algpoly_squarefree_factorization(p : AlgPoly) -> Array[AlgPolyFactor] {
  let out : Array[AlgPolyFactor] = []
  if algpoly_degree(p) <= 0 {
    return out
  }
  let f = algpoly_monic(p)
  let df = algpoly_derivative(f)
  let a0 = algpoly_gcd(f, df)
  let mut b = algpoly_div_exact(f, a0)
  let mut c = algpoly_div_exact(df, a0)
  let mut d = algpoly_sub(c, algpoly_derivative(b))
  let mut i = 1
  while algpoly_degree(b) > 0 {
    let a = algpoly_gcd(b, d)
    if algpoly_degree(a) > 0 {
      out.push(AlgPolyFactor::{ factor: algpoly_monic(a), multiplicity: i, })
    }
    b = algpoly_div_exact(b, a)
    c = algpoly_div_exact(d, a)
    i = i + 1
    d = algpoly_sub(c, algpoly_derivative(b))
  }
  out
}

///|
fn qpoly_interpolate_rat(xs : Array[Rat], ys : Array[Rat]) -> QPoly {
  let mut result = qpoly_zero()
  for j in 0..<xs.length() {
    let mut basis = qpoly_one()
    let mut denom = rat_one()
    for k in 0..<xs.length() {
      if k != j {
        basis = qpoly_mul(basis, qpoly_normalize([rat_neg(xs[k]), rat_one()]))
        denom = rat_mul(denom, rat_sub(xs[j], xs[k]))
      }
    }
    result = qpoly_add(result, qpoly_scale(rat_div(ys[j], denom), basis))
  }
  result
}

///|
fn sample_points(count : Int32) -> Array[Rat] {
  let out : Array[Rat] = []
  for k in 0..<count {
    let value = if k == 0 {
      0
    } else if k % 2 == 1 {
      (k + 1) / 2
    } else {
      0 - k / 2
    }
    out.push(rat_int(value))
  }
  out
}

///|
/// `Norm_{K/Q}(f(Y - s*alpha))` as a polynomial in `Y`, computed by
/// exact norm evaluations and rational interpolation.
pub fn algpoly_norm_shifted(f : AlgPoly, s : Int32) -> QPoly {
  let degree = alg_ext_degree(alg_generator(f.modulus)) * algpoly_degree(f)
  let xs = sample_points(degree + 1)
  let ys : Array[Rat] = []
  let alpha = alg_generator(f.modulus)
  for i in 0..<xs.length() {
    let point = alg_sub(
      alg_rat(f.modulus, xs[i]),
      alg_scale_rat(rat_int(s), alpha),
    )
    ys.push(alg_norm(algpoly_eval(f, point)))
  }
  qpoly_interpolate_rat(xs, ys)
}

///|
fn algpoly_shift_by_alpha(q : QPoly, modulus : QPoly, s : Int32) -> AlgPoly {
  // q(X + s*alpha), by Horner in K[X].
  let x_plus = algpoly_make(modulus, [
    alg_scale_rat(rat_int(s), alg_generator(modulus)),
    alg_one(modulus),
  ])
  let mut out = algpoly_zero(modulus)
  for i = q.coeffs.length() - 1; i >= 0; i = i - 1 {
    out = algpoly_add(
      algpoly_mul(out, x_plus),
      algpoly_make(modulus, [alg_rat(modulus, q.coeffs[i])]),
    )
  }
  out
}

///|
fn algpoly_array_contains(xs : Array[AlgPoly], x : AlgPoly) -> Bool {
  for i in 0..<xs.length() {
    if algpoly_eq(xs[i], x) {
      return true
    }
  }
  false
}

///|
fn trager_factor_squarefree(f0 : AlgPoly) -> Array[AlgPoly] {
  let f = algpoly_monic(f0)
  let n = algpoly_degree(f)
  if n <= 1 {
    return [f]
  }
  let ext_degree = qpoly_degree(f.modulus)
  let candidates = sample_points(n * n + 81)
  for ci in 0..<candidates.length() {
    let s_rat = candidates[ci]
    // sample_points yields integral rationals.
    let s = rat_to_double(s_rat).to_int()
    let norm = algpoly_norm_shifted(f, s)
    if qpoly_degree(norm) != ext_degree * n || !qpoly_is_squarefree(norm) {
      continue
    }
    let rational_factors = qpoly_factor_complete(norm)
    let factors : Array[AlgPoly] = []
    for i in 0..<rational_factors.factors.length() {
      let pulled = algpoly_shift_by_alpha(
        rational_factors.factors[i].factor,
        f.modulus,
        s,
      )
      let g = algpoly_gcd(f, pulled)
      if algpoly_degree(g) > 0 && !algpoly_array_contains(factors, g) {
        factors.push(g)
      }
    }
    let mut product = algpoly_one(f.modulus)
    let mut total_degree = 0
    for i in 0..<factors.length() {
      product = algpoly_mul(product, factors[i])
      total_degree = total_degree + algpoly_degree(factors[i])
    }
    if total_degree == n && algpoly_eq(algpoly_monic(product), f) {
      return factors
    }
  }
  [f]
}

///|
/// Complete factorization over the algebraic extension, with monic
/// irreducible factors and multiplicities.
pub fn algpoly_factor_complete(p : AlgPoly) -> Array[AlgPolyFactor] {
  let out : Array[AlgPolyFactor] = []
  let groups = algpoly_squarefree_factorization(p)
  for i in 0..<groups.length() {
    let factors = trager_factor_squarefree(groups[i].factor)
    for j in 0..<factors.length() {
      out.push(AlgPolyFactor::{
        factor: factors[j],
        multiplicity: groups[i].multiplicity,
      })
    }
  }
  out
}

///|
fn adjoin_root_collapse(
  modulus : QPoly,
  g : AlgPoly,
) -> (QPoly, AlgNum, AlgNum)? {
  let old_degree = qpoly_degree(modulus)
  let new_degree = algpoly_degree(g)
  let target_degree = old_degree * new_degree
  let candidate_points = sample_points(old_degree * new_degree * 4 + 81)
  for ci in 0..<candidate_points.length() {
    let c = rat_to_double(candidate_points[ci]).to_int()
    // R(T) = Norm_K(g_alpha(T - c*alpha)); its roots are beta+c*alpha
    // over all conjugate pairs.
    let xs = sample_points(target_degree + 1)
    let ys : Array[Rat] = []
    let alpha = alg_generator(modulus)
    for i in 0..<xs.length() {
      let point = alg_sub(
        alg_rat(modulus, xs[i]),
        alg_scale_rat(rat_int(c), alpha),
      )
      ys.push(alg_norm(algpoly_eval(g, point)))
    }
    let r = qpoly_interpolate_rat(xs, ys)
    if qpoly_degree(r) != target_degree {
      continue
    }
    let factors = qpoly_factor_complete(r)
    for fi in 0..<factors.factors.length() {
      let h = factors.factors[fi].factor
      if qpoly_degree(h) != target_degree {
        continue
      }
      // Build H(A) in L[A]: sum_j a_j(A) * (theta - c*A)^j.
      let theta = alg_generator(h)
      let theta_minus = algpoly_make(h, [theta, alg_int(h, 0 - c)])
      let mut transported = algpoly_zero(h)
      for j in 0..<g.coeffs.length() {
        let lifted = algpoly_from_qpoly(h, g.coeffs[j].poly)
        transported = algpoly_add(
          transported,
          algpoly_mul(lifted, algpoly_pow(theta_minus, j)),
        )
      }
      let common = algpoly_gcd(algpoly_from_qpoly(h, modulus), transported)
      if algpoly_degree(common) != 1 {
        continue
      }
      let alpha_expr = match
        alg_div(alg_neg(algpoly_coeff(common, 0)), algpoly_coeff(common, 1)) {
        Some(v) => v
        None => continue
      }
      let beta_expr = alg_sub(theta, alg_scale_rat(rat_int(c), alpha_expr))
      // Verify both defining equations in L.
      if !alg_is_zero(alg_eval_qpoly(modulus, alpha_expr)) {
        continue
      }
      let mapped_coeffs : Array[AlgNum] = []
      for j in 0..<g.coeffs.length() {
        mapped_coeffs.push(alg_eval_qpoly(g.coeffs[j].poly, alpha_expr))
      }
      let mapped_g = algpoly_make(h, mapped_coeffs)
      if alg_is_zero(algpoly_eval(mapped_g, beta_expr)) {
        return Some((h, alpha_expr, beta_expr))
      }
    }
  }
  None
}

///|
fn linear_root(f : AlgPoly) -> AlgNum? {
  if algpoly_degree(f) != 1 {
    return None
  }
  alg_div(alg_neg(algpoly_coeff(f, 0)), algpoly_coeff(f, 1))
}

///|
fn map_algpoly(f : AlgPoly, alpha_expr : AlgNum) -> AlgPoly {
  let coeffs : Array[AlgNum] = []
  for i in 0..<f.coeffs.length() {
    coeffs.push(alg_eval_qpoly(f.coeffs[i].poly, alpha_expr))
  }
  algpoly_make(alpha_expr.modulus, coeffs)
}

///|
/// Construct a splitting field as one simple extension and list all
/// distinct roots with their multiplicities in `p`.
///
/// The work list refines individual irreducible factors rather than
/// refactored whole squarefree groups after every adjunction.  This
/// keeps Trager norms at `(field degree)*(current factor degree)`
/// instead of repeatedly paying for the degree of the full input.
pub fn qpoly_splitting_field(p : QPoly) -> SplittingField? {
  if qpoly_degree(p) <= 0 {
    return Some(SplittingField::{ modulus: qpoly_x(), roots: [], })
  }
  let groups = qpoly_squarefree_factorization(p)
  let mut modulus = qpoly_x()
  let mut work : Array[AlgPolyFactor] = []
  for gi in 0..<groups.length() {
    let factors = qpoly_factor_complete(groups[gi].factor)
    for fi in 0..<factors.factors.length() {
      for _copy in 0..<factors.factors[fi].multiplicity {
        work.push(AlgPolyFactor::{
          factor: algpoly_from_qpoly(modulus, factors.factors[fi].factor),
          multiplicity: groups[gi].multiplicity,
        })
      }
    }
  }
  for _step in 0..<32 {
    let refined : Array[AlgPolyFactor] = []
    let mut nonlinear : AlgPoly? = None
    let mut nonlinear_index = -1
    for wi in 0..<work.length() {
      let factors = algpoly_factor_complete(work[wi].factor)
      for fi in 0..<factors.length() {
        refined.push(AlgPolyFactor::{
          factor: factors[fi].factor,
          multiplicity: work[wi].multiplicity * factors[fi].multiplicity,
        })
        match nonlinear {
          None =>
            if algpoly_degree(factors[fi].factor) > 1 {
              nonlinear = Some(factors[fi].factor)
              nonlinear_index = refined.length() - 1
            }
          Some(_) => ()
        }
      }
    }
    work = refined
    match nonlinear {
      None => {
        let roots : Array[SplittingRoot] = []
        for wi in 0..<work.length() {
          match linear_root(work[wi].factor) {
            Some(value) =>
              roots.push(SplittingRoot::{
                value,
                multiplicity: work[wi].multiplicity,
              })
            None => return None
          }
        }
        return Some(SplittingField::{ modulus, roots, })
      }
      Some(g) =>
        match adjoin_root_collapse(modulus, g) {
          Some((new_modulus, alpha_expr, beta_expr)) => {
            let mapped : Array[AlgPolyFactor] = []
            for wi in 0..<work.length() {
              let mapped_factor = map_algpoly(work[wi].factor, alpha_expr)
              if wi == nonlinear_index {
                // beta_expr is a known root of the transported
                // selected factor: split it immediately instead of
                // factoring that factor again in the larger field.
                let linear = algpoly_make(new_modulus, [
                  alg_neg(beta_expr),
                  alg_one(new_modulus),
                ])
                let dm = algpoly_divmod(mapped_factor, linear)
                if algpoly_is_zero(dm.remainder) {
                  mapped.push(AlgPolyFactor::{
                    factor: linear,
                    multiplicity: work[wi].multiplicity,
                  })
                  if algpoly_degree(dm.quotient) > 0 {
                    mapped.push(AlgPolyFactor::{
                      factor: algpoly_monic(dm.quotient),
                      multiplicity: work[wi].multiplicity,
                    })
                  }
                } else {
                  mapped.push(AlgPolyFactor::{
                    factor: mapped_factor,
                    multiplicity: work[wi].multiplicity,
                  })
                }
              } else {
                mapped.push(AlgPolyFactor::{
                  factor: mapped_factor,
                  multiplicity: work[wi].multiplicity,
                })
              }
            }
            work = mapped
            modulus = new_modulus
          }
          None => return None
        }
    }
  }
  None
}

///|
/// Certificate check: irreducible modulus, distinct roots in the
/// field, all roots of `p`, and a full linear factorization of `p`
/// after lifting it to the splitting field.
pub fn splitting_field_is_certified(p : QPoly, field : SplittingField) -> Bool {
  if qpoly_degree(field.modulus) > 1 && !qpoly_is_irreducible(field.modulus) {
    return false
  }
  let mut total = 0
  for i in 0..<field.roots.length() {
    let root = field.roots[i]
    if root.multiplicity <= 0 ||
      !qpoly_eq(root.value.modulus, field.modulus) ||
      !alg_is_zero(alg_eval_qpoly(p, root.value)) {
      return false
    }
    total = total + root.multiplicity
    for j in (i + 1)..<field.roots.length() {
      if alg_eq(root.value, field.roots[j].value) {
        return false
      }
    }
  }
  if total != qpoly_degree(p) {
    return false
  }
  let mut product = algpoly_make(field.modulus, [
    alg_rat(field.modulus, qpoly_leading(p)),
  ])
  for i in 0..<field.roots.length() {
    let linear = algpoly_make(field.modulus, [
      alg_neg(field.roots[i].value),
      alg_one(field.modulus),
    ])
    product = algpoly_mul(
      product,
      algpoly_pow(linear, field.roots[i].multiplicity),
    )
  }
  algpoly_eq(product, algpoly_from_qpoly(field.modulus, p))
}

///|
pub fn check_splitting_field() -> Bool {
  let x = qpoly_x()
  let cube = qpoly_sub(qpoly_pow(x, 3), qpoly_int(2))
  let biquadratic = qpoly_mul(
    qpoly_sub(qpoly_mul(x, x), qpoly_int(2)),
    qpoly_sub(qpoly_mul(x, x), qpoly_int(3)),
  )
  let repeated = qpoly_mul(
    qpoly_pow(qpoly_sub(x, qpoly_int(2)), 2),
    qpoly_add(qpoly_mul(x, x), qpoly_int(1)),
  )
  let cube_ok = match qpoly_splitting_field(cube) {
    Some(field) =>
      qpoly_degree(field.modulus) == 6 &&
      field.roots.length() == 3 &&
      splitting_field_is_certified(cube, field)
    None => false
  }
  let biquadratic_ok = match qpoly_splitting_field(biquadratic) {
    Some(field) =>
      qpoly_degree(field.modulus) == 4 &&
      field.roots.length() == 4 &&
      splitting_field_is_certified(biquadratic, field)
    None => false
  }
  let repeated_ok = match qpoly_splitting_field(repeated) {
    Some(field) =>
      field.roots.length() == 3 && splitting_field_is_certified(repeated, field)
    None => false
  }
  cube_ok && biquadratic_ok && repeated_ok
}
