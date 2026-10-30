///|
// Phase 14 exact-algebra extensions:
//
// 1. Cantor–Zassenhaus equal-degree factorization over F_p +
//    quadratic Hensel lifting over Z/p^{2^r}Z + Landau–Mignotte
//    subset recombination, paired with portable per-factor
//    irreducibility certificates (`QPolyFactorCertificate`).
// 2. Configurable-rank multiquadratic towers (`k <= 6`, up to 64
//    basis slots) and canonical real algebraic radical normal forms
//    (`RealAlgRadical`: monic irreducible minimal polynomial +
//    ordered Sturm root index) deciding nested dihedral quadratic
//    and mixed quadratic/cubic Ramanujan radical equalities.
// 3. Hermitian block-diagonal support-graph deflation
//    (`JacobiBlockDeflatedReport`) decomposing exact Hermitian
//    matrices into decoupled subblocks before adaptive Jacobi /
//    squarefree Sturm separation.

// ---------------------------------------------------------------------------
// 1. Cantor–Zassenhaus + Quadratic Hensel Lifting + Factor Certificates
// ---------------------------------------------------------------------------

///|
/// One monic irreducible factor together with its multiplicity and
/// an optional portable irreducibility witness.
pub struct QPolyCertifiedFactor {
  factor : QPoly
  multiplicity : Int32
  certificate : QPolyIrreducibilityCertificate?
} derive(Debug, Eq)

///|
pub extend QPolyCertifiedFactor with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend QPolyCertifiedFactor with Eq::{not_equal, equal}

///|
/// Portable complete factorization certificate over Q.
pub struct QPolyFactorCertificate {
  leading : Rat
  factors : Array[QPolyCertifiedFactor]
  hensel_prime : Int32
  hensel_exponent : Int32
} derive(Debug, Eq)

///|
pub extend QPolyFactorCertificate with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend QPolyFactorCertificate with Eq::{not_equal, equal}

///|
fn mod_powmod_big(
  p : Int32,
  base0 : Array[Int32],
  exponent0 : BigInt,
  modulus : Array[Int32],
) -> Array[Int32] {
  let mut exponent = exponent0
  let mut base = mod_divmod(p, base0, modulus).1
  let mut result = mod_divmod(p, [1], modulus).1
  while exponent > 0N {
    if exponent % 2N == 1N {
      result = mod_divmod(p, mod_mul(p, result, base), modulus).1
    }
    base = mod_divmod(p, mod_mul(p, base, base), modulus).1
    exponent = exponent / 2N
  }
  result
}

///|
fn mod_monic(p : Int32, f0 : Array[Int32]) -> Array[Int32] {
  mod_monic_prime(p, f0)
}

///|
/// Distinct-degree factorization over odd `F_p` for a degree-preserving,
/// squarefree reduction of `coeffs`: returns `(g_d, d)` buckets where
/// each `g_d` is a monic product of distinct irreducibles of degree `d`.
fn mod_ddf_buckets(
  coeffs : Array[BigInt],
  p : Int32,
) -> Array[(Array[Int32], Int32)]? {
  if p <= 2 {
    None
  } else {
    mod_ddf_buckets_any_prime(coeffs, p)
  }
}

///|
fn mod_cz_candidate_poly(
  deg : Int32,
  p : Int32,
  attempt : Int32,
) -> Array[Int32] {
  if attempt < p {
    return mod_norm(p, [attempt, 1])
  }
  let mut state = BigInt::from_int(attempt + 1) * 1103515245N + 12345N
  let out : Array[Int32] = []
  let p_big = BigInt::from_int(p)
  for i in 0..<deg {
    state = (state * 6364136223846793005N + 1442695040888963407N) &
      BigInt::from_string("18446744073709551615")
    let c = (state % p_big).to_int()
    out.push(if i == deg - 1 && c == 0 { 1 } else { c })
  }
  let normed = mod_norm(p, out)
  if mod_degree(normed) <= 0 {
    [1, 1]
  } else {
    normed
  }
}

///|
/// Cantor–Zassenhaus equal-degree splitting of a monic squarefree
/// polynomial `g` over odd `F_p` whose irreducible factors all have
/// degree `d`.
fn mod_cz_edf(
  p : Int32,
  g0 : Array[Int32],
  d : Int32,
  out : Array[Array[Int32]],
) -> Bool {
  let g = mod_monic(p, g0)
  let deg = mod_degree(g)
  if deg <= 0 {
    return true
  }
  if deg == d {
    out.push(g)
    return true
  }
  let mut pd = 1N
  let p_big = BigInt::from_int(p)
  for _i in 0..<d {
    pd = pd * p_big
  }
  let half_exp = (pd - 1N) / 2N
  for attempt in 0..<(p + 64) {
    let a = mod_cz_candidate_poly(deg, p, attempt)
    let g1 = mod_gcd(p, g, a)
    if mod_degree(g1) > 0 && mod_degree(g1) < deg {
      let q1 = mod_divmod(p, g, g1).0
      return mod_cz_edf(p, g1, d, out) && mod_cz_edf(p, q1, d, out)
    }
    let pow_a = mod_powmod_big(p, a, half_exp, g)
    let shifted = mod_sub(p, pow_a, [1])
    let split = mod_gcd(p, g, shifted)
    if mod_degree(split) > 0 && mod_degree(split) < deg {
      let cofactor = mod_divmod(p, g, split).0
      return mod_cz_edf(p, split, d, out) && mod_cz_edf(p, cofactor, d, out)
    }
  }
  false
}

///|
/// Extended Euclidean algorithm for coprime polynomials over `F_p`:
/// returns `(s, t)` with `s * a + t * b == 1 (mod p)`.
fn mod_ext_gcd_one(
  p : Int32,
  a0 : Array[Int32],
  b0 : Array[Int32],
) -> (Array[Int32], Array[Int32])? {
  let mut r0 = mod_norm(p, a0)
  let mut r1 = mod_norm(p, b0)
  let mut s0 : Array[Int32] = [1]
  let mut s1 : Array[Int32] = [0]
  let mut t0 : Array[Int32] = [0]
  let mut t1 : Array[Int32] = [1]
  while mod_degree(r1) >= 0 {
    let (q, r2) = mod_divmod(p, r0, r1)
    let s2 = mod_sub(p, s0, mod_mul(p, q, s1))
    let t2 = mod_sub(p, t0, mod_mul(p, q, t1))
    r0 = r1
    r1 = r2
    s0 = s1
    s1 = s2
    t0 = t1
    t1 = t2
  }
  if mod_degree(r0) != 0 {
    return None
  }
  let inv = int_mod_inv(r0[0], p)
  let su : Array[Int32] = []
  for i in 0..<s0.length() {
    su.push(mod_mul_scalar(s0[i], inv, p))
  }
  let tu : Array[Int32] = []
  for i in 0..<t0.length() {
    tu.push(mod_mul_scalar(t0[i], inv, p))
  }
  Some((mod_norm(p, su), mod_norm(p, tu)))
}

// Polynomial arithmetic over Z / m Z (with m > 1, division only by monic).

///|
fn zmod_scalar(c : BigInt, m : BigInt) -> BigInt {
  let r = c % m
  if r < 0N {
    r + m
  } else {
    r
  }
}

///|
fn zmod_norm(m : BigInt, a : Array[BigInt]) -> Array[BigInt] {
  let mut last = -1
  let reduced : Array[BigInt] = []
  for i in 0..<a.length() {
    let v = zmod_scalar(a[i], m)
    reduced.push(v)
    if v != 0N {
      last = i
    }
  }
  if last < 0 {
    [0N]
  } else {
    let out : Array[BigInt] = []
    for i in 0..<(last + 1) {
      out.push(reduced[i])
    }
    out
  }
}

///|
fn zmod_degree(a : Array[BigInt]) -> Int32 {
  if a.length() == 1 && a[0] == 0N {
    -1
  } else {
    a.length() - 1
  }
}

///|
fn zmod_add(m : BigInt, a : Array[BigInt], b : Array[BigInt]) -> Array[BigInt] {
  let len = if a.length() > b.length() { a.length() } else { b.length() }
  let out : Array[BigInt] = []
  for i in 0..<len {
    let av = if i < a.length() { a[i] } else { 0N }
    let bv = if i < b.length() { b[i] } else { 0N }
    out.push(av + bv)
  }
  zmod_norm(m, out)
}

///|
fn zmod_sub(m : BigInt, a : Array[BigInt], b : Array[BigInt]) -> Array[BigInt] {
  let len = if a.length() > b.length() { a.length() } else { b.length() }
  let out : Array[BigInt] = []
  for i in 0..<len {
    let av = if i < a.length() { a[i] } else { 0N }
    let bv = if i < b.length() { b[i] } else { 0N }
    out.push(av - bv)
  }
  zmod_norm(m, out)
}

///|
fn zmod_mul(
  m : BigInt,
  a0 : Array[BigInt],
  b0 : Array[BigInt],
) -> Array[BigInt] {
  let a = zmod_norm(m, a0)
  let b = zmod_norm(m, b0)
  if zmod_degree(a) < 0 || zmod_degree(b) < 0 {
    return [0N]
  }
  let out : Array[BigInt] = []
  for _i in 0..<(a.length() + b.length() - 1) {
    out.push(0N)
  }
  for i in 0..<a.length() {
    if a[i] == 0N {
      continue
    }
    for j in 0..<b.length() {
      out[i + j] = (out[i + j] + a[i] * b[j]) % m
    }
  }
  zmod_norm(m, out)
}

///|
/// Division with remainder by a *monic* divisor `b` over `Z / m Z`.
fn zmod_divmod_monic(
  m : BigInt,
  a0 : Array[BigInt],
  b : Array[BigInt],
) -> (Array[BigInt], Array[BigInt]) {
  let db = zmod_degree(b)
  if db <= 0 {
    return (zmod_norm(m, a0), [0N])
  }
  let mut rem = zmod_norm(m, a0)
  let qlen = if zmod_degree(rem) >= db { zmod_degree(rem) - db + 1 } else { 1 }
  let q : Array[BigInt] = []
  for _i in 0..<qlen {
    q.push(0N)
  }
  while zmod_degree(rem) >= db {
    let shift = zmod_degree(rem) - db
    let coeff = rem[rem.length() - 1]
    q[shift] = coeff
    let sub : Array[BigInt] = []
    for _i in 0..<shift {
      sub.push(0N)
    }
    for i in 0..<b.length() {
      sub.push(coeff * b[i])
    }
    rem = zmod_sub(m, rem, sub)
  }
  (zmod_norm(m, q), rem)
}

///|
fn zmod_from_fp(a : Array[Int32], m : BigInt) -> Array[BigInt] {
  let out : Array[BigInt] = []
  for i in 0..<a.length() {
    out.push(BigInt::from_int(a[i]))
  }
  zmod_norm(m, out)
}

///|
/// Lift a coprime monic factorization `f == g * h (mod p)` to `mod p^{2^steps}`
/// by von zur Gathen & Gerhard quadratic Hensel steps.
fn hensel_lift_two(
  f : Array[BigInt],
  p : Int32,
  g_fp : Array[Int32],
  h_fp : Array[Int32],
  target_modulus : BigInt,
) -> (Array[BigInt], Array[BigInt], BigInt)? {
  let (s_fp, t_fp) = match mod_ext_gcd_one(p, g_fp, h_fp) {
    Some(pair) => pair
    None => return None
  }
  let mut m = BigInt::from_int(p)
  let mut g = zmod_from_fp(g_fp, m)
  let mut h = zmod_from_fp(h_fp, m)
  let mut s = zmod_from_fp(s_fp, m)
  let mut t = zmod_from_fp(t_fp, m)
  while m <= target_modulus {
    let m2 = m * m
    let f_m2 = zmod_norm(m2, f)
    let e = zmod_sub(m2, f_m2, zmod_mul(m2, g, h))
    let (q, r) = zmod_divmod_monic(m2, zmod_mul(m2, s, e), h)
    let g_next = zmod_add(
      m2,
      g,
      zmod_add(m2, zmod_mul(m2, t, e), zmod_mul(m2, q, g)),
    )
    let h_next = zmod_add(m2, h, r)
    if m2 > target_modulus {
      return Some((g_next, h_next, m2))
    }
    let ec = zmod_sub(
      m2,
      zmod_add(m2, zmod_mul(m2, s, g_next), zmod_mul(m2, t, h_next)),
      [1N],
    )
    let (qc, rc) = zmod_divmod_monic(m2, zmod_mul(m2, s, ec), h_next)
    let s_next = zmod_sub(m2, s, rc)
    let t_raw = zmod_sub(
      m2,
      t,
      zmod_add(m2, zmod_mul(m2, t, ec), zmod_mul(m2, qc, g_next)),
    )
    let (_, t_next) = zmod_divmod_monic(m2, t_raw, g_next)
    g = g_next
    h = h_next
    s = s_next
    t = t_next
    m = m2
  }
  Some((g, h, m))
}

///|
fn mod_prod_slice(
  p : Int32,
  factors : Array[Array[Int32]],
  lo : Int32,
  hi : Int32,
) -> Array[Int32] {
  let mut acc : Array[Int32] = [1]
  for i in lo..<hi {
    acc = mod_mul(p, acc, factors[i])
  }
  mod_monic(p, acc)
}

///|
/// Multifactor Hensel tree lifting of pairwise-coprime monic modular
/// factors of a monic integer polynomial `f`.
fn hensel_lift_many(
  f : Array[BigInt],
  p : Int32,
  factors : Array[Array[Int32]],
  lo : Int32,
  hi : Int32,
  target_modulus : BigInt,
) -> (Array[Array[BigInt]], BigInt)? {
  let count = hi - lo
  if count <= 0 {
    return Some(([], BigInt::from_int(p)))
  }
  if count == 1 {
    let mut m = BigInt::from_int(p)
    while m <= target_modulus {
      m = m * m
    }
    return Some(([zmod_norm(m, f)], m))
  }
  let mid = lo + count / 2
  let g_fp = mod_prod_slice(p, factors, lo, mid)
  let h_fp = mod_prod_slice(p, factors, mid, hi)
  let (g_lift, h_lift, m_final) = match
    hensel_lift_two(f, p, g_fp, h_fp, target_modulus) {
    Some(triple) => triple
    None => return None
  }
  let (left_list, _) = match
    hensel_lift_many(g_lift, p, factors, lo, mid, target_modulus) {
    Some(pair) => pair
    None => return None
  }
  let (right_list, _) = match
    hensel_lift_many(h_lift, p, factors, mid, hi, target_modulus) {
    Some(pair) => pair
    None => return None
  }
  let all : Array[Array[BigInt]] = []
  for i in 0..<left_list.length() {
    all.push(left_list[i])
  }
  for i in 0..<right_list.length() {
    all.push(right_list[i])
  }
  Some((all, m_final))
}

///|
fn zmod_center_coeff(c : BigInt, m : BigInt) -> BigInt {
  let v = zmod_scalar(c, m)
  if v * 2N > m {
    v - m
  } else {
    v
  }
}

///|
/// Gauss monic scaling: `tilde_F(y) = A^(n-1) * F(y / A)`, which is
/// monic in `Z[y]` when `F(x) = a_n x^n + ... + a_0` has `A = a_n > 0`.
fn monic_scaled_int_coeffs(coeffs : Array[BigInt]) -> (Array[BigInt], BigInt) {
  let n = coeffs.length() - 1
  if n <= 0 {
    return (coeffs, 1N)
  }
  let lc = bigint_abs(coeffs[n])
  let sign = if coeffs[n] < 0N { -1N } else { 1N }
  let powers : Array[BigInt] = [1N]
  for _i in 1..<n {
    powers.push(powers[powers.length() - 1] * lc)
  }
  let out : Array[BigInt] = []
  for i in 0..<n {
    out.push(sign * coeffs[i] * powers[n - 1 - i])
  }
  out.push(1N)
  (out, lc)
}

///|
/// Unscale a monic candidate `G_tilde(y)` back to `monic(G_tilde(lc * x))`.
fn unscale_monic_candidate(g_tilde : Array[BigInt], lc : BigInt) -> QPoly {
  let coeffs : Array[Rat] = []
  let mut lc_pow = 1N
  for i in 0..<g_tilde.length() {
    coeffs.push(rat_big_int(g_tilde[i] * lc_pow))
    lc_pow = lc_pow * lc
  }
  qpoly_monic(qpoly_normalize(coeffs))
}

///|
fn mignotte_target_modulus(tilde_coeffs : Array[BigInt]) -> BigInt {
  let n = tilde_coeffs.length() - 1
  let mut norm1 = 0N
  for i in 0..<tilde_coeffs.length() {
    norm1 = norm1 + bigint_abs(tilde_coeffs[i])
  }
  let two_pow = 1N << (n + 2)
  2N * two_pow * (norm1 + 1N) + 4N
}

///|
fn hensel_recombine_subset(
  cur_f : QPoly,
  tilde_const : BigInt,
  lc : BigInt,
  lifted : Array[Array[BigInt]],
  active : Array[Int32],
  modulus : BigInt,
  target_card : Int32,
  pos : Int32,
  chosen : Array[Int32],
) -> (QPoly, Array[Int32])? {
  if chosen.length() == target_card {
    // Fast constant-term divisibility filter on tilde_F(0).
    let mut prod_const = 1N
    for i in 0..<chosen.length() {
      let idx = chosen[i]
      let c0 = if lifted[idx].length() > 0 { lifted[idx][0] } else { 0N }
      prod_const = prod_const * c0 % modulus
    }
    let centered0 = zmod_center_coeff(prod_const, modulus)
    if tilde_const != 0N && (centered0 == 0N || tilde_const % centered0 != 0N) {
      return None
    }
    let mut prod : Array[BigInt] = [1N]
    for i in 0..<chosen.length() {
      prod = zmod_mul(modulus, prod, lifted[chosen[i]])
    }
    let centered : Array[BigInt] = []
    for i in 0..<prod.length() {
      centered.push(zmod_center_coeff(prod[i], modulus))
    }
    let cand = unscale_monic_candidate(centered, lc)
    if qpoly_degree(cand) > 0 &&
      qpoly_degree(cand) < qpoly_degree(cur_f) &&
      qpoly_is_zero(qpoly_mod(cur_f, cand)) {
      return Some((cand, [..chosen]))
    }
    return None
  }
  let remaining_slots = target_card - chosen.length()
  if active.length() - pos < remaining_slots {
    return None
  }
  for i in pos..<(active.length() - remaining_slots + 1) {
    chosen.push(active[i])
    match
      hensel_recombine_subset(
        cur_f,
        tilde_const,
        lc,
        lifted,
        active,
        modulus,
        target_card,
        i + 1,
        chosen,
      ) {
      Some(hit) => return Some(hit)
      None => ignore(chosen.pop())
    }
  }
  None
}

///|
fn factor_squarefree_hensel(f0 : QPoly) -> (Array[QPoly], Int32, Int32) {
  let mut f = qpoly_monic(f0)
  let out : Array[QPoly] = []
  let mut used_prime = 0
  let mut used_exp = 0
  while qpoly_degree(f) > 0 {
    if qpoly_degree(f) == 1 {
      out.push(f)
      break
    }
    match qpoly_irreducibility_certificate(f, prime_bound=251, shift_bound=8) {
      Some(cert) =>
        if qpoly_irreducibility_certificate_check(f, cert) {
          out.push(f)
          break
        }
      None => ()
    }
    let roots = qpoly_rational_roots(f)
    if roots.length() > 0 {
      let lin = qpoly_monic(qpoly_normalize([rat_neg(roots[0]), rat_one()]))
      out.push(lin)
      f = qpoly_monic(qpoly_div_exact(f, lin))
      continue
    }
    let int_coeffs = qpoly_integer_coeffs_big(f)
    let (tilde_f, lc) = monic_scaled_int_coeffs(int_coeffs)
    let primes = small_primes_upto(509)
    let mut best_p = -1
    let mut best_buckets : Array[(Array[Int32], Int32)] = []
    let mut best_count = 1000000
    for pi in 0..<primes.length() {
      let p = primes[pi]
      if p <= 2 || lc % BigInt::from_int(p) == 0N {
        continue
      }
      match mod_ddf_buckets(tilde_f, p) {
        Some(buckets) => {
          let mut count = 0
          for bi in 0..<buckets.length() {
            count = count + mod_degree(buckets[bi].0) / buckets[bi].1
          }
          if count == 1 {
            best_p = p
            best_buckets = buckets
            best_count = 1
            break
          }
          if count < best_count {
            best_p = p
            best_buckets = buckets
            best_count = count
            if count <= 3 {
              break
            }
          }
        }
        None => ()
      }
    }
    if best_p < 0 {
      let fallback = qpoly_factor_complete(f)
      for i in 0..<fallback.factors.length() {
        out.push(fallback.factors[i].factor)
      }
      break
    }
    if best_count == 1 {
      used_prime = best_p
      used_exp = 1
      out.push(f)
      break
    }
    let mod_factors : Array[Array[Int32]] = []
    let mut edf_ok = true
    for bi in 0..<best_buckets.length() {
      if !mod_cz_edf(
          best_p,
          best_buckets[bi].0,
          best_buckets[bi].1,
          mod_factors,
        ) {
        edf_ok = false
        break
      }
    }
    if !edf_ok {
      let fallback = qpoly_factor_complete(f)
      for i in 0..<fallback.factors.length() {
        out.push(fallback.factors[i].factor)
      }
      break
    }
    let target = mignotte_target_modulus(tilde_f)
    let (lifted, modulus) = match
      hensel_lift_many(
        tilde_f,
        best_p,
        mod_factors,
        0,
        mod_factors.length(),
        target,
      ) {
      Some(pair) => pair
      None => {
        let fallback = qpoly_factor_complete(f)
        for i in 0..<fallback.factors.length() {
          out.push(fallback.factors[i].factor)
        }
        break
      }
    }
    used_prime = best_p
    let mut exp_count = 0
    let mut m_tmp = modulus
    let p_big = BigInt::from_int(best_p)
    while m_tmp > 1N && m_tmp % p_big == 0N {
      exp_count = exp_count + 1
      m_tmp = m_tmp / p_big
    }
    used_exp = exp_count
    let mut active : Array[Int32] = []
    for i in 0..<lifted.length() {
      active.push(i)
    }
    let mut cur_f = f
    let mut cur_tilde = tilde_f
    let mut cur_lc = lc
    let mut card = 1
    while 2 * card <= active.length() && qpoly_degree(cur_f) > 0 {
      let chosen : Array[Int32] = []
      let tilde_c0 = if cur_tilde.length() > 0 { cur_tilde[0] } else { 0N }
      match
        hensel_recombine_subset(
          cur_f, tilde_c0, cur_lc, lifted, active, modulus, card, 0, chosen,
        ) {
        Some((factor, used_indices)) => {
          out.push(factor)
          cur_f = qpoly_monic(qpoly_div_exact(cur_f, factor))
          let next_int = qpoly_integer_coeffs_big(cur_f)
          let (nt, nlc) = monic_scaled_int_coeffs(next_int)
          cur_tilde = nt
          cur_lc = nlc
          let next_active : Array[Int32] = []
          for k in 0..<active.length() {
            if !used_indices.contains(active[k]) {
              next_active.push(active[k])
            }
          }
          active = next_active
        }
        None => card = card + 1
      }
    }
    if qpoly_degree(cur_f) > 0 {
      out.push(cur_f)
    }
    break
  }
  (out, used_prime, used_exp)
}

///|
/// Complete factorization over Q via Yun squarefree decomposition,
/// Cantor–Zassenhaus equal-degree splitting over `F_p`, and
/// quadratic Hensel lifting with Landau–Mignotte recombination
/// (zero Kronecker divisor-tuple enumeration on squarefree inputs).
pub fn qpoly_factor_hensel(p : QPoly) -> QPolyCompleteFactorization {
  if qpoly_degree(p) <= 0 {
    return QPolyCompleteFactorization::{
      leading: qpoly_leading(p),
      factors: [],
    }
  }
  let groups = qpoly_squarefree_factorization(p)
  let factors : Array[QPolyFactor] = []
  for i in 0..<groups.length() {
    let (irreds, _, _) = factor_squarefree_hensel(groups[i].factor)
    for j in 0..<irreds.length() {
      add_factor(factors, irreds[j], groups[i].multiplicity)
    }
  }
  QPolyCompleteFactorization::{ leading: qpoly_leading(p), factors, }
}

///|
/// Produce a portable complete factorization certificate over Q.
pub fn qpoly_factor_certified(p : QPoly) -> QPolyFactorCertificate {
  if qpoly_degree(p) <= 0 {
    return QPolyFactorCertificate::{
      leading: qpoly_leading(p),
      factors: [],
      hensel_prime: 0,
      hensel_exponent: 0,
    }
  }
  let groups = qpoly_squarefree_factorization(p)
  let raw_factors : Array[QPolyFactor] = []
  let mut prime_used = 0
  let mut exp_used = 0
  for i in 0..<groups.length() {
    let (irreds, hp, he) = factor_squarefree_hensel(groups[i].factor)
    if hp > 0 {
      prime_used = hp
      exp_used = he
    }
    for j in 0..<irreds.length() {
      add_factor(raw_factors, irreds[j], groups[i].multiplicity)
    }
  }
  let certified : Array[QPolyCertifiedFactor] = []
  for i in 0..<raw_factors.length() {
    let fac = raw_factors[i].factor
    let cert = qpoly_irreducibility_certificate(
      fac,
      prime_bound=509,
      shift_bound=12,
    )
    certified.push(QPolyCertifiedFactor::{
      factor: fac,
      multiplicity: raw_factors[i].multiplicity,
      certificate: cert,
    })
  }
  QPolyFactorCertificate::{
    leading: qpoly_leading(p),
    factors: certified,
    hensel_prime: prime_used,
    hensel_exponent: exp_used,
  }
}

///|
/// Verify a `QPolyFactorCertificate`: checks leading scalar, exact
/// polynomial expansion, monic pairwise-distinct nonconstant factors,
/// and irreducibility of every factor (via its embedded witness when
/// present, or complete irreducibility fallback).
pub fn qpoly_factor_certificate_check(
  p : QPoly,
  cert : QPolyFactorCertificate,
  require_witnesses~ : Bool = false,
) -> Bool {
  if qpoly_degree(p) <= 0 {
    return cert.factors.length() == 0 && rat_eq(cert.leading, qpoly_leading(p))
  }
  if rat_is_zero(cert.leading) || cert.factors.length() == 0 {
    return false
  }
  let mut acc = qpoly_const(cert.leading)
  for i in 0..<cert.factors.length() {
    let item = cert.factors[i]
    if item.multiplicity <= 0 ||
      qpoly_degree(item.factor) < 1 ||
      !rat_is_one(qpoly_leading(item.factor)) {
      return false
    }
    for j in (i + 1)..<cert.factors.length() {
      if qpoly_eq(item.factor, cert.factors[j].factor) {
        return false
      }
    }
    match item.certificate {
      Some(w) =>
        if !qpoly_irreducibility_certificate_check(item.factor, w) {
          return false
        }
      None =>
        if require_witnesses || !qpoly_is_irreducible(item.factor) {
          return false
        }
    }
    acc = qpoly_mul(acc, qpoly_pow(item.factor, item.multiplicity))
  }
  qpoly_eq(acc, p)
}

// ---------------------------------------------------------------------------
// 2. Configurable-Rank Multiquadratic Towers (k <= 6) & RealAlgRadical
// ---------------------------------------------------------------------------

///|
/// Construct a multiquadratic element with up to `max_gens` (`<= 8`,
/// default `6` -> up to 64 basis slots) squareclass-independent
/// generators.
pub fn multiquad_make_upto(
  basis : Array[BigInt],
  coeffs : Array[Rat],
  max_gens~ : Int32 = 6,
) -> MultiQuadNum? {
  if !multiquad_basis_valid_upto(basis, max_gens) {
    return None
  }
  let sorted = biquad_sort_basis(basis)
  multiquad_reembed_slots(basis, multiquad_full_coeffs(basis, coeffs), sorted)
}

///|
pub fn multiquad_align_upto(
  x : MultiQuadNum,
  y : MultiQuadNum,
  max_gens~ : Int32 = 6,
) -> (MultiQuadNum, MultiQuadNum)? {
  let basis = match multiquad_common_basis_upto(x.basis, y.basis, max_gens) {
    Some(v) => v
    None => return None
  }
  match
    (
      multiquad_reembed_slots(x.basis, x.coeffs, basis),
      multiquad_reembed_slots(y.basis, y.coeffs, basis),
    ) {
    (Some(u), Some(v)) => Some((u, v))
    _ => None
  }
}

///|
pub fn multiquad_add_upto(
  x : MultiQuadNum,
  y : MultiQuadNum,
  max_gens~ : Int32 = 6,
) -> MultiQuadNum? {
  match multiquad_align_upto(x, y, max_gens~) {
    Some((u, v)) => Some(multiquad_add_same(u, v))
    None => None
  }
}

///|
pub fn multiquad_mul_upto(
  x : MultiQuadNum,
  y : MultiQuadNum,
  max_gens~ : Int32 = 6,
) -> MultiQuadNum? {
  match multiquad_align_upto(x, y, max_gens~) {
    Some((u, v)) => Some(multiquad_mul_same(u, v))
    None => None
  }
}

///|
pub fn multiquad_sqrt_extended_upto(
  x : MultiQuadNum,
  max_gens~ : Int32 = 6,
) -> MultiQuadNum? {
  let (gamma, w) = match multiquad_rational_square_adjustment(x) {
    Some(v) => v
    None => return None
  }
  if gamma == 1N {
    return Some(multiquad_positive_version(w))
  }
  let root_gamma = match
    multiquad_make_upto([gamma], [rat_zero(), rat_one()], max_gens~) {
    Some(v) => v
    None => return None
  }
  let z = match multiquad_mul_upto(w, root_gamma, max_gens~) {
    Some(v) => v
    None => return None
  }
  match multiquad_align_upto(multiquad_mul_same(z, z), x, max_gens~) {
    Some((z2, xx)) =>
      if z2.coeffs == xx.coeffs {
        Some(multiquad_positive_version(z))
      } else {
        None
      }
    None => None
  }
}

///|
pub fn radical_to_multiquad_upto(
  e : RadicalExpr,
  max_gens~ : Int32 = 6,
) -> MultiQuadNum? {
  match e {
    RRat(r) => Some(multiquad_rat(r))
    RNeg(a) =>
      match radical_to_multiquad_upto(a, max_gens~) {
        Some(v) => Some(multiquad_neg(v))
        None => None
      }
    RAdd(a, b) =>
      match
        (
          radical_to_multiquad_upto(a, max_gens~),
          radical_to_multiquad_upto(b, max_gens~),
        ) {
        (Some(x), Some(y)) => multiquad_add_upto(x, y, max_gens~)
        _ => None
      }
    RSub(a, b) =>
      match
        (
          radical_to_multiquad_upto(a, max_gens~),
          radical_to_multiquad_upto(b, max_gens~),
        ) {
        (Some(x), Some(y)) => multiquad_add_upto(x, multiquad_neg(y), max_gens~)
        _ => None
      }
    RMul(a, b) =>
      match
        (
          radical_to_multiquad_upto(a, max_gens~),
          radical_to_multiquad_upto(b, max_gens~),
        ) {
        (Some(x), Some(y)) => multiquad_mul_upto(x, y, max_gens~)
        _ => None
      }
    RDiv(a, b) =>
      match
        (
          radical_to_multiquad_upto(a, max_gens~),
          radical_to_multiquad_upto(b, max_gens~),
        ) {
        (Some(x), Some(y)) =>
          match multiquad_inv(y) {
            Some(inv) => multiquad_mul_upto(x, inv, max_gens~)
            None => None
          }
        _ => None
      }
    RRoot(2, a) =>
      match radical_to_multiquad_upto(a, max_gens~) {
        Some(v) => multiquad_sqrt_extended_upto(v, max_gens~)
        None => None
      }
    RRoot(_, _) => None
  }
}

///|
/// Canonical representation of a real algebraic number:
/// `minpoly` is its unique monic irreducible minimal polynomial over Q,
/// and `root_index` (0-based) selects its unique real root among the
/// ordered Sturm-isolated real roots of `minpoly`.
pub struct RealAlgRadical {
  minpoly : QPoly
  root_index : Int32
  lower : Rat
  upper : Rat
} derive(Debug, Eq)

///|
pub extend RealAlgRadical with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend RealAlgRadical with Eq::{not_equal, equal}

///|
pub fn real_alg_of_rat(r : Rat) -> RealAlgRadical {
  RealAlgRadical::{
    minpoly: qpoly_normalize([rat_neg(r), rat_one()]),
    root_index: 0,
    lower: r,
    upper: r,
  }
}

///|
/// Canonical equality of real algebraic numbers: identical monic
/// irreducible minimal polynomial and identical ordered real-root index.
pub fn real_alg_eq(a : RealAlgRadical, b : RealAlgRadical) -> Bool {
  qpoly_eq(a.minpoly, b.minpoly) && a.root_index == b.root_index
}

///|
fn real_alg_refine_interval(x : RealAlgRadical, bits : Int32) -> (Rat, Rat) {
  if qpoly_degree(x.minpoly) <= 1 || rat_eq(x.lower, x.upper) {
    let r = rat_neg(qpoly_coeff(x.minpoly, 0))
    return (r, r)
  }
  let roots = qpoly_isolate_real_roots(x.minpoly, bits)
  if x.root_index >= 0 && x.root_index < roots.length() {
    let refined = real_root_isolation_refine(roots[x.root_index], bits)
    (refined.lower, refined.upper)
  } else {
    (x.lower, x.upper)
  }
}

///|
pub fn real_alg_sign(x : RealAlgRadical) -> Int32 {
  if qpoly_degree(x.minpoly) == 1 {
    return rat_sign(rat_neg(qpoly_coeff(x.minpoly, 0)))
  }
  // An irreducible polynomial of degree >= 2 has no root at 0.
  let mut bits = 12
  while bits <= 128 {
    let (lo, hi) = real_alg_refine_interval(x, bits)
    if rat_cmp_exact(lo, rat_zero()) > 0 {
      return 1
    }
    if rat_cmp_exact(hi, rat_zero()) < 0 {
      return -1
    }
    bits = bits * 2
  }
  0
}

///|
fn companion_matrix_of_monic(m : QPoly) -> QMat {
  let d = qpoly_degree(m)
  let rows : Array[Array[Rat]] = []
  for i in 0..<d {
    let row : Array[Rat] = []
    for j in 0..<d {
      let entry = if j == d - 1 {
        rat_neg(qpoly_coeff(m, i))
      } else if i == j + 1 {
        rat_one()
      } else {
        rat_zero()
      }
      row.push(entry)
    }
    rows.push(row)
  }
  QMat::{ n: d, rows, }
}

///|
fn kronecker_sum_matrix(a : QMat, b : QMat) -> QMat {
  let n = a.n * b.n
  let rows : Array[Array[Rat]] = []
  for i1 in 0..<a.n {
    for i2 in 0..<b.n {
      let row : Array[Rat] = []
      for j1 in 0..<a.n {
        for j2 in 0..<b.n {
          let mut v = rat_zero()
          if i2 == j2 {
            v = rat_add(v, a.rows[i1][j1])
          }
          if i1 == j1 {
            v = rat_add(v, b.rows[i2][j2])
          }
          row.push(v)
        }
      }
      rows.push(row)
    }
  }
  QMat::{ n, rows, }
}

///|
fn kronecker_prod_matrix(a : QMat, b : QMat) -> QMat {
  let n = a.n * b.n
  let rows : Array[Array[Rat]] = []
  for i1 in 0..<a.n {
    for i2 in 0..<b.n {
      let row : Array[Rat] = []
      for j1 in 0..<a.n {
        for j2 in 0..<b.n {
          row.push(rat_mul(a.rows[i1][j1], b.rows[i2][j2]))
        }
      }
      rows.push(row)
    }
  }
  QMat::{ n, rows, }
}

///|
fn intervals_overlap(lo1 : Rat, hi1 : Rat, lo2 : Rat, hi2 : Rat) -> Bool {
  rat_cmp_exact(lo1, hi2) <= 0 && rat_cmp_exact(lo2, hi1) <= 0
}

///|
/// Given a nonconstant polynomial `ann` annihilating a real algebraic
/// target and a monotone enclosure provider `enclose(bits) -> (lo, hi)`
/// whose width shrinks to 0 as `bits` grows, uniquely identify the
/// monic irreducible factor of `ann` and the ordered Sturm root index.
fn real_alg_select_unique_root(
  ann : QPoly,
  max_degree : Int32,
  enclose : (Int32) -> (Rat, Rat),
) -> RealAlgRadical? {
  let factored = qpoly_factor_hensel(ann)
  let candidates : Array[QPoly] = []
  for i in 0..<factored.factors.length() {
    let f = factored.factors[i].factor
    if qpoly_degree(f) >= 1 && qpoly_degree(f) <= max_degree {
      candidates.push(f)
    }
  }
  if candidates.length() == 0 {
    return None
  }
  let mut bits = 14
  while bits <= 160 {
    let (enc_lo, enc_hi) = enclose(bits)
    let mut hit_poly : QPoly? = None
    let mut hit_idx = -1
    let mut hit_lo = rat_zero()
    let mut hit_hi = rat_zero()
    let mut hits = 0
    for ci in 0..<candidates.length() {
      let f = candidates[ci]
      let roots = qpoly_isolate_real_roots(f, bits)
      for ri in 0..<roots.length() {
        let r = roots[ri]
        if intervals_overlap(enc_lo, enc_hi, r.lower, r.upper) {
          hits = hits + 1
          hit_poly = Some(f)
          hit_idx = ri
          hit_lo = r.lower
          hit_hi = r.upper
        }
      }
    }
    if hits == 1 {
      match hit_poly {
        Some(mp) =>
          return Some(RealAlgRadical::{
            minpoly: mp,
            root_index: hit_idx,
            lower: hit_lo,
            upper: hit_hi,
          })
        None => ()
      }
    }
    bits = bits + 18
  }
  None
}

///|
pub fn real_alg_neg(x : RealAlgRadical) -> RealAlgRadical {
  let d = qpoly_degree(x.minpoly)
  if d == 1 {
    return real_alg_of_rat(qpoly_coeff(x.minpoly, 0))
  }
  let coeffs : Array[Rat] = []
  let parity_flip = d % 2 == 1
  for i in 0..<(d + 1) {
    let c = qpoly_coeff(x.minpoly, i)
    let signed = if i % 2 == 1 { rat_neg(c) } else { c }
    coeffs.push(if parity_flip { rat_neg(signed) } else { signed })
  }
  let mp = qpoly_monic(qpoly_normalize(coeffs))
  let roots = qpoly_isolate_real_roots(mp, 16)
  let idx = roots.length() - 1 - x.root_index
  let (lo, hi) = if idx >= 0 && idx < roots.length() {
    (roots[idx].lower, roots[idx].upper)
  } else {
    (rat_neg(x.upper), rat_neg(x.lower))
  }
  RealAlgRadical::{ minpoly: mp, root_index: idx, lower: lo, upper: hi, }
}

///|
pub fn real_alg_add(
  a : RealAlgRadical,
  b : RealAlgRadical,
  max_degree~ : Int32 = 24,
) -> RealAlgRadical? {
  let da = qpoly_degree(a.minpoly)
  let db = qpoly_degree(b.minpoly)
  if da == 1 && db == 1 {
    return Some(
      real_alg_of_rat(
        rat_add(
          rat_neg(qpoly_coeff(a.minpoly, 0)),
          rat_neg(qpoly_coeff(b.minpoly, 0)),
        ),
      ),
    )
  }
  if da * db > max_degree {
    return None
  }
  let op = kronecker_sum_matrix(
    companion_matrix_of_monic(a.minpoly),
    companion_matrix_of_monic(b.minpoly),
  )
  let e0 = qvec_zero(op.n)
  e0[0] = rat_one()
  let ann = qmat_vector_annihilator(op, e0)
  real_alg_select_unique_root(ann, max_degree, bits => {
    let (alo, ahi) = real_alg_refine_interval(a, bits + 4)
    let (blo, bhi) = real_alg_refine_interval(b, bits + 4)
    (rat_add(alo, blo), rat_add(ahi, bhi))
  })
}

///|
pub fn real_alg_sub(
  a : RealAlgRadical,
  b : RealAlgRadical,
  max_degree~ : Int32 = 24,
) -> RealAlgRadical? {
  real_alg_add(a, real_alg_neg(b), max_degree~)
}

///|
fn rat_interval_mul_bounds(
  alo : Rat,
  ahi : Rat,
  blo : Rat,
  bhi : Rat,
) -> (Rat, Rat) {
  let p1 = rat_mul(alo, blo)
  let p2 = rat_mul(alo, bhi)
  let p3 = rat_mul(ahi, blo)
  let p4 = rat_mul(ahi, bhi)
  let ps = [p2, p3, p4]
  let mut lo = p1
  let mut hi = p1
  for i in 0..<ps.length() {
    if rat_cmp_exact(ps[i], lo) < 0 {
      lo = ps[i]
    }
    if rat_cmp_exact(ps[i], hi) > 0 {
      hi = ps[i]
    }
  }
  (lo, hi)
}

///|
pub fn real_alg_mul(
  a : RealAlgRadical,
  b : RealAlgRadical,
  max_degree~ : Int32 = 24,
) -> RealAlgRadical? {
  if real_alg_sign(a) == 0 || real_alg_sign(b) == 0 {
    return Some(real_alg_of_rat(rat_zero()))
  }
  let da = qpoly_degree(a.minpoly)
  let db = qpoly_degree(b.minpoly)
  if da == 1 && db == 1 {
    return Some(
      real_alg_of_rat(
        rat_mul(
          rat_neg(qpoly_coeff(a.minpoly, 0)),
          rat_neg(qpoly_coeff(b.minpoly, 0)),
        ),
      ),
    )
  }
  if da * db > max_degree {
    return None
  }
  let op = kronecker_prod_matrix(
    companion_matrix_of_monic(a.minpoly),
    companion_matrix_of_monic(b.minpoly),
  )
  let e0 = qvec_zero(op.n)
  e0[0] = rat_one()
  let ann = qmat_vector_annihilator(op, e0)
  real_alg_select_unique_root(ann, max_degree, bits => {
    let (alo, ahi) = real_alg_refine_interval(a, bits + 6)
    let (blo, bhi) = real_alg_refine_interval(b, bits + 6)
    rat_interval_mul_bounds(alo, ahi, blo, bhi)
  })
}

///|
pub fn real_alg_inv(x : RealAlgRadical) -> RealAlgRadical? {
  if real_alg_sign(x) == 0 {
    return None
  }
  let d = qpoly_degree(x.minpoly)
  if d == 1 {
    let r = rat_neg(qpoly_coeff(x.minpoly, 0))
    return Some(real_alg_of_rat(rat_inv(r)))
  }
  let rev : Array[Rat] = []
  for i in 0..<(d + 1) {
    rev.push(qpoly_coeff(x.minpoly, d - i))
  }
  let mp = qpoly_monic(qpoly_normalize(rev))
  real_alg_select_unique_root(mp, d, bits => {
    let mut b = bits + 8
    while b <= 180 {
      let (lo, hi) = real_alg_refine_interval(x, b)
      if rat_cmp_exact(lo, rat_zero()) > 0 || rat_cmp_exact(hi, rat_zero()) < 0 {
        return (rat_inv(hi), rat_inv(lo))
      }
      b = b + 16
    }
    (rat_int(-1), rat_int(1))
  })
}

///|
pub fn real_alg_div(
  a : RealAlgRadical,
  b : RealAlgRadical,
  max_degree~ : Int32 = 24,
) -> RealAlgRadical? {
  match real_alg_inv(b) {
    Some(inv_b) => real_alg_mul(a, inv_b, max_degree~)
    None => None
  }
}

///|
fn rat_nonneg_nth_root_bounds(r : Rat, n : Int32, bits : Int32) -> (Rat, Rat) {
  if rat_cmp_exact(r, rat_zero()) <= 0 {
    return (rat_zero(), rat_zero())
  }
  let scale = 1N << bits
  let mut scale_pow = 1N
  let mut den_pow_m1 = 1N
  for _i in 0..<n {
    scale_pow = scale_pow * scale
  }
  for _i in 0..<(n - 1) {
    den_pow_m1 = den_pow_m1 * r.den
  }
  // Floor of (r * scale^n)^(1/n) = floor((num * den^(n-1) * scale^n)^(1/n)) / (den * scale).
  let radicand = r.num * den_pow_m1 * scale_pow
  let fl = match bigint_nth_root_floor(radicand, n) {
    Some(v) => v
    None => 0N
  }
  let denom = r.den * scale
  (rat_make_big(fl, denom), rat_make_big(fl + 1N, denom))
}

///|
/// Principal real `n`-th root (`n >= 2`) of a real algebraic number:
/// nonnegative `x` for even `n`, arbitrary real `x` for odd `n`.
pub fn real_alg_nth_root(
  x : RealAlgRadical,
  n : Int32,
  max_degree~ : Int32 = 24,
) -> RealAlgRadical? {
  if n < 1 {
    return None
  }
  if n == 1 {
    return Some(x)
  }
  let sgn = real_alg_sign(x)
  if sgn == 0 {
    return Some(real_alg_of_rat(rat_zero()))
  }
  if sgn < 0 {
    if n % 2 == 0 {
      return None
    }
    return match real_alg_nth_root(real_alg_neg(x), n, max_degree~) {
      Some(pos_root) => Some(real_alg_neg(pos_root))
      None => None
    }
  }
  let d = qpoly_degree(x.minpoly)
  if d * n > max_degree {
    return None
  }
  // P(y) = m_x(y^n).
  let coeffs : Array[Rat] = []
  for _i in 0..<(d * n + 1) {
    coeffs.push(rat_zero())
  }
  for k in 0..<(d + 1) {
    coeffs[k * n] = qpoly_coeff(x.minpoly, k)
  }
  let poly_yn = qpoly_monic(qpoly_normalize(coeffs))
  real_alg_select_unique_root(poly_yn, max_degree, bits => {
    let mut b = bits + 8
    while b <= 180 {
      let (lo, hi) = real_alg_refine_interval(x, b)
      if rat_cmp_exact(lo, rat_zero()) > 0 {
        let (rlo, _) = rat_nonneg_nth_root_bounds(lo, n, b)
        let (_, rhi) = rat_nonneg_nth_root_bounds(hi, n, b)
        return (rlo, rhi)
      }
      b = b + 16
    }
    let (_, rhi) = rat_nonneg_nth_root_bounds(rat_one(), n, bits)
    (rat_zero(), rhi)
  })
}

///|
/// Evaluate a `RadicalExpr` into its canonical `RealAlgRadical`
/// representation (`minpoly`, `root_index`), handling genuinely
/// non-multiquadratic nested radicals and mixed root indices up to
/// `max_degree`.
pub fn radical_to_real_alg(
  e : RadicalExpr,
  max_degree~ : Int32 = 24,
) -> RealAlgRadical? {
  match e {
    RRat(r) => Some(real_alg_of_rat(r))
    RNeg(a) =>
      match radical_to_real_alg(a, max_degree~) {
        Some(x) => Some(real_alg_neg(x))
        None => None
      }
    RAdd(a, b) =>
      match
        (
          radical_to_real_alg(a, max_degree~),
          radical_to_real_alg(b, max_degree~),
        ) {
        (Some(x), Some(y)) => real_alg_add(x, y, max_degree~)
        _ => None
      }
    RSub(a, b) =>
      match
        (
          radical_to_real_alg(a, max_degree~),
          radical_to_real_alg(b, max_degree~),
        ) {
        (Some(x), Some(y)) => real_alg_sub(x, y, max_degree~)
        _ => None
      }
    RMul(a, b) =>
      match
        (
          radical_to_real_alg(a, max_degree~),
          radical_to_real_alg(b, max_degree~),
        ) {
        (Some(x), Some(y)) => real_alg_mul(x, y, max_degree~)
        _ => None
      }
    RDiv(a, b) =>
      match
        (
          radical_to_real_alg(a, max_degree~),
          radical_to_real_alg(b, max_degree~),
        ) {
        (Some(x), Some(y)) => real_alg_div(x, y, max_degree~)
        _ => None
      }
    RRoot(n, a) =>
      match radical_to_real_alg(a, max_degree~) {
        Some(x) => real_alg_nth_root(x, n, max_degree~)
        None => None
      }
  }
}

///|
/// Decide exact equality of real radical expressions across extended
/// multiquadratic towers (`k <= 6`) and general real algebraic
/// minimal-polynomial + Sturm-index normal forms (`max_degree`).
pub fn radical_equal_algebraic(
  a : RadicalExpr,
  b : RadicalExpr,
  max_gens~ : Int32 = 6,
  max_degree~ : Int32 = 24,
) -> Bool? {
  match radical_equal_exact(a, b) {
    Some(ans) => return Some(ans)
    None => ()
  }
  match
    (
      radical_to_multiquad_upto(a, max_gens~),
      radical_to_multiquad_upto(b, max_gens~),
    ) {
    (Some(x), Some(y)) =>
      match multiquad_align_upto(x, y, max_gens~) {
        Some((u, v)) => return Some(u.coeffs == v.coeffs)
        None => ()
      }
    _ => ()
  }
  match
    (radical_to_real_alg(a, max_degree~), radical_to_real_alg(b, max_degree~)) {
    (Some(x), Some(y)) => Some(real_alg_eq(x, y))
    _ => None
  }
}

// ---------------------------------------------------------------------------
// 3. Hermitian Block-Diagonal Graph Deflation for Certified Jacobi
// ---------------------------------------------------------------------------

///|
pub struct JacobiBlockDeflatedReport {
  blocks : Array[Array[Int32]]
  max_block_dimension : Int32
  block_reports : Array[JacobiAdaptiveReport]
  intervals : Array[SeparatedEigenInterval]
  target_met : Bool
  max_interval_width : Rat
}

///|
fn qcpx_is_zero_exact(z : QCpx) -> Bool {
  rat_is_zero(z.re) && rat_is_zero(z.im)
}

///|
/// Connected components of the off-diagonal nonzero graph of an
/// exact Hermitian matrix, in deterministic ascending index order.
pub fn jacobi_block_components(input : QCpxMat) -> Array[Array[Int32]] {
  let n = input.n
  let visited : Array[Bool] = []
  for _i in 0..<n {
    visited.push(false)
  }
  let blocks : Array[Array[Int32]] = []
  for start in 0..<n {
    if visited[start] {
      continue
    }
    let comp : Array[Int32] = []
    let queue : Array[Int32] = [start]
    visited[start] = true
    let mut head = 0
    while head < queue.length() {
      let u = queue[head]
      head = head + 1
      comp.push(u)
      for v in 0..<n {
        if !visited[v] &&
          (
            !qcpx_is_zero_exact(input.rows[u][v]) ||
            !qcpx_is_zero_exact(input.rows[v][u])
          ) {
          visited[v] = true
          queue.push(v)
        }
      }
    }
    for _pass in 0..<comp.length() {
      for j in 0..<(comp.length() - 1) {
        if comp[j + 1] < comp[j] {
          let tmp = comp[j]
          comp[j] = comp[j + 1]
          comp[j + 1] = tmp
        }
      }
    }
    blocks.push(comp)
  }
  blocks
}

///|
fn qcpx_principal_submatrix(input : QCpxMat, indices : Array[Int32]) -> QCpxMat {
  let k = indices.length()
  let rows : Array[Array[QCpx]] = []
  for i in 0..<k {
    let row : Array[QCpx] = []
    for j in 0..<k {
      row.push(input.rows[indices[i]][indices[j]])
    }
    rows.push(row)
  }
  QCpxMat::{ n: k, rows, }
}

///|
fn extract_block_separated_intervals(
  rep : JacobiAdaptiveReport,
) -> Array[SeparatedEigenInterval] {
  match rep.separation {
    Some(sep) => sep.intervals
    None => {
      let out : Array[SeparatedEigenInterval] = []
      let eigs = rep.cluster_aware.certificate.eigenvalues
      for i in 0..<eigs.length() {
        out.push(SeparatedEigenInterval::{
          lo: eigs[i].lo,
          hi: eigs[i].hi,
          multiplicity: eigs[i].count,
          cluster: i,
        })
      }
      out
    }
  }
}

///|
/// Block-deflated adaptive Jacobi + exact Sturm eigenvalue isolation:
/// connected support components are solved independently (1x1 blocks
/// yield zero-width exact rational point intervals directly), then
/// overlapping/identical intervals are merged with summed multiplicity.
pub fn jacobi_block_deflated_eigen(
  input : QCpxMat,
  target_width~ : Rat = rat_make(1, 1024),
  max_steps~ : Int32 = 24,
  tolerance_sq~ : Rat = rat_make(1, 1048576),
  initial_bits~ : Int32 = 10,
  max_bits~ : Int32 = 26,
  max_exact_width_bits~ : Int32 = 40,
) -> JacobiBlockDeflatedReport? {
  if !qcpx_mat_is_hermitian(input) ||
    rat_cmp_exact(target_width, rat_zero()) <= 0 ||
    max_exact_width_bits <= 0 {
    return None
  }
  let blocks = jacobi_block_components(input)
  let mut max_dim = 0
  let block_reports : Array[JacobiAdaptiveReport] = []
  let raw_intervals : Array[SeparatedEigenInterval] = []
  let mut all_met = true
  for bi in 0..<blocks.length() {
    let sub = qcpx_principal_submatrix(input, blocks[bi])
    if sub.n > max_dim {
      max_dim = sub.n
    }
    let rep = match
      jacobi_interval_eigen_adaptive(
        sub,
        target_width~,
        max_steps~,
        tolerance_sq~,
        initial_bits~,
        max_bits~,
        max_exact_width_bits~,
      ) {
      Some(r) => r
      None => return None
    }
    if !rep.target_met {
      all_met = false
    }
    let sub_ivs = extract_block_separated_intervals(rep)
    for k in 0..<sub_ivs.length() {
      raw_intervals.push(SeparatedEigenInterval::{
        lo: sub_ivs[k].lo,
        hi: sub_ivs[k].hi,
        multiplicity: sub_ivs[k].multiplicity,
        cluster: bi,
      })
    }
    block_reports.push(rep)
  }
  for _pass in 0..<raw_intervals.length() {
    for j in 0..<(raw_intervals.length() - 1) {
      let a = raw_intervals[j]
      let b = raw_intervals[j + 1]
      if rat_cmp_exact(b.lo, a.lo) < 0 ||
        (rat_eq(b.lo, a.lo) && rat_cmp_exact(b.hi, a.hi) < 0) {
        raw_intervals[j] = b
        raw_intervals[j + 1] = a
      }
    }
  }
  let merged : Array[SeparatedEigenInterval] = []
  for i in 0..<raw_intervals.length() {
    let cur = raw_intervals[i]
    if merged.length() == 0 {
      merged.push(cur)
    } else {
      let prev = merged[merged.length() - 1]
      if rat_cmp_exact(cur.lo, prev.hi) <= 0 {
        let hi = if rat_cmp_exact(cur.hi, prev.hi) > 0 {
          cur.hi
        } else {
          prev.hi
        }
        let merged_iv = SeparatedEigenInterval::{
          lo: prev.lo,
          hi,
          multiplicity: prev.multiplicity + cur.multiplicity,
          cluster: prev.cluster,
        }
        merged[merged.length() - 1] = merged_iv
      } else {
        merged.push(cur)
      }
    }
  }
  let mut max_w = rat_zero()
  for i in 0..<merged.length() {
    let w = rat_sub(merged[i].hi, merged[i].lo)
    if rat_cmp_exact(w, max_w) > 0 {
      max_w = w
    }
  }
  let final_met = all_met && rat_cmp_exact(max_w, target_width) <= 0
  Some(JacobiBlockDeflatedReport::{
    blocks,
    max_block_dimension: max_dim,
    block_reports,
    intervals: merged,
    target_met: final_met,
    max_interval_width: max_w,
  })
}

///|
/// Independently verify a block-deflated Hermitian eigenvalue report:
/// checks partition completeness, exact vanishing of all cross-block
/// entries, soundness of every per-block Jacobi/Sturm certificate, and
/// exact multiplicity conservation (`sum == input.n`).
pub fn jacobi_block_deflated_certified(
  input : QCpxMat,
  report : JacobiBlockDeflatedReport,
) -> Bool {
  if !qcpx_mat_is_hermitian(input) ||
    report.blocks.length() != report.block_reports.length() {
    return false
  }
  let block_of : Array[Int32] = []
  for _i in 0..<input.n {
    block_of.push(-1)
  }
  let mut count = 0
  for bi in 0..<report.blocks.length() {
    let blk = report.blocks[bi]
    if blk.length() == 0 || blk.length() > report.max_block_dimension {
      return false
    }
    for k in 0..<blk.length() {
      let idx = blk[k]
      if idx < 0 || idx >= input.n || block_of[idx] != -1 {
        return false
      }
      block_of[idx] = bi
      count = count + 1
    }
  }
  if count != input.n {
    return false
  }
  for i in 0..<input.n {
    for j in 0..<input.n {
      if block_of[i] != block_of[j] && !qcpx_is_zero_exact(input.rows[i][j]) {
        return false
      }
    }
  }
  for bi in 0..<report.blocks.length() {
    let sub = qcpx_principal_submatrix(input, report.blocks[bi])
    let rep = report.block_reports[bi]
    if !jacobi_certificate_sound(sub, rep.cluster_aware.certificate) {
      return false
    }
    match rep.separation {
      Some(sep) =>
        if !jacobi_cluster_separation_certified(
            sub,
            rep.cluster_aware.certificate,
            sep,
          ) {
          return false
        }
      None => ()
    }
  }
  let mut mult_sum = 0
  for i in 0..<report.intervals.length() {
    let iv = report.intervals[i]
    if iv.multiplicity <= 0 || rat_cmp_exact(iv.lo, iv.hi) > 0 {
      return false
    }
    if i > 0 && rat_cmp_exact(iv.lo, report.intervals[i - 1].hi) <= 0 {
      return false
    }
    mult_sum = mult_sum + iv.multiplicity
  }
  mult_sum == input.n
}

// ---------------------------------------------------------------------------
// Phase 14 Exact-Algebra Law Bundles
// ---------------------------------------------------------------------------

///|
pub fn check_qpoly_hensel_factor_and_certificates() -> Bool {
  let x = qpoly_x()
  // Degree-8 rootless product of three distinct monic irreducibles:
  // (x^3 - x - 1)(x^3 + 2x + 1)(x^2 + x + 2), plus non-monic scaling 3.
  let f1 = qpoly_sub(qpoly_sub(qpoly_pow(x, 3), x), qpoly_int(1))
  let f2 = qpoly_add(
    qpoly_add(qpoly_pow(x, 3), qpoly_scale(rat_int(2), x)),
    qpoly_int(1),
  )
  let f3 = qpoly_add(qpoly_add(qpoly_pow(x, 2), x), qpoly_int(2))
  let prod = qpoly_scale(rat_int(3), qpoly_mul(qpoly_mul(f1, f2), f3))
  let hf = qpoly_factor_hensel(prod)
  if hf.factors.length() != 3 ||
    !rat_eq(hf.leading, rat_int(3)) ||
    !qpoly_eq(qpoly_complete_factorization_expand(hf), prod) {
    return false
  }
  let cert = qpoly_factor_certified(prod)
  if cert.hensel_prime < 3 ||
    cert.hensel_exponent < 1 ||
    !qpoly_factor_certificate_check(prod, cert, require_witnesses=true) {
    return false
  }
  // Tampered certificate: replacing two factors by their reducible product
  // with a forged witness is rejected by `qpoly_factor_certificate_check`.
  let forged = QPolyFactorCertificate::{
    leading: rat_int(3),
    factors: [
      QPolyCertifiedFactor::{
        factor: qpoly_mul(f1, f2),
        multiplicity: 1,
        certificate: Some(CertModPrime(3)),
      },
      QPolyCertifiedFactor::{
        factor: f3,
        multiplicity: 1,
        certificate: Some(CertModPrime(3)),
      },
    ],
    hensel_prime: cert.hensel_prime,
    hensel_exponent: cert.hensel_exponent,
  }
  if qpoly_factor_certificate_check(prod, forged) {
    return false
  }
  // Non-squarefree product with multiplicity 2 and Swinnerton-Dyer x^4+1.
  let x4p1 = qpoly_add(qpoly_pow(x, 4), qpoly_int(1))
  let mixed = qpoly_mul(qpoly_pow(f3, 2), x4p1)
  let cert_mixed = qpoly_factor_certified(mixed)
  cert_mixed.factors.length() == 2 &&
  qpoly_factor_certificate_check(mixed, cert_mixed, require_witnesses=true)
}

///|
/// Equality over a common multiquadratic basis up to `max_gens` generators.
pub fn multiquad_eq_upto(
  x : MultiQuadNum,
  y : MultiQuadNum,
  max_gens~ : Int32 = 6,
) -> Bool {
  match multiquad_align_upto(x, y, max_gens~) {
    Some((u, v)) => u.coeffs == v.coeffs
    None => false
  }
}

///|
pub fn check_algebraic_radicals_and_rank6_multiquad() -> Bool {
  // 1. 6-generator multiquadratic tower (64 basis slots):
  //    w5 = 1 + √2 + √3 + √5 + √7 + √11; sqrt(13 * w5^2) == √13 * w5.
  let primes5 = [2, 3, 5, 7, 11]
  let mut w5 = multiquad_rat(rat_one())
  for i in 0..<primes5.length() {
    let g = match
      multiquad_make_upto(
        [BigInt::from_int(primes5[i])],
        [rat_zero(), rat_one()],
        max_gens=6,
      ) {
      Some(v) => v
      None => return false
    }
    w5 = match multiquad_add_upto(w5, g, max_gens=6) {
      Some(v) => v
      None => return false
    }
  }
  if w5.basis.length() != 5 || w5.coeffs.length() != 32 {
    return false
  }
  match multiquad_inv(w5) {
    Some(inv5) =>
      match multiquad_mul_upto(w5, inv5, max_gens=6) {
        Some(prod) =>
          if !multiquad_eq_upto(prod, multiquad_rat(rat_one()), max_gens=6) {
            return false
          }
        None => return false
      }
    None => return false
  }
  let w5_sq = match multiquad_mul_upto(w5, w5, max_gens=6) {
    Some(v) => v
    None => return false
  }
  let scaled13 = multiquad_scale_bigint(w5_sq, 13N)
  let root6 = match multiquad_sqrt_extended_upto(scaled13, max_gens=6) {
    Some(v) => v
    None => return false
  }
  if root6.basis.length() != 6 || root6.coeffs.length() != 64 {
    return false
  }
  // A 7th independent generator (√17) is refused at max_gens=6.
  let s17 = match
    multiquad_make_upto([17N], [rat_zero(), rat_one()], max_gens=6) {
    Some(v) => v
    None => return false
  }
  if multiquad_add_upto(root6, s17, max_gens=6) != None {
    return false
  }

  // 2. Dihedral non-multiquadratic nested radical:
  //    sqrt(1 + sqrt(2)) * sqrt(sqrt(2) - 1) == 1
  //    (while `radical_to_multiquad` returns `None` on sqrt(1 + sqrt(2))).
  let r1 = radical_int(1)
  let r2 = radical_sqrt(radical_int(2))
  let a_dih = radical_sqrt(RadicalExpr::RAdd(r1, r2))
  let b_dih = radical_sqrt(RadicalExpr::RSub(r2, r1))
  if radical_to_multiquad(a_dih) != None {
    return false
  }
  if radical_equal_algebraic(RadicalExpr::RMul(a_dih, b_dih), r1) != Some(true) {
    return false
  }
  if radical_equal_algebraic(a_dih, b_dih) != Some(false) {
    return false
  }

  // 3. Irreducible sextic nested cubic-quadratic identity + Ramanujan identity:
  //    (a) cbrt(sqrt(2) + 1) * cbrt(sqrt(2) - 1) == 1 (minpoly x^6 - 2x^3 - 1,
  //        genuinely outside QuadNum/MultiQuadNum/CubicNum so radical_equal_exact == None).
  //    (b) Ramanujan: cbrt(sqrt(5) + 2) - cbrt(sqrt(5) - 2) == 1.
  let u_pell = RadicalExpr::RRoot(3, RadicalExpr::RAdd(r2, r1))
  let v_pell = RadicalExpr::RRoot(3, RadicalExpr::RSub(r2, r1))
  if radical_equal_exact(RadicalExpr::RMul(u_pell, v_pell), r1) != None {
    return false
  }
  if radical_equal_algebraic(
      RadicalExpr::RMul(u_pell, v_pell),
      r1,
      max_degree=48,
    ) !=
    Some(true) {
    return false
  }
  let s5 = radical_sqrt(radical_int(5))
  let u_ram = RadicalExpr::RRoot(3, RadicalExpr::RAdd(s5, radical_int(2)))
  let v_ram = RadicalExpr::RRoot(3, RadicalExpr::RSub(s5, radical_int(2)))
  if radical_equal_algebraic(RadicalExpr::RSub(u_ram, v_ram), r1, max_degree=48) !=
    Some(true) {
    return false
  }

  // 4. Mixed root indices: sqrt(2) * cbrt(2) == root_6(32), and
  //    even root of negative real returns None.
  let mix_lhs = RadicalExpr::RMul(r2, RadicalExpr::RRoot(3, radical_int(2)))
  let mix_rhs = RadicalExpr::RRoot(6, radical_int(32))
  if radical_equal_algebraic(mix_lhs, mix_rhs, max_degree=48) != Some(true) {
    return false
  }
  radical_to_real_alg(radical_sqrt(radical_int(-2))) == None
}

///|
pub fn check_jacobi_block_deflation_and_multiplicity() -> Bool {
  // 6x6 Hermitian matrix permuting three 2x2 blocks across interleaved
  // indices {0,3}, {1,4}, {2,5}:
  //   Block {0,3}: tight eigenvalues ±1/4096
  //   Block {1,4}: repeated eigenvalue 3 (multiplicity 2, rank-1 shift + I)
  //   Block {2,5}: irrational eigenvalues 1 ± √2 ([[1, 1+i], [1-i, 1]])
  let eps = rat_make(1, 4096)
  let z0 = qcpx_real(rat_zero())
  let rows : Array[Array[QCpx]] = []
  for _i in 0..<6 {
    let r : Array[QCpx] = []
    for _j in 0..<6 {
      r.push(z0)
    }
    rows.push(r)
  }
  // Block {0, 3}: [[0, eps], [eps, 0]]
  rows[0][3] = qcpx_real(eps)
  rows[3][0] = qcpx_real(eps)
  // Block {1, 4}: [[3, 0], [0, 3]] -> actually two 1x1 blocks {1}, {4}
  // that merge to multiplicity 2 at exact point [3, 3]!
  rows[1][1] = qcpx_real(rat_int(3))
  rows[4][4] = qcpx_real(rat_int(3))
  // Block {2, 5}: [[1, 1+i], [1-i, 1]] (eigenvalues 1 ± √2)
  rows[2][2] = qcpx_real(rat_int(1))
  rows[5][5] = qcpx_real(rat_int(1))
  rows[2][5] = QCpx::{ re: rat_int(1), im: rat_int(1), }
  rows[5][2] = QCpx::{ re: rat_int(1), im: rat_int(-1), }
  let mat = QCpxMat::{ n: 6, rows, }
  let target = rat_make(1, 16384)
  let rep = match
    jacobi_block_deflated_eigen(
      mat,
      target_width=target,
      initial_bits=6,
      max_bits=8,
      max_exact_width_bits=32,
    ) {
    Some(r) => r
    None => return false
  }
  if rep.blocks.length() != 4 ||
    rep.max_block_dimension != 2 ||
    !rep.target_met ||
    rat_cmp_exact(rep.max_interval_width, target) > 0 ||
    !jacobi_block_deflated_certified(mat, rep) {
    return false
  }
  // Intervals must have 5 separated clusters totaling multiplicity 6,
  // with exact multiplicity-2 cluster containing 3.
  if rep.intervals.length() != 5 {
    return false
  }
  let mut found_mult2_three = false
  for i in 0..<rep.intervals.length() {
    let iv = rep.intervals[i]
    if iv.multiplicity == 2 &&
      rat_le_exact(iv.lo, rat_int(3)) &&
      rat_le_exact(rat_int(3), iv.hi) {
      found_mult2_three = true
    }
  }
  if !found_mult2_three {
    return false
  }
  // Negative check: claiming a forged single-block partition when
  // cross-entries are nonzero fails certification.
  let coupled = qcpx_mat_from_rows([
    [qcpx_real(rat_int(1)), qcpx_real(rat_int(1))],
    [qcpx_real(rat_int(1)), qcpx_real(rat_int(1))],
  ])
  let fake = JacobiBlockDeflatedReport::{
    blocks: [[0], [1]],
    max_block_dimension: 1,
    block_reports: [rep.block_reports[1], rep.block_reports[2]],
    intervals: [],
    target_met: true,
    max_interval_width: rat_zero(),
  }
  !jacobi_block_deflated_certified(coupled, fake)
}
