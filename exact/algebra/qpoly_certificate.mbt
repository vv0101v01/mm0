// ==================================================================
// Irreducibility certificates for rational polynomials.
//
// Kronecker interpolation decides irreducibility over Q in
// general, but its cost is driven by divisor enumeration.  This
// file adds classical, independently checkable irreducibility
// certificates that short-circuit the search for the (large)
// class of polynomials they cover:
//
//   * degree 2 or 3 with no rational root;
//   * irreducibility modulo a single prime (distinct-degree
//     factorization over F_p returns the full degree);
//   * the Eisenstein criterion at a prime `p`, optionally after
//     an integer shift `x -> x + s` (which preserves
//     irreducibility).  The shifted form covers, for example,
//     `x^4 + 1` (Eisenstein at 2 after `x -> x + 1`), the
//     standard example where every mod-`p` degree pattern is
//     inconclusive;
//   * (Phase 13) a finite list of usable mod-`p` degree patterns
//     whose subset-sum constraints exclude every possible
//     nontrivial factor degree.  No single listed prime need
//     leave the polynomial irreducible: for a quartic, patterns
//     [2, 2] and [1, 3] together exclude degrees 1 and 2.
//
// A certificate is a small witness; the checker re-derives the
// conclusion from the witness alone.  The complete
// factorization consults certificates first: a certified
// polynomial is factored with zero Kronecker tuples, which is
// observable through the budgeted factorization API.
// ==================================================================

///|
pub enum QPolyIrreducibilityCertificate {
  CertLinear
  CertLowDegreeNoRationalRoot
  CertModPrime(Int32)
  CertEisenstein(Int32, Int32) // prime, shift
  CertModDegreePatterns(Array[Int32]) // usable primes, in scan order
} derive(Debug, Eq)

///|
pub extend QPolyIrreducibilityCertificate with @moonbitlang/core/debug.Debug::{
  to_repr,
}

///|
pub extend QPolyIrreducibilityCertificate with Eq::{not_equal, equal}

///|
fn cert_is_prime(p : Int32) -> Bool {
  if p < 2 {
    return false
  }
  let mut d = 2
  while d * d <= p {
    if p % d == 0 {
      return false
    }
    d = d + 1
  }
  true
}

///|
fn cert_binom_big(n : Int32, k : Int32) -> BigInt {
  if k < 0 || k > n {
    return 0N
  }
  let kk = if k > n - k { n - k } else { k }
  let mut acc = 1N
  for i in 0..<kk {
    acc = acc * BigInt::from_int(n - i) / BigInt::from_int(i + 1)
  }
  acc
}

///|
/// Coefficients (ascending) of `f(x + s)` from ascending integer
/// coefficients of `f`.
fn cert_shift_coeffs(coeffs : Array[BigInt], shift : Int32) -> Array[BigInt] {
  let n = coeffs.length() - 1
  let s = BigInt::from_int(shift)
  let powers : Array[BigInt] = [1N]
  for _i in 0..<n {
    powers.push(powers[powers.length() - 1] * s)
  }
  let out : Array[BigInt] = []
  for j in 0..<(n + 1) {
    let mut acc = 0N
    for i in j..<(n + 1) {
      acc = acc + coeffs[i] * cert_binom_big(i, j) * powers[i - j]
    }
    out.push(acc)
  }
  out
}

///|
fn cert_eisenstein_at(coeffs : Array[BigInt], prime : Int32) -> Bool {
  let n = coeffs.length() - 1
  if n < 1 {
    return false
  }
  let p = BigInt::from_int(prime)
  if coeffs[n] % p == 0N {
    return false
  }
  for i in 0..<n {
    if coeffs[i] % p != 0N {
      return false
    }
  }
  coeffs[0] % (p * p) != 0N
}

///|
fn cert_patterns_exclude_all(n : Int32, patterns : Array[Array[Int32]]) -> Bool {
  if patterns.length() == 0 {
    return false
  }
  let allowed = allowed_degrees_from_patterns(n, patterns)
  for degree in 1..<(n / 2 + 1) {
    if allowed[degree] {
      return false
    }
  }
  true
}

///|
fn cert_mod_degree_patterns_search(
  coeffs : Array[BigInt],
  n : Int32,
  primes : Array[Int32],
) -> QPolyIrreducibilityCertificate? {
  let used_primes : Array[Int32] = []
  let patterns : Array[Array[Int32]] = []
  for pi in 0..<primes.length() {
    match mod_distinct_degrees(coeffs, primes[pi]) {
      Some(degrees) => {
        // A one-piece pattern is the older, smaller CertModPrime
        // witness; let that search own it.
        if degrees.length() == 1 && degrees[0] == n {
          continue
        }
        used_primes.push(primes[pi])
        patterns.push(degrees)
        if cert_patterns_exclude_all(n, patterns) {
          return Some(CertModDegreePatterns(used_primes))
        }
      }
      None => ()
    }
  }
  None
}

///|
fn cert_mod_degree_patterns_ok(f : QPoly, primes : Array[Int32]) -> Bool {
  let n = qpoly_degree(f)
  if n < 2 || primes.length() == 0 {
    return false
  }
  let coeffs = qpoly_integer_coeffs_big(f)
  let patterns : Array[Array[Int32]] = []
  for i in 0..<primes.length() {
    if !cert_is_prime(primes[i]) {
      return false
    }
    for j in 0..<i {
      if primes[j] == primes[i] {
        return false
      }
    }
    match mod_distinct_degrees(coeffs, primes[i]) {
      Some(degrees) => patterns.push(degrees)
      None => return false
    }
  }
  cert_patterns_exclude_all(n, patterns)
}

///|
/// Search for an irreducibility certificate for `f`.  The search
/// is deliberately bounded (small primes, small shifts); failure
/// says nothing about reducibility.
pub fn qpoly_irreducibility_certificate(
  f : QPoly,
  prime_bound~ : Int32 = 50,
  shift_bound~ : Int32 = 5,
) -> QPolyIrreducibilityCertificate? {
  let n = qpoly_degree(f)
  if n == 1 {
    return Some(CertLinear)
  }
  if n < 1 {
    return None
  }
  // Eisenstein, including small shifts.  Candidates are cheap
  // and cover many sparse polynomials outright.
  let coeffs = qpoly_integer_coeffs_big(f)
  let primes = small_primes_upto(prime_bound)
  let shifts : Array[Int32] = [0]
  for s in 1..<(shift_bound + 1) {
    shifts.push(s)
    shifts.push(-s)
  }
  for si in 0..<shifts.length() {
    let shifted = if shifts[si] == 0 {
      coeffs
    } else {
      cert_shift_coeffs(coeffs, shifts[si])
    }
    for pi in 0..<primes.length() {
      if cert_eisenstein_at(shifted, primes[pi]) {
        return Some(CertEisenstein(primes[pi], shifts[si]))
      }
    }
  }
  // Irreducible modulo a single prime.
  for pi in 0..<primes.length() {
    match mod_distinct_degrees(coeffs, primes[pi]) {
      Some(degrees) =>
        if degrees.length() == 1 && degrees[0] == n {
          return Some(CertModPrime(primes[pi]))
        }
      None => ()
    }
  }
  // Joint mod-`p` degree patterns: no one pattern need be
  // irreducible by itself.
  match cert_mod_degree_patterns_search(coeffs, n, primes) {
    Some(cert) => return Some(cert)
    None => ()
  }
  // Degrees two and three are irreducible iff rootless.
  if n <= 3 && qpoly_rational_roots(f).length() == 0 {
    return Some(CertLowDegreeNoRationalRoot)
  }
  None
}

///|
fn cert_mod_prime_ok(f : QPoly, p : Int32) -> Bool {
  match mod_distinct_degrees(qpoly_integer_coeffs_big(f), p) {
    Some(degrees) => degrees.length() == 1 && degrees[0] == qpoly_degree(f)
    None => false
  }
}

///|
/// Verify a certificate from the witness alone.
pub fn qpoly_irreducibility_certificate_check(
  f : QPoly,
  cert : QPolyIrreducibilityCertificate,
) -> Bool {
  let n = qpoly_degree(f)
  match cert {
    CertLinear => n == 1
    CertLowDegreeNoRationalRoot =>
      (n == 2 || n == 3) && qpoly_rational_roots(f).length() == 0
    CertModPrime(p) => cert_is_prime(p) && cert_mod_prime_ok(f, p)
    CertEisenstein(p, shift) =>
      cert_is_prime(p) &&
      n >= 1 &&
      cert_eisenstein_at(
        cert_shift_coeffs(qpoly_integer_coeffs_big(f), shift),
        p,
      )
    CertModDegreePatterns(primes) => cert_mod_degree_patterns_ok(f, primes)
  }
}

///|
/// Irreducibility certified by witness; `false` also covers
/// "no certificate found", so this is a sufficient, not
/// necessary, test.
pub fn qpoly_irreducible_certified(f : QPoly) -> Bool {
  match qpoly_irreducibility_certificate(f) {
    Some(cert) => qpoly_irreducibility_certificate_check(f, cert)
    None => false
  }
}

///|
pub fn check_qpoly_irreducibility_certificates() -> Bool {
  let x = qpoly_x()
  // x^4 + 1: Eisenstein at 2 after a unit shift, although every
  // mod-p pattern is inconclusive.
  let x4p1 = qpoly_add(qpoly_pow(x, 4), qpoly_int(1))
  let cert = match qpoly_irreducibility_certificate(x4p1) {
    Some(v) => v
    None => return false
  }
  match cert {
    CertEisenstein(p, s) => if p != 2 || (s != 1 && s != -1) { return false }
    _ => return false
  }
  if !qpoly_irreducibility_certificate_check(x4p1, cert) ||
    qpoly_irreducibility_certificate_check(x4p1, CertEisenstein(3, 1)) ||
    qpoly_irreducibility_certificate_check(x4p1, CertEisenstein(2, 0)) {
    return false
  }
  // The certificate bypasses Kronecker entirely: factorization
  // succeeds with a zero tuple budget.
  match qpoly_factor_complete_with_budget(x4p1, 0) {
    Some(f) =>
      if f.factors.length() != 1 || !qpoly_eq(f.factors[0].factor, x4p1) {
        return false
      }
    None => return false
  }
  // x^6 - 2 is Eisenstein at 2 without a shift.
  let x6m2 = qpoly_sub(qpoly_pow(x, 6), qpoly_int(2))
  match qpoly_irreducibility_certificate(x6m2) {
    Some(CertEisenstein(2, 0)) => ()
    _ => return false
  }
  // x^2 + 1 is irreducible modulo 3.
  let x2p1 = qpoly_add(qpoly_mul(x, x), qpoly_int(1))
  if !qpoly_irreducibility_certificate_check(x2p1, CertModPrime(3)) ||
    qpoly_irreducibility_certificate_check(x2p1, CertModPrime(2)) ||
    qpoly_irreducibility_certificate_check(x2p1, CertModPrime(9)) {
    return false
  }
  // Reducible polynomials get no certificate.
  let reducible = qpoly_mul(
    x2p1,
    qpoly_add(qpoly_mul(x, x), qpoly_add(x, qpoly_int(1))),
  )
  if qpoly_irreducibility_certificate(reducible) != None ||
    qpoly_irreducible_certified(reducible) {
    return false
  }
  // Certified answers agree with the general decision on a
  // spread of examples.
  let examples = [
    x4p1,
    x6m2,
    x2p1,
    qpoly_add(qpoly_add(qpoly_pow(x, 6), x), qpoly_int(1)),
    qpoly_sub(qpoly_pow(x, 3), qpoly_int(2)),
  ]
  for i in 0..<examples.length() {
    if !qpoly_irreducible_certified(examples[i]) ||
      !qpoly_is_irreducible(examples[i]) {
      return false
    }
  }
  true
}

///|
/// Phase 13: joint mod-`p` degree-pattern irreducibility
/// certificates.  The quartic
/// `x^4 - 4x^3 - 3x^2 - x - 4` has usable patterns
/// `[1, 3]` modulo 2 and `[2, 2]` modulo 3: neither prime
/// alone proves irreducibility, but together they exclude
/// factor degrees 1 and 2.  It has no shifted Eisenstein or
/// single-prime certificate in the search bounds, yet factors
/// with a zero Kronecker tuple budget through the new
/// certificate.
pub fn check_qpoly_degree_pattern_certificates() -> Bool {
  let x = qpoly_x()
  let x2 = qpoly_mul(x, x)
  let x3 = qpoly_mul(x2, x)
  let x4 = qpoly_mul(x2, x2)
  let f = qpoly_sub(
    qpoly_sub(
      qpoly_sub(
        qpoly_sub(x4, qpoly_scale(rat_int(4), x3)),
        qpoly_scale(rat_int(3), x2),
      ),
      qpoly_scale(rat_int(1), x),
    ),
    qpoly_int(4),
  )
  let cert = match qpoly_irreducibility_certificate(f) {
    Some(value) => value
    None => return false
  }
  match cert {
    CertModDegreePatterns(primes) => if primes != [2, 3] { return false }
    _ => return false
  }
  if !qpoly_irreducibility_certificate_check(f, cert) ||
    !qpoly_irreducible_certified(f) ||
    !qpoly_is_irreducible(f) {
    return false
  }
  // Neither prime's pattern alone excludes both degrees, a
  // duplicate prime is not a second witness, and an unusable or
  // composite "prime" is rejected.
  if qpoly_irreducibility_certificate_check(f, CertModDegreePatterns([3])) ||
    qpoly_irreducibility_certificate_check(f, CertModDegreePatterns([5])) ||
    qpoly_irreducibility_certificate_check(f, CertModDegreePatterns([3, 3, 5])) ||
    qpoly_irreducibility_certificate_check(f, CertModDegreePatterns([3, 9])) ||
    qpoly_irreducibility_certificate_check(f, CertModPrime(2)) ||
    qpoly_irreducibility_certificate_check(f, CertModPrime(3)) {
    return false
  }
  // The new witness is on the factorization fast path.
  match qpoly_factor_complete_with_budget(f, 0) {
    Some(factorization) =>
      factorization.factors.length() == 1 &&
      qpoly_eq(factorization.factors[0].factor, f)
    None => false
  }
}
