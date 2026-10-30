///|
// Radical denesting beyond the elementary quadratic square-root
// formula.
//
// Three exact mechanisms are combined:
//   * BigInt/rational perfect-power extraction;
//   * the classical norm/resolvent denesting of a cube root in a
//     quadratic field; and
//   * root extraction inside an arbitrary simple algebraic field by
//     factoring `T^n - x` over that field (Trager factorization).
// A small radical-expression simplifier exposes those operations
// syntactically for the principal-real fragment.

///|
fn bigint_pow_int(a : BigInt, e : Int32) -> BigInt {
  let mut out = 1N
  for _i in 0..<e {
    out = out * a
  }
  out
}

///|
/// Floor of the real `k`-th root of a nonnegative BigInt.
pub fn bigint_nth_root_floor(n : BigInt, k : Int32) -> BigInt? {
  if k <= 0 || n < 0N {
    return None
  }
  if k == 1 || n == 0N || n == 1N {
    return Some(n)
  }
  let shift = (n.bit_length() + k - 1) / k + 1
  let mut x = 1N << shift
  let kk = BigInt::from_int(k)
  while true {
    let y = ((kk - 1N) * x + n / bigint_pow_int(x, k - 1)) / kk
    if y >= x {
      break
    }
    x = y
  }
  while bigint_pow_int(x + 1N, k) <= n {
    x = x + 1N
  }
  while bigint_pow_int(x, k) > n {
    x = x - 1N
  }
  Some(x)
}

///|
pub fn bigint_nth_root_exact(n : BigInt, k : Int32) -> BigInt? {
  if k <= 0 {
    return None
  }
  if n < 0N {
    if k % 2 == 0 {
      return None
    }
    return match bigint_nth_root_exact(-n, k) {
      Some(r) => Some(-r)
      None => None
    }
  }
  match bigint_nth_root_floor(n, k) {
    Some(r) => if bigint_pow_int(r, k) == n { Some(r) } else { None }
    None => None
  }
}

///|
pub fn rat_nth_root_exact(r : Rat, k : Int32) -> Rat? {
  match (bigint_nth_root_exact(r.num, k), bigint_nth_root_exact(r.den, k)) {
    (Some(a), Some(b)) => Some(rat_make_big(a, b))
    _ => None
  }
}

///|
/// Denest `cuberoot(a + b√d)` as `u + v√d` in the same quadratic
/// field, when such a denesting exists.  With `c = u² - v²d`, the
/// norm forces `c³ = a² - b²d`, and `u` is a rational root of
/// `4u³ - 3cu - a = 0`.
pub fn quad_denested_cuberoot(x : QuadNum) -> QuadNum? {
  if quad_is_zero(x) {
    return Some(quad_zero())
  }
  if rat_is_zero(x.b) {
    return match rat_nth_root_exact(x.a, 3) {
      Some(r) => Some(quad_rat(r))
      None => None
    }
  }
  let c = match rat_nth_root_exact(quad_norm(x), 3) {
    Some(v) => v
    None => return None
  }
  let resolvent = qpoly_normalize([
    rat_neg(x.a),
    rat_mul(rat_int(-3), c),
    rat_zero(),
    rat_int(4),
  ])
  let us = qpoly_rational_roots(resolvent)
  for ui in 0..<us.length() {
    let u = us[ui]
    let v_squared = rat_div(rat_sub(rat_mul(u, u), c), rat_big_int(x.d))
    match rat_sqrt_if_square(v_squared) {
      Some(v0) => {
        let candidates = [v0, rat_neg(v0)]
        for vi in 0..<candidates.length() {
          let y = quad_make_big(u, candidates[vi], x.d)
          if quad_eq(quad_pow(y, 3), x) {
            return Some(y)
          }
        }
      }
      None => ()
    }
  }
  None
}

///|
/// An `n`-th root of `x` inside the same algebraic field, if one
/// exists there.  This is the general denesting primitive: a nested
/// radical represented in an ambient field is simplified exactly
/// when the required root already lies in that field.
pub fn alg_nth_root_in_field(x : AlgNum, n : Int32) -> AlgNum? {
  if n <= 0 {
    return None
  }
  if n == 1 {
    return Some(x)
  }
  if alg_is_zero(x) {
    return Some(alg_zero(x.modulus))
  }
  let coeffs : Array[AlgNum] = []
  coeffs.push(alg_neg(x))
  for _i in 1..<n {
    coeffs.push(alg_zero(x.modulus))
  }
  coeffs.push(alg_one(x.modulus))
  let factors = algpoly_factor_complete(algpoly_make(x.modulus, coeffs))
  for i in 0..<factors.length() {
    match linear_root(factors[i].factor) {
      Some(root) => if alg_eq(alg_pow(root, n), x) { return Some(root) }
      None => ()
    }
  }
  None
}

///|
pub fn alg_sqrt_in_field(x : AlgNum) -> AlgNum? {
  alg_nth_root_in_field(x, 2)
}

///|
/// Convert an algebraic number of degree at most two to `QuadNum`.
/// For degree two the returned value is the standard generator
/// `(-p + sqrt(p² - 4q))/2` of its minimal polynomial `T²+pT+q`.
pub fn alg_to_quad(x : AlgNum) -> QuadNum? {
  let m = alg_minimal_polynomial(x)
  if qpoly_degree(m) == 0 {
    return Some(quad_zero())
  }
  if qpoly_degree(m) == 1 {
    return Some(
      quad_rat(rat_div(rat_neg(qpoly_coeff(m, 0)), qpoly_coeff(m, 1))),
    )
  }
  if qpoly_degree(m) != 2 {
    return None
  }
  let p = qpoly_coeff(m, 1)
  let q = qpoly_coeff(m, 0)
  let disc = rat_sub(rat_mul(p, p), rat_mul(rat_int(4), q))
  let sqrt_disc = quad_sqrt_rat(disc)
  if rat_is_zero(sqrt_disc.b) {
    return Some(quad_rat(rat_div(rat_add(rat_neg(p), sqrt_disc.a), rat_int(2))))
  }
  Some(
    quad_make_big(
      rat_div(rat_neg(p), rat_int(2)),
      rat_div(sqrt_disc.b, rat_int(2)),
      sqrt_disc.d,
    ),
  )
}

///|
/// An `n`-th root in the same quadratic field, extracted through the
/// general algebraic-field algorithm and converted back.
pub fn quad_nth_root_in_field(x : QuadNum, n : Int32) -> QuadNum? {
  if rat_is_zero(x.b) {
    return match rat_nth_root_exact(x.a, n) {
      Some(r) => Some(quad_rat(r))
      None => None
    }
  }
  let alg_x = alg_of_quad(x)
  match alg_nth_root_in_field(alg_x, n) {
    Some(root) => {
      let coeffs = alg_coeffs(root)
      if coeffs.length() >= 2 {
        Some(quad_make_big(coeffs[0], coeffs[1], x.d))
      } else if coeffs.length() == 1 {
        Some(quad_rat(coeffs[0]))
      } else {
        None
      }
    }
    None => None
  }
}

// ---------------------------------------------------------------------------
// Principal-real radical expressions
// ---------------------------------------------------------------------------

///|
pub enum RadicalExpr {
  RRat(Rat)
  RNeg(RadicalExpr)
  RAdd(RadicalExpr, RadicalExpr)
  RSub(RadicalExpr, RadicalExpr)
  RMul(RadicalExpr, RadicalExpr)
  RDiv(RadicalExpr, RadicalExpr)
  RRoot(Int32, RadicalExpr)
}

///|
pub fn radical_rat(r : Rat) -> RadicalExpr {
  RadicalExpr::RRat(r)
}

///|
pub fn radical_int(n : Int32) -> RadicalExpr {
  RadicalExpr::RRat(rat_int(n))
}

///|
pub fn radical_sqrt(e : RadicalExpr) -> RadicalExpr {
  RadicalExpr::RRoot(2, e)
}

///|
fn quad_to_radical(x : QuadNum) -> RadicalExpr {
  if rat_is_zero(x.b) {
    return RadicalExpr::RRat(x.a)
  }
  let root = RadicalExpr::RRoot(2, RadicalExpr::RRat(rat_big_int(x.d)))
  let term = if rat_is_one(x.b) {
    root
  } else if rat_eq(x.b, rat_int(-1)) {
    RadicalExpr::RNeg(root)
  } else {
    RadicalExpr::RMul(RadicalExpr::RRat(x.b), root)
  }
  if rat_is_zero(x.a) {
    term
  } else {
    RadicalExpr::RAdd(RadicalExpr::RRat(x.a), term)
  }
}

///|
fn radical_to_quad(e : RadicalExpr) -> QuadNum? {
  match e {
    RRat(r) => Some(quad_rat(r))
    RNeg(a) =>
      match radical_to_quad(a) {
        Some(q) => Some(quad_neg(q))
        None => None
      }
    RAdd(a, b) =>
      match (radical_to_quad(a), radical_to_quad(b)) {
        (Some(x), Some(y)) =>
          if quad_compatible(x, y) {
            Some(quad_add(x, y))
          } else {
            None
          }
        _ => None
      }
    RSub(a, b) =>
      match (radical_to_quad(a), radical_to_quad(b)) {
        (Some(x), Some(y)) =>
          if quad_compatible(x, y) {
            Some(quad_sub(x, y))
          } else {
            None
          }
        _ => None
      }
    RMul(a, b) =>
      match (radical_to_quad(a), radical_to_quad(b)) {
        (Some(x), Some(y)) =>
          if quad_compatible(x, y) {
            Some(quad_mul(x, y))
          } else {
            None
          }
        _ => None
      }
    RDiv(a, b) =>
      match (radical_to_quad(a), radical_to_quad(b)) {
        (Some(x), Some(y)) => quad_div(x, y)
        _ => None
      }
    RRoot(2, RRat(r)) => Some(quad_sqrt_rat(r))
    RRoot(3, a) =>
      match radical_to_quad(a) {
        Some(q) => quad_denested_cuberoot(q)
        None => None
      }
    RRoot(_, _) => None
  }
}

///|

///|
/// Phase 11 fallback: evaluate into a biquadratic number and
/// emit its canonical radical form, when possible.
fn radical_via_biquad(e : RadicalExpr) -> RadicalExpr {
  match radical_to_biquad(e) {
    Some(x) => biquad_to_radical(x)
    None => e
  }
}

///|
fn radical_is_nonnegative_rat(e : RadicalExpr) -> Bool {
  match e {
    RRat(r) => rat_cmp_exact(r, rat_zero()) >= 0
    _ => false
  }
}

///|
/// Bottom-up denesting for principal-real radical expressions:
/// exact powers, `root_n(root_m(r)) = root_{nm}(r)` under the sign
/// conditions, quadratic square-root denesting, and quadratic
/// cube-root denesting.
pub fn radical_simplify(e : RadicalExpr) -> RadicalExpr {
  match e {
    RRat(_) => e
    RNeg(a) => {
      let aa = radical_simplify(a)
      match radical_to_quad(RadicalExpr::RNeg(aa)) {
        Some(q) => quad_to_radical(q)
        None => radical_via_biquad(RadicalExpr::RNeg(aa))
      }
    }
    RAdd(a, b) => {
      let out = RadicalExpr::RAdd(radical_simplify(a), radical_simplify(b))
      match radical_to_quad(out) {
        Some(q) => quad_to_radical(q)
        None => radical_via_biquad(out)
      }
    }
    RSub(a, b) => {
      let out = RadicalExpr::RSub(radical_simplify(a), radical_simplify(b))
      match radical_to_quad(out) {
        Some(q) => quad_to_radical(q)
        None => radical_via_biquad(out)
      }
    }
    RMul(a, b) => {
      let out = RadicalExpr::RMul(radical_simplify(a), radical_simplify(b))
      match radical_to_quad(out) {
        Some(q) => quad_to_radical(q)
        None => radical_via_biquad(out)
      }
    }
    RDiv(a, b) => {
      let out = RadicalExpr::RDiv(radical_simplify(a), radical_simplify(b))
      match radical_to_quad(out) {
        Some(q) => quad_to_radical(q)
        None => radical_via_biquad(out)
      }
    }
    RRoot(n, a) => {
      let aa = radical_simplify(a)
      match aa {
        RRat(r) =>
          match rat_nth_root_exact(r, n) {
            Some(root) => return RadicalExpr::RRat(root)
            None => ()
          }
        RRoot(m, RRat(r)) =>
          if rat_cmp_exact(r, rat_zero()) >= 0 || (n % 2 == 1 && m % 2 == 1) {
            return radical_simplify(
              RadicalExpr::RRoot(n * m, RadicalExpr::RRat(r)),
            )
          }
        _ => ()
      }
      match radical_to_quad(aa) {
        Some(q) =>
          if n == 2 {
            match quad_denested_sqrt(q) {
              Some((u, v)) =>
                if quad_is_zero(v) {
                  quad_to_radical(u)
                } else {
                  RadicalExpr::RAdd(quad_to_radical(u), quad_to_radical(v))
                }
              None => RadicalExpr::RRoot(n, aa)
            }
          } else if n == 3 {
            match quad_denested_cuberoot(q) {
              Some(root) => quad_to_radical(root)
              None => RadicalExpr::RRoot(n, aa)
            }
          } else {
            match quad_nth_root_in_field(q, n) {
              Some(root) => quad_to_radical(root)
              None => RadicalExpr::RRoot(n, aa)
            }
          }
        None => radical_via_biquad(RadicalExpr::RRoot(n, aa))
      }
    }
  }
}

///|
fn radical_eq(a : RadicalExpr, b : RadicalExpr) -> Bool {
  match (a, b) {
    (RRat(x), RRat(y)) => rat_eq(x, y)
    (RNeg(x), RNeg(y)) => radical_eq(x, y)
    (RAdd(x1, x2), RAdd(y1, y2)) => radical_eq(x1, y1) && radical_eq(x2, y2)
    (RSub(x1, x2), RSub(y1, y2)) => radical_eq(x1, y1) && radical_eq(x2, y2)
    (RMul(x1, x2), RMul(y1, y2)) => radical_eq(x1, y1) && radical_eq(x2, y2)
    (RDiv(x1, x2), RDiv(y1, y2)) => radical_eq(x1, y1) && radical_eq(x2, y2)
    (RRoot(n, x), RRoot(m, y)) => n == m && radical_eq(x, y)
    _ => false
  }
}

///|
pub fn check_radical_denesting() -> Bool {
  let cube_input = quad_make(rat_int(7), rat_int(5), 2)
  let cube_ok = match quad_denested_cuberoot(cube_input) {
    Some(root) => quad_eq(root, quad_make(rat_one(), rat_one(), 2))
    None => false
  }
  let sqrt_expr = RadicalExpr::RRoot(
    2,
    RadicalExpr::RAdd(
      radical_int(5),
      RadicalExpr::RMul(radical_int(2), radical_sqrt(radical_int(6))),
    ),
  )
  let expected_sqrt = RadicalExpr::RAdd(
    radical_sqrt(radical_int(3)),
    radical_sqrt(radical_int(2)),
  )
  let cube_expr = RadicalExpr::RRoot(
    3,
    RadicalExpr::RAdd(
      radical_int(7),
      RadicalExpr::RMul(radical_int(5), radical_sqrt(radical_int(2))),
    ),
  )
  let nested_exact = RadicalExpr::RRoot(
    2,
    RadicalExpr::RRoot(2, radical_int(81)),
  )
  let x = qpoly_x()
  let biquadratic_modulus = qpoly_add(
    qpoly_sub(qpoly_pow(x, 4), qpoly_scale(rat_int(10), qpoly_mul(x, x))),
    qpoly_int(1),
  )
  let theta = alg_generator(biquadratic_modulus)
  let sqrt6 = alg_scale_rat(
    rat_make(1, 2),
    alg_sub(alg_pow(theta, 2), alg_int(biquadratic_modulus, 5)),
  )
  let nested_value = alg_add(
    alg_int(biquadratic_modulus, 5),
    alg_scale_rat(rat_int(2), sqrt6),
  )
  let alg_root_ok = match alg_sqrt_in_field(nested_value) {
    Some(root) => alg_eq(alg_pow(root, 2), nested_value)
    None => false
  }
  cube_ok &&
  radical_eq(radical_simplify(sqrt_expr), expected_sqrt) &&
  radical_eq(
    radical_simplify(cube_expr),
    RadicalExpr::RAdd(radical_int(1), radical_sqrt(radical_int(2))),
  ) &&
  radical_eq(radical_simplify(nested_exact), radical_int(3)) &&
  alg_root_ok &&
  rat_eq(
    match rat_nth_root_exact(rat_make(-27, 8), 3) {
      Some(r) => r
      None => rat_zero()
    },
    rat_make(-3, 2),
  ) &&
  radical_is_nonnegative_rat(radical_int(4))
}
