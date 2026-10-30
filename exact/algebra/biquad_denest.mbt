///|
/// Biquadratic numbers `Q(√d₁, √d₂)` (and their rational and
/// quadratic degenerations) in the product basis
/// `∏_{i ∈ S} √dᵢ`, `S ⊆ basis`, with `basis` a sorted list of
/// at most two squarefree integers `> 1`.  Arithmetic unifies
/// bases in `Q*/Q*²` and refuses compositums of degree 8; the
/// sign is decided exactly by the quadratic tower; square roots
/// are denested completely for elements of a quadratic subfield
/// (the classical `a² − b²d` square test in `quad_denested_sqrt`)
/// and completely within the element's own biquadratic field
/// (through the primitive-element `AlgNum` representation and
/// `alg_sqrt_in_field`).  A genuinely biquadratic radicand whose
/// root lives only in a different biquadratic or a higher
/// multiquadratic field is not denested.
pub struct BiquadNum {
  basis : Array[BigInt]
  coeffs : Array[Rat]
} derive(Debug, Eq)

///|
pub extend BiquadNum with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend BiquadNum with Eq::{not_equal, equal}

///|
fn biquad_slot_count(basis : Array[BigInt]) -> Int32 {
  1 << basis.length()
}

///|
/// The product-basis element at `mask` as `(h, d)` with
/// `∏_{i ∈ mask} √basis[i] = h·√d`, `d` squarefree.
fn biquad_slot_radical(basis : Array[BigInt], mask : Int32) -> (BigInt, BigInt) {
  let mut prod = 1N
  for i in 0..<basis.length() {
    let bit = (mask >> i) & 1
    if bit == 1 {
      prod = prod * basis[i]
    }
  }
  bigint_squarefree_decomp(prod)
}

///|
fn biquad_sort_basis(basis : Array[BigInt]) -> Array[BigInt] {
  let out : Array[BigInt] = []
  for i in 0..<basis.length() {
    let mut inserted = false
    let rebuilt : Array[BigInt] = []
    for j in 0..<out.length() {
      if !inserted && basis[i] < out[j] {
        rebuilt.push(basis[i])
        inserted = true
      }
      rebuilt.push(out[j])
    }
    if !inserted {
      rebuilt.push(basis[i])
    }
    while out.length() > 0 {
      ignore(out.pop())
    }
    for j in 0..<rebuilt.length() {
      out.push(rebuilt[j])
    }
  }
  out
}

///|
fn biquad_make(basis : Array[BigInt], coeffs : Array[Rat]) -> BiquadNum {
  let sorted = biquad_sort_basis(basis)
  let full : Array[Rat] = []
  for i in 0..<biquad_slot_count(sorted) {
    full.push(if i < coeffs.length() { coeffs[i] } else { rat_zero() })
  }
  BiquadNum::{ basis: sorted, coeffs: full, }
}

///|
pub fn biquad_rat(r : Rat) -> BiquadNum {
  biquad_make([], [r])
}

///|
pub fn biquad_zero() -> BiquadNum {
  biquad_rat(rat_zero())
}

///|
pub fn biquad_of_quad(q : QuadNum) -> BiquadNum {
  if rat_is_zero(q.b) {
    biquad_rat(q.a)
  } else {
    biquad_make([q.d], [q.a, q.b])
  }
}

///|
/// `√r` for a nonnegative rational, in canonical biquadratic
/// form; `None` for negative `r`.
pub fn biquad_sqrt_rat(r : Rat) -> BiquadNum? {
  if rat_sign(r) < 0 {
    return None
  }
  if rat_is_zero(r) {
    return Some(biquad_zero())
  }
  let (scale, d) = bigint_squarefree_decomp(r.num * r.den)
  let coeff = rat_make_big(scale, r.den)
  if d == 1N {
    Some(biquad_rat(coeff))
  } else {
    Some(biquad_make([d], [rat_zero(), coeff]))
  }
}

///|
fn biquad_is_zero(x : BiquadNum) -> Bool {
  for i in 0..<x.coeffs.length() {
    if !rat_is_zero(x.coeffs[i]) {
      return false
    }
  }
  true
}

///|
fn biquad_mul_same(x : BiquadNum, y : BiquadNum) -> BiquadNum {
  let n = biquad_slot_count(x.basis)
  let out : Array[Rat] = []
  for _i in 0..<n {
    out.push(rat_zero())
  }
  for i in 0..<n {
    if rat_is_zero(x.coeffs[i]) {
      continue
    }
    for j in 0..<n {
      if rat_is_zero(y.coeffs[j]) {
        continue
      }
      let mut factor = rat_one()
      let both = i & j
      for k in 0..<x.basis.length() {
        let bit = (both >> k) & 1
        if bit == 1 {
          factor = rat_mul(factor, rat_big_int(x.basis[k]))
        }
      }
      let slot = i ^ j
      out[slot] = rat_add(
        out[slot],
        rat_mul(rat_mul(x.coeffs[i], y.coeffs[j]), factor),
      )
    }
  }
  BiquadNum::{ basis: x.basis, coeffs: out, }
}

///|
/// Express `x` in `new_basis`; `None` when some `√d` of the old
/// basis is not in the new field.
fn biquad_convert(x : BiquadNum, new_basis : Array[BigInt]) -> BiquadNum? {
  let sorted = biquad_sort_basis(new_basis)
  // Image of each old basis root in the new basis.
  let images : Array[BiquadNum] = []
  for i in 0..<x.basis.length() {
    let d = x.basis[i]
    let mut found : BiquadNum? = None
    for mask in 0..<biquad_slot_count(sorted) {
      let (h, dd) = biquad_slot_radical(sorted, mask)
      if dd == d {
        let coeffs : Array[Rat] = []
        for _k in 0..<biquad_slot_count(sorted) {
          coeffs.push(rat_zero())
        }
        coeffs[mask] = rat_make_big(1N, h)
        found = Some(BiquadNum::{ basis: sorted, coeffs, })
        break
      }
    }
    match found {
      Some(img) => images.push(img)
      None => return None
    }
  }
  let acc = biquad_make(sorted, [])
  for mask in 0..<biquad_slot_count(x.basis) {
    let c = x.coeffs[mask]
    if rat_is_zero(c) {
      continue
    }
    let mut term = biquad_make(sorted, [c])
    for i in 0..<x.basis.length() {
      let bit = (mask >> i) & 1
      if bit == 1 {
        term = biquad_mul_same(term, images[i])
      }
    }
    for k in 0..<acc.coeffs.length() {
      acc.coeffs[k] = rat_add(acc.coeffs[k], term.coeffs[k])
    }
  }
  Some(acc)
}

///|
/// A common basis (at most two squarefree generators) spanning
/// both fields, or `None` when the compositum has degree 8.
fn biquad_common_basis(a : Array[BigInt], b : Array[BigInt]) -> Array[BigInt]? {
  let mut basis = biquad_sort_basis(a)
  for i in 0..<b.length() {
    let d = b[i]
    let mut spanned = false
    for mask in 0..<biquad_slot_count(basis) {
      if biquad_slot_radical(basis, mask).1 == d {
        spanned = true
        break
      }
    }
    if !spanned {
      if basis.length() >= 2 {
        return None
      }
      basis = biquad_sort_basis([..basis, d])
    }
  }
  Some(basis)
}

///|
fn biquad_unified(x : BiquadNum, y : BiquadNum) -> (BiquadNum, BiquadNum)? {
  match biquad_common_basis(x.basis, y.basis) {
    Some(basis) =>
      match (biquad_convert(x, basis), biquad_convert(y, basis)) {
        (Some(xx), Some(yy)) => Some((xx, yy))
        _ => None
      }
    None => None
  }
}

///|
pub fn biquad_neg(x : BiquadNum) -> BiquadNum {
  let out : Array[Rat] = []
  for i in 0..<x.coeffs.length() {
    out.push(rat_neg(x.coeffs[i]))
  }
  BiquadNum::{ basis: x.basis, coeffs: out, }
}

///|
pub fn biquad_add(x : BiquadNum, y : BiquadNum) -> BiquadNum? {
  match biquad_unified(x, y) {
    Some((xx, yy)) => {
      let out : Array[Rat] = []
      for i in 0..<xx.coeffs.length() {
        out.push(rat_add(xx.coeffs[i], yy.coeffs[i]))
      }
      Some(BiquadNum::{ basis: xx.basis, coeffs: out, })
    }
    None => None
  }
}

///|
pub fn biquad_sub(x : BiquadNum, y : BiquadNum) -> BiquadNum? {
  biquad_add(x, biquad_neg(y))
}

///|
pub fn biquad_mul(x : BiquadNum, y : BiquadNum) -> BiquadNum? {
  match biquad_unified(x, y) {
    Some((xx, yy)) => Some(biquad_mul_same(xx, yy))
    None => None
  }
}

///|
fn biquad_conjugate_flip(x : BiquadNum, pattern : Int32) -> BiquadNum {
  let out : Array[Rat] = []
  for mask in 0..<x.coeffs.length() {
    let odd = mask & pattern
    let mut bits = 0
    for k in 0..<x.basis.length() {
      bits = bits + ((odd >> k) & 1)
    }
    out.push(
      if bits % 2 == 1 {
        rat_neg(x.coeffs[mask])
      } else {
        x.coeffs[mask]
      },
    )
  }
  BiquadNum::{ basis: x.basis, coeffs: out, }
}

///|
pub fn biquad_inv(x : BiquadNum) -> BiquadNum? {
  if biquad_is_zero(x) {
    return None
  }
  let patterns = biquad_slot_count(x.basis)
  let mut numerator = biquad_make(x.basis, [rat_one()])
  for p in 1..<patterns {
    numerator = biquad_mul_same(numerator, biquad_conjugate_flip(x, p))
  }
  let norm = biquad_mul_same(x, numerator)
  for i in 1..<norm.coeffs.length() {
    if !rat_is_zero(norm.coeffs[i]) {
      return None
    }
  }
  if rat_is_zero(norm.coeffs[0]) {
    return None
  }
  let out : Array[Rat] = []
  for i in 0..<numerator.coeffs.length() {
    out.push(rat_div(numerator.coeffs[i], norm.coeffs[0]))
  }
  Some(BiquadNum::{ basis: x.basis, coeffs: out, })
}

///|
pub fn biquad_div(x : BiquadNum, y : BiquadNum) -> BiquadNum? {
  match biquad_unified(x, y) {
    Some((xx, yy)) =>
      match biquad_inv(yy) {
        Some(inv) => Some(biquad_mul_same(xx, inv))
        None => None
      }
    None => None
  }
}

///|
pub fn biquad_eq(x : BiquadNum, y : BiquadNum) -> Bool {
  match biquad_unified(x, y) {
    Some((xx, yy)) => {
      for i in 0..<xx.coeffs.length() {
        if !rat_eq(xx.coeffs[i], yy.coeffs[i]) {
          return false
        }
      }
      true
    }
    None => false
  }
}

///|
/// Exact sign by the quadratic tower: with `x = u + v·√d` over
/// the sub-basis, opposite signs are resolved by comparing
/// `u²` with `d·v²` one level down.
pub fn biquad_sign(x : BiquadNum) -> Int32 {
  if x.basis.length() == 0 {
    return rat_sign(x.coeffs[0])
  }
  let sub_basis : Array[BigInt] = []
  for i in 0..<(x.basis.length() - 1) {
    sub_basis.push(x.basis[i])
  }
  let half = biquad_slot_count(sub_basis)
  let u_coeffs : Array[Rat] = []
  let v_coeffs : Array[Rat] = []
  for i in 0..<half {
    u_coeffs.push(x.coeffs[i])
    v_coeffs.push(x.coeffs[i + half])
  }
  let u = BiquadNum::{ basis: sub_basis, coeffs: u_coeffs, }
  let v = BiquadNum::{ basis: sub_basis, coeffs: v_coeffs, }
  let su = biquad_sign(u)
  let sv = biquad_sign(v)
  if sv == 0 {
    return su
  }
  if su == 0 || su == sv {
    return sv
  }
  let d = rat_big_int(x.basis[x.basis.length() - 1])
  let u2 = biquad_mul_same(u, u)
  let v2 = biquad_mul_same(v, v)
  let dv2_coeffs : Array[Rat] = []
  for i in 0..<v2.coeffs.length() {
    dv2_coeffs.push(rat_mul(d, v2.coeffs[i]))
  }
  let diff_coeffs : Array[Rat] = []
  for i in 0..<u2.coeffs.length() {
    diff_coeffs.push(rat_sub(u2.coeffs[i], dv2_coeffs[i]))
  }
  let sd = biquad_sign(BiquadNum::{ basis: sub_basis, coeffs: diff_coeffs, })
  if sd > 0 {
    su
  } else if sd < 0 {
    sv
  } else {
    0
  }
}

///|
/// The biquadratic minimal polynomial of `√d₁ + √d₂`:
/// `x⁴ − 2(d₁+d₂)x² + (d₁−d₂)²`.
fn biquad_modulus(d1 : BigInt, d2 : BigInt) -> QPoly {
  let x = qpoly_x()
  let sum = rat_big_int(d1 + d2)
  let diff = d1 - d2
  qpoly_add(
    qpoly_sub(
      qpoly_pow(x, 4),
      qpoly_scale(rat_mul(rat_int(2), sum), qpoly_mul(x, x)),
    ),
    qpoly_const(rat_big_int(diff * diff)),
  )
}

///|
/// Embed into `AlgNum` at the primitive element `s = √d₁ + √d₂`
/// (basis must have exactly two elements).  With `u = √d₁`,
/// `v = √d₂ = s − u`: `u = ((3d₁+d₂)s − s³) / (2(d₁−d₂))`.
fn biquad_to_alg(x : BiquadNum) -> AlgNum {
  let d1 = x.basis[0]
  let d2 = x.basis[1]
  let modulus = biquad_modulus(d1, d2)
  let s = alg_generator(modulus)
  let big_b = rat_big_int(3N * d1 + d2)
  let big_e = rat_big_int(2N * (d1 - d2))
  let u_poly = qpoly_normalize([
    rat_zero(),
    rat_div(big_b, big_e),
    rat_zero(),
    rat_div(rat_int(-1), big_e),
  ])
  let u = alg_make(modulus, u_poly)
  let v = alg_sub(s, u)
  let uv = alg_mul(u, v)
  alg_add(
    alg_add(alg_rat(modulus, x.coeffs[0]), alg_scale_rat(x.coeffs[1], u)),
    alg_add(alg_scale_rat(x.coeffs[2], v), alg_scale_rat(x.coeffs[3], uv)),
  )
}

///|
/// Recover biquadratic coordinates from the power basis at
/// `s = √d₁ + √d₂` by the closed-form inverse of `biquad_to_alg`.
fn biquad_from_alg(x : AlgNum, d1 : BigInt, d2 : BigInt) -> BiquadNum {
  let t = alg_coeffs(x)
  let coeff = (i : Int32) => if i < t.length() { t[i] } else { rat_zero() }
  let big_b = rat_big_int(3N * d1 + d2)
  let big_e = rat_big_int(2N * (d1 - d2))
  let big_d = rat_big_int(d1 + d2)
  let delta = rat_mul(rat_int(2), coeff(2))
  let gamma = rat_add(coeff(1), rat_mul(big_b, coeff(3)))
  let beta = rat_sub(gamma, rat_mul(big_e, coeff(3)))
  let alpha = rat_add(coeff(0), rat_mul(big_d, coeff(2)))
  biquad_make([d1, d2], [alpha, beta, gamma, delta])
}

///|
/// Square root of a biquadratic number, denested as far as the
/// module doc describes; the result is verified by squaring.
pub fn biquad_sqrt(x : BiquadNum) -> BiquadNum? {
  if biquad_sign(x) < 0 {
    return None
  }
  if biquad_is_zero(x) {
    return Some(biquad_zero())
  }
  // Quadratic-subfield elements: at most one nonzero root slot.
  let mut root_mask = 0
  let mut root_slots = 0
  for mask in 1..<x.coeffs.length() {
    if !rat_is_zero(x.coeffs[mask]) {
      root_slots = root_slots + 1
      root_mask = mask
    }
  }
  let candidate = if root_slots <= 1 {
    let quad = if root_slots == 0 {
      quad_rat(x.coeffs[0])
    } else {
      let (h, d) = biquad_slot_radical(x.basis, root_mask)
      quad_make_big(
        x.coeffs[0],
        rat_mul(x.coeffs[root_mask], rat_big_int(h)),
        d,
      )
    }
    match quad_denested_sqrt(quad) {
      Some((u, v)) => biquad_add(biquad_of_quad(u), biquad_of_quad(v))
      None =>
        match quad_nth_root_in_field(quad, 2) {
          Some(root) => Some(biquad_of_quad(root))
          None => None
        }
    }
  } else if x.basis.length() == 2 {
    match alg_sqrt_in_field(biquad_to_alg(x)) {
      Some(root) => {
        let y = biquad_from_alg(root, x.basis[0], x.basis[1])
        Some(if biquad_sign(y) < 0 { biquad_neg(y) } else { y })
      }
      None => None
    }
  } else {
    None
  }
  match candidate {
    Some(y) =>
      match biquad_mul(y, y) {
        Some(y2) => if biquad_eq(y2, x) { Some(y) } else { None }
        None => None
      }
    None => None
  }
}

///|
/// Emit a biquadratic number as a radical expression: rational
/// part first, then `c·√d` terms (one per basis slot).
pub fn biquad_to_radical(x : BiquadNum) -> RadicalExpr {
  let mut out : RadicalExpr? = None
  let push_term = (term : RadicalExpr) => {
    out = match out {
      Some(prev) => Some(RadicalExpr::RAdd(prev, term))
      None => Some(term)
    }
  }
  for mask in 0..<x.coeffs.length() {
    let c = x.coeffs[mask]
    if rat_is_zero(c) {
      continue
    }
    if mask == 0 {
      push_term(RadicalExpr::RRat(c))
    } else {
      let (h, d) = biquad_slot_radical(x.basis, mask)
      let coeff = rat_mul(c, rat_big_int(h))
      let root = RadicalExpr::RRoot(2, RadicalExpr::RRat(rat_big_int(d)))
      if rat_is_one(coeff) {
        push_term(root)
      } else if rat_eq(coeff, rat_int(-1)) {
        push_term(RadicalExpr::RNeg(root))
      } else {
        push_term(RadicalExpr::RMul(RadicalExpr::RRat(coeff), root))
      }
    }
  }
  match out {
    Some(e) => e
    None => RadicalExpr::RRat(rat_zero())
  }
}

///|
/// Evaluate a radical expression into a biquadratic number when
/// possible: rational operations, square roots of rationals, and
/// square roots denested by `biquad_sqrt`.
pub fn radical_to_biquad(e : RadicalExpr) -> BiquadNum? {
  match e {
    RRat(r) => Some(biquad_rat(r))
    RNeg(a) =>
      match radical_to_biquad(a) {
        Some(x) => Some(biquad_neg(x))
        None => None
      }
    RAdd(a, b) =>
      match (radical_to_biquad(a), radical_to_biquad(b)) {
        (Some(x), Some(y)) => biquad_add(x, y)
        _ => None
      }
    RSub(a, b) =>
      match (radical_to_biquad(a), radical_to_biquad(b)) {
        (Some(x), Some(y)) => biquad_sub(x, y)
        _ => None
      }
    RMul(a, b) =>
      match (radical_to_biquad(a), radical_to_biquad(b)) {
        (Some(x), Some(y)) => biquad_mul(x, y)
        _ => None
      }
    RDiv(a, b) =>
      match (radical_to_biquad(a), radical_to_biquad(b)) {
        (Some(x), Some(y)) => biquad_div(x, y)
        _ => None
      }
    RRoot(2, RRat(r)) => biquad_sqrt_rat(r)
    RRoot(2, a) =>
      match radical_to_biquad(a) {
        Some(x) => biquad_sqrt(x)
        None => None
      }
    RRoot(n, RRat(r)) =>
      match rat_nth_root_exact(r, n) {
        Some(root) => Some(biquad_rat(root))
        None => None
      }
    RRoot(_, _) => None
  }
}

///|
/// Exact equality of two radical expressions through the
/// quadratic, biquadratic, triquadratic, multiquadratic (at
/// most four independent quadratic generators), and pure-cubic
/// normal forms; `None` when either side escapes all of them.
pub fn radical_equal_exact(a : RadicalExpr, b : RadicalExpr) -> Bool? {
  match (radical_to_biquad(a), radical_to_biquad(b)) {
    (Some(x), Some(y)) => return Some(biquad_eq(x, y))
    _ => ()
  }
  match (radical_to_triquad(a), radical_to_triquad(b)) {
    (Some(x), Some(y)) =>
      match triquad_align(x, y) {
        Some((u, v)) => return Some(u.coeffs == v.coeffs)
        None => ()
      }
    _ => ()
  }
  match (radical_to_multiquad(a), radical_to_multiquad(b)) {
    (Some(x), Some(y)) =>
      match multiquad_align(x, y) {
        Some((u, v)) => return Some(u.coeffs == v.coeffs)
        None => ()
      }
    _ => ()
  }
  match (radical_to_cubic(a), radical_to_cubic(b)) {
    (Some(x), Some(y)) =>
      match cubic_align(x, y) {
        Some((u, v)) => return Some(cubic_eq(u, v))
        None => ()
      }
    _ => ()
  }
  match (radical_to_quad(a), radical_to_quad(b)) {
    (Some(x), Some(y)) =>
      if quad_compatible(x, y) {
        Some(quad_is_zero(quad_sub(x, y)))
      } else {
        None
      }
    _ => None
  }
}

///|
pub fn check_biquadratic_denesting() -> Bool {
  let sqrt2 = radical_sqrt(radical_int(2))
  let sqrt3 = radical_sqrt(radical_int(3))
  let sqrt5 = radical_sqrt(radical_int(5))
  let sqrt6 = radical_sqrt(radical_int(6))
  // (√3 + √2)(√3 − √2) = 1 through biquadratic arithmetic.
  let product = RadicalExpr::RMul(
    RadicalExpr::RAdd(sqrt3, sqrt2),
    RadicalExpr::RSub(sqrt3, sqrt2),
  )
  if !radical_eq(radical_simplify(product), radical_int(1)) {
    return false
  }
  // (√2 + √3)² = 5 + 2√6.
  let square = RadicalExpr::RMul(
    RadicalExpr::RAdd(sqrt2, sqrt3),
    RadicalExpr::RAdd(sqrt2, sqrt3),
  )
  let five_plus = RadicalExpr::RAdd(
    radical_int(5),
    RadicalExpr::RMul(radical_int(2), sqrt6),
  )
  if !radical_eq(radical_simplify(square), five_plus) {
    return false
  }
  // 1/(√5 + √3) = (√5 − √3)/2.
  let reciprocal = RadicalExpr::RDiv(
    radical_int(1),
    RadicalExpr::RAdd(sqrt5, sqrt3),
  )
  match radical_equal_exact(reciprocal, radical_simplify(reciprocal)) {
    Some(true) => ()
    _ => return false
  }
  match
    radical_equal_exact(
      reciprocal,
      RadicalExpr::RMul(
        RadicalExpr::RRat(rat_make(1, 2)),
        RadicalExpr::RSub(sqrt5, sqrt3),
      ),
    ) {
    Some(true) => ()
    _ => return false
  }
  // √(5 + 2√6) + √(5 − 2√6) = 2√3: each root denests into the
  // biquadratic field and the sum collapses.
  let root_sum = RadicalExpr::RAdd(
    radical_sqrt(five_plus),
    radical_sqrt(
      RadicalExpr::RSub(
        radical_int(5),
        RadicalExpr::RMul(radical_int(2), sqrt6),
      ),
    ),
  )
  if !radical_eq(
      radical_simplify(root_sum),
      RadicalExpr::RMul(radical_int(2), sqrt3),
    ) {
    return false
  }
  // A square root inside its own biquadratic field:
  // √((√2+√3)²) computed through the AlgNum bridge equals √2+√3
  // when the radicand is presented in biquadratic coordinates.
  let theta = match
    biquad_add(
      match biquad_sqrt_rat(rat_int(2)) {
        Some(v) => v
        None => return false
      },
      match biquad_sqrt_rat(rat_int(3)) {
        Some(v) => v
        None => return false
      },
    ) {
    Some(v) => v
    None => return false
  }
  let theta2 = match biquad_mul(theta, theta) {
    Some(v) => v
    None => return false
  }
  // theta^2 = 5 + 2√6 has a single root slot, so use a genuinely
  // biquadratic square: (1 + √2 + √3)^2.
  let phi = match biquad_add(biquad_rat(rat_one()), theta) {
    Some(v) => v
    None => return false
  }
  let phi2 = match biquad_mul(phi, phi) {
    Some(v) => v
    None => return false
  }
  ignore(theta2)
  match biquad_sqrt(phi2) {
    Some(root) => if !biquad_eq(root, phi) { return false }
    None => return false
  }
  // Exact signs in the tower.
  let sign_probe = match
    biquad_sub(
      match biquad_sqrt_rat(rat_int(3)) {
        Some(v) => v
        None => return false
      },
      match biquad_sqrt_rat(rat_int(2)) {
        Some(v) => v
        None => return false
      },
    ) {
    Some(v) => v
    None => return false
  }
  if biquad_sign(sign_probe) != 1 || biquad_sign(biquad_neg(sign_probe)) != -1 {
    return false
  }
  // √2 + √3 ≠ √5 exactly, and √2·√3 = √6.
  match radical_equal_exact(RadicalExpr::RAdd(sqrt2, sqrt3), sqrt5) {
    Some(false) => ()
    _ => return false
  }
  radical_eq(radical_simplify(RadicalExpr::RMul(sqrt2, sqrt3)), sqrt6)
}
