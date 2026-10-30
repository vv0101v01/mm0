///|
// Exact root isolation.
//
// Real roots are counted and separated by Sturm sequences on each
// squarefree Yun factor, retaining the original multiplicity.
// Complex roots first use floating Durand-Kerner only as a search
// oracle: candidate centres are refined by exact Newton iteration in
// Q(i), and a disk is emitted only after a rational Rouche certificate
// proves that it contains exactly one root of the squarefree factor.
// If that fast search finds fewer disks than the degree, a complete
// exact subdivision search over the Cauchy square takes over.  It
// subdivides squares, discards a square only by a Taylor exclusion
// test on an enclosing disk (or because it is already inside a
// certified one-root disk), and accepts only pairwise disjoint Rouche
// disks.  For a squarefree factor it stops exactly when the number of
// certified disks equals the degree, so completeness does not depend
// on the floating oracle.

///|
pub struct RealRootIsolation {
  polynomial : QPoly
  lower : Rat
  upper : Rat
  multiplicity : Int32
}

///|
pub struct ComplexDisk {
  re : Rat
  im : Rat
  radius : Rat
}

///|
pub struct ComplexRootIsolation {
  polynomial : QPoly
  disk : ComplexDisk
  multiplicity : Int32
}

///|
fn rat_pow2_neg(bits : Int32) -> Rat {
  if bits <= 0 {
    rat_one()
  } else {
    rat_make_big(1N, 1N << bits)
  }
}

///|
fn normalize_positive_scale(p : QPoly) -> QPoly {
  if qpoly_is_zero(p) {
    p
  } else {
    qpoly_scale(rat_inv(rat_abs_exact(qpoly_leading(p))), p)
  }
}

///|
/// A Sturm sequence for a squarefree polynomial.  Positive scalar
/// normalization controls coefficient growth without changing signs.
pub fn qpoly_sturm_sequence(p0 : QPoly) -> Array[QPoly] {
  let p = qpoly_squarefree_part(p0)
  let seq : Array[QPoly] = []
  if qpoly_degree(p) <= 0 {
    return seq
  }
  seq.push(normalize_positive_scale(p))
  seq.push(normalize_positive_scale(qpoly_derivative(p)))
  while true {
    let n = seq.length()
    let rem = qpoly_mod(seq[n - 2], seq[n - 1])
    if qpoly_is_zero(rem) {
      break
    }
    seq.push(normalize_positive_scale(qpoly_scale(rat_int(-1), rem)))
  }
  seq
}

///|
pub fn qpoly_sturm_variations(seq : Array[QPoly], x : Rat) -> Int32 {
  let mut previous = 0
  let mut variations = 0
  for i in 0..<seq.length() {
    let sign = rat_sign(qpoly_eval(seq[i], x))
    if sign != 0 {
      if previous != 0 && sign != previous {
        variations = variations + 1
      }
      previous = sign
    }
  }
  variations
}

///|
/// Number of distinct real roots in `(lower, upper]`, by Sturm's
/// theorem applied to the squarefree part.
pub fn qpoly_real_root_count(p : QPoly, lower : Rat, upper : Rat) -> Int32 {
  let seq = qpoly_sturm_sequence(p)
  qpoly_sturm_variations(seq, lower) - qpoly_sturm_variations(seq, upper)
}

///|
fn qpoly_cauchy_bound(p : QPoly) -> Rat {
  let f = qpoly_monic(p)
  let mut maximum = rat_zero()
  for i in 0..<f.coeffs.length() {
    let a = rat_abs_exact(f.coeffs[i])
    if rat_cmp_exact(a, maximum) > 0 {
      maximum = a
    }
  }
  let target = rat_add(rat_one(), maximum)
  let mut bound = rat_one()
  while rat_cmp_exact(bound, target) < 0 {
    bound = rat_add(bound, bound)
  }
  bound
}

///|
fn isolate_squarefree_real(
  f0 : QPoly,
  multiplicity : Int32,
  width : Rat,
  out : Array[RealRootIsolation],
) -> Unit {
  // Remove rational roots first.  Every subsequent bisection point is
  // rational, so the residual search can never land exactly on a root
  // and chase it as an interval endpoint forever.
  let rational = qpoly_factor_rational_roots(f0)
  for i in 0..<rational.roots.length() {
    let r = rational.roots[i]
    out.push(RealRootIsolation::{
      polynomial: f0,
      lower: r,
      upper: r,
      multiplicity,
    })
  }
  let f = rational.residual
  if qpoly_degree(f) <= 0 {
    return
  }
  let seq = qpoly_sturm_sequence(f)
  let bound = qpoly_cauchy_bound(f)
  fn go(lower : Rat, upper : Rat) -> Unit {
    let count = qpoly_sturm_variations(seq, lower) -
      qpoly_sturm_variations(seq, upper)
    if count <= 0 {
      return
    }
    if count == 1 && rat_cmp_exact(rat_sub(upper, lower), width) <= 0 {
      out.push(RealRootIsolation::{
        polynomial: f0,
        lower,
        upper,
        multiplicity,
      })
      return
    }
    let mid = rat_div(rat_add(lower, upper), rat_int(2))
    go(lower, mid)
    go(mid, upper)
  }

  go(rat_neg(bound), bound)
}

///|
/// Isolate every distinct real root.  Non-point intervals have width
/// at most `2^-width_bits`, endpoints are not roots, and the stored
/// multiplicity is the multiplicity in the original polynomial.
pub fn qpoly_isolate_real_roots(
  p : QPoly,
  width_bits : Int32,
) -> Array[RealRootIsolation] {
  let out : Array[RealRootIsolation] = []
  if qpoly_degree(p) <= 0 {
    return out
  }
  let groups = qpoly_squarefree_factorization(p)
  let width = rat_pow2_neg(if width_bits < 0 { 0 } else { width_bits })
  for i in 0..<groups.length() {
    isolate_squarefree_real(
      groups[i].factor,
      groups[i].multiplicity,
      width,
      out,
    )
  }
  // Different Yun groups are coprime but their roots interleave.
  for _pass in 0..<out.length() {
    for j in 0..<(out.length() - 1) {
      if rat_cmp_exact(out[j + 1].lower, out[j].lower) < 0 {
        let tmp = out[j]
        out[j] = out[j + 1]
        out[j + 1] = tmp
      }
    }
  }
  out
}

///|
/// Refine an isolating interval by exact bisection.
pub fn real_root_isolation_refine(
  root : RealRootIsolation,
  width_bits : Int32,
) -> RealRootIsolation {
  if rat_eq(root.lower, root.upper) {
    return root
  }
  let width = rat_pow2_neg(if width_bits < 0 { 0 } else { width_bits })
  let mut lower = root.lower
  let mut upper = root.upper
  let lower_sign = rat_sign(qpoly_eval(root.polynomial, lower))
  while rat_cmp_exact(rat_sub(upper, lower), width) > 0 {
    let mid = rat_div(rat_add(lower, upper), rat_int(2))
    let value = qpoly_eval(root.polynomial, mid)
    if rat_is_zero(value) {
      return RealRootIsolation::{
        polynomial: root.polynomial,
        lower: mid,
        upper: mid,
        multiplicity: root.multiplicity,
      }
    }
    if rat_sign(value) == lower_sign {
      lower = mid
    } else {
      upper = mid
    }
  }
  RealRootIsolation::{
    polynomial: root.polynomial,
    lower,
    upper,
    multiplicity: root.multiplicity,
  }
}

///|
/// Verify sorted, disjoint, sign-changing (or exact point) real root
/// isolations, with multiplicities summing to the independently
/// Sturm-counted number of real roots of the original polynomial.
pub fn real_root_isolations_are_certified(
  p : QPoly,
  roots : Array[RealRootIsolation],
) -> Bool {
  let bound = qpoly_cauchy_bound(qpoly_squarefree_part(p))
  if roots.length() != qpoly_real_root_count(p, rat_neg(bound), bound) {
    return false
  }
  for i in 0..<roots.length() {
    let r = roots[i]
    if r.multiplicity <= 0 || rat_cmp_exact(r.upper, r.lower) < 0 {
      return false
    }
    if i > 0 && rat_cmp_exact(roots[i - 1].upper, r.lower) >= 0 {
      return false
    }
    if rat_eq(r.lower, r.upper) {
      if !rat_is_zero(qpoly_eval(p, r.lower)) {
        return false
      }
    } else {
      if qpoly_real_root_count(r.polynomial, r.lower, r.upper) != 1 {
        return false
      }
      let ls = rat_sign(qpoly_eval(r.polynomial, r.lower))
      let us = rat_sign(qpoly_eval(r.polynomial, r.upper))
      if ls == 0 || us == 0 || ls == us {
        return false
      }
    }
    if qpoly_root_multiplicity_via_squarefree(p, r) != r.multiplicity {
      return false
    }
  }
  true
}

///|
fn qpoly_root_multiplicity_via_squarefree(
  p : QPoly,
  root : RealRootIsolation,
) -> Int32 {
  let groups = qpoly_squarefree_factorization(p)
  for i in 0..<groups.length() {
    if qpoly_eq(groups[i].factor, root.polynomial) {
      return groups[i].multiplicity
    }
  }
  0
}

// ---------------------------------------------------------------------------
// Certified complex disks
// ---------------------------------------------------------------------------

///|
priv struct CRat {
  re : Rat
  im : Rat
}

///|
fn crat_add(a : CRat, b : CRat) -> CRat {
  CRat::{ re: rat_add(a.re, b.re), im: rat_add(a.im, b.im), }
}

///|
fn crat_sub(a : CRat, b : CRat) -> CRat {
  CRat::{ re: rat_sub(a.re, b.re), im: rat_sub(a.im, b.im), }
}

///|
fn crat_mul(a : CRat, b : CRat) -> CRat {
  CRat::{
    re: rat_sub(rat_mul(a.re, b.re), rat_mul(a.im, b.im)),
    im: rat_add(rat_mul(a.re, b.im), rat_mul(a.im, b.re)),
  }
}

///|
fn crat_div(a : CRat, b : CRat) -> CRat? {
  let den = rat_add(rat_mul(b.re, b.re), rat_mul(b.im, b.im))
  if rat_is_zero(den) {
    return None
  }
  Some(CRat::{
    re: rat_div(rat_add(rat_mul(a.re, b.re), rat_mul(a.im, b.im)), den),
    im: rat_div(rat_sub(rat_mul(a.im, b.re), rat_mul(a.re, b.im)), den),
  })
}

///|
fn qpoly_eval_complex(p : QPoly, z : CRat) -> CRat {
  let mut acc = CRat::{ re: rat_zero(), im: rat_zero(), }
  for i = p.coeffs.length() - 1; i >= 0; i = i - 1 {
    acc = crat_add(crat_mul(acc, z), CRat::{ re: p.coeffs[i], im: rat_zero(), })
  }
  acc
}

///|
fn rat_sqrt_bounds(x : Rat, bits : Int32) -> (Rat, Rat) {
  if rat_cmp_exact(x, rat_zero()) <= 0 {
    return (rat_zero(), rat_zero())
  }
  let scale = 1N << bits
  // floor(sqrt(x)*2^bits), with one extra output unit for the ceiling.
  let scaled_num = x.num * scale * scale
  let q = scaled_num / x.den
  let r = match bigint_sqrt_floor(q) {
    Some(value) => value
    None => 0N
  }
  (rat_make_big(r, scale), rat_make_big(r + 1N, scale))
}

///|
fn crat_abs_upper(z : CRat) -> Rat {
  let (_, hi) = rat_sqrt_bounds(
    rat_add(rat_mul(z.re, z.re), rat_mul(z.im, z.im)),
    80,
  )
  hi
}

///|
fn crat_abs_lower(z : CRat) -> Rat {
  let (lo, _) = rat_sqrt_bounds(
    rat_add(rat_mul(z.re, z.re), rat_mul(z.im, z.im)),
    80,
  )
  lo
}

///|
fn complex_disk_rouche_ok(f : QPoly, disk : ComplexDisk) -> Bool {
  if rat_cmp_exact(disk.radius, rat_zero()) < 0 {
    return false
  }
  let z = CRat::{ re: disk.re, im: disk.im, }
  if rat_is_zero(disk.radius) {
    let value = qpoly_eval_complex(f, z)
    return rat_is_zero(value.re) && rat_is_zero(value.im)
  }
  let fz = qpoly_eval_complex(f, z)
  let dfz = qpoly_eval_complex(qpoly_derivative(f), z)
  let linear_lower = rat_mul(crat_abs_lower(dfz), disk.radius)
  let mut remainder_upper = crat_abs_upper(fz)
  let mut derivative = qpoly_derivative(qpoly_derivative(f))
  let mut factorial = rat_int(2)
  let mut power = rat_mul(disk.radius, disk.radius)
  let mut order = 2
  while qpoly_degree(derivative) >= 0 && !qpoly_is_zero(derivative) {
    let coefficient = qpoly_eval_complex(
      qpoly_scale(rat_inv(factorial), derivative),
      z,
    )
    remainder_upper = rat_add(
      remainder_upper,
      rat_mul(crat_abs_upper(coefficient), power),
    )
    derivative = qpoly_derivative(derivative)
    order = order + 1
    factorial = rat_mul(factorial, rat_int(order))
    power = rat_mul(power, disk.radius)
    if order > qpoly_degree(f) {
      break
    }
  }
  rat_cmp_exact(remainder_upper, linear_lower) < 0
}

///|
/// Magnitude bounds for the Taylor expansion of a polynomial at one
/// rational complex centre.  `higher[k]` bounds the coefficient of
/// `(z-z0)^(k+2)`.  Keeping these bounds with the centre lets one
/// Taylor evaluation serve the exclusion test and many Rouche radius
/// trials during subdivision.
priv struct ComplexTaylorBounds {
  value : CRat
  constant_lower : Rat
  constant_upper : Rat
  linear_lower : Rat
  linear_upper : Rat
  higher : Array[Rat]
}

///|
fn complex_taylor_bounds(f : QPoly, z : CRat) -> ComplexTaylorBounds {
  let fz = qpoly_eval_complex(f, z)
  let dfz = qpoly_eval_complex(qpoly_derivative(f), z)
  let higher : Array[Rat] = []
  let mut derivative = qpoly_derivative(qpoly_derivative(f))
  let mut factorial = rat_int(2)
  let mut order = 2
  while qpoly_degree(derivative) >= 0 && !qpoly_is_zero(derivative) {
    let coefficient = qpoly_eval_complex(
      qpoly_scale(rat_inv(factorial), derivative),
      z,
    )
    higher.push(crat_abs_upper(coefficient))
    derivative = qpoly_derivative(derivative)
    order = order + 1
    factorial = rat_mul(factorial, rat_int(order))
    if order > qpoly_degree(f) {
      break
    }
  }
  ComplexTaylorBounds::{
    value: fz,
    constant_lower: crat_abs_lower(fz),
    constant_upper: crat_abs_upper(fz),
    linear_lower: crat_abs_lower(dfz),
    linear_upper: crat_abs_upper(dfz),
    higher,
  }
}

///|
fn complex_taylor_rouche_ok(bounds : ComplexTaylorBounds, radius : Rat) -> Bool {
  if rat_is_zero(radius) {
    return rat_is_zero(bounds.value.re) && rat_is_zero(bounds.value.im)
  }
  let mut remainder_upper = bounds.constant_upper
  let mut power = rat_mul(radius, radius)
  for i in 0..<bounds.higher.length() {
    remainder_upper = rat_add(remainder_upper, rat_mul(bounds.higher[i], power))
    power = rat_mul(power, radius)
  }
  rat_cmp_exact(remainder_upper, rat_mul(bounds.linear_lower, radius)) < 0
}

///|
/// Exclusion test: the constant Taylor term dominates every possible
/// variation on the disk, so the disk contains no root.
fn complex_taylor_exclusion_ok(
  bounds : ComplexTaylorBounds,
  radius : Rat,
) -> Bool {
  if rat_is_zero(radius) {
    return !(rat_is_zero(bounds.value.re) && rat_is_zero(bounds.value.im))
  }
  let mut variation_upper = rat_mul(bounds.linear_upper, radius)
  let mut power = rat_mul(radius, radius)
  for i in 0..<bounds.higher.length() {
    variation_upper = rat_add(variation_upper, rat_mul(bounds.higher[i], power))
    power = rat_mul(power, radius)
  }
  rat_cmp_exact(variation_upper, bounds.constant_lower) < 0
}

///|
fn complex_disk_contains_point_strict(disk : ComplexDisk, z : CRat) -> Bool {
  if rat_is_zero(disk.radius) {
    return false
  }
  let dz = CRat::{ re: rat_sub(z.re, disk.re), im: rat_sub(z.im, disk.im), }
  rat_cmp_exact(crat_abs_upper(dz), disk.radius) < 0
}

///|
/// Add a certified disk if it is disjoint from all previously chosen
/// disks.  One special case is useful in subdivision: a positive
/// disk that strictly contains an earlier exact (zero-radius) disk
/// may replace it; both contain the same unique certified root.
fn try_add_complex_disk(
  chosen : Array[ComplexDisk],
  disk : ComplexDisk,
) -> Bool {
  let mut replace_index = -1
  for j in 0..<chosen.length() {
    let old = chosen[j]
    if rat_eq(old.re, disk.re) &&
      rat_eq(old.im, disk.im) &&
      rat_eq(old.radius, disk.radius) {
      return false
    }
    if !disks_disjoint(disk, old) {
      let old_point = CRat::{ re: old.re, im: old.im, }
      let can_replace = replace_index < 0 &&
        rat_is_zero(old.radius) &&
        complex_disk_contains_point_strict(disk, old_point)
      if can_replace {
        replace_index = j
      } else {
        return false
      }
    }
  }
  if replace_index >= 0 {
    chosen[replace_index] = disk
  } else {
    chosen.push(disk)
  }
  true
}

///|
priv struct ComplexBox {
  re : Rat
  im : Rat
  half : Rat
}

///|
/// Conservative square-in-disk test.  The farthest corner is at most
/// `sqrt(2) * half < 3*half/2` from the square centre.
fn complex_box_inside_disk(box : ComplexBox, disk : ComplexDisk) -> Bool {
  if rat_is_zero(disk.radius) {
    return false
  }
  let dz = CRat::{ re: rat_sub(box.re, disk.re), im: rat_sub(box.im, disk.im), }
  let outer = rat_add(crat_abs_upper(dz), rat_mul(rat_make(3, 2), box.half))
  rat_cmp_exact(outer, disk.radius) < 0
}

///|
fn complex_box_inside_any_disk(
  box : ComplexBox,
  disks : Array[ComplexDisk],
) -> Bool {
  for i in 0..<disks.length() {
    if complex_box_inside_disk(box, disks[i]) {
      return true
    }
  }
  false
}

///|
/// Complete the isolation of one squarefree factor by exact square
/// subdivision.  `chosen` may already contain certified disjoint
/// disks (for example from the Durand-Kerner oracle); they are used
/// for pruning and retained.
///
/// Termination is the usual subdivision argument for a squarefree
/// polynomial: boxes shrinking to a non-root are eventually excluded
/// because the constant Taylor term has a positive limit while the
/// variation is O(half-width); boxes shrinking to a simple root
/// eventually pass a Rouche test at a radius comparable to their
/// half-width.  If such a disk overlaps an earlier disk for another
/// root it is rejected and subdivision continues, so successful
/// radii tend to zero around distinct roots and eventually become
/// disjoint.  The loop therefore has no arbitrary completeness cap:
/// it returns only after certifying `degree(f)` disjoint disks.
fn complex_subdivision_complete(f : QPoly, chosen : Array[ComplexDisk]) -> Unit {
  let degree = qpoly_degree(f)
  if degree <= 0 || chosen.length() >= degree {
    return
  }
  let bound = qpoly_cauchy_bound(f)
  let stack : Array[ComplexBox] = [
    ComplexBox::{ re: rat_zero(), im: rat_zero(), half: bound, },
  ]
  let radius_factors = [
    rat_make(1, 8),
    rat_make(1, 4),
    rat_make(1, 2),
    rat_one(),
    rat_make(3, 2),
    rat_int(2),
    rat_int(3),
    rat_int(4),
  ]
  while stack.length() > 0 && chosen.length() < degree {
    let box = stack[stack.length() - 1]
    ignore(stack.pop())
    if complex_box_inside_any_disk(box, chosen) {
      continue
    }
    let centre = CRat::{ re: box.re, im: box.im, }
    let bounds = complex_taylor_bounds(f, centre)
    // This disk certainly contains the closed square: its radius is
    // 3*half/2, whereas a corner is sqrt(2)*half from the centre.
    let enclosing_radius = rat_mul(rat_make(3, 2), box.half)
    if complex_taylor_exclusion_ok(bounds, enclosing_radius) {
      continue
    }
    let mut added_disk = false
    for i in 0..<radius_factors.length() {
      let radius = rat_mul(box.half, radius_factors[i])
      if complex_taylor_rouche_ok(bounds, radius) {
        let disk = ComplexDisk::{ re: box.re, im: box.im, radius, }
        // Re-run the standalone certificate before acceptance; the
        // Taylor-bound test above is the search filter, this is the
        // same certificate used by the public verifier.
        if complex_disk_rouche_ok(f, disk) && try_add_complex_disk(chosen, disk) {
          added_disk = true
          break
        }
      }
    }
    if chosen.length() >= degree {
      break
    }
    // An exact dyadic centre can occur for Gaussian-rational roots.
    // Prefer the positive Rouche disk just attempted, but retain an
    // exact point disk as a fallback; a later positive disk around
    // the same root replaces it in `try_add_complex_disk`.
    if !added_disk &&
      rat_is_zero(bounds.value.re) &&
      rat_is_zero(bounds.value.im) {
      let exact = ComplexDisk::{ re: box.re, im: box.im, radius: rat_zero(), }
      ignore(try_add_complex_disk(chosen, exact))
      if chosen.length() >= degree {
        break
      }
    }
    // Even after adding a disk, this square has to be subdivided
    // unless it is wholly inside a certified disk: in the latter
    // case the disk's unique root is the only root it can contain.
    if complex_box_inside_any_disk(box, chosen) {
      continue
    }
    let child_half = rat_div(box.half, rat_int(2))
    for sx in 0..<2 {
      for sy in 0..<2 {
        let dx = if sx == 0 { rat_neg(child_half) } else { child_half }
        let dy = if sy == 0 { rat_neg(child_half) } else { child_half }
        stack.push(ComplexBox::{
          re: rat_add(box.re, dx),
          im: rat_add(box.im, dy),
          half: child_half,
        })
      }
    }
  }
}

///|
fn bigint_from_integer_double(x0 : Double) -> BigInt {
  if x0 == 0.0 || x0.is_nan() || x0.is_inf() {
    return 0N
  }
  let negative = x0 < 0.0
  let mut x = x0.abs().floor()
  let chunks : Array[Int32] = []
  while x >= 1.0 {
    chunks.push((x % 1073741824.0).to_int())
    x = (x / 1073741824.0).floor()
  }
  let mut out = 0N
  for i = chunks.length() - 1; i >= 0; i = i - 1 {
    out = out * 1073741824N + BigInt::from_int(chunks[i])
  }
  if negative {
    -out
  } else {
    out
  }
}

///|
fn rat_from_double_dyadic(x : Double, bits : Int32) -> Rat? {
  if x.is_nan() || x.is_inf() || bits < 0 || bits > 160 {
    return None
  }
  let mut scale = 1.0
  for _i in 0..<bits {
    scale = scale * 2.0
  }
  let scaled = (x * scale).floor()
  if scaled.is_nan() || scaled.is_inf() {
    return None
  }
  Some(rat_make_big(bigint_from_integer_double(scaled), 1N << bits))
}

///|
fn crat_round_pow2(z : CRat, bits : Int32) -> CRat {
  CRat::{
    re: rat_round_down_pow2(z.re, bits),
    im: rat_round_down_pow2(z.im, bits),
  }
}

///|
fn complex_newton_refine(f : QPoly, z0 : CRat) -> CRat {
  let df = qpoly_derivative(f)
  let mut z = z0
  for _i in 0..<8 {
    match crat_div(qpoly_eval_complex(f, z), qpoly_eval_complex(df, z)) {
      Some(step) => z = crat_round_pow2(crat_sub(z, step), 42)
      None => break
    }
  }
  z
}

///|
fn durand_kerner_candidates(f : QPoly) -> Array[CRat] {
  let n = qpoly_degree(f)
  let out : Array[CRat] = []
  if n <= 0 {
    return out
  }
  if n == 1 {
    let root = rat_div(rat_neg(qpoly_coeff(f, 0)), qpoly_coeff(f, 1))
    out.push(CRat::{ re: root, im: rat_zero(), })
    return out
  }
  let monic = qpoly_monic(f)
  let coeffs : Array[Double] = []
  for i in 0..<(n + 1) {
    coeffs.push(rat_to_double(qpoly_coeff(monic, i)))
  }
  let bound = rat_to_double(qpoly_cauchy_bound(monic))
  if bound.is_nan() || bound.is_inf() || bound <= 0.0 {
    return out
  }
  let res : Array[Double] = []
  let ims : Array[Double] = []
  for i in 0..<n {
    let angle = 6.283185307179586 * i.to_double() / n.to_double() + 0.37
    res.push(bound * @math.cos(angle))
    ims.push(bound * @math.sin(angle))
  }
  for _iteration in 0..<500 {
    let next_re : Array[Double] = []
    let next_im : Array[Double] = []
    let mut max_step = 0.0
    for i in 0..<n {
      // f(z_i)
      let mut fr = 0.0
      let mut fi = 0.0
      for k = n; k >= 0; k = k - 1 {
        let nr = fr * res[i] - fi * ims[i] + coeffs[k]
        let ni = fr * ims[i] + fi * res[i]
        fr = nr
        fi = ni
      }
      // prod_{j != i}(z_i-z_j)
      let mut pr = 1.0
      let mut pi = 0.0
      for j in 0..<n {
        if j != i {
          let dr = res[i] - res[j]
          let di = ims[i] - ims[j]
          let nr = pr * dr - pi * di
          let ni = pr * di + pi * dr
          pr = nr
          pi = ni
        }
      }
      let den = pr * pr + pi * pi
      if den == 0.0 || den.is_nan() || den.is_inf() {
        next_re.push(res[i])
        next_im.push(ims[i])
      } else {
        let sr = (fr * pr + fi * pi) / den
        let si = (fi * pr - fr * pi) / den
        next_re.push(res[i] - sr)
        next_im.push(ims[i] - si)
        let step = (sr * sr + si * si).sqrt()
        if step > max_step {
          max_step = step
        }
      }
    }
    for i in 0..<n {
      res[i] = next_re[i]
      ims[i] = next_im[i]
    }
    if max_step < 1.0e-13 {
      break
    }
  }
  for i in 0..<n {
    match
      (rat_from_double_dyadic(res[i], 30), rat_from_double_dyadic(ims[i], 30)) {
      (Some(re), Some(im)) =>
        out.push(complex_newton_refine(f, CRat::{ re, im, }))
      _ => ()
    }
  }
  out
}

///|
fn disks_disjoint(a : ComplexDisk, b : ComplexDisk) -> Bool {
  let dz = CRat::{ re: rat_sub(a.re, b.re), im: rat_sub(a.im, b.im), }
  rat_cmp_exact(crat_abs_lower(dz), rat_add(a.radius, b.radius)) > 0
}

///|
fn isolate_squarefree_complex(
  f : QPoly,
  multiplicity : Int32,
  out : Array[ComplexRootIsolation],
) -> Unit {
  let candidates = durand_kerner_candidates(f)
  // Sort candidates by (re, im).
  for _pass in 0..<candidates.length() {
    for j in 0..<(candidates.length() - 1) {
      let a = candidates[j]
      let b = candidates[j + 1]
      if rat_cmp_exact(b.re, a.re) < 0 ||
        (rat_eq(b.re, a.re) && rat_cmp_exact(b.im, a.im) < 0) {
        candidates[j] = b
        candidates[j + 1] = a
      }
    }
  }
  let chosen : Array[ComplexDisk] = []
  for i in 0..<candidates.length() {
    let z = candidates[i]
    let exact_value = qpoly_eval_complex(f, z)
    if rat_is_zero(exact_value.re) && rat_is_zero(exact_value.im) {
      let disk = ComplexDisk::{ re: z.re, im: z.im, radius: rat_zero(), }
      let mut overlaps = false
      for j in 0..<chosen.length() {
        if !disks_disjoint(disk, chosen[j]) {
          overlaps = true
        }
      }
      if !overlaps {
        chosen.push(disk)
      }
      continue
    }
    let scale = rat_add(rat_one(), crat_abs_upper(z))
    let mut found : ComplexDisk? = None
    // Ascending dyadic radii.
    for exponent = 80; exponent >= -12; exponent = exponent - 1 {
      let radius = if exponent >= 0 {
        rat_mul(scale, rat_pow2_neg(exponent))
      } else {
        rat_mul(scale, rat_big_int(1N << (0 - exponent)))
      }
      let disk = ComplexDisk::{ re: z.re, im: z.im, radius, }
      if complex_disk_rouche_ok(f, disk) {
        let mut overlaps = false
        for j in 0..<chosen.length() {
          if !disks_disjoint(disk, chosen[j]) {
            overlaps = true
          }
        }
        if !overlaps {
          found = Some(disk)
          break
        }
      }
    }
    match found {
      Some(disk) => chosen.push(disk)
      None => ()
    }
  }
  if chosen.length() < qpoly_degree(f) {
    complex_subdivision_complete(f, chosen)
  }
  // Keep the emitted order deterministic even when the subdivision
  // fallback found some disks after the floating oracle.
  for _pass in 0..<chosen.length() {
    for j in 0..<(chosen.length() - 1) {
      let a = chosen[j]
      let b = chosen[j + 1]
      if rat_cmp_exact(b.re, a.re) < 0 ||
        (rat_eq(b.re, a.re) && rat_cmp_exact(b.im, a.im) < 0) {
        chosen[j] = b
        chosen[j + 1] = a
      }
    }
  }
  for i in 0..<chosen.length() {
    out.push(ComplexRootIsolation::{
      polynomial: f,
      disk: chosen[i],
      multiplicity,
    })
  }
}

///|
/// Isolate all complex roots of a nonzero polynomial.  Each Yun
/// squarefree factor first goes through the fast floating search;
/// if it produces fewer certified disks than the factor degree, the
/// complete exact subdivision search described at the top of this
/// file fills the gap.  Use
/// `complex_root_isolations_are_certified` to independently verify
/// disjointness, every Rouche certificate, and the total degree
/// count.  Completeness is therefore a theorem of the search, not
/// an assumption about the floating oracle.  As with other exact
/// root-isolation algorithms, extremely clustered roots can make
/// the subdivision stage expensive.
pub fn qpoly_isolate_complex_roots(p : QPoly) -> Array[ComplexRootIsolation] {
  let out : Array[ComplexRootIsolation] = []
  if qpoly_degree(p) <= 0 {
    return out
  }
  let groups = qpoly_squarefree_factorization(p)
  for i in 0..<groups.length() {
    isolate_squarefree_complex(groups[i].factor, groups[i].multiplicity, out)
  }
  out
}

///|
/// Full complex-isolation certificate: pairwise disjoint Rouche
/// disks, one root in each disk of its squarefree factor, and total
/// multiplicity equal to the degree of `p`.
pub fn complex_root_isolations_are_certified(
  p : QPoly,
  roots : Array[ComplexRootIsolation],
) -> Bool {
  let mut total = 0
  for i in 0..<roots.length() {
    if roots[i].multiplicity <= 0 ||
      !complex_disk_rouche_ok(roots[i].polynomial, roots[i].disk) {
      return false
    }
    total = total + roots[i].multiplicity
    for j in (i + 1)..<roots.length() {
      if !disks_disjoint(roots[i].disk, roots[j].disk) {
        return false
      }
    }
  }
  total == qpoly_degree(p)
}

///|
/// Exact eigenvalue isolations for a rational symmetric matrix, via
/// its characteristic polynomial.  `None` for a non-symmetric input.
pub fn qmat_symmetric_eigenvalue_isolations(
  a : QMat,
  width_bits : Int32,
) -> Array[RealRootIsolation]? {
  for i in 0..<a.n {
    for j in 0..<a.n {
      if !rat_eq(a.rows[i][j], a.rows[j][i]) {
        return None
      }
    }
  }
  Some(qpoly_isolate_real_roots(qmat_charpoly(a), width_bits))
}

///|
/// Characteristic polynomial of a rational-complex Hermitian matrix.
/// The real representation is a `2n x 2n` rational matrix whose
/// characteristic polynomial is the square of the Hermitian one;
/// the square root is recovered and verified from the Yun
/// squarefree factorization.
pub fn qcpx_hermitian_charpoly(a : QCpxMat) -> QPoly? {
  if !qcpx_mat_is_hermitian(a) {
    return None
  }
  let rows : Array[Array[Rat]] = []
  for block_row in 0..<(2 * a.n) {
    let row : Array[Rat] = []
    let i = block_row / 2
    let sub_i = block_row % 2
    for block_col in 0..<(2 * a.n) {
      let j = block_col / 2
      let sub_j = block_col % 2
      let z = a.rows[i][j]
      row.push(
        if sub_i == 0 && sub_j == 0 {
          z.re
        } else if sub_i == 0 && sub_j == 1 {
          rat_neg(z.im)
        } else if sub_i == 1 && sub_j == 0 {
          z.im
        } else {
          z.re
        },
      )
    }
    rows.push(row)
  }
  let squared = qmat_charpoly(qmat_from_rows(rows))
  let groups = qpoly_squarefree_factorization(squared)
  let mut root = qpoly_one()
  for i in 0..<groups.length() {
    if groups[i].multiplicity % 2 != 0 {
      return None
    }
    root = qpoly_mul(
      root,
      qpoly_pow(groups[i].factor, groups[i].multiplicity / 2),
    )
  }
  if qpoly_eq(qpoly_mul(root, root), qpoly_monic(squared)) {
    Some(qpoly_monic(root))
  } else {
    None
  }
}

///|
/// Individually separated arbitrary-precision eigenvalue intervals
/// for a rational-complex Hermitian matrix.  Unlike merged Jacobi
/// Gershgorin discs, every distinct eigenvalue gets a Sturm
/// isolation of width at most `2^-width_bits`, regardless of how
/// close distinct eigenvalues are.
pub fn qcpx_hermitian_eigenvalue_isolations(
  a : QCpxMat,
  width_bits : Int32,
) -> Array[RealRootIsolation]? {
  match qcpx_hermitian_charpoly(a) {
    Some(p) => Some(qpoly_isolate_real_roots(p, width_bits))
    None => None
  }
}

///|
/// Test helper: run the subdivision search from an empty disk set,
/// bypassing the floating oracle entirely, and verify the result
/// with the public certificate checker.
fn complex_subdivision_isolates(f : QPoly) -> Bool {
  let disks : Array[ComplexDisk] = []
  complex_subdivision_complete(f, disks)
  let roots : Array[ComplexRootIsolation] = []
  for i in 0..<disks.length() {
    roots.push(ComplexRootIsolation::{
      polynomial: f,
      disk: disks[i],
      multiplicity: 1,
    })
  }
  disks.length() == qpoly_degree(f) &&
  complex_root_isolations_are_certified(f, roots)
}

///|
pub fn check_root_isolation() -> Bool {
  let x = qpoly_x()
  let x2m2 = qpoly_sub(qpoly_mul(x, x), qpoly_int(2))
  let x2p1 = qpoly_add(qpoly_mul(x, x), qpoly_int(1))
  let p = qpoly_mul(
    qpoly_pow(qpoly_sub(x, qpoly_int(3)), 2),
    qpoly_mul(x2m2, x2p1),
  )
  let real_roots = qpoly_isolate_real_roots(p, 18)
  let complex_roots = qpoly_isolate_complex_roots(p)
  let refined = real_root_isolation_refine(real_roots[0], 36)
  let matrix = qmat_from_int_rows([[2, 1], [1, 2]])
  let eigenvalues = match qmat_symmetric_eigenvalue_isolations(matrix, 12) {
    Some(values) => values.length() == 2
    None => false
  }
  // The exact subdivision fallback is complete without any
  // floating candidate: quartic roots on the diagonals, a quintic
  // with two non-real pairs, and dyadic roots only 1/1024 apart
  // (the last also exercises roots on subdivision grid lines).
  let subdivision_quartic = qpoly_add(qpoly_pow(x, 4), qpoly_int(1))
  let subdivision_quintic = qpoly_sub(
    qpoly_sub(qpoly_pow(x, 5), x),
    qpoly_int(1),
  )
  let subdivision_clustered = qpoly_mul(
    qpoly_mul(x, qpoly_sub(x, qpoly_const(rat_make(1, 1024)))),
    x2p1,
  )
  let hermitian = qcpx_mat_from_rows([
    [qcpx_real(rat_zero()), qcpx(rat_one(), rat_one())],
    [qcpx(rat_one(), rat_int(-1)), qcpx_real(rat_zero())],
  ])
  let hermitian_eigenvalues = match
    qcpx_hermitian_eigenvalue_isolations(hermitian, 28) {
    Some(values) =>
      values.length() == 2 &&
      rat_cmp_exact(values[0].upper, values[1].lower) < 0
    None => false
  }
  real_roots.length() == 3 &&
  real_root_isolations_are_certified(p, real_roots) &&
  rat_cmp_exact(rat_sub(refined.upper, refined.lower), rat_pow2_neg(35)) <= 0 &&
  complex_roots.length() == 5 &&
  complex_root_isolations_are_certified(p, complex_roots) &&
  complex_subdivision_isolates(subdivision_quartic) &&
  complex_subdivision_isolates(subdivision_quintic) &&
  complex_subdivision_isolates(subdivision_clustered) &&
  eigenvalues &&
  hermitian_eigenvalues
}

// ---------------------------------------------------------------------------
// Phase 11: separation of Gershgorin eigenvalue clusters.
//
// Interval Jacobi returns eigenvalue clusters (`EigenInterval`
// with `count > 1`) whenever Gershgorin discs overlap; the
// discs alone cannot tell the eigenvalues inside a cluster
// apart.  Separation refines each cluster with the *exact*
// characteristic polynomial: its certified Sturm isolations are
// pairwise disjoint and carry exact multiplicities, so every
// cluster splits into one interval per distinct eigenvalue.
// A cluster consisting of a single eigenvalue of multiplicity
// `k` stays a single interval of multiplicity `k` -- identical
// eigenvalues cannot be separated further, and the exact
// multiplicity is the complete answer.
// ---------------------------------------------------------------------------

///|
pub struct SeparatedEigenInterval {
  lo : Rat
  hi : Rat
  multiplicity : Int32
  cluster : Int32
} derive(Debug, Eq)

///|
pub extend SeparatedEigenInterval with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend SeparatedEigenInterval with Eq::{not_equal, equal}

///|
pub struct JacobiClusterSeparation {
  intervals : Array[SeparatedEigenInterval]
  complete : Bool
} derive(Debug, Eq)

///|
pub extend JacobiClusterSeparation with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend JacobiClusterSeparation with Eq::{not_equal, equal}

///|
fn rat_intervals_overlap(lo1 : Rat, hi1 : Rat, lo2 : Rat, hi2 : Rat) -> Bool {
  rat_cmp_exact(lo1, hi2) <= 0 && rat_cmp_exact(lo2, hi1) <= 0
}

///|
/// Separate every cluster of a Jacobi certificate into disjoint
/// isolating intervals of width at most `2^-width_bits`, one per
/// distinct eigenvalue, with exact multiplicities.  Returns
/// `None` only when the exact characteristic polynomial is
/// unavailable (non-Hermitian input).  `complete` records that
/// every isolation matched exactly one cluster and that the
/// multiplicities inside each cluster sum to its Gershgorin
/// count; it can fail only if `width_bits` is too coarse to keep
/// isolations clear of neighbouring clusters.
pub fn jacobi_separate_clusters(
  input : QCpxMat,
  cert : JacobiCertificate,
  width_bits : Int32,
) -> JacobiClusterSeparation? {
  let charpoly = match qcpx_hermitian_charpoly(input) {
    Some(p) => p
    None => return None
  }
  let roots = qpoly_isolate_real_roots(charpoly, width_bits)
  let intervals : Array[SeparatedEigenInterval] = []
  let cluster_sums : Array[Int32] = []
  for _i in 0..<cert.eigenvalues.length() {
    cluster_sums.push(0)
  }
  let mut complete = true
  let mut total = 0
  for i in 0..<roots.length() {
    let r = roots[i]
    total = total + r.multiplicity
    let mut matched = -1
    let mut matches = 0
    for c in 0..<cert.eigenvalues.length() {
      let cl = cert.eigenvalues[c]
      if rat_intervals_overlap(r.lower, r.upper, cl.lo, cl.hi) {
        matched = c
        matches = matches + 1
      }
    }
    if matches != 1 {
      complete = false
      matched = -1
    } else {
      cluster_sums[matched] = cluster_sums[matched] + r.multiplicity
    }
    intervals.push({
      lo: r.lower,
      hi: r.upper,
      multiplicity: r.multiplicity,
      cluster: matched,
    })
  }
  if total != input.n {
    complete = false
  }
  for c in 0..<cert.eigenvalues.length() {
    if cluster_sums[c] != cert.eigenvalues[c].count {
      complete = false
    }
  }
  Some({ intervals, complete, })
}

///|
/// Multiplicity of the unique root of `p` in `[lo, hi]`, computed
/// through the gcd chain `gcd(p, p', ..., p^(k))`: the root has
/// multiplicity `>= m` iff the `m`-th gcd still vanishes there.
/// (Counting roots of the derivatives alone would be fooled by
/// unrelated critical points inside a wide interval.)
fn root_multiplicity_in(p : QPoly, lo : Rat, hi : Rat) -> Int32 {
  if rat_eq(lo, hi) {
    // Exact rational root: multiplicity is the order of the
    // first nonvanishing derivative at the point.
    let mut deriv = p
    let mut m = 0
    while qpoly_degree(deriv) >= 0 && rat_is_zero(qpoly_eval(deriv, lo)) {
      m = m + 1
      if qpoly_degree(deriv) == 0 {
        break
      }
      deriv = qpoly_derivative(deriv)
    }
    return m
  }
  let mut g = p
  let mut deriv = p
  let mut m = 0
  while qpoly_degree(g) > 0 && qpoly_real_root_count(g, lo, hi) >= 1 {
    m = m + 1
    deriv = qpoly_derivative(deriv)
    if qpoly_degree(deriv) < 0 || qpoly_is_zero(deriv) {
      break
    }
    g = qpoly_gcd(g, deriv)
  }
  m
}

///|
/// Independently certify a cluster separation: the Jacobi
/// certificate is sound; the separated intervals are sorted,
/// pairwise disjoint, each Sturm-isolates exactly one distinct
/// eigenvalue of the exact characteristic polynomial with the
/// stated multiplicity (recomputed through the gcd chain); all
/// eigenvalues are accounted for; and the intervals are
/// consistent with the clusters they refine (unique overlap,
/// multiplicity sums equal to Gershgorin counts).
pub fn jacobi_cluster_separation_certified(
  input : QCpxMat,
  cert : JacobiCertificate,
  separation : JacobiClusterSeparation,
) -> Bool {
  if !jacobi_certificate_sound(input, cert) {
    return false
  }
  let charpoly = match qcpx_hermitian_charpoly(input) {
    Some(p) => p
    None => return false
  }
  let intervals = separation.intervals
  let bound = qpoly_cauchy_bound(qpoly_squarefree_part(charpoly))
  if intervals.length() !=
    qpoly_real_root_count(charpoly, rat_neg(bound), bound) {
    return false
  }
  let cluster_sums : Array[Int32] = []
  for _i in 0..<cert.eigenvalues.length() {
    cluster_sums.push(0)
  }
  let mut total = 0
  for i in 0..<intervals.length() {
    let iv = intervals[i]
    if iv.multiplicity <= 0 || rat_cmp_exact(iv.hi, iv.lo) < 0 {
      return false
    }
    if i > 0 && rat_cmp_exact(intervals[i - 1].hi, iv.lo) >= 0 {
      return false
    }
    if rat_eq(iv.lo, iv.hi) {
      if !rat_is_zero(qpoly_eval(charpoly, iv.lo)) {
        return false
      }
    } else if qpoly_real_root_count(charpoly, iv.lo, iv.hi) != 1 {
      return false
    }
    if root_multiplicity_in(charpoly, iv.lo, iv.hi) != iv.multiplicity {
      return false
    }
    total = total + iv.multiplicity
    let mut matches = 0
    for c in 0..<cert.eigenvalues.length() {
      let cl = cert.eigenvalues[c]
      if rat_intervals_overlap(iv.lo, iv.hi, cl.lo, cl.hi) {
        matches = matches + 1
        if iv.cluster == c {
          cluster_sums[c] = cluster_sums[c] + iv.multiplicity
        }
      }
    }
    if separation.complete {
      if matches != 1 || iv.cluster < 0 {
        return false
      }
    }
  }
  if total != input.n {
    return false
  }
  if separation.complete {
    for c in 0..<cert.eigenvalues.length() {
      if cluster_sums[c] != cert.eigenvalues[c].count {
        return false
      }
    }
  }
  true
}

///|
/// Phase 11 checks for cluster separation.  With zero Jacobi
/// steps the eigenvalue enclosures are the raw Gershgorin discs,
/// which cluster for `[[1, 1/16], [1/16, 1]]` (eigenvalues
/// `15/16, 17/16`); separation must split the cluster exactly.
/// A repeated eigenvalue stays one interval of multiplicity 2,
/// and a tampered multiplicity is rejected by the certificate.
pub fn check_jacobi_cluster_separation() -> Bool {
  let one = rat_int(1)
  let sixteenth = rat_make(1, 16)
  let a2 = qcpx_mat_from_rows([
    [qcpx_real(one), qcpx_real(sixteenth)],
    [qcpx_real(sixteenth), qcpx_real(one)],
  ])
  let cert2 = match jacobi_interval_eigen(a2, max_steps=0) {
    Some(c) => c
    None => return false
  }
  if cert2.eigenvalues.length() != 1 || cert2.eigenvalues[0].count != 2 {
    return false
  }
  let sep2 = match jacobi_separate_clusters(a2, cert2, 12) {
    Some(s) => s
    None => return false
  }
  if !sep2.complete || sep2.intervals.length() != 2 {
    return false
  }
  if sep2.intervals[0].multiplicity != 1 || sep2.intervals[1].multiplicity != 1 {
    return false
  }
  if !eigen_interval_contains(
      { lo: sep2.intervals[0].lo, hi: sep2.intervals[0].hi, count: 1, },
      rat_make(15, 16),
    ) {
    return false
  }
  if !eigen_interval_contains(
      { lo: sep2.intervals[1].lo, hi: sep2.intervals[1].hi, count: 1, },
      rat_make(17, 16),
    ) {
    return false
  }
  if !jacobi_cluster_separation_certified(a2, cert2, sep2) {
    return false
  }
  let tampered = JacobiClusterSeparation::{
    intervals: [
      {
        lo: sep2.intervals[0].lo,
        hi: sep2.intervals[0].hi,
        multiplicity: 2,
        cluster: 0,
      },
      sep2.intervals[1],
    ],
    complete: true,
  }
  if jacobi_cluster_separation_certified(a2, cert2, tampered) {
    return false
  }
  // Block diagonal 3x3: a 2-cluster and a separated eigenvalue.
  let zero = rat_int(0)
  let a3 = qcpx_mat_from_rows([
    [qcpx_real(one), qcpx_real(sixteenth), qcpx_real(zero)],
    [qcpx_real(sixteenth), qcpx_real(one), qcpx_real(zero)],
    [qcpx_real(zero), qcpx_real(zero), qcpx_real(rat_int(5))],
  ])
  let cert3 = match jacobi_interval_eigen(a3, max_steps=0) {
    Some(c) => c
    None => return false
  }
  let sep3 = match jacobi_separate_clusters(a3, cert3, 12) {
    Some(s) => s
    None => return false
  }
  if !sep3.complete || sep3.intervals.length() != 3 {
    return false
  }
  if !jacobi_cluster_separation_certified(a3, cert3, sep3) {
    return false
  }
  // Repeated eigenvalue: one interval of multiplicity two.
  let a_rep = qcpx_mat_from_rows([
    [qcpx_real(rat_int(2)), qcpx_real(zero)],
    [qcpx_real(zero), qcpx_real(rat_int(2))],
  ])
  let cert_rep = match jacobi_interval_eigen(a_rep, max_steps=0) {
    Some(c) => c
    None => return false
  }
  let sep_rep = match jacobi_separate_clusters(a_rep, cert_rep, 8) {
    Some(s) => s
    None => return false
  }
  if !sep_rep.complete || sep_rep.intervals.length() != 1 {
    return false
  }
  if sep_rep.intervals[0].multiplicity != 2 {
    return false
  }
  jacobi_cluster_separation_certified(a_rep, cert_rep, sep_rep)
}

// ---------------------------------------------------------------------------
// Phase 13: separation-aware adaptive Jacobi driver.
//
// Cluster-aware Jacobi is the fast path, but its interval
// envelopes can stagnate when the requested width is far below
// an eigenvalue gap and every higher-precision attempt must
// restart the rotation sequence.  The adaptive driver therefore
// treats failure to meet the target as a strategy switch, not as
// a reason to keep restarting Jacobi: it separates the clusters
// by the exact characteristic polynomial, starting at the first
// dyadic width no larger than the target and doubling that width
// precision only while cluster matching is incomplete.  The
// remaining cost is then the intrinsic exact-separation cost
// (root separation and coefficient size), with multiplicities
// retained for genuinely repeated eigenvalues.
// ---------------------------------------------------------------------------

///|
pub struct JacobiAdaptiveReport {
  cluster_aware : JacobiClusterAwareReport
  separation : JacobiClusterSeparation?
  exact_fallback_used : Bool
  exact_width_bits : Int32
  target_met : Bool
  max_interval_width : Rat
} derive(Debug, Eq)

///|
pub extend JacobiAdaptiveReport with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend JacobiAdaptiveReport with Eq::{not_equal, equal}

///|
fn jacobi_eigen_max_width(intervals : Array[EigenInterval]) -> Rat {
  let mut best = rat_zero()
  for i in 0..<intervals.length() {
    let width = rat_sub(intervals[i].hi, intervals[i].lo)
    if rat_cmp_exact(width, best) > 0 {
      best = width
    }
  }
  best
}

///|
fn jacobi_separated_max_width(intervals : Array[SeparatedEigenInterval]) -> Rat {
  let mut best = rat_zero()
  for i in 0..<intervals.length() {
    let width = rat_sub(intervals[i].hi, intervals[i].lo)
    if rat_cmp_exact(width, best) > 0 {
      best = width
    }
  }
  best
}

///|
fn jacobi_singletons_meet_target(
  intervals : Array[EigenInterval],
  target_width : Rat,
) -> Bool {
  for i in 0..<intervals.length() {
    if intervals[i].count != 1 {
      return false
    }
    if rat_cmp_exact(rat_sub(intervals[i].hi, intervals[i].lo), target_width) >
      0 {
      return false
    }
  }
  true
}

///|
/// Certified eigenvalue intervals by cluster-aware Jacobi with an
/// exact characteristic-polynomial fallback.  The target is met
/// on the Jacobi path only when every Gershgorin cluster is a
/// singleton of width at most `target_width`; it is met on the
/// exact path when `jacobi_separate_clusters` is complete and
/// every distinct-eigenvalue isolation has width at most the
/// target.  A repeated eigenvalue can therefore meet the target
/// as one narrow interval with its exact multiplicity.  If
/// `max_exact_width_bits` is insufficient, the best exact attempt
/// is returned with `target_met=false` rather than being hidden.
pub fn jacobi_interval_eigen_adaptive(
  input : QCpxMat,
  target_width~ : Rat = rat_make(1, 64),
  max_steps~ : Int32 = 48,
  tolerance_sq~ : Rat = rat_make(1, 1048576),
  initial_bits~ : Int32 = 10,
  max_bits~ : Int32 = 40,
  max_exact_width_bits~ : Int32 = 128,
) -> JacobiAdaptiveReport? {
  if rat_cmp_exact(target_width, rat_zero()) <= 0 || max_exact_width_bits <= 0 {
    return None
  }
  let cluster_aware = match
    jacobi_interval_eigen_cluster_aware(
      input,
      target_width~,
      max_steps~,
      tolerance_sq~,
      initial_bits~,
      max_bits~,
    ) {
    Some(report) => report
    None => return None
  }
  let certificate = cluster_aware.certificate
  if jacobi_singletons_meet_target(certificate.eigenvalues, target_width) {
    return Some(JacobiAdaptiveReport::{
      cluster_aware,
      separation: None,
      exact_fallback_used: false,
      exact_width_bits: 0,
      target_met: true,
      max_interval_width: jacobi_eigen_max_width(certificate.eigenvalues),
    })
  }
  let mut bits = 1
  while bits < max_exact_width_bits &&
        rat_cmp_exact(rat_pow2_neg(bits), target_width) > 0 {
    bits = bits + 1
  }
  let mut chosen : JacobiClusterSeparation? = None
  let mut chosen_bits = bits
  while true {
    match jacobi_separate_clusters(input, certificate, bits) {
      Some(separation) => {
        chosen = Some(separation)
        chosen_bits = bits
        if separation.complete &&
          rat_cmp_exact(
            jacobi_separated_max_width(separation.intervals),
            target_width,
          ) <=
          0 {
          break
        }
      }
      None => break
    }
    if bits >= max_exact_width_bits {
      break
    }
    bits = if bits * 2 > max_exact_width_bits {
      max_exact_width_bits
    } else {
      bits * 2
    }
  }
  match chosen {
    Some(separation) => {
      let max_width = jacobi_separated_max_width(separation.intervals)
      Some(JacobiAdaptiveReport::{
        cluster_aware,
        separation: Some(separation),
        exact_fallback_used: true,
        exact_width_bits: chosen_bits,
        target_met: separation.complete &&
        rat_cmp_exact(max_width, target_width) <= 0,
        max_interval_width: max_width,
      })
    }
    None =>
      Some(JacobiAdaptiveReport::{
        cluster_aware,
        separation: None,
        exact_fallback_used: true,
        exact_width_bits: chosen_bits,
        target_met: false,
        max_interval_width: jacobi_eigen_max_width(certificate.eigenvalues),
      })
  }
}

///|
pub fn check_jacobi_adaptive_exact_fallback() -> Bool {
  // Fast path: the phase-12 example already separates into
  // singleton Jacobi intervals of the requested width.
  let easy = qcpx_mat_from_rows([
    [qcpx_real(rat_int(2)), qcpx_real(rat_make(1, 8))],
    [qcpx_real(rat_make(1, 8)), qcpx_real(rat_make(129, 64))],
  ])
  let easy_report = match
    jacobi_interval_eigen_adaptive(
      easy,
      target_width=rat_make(1, 16),
      tolerance_sq=rat_make(1, 16),
    ) {
    Some(r) => r
    None => return false
  }
  if easy_report.exact_fallback_used ||
    !easy_report.target_met ||
    easy_report.separation != None ||
    !jacobi_certificate_sound(easy, easy_report.cluster_aware.certificate) {
    return false
  }
  // Tight path: eigenvalues ±1/4096 with a 1/16384 target.  The
  // deliberately low Jacobi precision cap makes its envelopes
  // stagnate, so the adaptive driver must switch to exact Sturm
  // separation and still meet the width target.
  let eps = rat_make(1, 4096)
  let tight = qcpx_mat_from_rows([
    [qcpx_real(rat_zero()), qcpx_real(eps)],
    [qcpx_real(eps), qcpx_real(rat_zero())],
  ])
  let report = match
    jacobi_interval_eigen_adaptive(
      tight,
      target_width=rat_make(1, 16384),
      initial_bits=6,
      max_bits=8,
      max_exact_width_bits=32,
    ) {
    Some(r) => r
    None => return false
  }
  if !report.exact_fallback_used ||
    !report.target_met ||
    report.exact_width_bits < 14 ||
    rat_cmp_exact(report.max_interval_width, rat_make(1, 16384)) > 0 {
    return false
  }
  let separation = match report.separation {
    Some(s) => s
    None => return false
  }
  if !separation.complete || separation.intervals.length() != 2 {
    return false
  }
  if !eigen_interval_contains(
      {
        lo: separation.intervals[0].lo,
        hi: separation.intervals[0].hi,
        count: 1,
      },
      rat_neg(eps),
    ) ||
    !eigen_interval_contains(
      {
        lo: separation.intervals[1].lo,
        hi: separation.intervals[1].hi,
        count: 1,
      },
      eps,
    ) {
    return false
  }
  if !jacobi_cluster_separation_certified(
      tight,
      report.cluster_aware.certificate,
      separation,
    ) {
    return false
  }
  // A repeated eigenvalue meets a narrow target as one exact
  // multiplicity-two interval; it is not split artificially.
  let repeated = qcpx_mat_from_rows([
    [qcpx_real(rat_int(2)), qcpx_real(rat_zero())],
    [qcpx_real(rat_zero()), qcpx_real(rat_int(2))],
  ])
  let repeated_report = match
    jacobi_interval_eigen_adaptive(
      repeated,
      target_width=rat_make(1, 256),
      max_exact_width_bits=16,
    ) {
    Some(r) => r
    None => return false
  }
  let repeated_sep = match repeated_report.separation {
    Some(s) => s
    None => return false
  }
  repeated_report.exact_fallback_used &&
  repeated_report.target_met &&
  repeated_sep.complete &&
  repeated_sep.intervals.length() == 1 &&
  repeated_sep.intervals[0].multiplicity == 2 &&
  jacobi_cluster_separation_certified(
    repeated,
    repeated_report.cluster_aware.certificate,
    repeated_sep,
  )
}
