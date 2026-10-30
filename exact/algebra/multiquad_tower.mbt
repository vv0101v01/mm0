///|
// Multiquadratic tower fields `Q(√d₁, …, √d_k)` for `k <= 4`
// (degree at most 16), extending the biquadratic and
// triquadratic fragments by one further independent quadratic
// generator.  A value is stored in the product basis
// `∏_{i ∈ S} √d_i` for a sorted independent family of
// squarefree integers `d_i > 1`; alignment takes place in the
// square-class group `Q*/Q*²`, refusing composita that would
// need a fifth generator.
//
// Square roots are computed at two levels.
//
//   * `multiquad_sqrt_in_field` decides and computes a square
//     root already present in the value's own multiquadratic
//     field, by the usual relative-norm recursion down the
//     tower: for `x = u + v√d` over `L`, a root `p + q√d`
//     forces `u² - dv²` to be a square `s²` in `L`, after
//     which `p² = (u ± s)/2` is solved recursively in `L`
//     and `q = v/(2p)`; every candidate is verified by
//     squaring.
//
//   * `multiquad_rational_square_adjustment` determines the
//     rational square class of `x` when it comes from `Q`:
//     it looks for a positive squarefree integer `γ` and a
//     `w` in the same field with `x = γw²`, recursively
//     through the relative norm (the two factors
//     `(u ± s)/2` must carry the same rational `γ`).  At each
//     level `γ` is reduced to the least representative modulo
//     the rational square classes already trivial in that
//     field (the slot radicals): in `Q(√2)`, for instance,
//     `11` and `22` induce the same adjustment problem, and
//     the recursion must not mistake them for different
//     classes.
//     `multiquad_sqrt_extended` then returns `w√γ`, adjoining
//     `√γ` as a new generator when it is not already in the
//     field (subject to the four-generator bound).  A sqrt
//     whose radicand has no rational square class in this
//     sense needs a genuinely non-multiquadratic quadratic
//     extension and remains outside this fragment.

///|
pub struct MultiQuadNum {
  basis : Array[BigInt]
  coeffs : Array[Rat]
} derive(Debug, Eq)

///|
pub extend MultiQuadNum with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend MultiQuadNum with Eq::{not_equal, equal}

///|
fn multiquad_max_generators() -> Int32 {
  4
}

///|
fn multiquad_slot_count_for(basis : Array[BigInt]) -> Int32 {
  1 << basis.length()
}

///|
fn multiquad_basis_valid_upto(basis : Array[BigInt], max_gens : Int32) -> Bool {
  if max_gens < 0 || max_gens > 8 || basis.length() > max_gens {
    return false
  }
  for i in 0..<basis.length() {
    if basis[i] <= 1N {
      return false
    }
    let (scale, sqf) = bigint_squarefree_decomp(basis[i])
    if scale != 1N || sqf != basis[i] {
      return false
    }
  }
  let count = multiquad_slot_count_for(basis)
  for mask in 1..<count {
    let (_, sqf) = biquad_slot_radical(basis, mask)
    if sqf == 1N {
      return false
    }
  }
  true
}

///|
fn multiquad_basis_valid(basis : Array[BigInt]) -> Bool {
  multiquad_basis_valid_upto(basis, multiquad_max_generators())
}

///|
fn multiquad_raw(basis : Array[BigInt], coeffs : Array[Rat]) -> MultiQuadNum {
  MultiQuadNum::{ basis, coeffs, }
}

///|
fn multiquad_zero_coeffs(count : Int32) -> Array[Rat] {
  let out : Array[Rat] = []
  for _ in 0..<count {
    out.push(rat_zero())
  }
  out
}

///|
fn multiquad_full_coeffs(
  basis : Array[BigInt],
  coeffs : Array[Rat],
) -> Array[Rat] {
  let out = multiquad_zero_coeffs(multiquad_slot_count_for(basis))
  for i in 0..<coeffs.length() {
    if i < out.length() {
      out[i] = coeffs[i]
    }
  }
  out
}

///|
fn multiquad_reembed_slots(
  src_basis : Array[BigInt],
  src_coeffs : Array[Rat],
  dst_basis : Array[BigInt],
) -> MultiQuadNum? {
  let dst_count = multiquad_slot_count_for(dst_basis)
  let out = multiquad_zero_coeffs(dst_count)
  for mask in 0..<src_coeffs.length() {
    let coeff = src_coeffs[mask]
    if rat_is_zero(coeff) {
      continue
    }
    let (h, d) = biquad_slot_radical(src_basis, mask)
    let mut placed = false
    for tmask in 0..<dst_count {
      let (h2, d2) = biquad_slot_radical(dst_basis, tmask)
      if d2 == d {
        out[tmask] = rat_add(out[tmask], rat_mul(coeff, rat_make_big(h, h2)))
        placed = true
        break
      }
    }
    if !placed {
      return None
    }
  }
  Some(multiquad_raw(dst_basis, out))
}

///|
/// The element with the given product-basis coefficients.
/// `basis` must be an independent family of at most four
/// squarefree integers `> 1` (in any order); the stored basis is
/// sorted and coefficients are padded with zeros as needed.
pub fn multiquad_make(
  basis : Array[BigInt],
  coeffs : Array[Rat],
) -> MultiQuadNum? {
  if !multiquad_basis_valid(basis) {
    return None
  }
  let sorted = biquad_sort_basis(basis)
  multiquad_reembed_slots(basis, multiquad_full_coeffs(basis, coeffs), sorted)
}

///|
pub fn multiquad_rat(r : Rat) -> MultiQuadNum {
  multiquad_raw([], [r])
}

///|
pub fn multiquad_zero() -> MultiQuadNum {
  multiquad_rat(rat_zero())
}

///|
fn multiquad_zero_with_basis(basis : Array[BigInt]) -> MultiQuadNum {
  multiquad_raw(basis, multiquad_zero_coeffs(multiquad_slot_count_for(basis)))
}

///|
fn multiquad_one_with_basis(basis : Array[BigInt]) -> MultiQuadNum {
  let coeffs = multiquad_zero_coeffs(multiquad_slot_count_for(basis))
  coeffs[0] = rat_one()
  multiquad_raw(basis, coeffs)
}

///|
pub fn multiquad_is_zero(x : MultiQuadNum) -> Bool {
  for i in 0..<x.coeffs.length() {
    if !rat_is_zero(x.coeffs[i]) {
      return false
    }
  }
  true
}

///|
pub fn multiquad_is_rat(x : MultiQuadNum) -> Bool {
  for i in 1..<x.coeffs.length() {
    if !rat_is_zero(x.coeffs[i]) {
      return false
    }
  }
  true
}

///|
pub fn multiquad_to_rat(x : MultiQuadNum) -> Rat? {
  if multiquad_is_rat(x) {
    Some(x.coeffs[0])
  } else {
    None
  }
}

///|
pub fn multiquad_neg(x : MultiQuadNum) -> MultiQuadNum {
  let out : Array[Rat] = []
  for i in 0..<x.coeffs.length() {
    out.push(rat_neg(x.coeffs[i]))
  }
  multiquad_raw(x.basis, out)
}

///|
fn multiquad_scale_rat(x : MultiQuadNum, c : Rat) -> MultiQuadNum {
  let out : Array[Rat] = []
  for i in 0..<x.coeffs.length() {
    out.push(rat_mul(c, x.coeffs[i]))
  }
  multiquad_raw(x.basis, out)
}

///|
fn multiquad_scale_bigint(x : MultiQuadNum, c : BigInt) -> MultiQuadNum {
  multiquad_scale_rat(x, rat_big_int(c))
}

///|
fn multiquad_add_same(x : MultiQuadNum, y : MultiQuadNum) -> MultiQuadNum {
  let out : Array[Rat] = []
  for i in 0..<x.coeffs.length() {
    out.push(rat_add(x.coeffs[i], y.coeffs[i]))
  }
  multiquad_raw(x.basis, out)
}

///|
fn multiquad_sub_same(x : MultiQuadNum, y : MultiQuadNum) -> MultiQuadNum {
  multiquad_add_same(x, multiquad_neg(y))
}

///|
fn multiquad_mul_same(x : MultiQuadNum, y : MultiQuadNum) -> MultiQuadNum {
  let count = x.coeffs.length()
  let out = multiquad_zero_coeffs(count)
  for s in 0..<count {
    if rat_is_zero(x.coeffs[s]) {
      continue
    }
    for t in 0..<count {
      if rat_is_zero(y.coeffs[t]) {
        continue
      }
      let mut factor = 1N
      let both = s & t
      for i in 0..<x.basis.length() {
        if ((both >> i) & 1) == 1 {
          factor = factor * x.basis[i]
        }
      }
      let slot = s ^ t
      out[slot] = rat_add(
        out[slot],
        rat_mul(rat_mul(x.coeffs[s], y.coeffs[t]), rat_big_int(factor)),
      )
    }
  }
  multiquad_raw(x.basis, out)
}

///|
/// Express `x` in the field generated by `basis` (any order; the
/// stored form is sorted), or `None` when some slot radical of
/// `x` is not in that field.
pub fn multiquad_reembed(
  x : MultiQuadNum,
  basis : Array[BigInt],
) -> MultiQuadNum? {
  if !multiquad_basis_valid(basis) {
    return None
  }
  multiquad_reembed_slots(x.basis, x.coeffs, biquad_sort_basis(basis))
}

///|
fn multiquad_common_basis_upto(
  a : Array[BigInt],
  b : Array[BigInt],
  max_gens : Int32,
) -> Array[BigInt]? {
  if max_gens < 0 || max_gens > 8 {
    return None
  }
  let mut basis = biquad_sort_basis(a)
  if basis.length() > max_gens {
    return None
  }
  for i in 0..<b.length() {
    let d = b[i]
    let mut spanned = false
    for mask in 0..<multiquad_slot_count_for(basis) {
      if biquad_slot_radical(basis, mask).1 == d {
        spanned = true
        break
      }
    }
    if !spanned {
      if basis.length() >= max_gens {
        return None
      }
      basis = biquad_sort_basis([..basis, d])
    }
  }
  Some(basis)
}

///|
fn multiquad_common_basis(
  a : Array[BigInt],
  b : Array[BigInt],
) -> Array[BigInt]? {
  multiquad_common_basis_upto(a, b, multiquad_max_generators())
}

///|
/// Bring two values to a common multiquadratic basis (their
/// compositum), refusing a fifth independent generator.
pub fn multiquad_align(
  x : MultiQuadNum,
  y : MultiQuadNum,
) -> (MultiQuadNum, MultiQuadNum)? {
  let basis = match multiquad_common_basis(x.basis, y.basis) {
    Some(value) => value
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
pub fn multiquad_eq(x : MultiQuadNum, y : MultiQuadNum) -> Bool {
  match multiquad_align(x, y) {
    Some((u, v)) => u.coeffs == v.coeffs
    None => false
  }
}

///|
pub fn multiquad_add(x : MultiQuadNum, y : MultiQuadNum) -> MultiQuadNum? {
  match multiquad_align(x, y) {
    Some((u, v)) => Some(multiquad_add_same(u, v))
    None => None
  }
}

///|
pub fn multiquad_sub(x : MultiQuadNum, y : MultiQuadNum) -> MultiQuadNum? {
  multiquad_add(x, multiquad_neg(y))
}

///|
pub fn multiquad_mul(x : MultiQuadNum, y : MultiQuadNum) -> MultiQuadNum? {
  match multiquad_align(x, y) {
    Some((u, v)) => Some(multiquad_mul_same(u, v))
    None => None
  }
}

///|
/// Inverse through the product of the nontrivial Galois
/// conjugates (independent sign flips of the generators).
pub fn multiquad_inv(x : MultiQuadNum) -> MultiQuadNum? {
  if multiquad_is_zero(x) {
    return None
  }
  let count = x.coeffs.length()
  let mut acc = multiquad_one_with_basis(x.basis)
  for pattern in 1..<count {
    let coeffs : Array[Rat] = []
    for mask in 0..<count {
      let mut parity = 0
      for i in 0..<x.basis.length() {
        if ((mask >> i) & 1) == 1 && ((pattern >> i) & 1) == 1 {
          parity = parity + 1
        }
      }
      coeffs.push(
        if parity % 2 == 1 {
          rat_neg(x.coeffs[mask])
        } else {
          x.coeffs[mask]
        },
      )
    }
    acc = multiquad_mul_same(acc, multiquad_raw(x.basis, coeffs))
  }
  let norm_value = multiquad_mul_same(x, acc)
  let n = norm_value.coeffs[0]
  if rat_is_zero(n) {
    return None
  }
  for i in 1..<count {
    if !rat_is_zero(norm_value.coeffs[i]) {
      return None
    }
  }
  let out : Array[Rat] = []
  for i in 0..<count {
    out.push(rat_div(acc.coeffs[i], n))
  }
  Some(multiquad_raw(x.basis, out))
}

///|
fn multiquad_div_same(x : MultiQuadNum, y : MultiQuadNum) -> MultiQuadNum? {
  match multiquad_inv(y) {
    Some(inv) => Some(multiquad_mul_same(x, inv))
    None => None
  }
}

///|
pub fn multiquad_div(x : MultiQuadNum, y : MultiQuadNum) -> MultiQuadNum? {
  match multiquad_align(x, y) {
    Some((u, v)) => multiquad_div_same(u, v)
    None => None
  }
}

///|
/// Embed a quadratic number, when its radicand is a positive
/// squarefree integer (the real multiquadratic fragment).
pub fn multiquad_of_quad(q : QuadNum) -> MultiQuadNum? {
  multiquad_of_biquad(biquad_of_quad(q))
}

///|
pub fn multiquad_of_biquad(x : BiquadNum) -> MultiQuadNum? {
  multiquad_make(x.basis, x.coeffs)
}

///|
pub fn multiquad_of_triquad(x : TriquadNum) -> MultiQuadNum? {
  multiquad_make(x.gens, x.coeffs)
}

///|
/// `√r` for a nonnegative rational, as a multiquadratic number.
pub fn multiquad_sqrt_rat(r : Rat) -> MultiQuadNum? {
  if rat_sign(r) < 0 {
    return None
  }
  if rat_is_zero(r) {
    return Some(multiquad_zero())
  }
  let (scale, d) = bigint_squarefree_decomp(r.num * r.den)
  let coeff = rat_make_big(scale, r.den)
  if d == 1N {
    Some(multiquad_rat(coeff))
  } else {
    multiquad_make([d], [rat_zero(), coeff])
  }
}

///|
fn multiquad_sqrt_interval(d : BigInt, k : Int32) -> (Rat, Rat) {
  let mut scale = 1N
  for _ in 0..<k {
    scale = scale * 2N
  }
  let t = match bigint_nth_root_floor(d * scale * scale, 2) {
    Some(value) => value
    None => 0N
  }
  (rat_make_big(t, scale), rat_make_big(t + 1N, scale))
}

///|
/// Exact sign in the real embedding, by dyadic interval
/// refinement of the square-root generators.
pub fn multiquad_sign(x : MultiQuadNum) -> Int32 {
  if multiquad_is_zero(x) {
    return 0
  }
  let mut k = 8
  while k <= 512 {
    let intervals : Array[(Rat, Rat)] = []
    for i in 0..<x.basis.length() {
      intervals.push(multiquad_sqrt_interval(x.basis[i], k))
    }
    let mut total_lo = rat_zero()
    let mut total_hi = rat_zero()
    for mask in 0..<x.coeffs.length() {
      let mut slot_lo = rat_one()
      let mut slot_hi = rat_one()
      for i in 0..<x.basis.length() {
        if ((mask >> i) & 1) == 1 {
          slot_lo = rat_mul(slot_lo, intervals[i].0)
          slot_hi = rat_mul(slot_hi, intervals[i].1)
        }
      }
      let (term_lo, term_hi) = rat_interval_mul_rat_bounds(
        slot_lo,
        slot_hi,
        x.coeffs[mask],
      )
      total_lo = rat_add(total_lo, term_lo)
      total_hi = rat_add(total_hi, term_hi)
    }
    if rat_cmp_exact(total_lo, rat_zero()) > 0 {
      return 1
    }
    if rat_cmp_exact(total_hi, rat_zero()) < 0 {
      return -1
    }
    k = k * 2
  }
  0
}

///|
fn multiquad_positive_version(x : MultiQuadNum) -> MultiQuadNum {
  if multiquad_sign(x) < 0 {
    multiquad_neg(x)
  } else {
    x
  }
}

///|
fn multiquad_split_last(
  x : MultiQuadNum,
) -> (MultiQuadNum, MultiQuadNum, BigInt) {
  let k = x.basis.length()
  let lower_basis : Array[BigInt] = []
  for i in 0..<(k - 1) {
    lower_basis.push(x.basis[i])
  }
  let half = 1 << (k - 1)
  let u_coeffs : Array[Rat] = []
  let v_coeffs : Array[Rat] = []
  for i in 0..<half {
    u_coeffs.push(x.coeffs[i])
    v_coeffs.push(x.coeffs[half + i])
  }
  (
    multiquad_raw(lower_basis, u_coeffs),
    multiquad_raw(lower_basis, v_coeffs),
    x.basis[k - 1],
  )
}

///|
fn multiquad_combine_last(
  u : MultiQuadNum,
  v : MultiQuadNum,
  d : BigInt,
) -> MultiQuadNum {
  let basis : Array[BigInt] = []
  for i in 0..<u.basis.length() {
    basis.push(u.basis[i])
  }
  basis.push(d)
  let coeffs : Array[Rat] = []
  for i in 0..<u.coeffs.length() {
    coeffs.push(u.coeffs[i])
  }
  for i in 0..<v.coeffs.length() {
    coeffs.push(v.coeffs[i])
  }
  multiquad_raw(basis, coeffs)
}

///|
/// The positive square root of `x` when one lies in `x`'s own
/// multiquadratic field, computed by relative-norm recursion
/// down the tower (see the module doc).  `None` when `x` is
/// negative or has no square root in that field.
pub fn multiquad_sqrt_in_field(x : MultiQuadNum) -> MultiQuadNum? {
  if multiquad_is_zero(x) {
    return Some(multiquad_zero_with_basis(x.basis))
  }
  if multiquad_sign(x) < 0 {
    return None
  }
  if x.basis.length() == 0 {
    return match rat_sqrt_if_square(x.coeffs[0]) {
      Some(root) => Some(multiquad_rat(root))
      None => None
    }
  }
  let (u, v, d) = multiquad_split_last(x)
  if multiquad_is_zero(v) {
    match multiquad_sqrt_in_field(u) {
      Some(p) =>
        return Some(
          multiquad_positive_version(
            multiquad_combine_last(p, multiquad_zero_with_basis(u.basis), d),
          ),
        )
      None => ()
    }
    let u_over_d = multiquad_scale_rat(u, rat_make_big(1N, d))
    return match multiquad_sqrt_in_field(u_over_d) {
      Some(q) =>
        Some(
          multiquad_positive_version(
            multiquad_combine_last(multiquad_zero_with_basis(u.basis), q, d),
          ),
        )
      None => None
    }
  }
  let norm_down = multiquad_sub_same(
    multiquad_mul_same(u, u),
    multiquad_scale_bigint(multiquad_mul_same(v, v), d),
  )
  let s0 = match multiquad_sqrt_in_field(norm_down) {
    Some(value) => value
    None => return None
  }
  let signs = [s0, multiquad_neg(s0)]
  for si in 0..<signs.length() {
    let p2 = multiquad_scale_rat(
      multiquad_add_same(u, signs[si]),
      rat_make(1, 2),
    )
    let p = match multiquad_sqrt_in_field(p2) {
      Some(value) => value
      None => continue
    }
    if multiquad_is_zero(p) {
      continue
    }
    let q = match multiquad_div_same(v, multiquad_scale_rat(p, rat_int(2))) {
      Some(value) => value
      None => continue
    }
    let y = multiquad_combine_last(p, q, d)
    if multiquad_mul_same(y, y).coeffs == x.coeffs {
      return Some(multiquad_positive_version(y))
    }
  }
  None
}

///|
/// Reduce an adjustment `x = γw²` in `root`'s field to the
/// least positive squarefree representative of `γ` modulo the
/// slot-radical square classes already present in the field,
/// adjusting `w` by the corresponding slot square root.  This
/// makes the `γ` returned by the recursive adjustment a
/// canonical invariant of the lower field, which the parent
/// level can compare for equality.
fn multiquad_reduce_gamma(
  gamma : BigInt,
  root : MultiQuadNum,
) -> (BigInt, MultiQuadNum) {
  let mut best_gamma = gamma
  let mut best_mask = 0
  let mut best_h = 1N
  let mut best_d = 1N
  let mut best_scale = 1N
  let count = multiquad_slot_count_for(root.basis)
  for mask in 0..<count {
    let (h, d) = biquad_slot_radical(root.basis, mask)
    let (scale, candidate) = bigint_squarefree_decomp(gamma * d)
    if candidate < best_gamma {
      best_gamma = candidate
      best_mask = mask
      best_h = h
      best_d = d
      best_scale = scale
    }
  }
  if best_mask == 0 {
    return (gamma, root)
  }
  // The slot basis element at `best_mask` is `best_h·√best_d`,
  // so `√best_d` itself is that slot scaled by `1/best_h`.
  let slot_coeffs = multiquad_zero_coeffs(count)
  slot_coeffs[best_mask] = rat_make_big(1N, best_h)
  let slot_root = multiquad_raw(root.basis, slot_coeffs)
  // gamma·best_d = best_scale²·best_gamma and x = gamma·root²,
  // hence x = best_gamma·(root·√best_d·best_scale/best_d)².
  let adjusted = multiquad_scale_rat(
    multiquad_mul_same(root, slot_root),
    rat_make_big(best_scale, best_d),
  )
  (best_gamma, multiquad_positive_version(adjusted))
}

///|
/// The rational square class of a positive multiquadratic
/// number, when it is represented by a rational: a positive
/// squarefree integer `γ` and an element `w` of the same field
/// with `x = γw²`.  The returned `γ` is the least positive
/// squarefree representative modulo the slot-radical classes
/// already trivial in `x`'s field.  Computed by relative-norm
/// recursion: the relative norm must be a square in the lower
/// field, and the two resulting factors must carry the same
/// (lower-field-canonical) rational `γ`.
pub fn multiquad_rational_square_adjustment(
  x : MultiQuadNum,
) -> (BigInt, MultiQuadNum)? {
  if multiquad_is_zero(x) {
    return Some((1N, multiquad_zero_with_basis(x.basis)))
  }
  if multiquad_sign(x) < 0 {
    return None
  }
  if x.basis.length() == 0 {
    let r = x.coeffs[0]
    let (scale, gamma) = bigint_squarefree_decomp(r.num * r.den)
    return Some((gamma, multiquad_rat(rat_make_big(scale, r.den))))
  }
  let (u, v, d) = multiquad_split_last(x)
  if multiquad_is_zero(v) {
    match multiquad_rational_square_adjustment(u) {
      Some((gamma, p)) =>
        return Some(
          multiquad_reduce_gamma(
            gamma,
            multiquad_combine_last(p, multiquad_zero_with_basis(u.basis), d),
          ),
        )
      None => ()
    }
    let u_over_d = multiquad_scale_rat(u, rat_make_big(1N, d))
    return match multiquad_rational_square_adjustment(u_over_d) {
      Some((gamma, q)) =>
        Some(
          multiquad_reduce_gamma(
            gamma,
            multiquad_combine_last(multiquad_zero_with_basis(u.basis), q, d),
          ),
        )
      None => None
    }
  }
  let norm_down = multiquad_sub_same(
    multiquad_mul_same(u, u),
    multiquad_scale_bigint(multiquad_mul_same(v, v), d),
  )
  let s = match multiquad_sqrt_in_field(norm_down) {
    Some(value) => value
    None => return None
  }
  let a_factor = multiquad_scale_rat(multiquad_add_same(u, s), rat_make(1, 2))
  let b_factor = multiquad_scale_rat(multiquad_sub_same(u, s), rat_make(1, 2))
  let firsts = [a_factor, b_factor]
  let seconds = [b_factor, a_factor]
  for pair in 0..<2 {
    let (gamma_a, p) = match
      multiquad_rational_square_adjustment(firsts[pair]) {
      Some(value) => value
      None => continue
    }
    let second_over_d = multiquad_scale_rat(seconds[pair], rat_make_big(1N, d))
    let (gamma_c, q0) = match
      multiquad_rational_square_adjustment(second_over_d) {
      Some(value) => value
      None => continue
    }
    if gamma_a != gamma_c {
      continue
    }
    let q_choices = [q0, multiquad_neg(q0)]
    for qi in 0..<q_choices.length() {
      let y = multiquad_combine_last(p, q_choices[qi], d)
      let scaled = multiquad_scale_bigint(multiquad_mul_same(y, y), gamma_a)
      if scaled.coeffs == x.coeffs {
        return Some(
          multiquad_reduce_gamma(gamma_a, multiquad_positive_version(y)),
        )
      }
    }
  }
  None
}

///|
/// The positive square root of `x` in a multiquadratic field
/// obtained by adjoining at most one new rational square root
/// (still at most four generators in total).  Succeeds exactly
/// when `x` has a rational square class in its own field; see
/// the module doc.  Verified by squaring after alignment.
pub fn multiquad_sqrt_extended(x : MultiQuadNum) -> MultiQuadNum? {
  let (gamma, w) = match multiquad_rational_square_adjustment(x) {
    Some(value) => value
    None => return None
  }
  if gamma == 1N {
    return Some(multiquad_positive_version(w))
  }
  let root_gamma = match multiquad_make([gamma], [rat_zero(), rat_one()]) {
    Some(value) => value
    None => return None
  }
  let z = match multiquad_mul(w, root_gamma) {
    Some(value) => value
    None => return None
  }
  match multiquad_align(multiquad_mul_same(z, z), x) {
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
/// Evaluate a radical expression in a multiquadratic field with
/// at most four independent generators.  Square roots go through
/// `multiquad_sqrt_extended`; other root indices are outside the
/// fragment.
pub fn radical_to_multiquad(e : RadicalExpr) -> MultiQuadNum? {
  match e {
    RRat(r) => Some(multiquad_rat(r))
    RNeg(a) =>
      match radical_to_multiquad(a) {
        Some(value) => Some(multiquad_neg(value))
        None => None
      }
    RAdd(a, b) =>
      match (radical_to_multiquad(a), radical_to_multiquad(b)) {
        (Some(x), Some(y)) => multiquad_add(x, y)
        _ => None
      }
    RSub(a, b) =>
      match (radical_to_multiquad(a), radical_to_multiquad(b)) {
        (Some(x), Some(y)) => multiquad_sub(x, y)
        _ => None
      }
    RMul(a, b) =>
      match (radical_to_multiquad(a), radical_to_multiquad(b)) {
        (Some(x), Some(y)) => multiquad_mul(x, y)
        _ => None
      }
    RDiv(a, b) =>
      match (radical_to_multiquad(a), radical_to_multiquad(b)) {
        (Some(x), Some(y)) => multiquad_div(x, y)
        _ => None
      }
    RRoot(2, a) =>
      match radical_to_multiquad(a) {
        Some(value) => multiquad_sqrt_extended(value)
        None => None
      }
    RRoot(_, _) => None
  }
}

///|
fn multiquad_sqrt_of_int(n : Int32) -> MultiQuadNum? {
  multiquad_sqrt_rat(rat_int(n))
}

///|
pub fn check_multiquadratic_tower() -> Bool {
  let s2 = match multiquad_sqrt_of_int(2) {
    Some(v) => v
    None => return false
  }
  let s3 = match multiquad_sqrt_of_int(3) {
    Some(v) => v
    None => return false
  }
  let s5 = match multiquad_sqrt_of_int(5) {
    Some(v) => v
    None => return false
  }
  let s7 = match multiquad_sqrt_of_int(7) {
    Some(v) => v
    None => return false
  }
  let s11 = match multiquad_sqrt_of_int(11) {
    Some(v) => v
    None => return false
  }
  let one = multiquad_rat(rat_one())
  let sum3 = match
    multiquad_add(
      match multiquad_add(one, s2) {
        Some(v) => v
        None => return false
      },
      s3,
    ) {
    Some(v) =>
      match multiquad_add(v, s5) {
        Some(w) => w
        None => return false
      }
    None => return false
  }
  let sum4 = match multiquad_add(sum3, s7) {
    Some(v) => v
    None => return false
  }
  if sum4.basis.length() != 4 || sum4.coeffs.length() != 16 {
    return false
  }
  // A fifth independent generator is outside the fragment.
  if multiquad_add(sum4, s11) != None {
    return false
  }
  // Inverse and sign in the degree-16 field.
  match multiquad_inv(sum4) {
    Some(inv) =>
      match multiquad_mul(sum4, inv) {
        Some(product) => if !multiquad_eq(product, one) { return false }
        None => return false
      }
    None => return false
  }
  let sign_probe = match
    multiquad_sub(
      match multiquad_add(s7, s5) {
        Some(v) => v
        None => return false
      },
      match multiquad_add(s3, s2) {
        Some(v) => v
        None => return false
      },
    ) {
    Some(v) => v
    None => return false
  }
  if multiquad_sign(sign_probe) != 1 ||
    multiquad_sign(multiquad_neg(sign_probe)) != -1 {
    return false
  }
  // A square root already in the 4-generator field.
  let sum4_sq = match multiquad_mul(sum4, sum4) {
    Some(v) => v
    None => return false
  }
  match multiquad_sqrt_in_field(sum4_sq) {
    Some(root) => if !multiquad_eq(root, sum4) { return false }
    None => return false
  }
  // 11·(1 + √2 + √3 + √5)² has no square root in the
  // 3-generator field, but adjoining √11 gives one in the
  // 4-generator field.
  let sum3_sq = match multiquad_mul(sum3, sum3) {
    Some(v) => v
    None => return false
  }
  let y = multiquad_scale_bigint(sum3_sq, 11N)
  if multiquad_sqrt_in_field(y) != None {
    return false
  }
  match multiquad_rational_square_adjustment(y) {
    Some((gamma, w)) =>
      if gamma != 11N || !multiquad_eq(w, sum3) {
        return false
      }
    None => return false
  }
  let z = match multiquad_sqrt_extended(y) {
    Some(v) => v
    None => return false
  }
  if z.basis.length() != 4 || multiquad_sign(z) != 1 {
    return false
  }
  match multiquad_mul(z, z) {
    Some(z2) => if !multiquad_eq(z2, y) { return false }
    None => return false
  }
  let expected = match multiquad_mul(s11, sum3) {
    Some(v) => v
    None => return false
  }
  if !multiquad_eq(z, expected) {
    return false
  }
  // The same identities as radical expressions, through the
  // exact-equality dispatcher.
  let r2 = radical_sqrt(radical_int(2))
  let r3 = radical_sqrt(radical_int(3))
  let r5 = radical_sqrt(radical_int(5))
  let r7 = radical_sqrt(radical_int(7))
  let r11 = radical_sqrt(radical_int(11))
  let w3_expr = RadicalExpr::RAdd(
    RadicalExpr::RAdd(RadicalExpr::RAdd(radical_int(1), r2), r3),
    r5,
  )
  let lhs = radical_sqrt(
    RadicalExpr::RMul(radical_int(11), RadicalExpr::RMul(w3_expr, w3_expr)),
  )
  if radical_equal_exact(lhs, RadicalExpr::RMul(r11, w3_expr)) != Some(true) {
    return false
  }
  let w4_expr = RadicalExpr::RAdd(w3_expr, r7)
  let nested = radical_sqrt(RadicalExpr::RMul(w4_expr, w4_expr))
  if radical_equal_exact(nested, w4_expr) != Some(true) {
    return false
  }
  // Outside the fragment: negative square roots and cube roots.
  if multiquad_sqrt_extended(multiquad_rat(rat_int(-1))) != None ||
    radical_to_multiquad(RadicalExpr::RRoot(3, radical_int(2))) != None {
    return false
  }
  true
}
