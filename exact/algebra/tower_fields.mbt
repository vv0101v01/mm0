// ==================================================================
// Higher exact tower fields beyond the biquadratic fragment:
//
//   * `CubicNum`: the pure cubic field Q(∛m) for cubefree
//     `m`, |m| >= 2, in the basis 1, ∛m, ∛m².  The pair
//     (a, b) in the decomposition |m| = a·b² (a, b squarefree,
//     coprime) is canonicalised so that the two radicands
//     ab² and a²b, which generate the same field, share one
//     representation.  x³ - m is irreducible (no rational
//     root), so coordinates are unique and equality is exact.
//
//   * `TriquadNum`: the triquadratic field Q(√d₁, √d₂, √d₃)
//     (degree 8) in the product basis, for a fixed independent
//     triple of squarefree generators.  Values from `BiquadNum`
//     embed by matching slot radicals; two triples spanning
//     the same square-class space are realigned by the same
//     slot matching.
//
// The headline solver is `triquad_sqrt_of_biquad`: a square
// root of a biquadratic `y` that lies in a triquadratic field
// but not in `y`'s own field.  Any such root has the form
// `w·√γ` with `w` in the biquadratic field and `γ` rational
// (write the root as `z₀ + z₁√γ`; the cross term must vanish).
// Writing `y = u + v√d₂` over `K₁ = Q(√d₁)`, the norm
// `n = u² - d₂v²` must satisfy `n = γ²δ²` for some `δ ∈ K₁`;
// the resulting linear condition determines `δ` (using that
// `N(n)` must be a rational square), hence `γ`, and then
// `w = √(y/γ)` is found inside the biquadratic field.  The
// result is verified by squaring in the triquadratic field.
//
// `radical_to_cubic` and `radical_to_triquad` evaluate radical
// expressions into these normal forms, extending
// `radical_equal_exact` (in `biquad_denest.mbt`) to the pure
// cubic and triquadratic fragments.
// ==================================================================

// ---------------------------------------------------------------------------
// Pure cubic fields
// ---------------------------------------------------------------------------

///|
pub struct CubicNum {
  m : BigInt
  a : Rat
  b : Rat
  c : Rat
} derive(Debug, Eq)

///|
pub extend CubicNum with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend CubicNum with Eq::{not_equal, equal}

///|
fn tower_bigint_abs(n : BigInt) -> BigInt {
  if n < 0N {
    -n
  } else {
    n
  }
}

///|
/// `n = s³·m` with `m` cubefree (the sign stays in `m`).
fn bigint_cubefree_decomp(n : BigInt) -> (BigInt, BigInt) {
  let mut rest = n
  let mut s = 1N
  let mut i = 2N
  while i * i * i <= tower_bigint_abs(rest) {
    let cube = i * i * i
    while rest % cube == 0N {
      rest = rest / cube
      s = s * i
    }
    i = i + 1N
  }
  (s, rest)
}

///|
/// For cubefree `t > 0`, the unique squarefree coprime pair
/// `(a, b)` with `t = a·b²`.
fn cubefree_pair(t : BigInt) -> (BigInt, BigInt) {
  let mut rest = t
  let mut a = 1N
  let mut b = 1N
  let mut i = 2N
  while i * i <= rest {
    if rest % i == 0N {
      let mut exp = 0
      while rest % i == 0N {
        rest = rest / i
        exp = exp + 1
      }
      if exp % 3 == 1 {
        a = a * i
      } else if exp % 3 == 2 {
        b = b * i
      }
    }
    i = i + 1N
  }
  if rest > 1N {
    // `rest` is prime or the square of a prime.
    match bigint_nth_root_floor(rest, 2) {
      Some(r) => if r * r == rest { b = b * r } else { a = a * rest }
      None => a = a * rest
    }
  }
  (a, b)
}

///|
/// The element `a + b∛m + c∛m²` of Q(∛m), canonicalised to the
/// generator with the larger squarefree part (see the module
/// doc).  `None` unless `m` is cubefree with |m| >= 2.
pub fn cubic_make(m : BigInt, a : Rat, b : Rat, c : Rat) -> CubicNum? {
  let (s, mf) = bigint_cubefree_decomp(m)
  if s != 1N || mf != m || tower_bigint_abs(m) < 2N {
    return None
  }
  let (pa, pb) = cubefree_pair(tower_bigint_abs(m))
  if pb > pa {
    // Switch generator from ∛(±ab²) to ∛(±a²b):
    // θ = sgn·θ'²/a and θ² = sgn·b·θ' with sgn = sign(m),
    // where θ' is the (real) cube root for the new radicand.
    let sgn = if m < 0N { rat_int(-1) } else { rat_one() }
    let new_m = if m < 0N { -(pa * pa * pb) } else { pa * pa * pb }
    Some(CubicNum::{
      m: new_m,
      a,
      b: rat_mul(sgn, rat_mul(c, rat_big_int(pb))),
      c: rat_mul(sgn, rat_div(b, rat_big_int(pa))),
    })
  } else {
    Some(CubicNum::{ m, a, b, c, })
  }
}

///|
pub fn cubic_rat(m : BigInt, r : Rat) -> CubicNum? {
  cubic_make(m, r, rat_zero(), rat_zero())
}

///|
pub fn cubic_generator(m : BigInt) -> CubicNum? {
  cubic_make(m, rat_zero(), rat_one(), rat_zero())
}

///|
pub fn cubic_is_zero(x : CubicNum) -> Bool {
  rat_is_zero(x.a) && rat_is_zero(x.b) && rat_is_zero(x.c)
}

///|
pub fn cubic_is_rat(x : CubicNum) -> Bool {
  rat_is_zero(x.b) && rat_is_zero(x.c)
}

///|
pub fn cubic_eq(x : CubicNum, y : CubicNum) -> Bool {
  x == y
}

///|
/// Rebase a rational value to the other operand's field; two
/// genuinely different cubic fields do not align.
fn cubic_align(x : CubicNum, y : CubicNum) -> (CubicNum, CubicNum)? {
  if x.m == y.m {
    Some((x, y))
  } else if cubic_is_rat(x) {
    Some((CubicNum::{ m: y.m, a: x.a, b: rat_zero(), c: rat_zero(), }, y))
  } else if cubic_is_rat(y) {
    Some((x, CubicNum::{ m: x.m, a: y.a, b: rat_zero(), c: rat_zero(), }))
  } else {
    None
  }
}

///|
pub fn cubic_neg(x : CubicNum) -> CubicNum {
  CubicNum::{ m: x.m, a: rat_neg(x.a), b: rat_neg(x.b), c: rat_neg(x.c), }
}

///|
pub fn cubic_add(x : CubicNum, y : CubicNum) -> CubicNum? {
  match cubic_align(x, y) {
    Some((u, v)) =>
      Some(CubicNum::{
        m: u.m,
        a: rat_add(u.a, v.a),
        b: rat_add(u.b, v.b),
        c: rat_add(u.c, v.c),
      })
    None => None
  }
}

///|
pub fn cubic_sub(x : CubicNum, y : CubicNum) -> CubicNum? {
  cubic_add(x, cubic_neg(y))
}

///|
pub fn cubic_mul(x : CubicNum, y : CubicNum) -> CubicNum? {
  match cubic_align(x, y) {
    Some((u, v)) => {
      let m = rat_big_int(u.m)
      Some(CubicNum::{
        m: u.m,
        a: rat_add(
          rat_mul(u.a, v.a),
          rat_mul(m, rat_add(rat_mul(u.b, v.c), rat_mul(u.c, v.b))),
        ),
        b: rat_add(
          rat_add(rat_mul(u.a, v.b), rat_mul(u.b, v.a)),
          rat_mul(m, rat_mul(u.c, v.c)),
        ),
        c: rat_add(
          rat_add(rat_mul(u.a, v.c), rat_mul(u.b, v.b)),
          rat_mul(u.c, v.a),
        ),
      })
    }
    None => None
  }
}

///|
/// `a³ + m·b³ + m²·c³ - 3m·abc`.
pub fn cubic_norm(x : CubicNum) -> Rat {
  let m = rat_big_int(x.m)
  let a3 = rat_mul(x.a, rat_mul(x.a, x.a))
  let b3 = rat_mul(m, rat_mul(x.b, rat_mul(x.b, x.b)))
  let c3 = rat_mul(rat_mul(m, m), rat_mul(x.c, rat_mul(x.c, x.c)))
  let cross = rat_mul(rat_int(3), rat_mul(m, rat_mul(x.a, rat_mul(x.b, x.c))))
  rat_sub(rat_add(rat_add(a3, b3), c3), cross)
}

///|
pub fn cubic_inv(x : CubicNum) -> CubicNum? {
  let n = cubic_norm(x)
  if rat_is_zero(n) {
    return None
  }
  let m = rat_big_int(x.m)
  let big_a = rat_sub(rat_mul(x.a, x.a), rat_mul(m, rat_mul(x.b, x.c)))
  let big_b = rat_sub(rat_mul(m, rat_mul(x.c, x.c)), rat_mul(x.a, x.b))
  let big_c = rat_sub(rat_mul(x.b, x.b), rat_mul(x.a, x.c))
  Some(CubicNum::{
    m: x.m,
    a: rat_div(big_a, n),
    b: rat_div(big_b, n),
    c: rat_div(big_c, n),
  })
}

///|
pub fn cubic_div(x : CubicNum, y : CubicNum) -> CubicNum? {
  match cubic_align(x, y) {
    Some((u, v)) =>
      match cubic_inv(v) {
        Some(inv) => cubic_mul(u, inv)
        None => None
      }
    None => None
  }
}

///|
fn cubic_root_interval(m : BigInt, k : Int32) -> (Rat, Rat) {
  let mut scale = 1N
  for _i in 0..<k {
    scale = scale * 2N
  }
  let t = match
    bigint_nth_root_floor(tower_bigint_abs(m) * scale * scale * scale, 3) {
    Some(v) => v
    None => 0N
  }
  let lo = rat_make_big(t, scale)
  let hi = rat_make_big(t + 1N, scale)
  if m < 0N {
    (rat_neg(hi), rat_neg(lo))
  } else {
    (lo, hi)
  }
}

///|
fn rat_interval_mul_rat_bounds(lo : Rat, hi : Rat, coeff : Rat) -> (Rat, Rat) {
  let p = rat_mul(lo, coeff)
  let q = rat_mul(hi, coeff)
  if rat_cmp_exact(p, q) <= 0 {
    (p, q)
  } else {
    (q, p)
  }
}

///|
/// Exact sign in the real embedding `θ = ∛m ∈ ℝ`, by dyadic
/// interval refinement of `∛m`; a nonzero value's sign is
/// eventually isolated.
pub fn cubic_sign(x : CubicNum) -> Int32 {
  if cubic_is_zero(x) {
    return 0
  }
  let mut k = 8
  while k <= 512 {
    let (lo, hi) = cubic_root_interval(x.m, k)
    let (blo, bhi) = rat_interval_mul_rat_bounds(lo, hi, x.b)
    let sq_lo = if rat_cmp_exact(lo, rat_zero()) >= 0 {
      rat_mul(lo, lo)
    } else if rat_cmp_exact(hi, rat_zero()) <= 0 {
      rat_mul(hi, hi)
    } else {
      rat_zero()
    }
    let lo_sq = rat_mul(lo, lo)
    let hi_sq = rat_mul(hi, hi)
    let sq_hi = if rat_cmp_exact(lo_sq, hi_sq) >= 0 { lo_sq } else { hi_sq }
    let (clo, chi) = rat_interval_mul_rat_bounds(sq_lo, sq_hi, x.c)
    let total_lo = rat_add(rat_add(x.a, blo), clo)
    let total_hi = rat_add(rat_add(x.a, bhi), chi)
    if rat_cmp_exact(total_lo, rat_zero()) > 0 {
      return 1
    }
    if rat_cmp_exact(total_hi, rat_zero()) < 0 {
      return -1
    }
    k = k * 2
  }
  // Unreachable for the represented (nonzero) values: interval
  // widths tend to zero while the value stays fixed.
  0
}

///|
/// The real cube root of a rational, as a `CubicNum` (or a
/// rational value in the default Q(∛2) when it is rational).
pub fn cubic_cuberoot_rat(r : Rat) -> CubicNum? {
  if rat_is_zero(r) {
    return cubic_rat(2N, rat_zero())
  }
  // ∛(p/q) = ∛(pq²)/q for q > 0.
  let big_n = r.num * r.den * r.den
  let (s, m) = bigint_cubefree_decomp(big_n)
  let coeff = rat_make_big(s, r.den)
  if m == 1N {
    cubic_rat(2N, coeff)
  } else if m == -1N {
    cubic_rat(2N, rat_neg(coeff))
  } else {
    cubic_make(m, rat_zero(), coeff, rat_zero())
  }
}

///|
fn cubic_to_alg(x : CubicNum) -> AlgNum {
  let modulus = qpoly_normalize([
    rat_neg(rat_big_int(x.m)),
    rat_zero(),
    rat_zero(),
    rat_one(),
  ])
  alg_make(modulus, qpoly_normalize([x.a, x.b, x.c]))
}

///|
fn cubic_from_alg(m : BigInt, x : AlgNum) -> CubicNum? {
  let coeffs = alg_coeffs(x)
  let coeff = (i : Int32) => {
    if i < coeffs.length() {
      coeffs[i]
    } else {
      rat_zero()
    }
  }
  cubic_make(m, coeff(0), coeff(1), coeff(2))
}

///|
/// Evaluate a radical expression in a pure cubic field.  Cube
/// roots of rationals generate the field; cube roots of cubic
/// values are found inside the same field when they exist
/// there (through `AlgNum`); other roots are outside the
/// fragment.
pub fn radical_to_cubic(e : RadicalExpr) -> CubicNum? {
  match e {
    RRat(r) => cubic_rat(2N, r)
    RNeg(a) =>
      match radical_to_cubic(a) {
        Some(v) => Some(cubic_neg(v))
        None => None
      }
    RAdd(a, b) =>
      match (radical_to_cubic(a), radical_to_cubic(b)) {
        (Some(x), Some(y)) => cubic_add(x, y)
        _ => None
      }
    RSub(a, b) =>
      match (radical_to_cubic(a), radical_to_cubic(b)) {
        (Some(x), Some(y)) => cubic_sub(x, y)
        _ => None
      }
    RMul(a, b) =>
      match (radical_to_cubic(a), radical_to_cubic(b)) {
        (Some(x), Some(y)) => cubic_mul(x, y)
        _ => None
      }
    RDiv(a, b) =>
      match (radical_to_cubic(a), radical_to_cubic(b)) {
        (Some(x), Some(y)) => cubic_div(x, y)
        _ => None
      }
    RRoot(3, RRat(r)) => cubic_cuberoot_rat(r)
    RRoot(3, a) =>
      match radical_to_cubic(a) {
        Some(x) =>
          match alg_nth_root_in_field(cubic_to_alg(x), 3) {
            Some(root) => cubic_from_alg(x.m, root)
            None => None
          }
        None => None
      }
    RRoot(_, _) => None
  }
}

// ---------------------------------------------------------------------------
// Triquadratic fields
// ---------------------------------------------------------------------------

///|
pub struct TriquadNum {
  gens : Array[BigInt]
  coeffs : Array[Rat]
} derive(Debug, Eq)

///|
pub extend TriquadNum with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend TriquadNum with Eq::{not_equal, equal}

///|
fn triquad_gens_independent(gens : Array[BigInt]) -> Bool {
  if gens.length() != 3 {
    return false
  }
  for i in 0..<3 {
    if gens[i] <= 1N {
      return false
    }
    let (scale, sqf) = bigint_squarefree_decomp(gens[i])
    if scale != 1N || sqf != gens[i] {
      return false
    }
  }
  for mask in 1..<8 {
    let (_, sqf) = biquad_slot_radical(gens, mask)
    if sqf == 1N {
      return false
    }
  }
  true
}

///|
pub fn triquad_make(gens : Array[BigInt], coeffs : Array[Rat]) -> TriquadNum? {
  if !triquad_gens_independent(gens) {
    return None
  }
  let full : Array[Rat] = []
  for i in 0..<8 {
    full.push(if i < coeffs.length() { coeffs[i] } else { rat_zero() })
  }
  Some(TriquadNum::{ gens: [gens[0], gens[1], gens[2]], coeffs: full, })
}

///|
pub fn triquad_eq(x : TriquadNum, y : TriquadNum) -> Bool {
  match triquad_align(x, y) {
    Some((u, v)) => u.coeffs == v.coeffs
    None => false
  }
}

///|
pub fn triquad_is_zero(x : TriquadNum) -> Bool {
  for i in 0..<8 {
    if !rat_is_zero(x.coeffs[i]) {
      return false
    }
  }
  true
}

///|
fn triquad_raw(gens : Array[BigInt], coeffs : Array[Rat]) -> TriquadNum {
  TriquadNum::{ gens, coeffs, }
}

///|
pub fn triquad_neg(x : TriquadNum) -> TriquadNum {
  let out : Array[Rat] = []
  for i in 0..<8 {
    out.push(rat_neg(x.coeffs[i]))
  }
  triquad_raw(x.gens, out)
}

///|
fn triquad_add_same(x : TriquadNum, y : TriquadNum) -> TriquadNum {
  let out : Array[Rat] = []
  for i in 0..<8 {
    out.push(rat_add(x.coeffs[i], y.coeffs[i]))
  }
  triquad_raw(x.gens, out)
}

///|
fn triquad_mul_same(x : TriquadNum, y : TriquadNum) -> TriquadNum {
  let out : Array[Rat] = []
  for _i in 0..<8 {
    out.push(rat_zero())
  }
  for s in 0..<8 {
    for t in 0..<8 {
      if !rat_is_zero(x.coeffs[s]) && !rat_is_zero(y.coeffs[t]) {
        let mut factor = 1N
        let mut target = 0
        for i in 0..<3 {
          let sb = (s >> i) & 1
          let tb = (t >> i) & 1
          if sb == 1 && tb == 1 {
            factor = factor * x.gens[i]
          }
          if (sb + tb) % 2 == 1 {
            target = target + (1 << i)
          }
        }
        out[target] = rat_add(
          out[target],
          rat_mul(rat_mul(x.coeffs[s], y.coeffs[t]), rat_big_int(factor)),
        )
      }
    }
  }
  triquad_raw(x.gens, out)
}

///|
/// Embed basis slots by squarefree-radical matching: every
/// nonzero slot radical of the source must occur among the
/// target's slot radicals.
fn triquad_reembed_slots(
  src_gens : Array[BigInt],
  src_coeffs : Array[Rat],
  dst_gens : Array[BigInt],
) -> TriquadNum? {
  let out : Array[Rat] = []
  for _i in 0..<8 {
    out.push(rat_zero())
  }
  for mask in 0..<src_coeffs.length() {
    let coeff = src_coeffs[mask]
    if !rat_is_zero(coeff) {
      let (h, d) = biquad_slot_radical(src_gens, mask)
      let mut placed = false
      for tmask in 0..<8 {
        let (h2, d2) = biquad_slot_radical(dst_gens, tmask)
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
  }
  Some(triquad_raw([dst_gens[0], dst_gens[1], dst_gens[2]], out))
}

///|
pub fn triquad_embed_biquad(gens : Array[BigInt], x : BiquadNum) -> TriquadNum? {
  if !triquad_gens_independent(gens) {
    return None
  }
  triquad_reembed_slots(x.basis, x.coeffs, gens)
}

///|
pub fn triquad_reembed(x : TriquadNum, gens : Array[BigInt]) -> TriquadNum? {
  if !triquad_gens_independent(gens) {
    return None
  }
  triquad_reembed_slots(x.gens, x.coeffs, gens)
}

///|
/// Bring two values to a common generator triple when their
/// square-class spans agree.
pub fn triquad_align(
  x : TriquadNum,
  y : TriquadNum,
) -> (TriquadNum, TriquadNum)? {
  if x.gens == y.gens {
    return Some((x, y))
  }
  match triquad_reembed(y, x.gens) {
    Some(y2) => Some((x, y2))
    None =>
      match triquad_reembed(x, y.gens) {
        Some(x2) => Some((x2, y))
        None => None
      }
  }
}

///|
pub fn triquad_add(x : TriquadNum, y : TriquadNum) -> TriquadNum? {
  match triquad_align(x, y) {
    Some((u, v)) => Some(triquad_add_same(u, v))
    None => None
  }
}

///|
pub fn triquad_sub(x : TriquadNum, y : TriquadNum) -> TriquadNum? {
  triquad_add(x, triquad_neg(y))
}

///|
pub fn triquad_mul(x : TriquadNum, y : TriquadNum) -> TriquadNum? {
  match triquad_align(x, y) {
    Some((u, v)) => Some(triquad_mul_same(u, v))
    None => None
  }
}

///|
/// Inverse through the product of the seven nontrivial Galois
/// conjugates (independent sign flips of the generators).
pub fn triquad_inv(x : TriquadNum) -> TriquadNum? {
  if triquad_is_zero(x) {
    return None
  }
  let mut acc = triquad_raw(x.gens, [
    rat_one(),
    rat_zero(),
    rat_zero(),
    rat_zero(),
    rat_zero(),
    rat_zero(),
    rat_zero(),
    rat_zero(),
  ])
  for pattern in 1..<8 {
    let coeffs : Array[Rat] = []
    for mask in 0..<8 {
      let mut parity = 0
      for i in 0..<3 {
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
    acc = triquad_mul_same(acc, triquad_raw(x.gens, coeffs))
  }
  let norm_value = triquad_mul_same(x, acc)
  let n = norm_value.coeffs[0]
  if rat_is_zero(n) {
    return None
  }
  for i in 1..<8 {
    if !rat_is_zero(norm_value.coeffs[i]) {
      return None
    }
  }
  let out : Array[Rat] = []
  for i in 0..<8 {
    out.push(rat_div(acc.coeffs[i], n))
  }
  Some(triquad_raw(x.gens, out))
}

///|
pub fn triquad_div(x : TriquadNum, y : TriquadNum) -> TriquadNum? {
  match triquad_align(x, y) {
    Some((u, v)) =>
      match triquad_inv(v) {
        Some(inv) => Some(triquad_mul_same(u, inv))
        None => None
      }
    None => None
  }
}

///|
fn triquad_sqrt_interval(d : BigInt, k : Int32) -> (Rat, Rat) {
  let mut scale = 1N
  for _i in 0..<k {
    scale = scale * 2N
  }
  let t = match bigint_nth_root_floor(d * scale * scale, 2) {
    Some(v) => v
    None => 0N
  }
  (rat_make_big(t, scale), rat_make_big(t + 1N, scale))
}

///|
/// Exact sign in the real embedding, by dyadic interval
/// refinement of the three square roots.
pub fn triquad_sign(x : TriquadNum) -> Int32 {
  if triquad_is_zero(x) {
    return 0
  }
  let mut k = 8
  while k <= 512 {
    let intervals : Array[(Rat, Rat)] = []
    for i in 0..<3 {
      intervals.push(triquad_sqrt_interval(x.gens[i], k))
    }
    let mut total_lo = rat_zero()
    let mut total_hi = rat_zero()
    for mask in 0..<8 {
      let mut slot_lo = rat_one()
      let mut slot_hi = rat_one()
      for i in 0..<3 {
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
/// Independence of a set of squarefree integers in Q*/Q*²: no
/// nonempty subproduct is a rational square.
fn squareclass_independent_set(gens : Array[BigInt]) -> Bool {
  let count = 1 << gens.length()
  for mask in 1..<count {
    let (_, sqf) = biquad_slot_radical(gens, mask)
    if sqf == 1N {
      return false
    }
  }
  true
}

///|
/// Extend a biquadratic basis (length <= 2) to an independent
/// triple using the first suitable small primes.
fn triquad_extend_gens(basis : Array[BigInt]) -> Array[BigInt]? {
  let gens : Array[BigInt] = []
  for i in 0..<basis.length() {
    gens.push(basis[i])
  }
  let primes = small_primes_upto(50)
  let mut idx = 0
  while gens.length() < 3 && idx < primes.length() {
    let cand = BigInt::from_int(primes[idx])
    idx = idx + 1
    let trial : Array[BigInt] = []
    for i in 0..<gens.length() {
      trial.push(gens[i])
    }
    trial.push(cand)
    if squareclass_independent_set(trial) {
      gens.push(cand)
    }
  }
  if gens.length() == 3 && triquad_gens_independent(gens) {
    Some(gens)
  } else {
    None
  }
}

///|
/// Square root of a biquadratic number in a triquadratic
/// field, when one exists there (see the module doc for the
/// algorithm); the positive root is returned.
pub fn triquad_sqrt_of_biquad(y : BiquadNum) -> TriquadNum? {
  if biquad_sign(y) < 0 {
    return None
  }
  match biquad_sqrt(y) {
    Some(w) => {
      let gens = match triquad_extend_gens(w.basis) {
        Some(v) => v
        None => return None
      }
      triquad_embed_biquad(gens, w)
    }
    None => {
      if y.basis.length() != 2 {
        return None
      }
      let d1 = y.basis[0]
      let d2 = y.basis[1]
      let coeff = (i : Int32) => {
        if i < y.coeffs.length() {
          y.coeffs[i]
        } else {
          rat_zero()
        }
      }
      let u = quad_make_big(coeff(0), coeff(1), d1)
      let v = quad_make_big(coeff(2), coeff(3), d1)
      let n = quad_sub(
        quad_mul(u, u),
        quad_mul(quad_rat(rat_big_int(d2)), quad_mul(v, v)),
      )
      let s = match rat_sqrt_if_square(quad_norm(n)) {
        Some(vv) => vv
        None => return None
      }
      let deltas : Array[QuadNum] = []
      if rat_is_zero(n.b) {
        deltas.push(quad_one())
        deltas.push(quad_make_big(rat_zero(), rat_one(), d1))
      } else {
        deltas.push(quad_make_big(rat_div(rat_add(n.a, s), n.b), rat_one(), d1))
        deltas.push(quad_make_big(rat_div(rat_sub(n.a, s), n.b), rat_one(), d1))
      }
      for di in 0..<deltas.length() {
        let delta = deltas[di]
        let gammas = match quad_div(n, quad_mul(delta, delta)) {
          Some(q) =>
            if rat_is_zero(q.b) {
              match rat_sqrt_if_square(q.a) {
                Some(g) => [g]
                None => []
              }
            } else {
              []
            }
          None => []
        }
        for gi in 0..<gammas.length() {
          let gamma = gammas[gi]
          if rat_is_zero(gamma) {
            continue
          }
          let w = match biquad_div(y, biquad_rat(gamma)) {
            Some(scaled) =>
              match biquad_sqrt(scaled) {
                Some(ww) => ww
                None => continue
              }
            None => continue
          }
          let sqrt_gamma = quad_sqrt_rat(gamma)
          if rat_is_zero(sqrt_gamma.b) {
            match biquad_mul(w, biquad_rat(sqrt_gamma.a)) {
              Some(z) => {
                let gens = match triquad_extend_gens(z.basis) {
                  Some(vv) => vv
                  None => continue
                }
                match triquad_embed_biquad(gens, z) {
                  Some(zt) => return Some(zt)
                  None => continue
                }
              }
              None => continue
            }
          }
          let gens = [d1, d2, sqrt_gamma.d]
          let w_tri = match triquad_embed_biquad(gens, w) {
            Some(vv) => vv
            None => continue
          }
          let g_tri = triquad_raw(gens, [
            rat_zero(),
            rat_zero(),
            rat_zero(),
            rat_zero(),
            sqrt_gamma.b,
            rat_zero(),
            rat_zero(),
            rat_zero(),
          ])
          let mut z = triquad_mul_same(w_tri, g_tri)
          let y_tri = match triquad_embed_biquad(gens, y) {
            Some(vv) => vv
            None => continue
          }
          if triquad_mul_same(z, z).coeffs == y_tri.coeffs {
            if triquad_sign(z) < 0 {
              z = triquad_neg(z)
            }
            return Some(z)
          }
        }
      }
      None
    }
  }
}

///|
/// Evaluate a radical expression in a triquadratic field.
/// Square roots are taken of biquadratic-valued radicands
/// (through `triquad_sqrt_of_biquad`); deeper nesting and
/// other root indices are outside the fragment.
pub fn radical_to_triquad(e : RadicalExpr) -> TriquadNum? {
  match e {
    RRat(r) => triquad_make([2N, 3N, 5N], [r])
    RNeg(a) =>
      match radical_to_triquad(a) {
        Some(v) => Some(triquad_neg(v))
        None => None
      }
    RAdd(a, b) =>
      match (radical_to_triquad(a), radical_to_triquad(b)) {
        (Some(x), Some(y)) => triquad_add(x, y)
        _ => None
      }
    RSub(a, b) =>
      match (radical_to_triquad(a), radical_to_triquad(b)) {
        (Some(x), Some(y)) => triquad_sub(x, y)
        _ => None
      }
    RMul(a, b) =>
      match (radical_to_triquad(a), radical_to_triquad(b)) {
        (Some(x), Some(y)) => triquad_mul(x, y)
        _ => None
      }
    RDiv(a, b) =>
      match (radical_to_triquad(a), radical_to_triquad(b)) {
        (Some(x), Some(y)) => triquad_div(x, y)
        _ => None
      }
    RRoot(2, a) =>
      match radical_to_biquad(a) {
        Some(y) => triquad_sqrt_of_biquad(y)
        None => None
      }
    RRoot(_, _) => None
  }
}

///|
pub fn check_tower_fields() -> Bool {
  // --- Pure cubic field Q(∛2). ---
  let t = match cubic_generator(2N) {
    Some(v) => v
    None => return false
  }
  let t2 = match cubic_mul(t, t) {
    Some(v) => v
    None => return false
  }
  let t3 = match cubic_mul(t2, t) {
    Some(v) => v
    None => return false
  }
  match cubic_rat(2N, rat_int(2)) {
    Some(two) => if !cubic_eq(t3, two) { return false }
    None => return false
  }
  // ∛4 generates the same field and canonicalises to ∛2's
  // basis, where it is t².
  match cubic_cuberoot_rat(rat_int(4)) {
    Some(v) => if !cubic_eq(v, t2) { return false }
    None => return false
  }
  // (1 + t)(1 + t)^-1 = 1 and N(1 + t) = 1 + 2 = 3.
  let one_plus_t = match cubic_add(t, t) {
    Some(_) =>
      match cubic_make(2N, rat_one(), rat_one(), rat_zero()) {
        Some(v) => v
        None => return false
      }
    None => return false
  }
  if !rat_eq(cubic_norm(one_plus_t), rat_int(3)) {
    return false
  }
  match cubic_inv(one_plus_t) {
    Some(inv) =>
      match cubic_mul(one_plus_t, inv) {
        Some(prod) =>
          if !cubic_eq(prod, CubicNum::{
              m: 2N,
              a: rat_one(),
              b: rat_zero(),
              c: rat_zero(),
            }) {
            return false
          }
        None => return false
      }
    None => return false
  }
  // Signs: ∛2 > 1 and 4∛2 > 5 > 0, so 5 - 4∛2 < 0.
  let probe1 = match cubic_make(2N, rat_int(-1), rat_one(), rat_zero()) {
    Some(v) => v
    None => return false
  }
  let probe2 = match cubic_make(2N, rat_int(5), rat_int(-4), rat_zero()) {
    Some(v) => v
    None => return false
  }
  if cubic_sign(probe1) != 1 || cubic_sign(probe2) != -1 {
    return false
  }
  // (∛2 - 1)(1 + ∛2 + ∛4) = ∛8 - 1 = 1 through radical
  // expressions and the cubic normal form.
  let cbrt2 = RadicalExpr::RRoot(3, radical_int(2))
  let cbrt4 = RadicalExpr::RRoot(3, radical_int(4))
  let cubic_expr = RadicalExpr::RMul(
    RadicalExpr::RSub(cbrt2, radical_int(1)),
    RadicalExpr::RAdd(RadicalExpr::RAdd(radical_int(1), cbrt2), cbrt4),
  )
  if radical_equal_exact(cubic_expr, radical_int(1)) != Some(true) {
    return false
  }
  // --- Triquadratic square roots. ---
  // w = 1 + √2 + √3 in Q(√2, √3); y = 5w² has no square root
  // in that field (else √5 would lie in it), but
  // √y = w√5 in Q(√2, √3, √5).
  let w = biquad_make([2N, 3N], [rat_one(), rat_one(), rat_one(), rat_zero()])
  let w2 = match biquad_mul(w, w) {
    Some(v) => v
    None => return false
  }
  let y = match biquad_mul(w2, biquad_rat(rat_int(5))) {
    Some(v) => v
    None => return false
  }
  if biquad_sqrt(y) != None {
    return false
  }
  let z = match triquad_sqrt_of_biquad(y) {
    Some(v) => v
    None => return false
  }
  let y_tri = match triquad_embed_biquad(z.gens, y) {
    Some(v) => v
    None => return false
  }
  match triquad_mul(z, z) {
    Some(z2) => if !triquad_eq(z2, y_tri) { return false }
    None => return false
  }
  if triquad_sign(z) != 1 {
    return false
  }
  // The same identity through radical expressions:
  // √(5(1+√2+√3)²) = √5(1+√2+√3).
  let root2 = radical_sqrt(radical_int(2))
  let root3 = radical_sqrt(radical_int(3))
  let root5 = radical_sqrt(radical_int(5))
  let w_expr = RadicalExpr::RAdd(
    RadicalExpr::RAdd(radical_int(1), root2),
    root3,
  )
  let lhs = radical_sqrt(
    RadicalExpr::RMul(radical_int(5), RadicalExpr::RMul(w_expr, w_expr)),
  )
  let rhs = RadicalExpr::RMul(root5, w_expr)
  radical_equal_exact(lhs, rhs) == Some(true)
}
