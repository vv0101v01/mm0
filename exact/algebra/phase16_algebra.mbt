///|
// Phase 16 Exact Algebra Extensions:
//
// 1. Exact rational Lenstra–Lenstra–Lovász (`LLL`, δ = 3/4) lattice basis
//    reduction (`qmat_lll_reduce`, `qmat_is_lll_reduced`) producing both the
//    reduced basis and the unimodular integer transformation matrix `U`
//    (`det(U) = ±1`, `reduced = U * basis`).
// 2. Van Hoeij / LLL Newton-power-sum trace-lattice modular polynomial factor
//    recombination (`qpoly_factor_lll`), overcoming exponential subset search
//    on Swinnerton-Dyer polynomials and multi-factor Hensel splittings.
// 3. Full complex algebraic closure arithmetic `Q̄ ⊂ C` (`ComplexAlgNum`)
//    backed by monic irreducible minimal polynomials over `Q` paired with
//    Newton-contracted Gaussian-rational Rouché isolating disks.

// ---------------------------------------------------------------------------
// 1. Exact Rational LLL Lattice Basis Reduction (δ = 3/4)
// ---------------------------------------------------------------------------

///|
pub struct LllReductionReport {
  reduced_basis : Array[Array[Rat]]
  unimodular_u : Array[Array[BigInt]]
  swaps : Int32
  size_reductions : Int32
}

///|
fn rat_dot_vec(a : Array[Rat], b : Array[Rat]) -> Rat {
  let n = if a.length() < b.length() { a.length() } else { b.length() }
  let mut acc = rat_zero()
  for i in 0..<n {
    acc = rat_add(acc, rat_mul(a[i], b[i]))
  }
  acc
}

///|
/// Nearest integer `⌊x + 1/2⌋` for an exact rational `x`.
pub fn rat_round_nearest_bigint(x : Rat) -> BigInt {
  let shifted = rat_add(x, rat_make(1, 2))
  let n = shifted.num
  let d = shifted.den
  if n >= 0N {
    n / d
  } else {
    let pos = -n
    let q = pos / d
    let r = pos % d
    if r == 0N {
      -q
    } else {
      -(q + 1N)
    }
  }
}

///|
fn lll_compute_gram_schmidt(
  b : Array[Array[Rat]],
) -> (Array[Array[Rat]], Array[Array[Rat]], Array[Rat]) {
  let r = b.length()
  let d = if r > 0 { b[0].length() } else { 0 }
  let b_star : Array[Array[Rat]] = []
  let mu : Array[Array[Rat]] = []
  let norm2 : Array[Rat] = []
  for i in 0..<r {
    let mu_row : Array[Rat] = []
    for _j in 0..<r {
      mu_row.push(rat_zero())
    }
    mu_row[i] = rat_one()
    let star_i : Array[Rat] = []
    for col in 0..<d {
      star_i.push(b[i][col])
    }
    for j in 0..<i {
      let denom = norm2[j]
      let mij = if rat_is_zero(denom) {
        rat_zero()
      } else {
        rat_div(rat_dot_vec(b[i], b_star[j]), denom)
      }
      mu_row[j] = mij
      for col in 0..<d {
        star_i[col] = rat_sub(star_i[col], rat_mul(mij, b_star[j][col]))
      }
    }
    mu.push(mu_row)
    norm2.push(rat_dot_vec(star_i, star_i))
    b_star.push(star_i)
  }
  (b_star, mu, norm2)
}

///|
/// Exact rational LLL lattice basis reduction (`delta = delta_num / delta_den`,
/// defaulting to `3/4`) over `r` linearly independent row vectors in `Q^d`.
/// Returns `reduced_basis = U * basis` with `U ∈ GL_r(Z)`.
pub fn qmat_lll_reduce(
  basis : Array[Array[Rat]],
  delta_num~ : Int32 = 3,
  delta_den~ : Int32 = 4,
) -> LllReductionReport {
  let r = basis.length()
  if r == 0 {
    return LllReductionReport::{
      reduced_basis: [],
      unimodular_u: [],
      swaps: 0,
      size_reductions: 0,
    }
  }
  let d = basis[0].length()
  let delta = rat_make(delta_num, delta_den)
  let b : Array[Array[Rat]] = []
  let u : Array[Array[BigInt]] = []
  for i in 0..<r {
    let row : Array[Rat] = []
    for col in 0..<d {
      row.push(basis[i][col])
    }
    b.push(row)
    let urow : Array[BigInt] = []
    for j in 0..<r {
      urow.push(if i == j { 1N } else { 0N })
    }
    u.push(urow)
  }
  let (_, mu0, norm20) = lll_compute_gram_schmidt(b)
  let mut mu = mu0
  let mut norm2 = norm20
  let mut swaps = 0
  let mut reductions = 0
  let mut k = 1
  while k < r {
    let mut j = k - 1
    while j >= 0 {
      let q = rat_round_nearest_bigint(mu[k][j])
      if q != 0N {
        let q_rat = rat_make_big(q, 1N)
        for col in 0..<d {
          b[k][col] = rat_sub(b[k][col], rat_mul(q_rat, b[j][col]))
        }
        for col in 0..<r {
          u[k][col] = u[k][col] - q * u[j][col]
        }
        reductions = reductions + 1
        let (_, mu2, n2) = lll_compute_gram_schmidt(b)
        mu = mu2
        norm2 = n2
      }
      j = j - 1
    }
    // Lovász condition: `||b*_k||^2 >= (delta - mu_{k,k-1}^2) * ||b*_{k-1}||^2`.
    let mu_sq = rat_mul(mu[k][k - 1], mu[k][k - 1])
    let rhs = rat_mul(rat_sub(delta, mu_sq), norm2[k - 1])
    if rat_cmp_exact(norm2[k], rhs) >= 0 {
      k = k + 1
    } else {
      let tmp_b = b[k]
      b[k] = b[k - 1]
      b[k - 1] = tmp_b
      let tmp_u = u[k]
      u[k] = u[k - 1]
      u[k - 1] = tmp_u
      swaps = swaps + 1
      let (_, mu2, n2) = lll_compute_gram_schmidt(b)
      mu = mu2
      norm2 = n2
      k = if k - 1 > 1 { k - 1 } else { 1 }
    }
  }
  LllReductionReport::{
    reduced_basis: b,
    unimodular_u: u,
    swaps,
    size_reductions: reductions,
  }
}

///|
/// Verify size reduction (`|mu_{i,j}| <= 1/2` for `j < i`) and the Lovász
/// condition (`||b*_k||^2 >= (delta - mu_{k,k-1}^2) ||b*_{k-1}||^2`) on `basis`.
pub fn qmat_is_lll_reduced(
  basis : Array[Array[Rat]],
  delta_num~ : Int32 = 3,
  delta_den~ : Int32 = 4,
) -> Bool {
  let r = basis.length()
  if r <= 1 {
    return true
  }
  let half = rat_make(1, 2)
  let delta = rat_make(delta_num, delta_den)
  let (_, mu, norm2) = lll_compute_gram_schmidt(basis)
  for i in 0..<r {
    if rat_is_zero(norm2[i]) {
      return false
    }
    for j in 0..<i {
      if rat_cmp_exact(rat_abs_exact(mu[i][j]), half) > 0 {
        return false
      }
    }
    if i > 0 {
      let mu_sq = rat_mul(mu[i][i - 1], mu[i][i - 1])
      let rhs = rat_mul(rat_sub(delta, mu_sq), norm2[i - 1])
      if rat_cmp_exact(norm2[i], rhs) < 0 {
        return false
      }
    }
  }
  true
}

// ---------------------------------------------------------------------------
// 2. Van Hoeij / LLL Trace-Lattice Modular Polynomial Factor Recombination
// ---------------------------------------------------------------------------

///|
pub struct QPolyLllFactorReport {
  leading : Rat
  factors : Array[QPolyFactor]
  hensel_prime : Int32
  modular_factor_count : Int32
  lll_short_dimension : Int32
  used_lll_lattice : Bool
}

///|
/// Compute Newton power sums `S_1(h), ..., S_t(h) mod M` of a monic polynomial
/// `h(x) = x^d + c_{d-1} x^{d-1} + ... + c_0 (mod M)` via Newton's identities:
/// `S_k + c_{d-1} S_{k-1} + ... + c_{d-(k-1)} S_1 + k * c_{d-k} ≡ 0 (mod M)`.
fn newton_power_sums_mod(
  h : Array[BigInt],
  max_k : Int32,
  modulus : BigInt,
) -> Array[BigInt] {
  let d = h.length() - 1
  let sums : Array[BigInt] = []
  for k in 1..<=max_k {
    let mut acc = 0N
    for j in 1..<k {
      let idx = d - j
      if idx >= 0 && idx < d {
        acc = (acc + h[idx] * sums[k - j - 1]) % modulus
      }
    }
    let idx_k = d - k
    if idx_k >= 0 && idx_k < d {
      acc = (acc + BigInt::from_int(k) * h[idx_k]) % modulus
    }
    sums.push(zmod_scalar(-acc, modulus))
  }
  sums
}

///|
fn fujiwara_root_bound_big(tilde_f : Array[BigInt]) -> BigInt {
  let n = tilde_f.length() - 1
  if n <= 0 {
    return 2N
  }
  let mut half_b = 1N
  while true {
    let mut ok = true
    let mut pow_hb = 1N
    for k in 1..<=n {
      pow_hb = pow_hb * half_b
      let ak = bigint_abs(tilde_f[n - k])
      if pow_hb < ak {
        ok = false
        break
      }
    }
    if ok {
      return 2N * half_b
    }
    half_b = if half_b < 8N { half_b + 1N } else { half_b * 2N }
  }
  2N
}

///|
/// Attempt Van Hoeij LLL power-sum trace-lattice recombination on a monic
/// integer polynomial `tilde_f` (representing `lc * f_monic(x / lc)`):
/// builds the `(r + t) x (r + t)` trace lattice over `Q`, reduces it via
/// `qmat_lll_reduce`, extracts the short vector subspace whose traces satisfy
/// Fujiwara root bounds, and partitions `{0, ..., r-1}` by RREF column equality!
pub fn van_hoeij_lll_recombine(
  cur_f : QPoly,
  tilde_f : Array[BigInt],
  lc : BigInt,
  p : Int32,
  mod_factors : Array[Array[Int32]],
) -> (Array[QPoly], Int32)? {
  let r = mod_factors.length()
  let n = tilde_f.length() - 1
  if r <= 1 || n <= 1 {
    return Some(([cur_f], 1))
  }
  let root_bound = fujiwara_root_bound_big(tilde_f)
  let mut all_s1_zero = true
  for mf in mod_factors {
    let d_mf = mf.length() - 1
    if d_mf >= 1 && mf[d_mf - 1] % p != 0 {
      all_s1_zero = false
      break
    }
  }
  let trace_degs : Array[Int32] = if n >= 4 {
    if all_s1_zero {
      [2, 3, 4]
    } else {
      [1, 2, 3, 4]
    }
  } else if n >= 3 {
    [1, 2, 3]
  } else {
    [1, 2]
  }
  let max_k = trace_degs[trace_degs.length() - 1]
  let t = trace_degs.length()
  let bt = BigInt::from_int(n) * bigint_pow_int(root_bound, max_k)
  let c_scale = if bt > 1N { bt } else { 2N }
  let dim_total = r + t
  let lll_fudge = 1N << dim_total
  let min_m = mignotte_target_modulus(tilde_f)
  let trace_m = bigint_pow_int(
    c_scale * lll_fudge * BigInt::from_int(dim_total),
    2,
  )
  let target_mod = if trace_m > min_m { trace_m } else { min_m }
  let (lifted, modulus) = match
    hensel_lift_many(tilde_f, p, mod_factors, 0, r, target_mod) {
    Some(pair) => pair
    None => return None
  }
  let weights : Array[BigInt] = []
  for ti in 0..<t {
    let k = trace_degs[ti]
    let bk = BigInt::from_int(n) * bigint_pow_int(root_bound, k)
    let safe_bk = if bk > 0N { bk } else { 1N }
    let wk = c_scale / safe_bk
    weights.push(if wk > 0N { wk } else { 1N })
  }
  let factor_traces : Array[Array[BigInt]] = []
  for i in 0..<r {
    let all_ps = newton_power_sums_mod(lifted[i], max_k, modulus)
    let picked : Array[BigInt] = []
    for ti in 0..<t {
      picked.push(all_ps[trace_degs[ti] - 1])
    }
    factor_traces.push(picked)
  }
  // Build `(r + t) x (r + t)` lattice basis over Q.
  let lat : Array[Array[Rat]] = []
  for i in 0..<r {
    let row : Array[Rat] = []
    for j in 0..<r {
      row.push(if i == j { rat_make_big(c_scale, 1N) } else { rat_zero() })
    }
    for k in 0..<t {
      let centered = zmod_center_coeff(factor_traces[i][k], modulus)
      row.push(rat_make_big(weights[k] * centered, 1N))
    }
    lat.push(row)
  }
  for k in 0..<t {
    let row : Array[Rat] = []
    for _j in 0..<r {
      row.push(rat_zero())
    }
    for k2 in 0..<t {
      row.push(
        if k == k2 {
          rat_make_big(weights[k] * modulus, 1N)
        } else {
          rat_zero()
        },
      )
    }
    lat.push(row)
  }
  let red = qmat_lll_reduce(lat)
  // Collect reduced basis vectors compatible with Cauchy power-sum bounds:
  // for any integer combination in the true factor span, its first `r` entries
  // are multiples of `c_scale` and its norm is bounded!
  // Note: the all-ones vector `(1,...,1)` ALWAYS lies in the lattice because
  // `tilde_f` itself has integer coefficients, so `short_rows.length() >= 1`.
  let norm_cap_big = BigInt::from_int(dim_total) *
    (1N << dim_total) *
    c_scale *
    c_scale
  let norm_cap = rat_make_big(norm_cap_big, 1N)
  let short_rows : Array[Array[Rat]] = []
  for bi in 0..<red.reduced_basis.length() {
    let row = red.reduced_basis[bi]
    let nsq = rat_dot_vec(row, row)
    if rat_cmp_exact(nsq, norm_cap) <= 0 {
      let ind : Array[Rat] = []
      let mut integral_ok = true
      for j in 0..<r {
        let q = rat_div(row[j], rat_make_big(c_scale, 1N))
        if q.den != 1N {
          integral_ok = false
          break
        }
        ind.push(q)
      }
      if integral_ok {
        short_rows.push(ind)
      }
    }
  }
  if short_rows.length() == 0 {
    return None
  }
  if short_rows.length() == 1 {
    // Unique 1D short subspace = span{(1,...,1)} => `cur_f` is irreducible!
    return Some(([cur_f], 1))
  }
  // Compute RREF of `short_rows` (`s x r` matrix) via Gaussian elimination over Q
  // and partition columns `{0, ..., r-1}` by identical non-zero column vectors.
  let m_rows = short_rows.length()
  let mat : Array[Array[Rat]] = []
  for i in 0..<m_rows {
    let cp : Array[Rat] = []
    for j in 0..<r {
      cp.push(short_rows[i][j])
    }
    mat.push(cp)
  }
  let mut pivot_row = 0
  for col in 0..<r {
    if pivot_row >= m_rows {
      break
    }
    let mut sel = -1
    for i in pivot_row..<m_rows {
      if !rat_is_zero(mat[i][col]) {
        sel = i
        break
      }
    }
    if sel < 0 {
      continue
    }
    if sel != pivot_row {
      let tmp = mat[pivot_row]
      mat[pivot_row] = mat[sel]
      mat[sel] = tmp
    }
    let piv = mat[pivot_row][col]
    for j in col..<r {
      mat[pivot_row][j] = rat_div(mat[pivot_row][j], piv)
    }
    for i in 0..<m_rows {
      if i != pivot_row && !rat_is_zero(mat[i][col]) {
        let fac = mat[i][col]
        for j in col..<r {
          mat[i][j] = rat_sub(mat[i][j], rat_mul(fac, mat[pivot_row][j]))
        }
      }
    }
    pivot_row = pivot_row + 1
  }
  let assigned : Array[Bool] = []
  for _j in 0..<r {
    assigned.push(false)
  }
  let blocks : Array[Array[Int32]] = []
  for j in 0..<r {
    if assigned[j] {
      continue
    }
    let blk : Array[Int32] = [j]
    assigned[j] = true
    for j2 in (j + 1)..<r {
      if assigned[j2] {
        continue
      }
      let mut same = true
      for i in 0..<pivot_row {
        if !rat_eq(mat[i][j], mat[i][j2]) {
          same = false
          break
        }
      }
      if same {
        assigned[j2] = true
        blk.push(j2)
      }
    }
    blocks.push(blk)
  }
  // Reconstruct and verify each block candidate by exact division in Q[x].
  let emitted : Array[QPoly] = []
  let mut rem_f = cur_f
  for blk in blocks {
    let mut prod_mod : Array[BigInt] = [1N]
    for idx in blk {
      prod_mod = zmod_mul(modulus, prod_mod, lifted[idx])
    }
    let centered : Array[BigInt] = []
    for j in 0..<(prod_mod.length() - 1) {
      centered.push(zmod_center_coeff(prod_mod[j], modulus))
    }
    centered.push(lc % modulus)
    // Scale by `lc` before unscaling: `g_tilde(x) = lc^{deg-1} * lc * g(x/lc)`
    let deg_g = prod_mod.length() - 1
    let scaled_prod = zmod_norm(modulus, prod_mod.map(c => c * lc % modulus))
    ignore(centered)
    let g_tilde : Array[BigInt] = []
    for j in 0..<deg_g {
      let c_val = if j < scaled_prod.length() { scaled_prod[j] } else { 0N }
      g_tilde.push(zmod_center_coeff(c_val, modulus))
    }
    g_tilde.push(lc)
    let cand = unscale_monic_candidate(g_tilde, lc)
    if qpoly_degree(cand) <= 0 || !qpoly_is_zero(qpoly_mod(rem_f, cand)) {
      return None
    }
    emitted.push(cand)
    rem_f = qpoly_monic(qpoly_div_exact(rem_f, cand))
  }
  if qpoly_degree(rem_f) != 0 {
    return None
  }
  Some((emitted, pivot_row))
}

///|
/// Factor an arbitrary rational polynomial `p ∈ Q[x]` using Yun squarefree
/// decomposition, Cantor–Zassenhaus splitting over `F_p`, quadratic Hensel
/// lifting, and Van Hoeij LLL trace-lattice recombination (`qmat_lll_reduce`).
pub fn qpoly_factor_lll(p : QPoly) -> QPolyLllFactorReport {
  if qpoly_degree(p) <= 0 {
    return QPolyLllFactorReport::{
      leading: if qpoly_is_zero(p) {
        rat_zero()
      } else {
        qpoly_coeff(p, 0)
      },
      factors: [],
      hensel_prime: 0,
      modular_factor_count: 0,
      lll_short_dimension: 0,
      used_lll_lattice: false,
    }
  }
  let leading = qpoly_leading(p)
  let sqf_groups = qpoly_squarefree_factorization(qpoly_monic(p))
  let all_factors : Array[QPolyFactor] = []
  let mut rep_prime = 0
  let mut rep_mod_count = 0
  let mut rep_short_dim = 0
  let mut rep_used_lll = false
  for gi in 0..<sqf_groups.length() {
    let mult = sqf_groups[gi].multiplicity
    let mut f = qpoly_monic(sqf_groups[gi].factor)
    // Peel linear rational roots first.
    let mut peeled = true
    while peeled && qpoly_degree(f) > 1 {
      peeled = false
      let rts = qpoly_rational_roots(f)
      if rts.length() > 0 {
        let lin = qpoly_monic(qpoly_normalize([rat_neg(rts[0]), rat_one()]))
        all_factors.push(QPolyFactor::{ factor: lin, multiplicity: mult, })
        f = qpoly_monic(qpoly_div_exact(f, lin))
        peeled = true
      }
    }
    if qpoly_degree(f) == 0 {
      continue
    }
    if qpoly_degree(f) == 1 {
      all_factors.push(QPolyFactor::{ factor: f, multiplicity: mult, })
      continue
    }
    let int_coeffs = qpoly_integer_coeffs_big(f)
    let (tilde_f, lc) = monic_scaled_int_coeffs(int_coeffs)
    let primes = small_primes_upto(251)
    let mut best_p = -1
    let mut best_buckets : Array[(Array[Int32], Int32)] = []
    let mut best_count = 1000000
    for pi in 0..<primes.length() {
      let pr = primes[pi]
      if pr <= 2 || lc % BigInt::from_int(pr) == 0N {
        continue
      }
      match mod_ddf_buckets(tilde_f, pr) {
        Some(buckets) => {
          let mut cnt = 0
          for bi in 0..<buckets.length() {
            cnt = cnt + mod_degree(buckets[bi].0) / buckets[bi].1
          }
          if cnt == 1 {
            best_p = pr
            best_buckets = buckets
            best_count = 1
            break
          }
          if cnt < best_count {
            best_p = pr
            best_buckets = buckets
            best_count = cnt
            if cnt <= 4 {
              break
            }
          }
        }
        None => ()
      }
    }
    if best_p > 0 && best_count == 1 {
      rep_prime = best_p
      rep_mod_count = 1
      rep_short_dim = 1
      all_factors.push(QPolyFactor::{ factor: f, multiplicity: mult, })
      continue
    }
    let mut done_lll = false
    if best_p > 0 {
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
      if edf_ok {
        match van_hoeij_lll_recombine(f, tilde_f, lc, best_p, mod_factors) {
          Some((irreds, short_dim)) => {
            rep_prime = best_p
            rep_mod_count = mod_factors.length()
            rep_short_dim = short_dim
            rep_used_lll = true
            done_lll = true
            for ir in irreds {
              // Recursively ensure every block is completely split if two true
              // factors happened to share modular power sums at small `t`.
              let sub_cert = qpoly_factor_hensel(ir)
              for sf in sub_cert.factors {
                all_factors.push(QPolyFactor::{
                  factor: sf.factor,
                  multiplicity: mult * sf.multiplicity,
                })
              }
            }
          }
          None => ()
        }
      }
    }
    if !done_lll {
      let fb = qpoly_factor_hensel(f)
      for sf in fb.factors {
        all_factors.push(QPolyFactor::{
          factor: sf.factor,
          multiplicity: mult * sf.multiplicity,
        })
      }
    }
  }
  QPolyLllFactorReport::{
    leading,
    factors: all_factors,
    hensel_prime: rep_prime,
    modular_factor_count: rep_mod_count,
    lll_short_dimension: rep_short_dim,
    used_lll_lattice: rep_used_lll,
  }
}

// ---------------------------------------------------------------------------
// 3. Complex Algebraic Closure `Q̄ ⊂ C` via Newton-Contracted Rouché Disks
// ---------------------------------------------------------------------------

///|
/// Canonical element of the complex algebraic closure `Q̄ ⊂ C`:
/// - `minpoly`: monic irreducible minimal polynomial over `Q`,
/// - `root_index`: deterministic `(re, im)`-lexicographic index among the
///   isolated complex roots of `minpoly`,
/// - `disk`: certified Gaussian-rational Rouché isolating disk containing this
///   unique root of `minpoly` and disjoint from all its conjugates.
pub struct ComplexAlgNum {
  minpoly : QPoly
  root_index : Int32
  disk : ComplexDisk
}

///|
fn gauss_eval_poly(p : QPoly, re : Rat, im : Rat) -> (Rat, Rat) {
  let mut are = rat_zero()
  let mut aim = rat_zero()
  let mut i = p.coeffs.length() - 1
  while i >= 0 {
    let nre = rat_add(rat_sub(rat_mul(are, re), rat_mul(aim, im)), p.coeffs[i])
    let nim = rat_add(rat_mul(are, im), rat_mul(aim, re))
    are = nre
    aim = nim
    i = i - 1
  }
  (are, aim)
}

///|
fn gauss_abs_upper(re : Rat, im : Rat, bits : Int32) -> Rat {
  let (_, hi) = rat_sqrt_bounds(rat_add(rat_mul(re, re), rat_mul(im, im)), bits)
  hi
}

///|
fn round_rat_binary(r : Rat, bits : Int32) -> Rat {
  let scale = 1N << bits
  let q = rat_round_nearest_bigint(rat_mul(r, rat_make_big(scale, 1N)))
  rat_make_big(q, scale)
}

///|
/// Contract the certified Rouché isolating disk of `x : ComplexAlgNum` down to
/// `radius <= 2^{-target_bits}` via exact Gaussian-rational Newton steps
/// verified by `complex_disk_rouche_ok` and containment inside `x.disk`.
pub fn complex_alg_refine_disk(
  x : ComplexAlgNum,
  target_bits : Int32,
) -> ComplexDisk {
  if qpoly_degree(x.minpoly) <= 1 || rat_is_zero(x.disk.radius) {
    return x.disk
  }
  let target_rad = rat_make_big(1N, 1N << target_bits)
  if rat_cmp_exact(x.disk.radius, target_rad) <= 0 {
    return x.disk
  }
  let df = qpoly_derivative(x.minpoly)
  let mut cre = x.disk.re
  let mut cim = x.disk.im
  let mut cur_disk = x.disk
  let round_bits = target_bits + 28
  for _step in 0..<24 {
    let (fre, fim) = gauss_eval_poly(x.minpoly, cre, cim)
    if rat_is_zero(fre) && rat_is_zero(fim) {
      let exact_d = ComplexDisk::{ re: cre, im: cim, radius: rat_zero(), }
      let dist = gauss_abs_upper(
        rat_sub(cre, x.disk.re),
        rat_sub(cim, x.disk.im),
        round_bits,
      )
      if rat_cmp_exact(dist, x.disk.radius) < 0 {
        return exact_d
      }
    }
    let (dre, dim) = gauss_eval_poly(df, cre, cim)
    let denom = rat_add(rat_mul(dre, dre), rat_mul(dim, dim))
    if rat_is_zero(denom) {
      break
    }
    let qre = rat_div(rat_add(rat_mul(fre, dre), rat_mul(fim, dim)), denom)
    let qim = rat_div(rat_sub(rat_mul(fim, dre), rat_mul(fre, dim)), denom)
    cre = round_rat_binary(rat_sub(cre, qre), round_bits)
    cim = round_rat_binary(rat_sub(cim, qim), round_bits)
    let step_len = gauss_abs_upper(qre, qim, round_bits)
    let cand_rad = if rat_cmp_exact(rat_mul(rat_int(4), step_len), target_rad) <
      0 {
      target_rad
    } else {
      rat_mul(rat_int(4), step_len)
    }
    let cand = ComplexDisk::{ re: cre, im: cim, radius: cand_rad, }
    let center_dist = gauss_abs_upper(
      rat_sub(cre, x.disk.re),
      rat_sub(cim, x.disk.im),
      round_bits,
    )
    if rat_cmp_exact(rat_add(center_dist, cand_rad), x.disk.radius) < 0 &&
      complex_disk_rouche_ok(x.minpoly, cand) {
      cur_disk = cand
      if rat_cmp_exact(cur_disk.radius, target_rad) <= 0 {
        return cur_disk
      }
    }
  }
  cur_disk
}

///|
/// Embed a rational number `r ∈ Q` into `ComplexAlgNum`.
pub fn complex_alg_of_rat(r : Rat) -> ComplexAlgNum {
  ComplexAlgNum::{
    minpoly: qpoly_normalize([rat_neg(r), rat_one()]),
    root_index: 0,
    disk: ComplexDisk::{ re: r, im: rat_zero(), radius: rat_zero(), },
  }
}

///|
/// Canonical imaginary unit `i = √(-1) ∈ Q̄ ⊂ C` (`x^2 + 1 = 0`, `im > 0`).
pub fn complex_alg_i() -> ComplexAlgNum {
  let mp = qpoly_normalize([rat_one(), rat_zero(), rat_one()])
  let rts = qpoly_isolate_complex_roots(mp)
  for idx in 0..<rts.length() {
    if rat_cmp_exact(rts[idx].disk.im, rat_zero()) > 0 {
      return ComplexAlgNum::{
        minpoly: mp,
        root_index: idx,
        disk: rts[idx].disk,
      }
    }
  }
  ComplexAlgNum::{
    minpoly: mp,
    root_index: 1,
    disk: ComplexDisk::{ re: rat_zero(), im: rat_one(), radius: rat_zero(), },
  }
}

///|
/// Enumerate ALL complex algebraic roots (counted without multiplicity as
/// canonical `ComplexAlgNum` values paired with their multiplicities) of a
/// nonconstant polynomial `p ∈ Q[x]`.
pub fn complex_alg_roots_of(p : QPoly) -> Array[(ComplexAlgNum, Int32)] {
  let out : Array[(ComplexAlgNum, Int32)] = []
  if qpoly_degree(p) <= 0 {
    return out
  }
  let fac = qpoly_factor_lll(p)
  for f in fac.factors {
    let mp = qpoly_monic(f.factor)
    let rts = qpoly_isolate_complex_roots(mp)
    for idx in 0..<rts.length() {
      out.push(
        (
          ComplexAlgNum::{ minpoly: mp, root_index: idx, disk: rts[idx].disk, },
          f.multiplicity,
        ),
      )
    }
  }
  out
}

///|
/// Exact equality decision in `Q̄ ⊂ C`: two `ComplexAlgNum` values are equal
/// iff they share the same monic irreducible minimal polynomial and canonical
/// conjugate index.
pub fn complex_alg_eq(a : ComplexAlgNum, b : ComplexAlgNum) -> Bool {
  a.minpoly == b.minpoly && a.root_index == b.root_index
}

///|
fn complex_disks_may_overlap(a : ComplexDisk, b : ComplexDisk) -> Bool {
  !disks_disjoint(a, b)
}

///|
fn complex_alg_select_unique_root(
  ann : QPoly,
  max_degree : Int32,
  enclose : (Int32) -> ComplexDisk,
) -> ComplexAlgNum? {
  if qpoly_degree(ann) <= 0 {
    return None
  }
  let fac = qpoly_factor_lll(ann)
  let candidates : Array[(QPoly, Array[ComplexRootIsolation])] = []
  for f in fac.factors {
    let mp = qpoly_monic(f.factor)
    if qpoly_degree(mp) <= max_degree {
      candidates.push((mp, qpoly_isolate_complex_roots(mp)))
    }
  }
  let mut bits = 24
  while bits <= 200 {
    let enc = enclose(bits)
    let mut hits = 0
    let mut hit_val : ComplexAlgNum? = None
    for pair in candidates {
      let (mp, rts) = pair
      for idx in 0..<rts.length() {
        let cand_alg = ComplexAlgNum::{
          minpoly: mp,
          root_index: idx,
          disk: rts[idx].disk,
        }
        let refined_cand = complex_alg_refine_disk(cand_alg, bits + 8)
        if complex_disks_may_overlap(enc, refined_cand) {
          hits = hits + 1
          hit_val = Some(ComplexAlgNum::{
            minpoly: mp,
            root_index: idx,
            disk: refined_cand,
          })
        }
      }
    }
    if hits == 1 {
      return hit_val
    }
    bits = bits + 24
  }
  None
}

///|
/// Complex conjugation `z ↦ z̄` in `Q̄ ⊂ C` (preserving `minpoly` since
/// `minpoly ∈ Q[x]` has real coefficients!).
pub fn complex_alg_conj(x : ComplexAlgNum) -> ComplexAlgNum {
  if qpoly_degree(x.minpoly) <= 1 {
    return x
  }
  let target = fn(bits : Int32) -> ComplexDisk {
    let d = complex_alg_refine_disk(x, bits)
    ComplexDisk::{ re: d.re, im: rat_neg(d.im), radius: d.radius, }
  }
  match
    complex_alg_select_unique_root(x.minpoly, qpoly_degree(x.minpoly), target) {
    Some(v) => v
    None => x
  }
}

///|
/// Additive inverse `-z` in `Q̄ ⊂ C`.
pub fn complex_alg_neg(x : ComplexAlgNum) -> ComplexAlgNum {
  let d = qpoly_degree(x.minpoly)
  if d == 1 {
    return complex_alg_of_rat(qpoly_coeff(x.minpoly, 0))
  }
  let coeffs : Array[Rat] = []
  let parity_flip = d % 2 == 1
  for i in 0..<(d + 1) {
    let c = qpoly_coeff(x.minpoly, i)
    let signed = if i % 2 == 1 { rat_neg(c) } else { c }
    coeffs.push(if parity_flip { rat_neg(signed) } else { signed })
  }
  let mp = qpoly_monic(qpoly_normalize(coeffs))
  match
    complex_alg_select_unique_root(mp, d, bits => {
      let dk = complex_alg_refine_disk(x, bits)
      ComplexDisk::{
        re: rat_neg(dk.re),
        im: rat_neg(dk.im),
        radius: dk.radius,
      }
    }) {
    Some(v) => v
    None =>
      ComplexAlgNum::{
        minpoly: mp,
        root_index: 0,
        disk: ComplexDisk::{
          re: rat_neg(x.disk.re),
          im: rat_neg(x.disk.im),
          radius: x.disk.radius,
        },
      }
  }
}

///|
pub fn complex_alg_add(
  a : ComplexAlgNum,
  b : ComplexAlgNum,
  max_degree~ : Int32 = 32,
) -> ComplexAlgNum? {
  let da = qpoly_degree(a.minpoly)
  let db = qpoly_degree(b.minpoly)
  if da == 1 && db == 1 {
    return Some(
      complex_alg_of_rat(
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
  complex_alg_select_unique_root(ann, max_degree, bits => {
    let dka = complex_alg_refine_disk(a, bits + 6)
    let dkb = complex_alg_refine_disk(b, bits + 6)
    ComplexDisk::{
      re: rat_add(dka.re, dkb.re),
      im: rat_add(dka.im, dkb.im),
      radius: rat_add(dka.radius, dkb.radius),
    }
  })
}

///|
pub fn complex_alg_sub(
  a : ComplexAlgNum,
  b : ComplexAlgNum,
  max_degree~ : Int32 = 32,
) -> ComplexAlgNum? {
  complex_alg_add(a, complex_alg_neg(b), max_degree~)
}

///|
pub fn complex_alg_mul(
  a : ComplexAlgNum,
  b : ComplexAlgNum,
  max_degree~ : Int32 = 32,
) -> ComplexAlgNum? {
  let da = qpoly_degree(a.minpoly)
  let db = qpoly_degree(b.minpoly)
  if da == 1 && rat_is_zero(qpoly_coeff(a.minpoly, 0)) {
    return Some(complex_alg_of_rat(rat_zero()))
  }
  if db == 1 && rat_is_zero(qpoly_coeff(b.minpoly, 0)) {
    return Some(complex_alg_of_rat(rat_zero()))
  }
  if da == 1 && db == 1 {
    return Some(
      complex_alg_of_rat(
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
  complex_alg_select_unique_root(ann, max_degree, bits => {
    let dka = complex_alg_refine_disk(a, bits + 10)
    let dkb = complex_alg_refine_disk(b, bits + 10)
    let cre = rat_sub(rat_mul(dka.re, dkb.re), rat_mul(dka.im, dkb.im))
    let cim = rat_add(rat_mul(dka.re, dkb.im), rat_mul(dka.im, dkb.re))
    let abs_a = gauss_abs_upper(dka.re, dka.im, bits + 16)
    let abs_b = gauss_abs_upper(dkb.re, dkb.im, bits + 16)
    let rad = rat_add(
      rat_add(rat_mul(abs_a, dkb.radius), rat_mul(abs_b, dka.radius)),
      rat_mul(dka.radius, dkb.radius),
    )
    ComplexDisk::{ re: cre, im: cim, radius: rad, }
  })
}

///|
pub fn complex_alg_inv(x : ComplexAlgNum) -> ComplexAlgNum? {
  let d = qpoly_degree(x.minpoly)
  let c0 = qpoly_coeff(x.minpoly, 0)
  if rat_is_zero(c0) {
    return None
  }
  if d == 1 {
    return Some(complex_alg_of_rat(rat_inv(rat_neg(c0))))
  }
  let rev_coeffs : Array[Rat] = []
  for i in 0..<=d {
    rev_coeffs.push(qpoly_coeff(x.minpoly, d - i))
  }
  let mp = qpoly_monic(qpoly_normalize(rev_coeffs))
  complex_alg_select_unique_root(mp, d, bits => {
    let dk = complex_alg_refine_disk(x, bits + 12)
    let norm2 = rat_add(rat_mul(dk.re, dk.re), rat_mul(dk.im, dk.im))
    let (abs_lo, _) = rat_sqrt_bounds(norm2, bits + 16)
    let min_mod = rat_sub(abs_lo, dk.radius)
    if rat_cmp_exact(min_mod, rat_zero()) <= 0 {
      return ComplexDisk::{
        re: rat_zero(),
        im: rat_zero(),
        radius: rat_int(1000000),
      }
    }
    let ire = rat_div(dk.re, norm2)
    let iim = rat_neg(rat_div(dk.im, norm2))
    let rad = rat_div(dk.radius, rat_mul(abs_lo, min_mod))
    ComplexDisk::{ re: ire, im: iim, radius: rad, }
  })
}

///|
pub fn complex_alg_div(
  a : ComplexAlgNum,
  b : ComplexAlgNum,
  max_degree~ : Int32 = 32,
) -> ComplexAlgNum? {
  match complex_alg_inv(b) {
    Some(inv_b) => complex_alg_mul(a, inv_b, max_degree~)
    None => None
  }
}

///|
pub fn complex_alg_pow(
  x : ComplexAlgNum,
  n : Int32,
  max_degree~ : Int32 = 32,
) -> ComplexAlgNum? {
  if n == 0 {
    return Some(complex_alg_of_rat(rat_one()))
  }
  if n < 0 {
    return match complex_alg_inv(x) {
      Some(ix) => complex_alg_pow(ix, -n, max_degree~)
      None => None
    }
  }
  let mut acc = complex_alg_of_rat(rat_one())
  let mut base = x
  let mut exp = n
  while exp > 0 {
    if exp % 2 == 1 {
      acc = match complex_alg_mul(acc, base, max_degree~) {
        Some(v) => v
        None => return None
      }
    }
    exp = exp / 2
    if exp > 0 {
      base = match complex_alg_mul(base, base, max_degree~) {
        Some(v) => v
        None => return None
      }
    }
  }
  Some(acc)
}

///|
/// Compute ALL `n` exact complex algebraic `n`-th roots (`z^n == x`) of an
/// arbitrary `x ∈ Q̄ ⊂ C` (`n >= 1`) by factoring `p_x(z^n)` via LLL and
/// filtering the exact roots whose `n`-th power equals `x`.
pub fn complex_alg_all_nth_roots(
  x : ComplexAlgNum,
  n : Int32,
  max_degree~ : Int32 = 32,
) -> Array[ComplexAlgNum] {
  if n <= 0 {
    return []
  }
  if n == 1 {
    return [x]
  }
  let d = qpoly_degree(x.minpoly)
  if d == 1 && rat_is_zero(qpoly_coeff(x.minpoly, 0)) {
    return [complex_alg_of_rat(rat_zero())]
  }
  if d * n > max_degree {
    return []
  }
  let inflated : Array[Rat] = []
  for i in 0..<=d {
    inflated.push(qpoly_coeff(x.minpoly, i))
    if i < d {
      for _k in 1..<n {
        inflated.push(rat_zero())
      }
    }
  }
  let poly_zn = qpoly_normalize(inflated)
  let cands = complex_alg_roots_of(poly_zn)
  let out : Array[ComplexAlgNum] = []
  for pair in cands {
    let (cand, _mult) = pair
    match complex_alg_pow(cand, n, max_degree~) {
      Some(zn) => if complex_alg_eq(zn, x) { out.push(cand) }
      None => ()
    }
  }
  out
}

///|
/// Evaluate `p(z) ∈ Q̄ ⊂ C` for `p ∈ Q[x]` and `z ∈ Q̄`.
pub fn complex_alg_eval_poly(
  p : QPoly,
  z : ComplexAlgNum,
  max_degree~ : Int32 = 32,
) -> ComplexAlgNum? {
  if qpoly_is_zero(p) {
    return Some(complex_alg_of_rat(rat_zero()))
  }
  let mut acc = complex_alg_of_rat(rat_zero())
  let mut i = p.coeffs.length() - 1
  while i >= 0 {
    let prod = match complex_alg_mul(acc, z, max_degree~) {
      Some(v) => v
      None => return None
    }
    acc = match
      complex_alg_add(prod, complex_alg_of_rat(p.coeffs[i]), max_degree~) {
      Some(v) => v
      None => return None
    }
    i = i - 1
  }
  Some(acc)
}
