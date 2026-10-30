///|
fn require_square_int64(a : Array[Array[Int64]]) -> Int32? {
  let n = a.length()
  for row in a {
    if row.length() != n {
      return None
    }
    for x in row {
      if !(x > -400000000000000L && x < 400000000000000L) {
        return None
      }
    }
  }
  Some(n)
}

///|
fn all_permutations(n : Int32, cap : Int32) -> Array[@sym.Perm]? {
  let group = @sym.PermGroup::symmetric(n)
  if group.order() > cap.to_int64() {
    return None
  }
  Some(group.elements(cap))
}

///|
/// 一個指派在熱帶半環中的成本（普通整數和）。
pub fn assignment_cost(a : Array[Array[Int64]], p : @sym.Perm) -> Int64? {
  let n = match require_square_int64(a) {
    None => return None
    Some(n) => n
  }
  if p.size() != n {
    return None
  }
  let mut sum = 0L
  for i in 0..<n {
    sum = sum + a[i][p.apply(i)]
  }
  Some(sum)
}

///|
/// 所有達到 semiring `trop_det` 的指派，以 symlib 置換表達。
pub fn tropical_optimal_assignments(
  a : Array[Array[Int64]],
  cap : Int32,
) -> Array[@sym.Perm]? {
  let n = match require_square_int64(a) {
    None => return None
    Some(n) => n
  }
  let perms = match all_permutations(n, cap) {
    None => return None
    Some(ps) => ps
  }
  let best = @strop.trop_det(a)
  let out : Array[@sym.Perm] = []
  for p in perms {
    if assignment_cost(a, p) == Some(best) {
      out.push(p)
    }
  }
  Some(out)
}

///|
/// 同時重標行與列仍保矩陣的置換：
/// `a[p(i)][p(j)] = a[i][j]`。這是完全二部加權圖在對角
/// 置換作用下的穩定子；它以共軛作用在指派集合上。
pub fn tropical_matrix_symmetries(
  a : Array[Array[Int64]],
  cap : Int32,
) -> Array[@sym.Perm]? {
  let n = match require_square_int64(a) {
    None => return None
    Some(n) => n
  }
  let perms = match all_permutations(n, cap) {
    None => return None
    Some(ps) => ps
  }
  let out : Array[@sym.Perm] = []
  for p in perms {
    let mut ok = true
    for i in 0..<n {
      for j in 0..<n {
        if a[p.apply(i)][p.apply(j)] != a[i][j] {
          ok = false
        }
      }
    }
    if ok {
      out.push(p)
    }
  }
  Some(out)
}

///|
fn rat_of_int64(x : Int64) -> @algebra.Rat {
  @algebra.rat_big_int(BigInt::from_string(x.to_string()))
}

///|
/// 普通（非熱帶）永久式，以精確有理算術和 symlib 全置換枚舉計算。
pub fn exact_permanent_int64(
  a : Array[Array[Int64]],
  cap : Int32,
) -> @algebra.Rat? {
  let n = match require_square_int64(a) {
    None => return None
    Some(n) => n
  }
  let perms = match all_permutations(n, cap) {
    None => return None
    Some(ps) => ps
  }
  let mut total = @algebra.rat_zero()
  for p in perms {
    let mut term = @algebra.rat_one()
    for i in 0..<n {
      term = @algebra.rat_mul(term, rat_of_int64(a[i][p.apply(i)]))
    }
    total = @algebra.rat_add(total, term)
  }
  Some(total)
}

///|
/// 普通精確行列式，交由 cubical 精確 algebra 的 QMat 計算。
pub fn exact_determinant_int64(a : Array[Array[Int64]]) -> @algebra.Rat? {
  let n = match require_square_int64(a) {
    None => return None
    Some(n) => n
  }
  let rows : Array[Array[@algebra.Rat]] = []
  for i in 0..<n {
    let row : Array[@algebra.Rat] = []
    for j in 0..<n {
      row.push(rat_of_int64(a[i][j]))
    }
    rows.push(row)
  }
  Some(@algebra.qmat_det(@algebra.qmat_from_rows(rows)))
}

///|
fn is_prime_i32(p : Int32) -> Bool {
  guard p >= 2 else { return false }
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
fn bigint_padic_valuation(x0 : BigInt, p : Int32) -> Int32 {
  let bp = BigInt::from_int(p)
  let mut x = @algebra.bigint_abs(x0)
  let mut count = 0
  while x % bp == 0N {
    x = x / bp
    count = count + 1
  }
  count
}

///|
/// 有理數的 p-進賦值；零回傳 None（熱帶像為 +∞）。
pub fn rat_padic_valuation(r : @algebra.Rat, p : Int32) -> Int32? {
  // 非素數 ⇒ 沒有定義（回 None，不再中止）
  if !is_prime_i32(p) {
    return None
  }
  if @algebra.rat_is_zero(r) {
    return None
  }
  Some(bigint_padic_valuation(r.num, p) - bigint_padic_valuation(r.den, p))
}

///|
/// QPoly 以 p-進賦值熱帶化為 semiring UniPoly。
/// 零係數送到 semiring 的熱帶 +∞ 哨兵。
pub fn qpoly_tropicalize_padic(
  poly : @algebra.QPoly,
  p : Int32,
) -> Result[@strop.UniPoly, String] {
  if !is_prime_i32(p) {
    return Err("qpoly_tropicalize_padic: p = \{p} 不是素數")
  }
  let degree = @algebra.qpoly_degree(poly)
  if degree < 0 {
    return Ok(@strop.UniPoly::new([@semialg.trop_inf]))
  }
  let coeffs : Array[Int32] = []
  for i in 0..<(degree + 1) {
    match rat_padic_valuation(@algebra.qpoly_coeff(poly, i), p) {
      Some(v) => coeffs.push(v)
      None => coeffs.push(@semialg.trop_inf)
    }
  }
  Ok(@strop.UniPoly::new(coeffs))
}

///|
/// 熱帶橋接穿越檢查：
/// - 2×2 區塊矩陣有 8 個同時對稱、4 個最佳指派，且最佳集在
///   對稱共軛下封閉；
/// - 精確永久式/行列式由 Q 代數重算；
/// - (x-2)(x-4) 的 2-進熱帶根重數列是兩因子的併合 [1,2]。
pub fn check_tropical_bridges() -> Bool {
  let blocks : Array[Array[Int64]] = [
    [0L, 0L, 5L, 5L],
    [0L, 0L, 5L, 5L],
    [5L, 5L, 0L, 0L],
    [5L, 5L, 0L, 0L],
  ]
  let (symmetries, optima) = match (
    tropical_matrix_symmetries(blocks, 32),
    tropical_optimal_assignments(blocks, 32),
  ) {
    (Some(sy), Some(op)) => (sy, op)
    _ => return false
  }
  if symmetries.length() != 8 || optima.length() != 4 {
    return false
  }
  let best = @strop.trop_det(blocks)
  for s in symmetries {
    for q in optima {
      let conjugated = s.compose(q).compose(s.inverse())
      if assignment_cost(blocks, conjugated) != Some(best) {
        return false
      }
    }
  }
  let small : Array[Array[Int64]] = [[1L, 2L], [3L, 4L]]
  let perm = match exact_permanent_int64(small, 4) {
    None => return false
    Some(v) => v
  }
  let det = match exact_determinant_int64(small) {
    None => return false
    Some(v) => v
  }
  if !@algebra.rat_eq(perm, @algebra.rat_int(10)) ||
    !@algebra.rat_eq(det, @algebra.rat_int(-2)) {
    return false
  }
  let f = @algebra.qpoly_root_factor(@algebra.rat_int(2))
  let g = @algebra.qpoly_root_factor(@algebra.rat_int(4))
  let product = @algebra.qpoly_mul(f, g)
  let trop = match qpoly_tropicalize_padic(product, 2) {
    Ok(v) => v
    Err(_) => return false
  }
  let roots = @strop.sort_rats(trop.roots())
  roots.length() == 2 &&
  roots[0].n == 1L &&
  roots[0].d == 1L &&
  roots[1].n == 2L &&
  roots[1].d == 1L &&
  verify_kapranov_tropical_laurent_bridge()
}

///|
/// **Kapranov–Berkovich Non-Archimedean Valuation Bridge (`@scheme` ↔ `@strop`)**:
/// Connects the `t`-adic Discrete Valuation `v_t : Q((t))^× -> Z` used in `@scheme`'s
/// Valuative Criterion of Properness directly to `@strop`'s Min-Plus Tropical
/// Polynomial roots:
/// For `P(t)(u) = t^3 + t^1 * u + t^2 * u^2 ∈ Q((t))[u]`, its tropicalization in
/// `@strop.UniPoly` is `min(3, 1 + w, 2 + 2*w)` with tropical bend roots `{-1, 2}`;
/// substituting the Kapranov lift `u(t) = -t^{-1}` cancels leading valuations so
/// `v_t(P(t)(-t^{-1}))` jumps strictly from `0` to `3`, and `u(t)` extends uniquely
/// across `P^1_Q = scheme_projective_space(1)`!
pub fn verify_kapranov_tropical_laurent_bridge() -> Bool {
  let tp = @strop.UniPoly::new([3, 1, 2])
  let troots = tp.roots()
  if troots.length() != 2 ||
    troots[0] != @strop.Rat::of_int(-1) ||
    troots[1] != @strop.Rat::of_int(2) {
    return false
  }
  let s_neg1 = @scheme.laurent_monomial(-1)
  let s_pos2 = @scheme.laurent_monomial(2)
  if @scheme.laurent_mul(s_neg1, s_pos2).val != 1 {
    return false
  }
  let minus_inv_t = @scheme.laurent_sub(
    @scheme.laurent_const(@algebra.rat_zero()),
    s_neg1,
  )
  let term0 = @scheme.laurent_monomial(3)
  let term1 = @scheme.laurent_mul(@scheme.laurent_monomial(1), minus_inv_t)
  let term2 = @scheme.laurent_mul(
    @scheme.laurent_monomial(2),
    @scheme.laurent_mul(minus_inv_t, minus_inv_t),
  )
  let residual = @scheme.laurent_add(term0, @scheme.laurent_add(term1, term2))
  let p1_ext = @scheme.valuative_extension_classes_for_arc(
    @scheme.scheme_projective_space(1),
    0,
    [minus_inv_t],
  )
  residual.val == 3 && p1_ext == 1
}
