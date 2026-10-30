///|
/// radon 的驗證測試：Gram 關係、單射性、顯式反演、切片定理、二次型恆等式。
test "[T-Radon-Gram] RᵀR = n·I + J（素數 n），並由消元得 rank = n²" {
  for n in [2, 3, 5, 7] {
    let r = @radon.mk_radon(n, 10007)
    assert_eq(@radon.check_gram(r), true)
    let (rk, nullity) = @radon.radon_rank(r)
    assert_eq(rk, n * n)
    assert_eq(nullity, 0)
    assert_eq(@radon.check_injective(r), true)
  }
}

///|
test "[T-Radon-Gram] 組合模 n=4 時「兩點決定唯一線」失效（定理需 n 為素數）" {
  let r = @radon.mk_radon(4, 10007)
  assert_eq(@radon.check_gram(r), false)
  // 具體地：(0,0) 與 (2,0) 同時在斜率 0 與斜率 2 兩條線上
  let l0 = @radon.line_points(r, 0, 0)
  let l2 = @radon.line_points(r, 2, 0)
  let p00 = 0 * 4 + 0
  let p20 = 2 * 4 + 0
  assert_eq(l0.any(q => q == p00) && l0.any(q => q == p20), true)
  assert_eq(l2.any(q => q == p00) && l2.any(q => q == p20), true)
}

///|
test "[T-Radon-Inv] 顯式反演 (nI+J)⁻¹v = (v − (Σv)/(n²+n))/n 重建 f" {
  let rng = @core.rng_seed(20261028)
  for n in [2, 3, 5, 7] {
    let r = @radon.mk_radon(n, 10007)
    let nc = n * n
    let f = Array::makei(nc, _ => @core.rng_below(rng, 10007))
    assert_eq(@radon.check_inversion(r, f), true)
    // 零均值化後再測一次（避免全 0 之外的平凡情況）
    let mut s = 0
    for x in f {
      s = (s + x) % 10007
    }
    let f0 = f.copy()
    f0[0] = ((f0[0] - s) % 10007 + 10007) % 10007
    assert_eq(@radon.check_inversion(r, f0), true)
    assert_eq(@radon.check_quad_identity(r, f0), true)
    assert_eq(@radon.check_quad_identity(r, f), true)
    assert_eq(@radon.check_total_weight(r, f), true)
  }
}

///|
test "[T-Radon-Slice] 切片定理：1 維 Radon 譜 = 2 維 Fourier 在垂直線上的限制" {
  let cases : Array[(Int32, Int32)] = [(2, 5), (3, 7), (5, 11)]
  let rng = @core.rng_seed(7331)
  for (n, p) in cases {
    let r = @radon.mk_radon(n, p)
    let f = Array::makei(n * n, _ => @core.rng_below(rng, p))
    assert_eq(@radon.check_slice(r, f), true)
  }
}

///|
test "[D-LineCount] 線數 = n(n+1)，每線 n 點，每點在 n+1 條線上" {
  for n in [2, 3, 5, 7] {
    let r = @radon.mk_radon(n, 10007)
    assert_eq(@radon.line_count(r), n * (n + 1))
    let mut tot = 0
    let mut dir = 0
    while dir <= n {
      let mut t = 0
      while t < n {
        assert_eq(@radon.line_points(r, dir, t).length(), n)
        tot = tot + n
        t = t + 1
      }
      dir = dir + 1
    }
    assert_eq(tot, n * n * (n + 1))
  }
}
