///| score 測試：超轉置慣例（由計算釘死）、超跡定理（Λ 上 vs 純域）、

///| 分次 Jacobi、Berezinian 乘法性、Ber∘exp 一階恆等式、展平維度定理。

///|
test "[S-T-st] 超轉置 = 分次反同態：(MN)^st = (−1)^{|M||N|} N^st M^st" {
  // 隨機齊次對（四種奇偶組合）；此測試同時「釘死」st 的號規約定。
  let r = @core.rng_seed(20261029)
  let p = 10007
  let mut all_ok = true
  for trial = 0; trial < 30; trial = trial + 1 {
    let m = 2 + @core.rng_below(r, 2)
    let n = 1 + @core.rng_below(r, 2)
    for px = 0; px < 2; px = px + 1 {
      for py = 0; py < 2; py = py + 1 {
        let x = @score.smat_random(r, m, n, p, px)
        let y = @score.smat_random(r, m, n, p, py)
        let lhs = @score.smat_st(@score.smat_mul(x, y))
        let rhs = if px * py % 2 == 1 {
          @score.smat_scale(
            @score.smat_mul(@score.smat_st(y), @score.smat_st(x)),
            p - 1,
          )
        } else {
          @score.smat_mul(@score.smat_st(y), @score.smat_st(x))
        }
        if !@core.mat_eq_mod(@score.smat_full(lhs), @score.smat_full(rhs), p) {
          all_ok = false
        }
      }
    }
  }
  assert_true(all_ok)
  // 對照：奇矩陣的 st ≠ 普通轉置（號規在奇方塊上生效）
  let r2 = @core.rng_seed(7)
  let x = @score.smat_random(r2, 2, 1, p, 1)
  assert_false(
    @core.mat_eq_mod(
      @score.smat_full(@score.smat_st(x)),
      @core.mat_transpose(@score.smat_full(x)),
      p,
    ),
  )
}

///|
test "[S-T-strCyc] 超跡循環性（正確範圍）：Λ 係數全成立；純域僅偶齊次成立" {
  // (a) Λ 係數（GL(m|n) 的 Λ-點）：str(MN) = str(NM)
  let g = @score.gr_mk(4, 101)
  let r = @core.rng_seed(11)
  let mut ok_a = true
  for trial = 0; trial < 25; trial = trial + 1 {
    let m = 1 + @core.rng_below(r, 2)
    let n = 1 + @core.rng_below(r, 2)
    let x = @score.smatg_random(r, g, m, n)
    let y = @score.smatg_random(r, g, m, n)
    let s1 = @score.smatg_str(@score.smatg_mul(x, y))
    let s2 = @score.smatg_str(@score.smatg_mul(y, x))
    if !@score.gr_eq(s1, s2) {
      ok_a = false
    }
  }
  assert_true(ok_a)
  // (b) 純 F_p：X 偶齊次、Y 任意 ⟹ str(XY) = str(YX)
  let p = 10007
  let mut ok_b = true
  for trial = 0; trial < 30; trial = trial + 1 {
    let m = 1 + @core.rng_below(r, 2)
    let n = 1 + @core.rng_below(r, 2)
    let x = @score.smat_random(r, m, n, p, 0)
    let y0 = @score.smat_random(r, m, n, p, 0)
    let y1 = @score.smat_random(r, m, n, p, 1)
    let y = @score.smat_add(y0, y1)
    if @score.smat_str(@score.smat_mul(x, y)) !=
      @score.smat_str(@score.smat_mul(y, x)) {
      ok_b = false
    }
  }
  assert_true(ok_b)
}

///|
test "[S-NEG-strPlain] 純域反例：混合奇偶的 M,N 可使 str(MN) ≠ str(NM)" {
  // 混合 M = 偶+奇、N = 偶+奇；超跡的結合代數跡性質需要奇係數（Λ），
  // 純 F_p 上不成立——本測試以搜尋構造反例。
  let p = 10007
  let r = @core.rng_seed(55)
  let mut found = false
  for trial = 0; trial < 200 && !found; trial = trial + 1 {
    let m = 1
    let n = 1
    let x = @score.smat_add(
      @score.smat_random(r, m, n, p, 0),
      @score.smat_random(r, m, n, p, 1),
    )
    let y = @score.smat_add(
      @score.smat_random(r, m, n, p, 0),
      @score.smat_random(r, m, n, p, 1),
    )
    if @score.smat_str(@score.smat_mul(x, y)) !=
      @score.smat_str(@score.smat_mul(y, x)) {
      found = true
    }
  }
  assert_true(found)
}

///|
test "[S-T-strComm] str([X,Y]_s) = 0（齊次 X,Y ∈ gl(m|n) over F_p）" {
  let r = @core.rng_seed(13)
  let p = 10007
  let mut ok = true
  for trial = 0; trial < 25; trial = trial + 1 {
    let m = 1 + @core.rng_below(r, 2)
    let n = 1 + @core.rng_below(r, 2)
    for a = 0; a < 2; a = a + 1 {
      for b = 0; b < 2; b = b + 1 {
        let x = @score.smat_random(r, m, n, p, a)
        let y = @score.smat_random(r, m, n, p, b)
        if @score.smat_str(@score.smat_sbr(x, y, a, b)) != 0 {
          ok = false
        }
      }
    }
  }
  assert_true(ok)
}

///|
test "[S-T-Jacobi] gl(m|n) 分次 Jacobi 恆等式（全部 8 種奇偶組合）" {
  let r = @core.rng_seed(17)
  let p = 10007
  let mut ok = true
  for trial = 0; trial < 12; trial = trial + 1 {
    let m = 1 + @core.rng_below(r, 2)
    let n = 1 + @core.rng_below(r, 2)
    for a = 0; a < 2; a = a + 1 {
      for b = 0; b < 2; b = b + 1 {
        for c = 0; c < 2; c = c + 1 {
          let xx = @score.smat_random(r, m, n, p, a)
          let yy = @score.smat_random(r, m, n, p, b)
          let zz = @score.smat_random(r, m, n, p, c)
          // 內括號的奇偶 = 兩元素奇偶之和（mod 2）
          let p1 = (b + c) % 2
          let p2 = (c + a) % 2
          let p3 = (a + b) % 2
          let j1 = @score.smat_sbr(xx, @score.smat_sbr(yy, zz, b, c), a, p1)
          let j2 = @score.smat_sbr(yy, @score.smat_sbr(zz, xx, c, a), b, p2)
          let j3 = @score.smat_sbr(zz, @score.smat_sbr(xx, yy, a, b), c, p3)
          let s1 = if a * c % 2 == 1 {
            @score.smat_scale(j1, p - 1)
          } else {
            j1
          }
          let s2 = if b * a % 2 == 1 {
            @score.smat_scale(j2, p - 1)
          } else {
            j2
          }
          let s3 = if c * b % 2 == 1 {
            @score.smat_scale(j3, p - 1)
          } else {
            j3
          }
          let tot = @score.smat_add(@score.smat_add(s1, s2), s3)
          if !@core.mat_is_zero(@score.smat_full(tot)) {
            ok = false
          }
        }
      }
    }
  }
  assert_true(ok)
}

///|
test "[S-D-Gr] Grassmann 引擎：反對稱、平方零、結合律、交換偶部分" {
  let g = @score.gr_mk(5, 101)
  let t1 = @score.gr_gen(g, 1)
  let t2 = @score.gr_gen(g, 2)
  // θ₁θ₂ = −θ₂θ₁
  let p1 = @score.gr_mul(g, t1, t2)
  let p2 = @score.gr_mul(g, t2, t1)
  assert_true(@score.gr_eq(p1, @score.gr_scale(g, p2, 100)))
  // θ₁² = 0
  assert_true(@score.gr_eq(@score.gr_mul(g, t1, t1), @score.gr_zero(g)))
  // 結合律（隨機三元素）
  let r = @core.rng_seed(5)
  let mut ok = true
  for trial = 0; trial < 20; trial = trial + 1 {
    let x = @score.gr_zero(g)
    let y = @score.gr_zero(g)
    let z = @score.gr_zero(g)
    for i = 0; i < @score.gr_size(g); i = i + 1 {
      x[i] = @core.rng_below(r, 101)
      y[i] = @core.rng_below(r, 101)
      z[i] = @core.rng_below(r, 101)
    }
    let lhs = @score.gr_mul(g, @score.gr_mul(g, x, y), z)
    let rhs = @score.gr_mul(g, x, @score.gr_mul(g, y, z))
    if !@score.gr_eq(lhs, rhs) {
      ok = false
    }
  }
  assert_true(ok)
  // 偶部分彼此交換
  let e1 = @score.gr_mul(g, t1, t2)
  let e2 = @score.gr_mul(g, @score.gr_gen(g, 3), @score.gr_gen(g, 4))
  assert_true(@score.gr_eq(@score.gr_mul(g, e1, e2), @score.gr_mul(g, e2, e1)))
  // 逆元素：x·x⁻¹ = 1（隨機么正偶元素）
  let mut ok_inv = true
  for trial = 0; trial < 15; trial = trial + 1 {
    let x = @score.gr_zero(g)
    x[0] = 1 + @core.rng_below(r, 100)
    for i = 1; i < @score.gr_size(g); i = i + 1 {
      x[i] = @core.rng_below(r, 101)
    }
    let xi = @score.gr_inv(g, x)
    if !@score.gr_eq(@score.gr_mul(g, x, xi), @score.gr_one(g)) {
      ok_inv = false
    }
  }
  assert_true(ok_inv)
}

///|
test "[S-T-FlatSym] 展平對稱性：Sym(V₀)⊗Λ(V₁) 的維度 = 超交換單項式計數" {
  // m 偶 + n 奇生成元的次數 d 單項式數 = Σ_j C(n,j)·C(m+d−j−1, d−j)
  // （n=0 時 = Sym 維度；m=0 時 = Λ 維度——兩種對稱被同一引擎展平）
  let mut ok = true
  for m = 0; m <= 3; m = m + 1 {
    for n = 0; n <= 3; n = n + 1 {
      for d = 0; d <= 6; d = d + 1 {
        let brute = @score.count_monomials(m, n, d)
        let mut closed = 0
        for j = 0; j <= n; j = j + 1 {
          if d - j >= 0 {
            closed = closed +
              @algebra.int_binom(n, j) * @algebra.int_binom(m + d - j - 1, d - j)
          }
        }
        if brute != closed {
          ok = false
        }
      }
    }
  }
  assert_true(ok)
  // 關鍵案例：Λ^d(V) = Sym^d(ΠV)：m=0
  assert_eq(@score.count_monomials(0, 4, 2), 6)
  assert_eq(@score.count_monomials(0, 4, 3), 4)
  // Sym 維度：n=0
  assert_eq(@score.count_monomials(3, 0, 4), 15)
}

///|
test "[S-P-SuperBinom] 超二項式：(x+θ)^d = x^d + d·x^{d−1}θ（x 偶、θ 奇）" {
  let g = @score.gr_mk(4, 101)
  // x = 1 + θ₁θ₂（偶么元），θ = θ₃
  let t12 = @score.gr_mul(g, @score.gr_gen(g, 1), @score.gr_gen(g, 2))
  let x = @score.gr_add(g, @score.gr_one(g), t12)
  let th = @score.gr_gen(g, 3)
  let d = 5
  fn pow(base : Array[Int32], e : Int32) -> Array[Int32] {
    let mut acc = @score.gr_one(g)
    for i = 0; i < e; i = i + 1 {
      acc = @score.gr_mul(g, acc, base)
    }
    acc
  }
  let x5 = pow(x, d)
  let x4 = pow(x, 4)
  let rhs = @score.gr_add(
    g,
    x5,
    @score.gr_scale(g, @score.gr_mul(g, x4, th), d),
  )
  let lhs = pow(@score.gr_add(g, x, th), d)
  assert_true(@score.gr_eq(lhs, rhs))
}

///|
test "[S-T-Ber] Berezinian 乘法性：Ber(MN) = Ber(M)·Ber(N)（Λ₄ over F₁₀₁）" {
  let g = @score.gr_mk(4, 101)
  let r = @core.rng_seed(4242)
  let mut ok = true
  let mut checked = 0
  for trial = 0; trial < 20; trial = trial + 1 {
    let m = 1 + @core.rng_below(r, 2)
    let n = 1 + @core.rng_below(r, 2)
    let x = @score.smatg_random(r, g, m, n)
    let y = @score.smatg_random(r, g, m, n)
    let bxy = @score.smatg_ber(@score.smatg_mul(x, y))
    let bx = @score.smatg_ber(x)
    let by = @score.smatg_ber(y)
    if bxy is Some(v1) {
      if bx is Some(v2) {
        if by is Some(v3) {
          checked = checked + 1
          if !@score.gr_eq(v1, @score.gr_mul(g, v2, v3)) {
            ok = false
          }
        }
      }
    }
  }
  assert_true(ok)
  assert_true(checked >= 10) // 足夠多的可逆樣本
}

///|
test "[S-T-BerBranch] 兩個 Schur 分支給出相同 Ber（Λ 係數下的超恆等式）" {
  let g = @score.gr_mk(4, 101)
  let r = @core.rng_seed(99)
  let mut ok = true
  for trial = 0; trial < 12; trial = trial + 1 {
    let x = @score.smatg_random(r, g, 2, 2)
    let b1 = @score.smatg_ber(x)
    let b2 = @score.smatg_ber_abranch(x)
    if b1 is Some(v1) {
      if b2 is Some(v2) {
        if !@score.gr_eq(v1, v2) {
          ok = false
        }
      }
    } else {
      ok = false
    }
  }
  assert_true(ok)
}

///|
test "[S-C-BerDiag] Ber(diag(A,D)) = det(A)·det(D)⁻¹：奇體積以負號計入" {
  let g = @score.gr_mk(4, 101)
  let r = @core.rng_seed(31)
  let x = @score.smatg_random(r, g, 2, 2)
  let diag = @score.smatg_diagonalize(x)
  let ber = @score.smatg_ber(diag)
  let detA = @score.even_det(g, x.a)
  let detD = @score.even_det(g, x.d)
  if ber is Some(v) {
    assert_true(@score.gr_eq(v, @score.gr_mul(g, detA, @score.gr_inv(g, detD))))
  } else {
    assert_true(false)
  }
}

///|
test "[S-T-BerExp1] Ber(I+εX) = 1 + ε·str(X)（ε = θ₁θ₂ 偶冪零；Ber∘exp 的一階版）" {
  let p = 101
  let g = @score.gr_mk(2, p)
  // ε = θ₀θ₁（偶、ε² = 0）；X = s·I ⟹ str(X) = s·(m−n)
  let eps = @score.gr_mul(g, @score.gr_gen(g, 0), @score.gr_gen(g, 1))
  let r = @core.rng_seed(77)
  let mut ok = true
  for trial = 0; trial < 15; trial = trial + 1 {
    let m = 1 + @core.rng_below(r, 2)
    let n = 1 + @core.rng_below(r, 2)
    let s = @core.rng_below(r, p)
    let mi = @score.smatg_scalar_eps(g, m, n, eps, s)
    let ber = @score.smatg_ber(mi)
    if ber is Some(v) {
      let expect = @score.gr_add(
        g,
        @score.gr_one(g),
        @score.gr_scale(g, eps, (s * (m - n) % p + p) % p),
      )
      if !@score.gr_eq(v, expect) {
        ok = false
      }
    } else {
      ok = false
    }
  }
  assert_true(ok)
}

///|
test "[S-NEG-BerField] 純域上 Schur-Ber 非乘性：搜尋找到反例" {
  // k=0（純 F_p）但 b、c 方塊放非零 body（= 偶元素落在奇位置，破壞齊次性）：
  // 此時 Ber = det(A)det(D−CA⁻¹B)⁻¹ 對一般 M 不再乘性——
  // 「超行列式必須活在有奇方向的環上」的可計算反例。
  let p = 101
  let g = @score.gr_mk(0, p)
  let r = @core.rng_seed(123)
  fn body(v : Int32) -> Array[Int32] {
    let e = @score.gr_zero(g)
    e[0] = v % p
    e
  }
  let mut found = false
  for trial = 0; trial < 300 && !found; trial = trial + 1 {
    let m = 2
    let n = 1
    // 隨機 2×2 / 1×1 body 方塊
    let a : Array[Array[Array[Int32]]] = [
      [body(1 + @core.rng_below(r, p - 1)), body(@core.rng_below(r, p))],
      [body(@core.rng_below(r, p)), body(1 + @core.rng_below(r, p - 1))],
    ]
    let d : Array[Array[Array[Int32]]] = [[body(1 + @core.rng_below(r, p - 1))]]
    let b : Array[Array[Array[Int32]]] = [
      [body(@core.rng_below(r, p))],
      [body(@core.rng_below(r, p))],
    ]
    let c : Array[Array[Array[Int32]]] = [
      [body(@core.rng_below(r, p)), body(@core.rng_below(r, p))],
    ]
    let x = @score.smatg_of(m, n, g, a, b, c, d)
    let a2 : Array[Array[Array[Int32]]] = [
      [body(1 + @core.rng_below(r, p - 1)), body(@core.rng_below(r, p))],
      [body(@core.rng_below(r, p)), body(1 + @core.rng_below(r, p - 1))],
    ]
    let d2 : Array[Array[Array[Int32]]] = [
      [body(1 + @core.rng_below(r, p - 1))],
    ]
    let b2 : Array[Array[Array[Int32]]] = [
      [body(@core.rng_below(r, p))],
      [body(@core.rng_below(r, p))],
    ]
    let c2 : Array[Array[Array[Int32]]] = [
      [body(@core.rng_below(r, p)), body(@core.rng_below(r, p))],
    ]
    let y = @score.smatg_of(m, n, g, a2, b2, c2, d2)
    let bxy = @score.smatg_ber(@score.smatg_mul(x, y))
    let bx = @score.smatg_ber(x)
    let by = @score.smatg_ber(y)
    if bxy is Some(v1) {
      if bx is Some(v2) {
        if by is Some(v3) {
          if !@score.gr_eq(v1, @score.gr_mul(g, v2, v3)) {
            found = true
          }
        }
      }
    }
  }
  assert_true(found)
}
