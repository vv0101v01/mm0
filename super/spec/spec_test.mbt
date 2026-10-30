///| spec 測試：F_p 特徵多項式＋Cayley–Hamilton、Jacobi 收斂、譜流=行列式符號差、

///| 超對稱結構的冪跡恆等式 / 特徵多項式關係 / Witten 指標的形變不變性。

///|
test "[S-D-charpoly] F_p 特徵多項式：係數與 det、tr 一致＋Cayley–Hamilton" {
  let p = 10007
  let f = @core.mk_field(p)
  let r = @core.rng_seed(2026)
  let mut ok_cp = true
  let mut ok_ch = true
  for trial = 0; trial < 15; trial = trial + 1 {
    let n = 1 + @core.rng_below(r, 4)
    let a = @core.mat_build(n, n, (_i, _j) => @core.rng_below(r, p))
    let cp = @spec.charpoly(a, p)
    // c_n = det（符號：(−1)^n det A？det(xI−A) 的常數項 = (−1)^n det A）
    let det = @core.det_mod(a, f)
    let expect_c0 = if n % 2 == 0 { det } else { (p - det) % p }
    if cp[0] != expect_c0 {
      ok_cp = false
    }
    // c_{n−1} = −tr(A)
    let mut tr = 0
    for i = 0; i < n; i = i + 1 {
      tr = (tr + a.data[i * n + i]) % p
    }
    if cp[n - 1] != (p - tr) % p {
      ok_cp = false
    }
    if !@spec.check_cayley_hamilton(a, p) {
      ok_ch = false
    }
  }
  assert_true(ok_cp)
  assert_true(ok_ch)
  // 具體例：[[0,1],[0,0]] 的 charpoly = x²
  let j = @core.mat_from_rows([[0, 1], [0, 0]])
  let cpj = @spec.charpoly(j, p)
  assert_true(cpj[0] == 0 && cpj[1] == 0 && cpj[2] == 1)
}

///|
test "[S-NEG-GeoAlg] 代數重數 ≥ 幾何重數：冪零 Jordan 塊給嚴格不等式" {
  let p = 10007
  let f = @core.mk_field(p)
  // J₂：charpoly = x²（0 的代數重數 2），rank = 1 ⟹ nullity = 1 < 2
  let j = @core.mat_from_rows([[0, 1], [0, 0]])
  let cp = @spec.charpoly(j, p)
  assert_eq(@spec.root_zero_mult(cp), 2)
  assert_eq(@core.rank_mod(j, f), 1)
  // 對角（半單）情形：相等
  let dg = @core.mat_from_rows([[0, 0], [0, 5]])
  let cp2 = @spec.charpoly(dg, p)
  assert_eq(@spec.root_zero_mult(cp2), 1)
  assert_eq(@core.rank_mod(dg, f), 1)
  // 一般不等式 rank ≥ n − mult₀（多個隨機例子）
  let r = @core.rng_seed(9)
  let mut ok = true
  for trial = 0; trial < 10; trial = trial + 1 {
    let a = @core.mat_build(4, 4, (_i, _j) => {
      @core.rng_below(r, 3) * @core.rng_below(r, 2)
    })
    let cp3 = @spec.charpoly(a, p)
    let mult0 = @spec.root_zero_mult(cp3)
    if @core.rank_mod(a, f) < 4 - mult0 {
      ok = false
    }
  }
  assert_true(ok)
}

///|
test "[S-D-jacobi] Jacobi 特徵值解算器：Av = λv 殘差 ＋ 正交性" {
  let r = @core.rng_seed(31415)
  let mut ok_res = true
  let mut ok_orth = true
  for trial = 0; trial < 8; trial = trial + 1 {
    let n = 2 + @core.rng_below(r, 5)
    // 隨機對稱矩陣
    let raw : Array[Array[Double]] = []
    for i = 0; i < n; i = i + 1 {
      let row : Array[Double] = Array::make(n, 0.0)
      for j = 0; j < n; j = j + 1 {
        row[j] = (@core.rng_below(r, 20001) - 10000).to_double() / 100.0
      }
      let _ = raw.push(row)
    }
    let a : Array[Array[Double]] = []
    for i = 0; i < n; i = i + 1 {
      let row : Array[Double] = Array::make(n, 0.0)
      for j = 0; j < n; j = j + 1 {
        row[j] = (raw[i][j] + raw[j][i]) / 2.0
      }
      let _ = a.push(row)
    }
    let (vals, vecs) = @spec.jacobi_eigen(a)
    // 檢查排序
    for i = 1; i < n; i = i + 1 {
      if vals[i] < vals[i - 1] - 0.000000000001 {
        ok_res = false
      }
    }
    // 殘差：‖A v_i − λ_i v_i‖∞
    for k = 0; k < n; k = k + 1 {
      for i = 0; i < n; i = i + 1 {
        let mut s = 0.0
        for j = 0; j < n; j = j + 1 {
          s = s + a[i][j] * vecs[j][k]
        }
        let resid = (s - vals[k] * vecs[i][k]).abs()
        if resid > 0.0000001 {
          ok_res = false
        }
      }
    }
    // 正交性：v_i · v_j = δ_ij
    for k = 0; k < n; k = k + 1 {
      for l = k + 1; l < n; l = l + 1 {
        let mut s = 0.0
        for i = 0; i < n; i = i + 1 {
          s = s + vecs[i][k] * vecs[i][l]
        }
        if s.abs() > 0.00000001 {
          ok_orth = false
        }
      }
    }
  }
  assert_true(ok_res)
  assert_true(ok_orth)
}

///|
test "[S-T-FlowMorse] 譜流 = Morse 指標變化：flow = n₋(H₀) − n₋(H₁)" {
  let r = @core.rng_seed(2718)
  let mut ok = true
  let mut nonzero = 0
  for trial = 0; trial < 10; trial = trial + 1 {
    let n = 3 + @core.rng_below(r, 3)
    let mk = fn() -> Array[Array[Double]] {
      let raw : Array[Array[Double]] = []
      for i = 0; i < n; i = i + 1 {
        let row : Array[Double] = Array::make(n, 0.0)
        for j = 0; j < n; j = j + 1 {
          row[j] = (@core.rng_below(r, 2001) - 1000).to_double() / 50.0
        }
        let _ = raw.push(row)
      }
      let a : Array[Array[Double]] = []
      for i = 0; i < n; i = i + 1 {
        let row : Array[Double] = Array::make(n, 0.0)
        for j = 0; j < n; j = j + 1 {
          row[j] = (raw[i][j] + raw[j][i]) / 2.0
        }
        let _ = a.push(row)
      }
      a
    }
    let h0 = mk()
    let h1 = mk()
    let s0 = @spec.det_sign(h0)
    let s1 = @spec.det_sign(h1)
    if s0 != 0 && s1 != 0 {
      let (v0, _) = @spec.jacobi_eigen(h0)
      let (v1, _) = @spec.jacobi_eigen(h1)
      let neg0 = count_neg(v0)
      let neg1 = count_neg(v1)
      let flow = @spec.spectral_flow(h0, h1, 240)
      if flow != neg0 - neg1 {
        ok = false
      }
      if flow != 0 {
        nonzero = nonzero + 1
      }
    }
  }
  assert_true(ok)
  assert_true(nonzero >= 1) // 至少一個非平凡流
}

///|
fn count_neg(vals : Array[Double]) -> Int32 {
  let mut c = 0
  for v in vals {
    if v < -0.0000001 {
      c = c + 1
    }
  }
  c
}

///|
test "[S-NEG-FlowDet] 反例：flow ≠ ½(sgn det H₁ − sgn det H₀)" {
  // H₀ = diag(−25,−4,20)（n₋=2, det>0）、H₁ = diag(−26,9,13)（n₋=1, det<0）：
  // 恰一次向上穿越 ⟹ flow = +1，但 ½(−1 − 1) = −1。
  // 行列式符號只看 flow 的奇偶（與 sgn det₀ 的乘性），不是譜流本身。
  let h0 : Array[Array[Double]] = [
    [-25.0, 0.0, 0.0],
    [0.0, -4.0, 0.0],
    [0.0, 0.0, 20.0],
  ]
  let h1 : Array[Array[Double]] = [
    [-26.0, 0.0, 0.0],
    [0.0, 9.0, 0.0],
    [0.0, 0.0, 13.0],
  ]
  let flow = @spec.spectral_flow(h0, h1, 100)
  assert_eq(flow, 1)
  let s0 = @spec.det_sign(h0)
  let s1 = @spec.det_sign(h1)
  assert_eq(s0, 1)
  assert_eq(s1, -1)
  assert_eq((s1 - s0) / 2, -1) // ≠ flow = 1 ⟹ 公式被計算否決
  // 奇偶一致性：flow 奇 ⟺ det 變號（此例成立）
  assert_true((flow % 2 + 2) % 2 == 1)
}

///|
test "[S-C-SuperFlow] 超譜流 = 偶流 − 奇流（分塊偶 H 的例子）" {
  // H = diag(A, D)：偶方塊 A（2×2）沿路徑翻一個特徵值符號，奇方塊 D 不動
  let a0 : Array[Array[Double]] = [[-2.0, 0.0], [0.0, 3.0]]
  let a1 : Array[Array[Double]] = [[2.0, 0.0], [0.0, 3.0]]
  let d0 : Array[Array[Double]] = [[1.0, 0.5], [0.5, 1.0]]
  let d1 : Array[Array[Double]] = [[1.0, 0.5], [0.5, 1.0]]
  let sf = @spec.spectral_flow_super(a0, a1, d0, d1, 200)
  assert_eq(sf, 1)
  // 反向流
  let sf2 = @spec.spectral_flow_super(a1, a0, d0, d1, 200)
  assert_eq(sf2, -1)
}

///|
test "[S-T-PowTrace] tr((AB)^k) = tr((BA)^k)（mod p，k=1..4）" {
  let p = 10007
  let r = @core.rng_seed(60)
  let mut ok = true
  for trial = 0; trial < 10; trial = trial + 1 {
    let m = 1 + @core.rng_below(r, 3)
    let n = 1 + @core.rng_below(r, 3)
    let a = @core.mat_build(n, m, (_i, _j) => @core.rng_below(r, p)) // A: m→n（n×m）
    let b = @core.mat_build(m, n, (_i, _j) => @core.rng_below(r, p)) // B: n→m（m×n）
    let ab = @core.mat_mul(a, b, p) // n×n
    let ba = @core.mat_mul(b, a, p) // m×m
    for k = 1; k <= 4; k = k + 1 {
      if @spec.trace_pow(ab, k, p) != @spec.trace_pow(ba, k, p) {
        ok = false
      }
    }
  }
  assert_true(ok)
}

///|
test "[S-C-SUSYtrace] str(H^k) = 0（H = Q²，k ≥ 1）＋ [S-T-ChPolyRel]" {
  let p = 10007
  let r = @core.rng_seed(61)
  let mut ok_str = true
  let mut ok_cp = true
  for trial = 0; trial < 12; trial = trial + 1 {
    let m = 1 + @core.rng_below(r, 4)
    let n = 1 + @core.rng_below(r, 4)
    let d = @core.mat_build(n, m, (_i, _j) => @core.rng_below(r, p))
    let s = @spec.susy_of(d, p)
    for k = 1; k <= 5; k = k + 1 {
      if @spec.susy_str_pow(s, k) != 0 {
        ok_str = false
      }
    }
    if !@spec.check_chpoly_rel(s) {
      ok_cp = false
    }
  }
  assert_true(ok_str)
  assert_true(ok_cp)
}

///|
test "[S-T-Witten] Witten 指標 = m − n：核維數跳動、指標不變" {
  let p = 10007
  let r = @core.rng_seed(62)
  let mut ok_idx = true
  let mut saw_jump = false
  let prev_dims : Array[(Int32, Int32)] = []
  for trial = 0; trial < 10; trial = trial + 1 {
    let m = 2 + @core.rng_below(r, 3)
    let n = 2 + @core.rng_below(r, 3)
    let d0 = @core.mat_build(n, m, (_i, _j) => {
      @core.rng_below(r, 4) * @core.rng_below(r, 2)
    })
    let v = @core.mat_build(n, m, (_i, _j) => 1 + @core.rng_below(r, 3))
    for t = 0; t <= 4; t = t + 1 {
      // D(t) = D0 + t·V（整數矩陣；mod p 評估）
      let dt = @core.mat_add(d0, @core.mat_scale(v, t, p), p)
      let s = @spec.susy_of(dt, p)
      if @spec.susy_index(s) != m - n {
        ok_idx = false
      }
      let dims = @spec.susy_kernel_dims(s)
      let _ = prev_dims.push(dims)
    }
    // 檢查是否有核維數跳動（rank 改變）
    for i = 1; i < prev_dims.length(); i = i + 1 {
      if prev_dims[i] != prev_dims[i - 1] {
        saw_jump = true
      }
    }
  }
  assert_true(ok_idx)
  assert_true(saw_jump)
  // 具體小例：D = [[1,0],[0,t]] 在 t=0 與 t=1：核 (1,1) → (0,0)，指標 = 0 恆定
  let d_t0 = @core.mat_from_rows([[1, 0], [0, 0]])
  let d_t1 = @core.mat_from_rows([[1, 0], [0, 1]])
  assert_eq(@spec.susy_kernel_dims(@spec.susy_of(d_t0, p)), (1, 1))
  assert_eq(@spec.susy_kernel_dims(@spec.susy_of(d_t1, p)), (0, 0))
  assert_eq(@spec.susy_index(@spec.susy_of(d_t0, p)), 0)
  assert_eq(@spec.susy_index(@spec.susy_of(d_t1, p)), 0)
  // 長方形：2×3 的 D：指標 = 3 − 2 = 1（與 D 的內容無關）
  let d2 = @core.mat_from_rows([[1, 2, 3], [4, 5, 6]])
  assert_eq(@spec.susy_index(@spec.susy_of(d2, p)), 1)
  let d3 = @core.mat_from_rows([[0, 0, 0], [0, 0, 0]])
  assert_eq(@spec.susy_index(@spec.susy_of(d3, p)), 1)
}
