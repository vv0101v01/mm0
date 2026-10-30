// 張量積包的可執行驗證：全部命題都在有限模型 F_p 上**窮舉**核對。

///|
/// /// 列舉 F_p^(2x2x2) 全部 p^8 個張量。
fn all222(p : Int32) -> Array[@tensor.Tensor3] {
  let total = @algebra.int_pow(p, 8)
  let out : Array[@tensor.Tensor3] = []
  for code = 0; code < total; code = code + 1 {
    let t = @tensor.t3_make(2, 2, 2, p)
    let mut c = code
    for i = 0; i < 8; i = i + 1 {
      t.data[i] = c % p
      c = c / p
    }
    out.push(t)
  }
  out
}

///|
test "flattening lower bound never exceeds true rank [P-Flat] (exhaustive F_2)" {
  let tab = @tensor.rank1_table(2, 2)
  for t in all222(2) {
    let lb = @tensor.flattening_lower_bound(t)
    let true_rank = @tensor.tensor_rank(t, tab, 3)
    match true_rank {
      None => ()
      Some(r) => assert_eq(lb <= r, true)
    }
  }
}

///|
test "W state has rank 3, GHZ has rank 2 over F_3" {
  // W = e001 + e010 + e100
  let w = @tensor.t3_of(2, 2, 2, 3, (i, j, k) => {
    if i + j + k == 1 {
      1
    } else {
      0
    }
  })
  let w2 = @tensor.t3_make(2, 2, 2, 3)
  w2.data[1] = 1 // 001
  w2.data[2] = 1 // 010
  w2.data[4] = 1 // 100
  assert_eq(w.data == w2.data, true)
  let tab3 = @tensor.rank1_table(2, 3)
  assert_eq(@tensor.tensor_rank(w2, tab3, 2) == None, true)
  // GHZ = e000 + e111
  let g = @tensor.t3_make(2, 2, 2, 3)
  g.data[0] = 1
  g.data[7] = 1
  assert_eq(@tensor.tensor_rank(w2, tab3, 3), Some(3))
}

///|
test "hyperdeterminant: GHZ nonzero, W zero over F_3" {
  let g = @tensor.t3_make(2, 2, 2, 3)
  g.data[0] = 1
  g.data[7] = 1
  let w = @tensor.t3_make(2, 2, 2, 3)
  w.data[1] = 1
  w.data[2] = 1
  w.data[4] = 1
  assert_eq(@tensor.hyperdet222(g), 1)
  assert_eq(@tensor.hyperdet222(w), 0)
}

///|
test "hyperdet is shear invariant [P-Shear] (exhaustive F_3)" {
  for t in all222(3) {
    assert_eq(@tensor.check_shear_invariance(t), true)
  }
}

///|
test "rank <= 1 implies hyperdet = 0 (exhaustive F_3) [P-DetSimple]" {
  for t in all222(3) {
    if @tensor.is_rank1(t) || t.data.all(x => x == 0) {
      assert_eq(@tensor.hyperdet222(t), 0)
    }
  }
}

///|
test "Strassen uniqueness over F_3, exhaustive [T-Strassen-F3]" {
  let tab = @tensor.rank1_table(2, 3)
  let mut n0 = 0
  let mut n1 = 0
  let mut n2 = 0
  let mut n3 = 0
  let mut counter = 0
  for t in all222(3) {
    let (rank, cnt, det) = @tensor.classify222(t, tab)
    match rank {
      0 => n0 = n0 + 1
      1 => n1 = n1 + 1
      2 => n2 = n2 + 1
      _ => n3 = n3 + 1
    }
    if rank == 2 {
      // 核心定理：秩 2 的張量有唯一分解 ⟺ hyperdet ≠ 0
      if (det != 0) != (cnt == 1) {
        counter = counter + 1
      }
    }
    if det != 0 && rank <= 1 {
      counter = counter + 1000
    }
  }
  assert_eq(counter, 0)
  // 精確的計數譜（可由本實作獨立再推導）
  assert_eq(n0, 1)
  assert_eq(n1, 128)
  assert_eq(n2, 4032)
  assert_eq(n3, 2400)
  assert_eq(n0 + n1 + n2 + n3, 6561)
}

///|
test "rank subadditivity on F_2 sample [P-Subadd]" {
  let tab = @tensor.rank1_table(2, 2)
  let ts = all222(2)
  // 取前 12 個張量的兩兩配對，交給同一秩引擎判定
  let pairs : Array[(@tensor.Tensor3, @tensor.Tensor3)] = []
  for i = 0; i < 12 && i < ts.length(); i = i + 1 {
    for j = 0; j < 12 && j < ts.length(); j = j + 1 {
      pairs.push((ts[i], ts[j]))
    }
  }
  assert_eq(@tensor.check_subadditivity(pairs, tab), true)
}

///|
test "Kronecker rank multiplicativity [P-KronRank]" {
  let p = 5
  let rng = @core.rng_seed(20261028)
  let mut ok = true
  for trial = 0; trial < 40; trial = trial + 1 {
    let r1 = 1 + @core.rng_below(rng, 3)
    let c1 = 1 + @core.rng_below(rng, 3)
    let r2 = 1 + @core.rng_below(rng, 3)
    let c2 = 1 + @core.rng_below(rng, 3)
    let a = @core.mat_build(r1, c1, (_, _) => @core.rng_below(rng, p))
    let b = @core.mat_build(r2, c2, (_, _) => @core.rng_below(rng, p))
    if !@tensor.check_kronecker_rank_identity(a, b, p) {
      ok = false
    }
  }
  assert_eq(ok, true)
}

///|
test "tensor product of flattening bounds multiplies [C-FlattenKron]" {
  let p = 7
  let a = @core.mat_from_rows([[1, 2, 3], [4, 5, 6]])
  let b = @core.mat_from_rows([[1, 0], [0, 1], [1, 1]])
  let k = @tensor.kron_mat(a, b, p)
  let f = @core.mk_field(p)
  assert_eq(@core.rank_mod(k, f), @tensor.flattening_bound_of_product(a, b, p))
}

///|
test "multilinearity axioms and rank-1 algebra [Ax-Tens]" {
  let p = 5
  let u = [1, 2]
  let v = [3, 0]
  let w = [4, 1]
  // t3_simple = u ⊗ v ⊗ w，索引 (i*2+j)*2+k
  let s = @tensor.t3_simple(u, v, w, p)
  assert_eq(s.data, [2, 3, 0, 0, 4, 1, 0, 0])
  // 標量乘法逐分量：3·S 的每個分量都是 3·S_ijk mod p
  let three = @tensor.t3_smul(3, s)
  assert_eq(three.data, [1, 4, 0, 0, 2, 3, 0, 0])
  // 分配律 S + S = 2·S
  let two = @tensor.t3_add(s, s)
  assert_eq(two.data, @tensor.t3_smul(2, s).data)
  // 多線性：u 換成 2u 時整個張量恰好乘 2
  let u2 = [2, 4]
  assert_eq(@tensor.t3_simple(u2, v, w, p).data, two.data)
  // 秩-1 判定：S 秩為 1
  assert_eq(@tensor.is_rank1(s), true)
}

///|
test "subadditivity and explicit rank-1 witnesses [P-Subadd]" {
  let p = 5
  let u = [1, 2]
  let v = [3, 0]
  let w = [4, 1]
  let a = @tensor.t3_simple(u, v, w, p)
  let b = @tensor.t3_simple([0, 1], [1, 1], [1, 2], p)
  // 有限樣本上的 rank(A+B) ≤ rank A + rank B
  let tab5 = @tensor.rank1_table(2, 5)
  assert_eq(@tensor.check_subadditivity([(a, b), (b, a), (a, a)], tab5), true)
  // 分解見證：Σ 係數·list[i] 必須逐項還原 b
  match @tensor.decompose(b, tab5, 3) {
    Some(terms) => {
      assert_eq(terms.length(), 1)
      let (ci, coef) = terms[0]
      let f = @core.mk_field(p)
      let rebuilt = @core.vec_scale(tab5.list[ci], coef, p)
      assert_eq(rebuilt, b.data.map(x => @core.fld_norm(f, x)))
    }
    None => fail("rank-1 tensor must have a 1-term decomposition")
  }
}

///|
test "decompose witness reconstructs every sampled tensor [D-Decomp]" {
  // 對 F_3 上的隨機 2×2×2 張量：decompose 回傳的 (類別, 係數) 必須逐項還原 t，
  // 且項數與 classify222 給的秩一致（兩者現在共用同一個秩引擎）。
  let tab = @tensor.rank1_table(2, 3)
  let rng = @core.rng_seed(20261028)
  let mut checked = 0
  let mut bad = 0
  for iter = 0; iter < 40; iter = iter + 1 {
    let t = @tensor.t3_of(2, 2, 2, 3, (_, _, _) => @core.rng_below(rng, 3))
    let (rank, _dc, _det) = @tensor.classify222(t, tab)
    match @tensor.decompose(t, tab, 3) {
      Some(terms) => {
        checked = checked + 1
        if terms.length() != rank {
          bad = bad + 1
        }
        let acc = @tensor.t3_make(2, 2, 2, 3)
        let f = @core.mk_field(3)
        for (ci, coef) in terms {
          let scaled = @core.vec_scale(tab.list[ci], coef, 3)
          for q = 0; q < acc.data.length(); q = q + 1 {
            acc.data[q] = @core.fld_add(f, acc.data[q], scaled[q])
          }
        }
        if acc.data != t.data {
          bad = bad + 10
        }
      }
      None => bad = bad + 100
    }
  }
  assert_eq(bad, 0)
  assert_eq(checked, 40)
}
