///| ## `opt` 套件的驗收測試（LP／團數／Carlet）

///| `rat_floor` 必須對分數精確（第一版曾把 `9/2` 解析成 `0`）。
test "rat_floor: exact on fractions" {
  assert_eq(rat_floor(@algebra.rat_make(9, 2)), 4)
  assert_eq(rat_floor(@algebra.rat_make(6, 2)), 3)
  assert_eq(rat_floor(@algebra.rat_make(1, 3)), 0)
  assert_eq(rat_floor(@algebra.rat_make(8, 3)), 2)
}

///| 極小的 LP：`max x + y` s.t. `x ≤ 1`、`y ≤ 1` ⇒ 2。
test "lp_max: exact optimum on a box" {
  let a : Array[Array[@algebra.Rat]] = [
    [@algebra.rat_int(1), @algebra.rat_zero()],
    [@algebra.rat_zero(), @algebra.rat_int(1)],
  ]
  let b : Array[@algebra.Rat] = [@algebra.rat_int(1), @algebra.rat_int(1)]
  let c : Array[@algebra.Rat] = [@algebra.rat_int(1), @algebra.rat_int(1)]
  let (v, x, ok) = lp_max(2, a, b, c)
  assert_true(ok)
  assert_true(@algebra.rat_cmp_exact(v, @algebra.rat_int(2)) == 0)
  assert_true(@algebra.rat_cmp_exact(x[0], @algebra.rat_int(1)) == 0)
}

///| `K₄`：暴力 = 分支定界 = LP = 4。
test "clique: K4 agrees on all three methods" {
  let g = graph_new(4)
  for i = 0; i < 4; i = i + 1 {
    for j = (i + 1); j < 4; j = j + 1 {
      graph_add(g, i, j)
    }
  }
  assert_eq(clique_number(g), 4)
  assert_eq(clique_number_brute(g), 4)
  let all : Array[Int32] = [0, 1, 2, 3]
  assert_eq(rat_floor(lp_clique_bound(g, all)), 4)
}

///| `K(3,3)`：`ω = 2`，但 LP 給 `3`（整數間隙 1）——多部圖上的已知行為。
test "clique: K(3,3) has integrality gap 1" {
  let g = graph_new(6)
  for i = 0; i < 3; i = i + 1 {
    for j = 3; j < 6; j = j + 1 {
      graph_add(g, i, j)
    }
  }
  assert_eq(clique_number(g), 2)
  let all : Array[Int32] = [0, 1, 2, 3, 4, 5]
  let lp = lp_clique_bound(g, all)
  assert_true(@algebra.rat_cmp_exact(lp, @algebra.rat_int(3)) == 0)
  assert_eq(rat_floor(lp), 3)
}

///| `AND₂` 的 ANF 只有 `x₀x₁` 一項。
test "anf: AND2 has a single monomial" {
  let tt : Array[Int32] = [0, 0, 0, 1]
  let a = anf_coeffs(tt, 2)
  assert_eq(a[3], 1)
  assert_eq(a[0] + a[1] + a[2], 0)
}

///| 單點函數的 AI 是 1；Majority 在 n = 3,5,7 上達 `⌈n/2⌉`。
test "carlet: majority reaches the ceil(n/2) bound" {
  assert_eq(ceil_half(7), 4)
  assert_eq(ceil_half(8), 4)
  for n in [3, 5, 7] {
    assert_eq(algebraic_immunity(majority_tt(n), n), ceil_half(n))
  }
}

///| `AI(f) ≤ ⌈n/2⌉` 逐函數檢查（n ≤ 3，256 個函數）。
test "carlet: upper bound holds for every function up to n = 3" {
  let (ok, bad, tight, total) = carlet_bound_check(3)
  assert_true(ok)
  assert_eq(bad, 0 - 1)
  assert_eq(total, 256)
  assert_eq(tight, 56)
}

///| 三條界都必須是**合法上界**：在任何圖上 `LP ≥ ω`、`rank ≥ ω`、`colour ≥ ω`，
///| 而且四種界設定的分支定界都必須與暴力同值。
test "bnb: all three bounds are sound on structured and random graphs" {
  let g = graph_random(12, 500, 7)
  let all : Array[Int32] = []
  for i = 0; i < g.n; i = i + 1 {
    all.push(i)
  }
  let w = clique_number_brute(g)
  assert_true(rat_floor(lp_clique_bound(g, all)) >= w)
  assert_true(rank_bound_sub(g, all) >= w)
  assert_true(greedy_colour_bound(g, all) >= w)
  for flags in [0, 1, 2, 4, 7] {
    assert_eq(bnb(g, flags)[0], w)
  }
  // LP 在密集圖上必須收斂（缺 `x ≤ 1` 時會無界）
  let (_, ok, _it) = lp_clique_bound_stat(g, all)
  assert_true(ok)
}

///| 稠密圖上的老 bug 迴歸：`G(18,0.6)` 曾有 `ω = 5/6 < 暴力 7`。
test "bnb: dense 18-vertex graph matches brute force" {
  let g = graph_random(18, 600, 3)
  let w = clique_number_brute(g)
  assert_eq(w, 7)
  for flags in [0, 1, 2, 4, 7] {
    assert_eq(bnb(g, flags)[0], w)
  }
  assert_eq(clique_number(g), w)
}

///| 三界合流的分支定界在 K(3×3) 上一次到底（多部圖上秩界緊）。
test "bnb: pruning collapses on complete multipartite" {
  let g = graph_new(9)
  for i = 0; i < 9; i = i + 1 {
    for j = 0; j < 9; j = j + 1 {
      if i / 3 != j / 3 {
        graph_add(g, i, j)
      }
    }
  }
  let all : Array[Int32] = [0, 1, 2, 3, 4, 5, 6, 7, 8]
  assert_eq(bnb(g, flag_rank)[0], 3)
  assert_true(bnb(g, flag_rank)[1] < bnb(g, flag_none)[1])
  assert_eq(rank_bound_sub(g, all), 3)
}

///| 假孿生收縮必須保持 `ω`，且真孿生**不**被收縮（`K₃` 反例）。
test "refine: false-twin reduction preserves omega, true twins untouched" {
  let g = twinned_demo()
  let (keep, removed, true_pairs) = twin_reduce(g)
  assert_eq(g.n, 18)
  assert_eq(keep.length(), 13)
  assert_eq(removed, 5)
  assert_true(true_pairs >= 0)
  let w = clique_number_brute(g)
  let (w_red, _n) = omega_on(g, keep, flag_rank | flag_lp | flag_color)
  assert_eq(w_red, w)
  // K₃ 的三對真孿生一個都不該被刪
  let k3 = graph_new(3)
  graph_add(k3, 0, 1)
  graph_add(k3, 1, 2)
  graph_add(k3, 0, 2)
  let (keep3, removed3, tp3) = twin_reduce(k3)
  assert_eq(keep3.length(), 3)
  assert_eq(removed3, 0)
  assert_eq(tp3, 3)
}

///| 連通分解：`ω` 等於各分量最大者。
test "refine: components give the same omega" {
  let g = twinned_demo()
  let comps = components(g)
  assert_eq(comps.length(), 3)
  let mut best = 0
  for c in comps {
    let (w, _n) = omega_on(g, c.verts, flag_rank | flag_lp | flag_color)
    if w > best {
      best = w
    }
  }
  assert_eq(best, clique_number_brute(g))
}
