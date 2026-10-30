///|
test "non-crossing tree counts match closed formula [T-NCT-Count]" {
  // T(n) = C(3n-3, n-1)/(2n-1) : 1,1,3,12,55,273,1428
  let expect = [1L, 1L, 3L, 12L, 55L, 273L, 1428L]
  for n = 1; n <= 7; n = n + 1 {
    assert_eq(@nc.nc_tree_formula(n), expect[n - 1])
    if n <= 6 {
      assert_eq(@nc.count_nc_trees_brute(n).to_int64(), expect[n - 1])
    }
  }
}

///|
test "formula stays exact past Int32 (regression for silent truncation)" {
  // 早期 Int32 版本在 n=16 起給出負數；Int64 版本必須是這些精確值。
  let expect = [
    300830572L, 1822766520L, 11124755664L, 68328754959L, 422030545335L, 2619631042665L,
    16332922290300L, 102240109897695L, 642312451217745L,
  ]
  for n = 14; n <= 22; n = n + 1 {
    assert_eq(@nc.nc_tree_formula(n), expect[n - 14])
    assert_eq(@nc.nc_tree_formula(n) > 0L, true)
  }
}

///|
test "integrality of the counting formula [P-NCT-Int]" {
  for n = 1; n <= 22; n = n + 1 {
    assert_eq(@nc.nc_tree_divisible(n), true)
  }
}

///|
test "crossing predicate basic cases" {
  assert_eq(@nc.chords_cross(@nc.chord(0, 2), @nc.chord(1, 3)), true)
  assert_eq(@nc.chords_cross(@nc.chord(0, 1), @nc.chord(2, 3)), false)
  assert_eq(@nc.chords_cross(@nc.chord(0, 3), @nc.chord(0, 2)), false)
  // 五角形：對角線 (0,2) 與 (1,4) 交叉
  assert_eq(@nc.chords_cross(@nc.chord(0, 2), @nc.chord(1, 4)), true)
}

///|
test "catalan families: matchings & triangulations [T-Cat-Match][T-Tri-Cat]" {
  let cat = @nc.catalan_upto(8)
  for m = 1; m <= 6; m = m + 1 {
    assert_eq(@nc.nc_perfect_matchings(m).length(), cat[m])
  }
  for n = 3; n <= 8; n = n + 1 {
    assert_eq(@nc.triangulations(n).length(), cat[n - 2])
  }
}

///|
test "matching DP agrees with brute force" {
  let n = 8
  let mut seed : Int32 = 7 // 本地 LCG（避免為一個測試在 elim/nc 引入 elim/core 依賴）
  let mut ok = true
  for trial = 0; trial < 6; trial = trial + 1 {
    // 先抽上三角，再對稱化（保證 w 對稱）
    let up : Array[Int32] = Array::makei(n * n, k => {
      if k / n < k % n {
        seed = (seed * 1103515245 + 12345) % 1000003
        if seed < 0 {
          seed = 0 - seed
        }
        1 + seed % 13
      } else {
        0
      }
    })
    let w : Array[Array[Int32]] = Array::makei(n, i => {
      Array::makei(n, j => {
        if i == j {
          0
        } else if i < j {
          up[i * n + j]
        } else {
          up[j * n + i]
        }
      })
    })
    let (a, edges) = @nc.min_weight_nc_matching(w, n)
    let b = @nc.min_weight_nc_matching_brute(w, n)
    if a != b || edges.length() != n / 2 {
      ok = false
    }
    if !@nc.is_noncrossing(edges) {
      ok = false
    }
  }
  assert_eq(ok, true)
}

///|
test "dual of a triangulation is a subcubic tree [T-Dual]" {
  for n = 4; n <= 7; n = n + 1 {
    for tri in @nc.triangulations(n) {
      let tris = @nc.triangles_of(n, tri)
      assert_eq(tris.length(), n - 2)
      let dual = @nc.dual_graph(tris, tri)
      assert_eq(dual.length(), n - 3)
      assert_eq(@nc.max_degree(tris.length(), dual) <= 3, true)
      let dichords = dual.map(pr => @nc.chord(pr.0, pr.1))
      assert_eq(@nc.is_tree(n - 2, dichords), true)
    }
  }
}

///|
test "flip graph is (n-3)-regular and connected [T-Flip]" {
  for n = 4; n <= 6; n = n + 1 {
    let tris = @nc.triangulations(n)
    let degs = @nc.flip_degrees(tris)
    let mut ok = true
    for d in degs {
      if d != n - 3 {
        ok = false
      }
    }
    assert_eq(ok, true)
    assert_eq(@nc.flip_graph_connected(tris), true)
  }
}

///|
test "metric-free: NC constraint costs nothing for monotone cyclic weights [T-NC-Free]" {
  let fs = [[0, 1, 2, 3, 4], [0, 3, 7, 12, 20], [0, 1, 4, 9, 16]]
  for f in fs {
    for n = 4; n <= 6; n = n + 1 {
      if n / 2 < f.length() {
        assert_eq(@nc.strict_monotone(f), true)
        let (mst, ncmin) = @nc.nc_freedom_gap(f, n)
        let path = (n - 1) * f[1]
        assert_eq(mst, path)
        assert_eq(ncmin, path)
      }
    }
  }
}

///|
test "sharpness: a general metric CAN force crossings (hypothesis needed)" {
  // 四邊形：兩條對角線權重 1、其餘 5 —— 這是度量但 MST 交叉
  let n = 4
  let w = [[0, 5, 1, 5], [5, 0, 5, 1], [1, 5, 0, 5], [5, 1, 5, 0]]
  assert_eq(@nc.is_metric_w(w, n), true)
  let (mst, ncmin, crossing_free) = @nc.check_metric_freedom(w, n)
  assert_eq(mst, 7)
  assert_eq(ncmin, 11)
  assert_eq(mst < ncmin, true)
  assert_eq(crossing_free, false)
}
