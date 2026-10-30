///|
/// 衍生演算法基準：由「規範形式 + 範疇化」導出之演算法 vs 直接暴力/全搜索。
/// 每一項都同時驗證**結果一致**（OK/FAIL）與**成本比**（×）。
/// 運行：moon run cmd/symbench --target native --release

///|
/// 計時包裝：回傳 (結果, 毫秒)。
/// **單位注意**：`monotonic_clock_end` 回傳的是**微秒**（見 core/bench 文件），
/// 故此處除以 1000 換算為毫秒 —— 全庫計時只在此一點換算，避免單位散落。
fn[T] btime(f : () -> T) -> (T, Double) {
  let t0 = @mbench.monotonic_clock_start()
  let r = f()
  (r, @mbench.monotonic_clock_end(t0) / 1000.0)
}

///|
priv struct DecCase {
  name : String
  g : @symlib.Graph
  expect : Int64
  base : Bool
  note : String
}

///|
/// A. 分量分解 ⇒ |Aut| 積公式（免全搜索）。
fn bench_decomp() -> Unit {
  println(
    "-- A. 分量分解：|Aut| = Π(Π|Aut(Cᵢ)|^{mᵢ} · mᵢ!) 免全搜索 --",
  )
  let pet = @symlib.Graph::petersen()
  let c6 = @symlib.Graph::cycle(6)
  let k3 = @symlib.Graph::complete(3)
  let q3 = @symlib.Graph::hypercube(3)
  let cases : Array[DecCase] = [
    {
      name: "2×Petersen n=20",
      g: @symlib.Graph::disjoint_union([pet, pet]),
      expect: 28800L,
      base: true,
      note: "",
    },
    {
      name: "mix n=36",
      g: @symlib.Graph::disjoint_union([
        pet,
        c6,
        c6,
        @symlib.Graph::complete(5),
        @symlib.Graph::path(4),
        @symlib.Graph::empty(5),
      ]),
      expect: 995328000L,
      base: true,
      note: "",
    },
    {
      name: "3×Petersen n=30",
      g: @symlib.Graph::disjoint_union([pet, pet, pet]),
      expect: 10368000L,
      base: false,
      note: "搜索樹 >10⁶ 節點",
    },
    {
      name: "6×C6 n=36",
      g: @symlib.Graph::disjoint_union([c6, c6, c6, c6, c6, c6]),
      expect: 2149908480L,
      base: false,
      note: "搜索樹 >10⁶ 節點",
    },
    {
      name: "10×K3 n=30",
      g: @symlib.Graph::disjoint_union([k3, k3, k3, k3, k3, k3, k3, k3, k3, k3]),
      expect: 219419659468800L,
      base: false,
      note: "搜索樹 >10⁶ 節點",
    },
    {
      name: "8×Q3 n=64",
      g: @symlib.Graph::disjoint_union([q3, q3, q3, q3, q3, q3, q3, q3]),
      expect: 1136188586899537920L,
      base: false,
      note: "n=64，搜索不可行",
    },
    {
      name: "E20 n=20",
      g: @symlib.Graph::empty(20),
      expect: 2432902008176640000L,
      base: false,
      note: "全搜索實測（native release）：E12=4541 節點/7.3ms、E13=12758/42ms、E14=53533/0.64s、E16 >300s 未完成 ⇒ E20 不可行",
    },
  ]
  for c in cases {
    let (d, t_dec) = btime(fn() -> @symlib.Decomp { @symlib.decompose(c.g) })
    let (grp, t_sgs) = btime(fn() -> @symlib.PermGroup {
      d.automorphism_group()
    })
    let ok = if d.aut_order() == c.expect && grp.order() == c.expect {
      "OK"
    } else {
      "FAIL"
    }
    let head = "  " +
      c.name +
      ": |Aut|=" +
      c.expect.to_string() +
      "(" +
      ok +
      ") blocks=" +
      d.block_count().to_string() +
      " classes=" +
      d.class_count().to_string() +
      " 分解=" +
      t_dec.to_string() +
      "ms +SGS=" +
      t_sgs.to_string() +
      "ms"
    if c.base {
      let (ao, t_full) = btime(fn() -> Int64 { @symlib.aut_order(c.g) })
      let ok2 = if ao == c.expect { "OK" } else { "FAIL" }
      let ratio = t_full / (t_dec + t_sgs)
      println(
        head +
        " vs 全搜索=" +
        t_full.to_string() +
        "ms(" +
        ok2 +
        ") ⇒ " +
        ratio.to_string() +
        "× 加速",
      )
    } else {
      println(head + " （全搜索基線略：" + c.note + "）")
    }
  }
}

///|
/// B. Whitney 線圖定理 ⇒ |Aut(L(G))| 由 |Aut(G)| 與核階推出（免搜索 L(G)）。
fn bench_line() -> Unit {
  println(
    "-- B. Whitney：|Aut(L(G))| = |Aut(G)| / |ker Φ|（免搜索 L(G)）--",
  )
  let cases : Array[(String, @symlib.Graph)] = [
    ("Petersen", @symlib.Graph::petersen()),
    ("K5", @symlib.Graph::complete(5)),
    ("K3,3", @symlib.Graph::complete_bipartite(3, 3)),
    ("Q3", @symlib.Graph::hypercube(3)),
    ("C12", @symlib.Graph::cycle(12)),
    (
      "2×C5",
      @symlib.Graph::disjoint_union([
        @symlib.Graph::cycle(5),
        @symlib.Graph::cycle(5),
      ]),
    ),
    ("K7", @symlib.Graph::complete(7)),
  ]
  for t in cases {
    let (nm, g) = t
    let lg = @symlib.line_graph(g)
    let (derived, t_d) = btime(fn() -> Int64 {
      @symlib.aut_order(g) / @symlib.line_kernel_order(g)
    })
    let (direct, t_f) = btime(fn() -> Int64 { @symlib.aut_order(lg) })
    let ok = if derived == direct { "OK" } else { "FAIL" }
    println(
      "  " +
      nm +
      ": L(G) n=" +
      lg.order().to_string() +
      " m=" +
      lg.size().to_string() +
      " |Aut(L)|=" +
      direct.to_string() +
      "(" +
      ok +
      ") 定理=" +
      t_d.to_string() +
      "ms vs 搜索 L(G)=" +
      t_f.to_string() +
      "ms ⇒ " +
      (t_f / t_d).to_string() +
      "× 加速",
    )
  }
}

///|
/// C. 補圖對偶：雙通道交叉驗證（複雜度中性，賣點是**自我驗證**而非加速）。
fn bench_dual() -> Unit {
  println(
    "-- C. 補圖對偶：一次搜索得兩份規範形式（G 與 Ḡ）--",
  )
  for t in [(20, 50, 11), (24, 50, 22), (28, 45, 33), (32, 50, 44)] {
    let (n, p, seed) = t
    let g = @symlib.Graph::random(n, p, seed).0
    let (dp, t_pair) = btime(fn() -> (@symlib.DualCanon, @symlib.DualCanon) {
      @symlib.dual_pair(g)
    })
    let (dg, dc) = dp
    let (_, t_two) = btime(fn() -> (@symlib.Graph, @symlib.Graph) {
      (@symlib.canonical_form(g), @symlib.canonical_form(g.complement()))
    })
    let same = dg.nodes == dc.nodes
    println(
      "  n=" +
      n.to_string() +
      " m=" +
      g.size().to_string() +
      ": dual_pair=" +
      t_pair.to_string() +
      "ms nodes=" +
      dg.nodes.to_string() +
      "/" +
      dc.nodes.to_string() +
      (if same { "（單搜索）" } else { "（雙搜索）" }) +
      " vs 兩次 canonical_form=" +
      t_two.to_string() +
      "ms ⇒ " +
      (t_two / t_pair).to_string() +
      "×",
    )
  }
}

///|
/// D. 標記向量 = G-集之完全不變量 ⇒ 免階乘級枚舉判定 G-集同構。
fn bench_marks() -> Unit {
  println("-- D. G-集標記：|X|! 級暴力 ⇒ O(#類·|G|) 判定 --")
  let s4 = @symlib.PermGroup::symmetric(4)
  let (subs, t_sub) = btime(fn() -> Array[@symlib.Sub] {
    @symlib.subgroup_classes(s4, 400)
  })
  let (marks, t_marks) = btime(fn() -> Array[Array[Int32]] {
    @symlib.table_of_marks(s4, subs, 400)
  })
  let (_, t_cert) = btime(fn() -> (Bool, Bool, Bool, Int32, Int64) {
    @symlib.marks_cert(s4, 400)
  })
  println(
    "  S4: 子群共軛類=" +
    subs.length().to_string() +
    " (" +
    t_sub.to_string() +
    "ms) table_of_marks " +
    marks.length().to_string() +
    "×" +
    marks[0].length().to_string() +
    " (" +
    t_marks.to_string() +
    "ms) 證書 (" +
    t_cert.to_string() +
    "ms)",
  )
  // 兩個 12 點 G-集：S4/⟨(01)⟩ 與 S4/⟨(01)(23)⟩（同階但非共軛 ⇒ 非同構）
  let c2 : Array[@symlib.Sub] = []
  for h in subs {
    if h.order == 2L {
      c2.push(h)
    }
  }
  let x = @symlib.coset_gset(s4, c2[0], 400)
  let y = @symlib.coset_gset(s4, c2[1], 400)
  let (iso, t_iso) = btime(fn() -> Bool { @symlib.gset_isomorphic(x, y, subs) })
  let ok = if !iso { "OK" } else { "FAIL" }
  println(
    "  |X|=|Y|=" +
    x.x.to_string() +
    "：標記判定 G-集同構=" +
    iso.to_string() +
    "(" +
    ok +
    ") " +
    t_iso.to_string() +
    "ms；暴力需 " +
    x.x.to_string() +
    "! ≈ 4.79e8 個雙射（不可行）",
  )
  // 共軛子群 ⇒ 同構 G-集之正例由 marks_cert 之雙算法一致性覆蓋
  // （見測試 ext-marks-and-burnside / ext-cayley-graphs）
}

///|
/// E. PermSet 規範形式：可雜湊之決定性鍵 ⇒ 資料庫級去重 O(1)/對。
/// （單次判定之成本與暴力同階；暴力有早退，規範形式無早退但可**快取與重複使用**。）
fn bench_permset() -> Unit {
  println(
    "-- E. 置換集規範形式：一次 O(n!) 規範化 ⇒ 之後每對 O(1)（可雜湊/可快取）--",
  )
  for t in [(6, 8), (7, 4)] {
    let (n, k) = t
    let cyc_arr = Array::make(n, 0)
    for i in 0..<n {
      cyc_arr[i] = i
    }
    let rot = @symlib.Perm::from_cycles(n, [cyc_arr])
    let refl_img = Array::make(n, 0)
    for i in 0..<n {
      refl_img[i] = (n - i) % n
    }
    let refl = @symlib.Perm::from_img(refl_img)
    // k 個置換集：循環型與二面體型之共軛像（應分成 2 個同構類）
    let pss : Array[@symlib.PermSet] = []
    for i in 0..<k {
      let sig = @symlib.Perm::random(n, 100 * n + 7 * i).0
      let gens = if i % 2 == 0 {
        [rot.conjugate_by(sig)]
      } else {
        [rot.conjugate_by(sig), refl.conjugate_by(sig)]
      }
      pss.push(@symlib.permset(n, gens))
    }
    let (keys, t_canon) = btime(fn() -> Array[String] {
      let out : Array[String] = []
      for ps in pss {
        let c = @symlib.permset_canon(ps, 100000)
        let mut s = ""
        for v in c {
          s = s + v.to_string() + ","
        }
        out.push(s)
      }
      out
    })
    let npair = k * (k - 1) / 2
    let (nclass, t_cmp) = btime(fn() -> Int32 {
      let cls : Array[String] = []
      for key in keys {
        let mut found = false
        for c in cls {
          if c == key {
            found = true
            break
          }
        }
        if !found {
          cls.push(key)
        }
      }
      cls.length()
    })
    let (brute_cls, t_brute) = btime(fn() -> Int32 {
      // 暴力：對每一對窮舉 λ ∈ S_n 檢查生成元逐一共軛相等（union-find 併類）
      let perms = @symlib.all_perms(n, 100000)
      let parent = Array::make(k, 0)
      for i in 0..<k {
        parent[i] = i
      }
      fn find(a : Int32) -> Int32 {
        let mut r = a
        while parent[r] != r {
          r = parent[r]
        }
        r
      }
      for i in 0..<k {
        for j in (i + 1)..<k {
          let a = pss[i]
          let b = pss[j]
          if a.gens.length() != b.gens.length() {
            continue
          }
          let mut iso = false
          for l in perms {
            let linv = l.inverse()
            let mut ok = true
            for gi in 0..<a.gens.length() {
              if linv.compose(a.gens[gi]).compose(l) != b.gens[gi] {
                ok = false
                break
              }
            }
            if ok {
              iso = true
              break
            }
          }
          if iso {
            let ra = find(i)
            let rb = find(j)
            if ra != rb {
              parent[rb] = ra
            }
          }
        }
      }
      let cls : Array[Int32] = []
      for i in 0..<k {
        let mut found = false
        for c in cls {
          if c == find(i) {
            found = true
            break
          }
        }
        if !found {
          cls.push(find(i))
        }
      }
      cls.length()
    })
    let ok = if nclass == brute_cls { "OK" } else { "FAIL" }
    // 單項成本與損益兩平點：k·c + k(k-1)/2·0 vs k(k-1)/2·b
    let c_item = t_canon / k.to_double()
    let b_pair = t_brute / npair.to_double()
    let crossover = 2.0 * c_item / b_pair + 1.0
    println(
      "  n=" +
      n.to_string() +
      " k=" +
      k.to_string() +
      " 對數=" +
      npair.to_string() +
      ": 類數 規範鍵=" +
      nclass.to_string() +
      " 暴力=" +
      brute_cls.to_string() +
      "(" +
      ok +
      ") 規範化=" +
      t_canon.to_string() +
      "ms（每項 " +
      c_item.to_string() +
      "ms）+ 每對 " +
      (t_cmp / npair.to_double()).to_string() +
      "ms；暴力每對 " +
      b_pair.to_string() +
      "ms ⇒ 項數 > " +
      crossover.to_string() +
      " 時規範鍵勝出（且鍵可雜湊/快取/增量）",
    )
  }
}

///|
/// F. 規範折疊：一次搜索（生成元共軛搬運）vs 兩次搜索。
fn bench_fold() -> Unit {
  println(
    "-- F. 規範折疊：一次搜索 + 生成元共軛 vs 兩次搜索 --",
  )
  let pet = @symlib.Graph::petersen()
  for
    t in [
      ("P5", @symlib.Graph::path(5)),
      ("star4", @symlib.Graph::star(4)),
      ("Petersen", pet),
      ("Q4", @symlib.Graph::hypercube(4)),
      ("K3,3", @symlib.Graph::complete_bipartite(3, 3)),
    ] {
    let (nm, g) = t
    let (f1, t1) = btime(fn() -> @symlib.FoldedGraph {
      @symlib.fold_canonical(g)
    })
    // 舊法：canonical_form（搜索 1）+ automorphism_group（搜索 2）+ fold_graph
    let (f2, t2) = btime(fn() -> @symlib.FoldedGraph {
      let cf = @symlib.canonical_form(g)
      @symlib.fold_graph(cf, @symlib.automorphism_group(cf))
    })
    let eq = @symlib.fold_equal(f1, f2)
    // 重標號不變性：規範折疊相等，一般折疊之軌道順序則依賴標號
    let sig = @symlib.Perm::random(g.order(), 1234).0
    let inv = @symlib.fold_equal(f1, @symlib.fold_canonical(g.relabel(sig)))
    let plain = @symlib.fold_graph(g, @symlib.automorphism_group(g))
    let plain_inv = @symlib.fold_equal(
      plain,
      @symlib.fold_graph(
        g.relabel(sig),
        @symlib.automorphism_group(g.relabel(sig)),
      ),
    )
    println(
      "  " +
      nm +
      ": k=" +
      f1.k.to_string() +
      "/" +
      g.order().to_string() +
      " 一致=" +
      eq.to_string() +
      " 一次搜索=" +
      t1.to_string() +
      "ms vs 兩次搜索=" +
      t2.to_string() +
      "ms ⇒ " +
      (t2 / t1).to_string() +
      "×；重標號不變 規範=" +
      inv.to_string() +
      " 一般=" +
      plain_inv.to_string(),
    )
  }
}

///|
/// G. Cayley 定理：|Aut(Cay(G,S))| ≥ |G| 為 O(1) 下界（精確值需全搜索）。
fn bench_cayley() -> Unit {
  println(
    "-- G. Cayley 嵌入：O(1) 下界 |Aut(Cay(G,S))| ≥ |G| vs 全搜索 --",
  )
  for
    t in [
      ("C6", @symlib.PermGroup::cyclic(6)),
      ("D4", @symlib.PermGroup::dihedral(4)),
      ("S3", @symlib.PermGroup::symmetric(3)),
    ] {
    let (nm, grp) = t
    let cay = @symlib.cayley_graph(grp, 400)
    let (ao, t_full) = btime(fn() -> Int64 { @symlib.aut_order(cay) })
    let ok = if ao >= grp.order() { "OK" } else { "FAIL" }
    println(
      "  Cay(" +
      nm +
      "): n=" +
      cay.order().to_string() +
      " m=" +
      cay.size().to_string() +
      " |Aut|=" +
      ao.to_string() +
      " ≥ |G|=" +
      grp.order().to_string() +
      "(" +
      ok +
      ") 定理下界 O(1)（免搜索） vs 全搜索=" +
      t_full.to_string() +
      "ms",
    )
  }
}

///|
fn bench_derived() -> Unit {
  println("=== 衍生演算法基準（規範形式 × 範疇化）===")
  bench_decomp()
  bench_line()
  bench_dual()
  bench_marks()
  bench_permset()
  bench_fold()
  bench_cayley()
  println("=== 衍生演算法基準結束 ===")
}
