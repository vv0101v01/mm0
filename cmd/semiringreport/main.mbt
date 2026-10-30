// ===========================================================================
// 量測報告生成器
//
// 每一個數字都來自本次執行的真實計算：
//   * 時間：`time_min` 取重複執行的最小值（微秒）。
//   * 運算量：半環 ⊕/⊗ 的實際呼叫次數（`Ops`）。
//   * 記憶體：把演算法實際發出的存取序列餵給兩層快取模擬器（`Tracer`）。
//   * 正確性：每一節都附交叉檢查（不同演算法必須給出同一個答案）。
// ===========================================================================

///|
using @alg {
  type Rng,
  type Trop,
  type Ops,
  type Prob,
  type Counting,
  type BoolSr,
  type Bottleneck,
  type CyclicSet,
  type ParetoSet,
  trait Semiring,
  trait IdempotentSemiring,
  check_semiring,
  check_semiring_approx,
  check_idempotent,
  check_star_idem,
  check_group_element,
}

///|
using @mat {
  type Mat,
  mat_equal,
  mul_naive,
  mul_ikj,
  mul_blocked,
  mul_trop,
  closure_fw_inplace,
  closure_lehmann,
  closure_blocked,
}

///|
using @mon {
  type SegTree,
  type SparseTable,
  type Fenwick,
  type SumI64,
  type MaxI64,
  prefix_scan,
  prefix_scan_sequential,
}

///|
using @graph {
  type Graph,
  apsp_kleene,
  apsp_dijkstra,
  closure_bitset,
  functional_decompose,
  pareto_sssp,
  total_labels,
}

///|
using @spline {
  cubic_pole,
  interp_cubic_dense,
  interp_cubic_periodic,
  interp_cubic_banded,
  interp_cubic_dense_open,
}

///|
using @rl {type Limiter, type HierLimiter}

///|
using @io {
  parse_edges_fast,
  parse_edges_naive,
  synth_edge_list,
  synth_edge_bytes,
}

///|
using @sim {type Timer, type Tracer, time_min}

///|
fn line(s : String) -> Unit {
  println(s)
}

///|
fn ratio(a : Double, b : Double) -> String {
  if b <= 0.0 {
    "n/a".to_string()
  } else {
    f2((a / b * 100.0).round() / 100.0)
  }
}

///|
/// 執行一節並記錄其耗時（報告中同時給出每節成本，方便判斷哪一節最貴）。
fn section(id : String, f : () -> Unit) -> Unit {
  let t = Timer::start()
  f()
  line("")
  line(
    "*§\{id} 本節耗時 \{f2(t.elapsed_us() / 1000.0)} ms（含建表與交叉驗證）*",
  )
  line("")
}

///|
/// 小數點後 `digits` 位的四捨五入字串（唯一的格式化實作；f1/f2/f6 都走這裡）。
fn round_to(x : Double, digits : Int32) -> String {
  let mut scale = 1.0
  for _ in 0..<digits {
    scale = scale * 10.0
  }
  ((x * scale).round() / scale).to_string()
}

///|
fn f2(x : Double) -> String {
  round_to(x, 2)
}

///|
fn f1(x : Double) -> String {
  round_to(x, 1)
}

///|
fn rand_trop(rng : Rng, n : Int32, density : Int32, maxw : Int32) -> Mat[Trop] {
  let m = Mat::new(n, n, Trop::inf())
  for i in 0..<n {
    for j in 0..<n {
      if i != j && rng.next_int(100) < density {
        m.d[i * n + j] = Trop::new(1 + rng.next_int(maxw))
      }
    }
  }
  m
}

///|
fn main {
  let t_all = Timer::start()
  line("# 量測報告（semiring-lab）")
  line("")
  line(
    "> 由 `moon run cmd/semiringreport --target native` 產生；所有數字都是本次執行的實測值。",
  )
  line(
    "> 測試與基準使用固定種子的 SplitMix64，因此重跑會得到**相同的輸入與相同的正確性結論**（時間隨機器浮動）。",
  )
  line("")
  section("1", fn() { sec1_axioms() })
  section("2", fn() { sec2_matmul() })
  section("3", fn() { sec3_memory() })
  section("4", fn() { sec4_closure() })
  section("5", fn() { sec5_graph() })
  section("6", fn() { sec6_spline() })
  section("7", fn() { sec7_ratelimit() })
  section("8", fn() { sec8_loader() })
  section("9", fn() { sec9_monoid() })
  section("10", fn() { sec10_sparse() })
  section("11", fn() { sec11_float() })
  section("12", fn() { sec12_blocking() })
  section("13", fn() { sec13_parallel() })
  section("14", fn() { sec14_tropical_geometry() })
  section("15", fn() { sec15_normal_forms() })
  section("16", fn() { sec16_categorification() })
  section("17", fn() { sec17_app_portfolio() })
  section("18", fn() { sec18_belief() })
  section("19", fn() { sec19_limits() })
  line("")
  line("---")
  line("")
  line(
    "報告總產生時間：\{f2(t_all.elapsed_us() / 1000.0)} ms（含全部建表與交叉驗證）",
  )
}
