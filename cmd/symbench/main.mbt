///|
/// symlib 性能基準：一次搜索 → Schreier–Sims → 群作用 → 軌道折疊 全管線計時。
/// 運行：moon run cmd/symbench --target native --release
/// 注：所有時間以**毫秒**呈現；`monotonic_clock_end` 原生回傳微秒 ⇒ 各處除以 1000。

///|
priv struct Case {
  name : String
  g : @symlib.Graph
  expect : Int64
}

///|
fn bench_one(c : Case) -> Unit {
  let t0 = @mbench.monotonic_clock_start()
  let r = @symlib.search_graph(c.g, true)
  let t1 = @mbench.monotonic_clock_start()
  let dt_search = @mbench.monotonic_clock_end(t0) / 1000.0
  let grp = @symlib.PermGroup::new(c.g.order(), r.aut_gens)
  let t2 = @mbench.monotonic_clock_start()
  let dt_sgs = @mbench.monotonic_clock_end(t1) / 1000.0
  let folded = @symlib.fold_graph(c.g, grp)
  let dt_fold = @mbench.monotonic_clock_end(t2) / 1000.0
  let ok = if grp.order() == c.expect { "OK" } else { "FAIL" }
  println(
    "\{c.name}: |Aut|=\{grp.order()}(\{ok}) nodes=\{r.nodes} leaves=\{r.leaves} ties=\{r.ties} fold=\{folded.k}/\{c.g.order()} search=\{dt_search}ms sgs=\{dt_sgs}ms fold=\{dt_fold}ms",
  )
}

///|
fn main {
  println("=== symlib bench (native release) ===")
  let cases : Array[Case] = [
    { name: "P5", g: @symlib.Graph::path(5), expect: 2L, },
    { name: "C6", g: @symlib.Graph::cycle(6), expect: 12L, },
    { name: "Petersen", g: @symlib.Graph::petersen(), expect: 120L, },
    { name: "K5", g: @symlib.Graph::complete(5), expect: 120L, },
    { name: "K10", g: @symlib.Graph::complete(10), expect: 3628800L, },
    { name: "K3,3", g: @symlib.Graph::complete_bipartite(3, 3), expect: 72L, },
    { name: "star4", g: @symlib.Graph::star(4), expect: 24L, },
    { name: "Q3", g: @symlib.Graph::hypercube(3), expect: 48L, },
    { name: "Q4", g: @symlib.Graph::hypercube(4), expect: 384L, },
    { name: "Q5", g: @symlib.Graph::hypercube(5), expect: 3840L, },
    { name: "C60", g: @symlib.Graph::cycle(60), expect: 120L, },
    { name: "P40", g: @symlib.Graph::path(40), expect: 2L, },
  ]
  for c in cases {
    bench_one(c)
  }
  bench_derived()
  println("=== done ===")
}
