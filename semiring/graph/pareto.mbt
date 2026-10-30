// ===========================================================================
// 多目標最短路（格序半環 + 矩陣/鬆弛的嵌套）
//
// 這裡把 ParetoSet（格序半環）「放進」圖的鬆弛迴圈：
//   dist[v] ← dist[v] ⊕ ( dist[u] ⊗ w(u,v) )
// 因為 ⊕ 是「聯集 + 支配剪枝」且為冪等，這個鬆弛是單調的；
// 非負權重下最長的有效路徑是簡單路徑，故迭代在有限步內穩定。
//
// 與純量最短路最大的差別：標籤數不再是 1，而是「互不支配的標籤數」。
// 支配剪枝（absorption law: x ⊕ (x ⊕ y) = x ⊕ y）就是控制記憶體爆炸的關鍵。
// ===========================================================================

///|
/// 多目標最短路（Bellman–Ford 風格的標籤修正法）。
///
/// 回傳每個點相對 src 的 Pareto 標籤集，以及是否在迭代上限內穩定。
pub fn pareto_sssp(
  g : Graph,
  src : Int32,
  max_rounds~ : Int32 = 64,
  ops? : Ops,
) -> (Array[ParetoSet], Bool) {
  let n = g.n
  let dist = Array::make(n, ParetoSet::empty(2))
  let start = ParetoSet::empty(2)
  dist[src] = ParetoSet::plus(start, ParetoSet::point([0, 0]))
  let queue = Array(capacity=n)
  let inqueue = Array::make(n, false)
  queue.push(src)
  inqueue[src] = true
  let mut head = 0
  let mut rounds = 0
  let mut converged = true
  while head < queue.length() {
    if rounds >= max_rounds * n {
      converged = false
      break
    }
    let u = queue[head]
    head = head + 1
    inqueue[u] = false
    rounds = rounds + 1
    let du = dist[u]
    if du.size() == 0 {
      continue
    }
    for e in g.offsets[u]..<g.offsets[u + 1] {
      let v = g.to[e]
      let wset = ParetoSet::point([g.w[e], g.w2[e]])
      let cand = ParetoSet::times(du, wset)
      if ops is Some(o) {
        o.record_times()
      }
      // 只有當 candidate 帶來「新且不被支配」的標籤時才更新
      let merged = ParetoSet::plus(dist[v], cand)
      if ops is Some(o) {
        o.record_plus()
      }
      let old = dist[v]
      if merged.size() != old.size() || !(merged == old) {
        dist[v] = merged
        if !inqueue[v] {
          inqueue[v] = true
          queue.push(v)
        }
      }
    }
    if head > 4096 && head * 2 > queue.length() {
      // 佇列壓縮：避免長尾造成記憶體成長
      let rest = queue[head:]
      queue.clear()
      queue.append(rest)
      head = 0
    }
  }
  (dist, converged)
}

///|
/// 全部標籤總數（用於量測剪枝效果）。
pub fn total_labels(d : Array[ParetoSet]) -> Int32 {
  let mut s = 0
  for x in d {
    s = s + x.size()
  }
  s
}
