// ===========================================================================
// 連帶相信（belief propagation）：廣義分配律就是「半環上的消去」
//
// Aji–McEliece 的廣義分配律（GDL）說：
//
//   只要 ⊕ 對 ⊗ 分配（也就是半環），因子圖上的邊緣化就可以**局部**做：
//
//       ⊕_{x} [ f(x,y) ⊗ g(x,z) ]  =  ( ⊕_y f(x,y) ) ⊗ ( ⊕_z g(x,z) )
//
// 左邊要做 q³ 次運算，右邊只要 q² + q²。差別不是常數，是**指數**：
// 對 n 個變數、q 個取值的聯合分佈，暴力邊緣化要 q^n，樹上的訊息傳遞只要
//   Σ_f q^{|scope(f)|} 量級。
//
// 本檔把這件事寫成一份**對任意半環都成立**的程式：
//   * 換成 `Prob`（+ / ×）⇒ sum-product，得到邊緣機率；
//   * 換成 `TropMax`（max / +）⇒ max-product（取對數後就是 Viterbi），得到 MAP。
// 同一段訊息傳遞程式，兩種語義。
//
// 誠實的部分（§18 會印）：
//   * 樹上：訊息傳遞**精確**，與 q^n 暴力法逐位元相同。
//   * 有環：BP 只是近似（固定點 ≠ 真邊緣），本庫不掩蓋這件事，
//     而是量出誤差，並在文件裡寫明「有環要用 junction tree / cutset conditioning」。
// ===========================================================================

///|
using @alg {trait Semiring, type Prob, type TropMax}

///|
/// 因子：作用在 `vars` 這些變數上的一張表。
///
/// `table` 的索引方式：把 `vars` 各自的取值當成混合進位數字，
/// 最後一個座標變化最快（row-major）。
pub(all) struct Factor[E] {
  vars : Array[Int32]
  table : Array[E]
}

///|
pub fn[E] Factor::new(vars : Array[Int32], table : Array[E]) -> Factor[E] {
  { vars, table, }
}

///|
/// 因子圖：變數有 `card[v]` 個取值，因子的表長度必須等於 Π card。
pub(all) struct FactorGraph[E] {
  nvar : Int32
  card : Array[Int32]
  factors : Array[Factor[E]]
}

///|
/// 因子表的索引（`assign` 與 `f.vars` 位置對齊）。
pub fn[E] table_index(
  f : Factor[E],
  card : Array[Int32],
  assign : Array[Int32],
) -> Int32 {
  let mut idx = 0
  for p in 0..<f.vars.length() {
    idx = idx * card[f.vars[p]] + assign[p]
  }
  idx
}

///|
/// 把混合進位整數解碼成每個位置的取值。
pub fn decode_assign(
  code : Int32,
  card : Array[Int32],
  vars : Array[Int32],
) -> Array[Int32] {
  let d = vars.length()
  let out : Array[Int32] = Array::make(d, 0)
  let mut c = code
  let mut p = d - 1
  while p >= 0 {
    let q = card[vars[p]]
    out[p] = c % q
    c = c / q
    p = p - 1
  }
  out
}

///|
/// 因子表的大小（Π card）。
pub fn[E] factor_size(f : Factor[E], card : Array[Int32]) -> Int32 {
  let mut s = 1
  for v in f.vars {
    s = s * card[v]
  }
  s
}

///|
/// 訊息傳遞的結果：每個變數的邊緣（未正規化）。
pub(all) struct BpResult[E] {
  /// `marginal[v][x]`
  marginal : Array[Array[E]]
  /// 迭代次數
  rounds : Int32
  /// ⊗ 次數（可驗證的運算量）
  times_ops : Int64
}

///|
/// 廣義分配律的實作：在因子圖上迭代傳遞訊息。
///
///   因子 → 變數：   m_{f→v}[x] = ⊕_{其它變數}  f(...) ⊗ Π_{u≠v} m_{u→f}[x_u]
///   變數 → 因子：   m_{v→f}[x] = Π_{g≠f, g∋v} m_{g→v}[x]
///   邊緣：          b_v[x]     = Π_{g∋v} m_{g→v}[x]
///
/// 樹上跑 `rounds` = 直徑輪即收斂到精確值；有環時它收斂到 BP 固定點，
/// 那是近似值。程式不對此做任何補救或掩蓋。
pub fn[E : Semiring] bp_marginals(
  g : FactorGraph[E],
  rounds~ : Int32 = 32,
) -> BpResult[E] {
  let one = Semiring::one()
  // m_fv[f][p][x]：因子 f 對其第 p 個變數的訊息
  let m_fv : Array[Array[Array[E]]] = []
  for f in g.factors {
    let per_var : Array[Array[E]] = []
    for p in 0..<f.vars.length() {
      per_var.push(Array::make(g.card[f.vars[p]], one))
    }
    m_fv.push(per_var)
  }
  // m_vf[f][p][x]：該變數回傳給 f 的訊息
  let m_vf : Array[Array[Array[E]]] = []
  for f in g.factors {
    let per_var : Array[Array[E]] = []
    for p in 0..<f.vars.length() {
      per_var.push(Array::make(g.card[f.vars[p]], one))
    }
    m_vf.push(per_var)
  }
  let mut times_ops = 0L
  for _ in 0..<rounds {
    // 1. 變數 → 因子
    for fi in 0..<g.factors.length() {
      let f = g.factors[fi]
      for p in 0..<f.vars.length() {
        let v = f.vars[p]
        let acc : Array[E] = Array::make(g.card[v], one)
        for gj in 0..<g.factors.length() {
          if gj == fi {
            continue
          }
          let h = g.factors[gj]
          for q in 0..<h.vars.length() {
            if h.vars[q] == v {
              for x in 0..<g.card[v] {
                acc[x] = Semiring::times(acc[x], m_fv[gj][q][x])
                times_ops = times_ops + 1L
              }
            }
          }
        }
        m_vf[fi][p] = acc
      }
    }
    // 2. 因子 → 變數（這裡就是「局部邊緣化」，也是 GDL 的內容）
    for fi in 0..<g.factors.length() {
      let f = g.factors[fi]
      let d = f.vars.length()
      let size = factor_size(f, g.card)
      for p in 0..<d {
        let v = f.vars[p]
        let out : Array[E] = Array::make(g.card[v], Semiring::zero())
        let mut code = 0
        while code < size {
          let assign = decode_assign(code, g.card, f.vars)
          // 組合：因子值 ⊗ 其他變數傳進來的訊息
          let mut value = f.table[table_index(f, g.card, assign)]
          for q in 0..<d {
            if q != p {
              value = Semiring::times(value, m_vf[fi][q][assign[q]])
              times_ops = times_ops + 1L
            }
          }
          let x = assign[p]
          out[x] = Semiring::plus(out[x], value)
          code = code + 1
        }
        m_fv[fi][p] = out
      }
    }
  }
  // 3. 邊緣
  let marginal : Array[Array[E]] = []
  for v in 0..<g.nvar {
    let acc : Array[E] = Array::make(g.card[v], one)
    for fi in 0..<g.factors.length() {
      let f = g.factors[fi]
      for q in 0..<f.vars.length() {
        if f.vars[q] == v {
          for x in 0..<g.card[v] {
            acc[x] = Semiring::times(acc[x], m_fv[fi][q][x])
            times_ops = times_ops + 1L
          }
        }
      }
    }
    marginal.push(acc)
  }
  { marginal, rounds, times_ops, }
}

// ---------------------------------------------------------------------------
// 兩個具體語義
// ---------------------------------------------------------------------------

///|
/// sum-product：`Prob` 半環上的邊緣，回傳**正規化後**的機率。
pub fn marginals_sum_product(
  g : FactorGraph[Prob],
  rounds~ : Int32 = 32,
) -> (Array[Array[Double]], Int64) {
  let r = bp_marginals(g, rounds~)
  let out : Array[Array[Double]] = []
  for v in 0..<g.nvar {
    let mut z = 0.0
    for x in 0..<g.card[v] {
      z = z + r.marginal[v][x].value()
    }
    let row : Array[Double] = []
    for x in 0..<g.card[v] {
      row.push(if z > 0.0 { r.marginal[v][x].value() / z } else { 0.0 })
    }
    out.push(row)
  }
  (out, r.times_ops)
}

///|
/// max-product（以 log 域表示 ⇒ max-plus）：回傳每個變數的 max-marginal。
pub fn marginals_max_product(
  g : FactorGraph[TropMax],
  rounds~ : Int32 = 32,
) -> (Array[Array[Int32]], Int64) {
  let r = bp_marginals(g, rounds~)
  let out : Array[Array[Int32]] = []
  for v in 0..<g.nvar {
    let row : Array[Int32] = []
    for x in 0..<g.card[v] {
      row.push(r.marginal[v][x].value())
    }
    out.push(row)
  }
  (out, r.times_ops)
}

// ---------------------------------------------------------------------------
// 暴力對照：q^n 列舉，與訊息傳遞無關
// ---------------------------------------------------------------------------

///|
/// 暴力邊緣化（sum-product 版）：列舉所有 q^n 個聯合賦值。
///
/// 回傳 `(marginal, times_ops)`；`times_ops` 是暴力法真正的乘法次數，
/// 用來與訊息傳遞的次數直接比較（這是「複雜度下降」的實測證據）。
pub fn brute_force_sum_product(
  g : FactorGraph[Prob],
) -> (Array[Array[Double]], Int64) {
  let total = total_assignments(g.card)
  let sums : Array[Array[Double]] = []
  for v in 0..<g.nvar {
    sums.push(Array::make(g.card[v], 0.0))
  }
  let mut ops = 0L
  let mut code = 0
  while code < total {
    let assign = decode_assign(code, g.card, all_vars(g.nvar))
    let mut p = 1.0
    for f in g.factors {
      let sub : Array[Int32] = []
      for v in f.vars {
        sub.push(assign[v])
      }
      p = p * f.table[table_index(f, g.card, sub)].value()
      ops = ops + 1L
    }
    for v in 0..<g.nvar {
      sums[v][assign[v]] = sums[v][assign[v]] + p
    }
    code = code + 1
  }
  let out : Array[Array[Double]] = []
  for v in 0..<g.nvar {
    let mut z = 0.0
    for x in 0..<g.card[v] {
      z = z + sums[v][x]
    }
    let row : Array[Double] = []
    for x in 0..<g.card[v] {
      row.push(if z > 0.0 { sums[v][x] / z } else { 0.0 })
    }
    out.push(row)
  }
  (out, ops)
}

///|
/// 暴力邊緣化（max-product 版）。
pub fn brute_force_max_product(
  g : FactorGraph[TropMax],
) -> (Array[Array[Int32]], Int64) {
  let total = total_assignments(g.card)
  let best : Array[Array[Int32]] = []
  for v in 0..<g.nvar {
    best.push(Array::make(g.card[v], -0x3FFF_FFFF))
  }
  let mut ops = 0L
  let mut code = 0
  while code < total {
    let assign = decode_assign(code, g.card, all_vars(g.nvar))
    let mut s = 0
    for f in g.factors {
      let sub : Array[Int32] = []
      for v in f.vars {
        sub.push(assign[v])
      }
      s = s + f.table[table_index(f, g.card, sub)].value()
      ops = ops + 1L
    }
    for v in 0..<g.nvar {
      if s > best[v][assign[v]] {
        best[v][assign[v]] = s
      }
    }
    code = code + 1
  }
  (best, ops)
}

///|
fn all_vars(n : Int32) -> Array[Int32] {
  let out : Array[Int32] = []
  for v in 0..<n {
    out.push(v)
  }
  out
}

///|
/// 聯合賦值的總數 Π card。
pub fn total_assignments(card : Array[Int32]) -> Int32 {
  let mut s = 1
  for c in card {
    s = s * c
  }
  s
}

///|
/// 是否為樹：因子圖的二分圖上 |E| = |V| − 1 且連通（以聯集找集合判斷）。
pub fn[E] is_tree(g : FactorGraph[E]) -> Bool {
  let nv = g.nvar
  let nf = g.factors.length()
  let mut edges = 0
  for f in g.factors {
    edges = edges + f.vars.length()
  }
  if edges != nv + nf - 1 {
    return false
  }
  // 連通性：變數與因子都用同一個 union-find
  let parent : Array[Int32] = Array::make(nv + nf, 0)
  for i in 0..<(nv + nf) {
    parent[i] = i
  }
  for fi in 0..<nf {
    for v in g.factors[fi].vars {
      union(parent, v, nv + fi)
    }
  }
  let root = find(parent, 0)
  for i in 0..<(nv + nf) {
    if find(parent, i) != root {
      return false
    }
  }
  true
}

///|
fn find(parent : Array[Int32], x : Int32) -> Int32 {
  let mut r = x
  while parent[r] != r {
    r = parent[r]
  }
  r
}

///|
fn union(parent : Array[Int32], a : Int32, b : Int32) -> Unit {
  let ra = find(parent, a)
  let rb = find(parent, b)
  if ra != rb {
    parent[rb] = ra
  }
}
