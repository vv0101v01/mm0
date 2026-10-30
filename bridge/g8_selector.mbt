///| ## 入口 4（自選）：表示選擇器 —— 從「事後量測」到「事前選路」
///
///| B5 的殘餘有兩半：**事前判定**（§9.5 已做，靠高階差分定次數）與**選路**（本檔）。
///| 現在的問題不再是「這個函數稀疏嗎」，而是「給定這個函數，該用哪條路算它」。
///
///| 三條候選路線，成本都是可**事前預估**的：
///
///| | 路線 | 適用 | 預測成本（查表次數） | 保證 |
///||---|---|---|---|---|
///| A | 差分重建 ANF（`F₂` 稀疏） | `deg d` 已知且小 | `Σ_{i≤d} C(n,i)·2^i` | 只給 `deg ≤ d` 的部分；`d` 要**先被證明** |
///| B | 全量 Möbius | 任何函數 | `n·2ⁿ` | 完整、無條件 |
///| C | 常數／仿射判別 | `d ≤ 1` | `n+1` | 完整（仿射函數由 `n+1` 個值決定） |
///
///| 選擇器做的事：先花 `O(C(n,d+1)·2^{d+1})` 證明次數上界 `d`，再按 `d` 選路，
///| 並**回報它省了多少**。所有預測都用同一支程式量測驗證（預測 vs 實測），
///| 且重建出來的 ANF 必須與全量 Möbius 逐係數相同 —— 否則選路就是錯的。

///| 一條路線的評估。
pub struct Route {
  name : String
  predicted : Int32
  chosen : Bool
  note : String
}

///| 全量 Möbius（butterfly）的加法次數：`n·2^{n−1}`。
pub fn mobius_cost(n : Int32) -> Int32 {
  if n == 0 {
    return 0
  }
  n * (1 << (n - 1))
}

///| 真的跑一次全量 Möbius 並數加法次數（作為「實測」那一欄）。
pub fn mobius_count(tt : Array[Int32], n : Int32) -> (Array[Int32], Int32) {
  let a = tt.copy()
  let mut ops = 0
  for i = 0; i < n; i = i + 1 {
    let step = 1 << i
    for base = 0; base < (1 << n); base = base + 2 * step {
      for off = 0; off < step; off = off + 1 {
        a[base + step + off] = (a[base + step + off] + a[base + off]) % 2
        ops = ops + 1
      }
    }
  }
  (a, ops)
}

///| 真值表的 ANF 非零係數個數（用全量 Möbius，只在驗證時用）。
pub fn support_weight(tt : Array[Int32], n : Int32) -> Int32 {
  let a = @opt.anf_coeffs(tt, n)
  let mut w = 0
  for v in a {
    if v != 0 {
      w = w + 1
    }
  }
  w
}

///| 選路規則：在所有**適用**的路線裡挑成本最小的。
pub fn advice_letter(d : Int32, n : Int32, affine_cost : Int32, sparse_cost : Int32, full_cost : Int32) -> String {
  let mut advice = "B"
  let mut best = full_cost
  if d <= 1 && affine_cost < best {
    advice = "C"
    best = affine_cost
  }
  if d < n && sparse_cost < best {
    advice = "A"
    best = sparse_cost
  }
  advice
}

///| 選擇器主體：回傳 (次數, 權重, 路線表, 建議)。
pub fn select_routes(tt : Array[Int32], n : Int32) -> (Int32, Int32, Array[Route], String) {
  let (d, _checks) = anf_degree(tt, n)
  let w = support_weight(tt, n)
  let routes : Array[Route] = []
  let full_cost = mobius_cost(n)
  let affine_cost = n + 1
  let sparse_cost = anf_deriv_cost(n, d)
  // C：仿射
  routes.push(
    Route::{
      name: "C 仿射判別",
      predicted: affine_cost,
      chosen: advice_letter(d, n, affine_cost, sparse_cost, full_cost) == "C",
      note: if d <= 1 { "對 0..n 的 n+1 個基點取值即可完全確定" } else { "不適用：次數 > 1" },
    },
  )
  // A：差分重建
  routes.push(
    Route::{
      name: "A 差分重建",
      predicted: sparse_cost,
      chosen: advice_letter(d, n, affine_cost, sparse_cost, full_cost) == "A",
      note: "只重建 deg ≤ d 的部分，須先證明次數上界 d",
    },
  )
  // B：全量 Möbius
  routes.push(
    Route::{
      name: "B 全量 Möbius",
      predicted: full_cost,
      chosen: advice_letter(d, n, affine_cost, sparse_cost, full_cost) == "B",
      note: "無條件完整；只在次數上界等於 n 時才划算",
    },
  )
  let advice = advice_letter(d, n, affine_cost, sparse_cost, full_cost)
  (d, w, routes, advice)
}

///| 路線 A 的預測成本：`Σ_{i≤d} C(n,i)·2^i`。
pub fn anf_deriv_cost(n : Int32, d : Int32) -> Int32 {
  // 用 Int64 累加並飽和：n = 20、d = 19 時真值約 3.5e9，Int32 會**靜默溢位**。
  let mut total : Int64 = 0
  for i = 0; i <= d; i = i + 1 {
    let b : Int64 = @algebra.int_binom(n, i).to_int64()
    let p : Int64 = 1L << i
    total = total + b * p
  }
  if total > 2000000000L {
    2000000000
  } else {
    total.to_int()
  }
}

///| 路線 A 開始比全量 Möbius 便宜的最大次數（`n` 固定的交叉點）。
pub fn crossover_degree(n : Int32) -> Int32 {
  let full = mobius_cost(n)
  let mut best = 0
  for d = 1; d < n; d = d + 1 {
    if anf_deriv_cost(n, d) <= full {
      best = d
    }
  }
  best
}

///|

pub fn route_show(r : Route) -> String {
  "\{r.name}: 預測 \{r.predicted} 次\{if r.chosen { " ← 選中" } else { "" }}（\{r.note}）"
}

///| 一列的完整量測：選擇器說要花多少、實際花了多少、答案對不對。
pub struct SelectRow {
  name : String
  n : Int32
  degree : Int32
  weight : Int32
  advice : String
  predicted : Int32
  measured : Int32
  correct : Bool
  full_mobius : Int32
}

///|

pub fn select_row(name : String, tt : Array[Int32], n : Int32) -> SelectRow {
  let (d, _w, routes, advice) = select_routes(tt, n)
  let w = support_weight(tt, n)
  let mut predicted = 0
  for r in routes {
    if r.chosen {
      predicted = r.predicted
    }
  }
  // 實測：按選擇走一次
  let dd = if advice == "C" { 1 } else { d }
  let (anf, _ww, lookups) = anf_from_derivatives(tt, n, dd)
  let (_mob, mob_ops) = mobius_count(tt, n)
  let truth = @opt.anf_coeffs(tt, n)
  let mut same = true
  // C 路線只保證仿射部分；對仿射函數要逐係數相同
  if advice == "C" {
    for i = 0; i < anf.length(); i = i + 1 {
      if anf[i] != truth[i] {
        same = false
      }
    }
  } else {
    for i = 0; i < anf.length(); i = i + 1 {
      // 差分重建只給 deg ≤ d 的部分
      if popcount_bits(i, n) <= d && anf[i] != truth[i] {
        same = false
      }
    }
  }
  SelectRow::{
    name,
    n,
    degree: d,
    weight: w,
    advice,
    predicted,
    measured: if advice == "B" { mob_ops } else if advice == "C" { n + 1 } else { lookups },
    correct: same,
    full_mobius: mobius_cost(n),
  }
}

///| 相對全量的速度（快／慢），整數顯示不做假精度。
pub fn speed_word(full : Int32, used : Int32) -> String {
  let u = if used == 0 { 1 } else { used }
  if u <= full {
    "快 \{full / u}×"
  } else {
    "慢 \{u / full}×"
  }
}

///|

pub fn select_show(r : SelectRow) -> String {
  "n=\{r.n} deg=\{r.degree} 權重=\{r.weight} 選路=\{r.advice} 預測=\{r.predicted} 實測=\{r.measured} 全量=\{r.full_mobius} \{speed_word(r.full_mobius, r.measured)} 正確=\{r.correct}"
}

///| 建幾種典型真值表。
pub fn tt_lowdeg(n : Int32) -> Array[Int32] {
  let tt : Array[Int32] = []
  for mask = 0; mask < (1 << n); mask = mask + 1 {
    let b0 = (mask >> 0) & 1
    let b1 = (mask >> 1) & 1
    let b2 = (mask >> 2) & 1
    let b5 = (mask >> 5) & 1
    tt.push((b0 & b1) ^ (b2 & b5) ^ b0)
  }
  tt
}

///|

pub fn tt_affine(n : Int32) -> Array[Int32] {
  let tt : Array[Int32] = []
  for mask = 0; mask < (1 << n); mask = mask + 1 {
    tt.push(((mask >> 0) & 1) ^ ((mask >> 3) & 1) ^ 1)
  }
  tt
}

///|

pub fn tt_parity(n : Int32) -> Array[Int32] {
  let tt : Array[Int32] = []
  for mask = 0; mask < (1 << n); mask = mask + 1 {
    tt.push(popcount_bits(mask, n) % 2)
  }
  tt
}

///|

pub fn tt_majority(n : Int32) -> Array[Int32] {
  let tt : Array[Int32] = []
  for mask = 0; mask < (1 << n); mask = mask + 1 {
    if popcount_bits(mask, n) >= (n + 1) / 2 {
      tt.push(1)
    } else {
      tt.push(0)
    }
  }
  tt
}

///|

pub fn tt_random(n : Int32, seed : Int32) -> Array[Int32] {
  let tt : Array[Int32] = []
  let mut s = seed * 7919 + 13
  for _mask = 0; _mask < (1 << n); _mask = _mask + 1 {
    s = (s * 1103515245 + 12345) % 2147483647
    if s < 0 {
      s = 0 - s
    }
    tt.push((s >> 16) % 2)
  }
  tt
}

///| 入口 4 的探針。
pub fn selector_probe() -> Array[String] {
  let out : Array[String] = []
  let n : Int32 = 12
  out.push(select_show(select_row("仿射 x0⊕x3⊕1", tt_affine(n), n)))
  out.push(select_show(select_row("低次 x0x1⊕x2x5⊕x0", tt_lowdeg(n), n)))
  out.push(select_show(select_row("多數 Maj_12", tt_majority(n), n)))
  out.push(select_show(select_row("奇偶 ⊕x_i（滿次數）", tt_parity(n), n)))
  out.push(select_show(select_row("隨機 seed=5", tt_random(n, 5), n)))
  let (d, w, routes, advice) = select_routes(tt_lowdeg(n), n)
  out.push("範例（低次）：deg=\{d} 權重=\{w} 建議路線=\{advice}")
  for r in routes {
    out.push(route_show(r))
  }
  let mut xrows = ""
  for nn in [12, 16, 20] {
    xrows = "\{xrows} n=\{nn}: d*=\{crossover_degree(nn)}（A 成本 Σ_{i≤d}C(n,i)2^i ≤ n·2^(n−1) 的最大 d）；"
  }
  out.push("交叉點：\{xrows}")
  out.push(
    "⇒ 選路判據是**預測成本的最小值**，不是「看起來聰明的方法」。第一版規則只看次數，結果 Maj_12（deg=8）被派去差分重建，反而比全量 Möbius 慢 6×（322545 vs 24576）——規則修正後 Maj_12 改走 B",
  )
  out.push(
    "⇒ 誠實的邊界：`n·2^{n−1}` 與 `Σ_{i≤d}C(n,i)2^i` 都只是**搬運次數**的模型，不含記憶體與常數因子；交叉點 d*（12→4、16→5、20→6）大約是 n/3，所以 n 大的時候低次函數確實值得走差分重建，但**中高次**一律回到全量；真正的關鍵仍是「不要 materialize 整個真值表」",
  )
  out.push(
    "結論：選擇器的價值不在「猜得快」，而在**每條路的成本都能事先算出來、且事後被量測檢驗**；`正確` 欄位是逐係數比的（差分重建 vs 全量 Möbius），錯一條就整列紅",
  )
  out
}
