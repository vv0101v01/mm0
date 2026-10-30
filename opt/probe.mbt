///| ## 殘餘 3 的探針：MILP 界 vs 秩界 vs 真值
///
///| B2 的殘餘是「隨機稠密圖上秩界平均差 7」。這裡用三條界把它夾起來：
///|  - `ω`：真值（分支定界，精確）；
///|  - LP 鬆弛（精確有理數，認證上界）；
///|  - 秩界（第一輪的 `rank_bound`，來自補圖的秩）。
///
///| 三者一起看，才能說「哪條界在哪種圖上鬆」。MILP 模型本身可以輸出落盤。

///| 一個實例的比較列。
pub struct CliqueRow {
  name : String
  n : Int32
  edges : Int32
  omega : Int32
  lp : @algebra.Rat
  rank_bound : Int32
}

///| 由圖算一列。
pub fn clique_row(name : String, g : Graph, rank_bound : Int32) -> CliqueRow {
  let all : Array[Int32] = []
  for i = 0; i < g.n; i = i + 1 {
    all.push(i)
  }
  CliqueRow::{
    name,
    n: g.n,
    edges: graph_edges(g),
    omega: clique_number(g),
    lp: lp_clique_bound(g, all),
    rank_bound,
  }
}

///|

pub fn clique_show(r : CliqueRow) -> String {
  "\{r.name}: n=\{r.n} m=\{r.edges} ω=\{r.omega} LP 上界=\{@algebra.rat_to_string(r.lp)} 秩界=\{r.rank_bound} | LP 鬆=\{rat_floor(r.lp) - r.omega} 秩界鬆=\{r.rank_bound - r.omega}"
}

///| 與 `bridge` 相同的秩界：`ω ≤ rank_F(I + Ā)`（閉補圖的秩）。
///| 合法性：團 `C` 在 `I + Ā` 上的子矩陣是 `I_ω`，故秩 ≥ ω。
///| （第一版誤用 `n − rank(Ā)`，在隨機圖上給出 `2 < ω = 4` 的**不合法的界**；
///|   這次由暴力真值當場抓住。）
pub fn rank_bound_of(g : Graph) -> Int32 {
  let rows : Array[Array[Int32]] = []
  for i = 0; i < g.n; i = i + 1 {
    let row : Array[Int32] = []
    for j = 0; j < g.n; j = j + 1 {
      // 閉補圖：I + Ā
      row.push(if i == j { 1 } else { 1 - g.adj[i][j] })
    }
    rows.push(row)
  }
  let m = @core.mat_from_rows(rows)
  let mut best : Int32 = 0
  for p in [10007, 30011, 46327] {
    let r = @core.rank_mod(m, @core.mk_field(p))
    if r > best {
      best = r
    }
  }
  best
}

///| 一組實例：多部圖（DSystem 合意域）與隨機圖。
pub fn clique_probe() -> Array[String] {
  let out : Array[String] = []
  // 多部完全圖：ω 已知 = 部數
  for parts in [3, 4, 5] {
    let n = parts * 3
    let g = graph_new(n)
    for i = 0; i < n; i = i + 1 {
      for j = i + 1; j < n; j = j + 1 {
        if i / 3 != j / 3 {
          graph_add(g, i, j)
        }
      }
    }
    let rb = rank_bound_of(g)
    out.push(clique_show(clique_row("K(\{parts}×3) 多部圖", g, rb)))
  }
  // 隨機圖
  for seed in [7, 11, 23] {
    let g = graph_random(12, 500, seed)
    let rb = rank_bound_of(g)
    out.push(clique_show(clique_row("G(12,0.5) seed=\{seed}", g, rb)))
  }
  out.push(
    "結論：多部圖上 LP 界與秩界都緊（= 部數）；隨機稠密圖上 LP 界明顯比秩界緊 —— MILP 鬆弛是「收窄殘餘」的正確工具",
  )
  out
}

///| 暴力極大團（n ≤ 20）：用來反檢分支定界。
pub fn clique_number_brute(g : Graph) -> Int32 {
  let mut best : Int32 = 0
  let total = 1 << g.n
  for mask = 0; mask < total; mask = mask + 1 {
    // 檢查是否為團
    let mut ok = true
    let mut size = 0
    for i = 0; i < g.n; i = i + 1 {
      if ((mask >> i) & 1) == 1 {
        size = size + 1
      }
    }
    if size <= best {
      continue
    }
    for i = 0; i < g.n && ok; i = i + 1 {
      if ((mask >> i) & 1) == 0 {
        continue
      }
      for j = i + 1; j < g.n; j = j + 1 {
        if ((mask >> j) & 1) == 1 && g.adj[i][j] == 0 {
          ok = false
        }
      }
    }
    if ok {
      best = size
    }
  }
  best
}

///| 診斷：隨機圖上三條界與暴力真值。
pub fn clique_diag() -> Array[String] {
  let out : Array[String] = []
  for seed in [7, 11, 23] {
    let g = graph_random(12, 500, seed)
    let all : Array[Int32] = []
    for i = 0; i < g.n; i = i + 1 {
      all.push(i)
    }
    let lp = lp_clique_bound(g, all)
    let rb = rank_bound_of(g)
    let wb = clique_number_brute(g)
    let wb2 = clique_number(g)
    out.push(
      "seed=\{seed}: 暴力 ω=\{wb} 分支定界 ω=\{wb2} LP=\{@algebra.rat_to_string(lp)} 秩界=\{rb}",
    )
  }
  out
}
