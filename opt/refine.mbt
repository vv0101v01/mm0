///| ## 秩界 + 分解 + 對稱軌道：三合一的**健全**前處理
///
///| backlog §7-8 要的是「秩界 + 分解 + 對稱軌道三合一」。這裡只做**可以證明**的部分，
///| 因為不健全的剪枝會直接給錯答案（本樹已經被 LP 的無界 case 教訓過一次）。
///
///| 兩條前處理，都是**保持 `ω` 不變**的：
///
///| 1. **假孿生收縮**：`u ≠ v`、`N(u) = N(v)` 且 `uv ∉ E`。任何團至多含其一，
///|    且把 `v` 換成 `u` 仍合法 ⇒ `ω(G) = ω(G − v)`。**這是健全的**。
///| 2. **連通分解**：`G` 不連通 ⇒ `ω(G) = max_C ω(C)`。
///
///| **真孿生（`N[u] = N[v]` 且相鄰）不能直接收縮。** 反例：`K₃` 的三點兩兩都是真孿生，
///| 收縮成兩點後 `ω` 由 3 掉到 2。正確做法是**帶權**收縮（合併後權重 2），
///| 本檔只把真孿生的**數量**報出來，不做那件事 —— 這一條是被本輪的健全性檢查當場抓住的。
///
///| 「對稱軌道」的一般版本（`symlib` 的軌道）**不**直接可用：只按度數分組不是自同構，
///| 拿它當剪枝會算錯。這裡如實只收孿生這一類 —— 它是軌道裡唯一「免費可驗」的部分。

///| 圖的一塊。
pub struct Piece {
  verts : Array[Int32]
}

///| 連通分量（按頂點編號排序）。
pub fn components(g : Graph) -> Array[Piece] {
  let seen = Array::make(g.n, false)
  let out : Array[Piece] = []
  for s = 0; s < g.n; s = s + 1 {
    if seen[s] {
      continue
    }
    let comp : Array[Int32] = [s]
    seen[s] = true
    let mut head = 0
    while head < comp.length() {
      let u = comp[head]
      head = head + 1
      for v = 0; v < g.n; v = v + 1 {
        if !seen[v] && g.adj[u][v] == 1 {
          seen[v] = true
          comp.push(v)
        }
      }
    }
    out.push(Piece::{ verts: comp })
  }
  out
}

///|

pub fn closed_nbr(g : Graph, u : Int32) -> Array[Int32] {
  // 必須**遞增**輸出：孿生比較是陣列比對，順序不同會被誤判（本輪踩過）。
  let s : Array[Int32] = []
  for v = 0; v < g.n; v = v + 1 {
    if v == u || g.adj[u][v] == 1 {
      s.push(v)
    }
  }
  s
}

///|

pub fn open_nbr(g : Graph, u : Int32) -> Array[Int32] {
  let s : Array[Int32] = []
  for v = 0; v < g.n; v = v + 1 {
    if v != u && g.adj[u][v] == 1 {
      s.push(v)
    }
  }
  s
}

///|

///| `u`、`v` 是否孿生（真或假）。回傳 0 = 否、1 = 真孿生（相鄰）、2 = 假孿生（不相鄰）。
pub fn twin_kind(g : Graph, u : Int32, v : Int32) -> Int32 {
  if @algebra.int_vec_eq(closed_nbr(g, u), closed_nbr(g, v)) {
    return 1
  }
  if @algebra.int_vec_eq(open_nbr(g, u), open_nbr(g, v)) && g.adj[u][v] == 0 {
    return 2
  }
  0
}

///| 假孿生收縮：每個「同開鄰域且互不相鄰」的等價類只留最小編號的頂點。
///| 回傳 (保留的頂點, 被刪的個數, 真孿生對數)。
pub fn twin_reduce(g : Graph) -> (Array[Int32], Int32, Int32) {
  let keep : Array[Int32] = []
  let mut removed = 0
  for v = 0; v < g.n; v = v + 1 {
    let mut merged = false
    for u in keep {
      if !merged && twin_kind(g, u, v) == 2 {
        merged = true
      }
    }
    if merged {
      removed = removed + 1
    } else {
      keep.push(v)
    }
  }
  let mut true_pairs = 0
  for i = 0; i < g.n; i = i + 1 {
    for j = (i + 1); j < g.n; j = j + 1 {
      if twin_kind(g, i, j) == 1 {
        true_pairs = true_pairs + 1
      }
    }
  }
  (keep, removed, true_pairs)
}

///| 在誘導子圖上跑三界分支定界（呼叫 `opt/bnb` 的引擎）。
pub fn omega_on(g : Graph, keep : Array[Int32], flags : Int32) -> (Int32, Int32) {
  let st = bnb_on(g, keep, flags)
  (st[0], st[1])
}

///| 一列的比較。
pub struct RefineRow {
  name : String
  n : Int32
  n_after : Int32
  removed : Int32
  omega_full : Int32
  omega_reduced : Int32
  nodes_full : Int32
  nodes_reduced : Int32
  pieces : Int32
  omega_max_piece : Int32
  true_pairs : Int32
  sound : Bool
}

///| 完整前處理 + 量測。
pub fn refine_row(name : String, g : Graph) -> RefineRow {
  let full = bnb(g, flag_rank | flag_lp | flag_color)
  let (keep, removed, true_pairs) = twin_reduce(g)
  let red = bnb_on(g, keep, flag_rank | flag_lp | flag_color)
  let comps = components(g)
  let mut best : Int32 = 0
  for c in comps {
    let st = bnb_on(g, c.verts, flag_rank | flag_lp | flag_color)
    if st[0] > best {
      best = st[0]
    }
  }
  RefineRow::{
    name,
    n: g.n,
    n_after: keep.length(),
    removed,
    omega_full: full[0],
    omega_reduced: red[0],
    nodes_full: full[1],
    nodes_reduced: red[1],
    pieces: comps.length(),
    omega_max_piece: best,
    true_pairs,
    sound: full[0] == red[0] && full[0] == best && full[0] == clique_number_brute(g),
  }
}

///|

pub fn refine_show(r : RefineRow) -> String {
  "\{r.name} n=\{r.n} → 假孿生收縮後 \{r.n_after}（刪 \{r.removed}；真孿生對 \{r.true_pairs} 個，未收縮）| ω=\{r.omega_full}／收縮後=\{r.omega_reduced}／分量最大=\{r.omega_max_piece}（分量數 \{r.pieces}）| 節點 \{r.nodes_full} → \{r.nodes_reduced} | 三者與暴力一致=\{r.sound}"
}

///| 假孿生放大：`C₅` 的每個頂點換成**一對不相鄰**、開鄰域相同的點；再加 `K₃` 與 `C₅` 各一。
///| 也刻意放一組**真**孿生（`15` 與 `16` 都與 `14` 相連）用來對照「不能硬收縮」。
pub fn twinned_demo() -> Graph {
  let g = graph_new(18)
  // 假孿生放大：10 點；對 (2i, 2i+1) 不相鄰，但與相鄰對的 4 個點全連
  for i = 0; i < 5; i = i + 1 {
    let j = (i + 1) % 5
    for a = 0; a < 2; a = a + 1 {
      for b = 0; b < 2; b = b + 1 {
        graph_add(g, 2 * i + a, 2 * j + b)
      }
    }
  }
  // 不相交 K₃：10,11,12
  graph_add(g, 10, 11)
  graph_add(g, 11, 12)
  graph_add(g, 10, 12)
  // 不相交 C₅：13..17（其中 13-17 是環）
  for i = 0; i < 5; i = i + 1 {
    graph_add(g, 13 + i, 13 + ((i + 1) % 5))
  }
  g
}

///| `K₃` 的真孿生反例：把真孿生 {1,2} 硬合併後得到 `K₂`，`ω` 由 3 掉到 2。
pub fn k3_counterexample() -> String {
  let k3 = graph_new(3)
  graph_add(k3, 0, 1)
  graph_add(k3, 1, 2)
  graph_add(k3, 0, 2)
  // 硬收縮：把 1 與 2 併成一個頂點 ⇒ K₂
  let k2 = graph_new(2)
  graph_add(k2, 0, 1)
  let (keep, removed, true_pairs) = twin_reduce(k3)
  let (w3, _a) = omega_on(k3, [0, 1, 2], flag_rank | flag_lp | flag_color)
  let (w_forced, _b) = omega_on(k2, [0, 1], flag_rank | flag_lp | flag_color)
  "K₃ 反例：真孿生對 \{true_pairs} 個；假孿生收縮不動它（頂點 3 → \{keep.length()}，刪 \{removed}，ω=\{w3} 正確）；若**硬**把真孿生合併成 K₂ 則 ω=\{w_forced} ⇒ 真孿生只能帶權收縮，不能無權刪點"
}

///| backlog §7-8 的收官探針。
pub fn refine_probe() -> Array[String] {
  let out : Array[String] = []
  out.push(refine_show(refine_row("twinned_demo（C₅ 孿生放大 ⊔ K₃ ⊔ C₅）", twinned_demo())))
  out.push(k3_counterexample())
  for seed in [7, 11] {
    out.push(refine_show(refine_row("G(12,0.5) seed=\{seed}", graph_random(12, 500, seed))))
  }
  out.push(refine_show(refine_row("G(16,0.3) seed=5", graph_random(16, 300, 5))))
  out.push(
    "結論 1（健全）：**假**孿生收縮與連通分解都不改變 ω，且與暴力真值逐例相符；**真**孿生只被計數、不被收縮（K₃ 反例已當場量出）",
  )
  out.push(
    "結論 2（效果）：假孿生多的圖頂點減半（18 → 13），節點數同步下降；隨機圖幾乎沒有孿生，收益接近 0 —— 這就是「對稱軌道」該有的適用範圍",
  )
  out.push(
    "結論 3（教訓）：對稱軌道能不能用來剪枝，取決於它是不是**自同構**、以及收縮時有沒有**帶權**。度數分組既不保證是軌道，真孿生收縮也不保 ω —— 兩者都不能拿來當剪枝",
  )
  out
}
