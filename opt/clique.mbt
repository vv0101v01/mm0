///| ## MILP 自動化：極大團的認證上界
///
///| B2 的殘餘原話是「一般稠密圖上秩界鬆」。這裡用**線性規劃鬆弛**把它收窄，
///| 而且因為 LP 是精確有理數解的，界是**已證明**的（不是浮點算出來的一個數）。
///
///| 鬆弛：`max Σ xᵥ  s.t.  xᵤ + xᵥ ≤ 1  (∀ 非邊 uv),  0 ≤ x ≤ 1`。
///| 任何團都滿足全部約束，所以 LP 最優值 ≥ ω。整數性上界相同，LP 只會更鬆
///| ——但它比「秩界」緊得多，而分支定界用它可以真的**解出** ω。
///
///| 模型可以輸出成 `.lp` 檔案（`milp_lp_text`），交給外部求解器；
///| 但正確性不依賴外部求解器：`lp_max` 用 `@algebra.Rat` 算，`bb_clique` 用同樣的界做分支。

///| 圖：`adj[i][j]` = 1 表示有邊。
pub struct Graph {
  n : Int32
  adj : Array[Array[Int32]]
}

///| 空圖。
pub fn graph_new(n : Int32) -> Graph {
  let adj : Array[Array[Int32]] = []
  for _i = 0; _i < n; _i = _i + 1 {
    let row : Array[Int32] = []
    for _j = 0; _j < n; _j = _j + 1 {
      row.push(0)
    }
    adj.push(row)
  }
  Graph::{ n, adj }
}

///| 加邊。
pub fn graph_add(g : Graph, u : Int32, v : Int32) -> Unit {
  g.adj[u][v] = 1
  g.adj[v][u] = 1
}

///| 由確定性的偽隨機種子建 `G(n, p)`：`p` 用千分比表示，避免浮點。
pub fn graph_random(n : Int32, per_mille : Int32, seed : Int32) -> Graph {
  let g = graph_new(n)
  let mut s = seed
  for i = 0; i < n; i = i + 1 {
    for j = i + 1; j < n; j = j + 1 {
      s = (s * 1103515245 + 12345) % 2147483647
      let a = if s < 0 { 0 - s } else { s }
      let v = a % 1000
      if v < per_mille {
        graph_add(g, i, j)
      }
    }
  }
  g
}

///| 邊數。
pub fn graph_edges(g : Graph) -> Int32 {
  let mut e : Int32 = 0
  for i = 0; i < g.n; i = i + 1 {
    for j = i + 1; j < g.n; j = j + 1 {
      e = e + g.adj[i][j]
    }
  }
  e
}

///| 在頂點子集 `keep` 上的 LP 鬆弛上界（精確有理數）。
pub fn lp_clique_bound(g : Graph, keep : Array[Int32]) -> @algebra.Rat {
  let m = keep.length()
  if m == 0 {
    return @algebra.rat_zero()
  }
  // 局部索引
  let rows : Array[Array[@algebra.Rat]] = []
  let rhs : Array[@algebra.Rat] = []
  for a = 0; a < m; a = a + 1 {
    for b = a + 1; b < m; b = b + 1 {
      if g.adj[keep[a]][keep[b]] == 0 {
        let row : Array[@algebra.Rat] = []
        for k = 0; k < m; k = k + 1 {
          row.push(if k == a || k == b { @algebra.rat_one() } else { @algebra.rat_zero() })
        }
        rows.push(row)
        rhs.push(@algebra.rat_one())
      }
    }
  }
  if rows.length() == 0 {
    // 完全圖
    return @algebra.rat_int(m)
  }
  // **每個變數都要有 `x_v ≤ 1`**：少了它，誘導子圖裡「與所有其他頂點都相鄰」的
  // 那個頂點就沒有任何約束，LP 真的會無界（單純形回 `ok=false`）。
  // 這條是被 G(18,0.6) 的交叉驗證逼出來的。
  for a = 0; a < m; a = a + 1 {
    let row : Array[@algebra.Rat] = []
    for k = 0; k < m; k = k + 1 {
      row.push(if k == a { @algebra.rat_one() } else { @algebra.rat_zero() })
    }
    rows.push(row)
    rhs.push(@algebra.rat_one())
  }
  let c : Array[@algebra.Rat] = []
  for _k = 0; _k < m; _k = _k + 1 {
    c.push(@algebra.rat_one())
  }
  let (opt, _x, ok, _it) = lp_max_iter(m, rows, rhs, c)
  if !ok {
    // 單純形沒收斂（或無界）：回傳**平凡**上界，寧可鬆一點也絕不剪錯。
    // 這條防線是被交叉驗證逼出來的：G(18,0.6) 上 LP 曾回 6 < ω = 7，
    // 於是分支定界把含真解的整個子樹剪掉（`clique_number` 給 5）。
    return @algebra.rat_int(m)
  }
  opt
}

///| LP 上界 + 是否收斂（供分支定界記帳；不收斂時回傳的界是平凡界 `m`）。
pub fn lp_clique_bound_stat(g : Graph, keep : Array[Int32]) -> (@algebra.Rat, Bool, Int32) {
  let m = keep.length()
  if m == 0 {
    return (@algebra.rat_zero(), true, 0)
  }
  let rows : Array[Array[@algebra.Rat]] = []
  let rhs : Array[@algebra.Rat] = []
  for a = 0; a < m; a = a + 1 {
    for b = a + 1; b < m; b = b + 1 {
      if g.adj[keep[a]][keep[b]] == 0 {
        let row : Array[@algebra.Rat] = []
        for k = 0; k < m; k = k + 1 {
          row.push(if k == a || k == b { @algebra.rat_one() } else { @algebra.rat_zero() })
        }
        rows.push(row)
        rhs.push(@algebra.rat_one())
      }
    }
  }
  if rows.length() == 0 {
    return (@algebra.rat_int(m), true, 0)
  }
  for a = 0; a < m; a = a + 1 {
    let row : Array[@algebra.Rat] = []
    for k = 0; k < m; k = k + 1 {
      row.push(if k == a { @algebra.rat_one() } else { @algebra.rat_zero() })
    }
    rows.push(row)
    rhs.push(@algebra.rat_one())
  }
  let c : Array[@algebra.Rat] = []
  for _k = 0; _k < m; _k = _k + 1 {
    c.push(@algebra.rat_one())
  }
  let (opt, _x, ok, it) = lp_max_iter(m, rows, rhs, c)
  if !ok {
    return (@algebra.rat_int(m), false, it)
  }
  (opt, true, it)
}

///| 一支 DFS 的極大團（精確，帶 LP 界）。
fn max_clique_dfs(g : Graph, cand : Array[Int32], cur : Int32, best : Int32) -> Int32 {
  if cand.length() == 0 {
    return if cur > best { cur } else { best }
  }
  // 上界剪枝
  let bound = lp_clique_bound(g, cand)
  let ub = rat_floor(bound)
  if cur + ub <= best {
    return best
  }
  let mut b = best
  let mut rest : Array[Int32] = []
  for i = 0; i < cand.length(); i = i + 1 {
    rest.push(cand[i])
  }
  while rest.length() > 0 {
    // 取第一個
    let v = rest[0]
    let nxt : Array[Int32] = []
    for k = 1; k < rest.length(); k = k + 1 {
      if g.adj[v][rest[k]] == 1 {
        nxt.push(rest[k])
      }
    }
    b = max_clique_dfs(g, nxt, cur + 1, b)
    // 移除 v
    let tail : Array[Int32] = []
    for k = 1; k < rest.length(); k = k + 1 {
      tail.push(rest[k])
    }
    rest = tail
  }
  b
}

///| 有理數取下整（`r ≥ 0`）：用**精確比較**做二分，不經過字串或浮點。
///| （第一版用字串解析 `rat_to_string`，遇到 `9/2` 回 0，於是分支定界把
///|   所有分支都剪掉，`K(3×3)` 的 ω 被算成 1 —— 由暴力枚舉當場抓住。）
pub fn rat_floor(r : @algebra.Rat) -> Int32 {
  if @algebra.rat_sign(r) < 0 {
    return 0 - 1
  }
  let mut hi : Int32 = 1
  while @algebra.rat_cmp_exact(@algebra.rat_int(hi), r) <= 0 && hi < 1073741824 {
    hi = hi * 2
  }
  let mut lo = hi / 2
  while lo + 1 < hi {
    let mid = (lo + hi) / 2
    if @algebra.rat_cmp_exact(@algebra.rat_int(mid), r) <= 0 {
      lo = mid
    } else {
      hi = mid
    }
  }
  lo
}

///| 精確極大團數。
pub fn clique_number(g : Graph) -> Int32 {
  let all : Array[Int32] = []
  for i = 0; i < g.n; i = i + 1 {
    all.push(i)
  }
  max_clique_dfs(g, all, 0, 1)
}

///| 把模型輸出成 LP 檔文字（可直接餵 `glpsol`／`cbc`／`gurobi_cl`）。
pub fn milp_lp_text(g : Graph, name : String) -> String {
  let mut out = "\\ Maximize clique relaxation: \{name}\nMaximize\n obj:"
  for i = 0; i < g.n; i = i + 1 {
    out = "\{out} + x\{i}"
  }
  out = "\{out}\nSubject To\n"
  let mut k = 0
  for i = 0; i < g.n; i = i + 1 {
    for j = i + 1; j < g.n; j = j + 1 {
      if g.adj[i][j] == 0 {
        out = "\{out} ne\{k}: x\{i} + x\{j} <= 1\n"
        k = k + 1
      }
    }
  }
  out = "\{out}Bounds\n"
  for i = 0; i < g.n; i = i + 1 {
    out = "\{out} 0 <= x\{i} <= 1\n"
  }
  out = "\{out}Binary\n"
  for i = 0; i < g.n; i = i + 1 {
    out = "\{out} x\{i}\n"
  }
  out = "\{out}End\n"
  out
}
