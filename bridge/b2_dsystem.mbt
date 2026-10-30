///| ## B2 —— 原始 `DSystem` 邊界：極大團的認證上界與有限群 2-上閉鏈阻礙的判定
///

///| golden SPEC §四 第二條殘餘邊界：一般 NP-hard 稠密隨機圖的極大團最壞仍受組合

///| 複雜度制約；任意**非阿貝爾**高維通用 HIT 的點相等開盒仍保留形式中性 `DNComp`。
///

///| 合併動作（推遠 + 變化）：

///|  (a) 極大團由「搜尋」變成「搜尋 + 認證上界」。秩界定理

///|      ω(G) ≤ rank_F(I + Ā)

///|      （團 C 在補圖中是獨立集，故 (I+Ā)[C,C] = I，秩 ≥ |C|），

///|      一次消元就給出上界；當上界 = 找到的團大小，最大值即被**證明**，無需遍歷。

///|  (b) 非阿貝爾 HIT 的點相等開盒：在有限群的情形，阻礙類住 H²(G; F_ℓ)，

///|      可由 δ¹、δ² 的秩判定並**枚舉出阻礙基**；`DNComp` 的中性形式因此被

///|      「有限群片段 = 可判定」所收窄。

// ---------------------------------------------------------------- 秩上界 ----

///|
/// 補圖鄰接矩陣加單位（團 → 補圖獨立集 → 主子矩陣為 I）。
fn closed_complement(adj : Array[Array[Int32]]) -> @core.Mat {
  let n = adj.length()
  let rows : Array[Array[Int32]] = []
  for i = 0; i < n; i = i + 1 {
    let row : Array[Int32] = []
    for j = 0; j < n; j = j + 1 {
      let v = if i == j { 1 } else if adj[i][j] == 0 { 1 } else { 0 }
      row.push(v)
      continue
    }
    rows.push(row)
  }
  @core.mat_from_rows(rows)
}

///| ω(G) ≤ rank_F(I+Ā)。取多個素數 rank 的最大值（rank_Fp ≤ rank_Q 恆成立，

///|
/// 故仍是合法上界），並回報跨域一致性。
pub fn clique_rank_bound(adj : Array[Array[Int32]]) -> (Int32, Array[Int32]) {
  let m = closed_complement(adj)
  let primes : Array[Int32] = [10007, 30011, 46327]
  let ranks : Array[Int32] = []
  let mut best : Int32 = 0
  for p in primes {
    let r = @core.rank_mod(m, @core.mk_field(p))
    ranks.push(r)
    if r > best {
      best = r
    }
  }
  (best, ranks)
}

///|
/// 精確極大團（n ≤ 16 的子集枚舉；僅作合併後的對照基準）。
pub fn exact_clique(adj : Array[Array[Int32]]) -> Int32 {
  let n = adj.length()
  let total : Int32 = 1 << n
  let mut best : Int32 = 0
  let mut mask : Int32 = 1
  while mask < total {
    let mut ok = true
    let mut cnt : Int32 = 0
    for i = 0; i < n; i = i + 1 {
      if (mask >> i) % 2 == 1 {
        cnt = cnt + 1
        for j = i + 1; j < n; j = j + 1 {
          if (mask >> j) % 2 == 1 && adj[i][j] == 0 {
            ok = false
          }
        }
      }
    }
    if ok && cnt > best {
      best = cnt
    }
    mask = mask + 1
  }
  best
}

///|
/// 隨機圖（固定種子，可重現）。
pub fn random_graph(
  n : Int32,
  seed : Int32,
  pct : Int32,
) -> Array[Array[Int32]] {
  let rng = @core.rng_seed(seed)
  let adj : Array[Array[Int32]] = []
  for _i = 0; _i < n; _i = _i + 1 {
    adj.push(Array::make(n, 0))
  }
  for i = 0; i < n; i = i + 1 {
    for j = i + 1; j < n; j = j + 1 {
      if @core.rng_below(rng, 100) < pct {
        adj[i][j] = 1
        adj[j][i] = 1
      }
    }
  }
  adj
}

///|
/// 完整 r-部圖：ω = r 恆成立，秩界必緊。
pub fn complete_multipartite(parts : Array[Int32]) -> Array[Array[Int32]] {
  let n : Int32 = parts.fold(init=0, (a, b) => a + b)
  let part_of : Array[Int32] = []
  for i = 0; i < parts.length(); i = i + 1 {
    for _k = 0; _k < parts[i]; _k = _k + 1 {
      part_of.push(i)
    }
  }
  let adj : Array[Array[Int32]] = []
  for _i = 0; _i < n; _i = _i + 1 {
    adj.push(Array::make(n, 0))
  }
  for i = 0; i < n; i = i + 1 {
    for j = 0; j < n; j = j + 1 {
      if i != j && part_of[i] != part_of[j] {
        adj[i][j] = 1
      }
    }
  }
  adj
}

///|
/// 環 C_n。
pub fn cycle_graph(n : Int32) -> Array[Array[Int32]] {
  let adj : Array[Array[Int32]] = []
  for _i = 0; _i < n; _i = _i + 1 {
    adj.push(Array::make(n, 0))
  }
  for i = 0; i < n; i = i + 1 {
    let j = (i + 1) % n
    adj[i][j] = 1
    adj[j][i] = 1
  }
  adj
}

// ------------------------------------------------------- 有限群 2-阻礙 ----

///|
/// 把「列為上鏈座標」的矩陣取轉置，得到「行為座標」的矩陣。
fn rows_by_coord(m : @core.Mat) -> Array[Array[Int32]] {
  let out : Array[Array[Int32]] = []
  for c = 0; c < m.cols; c = c + 1 {
    let row : Array[Int32] = []
    for r = 0; r < m.rows; r = r + 1 {
      row.push(m.data[r * m.cols + c])
    }
    out.push(row)
  }
  out
}

///|
pub struct H2Basis {
  d : Int32
  dim_h2 : Int32
  representatives : Array[Array[Int32]]
  supports : Array[String]
  chain_ok : Bool
}

///| 計算 H²((ℤ/2)^d; F₂) 的**顯式阻礙基**：

///|  1. `h2_compute` 用消元給出 dim Z²、dim B²、dim H² 與鏈條件；

///|  2. 逐個單位向量測試：是否 cocycle（δ²v = 0）、是否 coboundary

///|     （δ¹ᵀμ = v 是否有解）；保留使秩遞增者，直到 dim H²。

///|
/// 這張基表就是 `DNComp` 在有限群片段上「從中性形式退回可判定」所需的資料。
pub fn h2_obstruction_basis(d : Int32) -> H2Basis {
  let moduli : Array[Int32] = []
  for _i = 0; _i < d; _i = _i + 1 {
    moduli.push(2)
  }
  let g = @twist.grp(moduli)
  let ell : Int32 = 2
  let fld = @core.mk_field(ell)
  let (_, _, dim_h2, chain_ok) = @twist.h2_compute(g, ell)
  let d2 = @twist.d2_matrix(g, ell)
  let d1t = @core.mat_transpose(@twist.d1_matrix(g, ell))
  let nv = @twist.var_count(g)
  // B² = δ¹ 的像（以座標向量空間的列集合表示）
  let base_rows = rows_by_coord(d1t)
  let current_rank = @core.gauss_jordan(@core.mat_from_rows(base_rows), fld).rank
  // Z² = ker δ²（消元直接給出基底）；退化情形（δ² 無約束）補上單位向量
  let z2 = @core.nullspace_basis(d2, fld)
  let cands : Array[Array[Int32]] = []
  let mut unit : Int32 = 0
  while unit < nv && z2.length() == 0 {
    let v = Array::make(nv, 0)
    v[unit] = 1
    let img = @core.mat_mul_vec(d2, v, ell)
    let mut closed = true
    for x in img {
      if x % ell != 0 {
        closed = false
      }
    }
    if closed {
      cands.push(v)
    }
    unit = unit + 1
  }
  let pool = if z2.length() > 0 { z2 } else { cands }
  let picks : Array[Array[Int32]] = []
  let supps : Array[String] = []
  for v in pool {
    let rows : Array[Array[Int32]] = []
    for r in base_rows {
      rows.push(r)
    }
    for p in picks {
      rows.push(p)
    }
    rows.push(v)
    let newrank = @core.gauss_jordan(@core.mat_from_rows(rows), fld).rank
    if newrank > current_rank + picks.length() {
      picks.push(v)
      supps.push(support_of(v))
    }
  }
  let _ = nv
  H2Basis::{ d, dim_h2, representatives: picks, supports: supps, chain_ok, }
}

///|
/// 向量支撐的簡短描述。
fn support_of(v : Array[Int32]) -> String {
  let mut out = "{"
  let mut first = true
  for i = 0; i < v.length(); i = i + 1 {
    if v[i] != 0 {
      if !first {
        out = "\{out},"
      }
      out = "\{out}\{i}=\{v[i]}"
      first = false
    }
  }
  "\{out}}"
}

///|
/// B2 的實驗輸出。
pub fn b2_probe() -> Array[String] {
  let out : Array[String] = []
  let structs : Array[(String, Array[Array[Int32]])] = [
    ("K(4,4,4)", complete_multipartite([4, 4, 4])),
    ("K(4,4,4,1)", complete_multipartite([4, 4, 4, 1])),
    ("C_5", cycle_graph(5)),
    ("C_9", cycle_graph(9)),
  ]
  for pair in structs {
    let name = pair.0
    let adj = pair.1
    let w = exact_clique(adj)
    let (b, ranks) = clique_rank_bound(adj)
    out.push(
      "團界 \{name}: omega=\{w} rank_bound=\{b} ranks=\{ints_line(ranks)} tight=\{b == w}",
    )
  }
  let mut tight = 0
  let mut total = 0
  let mut gap_sum : Int32 = 0
  for s = 0; s < 10; s = s + 1 {
    let adj = random_graph(12, 1000 + s, 50)
    let w = exact_clique(adj)
    let (b, _) = clique_rank_bound(adj)
    total = total + 1
    gap_sum = gap_sum + (b - w)
    if b == w {
      tight = tight + 1
    }
  }
  out.push(
    "隨機 G(12,0.5) x10: 認證最優 \{tight}/\{total}，平均界差 \{gap_sum / 10}",
  )
  // 團不交並族（= 補圖為完整多部圖，正是 DSystem 合意區域的形狀）
  let mut ctight = 0
  let rng = @core.rng_seed(20261029)
  for s = 0; s < 10; s = s + 1 {
    let parts : Array[Int32] = [
      @core.rng_below(rng, 5) + 2,
      @core.rng_below(rng, 5) + 2,
      @core.rng_below(rng, 5) + 2,
    ]
    let adj = complete_multipartite(parts)
    let w = exact_clique(adj)
    let (b, _) = clique_rank_bound(adj)
    if b == w {
      ctight = ctight + 1
    }
  }
  out.push(
    "補圖為多部圖 x10（DSystem 合意域族）: 認證最優 \{ctight}/10",
  )
  for d = 1; d <= 4; d = d + 1 {
    let h = h2_obstruction_basis(d)
    let mut supp = ""
    for s in h.supports {
      supp = "\{supp} \{s}"
    }
    out.push(
      "H^2((Z/2)^\{d};F2): dim=\{h.dim_h2} 公式=\{d * (d + 1) / 2} 阻礙基=\{h.representatives.length()}\{supp} chain_ok=\{h.chain_ok}",
    )
  }
  out
}

///| 整數向量單行顯示。
fn ints_line(a : Array[Int32]) -> String {
  let mut out = "["
  for i = 0; i < a.length(); i = i + 1 {
    let t = a[i].to_string()
    out = if i == 0 {
      out + t
    } else {
      out + "," + t
    }
  }
  out + "]"
}
