///| ## 實驗探針：把「係數環」變成可讀的數字

///|
/// 幾何模型：`S²`（四面體邊界）。
pub fn s2() -> Simplex {
  simplex_of_faces([[0, 1, 2], [0, 1, 3], [0, 2, 3], [1, 2, 3]])
}

///|
/// 幾何模型：`T²`（3×3 格點三角剖分）。
pub fn torus() -> Simplex {
  let out : Array[Array[Int32]] = []
  for i = 0; i < 3; i = i + 1 {
    for j = 0; j < 3; j = j + 1 {
      let a = i * 3 + j
      let b = (i + 1) % 3 * 3 + j
      let c = (i + 1) % 3 * 3 + (j + 1) % 3
      let e = i * 3 + (j + 1) % 3
      out.push([a, b, c])
      out.push([a, c, e])
    }
  }
  simplex_of_faces(out)
}

///|
/// 幾何模型：6 頂點極小 `RP²`（f-向量 (6,15,10)）。
pub fn rp2() -> Simplex {
  simplex_of_faces([
    [0, 1, 2],
    [0, 1, 3],
    [0, 2, 4],
    [0, 3, 5],
    [0, 4, 5],
    [1, 2, 5],
    [1, 3, 4],
    [1, 4, 5],
    [2, 3, 4],
    [2, 3, 5],
  ])
}

///|
/// 幾何模型：`S¹∨S¹∨S²`（基點 0）。
pub fn wedge() -> Simplex {
  simplex_of_faces([
    [0, 1],
    [1, 2],
    [2, 0],
    [0, 3],
    [3, 4],
    [4, 0],
    [0, 5, 6],
    [0, 5, 7],
    [0, 6, 7],
    [5, 6, 7],
  ])
}

///|
/// 全部模型（幾何 + CW）。
pub fn models() -> Array[(String, ChainComplex)] {
  [
    ("S^2", simplex_cc(s2())),
    ("T^2", simplex_cc(torus())),
    ("RP^2(simp)", simplex_cc(rp2())),
    ("RP^2(CW,deg2)", cw_rp2()),
    ("S1vS1vS2", simplex_cc(wedge())),
    ("M(Z/3,1)", moore_space(3)),
    ("M(Z/5,1)", moore_space(5)),
  ]
}

// --------------------------------------------------------- 可見性表 ----
///|
///| 把整數向量印成 `[a, b, …]`（不用 `Show`，避免 deprecated 警告）。
pub fn ints_show(a : Array[Int32]) -> String {
  let mut out = "["
  for i = 0; i < a.length(); i = i + 1 {
    let t = a[i].to_string()
    out = if i == 0 {
      out + t
    } else {
      out + ", " + t
    }
  }
  out + "]"
}

///| 盲區計數：有幾個模型在 ℚ 下與 ℤ 下給出**不同**的同調（= ℚ 抹平撓率的個數）。
pub fn blindness_count() -> (Int32, Int32) {
  let mut blind : Int32 = 0
  let mut total : Int32 = 0
  for m in models() {
    total = total + 1
    let hz = homology_z(m.1)
    let hq = homology_q(m.1)
    let mut same = true
    for k = 0; k < hz.groups.length(); k = k + 1 {
      if hz.groups[k].free != hq.groups[k].free ||
        hz.groups[k].tors.length() > 0 {
        same = false
      }
    }
    if !same {
      blind = blind + 1
    }
  }
  (blind, total)
}

// ---------------------------------------------------------- UCT 檢查 ----

///|
/// 對每個模型、每個素數做 UCT 交叉驗證（模 p 消元 vs SNF+UCT）。
pub fn uct_probe() -> Array[String] {
  let out : Array[String] = []
  let primes : Array[Int32] = [2, 3, 5, 7]
  for m in models() {
    let name = m.0
    let cx = m.1
    let mut line = "\{name}: chain_ok=\{cc_chain_ok(cx)} rankQ=rankZ=\{rank_paths_agree(cx)}"
    for p in primes {
      let c = uct_check(cx, p)
      line = "\{line}  UCT(p=\{p}):direct=\{ints_show(c.dim_direct)} predicted=\{ints_show(c.dim_predicted)} ok=\{c.ok}"
    }
    out.push(line)
  }
  out
}

// -------------------------------------------------------- Bockstein ----

///| Bockstein 探針：把「秩看不見、Bockstein 看得見」變成數字。

///| 對 `RP²`，`H₂(F₂)` 的生成類 `f`（2-胞腔）應該滿足 `β(f) = e ≠ 0 ∈ H₁`；

///|
/// 對 `S²`、`T²`、`S¹∨S¹∨S²` 則應為 0。
pub fn bockstein_probe() -> Array[String] {
  let out : Array[String] = []
  let cases : Array[(String, ChainComplex, Int32, Int32)] = [
    ("RP^2(CW)", cw_rp2(), 2, 2),
    ("M(Z/3,1)", moore_space(3), 3, 2),
    ("S^2(div 2 於 2-胞腔 0 除外)", simplex_cc(s2()), 2, 2),
    ("T^2", simplex_cc(torus()), 2, 2),
  ]
  for c in cases {
    let name = c.0
    let cx = c.1
    let p = c.2
    let k = c.3
    let r = bockstein_report(cx, p, k)
    let w = if r.dim_cycles_with_beta > 0 {
      ints_show(r.witness)
    } else {
      "—（β 的像全在邊界內 ⇒ 無撓率）"
    }
    out.push(
      "\{name}: p=\{p} k=\{k} dim Z_k=\{r.dim_cycles} dim(im β mod im ∂)=\{r.dim_cycles_with_beta} witness=\{w}",
    )
  }
  // 直接對 RP² 的 2-胞腔算一次，顯示 β(f)=e
  let cx = cw_rp2()
  let f : Array[Int32] = [1]
  let beta = bockstein_of_cycle(cx, 2, 2, f)
  out.push(
    "RP^2: β(2-胞腔) = \{ints_show(beta)}（= 生成 H₁ 的 1-胞腔 ⇒ 2-撓率被 Bockstein 抓到）",
  )
  out
}

// -------------------------------------------------------------- 杯積 ----

///|
/// 杯積探針：`T²` 與 `S¹∨S¹∨S²` 同調相同，但杯積把兩者分開。
pub fn cup_probe() -> Array[String] {
  let out : Array[String] = []
  let cases : Array[(String, Simplex)] = [
    ("T^2", torus()),
    ("S^2", s2()),
    ("S1vS1vS2", wedge()),
  ]
  for c in cases {
    let r = cup_scan(c.1, c.0)
    out.push(
      "\{r.name}: dim H^1=\{r.h1_dim} dim H^2=\{r.h2_dim} 非零 1∪1 的對數=\{r.nonzero_cup} \{r.witness}",
    )
  }
  // 明確對照：兩者 (β₀,β₁,β₂) 完全相同
  let h_t = homology_z(simplex_cc(torus()))
  let h_w = homology_z(simplex_cc(wedge()))
  out.push(
    "同調相同性檢查: T^2 = \{hom_show(h_t)} ； S1vS1vS2 = \{hom_show(h_w)} ； 完全同構=\{ab_eq(h_t.groups[1], h_w.groups[1]) && ab_eq(h_t.groups[2], h_w.groups[2])}",
  )
  out
}

// ------------------------------------------------------------ B4 表 ----

///|
/// 分裂表（B4 的係數環版本）。
pub fn splitting() -> Array[String] {
  splitting_probe()
}

// -------------------------------------------- 可見性表與 ℚ-盲區計數 ----

///| 係數環的可見性：7 個模型 × 6 個環，一張表看完「誰被 ℚ 抹掉」。
///
///| 這是 B6／G1 的核心量測，過去只寫在文檔裡、程式裡沒有入口（`visibility_table`
///| 曾落在「未被引用的 pub」清單上）。現在它有一個探針，接進 `cmd/audit --full`。
pub fn visibility_probe() -> Array[String] {
  let rings : Array[Coeff] = [CQ, CZ, CFp(2), CFp(3), CZm(2), CZm(3)]
  let out = visibility_table(models(), rings)
  let (blind, total) = blindness_count()
  out.push("")
  out.push(
    "ℚ-盲區計數：7 個模型裡有 \{blind}/\{total} 個在 ℚ 下與 ℤ 下不同（撓率被 ⊗ℚ 抹平）—— 這就是 B4／B6 的共同根因 G1 的量化",
  )
  out
}
