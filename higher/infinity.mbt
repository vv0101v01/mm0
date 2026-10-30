///| ## 殘餘 2 —— ∞-groupoid：補角是**弱等價**，但填法不唯一
///
///| ∞-groupoid 的定義是 **Kan 複形**：合成不是函數，而是「存在性」；
///| 而存在性的證明（補角）既不唯一、補法本身還要選對，否則**會改變同倫型**。
///
///| 本檔案把這件事做成兩個可算的實驗：
///
///| 1. **复用既有邊去補角**（`reuse` 模式）：把角上缺的那條邊**當成已有的邊**。
///|    這不是 pushout，實測會**殺掉 π₁**（`S¹∨S¹`：`ℤ² → 0`）。
///| 2. **新增一條邊去補角**（`fresh` 模式）：這才是 pushout，實測 `π₁` **不變**。
///
///| 於是「∞-groupoid 的合成」被定位得很精確：**合成 = 在自由生成的邊上取填充**，
///| 而不是在既有邊裡挑一條。挑一條是「嚴格合成」的幻覺，會在 `S¹∨S¹` 上量出 `ℤ² → 0`。
///
///| 第二個量是**填充的非唯一性**：同一個角有幾個候選填充（`max_fillers`）。
///| 非唯一 ⇒ 合成只在 2-胞腔之下唯一 ⇒ 要嚴格化必須一路填到無窮維。

///| 三角形是否存在。
fn tri_present(s : SSet2, t : (Int32, Int32, Int32)) -> Bool {
  for u in s.tris {
    if u == t {
      return true
    }
  }
  false
}

///| 一個缺角：`kind` 0/1/2 對應 `Λ²₀/Λ²₁/Λ²₂`，`a`、`b` 是兩條已知邊，
///| `want` 是缺失那條邊的 (源, 靶)，`fillers` 是既有邊中可用的填充（可能為空）。
pub struct Horn {
  kind : Int32
  a : Int32
  b : Int32
  want : (Int32, Int32)
  fillers : Array[(Int32, Int32, Int32)]
}

///|

fn has_cand(s : SSet2, cands : Array[(Int32, Int32, Int32)]) -> Bool {
  for t in cands {
    if tri_present(s, t) {
      return true
    }
  }
  false
}

///| 列出全部缺角（含候選填充）。
pub fn missing_horns(s : SSet2) -> Array[Horn] {
  let out : Array[Horn] = []
  let ne = s.edges.length()
  for a = 0; a < ne; a = a + 1 {
    for b = 0; b < ne; b = b + 1 {
      if s.degen[a] || s.degen[b] {
        continue
      }
      let (a0, a1) = s.edges[a]
      let (b0, b1) = s.edges[b]
      // Λ²₁（inner）：d0 = a: v1→v2、d2 = b: v0→v1，缺 d1: v0→v2，三角形 (a, c, b)
      if a0 == b1 {
        let cands : Array[(Int32, Int32, Int32)] = []
        for c = 0; c < ne; c = c + 1 {
          let (c0, c1) = s.edges[c]
          if c0 == b0 && c1 == a1 {
            cands.push((a, c, b))
          }
        }
        if !has_cand(s, cands) {
          out.push(Horn::{ kind: 1, a, b, want: (b0, a1), fillers: cands })
        }
      }
      // Λ²₀（outer）：d1 = a: v0→v2、d2 = b: v0→v1，缺 d0: v1→v2，三角形 (c, a, b)
      if a0 == b0 {
        let cands : Array[(Int32, Int32, Int32)] = []
        for c = 0; c < ne; c = c + 1 {
          let (c0, c1) = s.edges[c]
          if c0 == b1 && c1 == a1 {
            cands.push((c, a, b))
          }
        }
        if !has_cand(s, cands) {
          out.push(Horn::{ kind: 0, a, b, want: (b1, a1), fillers: cands })
        }
      }
      // Λ²₂（outer）：d0 = a: v1→v2、d1 = b: v0→v2，缺 d2: v0→v1，三角形 (a, b, c)
      if a1 == b1 {
        let cands : Array[(Int32, Int32, Int32)] = []
        for c = 0; c < ne; c = c + 1 {
          let (c0, c1) = s.edges[c]
          if c0 == b0 && c1 == a0 {
            cands.push((a, b, c))
          }
        }
        if !has_cand(s, cands) {
          out.push(Horn::{ kind: 2, a, b, want: (b0, a0), fillers: cands })
        }
      }
    }
  }
  out
}

///| `reuse` 模式：用既有邊補角（不是 pushout）。
pub fn kan_complete_once(s : SSet2) -> (SSet2, Int32) {
  let horns = missing_horns(s)
  let tris = s.tris.copy()
  let mut added = 0
  for h in horns {
    if h.fillers.length() > 0 {
      tris.push(h.fillers[0])
      added = added + 1
    }
  }
  (SSet2::{ nv: s.nv, edges: s.edges, degen: s.degen, tris }, added)
}

///| `fresh` 模式：每個缺角都**新增一條邊**再補（= pushout）。
pub fn kan_complete_fresh_once(s : SSet2) -> (SSet2, Int32) {
  let horns = missing_horns(s)
  let edges = s.edges.copy()
  let degen = s.degen.copy()
  let tris = s.tris.copy()
  let mut added = 0
  for h in horns {
    let idx = edges.length()
    edges.push(h.want)
    degen.push(false)
    if h.kind == 1 {
      tris.push((h.a, idx, h.b))
    } else if h.kind == 0 {
      tris.push((idx, h.a, h.b))
    } else {
      tris.push((h.a, h.b, idx))
    }
    added = added + 1
  }
  (SSet2::{ nv: s.nv, edges, degen, tris }, added)
}

///|

pub fn kan_complete(s : SSet2, fresh : Bool, max_rounds : Int32) -> (SSet2, Int32) {
  let mut cur = s
  let mut total = 0
  for _r = 0; _r < max_rounds; _r = _r + 1 {
    let pair = if fresh { kan_complete_fresh_once(cur) } else { kan_complete_once(cur) }
    total = total + pair.1
    cur = pair.0
    if pair.1 == 0 {
      break
    }
  }
  (cur, total)
}

///| 2-骨架 `∂Δ³`。
pub fn sset_s2() -> SSet2 {
  sset2_make(
    4,
    [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)],
    [(3, 1, 0), (4, 2, 0), (5, 2, 1), (5, 4, 3)],
  )
}

///| `ℝP²` 的極小三角剖分。
pub fn sset_rp2_min() -> SSet2 {
  sset2_make(1, [(0, 0)], [(0, 0, 0)])
}

///| 兩圓楔和 `S¹ ∨ S¹`。
pub fn sset_wedge2() -> SSet2 {
  sset2_make(1, [(0, 0), (0, 0)], [])
}

///|

pub struct InfRow {
  name : String
  nv : Int32
  ne : Int32
  nt : Int32
  kan_before : Bool
  missing_before : Int32
  max_fillers : Int32
  added : Int32
  kan_after : Bool
  pi1_same : Bool
}

///| 對一個複形跑 reuse 模式（用既有邊補角）。
pub fn inf_row(name : String, s : SSet2) -> InfRow {
  let (kb, mb, _tb) = kan_dim2(s)
  let horns = missing_horns(s)
  let mut maxf = 0
  for h in horns {
    if h.fillers.length() > maxf {
      maxf = h.fillers.length()
    }
  }
  let p0 = @coeff.ab_show(pres_abelianize(pi1_presentation(s)))
  let (done, added) = kan_complete(s, false, 3)
  let (ka, _ma, _ta) = kan_dim2(done)
  let pa = @coeff.ab_show(pres_abelianize(pi1_presentation(done)))
  InfRow::{
    name,
    nv: s.nv,
    ne: s.edges.length(),
    nt: s.tris.length(),
    kan_before: kb,
    missing_before: mb,
    max_fillers: maxf,
    added,
    kan_after: ka,
    pi1_same: p0 == pa,
  }
}

///|

pub fn inf_show(r : InfRow) -> String {
  "\{r.name} [\{r.nv}點/\{r.ne}邊/\{r.nt}面] Kan=\{r.kan_before}(缺\{r.missing_before}角,單角≤\{r.max_fillers}填充) → reuse 補\{r.added} → Kan=\{r.kan_after} H₁不變=\{r.pi1_same}"
}

///| 殘餘 2 的探針。
pub fn infinity_probe() -> Array[String] {
  let nz3 = sset_nerve_group(3, [0, 1, 2, 1, 2, 0, 2, 0, 1], 0)
  let out : Array[String] = []
  out.push(inf_show(inf_row("S¹", sset_circle())))
  out.push(inf_show(inf_row("RP²極小", sset_rp2_min())))
  out.push(inf_show(inf_row("Nerve(Z/3)", nz3)))
  out.push(inf_show(inf_row("S¹∨S¹", sset_wedge2())))
  out.push(inf_show(inf_row("Δ²", sset_delta2())))
  out.push(inf_show(inf_row("S²(6邊)", sset_s2())))
  out.push(fresh_demo("S¹∨S¹", sset_wedge2(), 1))
  out.push(fresh_demo("Δ²", sset_delta2(), 2))
  out.push("結論 1：**在既有邊裡挑一條來補角（reuse）會改變同倫型**——S¹∨S¹ 上 H₁ 由 Z² 掉到 0。嚴格合成的幻覺可以被量出來")
  out.push("結論 2：**新增自由邊再補（fresh / pushout）不改變 H₁**——S¹∨S¹ 上 Z² → Z²。這才是 ∞-groupoid 裡「合成」的語義")
  out.push("結論 3：fresh 補了 1~2 輪之後**仍然不是 Kan**（S¹∨S¹ 仍缺 552 角）⇒ 相干塔不會在有限維停下：這正是 ∞-groupoid 不可截斷的量化版本")
  out.push("結論 4：單角填充數可達 2（S¹∨S¹）⇒ 合成只在 2-胞腔之下唯一；要嚴格化必須一路填到無窮維")
  out
}

///| `fresh` 模式（pushout）在單一複形上的一次實驗。
pub fn fresh_demo(name : String, s : SSet2, rounds : Int32) -> String {
  let p0 = @coeff.ab_show(pres_abelianize(pi1_presentation(s)))
  let (done, added) = kan_complete(s, true, rounds)
  let (ka, ma, _ta) = kan_dim2(done)
  let pa = @coeff.ab_show(pres_abelianize(pi1_presentation(done)))
  "\{name} fresh: 新增 \{added} 條邊+面 → Kan=\{ka}（仍缺 \{ma} 角）H₁ \{p0} → \{pa}（不變=\{p0 == pa}）"
}

///| `fresh` 模式是否保持 `H₁`（供測試呼叫）。
pub fn fresh_pi1_same(name : String, s : SSet2, rounds : Int32) -> Bool {
  let p0 = @coeff.ab_show(pres_abelianize(pi1_presentation(s)))
  let (done, _added) = kan_complete(s, true, rounds)
  let pa = @coeff.ab_show(pres_abelianize(pi1_presentation(done)))
  let _ = name
  p0 == pa
}
