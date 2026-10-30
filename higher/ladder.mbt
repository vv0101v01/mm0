///| ## 截斷階梯的量測
///
///| 對每個空間，量出四層資訊與「每下一層丟掉多少」：
///
///|  ```
///|  Π_∞(X)             Π_1(X)            π₁(X)          H₁(X)          C_*(X)
///|  Kan 複形  ──截斷──▶  groupoid ──取基點──▶ 群 ──阿貝爾化──▶ 阿貝爾群 ──▶ 鏈複形
///|  ```
///
///| 丟失量的度量：`|Hom(−, S₃)|`（因為 `S₃` 非阿貝爾，它對非阿貝爾結構敏感）。

///| 一個空間的階梯列。
pub struct LadderRow {
  name : String
  ngen : Int32
  nrel : Int32
  ab : @coeff.Ab
  hom_pi1 : Int32
  hom_h1 : Int32
  h1_from_chain : @coeff.Ab
  ab_matches_chain : Bool
}

///| 由單純複形算出整條階梯。
pub fn ladder_row(name : String, sx : @coeff.Simplex) -> LadderRow {
  let s = sset2_of_simplex(sx)
  let p = pi1_presentation(s)
  let ab = pres_abelianize(p)
  let g = perm_group(3)
  let (hom_pi1, nodes) = hom_count_pruned(p, g)
  let _ = nodes
  let hom_h1 = hom_count_ab(ab, g)
  let hchain = @coeff.homology_z(@coeff.simplex_cc(sx)).groups[1]
  LadderRow::{
    name,
    ngen: p.ngen,
    nrel: p.relators.length(),
    ab,
    hom_pi1,
    hom_h1,
    h1_from_chain: hchain,
    ab_matches_chain: @coeff.ab_eq(ab, hchain),
  }
}

///| 一句話顯示。
pub fn ladder_show(r : LadderRow) -> String {
  let lost = if r.hom_pi1 == 0 {
    0
  } else {
    r.hom_pi1 - r.hom_h1
  }
  "\{r.name}: π₁=<\{r.ngen} 生成元, \{r.nrel} 關係> ab(π₁)=\{@coeff.ab_show(r.ab)} H₁(鏈)=\{@coeff.ab_show(r.h1_from_chain)} 一致=\{r.ab_matches_chain} |Hom(π₁,S₃)|=\{r.hom_pi1} |Hom(H₁,S₃)|=\{r.hom_h1} 丟失=\{lost}"
}

///| 全部模型的階梯表。
pub fn ladder() -> Array[LadderRow] {
  [
    ladder_row("S^2", @coeff.s2()),
    ladder_row("T^2", @coeff.torus()),
    ladder_row("RP^2", @coeff.rp2()),
    ladder_row("S1vS1vS2", @coeff.wedge()),
  ]
}

// ------------------------------------------------------ 群的有限性檢定 ----
///| 「一個有限 Kan 複形能不能有 `π₁ = F₂`」這個問題的極小反例檢查：
///| `F₂` 有表現 `<a,b | >`，阿貝爾化是 `Z²`。當 `S₃` 為目標群時，
///| `|Hom(F₂,S₃)| = 36` 而 `|Hom(Z²,S₃)| = 18`。
pub fn free_group_gap() -> (Int32, Int32) {
  let p = Pres::{ ngen: 2, relators: [] }
  let g = perm_group(3)
  let a = hom_count(p, g)
  let b = hom_count_ab(@coeff.ab_make(2, []), g)
  (a, b)
}

///| 秩 2 自由群的阿貝爾化與原群的同態數差異（= 非阿貝爾資訊的量）。
pub fn cyclicity_witness() -> String {
  let (a, b) = free_group_gap()
  "F₂: |Hom(F₂,S₃)|=\{a}，|Hom(Z²,S₃)|=\{b} —— 差 \{a - b} 個同態只能由非阿貝爾結構看見"
}
