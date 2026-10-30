///| ## G6 —— 非阿貝爾阻礙：把 `topos` 的 Čech `H¹` 接到 B2（入口 1）
///
///| B2 的殘餘原話是：「非阿貝爾群（`S₃` 及以上）的阻礙不在線性 `H²` 內」。
///| 這句話以前只是宣告；現在它變成一個**可算的比較**：
///
///|  - `topos.classify_group_torsor_cohomology(BG, nerve)` 枚舉全部 `G`- torsor
///|    並按規範等價分類，回傳 `(|Z¹|, |H¹|)`；
///|  - 對阿貝爾 `G = ℤ/3`，`|H¹|` 必然等於 `|Hom(π₁, G)|`（同一個東西的兩種算法）；
///|  - 對非阿貝爾 `G = S₃`，`|H¹|` 是**共軛類**的個數，線性 `H²` 根本無法定義。
///
///| 這就把「線性代數只能處理阿貝爾阻礙」變成一行可重跑的量測。

///| 一個 `(G, 空間)` 的 Čech 分類列。
pub struct CechRow {
  group_name : String
  space_name : String
  n_cocycles : Int32
  n_classes : Int32
  linear_h2 : Int32
  note : String
}

///| 對 `S₃`（`n = 3` 的對稱群）建 `BG`：單一物件、6 個態射。
pub fn bg_symmetric(n : Int32) -> @sym.FinCat {
  @sym.cat_group(@sym.PermGroup::symmetric(n), 64)
}

///| 對 `ℤ/m` 建 `BG`：用 `m` 個點的循環置換群。
pub fn bg_cyclic(m : Int32) -> @sym.FinCat {
  let cyc : Array[Int32] = []
  for i = 0; i < m; i = i + 1 {
    cyc.push((i + 1) % m)
  }
  @sym.cat_group(@sym.PermGroup::new(m, [@sym.Perm::from_cycles(m, [cyc])]), 64)
}

///| 執行一次 Čech 分類。
pub fn cech_row(
  group_name : String,
  gcat : @sym.FinCat,
  space_name : String,
  nerve : @topos.SimplicialNerve,
  linear_h2 : Int32,
  note : String,
) -> CechRow {
  let (z, h) = @topos.classify_group_torsor_cohomology(gcat, nerve)
  CechRow::{ group_name, space_name, n_cocycles: z, n_classes: h, linear_h2, note }
}

///|

pub fn cech_show(r : CechRow) -> String {
  "G=\{r.group_name} X=\{r.space_name}: |Z¹|=\{r.n_cocycles} |H¹|=\{r.n_classes} 線性 H² 給不出=\{r.linear_h2} —— \{r.note}"
}

///| 圓 `S¹` 的三頂點神經：3 個頂點、3 條邊、無三角形。
///| （`classify_group_torsor_cohomology` 對 `|G|^#edges` 枚舉，所以神經必須「小」——
///|   `T²` 的 7 頂點極小三角剖分有 21 條邊，`6^21` 不可能跑完。這本身就是一條邊界。）
pub fn nerve_circle3() -> @topos.SimplicialNerve {
  {
    num_vertices: 3,
    edges: [(0, 1), (0, 2), (1, 2)],
    triangles: [],
    tetrahedra: [],
  }
}

///| 圓盤（可縮）：4 個頂點、5 條邊、2 個三角形。
pub fn nerve_disk() -> @topos.SimplicialNerve {
  {
    num_vertices: 4,
    edges: [(0, 1), (0, 2), (0, 3), (1, 2), (2, 3)],
    triangles: [(0, 1, 2), (0, 2, 3)],
    tetrahedra: [],
  }
}

///| 入口 1 的探針：同一個空間上，阿貝爾與非阿貝爾的分類對照。
pub fn nonabelian_probe() -> Array[String] {
  let out : Array[String] = []
  let circle = nerve_circle3()
  let disk = nerve_disk()
  let c3 = bg_cyclic(3)
  let s3 = bg_symmetric(3)
  out.push(cech_show(cech_row("Z/3", c3, "S^1 (3 邊)", circle, 3, "阿貝爾：|H¹| = |Hom(π₁,Z/3)| = 3，線性 H² 正確")))
  out.push(cech_show(cech_row("S3", s3, "S^1 (3 邊)", circle, 6, "非阿貝爾：|H¹| = 共軛類數 = 3，線性計數會說 6（多算一倍）")))
  out.push(cech_show(cech_row("Z/3", c3, "D^2 (可縮)", disk, 1, "可縮空間：所有 torsor 平凡，|H¹| = 1")))
  out.push(cech_show(cech_row("S3", s3, "D^2 (可縮)", disk, 1, "可縮空間：非阿貝爾也一樣，|H¹| = 1")))
  out.push(
    "結論：線性 `H²` 對非阿貝爾 `G` **根本沒有定義**；Čech `H¹` 有，而且給出的是「共軛類」而非「同態個數」。B2 的殘餘因此從一句宣告變成一個可算的比較：6 vs 3。",
  )
  out
}
