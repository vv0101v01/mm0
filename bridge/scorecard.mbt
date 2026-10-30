///| ## 邊界計分卡 —— 七條邊界作為合併成效的指標
///

///| 每一列是一個「量測」而不只是主張：

///|  `before` 是 golden SPEC §四 的原話（第十六期後的殘餘邊界），

///|  `mode` 是合併對它做了什麼（突破／變化／推遠／剔除／不可動），

///|  `metric` 是可重跑的實測，

///|  `residual` 是誠實剩下的部分——邊界管理不是宣稱消滅，而是標定。

///|
pub struct BoundaryRow {
  id : String
  name : String
  mode : String
  before : String
  after : String
  metric : String
  residual : String
}

///|
pub fn scorecard() -> Array[BoundaryRow] {
  [
    BoundaryRow::{
      id: "B1",
      name: "Schema（大宇宙／索引容器）",
      mode: "變化",
      before: "無界宇宙多態大歸納—遞迴（Mahlo／超宇宙）與一般高階索引容器不在有限層級核心內",
      after: "層級約束 = 整數差分約束系統；可行性、最小解、循環升格阻礙全部由閉包演算法給出並帶證人",
      metric: "E1/E2 可行（最小解 Type0=0,Type1=1,Type2=2,F=1,muF=1），E3 循環升格不可行並輸出正環見證 B→A",
      residual: "Mahlo／超宇宙需要「對無界算子封閉」的公理，差分約束的解集對逐點 min 封閉，兩者不同層級；此角不可推遠，只能標定",
    },
    BoundaryRow::{
      id: "B2",
      name: "原始 DSystem（極大團／非阿貝爾 HIT 開盒）",
      mode: "推遠 + 變化",
      before: "一般 NP-hard 稠密隨機圖的極大團最壞受組合複雜度制約；任意非阿貝爾高維 HIT 的點相等開盒保留形式中性 DNComp",
      after: "極大團有認證上界 ω ≤ rank_F(I+Ā)；有限群 2-阻礙被顯式枚舉成 H² 的障礙基，DNComp 在有限群片段退回可判定",
      metric: "補圖為多部圖族（DSystem 合意域形狀）認證最優 10/10；隨機 G(12,0.5) 認證 0/10（平均界差 7，誠實揭露）；H²((Z/2)^d;F2) 基數 = 1/3/6/10 與公式 d(d+1)/2 全等",
      residual: "一般稠密圖上秩界鬆；非阿貝爾群（S₃ 及以上）的阻礙不在線性 H² 內，仍需群上同調的計算表示",
    },
    BoundaryRow::{
      id: "B3",
      name: "持久層（跨執行帳本）",
      mode: "突破 + 紀元封條",
      before: "記憶體內的帳本；跨程序無狀態、無篡改偵測、無冪等",
      after: "SHA-256 鏈落盤、跨執行驗證、竄改必被抓、JSONL 重放、冪等追加；審計定義演化時以舊鏈頭作封條開新紀元，兩紀元互鎖",
      metric: "四個紀元互鎖（payload 一改即封存舊鏈，新紀元創世記錄把舊鏈頭放進 prev）：目前 36 條記錄、VERIFY ok=true、head 7182d1b8…；竄改 payload/seq 皆 ok=false；重複 append 不再寫入；archive/ 保存全部封存檔",
      residual: "仍無 POSIX 檔案鎖與網路共識；多寫者競態與分散式一致性不在本層",
    },
    BoundaryRow::{
      id: "B4",
      name: "精確代數（位長成長／超越數）",
      mode: "推遠 + 變化 + 根治（係數環）",
      before: "極高維稠密不可約 Hermitian 矩陣的特徵多項式係數位長受本質成長制約；超越數不在 Q̄",
      after: "位長只在 ℚ 這一個環裡成長。三個環分工：F_p 當螢幕（係數恆在 p 位元內）、ℝ 定位（Jacobi O(n³)）、ℚ 認證（隔離區間寬度 2^{−k} 是參數）。CRT 的充分性條件被還原成係數環語句：p ∤ disc",
      metric: "譜表 n=6/8/10：精確係數 6/10/13 位十進位，F_p 平方自由全部 true，ℝ 偏差 ~1e-10 且全部落在 ℚ 隔離區間內（偏差 < 半寬）；分裂表 x²−2,3,5,−1 在 p ≤ 31 上各出現分歧/分裂/惰性；二次互反判據與 Euler 判準、暴力枚舉 24/24 一致",
      residual: "超越數仍不可表示；分裂／惰性判定必須避開判別式的素因子（壞素數可事先算出，但不可消除）",
    },
    BoundaryRow::{
      id: "B5",
      name: "BDD／SAT／宿主立方",
      mode: "剔除（一半）+ 變化 + 根治（係數環）",
      before: "n>20 一般最佳 ROBDD 排序 NP-hard（exact=false）；5 軸以上純黑盒閉包須升級 CheckedDCube",
      after: "換環即換難點：布林格上難在次序（NP-hard），F₂[x]/(x²=x) 上難在稀疏性。仿射輸入的 ANF 就是它自己；k 條獨立線性約束的解集指示函數 ANF 權重 = 3^k（與 n 無關）；決策等價不需任何次序搜尋",
      metric: "Tseitin 12 頂點 15 邊：一致電荷 sat 解數 2^4=16，奇電荷 UNSAT 附秩證書；ANF n=16：線性泛函權重 = 項數（4）；解集指示函數權重 3/9/27/81 = 3^k（原預測 2^k，被計算否決）；一般函數 32625 ≈ 2^15",
      residual: "ANF 的最壞情況是稀疏性爆炸（一般函數 ~2^{n−1}）；5 軸黑盒探針的信任邊界（CheckedDCube）本輪未動",
    },
    BoundaryRow::{
      id: "B6",
      name: "球面同倫與高階相干",
      mode: "變化 + 推遠 + 殘餘收窄（係數環）",
      before: "完整 1-連通高階 Blakers–Massey、撓率同倫群（π₄(S³)≅ℤ/2ℤ）與 n≥6 的 Stasheff K_n 相干塔仍開放",
      after: "係數環升為參數：同一複形在 ℤ／ℚ／F_p／ℤ/m 下的同調四路可算，UCT 交叉驗證，Bockstein 抓到撓率的階；T² 與 S¹∨S¹∨S² 由杯積分開（上一輪的殘餘已收掉）",
      metric: "可見性表 7 模型 × 6 環（ℚ 把 RP² 的 ℤ/2 與 M(ℤ/3,1) 的 ℤ/3 全抹成 0；ℚ-盲區 4/7，已由 `--full` 的 R19 節印出）；UCT 交叉驗證 7×4=28/28 PASS；Bockstein：RP² 2-撓率 1、M(ℤ/3,1) 3-撓率 1、S²/T² 為 0；杯積 T² 9 對非零 vs 楔和 0 對；奇撓率必須用 CW 模型（單純複形造不出 ℤ/3）；第八輪補上 ℚ vs F₂ 的 AW 對照：dim H¹(ℝP²) = 0/1、dim(H¹⌣H¹) = 0/1，分次交換在**上鏈層**只到差一個上邊界（48/48）",
      residual: "Hurewicz 仍只到 π₂；同調+杯積仍不足以決定全部同倫型；π₄(S³) 的 ℤ/2 只被『表示並驗證』，未獲型別論證明",
    },
    BoundaryRow::{
      id: "B7",
      name: "HOU 與模組系統",
      mode: "變化",
      before: "三階以上高階合一受 Goldfarb 限制本質不可判定；模組連結只針對靜態非循環 DAG，無執行期熱載入",
      after: "有限載體片段由秩與 p^{k−rank} 完全決定（仿射合一 = 整數消元）；模組連結事件寫進跨執行雜湊鏈帳本，可重放可撤銷",
      metric: "3 變元 mod 5：rank=2、解數公式 5 = 暴力 5；mod 7 欠定：7 = 7；矛盾式：不可解 0 = 0（三例公式與暴力全等）",
      residual: "無限項代數 + 非仿射約束仍不可判定（Goldfarb 不變）；熱載入止於程序／執行邊界，不是同進程記憶體熱替換",
    },
  ]
}

///|
pub fn scorecard_table() -> String {
  let mut out = "| 邊界 | 名稱 | 動作 | 量測（可重跑） | 殘餘 |\n|---|---|---|---|---|\n"
  for r in scorecard() {
    out = "\{out}| \{r.id} | \{r.name} | \{r.mode} | \{r.metric} | \{r.residual} |\n"
  }
  out
}

// ------------------------------------------------------------ 根因表 ----

///| 係數環作為**共同根因**的處置表。

///|
/// 這張表回答的不是「哪條邊界動了多少」，而是「七條邊界裡有幾條其實是同一個病」。
pub struct RootCauseRow {
  id : String
  symptom : String
  root_cause : String
  cure : String
  metric : String
}

///|
pub fn rootcause() -> Array[RootCauseRow] {
  [
    RootCauseRow::{
      id: "G1",
      symptom: "B4 位長牆、B6 撓率不可見、B7 ℤ/4 上秩失效",
      root_cause: "認證以 ℚ 為中心計算：ℚ 是域且平坦，任何撓率都被 ⊗ℚ 抹平（H₁(RP²;ℚ)=0）",
      cure: "係數環升為一等參數 `Coeff`；每個環用互不相干的演算法（ℚ 有理秩／ℤ Smith／F_p 模消元／ℤ/m 由 UCT 變換），彼此吻合即交叉驗證",
      metric: "可見性表 7 模型 × 6 環；UCT 28/28 PASS；Bockstein 抓到 2- 與 3-撓率；ℚ 下與 ℤ 下同調不同的模型數（見審計的「G1 盲區計數」行）",
    },
    RootCauseRow::{
      id: "G2",
      symptom: "B6 殘餘「同調不足以決定同倫型」",
      root_cause: "同調是 ℤ-模不變量，忘了它上面的乘法結構",
      cure: "Alexander–Whitney 杯積在 F₂ 上實作；決策等價用「杯積是否非零」而非「群是否同構」",
      metric: "T² 有 9 對非零 1∪1；S¹∨S¹∨S² 為 0 對，而同調完全同構（機器驗證）",
    },
    RootCauseRow::{
      id: "G3",
      symptom: "B4「特徵多項式係數位長爆炸」",
      root_cause: "把「必須在 ℚ 上一次算完」當成前提",
      cure: "三環分工：F_p 螢幕（p 位元）→ ℝ 定位（O(n³)）→ ℚ 認證（精度 2^{−k} 是參數）；壞素數 = 判別式素因子，事先算出",
      metric: "n=6/8/10：精確位數 6/10/13 vs F_p 恆定；ℝ 偏差 ~1e-10 全部落在 ℚ 隔離區間內；互反判據 24/24",
    },
    RootCauseRow::{
      id: "G5",
      symptom: "B5「最佳 ROBDD 次序 NP-hard」",
      root_cause: "把布林格 `({0,1},∧,∨,¬)` 當成唯一表示",
      cure: "改用 F₂[x]/(x²=x) 的代數正規形：沒有變數次序這個自由度，稀疏性由秩決定",
      metric: "k 條獨立線性約束的解集指示函數 ANF 權重 = 3^k（k=1..4 實測 3/9/27/81），與 n 無關；一般函數 ≈2^15",
    },
  ]
}

///|
pub fn rootcause_table() -> String {
  let mut out = "| 根因 | 症狀（對應邊界） | 病理 | 治法 | 量測 |\n|---|---|---|---|---|\n"
  for r in rootcause() {
    out = "\{out}| \{r.id} | \{r.symptom} | \{r.root_cause} | \{r.cure} | \{r.metric} |\n"
  }
  out
}
