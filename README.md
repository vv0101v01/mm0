# golden × notebook — 合併後單一模組 `vv0101v01/golden`

`https://github.com/vv0101v01/mm0` · 提交 `5d47031` · 267 個 `.mbt`／155,058 行 · 41 套件／13 聯邦 · `moon test` 192/192

兩個 MoonBit 庫合併成**一棵樹**：`golden`（cubical-hermitian：精確代數、立方型／Kan 填充、topos／概形）
×  `notebook`（tensorlab：模消元、半環、有限範疇／置換群）。
外加一層新寫的 `bridge/`，把 `SPEC.md` §四 的**七項能力邊界**變成可重跑的量測，
以及一支跨執行的 SHA-256 雜湊鏈帳本。

推上來的只有這棵合併樹：`golden/`、`notebook/` 兩個原倉的全部內容都已在這裡，**不重複推送**。

## 一眼看完（全部可重跑）

| 面向 | 數字 |
|---|---|
| 程式碼 | 267 個 `.mbt`／155,058 行 |
| 架構 | 41 個套件、13 個聯邦、103 條內部依賴邊 |
| 測試 | `moon test` **192 / 192** |
| 定理登記表 | `moon run cmd/main` **116 / 116**（`--time` 逐條計時，總計 ≈ 179 秒） |
| 審計 | `cmd/audit` 16 節／156 行（≈12 秒）；`--full` 340 行（≈3 分 48 秒） |
| 帳本 | 4 個紀元互鎖、36 條記錄、`VERIFY ok=true`、鏈頭 `7182d1b8…` |
| 閘門 | check／test／arch／doc／dead-code／abort／ledger —— 全綠 |

## 七項能力邊界：現況與瓶頸

| 邊界 | 現在的狀態（可重跑） | 真正的瓶頸 |
|---|---|---|
| **B1 Schema** | 層級約束 = 整數差分約束；E1/E2 可行並給最小解，E3 循環升格不可行並給正環見證；B1′ 序數層級＋嚴格 Lift 5/5 | Mahlo／超宇宙需要「對無界算子封閉」的公理，與差分約束不同層級 —— 不可推遠，只能標定（Palmgren 悖論） |
| **B2 DSystem／極大團** | 多部補圖 10/10 認證最優；隨機 `G(12,0.5)` 0/10（平均界差 7，誠實揭露）；`H²((ℤ/2)^d;F₂)` = `d(d+1)/2` | 稠密圖上秩界只是上界；非阿貝爾阻礙不在線性 `H²` 內 |
| **B3 持久層** | 跨程序雜湊鏈：驗證／竄改必抓／冪等／重放；payload 一改即封存舊鏈開新紀元 | 沒有檔案鎖與網路共識（多寫者與分散式不在這層） |
| **B4 精確代數** | 三環分工（`F_p` 螢幕 → ℝ 定位 → ℚ 認證 `2^{−k}`）；n=6/8/10 的 ℝ 偏差 ~1e-10 全落在 ℚ 隔離區間內 | 超越數不可表示；分裂／惰性判定必須避開判別式的素因子 |
| **B5 BDD／SAT／立方** | Tseitin 秩證書；`F₂` 代數正規形：解集指示函數權重 `3^k`（原預測 `2^k` 被計算否決） | ANF 最壞情況是稀疏性爆炸；`n>20` 最佳 ROBDD 順序 NP-hard |
| **B6 球面同倫** | 7 模型 × 6 環可見性表（**ℚ-盲區 4/7**）；UCT 28/28；Bockstein 抓撓率的階；杯積分開 `T²` 與楔和；ℝP² 上 `dim H¹` 與 `dim(H¹⌣H¹)` 在 ℚ/`F₂` 是 0/1 | Hurewicz 只到 π₂；同調＋杯積不足以決定同倫型 |
| **B7 HOU／模組** | 有限載體合一由秩與 `p^{k−rank}` 決定（與暴力全等）；模組連結寫進帳本可重放可撤銷 | Goldfarb 不變：三階以上一般高階合一不可判定 |

完整版（含每一條的殘餘與下一步）見 [`SPEC.md` §4.15.5](SPEC.md)／[`SPEC.en.md`](SPEC.en.md)。

## 執行

```sh
moon check --deny-warn             # 0 error / 0 warning
moon test                          # 192 / 192
moon run cmd/main                  # 116 / 116 定理
moon run cmd/main -- --time        # 逐條計時（總計 ≈ 178 秒）
moon run cmd/audit                 # 16 節／156 行（≈12 秒）
moon run cmd/audit -- --full       # 340 行（≈3 分 48 秒）
moon run cmd/showcase              # 五聯邦 + 加權圖 + 置換→立方往返
sh ledger/audit.sh append          # 跨執行帳本（落盤）
sh ledger/audit.sh verify          # 全鏈重驗（含紀元封條）
```

### 七支閘門（缺一不可）

```sh
moon check --deny-warn
moon test
python3 tools/arch_check.py --check   # 41 套件 / 13 聯邦 / 103 邊
python3 tools/doc_audit.py --check    # 每個 pub 都有文檔
python3 tools/dead_code.py --check    # 自家套件 0 個未引用 pub（基線已清空）
python3 tools/abort_audit.py --check  # 自家套件 0 個 abort（全樹 202 已分類）
sh ledger/audit.sh verify             # VERIFY ok=true
```

## 結構

```
exact/algebra/     精確 BigInt 代數 + 整數小工具（intutil：全樹唯一一份）
symlib/ topos/ scheme/   golden 的三個聯邦（有限範疇／拓樸／概形）
coeff/             係數環一等公民：同調四路（ℚ/ℤ/F_p/ℤ/m）+ Bockstein + 杯積
elim/…             古典消元（core/tensor/nc/twist/gauge/radon/metric）
super/…            ℤ₂ 分次／譜／跨執行雜湊鏈帳本（score/spec/sledger）
semiring/…         半環路徑代數、熱帶、平行後端（native）
higher/ homotopy/ opt/   3-截斷階梯、Brunerie／Steenrod、三界剪枝
bridge/            七邊界計分卡 + 根因表 + 21 條跨庫橋 + 契約測試
cmd/…              6 支可執行包（audit / main / showcase / symbench / symdemo / semiringreport）
ledger/audit.sh    宿主適配器（append / verify / rotate / show / head）
tools/             arch_check / doc_audit / dead_code / abort_audit（四支審計器）
```

## 文檔

| 檔案 | 內容 |
|---|---|
| `SPEC.md` / `SPEC.en.md` | **規格與工程記錄**（含 §4.15 專案現況、七邊界瓶頸、未完成待辦） |
| `MERGE-RESEARCH.md` | 合併研究與 15 輪記錄（為什麼這樣併、哪一步被自己的量推翻） |
| `AGENTS.md` | 給接手者的 46 條坑（每條都付過代價） |
| `DEAD-CODE.md` | 死碼與重複清冊（自動生成） |
| `ABORT-CONTRACTS.md` | `abort(` 逐站點契約表（自動生成，151 條待改清單） |

## 未完成（依優先序）

1. **P0**：`ABORT-CONTRACTS.md` §2 的 151 條公共 `precondition` 改成 `Result`（建議 `scheme` → `topos` → `symlib`）。
2. **P0**：`cmd/main` 前 5 慢的定理加快速模式（178 秒 → ~60 秒）。
3. **P1**：`π₄(S³)≅ℤ/2` 的型別論證明；B2 的 SDP／Lovász 鬆弛；B4 的壞素數表進 API；B5 的 `CheckedDCube` 信任邊界。
4. **P2**：`K_n (n≥6)` 相干塔、完整 1-連通 Blakers–Massey、`phase16_algebra` 職責清理。

授權：Apache-2.0（兩個上游庫同授權）。
