# cubical-hermitian 規格書（SPEC）

語言：**中文正本** · [English](SPEC.en.md) · [中文逐符號附錄](SPEC-APPENDIX.md) · [English appendix](SPEC-APPENDIX.en.md) · [架構](ARCHITECTURE.md)

> **聯邦範圍註記**：本文正文規格化 cubical 支柱（root＋精確 `algebra/`）；
> symlib、semiring、topos、scheme 的長文規格分別見 `docs/symlib.md`、
> `docs/semiring/` 與各聯邦程式碼註解，跨支柱與五聯邦大一統見 `docs/BRIDGE.md` 及 `bridge/`。逐符號附錄則覆蓋
> 全倉 **27 個套件、6,177 個公開符號**。

本文件對專案中**所有型別、算子、結構與規格逐樣**給出：

- **規範形式（canonical / normal form）**：選定的標準代表，相等由比較規範形式判定；
- **範疇化（categorification）**：該物件所屬／所生成的範疇結構（物件、態射、態射合成、函子、自然變換、萬有性或相干律）；
- **判定（decision）**：其主導等式或謂詞的演算法。

程式碼中的 `spec.mbt:spec_registry` 是本文件的條目級登記（121 條）。逐符號
**附錄已拆成生成檔** [SPEC-APPENDIX.md](SPEC-APPENDIX.md)／[SPEC-APPENDIX.en.md](SPEC-APPENDIX.en.md)：
`tools/audit_spec.py` 依 `architecture.json` 讀取每個套件的 `pkg.generated.mbti`
（`moon info`），逐一列出公共宣告、列舉構造子與結構欄位、其規格族與所屬
MoonBit 套件；審計以集合相等保證附錄與介面**無遺漏、無重複、無虛列**。

驗收（在專案根目錄）：

```text
moon info && python3 tools/audit_spec.py --write   # 重新生成附錄並審計
python3 tools/audit_spec.py --check                # 只審計，不改檔
python3 tools/arch_check.py                        # 五聯邦＋大一統依賴層級與檔案唯一歸位
moon check --deny-warn && moon test --release --target wasm-gc && moon run --release cmd/main --target wasm-gc && moon run --release cmd/showcase --target wasm-gc   # 單元測試 15/15、定理 110/110、大一統證書 39/39
```

---

## 一、歷期升級的正式規格

### 1.1 NbE 加 η（`nbe_eta.mbt`）

**型別與規範形式。** 單型別語言 `LTy ::= Bool | Unit | LTy × LTy | LTy → LTy`。
正規形是 **η 長（η-long）βπ-正規形**：`quote_eta` 按型別讀回語義值，

| 型別 | η 規則 | 範形 |
|---|---|---|
| `A → B` | 函數 η：`f ≡ λx. f x` | 一律 λ 開頭，對新中性變量施用後在 `B` 讀回 |
| `A × B` | 積 η：`p ≡ (fst p, snd p)` | 一律配對開頭，兩投影分別在 `A`、`B` 讀回 |
| `Unit` | 單位 η：`u ≡ ()` | 一律 `TmUnit` |
| `Bool` | 無 η（基型別） | 字面量或中性 spine |

**中性 spine 的型別攜帶。** 為了在 stuck 項內部也能 η 展開（例如
`f:(B→B)→B` 的範形是 `λg. f (λx. g x)`），`TNeutral` 的應用節點存參數型別、
投影節點存姊妹分量型別；`quote_tneutral` 因此能在 spine 的每一個位置重建型別。

**雙向程序。** `ty_infer / ty_check` 是句法雙向判定；`eval_infer_t / eval_check_t`
是與之一一對應的雙向求值。未註記 λ 不可推斷，`TmAnn(t, τ)` 提供註記並在求值
時被抹除；範形不含註記。

**範疇化。** 物件是 `LTy`，態射是閉函數項模 βπη，範形 `nf_eta` 是每個態射的
規範代表；這是 `Bool/Unit` 生成的**自由笛卡兒閉範疇（free CCC）**。合成
`tm_comp_at`、恒等 `tm_id_at` 及結合／恒等／逆律以 `def_eq_eta` 驗證
（`check_syntactic_category`）。未型別 NbE（`nbe.mbt`）是同一範疇在 βπ 商下的
較粗版本：其範形是 η 範形的 βπ 化簡；加上積 η 後，先前只能在元素上成立的
`swap ∘ swap = id` 現在在函數層面定義地成立（`check_eta_swap_involution`）。

**判定與單值性。** `nf_eta(nf_eta t) = nf_eta t`（範形冪等）；定義相等
= 範形結構相等。單純型別片斷強正規化，故對良型別輸入終止；不良型別輸入
由 `ty_check` 拒絕（`nf_eta` 回 `None`）。

### 1.2 一般 Glue 的 comp 求值（`glue_comp.mbt`）

**(a) 有限宇宙：端點 comp 算法，對一般數據成立。** 輸入是一條「等價線」
`GlueLineFinite{a_line, t_line, e0, e1, face0, face1}`：任意有限型別線
`A0≃A1`、`T0≃T1`（以 ua 呈現）、端點等價 `eᵢ:Tᵢ≃Aᵢ`、任意面公式 `φᵢ`。
前提是自然性方塊交換 `e₁∘coe_T = coe_A∘e₀`（`glue_line_coherent`，下文範疇化）。
算法是教科書 Glue-comp 的端點形態：

```text
a_raw := coe_A(a₀)                                -- 在 A 中合成未黏部分
若 φ₁ 不可滿足： (t₁, a₁) := (coe_T(t₀), a_raw)
若 φ₁ 可滿足：
    t₁ := coe_T(t₀)        （φ₀ 可滿足時)          -- 在 T 中合成偏部分
        | e₁⁻¹(a_raw)      （φ 僅在 1 出現時)      -- 「φ 亮起」：由 base 反造偏部分
    a₁ := e₁(t₁)                                 -- 校正：A 的帽子改到 e₁(t₁)
```

正確性（`glue_comp_finite_correct`）：輸出在目標 Glue 型別良構；若 φ 兩端皆可滿足，
相干性推出校正是常值的（`a₁ = a_raw`）——這是把「校正路徑存在」落到集合層模型
的相等形式；若 φ 只在 1 亮起，輸出 `base` 仍等於 `a_raw`（由構造）。不相干的線數據
（方塊不交換）以 `None` 拒絕。

**(b) 特徵子空間線：開盒 comp 與 hcomp 校正。** 「型別線」`SubLine` 是
`j ↦ im(P(j))`，`P(j)` 為 Hermitian 冪等；「等價線」`LinEquivLine` 是
`j ↦ U(j)`（秩一時的偏等距 `a(j)t(j)†`，一般地是逐點線性同構之矩陣族）。給定
在給定面上由 `U` 互相搬運的相容開盒（`glue_box_compatible`）：

1. 兩盒先以 ambient 公式填充，再逐點以 `P_T(j)`、`P_A(j)` 剪枝（變動投影線的
   retract Kan 結構，`fill_subline`）；
2. 原始帽子一般不滿足 `U(1)(t_cap) = a_cap`；構造校正方塊
   `(i,k) ↦ (1−k)·a_cap(i) + k·U(1)(t_cap(i))`，其 `k=1` 邊是 Glue 的正確帽子；
3. 側面處差異為零（開盒相容性），故校正不移動規定端點。

此方塊即教科書算法中在 `A` 內做的那次 `hcomp`，在仿射模型中顯式化。
可靠性 `glue_comp_vec_sound` 逐項驗證：填充合邊界、填充落子空間線、校正方塊
落 `A(1)`、帽子端點與 `U(1)` 相容方程。

**範疇化。** (a) 中等價線是**箭頭範疇（arrow category）**`Ty²` 的態射：
物件是等價 `T≃A`，態射是交換方塊；`glue_line_coherent` 判定該方塊。(b) 中
`SubLine` 是 Karoubi 包絡物件上的路徑（投影之連續族），剪枝填充是 retract 在
「值域隨參數變動」時的 Kan 提升。兩者合起來即：Glue 的 comp = 在 A 合成 +
在 T 合成 + 在 A 校正（hcomp），此處三個步驟逐一是函數 `coe_upath/coe_T`、
校正指派與校正方塊。

### 1.3 有限側符號判定（`bdd.mbt`, `wiring.mbt`, `system_symbolic.mbt`）

| 對象 | 舊判定（枚舉） | 新判定（符號） | 規範形 |
|---|---|---|---|
| 面公式 sat/≤/≡ | 2ⁿ 端點掃描 | ROBDD：`sat ⇔ bdd ≠ ⊥`；`f≤g ⇔ f∧¬g = ⊥`；`≡ ⇔ BDD` 結構相等 | 約化有序 BDD |
| 系統商相等 | 逐端點 lookup 比較 | 有效區域 `φᵢ∧¬(前覆蓋)` 的 BDD 區域分割按值合併排序 | `SystemNF` |
| 系統相容 | 交集面枚舉可滿足性 | `face_sat`（內部走 BDD） | — |
| 有限等價 wf/相等 | 逐元素檢查 2^k | wiring 置換性 O(#葉)；相等＝wiring 結構相等 | 帶號置換 `Wiring` |
| `coe` 往返律 | 逐元素往返 | `w;w⁻¹ = id` 的 wiring 等式 | `Wiring` |
| Glue 良構／可靠 | 逐端點、逐元素 | `face_sat`＋單一 BDD 見證；全稱陳述改為截面等式 `w⁻¹;w=id` | BDD＋`Wiring` |

枚舉代碼僅存於：(i) `elems_of` 作為有限型別的語義函數（定義域的列舉本身）；
(ii) `*_extensional / *_oracle` 函數與白箱測試中的暴力 oracle，用作符號判定的
**差分校驗**（differential testing）——它們不是任何庫內判定路徑的一部分。

**範疇化。** BDD 是生成元上面公式自由格的規範代表；wiring 是由
`id/not/swap/×/∘/⁻¹` 生成的**自由對稱冪冪範疇**的態射規範形（對象 `Ty`，
張量 `wiring_prod`，換位 `wiring_swap`，結合子／單位子顯式給出；
五邊形・三角形・六邊形相干律以 wiring 相等驗證，`check_wiring_coherence`）。

**複雜度注記。** ROBDD 在最壞情形指數大小（判定仍是符號化簡驅動而非盲掃描）；
wiring 判定是葉數的線性時間；`face_witness` 沿 BDD 一條到 ⊤ 的路徑讀出見證。

### 1.4 依賴型別 NbE：Π、Σ、宇宙（`nbe_dep.mbt`）

語法 `DTerm` 同時承載項與型別：`DUniv(i)`、`DBoolTy/DUnitTy`、
`DPi/DSigma`（第二分量在綁定子之下）、帶定義域註記的 `DLam`、只能在
check 模式導入的 `DPair`、投影與 `DAnn`；§1.7 在同一語法上再加入
維度、PathP、Kan、資料與 HIT 構造子，§1.8 再加入持久環境、惰性值、
語義系統以及通用歸納/HIT schema 構造子。語義域 `DValue` 中 Π/Σ 的
第二分量是閉包函數 `DValue -> DValue`，故依賴代入即閉包施用，例如
`snd` 的型別是 `B(fst p)` 並以定義方式計算。宇宙採累積層級
`Typeᵢ : Typeᵢ₊₁`，Π/Σ 形成於分量層級的最大值。

轉換與讀回均按型別進行，並同時帶項層級與維度層級：`conv_at/quote_at`
對 Π/Σ/Unit/Path 做 η，
`conv_ty/quote_ty` 處理作為宇宙元素的型別值；中性應用存參數型別，
中性投影存姊妹型別族，因此 spine 內仍有完整的型別導引。單純型別
片斷經 `lty_to_dterm` 嵌入（函數→Π、積→非依賴 Σ）。範疇化是帶族
範疇（categories with families）的句法模型：脈絡延伸是環境與型別
脈絡的平行 cons，代入是閉包施用，規範形是態射／項的標準代表。

### 1.5 Kan 結構推行至全專案型別（`kan_dep.mbt`）

型別線的規範結構是 `DLine{at, coe_fn, fill_fn}`，`comp` 定為
`fill(1)`，外部 `dcoe` 包裝保證 `coe(r,r)` 直接返回原值。構造子
遞迴覆蓋每個型別形成子：Bool/Unit/每層 Universe 為常線；Π 的 coe
在定義域反向傳輸並將餘域取在傳輸所得的參數路徑上；Σ 先傳第一
分量、再沿其路徑傳第二分量；fill/comp 採同一遞迴。依賴族因此以
`(A 中的路徑) -> DLine` 呈現，這正是依賴 comp 所需的數據。單純
型別（LTy）與有限型別（Ty）經非依賴族嵌入；有限 ua 路徑以
`dline_of_upath` 給出非恆常線。其餘專案型別族的 Kan 結構（特徵
空間與子空間線、有限與向量 Glue）由既有模組給出，並一併登記為
`check_kan_all_types`。

### 1.6 特徵值、投影 P 與仿射填充的完全符號代數（`algebra/symalg.mbt`, `algebra/spectral_symbolic.mbt`）

精確標量層由有理數、多變量多項式規範形、其分式與複有序對組成；
矩陣相等、Hermitian 與冪等都是多項式恆等。特徵值是多項式環中的
不同形式原子 λₖ，譜投影為拉格朗日公式 `Pₖ=qₖ(A)/qₖ(λₖ)`，
`qₖ(X)=∏_{j≠k}(X−λⱼ)`。冪等與正交化為單變量恆等
`qₖ²−qₖ(λₖ)qₖ ≡ 0 (mod m)`、`qₖqₗ ≡ 0 (mod m)`，以首一整除驗證；
單位分解與譜分解是多項式恆等 `Σqₖ/qₖ(λₖ)=1` 與
`Σλₖqₖ/qₖ(λₖ)=X`。特徵多項式由 `det(XI−A)` 精確展開，並在一般
Hermitian 2×2、對角特徵值矩陣與秩一投影上核對。

仿射唯一填充以座標原子 `i,j` 直接證明：四角一般雙線性插值與
`square_fill` 在仿射邊上給出的表達式是同一多項式；廣義雙線性
ansatz `k00+i·k10+j·k01+ij·k11` 的繫數可由四角值唯一解出
（差分公式逐項以多項式相等驗證），故在雙線性類中填充唯一。
對非仿射（多項式）邊，`square_fill` 的三個邊界方程仍是在 `i,j`
原子上的恆等；而投影剪枝滿足 `(I−P)(P·F)=0` 的精確恆等。

### 1.7 立方 AST：Path、資料、HIT 與 hcomp 按型別化簡（`nbe_dep.mbt`, `kan_ast.mbt`, `ast_laws.mbt`）

**語法樹。** `DTerm` 新增下列片斷；項變量與維度變量是分離的 de Bruijn
空間，`denv` 是維度環境，`dlevel` 是維度層級。型別線與 tube 都是「在一個
維度綁定子之下的 body」，系統是 `Array[DTubeTerm]`，每分支為
`d_tube(φ, body)`。

```text
PathP A a b       := DPathP(A, a, b)          Path A a b := DPath(A, a, b)
<i> e             := DLamDim(e)               e @ r      := DAppDim(e, r)
coe^j A r→s a     := DCoe(A, r, s, a)
comp^j A [φ↦u] a₀ := DComp(A, [d_tube(φ,u)], a₀)
hcomp A [φ↦u] a₀  := DHComp(A, [d_tube(φ,u)], a₀)
hfill A [φ↦u] a₀  := DHFill(A, [d_tube(φ,u)], a₀, r)   （在維度 r 取值）
```

資料與 HIT 亦在同一 AST：Bool（含 `DBoolElim`）、Nat、List 及各自的依賴
消去子；Circle 的 `base/loop/elim`；Torus 的 `base/loopA/loopB/square/elim`。
Circle 點正規化為 `loop@r`（`r=0,1` 皆為 base）；Torus 點正規化為
`square@(i,j)`，座標 `1` 等同 `0`，即方塊對邊黏合。雙向檢查器逐分支
要求 `tube(0)` 在其面上等於 base，且重疊分支在交面相容。

**Kan 化簡。** `comp_value` 先消去底面分支、頂面分支直接取其在 `1` 的帽，
再在新一般維度取樣型別線並按頭構造子派遣（`hcomp` 是常線的
`comp`）：

| 型別 | `comp` 的定義化簡 |
|---|---|
| `Π x:A. B x` | **反變**：結果是 `λy. comp^j B_j(x_j) [φ↦u_j(x_j)] (f₀ x₀)`，其中 `x_j` 是把目標參數 `y` 沿定義域線**反向填充**所得的路徑 |
| `Σ x:A. B x` | 先合成第一分量並取填充 `a_j=fill^j A [φ↦fst u] (fst a₀)`，第二分量再於線 `B_j(a_j)` 上合成 |
| `PathP A a b` | `<k> comp^j A_j(k) [φ↦u_j@k; k=0↦a_j; k=1↦b_j] (p₀@k)`：原 tube 之外加入隨 `j` 移動的左右**端點分支**，邊界律由此定義地成立 |
| `Universe Typeᵢ` | 空 tube 是恆等；非空 `hcomp` 回傳語義 Glue `Glue[φ₁↦T₁; …; φₙ↦Tₙ] A₀`，完整保留 DSystem；面決定處以 pack/unpack 在 `(partial, base)` 對與端點值之間轉換，多分支 partial 以 `DPartial/DVPartial` 表示 |
| `Glue` | 在 base 與每條 partial 型別分支分別 comp，再以各分支的 partial 填充在目標 base 型別中作 hcomp **校正**；僅目標分支亮起時，該 partial 分量由 base 沿對應 Glue 線反造 |
| `Bool`, `Nat`, `List A` | 按構造子遞迴：Bool 同字面量、Nat 的 `zero/succ`、List 的 `nil/cons`（head 另在元素線上 comp）；`Unit` 恆為 `()`。開放／不一致的宿主系統保留為形式 `DNComp/DNHComp` |
| `Circle`, `Torus` | 全為 base 的系統化簡為 base 點；非平凡 loop/square 系統保留為**形式 hcomp 點**（HIT 的標準 stuck composition） |
| 中性型別線 | 不強行化簡，保留 `DNComp(line, DSystem, base)`，quote 先把系統按值合併排序再完整讀回多分支 tube |

填充與一般 coe 由 comp 定義：
`fill^j A [φ↦u] a₀ @ r = comp^{j∧r} A [φ↦u; r=0↦a₀] a₀`，故在 `0` 是
base、在 `1` 是 comp、在既有面上是 tube 的前綴；`hfill` 是常線版。
`coe(r,r)` 是恆等，`coe(0→1)` 是空 tube 的 comp，反向與任意端點以
`¬j`、`r∨j`、`s∨¬j` 線段及 fill 化約，見
`coe_value`。語義維度/面的頂底與相交不再抽樣，而由既有 ROBDD
謂詞經 `dim_eq_sem`、`face_is_top_sem`、`face_is_bot_sem` 符號判定。

**消去與合成交換。** Bool/Nat/List/Circle/Torus 的依賴消去子在構造子上
按通常 β 律計算；若 scrutinee 是形式 composition，則先取其 filler，把
消去子逐分支作用，再於 `motive(filler j)` 線上 comp（`elim_over_comp`）。
因此例如把常值 Bool motive 的 Circle 消去子作用在形式 hcomp 點上仍會算
到常值，而非卡在 eliminator 外層。

**範疇化。** 這是 cubical CwF 的句法核心片斷：脈絡含項與維度變量，
`PathP` 是沿區間的依賴路徑物件；每一型別構造子保存 Kan 纖維化結構，
上表就是其提升運算。資料型別是帶依賴消去的初始代數；Circle/Torus 是
由點、路徑（及 Torus 的交換方塊）生成的高階歸納物件，其消去子是
motive 的截面。

### 1.8 語義系統重構與通用 schema 生成器（`nbe_dep.mbt`, `schema.mbt`）

#### 1.8.1 持久環境、惰性求值與語義快取

**環境。** 項環境 `DEnv` 與維度環境 `DDimEnv` 均為帶長度的持久連結
串列（`Nil | Cons(value, tail, length)`）。`denv_cons/ddim_cons` 只
新建一個節點並共享原尾部，故脈絡延伸是 O(1)，舊環境永不被改寫；
`DTVar(i)`／維度變量沿串列向外查找。宣告序陣列以
`denv_extend/ddim_extend` 逐一 cons（最後宣告成為索引 0），而公開的
陣列版邊界（例如 `deval(t, Array[DValue])`）只在入口以
`denv_from_array` 轉換一次。

**惰性值。** `DThunk{forced, compute, force_count}` 包作
`DValue::DVThunk`。`lazy_value` 建立未計算值，`force_value` 第一次
執行 `compute` 後把結果（再遞迴 force）存回同一 cell；後續 force 直接
取回，故 `force_count≤1`（`lazy_force_count/lazy_is_forced` 可觀察）。
求值器把函數引數、配對與資料構造子分量、消去子 case、partial 分支
與生成構造子引數放入 thunk，只有型別導向操作需要時才強制。

**快取。** `memo_dim_line` 以 `dim_simplify` 後的 `Dim` Debug 鍵
快取維度線；`memo_family` 以引數在定義域下 `quote_at` 的項 Debug 鍵
快取 Π/Σ 族。快取表是閉包內的關聯陣列，查到的值直接重用；鍵的
穩定性由化簡/引文保證。生成 schema 的 telescope 與 case 型別亦經
同一求值、轉換與引文基礎設施重用。

#### 1.8.2 `DSystem`、partial 值與多分支 Glue

語義 composition 分支不再以裸 `Array[DTubeBranch]` 傳遞，而是封裝為

```text
DSystem{ branches : Array[DTubeBranch] }
DTubeBranch{ face : Face, path : Dim -> DValue }
```

`dsystem_of/dsystem_singleton` 刪除底面並簡化面。給定型別線後，
`dsystem_canonical(level,dlevel,line,system)` 再以端點與一般維度的
型別導向轉換比較 branch paths：body 可轉換者把面以 `FOr` 聯集合併，
其餘類別按一般點 body 的引文鍵（再按面鍵）排序；AST 檢查器為已驗證
相容的 tube 系統套用此範形，quote 與中性 comp 轉換亦然。

值的對應物是 `DPartialValue`／`DValue::DVPartial`，AST 對應
`DPartial(Array[DFaceTerm])`。`partial_normal_form` 按 first-match
語義逐分支計算 BDD 有效區域 `φᵢ∧¬(前覆蓋)`，以 `conv_at` 合併同值
區域、按引文排序，並回傳 `DSystemNF{classes, undefined}`；
`tube_system_nf_at` 是 tube 在指定維度的取樣版。這與向量系統的
`SystemNF` 平行，但區域標籤換成任意依賴語義值。

`DVGlue` 的載荷改為 `(DSystem, base, level)`。`hcomp` 於 Universe
把全部型別分支放入 Glue，不再丟棄第一分支以外的 partial 線；
`DGlueParts.system` 是完整系統，`face` 是其 join，`line` 只保留作
單分支代表線。元素的 partial 分量以 `glue_partial_values` 按語義面
對齊各型別分支，並以 `glue_store_partial` 儲存：單分支沿用 raw 值，
多分支使用 `DVPartial`。檢查、轉換、quote 與 `comp_glue_value` 均
逐分支處理相容、校正與亮起分支；`DPartial` 是只能在 Glue pair 的
第一分量等 check 位置使用的導入形。

#### 1.8.3 通用歸納族 schema

一個歸納族由有限描述子 `DInductiveSpec` 完整給出：名稱、宇宙層級、
參數 telescope、索引 telescope 與構造子列。telescope 型別及構造子
引數型別都是 `DTerm`，其 `DTVar` 只指向 schema 局部綁定子（參數，
其後是先前 telescope/引數項目）。每項構造子引數必為三類之一：

| `DArgKind` | 語義引數型別 | 消去時多給的數據 |
|---|---|---|
| `DArgExternal` | 給定的外部型別 | 無 |
| `DArgRecursive` | 同族在給定索引項處 | 該遞迴引數的 IH |
| `DArgFunction` | `Π a:A. Family(index a)` | `Π a:A. motive(index a, f a)` |

構造子另給結果索引。`inductive_schema_validate` 檢查名稱不重複、
參數/索引 telescopes 可 elaboration、每項引數與遞迴/函數/結果索引
均良型別；外部型別與函數定義域若在句法上提及同名生成族即拒絕，
因此只接受保守的嚴格正性片斷。AST 形式為
`DInductive(spec, params++indices)`、`DIntro(spec, ctor, params, args)`
與 `DInductiveElim(spec, motive, cases, params, indices, scrut)`；
motive 是依序抽象索引與 scrutinee 的巢狀 λ。

生成器自動給出型別形成、構造子推斷、依賴消去、telescope 逐步的
type/value conversion 與 quote。消去在中性 scrutinee 上形成
`DNInductiveElim` 並可完整引文；遇到形式 `DNComp/DNHComp` 時按
型別線逐點取參數/索引，在 motive 中再 composition。當 base 與所有
tube 都是同一構造子時，`comp_inductive_value` 按引數序計算
fillers，並在後續引數型別中代入先前 fillers（即 Σ 的迭代形）；
函數遞迴引數直接由 Π 的 comp 規則完成。構造子不一致或 scrutinee
非 intro 時保留形式 comp。

內建範例為 `nat_schema`、`bool_schema`、`list_schema`（參數）、
`vec_schema`、`fin_schema`（索引）、`tree_schema` 與
`w_schema`（函數遞迴引數）；律涵蓋 Nat 加法、List 長度、Tree
葉數、Vec/Fin 索引正確性、W 的 Π 形 IH，以及 Nat/List/Vec comp。

#### 1.8.4 通用 HIT schema

`DHitSpec` 同樣含參數/索引 telescopes，但生成元是
`DHitCellSpec{name, dim_count, args, result_index, faces}`，其中
`dim_count∈{0,1,2}`，`faces` 按
`(dim0=0, dim0=1, dim1=0, dim1=1)` 排列。`DHitFaceExpr` 以目標
cell、引數項與維度式例示一個面；維度變量沿 `DDimEnv` 解釋
（最後一個 cell 維度是 `DVar(0)`）。`hit_schema_validate` 除共用
telescope/引數/正性檢查外，還逐 face 檢查目標引數型別、結果索引
轉換相等與維度變量範圍；2-cell 另以兩種化簡次序核對四個角落。

AST 形式為 `DHitType`、`DHitIntro(spec, cell, params, args, dims)` 與
`DHitElim`。`hit_cell_value` 是 cell 的智能構造子：先簡化每個維度，
若任一維是端點則例示該 face expression 並遞迴；conversion/quote
亦先正規化端點 cell。給定 motive 後，`hit_case_type` 依序生成
引數與 IH，最後按 cell 維數生成 point 型別、PathP 或巢狀 PathP
方塊型別；其端點值由較低維 face 的消去遞迴給出。消去時先供應
引數/IH，再把 cell 的實際維度逐一施於 case；中性與形式 comp 的
處理與歸納族相同。當 base/tube 恒為同一 cell 且所有 cell 維度沿
comp 線恒定時可逐引數 comp，否則保留形式 hcomp 點。

內建範例為 `circle_schema`、`segment_schema`（兩端點相異）與
`torus_schema`（base、兩 loop、交換 square）；律涵蓋端點正規化、
Circle/segment 的生成路徑消去、Torus square 消去、中性 elim 的
conversion/quote 與同 cell/移動 cell 的 comp 分界。

### 1.9 第六期：原六大邊界的收束

#### 1.9.1 Schema 函子、互歸納、商、宇宙 scheme 與高維 HIT

構造子引數不再侷限於三種硬編碼形狀：`DConstructorArg` 保存完整
`DTerm` 引數型別，並可攜帶 `DConstructorConstraint` 的依賴等式約束。
`DPositiveFunctor ::= Id | Const A | F×G | F+G | List F | Π(a:A),F`
給出可檢查的正性函子語法；`positive_functor_type`、`positive_functor_map`
與 `positive_functor_ih_type` 分別生成解碼型別、遞迴值映射與 decoded
induction hypothesis。巢狀遞迴（如經 `List` 的 rose tree）因此走同一套
引入、消去、轉換、引文與 comp。

正性判定改為結構化極性遞迴：先走訪完整 `DTerm`，記錄族出現的位置、
正/負極性與未知中性應用，透明別名在走訪中展開；負位置與無法證明正性的
中性族應用被拒絕。`DDecode` 把 Tarski 宇宙碼解碼回型別，令型別族與其
遞迴解碼可同時由 schema 生成（歸納—遞迴片斷）。`DMutualFamily` 將多個
分量編譯為以有限和索引的單一 schema，分量型別、構造子與消去子由偏移量
及索引等式還原；`DLevelExpr` 與 inductive/HIT level schemes 把宇宙層級
表示為可求值、可再驗證的 scheme。商型別表示為帶等式 1-cell 的 HIT。
HIT cells 推廣至任意有限維：任一坐標到端點時遞迴代入 face expression，
消去 case 是逐維巢狀 `PathP`；沿移動維度的 comp 在端點與目標維度可精確
判定時刻逐引數計算，否則保留有範形地位的形式中性合成。

#### 1.9.2 原始 `DSystem` 的相容性與 first-match 範形

宿主直接建立的 `DSystem` 不再假定相容。`conv_at_under_face` 把面轉成
BDD 滿足 cubes，在每個 cube 固定的局部維度脈絡下做型別導向轉換；
`dsystem_compatibility_report` 逐一檢查「分支在維度 0 與 base 相合」及
「兩分支在交面相合」，回報第一個衝突的種類與分支編號。`dsystem_checked`
及 `dsystem_checked_of` 是進入 composition 系統的受檢入口。對本質上採
first-match 優先序的原始系統，`DTubeNF` 以互不交疊的有效區域
`φ₁, φ₂∧¬φ₁, …` 分解並按值合併，給出精確語義範形；
`dsystem_first_match_checked` 只在不交化後還能與 base 相容時才提升為
composition 系統。

#### 1.9.3 AST 一等 `Equiv`、`ua` 與 `GlueEquiv`

`Equiv A B` 是 AST 型別形成子，其值由 `fwd : A→B`、`bwd : B→A` 及
section/retraction 兩條路徑證明組成；投影、`mk_equiv_term`、雙向檢查、
型別導向 conversion 與 quote 均遞迴至四個分量。`ua` 把一等等價送至
宇宙中的路徑，其型別線是 primitive `DVGlueEquiv`，沿它的 coe 在兩方向
直接計算為 `fwd`/`bwd`。`GlueEquiv` 的每條分支保存面、partial 型別與
指向 base 的一等等價，不再只保存一條型別線；glue/unglue、端點塌縮、
PathP 與 Kan comp 均保存這些分支資料。

#### 1.9.4 受檢查型別線與 schema 註冊表

`DCheckedTypeLine` 保存已檢查的開放型別 body、脈絡、環境與宇宙層級，
其 `at` 由在指定維度環境下求值 body 得到，故由構造尊重維度代換；
coe/fill/comp 直接派遣 AST Kan 引擎。裸宿主函數 `Dim -> DValue` 仍是
底層語義工具，但可信入口以 checked line 為界。`DSchemaRegistry` 以穩定
鍵 intern inductive/HIT plans，保存驗證結果、一般 telescope 型別及帶
語義引數快照的前綴鏈；schema 驗證與 telescope elaboration 先查表，
hit/miss 計數使重用可觀察。

#### 1.9.5 代數擴張、廣義特徵空間與 Jordan 理論

`QPoly`/`QMat` 提供精確單變量有理多項式與有理矩陣層（primitive
pseudo-remainder gcd、擴張歐氏、Yun squarefree 分解、有理根、特徵與
最小多項式、RREF）。`QuadNum a+b√d` 是二次根式的規範形（`d` 無平方
因數，含去巢平方根）；`AlgNum` 是 `Q[x]/(m)` 的餘式範形，可再基底化到
元素自身的極小多項式。廣義特徵空間由 `(A−λI)ᵏ` 的遞增核、代數/幾何
重數、指數與 Jordan 鏈給出；primary projectors 由互質因子的 Bézout
單位分解生成。Q 上分裂時得到完整 `PJP⁻¹=A`，未分裂部分明確保留殘餘
因子；`AlgMat` 把同一套理論搬到所選代數擴張。

#### 1.9.6 BDD DAG 擴展性與認證數值

面 BDD 的主表示改為 `BddManager` 中的 hash-consed DAG：節點以
`(rank,lo,hi)` 唯一化，apply 以 `(op,a,b)` memoize；同一 manager 內的
相等就是 root ID 相等、sat 就是 root 非 0，大小以 reachable node count
量測。`FaceDecision` 以節點預算把「無法在預算內決定」做為正式結果；
變量次序可在 index、首次出現、頻率與反序候選中選最小 DAG，亦有帶步數
預算的 DPLL sat/eq 後備。數值層的精確對應物是
`QuadC = QuadNum + i·QuadNum` 上的 `CertMat` 與次數至多 2 的係數式
`CertPath`/`CertSquare`：投影性、厄米性、正交分解、特徵空間填充與角落
相干均由精確結構相等驗證；原 `Double` 投影只回報對精確影子的最大偏差
與浮點 residual。`double_dyadic_interval` 給出包住一個 Double 的有理
dyadic 區間。

### 1.10 第七期：遞迴宣告、S³、認證 Jacobi、HOU elaborator 與模組

#### 1.10.1 互相歸納、歸納—遞迴與任意容器函子巢狀遞迴

互歸納與 Tarski 歸納—遞迴沿用 1.9.1 的編譯與 `DDecode`。正性函子
新增依賴多項式/container 節點
`DFunctorContainer(Shape, Positions, index)`，語義為
`Σ(s:Shape), Positions(s) → X(index s p)`；其 IH 型是
`Π(p:Positions(s)), P(index s p, contents p)`，map 逐 position 套用
消去子。`container_tree_schema` 把 Shape/Positions 本身做為族參數，故
同一生成器承載任意有限依賴多項式分支形狀與其巢狀遞迴；形狀/位置
型別不得提及本族，遞迴索引在 shape 與 position 兩綁定子下檢查，
互歸納編譯會把索引加上分量標籤。

#### 1.10.2 球面 `S³`

`suspension_schema` 對無索引 HIT `X` 生成 north、south 與每個
`x:X` 的 meridian 路徑。`sphere2_schema = Susp(circle_schema)`，
`sphere3_schema = Susp(sphere2_schema)`，且 `sphere_schema(n)` 遞迴迭代。
端點 meridian 在 0/1 分別化簡為 north/south；依賴消去、conversion、
quote 與 Kan/hcomp 全部由通用 HIT 生成器提供，恆等消去子在一般
meridian 上計算回自身。

#### 1.10.3 Jacobi 譜迭代的符號區間包含

精確複有理 Hermitian 矩陣先包成複矩形區間矩陣。每步以中點矩陣選
pivot，旋轉的 `|a|`、phase `a/|a|`、`c`、`s` 以有理區間算術和
「整數二分＋精確平方比較」的 sqrt 包絡表示；固定酉矩陣的區間包絡
再做 `J†AJ` 與 `VJ`，每乘一步以 dyadic 外向捨入控制分母並對
Hermitian 包絡對稱化。證書逐旋轉重算：係數包絡包含重算值、
`J†J-I` 區間含 0、after 包含相似變換、transform-after 包含 `VJ`。
最終特徵值是 Hermitian 區間矩陣的 Gershgorin 圓盤，重疊者組成帶
重數的簇。

#### 1.10.4 高階合一與雙向 semantic elaborator

完整高階合一不可判定；實作採 Miller pattern 片斷：
`?F x₁…xₙ` 的 spine 須為相異綁定變量，解由抽象這些變量得到，並
輔以 beta/eta/投影 WHNF、rigid 分解、occurs/scope 檢查、flex-headed
application 與閉項非常規 pattern fallback。命名表面語言 `STerm`
經雙向 `elab_infer/elab_check` 插入 implicit metavariables，求解後
以 `hou_semantic_optimize` 做 beta/投影/Nat 簡化，再譯至 `DTerm`；
Nat eliminator 的 dependent motive 可由預期結果型別以 HOU 解出。
未解 metavariable 的核心被拒絕，成功結果可再由依賴檢查器驗收。

#### 1.10.5 參數化模組、Open/Import 與名字空間

模組是 `params → imports → decls` 的 telescope。elaborator 遞迴
內聯 import：參數以 import 引數代換、目標宣告成為宿主 telescope
entries、逐條以 `d_check` 驗證；模組循環被拒絕。名字 bindings 與
entries 分離，同一個 entry 可由限定名、alias 或 opened/renamed 名
解析；`only/hiding` 篩選、歧義 open 拒絕、opaque export 在跨邊界後
中性化。`module_instantiate` 是函子套用：以閉合參數引數同時代換
整段宣告並逐條閉式檢查，從而把同一證明段抽象後實例化到不同型別。

---
### 1.11 第八期：套件架構、立方體演算法與計算性單值性

#### 1.11.1 套件與元件依賴（`architecture.json`, `algebra/`, `tools/arch_check.py`）

MoonBit 內同一 package 的檔案沒有編譯先後，專案的先後關係是可檢查的依賴 DAG。
實體套件圖為 `cmd/main → root → algebra`。精確代數已是獨立套件
`vv0101v01/cubical-hermitian/algebra`；它不依賴 root。root 以
`algebra_imports.mbt` 的非公開 `using` 集中引入所需 `@algebra` 符號，不把
它們重出口成 root API。`architecture.json` 再把每個 `.mbt` 指派給恰好一個
邏輯元件（L0 `foundation` 至 L9 `app`）；`tools/arch_check.py` 驗證唯一歸位、
實體套件 import、約定元件邊，並成為檔案與行數計數的單一工具來源。`verify.mbt`
位於 registry 層，故全局檢查 `check_kan_all_types` 可跨看模型與覈心而不會令
覈心反向依賴高層。詳細規則與為何不立即拆 `foundation` 見
[ARCHITECTURE.md](ARCHITECTURE.md)。

#### 1.11.2 立方體演算法（`cubical_algorithms.mbt`）

`KanBox{line, system, base, dlevel}` 打包一條語義型別線、一個
`DSystem` 與起點 base；`kan_box_fill` 是其 fill 函數（0 為 base、1 為
組成結果、在 tube 面上與該 tube 一致），`kan_box_comp` 是 cap，
`kan_box_pathp` 把 filler 包成線上的 `PathP` 值。`transport_value`、
`transport_back_value` 分別是沿線向 1／向 0 的 `coe`；
`transport_checked_line_value` 從 `DCheckedTypeLine` 取受檢線。
`transport_filler_value` 是 `i ↦ fill(i)`，`transport_pathp_value`
將它包成 `PathP`：點 `i` 屬 `line(i)`、0 點是原值、1 點是其
transport。`check_cubical_algorithms` 驗證 transport 端點與受檢線、
開盒 filler 在 0 的 base、在面上與 tube 一致，以及其 cap 等於
composition 結果。

路徑值直接以 `DValue` 的維度函數表示。`dpath_at_value` 取點、
`dpath_refl_value` 是常路徑、`dpath_sym_value` 以 `i↦p(¬i)` 反向；
`dpath_prefix_value`、`dpath_segment_value` 分別是 `j↦p(r∧j)` 與
`j↦p(r∨j)` 的前綴／後綴。`dpath_trans_square_value(p,q)` 對
`p:x=y`、`q:y=z` 以顯式 hcomp 構造方塊：組成方向座標 `i` 處的 base
是 `p(i)`，`i=0` 面為起點常值、`i=1` 面為 `q`；其頂邊
`i↦S(i,1)` 是 `dpath_trans_value`。`dpath_cong_value`（`ap`）
逐點施用函數，`dpath_funext_value` 把逐點路徑值交換為函數路徑，
`subst_value` 是 `coe^{j.B(p j)} v`，`subst_pathp_value` 是遠端為該
subst 的依賴路徑。這些運算只派遣核心 `coe_value`／`fill_value`／
`comp_value`，不另造平行 Kan 引擎。

閉項層有 `dtransport_term`、`dtransport_back_term`、path
refl/sym/cong、hcomp-square 的 `dpath_trans_term` 與
`dfunext_term` builders；`check_cubical_algorithms` 會把代表性閉項
再送入 `dep_check_closed`，並以型別導向 conversion 檢查語義端點。
規格登記見 `spec_registry` 的「立方體演算法」條目。

#### 1.11.3 計算性單值性（`univalence.mbt`）

**有限宇宙。** `UPath` 本身以 wiring 等價呈現，故
`upath_to_equiv` 直接取得該等價，`upath_refl/sym/trans` 是其路徑代數，
`finite_transport` 是沿路徑的傳輸。`check_finite_univalence`
在等價案例集上以 wiring 結構相等驗證兩邊往返以及兩個方向的
transport 計算；這是有限型別 `Bool`／`Unit`／積宇宙中的完全判定。

**語義 AST。** 對一條語義型別線 `L`，`path_to_equiv_value` 以
`coe 0→1` 為前向函數、`coe 1→0` 為反向函數；兩條往返證明由
`transport_roundtrip_path_value`（以及反向版本）利用 transport filler
組成，故得到一等 `DVEquiv` 值。`equiv_to_universe_path_value`
是既有 `ua_value` 的 Glue 線在本層的具名入口；
`ua_transport_value` 是沿 `ua(e)` 的 transport。
`ua_beta_path_value` 把沿 Glue 線的 transport filler unglue，得到
`dst` 中由 `equivFun e x` 至 `transport (ua e) x` 的路徑；
`ua_beta_back_path_value` 從反向 filler 的 partial 分量得到反方向的
對應律。端點中嵌套的 Glue 表示會以遞迴塌縮正規化。

兩條往返律分開見證。`univalence_retr_path_value` 對前／後函數以
`uaβ` 同倫插值，其 section／retraction 分量由 path congruence、
homotopy segment 與原證據組裝，給出 `Equiv src dst` 中的
`pathToEquiv (ua e) = e`。`univalence_sect_square_value` 是二維
Glue 方塊：`i=0` 邊是 `ua(pathToEquiv L)` 線、`i=1` 邊是 `L`、
`j=0`／`j=1` 邊恒為 `src`／`dst`；內部是以 `dst` 為 base 的
Glue，`j=0` 分支為 `(src,pathToEquiv L)`，`i=1∨j=1` 分支為
`(L(j), segment equivalence L(j)≃dst)`。
`univalence_equiv_value` 再把 `pathToEquiv` 與 `ua` 及這兩組見證包裝成
語義域 `DVEquiv`，型別為
`(Equiv A B) ≃ Path (Type level) A B` 的證書。

**受檢線與閉項。** `UniversePath` 保存一個 `DCheckedTypeLine`、
已完全塌縮的端點型別與宇宙層級；`universe_path_of_ua_term_closed`
從閉合等價項取得 checked ua 線。`universe_path_path_value`、
`universe_path_to_equiv_value` 與
`universe_path_normal_form = ua(pathToEquiv p)` 給出路徑值、傳輸等價
與範形；`universe_path_transport_conv` 以端點及傳輸等價均可轉換來判定
宇宙路徑的單值性相等。閉項側 `path_to_equiv_term` 生成 `DMkEquiv`，
其 round-trip 證據同為 fill/coe 組成；`ua_map_term` 與
`path_to_equiv_map_term` 是 0 層宇宙兩方向的映射。
`check_univalence` 串連有限側、語義 uaβ 與兩條往返、checked 宇宙路徑
與閉項驗收。

**陳述範圍。** 這裡的 `Equiv` 仍是 section／retraction 型的
quasi-inverse 證書；核心 conversion 對 `DVEquiv` 只比較 fwd/bwd，
proof 分量按命題性內容處理。故所得是本可執行語義中經 coe/comp/fill
驗證的計算性 quasi-inverse 單值性證書，不宣稱為帶 contractible-fiber
刻畫與全部高階相干的 HoTT 單值性形式定理，也不是加進邏輯的公理。
---

### 1.12 第九期：完備精確代數、一等宣告、同倫代表元與分離編譯

第九期按第八期 §4 的列明邊界逐項推進。下列每一小節都以
`verify.mbt` 中新的登記列與白箱測試驗收；沒有完成的部分在
更新後的 §4 明示，不以代表元或數值觀察冒充一般定理。

#### 1.12.1 精確代數完備化（`algebra/qpoly_factor.mbt`, `algebra/root_isolation.mbt`, `algebra/splitting_field.mbt`, `algebra/radical_denest.mbt`, `algebra/Jacobi_interval.mbt`）

`Rat` 與所有多項式／矩陣係數改用任意精度 `BigInt`，正規化後不再
受 `Int32` 係數溢出限制。`qpoly_factor_complete` 回傳首項係數與
不可約因式連同重數的完整因式分解；預算版本明示 `budget < 0`
為無限、`budget = 0` 不允許任何 Kronecker tuple、正值為 tuple
上限。實根以 Sturm 序列隔離並可任意細化。複根先可用
Durand–Kerner 產生候選，但完備性不依賴浮點搜尋：每個 Yun
squarefree 因子若未得到與次數相同的兩兩不交 Rouché 圓盤，
`complex_subdivision_complete` 會在 Cauchy 正方形上以精確
Taylor 排除、圓盤認證與二分細分補齊。`AlgPoly` 給出擴張係數
多項式代數，`qpoly_splitting_field` 以逐次擴張塔給出全部根並有
可重驗證書。根式層有精確 BigInt/有理 nth-root、擴張內 nth-root
搜尋與一般根式表達式化簡。Jacobi 端點同步改為任意精度，另以
有理 Hermitian 特徵多項式加實根隔離逐一分離接近特徵值。

驗收：`check_qpoly_factor_complete`、`check_root_isolation`、
`check_splitting_field`、`check_radical_denesting`、
`check_Jacobi_arbitrary_precision`。

#### 1.12.2 一等宇宙多態與同時宣告（`schema_phase9.mbt`）

層級現在以 AST 的 `DUnivLevel` 與一等宣告
`DLevelInductiveDecl`、`DLevelHitDecl`、`DLevelTermDecl` 呈現；
層級代換先實例化模板，未實例化的層級在 `d_infer` 中被拒絕。
型別算子正性不只認透明別名：`DTypeOperatorDecl` 展開算子 body
後抽取 `DPositiveFunctor`（含有限依賴 container），不透明中性
應用仍保守拒絕。`DNestedIterDecl` 以「每次遞迴將參數送入指定
轉換」編譯非均勻巢狀型，涵蓋 Bush 形狀。原始互歸納宣告
`DMutualDecl` 先做聯合正性報告再 elaboration；同時歸納—遞迴
以 `DSimultaneousIRSpec` 攜帶基底歸納族與同步函數並生成求值。
HIT 的移動維度情形多了 cell lift 與 argument-face 實例化，使
高維 cell 的形式 comp 可沿被移動維度檢查。

驗收：`check_level_polymorphic_declarations`、
`check_type_operator_positivity_extraction`、
`check_nested_iter_datatype`、`check_mutual_declaration_positivity`、
`check_simultaneous_induction_recursion`、
`check_hit_moving_dimension_lift`。

#### 1.12.3 原始 `DSystem` 剪枝、修復與命題截斷（`dsystem_compat.mbt`, `truncation.mbt`）

`conv_at_under_face_report` 把面下轉換做成可剪枝的 BDD 遍歷，
回報造訪與剪去的節點，不再先枚舉所有端點 cube 才檢查。
`face_agreement_region` 只回傳可證的合意子區域，不把只在端點
成立的資訊塌縮成整個面。`dsystem_repair_to_base` 對 first-match
系統做不交化後，再刪去與 base 在維度 0 可證不合的分支區域，
輸出被移除區域與修復分支數；不能證明的衝突仍保留而非猜測。
命題截斷 `prop_trunc_schema` 是以 point 與任意兩截斷點之間的
squash cell 定義的 HIT，並有向 Unit 命題的消去檢查。

驗收：`check_dsystem_repair_phase9`、
`check_propositional_truncation`。

#### 1.12.4 Adjoint 資料、fiber 表述與 GlueEquiv 引文（`equivalence_phase9.mbt`, `nbe_dep.mbt`）

`adjoint_equiv_type_term` 是 `Σ (e : Equiv A B), Π x, Path
(Path B (f(g(fx))) (fx)) (ap f (retr x)) (sect(fx))` 的 AST
型別；語義側有 `DAdjointEquivParts` 保存三角形值。對任意
quasi-inverse 數據，`equiv_improved_sect_value` 構造標準改良
counit `ε'(y)=ε(fgy)⁻¹∙ap f(η(gy))∙ε(y)`，並驗證其 section
端點；identity 有完整反射三角形。`isContr`、`fiber` 與
contractible-fibers 型別均為 AST builders，另有 based singleton
的定義性收縮與任一 quasi-inverse 的 fiber center `(gy,εy)`。
`quote_ty` 現在保留 primitive `DGlueEquiv` 句法而非先塌縮，
故被表示的 GlueEquiv 引文可還原原句法。在第九期當時，一般準逆的自動
adjointification 三角形及一般 fiber 全域收縮仍是邊界；第十期
§1.13.1 已以語義 `lemIso` 構造補上，其驗收範圍在該節明示。

驗收：`check_adjoint_equivalence_and_fibers`、
`check_glue_equiv_quote_preserves_syntax`。

#### 1.12.5 維度代換與持久 registry（`kan_dep.mbt`, `checked_line.mbt`, `schema_registry.mbt`）

裸 `DLine` 有 `dline_subst`／`dline_rev`，沿單維 De Morgan
表達式重參數化並保持 coe 行為；語義封閉值有
`dvalue_subst_dims`，受檢查線也有封閉重參數化檢查。Schema
registry 改為 64 個 inductive/HIT buckets 的 hash-cons 候選
索引，身分仍由完整穩定鍵確認；公開操作包括 snapshot、restore、
merge、批次註冊與 manifest 指紋，使同一進程模型中的 plan 可
持久保存、增量合併並核對重用。

驗收：`check_dline_dimension_substitution`、
`check_semantic_dimension_substitution`、
`check_schema_registry_persistence`。

#### 1.12.6 一般代數認證與 DAG 原生 BDD（`certified_algebraic.mbt`, `bdd_dag.mbt`）

`AlgC{re,im}` 把複數層放在同一個 `AlgNum` modulus 上，向量、
矩陣、Hermitian 內積、外積投影與任意次形式多項式路徑／方塊
均以精確係數檢查，不再限於二次 `QuadC` 或低次影子。BDD 的
求值、正規化滿足數（`BigInt`）、restrict、exists／forall 均
直接在 interned DAG 上運算；DAG 回 DNF 面公式帶 cube 預算，
超限回 `None`。`face_sat_decide`／`face_eq_decide` 先試 DAG，
失敗或超預算時轉 DPLL，給出總判定（但最壞時間仍可指數）。

驗收：`check_certified_algebraic_numeric`、
`check_bdd_dag_native_operations`。

#### 1.12.7 球面同倫代表元與 Hopf 連結數（`sphere_homotopy.mbt`）

閉項 builders `loop_space_type_term` 與 `based_map_type_term`
給出 `Ωⁿ(A,a)` 與基點映射型。圓的整數冪次環路經懸掛函子
迭代成 `sphere_degree_value(n)`；`suspension_unit_loop_value`
是單位 `x ↦ meridian(x)∙meridian(*)⁻¹` 在北極的環路代表元。
另一個 `sphere3_swapped_schema` 把 S³ 的 south/north cell 順序
交換，兩向映射及以依賴 HIT 消去構造的 sect／retr 路徑組成
`sphere3_swapped_equiv_value`。經典 Hopf 映射
`(z,w)↦(2Re(z w̄),2Im(z w̄),|z|²−|w|²)` 在 `C²` 單位球上
檢查像在 S² 與共同相位纖維不變性；南北纖維經立體投影後的
Gauss 連結積分絕對值在容差內為 1。這些是經檢查的代表元與
經典模型不變量，不是核內 `π₃(S³)≅ℤ` 或 `π₃(S²)≅ℤ`
分類定理，界線見 §4。

驗收：`check_sphere_homotopy_representatives`、
`check_hopf_numeric`。

#### 1.12.8 非 Miller HOU 片斷與模組分離編譯（`hou_elaborator.mbt`, `module_system.mbt`, `module_compilation.mbt`）

HOU 在原 Miller pattern 之外加入三個受限而健全的片斷：重複
變量 spine 取首個重複 binder；由 `succ`/pair 組成的構造子
spine 以 Nat predecessor 與 pair 投影擷取葉變量；兩個不同
flex head 在直接指派失敗時可取支援交集上的共同 fresh meta。
同一 flex head 只在逐項引數合一後 spine 全同才解。模組宣告
新增無 body 的 `module_decl_abstract`；已檢查模組可編成
`CompiledModule`，保存展平 telescope、exports、依賴指紋、
介面 hash 與實作 hash。`CompiledModuleEnv` 以 synthetic
import-free 定義連結客戶，抽象介面只能簽章，換入 hash 相同且
補足 body 的實作後才可實例化。另有編譯前綴特化
`compiled_module_specialize_prefix`，以及以來源＋依賴介面
指紋為鍵的 `ModuleCompileCache`。

驗收：`check_hou_phase9_extensions`、
`check_module_compilation`。


### 1.13 第十期：一般纖維收縮、核內 π₃ 呈現、有界 Huet、模組位元組格式與成本控制

第十期處理第九期 §4 餘下六項。完成程度逐項分開陳述：一般
`lemIso` 是語義值構造；球面部分是核內型別、典範生成元與代表元
分類，不是任意元素的一般同倫群分類；HOU 是有界搜尋而非一般
不可判定問題的完備判定；成本工作改善可達輸入範圍，不消除
最壞情況指數下界。

#### 1.13.1 一般 quasi-inverse 的 `lemIso`、可收縮纖維與自動 adjointification（`equivalence_phase10.mbt`, `kan_ast.mbt`）

對語義等價分量 `(f,g,ε,η)` 與 `y:B`，
`equiv_fiber_type_value` 是同倫纖維
`Σ x:A, Path B (f x) y`。`equiv_fiber_path_value` 對同一纖維的
任意兩個語義元素 `(x₀,p₀)`、`(x₁,p₁)` 執行標準三層 `lemIso`
方塊：先以 hfill 連接 `g(pᵢ(~i))`、中心 `g y` 與
retraction；再連接兩條填充的末邊；來源方塊以 hcomp 修正邊界，
最後在目標中以 `f` 的像與 section 自然性方塊閉合，得到依賴
Σ 路徑的第二分量。離散 Bool 的巢狀合成另由 `bool_cap_value`
展開 cap，使 Bool 檢查走值範形。

`equiv_fiber_contraction_value` 是由中心 `(g y, ε y)` 到任一
纖維元素的特化；`equiv_contractible_fibers_value` 把它包裝成
依賴 `y` 的語義 `(center, contraction)` 函數值。
`adjointify_equiv_value` 保留 `f`、`g` 與 section，把 retraction
換成 `f x` 纖維中由中心到 `(x,refl)` 的收縮之第一分量；
half-adjoint 三角形由該收縮的第二分量方塊經 corner hcomp
轉角抽出，回傳 `DAdjointEquivParts`。

這裡的「一般」指公式不特化於某個等價或型別，而是直接作用於
任意輸入的語義 quasi-inverse 分量；它仍是宿主語義構造與
轉換驗收，不是把一條閉合的 `Π (e:Equiv A B), …` 證明項書入後交給
一次依賴檢查。登記檢查涵蓋 Bool 非在兩個點上的纖維端點、包覆
收縮、新 retraction 與三角形端點；另涵蓋原語 Circle 恆等、
目標 `(base,loop)` 的收縮端點與 base 上的 adjointification。
Circle 收縮的一般中點只在第二維兩端面下以
`conv_at_under_face` 驗證，因為現行 Circle composition 對
開放中點不作全域化約宣稱。

驗收：`check_general_adjointification_and_contractible_fibers`。

#### 1.13.2 核內整數、π₃ 商型與球面環路代表元（`sphere_classification.mbt`）

`integer_schema` 是生成的非 HIT 歸納型 `IntegerS`，三個構造子
為 `zero`、`posSucc(n)`、`negSucc(n)`，其中後兩者的
schema-natural 引數 `n` 是絕對值減一，所以每個整數有唯一
構造子範形。`integer_term`／`integer_value` 給出閉項／語義值；
`integer_succ_value` 與 `integer_pred_value` 是對典範構造子值
的語義後繼／前驅計算。檢查驗證若干正負整數的閉項型別及
`pred∘succ`、`succ∘pred` 轉換。

`homotopy_group_type_term(A,a,n)` 把 πₙ 表為生成商 HIT
`QuotientS(Ωⁿ(A,a), λu v. ∥Path(Ωⁿ(A,a),u,v)∥₋₁)`；
`pi3_sphere_type_term(2)` 與 `pi3_sphere_type_term(3)` 因而是
核內型別，檢查確認兩者都有型別 `DUniv(0)`。
`pi3_sphere_point_term` 把一個已給的閉三環路項送到商點。
僅僅形成這類商型並不證明其中任意元素都由下面的典範環路代表。

典範生成元由 `sphere_loop_power_value` 遞迴構造：一維取
circle loop 的整數冪；升維時 `suspend_loop_value` 先逐點套用
suspension unit，再沿
`dpath_trans_sym_cancel_value` 構造的 `p ∙ p⁻¹` 消去路徑用
`subst_value` 改基，避免直接代換端點使 cube 塌縮。
`SphereLoopExpr` 是由 refl、generator、inverse 與 compose
自由生成的代表元演算；`sphere_loop_expr_degree` 是到宿主整數
的群同態，`sphere_loop_expr_of_integer` 給出整數到典範
generator 冪表達式的一條回程，`sphere_loop_expr_value` 把
表達式求值到 `Ω^dim(S^dim)`。這分類的是這套表達式演算
（decode／代表元層），其值亦只在 S²、S³ 的
`n∈{-1,0,1,2}` 與一條複合表達式上檢查了最外層端點。

因此第十期不宣稱已合成證明任意元素的
`π₃(S³)≅ℤ` 或 `π₃(S²)≅ℤ` encode/decode 等價，也未把
經典 Hopf 映射或連結數變成核內 Hopf 不變量證明。

驗收：`check_sphere_loop_representatives_internal`。

#### 1.13.3 有界 Huet 搜尋（`hou_elaborator.mbt`）

`hou_search_unify` 在確定性 `hou_unify` 上加一個交易式搜尋層。
每個節點先試原確定性片段；失敗時由 clone 回復 `Unifier`，
成功才保留指派。非 solved 的最外層結果會把輸入 unifier
精確回復。搜尋分支包括：閉合 rigid head 與項形成子的
imitation 模板（未知子項換成在 formal spine 及模板 binders
上的 fresh metas）；任一 formal 位置的 projection，含再套用到
0、1 或 2 個 fresh 引數；一層 eta 生成；常數猜測；rigid
分解（含 λ 對非 λ 的 eta 展開）；相異 flex-flex 分別嘗試及
共同常數。同頭 flex-flex 先逐位置記錄可由健全合一使兩邊相等的
不變座標，只保留那些座標；置換沒有不變座標時得到共同常數。
這種剪枝給的是一個具體 unifier，不是置換問題的 MGU，也不需要
假定原函數真的只依賴保留座標。

公開預算預設 `max_nodes=1000`、`max_depth=4`；公開入口的
`max_nodes≤0` 直接回報 budget exceeded。`HouSearchReport` 回報
`solved_metas`、節點數、分支數與最大搜尋深度，狀態區分：
`HouSolved`；確定性合一失敗且已無未解 meta 時的
`HouNoUnifier`（例如閉合 Bool 字面衝突）；分支／深度耗盡仍
未定的 `HouResidual`；以及 `HouBudgetExceeded`。檢查涵蓋
非變量 rigid spine 的 imitation+projection、同頭全置換與
部分不變座標、極小預算下交易回復，以及閉合衝突。完整 HOU
不可判定，故不宣稱搜尋完備或必給 MGU。

驗收：`check_hou_bounded_search`。

#### 1.13.4 已編譯模組的穩定二進位格式（`module_binary.mbt`）

版本 1 的位元組布局是 20-byte 小端標頭：0..8 為
`CHMODBIN`，8..10 為版本 u16（目前 1），10..12 為 flags u16
（目前必須 0），12..16 為 payload 長度 i32，16..20 為
payload 的 DJB2-xor checksum i32，其後正好是 payload。
API 以每元素一個 `0..255` 的 `Array[Int32]` 表示位元組，可
原樣寫出；hex 是同一位元組串的文字表示。格式不含檔案系統 API。

Payload 按欄位順序保存整個 `CompiledModule`。原始整數為
固定寬度小端 i32，Bool 為單一位元組 0/1，String 為 UTF-16
code units 的 i32 計數加小端 code units。現行全部 `DTerm`
構造子，以及 payload 引用的 `Dim`、`Face`、層級表達式、正性
函子、歸納與 HIT 描述子都有固定一字節標籤遞迴編碼；新增標籤
必須提升格式版本。解析器把每個計數與剩餘 payload 比較，遞迴
深度超過 1024 即拒絕，並要求 payload 精確耗盡。
`ModuleBinaryStatus` 分開回報壞 magic、不支援版本／flags、
截斷、checksum 不符、格式錯誤、尾隨位元組與語義驗證失敗。
`compiled_module_from_binary` 只做結構解析；
`compiled_module_load_binary` 額外執行
`compiled_module_validate`，重驗 hash 與 synthetic 定義的
re-elaboration。檢查對實作模組與泛型模組做完整往返、hex
往返、單字節竄改與截斷狀態，並只用還原出的實作連結客戶，
確認其 `answer` 正規化為 `DBoolLit(true)`。

驗收：`check_module_binary_format`。

#### 1.13.5 極端成本控制：BDD、watched-literal DPLL 與 QPoly 快速乘法（`bdd_dag.mbt`, `face_sat_watched.mbt`, `algebra/qpoly.mbt`）

既有節點表與 apply cache 均由 1024 桶開始：節點數超過桶數
四倍時節點表 doubling rehash，`apply_misses` 超過 apply 桶數
四倍時 apply cache doubling rehash；`bdd_manager_cache_stats`
公開兩種桶數與 apply 條目數。`bdd_dag_of_face_optimized`
先取既有候選序的最佳者，再做有 rebuild 預算的 sifting：
逐一把每個變量移到每個插入位置，重建並比較 reachable node
數，只採嚴格改善者；`BddOptimizedBuild` 回報初始／最終
reachable 數、嘗試數與是否真有改善。它是局部啟發搜尋，
不是全域最佳變量序或最小 BDD 定理。

`face_sat_watched_dpll` 先以 `face_bound` 把 `Face` 及其原子
內 `Dim` 編成布林式，再以 Tseitin 延伸變量編成 CNF；求解器
使用 two-watched literals、保存相位、衝突 activity 選變量與
一般 DPLL 回溯（沒有 clause learning）。陽性見證在離開求解器前
以 `face_holds` 重驗；`max_steps≤0` 在此入口表示不設步數上限，
正預算耗盡則回專屬 budget 狀態。面相等對對稱差求解。
`face_sat_decide`／`face_eq_decide` 的預算後備路徑已改用此
watched solver。驗收含 79 組生成的 7 變量面與 `2^7`
brute force 的 sat/eq 差分，以及 PHP(4,3) 不可滿足、
PHP(3,3) 有經驗證見證；最壞搜尋時間仍可指數。

`qpoly_mul` 按非零係數工作量自動選路：非零對數不超過
4096，或至多稠密長度乘積四分之一時，用跳零的有理卷積；
否則各以分母最小公倍數縮放一次為 BigInt 整係數多項式，
短邊少於 24 或長度乘積不超過 4096 時用 schoolbook，否則用
遞迴 Karatsuba，最後除以兩分母乘積。`qpoly_pow` 改用二進位冪。
公開檢查以兩個 97 項確定性多項式和獨立 schoolbook 整數卷積
逐係數對照，並驗證 `(x+1)^37`。這些改善不移除係數位長增長、
難因式分解、根簇細分或分裂塔的固有成本。

驗收：`check_bdd_cost_optimizations`、
`check_qpoly_fast_arithmetic`。

### 1.14 第十一期：跨家族宣告、精確修復、一般點收縮、位元組持久化、雙二次去巢、子句學習、圓的覆疊與交錯模組

第十一期處理第十期 §4 的八項邊界。完成程度逐項分開陳述：每項的
語義／判定內容皆有真實實作與登記檢查；不可逾越的數學或內涵界限
（不可判定性、最壞指數、組成在宇宙中的內涵性等）在各節與新 §4
中明示。

#### 1.14.1 跨家族巢狀函子與同時 IR 編譯（`schema.mbt`, `schema_functor.mbt`, `schema_positivity.mbt`, `schema_phase9.mbt`）

`DPositiveFunctor` 新增第九個變體
`DFunctorFamily(spec, params, indices)`：巢狀引數可實例化**另一**
已註冊歸納家族，參數槽由 `DFunctorParamArg` 區分
`DFunctorParamTerm`（外部項，經 `schema_eval_under` 在當前脈絡求值）
與 `DFunctorParamSelf`（宿主家族自身，於給定索引實例化）。型別、
IH 型別與 IH map 三臂經 `family_instantiate` 共用機械：頂層 Self
連回宿主 motive／消去、內層 Self 連回當前迭代的 T／map、Term 以
整變數穿透；IH 是每構造子引數一槽的巢狀 `DVPair…DVUnit` 束。
`validate` 要求目標規格的參數只出現在可 gather 的葉位置
（`spec_param_gatherable`），並拒絕 Decoded 類引數與非葉參數出現；
正性檔案以 `positivity_compose_param` 把目標規格的極性與參數槽
複合。範例 `FamRoseTreeS`（以 List 家族收子樹）與 `FamVecTreeS`
的巢狀束葉數與 IH 束型別均以轉換驗證，兩類負例 validate 為假；
tag 8 使該節點可經 registry 與模組 v2 位元組往返、v1 寫出拒絕。

同時歸納—遞迴 IR 形式新增
`simultaneous_ir_compile_decode`：以中性項探測解碼函數的宇宙
等級（真正依賴 code 的宇宙結果保守拒絕），把 simultaneous 側的
函數位置映射到 decode 側（引用別的同步函數的 IH 槽以 −1 標記、
出現即拒絕——真正互依沒有單一 decode 形），de Bruijn 索引按
Sigma/Pi 家族綁定逐層重編號，產出改名 `Base#函數名` 且換上
`decode_cases`/`decode_level` 的規格，並再過 decode 與
positivity 兩項 validate。`CodeS` 的 `El` 範例編譯後在值層與項層
都與 simultaneous 形式一致。

驗收：`check_family_nested_functors`、
`check_simultaneous_ir_compiled_decode`、
`check_family_functor_persistence`。

#### 1.14.2 原始 `DSystem` 的 Face 值合意區域與精確修復（`dsystem_compat.mbt`）

兩語義值的合意區域先前只有布林 BDD 形；布林化把「在 i=0 與
i=1 都相合、中段不合」的區域誤呈為全域或丟失端點。
`face_agreement_face` 直接構造最大的 Face 值合意面（圓點
`loop@i` 對基點的合意面在兩端為真、在自由 i 為非平凡面，
其 BDD 化為 `BddOne`，而 BDD 形區域只得到
`BddNode(0,BddOne,BddZero)`——只剩 0 端點），並附
`face_agreement_face_sound` 封閉檢查。`dsystem_repair_to_base_exact`
以 Face 值合意面截斷各分支（`DSystemRepairExact` 回報保留面與
頂點層面移除區域為 `BddZero`），與舊 BDD 修復「只留 0 端點」
對照驗證；修復仍只刪去可證不合的區域，不為缺值發明分支，
`dsystem_of_first_match_nf` 經 `face_of_bdd` 的過度宣稱路徑仍禁用。

驗收：`check_face_agreement_and_exact_repair`。

#### 1.14.3 `lemIso` 一般點驗證與 Circle/Torus 點值合成（`equivalence_phase10.mbt`, `kan_ast.mbt`）

`check_lemiso_generic_points` 把第十期一般 `lemIso` 構造推到
**中性點**與**中性路徑兩端**：對恆等等價在中性纖維元素上，
收縮路徑的端點與邊界直接轉換成立；原始 Circle 點亦入列。
兩處內涵邊界經實驗定性後明示不修：路徑消去的中性式在端點
不化約（需要 conversion 內的 Bool-η／case-split）；離散型別上
中性形式 `DNComp` 僅作結構比較，數學等價但填料不同的合成
不可轉換。另外 `comp_circle_value`／`comp_torus_value` 對
**點值** tube 改以 De Morgan 選擇計算（`dim_of_face` 把面公式
讀回維度式、pairwise 相容加 fold 選擇），cap 與 filler 皆落回
點值並以 `dim_eq_sem` 判定；非點值資料仍走形式 `DNComp`。

驗收：`check_lemiso_generic_points`、
`check_circle_torus_point_comp`。

#### 1.14.4 Schema registry 位元組持久化與全域 term hash-consing（`schema_registry_persist.mbt`, `dterm_intern.mbt`）

`CHREGBIN` v1 把 registry snapshot 寫成
magic＋版本＋長度＋校驗＋payload（重用模組 codec 的全
DTerm/schema 編碼，含 functor tag 8）；載入逐一拒絕壞
magic、截斷與校驗不符並以 `DSchemaRegistryBinaryLoad` 回報
狀態，往返後 registry 仍可驗證新註冊。這是位元組層持久形，
不是檔案系統層：檔案／路徑政策留待呼叫方。`dterm_intern`
提供真正的全域 hash-consing：以子項 stamp 自底向上 intern，
結構相等子項共享同一 id（`dterm_intern_id`），
`dterm_rebuild` 是 `dterm_children` 的逆（含 eliminator 與
partial 的複合形狀）；intern 前後 `dep_check_closed` 與
`dep_nf_closed` 一致，共享率以 tree/distinct 子項計數回報。

驗收：`check_schema_registry_byte_persistence`、
`check_dterm_hash_consing`。

#### 1.14.5 精確代數：自適應圖樣剪枝與雙二次去巢（`algebra/qpoly_factor.mbt`, `algebra/biquad_denest.mbt`）

`Q[x]` 因式分解在 Kronecker 列舉前先行**自適應 mod-p 次數
圖樣剪枝**：對至多 32 個小素數（≤251）記錄平方自由部分在
F_p 的不可約次數圖樣 `QPolyDegreePattern`，凡不能由整數
因式次數相加而得的候選次數組合整批排除；圖樣置於有理根
測試之前。`x⁶−2M⁶`（M=1236789689135）單憑圖樣證得不可約；
`x⁴+1` 因 Galois 群 V4 的置換型無法排除二次因式，誠實落回
完整列舉。根式層新增雙二次域 `BiquadNum`：至多兩個無平方
因子基底、基底 `[1,√d₁,√d₂,√(d₁d₂)]`，運算經 `Q*/Q*²` 的
公共基底（需第三個基底的合成回 `None`），逆以全共軛積、
符號以塔式平方比較判定；`biquad_sqrt` 對單根槽走二次去巢、
多根槽經原元 `√d₁+√d₂` 橋到 `AlgNum`，結果一律平方重驗。
`radical_simplify` 六個運算在原二次路徑失敗時落到雙二次路徑，
`radical_equal_exact` 給出差值判等。完備界限明示：二次子域
被開方數與「根仍在同一雙二次域」的情形完備；真正雙二次
被開方數需要「另一個雙二次域或更高 multicubic 根」者不做。

驗收：`check_qpoly_mod_pattern_pruning`、
`check_biquadratic_denesting`。

#### 1.14.6 宿主不透明立方、精確最佳 BDD 序與 CDCL（`dcube_filler.mbt`, `algebra/poly_cube.mbt`, `bdd_dag.mbt`, `face_sat_watched.mbt`）

`DCubeFunction` 把「宿主函數給的 n 維立方」提升為可操作
物件（面、退化、泛型維度點值），`dcube_box_validate` 逐對
檢查開盒重疊、`dcube_box_fill_verified` 只在相容時經
comp 給出填料並逐面重驗，帽由 `dcube_box_cap` 讀回；代數
側 `PolyCube` 是同型物件在精確有理多項式座標下的版本，
填充迭代為 `F += w·(S − F|face)`。BDD 方面
`bdd_dag_of_face_optimal` 在 n≤8 時枚舉全部排列給出可證
最優變量序（回報 `tried` 與 `exact`，超出上限明示非精確），
與 sifting 及封閉序對照並逐點對驗 `face_holds`。SAT 方面在
watched-literal DPLL 之上完成 CDCL：1-UIP 衝突分析給出以
斷言文字領頭的學習子句、VSIDS 活動、標準 Luby 重啟
（`FaceCdclStats` 回報 learned/conflicts 等）；與 brute force
在生成面集合上差分一致，鴿洞 (6,5) 要求學習數為正。SAT 與
BDD 的最壞指數下界不變；精確最佳序本身是 n! 工作，只在
小 n 有用。

驗收：`check_dcube_open_box_filler`、`check_poly_cubes`、
`check_bdd_optimal_order_exact`、`check_cdcl_clause_learning`。

#### 1.14.7 圓的萬有覆疊、encode/decode 與 Jacobi 特徵值簇分離（`circle_classify.mbt`, `algebra/root_isolation.mbt`）

分類對象是 schema 圓 `circle_schema()`（原始 `DVCircleTy` 的
點轉換只比對座標零點面的布林等價，`loop²` 與 `loop` 逐點
可轉換，不能承載繞數）。`circle_cover_value` 以圓消去入宇宙
定義 helix：base 纖維是 `IntegerS`、loop 纖維是後繼等價
（`integer_succ_equiv_value`，succ/pred 在規範整數上互逆、
中性值退化恆等使 refl 資料合法）的 `ua` 線；
`circle_encode_value` 是在覆疊中對 0 的 subst，
`circle_decode_value` 是整數消去（正負各經對 `|n|−1` 的
Nat 消去）給出的環路冪。為此在 `comp_glue_equiv_value`
補上了端點 Glue 結構合成：消去定義的族線在端點化約掉
Glue 形時，以一般點分支面在端點特化還原（`face_subst`）；
已 Glue 形的線（term 級 Glue 與 ua 線）行為不變。驗證內容：
base 纖維與 loop 點纖維在宇宙層分別轉換等於 ℤ 與 ua 線；
encode 在 refl/生成元/逆元直接算得 0/1/−1；decode∘encode
在該三元以環路空間轉換為恆等，encode∘decode 在 0,±1
直接、在 ±2,3 經 decode 自身分解以
`circle_encode_pieces_value` 細分 transport 計算。內涵邊界
明示：單次 subst 越過 trans 複合點時，覆疊經「在宇宙中
comp」呈現為 `DVGlue` 型別線，其 transport 不串接兩個後繼
等價（loop² 直算得 1、細分得 2）；任意中性環路的完整
π₁(S¹)≃ℤ 內部等價仍需商/funext 機械，見 §4。Jacobi 側
`jacobi_separate_clusters` 對特徵多項式取平方自由部分
（Sturm 鏈與導數 gcd）分離互異根，再逐區間對原多項式
Sturm 計數回多重數，區間重疊唯一匹配，給認證形
`jacobi_cluster_separation_certified`。

驗收：`check_circle_encode_decode`、
`check_jacobi_cluster_separation`。

#### 1.14.8 HOU 深搜尋、模組交錯編排、版本遷移與 artifact store（`hou_elaborator.mbt`, `module_system.mbt`, `module_binary.mbt`）

有界 Huet 搜尋新增深層 imitation（一層以上的 rigid 頭
候選）、projection 候選上限參數化與同頭 identification
（兩方程式共享同一見證）；確定性層的 abstract/constant
猜測會使多數單方程式平凡解出，測試因此要把確定路徑全堵
才迫使搜尋分支。`hou_search_unify_iterative` 迭代加深並以
`HouIterativeReport` 記錄輪次與求解深度；所得仍是 specific
unifier，非 MGU、非完備，一般 HOU 不可判定不變。模組定義
改以 `ModuleDef.items : Array[ModuleItem]` 交錯編排 import
與本地宣告（舊 `decls` 形展開為 imports 前置而向後相容）；
交錯範例中 legacy 排序必失敗而交錯成功。二進位推進到 v2
（v1 payload 後加 `producer`）：寫出預設 v2、載入接受
v1/v2 且 v1 遷移後逐欄相等；`compiled_module_to_binary_v1`
以截尾重建 v1 形，遇 v2-only 節點（functor tag 8）以
`None` 拒絕。`CompiledModuleStore` 是進程內 artifact
快取（blobs＋命中/未命中計數），不是磁碟快取。

驗收：`check_hou_search_extensions`、
`check_module_interleaved_items`、
`check_module_binary_versions_and_store`。

### 1.15 第十二期：同規格遞迴與 eliminator 編譯、結構合意與補入、case-split 轉換與路徑值合成、儲存庫與 DAG codec、塔體與證書、分層外延與單位律 3-胞、主合一子

第十二期處理第十一期 §四的八項邊界。依例逐項分開陳述
完成程度；所有檢查在 `phase12_laws.mbt`/`phase12_wbtest.mbt`
並登記於定理表 10 條（總表 74/74）。

#### 1.15.1 Schema：同規格非均勻遞迴與正性宣告（`schema_functor.mbt`, `schema_positivity.mbt`）

`DPositiveFunctor` 新增無規格標記 `DFunctorSelfFamily`（宿主
宣告字面值不能自引用其所屬規格，故同規格自嵌由專用構造子
表達）：`Bush A` 的 tail 得型別 `Bush (Bush A)` 並通過 IH
型別、範形與 registry 位元組往返。函子 handler 改以已建立的
真實宿主 Self 型別取代第十一期的 `DVUnitTy` 佔位，依賴先行
Self 參數的後續參數不再被誤拒，List/Sigma 參數形狀一併納入
可 gather 範圍（self-family 位置的 positivity 只回報 unknown，
明示）。不透明中性算子正性改走宣告制：`DPositivityDeclaration`
攜帶頭部項、元數與 strict/positive 引數集合，以 depth-aware
walk 在 binder 下正確移位比對（參數 probe 代換使後續變量
減一時，宣告頭同步代換且步行作用域減一）；無宣告時維持
unknown，domain 位置仍為負；`λX. List X`、`λX. Nat` 可由
`dpositivity_declaration_from_lambda` 結構驗證取得宣告，
`λX. (X→Nat)` 被拒。宣告是受信輸入，不宣稱已證明不透明
算子本身的正性。

驗收：`check_self_family_and_gather_shapes`、
`check_positivity_declarations`。

#### 1.15.2 同時 IR 的 eliminator 編譯片斷（`schema_phase9.mbt`）

第十一期的 decode 位置編譯拒絕一切外來 IH。另一條路線已
落地：互賴函數塊在同一 base 家族的 eliminator 上編譯，較早
函數的已編閉項供後續函數的外來 IH，函數引數上的自身遞迴在
lambda 下套用。此片斷的前提是 predicative 的：motive 餘域是
`DVUniv(base.level)`，函數值落 `Type_l` 須 `l < base.level`
（level-0 base 配 `El : Code → Type₀` 必然被拒，與 decode
路線的適用片斷互補）。驗證不只靠 `dep_check_closed`——其對
lambda 本體的檢查是惰性的，失敗要到套用時才經 DVUnit sentinel
浮現——而另加在外層脈絡以新鮮中性值強制套用 motive 與每個
case lambda 的逐一驗證。互賴 El/El2 在具體碼上的範形
`Π Nat. Σ Bool. Nat` 與 decode 路線相符；循環互賴回 `None`。
前向引用、非宇宙外來函數、nested/decoded 引數（涉及函子
映射的 IH）仍誠實拒絕；早先試作的「他人 IH 代入改名複本的
DDecode」路線已證明真 ill-typed（家族身分以完整規格結構
相等判定），記錄在案不再重試。

驗收：`check_simultaneous_ir_eliminator_compilation`。

#### 1.15.3 原始 `DSystem`：結構合意與 repair 補入（`dsystem_compat.mbt`, `bdd_dag.mbt`, `dterm_transform.mbt`）

合意檢查不再對脈絡全維度逐頂點探測：分支值的語法維度
支撐以 `dterm_dim_vars` 收集，合意區域的 BDD 以
`bdd_tree_cofactor` 對不相干變量求 cofactor 而自動消去，
逐頂點轉換只剩相關維度（12 維環境中的雙端點合意面給出
root var 0 的緊湊 BDD）。Exact repair 除截斷外可補入：
候選分支逐一在現有系統下驗證相容後加入、餘者拒絕並回報
計數，最終系統相容；結果是順序相依的極大（maximal）而非
最大（maximum）相容子系統，條目即如此記錄。

驗收：`check_dsystem_structural_agreement_and_supplementation`。

#### 1.15.4 轉換與合成：Bool case-split、Circle/Torus 路徑值 comp（`conv_case_split.mbt`, `kan_ast.mbt`）

項層級新增 `conv_terms_case_split(ctx, ty, a, b)`：先在新鮮
中性環境中試普通 `conv_at`，失敗時挑型別求值為 `DVBoolTy`
且確實出現於 `a`/`b`/`ty` 的脈絡變量，分別代入 `true`/`false`
（含型別與其後相依脈絡項目的同一替代並移除該項目）遞迴，
兩分支皆轉換才回真。Bool 離散，故此加強健全；Nat 變量不
切分，真依賴變量者（`if x then 0 else 1 ≢ 0`）仍拒絕，雙
變量巢狀切分與相依於 Bool 的型別均覆蓋。Circle/Torus 合成
方面，根因定位為資料讀法：原以評估後分支帽的座標組裝
De Morgan 選擇式，而走完環路的座標 1 會被端點範形化為
基點 0，繞數在合成前即丟失。改以分支在一般合成維度取值
的座標表式、把合成維度代入 1 讀出（且僅當其指示同一個點
時採用，否則退回舊帽座標）後，`comp_path_value` 以端點 tube
遞迴的路徑值合成真正計算：右端點沿環路移動的 Path 型別
中，截斷環路 tube 的帽精確為環路本身（Circle、Torus 兩座標
皆然）。端點迫使的修正只對合型別的系統有語義；輸入若非
該 Path 型別的元素（如要求基於基點的環路族在 refl 與環路
間同倫）本身不一致，合成結果不作保證。

驗收：`check_case_split_conversion_and_path_comp`。

#### 1.15.5 持久層：artifact 儲存庫、共享 DAG codec、版本協商（`artifact_repository.mbt`, `module_binary.mbt`, `schema_registry_persist.mbt`）

`ArtifactRepository` 在抽象位元組儲存（鍵→位元組的記錄
函數協議，含記憶體實現）之上提供持久層政策：命名 blobs、
攜雙哈希/長度/格式版本的 manifests、以及單一 index 鍵。
提交順序固定為 blobs→manifests→index，故崩潰至多留下不可見
的新 blobs 而 index 仍指舊狀態（原子可見性）；`get` 以哈希
驗證拒絕損壞，index 全失時由 manifests 掃描復原（範例復原
2 筆）。模組與 registry 的位元組格式推進為 CHMODBIN v3 /
CHREGBIN v2，共用 DAG 項 codec：節點數達門檻（6）時重複
子項以 tag 255 back-reference 表示，兩格式讀回逐欄相等；
v1 仍可讀。`BinaryVersionPolicy(current, supported,
oldest_writable)` 與 `binary_negotiate_version` 給出跨進程
協商模型：取雙方 supported 交集中不低於兩方 oldest_writable
的最高者，無共同版本回 `None`。儲存是抽象協議，不冒充
OS 磁碟。

驗收：`check_artifact_repository_and_dag_codec`。

#### 1.15.6 精確代數與 Jacobi：不可約證書、塔體擴張、迭代內簇精化（`algebra/qpoly_certificate.mbt`, `algebra/tower_fields.mbt`, `algebra/Jacobi_interval.mbt`）

因式分解前段加不可約證書 fast path：線性、低次無有理根、
模素數不可約與 Eisenstein（含量移搜尋）四種證書，各可由
獨立的 `qpoly_irreducibility_certificate_check` 以多項式
算術重驗，變造全拒；`x⁴+1` 在零 Kronecker 預算下即憑
平移 Eisenstein 證書判不可約（第十一期的 V4 圖樣死角由此
繞過，最壞成本仍在無證書時的 Kronecker 列舉）。根式判等塔
自雙二次向上擴：純三次體 `CubicNum`（`Q(∛m)` 的範數/符號/
立方根）與三二次體 `TriquadNum`（生成元逐步以平方類獨立
驗證後方納入 8 維基底，雙二次開方可在三二次中落點）加入
`radical_equal_exact` 的四層嘗試，判等仍以平方/範數重驗，
更高塔與需一般代數數根者明示不做。Jacobi 區間迭代具簇
感知：迭代內以 Gershgorin 碟偵測簇、簇懲罰改 pivot、精度
不足升級重跑，count-2 簇在迭代內分離為兩不交單點且整體
證書可由 `jacobi_certificate_sound` 核驗——與第十一期事後
Sturm 簇分離是兩條分開記錄的路徑，不混稱。

驗收：`check_qpoly_irreducibility_certificates`、
`check_tower_fields`、`check_jacobi_cluster_aware_iteration`。

#### 1.15.7 數值與搜尋：變量序 DP、CDCL 刪除與 RUP、宿主立方分層外延（`bdd_dag.mbt`, `face_sat_watched.mbt`, `dcube_filler.mbt`）

精確最佳 BDD 變量序從 n≤8 全排列推進至 n≤12 的子集 DP：
對每個前綴變量子集計算可達的最小上層寬度（父集合逐賦值
生成去重），由表重建最優序；n=10 時 tried=5120，n=13 起
`exact=false`。CDCL 加 LBD 子句刪除（僅在 decision level 0、
reason 子句保留、watches 重建；鴿洞 PHP(7,6) 刪除 116 條）
與 RUP 證明輸出：學習子句日誌與現行子句庫分開保存，獨立
checker 以單位傳播逐條重播驗證至空子句（PHP(6,5) 的 162 條
學習子句可稽核）。`Moon` 宿主立方函數的外延檢查改分層：
原 `dcube_cubes_conv` 只探一個一般內部點，宿主函數在端點、
對角（兩軸同值/與環境維度同值）與連接式（¬、∧、∨）上的
分歧全不可見。分層版在三層有限探針池（面內部、對角、連接）
上逐一以 `conv_at` 比較，盒重疊驗證與 verified 填充同步
改走分層版；只在角點與恆常立方相異的開盒面因此被拒；
探針數逾上限的層以 `complete=false` 明示（有限探針是強
檢查，不是外延等式的證明）。

驗收：`check_bdd_optimal_order_dp`、
`check_cdcl_proof_and_reduction`、
`check_dcube_stratified_extensionality`。

#### 1.15.8 球面代表元、Hopf 與 HOU 語意（`cubical_algorithms.mbt`, `sphere_homotopy.mbt`, `hou_elaborator.mbt`, `circle_classify.mbt`）

圓的覆疊計算修正第十一期的內涵邊界：單次 subst 越過複合
環路的 trans 點時，等價複合改經端點 Glue 線合成串接，
`loop²↦2、loop³↦3、loop⁻²↦−2、相互抵消↦0` 皆由單次 subst
直接計算並與 transport 細分一致，encode∘decode 覆蓋延至
−2..3；任意中性環路的 π₁(S¹)≃ℤ 仍未內部證明。代表元層為
環路合成的單位律建構了真正的 3-胞：`dpath_left_unit3_value`
以 transitivity 方塊上的兩階段連接旋轉（經對角線、先滑左邊
再滑下邊以保持兩端點）把 `refl ⬝ α` 連到 `α`，
`dpath_right_unit3_value` 滑行連接 `α ⬝ refl`；在 S²/S³ 冪
代表元上，兩胞的兩面與一般參數處的端點皆以轉換驗證。
結合律與 Eckmann–Hilton 交換律的 3-胞、內部 Hopf 映射與
π₃ 一般分類明示未做；Hopf 側改以精確有理算術驗證多項式
恆等式（在有理點與有理相位旋轉下落於 S²、沿纖維像不變、
極點纖維、兩纖維抽樣不交），與原浮點連結數並列為代表元證
據。HOU 方面 `hou_unify_mgu` 對 Miller pattern 片斷給出三態
語意：principal（歸一化主合一子）、no-unifier（失敗後狀態
還原）、或部分替代加殘留約束（可由後續替代續解）；重複/
constructor spine 等非 pattern 形狀一般只給殘留，不宣稱為
單一 MGU。

驗收：`check_circle_encode_decode`（第十一期條目，範例
擴充）、`check_loop_unit_3cells_and_hopf_exact`、
`check_hou_pattern_mgu_and_residuals`。

### 1.16 第十三期：正性不動點與 foreign IH 映射、最大相容補入、差異切分與方塊合成、intern 共圖、塔體與聯合證書、DRUP 與自適應譜分離、環路分類、殘差求解與完整性鏈

第十三期處理第十二期 §四的八項邊界。十三條 root 檢查在
`phase13_laws.mbt`/`phase13_wbtest.mbt`，三條代數檢查在
`algebra/qpoly_certificate.mbt`、`algebra/multiquad_tower.mbt`
與 `algebra/root_isolation.mbt` 及其白箱測試；十六條全數登記
於定理表（總表 90/90）與規格登記（101 條）。

#### 1.16.1 Schema：SelfFamily 參數正性不動點與巢狀 foreign IH（`schema_positivity.mbt`, `schema_functor.mbt`, `schema_phase9.mbt`）

第十一、十二期中，`DFunctorSelfFamily` 位置的參數嚴格正性只
能回 `unknown`，原因是判定某參數在同規格自嵌後是否仍嚴格
正，本身要引用同一規格全部參數的正性結論。`inductive_parameter_positivity` 與 `hit_parameter_positivity` 現把
逐參數報告合為一個相互遞迴方程組，自全 false 起迭代至
最小不動點：直接出現於葉位置的參數先取得正性，`SelfFamily`
應用再經由已被認證的同規格參數槽傳播。Bush 的儲存參數
因此跨一次自嵌仍為嚴格正；只遞迴到 `Phantom (Phantom A)`
而不儲存 `A` 的 phantom 參數維持不出現；在自嵌一層後才
變成函數定義域的參數，其負極性亦正確回傳；每次自應用互換
兩參數的 swap 族，只能經一層 swap 得知的第二參數也由不
動點認證。不透明算子的宣告仍是受信輸入，λ 驗證版仍只覆
蓋結構可見者；不動點只解決函子語法內的同規格自引用。

同時 IR 的 eliminator 路線補上 foreign IH 的項層函子映射。
第二個同步函數的 case 若在 Product、Pi 或 Product(List)
巢狀引數中讀第一函數的 IH，編譯器不再要求該 IH 恰在葉槽，
而以 `positive_functor_map` 的項層重建把已編外來 eliminator
搬過函子形狀，再組回 bundle。TreeSU 的 leaf、pair、Bool
分支函數與 head+List 子樹四種構造子上，El/El2 的編譯正規
形與同時語義一致。此路線仍是 predicative 片斷：函數層級
須嚴格低於 base 層級，前向引用、非宇宙外來函數與函子語法
外／decoded 的巢狀位置仍拒絕；與 decode 路線的併集仍非
一般同時 IR 的完備編譯。

驗收：`check_self_family_positivity_fixpoint`、
`check_simultaneous_ir_nested_foreign`。

#### 1.16.2 原始 `DSystem`：相關維度下降與最大相容完成（`dsystem_compat.mbt`）

面下轉換原已以 BDD cofactor 消去無關維度，但主導成本的
三向遞迴仍可能沿面的大量滿足路徑展開。現行走法先 quote
型別與兩值、收集三者語法上實際提及的維度，只在相關維度
作三向下降（等於 0、等於 1、一般內部點），其餘維度由
cofactor/商結構不展開。在 `(i9=0)` 與八變量 parity 面
合取（數百條滿足路徑）下，`i9` 上的 circle loop 轉換為
基點只需至多 12 個訪問節點；把 `i9` 留自由時（含其內部）
轉換正確失敗。端點析取 `(i=0)∨(i=1)` 在 Boolean BDD
層塌縮為 ⊤，不能冒充只關於兩端點的合意證據；兩端仍分開
判定，或改以保留端點的 Face 值合意面見證。

Repair 補入由「順序相依的極大」提升為可要求最大的完成。
`dsystem_repair_maximum` 先把原分支與候選分支各自
exact-restrict 到其與 base 相合的 Face 區域；此後相容性
退化為兩兩重疊合意，故可建分支相容圖，以 Tomita 風
branch-and-bound（貪心著色給上界）找 maximum clique。
五分支驗收例的衝突圖中順序貪心只得大小 2，最大完成取得
大小 3 且 `exact=true`、系統相容；`node_budget=0` 時回
`exact=false` 但 incumbent 不差於貪心結果。最大團最壞
成本仍是指數級，預算耗盡不冒充已證明最大。

驗收：`check_conv_under_face_relevant_descent`、
`check_dsystem_maximum_completion`。

#### 1.16.3 轉換與合成：差異導引 case split、Circle/Torus 方塊值 comp（`conv_case_split.mbt`, `kan_ast.mbt`）

第十二期的 Bool case-split 對每個有出現的 Bool 變量逐一
切分，成本受脈絡 Bool 數主導。`conv_terms_case_split_report` 改以差異導引：先試普通轉換，失敗後 quote 兩側與
型別作語法差異，只選在正規形中真正造成差異的 Bool 脈絡
變量遞迴代入 true/false（相依型別同步代入），並回報
`CaseSplitReport{holds,probes,root_difference_variables,
split_nodes}`。三個 Bool 假設中兩側共享依第一變量的子項、
只在最後變量相異時，差異集恰為最後一變量，`split_nodes=1`；
真正不等的對仍拒絕。此仍是項層級工具而非覈心 `conv_at`
規則，Nat 變量不切分，最壞成本仍隨「真正差異的 Bool 數」
指數增長。

Circle/Torus 的合成由路徑值再進到方塊值。關鍵更正不是只把
分支帽代入 1：端點同定不是維度代數的同餘，舊讀法可產生點
值看似對、限制到分支面卻錯的「帳篷」帽。合成現生成數個
候選 De Morgan 座標（兩序迭代選擇、分支帽的 undamped/
damped joins），逐候選驗證其在每一分支面上的限制恰為該分支
帽；第一個全數通過者才被取作帽。Tube 為 loop 的方塊在
Circle 與 Torus（第一座標）均算得 `DVPathLam`、兩端轉換
為基點、一般內部為點值，且整個方塊在 tube 面上轉換為原
loop。若盒子的邊界只以點相等（0~1）而非表達式地相合，使
任何候選座標都無法逐面驗證，結果仍如實停在形式 `DNComp`，
不以錯誤帽冒充已計算。

驗收：`check_difference_guided_case_split`、
`check_circle_torus_square_comp`。

#### 1.16.4 持久層：活 interner 與位元組共用同一 DAG（`dterm_intern.mbt`, `dterm_dag_binary.mbt`, `artifact_repository.mbt`）

`DTermInternTable` 除 stamp/id 外現保存每節點的 child ids，
故一個可達子圖可直接出成 `DTermDagSnapshot`：拓撲序節點
逐一保存 `DTermDagNode{shell, children}`（local shell 是把
直接子項以佔位抽走的本地形狀）與 `roots`。Snapshot 在
匯入前整體驗證：child id 必須在界內且嚴格較小（拓撲序）、
每個 shell 的實際子項數須合 arity、roots 須在界內。匯入
時逐節點以 `(shell, 目標 child ids)` 在目標表 hash-cons，
回 `DTermDagImportReport{added_nodes,reused_nodes,node_ids,
root_ids}`；同一圖第二次匯入 added=0 且 root ids 不變。

其穩定位元組形為 `CHDAGBIN` v1：8-byte magic、u16
版本、保留 u16=0、i32 payload 長度、DJB2-xor checksum，
payload 逐節點以 bare（無 back-reference）項 codec 寫
shell 後接 child-id 邊與 root ids——共用的是圖的邊本身，
不是第二套位元組層共享機制。載入對 bad magic、版次、截斷、
尾隨位元組、checksum 與畸形 DAG 給精確狀態。驗收中三個
root 的 snapshot 節點少於樹節點，往返逐欄相等，活表經
artifact repository 存入再取入另一活表後 roots 仍是原項，
刪除後不可再取。注意範圍：第十二期的 `CHMODBIN` v3 /
`CHREGBIN` v2 仍然只是各自 payload 內的 tag-255
back-reference，與活 interner 共圖者僅 `CHDAGBIN`。

驗收：`check_interned_dag_byte_sharing`。

#### 1.16.5 精確代數：聯合次數圖樣證書與四生成元多二次塔（`algebra/qpoly_certificate.mbt`, `algebra/multiquad_tower.mbt`, `algebra/biquad_denest.mbt`）

不可約證書新增可攜帶的 `CertModDegreePatterns(primes)`。
檢查器先驗證該列是無重覆素數且每一個的
`mod_distinct_degrees` 都可用（回 `Some`），逐素數重算
該多項式在 `𝔽_p` 的不可約因式次數圖樣，再試每個可能的
真因式次數（由對稱性只需 `d≤n/2`）：若 Q 上有 `d` 次
因式，則在任一可用素數下，`d` 必須能寫成該圖樣若干局部
次數之和。故只要每個 `d` 都被至少一個素數排除，即可證 Q
上不可約。`x⁴-4x³-3x²-x-4` 模 2 的圖樣是 `[1,3]`、模 3
是 `[2,2]`：前者容許一次、後者容許二次，單獨皆不足，聯合
則排除次數 1 與 2；它在搜尋界內無單素數或平移 Eisenstein
證書，卻以零 Kronecker 預算經新證書完成分解。重覆素數、
合數 9 與各單素數證書均被檢查器拒絕。

根式判等的二次塔自三二次推進為 `MultiQuadNum`：值在至多
四個於 `Q*/Q*²` 中獨立的無平方因子生成元所張乘積基底
`√∏_{i∈S} d_i`（最多 16 槽）上有理係數表示。兩值運算
前先對齊到兩生成集 span 的同一獨立基底，需第五生成元的
合成體回 `None`；逆元以 Galois 共軛乘積求得，符號以
二進精確區間細化至可判。同域開方以相對範數遞迴：對
`x=u+v√d∈L(√d)`，若有根 `p+q√d`，則 `u²-dv²` 必須
是在 `L` 中的平方，再由 `p²=(u±s)/2`、`q=v/(2p)` 回解
並逐候選平方重驗。域外一生成元的開方先算有理平方調整
`x=γw²`；γ 只在模掉該域已成平方的有理平方類後唯一，故
遞迴中以 `multiquad_reduce_gamma` 規範其等價類，之後才可
adjoin `√γ`（總生成元仍至多四）。`radical_equal_exact`
的平方根片斷已接此塔；無有理平方類而真正需要非多二次的
二次擴張者、一般代數被開方數與五個以上獨立生成元仍是
明示邊界。

驗收：`check_qpoly_degree_pattern_certificates`、
`check_multiquadratic_tower`。

#### 1.16.6 搜尋與數值：十六變量精確序、DRUP、Tier D 與自適應 Jacobi（`bdd_dag.mbt`, `face_sat_watched.mbt`, `dcube_filler.mbt`, `algebra/root_isolation.mbt`）

精確最佳 BDD 變量序的瓶頸原在每個前綴子集逐賦值生成父
cofactor。DP 現以已 hash-cons 的 `bdd_dag_restrict` 增量
生成子 cofactor 集，子集表與寬度計算同為同一演算法，但免去逐賦值重建
父 cofactor 集，精確上限由 12 提到 16。14 變量成對函數給
`exact=true`、`tried=114688=14·2¹³`，順序為完整排列、
逐賦值語義一致且不大於啟發式建構；16 變量在界內、17 起
如實 `exact=false`。

CDCL 的證明由 RUP 推進為帶真刪除步驟的 DRUP：結果攜帶
時序 `FaceCdclProofStep = CdclProofAdd(clause) |
CdclProofDelete(clause)`，子句以排序去重字面集合為身分。
求解器按真正學入／刪除的順序記步驟（含最後空子句）；獨立
`face_cdcl_drup_check` 維持演進中的 active 子句庫，每 Add
重播單位傳播驗證 RUP，每 Delete 必須指向一個當前 active
子句（可至集合序差異）。手寫例中刪除不存在子句、先刪後加
及使用已刪子句導出空子句皆被拒；PHP(6,5) 與 PHP(7,6) 的
步驟數與 solver 的 `learned+1`/`deleted` 精確對帳且後者
`deleted>0`。

宿主立方分層外延加逐軸深層連接 Tier D：探針座標除舊三層
的面內部、對角與連接外，還含每軸獨立的深巢連接式。只在
`¬(s∧t)` 形狀、或只在第二軸 `(s∨t)∧¬s` 形狀偏離常數
立方的宿主函數可穿舊層而被 Tier D 揭穿；二維相等對完整
執行 105 探針，五維時 Tier D 逾 4096 預算而回 2291 探針
連同 `complete=false`。仍為有限探針，不升格全外延證明。

Jacobi 最後加一自適應驅動：先跑簇感知區間迭代；只有每個
Gershgorin 簇都是 singleton 且寬度不大於目標時才算 Jacobi
路徑達標，否則自動轉入 `jacobi_separate_clusters` 的精確
特徵多項式/Sturm 分離（必要時倍增精確位數），在同一份
`JacobiAdaptiveReport` 記下 exact fallback、所用位數、
`target_met` 與最大寬度。易例維持純 Jacobi 路徑；特徵值
`±1/4096`、目標寬 `1/16384` 且故意封低 Jacobi 精度時，
包絡停滯後由精確後援達標。若精確位數上限先耗盡，報告保留
最佳分離並回 `target_met=false`，不假裝達標。

驗收：`check_bdd_optimal_order_dp_extended`、
`check_cdcl_drup_proof_with_deletions`、
`check_dcube_stratified_tier_d`、
`check_jacobi_adaptive_exact_fallback`。

#### 1.16.7 球面代表元：逆元／結合律 3-胞與閉代表式分類（`cubical_algorithms.mbt`, `sphere_classification.mbt`）

第十二期的單位律之後，環路代數再補齊左右逆元
`α⋅α⁻¹`、`α⁻¹⋅α → refl`（連接抵消胞）與結合律
`(α⋅β)⋅γ → α⋅(β⋅γ)`。結合律以 `dpath_triple_square_value` 同時參數化三段傳遞方塊，令左結合與右結合兩個
transitivity 方塊共用同一底與左右邊，再在方塊之間以
`hcomp` 填出頂邊間的路徑；`sym(α⋅β) →
sym(β)⋅sym(α)` 則由單位、逆元、結合律以「逆元唯一」
的共軛抵消組裝。逆元律在 S²（次數 ±1）與 S³ 驗證兩面及
一般參數端點，結合律與反同態覆蓋正負混合代表元。

據此可把閉代表式語言由「按 degree 分類」補成有同倫見證
的分類：`SphereLoopExpr` 的 refl、generator、inverse 與
compose 以 degree 為範數，`sphere_loop_expr_normalize3_value` 遞迴組裝一條從任意該語言表達式至同 degree 典範字
（`sphere_loop_canonical_value`）的 3-胞——生成元經單位律
對齊、inverse 經 sym 反同態、compose 經水平複合再以
典範冪乘法胞接合。`g⁻¹⋅(g⋅g)` 在 S²/S³ 皆正規化並連到
`g`，不同 degree 的 `sphere_loop_expr_same_class` 為假。
這嚴格分類的是此閉代表式語言：任意中性環路化約到代表元
的分類引理、一般 `π_n(S^m)`、Eckmann–Hilton/交換律與
更高相干仍未建構。

驗收：`check_loop_inverse_assoc_and_classification`。

#### 1.16.8 HOU 殘差求解與工件完整性鏈（`hou_elaborator.mbt`, `artifact_repository.mbt`）

第十二期使 `hou_unify_mgu` 能交還殘留約束，但殘差還只能
靠呼叫者逐條手動接回搜尋。`hou_solve_constraints` 現以
整個約束集為單位求解：先反覆跑 principal 傳播，把目前
能定的代換套到其餘方程式；停滯才取一條殘差進
transactional、迭代加深的 Huet 搜尋，搜尋的具體代換再回
到全集傳播。宣告 `HouSolved` 前逐條重驗原始約束；試到
的猜測若只令他條約束失敗但不能證明全集無解，仍回
residual，不誤報 no-unifier；先有 principal 賦值再遇
Bool 字面衝突時給 `HouNoUnifier` 且還原輸入 meta；節點
預算不足回 `HouBudgetExceeded` 連同殘差。`HouResidualSolveReport` 記初始／已解約束、search rounds 與搜尋計數。
正式定律直接把 `hou_unify_mgu` 對 rigid-spine 方程交回
的 `.residual` 送進求解器並驗重構結果，也解 rigid＋
repeated-spine 雙約束集；純 principal 例 `search_rounds=0`。
搜尋找到的仍是 specific unifier 而非一般 MGU，HOU 不可
判定性與所有預算邊界不變。

工件儲存庫新增 append-only 完整性鏈：每次成功的 put/remove 先驗證
既有鏈，再往 `chain.bin` 追加一條 `CHARTCHN` 條目
（序號、tombstone 旗標、完整 `ArtifactRecord`、前一條
摘要與本條雙雜湊摘要），鏈損壞時寫入 fail-closed。
`artifact_repository_chain_report` 重驗每條 link、replay
put 蓋名／remove tombstone 得 live records，並檢查其
覆蓋與 index 一致；讀取與復原可帶 `expected_head~ :
(Int32, Int32)?` 把鏈頭作外部信任錨（用 Option 而非
`-1` 哨兵，因雙雜湊的 Int32 溢位值可為負）。定律覆蓋同
blob 兩名加覆寫（entries=3/live=2）、remove 後舊錨被拒、
index 遭整段覆寫後以最新鏈頭 chained recovery 得 1 筆
且 tombstone 不復活、舊鏈 replay 對最新狀態無效且
recovery 回 -1、record-hash 或 blob 任一竄改令報告失效，
以及無鏈的 legacy index 在下一次 put 時先 bootstrap
既有兩筆再追加（entries=3/live=3）。雙 checksum 仍非
密碼簽章：若整個抽象儲存與信任錨一併被換，鏈只能證明
「相對此錨未改」。

驗收：`check_hou_residual_solver`、
`check_artifact_manifest_integrity_chain`。

### 1.17 第十四期：聯合 Σ 動機同時 IR 與展開正性見證、全部最大完成與有限閉型別切分、解耦 Torus 合成、增量 DAG 差分與共用 bundle、Hensel 因式分解與實代數根式及區塊消重根 Jacobi、剪枝 BDD 與 DRAT／正交表探針、Eckmann–Hilton／五邊形 4-胞／萬有覆疊截面／單值 Hopf 不變量、跨約束回溯枚舉與 TLV／認證 CAS／增量同步

第十四期逐條推進第十三期 §四所保留的七大邊界。十四條正式定律檢查位於
`phase14_laws.mbt`（配合代數層 `algebra/phase14_algebra.mbt`），全數登記於定理總表
（104/104）與規格登記表（115 條）。

#### 1.17.1 Schema：聯合 Σ 動機同時 IR 編譯與帶展開主體的正性見證（`schema_phase9.mbt`, `schema_positivity.mbt`, `schema_functor.mbt`）

同時 IR 的個別消去器路線在第十三期無法處理前向引用、循環互依函數塊、非宇宙小上域與餘積槽 `DFunctorSum`。`simultaneous_ir_compile_joint_block` 與 `simultaneous_ir_compile_joint` 改將整組同步函數 `f₀,…,fₖ₋₁` 打包為單一聯合 `Σ` 元組動機 `M(x) = f₀(x) × ⋯ × fₖ₋₁(x)`：基礎歸納族只做一次高階消去，葉槽與經 `DFunctorProduct`/`DFunctorSum`/`DFunctorList`/`DFunctorPi` 嵌套的遞迴槽皆以投影提升同時擷取任意前向或後向同組函數的 IH，且允許一般依賴／小上域（宇宙層級 `≤ base.level`，由 `simultaneous_ir_general_eliminator_type` 自動決定目標層級）。在含葉槽與 `Sum` 分支槽的雙向循環偶／奇互遞迴樹，以及非宇宙小上域 `Bool`／依賴函數上，編譯出的閉項皆通過 `dep_check_closed` 並與同時語義正規形一致；高於基礎宇宙層級的 impredicative 上域或 `DFunctorContainer`/`DFunctorDecodedFunction` 外來巢狀仍明示回 `None`。

不透明算子的正性不再只能依賴盲信宣告。`DPositivityWitness{declaration, definition}` 要求提交算子的閉合展開定義項，`dpositivity_witness_verify` 先獨立驗證閉合性、無宇宙層級懸空變數、嚴格正／正槽索引在界且互斥，再於新鮮引數脈絡下展開主體並逐槽檢查實際變數極性。把 `Bad(A) = A → Nat` 偽稱為嚴格正的見證立即被拒；協變容器 `Good(A,B) = A × B` 通過獨立驗證並由 `dterm_family_strictly_positive_certified` 認證自應用歸納定義。

驗收：`check_phase14_joint_simultaneous_ir_mutual`、`check_phase14_positivity_witness_certificates`。

#### 1.17.2 原始 `DSystem`、轉換與合成：全部最大相容完成、有限閉型別切分、語義圓座標與解耦 Torus 合成（`dsystem_compat.mbt`, `conv_case_split.mbt`, `kan_ast.mbt`）

`dsystem_repair_maximum` 原只回單一最大團。`dsystem_repair_all_maxima` 先將候選分支限制於與 base 相合的精確面，再把分支衝突圖拆為獨立連通分量，於每一分量枚舉全部最大相容團並取笛卡兒積，回報 `DSystemRepairAllMaxima{systems, max_branch_count, total_maximum_count, conflict_components, all_compatible, exact}`。兩組獨立衝突對恰枚舉出 `2 × 2 = 4` 個相異最大相容系統且逐一通過相容檢驗。

差異導引 case split 由 `Bool` 擴展至任意無遞迴有限閉合型別：`cs_finite_closed_inhabitants` 對 `Empty`、`Unit`、`Bool`、有限和積與無遞迴閉合歸納族（如三構造子 `Fin3`）遞迴生成全體閉合居民，`conv_terms_finite_case_split_report` 僅對兩側正規形真正產生差異的有限型別脈絡變量代入全體居民（相依型別同步代入）。`Fin3` 上的對稱查表等式以 `4` 次探針（初始 `1` 次＋`3` 居民）通過，單一構造子不等對立即拒絕，`Nat`/`List` 等無限遞迴型別維持不切分。

Circle/Torus 合成新增 De Morgan 座標語義範形壓縮（冪等、互補與吸收律化簡），並將 Torus 二維方塊合成 `comp_torus_value` 的兩條圓環座標完全解耦：兩分量各自獨立枚舉候選座標並逐分支面驗證，免去雙座標同步耦合限制。對角雙重繞行（兩座標在 tube 面上同時推進、沿不同邊界獨立收束）算得 `DVPathLam` 並逐面轉換回原雙重環路；僅端點點相等（`0 ~ 1`）而無表達式帽者仍誠實停在 `DNComp`。

驗收：`check_phase14_dsystem_all_maxima_and_finite_case_split`、`check_phase14_decoupled_torus_and_semantic_circle_norm`。

#### 1.17.3 持久層：增量 intern DAG 差分與跨產物共用 DAG bundle（`dterm_dag_binary.mbt`, `module_binary.mbt`）

`DTermInternTable` 的單調增長使舊快照成為新表的拓撲前綴。`dterm_dag_delta_compute` 以基表前綴雙雜湊摘要 `(base_digest_a, base_digest_b)` 為錨，只抽取索引 `≥ base_node_count` 的新增拓撲節點與新 roots，封裝為 `CHDAGDLT` v1（`DTermDagDelta`）。匯入時先核對目標表前綴摘要與拓撲邊界，不符則在修改目標表前拒絕；相符則只將新增節點 hash-cons 入表，payload 嚴格小於全量 `CHDAGBIN` 快照。

第十三期中 `CHMODBIN` v3、`CHREGBIN` v2 與 `CHDAGBIN` 仍各自維護局部表。`SharedDagBundle`（`CHSHRBUN` v1）將單一全局 `DTermInternTable` 共用項池置於標頭，令任意多份已編譯模組與一份 `DSchemaRegistry` 快照共同引用同一組節點 ID，載入時更可直接灌入呼叫者的活 interner（回報 `shared_term_entries`、`interned_dag_nodes`、`reused_dag_nodes`）。雙模組加註冊表的共用封包位元組數嚴格小於分開序列化總和，重載入同一活表時既有節點零重複新增。

驗收：`check_phase14_incremental_dag_delta_and_shared_bundle`。

#### 1.17.4 精確代數：Hensel 提升有理因式分解、六生成元塔與實代數根式、區塊消重根 Jacobi（`algebra/phase14_algebra.mbt`）

`QPoly` 一般因式分解擺脫指數級 Kronecker 整數除數枚舉：`qpoly_factor_hensel` 先取無平方因子本原部分，自動選取保持首項與無重根的素數 `p`，在 `𝔽_p[x]` 上執行完整 Berlekamp／Cantor–Zassenhaus 分解，再以線性 Hensel 提升將局部互質因式提升至 `p^k > 2 · MignotteBound(f)`，最後配合常數項整除剪枝在對稱餘數環中重組有理不可約本原因子。`qpoly_factor_certified` 進一步產出攜帶首項、帶重數因式與逐因式不可約證書的 `QPolyFactorCertificate`，由獨立檢查器 `qpoly_factor_certificate_check` 重驗展開乘積、次數正性、兩兩互質與不可約證書。八次複合多項式（兩個四次不可約因式乘積）在零 Kronecker 預算下直接分解並通過證書重驗。

根式判等雙路推進：其一，參數化多二次塔 `multiquad_*_upto` 將獨立無平方因子生成元上限推至 `6`（`64` 槽乘積基底），五個獨立素數平方根 `√2, √3, √5, √7, √11` 的線性組合平方與開方精確閉合；其二，對超越二次塔的一般實根式引入 `RealAlgRadical{minpoly, root_index, lower, upper}`（本原不可約最小多項式＋Sturm 唯一隔離有理區間），以平移結式、尺度結式與 `p(yⁿ)` 無平方因子分解實作封閉的實代數體算術與任意正整數次實根 `real_alg_nth_root`。Pell 單位立方根恆等式 `∛(√2+1) · ∛(√2-1) = 1`（涉及不可約六次式 `x⁶ - 2x³ - 1`，二次塔與純三次體皆回 `None`）由 `radical_equal_algebraic` 精確判定為 `Some(true)`，微擾對判為 `Some(false)`，偶次負被開方數回 `None`。

Hermitian 譜包絡新增區塊去耦與重根消除 `jacobi_block_deflated_certified`：先求伴隨非零圖的連通分量將矩陣正交直和拆為獨立子塊，對每塊特徵多項式 `f_B` 取無平方因子商 `g_B = f_B / gcd(f_B, f_B')` 把高重數退化簇化為單根 Sturm 隔離，再由因式分解次數差精確回填代數重數。含三重根與緊鄰雙根的 `6×6` 區塊矩陣拆為兩個 `3×3` 子塊後無須 `6×6` 全矩陣 Sturm 展開即精確回報重數 `3, 1, 1, 1` 且寬度達標。

驗收：`check_phase14_qpoly_hensel_factor_and_certificates`、`check_phase14_algebraic_radicals_and_rank6_multiquad`、`check_phase14_jacobi_block_deflation_and_multiplicity`。

#### 1.17.5 搜尋與宿主立方：上界剪枝 18 變量最佳 BDD 序、DRAT 檢查與證明裁剪、正交表覆蓋探針（`bdd_dag.mbt`, `face_sat_watched.mbt`, `dcube_filler.mbt`）

精確最佳 BDD 變量序 `bdd_dag_of_face_optimal_pruned` 先以啟發式建構取得緊上界 `incumbent_size`，再於增量 cofactor 子集 DP 中以「當前累積寬度＋剩餘活躍支援集下界 ≥ incumbent」剪去不可達前綴子集，將精確上限由 `16` 推進至 `18` 變量。`14` 變量例與無剪枝 DP 得完全相同最小大小且 `pruned_subsets > 0`；`17` 與 `18` 變量公式精確回 `exact=true`（`19` 起如實 `exact=false`）。

SAT 證明檢查器新增完整 DRAT 驗證 `face_cdcl_drat_check`（對 RUP 失敗的候選子句 `C` 以首字面 `l` 為 pivot，逐一檢驗含 `¬l` 的當前活躍子句 `D` 其解析式 `C ∪ (D \ {¬l})` 皆單位傳播蘊含）與反向依賴核心裁剪 `face_cdcl_drup_trim`（由空子句反向回溯標記必需引理，裁去冗餘學習步並輸出精簡證明）。純 RAT 阻斷子句被 DRUP 拒絕而通過 DRAT；含冗餘引理的證明經裁剪後步數嚴格減少且仍通過獨立 DRUP 重驗。

高維宿主立方比較的指數爆炸由確定性正交表／覆蓋陣列化解：`dcube_cubes_conv_covering_report` 以有限射影直線 `ℙ¹(𝔽₈)` 構造強度 `t = 3`、字母表 `{0, 1, r₀, r₁ ∧ ¬r₂}` 的覆蓋探針集，保證任意三條座標軸的全部 `4³ = 64` 種非退化組合無遺漏覆蓋。`8` 維立方（全格需 `65,536` 點）僅用 `≤ 520` 次探針即達 `complete_for_strength=true`，精確攔截僅在三軸特定連接交互處偏離的反例宿主函數。

驗收：`check_phase14_bdd_bnb_and_cdcl_drat`、`check_phase14_dcube_orthogonal_array_covering`。

#### 1.17.6 球面同倫與萬有覆疊：Eckmann–Hilton 3-胞、五邊形 4-胞、中性環路截面與單值 Hopf 不變量（`cubical_algorithms.mbt`, `circle_classify.mbt`, `sphere_homotopy.mbt`, `nbe_dep.mbt`）

高階道路廣群相干層補齊三項核心構造：`dpath_square_boundary3_value` 將共用四角與四邊的兩個路徑方塊連接為頂邊間的 3-胞；據此建立 `refl ⋅ refl` 上左右單位律重合 4-胞 `dpath_lr_unit_coherence4_value`、`Ω²(X)` 二階環路 `α ⋅ β ≡ β ⋅ α` 的完整 Eckmann–Hilton 交換 3-胞 `dpath_eckmann_hilton3_value`（水平與垂直合成經單位律插入與雙重連接互換），以及四段複合 `((p⋅q)⋅r)⋅s → p⋅(q⋅(r⋅s))` 兩條結合律 3-胞路徑之間的 Mac Lane 五邊形相干 4-胞 `dpath_pentagon4_value`。在 `S³` 的二階環路代表元與 `S²` 的四段環路複合上，3-胞兩端與五邊形 4-胞全部六個立方邊界面均通過型別化轉換核驗。

圓的萬有覆疊補上對**任意閉／中性環路**（含自由環路變數 `p : Path S¹ base base`）的內部截面 `circle_encode_decode_sect_value`：結合一般終點自由路徑的右單位律 `dpath_right_unit_general_value`、複合傳輸分解 `dpath_subst_trans_value` 與核心 `DNInductiveElim` 沿 `ua` 路徑端點的計算規則，由路徑 `J` 消去給出 `decode(encode(p)) ≡ p`，完成合成 `π₁(S¹) ≃ ℤ` 的萬有覆疊分類截面。同時以圓上 8 段連接閉路建立自旋轉等價族 `rot : S¹ → (S¹ ≃ S¹)`，經 `ua` 在 `S² = Susp(S¹)` 子午線上黏合出內部單值 Hopf 纖維叢 `Hopf : S² → Type₀`（`hopf_family_value`），並由二階傳輸提取連接環路 `Ω³(S²) → Ω(S¹)` 再經萬有覆疊 `encode` 算出內部整數 Hopf 不變量 `hopf_invariant_value`（語義維度線搭配 `memo_dim_line` 記憶化消除多重 `ua` 合成重算）。在 `Ω³(S²)` 的 `0, 1, -1, 2` 階代表元上精確算出規範整數 `0, ±1, ∓1, ±2`。

驗收：`check_phase14_eckmann_hilton_and_pentagon_coherence`、`check_phase14_internal_circle_sect_and_hopf_invariant`。

#### 1.17.7 高階合一與模組儲存：跨約束回溯與合一子枚舉、TLV 向前相容封套、認證 CAS 與增量同步（`hou_elaborator.mbt`, `module_binary.mbt`, `artifact_repository.mbt`）

第十三期 `hou_solve_constraints` 對單條殘差承諾首個找到的 Huet 分支，若該具體代換與後續約束衝突便停在 residual。`hou_solve_constraints_backtracking` 將 principal 傳播嵌入跨約束交易式 DFS 搜尋樹：某候選分支若令後續約束失敗，立即回滾 unifier 並嘗試同一殘差的其餘投影／模仿分支；`hou_enumerate_unifiers` 則在有界深度與預算下窮舉去重後的規範化合一子集合 `HouEnumerationReport{solutions, search_exhausted, capped, ...}`。首分支與第二方程衝突的雙約束系統現自動回溯得解，雙投影歧義方程枚舉出全部不等價閉合解且 `search_exhausted=true`。

模組與工件協議補齊向前相容、認證並發與差量同步：`CHMODENV` v1（`ModuleTlvSection`）在核心 `CHMODBIN` v3 外包裹帶 `critical` 旗標的 TLV 擴充節，載入器安全跳過未知非關鍵節（記錄於 `skipped_noncritical_tags`）並對未知關鍵節 fail-closed 拒絕；`ArtifactAuthKey`（`CHARTAUT` v1）以雙秘密金鑰混合鏈頭與全部條目計算對稱 MAC 認證籤，`artifact_repository_put_cas_authenticated` 同時驗證金鑰真實性與樂觀並發 `expected_head`（過期錨回 `ArtifactCasConflict`、偽鑰回 `ArtifactCasAuthFailed`）；`artifact_repository_sync_incremental` 比對兩庫鏈歷史共同前綴，只傳輸目標缺失的 blob 與新增鏈項（`skipped_existing_blobs > 0`），同步傳播 tombstone 並使雙庫認證鏈頭完全一致。

驗收：`check_phase14_hou_backtracking_and_enumeration`、`check_phase14_tlv_envelope_cas_and_incremental_sync`。

### 1.18 第十五期：BDD、SAT 與宿主立方極限推進，以及一般雙向雙射認證、`π₁(S¹)≃ℤ`、基點環路—懸掛伴隨與 Freudenthal 懸掛定理

第十五期雙軌並進：第一軌主攻第十四期保留的 **BDD、SAT 與宿主立方** 三大硬核瓶頸；第二軌在立方依賴核心內部完成**任意開放變數雙向雙射認證 `DVEquiv`**、**圓基本群同構 `π₁(S¹) = ‖Ω¹(S¹)‖₀ ≃ ℤ`**、**一般懸掛 `SuspS(A)` 與基點環路—懸掛伴隨 `(ΣA →* B) ≃ (A →* ΩB)`**，以及**0-連通 Freudenthal 懸掛定理 `‖Ω¹(Susp(A))‖₀ ≃ 1`**（實例化給出 `π₁(S²) ≃ 1` 與 `π₁(S³) ≃ 1`）與圓楔連通引理。六條正式定律位於 `phase15_laws.mbt`，全數納入定理總表（`110/110`）與規格登記表（`121` 條）。

#### 1.18.1 搜尋與宿主立方：對稱軌道剪枝與 28 變量連通分解最佳 BDD、索引化線性時間 LRAT 精化與 CHLRATBN、強度 4 射影覆蓋陣列＋五色 PHF＋立方 Yoneda 審計（`bdd_dag.mbt`, `face_sat_watched.mbt`, `dcube_filler.mbt`）

1. **對稱軌道剪枝與連通支援分解 ROBDD 最佳序**：`bdd_dag_of_face_optimal_pruned` 在增量 cofactor 子集 DP 中偵測同層剩餘變量的對換對稱等價類（交換兩變量不改變全部活躍 cofactor 集合），每個對稱軌道僅展開最小代表變量，單連通分量精確上限推至 `20` 變量（`19` 變量三組對稱對公式直接得 `exact=true, pruned_subsets > 0`）；`bdd_dag_of_face_optimal_decomposed` 進一步建立活躍變量共現交互圖，剔除不活躍死變量並分解獨立連通支援分量，對每個 `≤ 20` 變量分量各自求精確最佳排列再按區塊拼接全局共享 ROBDD。`28` 變量四分量獨立支援公式分解為 `4` 個 `≤ 7` 變量分量精確求解（`exact=true`），而 `22` 變量單一連通鏈誠實回退啟發式並標記 `exact=false`。
2. **索引化線性時間 LRAT 檢查器、DRAT→LRAT 精化與 `CHLRATBN` v1 二進位編解碼**：針對 DRAT 無提示全庫傳播瓶頸，引入帶顯式傳播提示鏈的 `FaceLratStep`（`LratAdd(id, lits, rup_hints, rat_hints)` 與 `LratDelete(ids)`）。`face_cdcl_lrat_check` 僅沿給定子句 ID 陣列做索引查表單位傳播，消除全庫掃描；`face_cdcl_elaborate_lrat` 將 CDCL/DRAT 證明反向裁剪至空子句依賴核心、萃取確定性 RUP/RAT 提示鏈並自動插入垃圾回收 `LratDelete`；`face_lrat_to_binary`／`face_lrat_from_binary` 提供帶魔數 `"CHLRATBN"` v1 與變長整數編碼的無損位元組序列化。`PHP(6,5)` 與純 RAT 阻斷證明皆精化並通過二進位往返核驗，竄改提示 ID、刪去 RAT 見證或損毀位元組均被拒絕。
3. **強度 `t ≤ 4` `ℙ¹(𝔽₈)` 正交覆蓋陣列、五色完美雜湊族 PHF、`CheckedDCube` 與立方 Yoneda 審計**：利用 `PGL₂(𝔽₈)` 在射影直線 `ℙ¹(𝔽₈)`（`9` 點）上的精確三重傳遞軌道結合線性擴張，構造強度 `t = 4` 的 `4` 元非退化維度字母表覆蓋陣列，搭配五色覆蓋完美雜湊族 `dcube_phf_5colors`，精確攔截 `t = 3` 漏放的 `9` 維四軸交互反例（`complete_for_strength=true`）。同時從根本範疇論解決黑盒閉包外延問題：`CheckedDCube` 將立方錨定於受型別檢查的語法項，透過通用維度變數讀回實現無探針精確外延等價 `checked_dcube_extensional_eq`；對一般宿主閉包，`dcube_yoneda_audit_report` 依據**立方範疇 `□` 上的米田引理（Cubical Yoneda Lemma）**檢驗通用對角讀回項在全體面／對角／連接維度代換下的自然性，直接揭穿偷看維度 AST 語法的病態非自然宿主閉包（`natural=false`），而自然閉包通過全部代換與忠實度審計。

驗收：`check_phase15_bdd_symmetry_orbit_and_decomposed_optimal`、`check_phase15_cdcl_lrat_elaboration_and_binary_codec`、`check_phase15_dcube_strength4_phf_and_yoneda_audit`。

#### 1.18.2 一般雙向雙射認證、集合截斷萬有性與圓基本群 `π₁(S¹) ≃ ℤ`（`cubical_algorithms.mbt`, `univalence.mbt`, `truncation.mbt`, `circle_classify.mbt`）

在核心層補齊 CCHM `DUnglueEquiv`／`DNUnglueEquiv` 一等轉換規則、型別導向中性變數反射 `reflect_neutral_at_type` 與單例 J 消去 `dj_singleton_elim_value` 後，`equiv_bidirectional_certified_in` 在任意開放變數脈絡 `(env, ty_env, denv)` 下驗證一般型別對 `(A, B)` 的雙向同倫雙射資料 `(f : A → B, g : B → A, η : Πa. g(f a) ≡ a, ε : Πb. f(g b) ≡ b)` 經 Vogt 半伴隨化提升所得的 `DVEquiv` 及其逆等價、還有開放 `5` 變數等價合成 `equiv_compose_value`。

`truncation.mbt` 引入 `0`-截斷（集合截斷）高階歸納型 `SetTruncS(A)`（由點構造子 `|a|₀`、圓心 `hub` 與車輻 `spoke` 生成 `‖A‖₀`），在核心內部證明 `set_trunc_is_set_value`（`‖A‖₀` 為 h-set）、向任意 h-set 的萬有消去 `set_trunc_rec_set_value`／`set_trunc_elim_set_value`，以及開放 `4` 變數定理 `set_trunc_equiv_of_equiv_set_value`：若 `X ≃ B` 且 `B` 為 h-set，則 `‖X‖₀ ≃ B`。在 `circle_classify.mbt` 中，展平單構造子歸納整數 `IntegerS` 並由觀察型別法內證 `integer_is_set_value`（`ℤ` 為 h-set），在開放變數脈絡下完成依賴萬有覆疊雙向同倫 `circle_path_equiv_cover_value`（`Πx:S¹. (base ≡ x) ≃ Cover(x)`），取 `x = base` 得 `Ω¹(S¹) ≃ ℤ`（`circle_loop_space_equiv_integer_value`），再與集合截斷定理合成，給出**完整內部認證等價 `π₁(S¹) = ‖Ω¹(S¹)‖₀ ≃ ℤ`**（`pi1_set_circle_equiv_integer_value`），正反向對 `0, ±1, ±2` 計算往返精確成立。

驗收：`check_phase15_bidirectional_bijectivity_and_pi1_circle`。

#### 1.18.3 一般懸掛 `SuspS(A)`、基點環路—懸掛伴隨 `Σ ⊣ Ω`、圓楔連通與 Freudenthal 懸掛定理（`sphere_homotopy.mbt`, `schema.mbt`）

`sphere_homotopy.mbt` 定義參數化一般懸掛高階歸納型 `SuspS(A)`（`north`、`south` 與 `merid(a) : north ≡ south`），首先建立雙向認證等價 `Susp(Bool) ≃ S¹`（`susp_bool_equiv_circle_value`）與非基點餘錐萬有性質 `(Susp(A) → B) ≃ Cocone(A, B)`（`susp_universal_equiv_value`）。進而在基點類型 `(A, a₀)` 與 `(B, b₀)` 的 `5` 自由變數開放脈絡下，由 `south` 端點單例收縮消去自由餘錐點，建立**基點環路—懸掛伴隨定理** `loop_suspension_adjunction_equiv_value`：
$$(\Sigma A \to_* B) \;\simeq\; (A \to_* \Omega B)$$
並通過開放變數雙向雙射認證。

同倫連通性與穩定化方面：
1. **0-連通 Freudenthal 懸掛定理**：對任意具 0-連通證書 `c : Πx:A. ‖x ≡ a₀‖₀` 的有基點型別 `(A, a₀)`（`4` 自由變數開放脈絡），在 `Susp(A)` 上構造 h-set 覆疊族 `P(s) := (‖north ≡ s‖₀ ≡ |refl_north|₀)`，由 `c(x)` 將全部子午線 `merid(x)` 壓縮為與 `merid(a₀)` 相同的截斷路徑，從而證明每個環路的 0-截斷皆等於單位元，給出認證雙向等價 `freudenthal_pi1_susp_connected_equiv_unit_value`：
   $$\|\Omega^1(\mathrm{Susp}(A))\|_0 \;\simeq\; \mathbf{1}$$
   配合 `circle_0_connected_value`（`S¹` 為 0-連通）與 `susp_0_connected_of_pointed_value`（任意有基點型別的懸掛皆 0-連通），立即實例化導出高維球面基本群平凡化 **`π₁(S²) = ‖Ω¹(Susp(S¹))‖₀ ≃ 1`**（`pi1_susp_circle_equiv_unit_value`）與 **`π₁(S³) = ‖Ω¹(Susp²(S¹))‖₀ ≃ 1`**（`pi1_susp2_circle_equiv_unit_value`）。
2. **圓楔連通引理與 Freudenthal 環路懸掛映射**：在 `7` 自由變數開放脈絡下建立 `S¹ × S¹` 向任意 h-set 纖維族的楔連通延伸 `wedge_connectivity_circle_set_ext_value` 及其左右軸相干路徑 `wedge_connectivity_circle_left_coh_value`／`wedge_connectivity_circle_right_coh_value`（配合 `schema.mbt` 中 `comp_hit_value` 對惰性 `branch_raw` 的強制求值修復），並構造 Freudenthal 一維環路懸掛映射 `σ₁ : Ω¹(S¹) → Ω²(Susp(S¹))`（`p ↦ merid(p(i)) ⋅ merid(base)⁻¹`）及其保單位環路 2-胞 `freudenthal_susp_loop1_preserves_refl_value`，與單值 Hopf 不變量度數 `k ∈ {-1, 0, 1}` 形成穩定化對照。

驗收：`check_phase15_suspension_and_loop_suspension_adjunction`、`check_phase15_freudenthal_suspension_and_wedge_connectivity`。

### 1.19 第十六期：六大核心工程完備推進——大宇宙與開放同時 IR／容器正性、DSATUR 最大團與 0~1 黏合方塊合成、標準 SHA/Ed25519 與 WAL 日誌、精確 LLL／Van Hoeij 與 Q̄⊂ℂ 代數閉包、纖維化環路序列／Hopf–Freudenthal 收縮／五維 K₅、Huet 延遲約束圖／惰性串流／模組重連結／三方倉庫合併

第十六期將第十五期 §四中除第 5 項（BDD、SAT 與宿主立方）以外的全部 **6 項待完成工程**逐一攻克。六組正式定律分置於 `phase16_laws.mbt` 與 `algebra/phase16_algebra_laws.mbt`，全數納入定理登記總表（`116/116`）與規格登記表（`127` 條），並於核心 `nbe_dep.mbt` 修復異質中性路徑線上規範值與中性型別之雙向讀回／轉換（`quote_at` 與 `conv_at` 在 `DVNeutral(_)` 型別下對自帶規範型別構造子的派發）。

#### 1.19.1 工程一（Schema）：大宇宙累積同時 IR、Dybjer–Setzer 開放多解碼器同時 IR 與語義容器正性憑證（`schema_phase9.mbt`, `schema_positivity.mbt`）

1. **大宇宙累積同時歸納—遞迴編譯**：消除 `simultaneous_ir_compile_joint_block` 先前 `codomain_level ≤ base.level` 的封閉限制，依據累積宇宙計算 `joint_motive_level = max(base.level, maxᵢ function_universe_level(fᵢ))`。當解碼器 `El : Code → Type₀`（值域落於 `Type₁`）與小宇宙計數函數 `size : Code → Nat`（值域落於 `Type₀`）雙向互賴時，聯合 `Σ` 元組動機在 `Type₁` 單次消去並投影出各自閉項，正規化結果精確吻合。
2. **Dybjer–Setzer 開放多解碼器同時歸納—遞迴（`DOpenSimultaneousIRSpec`）**：引入同時擁有 `m` 個互賴解碼器 `(T₀,…,Tₘ₋₁)` 的開放宇宙規格，構造子引數除外部型別與直接遞迴碼外，支援依賴先前解碼值的引數 `DOpenArgDecodedVal` 與**函數式互賴遞迴碼族** `DOpenArgDecodedCodeFn(target_arg, decoder_idx)`（即 `(x : Tⱼ(a)) → U`），提供完整驗證 `open_ir_validate`、碼檢查 `open_ir_check_code`、同步解碼求值 `open_ir_eval_decode`、依賴消去 `open_ir_elim_value` 與單解碼器核心降階 `open_ir_lower_single_decoder`。
3. **語義正性憑證（`DFunctorialPositivityCert`）**：針對無展開定義之公理化算子 `F : Type_u → Type_u`，以核心 `d_check` 核驗兩類語義憑證並嚴格區分權限：多項式容器同構 `DFunctorContainerIso`（見證 `ΠX. Equiv (F X) (Σs:S. P(s) → X)`，且對 `S, P` 強制反循環檢查以攔截 `S := F Unit` 偷渡）授予嚴格正性 `strict_args = [0]`；純協變函子律 `DFunctorCovariantLaws`（`map`、`map_id`、`map_comp`）因無法排除雙重反變算子 `¬¬X = (X → Empty) → Empty` 等非嚴格正性不動點悖論，誠實僅授予非嚴格正性 `positive_args = [0]`。

驗收：`check_phase16_schema_large_open_positivity`。

#### 1.19.2 工程二（原始 `DSystem`、轉換與合成）：DSATUR 著色上界最大團修復與高維 `0 ~ 1` 黏合圓／環面開盒合成（`dsystem_compat.mbt`, `kan_ast.mbt`）

1. **DSATUR 飽和度著色上界最大團枚舉（`dsystem_repair_all_maxima_dsatur`）**：先嚴格過濾在 `r = 0` 與開盒 `base` 轉換相容的候選分支，再於每個衝突連通分量上執行 DSATUR 動態飽和度貪婪著色，為排序後頂點賦予嚴謹上界 `c(v)`（任意團在前缀中的頂點色號兩兩相異，故團大小不超過最大色號），於回溯搜尋中以 `|C| + c(v) < best_size` 提前剪枝，完整枚舉全部最大相容子系統並回報 `DSystemDsaturCliqueReport`。
2. **高維端點黏合（`0 ~ 1`）圓與環面開盒合成（`circle_square_glued_cap`, `torus_square_glued_cap`）**：當二維圓或環面開盒邊界並非單一 De Morgan 座標表達式、而僅在端點因 `loop(0) ≡ base ≡ loop(1)` 黏合相容時，利用 `S¹ ≃ K(ℤ, 1)` 與 `T² ≃ S¹ × S¹` 的群胚 H-空間旋轉結構計算四邊有號繞數 `w(j=0), w(j=1), w(i=0), w(i=1)`。當二上循環淨纏繞 `w(j=0) - w(j=1) + w(i=1) - w(i=0) = 0` 時構造二維填充方塊與帽並逐邊轉換驗證；若淨纏繞非零（如單邊 `loop` 其餘三邊常值，淨纏繞 `±1`），精確偵測拓撲阻礙並回傳 `filler = None`。

驗收：`check_phase16_dsatur_and_glued_cubical_comp`。

#### 1.19.3 工程三（持久層）：FIPS 180-4 SHA-256/512、RFC 8032 Pure-Ed25519 非對稱封緘與崩潰一致 WAL 日誌（`artifact_crypto_wal.mbt`）

1. **標準密碼學雜湊與非對稱簽章**：實作無外部依賴的純 MoonBit **FIPS 180-4 SHA-256**（64 輪）與 **SHA-512**（80 輪 64-bit 運算），以及素數體 `𝔽_p`（`p = 2²⁵⁵ − 19`）扭曲愛德華曲線 `−x² + y² = 1 + d x² y²` 上的完整 **RFC 8032 Pure-Ed25519** 密鑰衍生、確定性簽章與嚴格驗證（含規範點解碼 `y < p`、非平凡標量範圍 `0 < S < L` 防延展檢查與無輔因子方程 `[8][S]B = [8]R + [8][k]A`），逐位元組通過 NIST 與 RFC 8032 §7.1 官方測試向量。`CHARTSIG` v1 將倉庫鏈頭、條目鏈與全部活頁 blob 之 SHA-256 摘要納入 Ed25519 簽章並固定公鑰。
2. **崩潰一致預寫式交易日誌（`ArtifactWalStore` / `CHWALJRN` v1）**：每筆交易以帶自身 SHA-256 校驗和的 `BEGIN`、`PUT`、`DELETE`、`COMMIT`、`ABORT` 日誌幀追加寫入。`artifact_wal_recover` 掃描日誌流：凡在尾端遭遇斷電截斷或校驗損毀幀（`discarded_torn_bytes > 0`），或缺少對應 `COMMIT` 幀的未完成交易，一律原子回滾不污染底層儲存；已提交交易則冪等重放並支援 `artifact_wal_checkpoint` 壓縮截斷。

驗收：`check_phase16_crypto_ed25519_and_wal`。

#### 1.19.4 工程四（精確代數）：精確有理 LLL 格基約化、Van Hoeij 冪和跡格因式重組與 `Q̄ ⊂ ℂ` Rouché 圓盤代數閉包（`algebra/phase16_algebra.mbt`）

1. **精確 `BigInt` 有理 LLL 格基約化與 Van Hoeij 因式重組（`qmat_lll_reduce`, `van_hoeij_lll_recombine`, `qpoly_factor_lll`）**：以無浮點誤差的精確有理 Gram–Schmidt 正交化實作 δ = 3/4 Lovász 條件與尺寸約化，同步維護行列式 `±1` 的單模整數變換矩陣 `U ∈ GLₙ(ℤ)`。面對模任意素數皆分裂為大量低次因子的 Swinnerton-Dyer 多項式，`van_hoeij_lll_recombine` 將局部因式 Hensel 提升至高精模數 `M = p^k`，計算帶奇偶次數冪和跡（`k = 1, 2, 3, 4`）並以 Fujiwara 根界構造 p-進跡約束格，由 LLL 短向量直接讀出精確 0-1 因式組合，零指數子集搜尋即完成八次 `S₃(x)` 不可約性證明與平移乘積 `S₂(x)·S₂(x − 1)` 分解。
2. **複代數閉包 `Q̄ ⊂ ℂ`（`ComplexAlgNum`）**：以首一無平方因子不可約有理極小多項式 `minpoly ∈ ℚ[x]` 搭配隔離單根的高斯有理 Rouché 圓盤 `disk` 唯一表示任意複代數數。封閉實作精確判等（極小多項式相等＋圓盤二分收縮分離）、複共軛 `z̄`、加法／減法／乘法／非零求逆／除法（二元結式消元＋平方自由分解＋區間算術隔離篩選）與全體 `n` 次複根 `complex_alg_all_nth_roots`，在 `x⁴ + 1`、`x³ − 2` 與 `√i` 上完整驗證代數體公理與韋達恆等式。

驗收：`check_lll_lattice_and_van_hoeij_factor`、`check_complex_algebraic_closure_rouche`。

#### 1.19.5 工程五（球面同倫與高階相干）：纖維化環路序列等價、開放變量 Hopf–Freudenthal 收縮、`π₂(S²)` 分裂收縮與五維 Stasheff `K₅` 相干胞（`cubical_algorithms.mbt`, `sphere_homotopy.mbt`, `nbe_dep.mbt`）

1. **依賴和路徑分裂與纖維化環路序列雙向等價**：在開放 4 變數脈絡 `(B, P, b₀, e₀)` 下構造異質路徑傳輸等價 `pathp_equiv_transport_eq_value`、一步直達 `Σ`-路徑分裂 `sigma_path_equiv_subst_value` 與基底基於基點的**一般纖維化環路序列等價** `fibration_loop_equiv_fiber_path_value`：
   $$\Omega^1(\Sigma_{x:B} P(x), (b_0, e_0)) \;\simeq\; \Sigma_{p:\Omega^1(B, b_0)} \bigl(\mathrm{subst}\,P\,p\,e_0 \equiv e_0\bigr)$$
   並實例化於單值 Hopf 全空間 `E_Hopf = Σ_{x:S²} H(x)` 得認證雙向等價 `hopf_total_loop_equiv_fiber_seq_value`（全部 8 項開放雙向轉換義務核驗通過）。
2. **開放變量 Hopf–Freudenthal 恆等收縮與 `π₂(S²)` 分裂截面**：對任意開放自由環路變數 `p : Ω¹(S¹, base)`，利用旋轉族基點求值恆等律 `rot(c)(base) ≡ c` 與右單位消去構造二維同倫 `hopf_freudenthal_retraction_value`：
   $$\partial_{\mathrm{Hopf}}\bigl(\sigma_{S^2}(p)\bigr) \;\equiv\; p$$
   進而在集合截斷二階同倫群 `π₂(S²) := ‖Ω²(S²)‖₀` 與 `ℤ` 之間建立同態 `pi2_s2_hopf_hom_value : π₂(S²) → ℤ` 與生成映射 `integer_to_pi2_s2_value : ℤ → π₂(S²)`，並在開放自由整數變數 `z : IntegerS` 上證明認證分裂截面 `pi2_s2_hopf_retract_sect_value`（`π₂(S²)` 以 `ℤ` 為自由循環分裂收縮核）。
3. **五維 Stasheff 結合多面體 `K₅` 相干 5-胞（`dpath_associahedron_k5_cell5_value`）**：對五段非平凡圓環路複合 `(((p⋅q)⋅r)⋅s)⋅t → p⋅(q⋅(r⋅(s⋅t)))` 構造北半球 4-胞路線（經中間頂點 `(p⋅q)⋅(r⋅(s⋅t))` 串接兩個 Mac Lane 五邊形與自然性方塊）與南半球 4-胞路線（外層五邊形＋尾端五邊形＋結合子自然性），再以五維單例收縮與顯式 4-胞邊界填充生成連接南北雙半球路線的五維 `K₅` 相干胞。

驗收：`check_phase16_sphere_homotopy_and_k5`。

#### 1.19.6 工程六（HOU 與模組系統）：Huet 延遲 flex-flex 約束圖、拉取式惰性合一串流、模組 DAG 介面雜湊重連結與三方倉庫合併（`hou_elaborator.mbt`, `module_compilation.mbt`, `artifact_repository.mbt`）

1. **Huet 延遲 flex-flex 約束圖與拉取式惰性合一串流**：`hou_solve_with_delayed_flex_flex` 實作 Huet 預合一（pre-unification）範式，把無法唯一主合一的非 pattern `flex-flex` 約束滯留為雙端點元變數索引圖邊 `HouFlexFlexEdge`，一旦任一端點被剛性約束推進實例化即自動喚醒重入佇列，並可選以保序常數投影具現為閉合合一子；`HouLazyUnifierStream` 將遞迴 DFS 改寫為顯式 continuation 幀堆疊，按呼叫者 `hou_unifier_stream_next` 按需逐一產出正規形合一子（首次拉取展開節點嚴格少於窮盡枚舉）。
2. **多模組 DAG 拓樸規劃與介面雜湊截止重連結（`module_build_dag_incremental`）**：以 Kahn 演算法對模組集合做拓樸排序與循環／缺頁偵測；當上游模組修改不透明（`transparent=false`）定義本體而公開 `interface_hash` 不變時，全部下游模組 100% 命中快取零重編譯（`cache_hit_paths`），並由驗證後 `ModuleEnv` 重新實例化連結出反映最新實作正規形的頂層實例；透明定義變更則精確觸發依賴鏈重編譯。
3. **基於最近共同祖先（LCA）的確定性三方倉庫合併（`artifact_repository_merge_three_way`）**：沿兩分支倉庫的 `CHARTCHN` 鏈定位最深共同祖先快照，逐鍵執行三方差異判定：單邊新增／修改自動合併、雙邊獨立收斂至相同內容自動去重（`convergent_merges`）、單邊刪除無對向修改自動傳播墓碑（`tombstones_applied`），對修改—修改與修改—刪除真衝突則依 `ArtifactMergePolicy`（`AbortOnConflict`／`PreferLeft`／`PreferRight`）確定性裁決並重新封緘認證鏈。

驗收：`check_phase16_hou_stream_and_module_merge`。

## 二、規範形式目錄（逐結構）

| 結構 | 規範形式 | 相等之判定 |
|---|---|---|
| `Complex` | `(re,im)` | eps 分量 |
| `CVec` | 分量列 | eps 逐分量 |
| `CMat` | 列之列 | eps 逐分量 |
| 投影 `P` | `Σ vₖvₖ†`（ONB 外積）；不變量：`im(P)`、秩 `tr(P)` | 矩陣 eps 相等 |
| 向量分解 | `(Pv, (I−P)v)` 正交對 | 分量相等 |
| `Dim` | 端點布林化＋`dim_simplify` | 經面 BDD |
| `Face` | `BddManager` 中的 DAG root；樹形 `bdd_of_face` 為相容展開 | 同 manager root ID 相等；sat 為 root≠0 |
| `VecSystem` | `SystemNF`：值標記的不交 BDD 分割＋未定義區域 | 分割逐類相等 |
| `Cube` | 函數本身；路徑範例為 `path_line` | 網格外延 |
| 開盒填充 | `square_fill` 公式（仿射唯一式） | 邊界方程 |
| `Term`（未型別） | βπ 正規形 `nf` | 結構相等 |
| `Term`（型別化） | η 長 βπ 正規形 `nf_eta`（不含註記） | 結構相等 |
| `HTm` | `hoas_to_term` 後取正規形 | 經 `Term` 範形 |
| `Ty` | 葉序 `leaves_of_ty` | 結構相等 |
| `PVal` | 葉值列 `flatten_pval` | 結構相等 |
| 有限等價 | `Wiring` 帶號置換 | `wiring_eq` |
| `UPath` | 其等價的 wiring | `upath_eq` |
| `PathPVal` | `pathp_canonical`（遠端為 coe 像） | 端點與線相等 |
| `DTerm` | 按型別 `quote_at` 的 η 長依賴正規形；型別值以 `quote_ty` 讀回 | 結構相等 |
| 型別線 `DLine`／`DCheckedTypeLine` | 底層 `{at, coe_fn, fill_fn}`；受檢線保存已檢查 body＋環境，代換由求值給出 | coe/comp 律；checked 構造時檢查宇宙層級 |
| 立方 `DTerm` 系統 | 語法 `Array[DTubeTerm]`（面＋維度綁定 body）；形式合成為 `DNComp/DNHComp` | base／重疊相容＋按型別化簡；quote 多分支讀回 |
| 語義系統 `DSystem` | 相容系統：去底面/簡化面後同 body 分支以面聯集合併排序；任意原始系統：first-match 的 `DTubeNF` 不交區域分解；最大完成先 exact-restrict 再取相容圖最大團 | 相關維度面下轉換判定相容性；checked 入口才提升為 composition 系統；最大完成以 Tomita branch-and-bound 並回報 exact |
| partial 值 | `DSystemNF`：不交 BDD 有效區域＋值類別＋未定義區域 | 區域 BDD 相等＋類別值 `conv_at` |
| 持久環境 | `DEnv/DDimEnv` 帶長度連結串列，最內綁定在頭 | de Bruijn 索引查找與長度 |
| 惰性值/快取 | `DVThunk` 強制後的值；維度簡化鍵與引文項鍵的關聯表 | `force_count≤1`；鍵相等後重用 |
| HIT 點（具體） | Circle：`loop@r`（端點 base）；Torus：`square@(i,j)` 模對邊黏合 | Dim 的 ROBDD 語義相等＋點構造子 η/消去 |
| AST Glue 值 | `DVGlue(DSystem,A,i)`，元素為 `(raw 或 DPartial partial,base)`，決定面處 pack/unpack | 每分支 partial 沿其 T 線 coe 至 A 後與 base 轉換相等 |
| 生成歸納型別/值 | `DVInductive(spec,params,indices)` / `DVIntro(spec,ctor,params,args)`；引文為 `DInductive/DIntro` | 描述子相等＋telescopes/引數逐步 `conv_at` |
| 生成 HIT 型別/值 | `DVHitType(spec,params,indices)` / 非端點 `DVHitCell`；任意有限維端點逐維按 face 化簡 | 描述子、cell、引數與 `Dim` 語義相等；不可計算的移動維度 comp 保留形式中性範形 |
| 符號標量/矩陣 | 多變量多項式規範形與分式對；矩陣逐元素 | 多項式恆等（交叉相乘） |
| 譜投影 | `qₖ(A)/qₖ(λₖ)`（拉格朗日公式） | 模最小多項式整除＋求值矩陣恆等 |
| 仿射填充 | 四角雙線性插值（繫數由角差分唯一決定） | 在原子 i,j 的多項式恆等 |
| `GlueElem` | `(partial, base)`；`glue_from_base(a) = (e⁻¹a, a)` 為由 base 的範形 | 分量相等＋`glue_wf` |
| Glue comp 輸出 | 有限版：`(t₁, e₁(t₁))`；向量版：校正方塊 `k=1` 邊 | `glue_wf`／`glue_comp_vec_sound` |
| AST 等價 | `(fwd,bwd,section,retraction)` 四分量；`ua(e)` 的 primitive GlueEquiv 線 | 四分量型別導向轉換；沿 ua coe 為 fwd/bwd |
| Schema plan／telescope 快取 | registry 中以穩定鍵 intern 的 plan 與語義前綴鏈 | 鍵相等命中；hit/miss 計數 |
| `QPoly`／`QMat` | 去尾零升冪有理係數；有理矩陣與 RREF pivot 基底 | 精確結構相等；多項式模運算 |
| 代數數 | `QuadNum(a,b,d)`（d 無平方因數）或 `AlgNum` 模極小多項式餘式 | 係數結構相等 |
| Jordan 分解 | 廣義核鏈塊大小＋鏈基底，`PJP⁻¹=A` | 矩陣恆等與塊大小相等 |
| 認證數值立方體 | `QuadC` 矩陣與次數≤2 的 `CertPath/CertSquare` 係數 | 精確結構相等；Double 只比偏差/residual |
| 球面 `S³` | `Susp(Susp(S¹))` 的 north/south/meridian 生成子 | meridian 端點化簡與 HIT 消去/conversion |
| Jacobi 迭代 | 每步 before/after Hermitian 區間包絡＋累積酉區間矩陣；自適應報告另記可選精確分離、fallback 與 target_met | 逐旋轉包含證書與 Gershgorin 簇重算；包絡未達 singleton 目標時以精確 Sturm 分離後援 |
| HOU 核心 `UTerm` | zonked Miller-pattern 解經 beta/投影/Nat 簡化 | 無未解 meta 後譯 DTerm 並 dep_check |
| 參數化模組實例 | telescope 同時代換後的閉合宣告列 | 每宣告 `dep_check_closed`；名字由 bindings 解析 |
| Kan 開盒 | `KanBox{line, DSystem, base}`；transport filler 的函數形式 `i↦fill(i)` | 0 點為 base、面上與 tube 一致、1 點為 `comp_value` 結果 |
| 宇宙路徑 | `UniversePath` 保存受檢型別線，並把端點中的嵌套 Glue 表示遞迴塌縮 | 端點及傳輸等價的型別導向轉換（`universe_path_transport_conv`） |
| Q 上完整因式分解 | 首項係數＋不可約因式（重數）列；展開回原多項式 | 不可約證書（線性/低次/mod-p/聯合次數圖樣/Eisenstein）獨立重驗為 fast path，否則 Kronecker/有限域提升與精確不可約判定 |
| 實／複根隔離 | Sturm 有理區間；兩兩不交 Rouché 複圓盤且數目等於 squarefree 次數 | Sturm 變號數；Taylor 排除與細分圓盤證書 |
| 分裂域 | 逐次 `AlgNum` 塔的 modulus＋全部根連同重數 | 在塔上完全因式分解並逐根求值為零 |
| 一等層級宣告 | 層級 binders＋模板；實例為層級向量代換後的普通宣告 | 作用域檢查、模板驗證與實例檢查 |
| 非均勻巢狀族 | 參數轉換迭代編譯出的輔助族（Bush 形狀） | 生成 telescope 的依賴檢查與 intro 轉換 |
| 截斷 | `∥A∥₋₁` 的 point 與 squash 1-cell HIT | HIT 消去與 squash 端點化簡 |
| Adjoint 等價資料 | quasi-inverse 四分量＋三角形 2-path；improved counit 為三段複合 | 三角形 AST 型別；代表元以 型別導向轉換檢查 |
| 一般 adjointification／纖維收縮 | `lemIso` 三層填充給出的纖維路徑；`(center, contraction)`；新 retr 是對角收縮第一分量，三角形是其第二方塊轉角 | Bool／Circle 代表元上的端點轉換；Circle 中點加面下轉換 |
| `IntegerS`／π 商型／球面代表元 | `zero`、`posSucc(n)`、`negSucc(n)`（`n=|z|-1`）；`QuotientS(Ωⁿ, ∥Path∥)`；閉代表式以同 degree 的典範字為範形 | 生成 schema 依賴檢查；單位/逆元/結合律/sym 複合 3-胞遞迴組裝正規化 3-胞；只分類閉代表式語言 |
| HOU 搜尋／殘差求解 | 可回復 `Unifier` 快照、`HouSearchReport` 與以整個殘留集求解的 `HouResidualSolveReport{status,substitution,residual,search_rounds,...}` | principal 傳播與 transactional Huet 搜尋交錯；solved 前逐條重驗原約束，非 solved 回復輸入 |
| 已編譯模組二進位 | `CHMODBIN` 標頭＋固定標籤 payload；現行寫出 v3（與 CHREGBIN v2 共用 payload-local DAG codec），載入受 v1/v2/v3；hex 為文字形 | 結構解析狀態分流；load 另跑 `compiled_module_validate`；舊版寫出遇較新節點（tag 8/9 等）拒絕 |
| 成本最佳化 BDD／CNF | sifting 後變量序與 initial/final reachable 數；Tseitin `FaceCnfStats` | reachable 嚴格改善才採納；見證由 `face_holds` 重驗 |
| 一般代數認證立方體 | 共通 modulus 的 `AlgC` 矩陣與任意次係數路徑／方塊 | 逐係數精確相等；外 bumps 被拒 |
| DAG BDD | manager 內 root ID；大小為 reachable count；滿足數為 BigInt | DAG apply/eval/count/restrict/quantify 或 DPLL |
| 球面度數映射 | circle loop 冪次逐層懸掛；極交換 S³ 由 cell 順序交換表示 | 生成 meridian 的轉換與依賴消去 sect/retr |
| Hopf 映射 | `C²` 座標 `(2Re(zw̄),2Im(zw̄),|z|²−|w|²)`；纖維為共同相位軌道 | 像範數/相位不變的代數式檢查；Gauss 連結積分 |
| 已編譯模組 | 展平 entries＋exports＋依賴介面指紋；介面／實作雙 hash | synthetic 定義重闡釋、hash 重算與連結實例檢查 |
| 跨家族巢狀函子 | `DFunctorFamily(spec,params,indices)`，參數槽標 `DFunctorParamArg`；IH 束為逐引數一槽的巢狀 `DVPair…DVUnit` | validate（葉出現且可 gather）＋IH 束封葉計數＋束型別轉換 |
| 同時 IR 編譯產物 | 改名 `Base#函數名` 的 decode 規格（位置映射＋de Bruijn 重編號） | 編譯前後 validate；互依（−1 槽被用）回 `None` |
| Face 合意面 | 最大合意 `Face`（FEq0/FEq1 析取保留雙端點）；布林形為其 BDD 化（只保留相關維度支撐） | 相關維度上逐頂點求值＋`face_agreement_face_sound` |
| 宿主不透明立方/開盒 | `DCubeFunction{arity,at}` 與缺一面開盒；多項式版 `PolyCube` 有理座標列 | 邊界驗證報告（complete/overlaps_ok）＋填料逐面重驗 |
| registry 位元組 | `CHREGBIN` v2：magic＋版本＋長度＋校驗＋DAG schema codec payload（v1 可讀） | 載入狀態分流；往返後重驗註冊 |
| hash-cons 項／DAG snapshot | intern id 與 child-id 邊的有限圖；`DTermDagSnapshot` 為拓撲序 local shells＋edges＋roots，`CHDAGBIN` v1 為其位元組形 | snapshot 驗拓撲序/arity/roots；逐節點 hash-cons 匯入並回報 added/reused；intern 前後 dep_check/dep_nf 一致 |
| 雙二次數／多二次數 | 雙二次基底 `[1,√d₁,√d₂,√(d₁d₂)]`；`MultiQuadNum` 為至多四個平方類獨立生成元的 16 槽乘積基底（以平方類 span 對齊） | 對齊後係數相等；逆元以共軛乘積、符號以二進區間、同域/加一根開方經平方重驗 |
| CDCL 結果／DRUP 證明 | `FaceCdclProofResult{decision,stats,proof_steps}`；時序 Add/Delete 步驟，子句以字面集合為身分 | 與 brute force 差分；獨立 checker 在演進 active 子句庫重播 RUP 與刪除身分 |
| BDD 精確最優序 | `BddOptimalBuild{order,size,tried,exact}` | 全排列（n≤8）與增量 cofactor 子集 DP（n≤16）可證；逐點 `face_holds` |
| 圓的覆疊纖維 | base 處 `IntegerS` 規範整數；loop 點處 `ua(succ)` 的 GlueEquiv 型別 | 宇宙層轉換等於 ℤ／ua 線 |
| 繞數 | 規範整數 `zero/posSucc/negSucc` | ℤ 上轉換；複合環路以細分 transport 算 |
| 交錯模組定義 | `ModuleDef.items : Array[ModuleItem]`（import/decl 交錯） | 依序 elaboration；legacy 排序必失敗的範例對照 |
| 差異導引 case split | `CaseSplitReport{holds,probes,root_difference_variables,split_nodes}`（覆蓋 Bool 與無遞迴有限閉歸納族居民樹） | 先普通轉換，再只沿兩範形真正差異的有限型別變量遞迴代入全體閉居民 |
| 工件完整性鏈／認證 CAS／增量同步 | `CHARTCHN` 前條摘要連結鏈＋`CHARTAUT` 雙金鑰 MAC 認證籤＋前綴差量 `ArtifactSyncReport` | 逐條雙雜湊與 MAC 重驗；認證 CAS 拒絕過期 head 或偽鑰，增量同步只搬移缺失 blob |
| 正性見證／聯合同時 IR | `DPositivityWitness{declaration,definition}`；基礎歸納族上的單次聯合 `Σ` 元組動機消去器 | 閉合展開主體逐槽極性獨立核驗；互依同步函數投影自聯合消去並通過 `dep_check_closed` |
| 增量 DAG 差分／共用 bundle／TLV 封套 | `CHDAGDLT` v1 基表摘要＋新增節點；`CHSHRBUN` v1 跨模組與註冊表單一項池；`CHMODENV` v1 帶 critical 位元之 TLV 節 | 前綴摘要匹配後無拷貝重灌活 interner；未知非關鍵 TLV 跳過、未知關鍵 TLV fail-closed 拒絕 |
| Hensel 全分解證書／實代數根式／區塊 Jacobi | `QPolyFactorCertificate`（首項＋不可約因式＋證書）；`RealAlgRadical{minpoly,root_index,lower,upper}`；`JacobiBlockDeflatedReport` | 有限域分解經線性 Hensel 提升與獨立證書重驗；結式與 Sturm 唯一根區間算術；伴隨塊分解＋無平方因子消重根 |
| 剪枝最佳 BDD／DRAT 與裁剪／正交表探針 | `BddPrunedOptimalBuild`（n≤18，對稱軌道剪枝達 n≤20）；`FaceDrupTrimReport`；`ℙ¹(𝔽₈)` 強度 3/4 正交表 `DCubeCoveringReport` | 啟發式上界＋對稱軌道剪枝子集 DP；首字面 pivot 解析環境 DRAT 驗證與反向依賴裁剪；高維任意三／四軸非退化組合全覆蓋 |
| 連通分解最佳 BDD／索引化 LRAT／立方 Yoneda | `BddDecomposedOptimalBuild`（獨立支援分量拼接）；`FaceLratStep`＋`CHLRATBN` v1；`CheckedDCube` 與 `DCubeYonedaReport` | 共現交互圖連通分量各自精確 DP（28 變量 4 分量 exact）；提示 ID 線性時間查表傳播與 DRAT→LRAT 精化；通用對角讀回自然性與無探針精確外延 |
| 高階道路相干／中性圓截面／單值 Hopf | Eckmann–Hilton 3-胞、五邊形 4-胞、中性 `decode(encode(p))≡p` 截面、單值 `Hopf:S²→Type₀` 與整數不變量 | 立方邊界面逐面型別化轉換；開放環路變數上 J 消去端點轉換；`Ω³(S²)` 代表元精確映至 `0,±1,∓1,±2` |
| 雙向雙射認證／集合截斷／`π₁(S¹)≃ℤ`／`Σ⊣Ω`／Freudenthal | 開放脈絡認證 `DVEquiv`；`SetTruncS`（`‖A‖₀`）；`π₁(S¹)≃ℤ`；`(ΣA→*B)≃(A→*ΩB)`；`‖Ω¹(Susp(A))‖₀≃1` 與圓楔連通 | 開放變數下雙向截面／收縮轉換核驗；`ℤ` 與 `‖A‖₀` 內部 h-set 證書；0-連通懸掛導出 `π₁(S²)=π₁(S³)=1` 及 `S¹×S¹` 雙軸相干 |
| 大宇宙與開放同時 IR／容器正性憑證 | 累積 `joint_motive_level` 聯合消去；`DOpenSimultaneousIRSpec` 多解碼器開放宇宙；`DFunctorialPositivityCert` | 跨宇宙 `Type₁×Type₀` 聯合編譯；多解碼器驗證、求值、消去與單解碼器降階；反循環容器同構授予嚴格正性、純協變律僅授予非嚴格正性 |
| DSATUR 最大團修復／高維 `0~1` 黏合開盒 | `DSystemDsaturCliqueReport`；`CircleSquareWindingReport` 與二維圓／環面黏合帽 | DSATUR 飽和度著色上界剪枝枚舉全部最大相容子系統；零淨纏繞以 H-空間旋轉構造二維填充，非零二上循環纏繞阻礙回 `None` |
| SHA-256/512／Ed25519 封緘／WAL 日誌 | FIPS 180-4 摘要；RFC 8032 `CHARTSIG` 64-byte 簽章；`CHWALJRN` 幀校驗交易日誌 | NIST/RFC 測試向量逐位吻合；公鑰固定、反高階扭轉與 `S<L` 檢查；斷尾與未提交交易原子回滾、已提交交易冪等重放 |
| 精確 LLL／Van Hoeij 重組／`Q̄⊂ℂ` 代數閉包 | `LllReductionReport`（`U∈GLₙ(ℤ)`）；`QPolyLllFactorReport`；`ComplexAlgNum{minpoly,root_index,disk}` | 精確有理 Gram–Schmidt δ=3/4 約化；Fujiwara 界冪和跡格重組八次 Swinnerton-Dyer；結式消元＋Rouché 圓盤細分實作 `Q̄⊂ℂ` 體算術與開方 |
| 纖維化環路序列／Hopf–Freudenthal／五維 `K₅` | `Ω¹(ΣB P)≃Σ(p:Ω¹B)(subst P p e₀≡e₀)`；開放環路 `∂_Hopf(σ_{S²}(p))≡p`；`π₂(S²)` 分裂截面與五維 `K₅` 胞 | 開放與 Hopf 全空間雙向認證等價；開放 `p:Ω¹(S¹)` 收縮與開放 `z:ℤ` 分裂截面；`K₅` 南北雙五邊形半球端點轉換核驗 |
| Huet 延遲圖／惰性串流／DAG 重連結／三方合併 | `HouDelayedGraphReport`；`HouLazyUnifierStream`；`ModuleIncrementalBuildReport`；`ArtifactThreeWayMergeReport` | 滯留 flex-flex 邊喚醒與具現、按需 continuation 枚舉；不透明變更下游零重編重連結；相對 `CHARTCHN` LCA 的收斂／墓碑／衝突合併 |
| 規格條目 | `SpecEntry` 六元組 | `spec_registry_sound` |

## 三、範疇目錄（逐範疇）

| 範疇 | 物件 | 態射 | 主要結構／律 | 實作 |
|---|---|---|---|---|
| Hilb（有限維） | `Cⁿ`（以 `CMat.n` 索引） | `CMat` | dagger `†`、雙積 ⊕ | `complex.mbt` |
| Karoubi 包絡 Kar(Hilb) | Hermitian 冪等 `P` | `QAP=A` 的矩陣 | 恒等 = P 自身；†；冪等分裂 | `categories.mbt` |
| 投影偏序 | 投影 | `P≤Q ⇔ QP=P`（蘊含唯一） | 交換者的積 = meet | `projector.mbt` |
| 面偏序／格 | `Face` 模 BDD | `φ≤ψ` | ∧ 積、∨ 餘積、⊤/⊥ | `interval.mbt`, `bdd.mbt` |
| 立方體範疇 □（De Morgan 味） | 維度 `n` | 面映射 `restrict_face`＋退化 `degenerate_cube` 生成 | 立方體恆等式 | `cube.mbt`, `categories.mbt` |
| 句法 CCC（βπ 版） | `LTy`（含未型別前身） | 項模 βπ | 積、指數 | `nbe.mbt` |
| 句法 CCC（βη 版） | `LTy` | 項模 βπη，範形為代表 | 積/指數萬有性；coe 箭頭是同構 | `nbe_eta.mbt` |
| 有限集合與 wiring | `Ty` | `Wiring` | 對稱冪冪（⊗、換位、結合子、單位子與三相干律） | `wiring.mbt` |
| 有限宇宙的路徑 | `Ty` | 同構（經 ua 變相等） | ua 計算性；積交換自然性方塊 | `pathp_glue.mbt` |
| 箭頭範疇 `Ty²` | 等價 `T≃A` | 交換方塊（等價線） | Glue comp 的定義域 | `glue_comp.mbt` |
| 句法帶族範疇 (CwF) | 脈絡與脈絡中的型別 (`DTerm/DValue`) | 代入與項（範形為代表） | Π/Σ 形成與依賴代入、Typeᵢ 宇宙族 | `nbe_dep.mbt` |
| Kan 纖維線 | `DLine` 的 `at(i)` | 立方體值與傳輸路徑 | coe/comp 對 Π/Σ/U 的遞迴；依賴族為路徑→線 | `kan_dep.mbt` |
| 立方 CwF 與 Kan 型別構造子 | 項＋維度脈絡中的 `DTerm/DValue` | 代入、維度作用與 comp/hcomp 項 | Π/Σ/PathP/資料/HIT/Glue/Universe 逐一保存 Kan 提升；消去子與形式 comp 交換 | `nbe_dep.mbt`, `kan_ast.mbt` |
| 生成歸納族函子 | `DInductiveSpec` 的參數化型別 | `DVIntro` 與生成消去子 | 嚴格正性函子的初始代數（含跨家族與同規格自嵌；SelfFamily 參數正性以最小不動點、foreign 巢狀 IH 以函子映射搬運，片斷外仍拒絕）；comp 逐引數沿先前 filler 提升 | `schema.mbt`, `schema_functor.mbt` |
| 生成 HIT 胞腔 | `DHitSpec` 的參數化型別 | 任意有限維 cells 與逐維 face 化簡 | 消去子保存 cells；多維角落相干；可判定移動維度時逐引數 comp，否則形式中性合成 | `schema.mbt`, `schema_extensions.mbt` |
| 多項式代數 | Q 上多變量多項式與分式 | 矩陣與其多項式 `q(A)` | 譜分解是單位分解；插值給出投影 | `algebra/symalg.mbt`, `algebra/spectral_symbolic.mbt` |
| AST 等價與 ua | AST 型別 | 一等 `Equiv` 四分量 | ua 的 coe 計算性；GlueEquiv 沿偏等價黏合；語義 `lemIso` 給出纖維收縮與 adjoint 三角形資料 | `equiv_ast.mbt`, `kan_ast.mbt`, `equivalence_phase10.mbt` |
| 路徑運算與單值性 | AST 型別與宇宙層 | 路徑值與傳輸等價 | transitivity 由顯式 hcomp 方塊構造；ua/pathToEquiv 以 uaβ、retraction 同倫與 Glue 方塊互見證 | `cubical_algorithms.mbt`, `univalence.mbt` |
| 代數擴張線性代數 | `AlgNum` 擴張上的向量空間 | `AlgMat` | 廣義特徵空間、primary 分解與 Jordan 型 | `algebra/algnum.mbt`, `algebra/Jordan.mbt` |
| BDD DAG | 固定次序布林函數 | root ID 與 apply 格運算 | hash-consing 規範圖；候選序、有預算 sifting 與可證最優序（n≤8 全排列、n≤16 子集 DP、對稱軌道剪枝單分量 n≤20、連通支援分解多分量精確拼接）；後備 Tseitin 上的 watched DPLL 與帶 LBD 刪除、DRUP/DRAT 檢查、核心裁剪、DRAT→LRAT 精化及索引化線性時間 LRAT（`CHLRATBN` v1）的 1-UIP CDCL | `bdd_dag.mbt`, `face_sat_watched.mbt` |
| 球面懸掛與 `Σ⊣Ω` | 參數化 `SuspS(A)` 與基點類型 | 子午線胞腔、餘錐與基點態射 | `Susp` 為同倫推出商；`Susp(Bool)≃S¹`、`(Susp A→B)≃Cocone(A,B)`、開放 5 變數 `(ΣA→*B)≃(A→*ΩB)`，以及 0-連通 Freudenthal 定理 `‖Ω¹(Susp A)‖₀≃1`（`π₁(S²)=π₁(S³)=1`）與圓楔連通 | `sphere3.mbt`, `sphere_homotopy.mbt` |
| 模組函子 | 參數模組與 import 圖 | 引數代換與內聯宣告 | telescope 為交錯的 import/宣告 items；open/alias 是名字投影；opaque 是邊界抽象 | `module_system.mbt` |
| Q[x] 與分裂擴張 | 有限代數擴張塔与實代數數 | `AlgPoly`、`RealAlgRadical` 與根 | 唯一因式分解（Berlekamp/CZ＋線性 Hensel 提升＋全分解證書）；結式與 Sturm 隔離封閉實根式算術；分裂塔完全線性化 | `algebra/qpoly_factor.mbt`, `algebra/phase14_algebra.mbt`, `algebra/splitting_field.mbt` |
| 層級方案與同時宣告 | 層級脈絡中的宣告模板 | 層級代換、聯合 Σ 元組消去與同步函數 | 宇宙 scheme 是層級指派函子；互歸納是向量初始代數；循環互依同時 IR 為基礎初始代數到相依乘積族的唯一截面 | `schema_phase9.mbt` |
| 基點球面映射與單值 Hopf | 懸掛球面（北極為基點） | 懸掛函子像、度數映射、Freudenthal 環路懸掛映射與單值 `Hopf:S²→Type₀` | 單位環路、極交換等價、Eckmann–Hilton 3-胞與 Mac Lane 五邊形 4-胞；單值 Hopf 纖維叢將 `Ω³(S²)` 代表元映至整數不變量 | `cubical_algorithms.mbt`, `sphere_homotopy.mbt`, `sphere_classification.mbt` |
| 圓上的覆疊族與基本群 | schema 圓 `S¹` 上的點 | 纖維中的 subst 提升、雙向 J/歸納同倫與 0-截斷反射 | helix 族（base↦ℤ、loop↦`ua(succ)`）；開放變數脈絡下完整證明 `Path S¹ base x ≃ Cover(x)`、`Ω¹(S¹)≃ℤ` 與 `π₁(S¹)=‖Ω¹(S¹)‖₀≃ℤ` | `circle_classify.mbt`, `truncation.mbt`, `univalence.mbt` |
| 已編譯模組函子與認證儲存 | 已檢查參數模組物件與共用項池 | 介面連結、TLV 封套、認證 CAS 與增量同步 | `CHSHRBUN` 共用全局 DAG；`CHMODENV` 支援向前相容 TLV；`CHARTAUT` 對稱 MAC＋樂觀 CAS 與鏈前綴差量同步 | `module_compilation.mbt`, `module_binary.mbt`, `artifact_repository.mbt` |
| Retract Kan 結構 | 特徵空間／子線 | 立方體 | 剪枝函子保持填充（在邊界恆等） | `cube.mbt`, `glue_comp.mbt` |

## 四、第十六期後仍保留的邊界

> **本節於合併第四輪（`merge/`）改寫**：改為「現況 ＋ 瓶頸坐標」雙欄制，所有數字可重跑（見 §4.10）。

第十五期 §四所列的 **6 項待完成工程**（Schema 大宇宙與開放同時 IR／語義正性、DSATUR 最大團與 `0~1` 黏合合成、SHA-256/512＋Ed25519＋WAL 持久層、LLL＋Van Hoeij＋`Q̄⊂ℂ` 代數閉包、纖維化環路序列＋開放 Hopf–Freudenthal 收縮＋五維 `K₅`、Huet 延遲約束圖＋惰性串流＋增量重連結＋三方合併）已於第十六期全數落地驗收。

自本輪起本節改為**雙欄制**：每一條邊界都必須同時寫出「**現況**」與「**瓶頸的精確坐標**」。
沒有任何一條可以用「仍屬開放前沿」單獨結案 —— 若剩下的部分說不清楚在哪，它就是尚未被理解的，而不是已量測的。

量測來源：合併樹 `merge/`（模組 `vv0101v01/golden`，20 套件／13 聯邦／153 測試），
全部數字由 `moon test`、`moon run cmd/audit`、`python3 tools/arch_check.py`、`sh ledger/audit.sh verify` 現算，不手寫。

### 4.0 判定用語（固定，不再變形）

| 標記 | 含義 | 驗收方式 |
|---|---|---|
| **突破** | 原本「做不到」的事現在做完，且有兩條獨立路徑互證 | 交叉驗證一致 |
| **推遠** | 邊界還在，但被推到新的、可量測的位置 | 有前後兩個數字可比 |
| **變化** | 問題被換成另一個問題（通常是更可控的） | 舊問題的殘餘被新問題取代並命名 |
| **剔除** | 該邊界被證明是某個更強結果的特例 | 給出化歸 |
| **殘餘** | 剩下未解的部分，**必須寫出坐標**（維度／階數／複雜度類） | 能被下一步直接瞄準 |

### 4.1 邊界總表

| # | 邊界 | 第十六期狀態 | 現在狀態 | 判定 | 精確殘餘 |
|---|---|---|---|---|---|
| B1 | Schema 大宇宙 | 無界宇宙多態、高階索引容器在外 | 差分約束判定＋最小解＋正環證人 | 變化 | Mahlo／超宇宙公理（不可動） |
| B2 | `DSystem`／轉換／合成 | NP-hard、`DNComp` 中性 | 三界合流剪枝、非阿貝爾 Čech `H¹` 接入 | **推遠** | 稠密圖 NP-hard；非阿貝爾**高維** HIT |
| B3 | 持久層 | 純函數位元組介面 | 跨程序、跨紀元雜湊鏈＋形狀防線 | 變化 | 無鎖、無共識 |
| B4 | 精確代數 | 位長成長制約 | 三環分工＋`ℚ(ζ_p)` 精確算術 | **推遠** | 超越數；壞素數 |
| B5 | BDD／SAT／立方 | `n>20` NP-hard | 事前判定（差分階數）＋**表示選擇器** | **根治（一半）** | 大 `n` 的 ROBDD 排序 |
| B6 | 球面同倫與高階相干 | 撓率群、Blakers–Massey 開放 | Hopf 雙路＋撓率分離＋`k₄=Sq²ι₃` | **突破一格＋推遠** | `ℤ/2` vs `ℤ/4`；`n≥6` 的 `K_n` 塔 |
| B7 | HOU／模組 | Goldfarb、熱載入 | 有限載體片段＋DAG 重連結 | 變化（治理） | Goldfarb（本質）；執行期熱載入 |

### 4.2 Schema（B1）

**現況。** 累積大宇宙同時 IR、`DOpenSimultaneousIRSpec` 多解碼器開放同時 IR 與反循環容器同構正性憑證均已實作；
`bridge/b1_schema_levels.mbt` 把層級約束化成差分約束系統，`O(V·E)` 判定可滿足性，並在不可滿足時輸出**正環證人**。

**瓶頸坐標（第五輪更正）。** 舊寫法是「Mahlo 不在核心內、不可動」。這一輪改掉：
目標本身要先修 —— 對 Mahlo 宇宙加自然消去規則不一致（Palmgren 定理 6.1），
而外部 Mahlo 已被歸納—遞迴捕捉（Dybjer–Setzer，強度 ≥ `KPM`），真正超出的是**內部** Mahlo。
故 B1 的目標改為 **B1′（方案 B + C）**：

> **B1′**：宇宙層級是一級物件、`<` 可判定；跨層 `Lift` **嚴格**保所有型別構造子；
> 任何不變量必須**對呈現無關**，且此契約要有閘門。

**B1′ 的落地（第六輪，`bridge/b1_level_algebra.mbt`）。**

1. **層級 = CNF 序數 `< ε₀`**：`0 | ω^e·c + r`；`<`／`sup`／`+`／`succ` 全部可判定，
   `ord_rank`／`ord_height` 是良基見證（任何嚴格遞減鏈都短於秩）。
   實測：`1 + ω = ω`、`ω + 1 ≠ ω`、`ω·3 + ω = ω·4`、`sup(ω³, ω) = ω³`。
2. **極限層級變成可判定的一級物件**：同一組約束 `U_ω ≥ sup_n U_n` 在 `Int32` 差分約束上**寫不出來**，
   在序數層級系統上可行且最小解是 `U_n = 0, U_ω = ω, T = ω + 1`。這是舊 `level_solve` 到 B1′ 的真正增量。
3. **嚴格 `Lift` 的五條等式**：E1 單位、E2 合成、E3 保構造子、E4 注入、E5 有限回原樣，strict **5/5**；
   cumulative（帶轉換節點）在 E1、E2 失敗 —— 「嚴格」在這裡是**可測的語法等式**，不是修辭。
   其中 E2 的位移是 **`b + a`** 而不是 `a + b`：序數加法非交換，先 `b` 後 `a` 的合成位移就是 `b + a`。
   第一版寫成 `a + b`，有限層級上看不出來，拉到 `ω` 立刻失敗 —— 這一條本身就是「為什麼要序數層級」的證據。
4. **呈現無關性閘門**（`bridge/g9_invariance.mbt`）：不變量登記表要求每條 `≥ 2` 個模型且值一致；
   4 條真登記通過，單模型與「兩模型不一致」兩種壞例都被擋下。

**仍未動的部分**：層級上的 Π₃-reflection（「對所有層級封閉的宇宙」）不在這裡。
差別是現在能**指名**缺的是哪一條，而不是把整個 Mahlo 目標懸空。

**判定：變化（目標更換並落地三步）＋ 殘餘指名（Π₃-reflection）。**

### 4.3 原始 `DSystem`、轉換與合成（B2）

**現況（三件事都已可量測）。**

1. **極大團的三條界同時在樹上**：秩界 `ω ≤ rank_F(I+Ā)`、LP 鬆弛（精確有理單純形，Bland 規則）、
   貪心色數界；三者可插拔進同一棵分支定界，且**分別記帳**每次剪枝。

   | 圖 | `ω`（暴力） | 節點：無界 → 三界 | 秩界鬆 | LP 鬆 |
   |---|---|---|---|---|
   | `G(12,0.5)` seed 7 | 4 | 45 → **9** | 8 | 2 |
   | `G(12,0.5)` seed 11 | 4 | 43 → **19** | 7 | 2 |
   | `G(12,0.5)` seed 23 | 4 | 61 → **13** | 8 | 2 |
   | `K(3×3)` 多部圖 | 3 | 79 → **7** | 0 | 0.5 |
   | `K(4×3)` / `K(5×3)` | 4 / 5 | — | 0 / 0 | 2 / 2 |

   四種界設定（無界／秩／色／三界）**全部與暴力同值** ⇒ 三條界都是合法上界，插拔不改變答案。
   多部圖上秩界一次到底；隨機稠密圖上 LP 明顯優於秩界（鬆 2 vs 鬆 7~8）。

2. **非阿貝爾阻礙可算了**：Čech `H¹` 分類器（枚舉全部 torsor、按規範等價分類）在 `S¹` 上給出
   `|Z¹(S¹; S₃)| = 216 → |H¹| = 3`（共軛類），而線性 `H²` 的計數會說 `6`；可縮空間 `D²` 上兩者都是 `1`。

3. **`0 ~ 1` 黏合圓／環面 H-空間開盒合成**（含二上循環纏繞阻礙偵測）與 DSATUR 飽和度著色上界剪枝仍如第十六期。

**瓶頸坐標。** 一般 NP-hard 稠密隨機圖的極大團最壞情形仍受組合複雜度制約（本節只把常數與界推遠，
沒有改變複雜度類）；有限居民切分仍是項層級外延工具；任意**非阿貝爾高維**通用 HIT（無 H-空間結構者）
的點相等開盒仍保留形式中性 `DNComp` —— 本輪只把「維度 1 的非阿貝爾阻礙」變成可算，高維那一段原樣保留。
**判定：推遠（兩處）。**

### 4.4 持久層（B3）

**現況。** SHA-256/512、Pure-Ed25519（`CHARTSIG`）、帶斷尾回滾的 WAL（`CHWALJRN`）之外，
帳本已是**跨程序雜湊鏈**：`sled_verify` 起點自洽、`sled_parse_lines_chain` 驗完整帳本、
payload 一變就**自動封存開新紀元**（舊鏈頭進新紀元的 `prev`，兩條鏈硬綁）。

實際使用的紀元鏈（五代）：

```text
c710be7d… → fc042b6f… → f241c62a… → 930f8804a88f… → 67fb8eeb60e2…   VERIFY ok=true records=23
```

本輪還補上一道防線：`emit()` 在落盤前檢查**形狀**（每行必須是 JSONL），否則 `EMIT_NOT_JSONL` 退出。
這條是被一次真實污染逼出來的 —— 見 §4.10。

**瓶頸坐標。** 儲存介面刻意保持純函數／抽象位元組協議（跨 `wasm-gc` 與 `native` 可重現），
因此**不直接耦合** POSIX `flock`／`mmap`／`fsync`，也沒有網路共識層：
多寫者併發下的互斥與線性化**不在**此層，且本節不假裝它在。**判定：變化。**

### 4.5 精確代數（B4）

**現況。** 精確有理 LLL、Van Hoeij 冪和跡格重組、`Q̄ ⊂ ℂ` Rouché 圓盤複代數閉包之外，本輪新增兩件：

1. **`ℚ(ζ_p)` 的精確算術**（`homotopy/torsion.mbt`）：元素是 `p−1` 個有理係數，
   乘法用 `Φ_p(ζ) = 1 + ζ + … + ζ^{p−1} = 0` 約化；**全程無浮點**，用於 Reidemeister 撓率（§4.8）。
2. **成本模型的整數安全**：`C(20,8)` 與 `Σ_{i≤d} C(n,i)2^i` 都曾在 `Int32` 靜默溢位（分別被算成 `19447` 與負值），
   現在一律 `Int64` 累加並飽和。

**瓶頸坐標。** 超越數（`e, π`、複對數／指數的 Schanuel 範疇）不在 `Q̄` 內；
極高維稠密不可約 Hermitian 矩陣的特徵多項式係數位長仍受精確有理算術本質成長制約。
本輪只把**新的係數域**（分圓整數環）納入同一套精確規則，沒有放寬任何既有界。
**判定：推遠。**

### 4.6 BDD、SAT 與宿主立方（B5）

**現況（B5 的殘餘被真正換掉了）。**

1. **事前判定**：`a_S = ∂_S f(0)`（高階差分）⇒ 代數次數可以在**不寫出 `2ⁿ` 個 Möbius 係數**的前提下被證明。

   | `n` | 判定出的次數 `d` | 高階差分檢查 | 稀疏重建查表 | 子空間維度 | 全量 Möbius | 加速 |
   |---|---|---|---|---|---|---|
   | 16 | 3 | 2516 | 4993 | 697 / 65536 | 1048576 | **210×** |
   | 20 | 3 | 6195 | 9921 | 1351 / 1048576 | 20971520 | **2113×** |

2. **表示選擇器**（`bridge/g8_selector.mbt`）：在「仿射判別 / 差分重建 / 全量 Möbius」三條路裡挑**預測成本最小**者，
   並用同一支程式驗證（預測 vs 實測；重建 ANF 與全量 Möbius 逐係數比對）。

   | 函數（`n = 12`） | 次數 | 選路 | 預測 = 實測 | 相對全量 |
   |---|---|---|---|---|
   | `x₀⊕x₃⊕1` | 1 | 仿射 | 13 | **快 1890×** |
   | `x₀x₁⊕x₂x₅⊕x₀` | 2 | 差分 | 289 | **快 85×** |
   | `Maj₁₂` | 8 | 全量 | 24576 | 1× |
   | 隨機 seed 5 | 11 | 全量 | 24576 | 1× |

   交叉點 `d*`（差分重建開始比全量貴的次數）：`n=12 → 4`、`16 → 5`、`20 → 6`（約 `n/3`）。
3. **Carlet 上界**：`AI(f) ≤ ⌈n/2⌉` 在 `n ≤ 4` 上**逐函數**（共 65772 個）成立；`Maj₅..₈` 全部達到上界 ⇒ 上界緊。

**瓶頸坐標。** 單一無對稱不可分解稠密布林函數在 `n > 20` 時一般最佳 ROBDD 排序仍屬 NP-hard（誠實回報 `exact=false`）；
選擇器的成本模型只算**搬運次數**，不含記憶體項 —— 交叉點分析顯示 `n = 20` 上真正的關鍵是「不要 materialize 整個真值表」，
而這一點本節尚只是**結論**，尚未成為**實作**。`5` 軸以上純黑盒閉包仍須提升為 `CheckedDCube`。
**判定：根治（稀疏性一路）＋選路（新能力），殘餘如上。**

### 4.7 球面同倫與高階相干（B6）

**現況。**

1. **Hopf 纖維化的雙路互證**：`S¹ → E → S²` 按歐拉類 `d` 分類，Gysin 上同調與 CW 鏈複形經 UCT 的結果**逐維一致**
   （`d ∈ {−1, 0, 1, 2, 3, 5}`：`(ℤ,0,0,ℤ)`、`(ℤ,ℤ,ℤ,ℤ)`、`(ℤ,ℤ/d,ℤ/d,ℤ)`），`π₁ = ℤ/|d|`。
2. **Reidemeister 撓率把同調看不見的那一格補上**：在 `ℚ(ζ_p)` 內精確計算 `τ_a = 1/((ζ^a−1)(ζ^{as}−1))`，
   `p = 5, 7, 11, 13` 上得到的分類與代數判據 `q' ≡ ±q^{±1} (mod p)` **完全一致**。
   於是 `L(7,1)` 與 `L(7,2)` 被分開（`H_*` 兩者都是 `(ℤ, ℤ/7, 0, ℤ)`）—— **同調看不見定向，撓率看得見**。
3. **第一個 Postnikov 不變量算出來了**：用 Serre 容許單項式定理得 `H^*(K(ℤ,3);F₂)` 逐維
   `1,0,0,1,0,1,1,0,1,2`（度 0..9），`H⁵ = ⟨Sq²ι₃⟩` 一維 ⇒ `k₄ = Sq²ι₃ ≠ 0`；
   奇質數下第一個能動 `ι₃` 的操作是 `P¹`（度 `3+2(p−1) ≥ 7 > 5`）⇒ `k₄` 的 mod `p` 化恆零 ⇒ **`π₄(S³)` 無奇撓率**。
4. **∞-groupoid 的「合成」被量測分開**：用既有邊補角（reuse）在 `S¹∨S¹` 上把 `H₁` 由 `ℤ²` 打成 `0`；
   新增自由邊再補（fresh／pushout）保 `ℤ²`。**補的是新胞腔還是舊胞腔，是可測的差別。**
   且 `fresh` 補 1~2 輪後仍不是 Kan（`S¹∨S¹` 仍缺 552 角、`Δ²` 缺 11040 角）⇒ 相干塔不會在有限維停下。

**瓶頸坐標。**

- `π₄(S³)` **已收斂**：`≅ coker(×β) = ℤ/2`，`β = ±2`（第六輪）。剩下的唯一缺口是 `[ι₂,ι₂] = ±2η`
  這條古典等式尚未在樹內形式化 —— 它現在是**引用**，不是缺口；若是哪天要完全自足，那就是下一個施工項。
- 完整 `1`-連通 Blakers–Massey 推出（`σ_{S²}` 在 0-截斷上的滿射性，閉合雙向同構 `π₂(S²) ≃ ℤ`、`π₃(S²) ≃ π₃(S³) ≃ ℤ`）仍為開放。
- 任意維度 `n ≥ 6` 的結合多面體 `K_n` 無窮相干塔仍為開放前沿；本樹只有 `K_n` 的**生成器**（翻轉圖），沒有進塔。
- ∞-groupoid 已推到 **3-截斷**（`tetra`）；停在這裡的原因是清楚的：`n`-球面的缺陷在 `n+1` 維，
  每加一維只是把缺陷往上一維推 ⇒ 有限截斷永遠不 Kan。

**第五輪新增兩件（都可重跑）。**

5. **撓率證書自動化**（`coeff/torsion_cert.mbt`）：不再手寫見證，改為「解 `∂₂ c = k z`、`z ∈ ker ∖ im`、
   `k` 最小」的自動搜尋（`solve_q` 有理高斯＋`solve_z` 整候選回代）。實測 `ℝP² → k=2`、`L(7) → k=7`、
   `M(ℤ/5,1) → k=5`、`ℤ/2⊕ℤ/3 → k=2, z=(1), c=(1,0)`、`S² → 無證書`，四項驗證逐條為真。
6. **呈現無關性**（`bridge/g9_invariance.mbt`）：同一個空間給兩個模型（單純剖分 vs CW 貼附），
   要求 `H_*(ℤ)`、`H_*(F₂)`、`χ`、撓率 `k` 逐項相同。`T²`、`S¹`、`ℝP²`、`S¹∨S¹∨S²` 四組全部一致。
   這是**單值性（univalence）在計算上的影子**：等價即相等 ⇒ 不變量不得依賴呈現。
   同時留下反面教材：`H_*` 分不出 `L(7,1)` 與 `L(7,2)`，說明「不變量相同」推不出「等價」。

**第六輪新增兩件。**

7. **`π₄(S³)` 由 `{ℤ/2, ℤ/4}` 收斂到 `ℤ/2`**（`homotopy/brunerie.mbt`）：把殘餘從「需要整係數 k-invariant」
   改寫成「需要一個整數 `β`」——`π₄(S³) ≅ coker(×β)`。`β` 的來源是 Whitehead 平方 `[ι₂,ι₂] = ±2η`（引用），
   而 Hopf 不變量 `d` 在胞腔層面**就是** Moore 空間 `M(ℤ/d,2)` 的 `d`（`∂₃ = d`）。
   可算的那一半全部精確：`H₂(M(ℤ/d,2)) = ℤ/d` 對 `d = 0,1,2,3,4,7` 逐值驗過，且與 `coker(×d)` 一致。
   於是 `β = 2 ⇒ ℤ/2`，而 `β = 4` 會給 `ℤ/4` —— **候選是可判別的，而值被釘在 2**。
   與 mod 2 Postnikov 一致（`k₄ ≠ 0`、無奇撓率）。證書逐列標明「算的」或「引的」，不混為一談。
8. **∞-groupoid 的 3-截斷**（`higher/tetra.mbt`）：把截斷推到 3 維，並用通用維度記帳量「填到第幾維才夠」。
   結果：`S² = ∂Δ³` 在 2-截斷上**沒有**缺 2-角，缺的是 **4 個 3-角**；`S³ = ∂Δ⁴` 在 3-截斷上**沒有**缺 3-角
   （已是 Kan），缺的是 **5 個 4-角**。也就是說 **每個 `n`-球面的 Kan 缺陷正好落在 `n+1` 維**——
   「補幾維就 Kan」不成立，每一維的角都要下一維的單形。這是相干塔不停的正確形式。

**判定：突破一格（撓率分離透鏡空間）＋推遠（Postnikov mod 2、∞-groupoid 語義、撓率證書、呈現無關性、`π₄` 收斂、3-截斷）。**

### 4.8 HOU 與模組系統（B7）

**現況。** Huet 延遲 `flex-flex` 約束圖、拉取式惰性合一串流、模組 DAG 介面雜湊截止重連結、
基於 `CHARTCHN` LCA 的確定性三方合併均如第十六期；治理面在本輪擴到 **13 聯邦／20 套件**
（新增 `higher`／`homotopy`／`opt` 三個聯邦），`architecture.v3.json` 一登記即通過 `arch_check`。

**瓶頸坐標。** 三階以上一般高階合一受 Goldfarb 定理限制**本質不可判定**（無窮合一子串流按拉取與預算惰性展開）；
模組連結仍針對**靜態非循環 DAG**，執行期熱載入不在本層。**判定：變化（治理），殘餘未變。**

### 4.9 三個「真邊界」（不可動，寫在這裡以免被誤讀為待辦）

1. **Mahlo／超宇宙公理**：不在有限層級核心內。**第五輪更正**：這不只是「不在核心內」，
   而是目標本身要先修 —— Palmgren 悖論（對 Mahlo 宇宙加自然消去規則 ⇒ `A = ¬A`，不一致且非正規化）
   使得「Mahlo + 消去」不是可用的目標；而外部 Mahlo 其實已被 IR 捕捉（Dybjer–Setzer，強度 ≥ `KPM`）。
   因此本方針**建議更換目標**：改為「宇宙層級代數 + 單值一致的呈現無關性」（B1′），
   Mahlo 降級為文獻註記。完整論證與三個候選方案見 `MERGE-RESEARCH.md` §10。
2. **Goldfarb 定理**：三階以上一般高階合一不可判定。
3. **超越數與 `Q̄`**：`e, π` 不在代數閉包內；精確有理算術的位長成長是**本質**成本。

**判定：不變。** 把這三條列出來，是為了讓 B1–B7 的「推遠」不被誤讀成「突破」——
本節的判定標準是「有沒有一條新的、可重跑的量測」，不是「有沒有講得更好聽」。

### 4.10 本節數字的重跑方式

```sh
cd merge
moon check --deny-warn             # 0 error / 0 warning（含 --deny-warn）
moon test                          # 192 / 192（41 套件）
moon run cmd/audit                 # 16 節／156 行／約 12 秒
moon run cmd/audit -- --quick      # ≤ 2 秒 CI 閘門：QUICK ok=true（七條）
moon run cmd/audit -- --full       # 340 行：+ 階梯／係數環／B1–B7／三界／Carlet／橋 18–21／Morse／可見性表
python3 tools/arch_check.py --graph # ARCH_OK packages=41 federations=13 internal_edges=103
python3 tools/doc_audit.py --check  # DOC_OK（0 缺文檔）
python3 tools/dead_code.py --check  # DEAD_CODE_OK（基線已清空：自家套件 0 個未引用 pub）
python3 tools/abort_audit.py --check # ABORT_OK（自家套件 0 個 abort）
sh ledger/audit.sh verify          # VERIFY ok=true records=36
sh ledger/audit.sh head            # 外部錨定值
```

一次值得記錄的事故：本輪 `cmd/audit` 一度被誤寫成只印探針的版本，`emit()` 於是把**報告文字**寫進了帳本，
`verify` 立刻回 `LEDGER_UNPARSABLE`。修法有兩層 —— 帳本從 `archive/` 還原並重生紀元，
`emit()` 增加 **JSONL 形狀檢查**（不是 JSONL 就 `EMIT_NOT_JSONL` 退出）。
「落盤前先驗形狀」自此是本節所有數字的落盤前提。

### 4.11 第五輪：backlog 逐項結案與 Mahlo 目標更換

**§7 的 12 項 backlog 逐項交代（不整表帶過）。**

| # | 項目 | 結局 | 依據 |
|---|---|---|---|
| 1 | 架構檢查 v3 + 依賴圖 | ✅ | `arch_check.py --graph`：20 套件／13 聯邦／35 內部邊；圖上 12 聯邦、18 聯邦邊 |
| 2 | 規格審計擴展 | ✅（改寫） | 併樹無「規格家族表」，改查**每符號必有文檔**：`doc_audit.py` → 961 pub / 0 缺 |
| 3 | 譜的三環分工（剩 Morse 指標流區間化） | ◐ | 三環已落地；Morse 需指標流單調性證明，本輪未動 |
| 4 | `score.Berezinian` ↔ `scheme` 上同調 | ⏸ | 兩邊都缺公共介面，硬接等於空殼互扣；改以「21 橋 → 三族 23 條」重新計數 |
| 5 | 撓率證書推廣到任意有限 CW | ✅ | `coeff/torsion_cert.mbt`，5 個例子逐條驗證通過 |
| 6 | `T²` vs `S¹∨S¹∨S²` 杯積判別 | ✅ | 第二輪 `coeff/cup.mbt`，本輪由呈現無關性釘住 |
| 7 | `DNComp` 接 `H²` 障礙基 | ⏸ | 缺「項 → 上鏈」解釋器層；本輪只接非阿貝爾 `H¹`（G6） |
| 8 | 秩界 + 分解 + 對稱軌道三合一 | ◐ | `opt/refine.mbt`：假孿生收縮與連通分解保 `ω`（18→13、節點 29→19）；**真孿生**只計數（`K₃` 反例） |
| 9 | 表示選擇器 | ✅ | `bridge/g8_selector.mbt` + 交叉點 `n=12→4`、`16→5`、`20→6` |
| 10 | 帳本接 `CHARTCHN`／`CHWALJRN` | ⏸ | 併樹無 WAL；改做 JSONL 形狀防線 |
| 11 | `--quick` 審計 | ✅ | `QUICK ok=true`（四條等式） |
| 12 | root 76k 行 + `symlib`／`topos`／`scheme` 併入 | ◐ | 後三者已在樹上；root 未併，另立工程量 |

**Mahlo 目標的更換（B1′）。** 文獻讀下來的結論是三段：①對 Mahlo 宇宙加自然消去規則不一致
（Palmgren 定理 6.1）；②外部 Mahlo 已被歸納—遞迴捕捉，真正超出的是**內部** Mahlo；
③更新路線（Dybjer–Setzer 的 indexed IR 版 extended predicative Mahlo）需要比現有 schema 更強的機制。
因此建議把 B1 的目標換成：

> **B1′**：宇宙層級是一級物件且 `<` 可判定；跨層 `Lift` **嚴格**保所有型別構造子；
> 任何不變量必須**對呈現無關**且此契約有閘門。

三步落地（都不需要新型別論）：層級代數（`Lvl` 正規形＋良基見證）、`Lift` 的保構造子檢查表、
呈現無關性登錄兩次（G9 已有 4 空間 × 2 模型）。詳見 `MERGE-RESEARCH.md` §10–§11。

### 4.12 第六輪：B1′ 採用（方案 B + C）與四項落地

**目標更換已生效。** 依 §4.9 的更正，B1 的目標由「Mahlo／超宇宙公理」改為 **B1′**（層級代數 + 嚴格 Lift + 呈現無關性）。

| 項 | 內容 | 狀態 | 可重跑的量測 |
|---|---|---|---|
| 1 | `Lvl` = CNF 序數，`<`／`sup`／`+` 可判定，良基秩與高度 | ✅ | `1+ω=ω`、`ω+1≠ω`、`ω·3+ω=ω*4`、`sup(ω^3,ω)=ω^3`；秩 3、高度 3、正規 true |
| 2 | 層級約束求解（含極限種子） | ✅ | 有限約束 `A≥B+1, B≥A+1` 不可行；極限約束可行，最小解 `U_n=0, U_ω=ω, T=ω+1` |
| 3 | 嚴格 `Lift` 五條等式 vs 累積模型 | ✅ | strict 5/5；cumulative 在 E1、E2 失敗 |
| 4 | 呈現無關性閘門（登記表） | ✅ | 4 條真登記通過；單模型、兩模型不一致皆被擋 |
| 5 | `π₄(S³)` 收斂為 `ℤ/2`（Brunerie 數） | ✅ | Moore 字典 `d∈{0,1,2,3,4,7}` 全一致；`β=2 ⇒ ℤ/2`、`β=4 ⇒ ℤ/4` 可判別 |
| 6 | ∞-groupoid 3-截斷 | ✅ | `S²` 缺 4 個 3-角；`S³` 缺 0 個 3-角、缺 5 個 4-角 |

**兩個新坑（都已寫進 `merge/AGENTS.md`）**：
①序數加法非交換 ⇒ `Lift` 的合成位移是 **`b + a`**，第一版寫成 `a + b`，有限層級上看不出來、拉到 `ω` 才失敗；
②`d`-角的面是 `(d−1)`-單形、填充是 `d`-單形，第一版整體錯一格，於是 `S²` 被算成「缺 4 個 2-角」（實際是 3-角）。

**殘餘（誠實列出）**：`[ι₂,ι₂] = ±2η` 仍是引用；層級上的 Π₃-reflection 仍缺；
Morse 指標流、`DNComp → H²`、`CHARTCHN/CHWALJRN`、root 76k 行四項維持 ◐／⏸，理由同 §4.11。

### 4.13 第七輪：合併完成與減債

**合併完成。** 前六輪的「待併清單」在這一輪清空，`golden` 剩下的三塊全部進入 `merge`：

| 併入 | 規模 | 手法 | 檢核 |
|---|---|---|---|
| root 套件 | 63 檔／76,456 行 | 原樣複製，只改 import（`algebra` → `exact/algebra`） | 第一次有了真正的 root 套件 |
| `semiring/*` | 23 套件／10,425 行 | 去自引用 import；`par_host` 加 `native` + `async@0.22.5` | 23 套件全登記進架構 |
| `golden/bridge` | 10 檔 | 併進同一個 `bridge`：公開符號衝突 **0**（87 vs 163） | 一個套件同時有 B／G／R 三族與原庫十橋 |
| `cmd/*` | 5 支 demo／3,784 行 | 整批複製、改 import | 可執行包 1 → 6 |

**架構帳**：套件 **20 → 41**、聯邦 13、內部邊 35 → 94、樹 **153,219 行／261 檔**。

**一次事故與它的代價（寫下來以免重演）**：`cp` 讓 `golden/bridge/bridge_wbtest.mbt` 覆蓋了同名檔，
24 條測試消失，`moon test` 總數由 168 掉到 149 才被發現。處置是按公開介面重建 29 條 bridge 測試
（B1–B7、G3、G5–G9、六條 `check_*`、大統一、憑證、分數卡、熱帶橋、隨機圖秩界方向），
並把「拷貝前先查同名」寫進 `AGENTS.md`。重建後 repo **172 / 172**。

**減債（可重跑）**：
- 新工具 `tools/dead_code.py`：`--write` 產生 `DEAD-CODE.md`，`--check` 對照基線，**自家套件出現新的未引用 pub 就退出 1**。
- 未引用 `pub fn`：全樹 204 → 180（golden 的公開 API 保留，那是規格）；自家 5 套件 **31 → 3**（12 個刪除、16 個 probe 接進 `--full`）。
- 跨套件同名定義 72 → 30；`abort(` 225 處全是守衛，分佈記在 `DEAD-CODE.md`。
- 修掉三個真錯：`@exactalg`／`@algebra` 同套件雙別名、兩個結構欄位記憶錯誤、**秩界方向寫反**（`ω ≤ rank(I+Ā)` 是上界）。

**判定：合併完成（changed）＋ 減債（debt down, tooled）。**

### 4.14 第八輪：補齊橋 18／20／21 與 Morse 指標流的區間化

前三輪留下三件「設計完成、未執行」的東西：MERGE-RESEARCH §2.3 標為 `⧗` 的橋 20／21、被標為
`◐`（缺單調性）的 Morse 指標流，以及與 golden `topos` 的 Alexander–Whitney 杯積「各說各話」的
狀態。這一輪把三件全部做成**可執行、可量測**，並且在過程中**推翻了自己原本的兩個寫法**。

#### 4.14.1 橋 18：接上 golden 的 AW 杯積環（`bridge/b18_aw_cup.mbt`）

`@topos` 有一支精確有理數的 AW 杯積（`simplicial_cup_1_1`／`verify_alexander_whitney_leibniz`／
`simplicial_cup_h1_h1_rank`），我們自己有 `coeff/cup.mbt` 的 `F₂` 版。橋接之後量到的**不是**
「兩邊一致」這種空話，而是係數環決定看得到什麼：

| 空間 | `dim H¹`（ℚ / `F₂`） | `dim(H¹⌣H¹)`（ℚ / `F₂`） | 分次交換的實際樣子 |
|---|---|---|---|
| `T²`（7 頂點 Möbius–Császár） | 2 / 2 | **1 / 1** | 上鏈層僅差上邊界（48/48），上同調層反交換 |
| `S¹∨S¹∨S²` | 2 / 2 | 0 / 0 | 5/5 個乘積全在 `B²` ⇒ 上同調層杯積為零 |
| `ℝP²`（6 頂點） | **0 / 1** | **0 / 1** | ℚ 上看不到；`F₂` 上 `α⌣α` 就是 `H²` 的生成元 |
| `S¹=∂Δ²` | 1 / 1 | 0 / 0 | `H¹` 非零但維度不夠乘 ⇒ 乘積為零 |
| `S²=∂Δ³` | 0 / 0 | 0 / 0 | 5/5 個乘積全在 `B²` |

**過程中修掉兩個真錯，第二個是數學上的真發現：**

1. **閉鏈基底不是閉的。** 上一版用 `@core.nullspace_basis(…, mk_field(2147483647))` 求 `Z¹`，
   而 `F_p` 的高斯消元用 `Int32` 相乘，`p = 2³¹−1` 時直接溢位 —— 拿回來的 7 個「閉鏈」
   逐個驗 `d¹w ≠ 0`。改用 `@algebra.qrows_nullspace`（分數精確 RREF）之後 `dim Z¹(T²) = 8`。
   這也是上一版「分次交換欄永遠顯示 ℚ 上全零」的真正原因（不是因為 `T²` 沒有符號，而是因為
   那批向量根本不是閉鏈）。
2. **分次交換律在上鏈層只是「差一個上邊界」。** 課本的 `α⌣β = (−1)^{pq}β⌣α` 是**上同調**層的命題；
   AW 杯積在上鏈層只到 `α⌣β + β⌣α ∈ B²`。因此這一欄不能二分（「互為負」／「全零」），
   而要量出三類：**strict**（逐座標就反交換）、**homotopy**（差一個上邊界 ⇒ 上同調層才反交換）、
   **zero**（`H¹⌣H¹ = 0`，符號無從談起）。`T²` 落在 homotopy（48/48），沒有一個例子落在 strict。
   順帶量到：**截斷會製造假象** —— 只取前 3 個閉鏈時 `T²` 的乘積全部落在 `B²`（看起來杯積為零），
   用完整 8 維基底才看到非平凡類。

順帶把 `dim Z¹` 與 `dim H¹` 分開：`Z¹(T²)` 是 8 維、`H¹` 是 2 維，混用會讓「ℚ 上的閉鏈有幾個」
被誤讀成貝蒂數。`F₂` 側則給出對照的杯積秩（`cup_rank_f2`），逐字對應 `simplicial_cup_h1_h1_rank`。

#### 4.14.2 橋 20：譜流的區間認證（`bridge/b20_spectral_cert.mbt`，`super ↔ cubical`）

把 `@algebra.qmat_symmetric_eigenvalue_isolations`（Jacobi 區間認證）與 `@spec.spectral_flow`
（浮點取樣）放在同一個 `SpecRow` 上對照：

| 端點對 | 認證 | 浮點（取樣 2/3/5/9/17/65） | 判定 |
|---|---|---|---|
| `diag(−1,−1,1) → I` | 2 | 2 | 一致 |
| `diag(−1,−1,1) → diag(−1,1,1)` | 1 | 1 | 一致 |
| `diag(−1,1) → diag(1,−1)` | 0 | 0 | 一致 |
| `[[−2,1],[1,−2]] → [[2,1],[1,2]]` | 2 | 2 | 一致 |
| `[[0,0],[0,−1]] → [[1,0],[0,−1]]` | **不確定（`None`）** | 0（六個取樣全部） | **浮點錯了** |

最後一行是本橋的價值所在：端點有 `0` 特徵值 ⇒ 「正/負」根本沒有定義，浮點取樣一律回 0，
看起來像一個乾淨的答案；區間認證則回 `None`。**認證的用處不是答案一樣，而是它敢說不知道。**
Witten 指標 `dim ker D − dim ker Dᵀ` 用精確秩算，與 `@spec.susy_index` 四例全一致
（`2×3 rank2 → 1`、`D=0 → 1`、`3×2 rank1 → −1`、`2×2 rank2 → 0`）。

#### 4.14.3 橋 21：Berezinian 與 `ℙ¹` 的 Čech 上同調（`bridge/b21_berezinian.mbt`，`super ↔ scheme`）

自帶 Laurent 多項式算術（`LPoly`，`Int32` 指數 ＋ `Int64` 係數）之後：

- **換圖 Jacobi 行列式**（`ν_i ↦ ν_i/x_i` 的餘切叢部分）：`det = −t^{−(m+1)}`（`m = 1,2,3` 逐一驗）；
- **Berezinian 的度數**：`Ber(ℙ^{m|n}) = −(m+1) + n`，實測 `1|0 → −2`、`1|1 → −1`、`1|2 → 0`、`2|0 → −3`、`2|1 → −2`；
- **`ℙ¹` 上 `O(d)` 的 Čech 上同調**：`d = 2,1,0,−1,−2,−3,−4` 給
  `(h⁰,h¹,χ) = (3,0,3),(2,0,2),(1,0,1),(0,0,0),(0,1,−1),(0,2,−2),(0,3,−3)` —— 即 `χ = d+1`、`h⁰ = max(d+1,0)`、`h¹ = max(−d−1,0)`；
- **橋等式**：`χ(Ber) = n − m = 1 − sdim`（`1|0 → −1`、`1|1 → 0`、`1|2 → 1`、`1|3 → 2` 全成立）——
  超版本的自旋叢度數與概形側的 Čech 計數是同一件事的兩面；
- `@score.smatg_ber` 的乘性在 Grassmann 代數上 20/20 成立（數值側與符號側對照）。

Čech 截斷寫錯過兩版（兩版都表現為「某個 `O(d)` 多出一個假維度」）：等窗 ⇒ `t^{−(M+1)}` 掉出 `C¹`
變成零行 ⇒ 假 `h⁰`；補 `|d|+1` 格 ⇒ `d>0` 時又製造零行（`O(0)` 算出 `h⁰=2`）。正解是
`j ≤ M + d`（`d` 可負，且 `jmax < 0` 直接回 `(0,0)`），令每個生成元的像都落在 `C¹` 內。

#### 4.14.4 Morse 指標流的區間化（`homotopy/morse.mbt`，§7-3 殘餘）

上一輪把「Morse 指標流」掛 `◐` 的理由是「缺一條單調性」。這一輪把它做成**區間族**：
對過濾後的胞腔複形做**保序消元**（`morse_reduce` 回 `low(j) = i` 的配對表），
由配對給出 `Bar{dim, birth, death}`，`β_p(t) = #{birth ≤ t < death}`。單調性不再是一句承諾，
而是四條可量測的斷言：

| 空間 | 胞腔 | 臨界胞腔 (0/1/2) | `β` (ℚ) | 單調 | 跳躍 ±1 | χ 守恆（次序／值） | 弱 Morse |
|---|---|---|---|---|---|---|---|
| `S²=∂Δ³` | 14 | 1/0/1 | 1/0/1 | ✓ | ✓ | ✓/✓ | ✓ |
| `T²`（7 頂點） | 42 | 1/2/1 | 1/2/1 | ✓ | ✓ | ✓/✓ | ✓ |
| `ℝP²`（6 頂點） | 31 | 1/0/0 | **1/0/0** | ✓ | ✓ | ✓/✓ | ✓ |
| `S¹`（3 邊） | 6 | 1/1 | 1/1 | ✓ | ✓ | ✓/✓ | ✓ |
| `S¹∨S¹∨S²` | 24 | 1/2/1 | 1/2/1 | ✓ | ✓ | ✓/✓ | ✓ |

`ℝP²` 的 `1/0/0` 是**有理**貝蒂數（`H₁ = ℤ/2` 在 ℚ 上看不到）——和 4.14.1 的 `F₂` 欄正好互補。

**這一節同樣推翻了兩版寫法，值得逐字記下來：**

1. **「`β_p(t)` 沿 `t` 單調」是錯的命題。** 過濾空間的 `β_0` 會**下降**（連通分支被合併），
   `β_1` 會先升後降。真正成立的是**逐區間**的 `f(出生) ≤ f(死亡)` —— 這才是 §7-3 缺的那條，
   也才是「指標流」一詞的內容：指標沿配對是單調的，不是沿 `t`。
2. **「每個臨界值上 `β` 恰有一個維度跳 ±1」要按**次序**講，不能按值講。** 撞值（同一個 `f` 上有多個胞腔）
   會讓一次跳兩格；更麻煩的是某個 `β` 的下降與另一個 `β` 的上升可以落在同一個值上（`T²` 的
   `f = 1005` 就是），於是「恰有一個維度改變」在數值切法下是假命題。改用**過濾次序**（它本身就是參數）
   之後，每加入一個胞腔必恰有一個維度變動 ±1，這才是離散 Morse 的內容。
   曾試著用 `< 1` 的微擾把值拉開來救，結果 `β(t+½)` 會把下一個胞腔一起算進來 ⇒ 歐拉守恆反而紅了。
3. **χ 守恆用兩種獨立算法對照**：沿次序（每個前綴）與沿函數值（每個臨界值）。
   兩條都過，才把 `◐` 改成 `✓`。

#### 4.14.5 本輪閘門與帳

```text
moon check                          0 error / 0 warning
moon test                           186 / 186（+14：橋 18 四條、橋 20 兩條、橋 21 三條、Morse 五條）
python3 tools/arch_check.py --check ARCH_OK packages=41 federations=13 internal_edges=95（bridge → super/{spec,score} 新邊）
python3 tools/doc_audit.py --check  DOC_OK
python3 tools/dead_code.py --check  DEAD_CODE_OK（基線 3 條，無新增）
python3 tools/dead_code.py          自家未引用 pub：31 → 3 → 3（本輪新增 6 個名字，全部接進 probe 或測試）
sh ledger/audit.sh verify           VERIFY ok=true records=33（新紀元，封條 = 舊鏈頭 9f31fcb3…）
sh ledger/audit.sh head             44fe8f72…
moon run cmd/audit                  155 行
moon run cmd/audit -- --full        328 行（新增「R18」四節）
```

樹 **265 檔／154,934 行**（+4 檔／+1,715 行）。

**判定：三項 `⧗`／`◐` 全部轉為 `✓`；其中兩項在執行時被自己的量測推翻並改寫（分次交換的層級、
`β` 單調性的方向）。**

### 4.15 第九輪：深度健檢、還債、與一次真的推送

第八輪把「設計過但沒跑」的三件事跑起來；這一輪只做一件事：**把債還清，然後把樹推到它該在的地方。**
四類債（重複、死碼、崩潰式錯誤、文檔漂移）逐類結清，並且每一類都留下一支**可重跑的閘門**，
而不是一次性打掃。

#### 4.15.0 專案現況概況（一頁）

| 面向 | 現況 |
|---|---|
| **這是什麼** | `golden`（cubical-hermitian，精確代數＋立方型／Kan 填充＋拓樸／概形）與 `notebook`（tensorlab，模消元＋半環＋有限範疇／置換群）**合併後的單一模組** `vv0101v01/golden` 0.3.0 |
| **規模** | 267 個 `.mbt`／155,058 行；41 個套件；13 個聯邦；103 條內部依賴邊 |
| **測試** | `moon test` **192 / 192**（41 套件全綠） |
| **定理登記表** | `moon run cmd/main` **116 / 116** 條；`--time` 逐條計時（總計 ≈ 179 秒，存於 `logs/theorems.txt`；最慢的是 BDD 最佳順序 53.2 秒） |
| **可執行包** | 6 支：`cmd/audit`（審計）、`cmd/main`（定理）、`cmd/showcase`（指標展示）、`cmd/symbench`、`cmd/symdemo`、`cmd/semiringreport`（native） |
| **審計** | `cmd/audit` 16 節／156 行（≈12 秒）；`--full` 340 行（≈3 分 48 秒），含 R1–R23 全部可重跑量測 |
| **閘門** | `moon check --deny-warn`／`moon test`／`arch_check.py`／`doc_audit.py`／`dead_code.py`／`abort_audit.py`／`ledger verify` —— 全綠 |
| **帳本** | 4 個紀元互鎖，36 條記錄，`VERIFY ok=true`，鏈頭 `7182d1b8…` |
| **文檔** | `SPEC.md`（本文件）／`SPEC.en.md`（英文鏡像）／`MERGE-RESEARCH.md`（合併研究與 15 輪記錄）／`AGENTS.md`（給 agent 的坑）／`DEAD-CODE.md`／`ABORT-CONTRACTS.md`（皆自動生成） |

一句話：**合併早已完成，這一輪把它變成一個可以被別人接手、也可以被下一輪繼續量測的狀態。**

#### 4.15.1 健檢：真正找到的三個錯（不是「看起來沒問題」）

1. **`binom` 有兩份實作，而且語義不同。** `bridge/g7_sparsity.mbt` 那份對 `C(−1, 0)` 回 **0**，
   `super/score/score.mbt` 那份回 **1**（先判 `k == 0`）。兩份都被各自的測試覆蓋，所以誰也沒紅；
   一旦去重、讓其中一份消失，`[S-T-FlatSym] 展平對稱性` 立刻紅 —— **去重本身就是一次等價性測試**。
   正解：`k == 0` 先回 1（廣義二項式的約定），並在 `intutil_wbtest` 寫明這條邊界。
2. **`push` 之後的 `abort` 回報是假的。** `cmd/main` 過去只有「全部通過」四個字；`--time` 一跑，
   116 條裡最慢的 5 條（BDD 最佳順序 52.8 秒、K₅ 相干 47.2 秒、`Ω¹(S¹)≃ℤ` 24.8 秒、LLL 18.7 秒、
   Freudenthal 13.7 秒）佔了總時間的 **88%**。這不是 bug，但它是「不知道自己在花什麼」的典型。
3. **`dim Z¹` 與 `dim H¹` 混用**（第八輪遺留，這一輪在文檔裡釘死）：`Z¹(T²)` 是 8 維、`H¹` 是 2 維。

**沒有找到的**：`moon check --deny-warn` 在整棵樹上 **0 warning**；`moon test` 192/192；
沒有任何 `Int32` 靜默溢位的新站點（`int_pow`／`int_binom` 現在只有一份，且 `binom` 用 `Int64`）。

#### 4.15.2 去重：10 個名字收斂到 `exact/algebra`，30 → 21

新建 `exact/algebra/intutil.mbt`（單一來源）：

| 函式 | 原本幾份 | 收斂後 |
|---|---|---|
| `int_pow` | 2（`cube.mbt`、`elim/core`） | 1（`@algebra.int_pow`，13 個呼叫點改指過來） |
| `int_binom` | 2（`bridge`、`super/score`） | 1（`Int64` 內部運算，飽和 2·10⁹） |
| `int_sort` | 2（`bdd.mbt`、`higher/tetra`） | 1（插入排序，穩定） |
| `int_lsr` | 2（`super/score`、`super/sledger`） | 1（邏輯右移，非算術右移） |
| `int_mod_inv` | 2（`exact/algebra` 私有、`super/spec`） | 1（`Int64` 中介，大素數不溢位） |
| `int_vec_eq` | 2（`same_face`、`same_set`） | 1 |
| `int_vec_is_zero` | 1 + 同名不同義（`complex.mbt` 是 `CVec` 構造子） | 1 |
| `int_vec_scale` | 1 + 同名不同義（`elim/core` 是 mod p、`complex.mbt` 是 `CVec`） | 1 |
| `int_mat_vec` | 2（`bridge`、`coeff`） | 1 |

**跨套件同名定義：30 → 21。剩下的 21 個逐條看過，結論是「不是債」**（詳見 `DEAD-CODE.md`）：

- **同名不同型別**：`Graph`（semiring 加權 vs symlib 有限）、`Perm`、`ab_show`、`mat_add/mul/from_rows/get/identity`（`Complex` 矩陣 vs `F_p` 矩陣）、`vec_scale`（`CVec` vs mod p）。
- **同名不同演算法**：`smat_mul`（`SetMat` 路徑集 vs `SMat` mod p）、`uf_find`（帶／不帶路徑壓縮）、`decompose`（三種分解）、`search`／`find`／`rec`／`build`／`go`（區域閉包與標籤迴圈）。
- **刻意平行**：`backend_name`／`par_for`／`shard_io_bench`（`semiring/par` 的介面 vs `par_host` 的 native 實作）。
- **本來就該重複**：`main`（6 支執行檔）。

也就是說：**「同名」從 30 降到 21，而真正需要收斂的 9 組已經收斂完**；剩下的是「重名但不是同一件事」，
這在原文檔裡被混在一起講，是這一輪順手修正的敘述錯誤。

#### 4.15.3 死碼：自家套件 3 → 0，基線清空

三個殘留全部**接進審計**（不是刪掉，因為它們是有意義的量測）：

- `coeff/probe.blindness_count` → 新探針 `visibility_probe()`，`--full` 的 R19 節印出「ℚ-盲區 4/7」；
- `coeff/homology.visibility_table` → 同一節印出 7 模型 × 6 環的完整表；
- `higher/infinity.sset_s2` → `infinity_probe()` 多一行 `S²(6邊)` 的 Kan/H₁ 量測。

`tools/dead_code_baseline.json` 已清空（`"ours": []`）：**任何自家套件新增未被引用的 `pub` 都會讓閘門紅**。

#### 4.15.4 abort 債：apex 從 18 → 0，全樹 202 站點逐條入帳

「錯誤用崩潰表達」是這棵樹最大的方法論債。這輪把它拆成兩半：

1. **apex（`bridge`／`higher`／`homotopy`／`opt`／`coeff`）= 0 個 `abort`。**
   `bridge` 的 18 處全部改成 `Option`／`Result`，一次改到底（含呼叫點）：

   | 函式 | 失敗模式 |
   |---|---|
   | `perm_wiring`／`signed_perm_wiring`／`perm_equiv` | 空置換（size 0 沒有 Bool 巢狀積的代表元）、號列長度不符、目標不是置換 |
   | `average_permutation_matrices` | 空輸入 |
   | `assignment_cost`／`tropical_optimal_assignments`／`tropical_matrix_symmetries` | 非方陣、元素超出安全範圍、枚舉超過上限 |
   | `exact_permanent_int64`／`exact_determinant_int64` | 同上 |
   | `qpoly_tropicalize_padic` | `p` 不是素數（回 `Result`，帶可讀訊息） |
   | `free_category_to_fincat` | 圖不是 DAG、合成路徑不在表內 |
   | `weighted_graph_report`／`semiring_graph_symmetry_projector` | 候選置換超過上限（**拒絕對不完整枚舉取平均**） |

   私有輔助函式（`adjacent_swap_wiring`／`not_at_wiring`／`path_index`）改回 `Option`，
   `bool_tuple_type` 改成全函式（`n ≤ 1` 一律 `Bool`）。

2. **golden 併入的套件 = 202 站點，逐條分類進 `ABORT-CONTRACTS.md`**：
   `cap` 1、`precondition` 151（公共 API）、`invariant` 50。分佈：
   `symlib` 98、`topos` 52、`scheme` 25、`semiring` 24、`(root)` 3、`cmd` 3。
   這 151 條是**下一輪的明確清單**（不是「以後再說」），並且新閘門 `tools/abort_audit.py --check`
   會擋住任何「新增站點」或「自家套件冒出 abort」。

**這一輪沒有假裝清空**：151 條公共 precondition 還在，只是現在有名有姓、有分類、有基線、有閘門。

#### 4.15.5 七項能力邊界：現況、瓶頸、下一步

| 邊界 | 現況（可重跑量測） | 真正的瓶頸 | 下一步 |
|---|---|---|---|
| **B1 Schema** | 層級約束＝整數差分約束系統；E1/E2 可行（最小解 `Type0=0,Type1=1,Type2=2`），E3 循環升格不可行＋正環見證 `B→A`；B1′ 序數層級＋嚴格 Lift 五條全過 | **Mahlo／超宇宙需要「對無界算子封閉」的公理**，而差分約束的解集對逐點 min 封閉 —— 兩者不同層級，此角「不可推遠，只能標定」（Palmgren 悖論：Mahlo＋自然消去規則 ⇒ 不一致） | 維持 B+C（B1′）；把「不可推遠」寫成定理而非註記 |
| **B2 DSystem／團** | 補圖為多部圖族認證最優 **10/10**；隨機 `G(12,0.5)` 認證 **0/10**（平均界差 7，誠實揭露）；`H²((ℤ/2)^d;F₂)` 基數 1/3/6/10 與 `d(d+1)/2` 全等 | **一般稠密圖上的秩界鬆**（`ω ≤ rank_F(I+Ā)` 只是上界）；非阿貝爾群（`S₃` 及以上）的阻礙不在線性 `H²` 內 | 秩界加一層 SDP／Lovász 型鬆弛；非阿貝爾阻礙改走群上同調的計算表示 |
| **B3 持久層** | 4 個紀元互鎖、36 條記錄、`VERIFY ok=true`、鏈頭 `7182d1b8…`；竄改 payload/seq 皆 `ok=false`；重複 append 不重寫 | **沒有檔案鎖與網路共識**：多寫者競態、分散式一致性不在這一層 | 檔案鎖（`flock`）＋ append 的 CAS；共識留給外部 |
| **B4 精確代數** | 譜表 n=6/8/10：精確係數 6/10/13 位十進位，`F_p` 平方自由全 true，ℝ 偏差 ~1e-10 全落在 ℚ 隔離區間內；二次互反 24/24；三環分工（`F_p` 螢幕→ℝ 定位→ℚ 認證） | **超越數不可表示**（`e, π ∉ Q̄`）；分裂／惰性判定必須避開判別式的素因子（壞素數可算出但不可消除） | 明確標出「壞素數表」作為 API 的一部分，而不是隱含假設 |
| **B5 BDD／SAT／立方** | Tseitin 12 頂點 15 邊：一致電荷 `sat` 解數 `2⁴=16`，奇電荷 UNSAT 附秩證書；ANF n=16：解集指示函數權重 3/9/27/81 `= 3^k`（原預測 `2^k` 被計算否決） | **ANF 最壞情況是稀疏性爆炸**（一般函數 ~`2^{n−1}`）；`n>20` 的一般最佳 ROBDD 排序 NP-hard；5 軸黑盒探針的信任邊界（CheckedDCube）未動 | 把 `CheckedDCube` 的信任邊界寫成可量測的假設；ANF 走分塊稀疏 |
| **B6 球面同倫** | 可見性表 7 模型 × 6 環（**ℚ-盲區 4/7**，R19 節印出）；UCT 28/28；Bockstein 抓到 2-/3-撓率；杯積分開 `T²` 與楔和；**第八輪：ℝP² 上 `dim H¹` 與 `dim(H¹⌣H¹)` 皆 ℚ/`F₂` = 0/1，分次交換在上鏈層只到差一個上邊界（48/48）** | **Hurewicz 只到 π₂**；同調＋杯積仍不足以決定同倫型；`π₄(S³)≅ℤ/2` 只被「表示並驗證」，未獲型別論證明 | 二次杯積／Steenrod 的 ℚ 版；用 Morse 區間族（第八輪）當「指標流」的獨立交叉驗證 |
| **B7 HOU／模組** | 有限載體合一由秩與 `p^{k−rank}` 完全決定（3 變元 mod 5/7 三例與暴力全等）；模組連結事件寫進雜湊鏈帳本，可重放可撤銷 | **Goldfarb 不變**：三階以上一般高階合一不可判定；熱載入止於程序／執行邊界 | 把「不可判定」的邊界畫在 API 上（哪些輸入直接拒絕） |

**七條的共同根因（G1：係數環）已經被治過一次**（R19 的 4/7 盲區就是它的量化），
剩下的瓶頸不再是同一個病：B1 是公理層級、B2 是鬆弛品質、B4 是壞素數、B5 是稀疏性、B6 是 Hurewicz 維度、
B7 是 Goldfarb。**這就是「瓶頸清晰」的意思 —— 六個不同的瓶頸，六條不同的路。**

#### 4.15.6 未完成待辦（P0 > P1 > P2，皆可執行）

**P0（下一次動工就做）**
1. **151 條公共 `precondition` 改成 `Result`**：清單已在 `ABORT-CONTRACTS.md` §2，按套件批量做
   （建議順序 `scheme` 25 → `topos` 52 → `symlib` 98，每次只動一個套件並跑 `moon test -p <pkg>`）。
2. **`cmd/main` 的 116 條逐條計時入帳**：把 `--time` 的輸出寫成 `logs/theorems.txt`，
   並對前 5 慢的條目加「快速模式」（例如 BDD 最佳順序的 `n ≤ 14` 版本），讓全跑從 178 秒降到 ~60 秒。

**P1（有明確路徑）**
3. B6：`π₄(S³)` 的 ℤ/2 從「表示並驗證」推到「型別論證明」（Brunerie 的 β 正規化，文獻已備）。
4. B2：秩界加 SDP／Lovász 鬆弛；非阿貝爾阻礙接上群上同調。
5. B4：把「壞素數表」變成 API 的可查詢部分。
6. B5：`CheckedDCube` 的 5 軸信任邊界寫成可量測假設。

**P2（結構性，收益大但動得深）**
7. `phase16_algebra.mbt` 與 `exact/algebra/phase14_algebra.mbt` 的職責重疊清理。
8. `symlib`／`topos` 的 `abort` 全面 `Result` 化（與 P0-1 同一件事，這裡標的是長期）。
9. `K_n (n ≥ 6)` 的 Stasheff 相干塔、Blakers–Massey 的完整 1-連通版本。

#### 4.15.7 閘門與帳（這一輪的終值）

```text
moon check --deny-warn              0 error / 0 warning
moon test                           192 / 192
moon run cmd/main                   116 / 116
moon run cmd/audit                  16 節／156 行／約 12 秒
moon run cmd/audit -- --full        340 行／約 3 分 48 秒
python3 tools/arch_check.py --graph ARCH_OK packages=41 federations=13 internal_edges=103
python3 tools/doc_audit.py --check  DOC_OK
python3 tools/dead_code.py --check  DEAD_CODE_OK（基線 0）
python3 tools/abort_audit.py --check ABORT_OK（自家 0／全樹 202 已分類）
sh ledger/audit.sh verify           VERIFY ok=true records=36
sh ledger/audit.sh head             7182d1b8…
```

樹 **267 檔／155,058 行**；跨套件同名定義 **30 → 21**（真重複 0）；自家未引用 `pub` **3 → 0**；
自家 `abort` **18 → 0**。

**判定：四類債（重複／死碼／崩潰式錯誤／文檔漂移）全部結清並上閘門；
apex 已無 `abort`、已無死碼；151 條 golden 公共 precondition 進入明確待辦（P0-1）。**

#### 4.15.8 這一輪學到的

- **去重是等價性測試**：兩份 `binom` 各自綠燈，合併才紅。把「同名」當成「同一件事」是合併後最容易犯的錯。
- **閘門要能表達「已清空」**：基線從 3 改成 0，才有辦法阻止回退；留著 3 的基線等於允許它變回 3。
- **「還清」有兩種**：一種是改完（apex 18→0），一種是**入帳**（其餘 202 條有名有姓、有分類、有閘門）。
  兩者都要有，但不要把第二種講成第一種。

---

## 附錄入口：逐符號登記

公共介面逐符號表已由本正文拆出並自動生成：

- [中文附錄](SPEC-APPENDIX.md)
- [English appendix](SPEC-APPENDIX.en.md)

生成與審計：

```text
moon info
python3 tools/audit_spec.py --write
python3 tools/audit_spec.py --check
```
#### 4.15.9 推送與冷啟動驗證

推送的內容就是 `merge/` 這一棵樹（**只含合成後的最新完全體**）：

| 項目 | 值 |
|---|---|
| 遠端 | `https://github.com/vv0101v01/mm0`（分支 `main`） |
| 提交 | `5d47031` |
| 檔案數 | **354**（267 個 `.mbt` ＋ 文檔／工具／帳本／日誌） |
| 樹大小 | 6.2 MB（工作目錄 268 MB —— 差額全在 `_build/`／`.mooncakes/`） |
| 排除 | `_build/`、`.mooncakes/`、`*.mbti`（`.gitignore` 明列） |
| 未推送 | `golden/`、`notebook/` 兩個原倉 —— 內容已在樹裡，再推就是重複的舊檔 |

**冷啟動驗證（不是「我這裡能跑」，是「 clone 下來能跑」）**：在空目錄 `git clone` 之後重跑

```text
moon check --deny-warn        131 tasks, 0 error / 0 warning
moon test                     192 / 192
doc_audit / arch_check        DOC_OK / ARCH_OK (41 / 13 / 103)
dead_code / abort_audit       DEAD_CODE_OK / ABORT_OK
ledger verify                 VERIFY ok=true records=36
```

全部重現。**推送的驗收標準是「別人 clone 後量到同樣的數字」，不是「我推上去了」。**

