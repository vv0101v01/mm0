///|
// The specification registry (規範形式與範疇化登記).
//
// Every type, operator, structure and specification in this project is
// registered here with three pieces of data:
//   canonical   — its normal / canonical form (規範形式): the chosen
//                 representative by which equality is decided;
//   categorical — its categorification (範疇化): the categorical structure
//                 it is an object / morphism / functor / law of;
//   decision    — how its governing equalities & predicates are decided.
// SPEC.md contains the same registry in document form, with an appendix
// listing every public symbol in the generated interface, grouped under
// these entries; tools/audit_spec.py checks the appendix is exhaustive.

///|
pub enum SpecKind {
  SpecType
  SpecOperator
  SpecStructure
  SpecTheorem
} derive(Debug, Eq)

///|
pub extend SpecKind with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend SpecKind with Eq::{not_equal, equal}

///|
pub struct SpecEntry {
  name : String
  kind : SpecKind
  symbols : Array[String]
  canonical : String
  categorical : String
  decision : String
}

///|
fn entry(
  name : String,
  kind : SpecKind,
  symbols : Array[String],
  canonical : String,
  categorical : String,
  decision : String,
) -> SpecEntry {
  SpecEntry::{ name, kind, symbols, canonical, categorical, decision, }
}

///|
pub fn spec_registry() -> Array[SpecEntry] {
  [
    entry(
      "複數標量",
      SpecType,
      ["Complex", "cx", "cx_add", "cx_mul", "cx_conj", "cx_approx_eq"],
      "(re, im) 有序對；相等以 eps 容差判定",
      "交換環 C 的元素；共軛是對合 (involution)",
      "分量比較",
    ),
    entry(
      "複向量與內積",
      SpecStructure,
      ["CVec", "vec_add", "vec_scale", "inner", "vec_orthogonal"],
      "分量表列；相等以 eps 逐分量判定",
      "有限維 Hilbert 空間 Hilb 的物件；內積給出對偶 v ↦ ⟨v, −⟩",
      "分量計算",
    ),
    entry(
      "複方陣與伴隨",
      SpecStructure,
      ["CMat", "mat_mul", "mat_adjoint", "mat_identity", "mat_vec", "outer2"],
      "列 (rows) 的表列",
      "Hilb 中的態射；伴隨 † 是 dagger 函子（反變、對合）",
      "矩陣運算",
    ),
    entry(
      "Hermitian／冪等／投影謂詞",
      SpecOperator,
      ["is_hermitian", "is_idempotent", "is_projector", "mat_commutes"],
      "P†=P 與 P²=P 兩方程的合取；規範形為 Σ vₖvₖ† (ONB 外積和)",
      "dagger 範疇中自伴冪等態射；其分裂即 Karoubi 包絡的物件",
      "eps 容差下矩陣方程",
    ),
    entry(
      "特徵空間分解",
      SpecTheorem,
      [
        "outer", "projector_from_orthonormal", "complement", "decompose", "in_image",
        "in_kernel", "eigenspace_well_formed", "prune_to_eigenspace", "pruning_is_retraction",
      ],
      "v 分解為 (Pv, (I−P)v) 的有序正交對",
      "冪等態射在 Hilb 中分裂：im(P) 是 retract，Cⁿ ≅ im(P) ⊕ ker(P) 是雙積 (biproduct)",
      "特徵值方程＋正交性＋tr(P) 整數性",
    ),
    entry(
      "可交換投影格",
      SpecTheorem,
      ["commuting_product", "commuting_projectors_compatible"],
      "交換族的乘積 PQ（交特徵空間的投影）",
      "投影偏序集 (P ≤ Q ⇔ QP=P) 中交換者的下確界 (meet)",
      "PQ=QP 方程",
    ),
    entry(
      "Karoubi 包絡",
      SpecStructure,
      ["karoubi_morphism", "karoubi_wrap", "karoubi_id", "karoubi_comp"],
      "物件：Hermitian 冪等 P；態射：被 (Q,P) 夾緊的矩陣 QAP=A",
      "冪等分裂完備化；恒等態射是 P 本身；† 給出 dagger 結構",
      "QAP=A 方程＋合成律抽樣驗證",
    ),
    entry(
      "Cubical 區間",
      SpecType,
      ["Dim", "eval_dim", "eval_dim_bool", "interval_laws_hold"],
      "De Morgan 代數表達式；端點語義化為布林公式",
      "區間物件 I 是 De Morgan 代數（有界分配格＋對合 ¬）",
      "端點求值＋dim_simplify 重寫",
    ),
    entry(
      "面公式（餘纖維）",
      SpecType,
      [
        "Face", "face_holds", "face_var0", "face_var1", "face_sat", "face_le", "face_eq_mod",
      ],
      "ROBDD（見下）",
      "餘纖維在面格中：子物件分類子的 cofibration 部分",
      "BDD 符號判定",
    ),
    entry(
      "面公式的 ROBDD 規範形式",
      SpecStructure,
      [
        "Bdd", "bdd_of_face", "bdd_not", "bdd_and", "bdd_or", "bdd_sat_face", "bdd_face_le",
        "bdd_face_eq", "face_witness", "dim_simplify", "face_simplify", "face_vars",
      ],
      "變量遞增序、等子節點消去的約化有序 BDD；結構相等即商相等",
      "自由有界分配格在生成元 Dim 變量上的規範代表；∧/∨ 即 BDD apply",
      "Shannon 展開＋常數簡化剪枝",
    ),
    entry(
      "面偏序範疇",
      SpecStructure,
      [
        "face_meet_universal", "face_join_universal", "check_face_poset_category",
      ],
      "物件為 BDD 等價類",
      "偏序範疇：∧=積，∨=餘積，⊤ 終物件，⊥ 始物件；態射存在性即 ≤",
      "bdd_face_le",
    ),
    entry(
      "系統（偏元素）與剪枝",
      SpecStructure,
      [
        "VecBranch", "VecSystem", "system_lookup", "system_compatible", "prune_system",
        "system_union", "union_commutes_mod", "system_extend_top",
      ],
      "符號規範形：以有效區域 BDD 分割端點立方體的值類別（system_normal_form）",
      "面上 presheaf 的偏元素；聯集是餘積式拼接，商由區域分割給出",
      "BDD 區域代數",
    ),
    entry(
      "系統符號規範形",
      SpecOperator,
      [
        "SymRegion", "SystemNF", "system_normal_form", "system_eq_mod_sym", "system_domain_bdd",
      ],
      "不交 BDD 區域＋值標籤，按值字典序排列，另加未定義區域",
      "偏元素到面格切片範疇中的像分解 (image factorisation)",
      "有效區域 φᵢ ∧ ¬(前覆蓋) 以 bdd_and/bdd_not/bdd_or 計算",
    ),
    entry(
      "立方體與路徑",
      SpecType,
      [
        "Cube", "cube_const", "path_line", "path_refl", "path_sym", "restrict_face",
        "degenerate_cube", "cube_ext_eq", "face_maps_commute",
      ],
      "函數 Iⁿ→Cᵐ 本身（語義立方體）；路徑範形為直線 path_line",
      "立方體範疇 □ 上的 cubical set 在 Cᵐ 中的實現；面/退化生成 □ 的態射",
      "樣本網格外延相等",
    ),
    entry(
      "Kan 填充與 comp（向量／特徵空間）",
      SpecOperator,
      [
        "open_box_wf", "square_fill", "kan_comp_path", "path_trans", "prune_cube",
        "kan_fill_eigenspace", "kan_comp_eigenspace", "eigenspace_kan_sound", "pruning_repairs_filler",
      ],
      "F(i,j)=b(i)+(1−i)(l(j)−b(0))+i(r(j)−b(1))，特徵空間版繼以 P 剪枝",
      "retract 的 Kan 纖維化結構：填充提升性質在 retraction 下封閉；comp 是帽子面",
      "邊界方程於樣本網格驗證",
    ),
    entry(
      "項語法與未型別 NbE",
      SpecStructure,
      [
        "Term", "Neutral", "Value", "eval", "quote", "nf", "def_eq", "nbe_single_valued",
        "coe_rules_definitional",
      ],
      "βπ-正規形（quote∘eval）",
      "λ× 句法範疇到指稱語義函子的單位/餘單位式分解；正規形是商的代表",
      "正規形結構相等",
    ),
    entry(
      "HOAS語法",
      SpecType,
      ["HTm", "happ", "term_to_hoas", "hoas_to_term", "hoas_roundtrip_term"],
      "reify 到 de Bruijn 正規形",
      "高階抽象語法作為函子範疇中的綁定；與一階語法互逆（模定義相等）即範疇等價",
      "reify/reflect 往返與 nf 比較",
    ),
    entry(
      "型別導向 NbE 與 η",
      SpecStructure,
      [
        "LTy", "TValue", "TNeutral", "ty_check", "ty_infer", "eval_check_t", "eval_infer_t",
        "quote_eta", "nf_eta", "def_eq_eta", "eta_single_valued_on",
      ],
      "η-長 βπ-正規形：函數 η 展開 λx.f x，積 η 展開 (fst p,snd p)，單位塌陷 ()",
      "自由笛卡兒閉範疇 (自由 CCC) 中態射的規範代表；quote 是按型別的反思 (reflection)",
      "雙向型別檢查＋按型別 quote＋結構比較",
    ),
    entry(
      "句法笛卡兒閉範疇",
      SpecStructure,
      [
        "tm_shift", "tm_comp_closed", "tm_comp_at", "tm_id_at", "check_syntactic_category",
      ],
      "箭頭：帶註記閉項，範形為其 nf_eta",
      "物件 LTy，態射為項模 βπη；積與指數由 λ/配對給出萬有性",
      "def_eq_eta 判定結合律／恒等律／逆律",
    ),
    entry(
      "Finite universe 型別與值",
      SpecType,
      ["Ty", "PVal", "elems_of", "in_ty", "leaves_of_ty", "flatten_pval"],
      "型別樹的葉序 (leaf sequence)；值樹展平為葉值列",
      "有限集合範疇中的物件，由 Bool/Unit 以積生成",
      "樹遞迴",
    ),
    entry(
      "Wiring 符號等價",
      SpecStructure,
      [
        "LeafKind", "LeafMap", "Wiring", "wiring_id", "wiring_not", "wiring_swap",
        "wiring_prod", "wiring_comp", "wiring_inv", "wiring_assoc", "wiring_left_unitor",
        "wiring_right_unitor", "wiring_wf", "wiring_eq", "wiring_apply",
      ],
      "帶號置換：每輸出葉的 (源索引, 否定旗)；Unit 輸出規範為 (−1,false)",
      "自由對稱冪冪範疇在 Bool(帶對合)/Unit 生成元上的態射；⊗ 與換位子 (braiding)",
      "置換性判定 O(#葉)；合成＝替換＋XOR；相等＝結構相等",
    ),
    entry(
      "同構／等價／ua／coe",
      SpecStructure,
      [
        "Iso", "Equiv", "UPath", "iso_of_wiring", "equiv_of_wiring", "iso_to_equiv",
        "equiv_prod", "equiv_comp", "equiv_inv", "equiv_wf", "equiv_ext_eq", "ua",
        "iso_to_path", "coe_upath", "coe_computes", "upath_eq", "swap_naturality",
      ],
      "wiring 規範形；coe 按端點分情況計算為 equivFun/equivInv/id",
      "ua 是 (A≃B)≃(A=B) 在此有限宇宙的迭代；swap 自然性方塊是交換圖",
      "wiring_eq 與 w;w⁻¹=id 的 wiring 等式",
    ),
    entry(
      "PathP 與離散路徑、J",
      SpecStructure,
      [
        "PathPVal", "pathp_canonical", "pathp_wf", "pathp_prod", "pathp_fst", "pathp_snd",
        "pathp_prod_exchange_roundtrip", "DiscPath", "refl_path", "disc_path_sym",
        "Family", "j_elim_disc", "j_roundtrip",
      ],
      "PathP 規範元：遠端 = coe 之像；離散路徑規範形為常值",
      "路徑物件與依賴路徑 (PathP)；J 是常值線上 coe 的恒等性陳述",
      "端點型別＋點值檢驗",
    ),
    entry(
      "有限 Glue（形成／可靠）",
      SpecStructure,
      [
        "GlueData", "GlueElem", "glue_wf", "make_glue", "unglue", "glue_restrict",
        "glue_from_base", "glue_sound",
      ],
      "(partial, base) 對；由 base 造的規範元 glue_from_base",
      "Glue 是沿等價把偏型別 T 黏到 A 的 (餘)極限式構造；unglue 是投影到 A 的纖維化",
      "φ 的 BDD 可滿足性＋相容方程",
    ),
    entry(
      "一般 Glue comp（有限線）",
      SpecOperator,
      [
        "GlueLineFinite", "glue_data_at0", "glue_data_at1", "glue_line_coherent",
        "glue_comp_finite", "glue_comp_finite_correct",
      ],
      "輸出 base 是校正後的 e₁(t₁)（當 φ₁ 成立）",
      "等價線 = 箭頭範疇 (arrow category) 中的態射；comp 是箭頭範疇中沿線的合成",
      "自然性方塊以 wiring_eq 判定；拒絕不相干線數據",
    ),
    entry(
      "特徵子空間線上的 Glue comp",
      SpecOperator,
      [
        "SubLine", "LinEquivLine", "GlueLineVec", "VecBox", "GlueCompVecResult",
        "prune_cube_subline", "fill_subline", "glue_box_compatible", "glue_comp_vec",
        "glue_comp_vec_sound",
      ],
      "校正方塊 (i,k)↦(1−k)·a_cap(i)+k·U(1)(t_cap(i)) 的 k=1 邊",
      "retract 線族上的 Kan 填充；校正即 A(1) 中的 hcomp 提升",
      "邊界/帽子/落點方程於網格驗證",
    ),
    entry(
      "依賴型別 NbE（Π/Σ/宇宙）",
      SpecStructure,
      [
        "DTerm", "DValue", "DNeutral", "DInfer", "d_infer", "d_check", "d_as_type",
        "conv_at", "conv_ty", "quote_at", "quote_ty", "dep_check_closed", "dep_nf_closed",
        "dep_type_of_closed", "lty_to_dterm", "check_dep_all",
      ],
      "按型別 quote 的 η 長依賴正規形；Π/Σ 的第二分量是語義閉包族，宇宙為累積層級 Typeᵢ:Typeᵢ₊₁",
      "帶族範疇 (categories with families) 的句法模型：脈絡延伸、依賴代入是閉包施用；單純片斷嵌入為非依賴 Π/Σ",
      "雙向 elaboration ＋ 型別導向 conversion；相等為範形結構相等",
    ),
    entry(
      "依賴 Kan 線 coe/comp",
      SpecStructure,
      [
        "DLine", "dline_at", "dcoe", "dfill", "dcomp", "dline_const", "dline_pi",
        "dline_sigma", "dline_univ", "dline_of_lty", "dline_of_ty", "dline_of_upath",
        "check_kan_all_types",
      ],
      "DLine{at, coe_fn, fill_fn}；Π 的 coe 在定義域反向、Σ 的第二分量沿第一分量路徑傳輸；comp=fill(1)",
      "型別即 Kan 纖維化結構；依賴族呈現為 (A 中的路徑)→DLine；連同特徵子空間與 Glue 覆蓋全專案型別族",
      "對型別構造子遞迴求值；coe(r,r) 由 wrapper 定義地恆等",
    ),
    entry(
      "精確符號代數",
      SpecStructure,
      [
        "Rat", "Poly", "PolyTerm", "SymFrac", "SymC", "SymMat", "UPoly", "poly_add",
        "poly_mul", "frac_eq", "sym_det", "charpoly_sym", "sym_projector_rank_one",
      ],
      "Q 上多變量多項式規範形（合併、去零、字典序）；分式以交叉相乘判定相等；複量為實符號有序對",
      "多項式戒與其分式體提供矩陣的代數語義；特徵多項式是 det(XI−A) 的精確展開",
      "多項式恆等（無 eps、無抽樣）",
    ),
    entry(
      "譜投影與仿射唯一填充的符號恆等",
      SpecTheorem,
      [
        "RPoly", "RPolyDiv", "spectral_q", "spectral_minpoly", "spectral_denominator",
        "spectral_projector_sym", "rpoly_divisible_by", "sym_square_fill", "sym_bilinear_from_corners",
        "sym_bilinear_ansatz", "check_symbolic_algebra_all",
      ],
      "譜投影 Pₖ=qₖ(A)/qₖ(λₖ)；仿射填充是四角的雙線性插值，繫數由角值唯一解出",
      "譜分解給出單位分解 ΣPₖ=I 與 ΣλₖPₖ=A；雙線性插值是張量積意義下兩個仿射方向的唯一黏合",
      "首一多項式整除（模最小多項式）及在座標原子 i,j 上的多項式恆等",
    ),
    entry(
      "立方 AST、PathP 與維度 NbE",
      SpecStructure,
      [
        "DTubeTerm", "d_tube", "DPathParts", "DGlueParts", "deval_dim", "eval_dim_expr",
        "dim_quote", "face_eval_env", "face_quote", "dapp_dim", "eval_tube_terms",
        "quote_tube_branches", "dep_def_eq_closed", "check_ast_paths",
      ],
      "同一 DTerm 以分離的項/維度 de Bruijn 索引表示型別線、tube 系統與路徑；範形由帶維度層級的 quote 給出，HIT 點在端點正規化",
      "帶區間脈絡的 cubical CwF 句法模型：PathP 是沿 I 的依賴路徑物件，維度代換即 denv 求值；Glue 值以 (單分支 raw 或多分支 DVPartial partial, base) 對表示",
      "雙向 elaboration；Dim/Face 以 dim_simplify、face_simplify 與 ROBDD 語義謂詞判定",
    ),
    entry(
      "AST Kan 運算 comp/hcomp/hfill/coe",
      SpecOperator,
      [
        "comp_value", "hcomp_value", "fill_value", "hfill_value", "coe_value", "comp_pi_value",
        "comp_sigma_value", "comp_path_value", "comp_glue_value", "comp_univ_value",
        "hcomp_univ_value", "check_ast_kan_terms", "check_ast_kan_types",
      ],
      "在一般維度取樣型別線後按頭構造子派遣：Π 沿反向定義域填充、Σ 沿第一分量填充、PathP 加端點分支、Universe 產生保留完整 DSystem 的 Glue；coe/fill 由 comp 的線段限制得到",
      "每個型別構造子保存 Kan 纖維化結構；系統分支是餘纖維上的偏路徑，形式 DNComp/DNHComp 是未化簡合成的中性見證",
      "系統以 base 相容與分支重疊相容檢查；頂面分支取帽、底面分支消去；其餘由型別遞迴或形式中性項判定",
    ),
    entry(
      "資料型別與高階歸納型別消去",
      SpecStructure,
      [
        "d_nat_lit", "dv_nat_lit", "eval_bool_elim", "eval_nat_elim", "eval_list_elim",
        "circle_point", "torus_point", "eval_circle_elim", "eval_torus_elim", "comp_bool_value",
        "comp_nat_value", "comp_list_value", "comp_circle_value", "comp_torus_value",
        "check_ast_data", "check_ast_hits",
      ],
      "Nat/List 以建構子遞迴；Circle 點為 loop@r（端點為 base），Torus 點為 square@(i,j) 且對邊等同；非平凡 HIT 系統保留形式 hcomp 點",
      "Nat/List 是依賴消去的初始代數；Circle/Torus 是帶路徑/方塊生成元的 HIT，消去子是 motive 的截面並與形式 composition 交換",
      "構造子模式遞迴、HIT 點座標的 Dim 語義相等，以及在 motive 中 composition 的消去交換律",
    ),
    entry(
      "持久環境、惰性與語義快取",
      SpecStructure,
      [
        "DEnv", "DDimEnv", "DThunk", "denv_cons", "ddim_cons", "denv_extend", "lazy_value",
        "force_value", "lazy_deval", "memo_dim_line", "memo_family", "check_persistent_env_lazy_cache",
      ],
      "帶長度的持久連結串列：cons 以 O(1) 共享尾部，陣列版環境只在公開邊界轉換一次；DVThunk 強制後保存值且最多計算一次；維度線以簡化 Dim 鍵、型別族以引文項鍵 memoize",
      "CwF 的脈絡延伸與弱化由共享環境尾部實現；惰性語義值是 call-by-need 值，快取是外延函數圖的有限延伸而不改變其指稱",
      "de Bruijn 索引查找、force_count 觀察與穩定 Debug 快取鍵相等",
    ),
    entry(
      "依賴語義系統與 partial 值",
      SpecStructure,
      [
        "DTubeBranch", "tube_branch", "DSystem", "dsystem_of", "dsystem_canonical",
        "DFaceTerm", "DPartialValue", "partial_normal_form", "DSystemNF", "partial_eq_at",
        "glue_partial_values", "glue_store_partial", "check_phase5_semantic_systems",
      ],
      "DSystem 先去底面並簡化面；沿型別線的規範形把可轉換 body 以面聯集合併並按引文排序。partial 值的範形是 BDD 有效區域值類別加未定義區域；DVGlue 保存全部 partial type 分支",
      "面格切片中的偏元素：系統是餘纖維上的偏路徑/偏元素，多分支 Glue 是 partial type 系統與 base type 的配對極限表示",
      "有效區域以 BDD and/not/or 計算；分支合併與排序以型別導向轉換及引文鍵判定",
    ),
    entry(
      "通用歸納族 schema",
      SpecStructure,
      [
        "DArgKind", "DTelescopeEntry", "DConstructorArg", "DConstructorSpec", "DInductiveSpec",
        "dinductive_spec", "inductive_schema_validate", "inductive_case_type", "eval_inductive_elim",
        "infer_inductive_elim", "comp_inductive_value", "nat_schema", "vec_schema",
        "w_schema", "check_generated_inductive_schemas",
      ],
      "有限描述子：參數/索引 telescopes、外部/直接遞迴/函數遞迴引數與結果索引；值範形為引文的 DIntro， 中性消去按生成 motive/case 型別引文",
      "嚴格正性依賴多項式函子的初始代數；依賴消去是 motive 的截面，Kan comp 沿先前引數 filler 逐引數遞迴，函數遞迴引數以 Π comp 處理",
      "描述子結構相等；telescope 與引數/索引由雙向檢查驗證；外部型別與函數定義域以同名族掃描拒絕非嚴格正性出現",
    ),
    entry(
      "通用 HIT schema",
      SpecStructure,
      [
        "DHitFaceExpr", "DHitCellSpec", "DHitSpec", "dhit_spec", "hit_schema_validate",
        "hit_cell_value", "hit_case_type", "eval_hit_elim", "infer_hit_elim", "comp_hit_value",
        "circle_schema", "segment_schema", "torus_schema", "check_generated_hit_schemas",
      ],
      "0/1/2 維 cells：DVHitCell 的維度先簡化，任一端點即代入對應 face expression 遞迴化簡；消去 case 型別為逐維巢狀 PathP，端點是較低維 face 的消去值",
      "帶 face 映射的胞腔高階初始代數；依賴消去把 point/path/square cells 送到 motive 的截面與其路徑/方塊，comp 只在同 cell 同維度時逐引數計算，其餘保留形式合成",
      "face 的目標 cell、引數型別與結果索引由檢查器驗證；2-cell 以兩種維度化簡次序在四角轉換相等驗證相容性",
    ),
    entry(
      "Schema 擴展：函子正性、互歸納、商與宇宙多態",
      SpecStructure,
      [
        "DPositiveFunctor", "DConstructorConstraint", "DMutualFamily", "DLevelExpr",
        "dpositivity_report", "positive_functor_map", "compile_mutual_inductive",
        "instantiate_inductive_level_scheme", "quotient_schema", "decode_term", "check_schema_extensions",
      ],
      "遞迴引數以完整型別或 DPositiveFunctor 解碼，IH 依函子結構生成；互歸納編譯為 Sum-indexed 單一 schema；商是帶等式 cell 的 HIT，任意有限維 cells 逐維以 face expression 化簡",
      "正性函子與互歸納族的初始代數、Tarski 解碼的歸納—遞迴對，以及宇宙層級指派下的 schema 族",
      "別名展開後以極性遞迴判定嚴格正性；構造子 Path 約束、層級 scheme 求值與多維 face 相干性均由檢查器驗證",
    ),
    entry(
      "原始 DSystem 相容性與 first-match 範形",
      SpecStructure,
      [
        "DSystemCompatibility", "DTubeNF", "conv_at_under_face", "dsystem_checked",
        "dsystem_compatibility_report", "dsystem_first_match_normal_form", "check_dsystem_compatibility",
        "check_dsystem_first_match_nf",
      ],
      "相容原始系統經 checked 入口化為通常的型別導向 DSystem 範形；任意 first-match 系統化為互不交疊的有效區域與值路徑類別",
      "面切片中的原始偏元素到 composition 偏元素的相容性反射；first-match 是優先序區域分解",
      "將面轉成 BDD cubes 並在局部維度脈絡下逐 cube 轉換比較 base 與兩兩分支，首個衝突精確回報",
    ),
    entry(
      "AST 一等 Equiv、ua 與 GlueEquiv",
      SpecStructure,
      [
        "DEquivParts", "DGlueEquivParts", "as_equiv_type", "mk_equiv_term", "infer_ua",
        "comp_equiv_value", "comp_glue_equiv_value", "check_equiv_ast",
      ],
      "Equiv 值由正向函數、反向函數與 section/retraction Path 證明組成；GlueEquiv 分支保存完整 partial type 與其指向 base 的一等等價",
      "AST 內帶同倫逆的等價範疇；ua 把等價送入宇宙路徑，GlueEquiv 是沿偏等價系統黏合的型別",
      "雙向檢查 Equiv 四分量，conversion/quote 遞迴至各分量；沿 ua 的 coe 直接計算為 fwd 或 bwd",
    ),
    entry(
      "受檢查型別線與 schema 註冊快取",
      SpecStructure,
      [
        "DCheckedTypeLine", "DSchemaRegistry", "DInductivePlan", "checked_type_line",
        "checked_comp_value", "schema_registry_register_inductive", "schema_registry_validate_hit",
        "default_schema_registry", "check_phase6_infrastructure",
      ],
      "受檢查線保存已驗證的開放型別 body 與環境而不保存任意宿主函數；schema 以穩定鍵 intern 為 plan，telescope 保存完整前綴鏈",
      "由句法 body 表示的型別線與維度代換自然交換；註冊表是 schema elaboration 函數的有限共享圖",
      "在新鮮維度下檢查線 body 的宇宙層級；registry 以鍵命中驗證及語義 telescope，計數器使重用可觀察",
    ),
    entry(
      "精確單變量多項式與有理矩陣",
      SpecStructure,
      [
        "QPoly", "QMat", "QRref", "qpoly_normalize", "qpoly_gcd", "qpoly_extgcd",
        "qpoly_factor_rational_roots", "qmat_charpoly", "qmat_minimal_polynomial",
        "qmat_inverse",
      ],
      "QPoly 為去除尾零的升冪有理係數列，QMat 為有理列之列，線性子空間以 RREF 自由變量基底表示",
      "歐氏環 Q[x] 與有限維有理線性範疇；矩陣多項式求值給出 Q[x] 模結構",
      "primitive pseudo-remainder gcd/extgcd、Yun squarefree 分解、有理根枚舉、Faddeev–LeVerrier 與精確 RREF",
    ),
    entry(
      "代數擴張、廣義特徵空間與 Jordan 理論",
      SpecStructure,
      [
        "QuadNum", "AlgNum", "AlgMat", "QGeneralizedEigenspace", "QJordanDecomposition",
        "quad_denested_sqrt", "alg_rebase_to_minimal", "qmat_generalized_projector",
        "qmat_Jordan_decomposition", "algmat_Jordan_decomposition", "check_algebraic_extensions_and_Jordan",
      ],
      "QuadNum 為 a+b√d 的無平方因數範式，AlgNum 為模極小多項式的餘式；Jordan 分解由廣義核鏈的塊大小與鏈基底給出",
      "有限代數擴張體上的線性代數；主分解來自互質多項式因子的單位分解，Jordan 型刻畫分裂時的相似類",
      "以特徵多項式重數、(A−λI) 冪次 nullity 與鏈提升精確計算；Q 上未分裂部分保留殘餘因子並可在 AlgMat 擴張上處理",
    ),
    entry(
      "BDD DAG、預算搜尋與認證數值影子",
      SpecStructure,
      [
        "BddManager", "FaceDecision", "FaceSatDecision", "bdd_dag_of_face_best",
        "face_eq_within_budget", "face_sat_dpll", "QuadC", "CertMat", "CertPath",
        "ProjectorCertificate", "certify_numeric_projector", "check_bdd_and_certified_numeric",
      ],
      "面在 manager 中以 hash-consed root 表示，大小為 reachable DAG 節點；數值矩陣的精確影子由 QuadC 矩陣與多項式係數立方體給出",
      "布林函數的共享 ROBDD 圖與精確複二次矩陣代數；Double 層是影子的近似觀察而非等式來源",
      "同 manager root 相等判定面等式，節點預算或 DPLL 處理不可行建構；投影與填充恆等以精確結構相等驗證，浮點只量偏差與 residual",
    ),
    entry(
      "容器函子巢狀遞迴、互歸納與歸納遞迴宣告面",
      SpecStructure,
      [
        "dfunctor_container", "container_tree_schema", "check_container_functor_tree",
        "check_mutual_inductives", "check_tarski_induction_recursion",
      ],
      "DFunctorContainer(shape, positions, index) 表示 Sigma(s:Shape), Positions(s)->X(index s p)，與既有正性函子、互歸納編譯和 DDecode 共用生成器",
      "任意有限依賴多項式/container 函子的初始代數；互歸納是標籤索引和，歸納—遞迴是碼族與解碼的同時初始結構",
      "形狀與位置型別不得提及本族，遞迴索引在 shape/position 兩綁定子下檢查；IH 是對所有 positions 的 Pi 型",
    ),
    entry(
      "懸掛球面與 S³",
      SpecStructure,
      [
        "suspension_schema", "sphere_schema", "sphere2_schema", "sphere3_schema",
        "sphere3_meridian_term", "sphere3_meridian_value", "check_sphere3",
      ],
      "Susp(X) 由 north、south 與每點一條 meridian 生成；S² 與 S³ 分別是圓的一次與兩次懸掛，端點在 hit_cell_value 中化簡",
      "把 X×I 的上下端各塌縮成一點的 HIT；消去子由南北兩點的值和所有 meridian 上的依賴路徑組成",
      "基底 HIT 須無索引且先驗證；端點、恆等消去與固定 meridian 的 hcomp 以轉換與引文範形判定",
    ),
    entry(
      "Jacobi 酉旋轉的符號區間證書",
      SpecStructure,
      [
        "RatInterval", "CInterval", "QCpxMat", "QCIntervalMat", "JacobiCoefficients",
        "JacobiRotationCertificate", "JacobiCertificate", "jacobi_coefficients",
        "jacobi_unitary_interval", "jacobi_interval_eigen", "jacobi_certificate_sound",
        "check_Jacobi_interval",
      ],
      "精確 Hermitian 點矩陣的複矩形區間包絡；每次旋轉保存 before/after、累積變換與有理 c/s/phase 包絡，矩陣以 dyadic 外向捨入保持有界分母",
      "酉相似變換在區間矩陣格上的包含單調提升；最終 Hermitian 包絡的 Gershgorin 圓盤依重疊分簇並計重數",
      "sqrt 以整數二分和精確平方比較包絡；逐旋轉重算係數包含、J†J-I 含零、after 包 J†AJ 與 transform 包 VJ",
    ),
    entry(
      "Miller pattern 高階合一與雙向 elaborator",
      SpecStructure,
      [
        "UTerm", "Unifier", "STerm", "Elaborator", "ElabResult", "hou_fresh_meta",
        "hou_unify", "hou_semantic_optimize", "elab_infer", "elab_check", "elab_result_to_dterm",
        "check_hou_elaborator",
      ],
      "表面命名項解析為 de Bruijn UTerm；metavariable 以作用域變量的 pattern spine 表示，zonked 核心經 beta/投影/Nat 語義簡化後譯至 DTerm",
      "Miller pattern 是高階合一的可判定片斷；雙向 elaboration 將隱含型別引數與 dependent motive 化為同一類 flex-rigid 問題",
      "WHNF、eta、rigid 分解、不同綁定變量 spine 的抽象、occurs/scope 檢查；未解 metavariable 不得進入 DTerm，結果再由依賴檢查器驗收",
    ),
    entry(
      "參數化模組、import/open 與名字空間",
      SpecStructure,
      [
        "ModuleDef", "ModuleImport", "ModuleDecl", "ModuleEnv", "ModuleSignature",
        "ModuleInstance", "module_signature", "module_validate", "module_resolve",
        "module_ref", "module_instantiate", "module_instance_find", "check_module_system",
      ],
      "模組是參數、imports、本地宣告組成的 telescope；bindings 把限定名、別名與 opened/renamed 名映射到 telescope ordinal，實例是同時代換的閉合宣告列",
      "參數化模組是函子，import 是遞迴函子套用後內聯，open 是名字投影而非複製宣告；opaque export 在邊界後成為中性常數",
      "模組循環與重複路徑拒絕，參數引數與每條映射宣告以 d_check 驗證，only/hiding/rename 的歧義名字拒絕，閉合實例逐條 dep_check",
    ),
    entry(
      "立方體演算法：transport、路徑代數與 Kan box",
      SpecStructure,
      [
        "KanBox", "kan_box", "kan_box_fill", "kan_box_comp", "kan_box_pathp", "transport_value",
        "transport_back_value", "transport_checked_line_value", "transport_filler_value",
        "transport_pathp_value", "dpath_refl_value", "dpath_sym_value", "dpath_segment_value",
        "dpath_prefix_value", "dpath_trans_square_value", "dpath_trans_value", "dpath_cong_value",
        "dpath_funext_value", "subst_value", "subst_pathp_value", "dtransport_term",
        "dpath_trans_term", "dfunext_term", "check_cubical_algorithms",
      ],
      "transport 是沿型別線的 coe，filler 是其 PathP；路徑傳遞是 hcomp 方塊的頂邊，funext 與 subst 分別是逐點路徑與族線 coe，KanBox 把開盒的線、系統與 base 打包",
      "cubical CwF 中由 Kan 纖維化結構生成的路徑物件運算：反演、串接、函子性與依賴代入",
      "全部派遣至核心 coe/comp/fill 並以型別導向轉換驗證端點；閉項 builders 再由 dep_check_closed 驗收",
    ),
    entry(
      "計算性單值性（univalence）",
      SpecStructure,
      [
        "UniversePath", "upath_to_equiv", "upath_refl", "upath_sym", "upath_trans",
        "finite_transport", "transport_roundtrip_path_value", "path_to_equiv_value",
        "equiv_to_universe_path_value", "ua_transport_value", "ua_beta_path_value",
        "ua_beta_back_path_value", "univalence_retr_path_value", "univalence_sect_square_value",
        "univalence_equiv_value", "universe_path_of_checked_line", "universe_path_of_ua_term_closed",
        "universe_path_to_equiv_value", "universe_path_normal_form", "universe_path_transport_conv",
        "path_to_equiv_term", "ua_map_term", "path_to_equiv_map_term", "check_finite_univalence",
        "check_univalence",
      ],
      "有限宇宙的路徑以 wiring 等價為範形；依賴 AST 的宇宙路徑以受檢查型別線表示，pathToEquiv 取其 coe 等價，ua 取 Glue 線，uaβ 由 transport filler unglue 得到，往返分別由 Equiv 中的同倫與二維 Glue 方塊見證",
      "宇宙的路徑範疇與等價範疇之間的等價 (Equiv A B) ≃ Path U A B；Glue 是沿等價的黏合，transport 是其 coe 函子",
      "有限側以 wiring 相等判定；AST 側以 coe/comp 計算、型別導向轉換驗證往返端點與方塊四邊，閉項 pathToEquiv 以 DMkEquiv 的 fill/coe 證明由依賴檢查器驗收",
    ),
    entry(
      "完備精確代數：因式分解、根隔離、分裂域與去巢",
      SpecStructure,
      [
        "QPolyCompleteFactorization", "qpoly_factor_complete", "qpoly_isolate_complex_roots",
        "complex_root_isolations_are_certified", "qpoly_splitting_field", "splitting_field_is_certified",
        "radical_simplify", "check_Jacobi_arbitrary_precision",
      ],
      "Rat 以 BigInt 正規化；Q[x] 化為不可約因式重數列；實根以 Sturm 隔離區間、複根以兩兩不交 Rouché 圓盤表示；分裂域以逐次 AlgNum 塔與全部分解表示；Jacobi 端點為任意精度有理數",
      "Q[x] 的唯一因式分解與代數閉包中的根多重集；分裂域是使多項式在擴張塔上完全分裂的有限擴張，根式去巢是擴張中 nth-root 的見證搜尋",
      "Kronecker 預算語義明示；複根在快路徑不足時以 Cauchy 正方形、Taylor 排除與 Rouché 細分補至次數；所有證書以精確多項式運算重驗",
    ),
    entry(
      "一等宇宙多態與同時宣告 schema",
      SpecStructure,
      [
        "DLevelDecl", "dterm_instantiate_levels", "DTypeOperatorDecl", "extract_positive_functor",
        "DNestedIterDecl", "compile_nested_iter_decl", "DMutualDecl", "mutual_decl_elaborate",
        "DSimultaneousIRSpec", "eval_simultaneous_ir", "check_hit_moving_dimension_lift",
      ],
      "層級宣告以 binders＋實例化層級向量表示；型別算子先展開透明定義再抽取正性函子；Bush 類巢狀型由迭代參數前進編譯；互歸納與同時 IR 以聯合規格及其生成消去／求值表示",
      "宇宙多態是層級指派上的 scheme；非均勻巢狀資料是參數迭代的初始代數族，互歸納是向量函子的聯合初始代數，同時 IR 是碼與同步函數的同時初始結構",
      "未實例化 DUnivLevel 在檢查時拒絕；正性報告記錄算子展開與極性；實例化、生成檢查與移動維度 HIT cell 以依賴轉換驗證",
    ),
    entry(
      "原始 DSystem 的剪枝、合意區域與受限修復",
      SpecOperator,
      [
        "conv_at_under_face_report", "tube_paths_conv_under_face", "face_agreement_region",
        "dsystem_repair_to_base", "check_dsystem_repair_phase9",
      ],
      "面下轉換只保留由 BDD 證明的合意子區域；修復輸出不交化後與 base 在維度端點相合的分支及被移除區域，無法修復者保留衝突報告",
      "partial element 在面格切片中的限制與像分解；agreement region 是兩分支在 cofibration 上的相等化子面",
      "以 BDD 區域剪枝取代立方體枚舉；端點與重疊處用型別導向轉換檢查，修復只刪去可證不相合區域",
    ),
    entry(
      "Adjoint 等價資料、contractible fiber 類型與命題截斷",
      SpecStructure,
      [
        "DAdjointEquivParts", "equiv_triangle_type", "adjoint_equiv_type_term", "equiv_improved_sect_value",
        "equiv_fiber_center_value", "singleton_contraction_value", "prop_trunc_schema",
        "trunc_type_term", "check_propositional_truncation",
      ],
      "adjoint 資料是在 quasi-inverse Equiv 上加三角形 Path(Path) 分量；improved counit 以 ε(fgy)⁻¹∙f(η(gy))∙εy 取代 section；命題截斷以 point 與任意兩點間 squash cell 的 HIT 表示",
      "half-adjoint equivalence 是帶一個三角形相干的等價；contractible fiber 以 Σ center 與全域收縮路徑刻畫；截斷是到命題宇宙的左伴隨式反射 HIT",
      "三角形與 fiber 型別以 AST 檢查；identity/singleton 與 improved section 端點以轉換驗證；一般收縮與 adjointification 由第十期 lemIso 構造另行登記",
    ),
    entry(
      "維度代換閉合與持久 schema 註冊",
      SpecStructure,
      [
        "dline_subst", "dline_rev", "dvalue_subst_dims", "checked_line_reparam_closed",
        "DSchemaRegistrySnapshot", "schema_registry_snapshot", "schema_registry_restore",
        "schema_registry_merge_into", "schema_registry_register_inductives", "schema_registry_manifest",
      ],
      "裸 DLine 與語義封閉值攜帶可重參數化的維度代換；註冊表以 64 個 bucket 的 hash-cons plan、snapshot 與 manifest 指紋為持久範形",
      "立方代換是維度脈絡間的函子作用；registry 是 schema 描述子集合上的 interned 有限圖，snapshot/merge 對 plan 身分函子性地保存",
      "代換後 coe 與反向線以轉換驗證；bucket 只縮小候選集而身分仍以完整鍵判定，restore/merge/batch 後統計與 plan 身分重驗",
    ),
    entry(
      "一般代數認證數值與 DAG 原生 BDD 操作",
      SpecStructure,
      [
        "AlgC", "AlgCertMat", "AlgCertPath", "alg_cert_outer", "alg_cert_is_projector",
        "alg_cert_square_in_image", "bdd_dag_reachable_count", "bdd_dag_eval", "bdd_dag_sat_count",
        "bdd_dag_restrict", "bdd_dag_exists", "bdd_dag_forall", "bdd_dag_dnf_face",
        "face_sat_decide", "face_eq_decide",
      ],
      "AlgC 是同一 AlgNum modulus 上的實虛對；形式路徑／方塊以任意次多項式係數表表示；BDD 以 reachable DAG root 為範形，滿足數是 BigInt",
      "一般有限代數擴張 C=K(i) 上的 Hermitian 線性代數；DAG 是固定變量序布林函數的共享規範圖，exists/forall 是投影量化",
      "投影、像與方塊含入以係數精確相等判定；DAG 操作直接在 interned graph 上 memoized，預算不足時 DNF 回 None 或轉 DPLL 總判定",
    ),
    entry(
      "球面同倫代表元與 Hopf 連結不變量",
      SpecStructure,
      [
        "loop_space_type_term", "based_map_type_term", "circle_degree_value", "sphere_degree_value",
        "suspension_unit_loop_value", "sphere3_swapped_schema", "sphere3_swapped_equiv_value",
        "hopf_map_s3_to_s2", "hopf_linking_number_numeric", "check_sphere_homotopy_representatives",
        "check_hopf_numeric",
      ],
      "Omega^n 以巢狀 Path 與迭代 refl 表示；整數度數映射由 circle loop 冪次逐層懸掛；極交換 S³ 以 south/north 順序互換的 HIT 表示；Hopf 映射採 C² 單位球座標",
      "懸掛是端點塌縮函子，基點映射與 loop space 是 pointed 類型範疇的代表元；Hopf 纖維是 S¹ 主叢纖維，其連結數是 Hopf 不變量",
      "生成 meridian 上以轉換檢查度數與單位環路，交換呈現以依賴消去 sect/retr 路徑檢查；Hopf 像與纖維由代數恆等檢查，連結數以立體投影後 Gauss 積分數值判定絕對值 1",
    ),
    entry(
      "非 Miller pattern 的受限高階合一",
      SpecOperator,
      ["check_hou_phase9_extensions"],
      "重複變量 spine 取首個重複 binder；succ/pair 構造子 spine 以 pred/fst/snd 擷取葉變量；相異 flex-flex 以支援交集上的共同 fresh meta 表示",
      "這些片斷是 pattern unification 在重複代換與可逆構造子模式上的保守擴張；共同 meta 是兩 flexible substitution 支援的交集反射",
      "此確定性層的同頭 flex-flex 只在逐項引數合一後 spine 相同才解；任意 rigid spine 與置換由第十期有界搜尋層處理",
    ),
    entry(
      "模組分離編譯、介面連結與增量快取",
      SpecStructure,
      [
        "CompiledModule", "CompiledModuleEnv", "ModuleCompileCache", "module_decl_abstract",
        "module_compile", "compiled_module_validate", "compiled_module_to_module_def",
        "module_link_instantiate", "module_compile_cached", "compiled_module_specialize_prefix",
        "check_module_compilation",
      ],
      "CompiledModule 保存已檢查的參數 telescope、展平 entries、exports、依賴介面指紋與 public projection 編碼；介面 hash 不含 opaque body，實作 hash 含全部 entries",
      "抽象宣告是 telescope 中的中性介面條目；編譯是模組函子到已檢查物件的映射，連結以 synthetic import-free 定義取代來源，prefix 特化是部分函子套用",
      "抽象模組可簽章但不可實例化；implementation 須介面 hash 相同且補足抽象 exports；cache 以來源與依賴介面指紋判定 hit；磁碟二進位格式由第十期 codec 另行登記",
    ),
    entry(
      "一般可收縮纖維與自動 adjointification",
      SpecStructure,
      [
        "equiv_fiber_type_value", "equiv_fiber_path_value", "equiv_fiber_contraction_value",
        "equiv_contractible_fibers_value", "adjointify_equiv_value", "check_general_adjointification_and_contractible_fibers",
      ],
      "任意纖維元素間的路徑以 lemIso 三層填充方塊表示：兩次 hfill 連接 g∘p 與 retr、再連接兩條填充，來源方塊 hcomp 後由 f 與 section 自然性方塊閉合；adjoint retr 是 f x 纖維中往 (x,refl) 收縮的第一分量，三角形由第二分量方塊轉角 hcomp 抽出",
      "quasi-inverse 的 isEquiv 刻畫是所有 homotopy fibers 可收縮；half-adjoint 三角形是該收縮在對角纖維上的邊界方塊",
      "Bool 非與圓形恆等上以轉換驗證收縮兩端、一般中點的面下邊界、替換 retr 端點與三角形兩端；離散 Bool composition 另以 cap 值展開使巢狀 hcomp 有布林範形",
    ),
    entry(
      "有界 Huet 高階合一搜尋",
      SpecOperator,
      [
        "HouSearchStatus", "HouSearchReport", "hou_search_unify", "hou_search_unify_bool",
        "check_hou_bounded_search",
      ],
      "搜尋狀態是可回復的 Unifier 快照、節點/分支計數與深度；候選範式為確定性片斷解、rigid imitation 模板、formal spine 上的 projection、eta 生成、同頭不變座標剪枝及相異 flex-flex 共同常數",
      "Huet 搜尋在高階代換的分支樹上以 imitation 與 projection 生成候選；回報區分已解、閉 rigid 衝突、深度殘餘與節點預算耗盡",
      "每節點先試確定性 hou_unify，失敗回復快照；任意 rigid spine 由 imitation 分解為 formal 引數上的 fresh 子目標；同頭置換只保留逐項可證不變座標，失敗不污染輸入 unifier；一般 HOU 不可判定故不宣稱完備必停判定",
    ),
    entry(
      "穩定已編譯模組二進位格式",
      SpecStructure,
      [
        "ModuleBinaryStatus", "ModuleBinaryLoad", "compiled_module_binary_format_version",
        "compiled_module_to_binary", "compiled_module_from_binary", "compiled_module_load_binary",
        "compiled_module_load_binary_report", "compiled_module_binary_to_hex", "compiled_module_binary_from_hex",
        "check_module_binary_format",
      ],
      "檔案是 CHMODBIN 魔數、版本/flags、payload 長度與 DJB2-xor checksum 標頭，後接小端固定欄位 payload；字串為 UTF-16LE code-unit 串，DTerm、Dim/Face、層級表達式、正性函子、歸納與 HIT 描述子各用固定標籤遞迴編碼",
      "CompiledModule 的持久範形是其全部已檢查欄位，接口/實作 hash 仍由模組編譯層定義；hex 是二進位位元組的文字檔案表示",
      "解析器驗證位元組範圍、魔數、版本、長度、checksum、計數剩餘量與遞迴深度，並要求 payload 精確耗盡；load 形式再以 compiled_module_validate 驗 hash 與 synthetic 定義重 elaboration，竄改與截斷回精確狀態",
    ),
    entry(
      "極端輸入成本控制：BDD、SAT 與精確多項式",
      SpecOperator,
      [
        "bdd_manager_cache_stats", "BddOptimizedBuild", "bdd_dag_of_face_optimized",
        "FaceCnfStats", "face_cnf_stats", "face_sat_watched_dpll", "face_eq_watched_dpll",
        "check_bdd_cost_optimizations", "check_qpoly_fast_arithmetic",
      ],
      "BDD 成本範形包括 reachable node 數、節點/apply 桶數與快取條數；face 的搜尋範形是 Tseitin CNF 的 variables/auxiliaries/clauses/literals；稠密整數多項式以共同分母縮放後 Karatsuba 分治，稀疏多項式保留跳零卷積",
      "sifting 是變量序上的局部搜尋；watched literals 把單位傳播限制在被賦值文字監視的子句；Karatsuba 以三次子乘法取代四次，這些都降低可處理片斷成本而不改變最壞情況指數下界",
      "BDD 初始候選序後逐變量試全部插入位置並受 rebuild 預算限制；apply cache 隨條數增長重散列；DPLL 以保存相位與衝突活動選變量且見證回驗，預算耗盡回明示狀態；多項式冪改二進位冪",
    ),
    entry(
      "核內整數、π₃ 商呈現與球面環路代表元分類",
      SpecStructure,
      [
        "integer_schema", "integer_type_term", "integer_value", "integer_succ_value",
        "integer_pred_value", "homotopy_group_type_term", "pi3_sphere_type_term",
        "sphere_loop_power_value", "SphereLoopExpr", "sphere_loop_expr_degree", "sphere_loop_expr_value",
        "check_sphere_loop_representatives_internal",
      ],
      "IntegerS 以 zero、posSucc(NatS)、negSucc(NatS) 唯一表示整數；πₙ 以 Ωⁿ 對命題截斷路徑關係的 QuotientS 表示；球面生成環路由 circle loop 經懸掛 unit 逐層提升，並沿 meridian(base) 與其逆的消去方塊 transport 改基；代表元表達式以 generator、逆與合成生成且 degree 為其範形",
      "Ωⁿ 是迭代基點路徑類型，πₙ 是代表元在高一路徑下的商；懸掛 unit 是 pointed suspension/loop 伴隨的單位，代表元微積分是自由生成子上的群字問題範形",
      "IntegerS 與 π₃(S²)/π₃(S³) 型別以依賴檢查驗證，succ/pred 與代表元 degree 往返以轉換/整數相等驗證，S²/S³ 生成環路檢查外層端點；此登記只宣稱代表元分類與 decode，一般合成 encode/decode 分類定理仍保留為邊界",
    ),
    entry(
      "跨家族巢狀函子與同時 IR 編譯（第十一期）",
      SpecStructure,
      [
        "DFunctorParamArg", "dfunctor_family", "dfunctor_param_self", "dfunctor_param_term",
        "simultaneous_ir_compile_decode", "code_interpretation_ir", "check_family_nested_functors",
        "check_simultaneous_ir_compiled_decode",
      ],
      "DFunctorFamily(spec, params, indices) 以值攜帶目標規格；參數槽由 DFunctorParamArg 標明 Term（外部項，經 schema_eval_under 在當前脈絡求值）或 Self（宿主家族於給定索引實例化）；IH bundle 是每構造子引數一槽的巢狀 DVPair…DVUnit；同時 IR 經中性探測宇宙等級與位置映射編譯為改名後的 decode 規格",
      "跨家族巢狀是嚴格正函子的複合（外部初始代數以宿主代數為參數）；gather 把巢狀 IH 束提升為宿主 motive 截面；同時歸納—遞迴在宇宙結果僅依賴單一解碼函數時退化為 Tarski 解碼",
      "validate 拒絕 Decoded* 引數類與參數非葉出現（不可 gather）；編譯拒絕真正互依（他函數 IH 槽被引用）與依賴 code 的宇宙等級；FamRoseTreeS/FamVecTreeS 以束葉計數與 IH 型別轉換驗證，編譯範例於值層與項層與同時形式一致；自引用同規格的 Bush 形巢狀明示不在本期範圍",
    ),
    entry(
      "Face 合意區域、精確修復與不透明立方開盒（第十一期）",
      SpecStructure,
      [
        "face_agreement_face", "face_agreement_face_sound", "DSystemRepairExact",
        "dsystem_repair_to_base_exact", "DCubeFunction", "DCubeOpenBox", "DCubeBoxFace",
        "DCubeBoxReport", "dcube_open_box", "dcube_box_validate", "dcube_box_fill_verified",
        "dcube_box_cap", "PolyCube", "PolyOpenBox", "poly_box_fill_verified", "check_face_agreement_and_exact_repair",
        "check_dcube_open_box_filler", "check_poly_cubes",
      ],
      "兩值的合意區域同給布林 BDD 形與 Face 值形（後者以 FEq0/FEq1 的析取保留 i=0 與 i=1 雙端點，布林化後等於 BddOne）；立方是宿主函數（維度列→語義值／有理多項式座標）；開盒缺一面、帽是填充在缺面的限制",
      "合意面是面格切片中兩偏元素的等化子；checked 修復是進入相容系統子類的反射；外部立方是 □ 上的外部函子資料，其填充是宿主層的 Kan 條件；多項式立方以 F += w·(S − F|face) 迭代修正至邊界恆等",
      "Face 合意以逐頂點轉換求最大面並以 sound 檢查封閉；exact repair 只保留 Face 值合意面內的分支部分（頂點層面不刪）；開盒逐對重疊以轉換／規範多項式相等驗證，不相容與不完整皆拒絕並給失敗計數",
    ),
    entry(
      "lemIso 一般點與 Circle/Torus 點值合成（第十一期）",
      SpecTheorem,
      [
        "check_lemiso_generic_points", "check_circle_torus_point_comp", "dim_of_face",
      ],
      "lemIso 收縮方塊在中性點與中性路徑兩端求值後以端點與邊界方程表示；圓與環面的點值合成範形是座標的 De Morgan 選擇式（dim_of_face 把面公式重讀為維度式）",
      "adjointification 的纖維收縮在一般（非規範）點上成立；原始 Circle/Torus 型別上的 comp 在點值資料下由座標方程閉合，非點值 tube 保留為 DNComp 形式合成",
      "中性點直接轉換判定；中性路徑案例以維度兩端限制檢查（端點不化約的路徑消去中性式需要 conversion 內 case-split，明示不做）；點值 tube 以 pairwise 相容加 fold 選擇計算並以 dim_eq_sem 驗證",
    ),
    entry(
      "註冊位元組持久化與 DTerm 全域 hash-consing（第十一期）",
      SpecStructure,
      [
        "schema_registry_to_binary", "schema_registry_from_binary", "schema_registry_snapshot_from_binary",
        "schema_registry_snapshot_load_binary_report", "DSchemaRegistryBinaryLoad",
        "schema_registry_binary_roundtrip_ok", "DTermInternTable", "dterm_intern",
        "dterm_intern_id", "dterm_rebuild", "check_schema_registry_byte_persistence",
        "check_dterm_hash_consing",
      ],
      "CHREGBIN v1＝magic＋版本 u16＋長度 u32＋校驗 u32＋以模組 codec 編碼的全 DTerm/schema payload（第十二期 v2 改共用 DAG codec、v1 仍可讀，見第十二期儲存庫條目）；hash-cons 範形是自底向上的 intern 表（stamp→id 的有限圖），重建項與原項結構相等",
      "註冊表是可共享 elaboration 計劃的有限圖，其位元組形是穩定外表示；intern 是項語言到其子項共享商的態射，不改變檢查與正規形",
      "位元組載入逐一拒絕 bad magic/版本/截斷/校驗並回報狀態；往返後重驗註冊；intern 以 tree/distinct 子項計數與 dep_check/dep_nf 在 intern 前後一致驗證",
    ),
    entry(
      "自適應因式圖樣剪枝、雙二次去巢與特徵值簇分離（第十一期）",
      SpecOperator,
      [
        "QPolyDegreePattern", "qpoly_mod_degree_patterns", "qpoly_irreducible_by_mod_patterns",
        "check_qpoly_mod_pattern_pruning", "BiquadNum", "biquad_sqrt", "biquad_sign",
        "radical_to_biquad", "radical_equal_exact", "check_biquadratic_denesting",
        "JacobiClusterSeparation", "SeparatedEigenInterval", "jacobi_separate_clusters",
        "jacobi_cluster_separation_certified", "check_jacobi_cluster_separation",
      ],
      "模素數不可約因式次數的升冪列即次數圖樣；雙二次範形為基底 [1,√d₁,√d₂,√(d₁d₂)]（d₁<d₂ 無平方因子、遞增）上的有理係數；分離範形為不交特徵區間連同多重數",
      "圖樣是 Galois 群在根集合置換的循環型；雙二次數是二次子域合成的 Galois 閉包元素，共軛給出範數；平方自由部分的根是互異特徵值集",
      "圖樣先於有理根與 Kronecker 列舉剪枝（素數至 251、圖樣配額 32；x⁴+1 型 V4 情形誠實無法排除二次因式）；雙二次運算在 Q*/Q*² 的公共基底上行、開根以單根槽二次公式與多根槽 AlgNum 橋判定並平方重驗，符號以塔式平方比較判定；簇分離以平方自由部分 Sturm 區間對原多項式計數並以重疊唯一匹配",
    ),
    entry(
      "CDCL 子句學習與 BDD 精確最佳變量序（第十一期）",
      SpecOperator,
      [
        "FaceCdclStats", "FaceCdclResult", "face_sat_cdcl", "face_eq_cdcl", "face_sat_cdcl_report",
        "BddOptimalBuild", "bdd_dag_of_face_optimal", "check_cdcl_clause_learning",
        "check_bdd_optimal_order_exact",
      ],
      "學習子句以 1-UIP 斷言文字領頭；最優序範形為使 reachable node 數在全部排列中最小的排列連同 tried/exact 旗標",
      "CDCL 是蘊含圖上的衝突分析（學習子句是衝突的 resolution 證書）；變量序問題是布林函數共享範形在對稱群作用下的極值化；兩者皆不改變面格語義",
      "watched 傳播、VSIDS 活動、Luby 重啟節奏；與 2ⁿ brute force 和舊 DPLL 差分驗證、鴿洞實例要求 learned>0；最優序 n≤8 全排列可證、超出回報 exact=false 並語義對驗 face_holds；SAT 與 BDD 最壞指數界保留不變",
    ),
    entry(
      "圓的萬有覆疊與 encode/decode（第十一期）",
      SpecStructure,
      [
        "circle_hit_type_value", "circle_loop_space_type_value", "integer_succ_equiv_value",
        "circle_cover_value", "circle_encode_value", "circle_encode_pieces_value",
        "circle_decode_value", "check_circle_encode_decode",
      ],
      "helix 族在 base 的纖維是 IntegerS（zero / posSucc(NatS) / negSucc(NatS)，|n|−1 編碼）、在 loop 點是後繼等價的 ua GlueEquiv 型别；繞數與整數代表皆為規範 DVIntro 值",
      "覆疊族是圓上的纖維化，encode 是 subst 路徑提升的端點，decode 是整數初始代數到環路空間的消去；分類陳述是兩向複合在代表元的範疇等式",
      "base 纖維以宇宙層轉換等於 ℤ、loop 點纖維等於 ua 線；encode 在 refl/生成元/逆元直接計算為 0/1/−1；單次 subst 越過複合環路的 trans 點原經宇宙 comp 的 Glue 型別線不串接後繼等價（第十一期內涵邊界），第十二期起改經端點 Glue 線合成串接，loop²/loop³/loop⁻²/抵消的單次 subst 分別得 2/3/−2/0 並與 transport 函子性細分的計算一致；decode∘encode 在代表元以環路空間轉換判定、encode∘decode 在 0,±1 直接而在 ±2,3 依 decode 分解細分；任意中性環路的完整 π₁(S¹)≃ℤ 等價需商/funext 機械，仍為保留邊界；原始 DVCircleTy 以 dim_eq_sem 作點轉換會把 loop² 折回 loop，不作為分類對象",
    ),
    entry(
      "HOU 深搜尋、模組交錯編排與二進位版本遷移（第十一期）",
      SpecStructure,
      [
        "HouIterativeReport", "hou_search_unify_iterative", "check_hou_search_extensions",
        "ModuleItem", "check_module_interleaved_items", "CompiledModuleStore", "CompiledModuleStoreStats",
        "compiled_module_store_put", "compiled_module_to_binary_v1", "check_module_binary_versions_and_store",
      ],
      "模組定義範形為參數後單一 ModuleItem 列（import 與 decl 交錯），舊 decls 形展開為 imports 前置的等價列；CHMODBIN v2 在 v1 payload 後加 producer 字串；store 範形為 (blobs, hits, misses)",
      "交錯的模組函子 telescope 中 import 與宣告同為可依賴先行條目的延伸；迭代加深是同一帶預算搜尋函子在深度偏序上的最小不動點逼近",
      "HOU 以深 imitation、放寬的 projection 上限與同頭 identification 擴展，HouIterativeReport 記錄求解深度且解僅 specific unifier（非 MGU、一般 HOU 不可判定仍明示）；交錯範例中 legacy 排序必失敗而交錯成功；v1 寫出由 v2 截尾重建、遷移載入逐欄相等，tag 8 的 Family 節點在 v1 寫出時被拒",
    ),
    entry(
      "BDD 子集 DP 最佳序與 CDCL 子句刪除／RUP 證明（第十二期）",
      SpecOperator,
      [
        "bdd_dag_of_face_optimal_dp", "FaceCdclProofResult", "face_sat_cdcl_proof",
        "face_cdcl_proof_check", "check_bdd_optimal_order_dp", "check_cdcl_proof_and_reduction",
      ],
      "子集 DP 範形是對每個前綴子集計算的最小上層節點寬度表與逐步重建的順序；RUP 證明範形是與子句庫分開的學習子句序列，每條皆為在先行子句下以單位傳播蘊含的子句",
      "變量序問題在固定順序向量子集格上是動態規劃的最短路；RUP 是 resolution 的單位傳播片段，子句刪除保持可滿足性不變式而證明日誌不受刪除影響",
      "DP 於 n≤12 給出可證最優序（n=10 時 tried=5120；精確上限第十三期擴至 n≤16，見該期條目）；LBD 刪除只在 decision level 0 執行、reason 子句保留並重建 watches；RUP checker 以單位傳播重播驗證鴿洞反駁，第十三期再擴為帶刪除步驟的 DRUP",
    ),
    entry(
      "Schema 同規格非均勻遞迴、Self 參數型別與正性宣告（第十二期）",
      SpecStructure,
      [
        "DFunctorSelfFamily", "check_self_family_and_gather_shapes", "DPositivityDeclaration",
        "dpositivity_declaration", "dpositivity_declaration_from_lambda", "dterm_family_positivity_declared",
        "dterm_family_strictly_positive_declared", "inductive_parameter_positivity_declared",
        "check_positivity_declarations",
      ],
      "DFunctorSelfFamily(pargs, index) 是不攜帶目標規格的同規格自嵌標記（宿主字面值不可自引用其規格）；DPositivityDeclaration 範形為 (head, arity, strict_args, positive_args, scope)",
      "同規格自嵌是參數位上的非均勻初始代數遞迴（Bush：tail 型別為 Bush (Bush Bool)）；正性宣告是把不透明算子視為已知正函子的受信延伸，λ 驗證版是結構分析認可的正函子子類",
      "handler 以已建立的宿主 Self 型別取代 DVUnitTy 使依賴先行 Self 參數的後續參數可通過（List/Sigma 形狀一併 gather）；宣告以 depth-aware walk 於 binder 下移位比對且對參數 probe 代換同型，無宣告時不透明應用正性為 unknown、有宣告可得 strict，domain 位置仍負；SelfFamily 參數正性第十三期改以最小不動點判定（見該期條目）；宣告不構成不透明算子正性的證明",
    ),
    entry(
      "同時 IR eliminator 編譯（第十二期）",
      SpecStructure,
      [
        "simultaneous_ir_eliminator_type", "simultaneous_ir_compile_eliminator_block",
        "simultaneous_ir_compile_eliminator", "check_simultaneous_ir_eliminator_compilation",
      ],
      "互賴函數塊逐函數依宣告序編為同一 base 家族 eliminator 的閉項：已編的較早宇宙函數項供外來 IH、函數引數的自身遞迴在 lambda 下套用",
      "在單一初始代數上的同步歸納—遞迴可由其 eliminator 的截面複合表示；motive 餘域為 DVUniv(base.level)，故函數層級須嚴格小於 base 層級（與 decode 路線的片斷互補）",
      "每項經 dep_check_closed 且在外層脈絡以新鮮中性值強制套用 motive 與各 case lambda 逐一檢查本體（d_check 對 lambda 本體惰性，僅閉項檢查不足）；循環互賴、層級不合、前向引用、非宇宙外來函數與第十三期函子映射片斷外的巢狀/decoded 引數回 None；互賴 El/El2 的範形與 decode 路線相符",
    ),
    entry(
      "DSystem 結構合意與 repair 補入（第十二期）",
      SpecStructure,
      [
        "bdd_tree_cofactor", "dterm_dim_vars", "DSystemRepairSupplemented", "dsystem_repair_with_candidates",
        "check_dsystem_structural_agreement_and_supplementation",
      ],
      "合意區域的結構範形只保留分支語法上實際出現的維度（其餘變量以 cofactor 相等自 BDD 消失）；補入結果記錄 (system, base_removed_region, repaired_branches, added_branches, rejected_candidates, compatible)",
      "面合意是面格中的等化子，其支撐是兩值維度支撐的聯集；補入是相容子系統格中沿給定順序的貪心延伸",
      "合意檢查把逐頂點轉換探測限制在相關維度（12 維環境中雙端點合意面仍得 root var 0 的緊湊 BDD）；repair 先 exact 截斷再逐一在可驗證相容下補入候選並拒絕其餘，結果是順序相依的極大相容子系統，不宣稱為最大",
    ),
    entry(
      "Bool case-split 轉換與路徑值合成（第十二期）",
      SpecOperator,
      [
        "conv_terms_case_split", "conv_terms_plain", "check_case_split_conversion_and_path_comp",
      ],
      "case-split 轉換以新鮮中性環境求值的普通轉換打頭，失敗時對型別求值為 DVBoolTy 且出現於兩項或型別的脈絡變量遞迴代入 true/false；路徑值合成的範形為 comp_path_value 以端點 tube 遞迴至基底 comp 的 DVPathLam",
      "Bool 是離散立方型別，變量 case-split 對轉換是健全的 η 型加強；Circle/Torus 分支帽座標以一般分支值代入合成方向 1 讀出，是座標多項式在端點的取值而非端點範形",
      "if x then 0 else 0 ≡ 0 切分可判、真正依賴 x 者仍拒絕，雙 Bool 變量與相依型別代入遞迴處理，Nat 變量不切分、未出現不誤判；右端點行經環路的 Path 型別合成算出環路帽（Circle 與 Torus 雙座標），輸入系統不合型別時結果不作保證",
    ),
    entry(
      "Artifact 儲存庫、共享 DAG codec 與版本協商（第十二期）",
      SpecStructure,
      [
        "ArtifactByteStore", "artifact_byte_store_new", "artifact_memory_byte_store_new",
        "ArtifactRecord", "ArtifactRepository", "artifact_repository_new", "artifact_repository_put",
        "artifact_repository_get", "artifact_repository_list", "artifact_repository_remove",
        "artifact_repository_recover", "artifact_repository_verify_all", "ArtifactRepositoryStats",
        "artifact_repository_put_compiled_module", "artifact_repository_get_registry_snapshot",
        "BinaryVersionPolicy", "binary_negotiate_version", "compiled_module_binary_version_policy",
        "schema_registry_binary_version_policy", "check_artifact_repository_and_dag_codec",
      ],
      "儲存庫範形為抽象鍵→位元組儲存上的 blobs 與 manifests（雙哈希、長度、格式版本）加單一 index 鍵；DAG codec 範形為達節點門檻後以 tag 255 back-reference 序列化的共享項圖，CHMODBIN v3 與 CHREGBIN v2 共用；版本政策範形為 (current, supported, oldest_writable)",
      "儲存庫是命名工件在抽象鍵值儲存上的函子式持久層，提交順序 blobs→manifests→index 給出原子可見性；版本協商是支持集交集在可寫偏序上的最大元",
      "put 後 index 才指向新 manifest，未完成提交不可見；blob 損壞於 get 以哈希拒絕，index 全失由 manifests 掃描復原並計數；DAG 往返逐欄相等且小項不啟用 back-ref；協商在無共同版本時回 None、寫出不低於雙方 oldest_writable；抽象儲存是協議而非 OS 磁碟",
    ),
    entry(
      "不可約證書、三次／三二次塔與簇感知 Jacobi（第十二期）",
      SpecOperator,
      [
        "QPolyIrreducibilityCertificate", "qpoly_irreducibility_certificate", "qpoly_irreducibility_certificate_check",
        "qpoly_irreducible_certified", "check_qpoly_irreducibility_certificates",
        "CubicNum", "cubic_make", "cubic_norm", "cubic_sign", "radical_to_cubic",
        "TriquadNum", "triquad_make", "triquad_sign", "triquad_sqrt_of_biquad", "radical_to_triquad",
        "check_tower_fields", "JacobiClusterAwareReport", "jacobi_interval_eigen_cluster_aware",
        "check_jacobi_cluster_aware_iteration",
      ],
      "不可約證書範形為 CertLinear/CertLowDegreeNoRationalRoot/CertModPrime/CertEisenstein 可重驗標記連同見證；CubicNum 為 cubefree m 上的 a+b∛m+c∛m²、TriquadNum 為三個平方類獨立生成元的 8 維係數；簇感知報告攜帶證書、精度、重啟次數與分離狀態",
      "證書是不可約性在證書範疇中的態射（檢查比重算因式分解便宜）；根式判等的塔是有限 Galois 塔的子格；簇感知迭代把譜簇資訊回饋進相似變換的 pivot 選擇",
      "x⁴+1 以零 Kronecker 預算經 Eisenstein 平移證書判定，證書檢查全拒變造；radical_equal_exact 逐層嘗試單二次/雙二次/純三次/三二次，第十三期其平方根片斷再接四生成元多二次塔且開方以平方重驗，生成元逐一以平方類獨立化簡；簇感知迭代在迭代內分離 count-2 簇且證書可由 jacobi_certificate_sound 核驗（與事後 Sturm 簇分離分開記錄）",
    ),
    entry(
      "HOU 主合一子與殘留約束語意（第十二期）",
      SpecOperator,
      [
        "HouMguStatus", "HouConstraint", "HouMguReport", "hou_unify_mgu", "check_hou_pattern_mgu_and_residuals",
      ],
      "報告範形為 (status, substitution, residual)：Principal 時 substitution 是字彙序規範化的主替代、Residual 時為部分替代連同 HouConstraint 列 (lhs, rhs, depth)",
      "Miller pattern 片斷中合一子範疇有初始物件（MGU 模改名唯一）；殘留約束是該範疇邊界上的未解相等問題，續解是替代在約束上的作用",
      "flex-flex 交集、pruning 與 pattern 抽象產主合一子並以具體其他合一子的可分解性抽查；occurs/頭衝突給 no-unifier 且失敗還原先行狀態；重複變量與 constructor-spine 形回 Residual 並可由後續替代續解，一般 HOU 不可判定性與非 pattern 形的不完整性明示",
    ),
    entry(
      "宿主立方分層外延檢查（第十二期）",
      SpecOperator,
      [
        "DCubeStratifiedReport", "dcube_cubes_conv_stratified_report", "dcube_cubes_conv_stratified",
        "dcube_box_validate_stratified", "dcube_filler_faces_ok_stratified", "dcube_box_fill_verified_stratified",
        "check_dcube_stratified_extensionality",
      ],
      "分層探針範形為三個基礎乘積池的維度賦值枚舉（逐軸 {0,1,新鮮變量}、{0,1,共享 s,共享 t} 與 {s,¬s,s∧t,s∨t}），第十三期另加逐軸深層連接 Tier D；報告為 (equal, probes, failed, complete)",
      "探針層對應立方體面格的層（strata）與連接退化：宿主函數在面、對角與連接子立方上的限制決定其在這些商上的外延行為",
      "逐探針以 conv_at 比較、首個失敗即停；只在端點/對角/連接層與常數立方相異的宿主函數被分層檢查拒絕而一般點檢查放行； arity 2 的相等對在原三層共行 41 探針、加入 Tier D 後共 105 探針；盒驗證與填充改走分層邊轉換；探針數逾 4096 的層跳過並回 complete=false，有限探針不構成全外延證明",
    ),
    entry(
      "環路單位律 3-胞與精確有理 Hopf（第十二期）",
      SpecTheorem,
      [
        "dpath_left_unit3_value", "dpath_right_unit3_value", "hopf_map_rat", "hopf_rotate_rat",
        "check_hopf_exact_rational", "check_loop_unit_3cells_and_hopf_exact",
      ],
      "單位 3-胞範形為巢狀 DVPathLam：左單位是 transitivity 方塊上保持端點的兩階段連接旋轉之複合、右單位是垂直滑行；Hopf 範形為 ℚ⁴→ℚ³ 的二次多項式映射與 ℚ 上的相位旋轉",
      "單位 3-胞是迭代環路空間 ∞-群胚中單位律的見證態射（代表元層）；有理 Hopf 恆等式是多項式恆等在稠密有理子集上的精確實現",
      "3-胞在 S²/S³ 冪代表元上以一般參數檢查兩面與中間端點轉換；有理檢查逐點精確驗證落於 S²、沿有理旋轉像不變、極點纖維與兩纖維抽樣不交；本條只登記單位律，逆元/結合律 3-胞與閉代表式分類由第十三期條目補上；交換律 3-胞、內部 Hopf 映射與一般中性環路的 π 分類仍不宣稱",
    ),
    entry(
      "SelfFamily 參數嚴格正性的不動點判定（第十三期）",
      SpecOperator,
      [
        "inductive_parameter_positivity", "hit_parameter_positivity", "check_self_family_positivity_fixpoint",
      ],
      "每個宿主規格參數的正性報告彼此引用，範形為由全部 false 開始的最小不動點：直接葉位置先成立，SelfFamily 應用再沿已證正的同規格參數位置傳播",
      "同規格非均勻初始代數在參數替換下是參數化初始代數；不動點是參數正性在自引用函子複合下閉合的聯合歸納定義，HIT 參數沿同一判準處理",
      "Bush 的儲存參數跨一次自嵌仍嚴格正、phantom 參數不出現、一層自嵌後的負位置正確傳播，雙參數 swap 族兩參數皆由相互不動點認證；不透明同規格外形仍不作超出函子語法的正性證明",
    ),
    entry(
      "同時 IR 的巢狀 foreign IH 函子映射（第十三期）",
      SpecStructure,
      ["check_simultaneous_ir_nested_foreign"],
      "互賴函數塊仍逐函數編為同一 base eliminator 的閉項；外來巢狀 IH 範形為對 Product／Pi／List 等正性函子值作項層 functor map 後重建的 bundle",
      "同步歸納—遞迴是單一初始代數上 motive 截面的函子複合；foreign bundle 的拼湊由正性函子的自然性給出，base motive 的餘域層級條件不變",
      "TreeSU 的積、函數與積含 List 巢狀引數中，第二函數自第一函數的巢狀 bundle 讀取 IH，閉樹上的編譯正規形與同時語義一致；前向引用、非宇宙外來函數、層級不合與此函子片斷外的 decoded 巢狀位置仍拒絕",
    ),
    entry(
      "面下轉換的相關維度下降（第十三期）",
      SpecOperator,
      ["check_conv_under_face_relevant_descent"],
      "面下轉換先以兩值的引文支撐與面 BDD 的 cofactor 結構界定實際相關維度，範形為同一個 holds 結果連同已訪問節點數",
      "面合意是面格切片中的等化子，值只依賴其維度支撐所成的商立方；下降是該支撐投影下的限制再提升",
      "十維環境中 (i9=0) 與八變量 parity 面的合取有數百條滿足路徑，但 i9 上的 loop 以至多 12 個探測轉換為 base；i9 自由（含內部）時正確失敗，端點析取仍依法分開或以 Face 值合意面見證",
    ),
    entry(
      "DSystem 最大相容補入（第十三期）",
      SpecStructure,
      [
        "DSystemRepairMaximum", "dsystem_repair_maximum", "check_dsystem_maximum_completion",
      ],
      "候選分支先 exact-restrict 到與 base/重疊可相容的區域，再在分支相容圖上取最大團；結果記錄 repaired/added/rejected、相容性與 exact 旗標",
      "相容偏元素在面格切片中是兩兩在重疊上同意的系統族；最大補入是此相容偏序中的真正最大元問題，而非順序貪心所得到的極大元",
      "五分支例中順序貪心只得 {b0,b4}（大小 2），最大完成得 {b1,b2,b3}（大小 3）且 exact/compatible 皆真；node budget 為 0 時回 exact=false，但 incumbent 不小於貪心結果",
    ),
    entry(
      "Circle/Torus 方塊值 comp 的驗證座標帽（第十三期）",
      SpecOperator,
      ["check_circle_torus_square_comp"],
      "Path 型別上 Circle/Torus tube 的帽由一組候選 De Morgan 座標（兩序迭代選擇、分支帽的未阻尼與阻尼 join）逐一試算，第一個在每一分支面都限制為該分支帽者勝出",
      "方塊合成是 Path 型別 Kan 纖維化結構在內部合成方向的提升；端點同定不是維度代數的同餘，故點相等不足以選座標，必須逐面驗證限制",
      "loop tube 的方塊帽是 DVPathLam、兩端轉換為基點、一般內部是點值且在 tube 面轉換為原 loop（Circle 與 Torus 第一座標皆然）；無任何候選座標能逐面驗證的盒子誠實保留為 DNComp 中性合成",
    ),
    entry(
      "差異導引的 Bool case-split 轉換（第十三期）",
      SpecOperator,
      [
        "CaseSplitReport", "conv_difference_variables", "conv_terms_case_split_report",
        "check_difference_guided_case_split",
      ],
      "兩項與型別先 quote 為範形並作語法差異，範形為根差異 Bool 變量列與 (holds, probes, root_difference_variables, split_nodes) 報告；只對差異變量作 true/false 遞迴代入",
      "Bool 的 case-split 是離散立方型別對轉換的健全 η 式加強；差異導引把搜尋限制在兩側正規形真正不一的脈絡坐標，不改變覈心轉換關係",
      "三個 Bool 假設中兩側共享依第一變量的子項而只在最後變量相異時，差異集恰為最後變量且 split_nodes=1；普通轉換仍先行，真正不等的對仍拒絕，Nat 變量不切分",
    ),
    entry(
      "DTerm intern DAG 與位元組共圖（第十三期）",
      SpecStructure,
      [
        "DTermDagNode", "DTermDagSnapshot", "DTermDagBinaryLoad", "DTermDagImportReport",
        "dterm_local_shell", "dterm_dag_snapshot", "dterm_dag_snapshot_validate",
        "dterm_dag_import", "dterm_dag_snapshot_to_binary", "dterm_dag_snapshot_from_binary",
        "artifact_repository_put_dterm_dag_snapshot", "artifact_repository_get_dterm_dag_into",
        "check_interned_dag_byte_sharing",
      ],
      "可達 intern 圖的範形為拓撲序的 local shell＋child-id 邊連同 root ids；CHDAGBIN v1 是此圖的穩定位元組外形，匯入時逐節點 hash-cons 並記錄 added/reused 與新 root ids",
      "intern 表是項語言模子項結構相等之商的有限 DAG 表示；snapshot/匯入保存此商身分，工件儲存庫的重取則把外部圖函子式地植入活表中",
      "三個 root 的 snapshot 節點少於樹節點、往返逐欄相等、root ids 與來源表一致；同一圖第二次匯入 added=0，前向／越界邊或 arity 不合在目標表改變前拒絕；既有 CHMODBIN v3/CHREGBIN v2 仍是 payload-local back-reference，僅 CHDAGBIN 與活 interner 共圖",
    ),
    entry(
      "聯合 mod-p 次數圖樣不可約證書（第十三期）",
      SpecOperator,
      [
        "QPolyIrreducibilityCertificate::CertModDegreePatterns", "check_qpoly_degree_pattern_certificates",
      ],
      "證書範形為一組無重覆且當地可用的素數；重驗時逐素數重算 mod-p 不可約因式次數圖樣，再檢查每個真因式次數至少被一個圖樣排除",
      "每個圖樣是 Dedekind 定理下 Frobenius 在根集上的循環型；若 f 在 Q 上有 d 次因式，則在每個可用素數下都須有若干局部次數合計為 d，故聯合證書是多個 Frobenius 約束的合取",
      "x⁴-4x³-3x²-x-4 模 2 為 [1,3]、模 3 為 [2,2]，單獨皆不能同時排除次數 1 與 2、聯合可以，且零 Kronecker 預算的因式分解經此 fast path 返回單一原多項式；重覆素數、合數 9 與不合用的圖樣皆拒",
    ),
    entry(
      "四生成元多二次塔體（第十三期）",
      SpecStructure,
      [
        "MultiQuadNum", "multiquad_make", "multiquad_align", "multiquad_mul", "multiquad_inv",
        "multiquad_sign", "multiquad_sqrt_in_field", "multiquad_sqrt_extended", "multiquad_rational_square_adjustment",
        "radical_to_multiquad", "check_multiquadratic_tower",
      ],
      "MultiQuadNum 是至多四個在 Q*/Q*² 中獨立的無平方因子生成元所張 16 維乘積基底（槽根為子集乘積 √∏dᵢ）上的有理係數；兩值先在平方類 span 中對齊再運算，需第五生成元的合成體回 None",
      "Q(√d₁,…,√dₖ) 是二次擴張合成的有限 Galois 塔；Galois 共軛的範數乘積給逆元，基底對齊是在平方類向量空間取兩生成集的同一 span 基底",
      "同域開方以相對範數遞迴 u²-dv²=s² 與 p²=(u±s)/2 判定並平方重驗；擴張開方先求有理平方調整 x=γw²（γ 依已平方槽根的等價類正規化）再 adjoin √γ，至多仍四生成元；符號以二進精確區間細化判定。radical_equal_exact 的平方根片斷接入此塔；無有理平方類、一般代數被開方數與高於四生成元的二次塔明示在片斷外",
    ),
    entry(
      "精確最佳 BDD 變量序的十六變量子集 DP（第十三期）",
      SpecOperator,
      ["check_bdd_optimal_order_dp_extended"],
      "DP 範形是逐前綴子集的最小上層寬度與增量限制得到的 cofactor 集，連同回溯出的變量排列、tried 與 exact 旗標；上限為 16 變量",
      "固定序 ROBDD 的大小由每層相異 cofactor 數決定；前綴子集格上的動態規劃是對稱群中最優序問題的最短路，增量 cofactor 是同一狀態的限制像",
      "14 變量成對函數給 exact 且 tried=114688=14·2¹³、逐賦值語義一致且不大於啟發式結果，統一入口亦路由至 DP；16 變量在界內 exact，17 變量起 exact=false，不改變 ROBDD 最壞指數界",
    ),
    entry(
      "帶子句刪除的 CDCL DRUP 證明（第十三期）",
      SpecOperator,
      [
        "FaceCdclProofStep", "face_cdcl_drup_check", "check_cdcl_drup_proof_with_deletions",
      ],
      "證明範形為時序化的 CdclProofAdd／CdclProofDelete 步驟列；子句身分以排序去重的字面集合為範形，檢查器維持演進中的 active 子句庫並要求空子句最終可單位導出",
      "DRUP 的每步 Add 都是在當時子句庫上可單位傳播蘊含的 resolution 後果，Delete 只改變後續可用前提而不改變已證後果的可滿足性不變式",
      "檢查器接受集合序不同的刪除，拒絕刪除不存在或尚未加入的子句、拒絕使用已刪子句證空子句；求解器對 PHP(6,5) 與 PHP(7,6) 的 Add/Delete 計數恰與 learned+1/deleted 對帳且後者 deletes>0，完整證明重播通過",
    ),
    entry(
      "宿主立方分層外延 Tier D（第十三期）",
      SpecOperator,
      ["check_dcube_stratified_tier_d"],
      "分層探針在面內部、對角與連接三層之外增逐軸深層連接 Tier D（含否定與巢狀連接形狀）；報告仍為 (equal, probes, failed, complete)",
      "Tier D 是立方體在每條座標軸上經連接代數式退化後的外延商，宿主函數若只在該軸的深層連接像上相異，舊三層的合成表達式形狀無法分辨",
      "只藏於 ¬(s∧t) 或第二軸 (s∨t)∧¬s 式形狀的反例現被拒絕；二維相等對完整執行 105 探針，五維時 Tier D 逾 4096 探針上限而跳過並回 equal 探針結果連同 complete=false；有限探針仍不宣稱為全外延證明",
    ),
    entry(
      "Jacobi 自適應驅動與精確 Sturm 後援（第十三期）",
      SpecOperator,
      [
        "JacobiAdaptiveReport", "jacobi_interval_eigen_adaptive", "check_jacobi_adaptive_exact_fallback",
      ],
      "報告範形為簇感知 Jacobi 證書連同可選精確分離、exact_fallback_used、exact_width_bits、target_met 與最大區間寬度；Jacobi 路徑達標要求全為不大於目標寬的 singleton，精確路徑允許一區間攜帶精確重數",
      "自適應驅動是區間相似變換與特徵多項式根隔離兩個譜包含函子的分段組合：前者停滯時用後者的 Sturm 計數恢復分離與重數，兩者都給同一組可核驗特徵包含",
      "易例直接由 Jacobi 路徑達 1/16 目標且 separation=None；特徵值 ±1/4096、目標 1/16384 且 Jacobi 精度刻意封頂時，驅動器切換精確後援、target_met=true；精確位數不足時保存最佳結果並如實回 target_met=false",
    ),
    entry(
      "環路逆元／結合律 3-胞與閉代表式分類（第十三期）",
      SpecTheorem,
      [
        "dpath_left_inverse3_value", "dpath_right_inverse3_value", "dpath_triple_square_value",
        "dpath_assoc3_value", "dpath_sym_compose3_value", "sphere_loop_canonical_expr",
        "sphere_loop_canonical_value", "sphere_loop_expr_normal_form", "sphere_loop_expr_normalize3_value",
        "sphere_loop_expr_same_class", "check_loop_inverse_assoc_and_classification",
      ],
      "3-胞範形為巢狀 DVPathLam：逆元律經連接滑行與抵消胞、結合律經通用 triple-square 重參數化、sym(α·β) 經反向連結至 sym(β)·sym(α)；閉代表式範形為相同 degree 的生成元冪典範字",
      "這些是迭代環路空間 ∞-群胚一維運算在二維的相干見證；代表式正規化依 compose/inverse/unit/assoc 與單位、逆元 3-胞遞迴組裝，是代表元群字範疇到典範冪的截面",
      "左右逆元、結合律與 sym 複合在 S²/S³ 冪代表元上逐面及中間端點核驗，閉式 g⁻¹·(g·g) 正規化並與 g 連通而不同次數不誤判；結果只分類生成的閉代表式語言，不宣稱任意中性環路的 π₁/πₙ 分類、Eckmann–Hilton 或交換律",
    ),
    entry(
      "HOU 殘留約束集求解器（第十三期）",
      SpecOperator,
      [
        "HouResidualSolveReport", "hou_solve_constraints", "hou_unify_residual",
        "check_hou_residual_solver",
      ],
      "報告範形沿用 solved/no-unifier/residual/budget-exceeded 狀態，連同規範化替代、未解 HouConstraint、search_rounds 與 nodes/branches/depth 計數；宣告 solved 前逐條以替代重驗原約束集",
      "求解器在代換偏序中交錯 principal 片斷傳播與 Huet 分支搜尋：前者是 Miller-pattern 初始合一子的傳播，後者是在交易式候選樹中尋找同時滿足全體方程式的一個具體代換",
      "hou_unify_mgu 的 rigid-spine 殘差與 rigid+repeated-spine 雙約束可續解，純 principal 例 search_rounds=0；principal 賦值造成的後續 Bool 衝突給 no-unifier；猜測與其他約束相衝但無法證不可解時回 residual、節點預算不足回 budget-exceeded，失敗路徑回復輸入 unifier；搜尋成功只給 specific unifier，一般 HOU 不可判定性不變",
    ),
    entry(
      "工件 manifest 的 append-only 完整性鏈（第十三期）",
      SpecStructure,
      [
        "ArtifactChainEntry", "ArtifactChainReport", "artifact_repository_chain_entries",
        "artifact_repository_chain_head", "artifact_repository_chain_report", "artifact_repository_get_chained",
        "artifact_repository_recover_chained", "check_artifact_manifest_integrity_chain",
      ],
      "CHARTCHN 條目範形為 (sequence, removed, complete ArtifactRecord, previous_a/b, entry_a/b)，每次成功 put/remove 僅在既有鏈驗證後 fail-closed 追加；報告攜帶 entries、鏈頭雙雜湊、由 replay 得到的 live records 與其是否覆蓋 index",
      "鏈是命名工件狀態轉換序列的前條摘要連結歷史：recovery 是沿 put 蓋名、remove 寫 tombstone 的折疊，鏈頭是此歷史範疇在外儲存時的信任錨而非密碼簽章",
      "同 blob 兩名與同名覆寫得 entries=3/live=2，remove 後 entries=4/live=1 且 Some(舊鏈頭) 必須拒絕；index 遭毀時攜正確 expected_head 的 chained recovery 重建 live 狀態且 tombstone 不復活，舊鏈 replay、entry record-hash 竄改及 blob 竄改皆無效；無鏈 legacy index 在下一次 put 時先把既有兩筆 bootstrap 入鏈再追加自身（合計 entries=3/live=3）",
    ),
    entry(
      "聯合 Σ 動機同時歸納遞迴編譯（第十四期）",
      SpecOperator,
      [
        "simultaneous_ir_general_eliminator_type", "simultaneous_ir_compile_joint_block",
        "simultaneous_ir_compile_joint", "check_phase14_joint_simultaneous_ir_mutual",
      ],
      "範形為在單一基礎歸納族上的聯合 Σ 元組動機 Πx. f₀(x)×⋯×fₖ₋₁(x) 之單次消去器，各分量透過索引投影取得閉項表示，覆蓋雙向循環互遞迴、DFunctorSum 餘積函子與小／依賴上域（層級 ≤ base.level）",
      "互依同時函數組成的同步歸納遞迴結構同構於基礎初始代數到相依乘積族的唯一截面；foreign IH 沿嚴格正函子（含 Product/Sum/List/Pi）作投影提升，將交互遞迴收斂為單一高階消去",
      "雙向循環偶／奇互遞迴樹（F 與 G 互相前向／後向讀取葉槽與 Sum 槽 IH）及非宇宙依賴小上域皆編譯為受 dep_check_closed 接受的閉項且正規形與同時語義一致；超越基礎宇宙層級的 impredicative 上域或 DFunctorContainer/DecodedFunction 外來巢狀仍明示回 None",
    ),
    entry(
      "帶展開主體的正性見證證書（第十四期）",
      SpecStructure,
      [
        "DPositivityWitness", "dpositivity_witness", "dpositivity_witness_verify",
        "dterm_family_strictly_positive_certified", "check_phase14_positivity_witness_certificates",
      ],
      "見證範形為 DPositivityWitness{declaration, definition}，攜帶宣告的嚴格正／正引數槽與算子閉合展開主體；驗證後才可轉交極性遞迴",
      "把外部不透明算子的可信宣告提升為結構可重驗的語義見證：算子透過展開定義的變數極性像證明其為正性子範疇上的保極性自函子",
      "dpositivity_witness_verify 獨立檢查閉合性、無宇宙層級懸空變數、槽索引在界與不交，並將展開主體在通用引數脈絡下逐槽驗證極性：隱藏負出現（如 A→Nat）的偽造見證被拒，真實協變容器（如 A×B）見證通過並驅動誘導嚴格正性判定",
    ),
    entry(
      "DSystem 全部最大相容完成與有限閉型別 case-split（第十四期）",
      SpecOperator,
      [
        "DSystemRepairAllMaxima", "dsystem_repair_all_maxima", "cs_finite_closed_inhabitants",
        "conv_terms_finite_case_split_report", "conv_terms_finite_case_split", "check_phase14_dsystem_all_maxima_and_finite_case_split",
      ],
      "最大完成集範形為分支相容圖各連通分量最大團的笛卡兒積列舉連同衝突分量數、總最大完成數與預算旗標；有限 case-split 範形為空／單元／Bool／有限和積無遞迴閉歸納族的閉合居民窮舉樹與差異導引報告",
      "互不相交衝突分量的最大相容子系統分解為獨立團範疇的乘積；無遞迴有限型別在脈絡切片中同構於有限餘積，全體居民代入構成對離散有限假設的 η 外延決定程序",
      "雙獨立衝突對枚舉恰得 2×2=4 個不同最大相容系統且逐一通過相容檢查；三構造子 Fin3 歸納假設上的對稱查表等式以 4 次探針（1 次初始＋3 居民）通過，單一構造子不等對立即拒絕，Nat/List 等無限型別維持不切分",
    ),
    entry(
      "圓環語義座標範形與解耦 Torus 二維合成（第十四期）",
      SpecOperator,
      ["check_phase14_decoupled_torus_and_semantic_circle_norm"],
      "圓座標先經 De Morgan 代數吸收／冪等／互補律壓成規範型再產生雙序迭代選擇與無阻尼／阻尼聯集候選；Torus 二維方塊合成將兩圓環座標獨立解耦，各自獨立枚舉候選並逐面驗證",
      "T¹×T¹ 在立方範疇中為兩份 S¹ 的笛卡兒積，其開盒填充泛性質等價於兩投影分量在各自圓環纖維上的獨立合成見證；座標規範化消去句法冗餘而不混淆端點同定 0~1",
      "對角雙重繞行（兩座標同時在 tube 面上移動且各自沿不同邊界收束）的 Torus 方塊合成無須雙座標耦合即算得 DVPathLam 並逐面轉換至原雙重環路；語義等價但句法異形的圓座標壓成同一範形，僅點相等而無表達式帽的邊界仍誠實保留形式 DNComp",
    ),
    entry(
      "增量 intern DAG 差分與跨產物共用 DAG bundle（第十四期）",
      SpecStructure,
      [
        "DTermDagDelta", "DTermDagDeltaBinaryLoad", "dterm_intern_table_prefix_digest",
        "dterm_dag_delta_compute", "dterm_dag_delta_validate", "dterm_dag_delta_apply",
        "dterm_dag_delta_to_binary", "dterm_dag_delta_load_binary_report", "dterm_dag_delta_import_binary",
        "SharedDagBundle", "SharedDagBundleLoad", "shared_dag_bundle_to_binary",
        "shared_dag_bundle_load_binary_report", "check_phase14_incremental_dag_delta_and_shared_bundle",
      ],
      "CHDAGDLT v1 範形為基表前綴節點數、基表雙雜湊摘要、僅含新增拓撲節點的 delta_nodes 與新 roots；CHSHRBUN v1 將單一 v3 共用項池置於標頭，令多份編譯模組與 schema 註冊快照共享同一 DAG 表",
      "intern 表隨單調增長形成子圖包含鏈，增量差分是該包含態射的餘核補圖；跨產物 bundle 是把多個模組與註冊表函子同時拉回同一全局項商圖的極限包裝",
      "基表擴充後的增量 payload 嚴格小於全圖快照、匯入目標表後重組全部新舊 roots，基表摘要不符時在變更目標表前拒絕；含兩模組與註冊表的 CHSHRBUN 嚴格小於分開編碼總和，載入時同步重灌活 interner 且 reused_dag_nodes>0",
    ),
    entry(
      "Hensel 提升有理因式分解與全分解證書（第十四期）",
      SpecOperator,
      [
        "QPolyCertifiedFactor", "QPolyFactorCertificate", "qpoly_irreducible_upto3",
        "qpoly_factor_hensel", "qpoly_factor_certified", "qpoly_factor_certificate_check",
        "check_qpoly_hensel_factor_and_certificates", "check_phase14_qpoly_hensel_factor_and_certificates",
      ],
      "分解器對無平方因子本原多項式選無重根素數 p 作有限域 Berlekamp/Cantor–Zassenhaus 完全分解，經線性 Hensel 提升至超過 2·Mignotte 界之 p^k 後以常數項整除剪枝重組本原因子；全分解證書攜帶首項、帶重數不可約因子及各自不可約證書",
      "Z[x]→F_p[x]→Z/p^k Z[x] 為進位完備化局部化函子，Mignotte 係數界保證真因子可由局部不可約因子子集模對稱餘數唯一還原，免去指數級 Kronecker 整數除數笛卡兒積",
      "六次與八次複合多項式（兩個四次不可約因式乘積）秒級還原且每個因式皆附獨立可重驗不可約證書；qpoly_factor_certificate_check 重驗展開乘積、次數正性、兩兩互質與逐因式不可約證書，可約偽因式與篡改重數均被拒絕",
    ),
    entry(
      "六生成元多二次塔與實代數根式隔離算術（第十四期）",
      SpecStructure,
      [
        "RealAlgRadical", "multiquad_make_upto", "multiquad_align_upto", "multiquad_add_upto",
        "multiquad_mul_upto", "multiquad_eq_upto", "multiquad_sqrt_extended_upto",
        "radical_to_multiquad_upto", "real_alg_of_rat", "real_alg_sign", "real_alg_eq",
        "real_alg_neg", "real_alg_add", "real_alg_sub", "real_alg_mul", "real_alg_inv",
        "real_alg_div", "real_alg_nth_root", "radical_to_real_alg", "radical_equal_algebraic",
        "check_algebraic_radicals_and_rank6_multiquad", "check_phase14_algebraic_radicals_and_rank6_multiquad",
      ],
      "參數化多二次塔將無平方因子獨立生成元上限推至 6（64 維基底）；一般實根式範形為 RealAlgRadical{minpoly, root_index, lower, upper}，即本原不可約最小多項式連同 Sturm 唯一隔離有理區間",
      "實代數數體 Q̄∩ℝ 由結式（resultant）合成與無平方因子不可約因式分解封閉：加／乘／高次開方分別對應平移結式、尺度結式與 p(yⁿ) 的局部根隔離選擇，超越二次塔限制",
      "五獨立素數平方根 √2,…,√11 在六生成元塔內精確對齊與平方重驗；Pell 單位立方根恆等式 ∛(√2+1)·∛(√2-1)=1（涉及不可約 x⁶-2x³-1，二次塔與純三次體皆回 None）由 radical_equal_algebraic 精確判定為 Some(true)，微擾對判為 Some(false)，偶次負被開方數回 None",
    ),
    entry(
      "Hermitian 區塊去耦與重根消除 Jacobi 譜證書（第十四期）",
      SpecOperator,
      [
        "JacobiBlockDeflatedReport", "jacobi_block_components", "jacobi_block_deflated_eigen",
        "jacobi_block_deflated_certified", "check_jacobi_block_deflation_and_multiplicity",
        "check_phase14_jacobi_block_deflation_and_multiplicity",
      ],
      "先求 Hermitian 伴隨圖連通分量將矩陣正交直和分解為獨立子塊，對每子塊計算精確特徵多項式 f_B 並以無平方因子商 f_B/gcd(f_B,f_B') 消除重根，再結合 Sturm 隔離與因式次數差精確回填代數重數",
      "Hermitian 算子按不變正交子空間分解為區塊對角直和，其譜重數集為各子塊譜之多重集併；無平方因子化把非單根退化簇化約為單根分離問題，因式重數即特徵空間維數",
      "6×6 三重根加近似雙根區塊矩陣分解為兩個最大維數 3 的獨立子塊，無須 6×6 全矩陣 Sturm 展開即精確回報重數 3、1、1、1 且區間寬度全數小於 1/4096（target_met=true）",
    ),
    entry(
      "上界剪枝 BDD 最佳序與 CDCL DRAT／反向裁剪（第十四期）",
      SpecOperator,
      [
        "BddPrunedOptimalBuild", "bdd_dag_of_face_optimal_pruned", "FaceDrupTrimReport",
        "face_cdcl_drat_check", "face_cdcl_drup_trim", "check_phase14_bdd_bnb_and_cdcl_drat",
      ],
      "BDD 最佳序先以啟發式建構上界 incumbent，再於前綴子集 DP 中以累積寬度加剩餘支援集下界剪枝不可達狀態並將精確上限推至 18 變量；證明檢查器支援以首字面為 pivot 的單步解析環境蘊含（DRAT），並提供由空子句反向標記依賴的 DRUP 核心裁剪",
      "子集格上的 A*/branch-and-bound 在保持最優解下裁去超過上界的前綴錐；DRAT 的阻斷環境條件保存可滿足性等價（非蘊含），反向傳播依賴圖則是不可滿足性導出樹的最小活躍核心提取",
      "14 變量函數剪枝版與無剪枝 DP 得完全相同最小大小且 pruned_subsets>0，17 與 18 變量稀疏公式回 exact=true（19 起回 exact=false）；純 RAT 阻斷子句被 DRUP 拒絕但通過 DRAT 檢查，含冗餘引理的證明經 face_cdcl_drup_trim 嚴格縮減且裁剪後仍通過獨立 DRUP 重驗",
    ),
    entry(
      "宿主立方正交表覆蓋陣列探針（第十四期）",
      SpecOperator,
      [
        "DCubeCoveringReport", "dcube_cubes_conv_covering_report", "check_phase14_dcube_orthogonal_array_covering",
      ],
      "以有限射影直線 P¹(𝔽₈) 構造強度 t=3 的確定性正交表／覆蓋陣列探針集，配合 4 元非退化維度字母表 {0, 1, r₀, r₁∧¬r₂}，確保高維立方任三條座標軸的全部 4³=64 種組合皆被精確覆蓋",
      "正交表 OA(N; t, n, q) 是高維乘積格 Iⁿ 到全部 t 維座標投影皆滿射的有限截面族，以對數／多項式級探針數取代隨環境維度 n 指數爆炸的全格枚舉",
      "8 維立方（全 4 元格需 65536 點）僅用 ≤520 次探針即保證 complete_for_strength=true，精準揭穿僅在 (d₁=1 ∧ d₄=r₀ ∧ d₇=r₁∧¬r₂) 三軸交互處偏離的反例宿主立方，同時對相等 8 維立方全數通過",
    ),
    entry(
      "Eckmann–Hilton 交換 3-胞與 Mac Lane 五邊形 4-胞（第十四期）",
      SpecTheorem,
      [
        "dpath_square_boundary3_value", "dpath_lr_unit_coherence4_value", "dpath_eckmann_hilton3_value",
        "dpath_pentagon_top3_value", "dpath_pentagon_bot3_value", "dpath_pentagon_path_top3_value",
        "dpath_pentagon_path_bot3_value", "dpath_pentagon4_value", "check_phase14_eckmann_hilton_and_pentagon_coherence",
      ],
      "dpath_square_boundary3_value 將共用四角與四邊的兩個路徑方塊連接為頂邊間的 3-胞；據此組裝 refl⋅refl 上左右單位律重合 4-胞、Ω² 二階環路 α⋅β ≡ β⋅α 的 Eckmann–Hilton 3-胞，以及四段結合律五邊形兩條 3-胞路徑間的 Mac Lane 4-胞",
      "二階環路空間 Ω²(X) 由水平與垂直合成的互換律退化為交換 ∞-群胚；五邊形 4-胞與單位相干 4-胞則是道路廣群作為弱 ω-群胚在四維的雙么半群相干公理見證",
      "S³ 的 Ω² 非平凡面代表元上 Eckmann–Hilton 3-胞兩端轉換為 α⋅β 與 β⋅α 且側邊固定為基點；S² 四段環路複合上的五邊形上下兩條結合律 3-胞與連接兩者的 4-胞全部六個立方邊界面逐面通過型別化轉換核驗",
    ),
    entry(
      "圓的中性環路萬有覆疊截面與單值 Hopf 不變量（第十四期）",
      SpecTheorem,
      [
        "dpath_right_unit_general_value", "dpath_subst_trans_value", "circle_encode_decode_sect_value",
        "circle_self_loop_value", "circle_rot_equiv_value", "hopf_family_value",
        "hopf_connecting_loop_value", "hopf_invariant_value", "check_phase14_internal_circle_sect_and_hopf_invariant",
      ],
      "對任意閉圓環路值 p（含變數脈絡下的符號中性環路），由 J 消去結合一般右單位律與複合傳輸引理組裝內部路徑 decode(encode(p)) ≡ p；Hopf 纖維叢 H:S²→Type₀ 以圓自旋轉等價 rot:S¹→(S¹≃S¹) 經 ua 在懸掛子午線上黏合，對 Ω³(S²) 元素提取連接環路並經圓萬有覆疊求整數 Hopf 不變量",
      "circle_encode_decode_sect_value 完成合成同倫論 π₁(S¹)≃ℤ 的內部萬有覆疊截面方向；Brunerie 式單值 Hopf 構造實現纖維序列 S¹→S³→S² 在立方單值宇宙中的分類映射與同倫長正合連接同態 Ω³(S²)→Ω²(S²;H)≃Ω(S¹)→ℤ",
      "在自由環路變數 p:Path S¹ base base 的開放脈絡下，circle_encode_decode_sect_value(p) 的兩端點按型別轉換精確等於 decode(encode(p)) 與 p；內部單值 Hopf 不變量在 Ω³(S²) 的 0, 1, -1, 2 階代表元上精確算出規範整數 0, ±1, ∓1, ±2（反號對嚴格互為相反數且二倍元給 ±2）",
    ),
    entry(
      "高階合一跨約束回溯與有界合一子枚舉（第十四期）",
      SpecOperator,
      [
        "HouEnumerationReport", "hou_enumerate_unifiers", "hou_solve_constraints_backtracking",
        "check_phase14_hou_backtracking_and_enumeration",
      ],
      "枚舉報告範形為去重正規化代換陣列 solutions 連同 search_exhausted、capped 與節點／分支／深度統計；跨約束回溯器對整個約束集作交易式 DFS，某條殘差的第一個具體合一子若與後續約束衝突則自動回溯嘗試其餘候選分支",
      "非 pattern 高階合一無單一最一般合一子（MGU），其解空間為極小完備合一子集合（MCU）的有界截斷；跨約束回溯實現約束滿足樹上的和積搜尋而非單約束貪心承諾",
      "首個投影分支解掉首條方程卻令第二條方程失敗的雙約束系統（舊貪心殘差求解器停在 residual）由跨約束回溯器自動退回並找到共同解；雙投影歧義方程 ?F x x = Bool→Bool 枚舉出全部不等價閉合解且 search_exhausted=true，解數上限觸發時如實標記 capped=true",
    ),
    entry(
      "模組 TLV 向前相容封套、認證 CAS 與增量同步（第十四期）",
      SpecStructure,
      [
        "ModuleTlvSection", "CompiledModuleEnvelopeLoad", "compiled_module_envelope_to_binary",
        "compiled_module_envelope_load_binary", "ArtifactAuthKey", "ArtifactCasStatus",
        "ArtifactSyncReport", "artifact_repository_seal_authenticated", "artifact_repository_verify_authenticated",
        "artifact_repository_put_cas_authenticated", "artifact_repository_sync_incremental",
        "check_phase14_tlv_envelope_cas_and_incremental_sync",
      ],
      "CHMODENV v1 以核心 CHMODBIN v3 payload 搭配帶 critical 位元的 TLV 擴充節列；CHARTAUT v1 以雙秘密金鑰混合鏈頭與條目序列計算對稱 MAC 認證籤；增量同步比對來源與目標鏈前綴，只搬移缺失 blob 與新增鏈記錄",
      "TLV 的 critical/non-critical 分離實現編譯產物格式的向前相容投影態射；帶認證的 CAS（Compare-And-Swap）把單寫者儲存庫提升為具樂觀並行控制與防偽造錨點的線性化狀態機，增量同步則是單調歷史鏈的餘極限補齊",
      "含未知非關鍵 TLV 節的未來封套安全跳過並載入模組，含未知關鍵 TLV 節則 fail-closed 拒絕；錯誤金鑰或過期 expected_head 的 CAS 寫入分別回 AuthFailed 與 Conflict 且不污染儲存庫；增量同步跳過既有共同 blob（skipped_existing_blobs>0）、正確傳播 tombstone 並使兩庫認證鏈頭完全一致",
    ),
    entry(
      "對稱軌道剪枝與連通支援分解 BDD 精確最佳序（第十五期）",
      SpecOperator,
      [
        "BddDecomposedOptimalBuild", "bdd_dag_of_face_optimal_decomposed", "check_phase15_bdd_symmetry_orbit_and_decomposed_optimal",
      ],
      "先建立變量共現交互圖分解連通支援分量（移除不活躍死變量），對每個 ≤20 變量的分量執行帶 cofactor 對換對稱軌道剪枝的子集 DP，再按區塊拼接全局排列並重建共享 ROBDD",
      "互不相交變量支援的子函數具有張量／笛卡兒獨立性，其共享 ROBDD 最小節點數分解為各連通分量獨立最佳序之和；cofactor 對稱等價把前綴子集格商掉不改變後續寬度的變量置換軌道",
      "19 變量三組對稱對公式直接通過對稱軌道剪枝精確求解（exact=true, pruned_subsets>0）；28 變量四分量獨立支援公式分解為 4 個 ≤7 變量分量精確求解（exact=true），而 22 變量單一連通鏈誠實回退啟發式並標記 exact=false",
    ),
    entry(
      "索引化線性時間 LRAT 檢查器、DRAT→LRAT 精化與 CHLRATBN 編解碼（第十五期）",
      SpecOperator,
      [
        "FaceLratStep", "FaceLratElaborateReport", "face_cdcl_lrat_check",
        "face_cdcl_lrat_check_binary", "face_cdcl_elaborate_lrat", "face_lrat_to_binary",
        "face_lrat_from_binary", "check_phase15_cdcl_lrat_elaboration_and_binary_codec",
      ],
      "LRAT 步驟範形為單調遞增子句 ID 的 LratAdd(id, lits, rup_hints, rat_hints) 與 LratDelete(ids)；精化器反向標記空子句依賴核心、發射確定性傳播 ID 提示鏈與自動垃圾回收刪除；CHLRATBN v1 提供帶魔數與版本檢查的無損二進位編解碼",
      "DRAT→LRAT 精化是從無提示可滿足性保持證明空間到帶顯式見證索引鏈之局部可決定證明範疇的函子提升，消除檢查器端的全庫單位傳播搜尋",
      "PHP(6,5) 的 CDCL 證明與純 RAT 阻斷證明皆精化為通過線性時間 face_cdcl_lrat_check 的顯式提示鏈且自動產生 LratDelete；竄改提示 ID、刪去 RAT 見證或損毀 CHLRATBN 位元組均被檢查器拒絕",
    ),
    entry(
      "強度 4 射影覆蓋陣列、五色完美雜湊與宿主立方 Yoneda 審計（第十五期）",
      SpecOperator,
      [
        "CheckedDCube", "DCubeYonedaReport", "checked_dcube_make",
        "checked_dcube_closed", "checked_dcube_extensional_eq", "dcube_phf_5colors",
        "dcube_cubes_conv_covering_phf_report", "dcube_yoneda_audit_report", "check_phase15_dcube_strength4_phf_and_yoneda_audit",
      ],
      "以 P¹(𝔽₈) 三重傳遞 PGL₂(𝔽₈) 軌道建構強度 t=4 的 4 元正交覆蓋陣列並搭配五色覆蓋完美雜湊族 PHF；CheckedDCube 將維度立方錨定於受型別檢查的語法項，透過通用維度變數讀回實現精確外延等價",
      "立方範疇 □ 中可表預層 Hom_□(-, Iⁿ) 的自然變換由通用對角元 id_{Iⁿ} 唯一決定（立方 Yoneda 引理）；宿主閉包只有滿足維度代換自然性才屬於語義預層態射，CheckedDCube 則是由語法直接保證自然性的可表立方",
      "9 維立方四軸交互反例被 t=3 漏放但由 t=4 精確攔截（complete_for_strength=true）；讀回維度語法的病態非自然宿主閉包由 dcube_yoneda_audit_report 揭穿（natural=false），而自然閉包通過全部代換與忠實度審計且 CheckedDCube 給出無探針精確外延判定",
    ),
    entry(
      "一般雙向雙射認證、集合截斷萬有性與圓基本群 π₁(S¹)≃ℤ（第十五期）",
      SpecTheorem,
      [
        "dj_singleton_elim_value", "dpathp_of_transport_eq_value", "dpathp_eq_in_set_family_value",
        "equiv_compose_value", "equiv_bidirectional_certified_in", "equiv_bidirectional_certified",
        "dprop_is_set_value", "set_trunc_schema", "set_trunc_schema_at",
        "set_trunc_type_term", "set_trunc_type_value", "set_trunc_point_term",
        "set_trunc_point_value", "set_trunc_hub_value", "set_trunc_spoke_path_value",
        "set_trunc_loop_trivial_value", "set_trunc_is_set_value", "set_trunc_rec_set_value",
        "set_trunc_elim_prop_value", "set_trunc_elim_set_value", "set_trunc_equiv_of_equiv_set_value",
        "integer_succ_pred_sect_value", "integer_pred_succ_retr_value", "integer_is_set_value",
        "circle_encode_x_value", "circle_decode_step_value", "circle_decode_x_value",
        "circle_encode_decode_x_sect_with_zset_value", "circle_encode_decode_x_sect_value", "circle_decode_encode_x_retr_value",
        "circle_decode_encode_retr_value", "circle_path_equiv_cover_with_zset_value", "circle_path_equiv_cover_value",
        "circle_loop_space_equiv_integer_value", "pi1_set_circle_equiv_integer_value", "check_phase15_bidirectional_bijectivity_and_pi1_circle",
      ],
      "equiv_bidirectional_certified_in 在自由變數脈絡下驗證任意型別對 (A,B) 上雙向雙射資料 (f,g,η,ε) 經半伴隨化升級得到的 DVEquiv 與逆等價；集合截斷 ‖A‖₀ 由 hub/spoke 高階歸納型給出 h-set 證書與向任意 h-set 的萬有消去；ℤ 由觀察型別法（Hedberg／encode-decode）內證為 h-set，進而完成 π₁(S¹)=‖Ω¹(S¹)‖₀≃ℤ",
      "同倫雙射（具左逆截面與右逆收縮）經 Vogt 引理半伴隨校正典範提升為相干立方等價，並在單值性 ua 下誘導路徑等價；集合截斷是 ∞-群胚範疇到 0-群胚（h-set）反射子範疇的左伴隨函子，在目標已為 h-set 時把 Ω¹(S¹)≃ℤ 提升為基本群同構",
      "抽象宇宙變數脈絡 (A,B,f,g,s,r) 與依賴纖維上的雙向雙射認證、5 變數開放等價合成與 4 變數開放 ‖X‖₀≃B 皆通過轉換核驗；自由環路與自由整數脈絡下 encode/decode 雙向同倫成立，π₁(S¹)≃ℤ 的正反向對 0, ±1, ±2 計算精確往返",
    ),
    entry(
      "一般懸掛型別 Susp(A)、餘錐萬有性與基點環路—懸掛伴隨（第十五期）",
      SpecTheorem,
      [
        "empty_inductive_schema", "empty_inductive_type_value", "empty_inductive_elim_value",
        "susp_type_schema", "susp_type_schema_at", "susp_type_value",
        "susp_north_value", "susp_south_value", "susp_merid_path_value",
        "susp_bool_to_circle_value", "circle_to_susp_bool_value", "susp_bool_equiv_circle_value",
        "susp_cocone_type_value", "susp_universal_equiv_value", "based_map_type_value",
        "susp_based_to_cocone_equiv_value", "cocone_to_based_loop_equiv_value", "loop_suspension_adjunction_equiv_value",
        "check_phase15_suspension_and_loop_suspension_adjunction",
      ],
      "一般參數化懸掛 HIT SuspS(A) 由 north、south 與對任意 a:A 的子午線路徑 merid(a):north≡south 生成；餘錐萬有性給出 (Susp(A)→B)≃Cocone(A,B)，基點版在 south 單例收縮下收斂為 (ΣA→*B)≃(A→*ΩB)",
      "懸掛 Σ 為空間在單位點雙錐上的同倫推出（homotopy pushout），其映出態射空間由餘錐極限萬有性質分類；在基點類型範疇 Type* 中，懸掛函子 Σ 與環路空間函子 Ω 構成典範同倫伴隨對 Σ⊣Ω",
      "Susp(Bool)≃S¹ 雙向同倫以函數外延與懸掛消去在開放脈絡下核驗；非基點餘錐萬有等價與 5 自由變數基點環路—懸掛伴隨 (ΣA→*B)≃(A→*ΩB) 均建構為內部認證 DVEquiv 並通過雙向截面／收縮轉換檢查",
    ),
    entry(
      "0-連通懸掛基本群平凡化、圓楔連通與 Freudenthal 懸掛定理（第十五期）",
      SpecTheorem,
      [
        "circle_0_connected_value", "susp_0_connected_of_pointed_value", "freudenthal_pi1_susp_connected_equiv_unit_value",
        "pi1_susp_circle_equiv_unit_value", "pi1_susp2_circle_equiv_unit_value", "wedge_connectivity_circle_set_ext_value",
        "wedge_connectivity_circle_left_coh_value", "wedge_connectivity_circle_right_coh_value", "freudenthal_susp_loop1_to_loop2_value",
        "freudenthal_susp_loop1_preserves_refl_value", "check_phase15_freudenthal_suspension_and_wedge_connectivity",
      ],
      "對任意具 0-連通證書 c:Πx:A.‖x≡a₀‖₀ 的有基點型別 (A,a₀)，以依賴覆疊族 P(s):=(‖north≡s‖₀≡|refl_north|₀) 壓縮子午線差異並導出 ‖Ω¹(Susp(A))‖₀≃1；圓楔連通引理在 h-set 纖維上延長 S¹×S¹ 軸向截面並驗證雙軸相干；Freudenthal 一維懸掛映射 σ₁:Ω¹(S¹)→Ω²(Susp(S¹)) 以 merid(p(i))⋅merid(base)⁻¹ 給出並保單位環路",
      "0-連通空間的懸掛為 1-連通（Freudenthal 懸掛定理在 n=0 的穩定化起點），故高維球面基本群退化為平凡群；楔連通引理（Wedge Connectivity）是 Blakers–Massey／高階 Freudenthal 編碼在乘積空間上的對角餘推出分解基石",
      "在 4 自由變數脈絡下證明一般定理 ‖Ω¹(Susp(A))‖₀≃1，並實例化導出 π₁(S²)≃1 與 π₁(S³)≃1；開放 7 變數圓楔連通延伸及左右軸相干路徑、Freudenthal 環路懸掛映射保基點路徑與 Hopf 度數 k∈{-1,0,1} 對比全部通過核驗",
    ),
    entry(
      "大宇宙累積同時 IR、Dybjer–Setzer 開放同時 IR 與語義容器正性憑證（第十六期）",
      SpecStructure,
      [
        "simultaneous_ir_joint_motive_level", "DOpenIRArgKind", "DOpenIRArg",
        "dopen_arg_external", "dopen_arg_code", "dopen_arg_decoded_val",
        "dopen_arg_decoded_code_fn", "DOpenIRConstructor", "dopen_ir_constructor",
        "DOpenIRDecoder", "dopen_ir_decoder", "DOpenSimultaneousIRSpec",
        "dopen_simultaneous_ir_spec", "DOpenIRArgVal", "dopen_val_term",
        "dopen_val_code", "dopen_val_code_fn", "DOpenIRCode", "dopen_ir_intro",
        "open_ir_validate", "open_ir_check_code", "open_ir_eval_decode",
        "open_ir_elim_value", "open_ir_lower_single_decoder",
        "DFunctorPositivityEvidence", "DFunctorialPositivityCert",
        "dfunctorial_positivity_covariant_cert", "dfunctorial_positivity_container_cert",
        "dfunctorial_positivity_verify", "dterm_family_strictly_positive_functorial",
        "check_phase16_schema_large_open_positivity",
      ],
      "累積宇宙同時 IR 以 joint_motive_level = maxᵢ function_universe_level(fᵢ) 聯合編譯跨宇宙互賴區塊；Dybjer–Setzer 開放同時 IR DOpenSimultaneousIRSpec 承載多解碼器 (T₁,…,Tₘ) 與互賴函數式遞迴引數 (x : Tⱼ(a)) → U；語義正性憑證區分容器同構 Equiv(F X, Σs:S. P(s)→X)（授予嚴格正性）與協變函子律（僅授予非嚴格正性）",
      "累積宇宙中 Σ 型動機在最高分量宇宙層級統一打包大宇宙解碼器與小宇宙計數函數；開放歸納—遞迴族是多切片纖維範疇 Famₘ(Type) 上的同步初始代數；多項式容器範疇對嚴格正性自函子給出反循環語義刻畫",
      "El:Code→Type₀ 與依賴 El 的 size:Code→Nat 在 joint_level=1 聯合編譯並正規化；雙解碼器開放宇宙驗證、求值、依賴消去與單解碼器降階皆通過檢查；容器同構憑證拒絕 shape 偷渡循環引用，協變律憑證誠實拒絕嚴格正性遞迴位置",
    ),
    entry(
      "DSATUR 著色上界最大團修復與高維 0~1 黏合圓／環面開盒合成（第十六期）",
      SpecOperator,
      [
        "DSystemDsaturCliqueReport", "dsatur_color_order", "dsystem_repair_all_maxima_dsatur",
        "circle_path_winding_int", "CircleSquareWindingReport",
        "circle_square_glued_cap", "torus_square_glued_cap",
        "check_phase16_dsatur_and_glued_cubical_comp",
      ],
      "DSATUR 飽和度排序為每頂點賦予貪婪著色上界 c(v)，以 |C| + c(v) < best 剪枝 Bron–Kerbosch 枚舉全部最大相容子系統（強制開盒基底與分支兩兩轉換一致）；二維圓／環面開盒填充以 H-空間旋轉黏合計算零淨纏繞方塊帽，非零二上循環纏繞阻礙明示回傳 None",
      "相容圖的正常著色數 χ(G[P]) 是團數 ω(G[P]) 的偶圖上界；圓 S¹≃K(ℤ,1) 與環面 T²≃S¹×S¹ 的群胚 H-空間乘法把端點 0~1 黏合方塊邊界化約為整數纏繞數守恆條件 w(j=0)−w(j=1)+w(i=1)−w(i=0)=0",
      "6 分支相容圖以 DSATUR 著色上界精確枚舉全部最大團並統計剪枝節點；四邊皆為 loop 的零淨纏繞圓／環面方塊構造二維填充並逐邊通過轉換核驗，淨纏繞為 +1 的阻礙邊界精確拒絕",
    ),
    entry(
      "標準 SHA-256/512、RFC 8032 Pure-Ed25519 非對稱封緘與崩潰一致 WAL 日誌（第十六期）",
      SpecStructure,
      [
        "crypto_sha256", "crypto_sha256_hex", "crypto_sha512", "crypto_sha512_hex",
        "Ed25519PublicKey", "Ed25519Keypair", "Ed25519Signature",
        "ed25519_keypair_from_seed", "ed25519_sign", "ed25519_verify",
        "artifact_repository_seal_ed25519", "artifact_repository_verify_ed25519",
        "ArtifactWalRecoveryReport", "ArtifactWalStore", "artifact_wal_store_open",
        "artifact_wal_recover", "artifact_wal_begin_tx", "artifact_wal_put",
        "artifact_wal_delete", "artifact_wal_abort_tx", "artifact_wal_commit_tx",
        "artifact_wal_checkpoint", "artifact_wal_byte_store",
        "check_phase16_crypto_ed25519_and_wal",
      ],
      "FIPS 180-4 SHA-256/SHA-512 摘要；GF(2²⁵⁵−19) 扭曲愛德華曲線 −x²+y²=1+dx²y² 上 RFC 8032 Pure-Ed25519 64 位元組確定性簽章與 CHARTSIG 非對稱倉庫封緘（含公鑰固定、反高階扭轉與 S<L 防延展檢查）；CHWALJRN 預寫式交易日誌以 SHA-256 幀校驗保證重放冪等與斷尾回滾",
      "內容定址儲存的密碼學雜湊給出抗碰撞單射指紋；非對稱簽章把知識庫完整性錨定於唯讀公鑰驗證態射；預寫式日誌（WAL）是可失敗狀態轉移單子到原子冪等提交單子的伴隨實現",
      "NIST 空字串與 \"abc\" 雜湊及 RFC 8032 §7.1 Test 1/2 逐位元組吻合；竄改簽章、非規範標量 S≥L 與 blob 位元翻轉全數攔截；未提交交易加模擬斷電截尾幀經 recover 精確回滾並重放已提交狀態",
    ),
    entry(
      "精確有理 LLL 格約化、Van Hoeij 跡格因式重組與 Q̄⊂ℂ Rouché 圓盤代數閉包（第十六期）",
      SpecOperator,
      [
        "LllReductionReport", "rat_round_nearest_bigint", "qmat_lll_reduce",
        "qmat_is_lll_reduced", "QPolyLllFactorReport", "van_hoeij_lll_recombine",
        "qpoly_factor_lll", "ComplexAlgNum", "complex_alg_refine_disk",
        "complex_alg_of_rat", "complex_alg_i", "complex_alg_roots_of",
        "complex_alg_eq", "complex_alg_conj", "complex_alg_neg",
        "complex_alg_add", "complex_alg_sub", "complex_alg_mul",
        "complex_alg_inv", "complex_alg_div", "complex_alg_pow",
        "complex_alg_all_nth_roots", "complex_alg_eval_poly",
        "check_lll_lattice_and_van_hoeij_factor", "check_complex_algebraic_closure_rouche",
      ],
      "精確 BigInt 有理 Gram–Schmidt 與 δ=3/4 Lovász 條件輸出 LLL 約化基底與單模變換 U∈GLₙ(ℤ)；Van Hoeij 冪和跡格以 Fujiwara 根界構造 p-進痕跡約束格重組模因式；複代數數 ComplexAlgNum 以首一不可約極小多項式加不交 Rouché 隔離圓盤唯一呈現 Q̄⊂ℂ 元素",
      "格約化在自由 ℤ-模 GLₙ(ℤ) 軌道中選取近正交規範代表；Frobenius／Hensel 冪和線性關係刻畫 Galois 軌道因式重組子格；代數閉包 Q̄ 為有限分裂擴張正向極限並具備複嵌入拓撲圓盤分離",
      "病態斜格約化滿足尺寸約化、Lovász 不等式與 det(U)=±1；Swinnerton-Dyer S₃(x) 不可約性與八次平移乘積 S₂(x)·S₂(x−1) 在模分裂質數下零組合爆炸精確重組；x⁴+1、x³−2、√i 算術、共軛、逆元與韋達恆等式全部精確成立",
    ),
    entry(
      "纖維化環路序列等價、開放變量 Hopf–Freudenthal 收縮與五維 Stasheff K₅ 相干胞（第十六期）",
      SpecTheorem,
      [
        "pathp_equiv_transport_eq_value", "sigma_path_equiv_value",
        "sigma_cong_snd_equiv_value", "sigma_path_equiv_subst_value",
        "fibration_loop_equiv_fiber_path_value", "hopf_total_space_type_value",
        "hopf_total_loop_equiv_fiber_seq_value", "circle_rot_eval_base_eq_value",
        "sphere2_susp_loop1_to_loop2_value", "hopf_unit_subst_eq_value",
        "hopf_freudenthal_retraction_value", "hopf_invariant_susp_retraction_value",
        "pi2_s2_type_value", "pi2_s2_hopf_hom_value", "integer_to_pi2_s2_value",
        "pi2_s2_hopf_retract_sect_value", "dpath_k5_lhs1_value", "dpath_k5_rhs1_value",
        "dpath_k5_route_outer3_value", "dpath_k5_route_inner3_value",
        "dpath_k5_hemi_north4_value", "dpath_k5_hemi_south4_value",
        "dpath_associahedron_k5_cell5_value", "check_phase16_sphere_homotopy_and_k5",
      ],
      "依賴和路徑分裂與異質路徑傳輸等價合成為纖維化環路等價 Ω¹(ΣB P) ≃ Σ(p:Ω¹B).(subst P p e₀ ≡ e₀) 並實例化於單值 Hopf 全空間 E_Hopf；開放自由環路 p:Ω¹(S¹) 上構造 ∂_Hopf(σ_{S²}(p))≡p 二維同倫，導出 π₂(S²)=‖Ω²(S²)‖₀ 到 ℤ 的內部認證分裂收縮；五條路徑經 Stasheff 結合多面體 K₅ 構造南北雙五邊形路線間的五維相干填充胞",
      "纖維化序列 F→E→B 誘導長精確環路序列，Hopf 纖維化 S¹→E_Hopf→S² 的連接映射在懸掛環路上構成恆等收縮，刻畫 π₂(S²) 的自由循環生成元；A_∞ 環路空間在五重結合上的相干性由四維多面體 K₅ 的 5-胞分類",
      "開放 4 變數纖維化環路等價與閉項 Hopf 全空間環路等價皆通過 equiv_bidirectional_certified(_in) 全部 8 項雙向檢查；開放環路 Hopf–Freudenthal 收縮四角與開放整數 z:ℤ 分裂截面及閉項 k∈{-2,0,+2} 轉換成立；圓上五重非平凡環路的 K₅ 五維胞南北端點通過轉換核驗",
    ),
    entry(
      "Huet 延遲 flex-flex 約束圖、拉取式惰性合一串流、模組 DAG 介面雜湊重連結與三方倉庫合併（第十六期）",
      SpecStructure,
      [
        "HouFlexFlexEdge", "HouDelayedSolveStatus", "HouDelayedGraphReport",
        "hou_reify_delayed_flex_flex", "hou_solve_with_delayed_flex_flex",
        "HouLazyUnifierStream", "hou_unifier_stream_new", "hou_unifier_stream_is_exhausted",
        "hou_unifier_stream_nodes", "hou_unifier_stream_next",
        "ModuleBuildPlanReport", "module_topological_plan",
        "ModuleIncrementalBuildReport", "module_build_dag_incremental",
        "ArtifactMergePolicy", "artifact_merge_policy_abort",
        "artifact_merge_policy_prefer_left", "artifact_merge_policy_prefer_right",
        "ArtifactMergeConflict", "ArtifactThreeWayMergeReport",
        "artifact_repository_common_ancestor_records", "artifact_repository_merge_three_way",
        "check_phase16_hou_stream_and_module_merge",
      ],
      "Huet 預合一器把非 Miller pattern 的 flex-flex 約束滯留為約束圖邊並在端點約束實例化時自動喚醒；HouLazyUnifierStream 以顯式 continuation 堆疊按需逐一產出正規形合一子；模組系統拓樸規劃 DAG 並在不透明定義本體變更而公開介面雜湊不變時零重編譯下游並以 module_instantiate 重連結；倉庫三方合併沿 CHARTCHN 鏈找最近共同祖先（LCA）並執行內容收斂合併、墓碑傳播與衝突策略判定",
      "Huet 預合一範疇以滯留 flex-flex 等式為態射商、惰性串流為搜尋樹的餘代數展開；模組介面雜湊截止是從實作範疇到簽章範疇遺忘函子的商不變性；三方合併是偏序歷史圖上相對 LCA 的推出與衝突餘極限分析",
      "耦合 flex-rigid＋flex-flex 系統精確產出 2 條滯留預合一邊並可具現為閉合解；惰性串流首次拉取節點嚴格少於窮盡拉取；三層模組 DAG 在不透明修改時僅重編底層但重連結後頂層正規形翻轉，透明修改與循環依賴精確觸發重編／拒絕；三方合併驗證無衝突收斂、墓碑刪除與三種衝突策略",
    ),
    entry(
      "定理登記表與範例",
      SpecTheorem,
      [
        "CheckResult", "run_all_checks", "all_checks_pass", "print_report", "example_projector",
        "sample_terms", "check_projector", "check_eigenspace", "check_cube_comp",
        "check_nbe", "check_eta_all", "check_bdd_canonical", "check_glue_comp_all",
        "check_categories_all",
      ],
      "條目 (名稱, Bool)；全表 PASS 為總驗收範式",
      "每一條目是一條可判定命題在具體見證上的實現",
      "moon test 與 moon run cmd/main",
    ),
    entry(
      "規格登記自身",
      SpecStructure,
      [
        "SpecKind", "SpecEntry", "spec_registry", "spec_registry_sound", "spec_covers",
        "spec_count",
      ],
      "條目本身即 (名稱, 類別, 符號, 範形, 範疇, 判定) 六元組",
      "登記是「規格的規格」；完備性由 SPEC-APPENDIX 雙語附錄以多套件產生介面核對",
      "tools/audit_spec.py 逐符號審計",
    ),
  ]
}

///|
fn spec_symbol_count(reg : Array[SpecEntry], sym : String) -> Int32 {
  let mut count = 0
  for i in 0..<reg.length() {
    for k in 0..<reg[i].symbols.length() {
      if reg[i].symbols[k] == sym {
        count = count + 1
      }
    }
  }
  count
}

///|
/// The registry is sound: every entry fully specified, names unique, and
/// no symbol claimed by two entries.
pub fn spec_registry_sound() -> Bool {
  let reg = spec_registry()
  for i in 0..<reg.length() {
    let e = reg[i]
    if e.name == "" ||
      e.canonical == "" ||
      e.categorical == "" ||
      e.decision == "" ||
      e.symbols.length() == 0 {
      return false
    }
    for j in 0..<reg.length() {
      if i != j && reg[j].name == e.name {
        return false
      }
    }
    for k in 0..<e.symbols.length() {
      if spec_symbol_count(reg, e.symbols[k]) != 1 {
        return false
      }
    }
  }
  true
}

///|
pub fn spec_covers(sym : String) -> Bool {
  spec_symbol_count(spec_registry(), sym) >= 1
}

///|
pub fn spec_count() -> Int32 {
  spec_registry().length()
}
