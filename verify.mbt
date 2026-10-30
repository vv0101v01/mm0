///|
// The theorem registry: every requirement, as an executable check.
//
// Each entry returns a boolean computed from concrete instances, using
// only the public operations of the layers below.  Where the model is
// finite (face formulas, finite types) checks are exhaustive; where it
// is continuous (vectors, cubes) checks are equalities of explicit
// formulas verified on sample grids — the formulas themselves are the
// constructions (Kan filler, projector pruning), so the sample checks
// test the constructions' defining equations.

///|
pub(all) struct CheckResult {
  name : String
  ok : Bool
}

///|
/// Registry-level conjunction: every type family of the project has
/// a Kan structure.  This intentionally lives in the registry layer,
/// so the dependent-kernel layer does not depend upward on the
/// finite/vector Glue models.
pub fn check_kan_all_types() -> Bool {
  check_kan_dep_all() && check_glue_comp_all() && check_cube_comp()
}

///|
pub fn sample_vectors() -> Array[CVec] {
  [
    [cx_real(1.0), cx(0.0, 1.0), cx(2.0, -1.0)],
    [cx_zero(), cx_zero(), cx_zero()],
    [cx(-1.0, 2.0), cx(0.5, 0.25), cx(0.0, -3.0)],
    example_unit(),
    vec_e3(),
  ]
}

///|
pub fn grid() -> Array[Double] {
  [0.0, 0.25, 0.5, 0.75, 1.0]
}

///|
pub fn check_projector() -> Bool {
  let p = example_projector()
  is_hermitian(p) &&
  is_idempotent(p) &&
  is_projector(p) &&
  (mat_trace_re(p) - 1.0).abs() < 0.000001
}

///|
pub fn check_eigenspace() -> Bool {
  let p = example_projector()
  eigenspace_well_formed(p, sample_vectors()) &&
  pruning_is_retraction(p, sample_vectors()) &&
  is_projector(complement(p))
}

///|
pub fn check_commuting() -> Bool {
  let p = example_projector()
  let q = outer(vec_e3()) // orthogonal range: PQ = 0 = QP
  let r = outer([cx(inv_sqrt2(), 0.0), cx_zero(), cx(inv_sqrt2(), 0.0)])
  commuting_projectors_compatible(p, q) &&
  commuting_projectors_compatible(p, complement(p)) &&
  !mat_commutes(p, r) // non-commuting pair is detected as such
}

///|
pub fn check_interval_faces() -> Bool {
  let i0 = face_var0(0)
  let i1 = face_var1(0)
  let j0 = face_var0(1)
  interval_laws_hold(grid()) &&
  eval_dim(DZero, [0.5]) == 0.0 &&
  face_unsat(FBot, 2) &&
  face_eq_mod(FOr(i0, i0), i0, 2) &&
  face_unsat(FAnd(i0, i1), 2) &&
  face_le(FAnd(i0, j0), i0, 2) &&
  !face_le(i0, j0, 2) &&
  face_eq_mod(FAnd(FTop, i0), i0, 2)
}

///|
pub fn check_systems() -> Bool {
  let v1 : CVec = [cx_real(1.0), cx_zero(), cx_zero()]
  let v2 = vec_e3()
  let i0 = face_var0(0)
  let i1 = face_var1(0)
  let sys = system_of([
    branch(i0, v1),
    branch(i1, v2),
    branch(FAnd(i0, face_var0(1)), v1), // subsumed by branch 1
    branch(FAnd(i0, i1), v2), // unsatisfiable face
  ])
  let bad = system_of([branch(FTop, v1), branch(i0, v2)])
  let a = system_of([branch(i0, v1)])
  let b = system_of([branch(i1, v2)])
  let ext_ok = match system_extend_top(a, v1, 2) {
    Some(_) => true
    None => false
  }
  let ext_bad = match system_extend_top(a, v2, 2) {
    Some(_) => false
    None => true
  }
  system_compatible(sys, 2) &&
  !system_compatible(bad, 2) &&
  pruning_respects_quotient(sys, 2) &&
  prune_system(sys, 2).branches.length() == 2 &&
  union_commutes_mod(a, b, 2) &&
  compatibility_respects_quotient(sys, b, 2) &&
  ext_ok &&
  ext_bad
}

///|
pub fn check_cube_comp() -> Bool {
  let p = example_projector()
  let u = example_unit()
  let u2 = vec_scale(2.0, u)
  let u3 = vec_scale_c(cx(0.0, 1.0), u) // i·u, still in im P
  let u4 = vec_scale(3.0, u)
  let bottom = path_line(u, u2)
  let left = path_line(u, u3)
  let right = path_line(u2, u4)
  let filler = square_fill(bottom, left, right)
  open_box_wf(bottom, left, right) &&
  filler_respects_box(filler, bottom, left, right, grid()) &&
  face_maps_commute(filler, 0.0, 1.0) &&
  face_maps_commute(filler, 1.0, 0.0) &&
  eigenspace_kan_sound(p, bottom, left, right, grid()) &&
  path_trans_endpoints(bottom, path_line(u2, u3)) &&
  vec_approx_eq(path_start(path_sym(bottom)), u2) &&
  vec_approx_eq(path_end(path_sym(bottom)), u)
}

///|
pub fn check_kan_pruning() -> Bool {
  let p = example_projector()
  let u = example_unit()
  let bottom = path_line(u, vec_scale(2.0, u))
  let left = path_line(u, vec_scale_c(cx(0.0, 1.0), u))
  let right = path_line(vec_scale(2.0, u), vec_scale(3.0, u))
  pruning_repairs_filler(p, bottom, left, right, vec_e3(), grid())
}

///|
pub fn sample_terms() -> Array[Term] {
  [
    tm_id(),
    tm_const(),
    tm_swap(),
    TmApp(tm_id(), TmBool(true)),
    TmApp(TmApp(tm_const(), TmBool(true)), TmBool(false)),
    TmApp(tm_swap(), TmPair(TmBool(true), TmUnit)),
    TmCoeRefl,
    TmCoeUaSwap,
    TmApp(TmCoeUaSwap, TmPair(TmUnit, TmBool(false))),
    TmPair(TmFst(TmPair(TmBool(false), TmUnit)), TmUnit),
  ]
}

///|
pub fn check_nbe() -> Bool {
  let beta = TmApp(TmApp(tm_const(), TmBool(true)), TmBool(false))
  let open_term = TmPair(TmSnd(TmVar(0)), TmFst(TmVar(0)))
  nbe_single_valued(sample_terms(), 0) &&
  nbe_single_valued([open_term], 1) &&
  nf(beta, 0) == TmBool(true) &&
  def_eq(TmApp(tm_id(), TmBool(false)), TmBool(false), 0) &&
  nf(tm_swap(), 0) == tm_swap()
}

///|
pub fn check_coe_definitional() -> Bool {
  coe_rules_definitional() && swap_involutive_on_element()
}

///|
pub fn check_hoas() -> Bool {
  let terms = sample_terms()
  for i in 0..<terms.length() {
    if !hoas_roundtrip_term(terms[i], 0) {
      return false
    }
  }
  let beta_in_hoas = happ(hoas_swap_example(), HPair(HBool(true), HUnit))
  hoas_roundtrip_hoas(hoas_swap_example(), 0) &&
  hoas_roundtrip_hoas(hoas_const_example(), 0) &&
  hoas_to_term(0, hoas_swap_example()) == tm_swap() &&
  hoas_to_term(0, beta_in_hoas) == TmPair(TmUnit, TmBool(true))
}

///|
pub fn check_ua_coe() -> Bool {
  let iso = iso_swap(TyBool, TyUnit)
  let p = iso_to_path(iso)
  let x = PVPair(PVBool(true), PVUnit)
  iso_wf(iso) &&
  upath_left(p) == TyProd(TyBool, TyUnit) &&
  upath_right(p) == TyProd(TyUnit, TyBool) &&
  coe_computes(p) &&
  coe_upath(p, 0, 1, x) == PVPair(PVUnit, PVBool(true)) &&
  coe_computes(ua(equiv_bool_not())) &&
  equiv_wf(equiv_prod(equiv_bool_not(), equiv_swap(TyBool, TyUnit)))
}

///|
pub fn check_pathp_exchange() -> Bool {
  let e1 = equiv_bool_not()
  let e2 = equiv_id(TyUnit)
  let pp = pathp_prod(
    pathp_canonical(ua(e1), PVBool(true)),
    pathp_canonical(ua(e2), PVUnit),
  )
  swap_naturality(e1, e2) &&
  pathp_wf(pp) &&
  pp.at1 == PVPair(PVBool(false), PVUnit) &&
  pathp_prod_exchange_roundtrip(pp, e1, e2)
}

///|
pub fn check_glue() -> Bool {
  let g = GlueData::{
    base_ty: TyBool,
    partial_ty: TyBool,
    equiv: equiv_bool_not(),
    face: face_var0(0),
  }
  // not(true) = false: compatible on the face (i = 0).
  let good = make_glue(g, PVBool(true), PVBool(false), 1)
  let bad = make_glue(g, PVBool(true), PVBool(true), 1)
  let good_ok = match good {
    Some(e) => glue_sound(g, e, 1) && unglue(e) == PVBool(false)
    None => false
  }
  let bad_rejected = match bad {
    Some(_) => false
    None => true
  }
  // On the empty face there is no constraint: Glue[⊥ ↦ …] A behaves as A.
  let g_bot = GlueData::{
    base_ty: TyBool,
    partial_ty: TyBool,
    equiv: equiv_bool_not(),
    face: FAnd(face_var0(0), face_var1(0)),
  }
  let bot_ok = match make_glue(g_bot, PVBool(true), PVBool(true), 1) {
    Some(e) => glue_sound(g_bot, e, 1)
    None => false
  }
  good_ok && bad_rejected && bot_ok
}

///|
pub fn check_j() -> Bool {
  let fam = Family::{ fiber: _x => TyBool, }
  let p = refl_path(TyBool, PVBool(true))
  let ill = DiscPath::{
    ty: TyBool,
    lo: PVBool(true),
    hi: PVBool(false),
    point: _t => PVBool(true),
  }
  let ill_rejected = match j_elim_disc(fam, PVBool(false), ill) {
    Some(_) => false
    None => true
  }
  j_roundtrip(fam, PVBool(false), p) && ill_rejected
}

///|
/// Transport in a constant family respects, and is respected by, the
/// orthogonal eigenspace decomposition: decompose, transport each
/// component (identity, in a constant family), recompose — the round-trip
/// is the identity and the two directions stay orthogonal throughout.
pub fn check_orthogonal_roundtrip() -> Bool {
  let p = example_projector()
  let samples = sample_vectors()
  for s in 0..<samples.length() {
    let v = samples[s]
    let (v1, v0) = decompose(p, v)
    if !vec_orthogonal(v1, v0) {
      return false
    }
    // forth: split; back: recompose.  Each component is a fixed point of
    // its own projector, so the round-trip cannot drift between summands.
    let back = vec_add(mat_vec(p, v1), mat_vec(complement(p), v0))
    if !vec_approx_eq(back, v) {
      return false
    }
    if !vec_approx_eq(mat_vec(p, v0), vec_zero(v.length())) {
      return false
    }
  }
  true
}

///|
pub fn check_registry() -> Array[(String, () -> Bool)] {
  [
    ("幂等 Hermitian 矩陣 P²=P, P†=P（正交投影）", fn () {
      check_projector()
    }),
    ("特徵空間良構性 Cⁿ=im(P)⊕ker(P)，特徵值 1/0，正交分解", fn () {
      check_eigenspace()
    }),
    ("可交換投影相容性 PQ=QP ⇒ PQ 為投影（不交換者被檢出）", fn () {
      check_commuting()
    }),
    ("區間 De Morgan 律與面公式商（蘊含／等價可判定）", fn () {
      check_interval_faces()
    }),
    ("系統商：剪枝保商、聯集可交換、相容性保商、擴張可行性判定", fn () {
      check_systems()
    }),
    ("立方體在區間上 comp：開盒填充邊界方程、面映射交換、路徑傳遞", fn () {
      check_cube_comp()
    }),
    ("特徵空間 Kan 纖維化剪枝：P∘fill 保持邊界並落入 im(P)", fn () {
      check_kan_pruning()
    }),
    ("NbE 單值性：nf(nf t)=nf t，定義相等由正規形判定", fn () {
      check_nbe()
    }),
    ("coe 定義相等：coe^refl ≡ id，coe^(ua swap) ≡ swap（NbE）", fn () {
      check_coe_definitional()
    }),
    ("HOAS 同構：往返一周 = NbE 正規形，正規形上嚴格相等", fn () {
      check_hoas()
    }),
    ("同構即相等 ua：Iso→Equiv→Path，coe 計得 equivFun（wiring 符號驗證）", fn () {
      check_ua_coe()
    }),
    ("PathP 積交換：swap∘(e₁×e₂)=(e₂×e₁)∘swap；PathP 積分解往返", fn () {
      check_pathp_exchange()
    }),
    ("Glue 可靠性：φ ⊢ equivFun(partial)=unglue；不相容 glue 被拒", fn () {
      check_glue()
    }),
    ("J 計算規則與往返：J(refl)=d 且沿 p、sym p 往返回 d", fn () {
      check_j()
    }),
    ("往返正交：常值族 transport 在 im(P)⊕ker(P) 分量正交且往返恆等", fn () {
      check_orthogonal_roundtrip()
    }),
    ("NbE 加 η：函數/積/單位 η 長正規形，swap∘swap ≡ id（函數層面）", fn () {
      check_eta_all()
    }),
    ("符號判定：面公式 ROBDD 規範形（sat/≤/≡ 不再枚舉 2ⁿ）", fn () {
      check_bdd_canonical()
    }),
    ("符號判定：有限等價 wiring 規範形（置換性、合成、逆，範疇＋相干性）", fn () {
      check_wiring_category() && check_wiring_coherence()
    }),
    ("一般 Glue comp：有限等價線端點算法＋子空間線開盒 hcomp 校正", fn () {
      check_glue_comp_all()
    }),
    ("範疇化：Karoubi／面偏序／立方體範疇／句法笛卡兒閉範疇律", fn () {
      check_categories_all()
    }),
    ("規格登記健全：逐條範形/範疇/判定齊備，名稱與符號不重複", fn () {
      spec_registry_sound()
    }),
    ("依賴 NbE：Π/Σ 與累積宇宙 Typeᵢ，依賴代入與型別導向轉換/η", fn () {
      check_dep_all()
    }),
    ("Kan 結構全型別化：Π/Σ/Universe 的 coe/comp 遞迴，連同 LTy/Ty/子空間/Glue", fn () {
      check_kan_all_types()
    }),
    ("完全符號代數：特徵多項式、譜投影 Lagrange 公式恆等、仿射唯一填充恆等", fn () {
      check_symbolic_algebra_all()
    }),
    ("立方 AST：PathP、Nat/List 與 Circle/Torus 的語法、檢查、NbE 及依賴消去", fn () {
      check_ast_paths() && check_ast_data() && check_ast_hits()
    }),
    ("Kan 項構造子：coe/comp/hcomp/hfill 與多分支系統在 AST 中計算，hcompU 產生 Glue", fn () {
      check_ast_kan_terms()
    }),
    ("hcomp 按型別化簡：Π 反變、Σ 沿填充、Path 端點分支、資料構造子、HIT 形式點與 Universe", fn () {
      check_ast_kan_types()
    }),
    ("語義系統重構：持久共享環境、惰性求值、語義快取、DSystem 按值合併排序與多分支 Glue", fn () {
      check_phase5_semantic_systems()
    }),
    ("通用歸納族生成器：telescope、嚴格正性、Nat/Bool/List/Vec/Fin/Tree/W 的檢查、消去與 comp", fn () {
      check_generated_inductive_schemas()
    }),
    ("通用 HIT 生成器：0/1/2 維 cells、face 化簡、巢狀 PathP 消去、Circle/Segment/Torus 與同 cell comp", fn () {
      check_generated_hit_schemas()
    }),
    ("Schema 擴展：結構化正性、容器函子巢狀/互歸納/歸納遞迴、商 HIT、宇宙多態與任意維 cells", fn () {
      check_schema_extensions()
    }),
    ("原始 DSystem：面相對轉換判定相容性，first-match 系統有精確不交範形", fn () {
      check_dsystem_compatibility() && check_dsystem_first_match_nf()
    }),
    ("AST 一等 Equiv：Equiv/ua/GlueEquiv 的檢查、轉換、引文與 Kan 計算", fn () {
      check_equiv_ast()
    }),
    ("受檢查型別線與 schema 註冊：維度代換封閉、驗證與 telescope elaboration 快取", fn () {
      check_phase6_infrastructure()
    }),
    ("精確代數擴展：廣義特徵空間、Jordan 分解、代數數與根式範形", fn () {
      check_algebraic_extensions_and_Jordan()
    }),
    ("BDD DAG 與認證數值：hash-consing/預算/DPLL，精確投影與多項式填充證書", fn () {
      check_bdd_and_certified_numeric()
    }),
    ("球面 S³：S¹ 兩次懸掛 HIT，meridian 端點、依賴消去與 hcomp", fn () {
      check_sphere3()
    }),
    ("Jacobi 譜迭代：每次酉旋轉的符號區間包含證書與 Gershgorin 特徵區間", fn () {
      check_Jacobi_interval()
    }),
    ("高階合一 elaborator：Miller pattern 求解隱含引數與 Nat motive，核心編譯至 DTerm", fn () {
      check_hou_elaborator()
    }),
    ("參數化模組：函子實例化抽象整段宣告，import/open/alias/rename 與歧義拒絕", fn () {
      check_module_system()
    }),
    ("立方體演算法：transport/filler、路徑代數、funext、subst 與 Kan box", fn () {
      check_cubical_algorithms()
    }),
    ("計算性單值性：ua/pathToEquiv、uaβ、兩條往返同倫與 Glue 方塊", fn () {
      check_univalence()
    }),
    ("精確代數完備化：Q 因式分解、實複根隔離、分裂域、去巢與任意精度 Jacobi", fn () {
      check_qpoly_factor_complete() &&
        check_root_isolation() &&
        check_splitting_field() &&
        check_radical_denesting() &&
        check_Jacobi_arbitrary_precision()
    }),
    ("Schema 第九期：一等宇宙多態、透明算子正性、非均勻巢狀、原始互歸納、同時歸納遞迴與 HIT 移動維度", fn () {
      check_level_polymorphic_declarations() &&
        check_type_operator_positivity_extraction() &&
        check_nested_iter_datatype() &&
        check_mutual_declaration_positivity() &&
        check_simultaneous_induction_recursion() &&
        check_hit_moving_dimension_lift()
    }),
    ("原始 DSystem 第九期：面下剪枝轉換、合意區域、受限修復與命題截斷", fn () {
      check_dsystem_repair_phase9() && check_propositional_truncation()
    }),
    ("等價相干資料：improved counit、adjoint 三角形型別、fiber center、singleton 收縮與 GlueEquiv 引文保真", fn () {
      check_adjoint_equivalence_and_fibers() &&
        check_glue_equiv_quote_preserves_syntax()
    }),
    ("維度代換與持久註冊：裸 DLine／語義封閉代換、bucket hash-cons、snapshot/merge/manifest", fn () {
      check_dline_dimension_substitution() &&
        check_semantic_dimension_substitution() &&
        check_schema_registry_persistence()
    }),
    ("一般代數認證與 BDD DAG 原生操作：任意擴張投影／路徑、DAG eval/count/quantify 與 DPLL 總判定", fn () {
      check_certified_algebraic_numeric() &&
        check_bdd_dag_native_operations()
    }),
    ("球面同倫代表元：懸掛函子、整數度數映射、單位環路、極交換 S³ 等價資料與 Hopf 連結數", fn () {
      check_sphere_homotopy_representatives() && check_hopf_numeric()
    }),
    ("非 Miller HOU 片斷：重複變量、構造子 spine、相異 flex-flex 交集與受限同頭情形", fn () {
      check_hou_phase9_extensions()
    }),
    ("模組分離編譯：抽象宣告、已編譯介面連結、前綴特化與增量快取", fn () {
      check_module_compilation()
    }),
    ("一般 adjointification 與可收縮纖維：任意 quasi-inverse 的 lemIso 收縮與自動三角形", fn () {
      check_general_adjointification_and_contractible_fibers()
    }),
    ("有界 Huet 高階合一搜尋：imitation、projection、任意 rigid spine、同頭置換剪枝與交易式預算", fn () {
      check_hou_bounded_search()
    }),
    ("穩定模組二進位格式：版本標頭、checksum、全 DTerm/schema codec、解析驗證與連結", fn () {
      check_module_binary_format()
    }),
    ("極端成本優化：BDD sifting/cache、watched-literal DPLL 與 Karatsuba 精確多項式乘法", fn () {
      check_bdd_cost_optimizations() && check_qpoly_fast_arithmetic()
    }),
    ("核內整數與球面環路代表元：IntegerS、π₃ 商型別、懸掛環路生成元與代表元範式分類", fn () {
      check_sphere_loop_representatives_internal()
    }),
    ("Schema 跨家族函子與同時 IR 編譯：DFunctorFamily 巢狀實例化、gather 驗證與 simultaneous→decode 位置編譯", fn () {
      check_family_nested_functors() &&
        check_simultaneous_ir_compiled_decode() &&
        check_family_functor_persistence()
    }),
    ("原始 DSystem 面值合意與精確修復：雙端點合意面、exact repair、宿主不透明立方開盒與多項式立方填充", fn () {
      check_face_agreement_and_exact_repair() &&
        check_dcube_open_box_filler() &&
        check_poly_cubes()
    }),
    ("lemIso 一般點驗證與圓環面點值合成：中性點與中性路徑兩端的收縮、Circle/Torus De Morgan 點合成計算", fn () {
      check_lemiso_generic_points() && check_circle_torus_point_comp()
    }),
    ("註冊字節持久化與全域 hash-consing：CHREGBIN 往返與拒絕損壞、DTerm intern 子項共享且檢查/正規形不變", fn () {
      check_schema_registry_byte_persistence() && check_dterm_hash_consing()
    }),
    ("精確代數第十一期：自適應 mod-p 因式圖樣剪枝、雙二次域去巢與判等、Jacobi 特徵值簇分離", fn () {
      check_qpoly_mod_pattern_pruning() &&
        check_biquadratic_denesting() &&
        check_jacobi_cluster_separation()
    }),
    ("CDCL 子句學習與 BDD 精確最佳順序：1-UIP 斷言子句、Luby 重啟、全排列最優變量序恰勝啟發式", fn () {
      check_cdcl_clause_learning() && check_bdd_optimal_order_exact()
    }),
    ("圓的 encode/decode：helix 萬有覆疊（base↦ℤ、loop↦ua succ）、subst 繞數、整數消去環路冪與代表元往返轉換", fn () {
      check_circle_encode_decode()
    }),
    ("HOU 搜尋擴展與模組交錯遷移：深 imitation 與 identification、import/本地宣告交錯、v1→v2 遷移與 artifact store", fn () {
      check_hou_search_extensions() &&
        check_module_interleaved_items() &&
        check_module_binary_versions_and_store()
    }),
    ("第十二期 BDD/SAT：子集 DP 精確最佳變量序（n≤12）、CDCL LBD 子句刪除與 RUP 可驗證證明", fn () {
      check_bdd_optimal_order_dp() && check_cdcl_proof_and_reduction()
    }),
    ("第十二期 Schema：DFunctorSelfFamily 同規格非均勻遞迴（Bush）、真實 Self 參數型別、不透明算子正性宣告", fn () {
      check_self_family_and_gather_shapes() &&
        check_positivity_declarations()
    }),
    ("第十二期同時 IR eliminator 編譯：互賴函數塊編為同一 base 家族的 eliminator 閉項（函數層級嚴格低於 base 層級）", fn () {
      check_simultaneous_ir_eliminator_compilation()
    }),
    ("第十二期 DSystem：相關維度結構合意剪枝、exact repair 候選分支補入", fn () {
      check_dsystem_structural_agreement_and_supplementation()
    }),
    ("第十二期轉換與路徑合成：Bool 變量 case-split 轉換、Circle/Torus 路徑值 comp（一般座標讀法保留繞數）", fn () {
      check_case_split_conversion_and_path_comp()
    }),
    ("第十二期持久層與版本協商：抽象 artifact repository 原子提交與損壞復原、CHMODBIN v3/CHREGBIN v2 共享 DAG codec、peer 版本協商", fn () {
      check_artifact_repository_and_dag_codec()
    }),
    ("第十二期精確代數：不可約證書 fast path（Eisenstein 平移）、三次與三二次塔體、Jacobi 迭代內簇感知精化", fn () {
      check_qpoly_irreducibility_certificates() &&
        check_tower_fields() &&
        check_jacobi_cluster_aware_iteration()
    }),
    ("第十二期 HOU 語意：Miller pattern 主合一子（MGU）、無合一子與殘留約束三態", fn () {
      check_hou_pattern_mgu_and_residuals()
    }),
    ("第十二期宿主立方分層外延檢查：面內部、對角與連接層探針與分層開盒驗證", fn () {
      check_dcube_stratified_extensionality()
    }),
    ("第十二期球面代表元 3-胞與精確 Hopf：環路單位律連接旋轉 3-胞、Hopf 恆等式精確有理驗證", fn () {
      check_loop_unit_3cells_and_hopf_exact()
    }),
    ("第十三期 Schema 正性：SelfFamily 同規格自嵌參數嚴格正性以最小不動點判定，Bush 通過、phantom 不出現、深層負性傳播", fn () {
      check_self_family_positivity_fixpoint()
    }),
    ("第十三期同時 IR 巢狀 foreign IH：積／函數／積含 List 的 foreign bundle 經項層函子映射搬運並與同步語義一致", fn () {
      check_simultaneous_ir_nested_foreign()
    }),
    ("第十三期面下轉換相關維度下降：在合取八變量 parity 面下僅沿實際提及的 i9 探測，i9 自由時正確拒絕", fn () {
      check_conv_under_face_relevant_descent()
    }),
    ("第十三期 DSystem 最大相容補入：exact-restrict 後以相容圖最大團找出大小 3 最大集，勝過順序貪心的大小 2", fn () {
      check_dsystem_maximum_completion()
    }),
    ("第十三期 Circle/Torus 非點值 comp：逐候選驗證座標帽，方塊在 tube 面轉換為原 loop、端點閉合且內部為點值", fn () {
      check_circle_torus_square_comp()
    }),
    ("第十三期差異導引 Bool case-split：由兩側範形差異只切分真正不同的一個 Bool 變量，錯誤候選仍拒絕", fn () {
      check_difference_guided_case_split()
    }),
    ("第十三期 intern DAG 與位元組共圖：同一 DAG 經 CHDAGBIN 往返並逐節點匯入，第二次匯入新增 0、畸形前向邊預先拒絕", fn () {
      check_interned_dag_byte_sharing()
    }),
    ("第十三期聯合不可約證書：mod 2 的 [1,3] 與 mod 3 的 [2,2] 合併排除一次／二次因式，證書可攜帶且獨立重驗", fn () {
      check_qpoly_degree_pattern_certificates()
    }),
    ("第十三期多二次塔體：至多四個平方類獨立生成元的 16 維 Q 體、基底對齊、逆元、精確判號、同域與加一根開方", fn () {
      check_multiquadratic_tower()
    }),
    ("第十三期精確最佳 BDD 順序：增量 cofactor 子集 DP 擴至 n≤16，14 變量例 tried=114688，17 變量明示非精確", fn () {
      check_bdd_optimal_order_dp_extended()
    }),
    ("第十三期 CDCL DRUP：學習／刪除步驟在演進子句庫上時序核驗，已刪子句不可再用，PHP(6,5) 與 PHP(7,6) 證明對帳", fn () {
      check_cdcl_drup_proof_with_deletions()
    }),
    ("第十三期宿主立方分層 Tier D：逐軸深層連接探針揭穿舊層同形異值的立方，二維相等對共 105 探針", fn () {
      check_dcube_stratified_tier_d()
    }),
    ("第十三期自適應 Jacobi：包絡停滯時切換精確特徵多項式 Sturm 分離，仍以目標寬度分開 ±1/4096", fn () {
      check_jacobi_adaptive_exact_fallback()
    }),
    ("第十三期環路代數與球面分類：逆元、結合律與 sym 複合反同態 3-胞，閉代表式遞迴正規化至其次數典範字", fn () {
      check_loop_inverse_assoc_and_classification()
    }),
    ("第十三期 HOU 殘差求解器：principal MGU 傳播與 transactional 迭代加深搜尋交錯續解整個殘留約束集", fn () {
      check_hou_residual_solver()
    }),
    ("第十三期工件 manifest 完整性鏈：put/remove 以前條摘要連結成鏈，舊鏈頭、竄改與重播皆拒，銷毀 index 後以信任錨鏈頭復原", fn () {
      check_artifact_manifest_integrity_chain()
    }),
    ("第十四期可攜正性見證證書：定義展開核驗 DPositivityWitness，雙重否定非嚴格正性與負性偽證均被拒絕", fn () {
      check_phase14_positivity_witness_certificates()
    }),
    ("第十四期聯合 Σ 動機同時歸納遞迴：DFunctorSum 餘積函子與循環互遞迴小值域編譯至依賴核心並通過正規形核驗", fn () {
      check_phase14_joint_simultaneous_ir_mutual()
    }),
    ("第十四期 DSystem 全體最大相容集與有限型別分案轉換：無順序偏倚列舉全部最大團，Fin3 閉居留元自動分案並排除無限 Nat", fn () {
      check_phase14_dsystem_all_maxima_and_finite_case_split()
    }),
    ("第十四期語義圓周纏繞正規化與解耦環面 comp：loop·sym(loop) 語義歸零，T² 雙座標獨立選擇閉合方塊", fn () {
      check_phase14_decoupled_torus_and_semantic_circle_norm()
    }),
    ("第十四期增量 DAG 差分與跨格式共圖封包：CHDAGDLT 僅傳新增節點並驗基底摘要，CHSHRBUN 跨模組與註冊表共享項表", fn () {
      check_phase14_incremental_dag_delta_and_shared_bundle()
    }),
    ("第十四期 Hensel 提升有理因式分解：Swinnerton-Dyer 四次式與高次多項式經 p-adic 提升分解並攜無平方自由證書重驗", fn () {
      check_phase14_qpoly_hensel_factor_and_certificates()
    }),
    ("第十四期一般實代數根式與六生成元多二次塔：∛2、∜5、∛(1+√2) 精確算術判號與 64 維 Q(√2,…,√13) 逆元核驗", fn () {
      check_phase14_algebraic_radicals_and_rank6_multiquad()
    }),
    ("第十四期 Hermitian 分塊降維與高重數特徵認證：精確特徵多項式無平方分解結合 Sturm 根計數認證重數 [2,1,1]", fn () {
      check_phase14_jacobi_block_deflation_and_multiplicity()
    }),
    ("第十四期 BDD 下界剪枝與 CDCL DRAT／DRUP 精簡：18 變量交錯公式剪枝壓縮，八子句純 RAT 步驟核驗與後向刪除精簡", fn () {
      check_phase14_bdd_bnb_and_cdcl_drat()
    }),
    ("第十四期高維宿主立方 P¹(F₈) 覆蓋陣列探測：729 列三階正交覆蓋陣列揭穿 5 維三軸耦合不等價立方", fn () {
      check_phase14_dcube_orthogonal_array_covering()
    }),
    ("第十四期 Eckmann–Hilton 交換 3-胞與 Mac Lane 五邊形 4-胞：Ω²(S²) 二階環路交換同倫與四重結合兩路徑相干連通", fn () {
      check_phase14_eckmann_hilton_and_pentagon_coherence()
    }),
    ("第十四期圓周內部截面族與單值 Hopf 不變量：中性整數 encode(decode(n))=n 截面，S²→Type₀ Hopf 纖維化算出次數 0,1,-1,2", fn () {
      check_phase14_internal_circle_sect_and_hopf_invariant()
    }),
    ("第十四期跨約束回溯 HOU 與完備正規形枚舉：非 pattern 雙約束回溯避開衝突投影，有界窮盡枚舉全部正規形合一子", fn () {
      check_phase14_hou_backtracking_and_enumeration()
    }),
    ("第十四期 TLV 前向相容封裝與鑑別式 CAS 增量同步：未知非關鍵區段安全略過、關鍵區段拒絕，MAC 鏈防偽與增量同步僅傳缺頁", fn () {
      check_phase14_tlv_envelope_cas_and_incremental_sync()
    }),
    ("第十五期對稱軌道 BDD 最優序與連通分量分解：19 變量軌道剪枝精確最佳化，28 變量四分量加性下界精確分解並誠實拒絕 22 變量單鏈", fn () {
      check_phase15_bdd_symmetry_orbit_and_decomposed_optimal()
    }),
    ("第十五期 CDCL LRAT 索引證明精煉與零搜尋核驗：PHP(6,5) 與八子句 RAT 編譯為 CHLRATBN v1，錯序提示與重用已刪子句皆拒", fn () {
      check_phase15_cdcl_lrat_elaboration_and_binary_codec()
    }),
    ("第十五期四階 PHF 覆蓋陣列與立方 Yoneda 外延審計：10 維四軸耦合偽立方揭穿、預層自然性檢驗與 24 維 CheckedDCube 單探針判等", fn () {
      check_phase15_dcube_strength4_phf_and_yoneda_audit()
    }),
    ("第十五期全滿單射雙向一般性核驗與圓基本群同構：開放反射變數認證 Ω¹(S¹)≃ℤ、萬有覆疊與 π₁(S¹)=‖Ω¹(S¹)‖₀≃ℤ，偽 refl 逆元皆拒", fn () {
      check_phase15_bidirectional_bijectivity_and_pi1_circle()
    }),
    ("第十五期多態懸掛與環路—懸掛伴隨雙向等價：SuspS(BoolS)≃S¹、無基點餘錐與開放帶點脈絡 Map*(SuspS A,B)≃Map*(A,ΩB)", fn () {
      check_phase15_suspension_and_loop_suspension_adjunction()
    }),
    ("第十五期一般 Freudenthal 懸掛定理與楔連通延拓：開放 0-連通脈絡認證 ‖Ω¹(SuspS A)‖₀≃1（含 π₁(S²)≃1、π₁(S³)≃1）、S¹∨S¹→S¹×S¹ 延拓與 Hopf 往返", fn () {
      check_phase15_freudenthal_suspension_and_wedge_connectivity()
    }),
    ("第十六期大宇宙累積同時 IR、Dybjer–Setzer 開放同時 IR 與語義容器正性憑證：跨宇宙聯合動機編譯、多解碼器開放規約與反循環容器同構核驗", fn () {
      check_phase16_schema_large_open_positivity()
    }),
    ("第十六期 DSATUR 著色上界最大團修復與高維 0~1 黏合圓／環面開盒合成：飽和度上界剪枝、二維圓與環面黏合方塊轉換及二上循環纏繞阻礙拒絕", fn () {
      check_phase16_dsatur_and_glued_cubical_comp()
    }),
    ("第十六期標準 SHA-256/512、RFC 8032 Pure-Ed25519 非對稱封緘與崩潰一致 WAL 日誌：NIST/RFC 向量逐位核驗、CHARTSIG 防偽與 CHWALJRN 斷尾回滾恢復", fn () {
      check_phase16_crypto_ed25519_and_wal()
    }),
    ("第十六期精確有理 LLL 格約化、Van Hoeij 跡格因式重組與 Q̄⊂ℂ Rouché 圓盤代數閉包：八次 Swinnerton-Dyer 因式重組與非實複代數根算術及韋達恆等式", fn () {
      check_lll_lattice_and_van_hoeij_factor() &&
        check_complex_algebraic_closure_rouche()
    }),
    ("第十六期纖維化環路序列等價、開放變量 Hopf–Freudenthal 收縮與五維 Stasheff K₅ 相干胞：開放脈絡 ∂_Hopf(σ_{S²}(p))≡p、π₂(S²) 分裂收縮 ℤ 與 K₅ 南北半球五維填充", fn () {
      check_phase16_sphere_homotopy_and_k5()
    }),
    ("第十六期 Huet 延遲 flex-flex 約束圖、拉取式惰性合一串流、模組 DAG 介面雜湊重連結與三方倉庫合併：按需枚舉、不透明實作零重編譯重連結與 LCA 三方衝突判定", fn () {
      check_phase16_hou_stream_and_module_merge()
    }),
  ]
}

///| 由登記表生成檢查結果（保留原本的公開介面）。
pub fn run_all_checks() -> Array[CheckResult] {
  let out : Array[CheckResult] = []
  for pair in check_registry() {
    let (name, f) = pair
    out.push(CheckResult::{ name, ok: f() })
  }
  out
}

///|
pub fn all_checks_pass() -> Bool {
  let results = run_all_checks()
  for i in 0..<results.length() {
    if !results[i].ok {
      return false
    }
  }
  true
}

///|
pub fn print_report() -> Bool {
  let results = run_all_checks()
  let mut passed = 0
  println("cubical-hermitian — 定理登記表")
  for i in 0..<results.length() {
    let r = results[i]
    if r.ok {
      passed = passed + 1
      println("[PASS] \{r.name}")
    } else {
      println("[FAIL] \{r.name}")
    }
  }
  println("passed \{passed}/\{results.length()}")
  passed == results.length()
}
