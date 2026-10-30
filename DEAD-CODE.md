# DEAD-CODE：死碼與重複清冊（自動生成）

- 掃描：266 個 `.mbt`／155257 行
- 未被引用的 `pub fn`：**173**（多為 golden 併入的公開 API）
- 私有未被引用：**0**
- 跨套件同名定義：**21**

## 1. 跨套件同名定義（同一演算法多份實作）

| 名稱 | 出現在 |
|---|---|
| `Graph` | semiring/graph/graph.mbt, symlib/graph.mbt, symlib/random.mbt |
| `Perm` | symlib/perm.mbt, symlib/random.mbt |
| `ab_show` | coeff/ring.mbt, elim/core/core.mbt |
| `backend_name` | semiring/par/backend.mbt, semiring/par_host/backend_async.mbt |
| `build` | scheme/sheafification_affine_reduced.mbt, symlib/monad.mbt |
| `decompose` | elim/tensor/tensor.mbt, projector.mbt, symlib/decomp.mbt |
| `find` | cmd/symbench/derived.mbt, higher/sset.mbt, semiring/bp/factor.mbt, symlib/fincat.mbt |
| `go` | exact/algebra/qpoly_factor.mbt, exact/algebra/root_isolation.mbt |
| `main` | cmd/audit/main.mbt, cmd/main/main.mbt, cmd/semiringreport/main.mbt, cmd/showcase/main.mbt, cmd/symbench/main.mbt, cmd/symdemo/main.mbt |
| `mat_add` | complex.mbt, elim/core/core.mbt |
| `mat_from_rows` | complex.mbt, elim/core/core.mbt |
| `mat_get` | complex.mbt, elim/core/core.mbt |
| `mat_identity` | complex.mbt, elim/core/core.mbt |
| `mat_mul` | complex.mbt, elim/core/core.mbt |
| `par_for` | semiring/par/backend.mbt, semiring/par_host/backend_async.mbt |
| `rec` | symlib/csp.mbt, symlib/fincat.mbt, symlib/gset.mbt, symlib/yoneda.mbt |
| `search` | scheme/cycles_dual_points_categorify.mbt, topos/site_presheaf.mbt, topos/stacks_cohomology_homotopy.mbt |
| `shard_io_bench` | semiring/par/backend.mbt, semiring/par_host/backend_async.mbt |
| `smat_mul` | semiring/cat/setmat.mbt, super/score/score.mbt |
| `uf_find` | symlib/marks.mbt, topos/site_presheaf.mbt |
| `vec_scale` | complex.mbt, elim/core/core.mbt |

## 2. 未被引用的公開符號（前 60）

| 檔案 | 符號 |
|---|---|
| `topos/stacks_cohomology_homotopy.mbt` | `abelian_presheaf_constant_q` |
| `equivalence_phase9.mbt` | `adjoint_equiv_make` |
| `equivalence_phase9.mbt` | `adjoint_equiv_to_equiv` |
| `scheme/sheafification_affine_reduced.mbt` | `affine_nilpotent_witness` |
| `scheme/derived_structural_theorems.mbt` | `affine_singular_locus_ideal` |
| `certified_algebraic.mbt` | `alg_cert_mat_from_rows` |
| `certified_algebraic.mbt` | `alg_cert_vec_add` |
| `exact/algebra/algnum.mbt` | `alg_modulus_irreducible_small` |
| `exact/algebra/radical_denest.mbt` | `alg_to_quad` |
| `exact/algebra/algnum.mbt` | `alg_to_rat` |
| `certified_algebraic.mbt` | `algc_is_zero` |
| `certified_algebraic.mbt` | `algc_make` |
| `certified_algebraic.mbt` | `algc_sub` |
| `exact/algebra/algnum.mbt` | `algmat_add` |
| `semiring/app/closed.mbt` | `app_counts` |
| `semiring/app/closed.mbt` | `app_mostlikely` |
| `semiring/cat/dequant.mbt` | `argmin_k` |
| `symlib/partition.mbt` | `arr_less` |
| `symlib/decomp.mbt` | `aut_order_decomposed` |
| `bdd_dag.mbt` | `bdd_manager_stats` |
| `symlib/decomp.mbt` | `block_encoding_of` |
| `semiring/bp/factor.mbt` | `brute_force_max_product` |
| `symlib/dual.mbt` | `canon_encoding_dual` |
| `symlib/decomp.mbt` | `canonical_form_decomposed` |
| `symlib/report.mbt` | `canonical_labeling_m` |
| `certified_numeric.mbt` | `cert_path_const` |
| `certified_numeric.mbt` | `cert_projector_of_vector` |
| `certified_numeric.mbt` | `cert_square_eq` |
| `certified_numeric.mbt` | `cert_vec_to_numeric` |
| `checked_line.mbt` | `checked_fill_value` |
| `checked_line.mbt` | `checked_line_body` |
| `checked_line.mbt` | `checked_line_conv` |
| `checked_line.mbt` | `checked_line_of_pathp_term` |
| `checked_line.mbt` | `checked_pathp_type` |
| `exact/algebra/Jacobi_interval.mbt` | `cinterval` |
| `schema.mbt` | `darg_mutual_function` |
| `dcube_filler.mbt` | `dcube_degenerate` |
| `dcube_filler.mbt` | `dcube_of_point` |
| `nbe_dep.mbt` | `deval` |
| `semiring/nf/dfa.mbt` | `dfa_reverse` |
| `schema.mbt` | `dfunctor_const` |
| `schema.mbt` | `dfunctor_sigma` |
| `interval.mbt` | `dim_and` |
| `interval.mbt` | `dim_neg` |
| `interval.mbt` | `dim_one` |
| `interval.mbt` | `dim_or` |
| `interval.mbt` | `dim_zero` |
| `semiring/cat/setmat.mbt` | `distinct_witnesses` |
| `schema_extensions.mbt` | `dlevel_const` |
| `schema_extensions.mbt` | `dlevel_max` |
| `schema_extensions.mbt` | `dlevel_succ` |
| `schema_extensions.mbt` | `dlevel_var` |
| `cubical_algorithms.mbt` | `dpath_at_value` |
| `cubical_algorithms.mbt` | `dpath_refl_term` |
| `dsystem_compat.mbt` | `dsystem_checked_of` |
| `dsystem_compat.mbt` | `dsystem_compatibility` |
| `dterm_intern.mbt` | `dterm_intern_all` |
| `dterm_intern.mbt` | `dterm_intern_table_children` |
| `dterm_intern.mbt` | `dterm_local_stamp` |
| `dterm_intern.mbt` | `dterm_sharing_ratio` |

## 3. 守衛中止分佈

| 套件 | `abort(` |
|---|---|
| symlib | 98 |
| topos | 52 |
| scheme | 27 |
| semiring | 25 |
| (root) | 3 |
| cmd | 3 |

## 判定

- 「未被引用」≠ 死碼：golden 併入的公開 API 保留是**規格**，不是債。
- 真正的債是第 1 節：同名同義的實作散在 2–3 個套件（例：`vec_scale` 三份、`mat_vec` 三份、`sort_ints` 兩份）。
- 第七輪已刪掉 12 個真正沒人用的自家函式；基線見 `tools/dead_code_baseline.json`。
