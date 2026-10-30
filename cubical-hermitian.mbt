// cubical-hermitian — a computational model, in MoonBit, of:
//   Hermitian idempotent matrices (orthogonal projectors) and their
//   orthogonal eigenspace decomposition, used as the retraction that
//   gives Kan filling for eigenspaces by pruning; cubical interval,
//   faces, systems modulo quotient, cubes and comp; NbE in three
//   layers (untyped beta-pi, typed eta-long, and dependent Pi/Sigma
//   over a cumulative universe hierarchy) with single-valued normal
//   forms deciding definitional equality, in which coe for refl and
//   ua computes definitionally; HOAS isomorphic to first-order syntax
//   on normal forms; symbolic decision on the finite side (ROBDD
//   faces, BDD system regions, wiring normal forms); Kan coe/comp
//   recursively through Pi/Sigma/Universe and every embedded type
//   family of the project; persistent shared environments, lazy
//   thunks and semantic caches; a cubical AST (PathP, Bool/Nat/List,
//   Circle/Torus, coe/comp/hcomp/hfill DSystems) whose compositions
//   reduce by type; multi-branch Glue partial systems; generic
//   inductive-family and HIT schema generation; general Glue composition over finite
//   equivalence lines and eigenspace lines; exact symbolic algebra
//   (characteristic polynomials, Lagrange spectral projectors, the
//   unique affine filler as polynomial identities); checked raw-system
//   compatibility, first-class AST equivalences and checked type lines;
//   exact rational/algebraic-extension linear algebra, generalized
//   eigenspaces and Jordan decompositions; interned DAG BDDs; certified
//   exact shadows of the numeric cube layer; and a per-symbol
//   canonical-form / categorification registry (SPEC.md).
//
// File map:
//   complex.mbt         C, CVec, CMat, adjoint, hermitian / idempotent
//   projector.mbt       eigenspace decomposition, commuting compatibility
//   interval.mbt        De Morgan interval, faces
//   bdd.mbt / bdd_dag.mbt tree-compatible faces; interned DAG ROBDD core
//   system.mbt          partial elements, pruning, quotient laws
//   system_symbolic.mbt BDD-region normal forms of systems
//   cube.mbt            cubes over I, open-box Kan comp, eigenspace pruning
//   nbe.mbt             syntax / higher-order semantics, beta-pi NbE, HOAS
//   nbe_eta.mbt         typed NbE with eta, syntactic CCC arrows
//   nbe_dep.mbt         dependent cubical NbE: Pi/Sigma, universes,
//                       PathP, data and HIT syntax over dimensions
//   kan_dep.mbt         DLine Kan structures for the dependent types
//   kan_ast.mbt         type-directed comp/hcomp/hfill/coe for the AST
//   ast_laws.mbt        Path/data/HIT and per-type Kan reduction laws
//   schema.mbt          generic inductive-family and HIT schema generation
//   schema_laws.mbt     laws for generated families/HITs and their comp
//   schema_extensions.mbt mutual/quotient/universe schemes, high-dim HITs
//   dsystem_compat.mbt  raw DSystem compatibility and first-match forms
//   equiv_ast.mbt       first-class AST Equiv, ua and GlueEquiv
//   conv_case_split.mbt Bool case-split strengthening of term conversion
//   artifact_repository.mbt named artifacts over an abstract byte store
//   checked_line.mbt / schema_registry.mbt checked lines; schema plans
//   qpoly.mbt / qmat.mbt exact univariate polynomials and rational matrices
//   algnum.mbt / Jordan.mbt algebraic extensions; generalized/Jordan theory
//   certified_numeric.mbt exact QuadC shadows of numeric projectors/cubes
//   sphere3.mbt         spheres by iterated HIT suspension, including S3
//   jacobi_interval.mbt certified Hermitian Jacobi interval iteration
//   hou_elaborator.mbt  Miller-pattern HOU and bidirectional elaboration
//   module_system.mbt   parameterized modules, imports/opens/namespaces
//   semantic_system_laws.mbt
//                       DSystem, environments, laziness/cache, multi-Glue
//   wiring.mbt          signed-permutation normal forms, monoidal coherence
//   pathp_glue.mbt      finite universe: ua, coe, PathP, Glue, J
//   glue_comp.mbt       general Glue comp (finite lines, subspace lines)
//   categories.mbt      Karoubi / face poset / cube category / syntactic CCC
//   symalg.mbt          exact polynomial algebra, symbolic matrices
//   spectral_symbolic.mbt spectral projectors, affine uniqueness identities
//   spec.mbt            canonical-form & categorification registry
//   verify.mbt          the theorem registry (run_all_checks / print_report)
