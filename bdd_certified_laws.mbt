///|
fn dim_xor_expr(a : Dim, b : Dim) -> Dim {
  DOr(DAnd(a, DNeg(b)), DAnd(DNeg(a), b))
}

///|
fn parity_face(n : Int32) -> Face {
  let mut acc = DVar(0)
  for i in 1..<n {
    acc = dim_xor_expr(acc, DVar(i))
  }
  FEq1(acc)
}

///|
fn equivalence_face(a : Int32, b : Int32) -> Face {
  FOr(FAnd(FEq1(DVar(a)), FEq1(DVar(b))), FAnd(FEq0(DVar(a)), FEq0(DVar(b))))
}

///|
fn check_bdd_dag_scalability() -> Bool {
  let parity = parity_face(8)
  let manager = bdd_manager_new(8)
  let root = bdd_dag_build_face(manager, parity)
  let nodes_after_parity = bdd_manager_node_count(manager)
  // Syntactically repeated copies of the same formula intern to the
  // same root and add no nodes.
  let mut repeated = parity
  for _i in 0..<12 {
    repeated = FAnd(repeated, repeated)
  }
  let repeated_root = bdd_dag_build_face(manager, repeated)
  let budget_ok = match face_eq_within_budget(parity, repeated, 8, 500) {
    FaceDecided(v) => v
    FaceBudgetExceeded => false
  }
  let budget_small = match face_eq_within_budget(parity, parity, 8, 3) {
    FaceDecided(_) => false
    FaceBudgetExceeded => true
  }
  let dpll_sat = match face_sat_dpll(FAnd(parity_face(4), FEq1(DVar(0))), 4) {
    FaceSat(env) => face_holds(FAnd(parity_face(4), FEq1(DVar(0))), env)
    _ => false
  }
  let dpll_unsat = match face_sat_dpll(FAnd(FEq0(DVar(0)), FEq1(DVar(0))), 2) {
    FaceUnsat => true
    _ => false
  }
  let paired = FAnd(
    equivalence_face(0, 3),
    FAnd(equivalence_face(1, 4), equivalence_face(2, 5)),
  )
  let identity_build = bdd_dag_of_face(paired, 6)
  let best = bdd_dag_of_face_best(paired, 6)
  let dpll_eq = match
    face_eq_dpll(
      FOr(FEq0(DVar(0)), FEq1(DVar(1))),
      FOr(FEq0(DVar(0)), FEq1(DVar(1))),
      2,
    ) {
    FaceDecided(v) => v
    FaceBudgetExceeded => false
  }
  root != 0 &&
  nodes_after_parity <= bdd_worst_case_nodes(8) &&
  repeated_root == root &&
  bdd_manager_node_count(manager) == nodes_after_parity &&
  manager.apply_hits > 0 &&
  budget_ok &&
  budget_small &&
  dpll_sat &&
  dpll_unsat &&
  dpll_eq &&
  best.built.ok &&
  bdd_dag_reachable_count(best.built.manager, best.built.root) <
  bdd_dag_reachable_count(identity_build.manager, identity_build.root) &&
  bdd_tree_of_dag(identity_build.manager, identity_build.root) ==
  bdd_of_face(paired, 6)
}

///|
fn cert_basis(i : Int32, n : Int32) -> CertVec {
  let v = cert_vec_zero(n)
  v[i] = qcc_one()
  v
}

///|
fn check_certified_projector() -> Bool {
  let u = cert_example_unit()
  let p = cert_example_projector()
  let cert = certify_projector(p)
  let e3 = cert_basis(2, 3)
  let mut decomposition = true
  for i in 0..<3 {
    let v = cert_basis(i, 3)
    let pv = cert_mat_vec(p, v)
    let qv = cert_mat_vec(cert_complement(p), v)
    if !cert_vec_eq(cert_vec_add(pv, qv), v) || !qcc_is_zero(cert_inner(pv, qv)) {
      decomposition = false
    }
  }
  let q = cert_outer(e3)
  let w : CertVec = [
    qcc_real(quad_sqrt_rat(rat_make(1, 2))),
    qcc_zero(),
    qcc_real(quad_sqrt_rat(rat_make(1, 2))),
  ]
  let r = cert_outer(w)
  let numeric = certify_numeric_projector(
    example_projector(),
    p,
    0.000000000001,
  )
  let interval_ok = match double_dyadic_interval(inv_sqrt2(), 20) {
    Some((lo, hi)) =>
      quad_to_double(quad_rat(lo)) <= inv_sqrt2() &&
      inv_sqrt2() <= quad_to_double(quad_rat(hi)) &&
      rat_eq(rat_sub(hi, lo), rat_make(1, 1048576))
    None => false
  }
  projector_certificate_ok(cert) &&
  qcc_eq(cert.trace, qcc_one()) &&
  cert_in_image(p, u) &&
  cert_in_kernel(p, e3) &&
  decomposition &&
  cert_is_projector(cert_mat_mul(p, q)) &&
  cert_mat_eq(cert_mat_mul(p, q), cert_mat_mul(q, p)) &&
  !cert_mat_eq(cert_mat_mul(p, r), cert_mat_mul(r, p)) &&
  numeric.ok &&
  numeric.numeric_residual < 0.000000001 &&
  interval_ok
}

///|
fn check_certified_kan() -> Bool {
  let p = cert_example_projector()
  let u = cert_example_unit()
  let u2 = cert_vec_scale(qcc_rat(rat_int(2), rat_zero()), u)
  let iu = cert_vec_scale(qcc_i(), u)
  let u3 = cert_vec_scale(qcc_rat(rat_int(3), rat_zero()), u)
  let bottom = cert_path_line(u, u2)
  let left = cert_path_line(u, iu)
  let right = cert_path_line(u2, u3)
  let filler = cert_square_fill(bottom, left, right)
  let corners_ok = cert_vec_eq(
      cert_path_start(cert_square_face(filler, 0)),
      cert_path_start(cert_square_face(filler, 2)),
    ) &&
    cert_vec_eq(
      cert_path_end(cert_square_face(filler, 0)),
      cert_path_start(cert_square_face(filler, 3)),
    ) &&
    cert_vec_eq(
      cert_path_end(cert_square_face(filler, 2)),
      cert_path_start(cert_square_face(filler, 1)),
    ) &&
    cert_vec_eq(
      cert_path_end(cert_square_face(filler, 3)),
      cert_path_end(cert_square_face(filler, 1)),
    )
  cert_filler_respects_box(filler, bottom, left, right) &&
  corners_ok &&
  cert_eigenspace_kan_sound(p, bottom, left, right) &&
  cert_pruning_repairs_filler(p, bottom, left, right, cert_basis(2, 3)) &&
  cert_vec_eq(cert_path_start(cert_path_sym(bottom)), u2) &&
  cert_vec_eq(cert_path_end(cert_path_sym(bottom)), u)
}

///|
pub fn check_bdd_and_certified_numeric() -> Bool {
  check_bdd_dag_scalability() &&
  check_certified_projector() &&
  check_certified_kan()
}
