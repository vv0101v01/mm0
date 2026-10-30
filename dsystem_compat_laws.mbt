///|
// Laws for raw-system compatibility and first-match tube normal forms.

///|
pub fn check_dsystem_compatibility() -> Bool {
  let line = (_ : Dim) => DVNatTy
  let compatible = DSystem::{
    branches: [
      tube_branch(FEq0(DVar(0)), _ => dv_nat_lit(0)),
      tube_branch(FEq1(DVar(0)), _ => dv_nat_lit(1)),
    ],
  }
  // The base is checked at dimension 0 on each branch face.  This
  // system is pairwise compatible (disjoint faces), but its second
  // branch does not agree with base 0, so only a different base or a
  // branch whose path starts at the base can compose.
  if !dsystem_pairwise_compatible(0, 1, line, compatible) {
    return false
  }
  let report = dsystem_compatibility_report(
    0,
    1,
    line,
    compatible,
    Some(dv_nat_lit(0)),
  )
  if report.compatible ||
    report.reason != DSystemBaseIncompatible ||
    report.branch != 1 {
    return false
  }
  let paths_from_zero = DSystem::{
    branches: [
      tube_branch(FEq0(DVar(0)), d => {
        if dim_is_one_sem_for_law(d) {
          dv_nat_lit(1)
        } else {
          dv_nat_lit(0)
        }
      }),
      tube_branch(FEq1(DVar(0)), _ => dv_nat_lit(0)),
    ],
  }
  match dsystem_checked(0, 1, line, paths_from_zero, dv_nat_lit(0)) {
    Some(_) => ()
    None => return false
  }
  let branch_clash = DSystem::{
    branches: [
      tube_branch(FTop, _ => dv_nat_lit(0)),
      tube_branch(FEq0(DVar(0)), _ => dv_nat_lit(1)),
    ],
  }
  let clash = dsystem_compatibility_report(0, 1, line, branch_clash, None)
  if clash.compatible ||
    clash.reason != DSystemBranchesIncompatible ||
    clash.branch != 0 ||
    clash.other_branch != 1 {
    return false
  }
  // Face-relative conversion: loop_i is the base point under i=0.
  let circle : DValue = DVCircleTy
  conv_at_under_face(
    0,
    1,
    FEq0(DVar(0)),
    circle,
    DVCirclePoint(DVar(0)),
    DVCirclePoint(DZero),
  ) &&
  !conv_at_under_face(
    0,
    1,
    FTop,
    circle,
    DVCirclePoint(DVar(0)),
    DVCirclePoint(DZero),
  )
}

///|
fn dim_is_one_sem_for_law(d : Dim) -> Bool {
  dim_eq_sem(d, DOne)
}

///|
pub fn check_dsystem_first_match_nf() -> Bool {
  let line = (_ : Dim) => DVNatTy
  let raw = DSystem::{
    branches: [
      tube_branch(FEq0(DVar(0)), _ => dv_nat_lit(0)),
      tube_branch(FTop, _ => dv_nat_lit(1)),
      tube_branch(FEq1(DVar(0)), _ => dv_nat_lit(2)),
    ],
  }
  if dsystem_pairwise_compatible(0, 1, line, raw) {
    return false
  }
  let nf = dsystem_first_match_normal_form(0, 1, line, raw)
  // First-match: 0 on (i=0), then 1 on the remaining (i=1); the
  // third branch is fully shadowed.
  if nf.classes.length() != 2 || nf.undefined != BddZero {
    return false
  }
  let disjoint = dsystem_of_first_match_nf(nf)
  if !dsystem_pairwise_compatible(0, 1, line, disjoint) {
    return false
  }
  let same_first_match = DSystem::{
    branches: [
      tube_branch(FEq0(DVar(0)), _ => dv_nat_lit(0)),
      tube_branch(FEq1(DVar(0)), _ => dv_nat_lit(1)),
      tube_branch(FTop, _ => dv_nat_lit(2)),
    ],
  }
  if !dsystem_first_match_eq(0, 1, line, raw, same_first_match) {
    return false
  }
  // Regions round-trip through DNF faces.
  if bdd_of_face(face_of_bdd(nf.classes[0].region), 1) != nf.classes[0].region {
    return false
  }
  // First-match disjointification does not repair a genuine base
  // mismatch: the effective Nat branch still starts at 1, not 0.
  match dsystem_first_match_checked(0, 1, line, raw, dv_nat_lit(0)) {
    Some(_) => return false
    None => ()
  }
  // But a fully shadowed branch need not agree with anything.  On
  // the circle, loop and its inverse clash on (i=1), while after
  // first-match disjointification only the loop branch remains
  // effective there and both effective branches start at the base.
  let circle_line = (_ : Dim) => DVCircleTy
  let circle_raw = DSystem::{
    branches: [
      tube_branch(FEq0(DVar(0)), _ => DVCirclePoint(DZero)),
      tube_branch(FTop, j => DVCirclePoint(j)),
      tube_branch(FEq1(DVar(0)), j => DVCirclePoint(DNeg(j))),
    ],
  }
  if dsystem_pairwise_compatible(0, 1, circle_line, circle_raw) {
    return false
  }
  match
    dsystem_first_match_checked(
      0,
      1,
      circle_line,
      circle_raw,
      DVCirclePoint(DZero),
    ) {
    Some(system) => system.branches.length() == 2
    None => false
  }
}

///|
pub fn check_dsystem_repair_phase9() -> Bool {
  // Pruned BDD traversal agrees with the decision it implements.
  let report = conv_at_under_face_report(
    0,
    1,
    FEq0(DVar(0)),
    DVCircleTy,
    DVCirclePoint(DVar(0)),
    DVCirclePoint(DZero),
  )
  if !report.holds || report.pruned_nodes == 0 {
    return false
  }
  // The agreement region of a loop with its base point on the whole
  // face lattice is exactly (i = 0).
  let agreement = face_agreement_region(
    0,
    1,
    FTop,
    DVCircleTy,
    DVCirclePoint(DVar(0)),
    DVCirclePoint(DZero),
  )
  if agreement != bdd_of_face(FEq0(DVar(0)), 1) {
    return false
  }
  // Repair by restriction: a constantly-1 branch on the top face is
  // dropped against base 0, the agreeing branch is kept, and the
  // removed region is reported.
  let line = (_ : Dim) => DVNatTy
  let raw = DSystem::{
    branches: [
      tube_branch(FTop, _ => dv_nat_lit(1)),
      tube_branch(FEq0(DVar(0)), _ => dv_nat_lit(0)),
    ],
  }
  let repair = dsystem_repair_to_base(0, 1, line, raw, dv_nat_lit(0))
  repair.compatible &&
  repair.repaired_branches == 1 &&
  repair.base_removed_region == BddOne &&
  repair.system.branches.length() == 1
}
