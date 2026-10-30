///|
// Compatibility decisions and first-match normal forms for raw
// semantic tube systems.
//
// A host program can build a `DSystem` directly from arbitrary tube
// branches.  Such a system need not be compatible: branches can
// disagree on overlaps, or disagree with a proposed composition base
// at dimension 0.  This file provides the missing checked boundary:
//
//   * `conv_at_under_face` decides conversion relative to a face by
//     decomposing the face BDD into satisfying cubes, restricting
//     the quoted values to each cube, and re-checking conversion;
//   * `dsystem_compatibility_report` / `dsystem_checked` decide and
//     package composition compatibility with a base;
//   * `dsystem_first_match_normal_form` gives every raw tube system
//     a BDD effective-region normal form (previously only partial
//     values had one), and `dsystem_first_match_system` turns it
//     back into a pairwise-disjoint composition system.

///|
fn bdd_cubes_into(
  b : Bdd,
  assignment : Array[Int32],
  out : Array[Array[Int32]],
) -> Unit {
  match b {
    BddZero => ()
    BddOne => out.push(assignment)
    BddNode(v, lo, hi) =>
      if v >= 0 && v < assignment.length() {
        let lo_assignment : Array[Int32] = []
        let hi_assignment : Array[Int32] = []
        for i in 0..<assignment.length() {
          lo_assignment.push(assignment[i])
          hi_assignment.push(assignment[i])
        }
        lo_assignment[v] = 0
        hi_assignment[v] = 1
        bdd_cubes_into(lo, lo_assignment, out)
        bdd_cubes_into(hi, hi_assignment, out)
      }
  }
}

///|
/// The satisfying cubes of a BDD over variables `[0, n)`.  Each cube
/// is a partial assignment: 0, 1, or -1 for an unconstrained variable.
pub fn bdd_satisfying_cubes(b : Bdd, n : Int32) -> Array[Array[Int32]] {
  let assignment : Array[Int32] = []
  for _i in 0..<n {
    assignment.push(-1)
  }
  let out : Array[Array[Int32]] = []
  bdd_cubes_into(b, assignment, out)
  out
}

///|
/// A Face formula for a BDD region, in disjunctive normal form over
/// literal faces `(i = 0)` and `(i = 1)`.
pub fn face_of_bdd(b : Bdd) -> Face {
  match b {
    BddZero => FBot
    BddOne => FTop
    BddNode(v, lo, hi) =>
      face_simplify(
        FOr(
          FAnd(FEq0(DVar(v)), face_of_bdd(lo)),
          FAnd(FEq1(DVar(v)), face_of_bdd(hi)),
        ),
      )
  }
}

///|
fn fresh_term_env(level : Int32) -> DEnv {
  let values : Array[DValue] = []
  for i in 0..<level {
    values.push(DVNeutral(DNVar(level - 1 - i)))
  }
  denv_from_array(values)
}

///|
fn cube_dim_env(assignment : Array[Int32]) -> DDimEnv {
  let n = assignment.length()
  let values : Array[Dim] = []
  for i in 0..<n {
    let level = n - 1 - i
    values.push(
      if assignment[level] == 0 {
        DZero
      } else if assignment[level] == 1 {
        DOne
      } else {
        DVar(level)
      },
    )
  }
  ddim_from_array(values)
}

///|
/// Statistics and outcome of face-relative conversion.  The BDD of
/// the face is traversed with semantic pruning: as soon as the
/// values become convertible under the current partial dimension
/// assignment, the whole remaining sub-BDD is accepted without
/// enumerating its satisfying paths.
pub struct DFaceConvReport {
  holds : Bool
  nodes_visited : Int32
  pruned_nodes : Int32
  leaf_checks : Int32
}

///|
fn assignment_with(
  assignment : Array[Int32],
  variable : Int32,
  value : Int32,
) -> Array[Int32] {
  let out : Array[Int32] = []
  for i in 0..<assignment.length() {
    out.push(if i == variable { value } else { assignment[i] })
  }
  out
}

///|
fn restricted_terms_conv(
  level : Int32,
  dl : Int32,
  ty_term : DTerm,
  a_term : DTerm,
  b_term : DTerm,
  term_env : DEnv,
  assignment : Array[Int32],
) -> Bool {
  let denv = cube_dim_env(assignment)
  conv_at(
    level,
    dl,
    deval_dim(ty_term, term_env, denv),
    deval_dim(a_term, term_env, denv),
    deval_dim(b_term, term_env, denv),
  )
}

///|
fn bdd_avoid_var(b : Bdd, variable : Int32) -> Bdd {
  // The subdiagram of paths that never fix `variable`: paths
  // through a `variable` node are cut.  The diagram is
  // variable-ordered, so a subtree whose root variable exceeds
  // `variable` contains no `variable` node at all.
  match b {
    BddZero | BddOne => b
    BddNode(v, lo, hi) =>
      if v == variable {
        BddZero
      } else if v > variable {
        b
      } else {
        let l = bdd_avoid_var(lo, variable)
        let h = bdd_avoid_var(hi, variable)
        if l == BddZero && h == BddZero {
          BddZero
        } else {
          BddNode(v, l, h)
        }
      }
  }
}

///|
fn conv_relevant_walk(
  region : Bdd,
  rel_index : Int32,
  relevant : Array[Int32],
  assignment : Array[Int32],
  level : Int32,
  dl : Int32,
  ty_term : DTerm,
  a_term : DTerm,
  b_term : DTerm,
  term_env : DEnv,
  counters : Array[Int32],
) -> Bool {
  counters[0] = counters[0] + 1
  match region {
    BddZero => {
      counters[1] = counters[1] + 1
      true
    }
    _ =>
      if restricted_terms_conv(
          level, dl, ty_term, a_term, b_term, term_env, assignment,
        ) {
        // Convertible as open terms under the current partial
        // assignment: every path subcube below converts.
        counters[1] = counters[1] + 1
        true
      } else if rel_index >= relevant.length() {
        // Every dimension the quoted terms mention is decided
        // (assigned, or left free by every remaining path) and
        // the open check still fails.
        counters[2] = counters[2] + 1
        false
      } else {
        // Three-way split on the next relevant dimension:
        // paths fixing it to 0, paths fixing it to 1, and
        // paths not fixing it at all.  The third family is
        // what a naive endpoint split would leave uncovered
        // (interior points of that dimension); carrying it
        // explicitly keeps this decision equivalent to the
        // structural face-BDD descent while never splitting a
        // dimension the values do not mention.
        let variable = relevant[rel_index]
        conv_relevant_walk(
          bdd_tree_cofactor(region, variable, false),
          rel_index + 1,
          relevant,
          assignment_with(assignment, variable, 0),
          level,
          dl,
          ty_term,
          a_term,
          b_term,
          term_env,
          counters,
        ) &&
        conv_relevant_walk(
          bdd_tree_cofactor(region, variable, true),
          rel_index + 1,
          relevant,
          assignment_with(assignment, variable, 1),
          level,
          dl,
          ty_term,
          a_term,
          b_term,
          term_env,
          counters,
        ) &&
        conv_relevant_walk(
          bdd_avoid_var(region, variable),
          rel_index + 1,
          relevant,
          assignment,
          level,
          dl,
          ty_term,
          a_term,
          b_term,
          term_env,
          counters,
        )
      }
  }
}

///|
/// Conversion under the assumption that `face` holds, with search
/// statistics.  Globally convertible values pass immediately;
/// otherwise quoted values are restricted along a descent that
/// splits only the dimensions the quoted terms actually mention
/// (open conversion at each partial assignment prunes the whole
/// remaining subcube), so irrelevant face dimensions cost no
/// vertex probes.
pub fn conv_at_under_face_report_in(
  term_env : DEnv,
  level : Int32,
  dlevel : Int32,
  face : Face,
  ty : DValue,
  a : DValue,
  b : DValue,
) -> DFaceConvReport {
  if face_is_bot_sem(face) || conv_at(level, dlevel, ty, a, b) {
    return DFaceConvReport::{
      holds: true,
      nodes_visited: 0,
      pruned_nodes: 1,
      leaf_checks: 0,
    }
  }
  let face_vars = face_nvars_sem(face)
  let dl = if dlevel > face_vars { dlevel } else { face_vars }
  let region = bdd_of_face(face, dl)
  if region == BddZero {
    return DFaceConvReport::{
      holds: true,
      nodes_visited: 1,
      pruned_nodes: 1,
      leaf_checks: 0,
    }
  }
  let ty_term = quote_ty(level, dl, ty)
  let a_term = quote_at(level, dl, ty, a)
  let b_term = quote_at(level, dl, ty, b)
  let assignment : Array[Int32] = []
  for _i in 0..<dl {
    assignment.push(-1)
  }
  let counters : Array[Int32] = [0, 0, 0]
  let holds = conv_relevant_walk(
    region,
    0,
    agreement_relevant_vars(ty_term, a_term, b_term, dl),
    assignment,
    level,
    dl,
    ty_term,
    a_term,
    b_term,
    term_env,
    counters,
  )
  DFaceConvReport::{
    holds,
    nodes_visited: counters[0],
    pruned_nodes: counters[1],
    leaf_checks: counters[2],
  }
}

///|
pub fn conv_at_under_face_report(
  level : Int32,
  dlevel : Int32,
  face : Face,
  ty : DValue,
  a : DValue,
  b : DValue,
) -> DFaceConvReport {
  conv_at_under_face_report_in(
    fresh_term_env(level),
    level,
    dlevel,
    face,
    ty,
    a,
    b,
  )
}

///|
fn subcube_top(dl : Int32) -> Array[Int32] {
  let out : Array[Int32] = []
  for _i in 0..<dl {
    out.push(-1)
  }
  out
}

///|
fn subcube_subsumes(general : Array[Int32], specific : Array[Int32]) -> Bool {
  for i in 0..<general.length() {
    if general[i] != -1 && general[i] != specific[i] {
      return false
    }
  }
  true
}

///|
fn subcubes_push_irredundant(
  list : Array[Array[Int32]],
  cand : Array[Int32],
) -> Array[Array[Int32]] {
  for i in 0..<list.length() {
    if subcube_subsumes(list[i], cand) {
      return list
    }
  }
  let out : Array[Array[Int32]] = []
  for i in 0..<list.length() {
    if !subcube_subsumes(cand, list[i]) {
      out.push(list[i])
    }
  }
  out.push(cand)
  out
}

///|
fn subcubes_union(
  a : Array[Array[Int32]],
  b : Array[Array[Int32]],
) -> Array[Array[Int32]] {
  let mut out = a
  for i in 0..<b.length() {
    out = subcubes_push_irredundant(out, b[i])
  }
  out
}

///|
fn subcubes_meet(
  a : Array[Array[Int32]],
  b : Array[Array[Int32]],
  dl : Int32,
) -> Array[Array[Int32]] {
  let mut out : Array[Array[Int32]] = []
  for i in 0..<a.length() {
    for j in 0..<b.length() {
      let merged : Array[Int32] = []
      let mut ok = true
      for k in 0..<dl {
        let va = a[i][k]
        let vb = b[j][k]
        if va == -1 {
          merged.push(vb)
        } else if vb == -1 || va == vb {
          merged.push(va)
        } else {
          ok = false
          break
        }
      }
      if ok {
        out = subcubes_push_irredundant(out, merged)
      }
    }
  }
  out
}

///|
fn cubical_dim_eq_subcubes(
  r : Dim,
  target : Int32,
  dl : Int32,
) -> Array[Array[Int32]] {
  match r {
    DZero => if target == 0 { [subcube_top(dl)] } else { [] }
    DOne => if target == 1 { [subcube_top(dl)] } else { [] }
    DVar(v) =>
      if v < 0 || v >= dl {
        if target == 0 {
          [subcube_top(dl)]
        } else {
          []
        }
      } else {
        let c = subcube_top(dl)
        c[v] = target
        [c]
      }
    DNeg(a) => cubical_dim_eq_subcubes(a, 1 - target, dl)
    DAnd(a, b) =>
      if target == 1 {
        subcubes_meet(
          cubical_dim_eq_subcubes(a, 1, dl),
          cubical_dim_eq_subcubes(b, 1, dl),
          dl,
        )
      } else {
        subcubes_union(
          cubical_dim_eq_subcubes(a, 0, dl),
          cubical_dim_eq_subcubes(b, 0, dl),
        )
      }
    DOr(a, b) =>
      if target == 0 {
        subcubes_meet(
          cubical_dim_eq_subcubes(a, 0, dl),
          cubical_dim_eq_subcubes(b, 0, dl),
          dl,
        )
      } else {
        subcubes_union(
          cubical_dim_eq_subcubes(a, 1, dl),
          cubical_dim_eq_subcubes(b, 1, dl),
        )
      }
  }
}

///|
/// Irredundant maximal cubical subcubes of `f` in CCHM's De Morgan face
/// lattice `𝔽` (preserving proper boundary joins such as `(i = 0) ∨ (i = 1)`
/// as two distinct subcubes rather than collapsing them to the full cube).
pub fn cubical_face_subcubes(f : Face, dl : Int32) -> Array[Array[Int32]] {
  match f {
    FTop => [subcube_top(dl)]
    FBot => []
    FEq0(r) => cubical_dim_eq_subcubes(r, 0, dl)
    FEq1(r) => cubical_dim_eq_subcubes(r, 1, dl)
    FAnd(a, b) =>
      subcubes_meet(
        cubical_face_subcubes(a, dl),
        cubical_face_subcubes(b, dl),
        dl,
      )
    FOr(a, b) =>
      subcubes_union(cubical_face_subcubes(a, dl), cubical_face_subcubes(b, dl))
  }
}

///|
/// Exact CCHM face-relative conversion `Γ, φ ⊢ a ≡ b : ty` in typed term
/// environment `term_env`: decomposes `φ` into irredundant maximal subcubes
/// in `𝔽` and checks open conversion under each subcube substitution.
pub fn conv_at_under_face_in(
  term_env : DEnv,
  level : Int32,
  dlevel : Int32,
  face : Face,
  ty : DValue,
  a : DValue,
  b : DValue,
) -> Bool {
  if face_is_bot_sem(face) || conv_at(level, dlevel, ty, a, b) {
    return true
  }
  let face_vars = face_nvars_sem(face)
  let dl = if dlevel > face_vars { dlevel } else { face_vars }
  let cubes = cubical_face_subcubes(face, dl)
  if cubes.length() == 0 {
    return true
  }
  let ty_term = quote_ty(level, dl, ty)
  let a_term = quote_at(level, dl, ty, a)
  let b_term = quote_at(level, dl, ty, b)
  for i in 0..<cubes.length() {
    if !restricted_terms_conv(
        level,
        dl,
        ty_term,
        a_term,
        b_term,
        term_env,
        cubes[i],
      ) {
      return false
    }
  }
  true
}

///|
/// Conversion under the assumption that `face` holds.  For example,
/// a loop at dimension `i` and its base point are convertible under
/// `(i = 0)` but not globally.
pub fn conv_at_under_face(
  level : Int32,
  dlevel : Int32,
  face : Face,
  ty : DValue,
  a : DValue,
  b : DValue,
) -> Bool {
  conv_at_under_face_report(level, dlevel, face, ty, a, b).holds
}

///|
pub fn tube_paths_conv_under_face_in(
  term_env : DEnv,
  level : Int32,
  dlevel : Int32,
  face : Face,
  line : (Dim) -> DValue,
  p : (Dim) -> DValue,
  q : (Dim) -> DValue,
) -> Bool {
  let fresh = DVar(dlevel)
  conv_at_under_face_in(
    term_env,
    level,
    dlevel,
    face,
    line(DZero),
    p(DZero),
    q(DZero),
  ) &&
  conv_at_under_face_in(
    term_env,
    level,
    dlevel + 1,
    face,
    line(fresh),
    p(fresh),
    q(fresh),
  ) &&
  conv_at_under_face_in(
    term_env,
    level,
    dlevel,
    face,
    line(DOne),
    p(DOne),
    q(DOne),
  )
}

///|
/// Tube-path conversion under a face, at both endpoints and at a
/// fresh generic composition dimension.
pub fn tube_paths_conv_under_face(
  level : Int32,
  dlevel : Int32,
  face : Face,
  line : (Dim) -> DValue,
  p : (Dim) -> DValue,
  q : (Dim) -> DValue,
) -> Bool {
  tube_paths_conv_under_face_in(
    fresh_term_env(level),
    level,
    dlevel,
    face,
    line,
    p,
    q,
  )
}

///|
pub enum DSystemIncompatibility {
  DSystemOk
  DSystemBaseIncompatible
  DSystemBranchesIncompatible
} derive(Debug, Eq)

///|
pub extend DSystemIncompatibility with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend DSystemIncompatibility with Eq::{not_equal, equal}

///|
pub struct DSystemCompatibility {
  compatible : Bool
  reason : DSystemIncompatibility
  branch : Int32
  other_branch : Int32
} derive(Debug, Eq)

///|
pub extend DSystemCompatibility with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend DSystemCompatibility with Eq::{not_equal, equal}

///|
pub fn dsystem_compatibility(
  compatible : Bool,
  reason : DSystemIncompatibility,
  branch : Int32,
  other_branch : Int32,
) -> DSystemCompatibility {
  DSystemCompatibility::{ compatible, reason, branch, other_branch, }
}

///|
/// Decide whether branches agree pairwise on every satisfiable
/// overlap.  Bottom branches are ignored.
pub fn dsystem_pairwise_compatible(
  level : Int32,
  dlevel : Int32,
  line : (Dim) -> DValue,
  system : DSystem,
) -> Bool {
  dsystem_compatibility_report(level, dlevel, line, system, None).compatible
}

///|
pub fn dsystem_compatible_with_base_in(
  term_env : DEnv,
  level : Int32,
  dlevel : Int32,
  line : (Dim) -> DValue,
  system : DSystem,
  base : DValue,
) -> Bool {
  dsystem_compatibility_report_in(
    term_env,
    level,
    dlevel,
    line,
    system,
    Some(base),
  ).compatible
}

///|
/// Full composition compatibility: pairwise agreement on overlaps
/// and agreement of every branch with `base` at dimension 0 on its
/// face.
pub fn dsystem_compatible_with_base(
  level : Int32,
  dlevel : Int32,
  line : (Dim) -> DValue,
  system : DSystem,
  base : DValue,
) -> Bool {
  dsystem_compatible_with_base_in(
    fresh_term_env(level),
    level,
    dlevel,
    line,
    system,
    base,
  )
}

///|
pub fn dsystem_compatibility_report_in(
  term_env : DEnv,
  level : Int32,
  dlevel : Int32,
  line : (Dim) -> DValue,
  system : DSystem,
  base : DValue?,
) -> DSystemCompatibility {
  for i in 0..<system.branches.length() {
    let br = system.branches[i]
    if face_is_bot_sem(br.face) {
      continue
    }
    match base {
      Some(base_value) =>
        if !conv_at_under_face_in(
            term_env,
            level,
            dlevel,
            br.face,
            line(DZero),
            (br.path)(DZero),
            base_value,
          ) {
          return DSystemCompatibility::{
            compatible: false,
            reason: DSystemBaseIncompatible,
            branch: i,
            other_branch: -1,
          }
        }
      None => ()
    }
    for j in (i + 1)..<system.branches.length() {
      let other = system.branches[j]
      if face_is_bot_sem(other.face) {
        continue
      }
      let overlap = face_simplify(FAnd(br.face, other.face))
      if face_is_sat_sem(overlap) &&
        !tube_paths_conv_under_face_in(
          term_env,
          level,
          dlevel,
          overlap,
          line,
          br.path,
          other.path,
        ) {
        return DSystemCompatibility::{
          compatible: false,
          reason: DSystemBranchesIncompatible,
          branch: i,
          other_branch: j,
        }
      }
    }
  }
  DSystemCompatibility::{
    compatible: true,
    reason: DSystemOk,
    branch: -1,
    other_branch: -1,
  }
}

///|
/// Compatibility decision with the first mismatching branch (or pair
/// of branches) as a witness.
pub fn dsystem_compatibility_report(
  level : Int32,
  dlevel : Int32,
  line : (Dim) -> DValue,
  system : DSystem,
  base : DValue?,
) -> DSystemCompatibility {
  dsystem_compatibility_report_in(
    fresh_term_env(level),
    level,
    dlevel,
    line,
    system,
    base,
  )
}

///|
/// The checked composition-system constructor: Some(canonical
/// system) for a compatible raw system, None for an incompatible one.
pub fn dsystem_checked(
  level : Int32,
  dlevel : Int32,
  line : (Dim) -> DValue,
  system : DSystem,
  base : DValue,
) -> DSystem? {
  if dsystem_compatible_with_base(level, dlevel, line, system, base) {
    Some(dsystem_canonical(level, dlevel, line, system))
  } else {
    None
  }
}

///|
/// Checked constructor from raw branches.
pub fn dsystem_checked_of(
  level : Int32,
  dlevel : Int32,
  line : (Dim) -> DValue,
  branches : Array[DTubeBranch],
  base : DValue,
) -> DSystem? {
  dsystem_checked(level, dlevel, line, dsystem_of(branches), base)
}

// ---------------------------------------------------------------------------
// First-match normal form for tube systems
// ---------------------------------------------------------------------------

///|
pub struct DTubeNFClass {
  region : Bdd
  path : (Dim) -> DValue
}

///|
pub struct DTubeNF {
  classes : Array[DTubeNFClass]
  undefined : Bdd
}

///|
pub fn dtube_nf_class(region : Bdd, path : (Dim) -> DValue) -> DTubeNFClass {
  DTubeNFClass::{ region, path, }
}

///|
fn dsystem_nvars(system : DSystem, dlevel : Int32) -> Int32 {
  let mut n = dlevel
  for i in 0..<system.branches.length() {
    let m = face_nvars_sem(system.branches[i].face)
    if m > n {
      n = m
    }
  }
  n
}

///|
/// First-match BDD normal form of a raw tube system.  The effective
/// region of a branch is its face minus all earlier faces;
/// convertible paths merge and classes are sorted by quoted path.
/// No compatibility assumption is made.
pub fn dsystem_first_match_normal_form(
  level : Int32,
  dlevel : Int32,
  line : (Dim) -> DValue,
  system0 : DSystem,
) -> DTubeNF {
  let system = dsystem_of(system0.branches)
  let nvars = dsystem_nvars(system, dlevel)
  let regions : Array[Bdd] = []
  let fresh = DVar(dlevel)
  let line_fresh = line(fresh)
  let paths : Array[(Dim) -> DValue] = []
  let quoted : Array[DTerm] = []
  let body_keys : Array[String] = []
  let mut covered = BddZero
  for i in 0..<system.branches.length() {
    let br = system.branches[i]
    let all = bdd_of_face(br.face, nvars)
    let effective = bdd_and(all, bdd_not(covered))
    covered = bdd_or(covered, all)
    if effective == BddZero {
      continue
    }
    let q_i = quote_at(level, dlevel + 1, line_fresh, (br.path)(fresh))
    let key_i = dterm_cache_key(q_i)
    let mut merged = false
    for k in 0..<paths.length() {
      let same = if body_keys[k] == key_i {
        conv_at(level, dlevel, line(DOne), paths[k](DOne), (br.path)(DOne)) &&
        conv_at(level, dlevel, line(DZero), paths[k](DZero), (br.path)(DZero))
      } else if dterm_conv_plausible(quoted[k], q_i) {
        tube_paths_conv(level, dlevel, line, paths[k], br.path)
      } else {
        false
      }
      if same {
        regions[k] = bdd_or(regions[k], effective)
        merged = true
        break
      }
    }
    if !merged {
      regions.push(effective)
      paths.push(br.path)
      quoted.push(q_i)
      body_keys.push(key_i)
    }
  }
  let region_keys : Array[String] = []
  for i in 0..<paths.length() {
    region_keys.push(Repr(regions[i]).to_string())
  }
  for _pass in 0..<paths.length() {
    for j in 0..<(paths.length() - 1) {
      let swap = body_keys[j + 1] < body_keys[j] ||
        (
          body_keys[j + 1] == body_keys[j] &&
          region_keys[j + 1] < region_keys[j]
        )
      if swap {
        let tmp_region = regions[j]
        regions[j] = regions[j + 1]
        regions[j + 1] = tmp_region
        let tmp_path = paths[j]
        paths[j] = paths[j + 1]
        paths[j + 1] = tmp_path
        let tmp_body = body_keys[j]
        body_keys[j] = body_keys[j + 1]
        body_keys[j + 1] = tmp_body
        let tmp_region_key = region_keys[j]
        region_keys[j] = region_keys[j + 1]
        region_keys[j + 1] = tmp_region_key
      }
    }
  }
  let classes : Array[DTubeNFClass] = []
  for i in 0..<paths.length() {
    classes.push(DTubeNFClass::{ region: regions[i], path: paths[i], })
  }
  DTubeNF::{ classes, undefined: bdd_not(covered), }
}

///|
/// The pairwise-disjoint composition system represented by a
/// first-match normal form.  Regions are converted back to DNF faces.
pub fn dsystem_of_first_match_nf(nf : DTubeNF) -> DSystem {
  let out : Array[DTubeBranch] = []
  for i in 0..<nf.classes.length() {
    out.push(tube_branch(face_of_bdd(nf.classes[i].region), nf.classes[i].path))
  }
  DSystem::{ branches: out, }
}

///|
/// Disjointify a raw system under first-match semantics.  The result
/// is pairwise compatible by construction (its regions are disjoint),
/// regardless of whether the raw branches agreed on their overlaps.
pub fn dsystem_first_match_system(
  level : Int32,
  dlevel : Int32,
  line : (Dim) -> DValue,
  system : DSystem,
) -> DSystem {
  dsystem_of_first_match_nf(
    dsystem_first_match_normal_form(level, dlevel, line, system),
  )
}

///|
/// First-match disjointification followed by the base-compatibility
/// check: shadowed branches no longer need to agree with the base.
pub fn dsystem_first_match_checked(
  level : Int32,
  dlevel : Int32,
  line : (Dim) -> DValue,
  system : DSystem,
  base : DValue,
) -> DSystem? {
  let disjoint = dsystem_first_match_system(level, dlevel, line, system)
  if dsystem_compatible_with_base(level, dlevel, line, disjoint, base) {
    Some(disjoint)
  } else {
    None
  }
}

///|
/// Equality of raw tube systems under first-match semantics.
pub fn dsystem_first_match_eq(
  level : Int32,
  dlevel : Int32,
  line : (Dim) -> DValue,
  a : DSystem,
  b : DSystem,
) -> Bool {
  let na = dsystem_first_match_normal_form(level, dlevel, line, a)
  let nb = dsystem_first_match_normal_form(level, dlevel, line, b)
  if na.undefined != nb.undefined || na.classes.length() != nb.classes.length() {
    return false
  }
  for i in 0..<na.classes.length() {
    if na.classes[i].region != nb.classes[i].region ||
      !tube_paths_conv(
        level,
        dlevel,
        line,
        na.classes[i].path,
        nb.classes[i].path,
      ) {
      return false
    }
  }
  true
}

// ---------------------------------------------------------------------------
// Agreement regions and repair by restriction
// ---------------------------------------------------------------------------

///|
/// Dimension variables below `dl` on which conversion of the
/// quoted terms can depend: exactly those occurring in dimension
/// or face positions of the type and the two values.  The
/// agreement walks split only on these variables -- splitting a
/// dimension that occurs nowhere cannot change the conversion
/// outcome -- so their cost is exponential only in the number
/// of *relevant* dimensions (times the region traversal), not
/// in the ambient context size.
fn agreement_relevant_vars(
  ty_term : DTerm,
  a_term : DTerm,
  b_term : DTerm,
  dl : Int32,
) -> Array[Int32] {
  let acc : Array[Int32] = []
  let sources = [
    dterm_dim_vars(ty_term),
    dterm_dim_vars(a_term),
    dterm_dim_vars(b_term),
  ]
  for src in sources {
    for i in 0..<src.length() {
      // Quoted terms use de Bruijn dimension indices; face and
      // BDD variables (and hence assignments) use semantic
      // levels.  The two are related by `level = dl - 1 - index`
      // (see `dim_quote` / `cube_dim_env`).
      if src[i] >= 0 && src[i] < dl {
        let level = dl - 1 - src[i]
        if !contains_int(acc, level) {
          acc.push(level)
        }
      }
    }
  }
  @algebra.int_sort(acc)
}

///|
fn agreement_bdd_walk(
  region : Bdd,
  rel_index : Int32,
  relevant : Array[Int32],
  assignment : Array[Int32],
  level : Int32,
  dl : Int32,
  ty_term : DTerm,
  a_term : DTerm,
  b_term : DTerm,
  term_env : DEnv,
) -> Bdd {
  match region {
    BddZero => BddZero
    _ =>
      if restricted_terms_conv(
          level, dl, ty_term, a_term, b_term, term_env, assignment,
        ) {
        region
      } else if rel_index >= relevant.length() {
        // Every dimension the terms mention is assigned, and
        // the open check still fails: no assignment of the
        // remaining (unmentioned) dimensions can change it.
        BddZero
      } else {
        let variable = relevant[rel_index]
        let lo = bdd_tree_cofactor(region, variable, false)
        let hi = bdd_tree_cofactor(region, variable, true)
        let kept_lo = agreement_bdd_walk(
          lo,
          rel_index + 1,
          relevant,
          assignment_with(assignment, variable, 0),
          level,
          dl,
          ty_term,
          a_term,
          b_term,
          term_env,
        )
        let kept_hi = agreement_bdd_walk(
          hi,
          rel_index + 1,
          relevant,
          assignment_with(assignment, variable, 1),
          level,
          dl,
          ty_term,
          a_term,
          b_term,
          term_env,
        )
        // Reassemble with BDD apply so the result stays ordered
        // even though irrelevant variables were never split.
        let var0 = BddNode(variable, BddOne, BddZero)
        let var1 = BddNode(variable, BddZero, BddOne)
        if kept_lo == BddZero && kept_hi == BddZero {
          BddZero
        } else if kept_lo == kept_hi {
          // Agreement at both endpoints of a dimension does not
          // imply agreement in its interior, and a reduced BDD
          // cannot express the endpoint disjunction without
          // collapsing it to top.  Retain the 0-endpoint part.
          bdd_and(var0, kept_lo)
        } else {
          bdd_or(bdd_and(var0, kept_lo), bdd_and(var1, kept_hi))
        }
      }
  }
}

///|
/// A sound BDD agreement subregion of `face` (over the bounded
/// dimension context) on which `a` and `b` are convertible, found
/// by recursively restricting quoted values.  It is maximal along
/// every restriction path; if agreement holds at both endpoints of
/// a dimension but not in its interior, only the 0-endpoint part is
/// retained, because a reduced BDD cannot express that endpoint
/// disjunction without collapsing it to top.  Unlike a yes/no
/// decision, this returns the usable part of a partially agreeing
/// face.
pub fn face_agreement_region(
  level : Int32,
  dlevel : Int32,
  face : Face,
  ty : DValue,
  a : DValue,
  b : DValue,
) -> Bdd {
  let face_vars = face_nvars_sem(face)
  let dl = if dlevel > face_vars { dlevel } else { face_vars }
  let region = bdd_of_face(face, dl)
  if region == BddZero {
    return BddZero
  }
  if conv_at(level, dlevel, ty, a, b) {
    return region
  }
  let assignment : Array[Int32] = []
  for _i in 0..<dl {
    assignment.push(-1)
  }
  let ty_term = quote_ty(level, dl, ty)
  let a_term = quote_at(level, dl, ty, a)
  let b_term = quote_at(level, dl, ty, b)
  agreement_bdd_walk(
    region,
    0,
    agreement_relevant_vars(ty_term, a_term, b_term, dl),
    assignment,
    level,
    dl,
    ty_term,
    a_term,
    b_term,
    fresh_term_env(level),
  )
}

///|
pub struct DSystemRepair {
  system : DSystem
  base_removed_region : Bdd
  repaired_branches : Int32
  compatible : Bool
}

///|
/// Repair a raw system against a composition base by restriction:
/// every branch is first restricted to the subregion of its face
/// where its value at dimension 0 agrees with the base (branches
/// with no agreement region disappear), and the restricted system
/// is then first-match disjointified.  The removed region is
/// reported, so the change of domain is explicit rather than silent.
pub fn dsystem_repair_to_base(
  level : Int32,
  dlevel : Int32,
  line : (Dim) -> DValue,
  system : DSystem,
  base : DValue,
) -> DSystemRepair {
  let nvars = dsystem_nvars(system, dlevel)
  let restricted : Array[DTubeBranch] = []
  let mut removed = BddZero
  let mut repaired = 0
  for i in 0..<system.branches.length() {
    let br = system.branches[i]
    if face_is_bot_sem(br.face) {
      continue
    }
    let region = bdd_of_face(br.face, nvars)
    let agreement = face_agreement_region(
      level,
      dlevel,
      br.face,
      line(DZero),
      (br.path)(DZero),
      base,
    )
    if agreement != region {
      repaired = repaired + 1
      removed = bdd_or(removed, bdd_and(region, bdd_not(agreement)))
    }
    if agreement != BddZero {
      restricted.push(tube_branch(face_of_bdd(agreement), br.path))
    }
  }
  let disjoint = dsystem_first_match_system(
    level,
    dlevel,
    line,
    dsystem_of(restricted),
  )
  DSystemRepair::{
    system: disjoint,
    base_removed_region: removed,
    repaired_branches: repaired,
    compatible: dsystem_compatible_with_base(
      level, dlevel, line, disjoint, base,
    ),
  }
}

// ---------------------------------------------------------------------------
// Phase 11: exact (Face-valued) agreement regions and repair
// ---------------------------------------------------------------------------

///|
fn agreement_face_walk(
  region : Bdd,
  rel_index : Int32,
  relevant : Array[Int32],
  assignment : Array[Int32],
  level : Int32,
  dl : Int32,
  ty_term : DTerm,
  a_term : DTerm,
  b_term : DTerm,
  term_env : DEnv,
) -> Face {
  match region {
    BddZero => FBot
    _ =>
      if restricted_terms_conv(
          level, dl, ty_term, a_term, b_term, term_env, assignment,
        ) {
        // Convertible as open terms under the current partial
        // assignment: agreement holds on the whole remaining
        // subcube, interiors included.
        face_of_bdd(region)
      } else if rel_index >= relevant.length() {
        FBot
      } else {
        let variable = relevant[rel_index]
        let lo = bdd_tree_cofactor(region, variable, false)
        let hi = bdd_tree_cofactor(region, variable, true)
        let kept_lo = agreement_face_walk(
          lo,
          rel_index + 1,
          relevant,
          assignment_with(assignment, variable, 0),
          level,
          dl,
          ty_term,
          a_term,
          b_term,
          term_env,
        )
        let kept_hi = agreement_face_walk(
          hi,
          rel_index + 1,
          relevant,
          assignment_with(assignment, variable, 1),
          level,
          dl,
          ty_term,
          a_term,
          b_term,
          term_env,
        )
        let var_dim = DVar(variable)
        if kept_lo == FBot && kept_hi == FBot {
          FBot
        } else if kept_lo == FBot {
          face_simplify(FAnd(FEq1(var_dim), kept_hi))
        } else if kept_hi == FBot {
          face_simplify(FAnd(FEq0(var_dim), kept_lo))
        } else if kept_lo == kept_hi {
          // Both endpoints agree but the open check above failed,
          // so the interior is *not* claimed: the endpoint
          // disjunction `(i = 0) or (i = 1)` is retained exactly.
          // A reduced BDD cannot express this without collapsing
          // it to top, which is why the region is Face-valued.
          face_simplify(FAnd(FOr(FEq0(var_dim), FEq1(var_dim)), kept_lo))
        } else {
          face_simplify(
            FOr(FAnd(FEq0(var_dim), kept_lo), FAnd(FEq1(var_dim), kept_hi)),
          )
        }
      }
  }
}

///|
/// The exact agreement subregion of `face` on which `a` and `b`
/// are convertible, as a `Face` formula.  Where
/// `face_agreement_region` (BDD-valued) must drop the 1-endpoint
/// of a dimension whose two endpoints agree but whose interior
/// does not, this version retains the endpoint disjunction
/// `(i = 0) or (i = 1)`, so no agreeing part is lost.  Maximality
/// is along every restriction path, as with the BDD version.
pub fn face_agreement_face(
  level : Int32,
  dlevel : Int32,
  face : Face,
  ty : DValue,
  a : DValue,
  b : DValue,
) -> Face {
  let face_vars = face_nvars_sem(face)
  let dl = if dlevel > face_vars { dlevel } else { face_vars }
  let region = bdd_of_face(face, dl)
  if region == BddZero {
    return FBot
  }
  if conv_at(level, dlevel, ty, a, b) {
    return face
  }
  let assignment : Array[Int32] = []
  for _i in 0..<dl {
    assignment.push(-1)
  }
  let ty_term = quote_ty(level, dl, ty)
  let a_term = quote_at(level, dl, ty, a)
  let b_term = quote_at(level, dl, ty, b)
  agreement_face_walk(
    region,
    0,
    agreement_relevant_vars(ty_term, a_term, b_term, dl),
    assignment,
    level,
    dl,
    ty_term,
    a_term,
    b_term,
    fresh_term_env(level),
  )
}

///|
/// Independent soundness audit of an agreement face: the Boolean
/// region of `agreement` must be contained in that of `face`, and
/// at every vertex of the bounded dimension context where the
/// agreement face holds, the fully restricted values must be
/// convertible.  (Interior agreement is guaranteed constructively
/// by the open-conversion pruning inside the walk; this audit
/// re-checks the endpoint content exhaustively.)  Returns false
/// if the context is too large to enumerate (more than 20 dims).
pub fn face_agreement_face_sound(
  level : Int32,
  dlevel : Int32,
  face : Face,
  agreement : Face,
  ty : DValue,
  a : DValue,
  b : DValue,
) -> Bool {
  let face_vars = face_nvars_sem(face)
  let ag_vars = face_nvars_sem(agreement)
  let mut dl = dlevel
  if face_vars > dl {
    dl = face_vars
  }
  if ag_vars > dl {
    dl = ag_vars
  }
  if dl > 20 {
    return false
  }
  let face_bdd = bdd_of_face(face, dl)
  let ag_bdd = bdd_of_face(agreement, dl)
  if bdd_and(ag_bdd, bdd_not(face_bdd)) != BddZero {
    return false
  }
  let ty_term = quote_ty(level, dl, ty)
  let a_term = quote_at(level, dl, ty, a)
  let b_term = quote_at(level, dl, ty, b)
  let term_env = fresh_term_env(level)
  let total = pow2(dl)
  for mask in 0..<total {
    let assignment : Array[Int32] = []
    let env : Array[Bool] = []
    for i in 0..<dl {
      let bit = (mask >> i) & 1
      assignment.push(bit)
      env.push(bit == 1)
    }
    if face_holds(agreement, env) &&
      !restricted_terms_conv(
        level, dl, ty_term, a_term, b_term, term_env, assignment,
      ) {
      return false
    }
  }
  true
}

///|
pub struct DSystemRepairExact {
  system : DSystem
  base_removed_region : Bdd
  repaired_branches : Int32
  compatible : Bool
}

///|
/// Repair against a composition base using *exact* Face-valued
/// agreement regions.  Unlike `dsystem_repair_to_base`, a branch
/// whose value agrees with the base at both endpoints of a
/// dimension (but not in its interior) keeps both endpoints
/// through the face `(i = 0) or (i = 1)` instead of losing the
/// 1-endpoint to BDD collapse.  The reported removed region is
/// the Boolean (vertex-level) part removed; the retained faces
/// themselves carry the finer interior information.
pub fn dsystem_repair_to_base_exact(
  level : Int32,
  dlevel : Int32,
  line : (Dim) -> DValue,
  system : DSystem,
  base : DValue,
) -> DSystemRepairExact {
  let nvars = dsystem_nvars(system, dlevel)
  let restricted : Array[DTubeBranch] = []
  let mut removed = BddZero
  let mut repaired = 0
  for i in 0..<system.branches.length() {
    let br = system.branches[i]
    if face_is_bot_sem(br.face) {
      continue
    }
    let region = bdd_of_face(br.face, nvars)
    let agreement = face_agreement_face(
      level,
      dlevel,
      br.face,
      line(DZero),
      (br.path)(DZero),
      base,
    )
    let agreement_bdd = bdd_of_face(agreement, nvars)
    if agreement_bdd != region {
      repaired = repaired + 1
      removed = bdd_or(removed, bdd_and(region, bdd_not(agreement_bdd)))
    }
    if agreement != FBot {
      restricted.push(tube_branch(agreement, br.path))
    }
  }
  let restricted_system = dsystem_of(restricted)
  DSystemRepairExact::{
    system: restricted_system,
    base_removed_region: removed,
    repaired_branches: repaired,
    compatible: dsystem_compatible_with_base(
      level, dlevel, line, restricted_system, base,
    ),
  }
}

///|
pub struct DSystemRepairSupplemented {
  system : DSystem
  base_removed_region : Bdd
  repaired_branches : Int32
  added_branches : Int32
  rejected_candidates : Int32
  compatible : Bool
}

///|
fn dsystem_try_accept(
  level : Int32,
  dlevel : Int32,
  line : (Dim) -> DValue,
  accepted : Array[DTubeBranch],
  branch : DTubeBranch,
  base : DValue,
) -> Bool {
  let tentative : Array[DTubeBranch] = []
  for i in 0..<accepted.length() {
    tentative.push(accepted[i])
  }
  tentative.push(branch)
  dsystem_compatible_with_base(level, dlevel, line, dsystem_of(tentative), base)
}

///|
/// Repair with supplementation.  Original branches are first
/// restricted to their exact base-agreement faces and then
/// greedily accepted, in order, whenever the tentative system
/// remains fully compatible (base agreement at dimension 0 and
/// pairwise agreement on overlaps); candidate branches are then
/// offered under exactly the same verifiable condition and are
/// added only when the whole tentative system checks.  The
/// result is an order-dependent maximal compatible subsystem of
/// the restricted originals plus accepted candidates -- not a
/// maximum one -- and every rejection is counted.  This
/// complements the deletion-only repairs above: branches removed
/// or never present can be restored from a candidate pool, but
/// only through the same compatibility audit as everything else.
pub fn dsystem_repair_with_candidates(
  level : Int32,
  dlevel : Int32,
  line : (Dim) -> DValue,
  system : DSystem,
  base : DValue,
  candidates : Array[DTubeBranch],
) -> DSystemRepairSupplemented {
  let mut nvars = dsystem_nvars(system, dlevel)
  for i in 0..<candidates.length() {
    let m = face_nvars_sem(candidates[i].face)
    if m > nvars {
      nvars = m
    }
  }
  let accepted : Array[DTubeBranch] = []
  let mut removed = BddZero
  let mut repaired = 0
  let mut added = 0
  let mut rejected = 0
  for i in 0..<system.branches.length() {
    let br = system.branches[i]
    if face_is_bot_sem(br.face) {
      continue
    }
    let region = bdd_of_face(br.face, nvars)
    let agreement = face_agreement_face(
      level,
      dlevel,
      br.face,
      line(DZero),
      (br.path)(DZero),
      base,
    )
    let agreement_bdd = bdd_of_face(agreement, nvars)
    let mut counted = false
    if agreement_bdd != region {
      repaired = repaired + 1
      counted = true
      removed = bdd_or(removed, bdd_and(region, bdd_not(agreement_bdd)))
    }
    if agreement == FBot {
      continue
    }
    let restricted_branch = tube_branch(agreement, br.path)
    if dsystem_try_accept(
        level, dlevel, line, accepted, restricted_branch, base,
      ) {
      accepted.push(restricted_branch)
    } else {
      // Dropped for pairwise incompatibility with an earlier
      // accepted branch: its whole retained region leaves the
      // repaired system's domain.
      if !counted {
        repaired = repaired + 1
      }
      removed = bdd_or(removed, agreement_bdd)
    }
  }
  for i in 0..<candidates.length() {
    let br = candidates[i]
    if face_is_bot_sem(br.face) {
      rejected = rejected + 1
      continue
    }
    let agreement = face_agreement_face(
      level,
      dlevel,
      br.face,
      line(DZero),
      (br.path)(DZero),
      base,
    )
    if agreement == FBot {
      rejected = rejected + 1
      continue
    }
    let restricted_branch = tube_branch(agreement, br.path)
    if dsystem_try_accept(
        level, dlevel, line, accepted, restricted_branch, base,
      ) {
      accepted.push(restricted_branch)
      added = added + 1
    } else {
      rejected = rejected + 1
    }
  }
  let repaired_system = dsystem_of(accepted)
  DSystemRepairSupplemented::{
    system: repaired_system,
    base_removed_region: removed,
    repaired_branches: repaired,
    added_branches: added,
    rejected_candidates: rejected,
    compatible: dsystem_compatible_with_base(
      level, dlevel, line, repaired_system, base,
    ),
  }
}

// ---------------------------------------------------------------------------
// Phase 13: maximum (not merely maximal) compatible completion.
//
// After base-restriction, compatibility of a branch set is
// pairwise (agreement with the base is per-branch, agreement
// between branches is per-overlap), so a largest compatible
// subset of the restricted pool is a maximum clique of the
// pairwise-compatibility graph.  We solve it exactly with a
// Tomita-style branch-and-bound (greedy coloring gives the
// upper bound), warm-started from the order-greedy clique, and
// stop at a node budget: on exhaustion the incumbent is
// returned with `exact = false`.  The result is therefore
// always at least as large as `dsystem_repair_with_candidates`'
// order-dependent maximal system on the same pool, and is a
// certified maximum whenever `exact` holds.
// ---------------------------------------------------------------------------

///|
pub struct DSystemRepairMaximum {
  system : DSystem
  base_removed_region : Bdd
  repaired_branches : Int32
  added_branches : Int32
  rejected_candidates : Int32
  compatible : Bool
  exact : Bool
}

///|
fn maxclique_color_sort(
  adj : Array[Array[Bool]],
  p : Array[Int32],
) -> Array[Int32] {
  // Greedy sequential coloring of `p` (in place order matters):
  // returns color bounds aligned with the reordered `p`, where
  // bounds[i] is the color number of p[i] and the vertices are
  // sorted by nondecreasing color.
  let bounds : Array[Int32] = []
  let classes : Array[Array[Int32]] = []
  for idx in 0..<p.length() {
    let v = p[idx]
    let mut placed = false
    for c in 0..<classes.length() {
      let mut fits = true
      for k in 0..<classes[c].length() {
        if adj[v][classes[c][k]] {
          fits = false
          break
        }
      }
      if fits {
        classes[c].push(v)
        placed = true
        break
      }
    }
    if !placed {
      classes.push([v])
    }
  }
  let mut w = 0
  for c in 0..<classes.length() {
    for k in 0..<classes[c].length() {
      p[w] = classes[c][k]
      bounds.push(c + 1)
      w = w + 1
    }
  }
  bounds
}

///|
fn maxclique_expand(
  adj : Array[Array[Bool]],
  clique : Array[Int32],
  p : Array[Int32],
  state : Array[Int32],
  best : Array[Int32],
  budget : Int32,
) -> Unit {
  // state[0] = incumbent size, state[1] = nodes used,
  // state[2] = 1 once the budget is exhausted.
  let bounds = maxclique_color_sort(adj, p)
  let mut i = p.length() - 1
  while i >= 0 {
    if state[2] == 1 {
      return
    }
    if clique.length() + bounds[i] <= state[0] {
      return
    }
    let v = p[i]
    state[1] = state[1] + 1
    if state[1] > budget {
      state[2] = 1
      return
    }
    let next_p : Array[Int32] = []
    for k in 0..<i {
      if adj[v][p[k]] {
        next_p.push(p[k])
      }
    }
    clique.push(v)
    if next_p.length() == 0 {
      if clique.length() > state[0] {
        state[0] = clique.length()
        while best.length() > 0 {
          ignore(best.pop())
        }
        for k in 0..<clique.length() {
          best.push(clique[k])
        }
      }
    } else {
      maxclique_expand(adj, clique, next_p, state, best, budget)
    }
    ignore(clique.pop())
    i = i - 1
  }
}

///|
/// A maximum-cardinality subset of `vertices` pairwise adjacent
/// in `adj`, warm-started from the greedy in-order clique.
/// Returns (clique, exact): `exact` is false iff the node
/// budget cut the search, in which case the clique is the best
/// incumbent found (at least the greedy one).
fn maxclique_exact(
  adj : Array[Array[Bool]],
  vertices : Array[Int32],
  budget : Int32,
) -> (Array[Int32], Bool) {
  let best : Array[Int32] = []
  for i in 0..<vertices.length() {
    let v = vertices[i]
    let mut ok = true
    for k in 0..<best.length() {
      if !adj[v][best[k]] {
        ok = false
        break
      }
    }
    if ok {
      best.push(v)
    }
  }
  let state : Array[Int32] = [best.length(), 0, 0]
  let p : Array[Int32] = []
  for i in 0..<vertices.length() {
    p.push(vertices[i])
  }
  maxclique_expand(adj, [], p, state, best, budget)
  (best, state[2] == 0)
}

///|
/// Repair with supplementation to a *maximum* compatible
/// subsystem.  Like `dsystem_repair_with_candidates`, original
/// and candidate branches are first restricted to their exact
/// base-agreement faces; the accepted subset is then a largest
/// pairwise-compatible subset of the whole restricted pool
/// (originals first, so order ties break toward originals and
/// then toward earlier candidates), computed exactly subject
/// to `node_budget` branch-and-bound nodes.  `exact` in the
/// result certifies that the search completed; otherwise the
/// returned system is the best incumbent found, never smaller
/// than the order-greedy maximal one.
pub fn dsystem_repair_maximum(
  level : Int32,
  dlevel : Int32,
  line : (Dim) -> DValue,
  system : DSystem,
  base : DValue,
  candidates : Array[DTubeBranch],
  node_budget~ : Int32 = 200000,
) -> DSystemRepairMaximum {
  let mut nvars = dsystem_nvars(system, dlevel)
  for i in 0..<candidates.length() {
    let m = face_nvars_sem(candidates[i].face)
    if m > nvars {
      nvars = m
    }
  }
  // Restricted pool: originals (origin 0) then candidates (1).
  let pool : Array[DTubeBranch] = []
  let origin : Array[Int32] = []
  let pool_region : Array[Bdd] = []
  let pool_counted : Array[Bool] = []
  let mut removed = BddZero
  let mut repaired = 0
  let mut rejected = 0
  for i in 0..<system.branches.length() {
    let br = system.branches[i]
    if face_is_bot_sem(br.face) {
      continue
    }
    let region = bdd_of_face(br.face, nvars)
    let agreement = face_agreement_face(
      level,
      dlevel,
      br.face,
      line(DZero),
      (br.path)(DZero),
      base,
    )
    let agreement_bdd = bdd_of_face(agreement, nvars)
    let mut counted = false
    if agreement_bdd != region {
      repaired = repaired + 1
      counted = true
      removed = bdd_or(removed, bdd_and(region, bdd_not(agreement_bdd)))
    }
    if agreement == FBot {
      continue
    }
    pool.push(tube_branch(agreement, br.path))
    origin.push(0)
    pool_region.push(agreement_bdd)
    pool_counted.push(counted)
  }
  for i in 0..<candidates.length() {
    let br = candidates[i]
    if face_is_bot_sem(br.face) {
      rejected = rejected + 1
      continue
    }
    let agreement = face_agreement_face(
      level,
      dlevel,
      br.face,
      line(DZero),
      (br.path)(DZero),
      base,
    )
    if agreement == FBot {
      rejected = rejected + 1
      continue
    }
    pool.push(tube_branch(agreement, br.path))
    origin.push(1)
    pool_region.push(bdd_of_face(agreement, nvars))
    pool_counted.push(true)
  }
  // Pairwise compatibility graph over the pool.
  let n = pool.length()
  let adj : Array[Array[Bool]] = []
  for _i in 0..<n {
    let row : Array[Bool] = []
    for _j in 0..<n {
      row.push(false)
    }
    adj.push(row)
  }
  for i in 0..<n {
    adj[i][i] = true
    for j in (i + 1)..<n {
      let overlap = face_simplify(FAnd(pool[i].face, pool[j].face))
      let ok = !face_is_sat_sem(overlap) ||
        tube_paths_conv_under_face(
          level,
          dlevel,
          overlap,
          line,
          pool[i].path,
          pool[j].path,
        )
      adj[i][j] = ok
      adj[j][i] = ok
    }
  }
  let vertices : Array[Int32] = []
  for i in 0..<n {
    vertices.push(i)
  }
  let (chosen, exact) = maxclique_exact(adj, vertices, node_budget)
  let in_chosen : Array[Bool] = []
  for _i in 0..<n {
    in_chosen.push(false)
  }
  for k in 0..<chosen.length() {
    in_chosen[chosen[k]] = true
  }
  let accepted : Array[DTubeBranch] = []
  let mut added = 0
  for i in 0..<n {
    if in_chosen[i] {
      accepted.push(pool[i])
      if origin[i] == 1 {
        added = added + 1
      }
    } else if origin[i] == 0 {
      // Dropped for pairwise incompatibility, exactly as in
      // the greedy repair's accounting.
      if !pool_counted[i] {
        repaired = repaired + 1
      }
      removed = bdd_or(removed, pool_region[i])
    } else {
      rejected = rejected + 1
    }
  }
  let repaired_system = dsystem_of(accepted)
  DSystemRepairMaximum::{
    system: repaired_system,
    base_removed_region: removed,
    repaired_branches: repaired,
    added_branches: added,
    rejected_candidates: rejected,
    compatible: dsystem_compatible_with_base(
      level, dlevel, line, repaired_system, base,
    ),
    exact,
  }
}

///|
/// Report of conflict-component decomposed enumeration of *all*
/// maximum-cardinality pairwise-compatible completions of a repaired
/// `DSystem`.
pub struct DSystemRepairAllMaxima {
  systems : Array[DSystem]
  max_branch_count : Int32
  total_maximum_count : Int32
  conflict_components : Int32
  all_compatible : Bool
  exact : Bool
}

///|
///|
/// DSATUR chromatic upper-bound report for maximum compatible `DSystem`
/// enumeration across conflict components.
pub struct DSystemDsaturCliqueReport {
  result : DSystemRepairAllMaxima
  chromatic_root_bound : Int32
  dsatur_visited_nodes : Int32
  color_pruned_branches : Int32
  uncolored_visited_nodes : Int32
}

///|
/// Greedy DSATUR vertex coloring on the compatibility subgraph `G[cand]`.
/// Returns `(ordered_cand, color_bounds)` sorted in ascending color-class
/// order `1 <= c_0 <= c_1 <= ... <= c_{m-1}`: no two compatible vertices in
/// `cand` receive the same color, so any clique contained in
/// `ordered_cand[0 .. idx]` has cardinality at most `color_bounds[idx]`.
pub fn dsatur_color_order(
  adj : Array[Array[Bool]],
  cand : Array[Int32],
) -> (Array[Int32], Array[Int32]) {
  let m = cand.length()
  if m == 0 {
    return ([], [])
  }
  let deg : Array[Int32] = []
  let color : Array[Int32] = []
  let colored : Array[Bool] = []
  for i in 0..<m {
    let u = cand[i]
    let mut d = 0
    for j in 0..<m {
      if i != j && adj[u][cand[j]] {
        d = d + 1
      }
    }
    deg.push(d)
    color.push(0)
    colored.push(false)
  }
  for _step in 0..<m {
    // Pick uncolored vertex with maximum saturation degree, tie-breaking by
    // induced degree and smallest pool index.
    let mut best = -1
    let mut best_sat = -1
    let mut best_deg = -1
    for i in 0..<m {
      if colored[i] {
        continue
      }
      let u = cand[i]
      let seen_colors : Array[Int32] = []
      for j in 0..<m {
        if colored[j] && adj[u][cand[j]] {
          let cj = color[j]
          if !seen_colors.contains(cj) {
            seen_colors.push(cj)
          }
        }
      }
      let sat = seen_colors.length()
      if best < 0 ||
        sat > best_sat ||
        (sat == best_sat && deg[i] > best_deg) ||
        (sat == best_sat && deg[i] == best_deg && cand[i] < cand[best]) {
        best = i
        best_sat = sat
        best_deg = deg[i]
      }
    }
    let u = cand[best]
    let mut chosen_c = 1
    while true {
      let mut clash = false
      for j in 0..<m {
        if colored[j] && color[j] == chosen_c && adj[u][cand[j]] {
          clash = true
          break
        }
      }
      if !clash {
        break
      }
      chosen_c = chosen_c + 1
    }
    colored[best] = true
    color[best] = chosen_c
  }
  // Bucket vertices in ascending color order (and pool order within each color
  // class) so `color_bounds` is non-decreasing.
  let mut max_c = 0
  for i in 0..<m {
    if color[i] > max_c {
      max_c = color[i]
    }
  }
  let ordered : Array[Int32] = []
  let bounds : Array[Int32] = []
  for c in 1..<=max_c {
    for i in 0..<m {
      if color[i] == c {
        ordered.push(cand[i])
        bounds.push(c)
      }
    }
  }
  (ordered, bounds)
}

///|
fn sort_clique_asc(clq : Array[Int32]) -> Array[Int32] {
  let out : Array[Int32] = []
  for i in 0..<clq.length() {
    out.push(clq[i])
  }
  for _p in 0..<out.length() {
    for q in 0..<(out.length() - 1) {
      if out[q + 1] < out[q] {
        let tmp = out[q]
        out[q] = out[q + 1]
        out[q + 1] = tmp
      }
    }
  }
  out
}

///|
fn clique_lex_lt(a : Array[Int32], b : Array[Int32]) -> Bool {
  let len = if a.length() < b.length() { a.length() } else { b.length() }
  for i in 0..<len {
    if a[i] != b[i] {
      return a[i] < b[i]
    }
  }
  a.length() < b.length()
}

///|
fn maxclique_uncolored_count_nodes(
  adj : Array[Array[Bool]],
  comp : Array[Int32],
  target : Int32,
  budget : Int32,
) -> Int32 {
  let k = comp.length()
  let cur : Array[Int32] = []
  let nodes = [0, 0]
  fn dfs(start : Int32) -> Unit {
    if nodes[1] != 0 || cur.length() == target {
      return
    }
    if cur.length() + (k - start) < target {
      return
    }
    for idx in start..<k {
      if cur.length() + (k - idx) < target {
        break
      }
      nodes[0] = nodes[0] + 1
      if nodes[0] > budget {
        nodes[1] = 1
        return
      }
      let v = comp[idx]
      let mut ok = true
      for j in 0..<cur.length() {
        if !adj[v][cur[j]] {
          ok = false
          break
        }
      }
      if ok {
        cur.push(v)
        dfs(idx + 1)
        ignore(cur.pop())
      }
    }
  }
  dfs(0)
  nodes[0]
}

///|
/// Two-phase Tomita–Sutani / DSATUR maximum-clique enumerator on a single
/// conflict component `comp`: Phase 1 finds the exact clique number `ω` via
/// DSATUR branch-and-bound; Phase 2 enumerates ALL cliques of size `ω` using
/// `|cur| + color_bound[idx] < ω` pruning, returning `(cliques, exact,
/// root_chromatic_bound, visited_nodes, color_pruned_branches)`.
fn maxclique_dsatur_component(
  adj : Array[Array[Bool]],
  comp : Array[Int32],
  budget : Int32,
) -> (Array[Array[Int32]], Bool, Int32, Int32, Int32) {
  let k = comp.length()
  if k == 0 {
    return ([[]], true, 0, 0, 0)
  }
  if k == 1 {
    return ([[comp[0]]], true, 1, 1, 0)
  }
  let (root_ord, root_bounds) = dsatur_color_order(adj, comp)
  let root_chi = root_bounds[root_bounds.length() - 1]
  // Phase 1: find exact maximum clique size `best[0]` with DSATUR bound.
  let best_clq : Array[Int32] = [comp[0]]
  let cur1 : Array[Int32] = []
  let stats = [0, 0, 0] // [visited_nodes, color_pruned, exceeded]
  fn search_omega(ord : Array[Int32], bounds : Array[Int32]) -> Unit {
    if stats[2] != 0 {
      return
    }
    let mut idx = ord.length() - 1
    while idx >= 0 {
      if cur1.length() + bounds[idx] <= best_clq.length() {
        stats[1] = stats[1] + (idx + 1)
        break
      }
      stats[0] = stats[0] + 1
      if stats[0] > budget {
        stats[2] = 1
        return
      }
      let v = ord[idx]
      cur1.push(v)
      let next_cand : Array[Int32] = []
      for t in 0..<idx {
        let u = ord[t]
        if adj[v][u] {
          next_cand.push(u)
        }
      }
      if next_cand.length() == 0 {
        if cur1.length() > best_clq.length() {
          best_clq.clear()
          for z in 0..<cur1.length() {
            best_clq.push(cur1[z])
          }
        }
      } else if cur1.length() + next_cand.length() > best_clq.length() {
        let (sub_ord, sub_bounds) = dsatur_color_order(adj, next_cand)
        search_omega(sub_ord, sub_bounds)
      }
      ignore(cur1.pop())
      if stats[2] != 0 {
        return
      }
      idx = idx - 1
    }
  }
  search_omega(root_ord, root_bounds)
  if stats[2] != 0 {
    return ([sort_clique_asc(best_clq)], false, root_chi, stats[0], stats[1])
  }
  let target = best_clq.length()
  // Phase 2: enumerate ALL cliques of size `target` using DSATUR upper bounds.
  let all_cliques : Array[Array[Int32]] = []
  let cur2 : Array[Int32] = []
  fn enum_omega(ord : Array[Int32], bounds : Array[Int32]) -> Unit {
    if stats[2] != 0 {
      return
    }
    if cur2.length() == target {
      all_cliques.push(sort_clique_asc(cur2))
      return
    }
    let mut idx = ord.length() - 1
    while idx >= 0 {
      if cur2.length() + bounds[idx] < target {
        stats[1] = stats[1] + (idx + 1)
        break
      }
      stats[0] = stats[0] + 1
      if stats[0] > budget {
        stats[2] = 1
        return
      }
      let v = ord[idx]
      cur2.push(v)
      if cur2.length() == target {
        all_cliques.push(sort_clique_asc(cur2))
      } else {
        let next_cand : Array[Int32] = []
        for t in 0..<idx {
          let u = ord[t]
          if adj[v][u] {
            next_cand.push(u)
          }
        }
        if cur2.length() + next_cand.length() >= target {
          let (sub_ord, sub_bounds) = dsatur_color_order(adj, next_cand)
          enum_omega(sub_ord, sub_bounds)
        }
      }
      ignore(cur2.pop())
      if stats[2] != 0 {
        return
      }
      idx = idx - 1
    }
  }
  enum_omega(root_ord, root_bounds)
  if stats[2] != 0 || all_cliques.length() == 0 {
    return ([sort_clique_asc(best_clq)], false, root_chi, stats[0], stats[1])
  }
  // Deterministic lexicographic order over pool indices.
  for _p in 0..<all_cliques.length() {
    for q in 0..<(all_cliques.length() - 1) {
      if clique_lex_lt(all_cliques[q + 1], all_cliques[q]) {
        let tmp = all_cliques[q]
        all_cliques[q] = all_cliques[q + 1]
        all_cliques[q + 1] = tmp
      }
    }
  }
  (all_cliques, true, root_chi, stats[0], stats[1])
}

///|
/// Decompose the pairwise conflict graph into connected components and run
/// Tomita–Sutani DSATUR chromatic upper-bound branch-and-bound on every
/// component, returning both the exact maximum-compatible `DSystem` solutions
/// and DSATUR pruning telemetry (`chromatic_root_bound`,
/// `dsatur_visited_nodes`, `color_pruned_branches`, `uncolored_visited_nodes`).
pub fn dsystem_repair_all_maxima_dsatur(
  level : Int32,
  dlevel : Int32,
  line : (Dim) -> DValue,
  system : DSystem,
  base : DValue,
  candidates : Array[DTubeBranch],
  max_solutions~ : Int32 = 32,
  node_budget~ : Int32 = 200000,
) -> DSystemDsaturCliqueReport {
  let pool : Array[DTubeBranch] = []
  for i in 0..<system.branches.length() {
    let br = system.branches[i]
    if face_is_bot_sem(br.face) {
      continue
    }
    let agreement = face_agreement_face(
      level,
      dlevel,
      br.face,
      line(DZero),
      (br.path)(DZero),
      base,
    )
    if agreement != FBot {
      pool.push(tube_branch(agreement, br.path))
    }
  }
  for i in 0..<candidates.length() {
    let br = candidates[i]
    if face_is_bot_sem(br.face) {
      continue
    }
    let agreement = face_agreement_face(
      level,
      dlevel,
      br.face,
      line(DZero),
      (br.path)(DZero),
      base,
    )
    if agreement != FBot {
      pool.push(tube_branch(agreement, br.path))
    }
  }
  let n = pool.length()
  if n == 0 {
    let empty_sys = dsystem_of([])
    return DSystemDsaturCliqueReport::{
      result: DSystemRepairAllMaxima::{
        systems: if max_solutions > 0 {
          [empty_sys]
        } else {
          []
        },
        max_branch_count: 0,
        total_maximum_count: 1,
        conflict_components: 0,
        all_compatible: true,
        exact: true,
      },
      chromatic_root_bound: 0,
      dsatur_visited_nodes: 0,
      color_pruned_branches: 0,
      uncolored_visited_nodes: 0,
    }
  }
  let adj : Array[Array[Bool]] = []
  for _i in 0..<n {
    let row : Array[Bool] = []
    for _j in 0..<n {
      row.push(false)
    }
    adj.push(row)
  }
  for i in 0..<n {
    adj[i][i] = true
    for j in (i + 1)..<n {
      let overlap = face_simplify(FAnd(pool[i].face, pool[j].face))
      let ok = !face_is_sat_sem(overlap) ||
        tube_paths_conv_under_face(
          level,
          dlevel,
          overlap,
          line,
          pool[i].path,
          pool[j].path,
        )
      adj[i][j] = ok
      adj[j][i] = ok
    }
  }
  // Connected components in the CONFLICT graph (!adj[u][v]).
  let visited : Array[Bool] = []
  for _i in 0..<n {
    visited.push(false)
  }
  let components : Array[Array[Int32]] = []
  for start in 0..<n {
    if visited[start] {
      continue
    }
    visited[start] = true
    let comp : Array[Int32] = [start]
    let mut head = 0
    while head < comp.length() {
      let u = comp[head]
      head = head + 1
      for v in 0..<n {
        if !visited[v] && !adj[u][v] {
          visited[v] = true
          comp.push(v)
        }
      }
    }
    for _p in 0..<comp.length() {
      for q in 0..<(comp.length() - 1) {
        if comp[q + 1] < comp[q] {
          let tmp = comp[q]
          comp[q] = comp[q + 1]
          comp[q + 1] = tmp
        }
      }
    }
    components.push(comp)
  }
  let comp_solutions : Array[Array[Array[Int32]]] = []
  let mut exact = true
  let mut max_branches = 0
  let mut total_count = 1
  let mut root_chi_sum = 0
  let mut dsatur_nodes = 0
  let mut pruned_sum = 0
  let mut uncolored_nodes = 0
  for ci in 0..<components.length() {
    let (sols, ex, chi, d_nodes, pruned) = maxclique_dsatur_component(
      adj,
      components[ci],
      node_budget,
    )
    if !ex {
      exact = false
    }
    let omega = sols[0].length()
    max_branches = max_branches + omega
    total_count = total_count * sols.length()
    root_chi_sum = root_chi_sum + chi
    dsatur_nodes = dsatur_nodes + d_nodes
    pruned_sum = pruned_sum + pruned
    uncolored_nodes = uncolored_nodes +
      maxclique_uncolored_count_nodes(adj, components[ci], omega, node_budget)
    comp_solutions.push(sols)
  }
  let cap = if max_solutions < 0 { 0 } else { max_solutions }
  let chosen_sets : Array[Array[Int32]] = [[]]
  for ci in 0..<comp_solutions.length() {
    let sols = comp_solutions[ci]
    let next_sets : Array[Array[Int32]] = []
    for a in 0..<chosen_sets.length() {
      for b in 0..<sols.length() {
        if next_sets.length() >= cap && cap > 0 {
          break
        }
        let merged : Array[Int32] = []
        for x in 0..<chosen_sets[a].length() {
          merged.push(chosen_sets[a][x])
        }
        for y in 0..<sols[b].length() {
          merged.push(sols[b][y])
        }
        next_sets.push(merged)
      }
      if next_sets.length() >= cap && cap > 0 {
        break
      }
    }
    chosen_sets.clear()
    for x in 0..<next_sets.length() {
      chosen_sets.push(next_sets[x])
    }
  }
  let out_systems : Array[DSystem] = []
  let mut all_ok = true
  if cap > 0 {
    for s in 0..<chosen_sets.length() {
      let in_set : Array[Bool] = []
      for _i in 0..<n {
        in_set.push(false)
      }
      for k in 0..<chosen_sets[s].length() {
        in_set[chosen_sets[s][k]] = true
      }
      let accepted : Array[DTubeBranch] = []
      for i in 0..<n {
        if in_set[i] {
          accepted.push(pool[i])
        }
      }
      let sys = dsystem_of(accepted)
      if !dsystem_compatible_with_base(level, dlevel, line, sys, base) {
        all_ok = false
      }
      out_systems.push(sys)
    }
  }
  DSystemDsaturCliqueReport::{
    result: DSystemRepairAllMaxima::{
      systems: out_systems,
      max_branch_count: max_branches,
      total_maximum_count: total_count,
      conflict_components: components.length(),
      all_compatible: all_ok,
      exact,
    },
    chromatic_root_bound: root_chi_sum,
    dsatur_visited_nodes: dsatur_nodes,
    color_pruned_branches: pruned_sum,
    uncolored_visited_nodes: uncolored_nodes,
  }
}

///|
/// Decompose the pairwise conflict graph (complement of `adj`) into
/// connected components, enumerate all maximum-cardinality compatible
/// branch subsets within each component independently, and take their
/// Cartesian product (up to `max_solutions` materialized `DSystem`s,
/// while reporting the exact `total_maximum_count`).
pub fn dsystem_repair_all_maxima(
  level : Int32,
  dlevel : Int32,
  line : (Dim) -> DValue,
  system : DSystem,
  base : DValue,
  candidates : Array[DTubeBranch],
  max_solutions~ : Int32 = 32,
  node_budget~ : Int32 = 200000,
) -> DSystemRepairAllMaxima {
  dsystem_repair_all_maxima_dsatur(
    level,
    dlevel,
    line,
    system,
    base,
    candidates,
    max_solutions~,
    node_budget~,
  ).result
}
