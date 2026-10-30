///|\
// Watched-literal DPLL for faces.
//
// A face and the dimension expressions inside its atoms form one
// Boolean formula over the dimension variables.  This file compiles
// that formula to CNF by Tseitin extension variables, then searches
// with watched literals, saved phases, and conflict-driven variable
// activity.  It complements the ROBDD decision procedure: the BDD
// is canonical but can be exponentially large for a bad order or a
// hard function, whereas this solver trades canonicity for search
// and returns the existing budget-exceeded status rather than
// guessing when its step budget is exhausted.

///|
pub struct FaceCnfStats {
  variables : Int32
  auxiliary_variables : Int32
  clauses : Int32
  literals : Int32
} derive(Debug, Eq)

///|
pub extend FaceCnfStats with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend FaceCnfStats with Eq::{not_equal, equal}

///|
priv enum FaceBoolExpr {
  FBEConst(Bool)
  FBEVar(Int32)
  FBENot(FaceBoolExpr)
  FBEAnd(FaceBoolExpr, FaceBoolExpr)
  FBEOr(FaceBoolExpr, FaceBoolExpr)
} derive(Eq)

///|
fn fbe_not(a : FaceBoolExpr) -> FaceBoolExpr {
  match a {
    FBEConst(b) => FBEConst(!b)
    FBENot(x) => x
    _ => FBENot(a)
  }
}

///|
fn fbe_and(a : FaceBoolExpr, b : FaceBoolExpr) -> FaceBoolExpr {
  match (a, b) {
    (FBEConst(false), _) | (_, FBEConst(false)) => FBEConst(false)
    (FBEConst(true), x) => x
    (x, FBEConst(true)) => x
    _ => if a == b { a } else { FBEAnd(a, b) }
  }
}

///|
fn fbe_or(a : FaceBoolExpr, b : FaceBoolExpr) -> FaceBoolExpr {
  match (a, b) {
    (FBEConst(true), _) | (_, FBEConst(true)) => FBEConst(true)
    (FBEConst(false), x) => x
    (x, FBEConst(false)) => x
    _ => if a == b { a } else { FBEOr(a, b) }
  }
}

///|
fn fbe_of_dim(r : Dim, n : Int32) -> FaceBoolExpr {
  match r {
    DZero => FBEConst(false)
    DOne => FBEConst(true)
    DVar(i) => if i >= 0 && i < n { FBEVar(i) } else { FBEConst(false) }
    DNeg(a) => fbe_not(fbe_of_dim(a, n))
    DAnd(a, b) => fbe_and(fbe_of_dim(a, n), fbe_of_dim(b, n))
    DOr(a, b) => fbe_or(fbe_of_dim(a, n), fbe_of_dim(b, n))
  }
}

///|
fn fbe_of_face(f : Face, n : Int32) -> FaceBoolExpr {
  match f {
    FTop => FBEConst(true)
    FBot => FBEConst(false)
    FEq0(r) => fbe_not(fbe_of_dim(r, n))
    FEq1(r) => fbe_of_dim(r, n)
    FAnd(a, b) => fbe_and(fbe_of_face(a, n), fbe_of_face(b, n))
    FOr(a, b) => fbe_or(fbe_of_face(a, n), fbe_of_face(b, n))
  }
}

///|
priv struct FaceCnfBuilder {
  clauses : Array[Array[Int32]]
  mut next_variable : Int32
}

///|
fn face_cnf_add_clause(builder : FaceCnfBuilder, input : Array[Int32]) -> Unit {
  let clause : Array[Int32] = []
  for i in 0..<input.length() {
    let lit = input[i]
    let mut duplicate = false
    let mut tautology = false
    for j in 0..<clause.length() {
      if clause[j] == lit {
        duplicate = true
      }
      if clause[j] == 0 - lit {
        tautology = true
      }
    }
    if tautology {
      return
    }
    if !duplicate {
      clause.push(lit)
    }
  }
  builder.clauses.push(clause)
}

///|
fn face_cnf_tseitin(builder : FaceCnfBuilder, expr : FaceBoolExpr) -> Int32 {
  match expr {
    FBEConst(true) => {
      let variable = builder.next_variable
      builder.next_variable = builder.next_variable + 1
      face_cnf_add_clause(builder, [variable])
      variable
    }
    FBEConst(false) => {
      let variable = builder.next_variable
      builder.next_variable = builder.next_variable + 1
      face_cnf_add_clause(builder, [0 - variable])
      variable
    }
    FBEVar(i) => i + 1
    FBENot(a) => 0 - face_cnf_tseitin(builder, a)
    FBEAnd(a, b) => {
      let la = face_cnf_tseitin(builder, a)
      let lb = face_cnf_tseitin(builder, b)
      let x = builder.next_variable
      builder.next_variable = builder.next_variable + 1
      face_cnf_add_clause(builder, [0 - x, la])
      face_cnf_add_clause(builder, [0 - x, lb])
      face_cnf_add_clause(builder, [x, 0 - la, 0 - lb])
      x
    }
    FBEOr(a, b) => {
      let la = face_cnf_tseitin(builder, a)
      let lb = face_cnf_tseitin(builder, b)
      let x = builder.next_variable
      builder.next_variable = builder.next_variable + 1
      face_cnf_add_clause(builder, [x, 0 - la])
      face_cnf_add_clause(builder, [x, 0 - lb])
      face_cnf_add_clause(builder, [0 - x, la, lb])
      x
    }
  }
}

///|
fn face_cnf_build(f : Face, n : Int32) -> FaceCnfBuilder {
  let builder = FaceCnfBuilder::{ clauses: [], next_variable: n + 1, }
  let root = face_cnf_tseitin(builder, fbe_of_face(face_bound(f, n), n))
  face_cnf_add_clause(builder, [root])
  builder
}

///|
/// Size of the Tseitin CNF used by the watched-literal solver.
pub fn face_cnf_stats(f : Face, n : Int32) -> FaceCnfStats {
  let builder = face_cnf_build(f, n)
  let mut literals = 0
  for i in 0..<builder.clauses.length() {
    literals = literals + builder.clauses[i].length()
  }
  FaceCnfStats::{
    variables: builder.next_variable - 1,
    auxiliary_variables: builder.next_variable - 1 - n,
    clauses: builder.clauses.length(),
    literals,
  }
}

///|
priv struct FaceSatSolver {
  clauses : Array[Array[Int32]]
  watches : Array[Array[Int32]]
  assignment : Array[Int32] // -1 unassigned, 0 false, 1 true; 1-based vars
  phase : Array[Bool]
  activity : Array[Double]
  trail : Array[Int32]
  mut qhead : Int32
  variables : Int32
  mut steps : Int32
  max_steps : Int32
  mut budget_exceeded : Bool
}

///|
fn face_sat_lit_index(lit : Int32) -> Int32 {
  let variable = if lit < 0 { 0 - lit } else { lit }
  2 * variable + (if lit < 0 { 1 } else { 0 })
}

///|
fn face_sat_lit_value(solver : FaceSatSolver, lit : Int32) -> Int32 {
  let variable = if lit < 0 { 0 - lit } else { lit }
  let value = solver.assignment[variable]
  if value < 0 {
    -1
  } else if lit > 0 {
    value
  } else {
    1 - value
  }
}

///|
fn face_sat_enqueue(solver : FaceSatSolver, lit : Int32) -> Bool {
  let variable = if lit < 0 { 0 - lit } else { lit }
  let wanted = if lit > 0 { 1 } else { 0 }
  let current = solver.assignment[variable]
  if current >= 0 {
    return current == wanted
  }
  solver.assignment[variable] = wanted
  solver.phase[variable] = wanted == 1
  solver.trail.push(lit)
  true
}

///|
fn face_sat_undo_to(solver : FaceSatSolver, length : Int32) -> Unit {
  while solver.trail.length() > length {
    match solver.trail.pop() {
      Some(lit) => {
        let variable = if lit < 0 { 0 - lit } else { lit }
        solver.assignment[variable] = -1
      }
      None => ()
    }
  }
  if solver.qhead > length {
    solver.qhead = length
  }
}

///|
fn face_sat_bump_clause(solver : FaceSatSolver, clause : Array[Int32]) -> Unit {
  for i in 0..<clause.length() {
    let variable = if clause[i] < 0 { 0 - clause[i] } else { clause[i] }
    solver.activity[variable] = solver.activity[variable] + 1.0
  }
}

///|
/// Propagate with watched literals.  Returns a conflicting clause
/// index, `-1` for no conflict, or `-2` on budget exhaustion.
fn face_sat_propagate(solver : FaceSatSolver) -> Int32 {
  while solver.qhead < solver.trail.length() {
    solver.steps = solver.steps + 1
    if solver.max_steps > 0 && solver.steps > solver.max_steps {
      solver.budget_exceeded = true
      return -2
    }
    let true_lit = solver.trail[solver.qhead]
    solver.qhead = solver.qhead + 1
    let false_lit = 0 - true_lit
    let watchers = solver.watches[face_sat_lit_index(false_lit)]
    let mut read = 0
    let mut write = 0
    let mut conflict = -1
    while read < watchers.length() {
      let clause_index = watchers[read]
      read = read + 1
      solver.steps = solver.steps + 1
      if solver.max_steps > 0 && solver.steps > solver.max_steps {
        solver.budget_exceeded = true
        conflict = -2
        // Preserve the unprocessed watchers before returning.
        watchers[write] = clause_index
        write = write + 1
        while read < watchers.length() {
          watchers[write] = watchers[read]
          write = write + 1
          read = read + 1
        }
        break
      }
      let clause = solver.clauses[clause_index]
      if clause.length() < 2 {
        watchers[write] = clause_index
        write = write + 1
        continue
      }
      if clause[0] == false_lit {
        clause[0] = clause[1]
        clause[1] = false_lit
      }
      if clause[1] != false_lit {
        watchers[write] = clause_index
        write = write + 1
        continue
      }
      let other = clause[0]
      if face_sat_lit_value(solver, other) == 1 {
        watchers[write] = clause_index
        write = write + 1
        continue
      }
      let mut replacement = -1
      for k in 2..<clause.length() {
        if face_sat_lit_value(solver, clause[k]) != 0 {
          replacement = k
          break
        }
      }
      if replacement >= 0 {
        let moved = clause[replacement]
        clause[replacement] = clause[1]
        clause[1] = moved
        solver.watches[face_sat_lit_index(moved)].push(clause_index)
        continue
      }
      watchers[write] = clause_index
      write = write + 1
      if face_sat_lit_value(solver, other) == 0 {
        conflict = clause_index
        while read < watchers.length() {
          watchers[write] = watchers[read]
          write = write + 1
          read = read + 1
        }
        break
      }
      if !face_sat_enqueue(solver, other) {
        conflict = clause_index
        while read < watchers.length() {
          watchers[write] = watchers[read]
          write = write + 1
          read = read + 1
        }
        break
      }
    }
    while watchers.length() > write {
      ignore(watchers.pop())
    }
    if conflict >= 0 {
      face_sat_bump_clause(solver, solver.clauses[conflict])
      return conflict
    }
    if conflict == -2 {
      return -2
    }
  }
  -1
}

///|
// Highest-activity unassigned variable, shared by the DPLL and
// CDCL engines (both keep 1-based assignment/activity arrays).
fn solver_pick_variable(
  variables : Int32,
  assignment : Array[Int32],
  activity : Array[Double],
) -> Int32 {
  let mut best = -1
  let mut best_activity = -1.0
  for variable in 1..<(variables + 1) {
    if assignment[variable] < 0 && activity[variable] > best_activity {
      best = variable
      best_activity = activity[variable]
    }
  }
  best
}

///|
fn face_sat_search(solver : FaceSatSolver) -> Int32 {
  let conflict = face_sat_propagate(solver)
  if conflict >= 0 {
    return 0
  }
  if conflict == -2 || solver.budget_exceeded {
    return -1
  }
  let variable = solver_pick_variable(
    solver.variables,
    solver.assignment,
    solver.activity,
  )
  if variable < 0 {
    return 1
  }
  solver.steps = solver.steps + 1
  if solver.max_steps > 0 && solver.steps > solver.max_steps {
    solver.budget_exceeded = true
    return -1
  }
  let checkpoint = solver.trail.length()
  let first_phase = solver.phase[variable]
  for attempt in 0..<2 {
    face_sat_undo_to(solver, checkpoint)
    let phase = if attempt == 0 { first_phase } else { !first_phase }
    let lit = if phase { variable } else { 0 - variable }
    if !face_sat_enqueue(solver, lit) {
      continue
    }
    let result = face_sat_search(solver)
    if result != 0 {
      return result
    }
  }
  face_sat_undo_to(solver, checkpoint)
  0
}

///|
/// Satisfiability by CNF conversion and watched-literal search.
/// `max_steps <= 0` means an unbounded search.
pub fn face_sat_watched_dpll(
  f : Face,
  n : Int32,
  max_steps~ : Int32 = 100000,
) -> FaceSatDecision {
  let builder = face_cnf_build(f, n)
  let variables = builder.next_variable - 1
  let watches : Array[Array[Int32]] = []
  for _i in 0..<(2 * (variables + 2)) {
    watches.push([])
  }
  let assignment : Array[Int32] = []
  let phase : Array[Bool] = []
  let activity : Array[Double] = []
  for _i in 0..<(variables + 1) {
    assignment.push(-1)
    phase.push(true)
    activity.push(0.0)
  }
  let solver = FaceSatSolver::{
    clauses: builder.clauses,
    watches,
    assignment,
    phase,
    activity,
    trail: [],
    qhead: 0,
    variables,
    steps: 0,
    max_steps,
    budget_exceeded: false,
  }
  for ci in 0..<solver.clauses.length() {
    let clause = solver.clauses[ci]
    if clause.length() == 0 {
      return FaceUnsat
    }
    for i in 0..<clause.length() {
      let variable = if clause[i] < 0 { 0 - clause[i] } else { clause[i] }
      solver.activity[variable] = solver.activity[variable] + 1.0
    }
    if clause.length() == 1 {
      if !face_sat_enqueue(solver, clause[0]) {
        return FaceUnsat
      }
    } else {
      solver.watches[face_sat_lit_index(clause[0])].push(ci)
      solver.watches[face_sat_lit_index(clause[1])].push(ci)
    }
  }
  match face_sat_search(solver) {
    1 => {
      let env : Array[Bool] = []
      for i in 0..<n {
        env.push(solver.assignment[i + 1] == 1)
      }
      // The witness is checked before it leaves the solver.
      if face_holds(face_bound(f, n), env) {
        FaceSat(env)
      } else {
        FaceSearchBudgetExceeded
      }
    }
    0 => FaceUnsat
    _ => FaceSearchBudgetExceeded
  }
}

///|
/// Face equality through the watched-literal solver applied to the
/// symmetric difference.
pub fn face_eq_watched_dpll(
  f : Face,
  g : Face,
  n : Int32,
  max_steps~ : Int32 = 100000,
) -> FaceDecision {
  let difference = FOr(FAnd(f, face_not(g)), FAnd(g, face_not(f)))
  match face_sat_watched_dpll(difference, n, max_steps~) {
    FaceSat(_) => FaceDecided(false)
    FaceUnsat => FaceDecided(true)
    FaceSearchBudgetExceeded => FaceBudgetExceeded
  }
}

// ---------------------------------------------------------------------------
// Phase 11: CDCL (conflict-driven clause learning) over the same CNF.
//
// The watched DPLL above backtracks chronologically.  This solver
// keeps the same CNF builder and two-watched-literal propagation,
// but records a reason clause for every propagated literal, and on
// conflict performs first-UIP analysis: the conflicting clause is
// resolved with reason clauses along the trail until a single
// literal of the current decision level remains.  The resolvent is
// learned (it is a resolution consequence of the original CNF, so
// learning is sound), the search back*jumps* to the second-highest
// level in the learned clause, and the learned clause immediately
// propagates there.  Variable selection is VSIDS with phase
// saving; restarts follow the Luby sequence.  At each restart a
// clause-database reduction deletes long, high-LBD learned
// clauses that are not reasons for the level-0 trail, while a
// separate proof log retains every learned clause for auditing.
// ---------------------------------------------------------------------------

///|
pub struct FaceCdclStats {
  decisions : Int32
  conflicts : Int32
  propagations : Int32
  learned : Int32
  deleted : Int32
  restarts : Int32
} derive(Debug, Eq)

///|
pub extend FaceCdclStats with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend FaceCdclStats with Eq::{not_equal, equal}

///|
pub struct FaceCdclResult {
  decision : FaceSatDecision
  stats : FaceCdclStats
}

///|
/// One step of a DRUP proof: add a clause that is a reverse-unit-
/// propagation consequence of the currently active clauses, or
/// delete a currently active clause.  Clause identity for a
/// deletion is literal-set identity, because the solver permutes
/// the two watched literals of a stored clause during search.
pub enum FaceCdclProofStep {
  CdclProofAdd(Array[Int32])
  CdclProofDelete(Array[Int32])
} derive(Debug, Eq)

///|
pub extend FaceCdclProofStep with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend FaceCdclProofStep with Eq::{not_equal, equal}

///|
/// A completed CDCL run together with the clause-level data
/// needed to audit an UNSAT answer independently.  Clauses use
/// the solver's signed-literal encoding (variables are positive
/// integers; negation is arithmetic negation).  For UNSAT,
/// `proof_clauses` is the deletion-free sequence of learned
/// clauses in the order they were derived, followed by the empty
/// clause; every entry is checkable by reverse unit propagation
/// (`face_cdcl_proof_check`).  `proof_steps` is the corresponding
/// DRUP proof: learning and database-reduction steps are recorded
/// in chronological order, followed by the addition of the empty
/// clause, and are checkable against the evolving active clause
/// database by `face_cdcl_drup_check`.
pub struct FaceCdclProofResult {
  decision : FaceSatDecision
  stats : FaceCdclStats
  original_clauses : Array[Array[Int32]]
  proof_clauses : Array[Array[Int32]]
  proof_steps : Array[FaceCdclProofStep]
}

///|
priv struct FaceCdclSolver {
  clauses : Array[Array[Int32]]
  clause_lbd : Array[Int32]
  clause_is_learned : Array[Bool]
  proof_clauses : Array[Array[Int32]]
  proof_steps : Array[FaceCdclProofStep]
  watches : Array[Array[Int32]]
  assignment : Array[Int32]
  level_of : Array[Int32]
  reason_of : Array[Int32]
  phase : Array[Bool]
  activity : Array[Double]
  mut var_inc : Double
  trail : Array[Int32]
  trail_lim : Array[Int32]
  mut qhead : Int32
  variables : Int32
  mut steps : Int32
  max_steps : Int32
  mut budget_exceeded : Bool
  seen : Array[Bool]
  mut decisions : Int32
  mut conflicts : Int32
  mut propagations : Int32
  mut learned_count : Int32
  mut deleted_count : Int32
  mut restarts : Int32
}

///|
fn cdcl_var_of(lit : Int32) -> Int32 {
  if lit < 0 {
    0 - lit
  } else {
    lit
  }
}

///|
fn cdcl_decision_level(solver : FaceCdclSolver) -> Int32 {
  solver.trail_lim.length()
}

///|
fn cdcl_enqueue(solver : FaceCdclSolver, lit : Int32, reason : Int32) -> Bool {
  let variable = cdcl_var_of(lit)
  let wanted = if lit > 0 { 1 } else { 0 }
  let current = solver.assignment[variable]
  if current >= 0 {
    return current == wanted
  }
  solver.assignment[variable] = wanted
  solver.phase[variable] = wanted == 1
  solver.level_of[variable] = cdcl_decision_level(solver)
  solver.reason_of[variable] = reason
  solver.trail.push(lit)
  true
}

///|
fn cdcl_cancel_to(solver : FaceCdclSolver, level : Int32) -> Unit {
  if cdcl_decision_level(solver) <= level {
    return
  }
  let target = solver.trail_lim[level]
  while solver.trail.length() > target {
    match solver.trail.pop() {
      Some(lit) => {
        let variable = cdcl_var_of(lit)
        solver.assignment[variable] = -1
        solver.reason_of[variable] = -1
      }
      None => ()
    }
  }
  while solver.trail_lim.length() > level {
    ignore(solver.trail_lim.pop())
  }
  solver.qhead = solver.trail.length()
}

///|
fn cdcl_lit_value(solver : FaceCdclSolver, lit : Int32) -> Int32 {
  let value = solver.assignment[cdcl_var_of(lit)]
  if value < 0 {
    -1
  } else if lit > 0 {
    value
  } else {
    1 - value
  }
}

///|
/// Watched propagation recording reasons.  Returns a conflicting
/// clause index, `-1` for no conflict, `-2` on budget exhaustion.
fn cdcl_propagate(solver : FaceCdclSolver) -> Int32 {
  while solver.qhead < solver.trail.length() {
    solver.steps = solver.steps + 1
    solver.propagations = solver.propagations + 1
    if solver.max_steps > 0 && solver.steps > solver.max_steps {
      solver.budget_exceeded = true
      return -2
    }
    let true_lit = solver.trail[solver.qhead]
    solver.qhead = solver.qhead + 1
    let false_lit = 0 - true_lit
    let watchers = solver.watches[face_sat_lit_index(false_lit)]
    let mut read = 0
    let mut write = 0
    let mut conflict = -1
    while read < watchers.length() {
      let clause_index = watchers[read]
      read = read + 1
      solver.steps = solver.steps + 1
      if solver.max_steps > 0 && solver.steps > solver.max_steps {
        solver.budget_exceeded = true
        conflict = -2
        watchers[write] = clause_index
        write = write + 1
        while read < watchers.length() {
          watchers[write] = watchers[read]
          write = write + 1
          read = read + 1
        }
        break
      }
      let clause = solver.clauses[clause_index]
      if clause.length() < 2 {
        watchers[write] = clause_index
        write = write + 1
        continue
      }
      if clause[0] == false_lit {
        clause[0] = clause[1]
        clause[1] = false_lit
      }
      if clause[1] != false_lit {
        watchers[write] = clause_index
        write = write + 1
        continue
      }
      let other = clause[0]
      if cdcl_lit_value(solver, other) == 1 {
        watchers[write] = clause_index
        write = write + 1
        continue
      }
      let mut replacement = -1
      for k in 2..<clause.length() {
        if cdcl_lit_value(solver, clause[k]) != 0 {
          replacement = k
          break
        }
      }
      if replacement >= 0 {
        let moved = clause[replacement]
        clause[replacement] = clause[1]
        clause[1] = moved
        solver.watches[face_sat_lit_index(moved)].push(clause_index)
        continue
      }
      watchers[write] = clause_index
      write = write + 1
      if cdcl_lit_value(solver, other) == 0 {
        conflict = clause_index
        while read < watchers.length() {
          watchers[write] = watchers[read]
          write = write + 1
          read = read + 1
        }
        break
      }
      if !cdcl_enqueue(solver, other, clause_index) {
        conflict = clause_index
        while read < watchers.length() {
          watchers[write] = watchers[read]
          write = write + 1
          read = read + 1
        }
        break
      }
    }
    while watchers.length() > write {
      ignore(watchers.pop())
    }
    if conflict >= 0 || conflict == -2 {
      return conflict
    }
  }
  -1
}

///|
fn cdcl_bump(solver : FaceCdclSolver, variable : Int32) -> Unit {
  solver.activity[variable] = solver.activity[variable] + solver.var_inc
  if solver.activity[variable] > 1.0e100 {
    for v in 1..<(solver.variables + 1) {
      solver.activity[v] = solver.activity[v] * 1.0e-100
    }
    solver.var_inc = solver.var_inc * 1.0e-100
  }
}

///|
/// First-UIP conflict analysis.  Returns the learned clause
/// (asserting literal first, highest-level other literal second)
/// and the backjump level.
fn cdcl_analyze(
  solver : FaceCdclSolver,
  conflict_index : Int32,
) -> (Array[Int32], Int32, Int32) {
  let learned : Array[Int32] = [0]
  let touched : Array[Int32] = []
  let current_level = cdcl_decision_level(solver)
  let mut path_count = 0
  let mut p = 0
  let mut index = solver.trail.length() - 1
  let mut clause_index = conflict_index
  while true {
    let clause = solver.clauses[clause_index]
    for qi in 0..<clause.length() {
      let q = clause[qi]
      if q == p && p != 0 {
        continue
      }
      let v = cdcl_var_of(q)
      if !solver.seen[v] && solver.level_of[v] > 0 {
        solver.seen[v] = true
        touched.push(v)
        cdcl_bump(solver, v)
        if solver.level_of[v] >= current_level {
          path_count = path_count + 1
        } else {
          learned.push(q)
        }
      }
    }
    while index >= 0 && !solver.seen[cdcl_var_of(solver.trail[index])] {
      index = index - 1
    }
    if index < 0 {
      break
    }
    p = solver.trail[index]
    index = index - 1
    solver.seen[cdcl_var_of(p)] = false
    path_count = path_count - 1
    if path_count <= 0 {
      break
    }
    clause_index = solver.reason_of[cdcl_var_of(p)]
    if clause_index < 0 {
      break
    }
  }
  learned[0] = 0 - p
  // Literal block distance: the number of distinct decision
  // levels represented in the learned clause.  Low-LBD clauses
  // are the ones retained by database reduction.
  let levels : Array[Int32] = []
  for i in 0..<learned.length() {
    let lv = solver.level_of[cdcl_var_of(learned[i])]
    let mut present = false
    for j in 0..<levels.length() {
      if levels[j] == lv {
        present = true
      }
    }
    if !present {
      levels.push(lv)
    }
  }
  let lbd = levels.length()
  for i in 0..<touched.length() {
    solver.seen[touched[i]] = false
  }
  // Backjump level: maximum level among the non-asserting
  // literals; move such a literal to the second watch position.
  let mut backtrack = 0
  let mut max_pos = -1
  for i in 1..<learned.length() {
    let lv = solver.level_of[cdcl_var_of(learned[i])]
    if lv > backtrack {
      backtrack = lv
      max_pos = i
    }
  }
  if max_pos > 1 {
    let tmp = learned[1]
    learned[1] = learned[max_pos]
    learned[max_pos] = tmp
  }
  (learned, backtrack, lbd)
}

///|
fn cdcl_Luby(x0 : Int32) -> Int32 {
  // The Luby sequence 1,1,2,1,1,2,4,... (0-based restart index),
  // by the standard iterative characterization.
  let mut size = 1
  let mut seq = 0
  while size < x0 + 1 {
    seq = seq + 1
    size = 2 * size + 1
  }
  let mut x = x0
  let mut sz = size
  while sz - 1 != x {
    sz = (sz - 1) / 2
    seq = seq - 1
    x = x % sz
  }
  1 << seq
}

///|
fn cdcl_clone_clause(clause : Array[Int32]) -> Array[Int32] {
  let out : Array[Int32] = []
  for i in 0..<clause.length() {
    out.push(clause[i])
  }
  out
}

///|
/// Learned-clause database reduction, run only at decision level
/// 0 (immediately after a restart).  Original clauses, unit
/// learned clauses and clauses that are reasons for literals
/// still on the trail are always kept.  Among the rest, clauses
/// that are both long and of high literal block distance are
/// deleted; deleting a learned clause is sound because it is a
/// consequence of the original CNF, and the recorded proof copy
/// is not touched.  Clause arrays are compacted in place and all
/// reason indices and watch lists are rebuilt.
fn cdcl_reduce_db(solver : FaceCdclSolver) -> Unit {
  let total = solver.clauses.length()
  let keep_clause : Array[Bool] = []
  for _i in 0..<total {
    keep_clause.push(false)
  }
  for variable in 1..<(solver.variables + 1) {
    let reason = solver.reason_of[variable]
    if reason >= 0 && reason < total {
      keep_clause[reason] = true
    }
  }
  let remap : Array[Int32] = []
  for _i in 0..<total {
    remap.push(-1)
  }
  let mut write = 0
  for read in 0..<total {
    let clause = solver.clauses[read]
    let deletable = solver.clause_is_learned[read] &&
      !keep_clause[read] &&
      clause.length() > 1 &&
      clause.length() > 8 &&
      solver.clause_lbd[read] > 6
    if deletable {
      solver.proof_steps.push(CdclProofDelete(cdcl_clone_clause(clause)))
    }
    if !deletable {
      remap[read] = write
      solver.clauses[write] = clause
      solver.clause_lbd[write] = solver.clause_lbd[read]
      solver.clause_is_learned[write] = solver.clause_is_learned[read]
      write = write + 1
    }
  }
  let removed = total - write
  if removed <= 0 {
    return
  }
  solver.deleted_count = solver.deleted_count + removed
  while solver.clauses.length() > write {
    ignore(solver.clauses.pop())
    ignore(solver.clause_lbd.pop())
    ignore(solver.clause_is_learned.pop())
  }
  for variable in 1..<(solver.variables + 1) {
    let reason = solver.reason_of[variable]
    if reason >= 0 && reason < total {
      solver.reason_of[variable] = remap[reason]
    }
  }
  for w in 0..<solver.watches.length() {
    while solver.watches[w].length() > 0 {
      ignore(solver.watches[w].pop())
    }
  }
  for ci in 0..<solver.clauses.length() {
    let clause = solver.clauses[ci]
    if clause.length() > 1 {
      solver.watches[face_sat_lit_index(clause[0])].push(ci)
      solver.watches[face_sat_lit_index(clause[1])].push(ci)
    }
  }
}

///|
/// CDCL main loop: 1 = SAT, 0 = UNSAT, -1 = budget exceeded.
fn cdcl_search(solver : FaceCdclSolver) -> Int32 {
  let mut restart_count = 0
  let mut conflicts_since_restart = 0
  while true {
    let conflict = cdcl_propagate(solver)
    if conflict == -2 || solver.budget_exceeded {
      return -1
    }
    if conflict >= 0 {
      solver.conflicts = solver.conflicts + 1
      conflicts_since_restart = conflicts_since_restart + 1
      if cdcl_decision_level(solver) == 0 {
        return 0
      }
      let (learned, backtrack, lbd) = cdcl_analyze(solver, conflict)
      cdcl_cancel_to(solver, backtrack)
      let clause_index = solver.clauses.length()
      solver.proof_clauses.push(cdcl_clone_clause(learned))
      solver.proof_steps.push(CdclProofAdd(cdcl_clone_clause(learned)))
      solver.clauses.push(learned)
      solver.clause_lbd.push(lbd)
      solver.clause_is_learned.push(true)
      solver.learned_count = solver.learned_count + 1
      if learned.length() > 1 {
        solver.watches[face_sat_lit_index(learned[0])].push(clause_index)
        solver.watches[face_sat_lit_index(learned[1])].push(clause_index)
      }
      if !cdcl_enqueue(solver, learned[0], clause_index) {
        return 0
      }
      solver.var_inc = solver.var_inc * (1.0 / 0.95)
      if conflicts_since_restart >= cdcl_Luby(restart_count) * 100 {
        cdcl_cancel_to(solver, 0)
        cdcl_reduce_db(solver)
        solver.restarts = solver.restarts + 1
        restart_count = restart_count + 1
        conflicts_since_restart = 0
      }
    } else {
      let variable = solver_pick_variable(
        solver.variables,
        solver.assignment,
        solver.activity,
      )
      if variable < 0 {
        return 1
      }
      solver.steps = solver.steps + 1
      if solver.max_steps > 0 && solver.steps > solver.max_steps {
        solver.budget_exceeded = true
        return -1
      }
      solver.trail_lim.push(solver.trail.length())
      solver.decisions = solver.decisions + 1
      let lit = if solver.phase[variable] { variable } else { 0 - variable }
      ignore(cdcl_enqueue(solver, lit, -1))
    }
  }
  -1
}

///|
fn cdcl_stats_of(solver : FaceCdclSolver) -> FaceCdclStats {
  FaceCdclStats::{
    decisions: solver.decisions,
    conflicts: solver.conflicts,
    propagations: solver.propagations,
    learned: solver.learned_count,
    deleted: solver.deleted_count,
    restarts: solver.restarts,
  }
}

///|
fn cdcl_decision_of(
  code : Int32,
  solver : FaceCdclSolver,
  f : Face,
  n : Int32,
) -> FaceSatDecision {
  match code {
    1 => {
      let env : Array[Bool] = []
      for i in 0..<n {
        env.push(solver.assignment[i + 1] == 1)
      }
      if face_holds(face_bound(f, n), env) {
        FaceSat(env)
      } else {
        FaceSearchBudgetExceeded
      }
    }
    0 => FaceUnsat
    _ => FaceSearchBudgetExceeded
  }
}

///|
/// Build and run a CDCL solver, returning its search code
/// (1 = SAT, 0 = UNSAT, -1 = budget exceeded), the solver, and a
/// pristine copy of the original CNF (the solver permutes watched
/// literals inside its own clause arrays).
fn cdcl_run_solver(
  f : Face,
  n : Int32,
  max_steps : Int32,
) -> (Int32, FaceCdclSolver, Array[Array[Int32]]) {
  let builder = face_cnf_build(f, n)
  let original_clauses : Array[Array[Int32]] = []
  for ci in 0..<builder.clauses.length() {
    original_clauses.push(cdcl_clone_clause(builder.clauses[ci]))
  }
  let variables = builder.next_variable - 1
  let watches : Array[Array[Int32]] = []
  for _i in 0..<(2 * (variables + 2)) {
    watches.push([])
  }
  let assignment : Array[Int32] = []
  let level_of : Array[Int32] = []
  let reason_of : Array[Int32] = []
  let phase : Array[Bool] = []
  let seen : Array[Bool] = []
  let activity : Array[Double] = []
  for _i in 0..<(variables + 1) {
    assignment.push(-1)
    level_of.push(0)
    reason_of.push(-1)
    phase.push(true)
    seen.push(false)
    activity.push(0.0)
  }
  let clause_lbd : Array[Int32] = []
  let clause_is_learned : Array[Bool] = []
  for _i in 0..<builder.clauses.length() {
    clause_lbd.push(0)
    clause_is_learned.push(false)
  }
  let solver = FaceCdclSolver::{
    clauses: builder.clauses,
    clause_lbd,
    clause_is_learned,
    proof_clauses: [],
    proof_steps: [],
    watches,
    assignment,
    level_of,
    reason_of,
    phase,
    activity,
    var_inc: 1.0,
    trail: [],
    trail_lim: [],
    qhead: 0,
    variables,
    steps: 0,
    max_steps,
    budget_exceeded: false,
    seen,
    decisions: 0,
    conflicts: 0,
    propagations: 0,
    learned_count: 0,
    deleted_count: 0,
    restarts: 0,
  }
  for ci in 0..<solver.clauses.length() {
    let clause = solver.clauses[ci]
    if clause.length() == 0 {
      return (0, solver, original_clauses)
    }
    for i in 0..<clause.length() {
      let variable = cdcl_var_of(clause[i])
      solver.activity[variable] = solver.activity[variable] + 1.0
    }
    if clause.length() == 1 {
      if !cdcl_enqueue(solver, clause[0], ci) {
        return (0, solver, original_clauses)
      }
    } else {
      solver.watches[face_sat_lit_index(clause[0])].push(ci)
      solver.watches[face_sat_lit_index(clause[1])].push(ci)
    }
  }
  let code = cdcl_search(solver)
  (code, solver, original_clauses)
}

///|
/// Satisfiability by CDCL with clause learning.  `max_steps <= 0`
/// means an unbounded search.
pub fn face_sat_cdcl_report(
  f : Face,
  n : Int32,
  max_steps~ : Int32 = 100000,
) -> FaceCdclResult {
  let (code, solver, _) = cdcl_run_solver(f, n, max_steps)
  {
    decision: cdcl_decision_of(code, solver, f, n),
    stats: cdcl_stats_of(solver),
  }
}

///|
/// CDCL with independently checkable UNSAT proofs.  On SAT or
/// budget exhaustion both proof fields are empty; on UNSAT
/// `proof_clauses` is the deletion-free RUP sequence and
/// `proof_steps` is the chronological DRUP sequence, each ending
/// with the empty clause.  Audit them with
/// `face_cdcl_proof_check` and `face_cdcl_drup_check` against
/// `original_clauses` from the same result.
pub fn face_sat_cdcl_proof(
  f : Face,
  n : Int32,
  max_steps~ : Int32 = 100000,
) -> FaceCdclProofResult {
  let (code, solver, original_clauses) = cdcl_run_solver(f, n, max_steps)
  let proof_clauses : Array[Array[Int32]] = []
  let proof_steps : Array[FaceCdclProofStep] = []
  if code == 0 {
    for i in 0..<solver.proof_clauses.length() {
      proof_clauses.push(cdcl_clone_clause(solver.proof_clauses[i]))
    }
    proof_clauses.push([])
    for i in 0..<solver.proof_steps.length() {
      match solver.proof_steps[i] {
        CdclProofAdd(clause) =>
          proof_steps.push(CdclProofAdd(cdcl_clone_clause(clause)))
        CdclProofDelete(clause) =>
          proof_steps.push(CdclProofDelete(cdcl_clone_clause(clause)))
      }
    }
    proof_steps.push(CdclProofAdd([]))
  }
  {
    decision: cdcl_decision_of(code, solver, f, n),
    stats: cdcl_stats_of(solver),
    original_clauses,
    proof_clauses,
    proof_steps,
  }
}

///|
fn cdcl_proof_max_var(
  original_clauses : Array[Array[Int32]],
  proof_clauses : Array[Array[Int32]],
) -> Int32 {
  let mut best = 0
  for ci in 0..<original_clauses.length() {
    let clause = original_clauses[ci]
    for i in 0..<clause.length() {
      let v = cdcl_var_of(clause[i])
      if v > best {
        best = v
      }
    }
  }
  for ci in 0..<proof_clauses.length() {
    let clause = proof_clauses[ci]
    for i in 0..<clause.length() {
      let v = cdcl_var_of(clause[i])
      if v > best {
        best = v
      }
    }
  }
  best
}

///|
fn cdcl_proof_lit_value(assignment : Array[Int32], lit : Int32) -> Int32 {
  let value = assignment[cdcl_var_of(lit)]
  if value < 0 {
    -1
  } else if lit > 0 {
    value
  } else {
    1 - value
  }
}

///|
/// Whether assuming every literal of `assumptions` true makes
/// `clauses` conflict under unit propagation.
fn cdcl_proof_up_conflict(
  clauses : Array[Array[Int32]],
  assumptions : Array[Int32],
  max_var : Int32,
) -> Bool {
  let assignment : Array[Int32] = []
  for _i in 0..<(max_var + 1) {
    assignment.push(-1)
  }
  for i in 0..<assumptions.length() {
    let lit = assumptions[i]
    if lit == 0 {
      return false
    }
    let variable = cdcl_var_of(lit)
    let wanted = if lit > 0 { 1 } else { 0 }
    if assignment[variable] >= 0 && assignment[variable] != wanted {
      return true
    }
    assignment[variable] = wanted
  }
  while true {
    let mut changed = false
    for ci in 0..<clauses.length() {
      let clause = clauses[ci]
      let mut satisfied = false
      let mut open_count = 0
      let mut open_lit = 0
      for i in 0..<clause.length() {
        let lit = clause[i]
        if lit == 0 || cdcl_var_of(lit) > max_var {
          return false
        }
        let value = cdcl_proof_lit_value(assignment, lit)
        if value == 1 {
          satisfied = true
        } else if value < 0 {
          open_count = open_count + 1
          open_lit = lit
        }
      }
      if satisfied {
        continue
      }
      if open_count == 0 {
        return true
      }
      if open_count == 1 {
        let variable = cdcl_var_of(open_lit)
        let wanted = if open_lit > 0 { 1 } else { 0 }
        if assignment[variable] < 0 {
          assignment[variable] = wanted
          changed = true
        } else if assignment[variable] != wanted {
          return true
        }
      }
    }
    if !changed {
      return false
    }
  }
  false
}

///|
/// Check a CDCL UNSAT proof by reverse unit propagation: each
/// proof clause must become conflicting when all of its literals
/// are assumed false, using only the original clauses and the
/// proof clauses before it; the final proof clause must be
/// empty.  This is the standard RUP audit and is independent of
/// the solver's watch lists, activities and deletion policy.
pub fn face_cdcl_proof_check(
  original_clauses : Array[Array[Int32]],
  proof_clauses : Array[Array[Int32]],
) -> Bool {
  if proof_clauses.length() == 0 {
    return false
  }
  if proof_clauses[proof_clauses.length() - 1].length() != 0 {
    return false
  }
  let max_var = cdcl_proof_max_var(original_clauses, proof_clauses)
  let db : Array[Array[Int32]] = []
  for ci in 0..<original_clauses.length() {
    db.push(original_clauses[ci])
  }
  for pi in 0..<proof_clauses.length() {
    let clause = proof_clauses[pi]
    let assumptions : Array[Int32] = []
    for i in 0..<clause.length() {
      if clause[i] == 0 {
        return false
      }
      assumptions.push(0 - clause[i])
    }
    if !cdcl_proof_up_conflict(db, assumptions, max_var) {
      return false
    }
    db.push(clause)
  }
  true
}

///|
fn cdcl_clause_contains(clause : Array[Int32], lit : Int32) -> Bool {
  for i in 0..<clause.length() {
    if clause[i] == lit {
      return true
    }
  }
  false
}

///|
/// Literal-set equality for DRUP deletions.  Literal order and
/// duplicates are ignored, matching the logical identity of a
/// clause and the solver's watched-literal permutations.
fn cdcl_clause_set_equal(a : Array[Int32], b : Array[Int32]) -> Bool {
  for i in 0..<a.length() {
    if !cdcl_clause_contains(b, a[i]) {
      return false
    }
  }
  for i in 0..<b.length() {
    if !cdcl_clause_contains(a, b[i]) {
      return false
    }
  }
  true
}

///|
fn cdcl_drup_max_var(
  original_clauses : Array[Array[Int32]],
  proof_steps : Array[FaceCdclProofStep],
) -> Int32 {
  let mut best = 0
  for ci in 0..<original_clauses.length() {
    let clause = original_clauses[ci]
    for i in 0..<clause.length() {
      let v = cdcl_var_of(clause[i])
      if v > best {
        best = v
      }
    }
  }
  for si in 0..<proof_steps.length() {
    let clause = match proof_steps[si] {
      CdclProofAdd(c) => c
      CdclProofDelete(c) => c
    }
    for i in 0..<clause.length() {
      let v = cdcl_var_of(clause[i])
      if v > best {
        best = v
      }
    }
  }
  best
}

///|
/// Check a DRUP proof against the evolving active clause
/// database.  An addition must be a RUP consequence of the
/// clauses active at that point; a deletion must name an active
/// clause (up to literal order and duplicates) and removes one
/// occurrence of it.  The unique empty-clause addition must be
/// the final step.  This audits CDCL proofs "in the presence
/// of solver deletion": a clause deleted by database reduction
/// can no longer be used to justify later additions.
pub fn face_cdcl_drup_check(
  original_clauses : Array[Array[Int32]],
  proof_steps : Array[FaceCdclProofStep],
) -> Bool {
  if proof_steps.length() == 0 {
    return false
  }
  match proof_steps[proof_steps.length() - 1] {
    CdclProofAdd(clause) => if clause.length() != 0 { return false }
    CdclProofDelete(_) => return false
  }
  let max_var = cdcl_drup_max_var(original_clauses, proof_steps)
  let mut active : Array[Array[Int32]] = []
  for ci in 0..<original_clauses.length() {
    active.push(original_clauses[ci])
  }
  for si in 0..<proof_steps.length() {
    match proof_steps[si] {
      CdclProofAdd(clause) => {
        if clause.length() == 0 && si != proof_steps.length() - 1 {
          return false
        }
        let assumptions : Array[Int32] = []
        for i in 0..<clause.length() {
          if clause[i] == 0 {
            return false
          }
          assumptions.push(0 - clause[i])
        }
        if !cdcl_proof_up_conflict(active, assumptions, max_var) {
          return false
        }
        active.push(clause)
      }
      CdclProofDelete(clause) => {
        for i in 0..<clause.length() {
          if clause[i] == 0 {
            return false
          }
        }
        let mut found = -1
        for ci in 0..<active.length() {
          if cdcl_clause_set_equal(active[ci], clause) {
            found = ci
            break
          }
        }
        if found < 0 {
          return false
        }
        let next : Array[Array[Int32]] = []
        for ci in 0..<active.length() {
          if ci != found {
            next.push(active[ci])
          }
        }
        active = next
      }
    }
  }
  true
}

///|
pub struct FaceDrupTrimReport {
  valid : Bool
  original_steps : Int32
  trimmed_steps : Int32
  steps : Array[FaceCdclProofStep]
}

///|
fn cdcl_clause_is_tautology(clause : Array[Int32]) -> Bool {
  for i in 0..<clause.length() {
    for j in (i + 1)..<clause.length() {
      if clause[i] == 0 - clause[j] {
        return true
      }
    }
  }
  false
}

///|
/// Check a DRAT (Delete Resolution Asymmetric Tautology) proof over
/// the evolving active clause database.  Each `CdclProofAdd(C)` step
/// must either be RUP, or be RAT on its leading pivot literal `C[0]`
/// (for every active clause `D` containing `-C[0]`, the resolvent
/// `C ∪ (D \ {-C[0]})` is tautological or RUP).  Deletions follow
/// literal-set identity, and the final step must be `CdclProofAdd([])`.
pub fn face_cdcl_drat_check(
  original_clauses : Array[Array[Int32]],
  proof_steps : Array[FaceCdclProofStep],
) -> Bool {
  if proof_steps.length() == 0 {
    return false
  }
  match proof_steps[proof_steps.length() - 1] {
    CdclProofAdd(clause) => if clause.length() != 0 { return false }
    CdclProofDelete(_) => return false
  }
  let max_var = cdcl_drup_max_var(original_clauses, proof_steps)
  let mut active : Array[Array[Int32]] = []
  for ci in 0..<original_clauses.length() {
    active.push(original_clauses[ci])
  }
  for si in 0..<proof_steps.length() {
    match proof_steps[si] {
      CdclProofAdd(clause) => {
        if clause.length() == 0 && si != proof_steps.length() - 1 {
          return false
        }
        for i in 0..<clause.length() {
          if clause[i] == 0 {
            return false
          }
        }
        if cdcl_clause_is_tautology(clause) {
          active.push(clause)
          continue
        }
        let assumptions : Array[Int32] = []
        for i in 0..<clause.length() {
          assumptions.push(0 - clause[i])
        }
        let mut accepted = cdcl_proof_up_conflict(active, assumptions, max_var)
        if !accepted && clause.length() > 0 {
          let pivot = clause[0]
          let neg_pivot = 0 - pivot
          let mut rat_ok = true
          for di in 0..<active.length() {
            let d = active[di]
            if !cdcl_clause_contains(d, neg_pivot) {
              continue
            }
            let resolvent : Array[Int32] = []
            for i in 0..<clause.length() {
              if !cdcl_clause_contains(resolvent, clause[i]) {
                resolvent.push(clause[i])
              }
            }
            for i in 0..<d.length() {
              if d[i] != neg_pivot && !cdcl_clause_contains(resolvent, d[i]) {
                resolvent.push(d[i])
              }
            }
            if cdcl_clause_is_tautology(resolvent) {
              continue
            }
            let res_assump : Array[Int32] = []
            for i in 0..<resolvent.length() {
              res_assump.push(0 - resolvent[i])
            }
            if !cdcl_proof_up_conflict(active, res_assump, max_var) {
              rat_ok = false
              break
            }
          }
          accepted = rat_ok
        }
        if !accepted {
          return false
        }
        active.push(clause)
      }
      CdclProofDelete(clause) => {
        for i in 0..<clause.length() {
          if clause[i] == 0 {
            return false
          }
        }
        let mut found = -1
        for ci in 0..<active.length() {
          if cdcl_clause_set_equal(active[ci], clause) {
            found = ci
            break
          }
        }
        if found < 0 {
          return false
        }
        let next : Array[Array[Int32]] = []
        for ci in 0..<active.length() {
          if ci != found {
            next.push(active[ci])
          }
        }
        active = next
      }
    }
  }
  true
}

///|
/// Reverse unit propagation returning a minimal topologically ordered
/// sequence of active clause IDs (`hint_chain`) whose unit propagations
/// end at a falsified conflict clause under `assumptions`.
fn cdcl_up_conflict_ordered_chain(
  active : Array[Array[Int32]],
  active_ids : Array[Int32],
  assumptions : Array[Int32],
  max_var : Int32,
) -> (Bool, Array[Int32]) {
  let val_arr : Array[Int32] = []
  let reason_slot : Array[Int32] = []
  for _v in 0..<(max_var + 1) {
    val_arr.push(0)
    reason_slot.push(-1)
  }
  for i in 0..<assumptions.length() {
    let lit = assumptions[i]
    let v = cdcl_var_of(lit)
    let sign = if lit > 0 { 1 } else { -1 }
    if val_arr[v] == 0 - sign {
      return (true, [])
    }
    if val_arr[v] == 0 {
      val_arr[v] = sign
    }
  }
  let prop_vars : Array[Int32] = []
  let prop_slots : Array[Int32] = []
  let mut conflict_slot = -1
  let mut progress = true
  while progress && conflict_slot < 0 {
    progress = false
    for ci in 0..<active.length() {
      let c = active[ci]
      let mut sat = false
      let mut unassigned_count = 0
      let mut last_lit = 0
      for i in 0..<c.length() {
        let lit = c[i]
        let v = cdcl_var_of(lit)
        let s = if lit > 0 { 1 } else { -1 }
        if val_arr[v] == s {
          sat = true
          break
        }
        if val_arr[v] == 0 {
          unassigned_count = unassigned_count + 1
          last_lit = lit
        }
      }
      if sat {
        continue
      }
      if unassigned_count == 0 {
        conflict_slot = ci
        break
      }
      if unassigned_count == 1 {
        let v = cdcl_var_of(last_lit)
        val_arr[v] = if last_lit > 0 { 1 } else { -1 }
        reason_slot[v] = prop_vars.length()
        prop_vars.push(v)
        prop_slots.push(ci)
        progress = true
      }
    }
  }
  if conflict_slot < 0 {
    return (false, [])
  }
  let needed_var : Array[Bool] = []
  for _v in 0..<(max_var + 1) {
    needed_var.push(false)
  }
  let needed_prop : Array[Bool] = []
  for _p in 0..<prop_vars.length() {
    needed_prop.push(false)
  }
  let conf_c = active[conflict_slot]
  for i in 0..<conf_c.length() {
    needed_var[cdcl_var_of(conf_c[i])] = true
  }
  let mut pi = prop_vars.length() - 1
  while pi >= 0 {
    let v = prop_vars[pi]
    if needed_var[v] {
      needed_prop[pi] = true
      let rc = active[prop_slots[pi]]
      for j in 0..<rc.length() {
        needed_var[cdcl_var_of(rc[j])] = true
      }
    }
    pi = pi - 1
  }
  let chain : Array[Int32] = []
  for i in 0..<prop_vars.length() {
    if needed_prop[i] {
      let cid = active_ids[prop_slots[i]]
      if cid >= 0 {
        chain.push(cid)
      }
    }
  }
  let conf_id = active_ids[conflict_slot]
  if conf_id >= 0 {
    chain.push(conf_id)
  }
  (true, chain)
}

///|
/// Backward conflict-core trimming of a DRUP proof: replays unit
/// propagation while recording propagation-reason dependencies, marks
/// only additions reachable from the final empty clause, and emits an
/// audited core proof verified by `face_cdcl_drup_check`.
pub fn face_cdcl_drup_trim(
  original_clauses : Array[Array[Int32]],
  proof_steps : Array[FaceCdclProofStep],
) -> FaceDrupTrimReport {
  if !face_cdcl_drup_check(original_clauses, proof_steps) {
    return FaceDrupTrimReport::{
      valid: false,
      original_steps: proof_steps.length(),
      trimmed_steps: 0,
      steps: [],
    }
  }
  let max_var = cdcl_drup_max_var(original_clauses, proof_steps)
  let mut active : Array[Array[Int32]] = []
  let mut active_ids : Array[Int32] = []
  for ci in 0..<original_clauses.length() {
    active.push(original_clauses[ci])
    active_ids.push(-1)
  }
  let step_deps : Array[Array[Int32]] = []
  for si in 0..<proof_steps.length() {
    match proof_steps[si] {
      CdclProofAdd(clause) => {
        let assumptions : Array[Int32] = []
        for i in 0..<clause.length() {
          assumptions.push(0 - clause[i])
        }
        let (ok, deps) = cdcl_up_conflict_ordered_chain(
          active, active_ids, assumptions, max_var,
        )
        if !ok {
          return FaceDrupTrimReport::{
            valid: false,
            original_steps: proof_steps.length(),
            trimmed_steps: 0,
            steps: [],
          }
        }
        step_deps.push(deps)
        active.push(clause)
        active_ids.push(si)
      }
      CdclProofDelete(clause) => {
        step_deps.push([])
        let mut found = -1
        for ci in 0..<active.length() {
          if cdcl_clause_set_equal(active[ci], clause) {
            found = ci
            break
          }
        }
        if found >= 0 {
          let next_c : Array[Array[Int32]] = []
          let next_id : Array[Int32] = []
          for ci in 0..<active.length() {
            if ci != found {
              next_c.push(active[ci])
              next_id.push(active_ids[ci])
            }
          }
          active = next_c
          active_ids = next_id
        }
      }
    }
  }
  let needed : Array[Bool] = []
  for _si in 0..<proof_steps.length() {
    needed.push(false)
  }
  needed[proof_steps.length() - 1] = true
  let mut idx = proof_steps.length() - 1
  while idx >= 0 {
    if needed[idx] {
      let deps = step_deps[idx]
      for i in 0..<deps.length() {
        let d = deps[i]
        if d >= 0 && d < idx {
          needed[d] = true
        }
      }
    }
    idx = idx - 1
  }
  let trimmed : Array[FaceCdclProofStep] = []
  for si in 0..<proof_steps.length() {
    if needed[si] {
      match proof_steps[si] {
        CdclProofAdd(c) => trimmed.push(CdclProofAdd(c))
        CdclProofDelete(_) => ()
      }
    }
  }
  let ok = face_cdcl_drup_check(original_clauses, trimmed)
  FaceDrupTrimReport::{
    valid: ok,
    original_steps: proof_steps.length(),
    trimmed_steps: trimmed.length(),
    steps: if ok {
      trimmed
    } else {
      []
    },
  }
}

///|
/// Indexed LRAT (Linear Resolution Asymmetric Tautology) proof step:
/// - `LratAdd(clause_id, literals, rup_hints, rat_hints)`: introduces a
///   clause at strictly increasing `clause_id` (`> original_clauses.length()`),
///   justified either by an explicit topological unit-propagation chain
///   `rup_hints` or (when `rup_hints` is empty and `literals` is non-empty)
///   by RAT resolution chains `(neg_pivot_clause_id, sub_hints)` on pivot
///   `literals[0]`.
/// - `LratDelete(step_id, deleted_clause_ids)`: deletes active clauses in
///   `O(1)` per ID without literal-set scanning.
pub(all) enum FaceLratStep {
  LratAdd(
    Int32,
    Array[Int32],
    Array[Int32],
    Array[(Int32, Array[Int32])]
  )
  LratDelete(Int32, Array[Int32])
} derive(Debug, Eq)

///|
pub extend FaceLratStep with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend FaceLratStep with Eq::{not_equal, equal}

///|
pub(all) struct FaceLratElaborateReport {
  valid : Bool
  original_clauses : Int32
  input_steps : Int32
  lrat_adds : Int32
  lrat_deletes : Int32
  total_hints : Int32
  steps : Array[FaceLratStep]
} derive(Debug, Eq)

///|
pub extend FaceLratElaborateReport with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend FaceLratElaborateReport with Eq::{not_equal, equal}

///|
fn lrat_lit_index(lit : Int32) -> Int32 {
  let v = cdcl_var_of(lit)
  if lit > 0 {
    2 * v
  } else {
    2 * v + 1
  }
}

///|
/// Zero-search linear-time LRAT proof checker.
///
/// Original CNF clauses receive 1-based IDs `1 .. M` (`M = original_clauses.length()`).
/// Every `LratAdd` RUP step is verified solely by stepping through its
/// `rup_hints` array: each hinted clause must be active, non-satisfied,
/// and have at most one unassigned literal (`1` propagates; `0` must
/// occur on the final hint as the falsified conflict clause).  Any hint
/// with `>= 2` unassigned literals, an already-satisfied literal, an
/// inactive/deleted ID, or trailing hints after conflict is immediately
/// rejected without searching the active database.  Pure RAT steps verify
/// exhaustive coverage of active `-pivot` clauses via per-literal
/// occurrence lists plus zero-search RUP verification of each resolvent.
pub fn face_cdcl_lrat_check(
  original_clauses : Array[Array[Int32]],
  lrat_steps : Array[FaceLratStep],
) -> Bool {
  if lrat_steps.length() == 0 {
    return false
  }
  match lrat_steps[lrat_steps.length() - 1] {
    LratAdd(_, clause, _, _) => if clause.length() != 0 { return false }
    LratDelete(_, _) => return false
  }
  let orig_count = original_clauses.length()
  let mut max_id = orig_count
  let mut max_var = 0
  for ci in 0..<orig_count {
    let c = original_clauses[ci]
    for j in 0..<c.length() {
      let lit = c[j]
      if lit == 0 {
        return false
      }
      let v = cdcl_var_of(lit)
      if v > max_var {
        max_var = v
      }
    }
  }
  let mut prev_id = orig_count
  for si in 0..<lrat_steps.length() {
    match lrat_steps[si] {
      LratAdd(cid, clause, _, _) => {
        if cid <= prev_id {
          return false
        }
        if clause.length() == 0 && si != lrat_steps.length() - 1 {
          return false
        }
        for j in 0..<clause.length() {
          let lit = clause[j]
          if lit == 0 {
            return false
          }
          let v = cdcl_var_of(lit)
          if v > max_var {
            max_var = v
          }
        }
        prev_id = cid
        if cid > max_id {
          max_id = cid
        }
      }
      LratDelete(sid, del_ids) => {
        if sid < prev_id || del_ids.length() == 0 {
          return false
        }
        prev_id = sid
        if sid > max_id {
          max_id = sid
        }
      }
    }
  }

  let clauses_by_id : Array[Array[Int32]] = []
  let is_active : Array[Bool] = []
  for _i in 0..<(max_id + 1) {
    clauses_by_id.push([])
    is_active.push(false)
  }
  let occ : Array[Array[Int32]] = []
  for _li in 0..<(2 * max_var + 2) {
    occ.push([])
  }
  let register_clause = (cid : Int32, c : Array[Int32]) => {
    clauses_by_id[cid] = c
    is_active[cid] = true
    for j in 0..<c.length() {
      let li = lrat_lit_index(c[j])
      if !cdcl_clause_contains(occ[li], cid) {
        occ[li].push(cid)
      }
    }
  }
  for ci in 0..<orig_count {
    register_clause(ci + 1, original_clauses[ci])
  }

  let val_arr : Array[Int32] = []
  for _v in 0..<(max_var + 1) {
    val_arr.push(0)
  }
  let touched : Array[Int32] = []
  let reset_touched = () => {
    while touched.length() > 0 {
      let v = touched[touched.length() - 1]
      let _ = touched.pop()
      val_arr[v] = 0
    }
  }

  let verify_hint_chain = (
    assumptions : Array[Int32],
    hints : Array[Int32],
  ) => {
    let mut trivial_conflict = false
    for i in 0..<assumptions.length() {
      let lit = assumptions[i]
      let v = cdcl_var_of(lit)
      let s = if lit > 0 { 1 } else { -1 }
      if val_arr[v] == 0 - s {
        trivial_conflict = true
        break
      }
      if val_arr[v] == 0 {
        val_arr[v] = s
        touched.push(v)
      }
    }
    if trivial_conflict {
      reset_touched()
      return hints.length() == 0
    }
    if hints.length() == 0 {
      reset_touched()
      return false
    }
    for hi in 0..<hints.length() {
      let hid = hints[hi]
      if hid <= 0 || hid > max_id || !is_active[hid] {
        reset_touched()
        return false
      }
      let c = clauses_by_id[hid]
      let mut sat = false
      let mut unassigned_count = 0
      let mut last_lit = 0
      for j in 0..<c.length() {
        let lit = c[j]
        let v = cdcl_var_of(lit)
        let s = if lit > 0 { 1 } else { -1 }
        if val_arr[v] == s {
          sat = true
          break
        }
        if val_arr[v] == 0 {
          unassigned_count = unassigned_count + 1
          last_lit = lit
          if unassigned_count >= 2 {
            break
          }
        }
      }
      if sat || unassigned_count >= 2 {
        reset_touched()
        return false
      }
      if unassigned_count == 0 {
        reset_touched()
        return hi == hints.length() - 1
      }
      // Exactly 1 unassigned literal: must propagate before final conflict hint.
      if hi == hints.length() - 1 {
        reset_touched()
        return false
      }
      let pv = cdcl_var_of(last_lit)
      val_arr[pv] = if last_lit > 0 { 1 } else { -1 }
      touched.push(pv)
    }
    reset_touched()
    false
  }

  for si in 0..<lrat_steps.length() {
    match lrat_steps[si] {
      LratAdd(cid, clause, rup_hints, rat_hints) => {
        if cdcl_clause_is_tautology(clause) {
          if rup_hints.length() != 0 || rat_hints.length() != 0 {
            return false
          }
          register_clause(cid, clause)
          continue
        }
        if rup_hints.length() > 0 || rat_hints.length() == 0 {
          if rat_hints.length() != 0 {
            return false
          }
          let assump : Array[Int32] = []
          for j in 0..<clause.length() {
            assump.push(0 - clause[j])
          }
          if !verify_hint_chain(assump, rup_hints) {
            return false
          }
          register_clause(cid, clause)
        } else {
          // Pure RAT step on leading literal `clause[0]`.
          if clause.length() == 0 {
            return false
          }
          let pivot = clause[0]
          let neg_pivot = 0 - pivot
          let seen_rat_ids : Array[Int32] = []
          for ri in 0..<rat_hints.length() {
            let (dcid, sub_hints) = rat_hints[ri]
            if dcid <= 0 ||
              dcid > max_id ||
              !is_active[dcid] ||
              cdcl_clause_contains(seen_rat_ids, dcid) {
              return false
            }
            let d = clauses_by_id[dcid]
            if !cdcl_clause_contains(d, neg_pivot) {
              return false
            }
            seen_rat_ids.push(dcid)
            let resolvent : Array[Int32] = []
            for j in 0..<clause.length() {
              if !cdcl_clause_contains(resolvent, clause[j]) {
                resolvent.push(clause[j])
              }
            }
            for j in 0..<d.length() {
              if d[j] != neg_pivot && !cdcl_clause_contains(resolvent, d[j]) {
                resolvent.push(d[j])
              }
            }
            if cdcl_clause_is_tautology(resolvent) {
              if sub_hints.length() != 0 {
                return false
              }
            } else {
              let res_assump : Array[Int32] = []
              for j in 0..<resolvent.length() {
                res_assump.push(0 - resolvent[j])
              }
              if !verify_hint_chain(res_assump, sub_hints) {
                return false
              }
            }
          }
          // Verify that no active clause containing `-pivot` with a
          // non-tautological resolvent was omitted from `rat_hints`.
          let neg_list = occ[lrat_lit_index(neg_pivot)]
          for oi in 0..<neg_list.length() {
            let ocid = neg_list[oi]
            if !is_active[ocid] || cdcl_clause_contains(seen_rat_ids, ocid) {
              continue
            }
            let d = clauses_by_id[ocid]
            let resolvent : Array[Int32] = []
            for j in 0..<clause.length() {
              if !cdcl_clause_contains(resolvent, clause[j]) {
                resolvent.push(clause[j])
              }
            }
            for j in 0..<d.length() {
              if d[j] != neg_pivot && !cdcl_clause_contains(resolvent, d[j]) {
                resolvent.push(d[j])
              }
            }
            if !cdcl_clause_is_tautology(resolvent) {
              return false
            }
          }
          register_clause(cid, clause)
        }
      }
      LratDelete(_, del_ids) =>
        for di in 0..<del_ids.length() {
          let did = del_ids[di]
          if did <= 0 || did > max_id || !is_active[did] {
            return false
          }
          is_active[did] = false
        }
    }
  }
  true
}

///|
/// Elaborate any valid DRUP or DRAT proof into a backward-trimmed,
/// deletion-scheduled indexed LRAT proof, and self-audit the result via
/// `face_cdcl_lrat_check`.
///
/// NOTE: For pure RAT steps (`rup_hints == []`), deleting an active
/// clause earlier than in the source proof could introduce *fewer* `-pivot`
/// obligations, which is sound, whereas keeping extra active `-pivot`
/// clauses not present in the source proof could break a later RAT step!
/// Therefore:
/// - If the proof contains any pure RAT step, we preserve source deletions
///   faithfully (emitting `LratDelete` at exact deletion points) while
///   annotating every step with exact ordered unit-propagation hint chains.
/// - On pure DRUP proofs (such as all CDCL refutations), we perform full
///   backward dependency-core trimming AND emit scheduled `LratDelete`
///   steps immediately after each clause's final reference!
pub fn face_cdcl_elaborate_lrat(
  original_clauses : Array[Array[Int32]],
  proof_steps : Array[FaceCdclProofStep],
) -> FaceLratElaborateReport {
  let orig_count = original_clauses.length()
  let fail_rep = FaceLratElaborateReport::{
    valid: false,
    original_clauses: orig_count,
    input_steps: proof_steps.length(),
    lrat_adds: 0,
    lrat_deletes: 0,
    total_hints: 0,
    steps: [],
  }
  if proof_steps.length() == 0 {
    return fail_rep
  }
  match proof_steps[proof_steps.length() - 1] {
    CdclProofAdd(c) => if c.length() != 0 { return fail_rep }
    CdclProofDelete(_) => return fail_rep
  }
  let max_var = cdcl_drup_max_var(original_clauses, proof_steps)
  let mut active : Array[Array[Int32]] = []
  let mut active_ids : Array[Int32] = []
  for ci in 0..<orig_count {
    for j in 0..<original_clauses[ci].length() {
      if original_clauses[ci][j] == 0 {
        return fail_rep
      }
    }
    active.push(original_clauses[ci])
    active_ids.push(ci + 1)
  }

  let raw_is_add : Array[Bool] = []
  let raw_cid : Array[Int32] = []
  let raw_clause : Array[Array[Int32]] = []
  let raw_rup : Array[Array[Int32]] = []
  let raw_rat : Array[Array[(Int32, Array[Int32])]] = []
  let raw_del : Array[Int32] = []
  let mut next_cid = orig_count + 1
  let mut has_rat_step = false

  for si in 0..<proof_steps.length() {
    match proof_steps[si] {
      CdclProofAdd(clause) => {
        if clause.length() == 0 && si != proof_steps.length() - 1 {
          return fail_rep
        }
        for j in 0..<clause.length() {
          if clause[j] == 0 {
            return fail_rep
          }
        }
        let cid = next_cid
        next_cid = next_cid + 1
        if cdcl_clause_is_tautology(clause) {
          raw_is_add.push(true)
          raw_cid.push(cid)
          raw_clause.push(clause)
          raw_rup.push([])
          raw_rat.push([])
          raw_del.push(-1)
          active.push(clause)
          active_ids.push(cid)
          continue
        }
        let assump : Array[Int32] = []
        for j in 0..<clause.length() {
          assump.push(0 - clause[j])
        }
        let (rup_ok, rup_chain) = cdcl_up_conflict_ordered_chain(
          active, active_ids, assump, max_var,
        )
        if rup_ok {
          raw_is_add.push(true)
          raw_cid.push(cid)
          raw_clause.push(clause)
          raw_rup.push(rup_chain)
          raw_rat.push([])
          raw_del.push(-1)
          active.push(clause)
          active_ids.push(cid)
        } else {
          if clause.length() == 0 {
            return fail_rep
          }
          has_rat_step = true
          let pivot = clause[0]
          let neg_pivot = 0 - pivot
          let rat_pairs : Array[(Int32, Array[Int32])] = []
          for di in 0..<active.length() {
            let d = active[di]
            if !cdcl_clause_contains(d, neg_pivot) {
              continue
            }
            let resolvent : Array[Int32] = []
            for j in 0..<clause.length() {
              if !cdcl_clause_contains(resolvent, clause[j]) {
                resolvent.push(clause[j])
              }
            }
            for j in 0..<d.length() {
              if d[j] != neg_pivot && !cdcl_clause_contains(resolvent, d[j]) {
                resolvent.push(d[j])
              }
            }
            if cdcl_clause_is_tautology(resolvent) {
              continue
            }
            let res_assump : Array[Int32] = []
            for j in 0..<resolvent.length() {
              res_assump.push(0 - resolvent[j])
            }
            let (sub_ok, sub_chain) = cdcl_up_conflict_ordered_chain(
              active, active_ids, res_assump, max_var,
            )
            if !sub_ok {
              return fail_rep
            }
            rat_pairs.push((active_ids[di], sub_chain))
          }
          raw_is_add.push(true)
          raw_cid.push(cid)
          raw_clause.push(clause)
          raw_rup.push([])
          raw_rat.push(rat_pairs)
          raw_del.push(-1)
          active.push(clause)
          active_ids.push(cid)
        }
      }
      CdclProofDelete(clause) => {
        for j in 0..<clause.length() {
          if clause[j] == 0 {
            return fail_rep
          }
        }
        let mut found = -1
        for ci in 0..<active.length() {
          if cdcl_clause_set_equal(active[ci], clause) {
            found = ci
            break
          }
        }
        if found < 0 {
          return fail_rep
        }
        let dcid = active_ids[found]
        let next_c : Array[Array[Int32]] = []
        let next_id : Array[Int32] = []
        for ci in 0..<active.length() {
          if ci != found {
            next_c.push(active[ci])
            next_id.push(active_ids[ci])
          }
        }
        active = next_c
        active_ids = next_id
        raw_is_add.push(false)
        raw_cid.push(next_cid - 1)
        raw_clause.push([])
        raw_rup.push([])
        raw_rat.push([])
        raw_del.push(dcid)
      }
    }
  }

  let out_steps : Array[FaceLratStep] = []
  let mut add_count = 0
  let mut del_count = 0
  let mut hint_count = 0

  if has_rat_step {
    for si in 0..<raw_is_add.length() {
      if raw_is_add[si] {
        add_count = add_count + 1
        hint_count = hint_count + raw_rup[si].length()
        for ri in 0..<raw_rat[si].length() {
          hint_count = hint_count + raw_rat[si][ri].1.length()
        }
        out_steps.push(
          LratAdd(raw_cid[si], raw_clause[si], raw_rup[si], raw_rat[si]),
        )
      } else {
        del_count = del_count + 1
        out_steps.push(LratDelete(raw_cid[si], [raw_del[si]]))
      }
    }
  } else {
    // Pure DRUP proof: backward conflict-core trim + compact ID renumbering
    // + automatic last-use `LratDelete` scheduling.
    let step_by_cid : Array[Int32] = []
    for _i in 0..<next_cid {
      step_by_cid.push(-1)
    }
    for si in 0..<raw_is_add.length() {
      if raw_is_add[si] {
        step_by_cid[raw_cid[si]] = si
      }
    }
    let needed_cid : Array[Bool] = []
    for _i in 0..<next_cid {
      needed_cid.push(false)
    }
    let final_cid = raw_cid[raw_is_add.length() - 1]
    needed_cid[final_cid] = true
    let mut cid_cursor = final_cid
    while cid_cursor > orig_count {
      if needed_cid[cid_cursor] {
        let si = step_by_cid[cid_cursor]
        if si >= 0 {
          let chain = raw_rup[si]
          for hi in 0..<chain.length() {
            let dep_id = chain[hi]
            if dep_id > 0 && dep_id < cid_cursor {
              needed_cid[dep_id] = true
            }
          }
        }
      }
      cid_cursor = cid_cursor - 1
    }

    let id_remap : Array[Int32] = []
    for i in 0..<next_cid {
      if i <= orig_count {
        id_remap.push(i)
      } else {
        id_remap.push(-1)
      }
    }
    let kept_steps : Array[Int32] = []
    let mut compact_id = orig_count + 1
    for si in 0..<raw_is_add.length() {
      if raw_is_add[si] && needed_cid[raw_cid[si]] {
        id_remap[raw_cid[si]] = compact_id
        compact_id = compact_id + 1
        kept_steps.push(si)
      }
    }
    let total_compact_ids = compact_id - 1
    let last_use : Array[Int32] = []
    for _i in 0..<(total_compact_ids + 1) {
      last_use.push(-1)
    }
    for ki in 0..<kept_steps.length() {
      let si = kept_steps[ki]
      let chain = raw_rup[si]
      for hi in 0..<chain.length() {
        let new_hid = id_remap[chain[hi]]
        if new_hid > 0 {
          last_use[new_hid] = ki
        }
      }
    }
    // Unused original clauses can be deleted before the first derived step
    // (or after step 0 if step 0 is the final step).
    let unused_orig : Array[Int32] = []
    for oid in 1..<(orig_count + 1) {
      if last_use[oid] < 0 {
        unused_orig.push(oid)
      }
    }
    if unused_orig.length() > 0 && kept_steps.length() > 1 {
      del_count = del_count + 1
      out_steps.push(LratDelete(orig_count, unused_orig))
    }

    for ki in 0..<kept_steps.length() {
      let si = kept_steps[ki]
      let new_cid = id_remap[raw_cid[si]]
      let remapped_rup : Array[Int32] = []
      for hi in 0..<raw_rup[si].length() {
        remapped_rup.push(id_remap[raw_rup[si][hi]])
      }
      add_count = add_count + 1
      hint_count = hint_count + remapped_rup.length()
      out_steps.push(LratAdd(new_cid, raw_clause[si], remapped_rup, []))

      if ki < kept_steps.length() - 1 {
        let retiring : Array[Int32] = []
        for id in 1..<(new_cid + 1) {
          if id <= orig_count && last_use[id] < 0 {
            continue
          }
          if last_use[id] == ki || (id > orig_count && last_use[id] < 0) {
            retiring.push(id)
          }
        }
        if retiring.length() > 0 {
          del_count = del_count + 1
          out_steps.push(LratDelete(new_cid, retiring))
        }
      }
    }
  }

  let ok = face_cdcl_lrat_check(original_clauses, out_steps)
  FaceLratElaborateReport::{
    valid: ok,
    original_clauses: orig_count,
    input_steps: proof_steps.length(),
    lrat_adds: if ok { add_count } else { 0 },
    lrat_deletes: if ok { del_count } else { 0 },
    total_hints: if ok { hint_count } else { 0 },
    steps: if ok { out_steps } else { [] },
  }
}

///|
fn lrat_bin_push_i32(buf : Array[Byte], v : Int32) -> Unit {
  buf.push((v & 0xFF).to_byte())
  buf.push(((v >> 8) & 0xFF).to_byte())
  buf.push(((v >> 16) & 0xFF).to_byte())
  buf.push(((v >> 24) & 0xFF).to_byte())
}

///|
fn lrat_bin_read_i32(bytes : Bytes, offset : Int32) -> Int32? {
  if offset < 0 || offset + 4 > bytes.length() {
    return None
  }
  let b0 = bytes[offset].to_int() & 0xFF
  let b1 = bytes[offset + 1].to_int() & 0xFF
  let b2 = bytes[offset + 2].to_int() & 0xFF
  let b3 = bytes[offset + 3].to_int() & 0xFF
  Some(b0 | (b1 << 8) | (b2 << 16) | (b3 << 24))
}

///|
fn lrat_bin_checksum(payload : Array[Byte]) -> Int32 {
  let mut h : Int32 = 5381
  for i in 0..<payload.length() {
    let b = payload[i].to_int() & 0xFF
    h = ((h << 5) + h) ^ b
  }
  h
}

///|
/// Serialize an indexed LRAT proof into the compact `CHLRATBN` v1 binary
/// envelope (`8`-byte magic `"CHLRATBN"`, `u16` version `1`, `u16` flags `0`,
/// `i32` payload byte length, `i32` DJB2-xor checksum, followed by step
/// records `'a'` / `'d'`).
pub fn face_lrat_to_binary(steps : Array[FaceLratStep]) -> Bytes {
  let payload : Array[Byte] = []
  lrat_bin_push_i32(payload, steps.length())
  for i in 0..<steps.length() {
    match steps[i] {
      LratAdd(cid, clause, rup_hints, rat_hints) => {
        payload.push((0x61).to_byte()) // 'a'
        lrat_bin_push_i32(payload, cid)
        lrat_bin_push_i32(payload, clause.length())
        for j in 0..<clause.length() {
          lrat_bin_push_i32(payload, clause[j])
        }
        lrat_bin_push_i32(payload, rup_hints.length())
        for j in 0..<rup_hints.length() {
          lrat_bin_push_i32(payload, rup_hints[j])
        }
        lrat_bin_push_i32(payload, rat_hints.length())
        for j in 0..<rat_hints.length() {
          let (dcid, sub) = rat_hints[j]
          lrat_bin_push_i32(payload, dcid)
          lrat_bin_push_i32(payload, sub.length())
          for k in 0..<sub.length() {
            lrat_bin_push_i32(payload, sub[k])
          }
        }
      }
      LratDelete(sid, del_ids) => {
        payload.push((0x64).to_byte()) // 'd'
        lrat_bin_push_i32(payload, sid)
        lrat_bin_push_i32(payload, del_ids.length())
        for j in 0..<del_ids.length() {
          lrat_bin_push_i32(payload, del_ids[j])
        }
      }
    }
  }
  let out : Array[Byte] = [
    (0x43).to_byte(), // 'C'
    (0x48).to_byte(), // 'H'
    (0x4C).to_byte(), // 'L'
    (0x52).to_byte(), // 'R'
    (0x41).to_byte(), // 'A'
    (0x54).to_byte(), // 'T'
    (0x42).to_byte(), // 'B'
    (0x4E).to_byte(), // 'N'
    (0x01).to_byte(), // version lo = 1
    (0x00).to_byte(), // version hi = 0
    (0x00).to_byte(), // flags lo = 0
    (0x00).to_byte(), // flags hi = 0
  ]
  lrat_bin_push_i32(out, payload.length())
  lrat_bin_push_i32(out, lrat_bin_checksum(payload))
  for i in 0..<payload.length() {
    out.push(payload[i])
  }
  Bytes::from_array(out)
}

///|
/// Parse and integrity-check a `CHLRATBN` v1 binary LRAT proof stream.
/// Rejects corrupted magic, unsupported versions/flags, length mismatch,
/// trailing bytes, negative/overflowing counts, unknown step tags, and
/// checksum tampering.
pub fn face_lrat_from_binary(bytes : Bytes) -> Array[FaceLratStep]? {
  if bytes.length() < 20 {
    return None
  }
  let magic = [0x43, 0x48, 0x4C, 0x52, 0x41, 0x54, 0x42, 0x4E]
  for i in 0..<8 {
    if (bytes[i].to_int() & 0xFF) != magic[i] {
      return None
    }
  }
  let ver = (bytes[8].to_int() & 0xFF) | ((bytes[9].to_int() & 0xFF) << 8)
  let flags = (bytes[10].to_int() & 0xFF) | ((bytes[11].to_int() & 0xFF) << 8)
  if ver != 1 || flags != 0 {
    return None
  }
  let payload_len = match lrat_bin_read_i32(bytes, 12) {
    Some(n) => n
    None => return None
  }
  let expected_csum = match lrat_bin_read_i32(bytes, 16) {
    Some(c) => c
    None => return None
  }
  if payload_len < 4 || 20 + payload_len != bytes.length() {
    return None
  }
  let payload_copy : Array[Byte] = []
  for i in 0..<payload_len {
    payload_copy.push(bytes[20 + i])
  }
  if lrat_bin_checksum(payload_copy) != expected_csum {
    return None
  }
  let mut pos = 20
  let step_count = match lrat_bin_read_i32(bytes, pos) {
    Some(n) => n
    None => return None
  }
  pos = pos + 4
  if step_count < 0 || step_count > payload_len {
    return None
  }
  let steps : Array[FaceLratStep] = []
  for _si in 0..<step_count {
    if pos >= bytes.length() {
      return None
    }
    let tag = bytes[pos].to_int() & 0xFF
    pos = pos + 1
    if tag == 0x61 {
      let cid = match lrat_bin_read_i32(bytes, pos) {
        Some(v) => v
        None => return None
      }
      pos = pos + 4
      let clen = match lrat_bin_read_i32(bytes, pos) {
        Some(v) => v
        None => return None
      }
      pos = pos + 4
      if clen < 0 || pos + 4 * clen > bytes.length() {
        return None
      }
      let clause : Array[Int32] = []
      for _j in 0..<clen {
        match lrat_bin_read_i32(bytes, pos) {
          Some(lit) => clause.push(lit)
          None => return None
        }
        pos = pos + 4
      }
      let rlen = match lrat_bin_read_i32(bytes, pos) {
        Some(v) => v
        None => return None
      }
      pos = pos + 4
      if rlen < 0 || pos + 4 * rlen > bytes.length() {
        return None
      }
      let rup_hints : Array[Int32] = []
      for _j in 0..<rlen {
        match lrat_bin_read_i32(bytes, pos) {
          Some(hid) => rup_hints.push(hid)
          None => return None
        }
        pos = pos + 4
      }
      let rat_len = match lrat_bin_read_i32(bytes, pos) {
        Some(v) => v
        None => return None
      }
      pos = pos + 4
      if rat_len < 0 || pos + 8 * rat_len > bytes.length() {
        return None
      }
      let rat_hints : Array[(Int32, Array[Int32])] = []
      for _j in 0..<rat_len {
        let dcid = match lrat_bin_read_i32(bytes, pos) {
          Some(v) => v
          None => return None
        }
        pos = pos + 4
        let sub_len = match lrat_bin_read_i32(bytes, pos) {
          Some(v) => v
          None => return None
        }
        pos = pos + 4
        if sub_len < 0 || pos + 4 * sub_len > bytes.length() {
          return None
        }
        let sub : Array[Int32] = []
        for _k in 0..<sub_len {
          match lrat_bin_read_i32(bytes, pos) {
            Some(hid) => sub.push(hid)
            None => return None
          }
          pos = pos + 4
        }
        rat_hints.push((dcid, sub))
      }
      steps.push(LratAdd(cid, clause, rup_hints, rat_hints))
    } else if tag == 0x64 {
      let sid = match lrat_bin_read_i32(bytes, pos) {
        Some(v) => v
        None => return None
      }
      pos = pos + 4
      let dlen = match lrat_bin_read_i32(bytes, pos) {
        Some(v) => v
        None => return None
      }
      pos = pos + 4
      if dlen <= 0 || pos + 4 * dlen > bytes.length() {
        return None
      }
      let del_ids : Array[Int32] = []
      for _j in 0..<dlen {
        match lrat_bin_read_i32(bytes, pos) {
          Some(did) => del_ids.push(did)
          None => return None
        }
        pos = pos + 4
      }
      steps.push(LratDelete(sid, del_ids))
    } else {
      return None
    }
  }
  if pos != bytes.length() {
    return None
  }
  Some(steps)
}

///|
/// Decode and zero-search verify a `CHLRATBN` v1 binary LRAT proof stream.
pub fn face_cdcl_lrat_check_binary(
  original_clauses : Array[Array[Int32]],
  bytes : Bytes,
) -> Bool {
  match face_lrat_from_binary(bytes) {
    Some(steps) => face_cdcl_lrat_check(original_clauses, steps)
    None => false
  }
}

///|
pub fn face_sat_cdcl(
  f : Face,
  n : Int32,
  max_steps~ : Int32 = 100000,
) -> FaceSatDecision {
  face_sat_cdcl_report(f, n, max_steps~).decision
}

///|
/// Face equality through the CDCL solver applied to the symmetric
/// difference.
pub fn face_eq_cdcl(
  f : Face,
  g : Face,
  n : Int32,
  max_steps~ : Int32 = 100000,
) -> FaceDecision {
  let difference = FOr(FAnd(f, face_not(g)), FAnd(g, face_not(f)))
  match face_sat_cdcl(difference, n, max_steps~) {
    FaceSat(_) => FaceDecided(false)
    FaceUnsat => FaceDecided(true)
    FaceSearchBudgetExceeded => FaceBudgetExceeded
  }
}
