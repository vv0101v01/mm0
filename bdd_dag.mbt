///|
// Interned DAG binary decision diagrams.
//
// The legacy `Bdd` type is a tree: equal subdiagrams can occur many
// times, and structural recursion may revisit them exponentially
// often.  `BddManager` is the scalable representation.  Every node
// `(rank, low, high)` is interned in a hash table, Boolean `apply`
// operations are memoized, and two faces are equal exactly when
// their root node identifiers in one manager are equal.  A manager
// may carry a hard node budget; exceeding it sets an explicit flag
// instead of silently consuming exponential memory.  Variable order
// is part of a manager, and statistics expose node and cache counts.
//
// No representation can make every Boolean function small: over `n`
// ordered variables some functions require exponentially many BDD
// nodes.  The functions here therefore also provide a tight
// worst-case node bound and budget-aware decision procedures which
// return an explicit budget-exceeded result; a separate DPLL
// fallback decides satisfiability by branching on face variables
// when a caller prefers search to canonical-form construction.

///|
pub struct BddDagNode {
  rank : Int32 // position in the manager's variable order
  lo : Int32
  hi : Int32
}

///|
pub struct BddApplyEntry {
  op : Int32 // 0=and, 1=or, 2=xor, 3=not (b ignored)
  a : Int32
  b : Int32
  result : Int32
}

///|
pub struct BddManager {
  n : Int32
  order : Array[Int32] // variable ids by rank
  position : Array[Int32] // rank by variable id
  nodes : Array[BddDagNode] // 0=false, 1=true, then interned nodes
  buckets : Array[Array[Int32]]
  apply_buckets : Array[Array[BddApplyEntry]]
  max_nodes : Int32 // 0 means unbounded
  mut exceeded : Bool
  mut apply_hits : Int32
  mut apply_misses : Int32
  mut mk_calls : Int32
}

///|
fn bdd_buckets_new(size : Int32) -> Array[Array[Int32]] {
  let out : Array[Array[Int32]] = []
  for _i in 0..<size {
    out.push([])
  }
  out
}

///|
fn bdd_apply_buckets_new(size : Int32) -> Array[Array[BddApplyEntry]] {
  let out : Array[Array[BddApplyEntry]] = []
  for _i in 0..<size {
    out.push([])
  }
  out
}

///|
fn bdd_node_hash(rank : Int32, lo : Int32, hi : Int32, size : Int32) -> Int32 {
  let mut h = (rank * 73856093) ^ (lo * 19349663) ^ (hi * 83492791)
  h = h ^ ((h >> 13) & 0x7ffff)
  if (size & (size - 1)) == 0 {
    h & (size - 1)
  } else {
    (h & 0x7fffffff) % size
  }
}

///|
fn bdd_apply_hash(op : Int32, a : Int32, b : Int32, size : Int32) -> Int32 {
  let mut h = (op * 83492791) ^ (a * 73856093) ^ (b * 19349663)
  h = h ^ ((h >> 13) & 0x7ffff)
  if (size & (size - 1)) == 0 {
    h & (size - 1)
  } else {
    (h & 0x7fffffff) % size
  }
}

///|
fn bdd_manager_rehash(m : BddManager) -> Unit {
  let new_size = m.buckets.length() * 2
  let fresh = bdd_buckets_new(new_size)
  for id in 2..<m.nodes.length() {
    let node = m.nodes[id]
    fresh[bdd_node_hash(node.rank, node.lo, node.hi, new_size)].push(id)
  }
  // Replace bucket contents in place (the array itself is shared).
  while m.buckets.length() > 0 {
    ignore(m.buckets.pop())
  }
  for i in 0..<fresh.length() {
    m.buckets.push(fresh[i])
  }
}

///|
pub fn bdd_manager_new(n : Int32, max_nodes~ : Int32 = 0) -> BddManager {
  let order : Array[Int32] = []
  let position : Array[Int32] = []
  for i in 0..<n {
    order.push(i)
    position.push(i)
  }
  BddManager::{
    n,
    order,
    position,
    nodes: [
      BddDagNode::{ rank: n, lo: 0, hi: 0, },
      BddDagNode::{ rank: n, lo: 1, hi: 1, },
    ],
    buckets: bdd_buckets_new(1024),
    apply_buckets: bdd_apply_buckets_new(1024),
    max_nodes,
    exceeded: false,
    apply_hits: 0,
    apply_misses: 0,
    mk_calls: 0,
  }
}

///|
/// A manager with a prescribed variable order.  Non-permutation
/// inputs are completed with the missing variables in index order.
pub fn bdd_manager_with_order(
  order_in : Array[Int32],
  n : Int32,
  max_nodes~ : Int32 = 0,
) -> BddManager {
  let order : Array[Int32] = []
  let seen : Array[Bool] = []
  for _i in 0..<n {
    seen.push(false)
  }
  for i in 0..<order_in.length() {
    let v = order_in[i]
    if v >= 0 && v < n && !seen[v] {
      seen[v] = true
      order.push(v)
    }
  }
  for v in 0..<n {
    if !seen[v] {
      seen[v] = true
      order.push(v)
    }
  }
  let position : Array[Int32] = []
  for _i in 0..<n {
    position.push(0)
  }
  for r in 0..<order.length() {
    position[order[r]] = r
  }
  BddManager::{
    n,
    order,
    position,
    nodes: [
      BddDagNode::{ rank: n, lo: 0, hi: 0, },
      BddDagNode::{ rank: n, lo: 1, hi: 1, },
    ],
    buckets: bdd_buckets_new(1024),
    apply_buckets: bdd_apply_buckets_new(1024),
    max_nodes,
    exceeded: false,
    apply_hits: 0,
    apply_misses: 0,
    mk_calls: 0,
  }
}

///|
fn bdd_dag_mk(m : BddManager, rank : Int32, lo : Int32, hi : Int32) -> Int32 {
  if lo == hi {
    return lo
  }
  m.mk_calls = m.mk_calls + 1
  let bucket = bdd_node_hash(rank, lo, hi, m.buckets.length())
  for i in 0..<m.buckets[bucket].length() {
    let id = m.buckets[bucket][i]
    let node = m.nodes[id]
    if node.rank == rank && node.lo == lo && node.hi == hi {
      return id
    }
  }
  if m.max_nodes > 0 && m.nodes.length() - 2 >= m.max_nodes {
    m.exceeded = true
    return 0
  }
  let id = m.nodes.length()
  m.nodes.push(BddDagNode::{ rank, lo, hi, })
  m.buckets[bucket].push(id)
  if m.nodes.length() > m.buckets.length() * 4 {
    bdd_manager_rehash(m)
  }
  id
}

///|
fn bdd_dag_top(m : BddManager, id : Int32) -> Int32 {
  m.nodes[id].rank
}

///|
fn bdd_cofactor(m : BddManager, id : Int32, rank : Int32, high : Bool) -> Int32 {
  if id < 2 || bdd_dag_top(m, id) != rank {
    id
  } else if high {
    m.nodes[id].hi
  } else {
    m.nodes[id].lo
  }
}

///|
fn bdd_apply_lookup(m : BddManager, op : Int32, a : Int32, b : Int32) -> Int32? {
  let bucket = bdd_apply_hash(op, a, b, m.apply_buckets.length())
  for i in 0..<m.apply_buckets[bucket].length() {
    let e = m.apply_buckets[bucket][i]
    if e.op == op && e.a == a && e.b == b {
      return Some(e.result)
    }
  }
  None
}

///|
fn bdd_apply_rehash(m : BddManager) -> Unit {
  let new_size = m.apply_buckets.length() * 2
  let fresh = bdd_apply_buckets_new(new_size)
  for bucket in 0..<m.apply_buckets.length() {
    for i in 0..<m.apply_buckets[bucket].length() {
      let entry = m.apply_buckets[bucket][i]
      fresh[bdd_apply_hash(entry.op, entry.a, entry.b, new_size)].push(entry)
    }
  }
  while m.apply_buckets.length() > 0 {
    ignore(m.apply_buckets.pop())
  }
  for i in 0..<fresh.length() {
    m.apply_buckets.push(fresh[i])
  }
}

///|
fn bdd_apply_store(
  m : BddManager,
  op : Int32,
  a : Int32,
  b : Int32,
  result : Int32,
) -> Unit {
  let bucket = bdd_apply_hash(op, a, b, m.apply_buckets.length())
  m.apply_buckets[bucket].push(BddApplyEntry::{ op, a, b, result, })
  // Every miss that reaches storage contributes one cache entry.
  // Growing with the node table keeps lookup chains bounded on
  // large apply workloads instead of retaining the initial
  // 1024-bucket table forever.
  if m.apply_misses > m.apply_buckets.length() * 4 {
    bdd_apply_rehash(m)
  }
}

///|
fn bdd_dag_not_rec(m : BddManager, a : Int32) -> Int32 {
  if m.exceeded {
    return 0
  }
  if a == 0 {
    return 1
  }
  if a == 1 {
    return 0
  }
  match bdd_apply_lookup(m, 3, a, 0) {
    Some(r) => {
      m.apply_hits = m.apply_hits + 1
      r
    }
    None => {
      m.apply_misses = m.apply_misses + 1
      let node = m.nodes[a]
      let result = bdd_dag_mk(
        m,
        node.rank,
        bdd_dag_not_rec(m, node.lo),
        bdd_dag_not_rec(m, node.hi),
      )
      bdd_apply_store(m, 3, a, 0, result)
      result
    }
  }
}

///|
fn bdd_dag_apply(m : BddManager, op : Int32, a0 : Int32, b0 : Int32) -> Int32 {
  if m.exceeded {
    return 0
  }
  // Terminal and identity rules.
  if op == 0 { // and
    if a0 == 0 || b0 == 0 {
      return 0
    }
    if a0 == 1 {
      return b0
    }
    if b0 == 1 {
      return a0
    }
    if a0 == b0 {
      return a0
    }
  } else if op == 1 { // or
    if a0 == 1 || b0 == 1 {
      return 1
    }
    if a0 == 0 {
      return b0
    }
    if b0 == 0 {
      return a0
    }
    if a0 == b0 {
      return a0
    }
  } else { // xor
    if a0 == 0 {
      return b0
    }
    if b0 == 0 {
      return a0
    }
    if a0 == b0 {
      return 0
    }
    if a0 == 1 {
      return bdd_dag_not_rec(m, b0)
    }
    if b0 == 1 {
      return bdd_dag_not_rec(m, a0)
    }
  }
  let (a, b) = if a0 <= b0 { (a0, b0) } else { (b0, a0) }
  match bdd_apply_lookup(m, op, a, b) {
    Some(r) => {
      m.apply_hits = m.apply_hits + 1
      r
    }
    None => {
      m.apply_misses = m.apply_misses + 1
      let ra = bdd_dag_top(m, a)
      let rb = bdd_dag_top(m, b)
      let rank = if ra < rb { ra } else { rb }
      let lo = bdd_dag_apply(
        m,
        op,
        bdd_cofactor(m, a, rank, false),
        bdd_cofactor(m, b, rank, false),
      )
      let hi = bdd_dag_apply(
        m,
        op,
        bdd_cofactor(m, a, rank, true),
        bdd_cofactor(m, b, rank, true),
      )
      let result = bdd_dag_mk(m, rank, lo, hi)
      bdd_apply_store(m, op, a, b, result)
      result
    }
  }
}

///|
pub fn bdd_dag_false(_m : BddManager) -> Int32 {
  0
}

///|
pub fn bdd_dag_true(_m : BddManager) -> Int32 {
  1
}

///|
pub fn bdd_dag_var(m : BddManager, variable : Int32) -> Int32 {
  if variable < 0 || variable >= m.n {
    0
  } else {
    bdd_dag_mk(m, m.position[variable], 0, 1)
  }
}

///|
pub fn bdd_dag_not(m : BddManager, a : Int32) -> Int32 {
  bdd_dag_not_rec(m, a)
}

///|
pub fn bdd_dag_and(m : BddManager, a : Int32, b : Int32) -> Int32 {
  bdd_dag_apply(m, 0, a, b)
}

///|
pub fn bdd_dag_or(m : BddManager, a : Int32, b : Int32) -> Int32 {
  bdd_dag_apply(m, 1, a, b)
}

///|
pub fn bdd_dag_xor(m : BddManager, a : Int32, b : Int32) -> Int32 {
  bdd_dag_apply(m, 2, a, b)
}

///|
fn bdd_dag_of_dim(m : BddManager, r : Dim) -> Int32 {
  match dim_simplify(r) {
    DZero => 0
    DOne => 1
    DVar(i) => bdd_dag_var(m, i)
    DNeg(a) => bdd_dag_not(m, bdd_dag_of_dim(m, a))
    DAnd(a, b) => bdd_dag_and(m, bdd_dag_of_dim(m, a), bdd_dag_of_dim(m, b))
    DOr(a, b) => bdd_dag_or(m, bdd_dag_of_dim(m, a), bdd_dag_of_dim(m, b))
  }
}

///|
/// Build a face in an existing manager.  Variables outside the
/// manager's range denote false, matching `face_bound`.
pub fn bdd_dag_build_face(m : BddManager, f : Face) -> Int32 {
  match f {
    FTop => 1
    FBot => 0
    FEq0(r) => bdd_dag_not(m, bdd_dag_of_dim(m, r))
    FEq1(r) => bdd_dag_of_dim(m, r)
    FAnd(a, b) =>
      bdd_dag_and(m, bdd_dag_build_face(m, a), bdd_dag_build_face(m, b))
    FOr(a, b) =>
      bdd_dag_or(m, bdd_dag_build_face(m, a), bdd_dag_build_face(m, b))
  }
}

///|
pub struct BddDagFace {
  manager : BddManager
  root : Int32
  ok : Bool
}

///|
pub fn bdd_dag_of_face(
  f : Face,
  n : Int32,
  max_nodes~ : Int32 = 0,
) -> BddDagFace {
  let manager = bdd_manager_new(n, max_nodes~)
  let root = bdd_dag_build_face(manager, f)
  BddDagFace::{ manager, root, ok: !manager.exceeded, }
}

///|
pub fn bdd_manager_node_count(m : BddManager) -> Int32 {
  m.nodes.length() - 2
}

///|
pub fn bdd_manager_stats(m : BddManager) -> (Int32, Int32, Int32, Int32, Bool) {
  (
    bdd_manager_node_count(m),
    m.apply_hits,
    m.apply_misses,
    m.mk_calls,
    m.exceeded,
  )
}

///|
/// Hash-table diagnostics: node bucket count, apply-cache bucket
/// count, and the total number of stored apply-cache entries.
pub fn bdd_manager_cache_stats(m : BddManager) -> (Int32, Int32, Int32) {
  let mut entries = 0
  for i in 0..<m.apply_buckets.length() {
    entries = entries + m.apply_buckets[i].length()
  }
  (m.buckets.length(), m.apply_buckets.length(), entries)
}

///|
/// A safe worst-case bound on ROBDD node count over `n` variables,
/// saturated at the largest `Int32`.
pub fn bdd_worst_case_nodes(n : Int32) -> Int32 {
  let max = 2147483647
  if n < 0 {
    return 0
  }
  if n >= 31 {
    return max
  }
  let mut pow = 1
  for _i in 0..<(n + 1) {
    pow = pow * 2
  }
  pow - 1
}

///|
fn bdd_tree_of_id(m : BddManager, id : Int32, memo : Array[Bdd?]) -> Bdd {
  if id == 0 {
    return BddZero
  }
  if id == 1 {
    return BddOne
  }
  match memo[id] {
    Some(b) => b
    None => {
      let node = m.nodes[id]
      let out = BddNode(
        m.order[node.rank],
        bdd_tree_of_id(m, node.lo, memo),
        bdd_tree_of_id(m, node.hi, memo),
      )
      memo[id] = Some(out)
      out
    }
  }
}

///|
/// Expand a DAG root to the legacy tree representation.  Shared
/// subdiagrams are built once and shared as values.
pub fn bdd_tree_of_dag(m : BddManager, root : Int32) -> Bdd {
  let memo : Array[Bdd?] = []
  for _i in 0..<m.nodes.length() {
    memo.push(None)
  }
  bdd_tree_of_id(m, root, memo)
}

///|
fn bdd_dag_witness_into(m : BddManager, id : Int32, env : Array[Bool]) -> Bool {
  if id == 0 {
    false
  } else if id == 1 {
    true
  } else {
    let node = m.nodes[id]
    if bdd_dag_witness_into(m, node.lo, env) {
      true
    } else {
      env[m.order[node.rank]] = true
      if bdd_dag_witness_into(m, node.hi, env) {
        true
      } else {
        env[m.order[node.rank]] = false
        false
      }
    }
  }
}

///|
pub fn bdd_dag_witness(m : BddManager, root : Int32) -> Array[Bool]? {
  let env : Array[Bool] = []
  for _i in 0..<m.n {
    env.push(false)
  }
  if bdd_dag_witness_into(m, root, env) {
    Some(env)
  } else {
    None
  }
}

///|
pub enum FaceDecision {
  FaceDecided(Bool)
  FaceBudgetExceeded
} derive(Debug, Eq)

///|
pub extend FaceDecision with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend FaceDecision with Eq::{not_equal, equal}

///|
/// Equality decided by root identity in one shared DAG manager.
pub fn bdd_dag_face_eq(f : Face, g : Face, n : Int32) -> Bool {
  let m = bdd_manager_new(n)
  bdd_dag_build_face(m, f) == bdd_dag_build_face(m, g)
}

///|
pub fn bdd_dag_face_le(f : Face, g : Face, n : Int32) -> Bool {
  let m = bdd_manager_new(n)
  let a = bdd_dag_build_face(m, f)
  let b = bdd_dag_build_face(m, g)
  bdd_dag_and(m, a, bdd_dag_not(m, b)) == 0
}

///|
pub fn bdd_dag_sat_face(f : Face, n : Int32) -> Bool {
  let built = bdd_dag_of_face(f, n)
  built.root != 0
}

///|
/// Budget-aware equality: if canonical construction would exceed
/// `max_nodes`, the result says so explicitly rather than guessing.
pub fn face_eq_within_budget(
  f : Face,
  g : Face,
  n : Int32,
  max_nodes : Int32,
) -> FaceDecision {
  let m = bdd_manager_new(n, max_nodes~)
  let a = bdd_dag_build_face(m, f)
  if m.exceeded {
    return FaceBudgetExceeded
  }
  let b = bdd_dag_build_face(m, g)
  if m.exceeded {
    FaceBudgetExceeded
  } else {
    FaceDecided(a == b)
  }
}

///|
pub fn face_sat_within_budget(
  f : Face,
  n : Int32,
  max_nodes : Int32,
) -> FaceDecision {
  let built = bdd_dag_of_face(f, n, max_nodes~)
  if built.ok {
    FaceDecided(built.root != 0)
  } else {
    FaceBudgetExceeded
  }
}

// ---------------------------------------------------------------------------
// DPLL fallback for satisfiability
// ---------------------------------------------------------------------------

///|
pub fn face_not(f : Face) -> Face {
  match f {
    FTop => FBot
    FBot => FTop
    FEq0(r) => FEq1(r)
    FEq1(r) => FEq0(r)
    FAnd(a, b) => face_simplify(FOr(face_not(a), face_not(b)))
    FOr(a, b) => face_simplify(FAnd(face_not(a), face_not(b)))
  }
}

///|
fn face_dpll(
  f : Face,
  vars : Array[Int32],
  idx : Int32,
  env : Array[Bool],
  steps : Array[Int32],
  max_steps : Int32,
) -> Int32 {
  // Return codes: 1 sat (env filled), 0 unsat, -1 budget exceeded.
  steps[0] = steps[0] + 1
  if max_steps > 0 && steps[0] > max_steps {
    return -1
  }
  let simplified = face_simplify(f)
  match simplified {
    FTop => return 1
    FBot => return 0
    _ => ()
  }
  let remaining = face_vars(simplified)
  if remaining.length() == 0 {
    return if face_holds(simplified, env) { 1 } else { 0 }
  }
  if idx >= vars.length() {
    return if face_holds(simplified, env) { 1 } else { 0 }
  }
  let v = remaining[0]
  env[v] = false
  let low = face_dpll(
    face_subst(simplified, v, false),
    vars,
    idx + 1,
    env,
    steps,
    max_steps,
  )
  if low != 0 {
    return low
  }
  env[v] = true
  let high = face_dpll(
    face_subst(simplified, v, true),
    vars,
    idx + 1,
    env,
    steps,
    max_steps,
  )
  if high != 1 {
    env[v] = false
  }
  high
}

///|
pub enum FaceSatDecision {
  FaceSat(Array[Bool])
  FaceUnsat
  FaceSearchBudgetExceeded
} derive(Debug, Eq)

///|
pub extend FaceSatDecision with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend FaceSatDecision with Eq::{not_equal, equal}

///|
/// Satisfiability by DPLL search on the face itself, with an explicit
/// step budget.  This trades canonical-form size for search and can
/// decide instances whose DAG exceeds a chosen node budget.
pub fn face_sat_dpll(
  f : Face,
  n : Int32,
  max_steps~ : Int32 = 100000,
) -> FaceSatDecision {
  let env : Array[Bool] = []
  for _i in 0..<n {
    env.push(false)
  }
  let bounded = face_bound(f, n)
  let result = face_dpll(bounded, face_vars(bounded), 0, env, [0], max_steps)
  if result == 1 {
    FaceSat(env)
  } else if result == 0 {
    FaceUnsat
  } else {
    FaceSearchBudgetExceeded
  }
}

///|
/// Equality through DPLL on the symmetric difference, used when a
/// caller does not want to build BDDs at all.
pub fn face_eq_dpll(
  f : Face,
  g : Face,
  n : Int32,
  max_steps~ : Int32 = 100000,
) -> FaceDecision {
  let difference = FOr(FAnd(f, face_not(g)), FAnd(g, face_not(f)))
  match face_sat_dpll(difference, n, max_steps~) {
    FaceSat(_) => FaceDecided(false)
    FaceUnsat => FaceDecided(true)
    FaceSearchBudgetExceeded => FaceBudgetExceeded
  }
}

// ---------------------------------------------------------------------------
// Variable-order candidates
// ---------------------------------------------------------------------------

///|
fn dim_var_counts_into(
  r : Dim,
  counts : Array[Int32],
  first : Array[Int32],
) -> Unit {
  match r {
    DZero | DOne => ()
    DVar(i) =>
      if i >= 0 && i < counts.length() {
        counts[i] = counts[i] + 1
        if !contains_int(first, i) {
          first.push(i)
        }
      }
    DNeg(a) => dim_var_counts_into(a, counts, first)
    DAnd(a, b) => {
      dim_var_counts_into(a, counts, first)
      dim_var_counts_into(b, counts, first)
    }
    DOr(a, b) => {
      dim_var_counts_into(a, counts, first)
      dim_var_counts_into(b, counts, first)
    }
  }
}

///|
fn face_var_counts_into(
  f : Face,
  counts : Array[Int32],
  first : Array[Int32],
) -> Unit {
  match f {
    FTop | FBot => ()
    FEq0(r) | FEq1(r) => dim_var_counts_into(r, counts, first)
    FAnd(a, b) => {
      face_var_counts_into(a, counts, first)
      face_var_counts_into(b, counts, first)
    }
    FOr(a, b) => {
      face_var_counts_into(a, counts, first)
      face_var_counts_into(b, counts, first)
    }
  }
}

///|
/// Variable orderings worth trying: index order, first-occurrence
/// order in the syntax, decreasing occurrence frequency, and reverse
/// index order.  Missing variables are appended in index order.
pub fn bdd_var_order_candidates(f : Face, n : Int32) -> Array[Array[Int32]] {
  let counts : Array[Int32] = []
  for _i in 0..<n {
    counts.push(0)
  }
  let first : Array[Int32] = []
  face_var_counts_into(f, counts, first)
  let identity : Array[Int32] = []
  let reverse : Array[Int32] = []
  for i in 0..<n {
    identity.push(i)
    reverse.push(n - 1 - i)
  }
  let frequency : Array[Int32] = []
  for i in 0..<n {
    frequency.push(i)
  }
  for _pass in 0..<frequency.length() {
    for j in 0..<(frequency.length() - 1) {
      if counts[frequency[j + 1]] > counts[frequency[j]] {
        let tmp = frequency[j]
        frequency[j] = frequency[j + 1]
        frequency[j + 1] = tmp
      }
    }
  }
  [identity, first, frequency, reverse]
}

///|
pub struct BddBestBuild {
  built : BddDagFace
  order : Array[Int32]
}

///|
/// Build using the smallest DAG among the candidate orders.
pub fn bdd_dag_of_face_best(
  f : Face,
  n : Int32,
  max_nodes~ : Int32 = 0,
) -> BddBestBuild {
  let candidates = bdd_var_order_candidates(f, n)
  let mut best_order = candidates[0]
  let first_manager = bdd_manager_with_order(best_order, n, max_nodes~)
  let first_root = bdd_dag_build_face(first_manager, f)
  let mut best = BddDagFace::{
    manager: first_manager,
    root: first_root,
    ok: !first_manager.exceeded,
  }
  for c in 1..<candidates.length() {
    let manager = bdd_manager_with_order(candidates[c], n, max_nodes~)
    let root = bdd_dag_build_face(manager, f)
    let candidate = BddDagFace::{ manager, root, ok: !manager.exceeded, }
    if candidate.ok &&
      (
        !best.ok ||
        bdd_dag_reachable_count(manager, root) <
        bdd_dag_reachable_count(best.manager, best.root)
      ) {
      best = candidate
      best_order = candidates[c]
    }
  }
  BddBestBuild::{ built: best, order: best_order, }
}

///|
pub struct BddOptimizedBuild {
  built : BddDagFace
  order : Array[Int32]
  initial_reachable : Int32
  reachable : Int32
  attempts : Int32
  improved : Bool
}

///|
fn bdd_order_after_move(
  order : Array[Int32],
  from : Int32,
  to : Int32,
) -> Array[Int32] {
  let variable = order[from]
  let without : Array[Int32] = []
  for i in 0..<order.length() {
    if i != from {
      without.push(order[i])
    }
  }
  let out : Array[Int32] = []
  for i in 0..<without.length() {
    if i == to {
      out.push(variable)
    }
    out.push(without[i])
  }
  if to >= without.length() {
    out.push(variable)
  }
  out
}

///|
/// Budgeted sifting on top of the candidate-order build.  Each
/// variable is moved through every position of the current order
/// and the best resulting order is retained; passes repeat while
/// they improve the reachable node count and while the explicit
/// rebuild budget lasts.  This is a heuristic optimizer, not a
/// claim of a globally minimum order.
pub fn bdd_dag_of_face_optimized(
  f : Face,
  n : Int32,
  max_nodes~ : Int32 = 0,
  max_attempts~ : Int32 = 64,
) -> BddOptimizedBuild {
  let initial = bdd_dag_of_face_best(f, n, max_nodes~)
  let mut best = initial.built
  let mut order : Array[Int32] = []
  for i in 0..<best.manager.order.length() {
    order.push(best.manager.order[i])
  }
  let initial_reachable = if best.ok {
    bdd_dag_reachable_count(best.manager, best.root)
  } else {
    -1
  }
  let mut best_reachable = initial_reachable
  let mut attempts = 0
  let mut improved = false
  // Do not spend the budget "optimizing" a failed build or a
  // uniquely ordered problem.
  let mut pass_improved = best.ok && n > 1 && max_attempts > 0
  while pass_improved && attempts < max_attempts {
    pass_improved = false
    // The variables to sift are those of the order at pass entry;
    // their positions are recomputed after each adoption.
    let variables : Array[Int32] = []
    for i in 0..<order.length() {
      variables.push(order[i])
    }
    for vi in 0..<variables.length() {
      if attempts >= max_attempts {
        break
      }
      let variable = variables[vi]
      let mut from = -1
      for i in 0..<order.length() {
        if order[i] == variable {
          from = i
        }
      }
      if from < 0 {
        continue
      }
      let mut round_best_order : Array[Int32] = []
      for i in 0..<order.length() {
        round_best_order.push(order[i])
      }
      let mut round_best = best
      let mut round_best_reachable = best_reachable
      for to in 0..<n {
        if attempts >= max_attempts {
          break
        }
        if to == from {
          continue
        }
        let candidate_order = bdd_order_after_move(order, from, to)
        let manager = bdd_manager_with_order(candidate_order, n, max_nodes~)
        let root = bdd_dag_build_face(manager, f)
        attempts = attempts + 1
        if !manager.exceeded {
          let reachable = bdd_dag_reachable_count(manager, root)
          if reachable < round_best_reachable {
            round_best_reachable = reachable
            round_best = BddDagFace::{ manager, root, ok: true, }
            round_best_order = candidate_order
          }
        }
      }
      if round_best_reachable < best_reachable {
        best = round_best
        best_reachable = round_best_reachable
        order = round_best_order
        improved = true
        pass_improved = true
      }
    }
  }
  BddOptimizedBuild::{
    built: best,
    order,
    initial_reachable,
    reachable: best_reachable,
    attempts,
    improved,
  }
}

///|
fn bdd_mark_reachable(m : BddManager, id : Int32, seen : Array[Bool]) -> Unit {
  if id < 2 || seen[id] {
    return
  }
  seen[id] = true
  bdd_mark_reachable(m, m.nodes[id].lo, seen)
  bdd_mark_reachable(m, m.nodes[id].hi, seen)
}

///|
/// The number of nonterminal DAG nodes reachable from a root.  This
/// is the size of the represented ROBDD, as opposed to
/// `bdd_manager_node_count`, which also counts interned intermediate
/// nodes created during apply operations.
pub fn bdd_dag_reachable_count(m : BddManager, root : Int32) -> Int32 {
  let seen : Array[Bool] = []
  for _i in 0..<m.nodes.length() {
    seen.push(false)
  }
  bdd_mark_reachable(m, root, seen)
  let mut count = 0
  for i in 0..<seen.length() {
    if seen[i] {
      count = count + 1
    }
  }
  count
}

// ---------------------------------------------------------------------------
// DAG-native operations (no tree/DNF expansion)
// ---------------------------------------------------------------------------

///|
/// Evaluate a DAG root under a complete assignment, walking the
/// DAG once.
pub fn bdd_dag_eval(m : BddManager, root : Int32, env : Array[Bool]) -> Bool {
  let mut id = root
  while id >= 2 {
    let node = m.nodes[id]
    let variable = m.order[node.rank]
    id = if variable >= 0 && variable < env.length() && env[variable] {
      node.hi
    } else {
      node.lo
    }
  }
  id == 1
}

///|
fn bdd_pow2(k : Int32) -> BigInt {
  let mut out = 1N
  for _i in 0..<k {
    out = out * 2N
  }
  out
}

///|
fn bdd_sat_count_from(
  m : BddManager,
  id : Int32,
  rank : Int32,
  memo : Array[BigInt?],
) -> BigInt {
  if id == 0 {
    return 0N
  }
  if id == 1 {
    return bdd_pow2(m.n - rank)
  }
  match memo[id] {
    Some(c) => c
    None => {
      let node = m.nodes[id]
      let skipped = bdd_pow2(node.rank - rank)
      let total = skipped *
        (
          bdd_sat_count_from(m, node.lo, node.rank + 1, memo) +
          bdd_sat_count_from(m, node.hi, node.rank + 1, memo)
        )
      memo[id] = Some(total)
      total
    }
  }
}

///|
/// The number of satisfying assignments, counted on the DAG with
/// memoization.  This is polynomial in the DAG size and never
/// materializes the DNF or the tree expansion.
pub fn bdd_dag_sat_count(m : BddManager, root : Int32) -> BigInt {
  let memo : Array[BigInt?] = []
  for _i in 0..<m.nodes.length() {
    memo.push(None)
  }
  bdd_sat_count_from(m, root, 0, memo)
}

///|
fn bdd_dag_restrict_rec(
  m : BddManager,
  id : Int32,
  rank : Int32,
  value : Bool,
  memo : Array[Int32],
) -> Int32 {
  if id < 2 {
    return id
  }
  if memo[id] >= 0 {
    return memo[id]
  }
  let node = m.nodes[id]
  let result = if node.rank == rank {
    bdd_dag_restrict_rec(
      m,
      if value {
        node.hi
      } else {
        node.lo
      },
      rank,
      value,
      memo,
    )
  } else if node.rank > rank {
    id
  } else {
    bdd_dag_mk(
      m,
      node.rank,
      bdd_dag_restrict_rec(m, node.lo, rank, value, memo),
      bdd_dag_restrict_rec(m, node.hi, rank, value, memo),
    )
  }
  memo[id] = result
  result
}

///|
/// Restrict a variable to a constant, on the DAG.
pub fn bdd_dag_restrict(
  m : BddManager,
  root : Int32,
  variable : Int32,
  value : Bool,
) -> Int32 {
  if variable < 0 || variable >= m.n {
    return root
  }
  let memo : Array[Int32] = []
  for _i in 0..<m.nodes.length() {
    memo.push(-1)
  }
  bdd_dag_restrict_rec(m, root, m.position[variable], value, memo)
}

///|
/// Existential quantification over one variable, on the DAG.
pub fn bdd_dag_exists(m : BddManager, root : Int32, variable : Int32) -> Int32 {
  bdd_dag_or(
    m,
    bdd_dag_restrict(m, root, variable, false),
    bdd_dag_restrict(m, root, variable, true),
  )
}

///|
/// Universal quantification over one variable, on the DAG.
pub fn bdd_dag_forall(m : BddManager, root : Int32, variable : Int32) -> Int32 {
  bdd_dag_and(
    m,
    bdd_dag_restrict(m, root, variable, false),
    bdd_dag_restrict(m, root, variable, true),
  )
}

///|
fn bdd_dnf_into(
  m : BddManager,
  id : Int32,
  cube : Face,
  out : Array[Face],
  counter : Array[Int32],
  max_cubes : Int32,
) -> Unit {
  if counter[0] > max_cubes {
    return
  }
  if id == 0 {
    return
  }
  if id == 1 {
    counter[0] = counter[0] + 1
    if counter[0] <= max_cubes {
      out.push(cube)
    }
    return
  }
  let node = m.nodes[id]
  let variable = DVar(m.order[node.rank])
  bdd_dnf_into(
    m,
    node.lo,
    face_simplify(FAnd(cube, FEq0(variable))),
    out,
    counter,
    max_cubes,
  )
  bdd_dnf_into(
    m,
    node.hi,
    face_simplify(FAnd(cube, FEq1(variable))),
    out,
    counter,
    max_cubes,
  )
}

///|
/// Convert a DAG root back to a DNF face, but only if the number
/// of cubes stays within `max_cubes`; otherwise return `None`
/// instead of paying the DAG-to-DNF expansion blowup.
pub fn bdd_dag_dnf_face(
  m : BddManager,
  root : Int32,
  max_cubes : Int32,
) -> Face? {
  let out : Array[Face] = []
  let counter : Array[Int32] = [0]
  bdd_dnf_into(m, root, FTop, out, counter, max_cubes)
  if counter[0] > max_cubes {
    None
  } else {
    let mut face = FBot
    for i in 0..<out.length() {
      face = face_simplify(FOr(face, out[i]))
    }
    Some(face)
  }
}

// ---------------------------------------------------------------------------
// Total decisions: budgeted DAG construction with DPLL fallback
// ---------------------------------------------------------------------------

///|
/// Satisfiability decided one way or the other: first try DAG
/// construction within the node budget (which also yields a
/// witness); if the budget is exceeded, fall back to DPLL search
/// within its step budget.  Only if both budgets are exhausted is
/// the result the explicit budget-exceeded case.
pub fn face_sat_decide(
  f : Face,
  n : Int32,
  max_nodes~ : Int32 = 4096,
  max_steps~ : Int32 = 100000,
) -> FaceSatDecision {
  let built = bdd_dag_of_face(f, n, max_nodes~)
  if built.ok {
    if built.root == 0 {
      return FaceUnsat
    }
    match bdd_dag_witness(built.manager, built.root) {
      Some(env) => return FaceSat(env)
      None => return FaceUnsat
    }
  }
  face_sat_watched_dpll(f, n, max_steps~)
}

///|
/// Face equality with the same two-stage strategy.
pub fn face_eq_decide(
  f : Face,
  g : Face,
  n : Int32,
  max_nodes~ : Int32 = 4096,
  max_steps~ : Int32 = 100000,
) -> FaceDecision {
  match face_eq_within_budget(f, g, n, max_nodes) {
    FaceDecided(b) => FaceDecided(b)
    FaceBudgetExceeded => face_eq_watched_dpll(f, g, n, max_steps~)
  }
}

///|
pub fn check_bdd_dag_native_operations() -> Bool {
  // Parity of 6 variables: the DAG is linear (2 nodes per level)
  // while its DNF has 32 cubes and its tree expansion is larger
  // still; the DAG-native operations never expand it.
  let n = 6
  let m = bdd_manager_new(n)
  let mut parity = bdd_dag_false(m)
  for v in 0..<n {
    parity = bdd_dag_xor(m, parity, bdd_dag_var(m, v))
  }
  if bdd_dag_reachable_count(m, parity) > 20 {
    return false
  }
  if bdd_dag_sat_count(m, parity) != 32N {
    return false
  }
  if !bdd_dag_eval(m, parity, [true, false, false, false, false, false]) ||
    bdd_dag_eval(m, parity, [true, true, false, false, false, false]) {
    return false
  }
  // Restricting x0=true negates the parity of the rest (still
  // satisfied by half of the 64 assignments, x0 now being free).
  let restricted = bdd_dag_restrict(m, parity, 0, true)
  if bdd_dag_sat_count(m, restricted) != 32N {
    return false
  }
  // Both quantifications over x0 collapse parity: exists is the
  // parity of the rest OR its negation (= true), forall is false.
  if bdd_dag_exists(m, parity, 0) != bdd_dag_true(m) ||
    bdd_dag_forall(m, parity, 0) != bdd_dag_false(m) {
    return false
  }
  // Budgeted DNF conversion refuses the 32-cube expansion under a
  // small budget and performs it under a sufficient one.
  match (bdd_dag_dnf_face(m, parity, 8), bdd_dag_dnf_face(m, parity, 64)) {
    (None, Some(face)) => {
      // Total decision with a tiny node budget still decides via
      // the search fallback.
      let sat_ok = match face_sat_decide(face, n, max_nodes=2) {
        FaceSat(env) => face_holds(face, env)
        _ => false
      }
      sat_ok && face_eq_decide(face, face, n, max_nodes=2) == FaceDecided(true)
    }
    _ => false
  }
}

///|
fn pair_or_face_for_cost_check(pairs : Int32) -> Face {
  let mut face = FBot
  for i in 0..<pairs {
    face = FOr(face, FEq1(DAnd(DVar(i), DVar(i + pairs))))
  }
  face
}

///|
fn pigeonhole_face_for_cost_check(pigeons : Int32, holes : Int32) -> Face {
  let variable = (pigeon : Int32, hole : Int32) => pigeon * holes + hole
  let mut face = FTop
  for pigeon in 0..<pigeons {
    let mut placed = FBot
    for hole in 0..<holes {
      placed = FOr(placed, FEq1(DVar(variable(pigeon, hole))))
    }
    face = FAnd(face, placed)
  }
  for hole in 0..<holes {
    for a in 0..<pigeons {
      for b in (a + 1)..<pigeons {
        face = FAnd(
          face,
          FOr(FEq0(DVar(variable(a, hole))), FEq0(DVar(variable(b, hole)))),
        )
      }
    }
  }
  face
}

///|
/// Cost-oriented checks: variable-order optimization on the
/// standard separated-pair function, apply-cache table growth on a
/// large elementary-symmetric construction, and watched-literal
/// DPLL on a small pigeonhole formula.
pub fn check_bdd_cost_optimizations() -> Bool {
  let pairs = 4
  let n = 2 * pairs
  let separated = pair_or_face_for_cost_check(pairs)
  let identity = bdd_dag_of_face(separated, n)
  let optimized = bdd_dag_of_face_optimized(separated, n, max_attempts=128)
  if !identity.ok || !optimized.built.ok {
    return false
  }
  let identity_reachable = bdd_dag_reachable_count(
    identity.manager,
    identity.root,
  )
  if optimized.reachable < 0 || optimized.reachable * 3 > identity_reachable {
    return false
  }
  if optimized.order.length() != n {
    return false
  }
  for mask in 0..<pow2(n) {
    let env = assignment_of_mask(mask, n)
    if bdd_dag_eval(optimized.built.manager, optimized.built.root, env) !=
      face_holds(separated, env) {
      return false
    }
  }
  // XOR of every pairwise conjunction gives thousands of apply
  // cache entries; the table must outgrow its initial 1024 buckets.
  let m = bdd_manager_new(20)
  let mut symmetric = bdd_dag_false(m)
  for i in 0..<20 {
    for j in (i + 1)..<20 {
      symmetric = bdd_dag_xor(
        m,
        symmetric,
        bdd_dag_and(m, bdd_dag_var(m, i), bdd_dag_var(m, j)),
      )
    }
  }
  let (_, apply_buckets, apply_entries) = bdd_manager_cache_stats(m)
  if bdd_dag_reachable_count(m, symmetric) == 0 ||
    apply_entries <= 4096 ||
    apply_buckets < 2048 {
    return false
  }
  // PHP(4,3) is unsatisfiable; PHP(3,3) has a checked witness.
  let unsat = pigeonhole_face_for_cost_check(4, 3)
  match face_sat_watched_dpll(unsat, 12, max_steps=100000) {
    FaceUnsat => ()
    _ => return false
  }
  let sat = pigeonhole_face_for_cost_check(3, 3)
  match face_sat_watched_dpll(sat, 9, max_steps=100000) {
    FaceSat(env) => if !face_holds(sat, env) { return false }
    _ => return false
  }
  let stats = face_cnf_stats(unsat, 12)
  stats.variables > 12 && stats.clauses > 12 && stats.literals > stats.clauses
}

// ---------------------------------------------------------------------------
// Phase 11: exact optimal variable order for small variable counts
// ---------------------------------------------------------------------------

///|
fn bdd_next_permutation(perm : Array[Int32]) -> Bool {
  let n = perm.length()
  let mut i = n - 2
  while i >= 0 && perm[i] >= perm[i + 1] {
    i = i - 1
  }
  if i < 0 {
    return false
  }
  let mut j = n - 1
  while perm[j] <= perm[i] {
    j = j - 1
  }
  let tmp = perm[i]
  perm[i] = perm[j]
  perm[j] = tmp
  let mut lo = i + 1
  let mut hi = n - 1
  while lo < hi {
    let t = perm[lo]
    perm[lo] = perm[hi]
    perm[hi] = t
    lo = lo + 1
    hi = hi - 1
  }
  true
}

///|
pub struct BddOptimalBuild {
  built : BddDagFace
  order : Array[Int32]
  size : Int32
  exact : Bool
  tried : Int32
}

///|
/// Build a face's ROBDD under an optimal variable order.  For
/// `n <= exact_max_vars` (default 8) every permutation is tried,
/// so `size` is the true minimum reachable node count and
/// `exact` is true.  Callers that raise `exact_max_vars` to at
/// most 16 use the subset dynamic program in
/// `bdd_dag_of_face_optimal_dp` instead of the factorial
/// enumeration for `n > 8`.  Above the exact bound the budgeted
/// sifting optimizer is used and `exact` is false: exact BDD
/// minimization is NP-hard, so an exponential exact cost remains
/// unavoidable in the worst case.
pub fn bdd_dag_of_face_optimal(
  f : Face,
  n : Int32,
  exact_max_vars~ : Int32 = 8,
  max_nodes~ : Int32 = 0,
) -> BddOptimalBuild {
  if n > 8 && n <= exact_max_vars {
    return bdd_dag_of_face_optimal_dp(f, n, exact_max_vars~, max_nodes~)
  }
  if n > exact_max_vars {
    let opt = bdd_dag_of_face_optimized(f, n, max_nodes~)
    return BddOptimalBuild::{
      built: opt.built,
      order: opt.order,
      size: opt.reachable,
      exact: false,
      tried: opt.attempts,
    }
  }
  let perm : Array[Int32] = []
  for i in 0..<n {
    perm.push(i)
  }
  let mut tried = 0
  let mut best_size = -1
  let mut best_order : Array[Int32] = []
  let mut best_built : BddDagFace? = None
  while true {
    tried = tried + 1
    let order_copy : Array[Int32] = []
    for i in 0..<perm.length() {
      order_copy.push(perm[i])
    }
    let manager = bdd_manager_with_order(order_copy, n, max_nodes~)
    let root = bdd_dag_build_face(manager, f)
    if !manager.exceeded {
      let size = bdd_dag_reachable_count(manager, root)
      if best_size < 0 || size < best_size {
        best_size = size
        best_order = order_copy
        best_built = Some(BddDagFace::{ manager, root, ok: true, })
      }
    }
    if !bdd_next_permutation(perm) {
      break
    }
  }
  match best_built {
    Some(built) =>
      BddOptimalBuild::{
        built,
        order: best_order,
        size: best_size,
        exact: true,
        tried,
      }
    None => {
      // Every order exceeded the node budget: fall back to the
      // heuristic build and say so.
      let opt = bdd_dag_of_face_optimized(f, n, max_nodes~)
      BddOptimalBuild::{
        built: opt.built,
        order: opt.order,
        size: opt.reachable,
        exact: false,
        tried,
      }
    }
  }
}

///|
fn bdd_dp_push_unique(values : Array[Int32], value : Int32) -> Unit {
  for i in 0..<values.length() {
    if values[i] == value {
      return
    }
  }
  values.push(value)
}

///|
/// Build a face's ROBDD under an optimal variable order by dynamic
/// programming over subsets of variables already placed.  If `S` is
/// a set of leading variables, the distinct cofactors obtained by
/// assigning `S` in all possible ways are exactly the subfunctions
/// that can occur immediately below the `S` levels; among them,
/// those depending on the next variable `v` contribute one node
/// each at the `v` level.  Summing this contribution over an order
/// therefore gives its exact nonterminal ROBDD size, and Held-Karp
/// dynamic programming over subsets minimizes the sum.  The
/// cofactor set for `S ∪ {v}` is generated incrementally by
/// restricting every cofactor for `S` at both values of `v`, so
/// the preparation work follows the total number of distinct
/// residual functions actually encountered rather than blindly
/// enumerating all `3^n` subset/assignment pairs.  The result is
/// exact for `n <= exact_max_vars` (capped at 16, because the
/// `2^n` subset table and residual sets must remain finite);
/// above that it falls back to the sifting optimizer with
/// `exact=false`.  `tried` counts DP transitions evaluated.
pub fn bdd_dag_of_face_optimal_dp(
  f : Face,
  n : Int32,
  exact_max_vars~ : Int32 = 16,
  max_nodes~ : Int32 = 0,
) -> BddOptimalBuild {
  if n < 0 || n > exact_max_vars || n > 16 {
    let opt = bdd_dag_of_face_optimized(f, n, max_nodes~)
    return BddOptimalBuild::{
      built: opt.built,
      order: opt.order,
      size: opt.reachable,
      exact: false,
      tried: opt.attempts,
    }
  }
  let m = bdd_manager_new(n, max_nodes~)
  let root = bdd_dag_build_face(m, f)
  if m.exceeded {
    let opt = bdd_dag_of_face_optimized(f, n, max_nodes~)
    return BddOptimalBuild::{
      built: opt.built,
      order: opt.order,
      size: opt.reachable,
      exact: false,
      tried: opt.attempts,
    }
  }
  let subset_count = 1 << n
  // Cofactor sets are built one subset at a time.  Removing the
  // least variable `v` from a nonempty mask gives a numerically
  // smaller predecessor, and the set for the mask is the union of
  // the two restrictions of every predecessor cofactor at `v`.
  let cofactor_sets : Array[Array[Int32]] = []
  for mask in 0..<subset_count {
    if mask == 0 {
      cofactor_sets.push([root])
      continue
    }
    let mut chosen = 0
    for variable in 0..<n {
      let bit = 1 << variable
      let present = mask & bit
      if present != 0 {
        chosen = variable
        break
      }
    }
    let previous = cofactor_sets[mask - (1 << chosen)]
    let roots : Array[Int32] = []
    for i in 0..<previous.length() {
      bdd_dp_push_unique(roots, bdd_dag_restrict(m, previous[i], chosen, false))
      bdd_dp_push_unique(roots, bdd_dag_restrict(m, previous[i], chosen, true))
    }
    cofactor_sets.push(roots)
  }
  if m.exceeded {
    let opt = bdd_dag_of_face_optimized(f, n, max_nodes~)
    return BddOptimalBuild::{
      built: opt.built,
      order: opt.order,
      size: opt.reachable,
      exact: false,
      tried: opt.attempts,
    }
  }
  // Node ids are allocated after their children, so supports can
  // be computed in id order.
  let support : Array[Int32] = [0, 0]
  for id in 2..<m.nodes.length() {
    let node = m.nodes[id]
    let variable_bit = 1 << m.order[node.rank]
    support.push(variable_bit | support[node.lo] | support[node.hi])
  }
  let no_cost = 1000000000
  let cost : Array[Int32] = []
  let parent : Array[Int32] = []
  for _i in 0..<subset_count {
    cost.push(no_cost)
    parent.push(-1)
  }
  cost[0] = 0
  let mut tried = 0
  for mask in 0..<subset_count {
    if cost[mask] == no_cost {
      continue
    }
    for variable in 0..<n {
      let bit = 1 << variable
      let already = mask & bit
      if already != 0 {
        continue
      }
      tried = tried + 1
      let mut active = 0
      let roots = cofactor_sets[mask]
      for i in 0..<roots.length() {
        let depends = support[roots[i]] & bit
        if depends != 0 {
          active = active + 1
        }
      }
      let next = mask | bit
      let candidate = cost[mask] + active
      if candidate < cost[next] {
        cost[next] = candidate
        parent[next] = variable
      }
    }
  }
  let full = subset_count - 1
  let reversed : Array[Int32] = []
  let mut cursor = full
  while cursor != 0 {
    let variable = parent[cursor]
    if variable < 0 {
      break
    }
    reversed.push(variable)
    cursor = cursor - (1 << variable)
  }
  let order : Array[Int32] = []
  let mut index = reversed.length() - 1
  while index >= 0 {
    order.push(reversed[index])
    index = index - 1
  }
  // Defensive completion; the DP parent chain should already be a
  // permutation.
  for variable in 0..<n {
    bdd_dp_push_unique(order, variable)
  }
  let manager = bdd_manager_with_order(order, n, max_nodes~)
  let built_root = bdd_dag_build_face(manager, f)
  if manager.exceeded {
    let opt = bdd_dag_of_face_optimized(f, n, max_nodes~)
    return BddOptimalBuild::{
      built: opt.built,
      order: opt.order,
      size: opt.reachable,
      exact: false,
      tried,
    }
  }
  let size = bdd_dag_reachable_count(manager, built_root)
  BddOptimalBuild::{
    built: BddDagFace::{ manager, root: built_root, ok: true, },
    order,
    size,
    exact: size == cost[full],
    tried,
  }
}

///|
pub struct BddPrunedOptimalBuild {
  built : BddDagFace
  order : Array[Int32]
  size : Int32
  active_vars : Int32
  incumbent_size : Int32
  tried : Int32
  pruned_subsets : Int32
  exact : Bool
}

///|
fn bdd_popcount32(mask0 : Int32) -> Int32 {
  let mut mask = mask0
  let mut count = 0
  while mask != 0 {
    mask = mask & (mask - 1)
    count = count + 1
  }
  count
}

///|
fn bdd_remap_dim(d : Dim, var_map : Array[Int32]) -> Dim {
  match d {
    DZero => DZero
    DOne => DOne
    DVar(v) =>
      if v >= 0 && v < var_map.length() && var_map[v] >= 0 {
        DVar(var_map[v])
      } else {
        DZero
      }
    DNeg(a) => DNeg(bdd_remap_dim(a, var_map))
    DAnd(a, b) => DAnd(bdd_remap_dim(a, var_map), bdd_remap_dim(b, var_map))
    DOr(a, b) => DOr(bdd_remap_dim(a, var_map), bdd_remap_dim(b, var_map))
  }
}

///|
fn bdd_remap_face(f : Face, var_map : Array[Int32]) -> Face {
  match f {
    FTop => FTop
    FBot => FBot
    FEq0(d) => FEq0(bdd_remap_dim(d, var_map))
    FEq1(d) => FEq1(bdd_remap_dim(d, var_map))
    FAnd(a, b) => FAnd(bdd_remap_face(a, var_map), bdd_remap_face(b, var_map))
    FOr(a, b) => FOr(bdd_remap_face(a, var_map), bdd_remap_face(b, var_map))
  }
}

///|
/// Exact optimal ROBDD variable ordering with active-support
/// projection, incremental cofactor support maintenance, cofactor
/// symmetry-orbit canonicalization, and admissible branch-and-bound
/// subset pruning.
///
/// 1. Variables outside `face_vars(f)` contribute zero ROBDD nodes at
///    any rank; projecting `f` onto its active variable support `V`
///    decides exact optimal orders for arbitrary ambient `n` whenever
///    `|V| <= exact_max_vars` (`<= 22`).
/// 2. Seeding an upper bound `U` with `bdd_dag_of_face_optimized` on
///    `V`, any subset prefix `S` whose partial cost plus the union
///    of remaining essential cofactor supports reaches `U` cannot
///    strictly improve `U` and is pruned without expanding transitions.
/// 3. If unplaced variables `u < v` are functionally symmetric in every
///    residual cofactor at `S` (`r[u:=0,v:=1] == r[u:=1,v:=0]`), the
///    transposition `(u v)` preserves residual ROBDD size across every
///    completion of `S`; canonically requiring `u` to precede `v`
///    prunes symmetric factorial orbits while preserving exact global
///    optimality.
pub fn bdd_dag_of_face_optimal_pruned(
  f : Face,
  n : Int32,
  exact_max_vars~ : Int32 = 20,
  max_nodes~ : Int32 = 0,
) -> BddPrunedOptimalBuild {
  if n < 0 {
    let opt = bdd_dag_of_face_optimized(f, 0, max_nodes~)
    return BddPrunedOptimalBuild::{
      built: opt.built,
      order: opt.order,
      size: opt.reachable,
      active_vars: 0,
      incumbent_size: opt.reachable,
      tried: opt.attempts,
      pruned_subsets: 0,
      exact: false,
    }
  }
  let raw_vars = face_vars(f)
  let active : Array[Int32] = []
  for v in 0..<n {
    if raw_vars.contains(v) {
      active.push(v)
    }
  }
  let k = active.length()
  if k == 0 {
    let order : Array[Int32] = []
    for v in 0..<n {
      order.push(v)
    }
    let manager = bdd_manager_with_order(order, n, max_nodes~)
    let root = bdd_dag_build_face(manager, f)
    return BddPrunedOptimalBuild::{
      built: BddDagFace::{ manager, root, ok: !manager.exceeded, },
      order,
      size: 0,
      active_vars: 0,
      incumbent_size: 0,
      tried: 0,
      pruned_subsets: 0,
      exact: !manager.exceeded,
    }
  }
  let cap = if exact_max_vars > 22 { 22 } else { exact_max_vars }
  if k > cap {
    let opt = bdd_dag_of_face_optimized(f, n, max_nodes~)
    return BddPrunedOptimalBuild::{
      built: opt.built,
      order: opt.order,
      size: opt.reachable,
      active_vars: k,
      incumbent_size: opt.reachable,
      tried: opt.attempts,
      pruned_subsets: 0,
      exact: false,
    }
  }
  let var_map : Array[Int32] = []
  for _v in 0..<n {
    var_map.push(-1)
  }
  for idx in 0..<k {
    var_map[active[idx]] = idx
  }
  let f_proj = bdd_remap_face(f, var_map)
  let seed = bdd_dag_of_face_optimized(f_proj, k, max_nodes~)
  let m = bdd_manager_new(k, max_nodes~)
  let root = bdd_dag_build_face(m, f_proj)
  if m.exceeded || !seed.built.ok {
    let opt = bdd_dag_of_face_optimized(f, n, max_nodes~)
    return BddPrunedOptimalBuild::{
      built: opt.built,
      order: opt.order,
      size: opt.reachable,
      active_vars: k,
      incumbent_size: opt.reachable,
      tried: opt.attempts,
      pruned_subsets: 0,
      exact: false,
    }
  }
  let incumbent = seed.reachable
  let subset_count = 1 << k
  let no_cost = 1000000000
  let cost : Array[Int32] = []
  let parent : Array[Int32] = []
  let cofactor_sets : Array[Array[Int32]] = []
  let has_cofactors : Array[Bool] = []
  for _i in 0..<subset_count {
    cost.push(no_cost)
    parent.push(-1)
    cofactor_sets.push([])
    has_cofactors.push(false)
  }
  cost[0] = 0
  cofactor_sets[0] = [root]
  has_cofactors[0] = true

  let support : Array[Int32] = [0, 0]
  let sync_support = () => {
    while support.length() < m.nodes.length() {
      let id = support.length()
      let node = m.nodes[id]
      let vbit = 1 << m.order[node.rank]
      support.push(vbit | support[node.lo] | support[node.hi])
    }
  }

  let ensure_cofactors = (mask : Int32) => {
    let stack : Array[Int32] = []
    let mut cur = mask
    while cur > 0 && !has_cofactors[cur] {
      stack.push(cur)
      let mut low_v = 0
      for v in 0..<k {
        if (cur & (1 << v)) != 0 {
          low_v = v
          break
        }
      }
      cur = cur - (1 << low_v)
    }
    let mut si = stack.length() - 1
    while si >= 0 {
      let target = stack[si]
      let mut chosen = 0
      for v in 0..<k {
        if (target & (1 << v)) != 0 {
          chosen = v
          break
        }
      }
      let prev_roots = cofactor_sets[target - (1 << chosen)]
      let roots : Array[Int32] = []
      for i in 0..<prev_roots.length() {
        bdd_dp_push_unique(
          roots,
          bdd_dag_restrict(m, prev_roots[i], chosen, false),
        )
        bdd_dp_push_unique(
          roots,
          bdd_dag_restrict(m, prev_roots[i], chosen, true),
        )
      }
      cofactor_sets[target] = roots
      has_cofactors[target] = true
      si = si - 1
    }
  }

  let vars_symmetric_at = (roots : Array[Int32], u : Int32, v : Int32) => {
    let ubit = 1 << u
    let vbit = 1 << v
    for i in 0..<roots.length() {
      let r = roots[i]
      let sup_r = support[r]
      if (sup_r & (ubit | vbit)) == 0 {
        continue
      }
      let r_u0_v1 = bdd_dag_restrict(
        m,
        bdd_dag_restrict(m, r, u, false),
        v,
        true,
      )
      let r_u1_v0 = bdd_dag_restrict(
        m,
        bdd_dag_restrict(m, r, u, true),
        v,
        false,
      )
      if r_u0_v1 != r_u1_v0 {
        return false
      }
    }
    true
  }

  let full_mask = (1 << k) - 1
  let mut tried = 0
  let mut pruned_subsets = 0
  for mask in 0..<(subset_count - 1) {
    if cost[mask] >= incumbent {
      if cost[mask] != no_cost {
        pruned_subsets = pruned_subsets + 1
      }
      continue
    }
    ensure_cofactors(mask)
    if m.exceeded {
      break
    }
    sync_support()
    let roots = cofactor_sets[mask]
    let rem_mask = full_mask ^ mask
    let mut rem_union = 0
    for i in 0..<roots.length() {
      rem_union = rem_union | (support[roots[i]] & rem_mask)
    }
    if cost[mask] + bdd_popcount32(rem_union) >= incumbent {
      pruned_subsets = pruned_subsets + 1
      continue
    }
    let unplaced : Array[Int32] = []
    for variable in 0..<k {
      if (mask & (1 << variable)) == 0 {
        unplaced.push(variable)
      }
    }
    for ui in 0..<unplaced.length() {
      let variable = unplaced[ui]
      let mut has_sym_pred = false
      for pi in 0..<ui {
        let pred = unplaced[pi]
        if vars_symmetric_at(roots, pred, variable) {
          has_sym_pred = true
          break
        }
      }
      sync_support()
      if m.exceeded {
        break
      }
      if has_sym_pred {
        continue
      }
      let bit = 1 << variable
      tried = tried + 1
      let mut active_cnt = 0
      for i in 0..<roots.length() {
        if (support[roots[i]] & bit) != 0 {
          active_cnt = active_cnt + 1
        }
      }
      let next = mask | bit
      let cand = cost[mask] + active_cnt
      if cand < incumbent && cand < cost[next] {
        cost[next] = cand
        parent[next] = variable
      }
    }
    if m.exceeded {
      break
    }
  }
  if m.exceeded {
    let opt = bdd_dag_of_face_optimized(f, n, max_nodes~)
    return BddPrunedOptimalBuild::{
      built: opt.built,
      order: opt.order,
      size: opt.reachable,
      active_vars: k,
      incumbent_size: incumbent,
      tried,
      pruned_subsets,
      exact: false,
    }
  }
  let full = subset_count - 1
  let proj_order : Array[Int32] = if cost[full] < incumbent {
    let rev : Array[Int32] = []
    let mut cursor = full
    while cursor != 0 {
      let v = parent[cursor]
      if v < 0 {
        break
      }
      rev.push(v)
      cursor = cursor - (1 << v)
    }
    let ord : Array[Int32] = []
    let mut idx = rev.length() - 1
    while idx >= 0 {
      ord.push(rev[idx])
      idx = idx - 1
    }
    for v in 0..<k {
      bdd_dp_push_unique(ord, v)
    }
    ord
  } else {
    seed.order
  }
  let full_order : Array[Int32] = []
  for i in 0..<proj_order.length() {
    full_order.push(active[proj_order[i]])
  }
  for v in 0..<n {
    if !raw_vars.contains(v) {
      full_order.push(v)
    }
  }
  let manager = bdd_manager_with_order(full_order, n, max_nodes~)
  let built_root = bdd_dag_build_face(manager, f)
  if manager.exceeded {
    let opt = bdd_dag_of_face_optimized(f, n, max_nodes~)
    return BddPrunedOptimalBuild::{
      built: opt.built,
      order: opt.order,
      size: opt.reachable,
      active_vars: k,
      incumbent_size: incumbent,
      tried,
      pruned_subsets,
      exact: false,
    }
  }
  let final_size = bdd_dag_reachable_count(manager, built_root)
  let expected_opt = if cost[full] < incumbent { cost[full] } else { incumbent }
  BddPrunedOptimalBuild::{
    built: BddDagFace::{ manager, root: built_root, ok: true, },
    order: full_order,
    size: final_size,
    active_vars: k,
    incumbent_size: incumbent,
    tried,
    pruned_subsets,
    exact: final_size == expected_opt,
  }
}

///|
pub struct BddDecomposedOptimalBuild {
  built : BddDagFace
  order : Array[Int32]
  size : Int32
  active_vars : Int32
  component_count : Int32
  max_component_vars : Int32
  tried : Int32
  pruned_subsets : Int32
  exact : Bool
}

///|
fn bdd_collect_conjuncts(f : Face, out : Array[Face]) -> Unit {
  match f {
    FAnd(a, b) => {
      bdd_collect_conjuncts(a, out)
      bdd_collect_conjuncts(b, out)
    }
    FEq0(DOr(a, b)) => {
      bdd_collect_conjuncts(FEq0(a), out)
      bdd_collect_conjuncts(FEq0(b), out)
    }
    FEq1(DAnd(a, b)) => {
      bdd_collect_conjuncts(FEq1(a), out)
      bdd_collect_conjuncts(FEq1(b), out)
    }
    FEq0(DNeg(a)) => bdd_collect_conjuncts(FEq1(a), out)
    FEq1(DNeg(a)) => bdd_collect_conjuncts(FEq0(a), out)
    _ => out.push(f)
  }
}

///|
fn bdd_collect_disjuncts(f : Face, out : Array[Face]) -> Unit {
  match f {
    FOr(a, b) => {
      bdd_collect_disjuncts(a, out)
      bdd_collect_disjuncts(b, out)
    }
    FEq0(DAnd(a, b)) => {
      bdd_collect_disjuncts(FEq0(a), out)
      bdd_collect_disjuncts(FEq0(b), out)
    }
    FEq1(DOr(a, b)) => {
      bdd_collect_disjuncts(FEq1(a), out)
      bdd_collect_disjuncts(FEq1(b), out)
    }
    FEq0(DNeg(a)) => bdd_collect_disjuncts(FEq1(a), out)
    FEq1(DNeg(a)) => bdd_collect_disjuncts(FEq0(a), out)
    _ => out.push(f)
  }
}

///|
fn bdd_uf_find(parent : Array[Int32], x0 : Int32) -> Int32 {
  let mut x = x0
  while parent[x] != x {
    parent[x] = parent[parent[x]]
    x = parent[x]
  }
  x
}

///|
fn bdd_uf_union(parent : Array[Int32], a : Int32, b : Int32) -> Unit {
  let ra = bdd_uf_find(parent, a)
  let rb = bdd_uf_find(parent, b)
  if ra != rb {
    if ra < rb {
      parent[rb] = ra
    } else {
      parent[ra] = rb
    }
  }
}

///|
/// Exact ROBDD variable ordering via disjoint-support connected-component
/// decomposition + symmetry-orbit pruned DP (`bdd_dag_of_face_optimal_pruned`),
/// breaking the monolithic `n <= 18` barrier whenever top-level conjunctive
/// or disjunctive cubical constraints partition into independent variable
/// components of size `<= component_max_vars` (certifying `exact = true`
/// across `n = 24..36+` active variables).
///
/// By the Disjoint-Support ROBDD Additivity Theorem, if `f` is a
/// conjunction (or disjunction) of non-constant subformulas `g_1(V_1), ...,
/// g_m(V_m)` over pairwise disjoint active variable supports `V_r`, every
/// global variable permutation `pi` induces orders `pi_r` on `V_r` with
/// `|ROBDD(f, pi)| >= sum_r |ROBDD(g_r, pi_r)| >= sum_r opt(g_r)`, and
/// concatenating the exact optimal component orders achieves exact equality.
pub fn bdd_dag_of_face_optimal_decomposed(
  f : Face,
  n : Int32,
  component_max_vars~ : Int32 = 20,
  max_nodes~ : Int32 = 0,
) -> BddDecomposedOptimalBuild {
  if n <= 0 {
    let res = bdd_dag_of_face_optimal_pruned(
      f,
      if n < 0 { 0 } else { n },
      exact_max_vars=component_max_vars,
      max_nodes~,
    )
    return BddDecomposedOptimalBuild::{
      built: res.built,
      order: res.order,
      size: res.size,
      active_vars: res.active_vars,
      component_count: if res.active_vars > 0 { 1 } else { 0 },
      max_component_vars: res.active_vars,
      tried: res.tried,
      pruned_subsets: res.pruned_subsets,
      exact: res.exact,
    }
  }
  let raw_vars = face_vars(f)
  let active : Array[Int32] = []
  for v in 0..<n {
    if raw_vars.contains(v) {
      active.push(v)
    }
  }
  let k = active.length()
  if k == 0 {
    let res = bdd_dag_of_face_optimal_pruned(
      f,
      n,
      exact_max_vars=component_max_vars,
      max_nodes~,
    )
    return BddDecomposedOptimalBuild::{
      built: res.built,
      order: res.order,
      size: res.size,
      active_vars: 0,
      component_count: 0,
      max_component_vars: 0,
      tried: 0,
      pruned_subsets: 0,
      exact: res.exact,
    }
  }
  let conjuncts : Array[Face] = []
  bdd_collect_conjuncts(f, conjuncts)
  let disjuncts : Array[Face] = []
  bdd_collect_disjuncts(f, disjuncts)
  let is_conj = conjuncts.length() >= disjuncts.length()
  let clauses = if is_conj { conjuncts } else { disjuncts }

  if clauses.length() <= 1 {
    let single = bdd_dag_of_face_optimal_pruned(
      f,
      n,
      exact_max_vars=component_max_vars,
      max_nodes~,
    )
    return BddDecomposedOptimalBuild::{
      built: single.built,
      order: single.order,
      size: single.size,
      active_vars: k,
      component_count: 1,
      max_component_vars: k,
      tried: single.tried,
      pruned_subsets: single.pruned_subsets,
      exact: single.exact,
    }
  }

  let var_to_idx : Array[Int32] = []
  for _v in 0..<n {
    var_to_idx.push(-1)
  }
  for idx in 0..<k {
    var_to_idx[active[idx]] = idx
  }
  let uf : Array[Int32] = []
  for idx in 0..<k {
    uf.push(idx)
  }
  let clause_var_indices : Array[Array[Int32]] = []
  for ci in 0..<clauses.length() {
    let cv = face_vars(clauses[ci])
    let idxs : Array[Int32] = []
    for v in 0..<n {
      if cv.contains(v) && var_to_idx[v] >= 0 {
        idxs.push(var_to_idx[v])
      }
    }
    for j in 1..<idxs.length() {
      bdd_uf_union(uf, idxs[0], idxs[j])
    }
    clause_var_indices.push(idxs)
  }

  let comp_roots : Array[Int32] = []
  for idx in 0..<k {
    let r = bdd_uf_find(uf, idx)
    bdd_dp_push_unique(comp_roots, r)
  }
  if comp_roots.length() <= 1 {
    let single = bdd_dag_of_face_optimal_pruned(
      f,
      n,
      exact_max_vars=component_max_vars,
      max_nodes~,
    )
    return BddDecomposedOptimalBuild::{
      built: single.built,
      order: single.order,
      size: single.size,
      active_vars: k,
      component_count: 1,
      max_component_vars: k,
      tried: single.tried,
      pruned_subsets: single.pruned_subsets,
      exact: single.exact,
    }
  }

  let comp_order : Array[Int32] = []
  let mut sum_opt_sizes = 0
  let mut total_tried = 0
  let mut total_pruned = 0
  let mut all_comp_exact = true
  let mut max_comp_k = 0
  let mut annihilated = false

  for ci in 0..< clauses.length() {
    if clause_var_indices[ci].length() == 0 {
      let c_res = bdd_dag_of_face_optimal_pruned(
        clauses[ci],
        n,
        exact_max_vars=component_max_vars,
        max_nodes~,
      )
      if is_conj && c_res.built.root == 0 {
        annihilated = true
      }
      if !is_conj && c_res.built.root == 1 {
        annihilated = true
      }
    }
  }

  for cri in 0..<comp_roots.length() {
    let root_id = comp_roots[cri]
    let comp_vars : Array[Int32] = []
    for idx in 0..<k {
      if bdd_uf_find(uf, idx) == root_id {
        comp_vars.push(active[idx])
      }
    }
    if comp_vars.length() > max_comp_k {
      max_comp_k = comp_vars.length()
    }
    let mut sub_face : Face = if is_conj { FTop } else { FBot }
    let mut first = true
    for ci in 0..<clauses.length() {
      let idxs = clause_var_indices[ci]
      if idxs.length() > 0 && bdd_uf_find(uf, idxs[0]) == root_id {
        if first {
          sub_face = clauses[ci]
          first = false
        } else if is_conj {
          sub_face = FAnd(sub_face, clauses[ci])
        } else {
          sub_face = FOr(sub_face, clauses[ci])
        }
      }
    }
    let sub_opt = bdd_dag_of_face_optimal_pruned(
      sub_face,
      n,
      exact_max_vars=component_max_vars,
      max_nodes~,
    )
    total_tried = total_tried + sub_opt.tried
    total_pruned = total_pruned + sub_opt.pruned_subsets
    if !sub_opt.exact || !sub_opt.built.ok {
      all_comp_exact = false
    }
    if is_conj && sub_opt.built.root == 0 {
      annihilated = true
    }
    if !is_conj && sub_opt.built.root == 1 {
      annihilated = true
    }
    sum_opt_sizes = sum_opt_sizes + sub_opt.size
    for oi in 0..<sub_opt.order.length() {
      let v = sub_opt.order[oi]
      if comp_vars.contains(v) {
        bdd_dp_push_unique(comp_order, v)
      }
    }
    for vi in 0..<comp_vars.length() {
      bdd_dp_push_unique(comp_order, comp_vars[vi])
    }
  }

  for v in 0..<n {
    bdd_dp_push_unique(comp_order, v)
  }

  let manager = bdd_manager_with_order(comp_order, n, max_nodes~)
  let built_root = bdd_dag_build_face(manager, f)
  if manager.exceeded {
    let opt = bdd_dag_of_face_optimized(f, n, max_nodes~)
    return BddDecomposedOptimalBuild::{
      built: opt.built,
      order: opt.order,
      size: opt.reachable,
      active_vars: k,
      component_count: comp_roots.length(),
      max_component_vars: max_comp_k,
      tried: total_tried,
      pruned_subsets: total_pruned,
      exact: false,
    }
  }
  let final_size = bdd_dag_reachable_count(manager, built_root)
  let exact_ok = if annihilated {
    final_size == 0
  } else {
    all_comp_exact && final_size == sum_opt_sizes
  }
  BddDecomposedOptimalBuild::{
    built: BddDagFace::{ manager, root: built_root, ok: true, },
    order: comp_order,
    size: final_size,
    active_vars: k,
    component_count: comp_roots.length(),
    max_component_vars: max_comp_k,
    tried: total_tried,
    pruned_subsets: total_pruned,
    exact: exact_ok,
  }
}
