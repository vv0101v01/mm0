///|
/// Phase 11: hash-consing (interning) for dependent terms.
///
/// `dterm_rebuild` is the exact inverse of `dterm_children`: it
/// reassembles a term from a same-shaped spine and a replacement
/// child list (in `dterm_children` order).  On top of it,
/// `DTermInternTable` implements classical bottom-up hash-consing:
/// children are interned first, then the node is keyed by a local
/// stamp (the cache key of the node with its children replaced by
/// marker variables, which captures the constructor and every
/// non-term field: dimensions, faces, levels, constructor indices
/// and embedded schema descriptors) together with the children's
/// intern ids.  Structurally equal subterms therefore collapse to
/// one shared representative, so repeated subtrees are stored once.
///
/// Interning is purely representational: `dterm_intern(table, t)` is
/// structurally equal to `t` (same `dterm_cache_key`), hence every
/// kernel operation (inference, evaluation, conversion) gives the
/// same answers on interned and uninterned terms.  The table is an
/// explicit value threaded by the caller (the kernel keeps no
/// mutable global state), which is the form in which global
/// hash-consing can be adopted incrementally by the checker and the
/// module system.
///
/// Phase 13 makes the table's node graph explicit.  Every entry
/// records its child intern ids, so a reachable part of the table
/// can be exported as a `DTermDagSnapshot` -- local node shells
/// plus child-id edges and root ids -- and imported into another
/// (or the same) table by node-wise hash-consing.  The byte codec
/// for this snapshot in `dterm_dag_binary.mbt` therefore
/// serializes the same DAG that the in-process interner uses,
/// rather than introducing a second term-sharing representation.

///|
/// Reassemble `t` with its `DTerm` children replaced by `cs`
/// (in `dterm_children` order).  If the arity does not match,
/// `t` is returned unchanged.  Non-term fields (schema
/// descriptors, faces, dimensions, levels, indices) are preserved.
pub fn dterm_rebuild(t : DTerm, cs : Array[DTerm]) -> DTerm {
  if cs.length() != dterm_children(t).length() {
    return t
  }
  match t {
    DPi(_, _) => DPi(cs[0], cs[1])
    DSigma(_, _) => DSigma(cs[0], cs[1])
    DLam(_, _) => DLam(cs[0], cs[1])
    DApp(_, _) => DApp(cs[0], cs[1])
    DPair(_, _) => DPair(cs[0], cs[1])
    DAnn(_, _) => DAnn(cs[0], cs[1])
    DCons(_, _) => DCons(cs[0], cs[1])
    DFst(_) => DFst(cs[0])
    DSnd(_) => DSnd(cs[0])
    DLamDim(_) => DLamDim(cs[0])
    DSucc(_) => DSucc(cs[0])
    DListTy(_) => DListTy(cs[0])
    DBoolElim(_, _, _, _) => DBoolElim(cs[0], cs[1], cs[2], cs[3])
    DNatElim(_, _, _, _) => DNatElim(cs[0], cs[1], cs[2], cs[3])
    DListElim(_, _, _, _) => DListElim(cs[0], cs[1], cs[2], cs[3])
    DCircleElim(_, _, _, _) => DCircleElim(cs[0], cs[1], cs[2], cs[3])
    DPartial(branches) => DPartial(dterm_intern_zip_face_terms(branches, cs, 0))
    DPathP(_, _, _) => DPathP(cs[0], cs[1], cs[2])
    DPath(_, _, _) => DPath(cs[0], cs[1], cs[2])
    DAppDim(_, d) => DAppDim(cs[0], d)
    DCoe(_, r, s, _) => DCoe(cs[0], r, s, cs[1])
    DComp(_, tubes, _) =>
      DComp(cs[0], dterm_intern_zip_tube_terms(tubes, cs, 2), cs[1])
    DHComp(_, tubes, _) =>
      DHComp(cs[0], dterm_intern_zip_tube_terms(tubes, cs, 2), cs[1])
    DHFill(_, tubes, _, d) =>
      DHFill(cs[0], dterm_intern_zip_tube_terms(tubes, cs, 2), cs[1], d)
    DTorusElim(_, _, _) => DTorusElim(cs[0], cs[1], cs[2])
    DInductive(spec, _) => DInductive(spec, cs)
    DHitType(spec, _) => DHitType(spec, cs)
    DIntro(spec, k, params, _) =>
      DIntro(
        spec,
        k,
        dterm_intern_slice(cs, 0, params.length()),
        dterm_intern_slice(cs, params.length(), cs.length()),
      )
    DHitIntro(spec, k, params, _, dims) =>
      DHitIntro(
        spec,
        k,
        dterm_intern_slice(cs, 0, params.length()),
        dterm_intern_slice(cs, params.length(), cs.length()),
        dims,
      )
    DInductiveElim(spec, _, cases, params, _, _) =>
      DInductiveElim(
        spec,
        cs[0],
        dterm_intern_slice(cs, 2, 2 + cases.length()),
        dterm_intern_slice(
          cs,
          2 + cases.length(),
          2 + cases.length() + params.length(),
        ),
        dterm_intern_slice(
          cs,
          2 + cases.length() + params.length(),
          cs.length(),
        ),
        cs[1],
      )
    DHitElim(spec, _, cases, params, _, _) =>
      DHitElim(
        spec,
        cs[0],
        dterm_intern_slice(cs, 2, 2 + cases.length()),
        dterm_intern_slice(
          cs,
          2 + cases.length(),
          2 + cases.length() + params.length(),
        ),
        dterm_intern_slice(
          cs,
          2 + cases.length() + params.length(),
          cs.length(),
        ),
        cs[1],
      )
    DEquivTy(_, _) => DEquivTy(cs[0], cs[1])
    DMkEquiv(_, _, _, _, _, _) =>
      DMkEquiv(cs[0], cs[1], cs[2], cs[3], cs[4], cs[5])
    DEquivFwd(_) => DEquivFwd(cs[0])
    DEquivBwd(_) => DEquivBwd(cs[0])
    DEquivSect(_) => DEquivSect(cs[0])
    DEquivRetr(_) => DEquivRetr(cs[0])
    DUa(_) => DUa(cs[0])
    DGlueEquiv(_, branches) =>
      DGlueEquiv(cs[0], dterm_intern_zip_equiv_branches(branches, cs))
    DUnglueEquiv(_, _, branches) => {
      let out : Array[DEquivBranch] = []
      for i in 0..<branches.length() {
        out.push({
          face: branches[i].face,
          ty: cs[2 + 2 * i],
          equiv: cs[3 + 2 * i],
        })
      }
      DUnglueEquiv(cs[0], cs[1], out)
    }
    DDecode(spec, params, _, _) =>
      DDecode(
        spec,
        dterm_intern_slice(cs, 1, 1 + params.length()),
        dterm_intern_slice(cs, 1 + params.length(), cs.length()),
        cs[0],
      )
    _ => t
  }
}

///|
fn dterm_intern_slice(
  cs : Array[DTerm],
  lo : Int32,
  hi : Int32,
) -> Array[DTerm] {
  let out : Array[DTerm] = []
  for i in lo..<hi {
    out.push(cs[i])
  }
  out
}

///|
fn dterm_intern_zip_face_terms(
  branches : Array[DFaceTerm],
  cs : Array[DTerm],
  offset : Int32,
) -> Array[DFaceTerm] {
  let out : Array[DFaceTerm] = []
  for i in 0..<branches.length() {
    out.push({ face: branches[i].face, body: cs[offset + i], })
  }
  out
}

///|
fn dterm_intern_zip_tube_terms(
  tubes : Array[DTubeTerm],
  cs : Array[DTerm],
  offset : Int32,
) -> Array[DTubeTerm] {
  let out : Array[DTubeTerm] = []
  for i in 0..<tubes.length() {
    out.push({ face: tubes[i].face, body: cs[offset + i], })
  }
  out
}

///|
fn dterm_intern_zip_equiv_branches(
  branches : Array[DEquivBranch],
  cs : Array[DTerm],
) -> Array[DEquivBranch] {
  let out : Array[DEquivBranch] = []
  for i in 0..<branches.length() {
    out.push({
      face: branches[i].face,
      ty: cs[1 + 2 * i],
      equiv: cs[2 + 2 * i],
    })
  }
  out
}

///|
/// Hash-consing table: maps each distinct node's composite key to
/// its id, with the representatives stored by id.
pub struct DTermInternTable {
  ids : Map[String, Int32]
  terms : Array[DTerm]
  node_children : Array[Array[Int32]]
}

///|
pub fn dterm_intern_table_new() -> DTermInternTable {
  { ids: {}, terms: [], node_children: [], }
}

///|
pub fn dterm_intern_table_size(table : DTermInternTable) -> Int32 {
  table.terms.length()
}

///|
/// The local shell of a node: the node with every child replaced
/// by a positional marker variable `DTVar(1000000 + i)`.  A shell
/// plus a list of child intern ids is the unit stored in a DAG
/// snapshot.  Rebuilding the shell with the children denoted by
/// those ids reconstructs the node.
pub fn dterm_local_shell(t : DTerm) -> DTerm {
  let count = dterm_children(t).length()
  let markers : Array[DTerm] = []
  for i in 0..<count {
    markers.push(DTVar(1000000 + i))
  }
  dterm_rebuild(t, markers)
}

///|
/// Local stamp: the cache key of a node's local shell.  Two nodes
/// share a stamp iff they use the same constructor with the same
/// non-term fields (and the same number of children).
pub fn dterm_local_stamp(t : DTerm) -> String {
  dterm_cache_key(dterm_local_shell(t))
}

///|
fn dterm_intern_key(shell : DTerm, child_ids : Array[Int32]) -> String {
  let mut key = dterm_cache_key(dterm_local_shell(shell))
  key = key + "<"
  for i in 0..<child_ids.length() {
    if i > 0 {
      key = key + ","
    }
    key = key + child_ids[i].to_string()
  }
  key + ">"
}

///|
/// The representative stored at an intern id, or `None` for an
/// out-of-range id.
pub fn dterm_intern_table_term(table : DTermInternTable, id : Int32) -> DTerm? {
  if id < 0 || id >= table.terms.length() {
    None
  } else {
    Some(table.terms[id])
  }
}

///|
/// A copy of the child intern ids of the node at `id`, in
/// `dterm_children` order, or `None` for an out-of-range id.
pub fn dterm_intern_table_children(
  table : DTermInternTable,
  id : Int32,
) -> Array[Int32]? {
  if id < 0 || id >= table.node_children.length() {
    return None
  }
  let out : Array[Int32] = []
  for i in 0..<table.node_children[id].length() {
    out.push(table.node_children[id][i])
  }
  Some(out)
}

///|
/// Non-inserting lookup: the intern id of `t` when every subterm
/// of `t` is already present in `table`, and -1 otherwise.  This
/// is the read-only counterpart of `dterm_intern_id`.
pub fn dterm_intern_lookup_id(table : DTermInternTable, t : DTerm) -> Int32 {
  let children = dterm_children(t)
  let child_ids : Array[Int32] = []
  for i in 0..<children.length() {
    let child_id = dterm_intern_lookup_id(table, children[i])
    if child_id < 0 {
      return -1
    }
    child_ids.push(child_id)
  }
  match table.ids.get(dterm_intern_key(t, child_ids)) {
    Some(id) => id
    None => -1
  }
}

///|
/// Intern one already-decomposed node: `shell` supplies the
/// constructor and every non-term field (its own children are
/// ignored, conventionally the positional markers of
/// `dterm_local_shell`), and `child_ids` supplies the children
/// by intern id.  This is the node-wise operation behind DAG
/// import: it neither traverses nor rebuilds the children's
/// subtrees.  Returns `None` when the arity disagrees or a child
/// id is out of range.
pub fn dterm_intern_node(
  table : DTermInternTable,
  shell : DTerm,
  child_ids : Array[Int32],
) -> (DTerm, Int32)? {
  if dterm_children(shell).length() != child_ids.length() {
    return None
  }
  let child_terms : Array[DTerm] = []
  let stored_child_ids : Array[Int32] = []
  for i in 0..<child_ids.length() {
    let child_id = child_ids[i]
    if child_id < 0 || child_id >= table.terms.length() {
      return None
    }
    child_terms.push(table.terms[child_id])
    stored_child_ids.push(child_id)
  }
  let key = dterm_intern_key(shell, stored_child_ids)
  match table.ids.get(key) {
    Some(id) => Some((table.terms[id], id))
    None => {
      let rebuilt = dterm_rebuild(shell, child_terms)
      let id = table.terms.length()
      table.terms.push(rebuilt)
      table.node_children.push(stored_child_ids)
      table.ids.set(key, id)
      Some((rebuilt, id))
    }
  }
}

///|
/// Intern `t`, returning the shared representative and its id.
/// The representative is structurally equal to `t`; equal subterms
/// anywhere (in this or later calls with the same table) receive
/// the same id and the same stored representative.
pub fn dterm_intern_id(table : DTermInternTable, t : DTerm) -> (DTerm, Int32) {
  let children = dterm_children(t)
  let interned_children : Array[DTerm] = []
  let child_ids : Array[Int32] = []
  for i in 0..<children.length() {
    let (child, child_id) = dterm_intern_id(table, children[i])
    interned_children.push(child)
    child_ids.push(child_id)
  }
  let key = dterm_intern_key(t, child_ids)
  match table.ids.get(key) {
    Some(id) => (table.terms[id], id)
    None => {
      let rebuilt = dterm_rebuild(t, interned_children)
      let id = table.terms.length()
      table.terms.push(rebuilt)
      table.node_children.push(child_ids)
      table.ids.set(key, id)
      (rebuilt, id)
    }
  }
}

///|
pub fn dterm_intern(table : DTermInternTable, t : DTerm) -> DTerm {
  dterm_intern_id(table, t).0
}

///|
/// Intern every term, reusing `table`.
pub fn dterm_intern_all(
  table : DTermInternTable,
  ts : Array[DTerm],
) -> Array[DTerm] {
  let out : Array[DTerm] = []
  for i in 0..<ts.length() {
    out.push(dterm_intern(table, ts[i]))
  }
  out
}

///|
/// Number of nodes in the unshared tree.
pub fn dterm_tree_node_count(t : DTerm) -> Int32 {
  let children = dterm_children(t)
  let mut total = 1
  for i in 0..<children.length() {
    total = total + dterm_tree_node_count(children[i])
  }
  total
}

///|
/// Number of structurally distinct subterms (the hash-consed DAG
/// size).  Uses a fresh table.
pub fn dterm_distinct_subterm_count(t : DTerm) -> Int32 {
  let table = dterm_intern_table_new()
  ignore(dterm_intern(table, t))
  dterm_intern_table_size(table)
}

///|
/// The sharing ratio `distinct / tree` as an exact rational pair
/// reduced by gcd: `(distinct/g, tree/g)`.
pub fn dterm_sharing_ratio(t : DTerm) -> (Int32, Int32) {
  let distinct = dterm_distinct_subterm_count(t)
  let tree = dterm_tree_node_count(t)
  let g = int_gcd_nonnegative(distinct, tree)
  if g <= 0 {
    (distinct, tree)
  } else {
    (distinct / g, tree / g)
  }
}

///|
fn int_gcd_nonnegative(a : Int32, b : Int32) -> Int32 {
  let mut x = if a < 0 { 0 - a } else { a }
  let mut y = if b < 0 { 0 - b } else { b }
  while y != 0 {
    let r = x % y
    x = y
    y = r
  }
  x
}

///|
/// One node of a persistent `DTerm` DAG: a local shell (children
/// replaced by positional marker variables) and the snapshot-local
/// intern ids of its children, in `dterm_children` order.
pub struct DTermDagNode {
  shell : DTerm
  children : Array[Int32]
} derive(Debug, Eq)

///|
pub extend DTermDagNode with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend DTermDagNode with Eq::{not_equal, equal}

///|
/// A finite, topologically ordered DAG of interned `DTerm` nodes
/// plus root ids.  Node ids are positions in `nodes`; every child
/// id is smaller than its parent's id.  This is both the exported
/// form of an intern table's reachable graph and the value carried
/// by the `CHDAGBIN` byte codec.
pub struct DTermDagSnapshot {
  nodes : Array[DTermDagNode]
  roots : Array[Int32]
} derive(Debug, Eq)

///|
pub extend DTermDagSnapshot with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend DTermDagSnapshot with Eq::{not_equal, equal}

///|
/// The result of importing a DAG snapshot into an intern table:
/// the destination id of every source node and root, and how many
/// source nodes were newly added versus deduplicated against nodes
/// already present in the destination table.
pub struct DTermDagImportReport {
  node_ids : Array[Int32]
  root_ids : Array[Int32]
  added_nodes : Int32
  reused_nodes : Int32
} derive(Debug, Eq)

///|
pub extend DTermDagImportReport with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend DTermDagImportReport with Eq::{not_equal, equal}

///|
fn dterm_dag_snapshot_of_old_ids(
  table : DTermInternTable,
  root_ids : Array[Int32],
  all_nodes : Bool,
) -> DTermDagSnapshot {
  let total = table.terms.length()
  let reachable : Array[Bool] = []
  for _ in 0..<total {
    reachable.push(false)
  }
  if all_nodes {
    for i in 0..<total {
      reachable[i] = true
    }
  } else {
    let stack : Array[Int32] = []
    for i in 0..<root_ids.length() {
      stack.push(root_ids[i])
    }
    while stack.length() > 0 {
      let id = stack[stack.length() - 1]
      ignore(stack.remove(stack.length() - 1))
      if id >= 0 && id < total && !reachable[id] {
        reachable[id] = true
        for i in 0..<table.node_children[id].length() {
          stack.push(table.node_children[id][i])
        }
      }
    }
  }
  let remap : Array[Int32] = []
  for _ in 0..<total {
    remap.push(-1)
  }
  let mut next_id = 0
  for old_id in 0..<total {
    if reachable[old_id] {
      remap[old_id] = next_id
      next_id = next_id + 1
    }
  }
  let nodes : Array[DTermDagNode] = []
  for old_id in 0..<total {
    if reachable[old_id] {
      let children : Array[Int32] = []
      for i in 0..<table.node_children[old_id].length() {
        children.push(remap[table.node_children[old_id][i]])
      }
      nodes.push(DTermDagNode::{
        shell: dterm_local_shell(table.terms[old_id]),
        children,
      })
    }
  }
  let roots : Array[Int32] = []
  if all_nodes {
    // Every node is retained by position; roots are the whole
    // final frontier in old-id order (equivalently, every node).
    for old_id in 0..<total {
      roots.push(remap[old_id])
    }
  } else {
    for i in 0..<root_ids.length() {
      let old_id = root_ids[i]
      if old_id >= 0 && old_id < total {
        roots.push(remap[old_id])
      }
    }
  }
  { nodes, roots, }
}

///|
/// Export the reachable DAG of `roots` from `table`, interning
/// the roots first.  Only nodes reachable from the roots are
/// retained; ids are compacted in the table's existing (bottom-up)
/// order, so children precede parents.
pub fn dterm_dag_snapshot(
  table : DTermInternTable,
  roots : Array[DTerm],
) -> DTermDagSnapshot {
  let root_ids : Array[Int32] = []
  for i in 0..<roots.length() {
    let (_, id) = dterm_intern_id(table, roots[i])
    root_ids.push(id)
  }
  dterm_dag_snapshot_of_old_ids(table, root_ids, false)
}

///|
/// Export the whole intern table as a DAG snapshot.  The roots
/// list contains every node id, in table order, so importing the
/// snapshot reports a destination id for every source node.
pub fn dterm_intern_table_snapshot(
  table : DTermInternTable,
) -> DTermDagSnapshot {
  dterm_dag_snapshot_of_old_ids(table, [], true)
}

///|
/// Structural validation of a DAG snapshot: node arity agrees
/// with the shell, shell children are exactly the positional
/// markers, every child edge points to an earlier node, and every
/// root is in range.  Import runs this check before touching the
/// destination table.
pub fn dterm_dag_snapshot_validate(snapshot : DTermDagSnapshot) -> Bool {
  for i in 0..<snapshot.nodes.length() {
    let node = snapshot.nodes[i]
    let shell_children = dterm_children(node.shell)
    if shell_children.length() != node.children.length() {
      return false
    }
    for j in 0..<node.children.length() {
      let child = node.children[j]
      if child < 0 || child >= i {
        return false
      }
      if shell_children[j] != DTVar(1000000 + j) {
        return false
      }
    }
  }
  for i in 0..<snapshot.roots.length() {
    let root = snapshot.roots[i]
    if root < 0 || root >= snapshot.nodes.length() {
      return false
    }
  }
  true
}

///|
/// Import a validated DAG snapshot into `table`, node by node.
/// Nodes already present (by local shell and destination child
/// ids) are reused rather than duplicated, so importing the same
/// snapshot twice is an identity on the table after the first
/// import.  A structurally invalid snapshot is rejected before
/// the destination is modified.
pub fn dterm_dag_import(
  table : DTermInternTable,
  snapshot : DTermDagSnapshot,
) -> DTermDagImportReport? {
  if !dterm_dag_snapshot_validate(snapshot) {
    return None
  }
  let node_ids : Array[Int32] = []
  let mut added_nodes = 0
  let mut reused_nodes = 0
  for i in 0..<snapshot.nodes.length() {
    let node = snapshot.nodes[i]
    let child_ids : Array[Int32] = []
    for j in 0..<node.children.length() {
      child_ids.push(node_ids[node.children[j]])
    }
    let before = table.terms.length()
    let (_, id) = match dterm_intern_node(table, node.shell, child_ids) {
      Some(pair) => pair
      None => return None
    }
    if table.terms.length() > before {
      added_nodes = added_nodes + 1
    } else {
      reused_nodes = reused_nodes + 1
    }
    node_ids.push(id)
  }
  let root_ids : Array[Int32] = []
  for i in 0..<snapshot.roots.length() {
    root_ids.push(node_ids[snapshot.roots[i]])
  }
  Some({ node_ids, root_ids, added_nodes, reused_nodes, })
}
