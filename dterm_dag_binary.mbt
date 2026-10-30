///|
// Persistent binary form of the in-process `DTerm` intern DAG.
//
// Format (all integers little-endian, one byte 0--255 per
// `Array[Int32]` element):
//
//   bytes  0..8   magic `CHDAGBIN`
//          8..10  format version (u16; version 1)
//         10..12  reserved, must be 0
//         12..16  payload length (i32)
//         16..20  DJB2-xor checksum of the payload
//         20..    payload: node count; for each node its local
//                 shell in the bare (back-reference-free) term
//                 codec, then the child count and child node
//                 ids; finally the root count and root ids.
//
// The payload is a serialization of `DTermDagSnapshot` itself:
// sharing is represented by the same child-id edges used by
// `DTermInternTable`, not by a second byte-level sharing scheme.
// Importing decoded bytes into an intern table therefore reuses
// the destination table's existing nodes whenever the shell and
// destination child ids already occur there.

///|
pub struct DTermDagBinaryLoad {
  status : ModuleBinaryStatus
  snapshot : DTermDagSnapshot?
} derive(Debug, Eq)

///|
pub extend DTermDagBinaryLoad with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend DTermDagBinaryLoad with Eq::{not_equal, equal}

///|
/// The `CHDAGBIN` layout version written by this build.
pub fn dterm_dag_binary_format_version() -> Int32 {
  1
}

///|
/// All `CHDAGBIN` layout versions this loader can read.
pub fn dterm_dag_binary_supported_versions() -> Array[Int32] {
  [1]
}

///|
pub fn dterm_dag_binary_version_policy() -> BinaryVersionPolicy {
  BinaryVersionPolicy::{
    current: dterm_dag_binary_format_version(),
    supported: dterm_dag_binary_supported_versions(),
    oldest_writable: 1,
  }
}

///|
fn dterm_dag_binary_magic() -> Array[Int32] {
  [67, 72, 68, 65, 71, 66, 73, 78]
}

///|
/// The layout version declared by a blob's header, or -1 when the
/// header is too short or its magic disagrees.
pub fn dterm_dag_binary_version_of(bytes : Array[Int32]) -> Int32 {
  if bytes.length() < 10 {
    return -1
  }
  let magic = dterm_dag_binary_magic()
  for i in 0..<8 {
    if bytes[i] != magic[i] {
      return -1
    }
  }
  module_binary_u16_at(bytes, 8)
}

///|
fn bw_dterm_dag_payload(
  w : ModuleBinWriter,
  snapshot : DTermDagSnapshot,
) -> Unit {
  bw_i32(w, snapshot.nodes.length())
  for i in 0..<snapshot.nodes.length() {
    let node = snapshot.nodes[i]
    bw_term(w, node.shell)
    bw_i32(w, node.children.length())
    for j in 0..<node.children.length() {
      bw_i32(w, node.children[j])
    }
  }
  bw_i32(w, snapshot.roots.length())
  for i in 0..<snapshot.roots.length() {
    bw_i32(w, snapshot.roots[i])
  }
}

///|
/// Serialize a DAG snapshot, or `None` when the snapshot is
/// structurally invalid (`dterm_dag_snapshot_validate`).
pub fn dterm_dag_snapshot_to_binary(
  snapshot : DTermDagSnapshot,
) -> Array[Int32]? {
  if !dterm_dag_snapshot_validate(snapshot) {
    return None
  }
  let payload_writer = module_bin_writer_new_bare()
  bw_dterm_dag_payload(payload_writer, snapshot)
  let payload = payload_writer.bytes
  let writer = module_bin_writer_new()
  let magic = dterm_dag_binary_magic()
  for i in 0..<magic.length() {
    bw_u8(writer, magic[i])
  }
  let version = dterm_dag_binary_format_version()
  bw_u8(writer, version)
  bw_u8(writer, version >> 8)
  bw_u8(writer, 0)
  bw_u8(writer, 0)
  bw_i32(writer, payload.length())
  bw_i32(writer, module_binary_checksum(payload))
  for i in 0..<payload.length() {
    bw_u8(writer, payload[i])
  }
  Some(writer.bytes)
}

///|
fn dterm_dag_binary_failure(status : ModuleBinaryStatus) -> DTermDagBinaryLoad {
  { status, snapshot: None, }
}

///|
fn br_dterm_dag_payload(r : ModuleBinReader) -> DTermDagSnapshot? {
  let nodes : Array[DTermDagNode] = []
  let node_count = br_count(r)
  if !br_require_ok(r) {
    return None
  }
  for _ in 0..<node_count {
    let shell = match br_term(r, 0) {
      Some(value) => value
      None => return None
    }
    let child_count = br_count(r)
    if !br_require_ok(r) {
      return None
    }
    let children : Array[Int32] = []
    for _ in 0..<child_count {
      children.push(br_i32(r))
      if !br_require_ok(r) {
        return None
      }
    }
    nodes.push(DTermDagNode::{ shell, children, })
  }
  let roots : Array[Int32] = []
  let root_count = br_count(r)
  if !br_require_ok(r) {
    return None
  }
  for _ in 0..<root_count {
    roots.push(br_i32(r))
    if !br_require_ok(r) {
      return None
    }
  }
  Some({ nodes, roots, })
}

///|
/// Parse `CHDAGBIN` bytes, reporting a precise format status.
/// A payload that parses but is not a valid topologically
/// ordered snapshot is `ModuleBinaryMalformed`.
pub fn dterm_dag_snapshot_load_binary_report(
  bytes : Array[Int32],
) -> DTermDagBinaryLoad {
  for i in 0..<bytes.length() {
    if bytes[i] < 0 || bytes[i] > 255 {
      return dterm_dag_binary_failure(ModuleBinaryMalformed)
    }
  }
  if bytes.length() < 20 {
    return dterm_dag_binary_failure(ModuleBinaryTruncated)
  }
  let magic = dterm_dag_binary_magic()
  for i in 0..<magic.length() {
    if bytes[i] != magic[i] {
      return dterm_dag_binary_failure(ModuleBinaryBadMagic)
    }
  }
  let layout_version = module_binary_u16_at(bytes, 8)
  if !contains_int(dterm_dag_binary_supported_versions(), layout_version) ||
    module_binary_u16_at(bytes, 10) != 0 {
    return dterm_dag_binary_failure(ModuleBinaryUnsupportedVersion)
  }
  let payload_length = module_binary_i32_at(bytes, 12)
  if payload_length < 0 {
    return dterm_dag_binary_failure(ModuleBinaryMalformed)
  }
  if bytes.length() < 20 + payload_length {
    return dterm_dag_binary_failure(ModuleBinaryTruncated)
  }
  if bytes.length() > 20 + payload_length {
    return dterm_dag_binary_failure(ModuleBinaryTrailingBytes)
  }
  let payload : Array[Int32] = []
  for i in 20..<bytes.length() {
    payload.push(bytes[i])
  }
  if module_binary_checksum(payload) != module_binary_i32_at(bytes, 16) {
    return dterm_dag_binary_failure(ModuleBinaryChecksumMismatch)
  }
  let reader = module_bin_reader_new_bare(payload)
  let snapshot = match br_dterm_dag_payload(reader) {
    Some(value) => value
    None => return dterm_dag_binary_failure(reader.status)
  }
  if reader.pos != payload.length() {
    return dterm_dag_binary_failure(ModuleBinaryTrailingBytes)
  }
  if !dterm_dag_snapshot_validate(snapshot) {
    return dterm_dag_binary_failure(ModuleBinaryMalformed)
  }
  { status: ModuleBinaryOk, snapshot: Some(snapshot), }
}

///|
pub fn dterm_dag_snapshot_from_binary(
  bytes : Array[Int32],
) -> DTermDagSnapshot? {
  dterm_dag_snapshot_load_binary_report(bytes).snapshot
}

///|
/// Decode `CHDAGBIN` bytes and import the DAG into `table`,
/// reusing any nodes the table already contains.  This is the
/// point where the byte backend and the in-process interner meet:
/// the imported roots are nodes of `table` itself.
pub fn dterm_dag_import_binary(
  table : DTermInternTable,
  bytes : Array[Int32],
) -> DTermDagImportReport? {
  match dterm_dag_snapshot_from_binary(bytes) {
    Some(snapshot) => dterm_dag_import(table, snapshot)
    None => None
  }
}

// ---------------------------------------------------------------------------
// Phase 14: Incremental DAG delta snapshots (`CHDAGDLT` v1)
// ---------------------------------------------------------------------------

///|
/// Incremental DAG delta over an existing `DTermInternTable` prefix of
/// length `base_node_count`. Nodes in `0 ..< base_node_count` are referenced
/// directly by base id without re-transmitting their shells; `delta_nodes[k]`
/// defines node id `base_node_count + k`.
pub(all) struct DTermDagDelta {
  base_node_count : Int32
  base_digest_a : Int32
  base_digest_b : Int32
  delta_nodes : Array[DTermDagNode]
  roots : Array[Int32]
} derive(Debug, Eq)

///|
pub extend DTermDagDelta with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend DTermDagDelta with Eq::{not_equal, equal}

///|
pub(all) struct DTermDagDeltaBinaryLoad {
  status : ModuleBinaryStatus
  delta : DTermDagDelta?
} derive(Debug, Eq)

///|
pub extend DTermDagDeltaBinaryLoad with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend DTermDagDeltaBinaryLoad with Eq::{not_equal, equal}

///|
fn dterm_dag_delta_magic() -> Array[Int32] {
  // ASCII `CHDAGDLT`
  [67, 72, 68, 65, 71, 68, 76, 84]
}

///|
/// Deterministic 64-bit `(digest_a, digest_b)` stamp of the first `count`
/// nodes of `table` so delta import rejects mismatched or mutated base tables.
pub fn dterm_intern_table_prefix_digest(
  table : DTermInternTable,
  count : Int32,
) -> (Int32, Int32)? {
  if count < 0 || count > table.terms.length() {
    return None
  }
  let w = module_bin_writer_new_bare()
  bw_i32(w, count)
  for i in 0..<count {
    bw_term(w, dterm_local_shell(table.terms[i]))
    let cs = table.node_children[i]
    bw_i32(w, cs.length())
    for j in 0..<cs.length() {
      bw_i32(w, cs[j])
    }
  }
  let mut ha = 5381
  let mut hb = -2128831035
  for i in 0..<w.bytes.length() {
    let b = w.bytes[i] & 255
    ha = (ha * 33) ^ b
    hb = (hb ^ b) * 16777619
  }
  Some((ha, hb))
}

///|
/// Validate structural invariants of a `DTermDagDelta`.
pub fn dterm_dag_delta_validate(delta : DTermDagDelta) -> Bool {
  if delta.base_node_count < 0 {
    return false
  }
  let total = delta.base_node_count + delta.delta_nodes.length()
  for k in 0..<delta.delta_nodes.length() {
    let node_id = delta.base_node_count + k
    let node = delta.delta_nodes[k]
    let shell_cs = dterm_children(node.shell)
    if shell_cs.length() != node.children.length() {
      return false
    }
    for j in 0..<node.children.length() {
      let c = node.children[j]
      if c < 0 || c >= node_id || shell_cs[j] != DTVar(1000000 + j) {
        return false
      }
    }
  }
  for r in delta.roots {
    if r < 0 || r >= total {
      return false
    }
  }
  true
}

///|
/// Compute an incremental `DTermDagDelta` for `roots` relative to the first
/// `base_node_count` entries of `table`. Base nodes (`< base_node_count`) are
/// referenced by id and never re-emitted into `delta_nodes`.
pub fn dterm_dag_delta_compute(
  table : DTermInternTable,
  base_node_count : Int32,
  roots : Array[DTerm],
) -> DTermDagDelta? {
  let (digest_a, digest_b) = match
    dterm_intern_table_prefix_digest(table, base_node_count) {
    Some(p) => p
    None => return None
  }
  let raw_roots : Array[Int32] = []
  for r in roots {
    let (_, id) = dterm_intern_id(table, r)
    raw_roots.push(id)
  }
  let total = table.terms.length()
  let reachable : Array[Bool] = Array::make(total, false)
  let stack : Array[Int32] = []
  for id in raw_roots {
    if id >= base_node_count && !reachable[id] {
      reachable[id] = true
      stack.push(id)
    }
  }
  while stack.length() > 0 {
    let cur = stack.pop().unwrap()
    for c in table.node_children[cur] {
      if c >= base_node_count && !reachable[c] {
        reachable[c] = true
        stack.push(c)
      }
    }
  }
  let remap : Array[Int32] = Array::make(total, -1)
  for i in 0..<base_node_count {
    remap[i] = i
  }
  let delta_nodes : Array[DTermDagNode] = []
  for i in base_node_count..<total {
    if reachable[i] {
      remap[i] = base_node_count + delta_nodes.length()
      let mapped_children : Array[Int32] = []
      for c in table.node_children[i] {
        mapped_children.push(remap[c])
      }
      delta_nodes.push(DTermDagNode::{
        shell: dterm_local_shell(table.terms[i]),
        children: mapped_children,
      })
    }
  }
  let mapped_roots : Array[Int32] = []
  for id in raw_roots {
    mapped_roots.push(remap[id])
  }
  Some(DTermDagDelta::{
    base_node_count,
    base_digest_a: digest_a,
    base_digest_b: digest_b,
    delta_nodes,
    roots: mapped_roots,
  })
}

///|
/// Serialize a validated `DTermDagDelta` in `CHDAGDLT` v1 binary format.
pub fn dterm_dag_delta_to_binary(delta : DTermDagDelta) -> Array[Int32]? {
  if !dterm_dag_delta_validate(delta) {
    return None
  }
  let pw = module_bin_writer_new_bare()
  bw_i32(pw, delta.base_node_count)
  bw_i32(pw, delta.base_digest_a)
  bw_i32(pw, delta.base_digest_b)
  bw_i32(pw, delta.delta_nodes.length())
  for node in delta.delta_nodes {
    bw_term(pw, node.shell)
    bw_i32(pw, node.children.length())
    for c in node.children {
      bw_i32(pw, c)
    }
  }
  bw_i32(pw, delta.roots.length())
  for r in delta.roots {
    bw_i32(pw, r)
  }
  let payload = pw.bytes
  let w = module_bin_writer_new()
  for b in dterm_dag_delta_magic() {
    bw_u8(w, b)
  }
  bw_u8(w, 1)
  bw_u8(w, 0)
  bw_u8(w, 0)
  bw_u8(w, 0)
  bw_i32(w, payload.length())
  bw_i32(w, module_binary_checksum(payload))
  for b in payload {
    bw_u8(w, b)
  }
  Some(w.bytes)
}

///|
/// Parse `CHDAGDLT` v1 bytes with full header, checksum, trailing-byte, and
/// topological validation.
pub fn dterm_dag_delta_load_binary_report(
  bytes : Array[Int32],
) -> DTermDagDeltaBinaryLoad {
  for b in bytes {
    if b < 0 || b > 255 {
      return DTermDagDeltaBinaryLoad::{
        status: ModuleBinaryMalformed,
        delta: None,
      }
    }
  }
  if bytes.length() < 20 {
    return DTermDagDeltaBinaryLoad::{
      status: ModuleBinaryTruncated,
      delta: None,
    }
  }
  let magic = dterm_dag_delta_magic()
  for i in 0..<8 {
    if bytes[i] != magic[i] {
      return DTermDagDeltaBinaryLoad::{
        status: ModuleBinaryBadMagic,
        delta: None,
      }
    }
  }
  if module_binary_u16_at(bytes, 8) != 1 || module_binary_u16_at(bytes, 10) != 0 {
    return DTermDagDeltaBinaryLoad::{
      status: ModuleBinaryUnsupportedVersion,
      delta: None,
    }
  }
  let payload_len = module_binary_i32_at(bytes, 12)
  if payload_len < 0 {
    return DTermDagDeltaBinaryLoad::{
      status: ModuleBinaryMalformed,
      delta: None,
    }
  }
  if bytes.length() < 20 + payload_len {
    return DTermDagDeltaBinaryLoad::{
      status: ModuleBinaryTruncated,
      delta: None,
    }
  }
  if bytes.length() > 20 + payload_len {
    return DTermDagDeltaBinaryLoad::{
      status: ModuleBinaryTrailingBytes,
      delta: None,
    }
  }
  let payload : Array[Int32] = []
  for i in 20..<bytes.length() {
    payload.push(bytes[i])
  }
  if module_binary_checksum(payload) != module_binary_i32_at(bytes, 16) {
    return DTermDagDeltaBinaryLoad::{
      status: ModuleBinaryChecksumMismatch,
      delta: None,
    }
  }
  let r = module_bin_reader_new_bare(payload)
  let base_node_count = br_i32(r)
  let base_digest_a = br_i32(r)
  let base_digest_b = br_i32(r)
  let delta_count = br_count(r)
  if !br_require_ok(r) {
    return DTermDagDeltaBinaryLoad::{ status: r.status, delta: None, }
  }
  let delta_nodes : Array[DTermDagNode] = []
  for _ in 0..<delta_count {
    let shell = match br_term(r, 0) {
      Some(s) => s
      None => return DTermDagDeltaBinaryLoad::{ status: r.status, delta: None, }
    }
    let cc = br_count(r)
    if !br_require_ok(r) {
      return DTermDagDeltaBinaryLoad::{ status: r.status, delta: None, }
    }
    let children : Array[Int32] = []
    for _ in 0..<cc {
      children.push(br_i32(r))
      if !br_require_ok(r) {
        return DTermDagDeltaBinaryLoad::{ status: r.status, delta: None, }
      }
    }
    delta_nodes.push(DTermDagNode::{ shell, children, })
  }
  let root_count = br_count(r)
  if !br_require_ok(r) {
    return DTermDagDeltaBinaryLoad::{ status: r.status, delta: None, }
  }
  let roots : Array[Int32] = []
  for _ in 0..<root_count {
    roots.push(br_i32(r))
    if !br_require_ok(r) {
      return DTermDagDeltaBinaryLoad::{ status: r.status, delta: None, }
    }
  }
  if r.pos != payload.length() {
    return DTermDagDeltaBinaryLoad::{
      status: ModuleBinaryTrailingBytes,
      delta: None,
    }
  }
  let delta = DTermDagDelta::{
    base_node_count,
    base_digest_a,
    base_digest_b,
    delta_nodes,
    roots,
  }
  if !dterm_dag_delta_validate(delta) {
    return DTermDagDeltaBinaryLoad::{
      status: ModuleBinaryMalformed,
      delta: None,
    }
  }
  DTermDagDeltaBinaryLoad::{ status: ModuleBinaryOk, delta: Some(delta), }
}

///|
/// Apply a validated `DTermDagDelta` to `table` after verifying that `table`'s
/// `0 ..< base_node_count` prefix digest matches `(base_digest_a, base_digest_b)`.
pub fn dterm_dag_delta_apply(
  table : DTermInternTable,
  delta : DTermDagDelta,
) -> DTermDagImportReport? {
  if !dterm_dag_delta_validate(delta) {
    return None
  }
  match dterm_intern_table_prefix_digest(table, delta.base_node_count) {
    Some((ha, hb)) =>
      if ha != delta.base_digest_a || hb != delta.base_digest_b {
        return None
      }
    None => return None
  }
  let resolved : Array[Int32] = []
  for i in 0..<delta.base_node_count {
    resolved.push(i)
  }
  let delta_ids : Array[Int32] = []
  let mut added_nodes = 0
  let mut reused_nodes = 0
  for node in delta.delta_nodes {
    let cs : Array[Int32] = []
    for c in node.children {
      cs.push(resolved[c])
    }
    let before = table.terms.length()
    let (_, id) = match dterm_intern_node(table, node.shell, cs) {
      Some(p) => p
      None => return None
    }
    if table.terms.length() > before {
      added_nodes = added_nodes + 1
    } else {
      reused_nodes = reused_nodes + 1
    }
    resolved.push(id)
    delta_ids.push(id)
  }
  let root_ids : Array[Int32] = []
  for r in delta.roots {
    root_ids.push(resolved[r])
  }
  Some(DTermDagImportReport::{
    node_ids: delta_ids,
    root_ids,
    added_nodes,
    reused_nodes,
  })
}

///|
/// Decode `CHDAGDLT` v1 bytes and import the incremental delta into `table`.
pub fn dterm_dag_delta_import_binary(
  table : DTermInternTable,
  bytes : Array[Int32],
) -> DTermDagImportReport? {
  match dterm_dag_delta_load_binary_report(bytes).delta {
    Some(delta) => dterm_dag_delta_apply(table, delta)
    None => None
  }
}
