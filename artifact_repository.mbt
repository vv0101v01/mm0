// ==================================================================
// Durable artifact repository over an abstract byte store.
//
// The compiled-module and schema-registry binary formats produce
// self-checking byte blobs; this file gives them a storage
// policy that can outlive a process.  MoonBit core (as used by
// this project) exposes no importable filesystem package, so the
// repository is written against an abstract byte-store interface
// (`ArtifactByteStore`: read/write/remove/list callbacks over
// string keys).  An in-memory implementation is provided; a host
// embedding can back the same interface with real files.  The
// repository protocol itself — content addressing, verified
// two-phase writes, commit manifests, an index, and recovery by
// rescanning commit manifests — is fully implemented and
// checked here, and depends only on the store honouring "a
// completed write is durable".
//
// Layout under the repository prefix:
//   <prefix>/index.bin                  CHARTIDX envelope
//   <prefix>/chain.bin                  CHARTCHN integrity chain
//   <prefix>/blobs/<digest>.bin        artifact bytes
//   <prefix>/blobs/<digest>.bin.commit CHARTCOM manifest
// A blob becomes visible only when its commit manifest exists;
// the index is a cache of the manifests and can always be
// rebuilt by `artifact_repository_recover`.
// ==================================================================

///|
/// Abstract byte store: the storage backend the repository
/// protocol runs over.  `write` reports whether the bytes were
/// durably accepted; `list` enumerates all keys.
pub struct ArtifactByteStore {
  read : (String) -> Array[Int32]?
  write : (String, Array[Int32]) -> Bool
  remove : (String) -> Bool
  list : () -> Array[String]
}

///|
pub fn artifact_byte_store_new(
  read~ : (String) -> Array[Int32]?,
  write~ : (String, Array[Int32]) -> Bool,
  remove~ : (String) -> Bool,
  list~ : () -> Array[String],
) -> ArtifactByteStore {
  ArtifactByteStore::{ read, write, remove, list, }
}

///|
/// In-memory byte store, for tests and same-process use.  Bytes
/// are copied on write and on read, so callers cannot mutate
/// stored content behind the repository's back.
pub fn artifact_memory_byte_store_new() -> ArtifactByteStore {
  let entries : Array[(String, Array[Int32])] = []
  let copy = (bytes : Array[Int32]) => {
    let out : Array[Int32] = []
    for i in 0..<bytes.length() {
      out.push(bytes[i])
    }
    out
  }
  artifact_byte_store_new(
    read=key => {
      for i in 0..<entries.length() {
        if entries[i].0 == key {
          return Some(copy(entries[i].1))
        }
      }
      None
    },
    write=(key, bytes) => {
      for i in 0..<entries.length() {
        if entries[i].0 == key {
          entries[i] = (key, copy(bytes))
          return true
        }
      }
      entries.push((key, copy(bytes)))
      true
    },
    remove=key => {
      for i in 0..<entries.length() {
        if entries[i].0 == key {
          ignore(entries.remove(i))
          return true
        }
      }
      false
    },
    list=() => {
      let out : Array[String] = []
      for i in 0..<entries.length() {
        out.push(entries[i].0)
      }
      out
    },
  )
}

///|
/// One committed artifact: its logical identity (`kind`, `name`)
/// and the content-addressed blob holding its bytes, with the
/// length and dual checksums recorded in the commit manifest.
pub struct ArtifactRecord {
  kind : String
  name : String
  blob_key : String
  byte_length : Int32
  hash_a : Int32
  hash_b : Int32
  format_version : Int32
} derive(Debug, Eq)

///|
pub extend ArtifactRecord with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend ArtifactRecord with Eq::{not_equal, equal}

///|
pub struct ArtifactRepository {
  store : ArtifactByteStore
  prefix : String
  mut puts : Int32
  mut recoveries : Int32
}

///|
pub fn artifact_repository_new(
  store : ArtifactByteStore,
  prefix~ : String = "artifacts",
) -> ArtifactRepository {
  ArtifactRepository::{ store, prefix, puts: 0, recoveries: 0, }
}

///|
pub struct ArtifactRepositoryStats {
  records : Int32
  total_bytes : Int32
  puts : Int32
  recoveries : Int32
} derive(Debug, Eq)

///|
pub extend ArtifactRepositoryStats with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend ArtifactRepositoryStats with Eq::{not_equal, equal}

// ------------------------------------------------------------------
// Digests and small helpers
// ------------------------------------------------------------------

///|
fn artifact_hash_pair(bytes : Array[Int32]) -> (Int32, Int32) {
  let mut a = 17
  let mut b = 29
  for i in 0..<bytes.length() {
    let byte = bytes[i] & 255
    a = (a * 31 + byte + 1) % 1000000007
    b = (b * 131 + byte + 7) % 998244353
  }
  (a, b)
}

///|
fn artifact_blob_digest(bytes : Array[Int32]) -> String {
  let (a, b) = artifact_hash_pair(bytes)
  "\{bytes.length()}-\{a}-\{b}"
}

///|
fn artifact_name_ok(name : String) -> Bool {
  if name.length() == 0 {
    return false
  }
  for c in name {
    if c == '/' || c == '\\' {
      return false
    }
  }
  true
}

///|
fn artifact_index_key(repo : ArtifactRepository) -> String {
  repo.prefix + "/index.bin"
}

///|
fn artifact_blob_key(repo : ArtifactRepository, digest : String) -> String {
  repo.prefix + "/blobs/" + digest + ".bin"
}

///|
/// Two-phase verified write: stage at `<key>.tmp`, read back and
/// compare, then write the final key and verify again.  A crash
/// between phases leaves at most a harmless staging key.
fn artifact_store_write_verified(
  store : ArtifactByteStore,
  key : String,
  bytes : Array[Int32],
) -> Bool {
  let staging = key + ".tmp"
  if !(store.write)(staging, bytes) {
    return false
  }
  match (store.read)(staging) {
    Some(back) => if back != bytes { return false }
    None => return false
  }
  if !(store.write)(key, bytes) {
    return false
  }
  match (store.read)(key) {
    Some(back) => if back != bytes { return false }
    None => return false
  }
  ignore((store.remove)(staging))
  true
}

// ------------------------------------------------------------------
// Envelopes (CHARTCOM manifests and the CHARTIDX index)
// ------------------------------------------------------------------

///|
fn artifact_envelope(
  magic : Array[Int32],
  payload : Array[Int32],
) -> Array[Int32] {
  let writer = module_bin_writer_new()
  for i in 0..<magic.length() {
    bw_u8(writer, magic[i])
  }
  bw_u8(writer, 1)
  bw_u8(writer, 0)
  bw_u8(writer, 0)
  bw_u8(writer, 0)
  bw_i32(writer, payload.length())
  bw_i32(writer, module_binary_checksum(payload))
  for i in 0..<payload.length() {
    bw_u8(writer, payload[i])
  }
  writer.bytes
}

///|
fn artifact_envelope_payload(
  magic : Array[Int32],
  bytes : Array[Int32],
) -> Array[Int32]? {
  if bytes.length() < 20 {
    return None
  }
  for i in 0..<bytes.length() {
    if bytes[i] < 0 || bytes[i] > 255 {
      return None
    }
  }
  for i in 0..<8 {
    if bytes[i] != magic[i] {
      return None
    }
  }
  if module_binary_u16_at(bytes, 8) != 1 || module_binary_u16_at(bytes, 10) != 0 {
    return None
  }
  let payload_length = module_binary_i32_at(bytes, 12)
  if payload_length < 0 || bytes.length() != 20 + payload_length {
    return None
  }
  let payload : Array[Int32] = []
  for i in 0..<payload_length {
    payload.push(bytes[20 + i])
  }
  if module_binary_checksum(payload) != module_binary_i32_at(bytes, 16) {
    return None
  }
  Some(payload)
}

///|
fn bw_artifact_record(w : ModuleBinWriter, record : ArtifactRecord) -> Unit {
  bw_string(w, record.kind)
  bw_string(w, record.name)
  bw_string(w, record.blob_key)
  bw_i32(w, record.byte_length)
  bw_i32(w, record.hash_a)
  bw_i32(w, record.hash_b)
  bw_i32(w, record.format_version)
}

///|
fn br_artifact_record(r : ModuleBinReader) -> ArtifactRecord? {
  let kind = match br_string(r) {
    Some(v) => v
    None => return None
  }
  let name = match br_string(r) {
    Some(v) => v
    None => return None
  }
  let blob_key = match br_string(r) {
    Some(v) => v
    None => return None
  }
  let byte_length = br_i32(r)
  let hash_a = br_i32(r)
  let hash_b = br_i32(r)
  let format_version = br_i32(r)
  if !br_require_ok(r) || byte_length < 0 {
    return None
  }
  Some(ArtifactRecord::{
    kind,
    name,
    blob_key,
    byte_length,
    hash_a,
    hash_b,
    format_version,
  })
}

///|
fn artifact_manifest_bytes(record : ArtifactRecord) -> Array[Int32] {
  let writer = module_bin_writer_new_versioned(3)
  bw_artifact_record(writer, record)
  artifact_envelope([67, 72, 65, 82, 84, 67, 79, 77], writer.bytes)
}

///|
fn artifact_manifest_parse(bytes : Array[Int32]) -> ArtifactRecord? {
  let payload = match
    artifact_envelope_payload([67, 72, 65, 82, 84, 67, 79, 77], bytes) {
    Some(v) => v
    None => return None
  }
  let reader = module_bin_reader_new_versioned(payload, 3)
  let record = br_artifact_record(reader)
  if reader.pos != payload.length() || reader.status != ModuleBinaryOk {
    return None
  }
  record
}

///|
fn artifact_index_bytes(records : Array[ArtifactRecord]) -> Array[Int32] {
  let writer = module_bin_writer_new_versioned(3)
  bw_i32(writer, records.length())
  for i in 0..<records.length() {
    bw_artifact_record(writer, records[i])
  }
  artifact_envelope([67, 72, 65, 82, 84, 73, 68, 88], writer.bytes)
}

///|
fn artifact_index_parse(bytes : Array[Int32]) -> Array[ArtifactRecord]? {
  let payload = match
    artifact_envelope_payload([67, 72, 65, 82, 84, 73, 68, 88], bytes) {
    Some(v) => v
    None => return None
  }
  let reader = module_bin_reader_new_versioned(payload, 3)
  let count = br_count(reader)
  if !br_require_ok(reader) {
    return None
  }
  let records : Array[ArtifactRecord] = []
  for _i in 0..<count {
    match br_artifact_record(reader) {
      Some(v) => records.push(v)
      None => return None
    }
  }
  if reader.pos != payload.length() || reader.status != ModuleBinaryOk {
    return None
  }
  Some(records)
}

// ------------------------------------------------------------------
// Index handling
// ------------------------------------------------------------------

///|
/// Load the index; a missing index is the empty repository, a
/// corrupt one is reported as `None` (run recovery).
fn artifact_repository_load_index(
  repo : ArtifactRepository,
) -> Array[ArtifactRecord]? {
  match (repo.store.read)(artifact_index_key(repo)) {
    Some(bytes) => artifact_index_parse(bytes)
    None => Some([])
  }
}

///|
fn artifact_repository_save_index(
  repo : ArtifactRepository,
  records : Array[ArtifactRecord],
) -> Bool {
  artifact_store_write_verified(
    repo.store,
    artifact_index_key(repo),
    artifact_index_bytes(records),
  )
}

///|
fn artifact_records_find(
  records : Array[ArtifactRecord],
  kind : String,
  name : String,
) -> ArtifactRecord? {
  for i in 0..<records.length() {
    if records[i].kind == kind && records[i].name == name {
      return Some(records[i])
    }
  }
  None
}

///|
fn artifact_record_matches_bytes(
  record : ArtifactRecord,
  bytes : Array[Int32],
) -> Bool {
  let (a, b) = artifact_hash_pair(bytes)
  record.byte_length == bytes.length() &&
  record.hash_a == a &&
  record.hash_b == b
}

// ------------------------------------------------------------------
// Repository operations
// ------------------------------------------------------------------

///|
/// Commit `bytes` as the artifact `(kind, name)`.  The bytes are
/// content-addressed: re-putting identical content reuses the
/// existing blob.  The write is committed by its manifest before
/// the index is updated, so an interrupted put is invisible and
/// recoverable.  Returns the committed record.
pub fn artifact_repository_put(
  repo : ArtifactRepository,
  kind : String,
  name : String,
  bytes : Array[Int32],
  format_version~ : Int32 = -1,
) -> ArtifactRecord? {
  if !artifact_name_ok(kind) || !artifact_name_ok(name) {
    return None
  }
  for i in 0..<bytes.length() {
    if bytes[i] < 0 || bytes[i] > 255 {
      return None
    }
  }
  let (hash_a, hash_b) = artifact_hash_pair(bytes)
  let base_digest = artifact_blob_digest(bytes)
  let mut suffix = 0
  let mut blob_key = ""
  let mut blob_found = false
  while !blob_found {
    if suffix > 1024 {
      return None
    }
    let digest = if suffix == 0 {
      base_digest
    } else {
      base_digest + "-x" + suffix.to_string()
    }
    let candidate = artifact_blob_key(repo, digest)
    match (repo.store.read)(candidate + ".commit") {
      Some(manifest) =>
        match artifact_manifest_parse(manifest) {
          Some(existing) =>
            if artifact_record_matches_bytes(existing, bytes) {
              blob_key = candidate
              blob_found = true
            } else {
              suffix = suffix + 1
            }
          None => suffix = suffix + 1
        }
      None => {
        blob_key = candidate
        blob_found = true
      }
    }
  }
  let record = ArtifactRecord::{
    kind,
    name,
    blob_key,
    byte_length: bytes.length(),
    hash_a,
    hash_b,
    format_version,
  }
  match (repo.store.read)(blob_key) {
    Some(existing) =>
      if existing != bytes {
        if !artifact_store_write_verified(repo.store, blob_key, bytes) {
          return None
        }
      }
    None =>
      if !artifact_store_write_verified(repo.store, blob_key, bytes) {
        return None
      }
  }
  if !artifact_store_write_verified(
      repo.store,
      blob_key + ".commit",
      artifact_manifest_bytes(record),
    ) {
    return None
  }
  let records = match artifact_repository_load_index(repo) {
    Some(v) => v
    None => return None
  }
  if !artifact_chain_append(repo, records, false, record) {
    return None
  }
  let kept : Array[ArtifactRecord] = []
  for i in 0..<records.length() {
    if !(records[i].kind == kind && records[i].name == name) {
      kept.push(records[i])
    }
  }
  kept.push(record)
  if !artifact_repository_save_index(repo, kept) {
    return None
  }
  repo.puts = repo.puts + 1
  Some(record)
}

///|
/// Fetch and fully verify an artifact: the commit manifest must
/// agree with the index, and the blob must match the recorded
/// length and both checksums.
pub fn artifact_repository_get(
  repo : ArtifactRepository,
  kind : String,
  name : String,
) -> Array[Int32]? {
  let records = match artifact_repository_load_index(repo) {
    Some(v) => v
    None => return None
  }
  let record = match artifact_records_find(records, kind, name) {
    Some(v) => v
    None => return None
  }
  let manifest = match (repo.store.read)(record.blob_key + ".commit") {
    Some(bytes) =>
      match artifact_manifest_parse(bytes) {
        Some(v) => v
        None => return None
      }
    None => return None
  }
  if manifest.blob_key != record.blob_key ||
    manifest.byte_length != record.byte_length ||
    manifest.hash_a != record.hash_a ||
    manifest.hash_b != record.hash_b {
    return None
  }
  let bytes = match (repo.store.read)(record.blob_key) {
    Some(v) => v
    None => return None
  }
  if !artifact_record_matches_bytes(record, bytes) {
    return None
  }
  Some(bytes)
}

///|
pub fn artifact_repository_record(
  repo : ArtifactRepository,
  kind : String,
  name : String,
) -> ArtifactRecord? {
  match artifact_repository_load_index(repo) {
    Some(records) => artifact_records_find(records, kind, name)
    None => None
  }
}

///|
pub fn artifact_repository_list(
  repo : ArtifactRepository,
) -> Array[ArtifactRecord] {
  match artifact_repository_load_index(repo) {
    Some(records) => records
    None => []
  }
}

///|
/// Remove an artifact from the index; its blob and manifest are
/// deleted when no remaining record references the same blob.
pub fn artifact_repository_remove(
  repo : ArtifactRepository,
  kind : String,
  name : String,
) -> Bool {
  let records = match artifact_repository_load_index(repo) {
    Some(v) => v
    None => return false
  }
  let record = match artifact_records_find(records, kind, name) {
    Some(v) => v
    None => return false
  }
  if !artifact_chain_append(repo, records, true, record) {
    return false
  }
  let kept : Array[ArtifactRecord] = []
  for i in 0..<records.length() {
    if !(records[i].kind == kind && records[i].name == name) {
      kept.push(records[i])
    }
  }
  if !artifact_repository_save_index(repo, kept) {
    return false
  }
  let mut referenced = false
  for i in 0..<kept.length() {
    if kept[i].blob_key == record.blob_key {
      referenced = true
    }
  }
  if !referenced {
    ignore((repo.store.remove)(record.blob_key))
    ignore((repo.store.remove)(record.blob_key + ".commit"))
  }
  true
}

///|
/// Rebuild the index from the commit manifests present in the
/// store, keeping only manifests whose blobs verify.  This is
/// the corruption-recovery path for a lost or damaged index.
/// Returns the number of recovered records, or -1 when the
/// rebuilt index could not be saved.
pub fn artifact_repository_recover(repo : ArtifactRepository) -> Int32 {
  let blob_prefix = repo.prefix + "/blobs/"
  let keys = (repo.store.list)()
  let records : Array[ArtifactRecord] = []
  for i in 0..<keys.length() {
    let key = keys[i]
    if key.has_prefix(blob_prefix) && key.has_suffix(".commit") {
      match (repo.store.read)(key) {
        Some(manifest_bytes) =>
          match artifact_manifest_parse(manifest_bytes) {
            Some(record) =>
              match (repo.store.read)(record.blob_key) {
                Some(bytes) =>
                  if artifact_record_matches_bytes(record, bytes) &&
                    artifact_records_find(records, record.kind, record.name) ==
                    None {
                    records.push(record)
                  }
                None => ()
              }
            None => ()
          }
        None => ()
      }
    }
  }
  // Deterministic order, independent of store enumeration.
  for i in 0..<records.length() {
    for j in (i + 1)..<records.length() {
      let a = records[i]
      let b = records[j]
      if b.kind + "/" + b.name < a.kind + "/" + a.name {
        records[i] = b
        records[j] = a
      }
    }
  }
  if !artifact_repository_save_index(repo, records) {
    return -1
  }
  repo.recoveries = repo.recoveries + 1
  records.length()
}

///|
/// Every indexed artifact reads back and verifies.
pub fn artifact_repository_verify_all(repo : ArtifactRepository) -> Bool {
  let records = artifact_repository_list(repo)
  for i in 0..<records.length() {
    if artifact_repository_get(repo, records[i].kind, records[i].name) == None {
      return false
    }
  }
  true
}

///|
pub fn artifact_repository_stats(
  repo : ArtifactRepository,
) -> ArtifactRepositoryStats {
  let records = artifact_repository_list(repo)
  let mut total = 0
  for i in 0..<records.length() {
    total = total + records[i].byte_length
  }
  ArtifactRepositoryStats::{
    records: records.length(),
    total_bytes: total,
    puts: repo.puts,
    recoveries: repo.recoveries,
  }
}

// ------------------------------------------------------------------
// Typed wrappers: compiled modules and registry snapshots
// ------------------------------------------------------------------

///|
pub fn artifact_kind_compiled_module() -> String {
  "compiled-module"
}

///|
pub fn artifact_kind_schema_registry() -> String {
  "schema-registry"
}

///|
/// Store a compiled module under its module path.  With a
/// non-empty `peer_versions`, the bytes are negotiated down to
/// the highest mutually supported layout that can express the
/// module; otherwise the current layout is used.
pub fn artifact_repository_put_compiled_module(
  repo : ArtifactRepository,
  compiled : CompiledModule,
  peer_versions~ : Array[Int32] = [],
) -> ArtifactRecord? {
  let bytes = if peer_versions.length() == 0 {
    compiled_module_to_binary(compiled)
  } else {
    match compiled_module_to_binary_for_peer(compiled, peer_versions) {
      Some(v) => v
      None => return None
    }
  }
  artifact_repository_put(
    repo,
    artifact_kind_compiled_module(),
    compiled.module_path,
    bytes,
    format_version=compiled_module_binary_version_of(bytes),
  )
}

///|
pub fn artifact_repository_get_compiled_module(
  repo : ArtifactRepository,
  module_path : String,
) -> CompiledModule? {
  let bytes = match
    artifact_repository_get(repo, artifact_kind_compiled_module(), module_path) {
    Some(v) => v
    None => return None
  }
  compiled_module_load_binary(bytes)
}

///|
pub fn artifact_repository_put_registry_snapshot(
  repo : ArtifactRepository,
  name : String,
  snapshot : DSchemaRegistrySnapshot,
  peer_versions~ : Array[Int32] = [],
) -> ArtifactRecord? {
  let bytes = if peer_versions.length() == 0 {
    schema_registry_snapshot_to_binary(snapshot)
  } else {
    match schema_registry_snapshot_to_binary_for_peer(snapshot, peer_versions) {
      Some(v) => v
      None => return None
    }
  }
  artifact_repository_put(
    repo,
    artifact_kind_schema_registry(),
    name,
    bytes,
    format_version=schema_registry_binary_version_of(bytes),
  )
}

///|
pub fn artifact_repository_get_registry_snapshot(
  repo : ArtifactRepository,
  name : String,
) -> DSchemaRegistrySnapshot? {
  let bytes = match
    artifact_repository_get(repo, artifact_kind_schema_registry(), name) {
    Some(v) => v
    None => return None
  }
  schema_registry_snapshot_from_binary(bytes)
}

///|
pub fn artifact_kind_dterm_dag() -> String {
  "dterm-dag"
}

///|
/// Store a persistent interned-DAG snapshot (`CHDAGBIN`).  The
/// stored bytes are the DAG's node shells and child-id edges
/// themselves, so no second byte-level sharing representation is
/// involved.
pub fn artifact_repository_put_dterm_dag_snapshot(
  repo : ArtifactRepository,
  name : String,
  snapshot : DTermDagSnapshot,
) -> ArtifactRecord? {
  let bytes = match dterm_dag_snapshot_to_binary(snapshot) {
    Some(value) => value
    None => return None
  }
  artifact_repository_put(
    repo,
    artifact_kind_dterm_dag(),
    name,
    bytes,
    format_version=dterm_dag_binary_version_of(bytes),
  )
}

///|
/// Intern `roots` into `table` and store their reachable DAG.
/// The table is the same one the caller keeps using in-process:
/// exporting does not rebuild the terms into a separate graph.
pub fn artifact_repository_put_dterm_dag_terms(
  repo : ArtifactRepository,
  name : String,
  table : DTermInternTable,
  roots : Array[DTerm],
) -> ArtifactRecord? {
  artifact_repository_put_dterm_dag_snapshot(
    repo,
    name,
    dterm_dag_snapshot(table, roots),
  )
}

///|
pub fn artifact_repository_get_dterm_dag_snapshot(
  repo : ArtifactRepository,
  name : String,
) -> DTermDagSnapshot? {
  let bytes = match
    artifact_repository_get(repo, artifact_kind_dterm_dag(), name) {
    Some(value) => value
    None => return None
  }
  dterm_dag_snapshot_from_binary(bytes)
}

///|
/// Fetch a DAG artifact and import it directly into `table`.
/// Destination nodes that already exist are reused, so the
/// returned root ids are ids in the caller's live interner.
pub fn artifact_repository_get_dterm_dag_into(
  repo : ArtifactRepository,
  name : String,
  table : DTermInternTable,
) -> DTermDagImportReport? {
  let bytes = match
    artifact_repository_get(repo, artifact_kind_dterm_dag(), name) {
    Some(value) => value
    None => return None
  }
  dterm_dag_import_binary(table, bytes)
}

// ------------------------------------------------------------------
// Phase 13: append-only manifest integrity chain.
//
// Every successful repository mutation appends a sequence entry
// to `<prefix>/chain.bin` before the index is updated.  An entry
// binds its sequence number, put/remove flag and full artifact
// record to the previous entry digest; the first entry binds to
// the genesis digest `(0, 0)`.  Recomputing the chain therefore
// detects edited, deleted, reordered and replayed commit
// records.  The chain head returned by
// `artifact_repository_chain_head` is the caller's external
// trust anchor: passing it back to the report/get/recovery APIs
// detects even a wholesale replacement of the chain file.
// This is an integrity protocol over the repository's existing
// dual checksums, not a cryptographic signature scheme.
// ------------------------------------------------------------------

///|
pub struct ArtifactChainEntry {
  sequence : Int32
  removed : Bool
  record : ArtifactRecord
  previous_a : Int32
  previous_b : Int32
  entry_a : Int32
  entry_b : Int32
} derive(Debug, Eq)

///|
pub extend ArtifactChainEntry with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend ArtifactChainEntry with Eq::{not_equal, equal}

///|
pub struct ArtifactChainReport {
  valid : Bool
  entries : Int32
  live_records : Int32
  head_a : Int32
  head_b : Int32
  covers_index : Bool
} derive(Debug, Eq)

///|
pub extend ArtifactChainReport with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend ArtifactChainReport with Eq::{not_equal, equal}

///|
fn artifact_chain_key(repo : ArtifactRepository) -> String {
  repo.prefix + "/chain.bin"
}

///|
fn artifact_chain_entry_digest(
  sequence : Int32,
  removed : Bool,
  record : ArtifactRecord,
  previous_a : Int32,
  previous_b : Int32,
) -> (Int32, Int32) {
  let writer = module_bin_writer_new_versioned(3)
  bw_i32(writer, sequence)
  bw_bool(writer, removed)
  bw_artifact_record(writer, record)
  bw_i32(writer, previous_a)
  bw_i32(writer, previous_b)
  artifact_hash_pair(writer.bytes)
}

///|
fn bw_artifact_chain_entry(
  w : ModuleBinWriter,
  entry : ArtifactChainEntry,
) -> Unit {
  bw_i32(w, entry.sequence)
  bw_bool(w, entry.removed)
  bw_artifact_record(w, entry.record)
  bw_i32(w, entry.previous_a)
  bw_i32(w, entry.previous_b)
  bw_i32(w, entry.entry_a)
  bw_i32(w, entry.entry_b)
}

///|
fn br_artifact_chain_entry(r : ModuleBinReader) -> ArtifactChainEntry? {
  let sequence = br_i32(r)
  let removed = br_bool(r)
  let record = match br_artifact_record(r) {
    Some(v) => v
    None => return None
  }
  let previous_a = br_i32(r)
  let previous_b = br_i32(r)
  let entry_a = br_i32(r)
  let entry_b = br_i32(r)
  if !br_require_ok(r) || sequence <= 0 {
    return None
  }
  Some(ArtifactChainEntry::{
    sequence,
    removed,
    record,
    previous_a,
    previous_b,
    entry_a,
    entry_b,
  })
}

///|
fn artifact_chain_bytes(entries : Array[ArtifactChainEntry]) -> Array[Int32] {
  let writer = module_bin_writer_new_versioned(3)
  bw_i32(writer, entries.length())
  for i in 0..<entries.length() {
    bw_artifact_chain_entry(writer, entries[i])
  }
  artifact_envelope([67, 72, 65, 82, 84, 67, 72, 78], writer.bytes)
}

///|
fn artifact_chain_parse(bytes : Array[Int32]) -> Array[ArtifactChainEntry]? {
  let payload = match
    artifact_envelope_payload([67, 72, 65, 82, 84, 67, 72, 78], bytes) {
    Some(v) => v
    None => return None
  }
  let reader = module_bin_reader_new_versioned(payload, 3)
  let count = br_count(reader)
  if !br_require_ok(reader) {
    return None
  }
  let entries : Array[ArtifactChainEntry] = []
  for _i in 0..<count {
    match br_artifact_chain_entry(reader) {
      Some(v) => entries.push(v)
      None => return None
    }
  }
  if reader.pos != payload.length() || reader.status != ModuleBinaryOk {
    return None
  }
  Some(entries)
}

///|
/// `(chain file exists, entries)`; `None` means a present chain
/// file is corrupt.
fn artifact_chain_load_state(
  repo : ArtifactRepository,
) -> (Bool, Array[ArtifactChainEntry])? {
  match (repo.store.read)(artifact_chain_key(repo)) {
    Some(bytes) =>
      match artifact_chain_parse(bytes) {
        Some(entries) => Some((true, entries))
        None => None
      }
    None => Some((false, []))
  }
}

///|
fn artifact_chain_save(
  repo : ArtifactRepository,
  entries : Array[ArtifactChainEntry],
) -> Bool {
  artifact_store_write_verified(
    repo.store,
    artifact_chain_key(repo),
    artifact_chain_bytes(entries),
  )
}

///|
fn artifact_chain_links_valid(entries : Array[ArtifactChainEntry]) -> Bool {
  let mut previous_a = 0
  let mut previous_b = 0
  for i in 0..<entries.length() {
    let entry = entries[i]
    if entry.sequence != i + 1 ||
      entry.previous_a != previous_a ||
      entry.previous_b != previous_b ||
      !artifact_name_ok(entry.record.kind) ||
      !artifact_name_ok(entry.record.name) {
      return false
    }
    let (a, b) = artifact_chain_entry_digest(
      entry.sequence,
      entry.removed,
      entry.record,
      entry.previous_a,
      entry.previous_b,
    )
    if a != entry.entry_a || b != entry.entry_b {
      return false
    }
    previous_a = entry.entry_a
    previous_b = entry.entry_b
  }
  true
}

///|
fn artifact_chain_head_of(
  entries : Array[ArtifactChainEntry],
) -> (Int32, Int32) {
  if entries.length() == 0 {
    (0, 0)
  } else {
    let last = entries[entries.length() - 1]
    (last.entry_a, last.entry_b)
  }
}

///|
fn artifact_chain_bootstrap(
  records : Array[ArtifactRecord],
) -> Array[ArtifactChainEntry] {
  let entries : Array[ArtifactChainEntry] = []
  let mut previous_a = 0
  let mut previous_b = 0
  for i in 0..<records.length() {
    let sequence = i + 1
    let (entry_a, entry_b) = artifact_chain_entry_digest(
      sequence,
      false,
      records[i],
      previous_a,
      previous_b,
    )
    entries.push(ArtifactChainEntry::{
      sequence,
      removed: false,
      record: records[i],
      previous_a,
      previous_b,
      entry_a,
      entry_b,
    })
    previous_a = entry_a
    previous_b = entry_b
  }
  entries
}

///|
/// Append one mutation.  A repository with legacy indexed
/// records but no chain entries is migrated by first chaining
/// those records in index order.
fn artifact_chain_append(
  repo : ArtifactRepository,
  records_before : Array[ArtifactRecord],
  removed : Bool,
  record : ArtifactRecord,
) -> Bool {
  let (_, existing) = match artifact_chain_load_state(repo) {
    Some(v) => v
    None => return false
  }
  let entries = if existing.length() == 0 {
    artifact_chain_bootstrap(records_before)
  } else {
    existing
  }
  if !artifact_chain_links_valid(entries) {
    return false
  }
  let (previous_a, previous_b) = artifact_chain_head_of(entries)
  let sequence = entries.length() + 1
  let (entry_a, entry_b) = artifact_chain_entry_digest(
    sequence, removed, record, previous_a, previous_b,
  )
  entries.push(ArtifactChainEntry::{
    sequence,
    removed,
    record,
    previous_a,
    previous_b,
    entry_a,
    entry_b,
  })
  artifact_chain_save(repo, entries)
}

///|
/// The latest live record set obtained by replaying the chain;
/// `None` for a tombstone naming no live record.
fn artifact_chain_live_records(
  entries : Array[ArtifactChainEntry],
) -> Array[ArtifactRecord]? {
  let mut live : Array[ArtifactRecord] = []
  for i in 0..<entries.length() {
    let entry = entries[i]
    let kept : Array[ArtifactRecord] = []
    let mut found = false
    for j in 0..<live.length() {
      if live[j].kind == entry.record.kind && live[j].name == entry.record.name {
        found = true
      } else {
        kept.push(live[j])
      }
    }
    if entry.removed {
      if !found {
        return None
      }
    } else {
      kept.push(entry.record)
    }
    live = kept
  }
  Some(live)
}

///|
fn artifact_chain_contains_record(
  records : Array[ArtifactRecord],
  record : ArtifactRecord,
) -> Bool {
  for i in 0..<records.length() {
    if records[i] == record {
      return true
    }
  }
  false
}

///|
fn artifact_chain_expected_ok(
  head : (Int32, Int32),
  expected_head : (Int32, Int32)?,
) -> Bool {
  match expected_head {
    None => true
    Some((a, b)) => head.0 == a && head.1 == b
  }
}

///|
/// The parsed chain entries, if the chain file exists and
/// parses.  Link validity is reported by
/// `artifact_repository_chain_report`.
pub fn artifact_repository_chain_entries(
  repo : ArtifactRepository,
) -> Array[ArtifactChainEntry]? {
  match artifact_chain_load_state(repo) {
    Some((_, entries)) => Some(entries)
    None => None
  }
}

///|
/// The current integrity-chain head.  Returns `None` when the
/// chain is corrupt or when indexed legacy records exist without
/// any chain commitment.
pub fn artifact_repository_chain_head(
  repo : ArtifactRepository,
) -> (Int32, Int32)? {
  let (exists, entries) = match artifact_chain_load_state(repo) {
    Some(v) => v
    None => return None
  }
  if !artifact_chain_links_valid(entries) {
    return None
  }
  if !exists {
    match artifact_repository_load_index(repo) {
      Some(records) => if records.length() != 0 { return None }
      None => return None
    }
  }
  Some(artifact_chain_head_of(entries))
}

///|
/// Verify the full chain: sequence links and entry digests,
/// replay to the live record set, equality with the index, and
/// readable verified blobs for every live record.  Supplying a
/// previously obtained head additionally anchors the chain
/// against wholesale replacement or replay of an older chain.
pub fn artifact_repository_chain_report(
  repo : ArtifactRepository,
  expected_head~ : (Int32, Int32)? = None,
) -> ArtifactChainReport {
  let invalid = ArtifactChainReport::{
    valid: false,
    entries: 0,
    live_records: 0,
    head_a: 0,
    head_b: 0,
    covers_index: false,
  }
  let (exists, entries) = match artifact_chain_load_state(repo) {
    Some(v) => v
    None => return invalid
  }
  let index = match artifact_repository_load_index(repo) {
    Some(v) => v
    None => return invalid
  }
  let head = artifact_chain_head_of(entries)
  let expected_ok = artifact_chain_expected_ok(head, expected_head)
  if !exists {
    return ArtifactChainReport::{
      valid: index.length() == 0 && expected_ok,
      entries: 0,
      live_records: 0,
      head_a: 0,
      head_b: 0,
      covers_index: index.length() == 0,
    }
  }
  let live = match artifact_chain_live_records(entries) {
    Some(v) => v
    None =>
      return ArtifactChainReport::{
        valid: false,
        entries: entries.length(),
        live_records: 0,
        head_a: head.0,
        head_b: head.1,
        covers_index: false,
      }
  }
  let mut covers = live.length() == index.length()
  for i in 0..<live.length() {
    if !artifact_chain_contains_record(index, live[i]) {
      covers = false
    }
  }
  for i in 0..<index.length() {
    if !artifact_chain_contains_record(live, index[i]) {
      covers = false
    }
  }
  let mut blobs_ok = true
  for i in 0..<live.length() {
    if artifact_repository_get(repo, live[i].kind, live[i].name) == None {
      blobs_ok = false
    }
  }
  ArtifactChainReport::{
    valid: artifact_chain_links_valid(entries) &&
    covers &&
    blobs_ok &&
    expected_ok,
    entries: entries.length(),
    live_records: live.length(),
    head_a: head.0,
    head_b: head.1,
    covers_index: covers,
  }
}

///|
/// Fetch an artifact only when the whole integrity chain (and,
/// when supplied, its expected head) verifies.
pub fn artifact_repository_get_chained(
  repo : ArtifactRepository,
  kind : String,
  name : String,
  expected_head~ : (Int32, Int32)? = None,
) -> Array[Int32]? {
  let report = artifact_repository_chain_report(repo, expected_head~)
  if !report.valid {
    return None
  }
  artifact_repository_get(repo, kind, name)
}

///|
fn artifact_chain_live_blob_ok(
  repo : ArtifactRepository,
  record : ArtifactRecord,
) -> Bool {
  let manifest = match (repo.store.read)(record.blob_key + ".commit") {
    Some(bytes) =>
      match artifact_manifest_parse(bytes) {
        Some(v) => v
        None => return false
      }
    None => return false
  }
  if manifest.blob_key != record.blob_key ||
    manifest.byte_length != record.byte_length ||
    manifest.hash_a != record.hash_a ||
    manifest.hash_b != record.hash_b {
    return false
  }
  match (repo.store.read)(record.blob_key) {
    Some(bytes) => artifact_record_matches_bytes(record, bytes)
    None => false
  }
}

///|
/// Rebuild the index by replaying a verified integrity chain.
/// Unlike manifest scanning, replay respects overwrites and
/// tombstones.  Returns the number of live records, or `-1`
/// when the chain, expected head, a live blob, or the rebuilt
/// index write fails verification.
pub fn artifact_repository_recover_chained(
  repo : ArtifactRepository,
  expected_head~ : (Int32, Int32)? = None,
) -> Int32 {
  let (exists, entries) = match artifact_chain_load_state(repo) {
    Some(v) => v
    None => return -1
  }
  if !exists || !artifact_chain_links_valid(entries) {
    return -1
  }
  let head = artifact_chain_head_of(entries)
  if !artifact_chain_expected_ok(head, expected_head) {
    return -1
  }
  let live = match artifact_chain_live_records(entries) {
    Some(v) => v
    None => return -1
  }
  for i in 0..<live.length() {
    if !artifact_chain_live_blob_ok(repo, live[i]) {
      return -1
    }
  }
  for i in 0..<live.length() {
    for j in (i + 1)..<live.length() {
      let a = live[i]
      let b = live[j]
      if b.kind + "/" + b.name < a.kind + "/" + a.name {
        live[i] = b
        live[j] = a
      }
    }
  }
  if !artifact_repository_save_index(repo, live) {
    return -1
  }
  repo.recoveries = repo.recoveries + 1
  live.length()
}

// ---------------------------------------------------------------------------
// Phase 14: Keyed-MAC authenticated chain, optimistic CAS multi-writer commit,
// and producer-attested incremental artifact sync
// ---------------------------------------------------------------------------

///|
/// Symmetric MAC key authenticating repository integrity chains against an
/// untrusted byte store (`CHARTAUT` v1).
pub(all) struct ArtifactAuthKey {
  key_id : String
  secret_a : Int32
  secret_b : Int32
} derive(Debug, Eq)

///|
pub extend ArtifactAuthKey with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend ArtifactAuthKey with Eq::{not_equal, equal}

///|
pub(all) enum ArtifactCasStatus {
  ArtifactCasCommitted
  ArtifactCasConflict
  ArtifactCasAuthFailed
  ArtifactCasIoError
} derive(Debug, Eq)

///|
pub extend ArtifactCasStatus with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend ArtifactCasStatus with Eq::{not_equal, equal}

///|
pub(all) struct ArtifactSyncReport {
  ok : Bool
  transferred_blobs : Int32
  skipped_existing_blobs : Int32
  tombstones_applied : Int32
  final_head_a : Int32
  final_head_b : Int32
} derive(Debug, Eq)

///|
pub extend ArtifactSyncReport with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend ArtifactSyncReport with Eq::{not_equal, equal}

///|
fn artifact_auth_key_path(repo : ArtifactRepository) -> String {
  repo.prefix + "/chain.auth"
}

///|
fn artifact_auth_magic() -> Array[Int32] {
  // ASCII `CHARTAUT`
  [67, 72, 65, 82, 84, 65, 85, 84]
}

///|
/// Two-stage HMAC-like keyed digest over `(key_id, entries, head_a, head_b)`.
/// Forging `chain.bin` without `(secret_a, secret_b)` invalidates this tag.
fn artifact_chain_keyed_mac(
  key : ArtifactAuthKey,
  entries : Array[ArtifactChainEntry],
) -> (Int32, Int32) {
  let inner = module_bin_writer_new_versioned(3)
  bw_i32(inner, key.secret_a ^ 0x36363636)
  bw_i32(inner, key.secret_b ^ 0x36363636)
  bw_string(inner, key.key_id)
  bw_i32(inner, entries.length())
  for e in entries {
    bw_artifact_chain_entry(inner, e)
  }
  let (ia, ib) = artifact_hash_pair(inner.bytes)
  let outer = module_bin_writer_new_versioned(3)
  bw_i32(outer, key.secret_a ^ 0x5c5c5c5c)
  bw_i32(outer, key.secret_b ^ 0x5c5c5c5c)
  bw_string(outer, key.key_id)
  bw_i32(outer, ia)
  bw_i32(outer, ib)
  artifact_hash_pair(outer.bytes)
}

///|
fn artifact_auth_stamp_write(
  repo : ArtifactRepository,
  key : ArtifactAuthKey,
  entries : Array[ArtifactChainEntry],
) -> Bool {
  let (head_a, head_b) = artifact_chain_head_of(entries)
  let (mac_a, mac_b) = artifact_chain_keyed_mac(key, entries)
  let pw = module_bin_writer_new_versioned(3)
  bw_string(pw, key.key_id)
  bw_i32(pw, entries.length())
  bw_i32(pw, head_a)
  bw_i32(pw, head_b)
  bw_i32(pw, mac_a)
  bw_i32(pw, mac_b)
  let env = artifact_envelope(artifact_auth_magic(), pw.bytes)
  (repo.store.write)(artifact_auth_key_path(repo), env)
}

///|
/// Verify both the repository's hash chain/blobs AND its keyed MAC attestation
/// under `key`.
pub fn artifact_repository_verify_authenticated(
  repo : ArtifactRepository,
  key : ArtifactAuthKey,
  expected_head~ : (Int32, Int32)? = None,
) -> Bool {
  let raw_auth = match (repo.store.read)(artifact_auth_key_path(repo)) {
    Some(b) => b
    None => return false
  }
  let payload = match
    artifact_envelope_payload(artifact_auth_magic(), raw_auth) {
    Some(p) => p
    None => return false
  }
  let r = module_bin_reader_new_versioned(payload, 3)
  let stored_kid = match br_string(r) {
    Some(s) => s
    None => return false
  }
  let stored_len = br_i32(r)
  let stored_ha = br_i32(r)
  let stored_hb = br_i32(r)
  let stored_ma = br_i32(r)
  let stored_mb = br_i32(r)
  if !br_require_ok(r) || r.pos != payload.length() || stored_kid != key.key_id {
    return false
  }
  let report = artifact_repository_chain_report(repo, expected_head~)
  if !report.valid ||
    report.entries != stored_len ||
    report.head_a != stored_ha ||
    report.head_b != stored_hb {
    return false
  }
  let entries = match artifact_repository_chain_entries(repo) {
    Some(es) => es
    None => return false
  }
  let (mac_a, mac_b) = artifact_chain_keyed_mac(key, entries)
  mac_a == stored_ma && mac_b == stored_mb
}

///|
/// Seal the current chain state of `repo` with `key` after verifying chain and
/// live blob integrity.
pub fn artifact_repository_seal_authenticated(
  repo : ArtifactRepository,
  key : ArtifactAuthKey,
) -> Bool {
  let report = artifact_repository_chain_report(repo)
  if !report.valid {
    return false
  }
  let entries = match artifact_repository_chain_entries(repo) {
    Some(es) => es
    None => return false
  }
  artifact_auth_stamp_write(repo, key, entries)
}

///|
/// Multi-writer optimistic compare-and-swap (`CAS`) authenticated commit:
/// 1. If `chain.auth` already exists, verifies `repo` under `key` (returning
///    `ArtifactCasAuthFailed` on forgery/key mismatch);
/// 2. Compares current chain head `(head_a, head_b)` against `expected_head`
///    (returning `ArtifactCasConflict` without modifying the store when a
///    concurrent writer has advanced the head);
/// 3. Commits `(kind, name, bytes)` and updates `chain.auth`.
pub fn artifact_repository_put_cas_authenticated(
  repo : ArtifactRepository,
  kind : String,
  name : String,
  bytes : Array[Int32],
  format_version : Int32,
  expected_head : (Int32, Int32),
  key : ArtifactAuthKey,
) -> ArtifactCasStatus {
  let has_auth = (repo.store.read)(artifact_auth_key_path(repo)) != None
  if has_auth && !artifact_repository_verify_authenticated(repo, key) {
    return ArtifactCasAuthFailed
  }
  let chain_state = match artifact_chain_load_state(repo) {
    Some(s) => s
    None => return ArtifactCasIoError
  }
  let (_, cur_entries) = chain_state
  if !artifact_chain_links_valid(cur_entries) {
    return ArtifactCasAuthFailed
  }
  let cur_head = artifact_chain_head_of(cur_entries)
  if cur_head != expected_head {
    return ArtifactCasConflict
  }
  if artifact_repository_put(repo, kind, name, bytes, format_version~) == None {
    return ArtifactCasIoError
  }
  let updated_entries = match artifact_repository_chain_entries(repo) {
    Some(es) => es
    None => return ArtifactCasIoError
  }
  if !artifact_auth_stamp_write(repo, key, updated_entries) {
    return ArtifactCasIoError
  }
  ArtifactCasCommitted
}

///|
/// Authenticated incremental repository sync from `source` to `target`:
/// - Verifies `source` (and `target`, if non-empty) under `key`;
/// - Checks that `source`'s chain extends `target`'s chain monotonically;
/// - When `trusted_producers` is non-empty, verifies that every live
///   `"compiled-module"` artifact carries a producer stamp in
///   `trusted_producers`;
/// - Transfers ONLY missing live blobs/manifests (`skipped_existing_blobs`
///   vs `transferred_blobs`), replays tombstones and index, and seals `target`
///   with `key`.
pub fn artifact_repository_sync_incremental(
  source : ArtifactRepository,
  target : ArtifactRepository,
  key : ArtifactAuthKey,
  trusted_producers~ : Array[String] = [],
) -> ArtifactSyncReport {
  let fail = () => ArtifactSyncReport::{
    ok: false,
    transferred_blobs: 0,
    skipped_existing_blobs: 0,
    tombstones_applied: 0,
    final_head_a: 0,
    final_head_b: 0,
  }
  if !artifact_repository_verify_authenticated(source, key) {
    return fail()
  }
  let target_has_auth = (target.store.read)(artifact_auth_key_path(target)) !=
    None
  if target_has_auth && !artifact_repository_verify_authenticated(target, key) {
    return fail()
  }
  let src_entries = match artifact_repository_chain_entries(source) {
    Some(es) => es
    None => return fail()
  }
  let (_, tgt_entries) = match artifact_chain_load_state(target) {
    Some(s) => s
    None => return fail()
  }
  if tgt_entries.length() > src_entries.length() {
    return fail()
  }
  for i in 0..<tgt_entries.length() {
    if src_entries[i] != tgt_entries[i] {
      return fail()
    }
  }
  let mut tombstones = 0
  for i in tgt_entries.length()..<src_entries.length() {
    if src_entries[i].removed {
      tombstones = tombstones + 1
    }
  }
  let live = match artifact_chain_live_records(src_entries) {
    Some(rs) => rs
    None => return fail()
  }
  let mut transferred = 0
  let mut skipped = 0
  for rec in live {
    let src_blob = match (source.store.read)(rec.blob_key) {
      Some(b) => b
      None => return fail()
    }
    if !artifact_record_matches_bytes(rec, src_blob) {
      return fail()
    }
    if trusted_producers.length() > 0 && rec.kind == "compiled-module" {
      match compiled_module_load_binary(src_blob) {
        Some(cm) =>
          if !trusted_producers.contains(cm.producer) {
            return fail()
          }
        None => return fail()
      }
    }
    if artifact_chain_live_blob_ok(target, rec) {
      skipped = skipped + 1
    } else {
      let src_commit = match (source.store.read)(rec.blob_key + ".commit") {
        Some(c) => c
        None => return fail()
      }
      if !(target.store.write)(rec.blob_key, src_blob) ||
        !(target.store.write)(rec.blob_key + ".commit", src_commit) {
        return fail()
      }
      transferred = transferred + 1
    }
  }
  if !artifact_chain_save(target, src_entries) {
    return fail()
  }
  if artifact_repository_recover_chained(target) < 0 {
    return fail()
  }
  if !artifact_auth_stamp_write(target, key, src_entries) {
    return fail()
  }
  let (ha, hb) = artifact_chain_head_of(src_entries)
  ArtifactSyncReport::{
    ok: true,
    transferred_blobs: transferred,
    skipped_existing_blobs: skipped,
    tombstones_applied: tombstones,
    final_head_a: ha,
    final_head_b: hb,
  }
}

// ===========================================================================
// Phase 16 (Track 6C): Hash-Chain LCA Discovery & Deterministic Three-Way
// Repository Merge
// ===========================================================================

///|
pub enum ArtifactMergePolicy {
  ArtifactMergeAbortOnConflict
  ArtifactMergePreferLeft
  ArtifactMergePreferRight
} derive(Debug, Eq)

///|
pub extend ArtifactMergePolicy with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend ArtifactMergePolicy with Eq::{not_equal, equal}

///|
pub fn artifact_merge_policy_abort() -> ArtifactMergePolicy {
  ArtifactMergeAbortOnConflict
}

///|
pub fn artifact_merge_policy_prefer_left() -> ArtifactMergePolicy {
  ArtifactMergePreferLeft
}

///|
pub fn artifact_merge_policy_prefer_right() -> ArtifactMergePolicy {
  ArtifactMergePreferRight
}

///|
pub struct ArtifactMergeConflict {
  kind : String
  name : String
  base_blob_key : String?
  left_blob_key : String?
  right_blob_key : String?
} derive(Debug, Eq)

///|
pub extend ArtifactMergeConflict with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend ArtifactMergeConflict with Eq::{not_equal, equal}

///|
pub struct ArtifactThreeWayMergeReport {
  ok : Bool
  lca_entries : Int32
  merged_records : Int32
  left_applied : Int32
  right_applied : Int32
  convergent_merges : Int32
  tombstones_applied : Int32
  conflicts : Array[ArtifactMergeConflict]
  final_head_a : Int32
  final_head_b : Int32
} derive(Debug, Eq)

///|
pub extend ArtifactThreeWayMergeReport with @moonbitlang/core/debug.Debug::{
  to_repr,
}

///|
pub extend ArtifactThreeWayMergeReport with Eq::{not_equal, equal}

///|
fn artifact_record_same_content(a : ArtifactRecord?, b : ArtifactRecord?) -> Bool {
  match (a, b) {
    (None, None) => true
    (Some(ra), Some(rb)) =>
      ra.byte_length == rb.byte_length &&
      ra.hash_a == rb.hash_a &&
      ra.hash_b == rb.hash_b &&
      ra.format_version == rb.format_version
    _ => false
  }
}

///|
/// Compute the exact Lowest Common Ancestor (LCA) chain prefix length and live
/// record snapshot of two repositories `left` and `right` after verifying both
/// hash-linked integrity chains.
pub fn artifact_repository_common_ancestor_records(
  left : ArtifactRepository,
  right : ArtifactRepository,
) -> (Int32, Array[ArtifactRecord])? {
  if !artifact_repository_chain_report(left).valid ||
    !artifact_repository_chain_report(right).valid {
    return None
  }
  let left_es = match artifact_repository_chain_entries(left) {
    Some(es) => es
    None => return None
  }
  let right_es = match artifact_repository_chain_entries(right) {
    Some(es) => es
    None => return None
  }
  let min_len = if left_es.length() < right_es.length() {
    left_es.length()
  } else {
    right_es.length()
  }
  let mut lca = 0
  while lca < min_len && left_es[lca] == right_es[lca] {
    lca = lca + 1
  }
  let prefix : Array[ArtifactChainEntry] = []
  for i in 0..<lca {
    prefix.push(left_es[i])
  }
  match artifact_chain_live_records(prefix) {
    Some(base_live) => Some((lca, base_live))
    None => None
  }
}

///|
/// Deterministic three-way repository merge of divergent branches `left` and
/// `right` into `target`:
/// - Reconstructs the exact LCA snapshot from the longest common hash-chain
///   prefix of `left` and `right`;
/// - Merges disjoint additions, updates, and deletions cleanly;
/// - Treats identical concurrent edits/deletions as convergent (`convergent_merges`);
/// - Detects true edit/edit, edit/delete, and add/add content conflicts, either
///   aborting cleanly without mutating `target` (`ArtifactMergeAbortOnConflict`)
///   or resolving deterministically under `ArtifactMergePreferLeft` /
///   `ArtifactMergePreferRight`;
/// - Verifies every transferred blob against its dual digest and optionally
///   seals `target` under `auth_key`.
pub fn artifact_repository_merge_three_way(
  left : ArtifactRepository,
  right : ArtifactRepository,
  target : ArtifactRepository,
  policy~ : ArtifactMergePolicy = ArtifactMergeAbortOnConflict,
  auth_key~ : ArtifactAuthKey? = None,
) -> ArtifactThreeWayMergeReport {
  let fail = (lca_n : Int32, conflicts : Array[ArtifactMergeConflict]) => {
    ArtifactThreeWayMergeReport::{
      ok: false,
      lca_entries: lca_n,
      merged_records: 0,
      left_applied: 0,
      right_applied: 0,
      convergent_merges: 0,
      tombstones_applied: 0,
      conflicts,
      final_head_a: 0,
      final_head_b: 0,
    }
  }
  match auth_key {
    Some(k) =>
      if !artifact_repository_verify_authenticated(left, k) ||
        !artifact_repository_verify_authenticated(right, k) {
        return fail(0, [])
      }
    None => ()
  }
  let (lca_len, base_recs) = match
    artifact_repository_common_ancestor_records(left, right) {
    Some(v) => v
    None => return fail(0, [])
  }
  let left_recs = artifact_repository_list(left)
  let right_recs = artifact_repository_list(right)

  // Collect sorted unique `(kind, name)` keys across `base ∪ left ∪ right`.
  let keys : Array[(String, String)] = []
  let add_key = (k : String, n : String) => {
    for pair in keys {
      if pair.0 == k && pair.1 == n {
        return
      }
    }
    keys.push((k, n))
  }
  for r in base_recs {
    add_key(r.kind, r.name)
  }
  for r in left_recs {
    add_key(r.kind, r.name)
  }
  for r in right_recs {
    add_key(r.kind, r.name)
  }
  for i in 0..<keys.length() {
    for j in (i + 1)..<keys.length() {
      let ki = keys[i].0 + "\u{0}" + keys[i].1
      let kj = keys[j].0 + "\u{0}" + keys[j].1
      if kj < ki {
        let tmp = keys[i]
        keys[i] = keys[j]
        keys[j] = tmp
      }
    }
  }

  let conflicts : Array[ArtifactMergeConflict] = []
  // `chosen`: `(kind, name, source_side: 1=left | 2=right, chosen_rec?)`
  let chosen : Array[(String, String, Int32, ArtifactRecord?)] = []
  let mut left_applied = 0
  let mut right_applied = 0
  let mut convergent = 0
  let mut tombstones = 0

  for pair in keys {
    let (kind, name) = pair
    let b = artifact_records_find(base_recs, kind, name)
    let l = artifact_records_find(left_recs, kind, name)
    let r = artifact_records_find(right_recs, kind, name)
    let l_unchanged = artifact_record_same_content(l, b)
    let r_unchanged = artifact_record_same_content(r, b)
    if l_unchanged && r_unchanged {
      match l {
        Some(rec) => chosen.push((kind, name, 1, Some(rec)))
        None => ()
      }
    } else if r_unchanged && !l_unchanged {
      left_applied = left_applied + 1
      if l == None && b != None {
        tombstones = tombstones + 1
      }
      chosen.push((kind, name, 1, l))
    } else if l_unchanged && !r_unchanged {
      right_applied = right_applied + 1
      if r == None && b != None {
        tombstones = tombstones + 1
      }
      chosen.push((kind, name, 2, r))
    } else if artifact_record_same_content(l, r) {
      convergent = convergent + 1
      if l == None && b != None {
        tombstones = tombstones + 1
      }
      chosen.push((kind, name, 1, l))
    } else {
      let b_key = match b {
        Some(v) => Some(v.blob_key)
        None => None
      }
      let l_key = match l {
        Some(v) => Some(v.blob_key)
        None => None
      }
      let r_key = match r {
        Some(v) => Some(v.blob_key)
        None => None
      }
      conflicts.push(ArtifactMergeConflict::{
        kind,
        name,
        base_blob_key: b_key,
        left_blob_key: l_key,
        right_blob_key: r_key,
      })
      match policy {
        ArtifactMergeAbortOnConflict => ()
        ArtifactMergePreferLeft => {
          left_applied = left_applied + 1
          if l == None && b != None {
            tombstones = tombstones + 1
          }
          chosen.push((kind, name, 1, l))
        }
        ArtifactMergePreferRight => {
          right_applied = right_applied + 1
          if r == None && b != None {
            tombstones = tombstones + 1
          }
          chosen.push((kind, name, 2, r))
        }
      }
    }
  }

  if conflicts.length() > 0 && policy == ArtifactMergeAbortOnConflict {
    return fail(lca_len, conflicts)
  }

  // Stage and verify all blobs before mutating `target`.
  let staged : Array[(String, String, Array[Int32], Int32)] = []
  for item in chosen {
    let (kind, name, side, rec_opt) = item
    match rec_opt {
      Some(rec) => {
        let src_repo = if side == 1 { left } else { right }
        let bytes = match (src_repo.store.read)(rec.blob_key) {
          Some(bs) => bs
          None => return fail(lca_len, conflicts)
        }
        if !artifact_record_matches_bytes(rec, bytes) {
          return fail(lca_len, conflicts)
        }
        staged.push((kind, name, bytes, rec.format_version))
      }
      None => ()
    }
  }

  // Apply tombstones for any record currently live in `target` that is not in `staged`.
  let cur_target = artifact_repository_list(target)
  for trec in cur_target {
    let mut keep = false
    for s in staged {
      if s.0 == trec.kind && s.1 == trec.name {
        keep = true
        break
      }
    }
    if !keep {
      if !artifact_repository_remove(target, trec.kind, trec.name) {
        return fail(lca_len, conflicts)
      }
    }
  }

  for s in staged {
    let (kind, name, bytes, fmt_ver) = s
    if artifact_repository_put(target, kind, name, bytes, format_version=fmt_ver) ==
      None {
      return fail(lca_len, conflicts)
    }
  }

  let final_entries = match artifact_repository_chain_entries(target) {
    Some(es) => es
    None => return fail(lca_len, conflicts)
  }
  match auth_key {
    Some(k) =>
      if !artifact_auth_stamp_write(target, k, final_entries) {
        return fail(lca_len, conflicts)
      }
    None => ()
  }
  let (ha, hb) = artifact_chain_head_of(final_entries)
  ArtifactThreeWayMergeReport::{
    ok: true,
    lca_entries: lca_len,
    merged_records: staged.length(),
    left_applied,
    right_applied,
    convergent_merges: convergent,
    tombstones_applied: tombstones,
    conflicts,
    final_head_a: ha,
    final_head_b: hb,
  }
}
