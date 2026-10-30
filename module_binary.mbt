///|\
// Stable on-disk binary format for compiled modules.
//
// File layout (all integers little-endian):
//
//   bytes  0..8   magic `CHMODBIN`
//          8..10  binary format version (u16; see version policy)
//         10..12  flags (u16, currently 0)
//         12..16  payload length (i32 bit pattern, nonnegative)
//         16..20  DJB2-xor checksum of the payload (i32 bit pattern)
//         20..    payload
//
// Strings are a signed 32-bit count of UTF-16 code units followed
// by those units in little-endian order.  The payload stores every
// field of `CompiledModule` in declaration order.  Terms and schema
// descriptors use the fixed one-byte tags in this file; new tags may
// only be added in a new binary-format version.  The parser bounds
// counts by the remaining payload and bounds recursion depth, so a
// malformed file is rejected rather than expanded without limit.

///|
pub enum ModuleBinaryStatus {
  ModuleBinaryOk
  ModuleBinaryBadMagic
  ModuleBinaryUnsupportedVersion
  ModuleBinaryTruncated
  ModuleBinaryChecksumMismatch
  ModuleBinaryMalformed
  ModuleBinaryTrailingBytes
  ModuleBinaryValidationFailed
} derive(Debug, Eq)

///|
pub extend ModuleBinaryStatus with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend ModuleBinaryStatus with Eq::{not_equal, equal}

///|
pub struct ModuleBinaryLoad {
  status : ModuleBinaryStatus
  module_ : CompiledModule?
} derive(Debug, Eq)

///|
pub extend ModuleBinaryLoad with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend ModuleBinaryLoad with Eq::{not_equal, equal}

///|
/// The binary layout version written by this build.  Version 2
/// payloads extend the version 1 payload with a producer string
/// and admit tag-8 schema functor nodes (`DFunctorFamily`).
/// Version 3 admits tag-9 self-family functor nodes and encodes
/// repeated `DTerm` subterms by back-reference into a shared
/// per-payload term table (a DAG codec): a subterm of at least
/// `module_binary_dag_min_nodes` nodes is written in full once,
/// and later occurrences are a one-byte reference tag with the
/// table index.  The loader accepts all three versions.
pub fn compiled_module_binary_format_version() -> Int32 {
  3
}

///|
/// All binary layout versions this loader can read.
pub fn compiled_module_binary_supported_versions() -> Array[Int32] {
  [1, 2, 3]
}

///|
/// Machine-readable version policy for the compiled-module
/// format: the current written version, every readable version,
/// and the oldest version this build can still write on request.
pub struct BinaryVersionPolicy {
  current : Int32
  supported : Array[Int32]
  oldest_writable : Int32
} derive(Debug, Eq)

///|
pub extend BinaryVersionPolicy with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend BinaryVersionPolicy with Eq::{not_equal, equal}

///|
pub fn compiled_module_binary_version_policy() -> BinaryVersionPolicy {
  BinaryVersionPolicy::{
    current: compiled_module_binary_format_version(),
    supported: compiled_module_binary_supported_versions(),
    oldest_writable: 1,
  }
}

///|
/// Highest version present in both lists, or -1 when the two
/// sides share no version.
pub fn binary_negotiate_version(
  supported : Array[Int32],
  peer_versions : Array[Int32],
) -> Int32 {
  let mut best = -1
  for i in 0..<supported.length() {
    if supported[i] > best && contains_int(peer_versions, supported[i]) {
      best = supported[i]
    }
  }
  best
}

///|
pub fn compiled_module_binary_negotiate_version(
  peer_versions : Array[Int32],
) -> Int32 {
  binary_negotiate_version(
    compiled_module_binary_supported_versions(),
    peer_versions,
  )
}

///|
/// The layout version recorded in a binary blob's header, or -1
/// when the blob does not even carry a recognizable header.
pub fn compiled_module_binary_version_of(bytes : Array[Int32]) -> Int32 {
  if bytes.length() < 12 {
    return -1
  }
  let magic = [67, 72, 77, 79, 68, 66, 73, 78]
  for i in 0..<magic.length() {
    if (bytes[i] & 255) != magic[i] {
      return -1
    }
  }
  module_binary_u16_at(bytes, 8)
}

///|
priv struct ModuleBinWriter {
  bytes : Array[Int32]
  version : Int32
  /// Completed large subterms already written in this payload,
  /// keyed by cache key, for the v3 DAG term codec.
  term_table : Array[(String, DTerm)]
  /// Write terms as bare node trees, with no back-references or
  /// term-table registration.  Used for the local shells of the
  /// persistent interned-DAG codec (`CHDAGBIN`), whose sharing is
  /// expressed by explicit child-id edges instead.
  bare_terms : Bool
}

///|
priv struct ModuleBinReader {
  bytes : Array[Int32]
  mut pos : Int32
  mut status : ModuleBinaryStatus
  /// Binary layout version being read; version-gated payload
  /// nodes (tag-8/9 functors, the v2 producer extension, the v3
  /// DAG term references) consult this field.
  version : Int32
  /// Completed large subterms, in writer registration order.
  term_table : Array[DTerm]
  /// Read bare node trees only (the counterpart of the writer
  /// flag): a tag-255 back-reference is malformed here.
  bare_terms : Bool
}

///|
fn module_bin_writer_new() -> ModuleBinWriter {
  { bytes: [], version: 2, term_table: [], bare_terms: false, }
}

///|
fn module_bin_writer_new_versioned(version : Int32) -> ModuleBinWriter {
  { bytes: [], version, term_table: [], bare_terms: false, }
}

///|
fn module_bin_writer_new_bare() -> ModuleBinWriter {
  // Codec generation 3, so every node tag readable by the
  // current term codec may appear in a shell.
  { bytes: [], version: 3, term_table: [], bare_terms: true, }
}

///|
fn module_bin_reader_new_versioned(
  bytes : Array[Int32],
  version : Int32,
) -> ModuleBinReader {
  {
    bytes,
    pos: 0,
    status: ModuleBinaryOk,
    version,
    term_table: [],
    bare_terms: false,
  }
}

///|
fn module_bin_reader_new_bare(bytes : Array[Int32]) -> ModuleBinReader {
  {
    bytes,
    pos: 0,
    status: ModuleBinaryOk,
    version: 3,
    term_table: [],
    bare_terms: true,
  }
}

///|
fn bw_u8(w : ModuleBinWriter, value : Int32) -> Unit {
  w.bytes.push(value & 255)
}

///|
fn bw_i32(w : ModuleBinWriter, value : Int32) -> Unit {
  bw_u8(w, value)
  bw_u8(w, value >> 8)
  bw_u8(w, value >> 16)
  bw_u8(w, value >> 24)
}

///|
fn bw_bool(w : ModuleBinWriter, value : Bool) -> Unit {
  bw_u8(w, if value { 1 } else { 0 })
}

///|
fn bw_string(w : ModuleBinWriter, value : String) -> Unit {
  bw_i32(w, value.length())
  for i in 0..<value.length() {
    let unit = value[i].to_int()
    bw_u8(w, unit)
    bw_u8(w, unit >> 8)
  }
}

///|
fn br_u8(r : ModuleBinReader) -> Int32 {
  if r.status != ModuleBinaryOk {
    return 0
  }
  if r.pos < 0 || r.pos >= r.bytes.length() {
    r.status = ModuleBinaryTruncated
    return 0
  }
  let value = r.bytes[r.pos]
  r.pos = r.pos + 1
  if value < 0 || value > 255 {
    r.status = ModuleBinaryMalformed
    0
  } else {
    value
  }
}

///|
fn br_i32(r : ModuleBinReader) -> Int32 {
  let b0 = br_u8(r)
  let b1 = br_u8(r)
  let b2 = br_u8(r)
  let b3 = br_u8(r)
  b0 | (b1 << 8) | (b2 << 16) | (b3 << 24)
}

///|
fn br_count(r : ModuleBinReader) -> Int32 {
  let count = br_i32(r)
  if r.status == ModuleBinaryOk &&
    (count < 0 || count > r.bytes.length() - r.pos) {
    r.status = ModuleBinaryMalformed
  }
  count
}

///|
fn br_bool(r : ModuleBinReader) -> Bool {
  match br_u8(r) {
    0 => false
    1 => true
    _ => {
      if r.status == ModuleBinaryOk {
        r.status = ModuleBinaryMalformed
      }
      false
    }
  }
}

///|
fn br_string(r : ModuleBinReader) -> String? {
  let count = br_i32(r)
  if r.status != ModuleBinaryOk {
    return None
  }
  if count < 0 || count > (r.bytes.length() - r.pos) / 2 {
    r.status = ModuleBinaryMalformed
    return None
  }
  let builder = StringBuilder(size_hint=count)
  for _i in 0..<count {
    let lo = br_u8(r)
    let hi = br_u8(r)
    if r.status != ModuleBinaryOk {
      return None
    }
    builder.write_char((lo | (hi << 8)).unsafe_to_char())
  }
  Some(builder.to_string())
}

///|
fn br_require_ok(r : ModuleBinReader) -> Bool {
  r.status == ModuleBinaryOk
}

///|
fn br_depth_failed(r : ModuleBinReader, depth : Int32) -> Bool {
  if depth > 1024 {
    r.status = ModuleBinaryMalformed
    true
  } else {
    false
  }
}

///|
fn bw_dim(w : ModuleBinWriter, value : Dim) -> Unit {
  match value {
    DZero => bw_u8(w, 0)
    DOne => bw_u8(w, 1)
    DVar(i) => {
      bw_u8(w, 2)
      bw_i32(w, i)
    }
    DNeg(a) => {
      bw_u8(w, 3)
      bw_dim(w, a)
    }
    DAnd(a, b) => {
      bw_u8(w, 4)
      bw_dim(w, a)
      bw_dim(w, b)
    }
    DOr(a, b) => {
      bw_u8(w, 5)
      bw_dim(w, a)
      bw_dim(w, b)
    }
  }
}

///|
fn br_dim(r : ModuleBinReader, depth : Int32) -> Dim? {
  if br_depth_failed(r, depth) {
    return None
  }
  match br_u8(r) {
    0 => Some(DZero)
    1 => Some(DOne)
    2 => {
      let value = br_i32(r)
      if br_require_ok(r) {
        Some(DVar(value))
      } else {
        None
      }
    }
    3 =>
      match br_dim(r, depth + 1) {
        Some(a) => Some(DNeg(a))
        None => None
      }
    4 => {
      let a = match br_dim(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      let b = match br_dim(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      Some(DAnd(a, b))
    }
    5 => {
      let a = match br_dim(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      let b = match br_dim(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      Some(DOr(a, b))
    }
    _ => {
      if r.status == ModuleBinaryOk {
        r.status = ModuleBinaryMalformed
      }
      None
    }
  }
}

///|
fn bw_face(w : ModuleBinWriter, value : Face) -> Unit {
  match value {
    FTop => bw_u8(w, 0)
    FBot => bw_u8(w, 1)
    FEq0(d) => {
      bw_u8(w, 2)
      bw_dim(w, d)
    }
    FEq1(d) => {
      bw_u8(w, 3)
      bw_dim(w, d)
    }
    FAnd(a, b) => {
      bw_u8(w, 4)
      bw_face(w, a)
      bw_face(w, b)
    }
    FOr(a, b) => {
      bw_u8(w, 5)
      bw_face(w, a)
      bw_face(w, b)
    }
  }
}

///|
fn br_face(r : ModuleBinReader, depth : Int32) -> Face? {
  if br_depth_failed(r, depth) {
    return None
  }
  match br_u8(r) {
    0 => Some(FTop)
    1 => Some(FBot)
    2 =>
      match br_dim(r, depth + 1) {
        Some(d) => Some(FEq0(d))
        None => None
      }
    3 =>
      match br_dim(r, depth + 1) {
        Some(d) => Some(FEq1(d))
        None => None
      }
    4 => {
      let a = match br_face(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      let b = match br_face(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      Some(FAnd(a, b))
    }
    5 => {
      let a = match br_face(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      let b = match br_face(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      Some(FOr(a, b))
    }
    _ => {
      if r.status == ModuleBinaryOk {
        r.status = ModuleBinaryMalformed
      }
      None
    }
  }
}

///|
fn bw_level_expr(w : ModuleBinWriter, value : DLevelExpr) -> Unit {
  match value {
    DLevelConst(n) => {
      bw_u8(w, 0)
      bw_i32(w, n)
    }
    DLevelVar(n) => {
      bw_u8(w, 1)
      bw_i32(w, n)
    }
    DLevelSucc(a) => {
      bw_u8(w, 2)
      bw_level_expr(w, a)
    }
    DLevelMax(a, b) => {
      bw_u8(w, 3)
      bw_level_expr(w, a)
      bw_level_expr(w, b)
    }
  }
}

///|
fn br_level_expr(r : ModuleBinReader, depth : Int32) -> DLevelExpr? {
  if br_depth_failed(r, depth) {
    return None
  }
  match br_u8(r) {
    0 => {
      let value = br_i32(r)
      if br_require_ok(r) {
        Some(DLevelConst(value))
      } else {
        None
      }
    }
    1 => {
      let value = br_i32(r)
      if br_require_ok(r) {
        Some(DLevelVar(value))
      } else {
        None
      }
    }
    2 =>
      match br_level_expr(r, depth + 1) {
        Some(a) => Some(DLevelSucc(a))
        None => None
      }
    3 => {
      let a = match br_level_expr(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      let b = match br_level_expr(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      Some(DLevelMax(a, b))
    }
    _ => {
      if r.status == ModuleBinaryOk {
        r.status = ModuleBinaryMalformed
      }
      None
    }
  }
}

///|
/// Minimum tree size for a subterm to enter the v3 shared term
/// table; below this a back-reference would not pay for itself.
fn module_binary_dag_min_nodes() -> Int32 {
  6
}

///|
fn bw_term(w : ModuleBinWriter, value : DTerm) -> Unit {
  if !w.bare_terms &&
    w.version >= 3 &&
    dterm_tree_node_count(value) >= module_binary_dag_min_nodes() {
    let key = dterm_cache_key(value)
    for i in 0..<w.term_table.length() {
      if w.term_table[i].0 == key && w.term_table[i].1 == value {
        bw_u8(w, 255)
        bw_i32(w, i)
        return
      }
    }
    bw_term_node(w, value)
    w.term_table.push((key, value))
  } else {
    bw_term_node(w, value)
  }
}

///|
fn bw_term_node(w : ModuleBinWriter, value : DTerm) -> Unit {
  match value {
    DTVar(a) => {
      bw_u8(w, 0)
      bw_i32(w, a)
    }
    DUniv(a) => {
      bw_u8(w, 1)
      bw_i32(w, a)
    }
    DUnivLevel(a) => {
      bw_u8(w, 2)
      bw_level_expr(w, a)
    }
    DBoolTy => bw_u8(w, 3)
    DUnitTy => bw_u8(w, 4)
    DPi(a, b) => {
      bw_u8(w, 5)
      bw_term(w, a)
      bw_term(w, b)
    }
    DSigma(a, b) => {
      bw_u8(w, 6)
      bw_term(w, a)
      bw_term(w, b)
    }
    DLam(a, b) => {
      bw_u8(w, 7)
      bw_term(w, a)
      bw_term(w, b)
    }
    DApp(a, b) => {
      bw_u8(w, 8)
      bw_term(w, a)
      bw_term(w, b)
    }
    DPair(a, b) => {
      bw_u8(w, 9)
      bw_term(w, a)
      bw_term(w, b)
    }
    DFst(a) => {
      bw_u8(w, 10)
      bw_term(w, a)
    }
    DSnd(a) => {
      bw_u8(w, 11)
      bw_term(w, a)
    }
    DBoolLit(a) => {
      bw_u8(w, 12)
      bw_bool(w, a)
    }
    DBoolElim(a, b, c, d) => {
      bw_u8(w, 13)
      bw_term(w, a)
      bw_term(w, b)
      bw_term(w, c)
      bw_term(w, d)
    }
    DUnitLit => bw_u8(w, 14)
    DAnn(a, b) => {
      bw_u8(w, 15)
      bw_term(w, a)
      bw_term(w, b)
    }
    DPartial(a) => {
      bw_u8(w, 16)
      bw_face_terms(w, a)
    }
    DPathP(a, b, c) => {
      bw_u8(w, 17)
      bw_term(w, a)
      bw_term(w, b)
      bw_term(w, c)
    }
    DPath(a, b, c) => {
      bw_u8(w, 18)
      bw_term(w, a)
      bw_term(w, b)
      bw_term(w, c)
    }
    DLamDim(a) => {
      bw_u8(w, 19)
      bw_term(w, a)
    }
    DAppDim(a, b) => {
      bw_u8(w, 20)
      bw_term(w, a)
      bw_dim(w, b)
    }
    DCoe(a, b, c, d) => {
      bw_u8(w, 21)
      bw_term(w, a)
      bw_dim(w, b)
      bw_dim(w, c)
      bw_term(w, d)
    }
    DComp(a, b, c) => {
      bw_u8(w, 22)
      bw_term(w, a)
      bw_tube_terms(w, b)
      bw_term(w, c)
    }
    DHComp(a, b, c) => {
      bw_u8(w, 23)
      bw_term(w, a)
      bw_tube_terms(w, b)
      bw_term(w, c)
    }
    DHFill(a, b, c, d) => {
      bw_u8(w, 24)
      bw_term(w, a)
      bw_tube_terms(w, b)
      bw_term(w, c)
      bw_dim(w, d)
    }
    DNatTy => bw_u8(w, 25)
    DNatZero => bw_u8(w, 26)
    DSucc(a) => {
      bw_u8(w, 27)
      bw_term(w, a)
    }
    DNatElim(a, b, c, d) => {
      bw_u8(w, 28)
      bw_term(w, a)
      bw_term(w, b)
      bw_term(w, c)
      bw_term(w, d)
    }
    DListTy(a) => {
      bw_u8(w, 29)
      bw_term(w, a)
    }
    DNil => bw_u8(w, 30)
    DCons(a, b) => {
      bw_u8(w, 31)
      bw_term(w, a)
      bw_term(w, b)
    }
    DListElim(a, b, c, d) => {
      bw_u8(w, 32)
      bw_term(w, a)
      bw_term(w, b)
      bw_term(w, c)
      bw_term(w, d)
    }
    DCircleTy => bw_u8(w, 33)
    DCircleBase => bw_u8(w, 34)
    DCircleLoop => bw_u8(w, 35)
    DCircleElim(a, b, c, d) => {
      bw_u8(w, 36)
      bw_term(w, a)
      bw_term(w, b)
      bw_term(w, c)
      bw_term(w, d)
    }
    DTorusTy => bw_u8(w, 37)
    DTorusBase => bw_u8(w, 38)
    DTorusLoopA => bw_u8(w, 39)
    DTorusLoopB => bw_u8(w, 40)
    DTorusSquare => bw_u8(w, 41)
    DTorusElim(a, b, c) => {
      bw_u8(w, 42)
      bw_term(w, a)
      bw_term(w, b)
      bw_term(w, c)
    }
    DInductive(a, b) => {
      bw_u8(w, 43)
      bw_inductive_spec(w, a)
      bw_terms(w, b)
    }
    DIntro(a, b, c, d) => {
      bw_u8(w, 44)
      bw_inductive_spec(w, a)
      bw_i32(w, b)
      bw_terms(w, c)
      bw_terms(w, d)
    }
    DInductiveElim(a, b, c, d, e, f) => {
      bw_u8(w, 45)
      bw_inductive_spec(w, a)
      bw_term(w, b)
      bw_terms(w, c)
      bw_terms(w, d)
      bw_terms(w, e)
      bw_term(w, f)
    }
    DHitType(a, b) => {
      bw_u8(w, 46)
      bw_hit_spec(w, a)
      bw_terms(w, b)
    }
    DHitIntro(a, b, c, d, e) => {
      bw_u8(w, 47)
      bw_hit_spec(w, a)
      bw_i32(w, b)
      bw_terms(w, c)
      bw_terms(w, d)
      bw_dims(w, e)
    }
    DHitElim(a, b, c, d, e, f) => {
      bw_u8(w, 48)
      bw_hit_spec(w, a)
      bw_term(w, b)
      bw_terms(w, c)
      bw_terms(w, d)
      bw_terms(w, e)
      bw_term(w, f)
    }
    DDecode(a, b, c, d) => {
      bw_u8(w, 49)
      bw_inductive_spec(w, a)
      bw_terms(w, b)
      bw_terms(w, c)
      bw_term(w, d)
    }
    DEquivTy(a, b) => {
      bw_u8(w, 50)
      bw_term(w, a)
      bw_term(w, b)
    }
    DMkEquiv(a, b, c, d, e, f) => {
      bw_u8(w, 51)
      bw_term(w, a)
      bw_term(w, b)
      bw_term(w, c)
      bw_term(w, d)
      bw_term(w, e)
      bw_term(w, f)
    }
    DEquivFwd(a) => {
      bw_u8(w, 52)
      bw_term(w, a)
    }
    DEquivBwd(a) => {
      bw_u8(w, 53)
      bw_term(w, a)
    }
    DEquivSect(a) => {
      bw_u8(w, 54)
      bw_term(w, a)
    }
    DEquivRetr(a) => {
      bw_u8(w, 55)
      bw_term(w, a)
    }
    DGlueEquiv(a, b) => {
      bw_u8(w, 56)
      bw_term(w, a)
      bw_equiv_branches(w, b)
    }
    DUa(a) => {
      bw_u8(w, 57)
      bw_term(w, a)
    }
    DUnglueEquiv(term, base, branches) => {
      bw_u8(w, 58)
      bw_term(w, term)
      bw_term(w, base)
      bw_equiv_branches(w, branches)
    }
  }
}

///|
fn br_term(r : ModuleBinReader, depth : Int32) -> DTerm? {
  if br_depth_failed(r, depth) {
    return None
  }
  let tag = br_u8(r)
  if tag == 255 {
    if r.bare_terms {
      if r.status == ModuleBinaryOk {
        r.status = ModuleBinaryMalformed
      }
      return None
    }
    if r.version < 3 {
      if r.status == ModuleBinaryOk {
        r.status = ModuleBinaryUnsupportedVersion
      }
      return None
    }
    let id = br_i32(r)
    if !br_require_ok(r) || id < 0 || id >= r.term_table.length() {
      if r.status == ModuleBinaryOk {
        r.status = ModuleBinaryMalformed
      }
      return None
    }
    return Some(r.term_table[id])
  }
  let result = br_term_from_tag(r, depth, tag)
  match result {
    Some(term) =>
      if !r.bare_terms &&
        r.version >= 3 &&
        dterm_tree_node_count(term) >= module_binary_dag_min_nodes() {
        r.term_table.push(term)
      }
    None => ()
  }
  result
}

///|
fn br_term_from_tag(r : ModuleBinReader, depth : Int32, tag : Int32) -> DTerm? {
  match tag {
    0 => {
      let a = br_i32(r)
      if !br_require_ok(r) {
        return None
      }
      Some(DTVar(a))
    }
    1 => {
      let a = br_i32(r)
      if !br_require_ok(r) {
        return None
      }
      Some(DUniv(a))
    }
    2 => {
      let a = match br_level_expr(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      Some(DUnivLevel(a))
    }
    3 => Some(DBoolTy)
    4 => Some(DUnitTy)
    5 => {
      let a = match br_term(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      let b = match br_term(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      Some(DPi(a, b))
    }
    6 => {
      let a = match br_term(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      let b = match br_term(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      Some(DSigma(a, b))
    }
    7 => {
      let a = match br_term(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      let b = match br_term(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      Some(DLam(a, b))
    }
    8 => {
      let a = match br_term(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      let b = match br_term(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      Some(DApp(a, b))
    }
    9 => {
      let a = match br_term(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      let b = match br_term(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      Some(DPair(a, b))
    }
    10 => {
      let a = match br_term(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      Some(DFst(a))
    }
    11 => {
      let a = match br_term(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      Some(DSnd(a))
    }
    12 => {
      let a = br_bool(r)
      if !br_require_ok(r) {
        return None
      }
      Some(DBoolLit(a))
    }
    13 => {
      let a = match br_term(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      let b = match br_term(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      let c = match br_term(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      let d = match br_term(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      Some(DBoolElim(a, b, c, d))
    }
    14 => Some(DUnitLit)
    15 => {
      let a = match br_term(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      let b = match br_term(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      Some(DAnn(a, b))
    }
    16 => {
      let a = match br_face_terms(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      Some(DPartial(a))
    }
    17 => {
      let a = match br_term(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      let b = match br_term(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      let c = match br_term(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      Some(DPathP(a, b, c))
    }
    18 => {
      let a = match br_term(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      let b = match br_term(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      let c = match br_term(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      Some(DPath(a, b, c))
    }
    19 => {
      let a = match br_term(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      Some(DLamDim(a))
    }
    20 => {
      let a = match br_term(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      let b = match br_dim(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      Some(DAppDim(a, b))
    }
    21 => {
      let a = match br_term(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      let b = match br_dim(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      let c = match br_dim(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      let d = match br_term(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      Some(DCoe(a, b, c, d))
    }
    22 => {
      let a = match br_term(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      let b = match br_tube_terms(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      let c = match br_term(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      Some(DComp(a, b, c))
    }
    23 => {
      let a = match br_term(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      let b = match br_tube_terms(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      let c = match br_term(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      Some(DHComp(a, b, c))
    }
    24 => {
      let a = match br_term(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      let b = match br_tube_terms(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      let c = match br_term(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      let d = match br_dim(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      Some(DHFill(a, b, c, d))
    }
    25 => Some(DNatTy)
    26 => Some(DNatZero)
    27 => {
      let a = match br_term(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      Some(DSucc(a))
    }
    28 => {
      let a = match br_term(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      let b = match br_term(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      let c = match br_term(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      let d = match br_term(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      Some(DNatElim(a, b, c, d))
    }
    29 => {
      let a = match br_term(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      Some(DListTy(a))
    }
    30 => Some(DNil)
    31 => {
      let a = match br_term(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      let b = match br_term(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      Some(DCons(a, b))
    }
    32 => {
      let a = match br_term(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      let b = match br_term(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      let c = match br_term(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      let d = match br_term(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      Some(DListElim(a, b, c, d))
    }
    33 => Some(DCircleTy)
    34 => Some(DCircleBase)
    35 => Some(DCircleLoop)
    36 => {
      let a = match br_term(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      let b = match br_term(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      let c = match br_term(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      let d = match br_term(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      Some(DCircleElim(a, b, c, d))
    }
    37 => Some(DTorusTy)
    38 => Some(DTorusBase)
    39 => Some(DTorusLoopA)
    40 => Some(DTorusLoopB)
    41 => Some(DTorusSquare)
    42 => {
      let a = match br_term(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      let b = match br_term(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      let c = match br_term(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      Some(DTorusElim(a, b, c))
    }
    43 => {
      let a = match br_inductive_spec(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      let b = match br_terms(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      Some(DInductive(a, b))
    }
    44 => {
      let a = match br_inductive_spec(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      let b = br_i32(r)
      if !br_require_ok(r) {
        return None
      }
      let c = match br_terms(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      let d = match br_terms(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      Some(DIntro(a, b, c, d))
    }
    45 => {
      let a = match br_inductive_spec(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      let b = match br_term(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      let c = match br_terms(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      let d = match br_terms(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      let e = match br_terms(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      let f = match br_term(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      Some(DInductiveElim(a, b, c, d, e, f))
    }
    46 => {
      let a = match br_hit_spec(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      let b = match br_terms(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      Some(DHitType(a, b))
    }
    47 => {
      let a = match br_hit_spec(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      let b = br_i32(r)
      if !br_require_ok(r) {
        return None
      }
      let c = match br_terms(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      let d = match br_terms(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      let e = match br_dims(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      Some(DHitIntro(a, b, c, d, e))
    }
    48 => {
      let a = match br_hit_spec(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      let b = match br_term(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      let c = match br_terms(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      let d = match br_terms(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      let e = match br_terms(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      let f = match br_term(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      Some(DHitElim(a, b, c, d, e, f))
    }
    49 => {
      let a = match br_inductive_spec(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      let b = match br_terms(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      let c = match br_terms(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      let d = match br_term(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      Some(DDecode(a, b, c, d))
    }
    50 => {
      let a = match br_term(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      let b = match br_term(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      Some(DEquivTy(a, b))
    }
    51 => {
      let a = match br_term(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      let b = match br_term(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      let c = match br_term(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      let d = match br_term(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      let e = match br_term(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      let f = match br_term(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      Some(DMkEquiv(a, b, c, d, e, f))
    }
    52 => {
      let a = match br_term(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      Some(DEquivFwd(a))
    }
    53 => {
      let a = match br_term(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      Some(DEquivBwd(a))
    }
    54 => {
      let a = match br_term(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      Some(DEquivSect(a))
    }
    55 => {
      let a = match br_term(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      Some(DEquivRetr(a))
    }
    56 => {
      let a = match br_term(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      let b = match br_equiv_branches(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      Some(DGlueEquiv(a, b))
    }
    57 => {
      let a = match br_term(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      Some(DUa(a))
    }
    58 => {
      let term = match br_term(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      let base = match br_term(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      let branches = match br_equiv_branches(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      Some(DUnglueEquiv(term, base, branches))
    }
    _ => {
      if r.status == ModuleBinaryOk {
        r.status = ModuleBinaryMalformed
      }
      None
    }
  }
}

///|
fn bw_terms(w : ModuleBinWriter, values : Array[DTerm]) -> Unit {
  bw_i32(w, values.length())
  for i in 0..<values.length() {
    bw_term(w, values[i])
  }
}

///|
fn br_terms(r : ModuleBinReader, depth : Int32) -> Array[DTerm]? {
  let count = br_count(r)
  if !br_require_ok(r) {
    return None
  }
  let values : Array[DTerm] = []
  for _i in 0..<count {
    match br_term(r, depth + 1) {
      Some(v) => values.push(v)
      None => return None
    }
  }
  Some(values)
}

///|
fn bw_dims(w : ModuleBinWriter, values : Array[Dim]) -> Unit {
  bw_i32(w, values.length())
  for i in 0..<values.length() {
    bw_dim(w, values[i])
  }
}

///|
fn br_dims(r : ModuleBinReader, depth : Int32) -> Array[Dim]? {
  let count = br_count(r)
  if !br_require_ok(r) {
    return None
  }
  let values : Array[Dim] = []
  for _i in 0..<count {
    match br_dim(r, depth + 1) {
      Some(v) => values.push(v)
      None => return None
    }
  }
  Some(values)
}

///|
fn bw_tube_terms(w : ModuleBinWriter, values : Array[DTubeTerm]) -> Unit {
  bw_i32(w, values.length())
  for i in 0..<values.length() {
    bw_face(w, values[i].face)
    bw_term(w, values[i].body)
  }
}

///|
fn br_tube_terms(r : ModuleBinReader, depth : Int32) -> Array[DTubeTerm]? {
  let count = br_count(r)
  if !br_require_ok(r) {
    return None
  }
  let values : Array[DTubeTerm] = []
  for _i in 0..<count {
    let face = match br_face(r, depth + 1) {
      Some(v) => v
      None => return None
    }
    let body = match br_term(r, depth + 1) {
      Some(v) => v
      None => return None
    }
    values.push(DTubeTerm::{ face, body, })
  }
  Some(values)
}

///|
fn bw_face_terms(w : ModuleBinWriter, values : Array[DFaceTerm]) -> Unit {
  bw_i32(w, values.length())
  for i in 0..<values.length() {
    bw_face(w, values[i].face)
    bw_term(w, values[i].body)
  }
}

///|
fn br_face_terms(r : ModuleBinReader, depth : Int32) -> Array[DFaceTerm]? {
  let count = br_count(r)
  if !br_require_ok(r) {
    return None
  }
  let values : Array[DFaceTerm] = []
  for _i in 0..<count {
    let face = match br_face(r, depth + 1) {
      Some(v) => v
      None => return None
    }
    let body = match br_term(r, depth + 1) {
      Some(v) => v
      None => return None
    }
    values.push(DFaceTerm::{ face, body, })
  }
  Some(values)
}

///|
fn bw_equiv_branches(w : ModuleBinWriter, values : Array[DEquivBranch]) -> Unit {
  bw_i32(w, values.length())
  for i in 0..<values.length() {
    bw_face(w, values[i].face)
    bw_term(w, values[i].ty)
    bw_term(w, values[i].equiv)
  }
}

///|
fn br_equiv_branches(
  r : ModuleBinReader,
  depth : Int32,
) -> Array[DEquivBranch]? {
  let count = br_count(r)
  if !br_require_ok(r) {
    return None
  }
  let values : Array[DEquivBranch] = []
  for _i in 0..<count {
    let face = match br_face(r, depth + 1) {
      Some(v) => v
      None => return None
    }
    let ty = match br_term(r, depth + 1) {
      Some(v) => v
      None => return None
    }
    let equiv = match br_term(r, depth + 1) {
      Some(v) => v
      None => return None
    }
    values.push(DEquivBranch::{ face, ty, equiv, })
  }
  Some(values)
}

///|
fn bw_telescope(w : ModuleBinWriter, values : Array[DTelescopeEntry]) -> Unit {
  bw_i32(w, values.length())
  for i in 0..<values.length() {
    bw_string(w, values[i].name)
    bw_term(w, values[i].ty)
  }
}

///|
fn br_telescope(r : ModuleBinReader, depth : Int32) -> Array[DTelescopeEntry]? {
  let count = br_count(r)
  if !br_require_ok(r) {
    return None
  }
  let values : Array[DTelescopeEntry] = []
  for _i in 0..<count {
    let name = match br_string(r) {
      Some(v) => v
      None => return None
    }
    let ty = match br_term(r, depth + 1) {
      Some(v) => v
      None => return None
    }
    values.push(DTelescopeEntry::{ name, ty, })
  }
  Some(values)
}

///|
fn bw_arg_kind(w : ModuleBinWriter, value : DArgKind) -> Unit {
  match value {
    DArgExternal => bw_u8(w, 0)
    DArgRecursive => bw_u8(w, 1)
    DArgFunction => bw_u8(w, 2)
    DArgNested => bw_u8(w, 3)
    DArgDecoded => bw_u8(w, 4)
    DArgDecodedFunction => bw_u8(w, 5)
  }
}

///|
fn br_arg_kind(r : ModuleBinReader) -> DArgKind? {
  match br_u8(r) {
    0 => Some(DArgExternal)
    1 => Some(DArgRecursive)
    2 => Some(DArgFunction)
    3 => Some(DArgNested)
    4 => Some(DArgDecoded)
    5 => Some(DArgDecodedFunction)
    _ => {
      if r.status == ModuleBinaryOk {
        r.status = ModuleBinaryMalformed
      }
      None
    }
  }
}

///|
fn bw_positive_functor(w : ModuleBinWriter, value : DPositiveFunctor) -> Unit {
  match value {
    DFunctorIdentity(terms) => {
      bw_u8(w, 0)
      bw_terms(w, terms)
    }
    DFunctorConst(term) => {
      bw_u8(w, 1)
      bw_term(w, term)
    }
    DFunctorProduct(a, b) => {
      bw_u8(w, 2)
      bw_positive_functor(w, a)
      bw_positive_functor(w, b)
    }
    DFunctorSum(a, b) => {
      bw_u8(w, 3)
      bw_positive_functor(w, a)
      bw_positive_functor(w, b)
    }
    DFunctorList(a) => {
      bw_u8(w, 4)
      bw_positive_functor(w, a)
    }
    DFunctorPi(term, a) => {
      bw_u8(w, 5)
      bw_term(w, term)
      bw_positive_functor(w, a)
    }
    DFunctorContainer(a, b, terms) => {
      bw_u8(w, 6)
      bw_term(w, a)
      bw_term(w, b)
      bw_terms(w, terms)
    }
    DFunctorSigma(a, b) => {
      bw_u8(w, 7)
      bw_positive_functor(w, a)
      bw_positive_functor(w, b)
    }
    DFunctorFamily(spec, pargs, index) => {
      // Tag 8 exists only in layout version 2; the reader gate
      // below rejects it in v1 payloads, which is also what makes
      // `compiled_module_to_binary_v1` refuse such modules.
      bw_u8(w, 8)
      bw_inductive_spec(w, spec)
      bw_i32(w, pargs.length())
      for i in 0..<pargs.length() {
        match pargs[i] {
          DFunctorParamTerm(t) => {
            bw_u8(w, 0)
            bw_term(w, t)
          }
          DFunctorParamSelf(js) => {
            bw_u8(w, 1)
            bw_terms(w, js)
          }
        }
      }
      bw_terms(w, index)
    }
    DFunctorSelfFamily(pargs, index) => {
      // Tag 9, layout version 3 and above: parameter arguments
      // and indices, with no target spec (the enclosing
      // declaration is the target).
      bw_u8(w, 9)
      bw_i32(w, pargs.length())
      for i in 0..<pargs.length() {
        match pargs[i] {
          DFunctorParamTerm(t) => {
            bw_u8(w, 0)
            bw_term(w, t)
          }
          DFunctorParamSelf(js) => {
            bw_u8(w, 1)
            bw_terms(w, js)
          }
        }
      }
      bw_terms(w, index)
    }
  }
}

///|
fn br_positive_functor(r : ModuleBinReader, depth : Int32) -> DPositiveFunctor? {
  if br_depth_failed(r, depth) {
    return None
  }
  match br_u8(r) {
    0 =>
      match br_terms(r, depth + 1) {
        Some(v) => Some(DFunctorIdentity(v))
        None => None
      }
    1 =>
      match br_term(r, depth + 1) {
        Some(v) => Some(DFunctorConst(v))
        None => None
      }
    2 => {
      let a = match br_positive_functor(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      let b = match br_positive_functor(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      Some(DFunctorProduct(a, b))
    }
    3 => {
      let a = match br_positive_functor(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      let b = match br_positive_functor(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      Some(DFunctorSum(a, b))
    }
    4 =>
      match br_positive_functor(r, depth + 1) {
        Some(v) => Some(DFunctorList(v))
        None => None
      }
    5 => {
      let term = match br_term(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      let inner = match br_positive_functor(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      Some(DFunctorPi(term, inner))
    }
    6 => {
      let a = match br_term(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      let b = match br_term(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      let terms = match br_terms(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      Some(DFunctorContainer(a, b, terms))
    }
    7 => {
      let a = match br_positive_functor(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      let b = match br_positive_functor(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      Some(DFunctorSigma(a, b))
    }
    8 => {
      if r.version < 2 {
        if r.status == ModuleBinaryOk {
          r.status = ModuleBinaryUnsupportedVersion
        }
        return None
      }
      let spec = match br_inductive_spec(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      let count = br_i32(r)
      if !br_require_ok(r) || count < 0 || count > 4096 {
        return None
      }
      let pargs : Array[DFunctorParamArg] = []
      for _i in 0..<count {
        match br_u8(r) {
          0 => {
            let t = match br_term(r, depth + 1) {
              Some(v) => v
              None => return None
            }
            pargs.push(DFunctorParamTerm(t))
          }
          1 => {
            let js = match br_terms(r, depth + 1) {
              Some(v) => v
              None => return None
            }
            pargs.push(DFunctorParamSelf(js))
          }
          _ => return None
        }
      }
      let index = match br_terms(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      Some(DFunctorFamily(spec, pargs, index))
    }
    9 => {
      if r.version < 3 {
        if r.status == ModuleBinaryOk {
          r.status = ModuleBinaryUnsupportedVersion
        }
        return None
      }
      let count = br_i32(r)
      if !br_require_ok(r) || count < 0 || count > 4096 {
        return None
      }
      let pargs : Array[DFunctorParamArg] = []
      for _i in 0..<count {
        match br_u8(r) {
          0 => {
            let t = match br_term(r, depth + 1) {
              Some(v) => v
              None => return None
            }
            pargs.push(DFunctorParamTerm(t))
          }
          1 => {
            let js = match br_terms(r, depth + 1) {
              Some(v) => v
              None => return None
            }
            pargs.push(DFunctorParamSelf(js))
          }
          _ => return None
        }
      }
      let index = match br_terms(r, depth + 1) {
        Some(v) => v
        None => return None
      }
      Some(DFunctorSelfFamily(pargs, index))
    }
    _ => {
      if r.status == ModuleBinaryOk {
        r.status = ModuleBinaryMalformed
      }
      None
    }
  }
}

///|
fn bw_constraints(
  w : ModuleBinWriter,
  values : Array[DConstructorConstraint],
) -> Unit {
  bw_i32(w, values.length())
  for i in 0..<values.length() {
    bw_term(w, values[i].ty)
    bw_term(w, values[i].lhs)
    bw_term(w, values[i].rhs)
  }
}

///|
fn br_constraints(
  r : ModuleBinReader,
  depth : Int32,
) -> Array[DConstructorConstraint]? {
  let count = br_count(r)
  if !br_require_ok(r) {
    return None
  }
  let values : Array[DConstructorConstraint] = []
  for _i in 0..<count {
    let ty = match br_term(r, depth + 1) {
      Some(v) => v
      None => return None
    }
    let lhs = match br_term(r, depth + 1) {
      Some(v) => v
      None => return None
    }
    let rhs = match br_term(r, depth + 1) {
      Some(v) => v
      None => return None
    }
    values.push(DConstructorConstraint::{ ty, lhs, rhs, })
  }
  Some(values)
}

///|
fn bw_constructor_args(
  w : ModuleBinWriter,
  values : Array[DConstructorArg],
) -> Unit {
  bw_i32(w, values.length())
  for i in 0..<values.length() {
    bw_string(w, values[i].name)
    bw_arg_kind(w, values[i].kind)
    bw_term(w, values[i].ty)
    bw_terms(w, values[i].index)
    bw_positive_functor(w, values[i].nested)
    bw_i32(w, values[i].target)
  }
}

///|
fn br_constructor_args(
  r : ModuleBinReader,
  depth : Int32,
) -> Array[DConstructorArg]? {
  let count = br_count(r)
  if !br_require_ok(r) {
    return None
  }
  let values : Array[DConstructorArg] = []
  for _i in 0..<count {
    let name = match br_string(r) {
      Some(v) => v
      None => return None
    }
    let kind = match br_arg_kind(r) {
      Some(v) => v
      None => return None
    }
    let ty = match br_term(r, depth + 1) {
      Some(v) => v
      None => return None
    }
    let index = match br_terms(r, depth + 1) {
      Some(v) => v
      None => return None
    }
    let nested = match br_positive_functor(r, depth + 1) {
      Some(v) => v
      None => return None
    }
    let target = br_i32(r)
    if !br_require_ok(r) {
      return None
    }
    values.push(DConstructorArg::{ name, kind, ty, index, nested, target, })
  }
  Some(values)
}

///|
fn bw_constructor_specs(
  w : ModuleBinWriter,
  values : Array[DConstructorSpec],
) -> Unit {
  bw_i32(w, values.length())
  for i in 0..<values.length() {
    bw_string(w, values[i].name)
    bw_constructor_args(w, values[i].args)
    bw_terms(w, values[i].result_index)
    bw_constraints(w, values[i].constraints)
  }
}

///|
fn br_constructor_specs(
  r : ModuleBinReader,
  depth : Int32,
) -> Array[DConstructorSpec]? {
  let count = br_count(r)
  if !br_require_ok(r) {
    return None
  }
  let values : Array[DConstructorSpec] = []
  for _i in 0..<count {
    let name = match br_string(r) {
      Some(v) => v
      None => return None
    }
    let args = match br_constructor_args(r, depth + 1) {
      Some(v) => v
      None => return None
    }
    let result_index = match br_terms(r, depth + 1) {
      Some(v) => v
      None => return None
    }
    let constraints = match br_constraints(r, depth + 1) {
      Some(v) => v
      None => return None
    }
    values.push(DConstructorSpec::{ name, args, result_index, constraints, })
  }
  Some(values)
}

///|
fn bw_inductive_spec(w : ModuleBinWriter, value : DInductiveSpec) -> Unit {
  bw_string(w, value.name)
  bw_i32(w, value.level)
  bw_telescope(w, value.params)
  bw_telescope(w, value.indices)
  bw_constructor_specs(w, value.constructors)
  bw_terms(w, value.decode_cases)
  bw_i32(w, value.decode_level)
}

///|
fn br_inductive_spec(r : ModuleBinReader, depth : Int32) -> DInductiveSpec? {
  if br_depth_failed(r, depth) {
    return None
  }
  let name = match br_string(r) {
    Some(v) => v
    None => return None
  }
  let level = br_i32(r)
  if !br_require_ok(r) {
    return None
  }
  let params = match br_telescope(r, depth + 1) {
    Some(v) => v
    None => return None
  }
  let indices = match br_telescope(r, depth + 1) {
    Some(v) => v
    None => return None
  }
  let constructors = match br_constructor_specs(r, depth + 1) {
    Some(v) => v
    None => return None
  }
  let decode_cases = match br_terms(r, depth + 1) {
    Some(v) => v
    None => return None
  }
  let decode_level = br_i32(r)
  if !br_require_ok(r) {
    return None
  }
  Some(DInductiveSpec::{
    name,
    level,
    params,
    indices,
    constructors,
    decode_cases,
    decode_level,
  })
}

///|
fn bw_hit_face_exprs(w : ModuleBinWriter, values : Array[DHitFaceExpr]) -> Unit {
  bw_i32(w, values.length())
  for i in 0..<values.length() {
    bw_i32(w, values[i].cell)
    bw_terms(w, values[i].args)
    bw_dims(w, values[i].dims)
  }
}

///|
fn br_hit_face_exprs(
  r : ModuleBinReader,
  depth : Int32,
) -> Array[DHitFaceExpr]? {
  let count = br_count(r)
  if !br_require_ok(r) {
    return None
  }
  let values : Array[DHitFaceExpr] = []
  for _i in 0..<count {
    let cell = br_i32(r)
    if !br_require_ok(r) {
      return None
    }
    let args = match br_terms(r, depth + 1) {
      Some(v) => v
      None => return None
    }
    let dims = match br_dims(r, depth + 1) {
      Some(v) => v
      None => return None
    }
    values.push(DHitFaceExpr::{ cell, args, dims, })
  }
  Some(values)
}

///|
fn bw_hit_cell_specs(w : ModuleBinWriter, values : Array[DHitCellSpec]) -> Unit {
  bw_i32(w, values.length())
  for i in 0..<values.length() {
    bw_string(w, values[i].name)
    bw_i32(w, values[i].dim_count)
    bw_constructor_args(w, values[i].args)
    bw_terms(w, values[i].result_index)
    bw_hit_face_exprs(w, values[i].faces)
    bw_constraints(w, values[i].constraints)
  }
}

///|
fn br_hit_cell_specs(
  r : ModuleBinReader,
  depth : Int32,
) -> Array[DHitCellSpec]? {
  let count = br_count(r)
  if !br_require_ok(r) {
    return None
  }
  let values : Array[DHitCellSpec] = []
  for _i in 0..<count {
    let name = match br_string(r) {
      Some(v) => v
      None => return None
    }
    let dim_count = br_i32(r)
    if !br_require_ok(r) {
      return None
    }
    let args = match br_constructor_args(r, depth + 1) {
      Some(v) => v
      None => return None
    }
    let result_index = match br_terms(r, depth + 1) {
      Some(v) => v
      None => return None
    }
    let faces = match br_hit_face_exprs(r, depth + 1) {
      Some(v) => v
      None => return None
    }
    let constraints = match br_constraints(r, depth + 1) {
      Some(v) => v
      None => return None
    }
    values.push(DHitCellSpec::{
      name,
      dim_count,
      args,
      result_index,
      faces,
      constraints,
    })
  }
  Some(values)
}

///|
fn bw_hit_spec(w : ModuleBinWriter, value : DHitSpec) -> Unit {
  bw_string(w, value.name)
  bw_i32(w, value.level)
  bw_telescope(w, value.params)
  bw_telescope(w, value.indices)
  bw_hit_cell_specs(w, value.cells)
}

///|
fn br_hit_spec(r : ModuleBinReader, depth : Int32) -> DHitSpec? {
  if br_depth_failed(r, depth) {
    return None
  }
  let name = match br_string(r) {
    Some(v) => v
    None => return None
  }
  let level = br_i32(r)
  if !br_require_ok(r) {
    return None
  }
  let params = match br_telescope(r, depth + 1) {
    Some(v) => v
    None => return None
  }
  let indices = match br_telescope(r, depth + 1) {
    Some(v) => v
    None => return None
  }
  let cells = match br_hit_cell_specs(r, depth + 1) {
    Some(v) => v
    None => return None
  }
  Some(DHitSpec::{ name, level, params, indices, cells, })
}

///|
fn bw_module_entries(w : ModuleBinWriter, values : Array[ModuleEntry]) -> Unit {
  bw_i32(w, values.length())
  for i in 0..<values.length() {
    bw_string(w, values[i].canonical_name)
    bw_string(w, values[i].local_name)
    bw_string(w, values[i].source_module)
    bw_term(w, values[i].ty)
    match values[i].body {
      Some(body) => {
        bw_bool(w, true)
        bw_term(w, body)
      }
      None => bw_bool(w, false)
    }
    bw_bool(w, values[i].exported)
    bw_bool(w, values[i].transparent)
  }
}

///|
fn br_module_entries(r : ModuleBinReader, depth : Int32) -> Array[ModuleEntry]? {
  let count = br_count(r)
  if !br_require_ok(r) {
    return None
  }
  let values : Array[ModuleEntry] = []
  for _i in 0..<count {
    let canonical_name = match br_string(r) {
      Some(v) => v
      None => return None
    }
    let local_name = match br_string(r) {
      Some(v) => v
      None => return None
    }
    let source_module = match br_string(r) {
      Some(v) => v
      None => return None
    }
    let ty = match br_term(r, depth + 1) {
      Some(v) => v
      None => return None
    }
    let has_body = br_bool(r)
    if !br_require_ok(r) {
      return None
    }
    let body : DTerm? = if has_body {
      match br_term(r, depth + 1) {
        Some(v) => Some(v)
        None => return None
      }
    } else {
      None
    }
    let exported = br_bool(r)
    let transparent = br_bool(r)
    if !br_require_ok(r) {
      return None
    }
    values.push(ModuleEntry::{
      canonical_name,
      local_name,
      source_module,
      ty,
      body,
      exported,
      transparent,
    })
  }
  Some(values)
}

///|
fn bw_module_exports(w : ModuleBinWriter, values : Array[ModuleExport]) -> Unit {
  bw_i32(w, values.length())
  for i in 0..<values.length() {
    bw_string(w, values[i].name)
    bw_i32(w, values[i].ordinal)
    bw_bool(w, values[i].transparent)
  }
}

///|
fn br_module_exports(r : ModuleBinReader) -> Array[ModuleExport]? {
  let count = br_count(r)
  if !br_require_ok(r) {
    return None
  }
  let values : Array[ModuleExport] = []
  for _i in 0..<count {
    let name = match br_string(r) {
      Some(v) => v
      None => return None
    }
    let ordinal = br_i32(r)
    let transparent = br_bool(r)
    if !br_require_ok(r) {
      return None
    }
    values.push(ModuleExport::{ name, ordinal, transparent, })
  }
  Some(values)
}

///|
fn bw_dependencies(
  w : ModuleBinWriter,
  values : Array[ModuleDependencyFingerprint],
) -> Unit {
  bw_i32(w, values.length())
  for i in 0..<values.length() {
    bw_string(w, values[i].path)
    bw_i32(w, values[i].interface_hash)
  }
}

///|
fn br_dependencies(r : ModuleBinReader) -> Array[ModuleDependencyFingerprint]? {
  let count = br_count(r)
  if !br_require_ok(r) {
    return None
  }
  let values : Array[ModuleDependencyFingerprint] = []
  for _i in 0..<count {
    let path = match br_string(r) {
      Some(v) => v
      None => return None
    }
    let interface_hash = br_i32(r)
    if !br_require_ok(r) {
      return None
    }
    values.push(ModuleDependencyFingerprint::{ path, interface_hash, })
  }
  Some(values)
}

///|
fn bw_compiled_payload_versioned(
  w : ModuleBinWriter,
  compiled : CompiledModule,
  version : Int32,
) -> Unit {
  bw_i32(w, compiled.format_version)
  bw_string(w, compiled.module_path)
  bw_telescope(w, compiled.params)
  bw_module_entries(w, compiled.entries)
  bw_module_exports(w, compiled.exports)
  bw_dependencies(w, compiled.dependencies)
  bw_i32(w, compiled.interface_hash)
  bw_i32(w, compiled.implementation_hash)
  bw_string(w, compiled.interface_encoding)
  if version >= 2 {
    bw_string(w, compiled.producer)
  }
}

///|
fn br_compiled_payload(r : ModuleBinReader) -> CompiledModule? {
  let format_version = br_i32(r)
  if !br_require_ok(r) {
    return None
  }
  let module_path = match br_string(r) {
    Some(v) => v
    None => return None
  }
  let params = match br_telescope(r, 0) {
    Some(v) => v
    None => return None
  }
  let entries = match br_module_entries(r, 0) {
    Some(v) => v
    None => return None
  }
  let exports = match br_module_exports(r) {
    Some(v) => v
    None => return None
  }
  let dependencies = match br_dependencies(r) {
    Some(v) => v
    None => return None
  }
  let interface_hash = br_i32(r)
  let implementation_hash = br_i32(r)
  if !br_require_ok(r) {
    return None
  }
  let interface_encoding = match br_string(r) {
    Some(v) => v
    None => return None
  }
  let producer = if r.version >= 2 {
    match br_string(r) {
      Some(v) => v
      None => return None
    }
  } else {
    ""
  }
  Some(CompiledModule::{
    format_version,
    module_path,
    params,
    entries,
    exports,
    dependencies,
    interface_hash,
    implementation_hash,
    interface_encoding,
    producer,
  })
}

///|
fn module_binary_checksum(bytes : Array[Int32]) -> Int32 {
  let mut hash = 5381
  for i in 0..<bytes.length() {
    hash = (hash * 33) ^ (bytes[i] & 255)
  }
  hash
}

///|
fn module_binary_u16_at(bytes : Array[Int32], offset : Int32) -> Int32 {
  (bytes[offset] & 255) | ((bytes[offset + 1] & 255) << 8)
}

///|
fn module_binary_i32_at(bytes : Array[Int32], offset : Int32) -> Int32 {
  (bytes[offset] & 255) |
  ((bytes[offset + 1] & 255) << 8) |
  ((bytes[offset + 2] & 255) << 16) |
  ((bytes[offset + 3] & 255) << 24)
}

///|
/// Serialize a compiled module in the stable binary format.  The
/// resulting array contains one byte (0--255) per element and is
/// suitable for writing to disk unchanged.
fn compiled_module_to_binary_versioned(
  compiled : CompiledModule,
  version : Int32,
) -> Array[Int32] {
  let payload_writer = module_bin_writer_new_versioned(version)
  bw_compiled_payload_versioned(payload_writer, compiled, version)
  let payload = payload_writer.bytes
  let writer = module_bin_writer_new()
  for byte in [67, 72, 77, 79, 68, 66, 73, 78] {
    bw_u8(writer, byte)
  }
  bw_u8(writer, version)
  bw_u8(writer, version >> 8)
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
pub fn compiled_module_to_binary(compiled : CompiledModule) -> Array[Int32] {
  compiled_module_to_binary_versioned(
    compiled,
    compiled_module_binary_format_version(),
  )
}

///|
/// Serialize at a requested supported layout version.  Returns
/// `None` when the module uses features the requested version
/// cannot express (for example a tag-9 self-family functor node
/// below version 3, or a tag-8 family node below version 2):
/// the candidate bytes are parsed back under that version's
/// rules and must reproduce the module's interface encoding and
/// entry encodings exactly (the producer stamp, absent in v1,
/// is the one field not compared).
pub fn compiled_module_to_binary_version(
  compiled : CompiledModule,
  version : Int32,
) -> Array[Int32]? {
  if !contains_int(compiled_module_binary_supported_versions(), version) {
    return None
  }
  let bytes = compiled_module_to_binary_versioned(compiled, version)
  match compiled_module_from_binary(bytes) {
    Some(back) =>
      if back.module_path == compiled.module_path &&
        back.params == compiled.params &&
        back.entries == compiled.entries &&
        back.exports == compiled.exports &&
        back.dependencies == compiled.dependencies &&
        back.interface_encoding == compiled.interface_encoding &&
        back.interface_hash == compiled.interface_hash &&
        back.implementation_hash == compiled.implementation_hash {
        Some(bytes)
      } else {
        None
      }
    None => None
  }
}

///|
/// Serialize in the legacy version 1 layout.
pub fn compiled_module_to_binary_v1(compiled : CompiledModule) -> Array[Int32]? {
  compiled_module_to_binary_version(compiled, 1)
}

///|
/// Serialize for a peer advertising `peer_versions`: the highest
/// mutually supported version that can express this module is
/// used, trying lower common versions when a higher one cannot
/// (which in practice means the negotiated version already
/// decides).  `None` when no common version can express it.
pub fn compiled_module_to_binary_for_peer(
  compiled : CompiledModule,
  peer_versions : Array[Int32],
) -> Array[Int32]? {
  let supported = compiled_module_binary_supported_versions()
  let mut index = supported.length() - 1
  while index >= 0 {
    let version = supported[index]
    if contains_int(peer_versions, version) {
      match compiled_module_to_binary_version(compiled, version) {
        Some(bytes) => return Some(bytes)
        None => ()
      }
    }
    index = index - 1
  }
  None
}

///|
/// Migrate a binary blob of any supported layout version to the
/// current layout: the object is parsed and semantically
/// validated, stamped with the default producer when it carries
/// none, and re-emitted.  `None` when the input is not a valid,
/// supported compiled module.
pub fn compiled_module_migrate_binary(bytes : Array[Int32]) -> Array[Int32]? {
  let compiled = match compiled_module_load_binary(bytes) {
    Some(v) => v
    None => return None
  }
  if compiled.producer.length() == 0 {
    let stamped = CompiledModule::{
      format_version: compiled.format_version,
      module_path: compiled.module_path,
      params: compiled.params,
      entries: compiled.entries,
      exports: compiled.exports,
      dependencies: compiled.dependencies,
      interface_hash: compiled.interface_hash,
      implementation_hash: compiled.implementation_hash,
      interface_encoding: compiled.interface_encoding,
      producer: compiled_module_producer_default(),
    }
    Some(compiled_module_to_binary(stamped))
  } else {
    Some(compiled_module_to_binary(compiled))
  }
}

///|
fn module_binary_failure(status : ModuleBinaryStatus) -> ModuleBinaryLoad {
  { status, module_: None, }
}

///|
/// Parse a compiled module, reporting a precise format status.
/// With `validate=true`, the parsed object is additionally checked
/// by `compiled_module_validate` (hashes plus re-elaboration of its
/// synthetic module definition).
pub fn compiled_module_load_binary_report(
  bytes : Array[Int32],
  validate~ : Bool = true,
) -> ModuleBinaryLoad {
  for i in 0..<bytes.length() {
    if bytes[i] < 0 || bytes[i] > 255 {
      return module_binary_failure(ModuleBinaryMalformed)
    }
  }
  if bytes.length() < 20 {
    return module_binary_failure(ModuleBinaryTruncated)
  }
  let magic = [67, 72, 77, 79, 68, 66, 73, 78]
  for i in 0..<magic.length() {
    if bytes[i] != magic[i] {
      return module_binary_failure(ModuleBinaryBadMagic)
    }
  }
  let header_version = module_binary_u16_at(bytes, 8)
  if (header_version != 1 && header_version != 2 && header_version != 3) ||
    module_binary_u16_at(bytes, 10) != 0 {
    return module_binary_failure(ModuleBinaryUnsupportedVersion)
  }
  let payload_length = module_binary_i32_at(bytes, 12)
  if payload_length < 0 {
    return module_binary_failure(ModuleBinaryMalformed)
  }
  if bytes.length() < 20 + payload_length {
    return module_binary_failure(ModuleBinaryTruncated)
  }
  if bytes.length() > 20 + payload_length {
    return module_binary_failure(ModuleBinaryTrailingBytes)
  }
  let payload : Array[Int32] = []
  for i in 20..<bytes.length() {
    payload.push(bytes[i])
  }
  if module_binary_checksum(payload) != module_binary_i32_at(bytes, 16) {
    return module_binary_failure(ModuleBinaryChecksumMismatch)
  }
  let reader = module_bin_reader_new_versioned(payload, header_version)
  let compiled = match br_compiled_payload(reader) {
    Some(v) => v
    None => return module_binary_failure(reader.status)
  }
  if reader.pos != payload.length() {
    return module_binary_failure(ModuleBinaryTrailingBytes)
  }
  if validate && !compiled_module_validate(compiled) {
    return module_binary_failure(ModuleBinaryValidationFailed)
  }
  { status: ModuleBinaryOk, module_: Some(compiled), }
}

///|
/// Structural parse without semantic validation.
pub fn compiled_module_from_binary(bytes : Array[Int32]) -> CompiledModule? {
  compiled_module_load_binary_report(bytes, validate=false).module_
}

///|
/// Parse and semantically validate a binary compiled module.
pub fn compiled_module_load_binary(bytes : Array[Int32]) -> CompiledModule? {
  compiled_module_load_binary_report(bytes, validate=true).module_
}

///|
/// Lowercase hexadecimal file representation of binary bytes.
pub fn compiled_module_binary_to_hex(bytes : Array[Int32]) -> String {
  let digits = "0123456789abcdef"
  let builder = StringBuilder(size_hint=bytes.length() * 2)
  for i in 0..<bytes.length() {
    let byte = bytes[i] & 255
    builder.write_char(digits[byte >> 4].to_int().unsafe_to_char())
    builder.write_char(digits[byte & 15].to_int().unsafe_to_char())
  }
  builder.to_string()
}

///|
fn module_hex_value(unit : Int32) -> Int32 {
  if unit >= 48 && unit <= 57 {
    unit - 48
  } else if unit >= 97 && unit <= 102 {
    unit - 87
  } else if unit >= 65 && unit <= 70 {
    unit - 55
  } else {
    -1
  }
}

///|
/// Parse the hexadecimal representation produced above.  ASCII
/// whitespace is ignored; an odd number of digits is rejected.
pub fn compiled_module_binary_from_hex(text : String) -> Array[Int32]? {
  let digits : Array[Int32] = []
  for i in 0..<text.length() {
    let unit = text[i].to_int()
    if unit == 32 || unit == 9 || unit == 10 || unit == 13 {
      continue
    }
    let value = module_hex_value(unit)
    if value < 0 {
      return None
    }
    digits.push(value)
  }
  if digits.length() % 2 != 0 {
    return None
  }
  let bytes : Array[Int32] = []
  for i = 0; i < digits.length(); i = i + 2 {
    bytes.push((digits[i] << 4) | digits[i + 1])
  }
  Some(bytes)
}

///|
/// Round-trip and tamper-evidence checks, including linking a
/// client against a module recovered solely from serialized bytes.
pub fn check_module_binary_format() -> Bool {
  let implementation = match
    module_compile(module_env_new(), point_implementation_module(), []) {
    Some(v) => v
    None => return false
  }
  let generic_env = compiled_module_env_new()
  let bool_compiled = match
    module_compile(module_env_new(), bool_ops_module(), []) {
    Some(v) => v
    None => return false
  }
  if !compiled_module_env_add(generic_env, bool_compiled) {
    return false
  }
  let generic = match
    module_compile_with_compiled(generic_env, generic_iterate_module()) {
    Some(v) => v
    None => return false
  }
  for compiled in [implementation, generic] {
    let bytes = compiled_module_to_binary(compiled)
    if bytes.length() <= 20 {
      return false
    }
    match compiled_module_load_binary(bytes) {
      Some(parsed) =>
        if parsed != compiled || !compiled_module_validate(parsed) {
          return false
        }
      None => return false
    }
    let hex = compiled_module_binary_to_hex(bytes)
    match compiled_module_binary_from_hex(hex) {
      Some(decoded) => if decoded != bytes { return false }
      None => return false
    }
    let tampered : Array[Int32] = []
    for i in 0..<bytes.length() {
      tampered.push(bytes[i])
    }
    tampered[tampered.length() - 1] = (tampered[tampered.length() - 1] + 1) %
      256
    if compiled_module_load_binary_report(tampered).status !=
      ModuleBinaryChecksumMismatch {
      return false
    }
    let truncated : Array[Int32] = []
    for i in 0..<(bytes.length() - 1) {
      truncated.push(bytes[i])
    }
    if compiled_module_load_binary_report(truncated).status !=
      ModuleBinaryTruncated {
      return false
    }
  }
  // Recover the implementation from bytes and link the client
  // against the recovered object alone.
  let recovered = match
    compiled_module_load_binary(compiled_module_to_binary(implementation)) {
    Some(v) => v
    None => return false
  }
  let env = compiled_module_env_new()
  if !compiled_module_env_add(env, recovered) {
    return false
  }
  let instance = match module_link_instantiate(env, point_client_module(), []) {
    Some(v) => v
    None => return false
  }
  let answer = match module_instance_find(instance, "answer") {
    Some(v) => v
    None => return false
  }
  dep_nf_closed(answer.body, DBoolTy) == Some(DBoolLit(true))
}

///|
/// An in-memory byte-store cache of compiled modules, keyed by
/// module path.  `put` serializes at the current layout version;
/// `get` parses and semantically validates the stored bytes, so
/// a corrupted or stale blob registers as a miss rather than a
/// bad object.  Hit/miss counters make the cache policy
/// observable to tests and diagnostics.
pub struct CompiledModuleStore {
  blobs : Array[(String, Array[Int32])]
  mut hits : Int32
  mut misses : Int32
}

///|
pub struct CompiledModuleStoreStats {
  entries : Int32
  total_bytes : Int32
  hits : Int32
  misses : Int32
} derive(Debug, Eq)

///|
pub extend CompiledModuleStoreStats with @moonbitlang/core/debug.Debug::{
  to_repr,
}

///|
pub extend CompiledModuleStoreStats with Eq::{not_equal, equal}

///|
pub fn compiled_module_store_new() -> CompiledModuleStore {
  { blobs: [], hits: 0, misses: 0, }
}

///|
pub fn compiled_module_store_put(
  store : CompiledModuleStore,
  compiled : CompiledModule,
) -> Unit {
  let kept : Array[(String, Array[Int32])] = []
  for i in 0..<store.blobs.length() {
    if store.blobs[i].0 != compiled.module_path {
      kept.push(store.blobs[i])
    }
  }
  while store.blobs.length() > 0 {
    ignore(store.blobs.pop())
  }
  for i in 0..<kept.length() {
    store.blobs.push(kept[i])
  }
  store.blobs.push((compiled.module_path, compiled_module_to_binary(compiled)))
}

///|
pub fn compiled_module_store_get(
  store : CompiledModuleStore,
  module_path : String,
) -> CompiledModule? {
  for i in 0..<store.blobs.length() {
    if store.blobs[i].0 == module_path {
      match compiled_module_load_binary(store.blobs[i].1) {
        Some(compiled) =>
          if compiled.module_path == module_path {
            store.hits = store.hits + 1
            return Some(compiled)
          }
        None => ()
      }
      store.misses = store.misses + 1
      return None
    }
  }
  store.misses = store.misses + 1
  None
}

///|
pub fn compiled_module_store_contains(
  store : CompiledModuleStore,
  module_path : String,
) -> Bool {
  for i in 0..<store.blobs.length() {
    if store.blobs[i].0 == module_path {
      return true
    }
  }
  false
}

///|
pub fn compiled_module_store_stats(
  store : CompiledModuleStore,
) -> CompiledModuleStoreStats {
  let mut total = 0
  for i in 0..<store.blobs.length() {
    total = total + store.blobs[i].1.length()
  }
  {
    entries: store.blobs.length(),
    total_bytes: total,
    hits: store.hits,
    misses: store.misses,
  }
}

///|
/// Phase 11 verification of the versioned binary format and the
/// byte-store cache: v2 is the written layout and round-trips;
/// legacy v1 blobs are produced for v1-expressible modules, are
/// accepted by the loader, and migrate to v2 preserving the
/// object (with the producer stamped); an unknown header version
/// is rejected; the store records hits and misses and validates
/// on read.
pub fn check_module_binary_versions_and_store() -> Bool {
  let compiled = match module_compile(module_env_new(), bool_ops_module(), []) {
    Some(v) => v
    None => return false
  }
  if compiled.producer != compiled_module_producer_default() ||
    compiled_module_binary_format_version() != 3 ||
    compiled_module_binary_supported_versions() != [1, 2, 3] {
    return false
  }
  let bytes = compiled_module_to_binary(compiled)
  if compiled_module_binary_version_of(bytes) != 3 ||
    compiled_module_binary_version_of([]) != -1 ||
    compiled_module_binary_version_of([1, 2, 3]) != -1 {
    return false
  }
  match compiled_module_load_binary(bytes) {
    Some(back) => if back != compiled { return false }
    None => return false
  }
  // Legacy v1: writable for this module, loadable, and migrates.
  let v1 = match compiled_module_to_binary_v1(compiled) {
    Some(b) => b
    None => return false
  }
  if compiled_module_binary_version_of(v1) != 1 {
    return false
  }
  let from_v1 = match compiled_module_load_binary(v1) {
    Some(v) => v
    None => return false
  }
  if from_v1.producer.length() != 0 ||
    from_v1.interface_hash != compiled.interface_hash ||
    from_v1.entries != compiled.entries {
    return false
  }
  let migrated = match compiled_module_migrate_binary(v1) {
    Some(b) => b
    None => return false
  }
  if compiled_module_binary_version_of(migrated) != 3 {
    return false
  }
  match compiled_module_load_binary(migrated) {
    Some(back) => if back != compiled { return false }
    None => return false
  }
  // Migration is the identity on current-version blobs.
  match compiled_module_migrate_binary(bytes) {
    Some(again) => if again != bytes { return false }
    None => return false
  }
  // An unknown header version is rejected precisely.
  let futuristic : Array[Int32] = []
  for i in 0..<bytes.length() {
    futuristic.push(bytes[i])
  }
  futuristic[8] = 4
  if compiled_module_load_binary_report(futuristic).status !=
    ModuleBinaryUnsupportedVersion ||
    compiled_module_migrate_binary(futuristic) != None {
    return false
  }
  // Byte-store cache.
  let store = compiled_module_store_new()
  if compiled_module_store_get(store, compiled.module_path) != None ||
    compiled_module_store_stats(store).misses != 1 {
    return false
  }
  compiled_module_store_put(store, compiled)
  if !compiled_module_store_contains(store, compiled.module_path) ||
    compiled_module_store_contains(store, "No.Such.Module") {
    return false
  }
  match compiled_module_store_get(store, compiled.module_path) {
    Some(back) => if back != compiled { return false }
    None => return false
  }
  let stats = compiled_module_store_stats(store)
  stats.entries == 1 &&
  stats.hits == 1 &&
  stats.misses == 1 &&
  stats.total_bytes == bytes.length()
}

// ---------------------------------------------------------------------------
// Phase 14: Unified shared-DAG bundle (`CHSHRBUN` v1) & forward-compatible
// TLV extension envelope (`CHMODENV` v1)
// ---------------------------------------------------------------------------

///|
/// Unified bundle persisting compiled modules together with a schema-registry
/// snapshot over a single shared v3 term-DAG table (`CHSHRBUN` v1).
pub struct SharedDagBundle {
  modules : Array[CompiledModule]
  registry : DSchemaRegistrySnapshot
}

///|
pub struct SharedDagBundleLoad {
  status : ModuleBinaryStatus
  bundle : SharedDagBundle?
  shared_term_entries : Int32
  interned_dag_nodes : Int32
  reused_dag_nodes : Int32
}

///|
fn shared_dag_bundle_magic() -> Array[Int32] {
  // ASCII `CHSHRBUN`
  [67, 72, 83, 72, 82, 66, 85, 78]
}

///|
/// Serialize a `SharedDagBundle` using ONE shared v3 `ModuleBinWriter` so
/// identical subterms occurring across multiple modules and schema specs are
/// stored once in the shared term table.
pub fn shared_dag_bundle_to_binary(bundle : SharedDagBundle) -> Array[Int32] {
  let pw = module_bin_writer_new_versioned(3)
  bw_i32(pw, bundle.modules.length())
  for m in bundle.modules {
    bw_compiled_payload_versioned(pw, m, 3)
  }
  bw_registry_snapshot_payload(pw, bundle.registry)
  let payload = pw.bytes
  let w = module_bin_writer_new()
  for b in shared_dag_bundle_magic() {
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
  w.bytes
}

///|
fn shared_dag_bundle_intern_module(
  table : DTermInternTable,
  m : CompiledModule,
) -> (Int32, Int32) {
  let mut added = 0
  let mut reused = 0
  let intern_one = (t : DTerm) => {
    let before = table.terms.length()
    ignore(dterm_intern_id(table, t))
    if table.terms.length() > before {
      added = added + (table.terms.length() - before)
    } else {
      reused = reused + 1
    }
  }
  for p in m.params {
    intern_one(p.ty)
  }
  for e in m.entries {
    intern_one(e.ty)
    match e.body {
      Some(b) => intern_one(b)
      None => ()
    }
  }
  (added, reused)
}

///|
/// Load and optionally validate a `SharedDagBundle` (`CHSHRBUN` v1), linking
/// all decoded module/schema terms into `intern_table` (or a fresh shared
/// `DTermInternTable` when omitted).
pub fn shared_dag_bundle_load_binary_report(
  bytes : Array[Int32],
  intern_table~ : DTermInternTable = dterm_intern_table_new(),
  validate~ : Bool = true,
) -> SharedDagBundleLoad {
  let fail = (st : ModuleBinaryStatus) => SharedDagBundleLoad::{
    status: st,
    bundle: None,
    shared_term_entries: 0,
    interned_dag_nodes: 0,
    reused_dag_nodes: 0,
  }
  for b in bytes {
    if b < 0 || b > 255 {
      return fail(ModuleBinaryMalformed)
    }
  }
  if bytes.length() < 20 {
    return fail(ModuleBinaryTruncated)
  }
  let magic = shared_dag_bundle_magic()
  for i in 0..<8 {
    if bytes[i] != magic[i] {
      return fail(ModuleBinaryBadMagic)
    }
  }
  if module_binary_u16_at(bytes, 8) != 1 || module_binary_u16_at(bytes, 10) != 0 {
    return fail(ModuleBinaryUnsupportedVersion)
  }
  let payload_len = module_binary_i32_at(bytes, 12)
  if payload_len < 0 {
    return fail(ModuleBinaryMalformed)
  }
  if bytes.length() < 20 + payload_len {
    return fail(ModuleBinaryTruncated)
  }
  if bytes.length() > 20 + payload_len {
    return fail(ModuleBinaryTrailingBytes)
  }
  let payload : Array[Int32] = []
  for i in 20..<bytes.length() {
    payload.push(bytes[i])
  }
  if module_binary_checksum(payload) != module_binary_i32_at(bytes, 16) {
    return fail(ModuleBinaryChecksumMismatch)
  }
  let r = module_bin_reader_new_versioned(payload, 3)
  let mod_count = br_count(r)
  if !br_require_ok(r) {
    return fail(r.status)
  }
  let modules : Array[CompiledModule] = []
  for _ in 0..<mod_count {
    match br_compiled_payload(r) {
      Some(m) => modules.push(m)
      None => return fail(r.status)
    }
  }
  let registry = match br_registry_snapshot_payload(r) {
    Some(reg) => reg
    None => return fail(r.status)
  }
  if r.pos != payload.length() {
    return fail(ModuleBinaryTrailingBytes)
  }
  if validate {
    for m in modules {
      if !compiled_module_validate(m) {
        return fail(ModuleBinaryValidationFailed)
      }
    }
  }
  let mut added_total = 0
  let mut reused_total = 0
  for m in modules {
    let (a, ru) = shared_dag_bundle_intern_module(intern_table, m)
    added_total = added_total + a
    reused_total = reused_total + ru
  }
  for spec in registry.inductive_specs {
    let dummy = DInductive(spec, [])
    let before = intern_table.terms.length()
    ignore(dterm_intern_id(intern_table, dummy))
    if intern_table.terms.length() > before {
      added_total = added_total + (intern_table.terms.length() - before)
    } else {
      reused_total = reused_total + 1
    }
  }
  for spec in registry.hit_specs {
    let dummy = DHitType(spec, [])
    let before = intern_table.terms.length()
    ignore(dterm_intern_id(intern_table, dummy))
    if intern_table.terms.length() > before {
      added_total = added_total + (intern_table.terms.length() - before)
    } else {
      reused_total = reused_total + 1
    }
  }
  SharedDagBundleLoad::{
    status: ModuleBinaryOk,
    bundle: Some(SharedDagBundle::{ modules, registry, }),
    shared_term_entries: r.term_table.length(),
    interned_dag_nodes: added_total,
    reused_dag_nodes: reused_total,
  }
}

///|
/// Typed TLV extension section attached to a forward-compatible compiled-module
/// envelope (`CHMODENV` v1).
pub(all) struct ModuleTlvSection {
  tag : Int32
  critical : Bool
  payload : Array[Int32]
} derive(Debug, Eq)

///|
pub extend ModuleTlvSection with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend ModuleTlvSection with Eq::{not_equal, equal}

///|
pub(all) struct CompiledModuleEnvelopeLoad {
  status : ModuleBinaryStatus
  module_ : CompiledModule?
  recognized_sections : Array[ModuleTlvSection]
  skipped_noncritical_tags : Array[Int32]
} derive(Debug, Eq)

///|
pub extend CompiledModuleEnvelopeLoad with @moonbitlang/core/debug.Debug::{
  to_repr,
}

///|
pub extend CompiledModuleEnvelopeLoad with Eq::{not_equal, equal}

///|
fn compiled_module_envelope_magic() -> Array[Int32] {
  // ASCII `CHMODENV`
  [67, 72, 77, 79, 68, 69, 78, 86]
}

///|
/// Serialize a `CompiledModule` together with typed TLV extension sections
/// (`CHMODENV` v1). Unknown non-critical sections can be safely skipped by
/// older readers, whereas unknown critical sections fail closed.
pub fn compiled_module_envelope_to_binary(
  compiled : CompiledModule,
  sections : Array[ModuleTlvSection],
) -> Array[Int32]? {
  for sec in sections {
    if sec.tag < 0 {
      return None
    }
    for b in sec.payload {
      if b < 0 || b > 255 {
        return None
      }
    }
  }
  let core_bytes = compiled_module_to_binary(compiled)
  let pw = module_bin_writer_new()
  bw_i32(pw, core_bytes.length())
  for b in core_bytes {
    bw_u8(pw, b)
  }
  bw_i32(pw, sections.length())
  for sec in sections {
    bw_i32(pw, sec.tag)
    bw_u8(pw, if sec.critical { 1 } else { 0 })
    bw_i32(pw, sec.payload.length())
    bw_i32(pw, module_binary_checksum(sec.payload))
    for b in sec.payload {
      bw_u8(pw, b)
    }
  }
  let payload = pw.bytes
  let w = module_bin_writer_new()
  for b in compiled_module_envelope_magic() {
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
/// Decode a `CHMODENV` v1 compiled-module envelope against `known_tags`:
/// - sections with `tag` in `known_tags` are verified and returned in
///   `recognized_sections`;
/// - unknown sections with `critical == false` are checksum-verified, skipped,
///   and recorded in `skipped_noncritical_tags`;
/// - unknown sections with `critical == true` reject the blob with
///   `ModuleBinaryUnsupportedVersion`.
pub fn compiled_module_envelope_load_binary(
  bytes : Array[Int32],
  known_tags : Array[Int32],
  validate~ : Bool = true,
) -> CompiledModuleEnvelopeLoad {
  let fail = (st : ModuleBinaryStatus) => CompiledModuleEnvelopeLoad::{
    status: st,
    module_: None,
    recognized_sections: [],
    skipped_noncritical_tags: [],
  }
  for b in bytes {
    if b < 0 || b > 255 {
      return fail(ModuleBinaryMalformed)
    }
  }
  if bytes.length() < 20 {
    return fail(ModuleBinaryTruncated)
  }
  let magic = compiled_module_envelope_magic()
  for i in 0..<8 {
    if bytes[i] != magic[i] {
      return fail(ModuleBinaryBadMagic)
    }
  }
  if module_binary_u16_at(bytes, 8) != 1 || module_binary_u16_at(bytes, 10) != 0 {
    return fail(ModuleBinaryUnsupportedVersion)
  }
  let payload_len = module_binary_i32_at(bytes, 12)
  if payload_len < 0 {
    return fail(ModuleBinaryMalformed)
  }
  if bytes.length() < 20 + payload_len {
    return fail(ModuleBinaryTruncated)
  }
  if bytes.length() > 20 + payload_len {
    return fail(ModuleBinaryTrailingBytes)
  }
  let payload : Array[Int32] = []
  for i in 20..<bytes.length() {
    payload.push(bytes[i])
  }
  if module_binary_checksum(payload) != module_binary_i32_at(bytes, 16) {
    return fail(ModuleBinaryChecksumMismatch)
  }
  let r = module_bin_reader_new_versioned(payload, 3)
  let core_len = br_count(r)
  if !br_require_ok(r) {
    return fail(r.status)
  }
  let core_bytes : Array[Int32] = []
  for _ in 0..<core_len {
    core_bytes.push(br_u8(r))
    if !br_require_ok(r) {
      return fail(r.status)
    }
  }
  let core_load = compiled_module_load_binary_report(core_bytes, validate~)
  let compiled = match core_load.module_ {
    Some(m) => m
    None => return fail(core_load.status)
  }
  let sec_count = br_count(r)
  if !br_require_ok(r) {
    return fail(r.status)
  }
  let recognized : Array[ModuleTlvSection] = []
  let skipped : Array[Int32] = []
  for _ in 0..<sec_count {
    let tag = br_i32(r)
    let flags = br_u8(r)
    let slen = br_count(r)
    let expected_sum = br_i32(r)
    if !br_require_ok(r) || tag < 0 || (flags != 0 && flags != 1) {
      return fail(
        if r.status != ModuleBinaryOk {
          r.status
        } else {
          ModuleBinaryMalformed
        },
      )
    }
    let critical = flags == 1
    let spayload : Array[Int32] = []
    for _ in 0..<slen {
      spayload.push(br_u8(r))
      if !br_require_ok(r) {
        return fail(r.status)
      }
    }
    if module_binary_checksum(spayload) != expected_sum {
      return fail(ModuleBinaryChecksumMismatch)
    }
    if contains_int(known_tags, tag) {
      recognized.push(ModuleTlvSection::{ tag, critical, payload: spayload, })
    } else if critical {
      return fail(ModuleBinaryUnsupportedVersion)
    } else {
      skipped.push(tag)
    }
  }
  if r.pos != payload.length() {
    return fail(ModuleBinaryTrailingBytes)
  }
  CompiledModuleEnvelopeLoad::{
    status: ModuleBinaryOk,
    module_: Some(compiled),
    recognized_sections: recognized,
    skipped_noncritical_tags: skipped,
  }
}
