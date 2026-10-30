// ============================================================================
// Phase 16 Persistence Cryptography & Crash-Consistent WAL Journal
//
// 1. Standard FIPS 180-4 SHA-256 (64-round 32-bit) and SHA-512 (80-round
//    64-bit) message digests over byte arrays (`Array[Int32]`).
// 2. Pure RFC 8032 Ed25519 asymmetric public-key signatures over GF(2^255-19)
//    using complete extended twisted Edwards coordinates `(X : Y : Z : T)` and
//    repository-level asymmetric sealing (`CHARTSIG` v1).
// 3. Crash-consistent Write-Ahead Log (`CHWALJRN` v1) transactional byte-store
//    wrapper with SHA-256-authenticated commit records, torn-tail recovery,
//    and checkpoint log compaction.
// ============================================================================

///|
fn u32_rotr(x : UInt, n : Int) -> UInt {
  (x >> n) | (x << (32 - n))
}

///|
fn u64_rotr(x : UInt64, n : Int) -> UInt64 {
  (x >> n) | (x << (64 - n))
}

///|
/// FIPS 180-4 SHA-256 digest returning 32 big-endian bytes (`0..255`).
pub fn crypto_sha256(msg : Array[Int32]) -> Array[Int32] {
  let k : Array[UInt] = [
    0x428a2f98U, 0x71374491U, 0xb5c0fbcfU, 0xe9b5dba5U, 0x3956c25bU, 0x59f111f1U,
    0x923f82a4U, 0xab1c5ed5U, 0xd807aa98U, 0x12835b01U, 0x243185beU, 0x550c7dc3U,
    0x72be5d74U, 0x80deb1feU, 0x9bdc06a7U, 0xc19bf174U, 0xe49b69c1U, 0xefbe4786U,
    0x0fc19dc6U, 0x240ca1ccU, 0x2de92c6fU, 0x4a7484aaU, 0x5cb0a9dcU, 0x76f988daU,
    0x983e5152U, 0xa831c66dU, 0xb00327c8U, 0xbf597fc7U, 0xc6e00bf3U, 0xd5a79147U,
    0x06ca6351U, 0x14292967U, 0x27b70a85U, 0x2e1b2138U, 0x4d2c6dfcU, 0x53380d13U,
    0x650a7354U, 0x766a0abbU, 0x81c2c92eU, 0x92722c85U, 0xa2bfe8a1U, 0xa81a664bU,
    0xc24b8b70U, 0xc76c51a3U, 0xd192e819U, 0xd6990624U, 0xf40e3585U, 0x106aa070U,
    0x19a4c116U, 0x1e376c08U, 0x2748774cU, 0x34b0bcb5U, 0x391c0cb3U, 0x4ed8aa4aU,
    0x5b9cca4fU, 0x682e6ff3U, 0x748f82eeU, 0x78a5636fU, 0x84c87814U, 0x8cc70208U,
    0x90befffaU, 0xa4506cebU, 0xbef9a3f7U, 0xc67178f2U,
  ]
  let mut h0 = 0x6a09e667U
  let mut h1 = 0xbb67ae85U
  let mut h2 = 0x3c6ef372U
  let mut h3 = 0xa54ff53aU
  let mut h4 = 0x510e527fU
  let mut h5 = 0x9b05688cU
  let mut h6 = 0x1f83d9abU
  let mut h7 = 0x5be0cd19U

  let padded : Array[Int32] = []
  for i in 0..<msg.length() {
    padded.push(msg[i] & 0xff)
  }
  padded.push(0x80)
  while padded.length() % 64 != 56 {
    padded.push(0)
  }
  let bit_len : UInt64 = msg.length().to_uint64() * 8UL
  for s in 0..<8 {
    let shift = (7 - s) * 8
    padded.push(((bit_len >> shift) & 0xffUL).to_int())
  }
  let mut offset = 0
  while offset < padded.length() {
    let w : Array[UInt] = []
    for i in 0..<16 {
      let idx = offset + i * 4
      let b0 = padded[idx].reinterpret_as_uint()
      let b1 = padded[idx + 1].reinterpret_as_uint()
      let b2 = padded[idx + 2].reinterpret_as_uint()
      let b3 = padded[idx + 3].reinterpret_as_uint()
      w.push((b0 << 24) | (b1 << 16) | (b2 << 8) | b3)
    }
    for i in 16..<64 {
      let s0 = u32_rotr(w[i - 15], 7) ^
        u32_rotr(w[i - 15], 18) ^
        (w[i - 15] >> 3)
      let s1 = u32_rotr(w[i - 2], 17) ^
        u32_rotr(w[i - 2], 19) ^
        (w[i - 2] >> 10)
      w.push(w[i - 16] + s0 + w[i - 7] + s1)
    }
    let mut a = h0
    let mut b = h1
    let mut c = h2
    let mut d = h3
    let mut e = h4
    let mut f = h5
    let mut g = h6
    let mut h = h7
    for i in 0..<64 {
      let s1 = u32_rotr(e, 6) ^ u32_rotr(e, 11) ^ u32_rotr(e, 25)
      let ch = (e & f) ^ ((e ^ 0xffffffffU) & g)
      let temp1 = h + s1 + ch + k[i] + w[i]
      let s0 = u32_rotr(a, 2) ^ u32_rotr(a, 13) ^ u32_rotr(a, 22)
      let maj = (a & b) ^ (a & c) ^ (b & c)
      let temp2 = s0 + maj
      h = g
      g = f
      f = e
      e = d + temp1
      d = c
      c = b
      b = a
      a = temp1 + temp2
    }
    h0 = h0 + a
    h1 = h1 + b
    h2 = h2 + c
    h3 = h3 + d
    h4 = h4 + e
    h5 = h5 + f
    h6 = h6 + g
    h7 = h7 + h
    offset = offset + 64
  }
  let words = [h0, h1, h2, h3, h4, h5, h6, h7]
  let out : Array[Int32] = []
  for w in words {
    out.push(((w >> 24) & 0xffU).reinterpret_as_int())
    out.push(((w >> 16) & 0xffU).reinterpret_as_int())
    out.push(((w >> 8) & 0xffU).reinterpret_as_int())
    out.push((w & 0xffU).reinterpret_as_int())
  }
  out
}

///|
pub fn crypto_sha256_hex(msg : Array[Int32]) -> String {
  compiled_module_binary_to_hex(crypto_sha256(msg))
}

///|
/// FIPS 180-4 SHA-512 digest returning 64 big-endian bytes (`0..255`).
pub fn crypto_sha512(msg : Array[Int32]) -> Array[Int32] {
  let k : Array[UInt64] = [
    0x428a2f98d728ae22UL, 0x7137449123ef65cdUL, 0xb5c0fbcfec4d3b2fUL, 0xe9b5dba58189dbbcUL,
    0x3956c25bf348b538UL, 0x59f111f1b605d019UL, 0x923f82a4af194f9bUL, 0xab1c5ed5da6d8118UL,
    0xd807aa98a3030242UL, 0x12835b0145706fbeUL, 0x243185be4ee4b28cUL, 0x550c7dc3d5ffb4e2UL,
    0x72be5d74f27b896fUL, 0x80deb1fe3b1696b1UL, 0x9bdc06a725c71235UL, 0xc19bf174cf692694UL,
    0xe49b69c19ef14ad2UL, 0xefbe4786384f25e3UL, 0x0fc19dc68b8cd5b5UL, 0x240ca1cc77ac9c65UL,
    0x2de92c6f592b0275UL, 0x4a7484aa6ea6e483UL, 0x5cb0a9dcbd41fbd4UL, 0x76f988da831153b5UL,
    0x983e5152ee66dfabUL, 0xa831c66d2db43210UL, 0xb00327c898fb213fUL, 0xbf597fc7beef0ee4UL,
    0xc6e00bf33da88fc2UL, 0xd5a79147930aa725UL, 0x06ca6351e003826fUL, 0x142929670a0e6e70UL,
    0x27b70a8546d22ffcUL, 0x2e1b21385c26c926UL, 0x4d2c6dfc5ac42aedUL, 0x53380d139d95b3dfUL,
    0x650a73548baf63deUL, 0x766a0abb3c77b2a8UL, 0x81c2c92e47edaee6UL, 0x92722c851482353bUL,
    0xa2bfe8a14cf10364UL, 0xa81a664bbc423001UL, 0xc24b8b70d0f89791UL, 0xc76c51a30654be30UL,
    0xd192e819d6ef5218UL, 0xd69906245565a910UL, 0xf40e35855771202aUL, 0x106aa07032bbd1b8UL,
    0x19a4c116b8d2d0c8UL, 0x1e376c085141ab53UL, 0x2748774cdf8eeb99UL, 0x34b0bcb5e19b48a8UL,
    0x391c0cb3c5c95a63UL, 0x4ed8aa4ae3418acbUL, 0x5b9cca4f7763e373UL, 0x682e6ff3d6b2b8a3UL,
    0x748f82ee5defb2fcUL, 0x78a5636f43172f60UL, 0x84c87814a1f0ab72UL, 0x8cc702081a6439ecUL,
    0x90befffa23631e28UL, 0xa4506cebde82bde9UL, 0xbef9a3f7b2c67915UL, 0xc67178f2e372532bUL,
    0xca273eceea26619cUL, 0xd186b8c721c0c207UL, 0xeada7dd6cde0eb1eUL, 0xf57d4f7fee6ed178UL,
    0x06f067aa72176fbaUL, 0x0a637dc5a2c898a6UL, 0x113f9804bef90daeUL, 0x1b710b35131c471bUL,
    0x28db77f523047d84UL, 0x32caab7b40c72493UL, 0x3c9ebe0a15c9bebcUL, 0x431d67c49c100d4cUL,
    0x4cc5d4becb3e42b6UL, 0x597f299cfc657e2aUL, 0x5fcb6fab3ad6faecUL, 0x6c44198c4a475817UL,
  ]
  let mut h0 = 0x6a09e667f3bcc908UL
  let mut h1 = 0xbb67ae8584caa73bUL
  let mut h2 = 0x3c6ef372fe94f82bUL
  let mut h3 = 0xa54ff53a5f1d36f1UL
  let mut h4 = 0x510e527fade682d1UL
  let mut h5 = 0x9b05688c2b3e6c1fUL
  let mut h6 = 0x1f83d9abfb41bd6bUL
  let mut h7 = 0x5be0cd19137e2179UL

  let padded : Array[Int32] = []
  for i in 0..<msg.length() {
    padded.push(msg[i] & 0xff)
  }
  padded.push(0x80)
  while padded.length() % 128 != 112 {
    padded.push(0)
  }
  for _s in 0..<8 {
    padded.push(0)
  }
  let bit_len : UInt64 = msg.length().to_uint64() * 8UL
  for s in 0..<8 {
    let shift = (7 - s) * 8
    padded.push(((bit_len >> shift) & 0xffUL).to_int())
  }
  let mut offset = 0
  while offset < padded.length() {
    let w : Array[UInt64] = []
    for i in 0..<16 {
      let idx = offset + i * 8
      let mut word = 0UL
      for b in 0..<8 {
        word = (word << 8) | padded[idx + b].to_uint64()
      }
      w.push(word)
    }
    for i in 16..<80 {
      let s0 = u64_rotr(w[i - 15], 1) ^
        u64_rotr(w[i - 15], 8) ^
        (w[i - 15] >> 7)
      let s1 = u64_rotr(w[i - 2], 19) ^
        u64_rotr(w[i - 2], 61) ^
        (w[i - 2] >> 6)
      w.push(w[i - 16] + s0 + w[i - 7] + s1)
    }
    let mut a = h0
    let mut b = h1
    let mut c = h2
    let mut d = h3
    let mut e = h4
    let mut f = h5
    let mut g = h6
    let mut h = h7
    for i in 0..<80 {
      let s1 = u64_rotr(e, 14) ^ u64_rotr(e, 18) ^ u64_rotr(e, 41)
      let ch = (e & f) ^ ((e ^ 0xffffffffffffffffUL) & g)
      let temp1 = h + s1 + ch + k[i] + w[i]
      let s0 = u64_rotr(a, 28) ^ u64_rotr(a, 34) ^ u64_rotr(a, 39)
      let maj = (a & b) ^ (a & c) ^ (b & c)
      let temp2 = s0 + maj
      h = g
      g = f
      f = e
      e = d + temp1
      d = c
      c = b
      b = a
      a = temp1 + temp2
    }
    h0 = h0 + a
    h1 = h1 + b
    h2 = h2 + c
    h3 = h3 + d
    h4 = h4 + e
    h5 = h5 + f
    h6 = h6 + g
    h7 = h7 + h
    offset = offset + 128
  }
  let words = [h0, h1, h2, h3, h4, h5, h6, h7]
  let out : Array[Int32] = []
  for w in words {
    for b in 0..<8 {
      let shift = (7 - b) * 8
      out.push(((w >> shift) & 0xffUL).to_int())
    }
  }
  out
}

///|
pub fn crypto_sha512_hex(msg : Array[Int32]) -> String {
  compiled_module_binary_to_hex(crypto_sha512(msg))
}

// ---------------------------------------------------------------------------
// RFC 8032 Pure-Ed25519 over GF(2^255 - 19)
// ---------------------------------------------------------------------------

///|
pub struct Ed25519PublicKey {
  bytes : Array[Int32]
} derive(Debug, Eq)

///|
pub extend Ed25519PublicKey with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend Ed25519PublicKey with Eq::{not_equal, equal}

///|
pub struct Ed25519Keypair {
  seed : Array[Int32]
  public_key : Ed25519PublicKey
} derive(Debug, Eq)

///|
pub extend Ed25519Keypair with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend Ed25519Keypair with Eq::{not_equal, equal}

///|
pub struct Ed25519Signature {
  bytes : Array[Int32]
} derive(Debug, Eq)

///|
pub extend Ed25519Signature with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend Ed25519Signature with Eq::{not_equal, equal}

///|
priv struct EdPoint {
  x : BigInt
  y : BigInt
  z : BigInt
  t : BigInt
}

///|
fn ed_p() -> BigInt {
  (1N << 255) - 19N
}

///|
fn ed_l() -> BigInt {
  (1N << 252) + 27742317777372353535851937790883648493N
}

///|
fn ed_mod(a : BigInt, m : BigInt) -> BigInt {
  let r = a % m
  if r < 0N {
    r + m
  } else {
    r
  }
}

///|
fn ed_powmod(base0 : BigInt, exp0 : BigInt, m : BigInt) -> BigInt {
  let mut base = ed_mod(base0, m)
  let mut exp = exp0
  let mut acc = 1N
  while exp > 0N {
    if (exp & 1N) == 1N {
      acc = acc * base % m
    }
    base = base * base % m
    exp = exp >> 1
  }
  acc
}

///|
fn ed_inv(a : BigInt, p : BigInt) -> BigInt {
  ed_powmod(a, p - 2N, p)
}

///|
fn ed_d(p : BigInt) -> BigInt {
  ed_mod(-121665N * ed_inv(121666N, p), p)
}

///|
fn ed_sqrt_m1(p : BigInt) -> BigInt {
  ed_powmod(2N, (p - 1N) >> 2, p)
}

///|
fn ed_recover_x(y : BigInt, sign : Int32, p : BigInt, d : BigInt) -> BigInt? {
  if y < 0N || y >= p {
    return None
  }
  let y2 = y * y % p
  let u = ed_mod(y2 - 1N, p)
  let v = ed_mod(d * y2 + 1N, p)
  let x2 = u * ed_inv(v, p) % p
  if x2 == 0N {
    if sign != 0 {
      return None
    }
    return Some(0N)
  }
  let mut x = ed_powmod(x2, (p + 3N) >> 3, p)
  if x * x % p != x2 {
    x = x * ed_sqrt_m1(p) % p
  }
  if x * x % p != x2 {
    return None
  }
  let parity = if (x & 1N) == 1N { 1 } else { 0 }
  if parity != sign {
    x = p - x
  }
  Some(x)
}

///|
fn ed_zero_point() -> EdPoint {
  EdPoint::{ x: 0N, y: 1N, z: 1N, t: 0N }
}

///|
fn ed_base_point(p : BigInt, d : BigInt) -> EdPoint {
  let by = 4N * ed_inv(5N, p) % p
  let bx = match ed_recover_x(by, 0, p, d) {
    Some(v) => v
    None => 0N
  }
  EdPoint::{ x: bx, y: by, z: 1N, t: bx * by % p }
}

///|
fn ed_point_add(a : EdPoint, b : EdPoint, p : BigInt, two_d : BigInt) -> EdPoint {
  let ca = ed_mod(a.y - a.x, p) * ed_mod(b.y - b.x, p) % p
  let cb = (a.y + a.x) % p * ((b.y + b.x) % p) % p
  let cc = a.t * two_d % p * b.t % p
  let cd = a.z * 2N * b.z % p
  let ce = ed_mod(cb - ca, p)
  let cf = ed_mod(cd - cc, p)
  let cg = (cd + cc) % p
  let ch = (cb + ca) % p
  EdPoint::{
    x: ce * cf % p,
    y: cg * ch % p,
    z: cf * cg % p,
    t: ce * ch % p,
  }
}

///|
fn ed_scalar_mul(
  scalar0 : BigInt,
  pt : EdPoint,
  p : BigInt,
  two_d : BigInt,
) -> EdPoint {
  let mut s = scalar0
  let mut cur = pt
  let mut acc = ed_zero_point()
  while s > 0N {
    if (s & 1N) == 1N {
      acc = ed_point_add(acc, cur, p, two_d)
    }
    cur = ed_point_add(cur, cur, p, two_d)
    s = s >> 1
  }
  acc
}

///|
fn ed_point_eq(a : EdPoint, b : EdPoint, p : BigInt) -> Bool {
  ed_mod(a.x * b.z - b.x * a.z, p) == 0N &&
  ed_mod(a.y * b.z - b.y * a.z, p) == 0N
}

///|
fn ed_point_encode(pt : EdPoint, p : BigInt) -> Array[Int32] {
  let zinv = ed_inv(pt.z, p)
  let x = pt.x * zinv % p
  let y = pt.y * zinv % p
  let out : Array[Int32] = []
  let mut cur = y
  for _i in 0..<32 {
    out.push((cur & 0xffN).to_int())
    cur = cur >> 8
  }
  if (x & 1N) == 1N {
    out[31] = out[31] | 0x80
  }
  out
}

///|
fn ed_point_decode(enc : Array[Int32], p : BigInt, d : BigInt) -> EdPoint? {
  if enc.length() != 32 {
    return None
  }
  let mut y = 0N
  for i in 0..<32 {
    let b = if i == 31 { enc[i] & 0x7f } else { enc[i] & 0xff }
    y = y + (BigInt::from_int(b) << (i * 8))
  }
  let sign = (enc[31] >> 7) & 1
  match ed_recover_x(y, sign, p, d) {
    Some(x) => Some(EdPoint::{ x, y, z: 1N, t: x * y % p })
    None => None
  }
}

///|
fn le_bytes_to_bigint(bytes : Array[Int32], start : Int32, len : Int32) -> BigInt {
  let mut acc = 0N
  for i in 0..<len {
    let b = bytes[start + i] & 0xff
    acc = acc + (BigInt::from_int(b) << (i * 8))
  }
  acc
}

///|
fn bigint_to_le32(val0 : BigInt) -> Array[Int32] {
  let out : Array[Int32] = []
  let mut cur = val0
  for _i in 0..<32 {
    out.push((cur & 0xffN).to_int())
    cur = cur >> 8
  }
  out
}

///|
fn ed_expand_seed(seed : Array[Int32]) -> (BigInt, Array[Int32], Array[Int32])? {
  if seed.length() != 32 {
    return None
  }
  let p = ed_p()
  let d = ed_d(p)
  let two_d = d * 2N % p
  let h = crypto_sha512(seed)
  let a_bytes : Array[Int32] = []
  for i in 0..<32 {
    a_bytes.push(h[i] & 0xff)
  }
  a_bytes[0] = a_bytes[0] & 248
  a_bytes[31] = (a_bytes[31] & 127) | 64
  let s = le_bytes_to_bigint(a_bytes, 0, 32)
  let prefix : Array[Int32] = []
  for i in 32..<64 {
    prefix.push(h[i] & 0xff)
  }
  let pub_pt = ed_scalar_mul(s, ed_base_point(p, d), p, two_d)
  let pk_bytes = ed_point_encode(pub_pt, p)
  Some((s, prefix, pk_bytes))
}

///|
/// Derive a deterministic RFC 8032 Ed25519 keypair from a 32-byte seed.
pub fn ed25519_keypair_from_seed(seed : Array[Int32]) -> Ed25519Keypair? {
  match ed_expand_seed(seed) {
    Some((_s, _prefix, pk_bytes)) => {
      let seed_copy : Array[Int32] = []
      for i in 0..<32 {
        seed_copy.push(seed[i] & 0xff)
      }
      Some(Ed25519Keypair::{
        seed: seed_copy,
        public_key: Ed25519PublicKey::{ bytes: pk_bytes },
      })
    }
    None => None
  }
}

///|
/// Sign an arbitrary byte message with RFC 8032 Pure-Ed25519 (64-byte signature).
pub fn ed25519_sign(
  kp : Ed25519Keypair,
  msg : Array[Int32],
) -> Ed25519Signature? {
  let (s, prefix, pk_bytes) = match ed_expand_seed(kp.seed) {
    Some(v) => v
    None => return None
  }
  if pk_bytes != kp.public_key.bytes {
    return None
  }
  let p = ed_p()
  let d = ed_d(p)
  let two_d = d * 2N % p
  let l = ed_l()
  let r_in : Array[Int32] = []
  for b in prefix {
    r_in.push(b)
  }
  for b in msg {
    r_in.push(b & 0xff)
  }
  let r = ed_mod(le_bytes_to_bigint(crypto_sha512(r_in), 0, 64), l)
  let r_enc = ed_point_encode(
    ed_scalar_mul(r, ed_base_point(p, d), p, two_d),
    p,
  )
  let k_in : Array[Int32] = []
  for b in r_enc {
    k_in.push(b)
  }
  for b in pk_bytes {
    k_in.push(b)
  }
  for b in msg {
    k_in.push(b & 0xff)
  }
  let k = ed_mod(le_bytes_to_bigint(crypto_sha512(k_in), 0, 64), l)
  let s_scalar = ed_mod(r + k * s, l)
  let s_enc = bigint_to_le32(s_scalar)
  let sig : Array[Int32] = []
  for b in r_enc {
    sig.push(b)
  }
  for b in s_enc {
    sig.push(b)
  }
  Some(Ed25519Signature::{ bytes: sig })
}

///|
/// Verify an RFC 8032 Pure-Ed25519 64-byte signature using only the 32-byte
/// `Ed25519PublicKey` (enforcing canonical `S < L` and `[8][S]B == [8](R + [k]A)`).
pub fn ed25519_verify(
  pk : Ed25519PublicKey,
  msg : Array[Int32],
  sig : Ed25519Signature,
) -> Bool {
  if pk.bytes.length() != 32 || sig.bytes.length() != 64 {
    return false
  }
  let p = ed_p()
  let d = ed_d(p)
  let two_d = d * 2N % p
  let l = ed_l()
  let s_scalar = le_bytes_to_bigint(sig.bytes, 32, 32)
  if s_scalar < 0N || s_scalar >= l {
    return false
  }
  let r_enc : Array[Int32] = []
  for i in 0..<32 {
    r_enc.push(sig.bytes[i] & 0xff)
  }
  let a_pt = match ed_point_decode(pk.bytes, p, d) {
    Some(pt) => pt
    None => return false
  }
  let r_pt = match ed_point_decode(r_enc, p, d) {
    Some(pt) => pt
    None => return false
  }
  let k_in : Array[Int32] = []
  for b in r_enc {
    k_in.push(b)
  }
  for b in pk.bytes {
    k_in.push(b & 0xff)
  }
  for b in msg {
    k_in.push(b & 0xff)
  }
  let k = ed_mod(le_bytes_to_bigint(crypto_sha512(k_in), 0, 64), l)
  let lhs = ed_scalar_mul(8N * s_scalar, ed_base_point(p, d), p, two_d)
  let ka = ed_scalar_mul(k, a_pt, p, two_d)
  let rhs = ed_scalar_mul(8N, ed_point_add(r_pt, ka, p, two_d), p, two_d)
  ed_point_eq(lhs, rhs, p)
}

// ---------------------------------------------------------------------------
// Repository Asymmetric Public-Key Sealing (`CHARTSIG` v1)
// ---------------------------------------------------------------------------

///|
fn artifact_sig_path(repo : ArtifactRepository) -> String {
  repo.prefix + "/ed25519.sig"
}

///|
fn push_u32_le(buf : Array[Int32], val : Int32) -> Unit {
  let u = val.reinterpret_as_uint()
  buf.push((u & 0xffU).reinterpret_as_int())
  buf.push(((u >> 8) & 0xffU).reinterpret_as_int())
  buf.push(((u >> 16) & 0xffU).reinterpret_as_int())
  buf.push(((u >> 24) & 0xffU).reinterpret_as_int())
}

///|
fn read_u32_le(buf : Array[Int32], off : Int32) -> Int32? {
  if off < 0 || off + 4 > buf.length() {
    return None
  }
  let b0 = (buf[off] & 0xff).reinterpret_as_uint()
  let b1 = (buf[off + 1] & 0xff).reinterpret_as_uint()
  let b2 = (buf[off + 2] & 0xff).reinterpret_as_uint()
  let b3 = (buf[off + 3] & 0xff).reinterpret_as_uint()
  Some((b0 | (b1 << 8) | (b2 << 16) | (b3 << 24)).reinterpret_as_int())
}

///|
fn push_ascii_bytes(buf : Array[Int32], s : String) -> Unit {
  for ch in s {
    buf.push(ch.to_int() & 0xff)
  }
}

///|
fn artifact_repository_canonical_merkle_digest(
  repo : ArtifactRepository,
) -> Array[Int32]? {
  let chain_path = repo.prefix + "/chain.bin"
  let chain_bytes = match (repo.store.read)(chain_path) {
    Some(b) => b
    None => return None
  }
  let entries = match artifact_repository_chain_entries(repo) {
    Some(es) => es
    None => return None
  }
  if !artifact_chain_links_valid(entries) {
    return None
  }
  let live = match artifact_chain_live_records(entries) {
    Some(rs) => rs
    None => return None
  }
  // Sort live records canonically by `kind + "/" + name`.
  for i in 0..<live.length() {
    for j in (i + 1)..<live.length() {
      if live[j].kind + "/" + live[j].name < live[i].kind + "/" + live[i].name {
        let tmp = live[i]
        live[i] = live[j]
        live[j] = tmp
      }
    }
  }
  let transcript : Array[Int32] = []
  push_ascii_bytes(transcript, "CHARTSIG-V1:")
  for b in crypto_sha256(chain_bytes) {
    transcript.push(b)
  }
  push_u32_le(transcript, live.length())
  for rec in live {
    let blob = match (repo.store.read)(rec.blob_key) {
      Some(b) => b
      None => return None
    }
    if !artifact_record_matches_bytes(rec, blob) {
      return None
    }
    push_u32_le(transcript, rec.kind.length())
    push_ascii_bytes(transcript, rec.kind)
    push_u32_le(transcript, rec.name.length())
    push_ascii_bytes(transcript, rec.name)
    for b in crypto_sha256(blob) {
      transcript.push(b)
    }
  }
  Some(crypto_sha256(transcript))
}

///|
/// Seal `repo` asymmetrically with an `Ed25519Keypair`: computes a SHA-256
/// Merkle digest over `chain.bin` and every live artifact blob, signs it via
/// RFC 8032 Ed25519, and writes `<prefix>/ed25519.sig` (`CHARTSIG` v1).
pub fn artifact_repository_seal_ed25519(
  repo : ArtifactRepository,
  kp : Ed25519Keypair,
) -> Bool {
  let digest = match artifact_repository_canonical_merkle_digest(repo) {
    Some(d) => d
    None => return false
  }
  let sig = match ed25519_sign(kp, digest) {
    Some(s) => s
    None => return false
  }
  let env : Array[Int32] = []
  push_ascii_bytes(env, "CHARTSIG")
  push_u32_le(env, 1)
  for b in kp.public_key.bytes {
    env.push(b & 0xff)
  }
  for b in digest {
    env.push(b & 0xff)
  }
  for b in sig.bytes {
    env.push(b & 0xff)
  }
  (repo.store.write)(artifact_sig_path(repo), env)
}

///|
/// Verify `<prefix>/ed25519.sig` against a trusted `Ed25519PublicKey` WITHOUT
/// requiring any secret key material: recomputes the SHA-256 Merkle digest of
/// `chain.bin` + all live blobs and checks the 64-byte Ed25519 signature.
pub fn artifact_repository_verify_ed25519(
  repo : ArtifactRepository,
  trusted_pk : Ed25519PublicKey,
) -> Bool {
  if trusted_pk.bytes.length() != 32 {
    return false
  }
  let env = match (repo.store.read)(artifact_sig_path(repo)) {
    Some(b) => b
    None => return false
  }
  // 8 ("CHARTSIG") + 4 (ver=1) + 32 (pk) + 32 (digest) + 64 (sig) = 140 bytes.
  if env.length() != 140 {
    return false
  }
  let magic = "CHARTSIG"
  let mut mi = 0
  for ch in magic {
    if (env[mi] & 0xff) != (ch.to_int() & 0xff) {
      return false
    }
    mi = mi + 1
  }
  match read_u32_le(env, 8) {
    Some(1) => ()
    _ => return false
  }
  for i in 0..<32 {
    if (env[12 + i] & 0xff) != (trusted_pk.bytes[i] & 0xff) {
      return false
    }
  }
  let actual_digest = match artifact_repository_canonical_merkle_digest(repo) {
    Some(d) => d
    None => return false
  }
  for i in 0..<32 {
    if (env[44 + i] & 0xff) != (actual_digest[i] & 0xff) {
      return false
    }
  }
  let sig_bytes : Array[Int32] = []
  for i in 0..<64 {
    sig_bytes.push(env[76 + i] & 0xff)
  }
  ed25519_verify(trusted_pk, actual_digest, Ed25519Signature::{
    bytes: sig_bytes,
  })
}

// ---------------------------------------------------------------------------
// Crash-Consistent Write-Ahead Log (`CHWALJRN` v1)
// ---------------------------------------------------------------------------

///|
enum WalOp {
  WalPut(String, Array[Int32])
  WalDel(String)
}

///|
pub struct ArtifactWalRecoveryReport {
  replayed_transactions : Int32
  discarded_torn_bytes : Int32
  active_tx_rolled_back : Bool
} derive(Debug, Eq)

///|
pub extend ArtifactWalRecoveryReport with @moonbitlang/core/debug.Debug::{
  to_repr,
}

///|
pub extend ArtifactWalRecoveryReport with Eq::{not_equal, equal}

///|
pub struct ArtifactWalStore {
  backing : ArtifactByteStore
  wal_key : String
  mut next_tx_id : Int32
  mut active_tx_id : Int32
  staged : Array[WalOp]
}

///|
fn wal_header_bytes() -> Array[Int32] {
  let out : Array[Int32] = []
  push_ascii_bytes(out, "CHWALJRN")
  push_u32_le(out, 1)
  out
}

///|
fn wal_encode_tx_record(tx_id : Int32, ops : Array[WalOp]) -> Array[Int32] {
  let payload : Array[Int32] = []
  push_u32_le(payload, tx_id)
  push_u32_le(payload, ops.length())
  for op in ops {
    match op {
      WalPut(k, bytes) => {
        payload.push(1)
        push_u32_le(payload, k.length())
        push_ascii_bytes(payload, k)
        push_u32_le(payload, bytes.length())
        for b in bytes {
          payload.push(b & 0xff)
        }
      }
      WalDel(k) => {
        payload.push(2)
        push_u32_le(payload, k.length())
        push_ascii_bytes(payload, k)
      }
    }
  }
  let digest = crypto_sha256(payload)
  let frame : Array[Int32] = []
  // Frame tag 0xA5 + payload_len (u32) + payload + 32-byte SHA-256 commit seal.
  frame.push(0xa5)
  push_u32_le(frame, payload.length())
  for b in payload {
    frame.push(b)
  }
  for b in digest {
    frame.push(b)
  }
  frame
}

///|
fn read_ascii_slice(buf : Array[Int32], off : Int32, len : Int32) -> String? {
  if len < 0 || off < 0 || off + len > buf.length() {
    return None
  }
  let sb = StringBuilder()
  for i in 0..<len {
    sb.write_char((buf[off + i] & 0xff).unsafe_to_char())
  }
  Some(sb.to_string())
}

///|
fn wal_decode_payload(payload : Array[Int32]) -> (Int32, Array[WalOp])? {
  let tx_id = match read_u32_le(payload, 0) {
    Some(v) => v
    None => return None
  }
  let count = match read_u32_le(payload, 4) {
    Some(v) => v
    None => return None
  }
  if count < 0 {
    return None
  }
  let ops : Array[WalOp] = []
  let mut pos = 8
  for _i in 0..<count {
    if pos >= payload.length() {
      return None
    }
    let kind = payload[pos] & 0xff
    pos = pos + 1
    let klen = match read_u32_le(payload, pos) {
      Some(v) => v
      None => return None
    }
    pos = pos + 4
    let key = match read_ascii_slice(payload, pos, klen) {
      Some(s) => s
      None => return None
    }
    pos = pos + klen
    if kind == 1 {
      let blen = match read_u32_le(payload, pos) {
        Some(v) => v
        None => return None
      }
      pos = pos + 4
      if blen < 0 || pos + blen > payload.length() {
        return None
      }
      let data : Array[Int32] = []
      for j in 0..<blen {
        data.push(payload[pos + j] & 0xff)
      }
      pos = pos + blen
      ops.push(WalPut(key, data))
    } else if kind == 2 {
      ops.push(WalDel(key))
    } else {
      return None
    }
  }
  if pos != payload.length() {
    return None
  }
  Some((tx_id, ops))
}

///|
fn wal_apply_ops(backing : ArtifactByteStore, ops : Array[WalOp]) -> Bool {
  for op in ops {
    match op {
      WalPut(k, bytes) =>
        if !(backing.write)(k, bytes) {
          return false
        }
      WalDel(k) => ignore((backing.remove)(k))
    }
  }
  true
}

///|
/// Open a crash-consistent WAL wrapper around `backing` with journal stored at
/// `wal_key` (initializing an empty `CHWALJRN` v1 header if absent and running
/// crash recovery immediately).
pub fn artifact_wal_store_open(
  backing : ArtifactByteStore,
  wal_key~ : String = "repo/_wal/journal.bin",
) -> (ArtifactWalStore, ArtifactWalRecoveryReport)? {
  if (backing.read)(wal_key) == None {
    if !(backing.write)(wal_key, wal_header_bytes()) {
      return None
    }
  }
  let wal = ArtifactWalStore::{
    backing,
    wal_key,
    next_tx_id: 1,
    active_tx_id: 0,
    staged: [],
  }
  match artifact_wal_recover(wal) {
    Some(rep) => Some((wal, rep))
    None => None
  }
}

///|
/// Replay all SHA-256-authenticated committed frames in `wal.wal_key`,
/// roll back any active in-memory transaction, and truncate any torn or
/// corrupted tail bytes at the end of the journal.
pub fn artifact_wal_recover(
  wal : ArtifactWalStore,
) -> ArtifactWalRecoveryReport? {
  let had_active = wal.active_tx_id != 0
  wal.active_tx_id = 0
  wal.staged.clear()
  let raw = match (wal.backing.read)(wal.wal_key) {
    Some(b) => b
    None => return None
  }
  let hdr = wal_header_bytes()
  if raw.length() < hdr.length() {
    return None
  }
  for i in 0..<hdr.length() {
    if (raw[i] & 0xff) != (hdr[i] & 0xff) {
      return None
    }
  }
  let mut pos = hdr.length()
  let mut valid_end = pos
  let mut replayed = 0
  let mut max_tx = 0
  while pos < raw.length() {
    if (raw[pos] & 0xff) != 0xa5 || pos + 5 > raw.length() {
      break
    }
    let plen = match read_u32_le(raw, pos + 1) {
      Some(v) => v
      None => break
    }
    if plen < 0 || pos + 5 + plen + 32 > raw.length() {
      break
    }
    let payload : Array[Int32] = []
    for j in 0..<plen {
      payload.push(raw[pos + 5 + j] & 0xff)
    }
    let expected_sha = crypto_sha256(payload)
    let mut sha_ok = true
    for j in 0..<32 {
      if (raw[pos + 5 + plen + j] & 0xff) != expected_sha[j] {
        sha_ok = false
        break
      }
    }
    if !sha_ok {
      break
    }
    let (tx_id, ops) = match wal_decode_payload(payload) {
      Some(v) => v
      None => break
    }
    if !wal_apply_ops(wal.backing, ops) {
      return None
    }
    if tx_id > max_tx {
      max_tx = tx_id
    }
    replayed = replayed + 1
    pos = pos + 5 + plen + 32
    valid_end = pos
  }
  let discarded = raw.length() - valid_end
  if discarded > 0 {
    let clean : Array[Int32] = []
    for i in 0..<valid_end {
      clean.push(raw[i] & 0xff)
    }
    if !(wal.backing.write)(wal.wal_key, clean) {
      return None
    }
  }
  if max_tx >= wal.next_tx_id {
    wal.next_tx_id = max_tx + 1
  }
  Some(ArtifactWalRecoveryReport::{
    replayed_transactions: replayed,
    discarded_torn_bytes: discarded,
    active_tx_rolled_back: had_active,
  })
}

///|
pub fn artifact_wal_begin_tx(wal : ArtifactWalStore) -> Int32? {
  if wal.active_tx_id != 0 {
    return None
  }
  let tx = wal.next_tx_id
  wal.next_tx_id = wal.next_tx_id + 1
  wal.active_tx_id = tx
  wal.staged.clear()
  Some(tx)
}

///|
pub fn artifact_wal_put(
  wal : ArtifactWalStore,
  key : String,
  bytes : Array[Int32],
) -> Bool {
  if wal.active_tx_id == 0 || key == wal.wal_key {
    return false
  }
  let copy : Array[Int32] = []
  for b in bytes {
    copy.push(b & 0xff)
  }
  wal.staged.push(WalPut(key, copy))
  true
}

///|
pub fn artifact_wal_delete(wal : ArtifactWalStore, key : String) -> Bool {
  if wal.active_tx_id == 0 || key == wal.wal_key {
    return false
  }
  wal.staged.push(WalDel(key))
  true
}

///|
pub fn artifact_wal_abort_tx(wal : ArtifactWalStore) -> Bool {
  if wal.active_tx_id == 0 {
    return false
  }
  wal.active_tx_id = 0
  wal.staged.clear()
  true
}

///|
/// Durable two-step WAL commit: appends the SHA-256-sealed transaction frame
/// to `wal.wal_key` BEFORE materializing `wal.staged` into `wal.backing`.
pub fn artifact_wal_commit_tx(wal : ArtifactWalStore) -> Bool {
  if wal.active_tx_id == 0 {
    return false
  }
  let cur_log = match (wal.backing.read)(wal.wal_key) {
    Some(b) => b
    None => return false
  }
  let frame = wal_encode_tx_record(wal.active_tx_id, wal.staged)
  let next_log : Array[Int32] = []
  for b in cur_log {
    next_log.push(b & 0xff)
  }
  for b in frame {
    next_log.push(b & 0xff)
  }
  if !(wal.backing.write)(wal.wal_key, next_log) {
    return false
  }
  let ok = wal_apply_ops(wal.backing, wal.staged)
  wal.active_tx_id = 0
  wal.staged.clear()
  ok
}

///|
/// Compact the committed WAL journal back to its 12-byte header once all
/// committed operations have been materialized in `wal.backing` (refusing if
/// an uncommitted transaction is currently active).
pub fn artifact_wal_checkpoint(wal : ArtifactWalStore) -> Bool {
  if wal.active_tx_id != 0 {
    return false
  }
  match artifact_wal_recover(wal) {
    Some(_) => (wal.backing.write)(wal.wal_key, wal_header_bytes())
    None => false
  }
}

///|
/// Read-your-own-writes view over `wal`, hiding the internal `wal.wal_key`
/// from `list()` and routing standalone writes/removes as atomic single-op
/// WAL transactions when no explicit transaction is open.
pub fn artifact_wal_byte_store(wal : ArtifactWalStore) -> ArtifactByteStore {
  artifact_byte_store_new(
    read=key => {
      if key == wal.wal_key {
        return None
      }
      if wal.active_tx_id != 0 {
        let mut idx = wal.staged.length() - 1
        while idx >= 0 {
          match wal.staged[idx] {
            WalPut(k, bytes) =>
              if k == key {
                let cp : Array[Int32] = []
                for b in bytes {
                  cp.push(b)
                }
                return Some(cp)
              }
            WalDel(k) => if k == key { return None }
          }
          idx = idx - 1
        }
      }
      (wal.backing.read)(key)
    },
    write=(key, bytes) => {
      if key == wal.wal_key {
        return false
      }
      if wal.active_tx_id != 0 {
        artifact_wal_put(wal, key, bytes)
      } else {
        match artifact_wal_begin_tx(wal) {
          Some(_) =>
            artifact_wal_put(wal, key, bytes) && artifact_wal_commit_tx(wal)
          None => false
        }
      }
    },
    remove=key => {
      if key == wal.wal_key {
        return false
      }
      if wal.active_tx_id != 0 {
        artifact_wal_delete(wal, key)
      } else {
        match artifact_wal_begin_tx(wal) {
          Some(_) =>
            artifact_wal_delete(wal, key) && artifact_wal_commit_tx(wal)
          None => false
        }
      }
    },
    list=() => {
      let base_keys = (wal.backing.list)()
      let out : Array[String] = []
      for k in base_keys {
        if k != wal.wal_key && !out.contains(k) {
          out.push(k)
        }
      }
      if wal.active_tx_id != 0 {
        for op in wal.staged {
          match op {
            WalPut(k, _) => if !out.contains(k) { out.push(k) }
            WalDel(k) =>
              for i in 0..<out.length() {
                if out[i] == k {
                  ignore(out.remove(i))
                  break
                }
              }
          }
        }
      }
      out
    },
  )
}
