///|
/// 一條帳本記錄。
pub struct SRec {
  seq : Int32
  tag : String
  kind : String
  payload : String
  prev : String
  hash : String
}

///|
/// 帳本（記錄序列；創世為第一筆）。
pub struct SLedger {
  recs : Array[SRec]
}

///|
/// 複製帳本並把指定 tag 的 payload 換掉（不改雜湊）——篡改實驗的構造器。
pub fn sled_tamper(l : SLedger, tag : String, new_payload : String) -> SLedger {
  let out : Array[SRec] = []
  for r in l.recs {
    if r.tag == tag {
      let _ = out.push(SRec::{
        seq: r.seq,
        tag: r.tag,
        kind: r.kind,
        payload: new_payload,
        prev: r.prev,
        hash: r.hash,
      })
    } else {
      let _ = out.push(r)
    }
  }
  SLedger::{ recs: out, }
}

///|
/// 重複字串（String::repeat 的本地版本）。
fn rep(s : String, n : Int32) -> String {
  let mut out = ""
  let mut i = 0
  while i < n {
    out = "\{out}\{s}"
    i = i + 1
  }
  out
}

///|
/// 創世記錄（固定常數；所有帳本同一起點）。
pub fn genesis() -> SRec {
  let seq = 0
  let tag = "[S-GENESIS]"
  let kind = "genesis"
  let payload = "superlab-persistent-ledger-v1"
  let prev = rep("0", 64)
  SRec::{
    seq,
    tag,
    kind,
    payload,
    prev,
    hash: rec_hash(seq, tag, kind, payload, prev),
  }
}

///|
/// 記錄雜湊：SHA-256 over "seq|tag|kind|payload|prev"。
pub fn rec_hash(
  seq : Int32,
  tag : String,
  kind : String,
  payload : String,
  prev : String,
) -> String {
  sha256_hex("\{seq}|\{tag}|\{kind}|\{payload}|\{prev}")
}

///|
/// 新帳本。
pub fn sled_new() -> SLedger {
  SLedger::{ recs: [genesis()], }
}

///|
/// 帳本長度（含創世記錄）。
pub fn sled_len(l : SLedger) -> Int32 {
  l.recs.length()
}

///|
/// 當前鏈頭雜湊。
pub fn sled_head(l : SLedger) -> String {
  l.recs[l.recs.length() - 1].hash
}

///|
/// 清洗 payload：把會破壞 JSONL 的字元換成底線。
pub fn sled_sanitize(s : String) -> String {
  let mut out = ""
  for c in s {
    if c == '"' || c == '{' || c == '}' || c == ',' || c == '\n' || c == '|' {
      out = "\{out}_"
    } else {
      out = "\{out}\{c}"
    }
  }
  out
}

///|
/// 冪等記錄：若 (tag,kind,payload) 已存在則跳過並回傳 false。
pub fn sled_record(
  l : SLedger,
  tag : String,
  kind : String,
  payload : String,
) -> Bool {
  let pay = sled_sanitize(payload)
  for r in l.recs {
    if r.tag == tag && r.kind == kind && r.payload == pay {
      return false
    }
  }
  let seq = l.recs.length()
  let prev = sled_head(l)
  let _ = l.recs.push(SRec::{
    seq,
    tag,
    kind,
    payload: pay,
    prev,
    hash: rec_hash(seq, tag, kind, pay, prev),
  })
  true
}

///|
/// 全鏈自我驗證：起點自洽（創世或紀元封條）、seq 連續、prev 銜接、hash 重算一致。
pub fn sled_verify(l : SLedger) -> Bool {
  if l.recs.length() == 0 {
    return false
  }
  let g = l.recs[0]
  if g.kind != "genesis" || g.seq != 0 {
    return false
  }
  if g.hash != rec_hash(g.seq, g.tag, g.kind, g.payload, g.prev) {
    return false
  }
  for i = 1; i < l.recs.length(); i = i + 1 {
    let r = l.recs[i]
    let p = l.recs[i - 1]
    if r.seq != p.seq + 1 || r.prev != p.hash {
      return false
    }
    if r.hash != rec_hash(r.seq, r.tag, r.kind, r.payload, r.prev) {
      return false
    }
  }
  true
}

///|
/// 規範化 JSONL（每行一筆；無空白）。
pub fn rec_jsonl(r : SRec) -> String {
  "{\"seq\":\{r.seq},\"tag\":\"\{r.tag}\",\"kind\":\"\{r.kind}\",\"payload\":\"\{r.payload}\",\"prev\":\"\{r.prev}\",\"hash\":\"\{r.hash}\"}"
}

///|
pub fn sled_jsonl(l : SLedger) -> String {
  let mut out = ""
  for r in l.recs {
    out = "\{out}\{rec_jsonl(r)}\n"
  }
  out
}

// ---------------------------------------------------------------- 剖析器 --

///|
/// 字串 → 字元陣列（String 隨機索引是 UTF-16 碼元；統一走 Array[Char]）。
fn chars_of(s : String) -> Array[Char] {
  let out : Array[Char] = []
  for c in s {
    let _ = out.push(c)
  }
  out
}

///|
/// 在 cs 中尋找 sub 的首次出現位置；找不到回傳 -1。
fn find_sub(cs : Array[Char], sub : Array[Char]) -> Int32 {
  let n = cs.length()
  let m = sub.length()
  if m == 0 || m > n {
    return -1
  }
  for i = 0; i <= n - m; i = i + 1 {
    let mut ok = true
    for j = 0; j < m; j = j + 1 {
      if cs[i + j] != sub[j] {
        ok = false
      }
    }
    if ok {
      return i
    }
  }
  -1
}

///|
/// 從 JSONL 行抽取欄位值：`"key":"value"` 或 `"key":123`。
fn extract_field(line : String, key : String) -> String? {
  let cs = chars_of(line)
  let pat = chars_of("\"\{key}\":")
  let idx = find_sub(cs, pat)
  if idx < 0 {
    return None
  }
  let mut pos = idx + pat.length()
  if pos >= cs.length() {
    return None
  }
  if cs[pos] == '"' {
    pos = pos + 1
    let start = pos
    while pos < cs.length() && cs[pos] != '"' {
      pos = pos + 1
    }
    if pos >= cs.length() {
      return None
    }
    let mut out = ""
    for k = start; k < pos; k = k + 1 {
      out = "\{out}\{cs[k]}"
    }
    Some(out)
  } else {
    let start = pos
    while pos < cs.length() && cs[pos] != ',' && cs[pos] != '}' {
      pos = pos + 1
    }
    let mut out = ""
    for k = start; k < pos; k = k + 1 {
      out = "\{out}\{cs[k]}"
    }
    Some(out)
  }
}

///|
fn parse_int_safe(s : String) -> Int32 {
  @string.parse_int(s[:], base=10) catch {
    _ => -999999
  }
}

///|
/// 剖析單行 JSONL 為記錄；格式不符回傳 None。
pub fn sled_parse_line(line : String) -> SRec? {
  if line.length() == 0 {
    return None
  }
  let seq_s = extract_field(line, "seq")
  let tag = extract_field(line, "tag")
  let kind = extract_field(line, "kind")
  let payload = extract_field(line, "payload")
  let prev = extract_field(line, "prev")
  let hash = extract_field(line, "hash")
  if seq_s is None ||
    tag is None ||
    kind is None ||
    payload is None ||
    prev is None ||
    hash is None {
    return None
  }
  if seq_s is Some(sv) {
    if tag is Some(t) {
      if kind is Some(k) {
        if payload is Some(p) {
          if prev is Some(pr) {
            if hash is Some(h) {
              let seq = parse_int_safe(sv)
              return Some(SRec::{
                seq,
                tag: t,
                kind: k,
                payload: p,
                prev: pr,
                hash: h,
              })
            }
          }
        }
      }
    }
  }
  None
}

///| 驗證一組持久化行（來自 argv 的 LEDGER.jsonl 內容）：

///|
/// 回傳 (是否通過驗鏈, 記錄數)。行序須從 seq=1 起連續銜接創世鏈。
pub fn sled_parse_lines(lines : Array[String]) -> (Bool, Int32) {
  let g = genesis()
  let mut prev_hash = g.hash
  let mut expect_seq = 1
  let mut count = 0
  for line in lines {
    let r = sled_parse_line(line)
    if r is None {
      return (false, count)
    }
    if r is Some(rec) {
      if rec.seq != expect_seq || rec.prev != prev_hash {
        return (false, count)
      }
      if rec.hash != rec_hash(rec.seq, rec.tag, rec.kind, rec.payload, rec.prev) {
        return (false, count)
      }
      prev_hash = rec.hash
      expect_seq = expect_seq + 1
      count = count + 1
    }
  }
  (true, count)
}

// ---------------------------------------------------------------- SHA-256 --

///| 純 MoonBit SHA-256（BMP 內輸入；帳本內容為受控 ASCII）。

///|
/// 以 32 位元 Int（Two's-complement 位元模式）實作；回傳 64 字元十六進位。
pub fn sha256_hex(s : String) -> String {
  // 1. UTF-8 編碼
  let bytes : Array[Int32] = []
  for c in s {
    let v = c.to_int()
    if v < 0x80 {
      let _ = bytes.push(v)
    } else if v < 0x800 {
      let _ = bytes.push(0xC0 | (v >> 6))
      let _ = bytes.push(0x80 | (v & 0x3F))
    } else {
      let _ = bytes.push(0xE0 | (v >> 12))
      let _ = bytes.push(0x80 | ((v >> 6) & 0x3F))
      let _ = bytes.push(0x80 | (v & 0x3F))
    }
  }
  // 2. 填充
  let bitlen = bytes.length() * 8
  let _ = bytes.push(0x80)
  while bytes.length() % 64 != 56 {
    let _ = bytes.push(0)
  }
  let _ = bytes.push(0)
  let _ = bytes.push(0)
  let _ = bytes.push(0)
  let _ = bytes.push(0)
  let _ = bytes.push((bitlen >> 24) & 0xFF)
  let _ = bytes.push((bitlen >> 16) & 0xFF)
  let _ = bytes.push((bitlen >> 8) & 0xFF)
  let _ = bytes.push(bitlen & 0xFF)
  // 3. 壓縮
  let k : Array[Int32] = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4,
    0xab1c5ed5, 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe,
    0x9bdc06a7, 0xc19bf174, 0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f,
    0x4a7484aa, 0x5cb0a9dc, 0x76f988da, 0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
    0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc,
    0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 0xa2bfe8a1, 0xa81a664b,
    0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070, 0x19a4c116,
    0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7,
    0xc67178f2,
  ]
  let mut h0 = 0x6a09e667
  let mut h1 = 0xbb67ae85
  let mut h2 = 0x3c6ef372
  let mut h3 = 0xa54ff53a
  let mut h4 = 0x510e527f
  let mut h5 = 0x9b05688c
  let mut h6 = 0x1f83d9ab
  let mut h7 = 0x5be0cd19
  let w : Array[Int32] = Array::make(64, 0)
  for chunk = 0; chunk < bytes.length() / 64; chunk = chunk + 1 {
    let base = chunk * 64
    for t = 0; t < 16; t = t + 1 {
      let idx = base + t * 4
      w[t] = (bytes[idx] << 24) |
        (bytes[idx + 1] << 16) |
        (bytes[idx + 2] << 8) |
        bytes[idx + 3]
    }
    for t = 16; t < 64; t = t + 1 {
      let s0 = rotr(w[t - 15], 7) ^ rotr(w[t - 15], 18) ^ @algebra.int_lsr(w[t - 15], 3)
      let s1 = rotr(w[t - 2], 17) ^ rotr(w[t - 2], 19) ^ @algebra.int_lsr(w[t - 2], 10)
      w[t] = w[t - 16] + s0 + w[t - 7] + s1
    }
    let mut a = h0
    let mut b = h1
    let mut c = h2
    let mut d = h3
    let mut e = h4
    let mut f = h5
    let mut g = h6
    let mut hh = h7
    for i = 0; i < 64; i = i + 1 {
      let s1 = rotr(e, 6) ^ rotr(e, 11) ^ rotr(e, 25)
      let ch = (e & f) ^ ((e ^ 0xFFFFFFFF) & g)
      let temp1 = hh + s1 + ch + k[i] + w[i]
      let s0 = rotr(a, 2) ^ rotr(a, 13) ^ rotr(a, 22)
      let maj = (a & b) ^ (a & c) ^ (b & c)
      let temp2 = s0 + maj
      hh = g
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
    h7 = h7 + hh
  }
  hex(h0) + hex(h1) + hex(h2) + hex(h3) + hex(h4) + hex(h5) + hex(h6) + hex(h7)
}

///|
/// 32 位元循環右移（以 lsr 實現邏輯右移）。
fn rotr(x : Int32, n : Int32) -> Int32 {
  @algebra.int_lsr(x, n) | (x << (32 - n))
}

///|
fn hex(x : Int32) -> String {
  let digits = "0123456789abcdef"
  let d = chars_of(digits)
  let mut out = ""
  for i = 28; i >= 0; i = i - 4 {
    let nib = @algebra.int_lsr(x, i) & 0xF
    out = "\{out}\{d[nib]}"
  }
  out
}

///|
/// 32 位元邏輯右移（經 UInt 避免 Int 的算術移位）。
// ---------------------------------------------------------------- 紀元 (era) --

///| **紀元封條**：當審計的 payload 定義改變（新一輪的量測），舊鏈不能被偽造性地續接，

///| 只能被「封存」——新紀元的創世記錄把舊鏈頭 hash 放進 `prev`。

///|
/// 這樣兩個紀元被硬綁在一起：改動任一紀元的任一記錄，兩條鏈都會斷。
pub fn genesis_sealed(seal : String) -> SRec {
  let seq = 0
  let tag = "[S-GENESIS]"
  let kind = "genesis"
  let payload = "superlab-persistent-ledger-v1|seal=\{seal}"
  let prev = seal
  SRec::{
    seq,
    tag,
    kind,
    payload,
    prev,
    hash: rec_hash(seq, tag, kind, payload, prev),
  }
}

///|
/// 以封條開啟新紀元。
pub fn sled_new_sealed(seal : String) -> SLedger {
  SLedger::{ recs: [genesis_sealed(seal)], }
}

///| 從「首行即創世／紀元起點」的完整帳本驗證：

///|
/// 起點必須自洽（hash 重算相符），其後 seq 連續、prev 銜接、hash 相符。
pub fn sled_parse_lines_chain(lines : Array[String]) -> (Bool, Int32) {
  if lines.length() == 0 {
    return (false, 0)
  }
  let head = match sled_parse_line(lines[0]) {
    Some(r) => r
    None => return (false, 0)
  }
  if head.kind != "genesis" {
    return (false, 0)
  }
  if head.hash !=
    rec_hash(head.seq, head.tag, head.kind, head.payload, head.prev) {
    return (false, 0)
  }
  let mut prev_hash = head.hash
  let mut expect_seq = head.seq + 1
  let mut count = 0
  for i = 1; i < lines.length(); i = i + 1 {
    let r = sled_parse_line(lines[i])
    if r is None {
      return (false, count)
    }
    if r is Some(rec) {
      if rec.seq != expect_seq || rec.prev != prev_hash {
        return (false, count)
      }
      if rec.hash != rec_hash(rec.seq, rec.tag, rec.kind, rec.payload, rec.prev) {
        return (false, count)
      }
      prev_hash = rec.hash
      expect_seq = expect_seq + 1
      count = count + 1
    }
  }
  (true, count)
}
