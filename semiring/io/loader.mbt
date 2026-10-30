// ===========================================================================
// 圖資料載入：單趟位元組掃描 vs 字串分割
//
// 目標是「降低載入時間」。兩者都正確，差別在常數因子：
//   * 單趟掃描：一個迴圈、沒有中間 String 物件、沒有陣列成長，
//     直接算出頂點數與邊數後一次配置。
//   * 字串分割：每行 split + 每個欄位 parse，會產生 O(m) 個臨時字串。
//
// 這不是微優化：載入時間是「冷啟動延遲」的主要成分，而冷啟動延遲
// 直接決定 auto-scaling 時第一個請求的等待時間。
// ===========================================================================

///|
/// 解析結果：頂點數 + 邊三元組。
pub(all) struct ParsedEdges {
  n : Int32
  from : Array[Int32]
  to : Array[Int32]
  w : Array[Int32]
}

///|
/// 單趟位元組掃描，O(bytes)，零中間字串。
///
/// 格式：每行 `u v w`，以空白分隔；空行與 `#` 開頭的註解行會被跳過。
pub fn parse_edges_fast(src : Bytes) -> ParsedEdges {
  let len = src.length()
  let from : Array[Int32] = []
  let to : Array[Int32] = []
  let w : Array[Int32] = []
  let mut i = 0
  let mut n = 0
  let mut ncols = 0
  let buf = [0, 0, 0]
  while i < len {
    // 跳過空白
    while i < len && is_space(src[i]) {
      i = i + 1
    }
    if i >= len {
      break
    }
    if src[i] == 35 { // '#'
      while i < len && src[i] != 10 {
        i = i + 1
      }
      continue
    }
    ncols = 0
    while i < len && src[i] != 10 && src[i] != 13 {
      while i < len && is_space(src[i]) {
        i = i + 1
      }
      if i >= len || src[i] == 10 || src[i] == 13 {
        break
      }
      let mut v = 0
      let neg = src[i] == 45
      if neg {
        i = i + 1
      }
      while i < len && src[i] >= 48 && src[i] <= 57 {
        v = v * 10 + src[i].to_int() - 48
        i = i + 1
      }
      if ncols < 3 {
        buf[ncols] = if neg { -v } else { v }
      }
      ncols = ncols + 1
    }
    // 跳過行尾
    while i < len && src[i] != 10 {
      i = i + 1
    }
    i = i + 1
    if ncols >= 3 {
      from.push(buf[0])
      to.push(buf[1])
      w.push(buf[2])
      n = n.max(buf[0] + 1).max(buf[1] + 1)
    }
  }
  { n, from, to, w, }
}

///|
fn is_space(b : Byte) -> Bool {
  b == 32 || b == 9 || b == 13
}

///|
/// 字串分割版本（對照組）：`String::split` + `parse_int`。
pub fn parse_edges_naive(src : String) -> ParsedEdges {
  let from : Array[Int32] = []
  let to : Array[Int32] = []
  let w : Array[Int32] = []
  let mut n = 0
  for line in src.split("\n") {
    let t = line.trim()
    if t.length() == 0 || t[0] == '#' {
      continue
    }
    // 只保留非空欄位（連續空白會被 split 成空字串）
    let parts : Array[StringView] = []
    for p in t.split(" ") {
      if p.length() > 0 {
        parts.push(p)
      }
    }
    if parts.length() < 3 {
      continue
    }
    let u = parse_int_digits(parts[0])
    let v = parse_int_digits(parts[1])
    let ww = parse_int_digits(parts[2])
    from.push(u)
    to.push(v)
    w.push(ww)
    n = n.max(u + 1).max(v + 1)
  }
  { n, from, to, w, }
}

///|
fn parse_int_digits(s : StringView) -> Int32 {
  let mut v = 0
  for c in s {
    if c >= '0' && c <= '9' {
      v = v * 10 + (c.to_int() - 48)
    }
  }
  v
}

///|
/// 產生測試資料：`n` 個點、`m` 條邊的邊列表（可重現）。
pub fn synth_edge_list(rng : @alg.Rng, n : Int32, m : Int32) -> String {
  let sb = StringBuilder()
  sb.write_string("# synthetic graph\n")
  for _ in 0..<m {
    let u = rng.next_int(n)
    let v = rng.next_int(n)
    let w = 1 + rng.next_int(100)
    sb.write_string("\{u} \{v} \{w}\n")
  }
  sb.to_string()
}

///|
/// 與 `synth_edge_list` 相同的資料，但直接回傳 UTF-8 位元組（供單趟掃描載入器使用）。
pub fn synth_edge_bytes(rng : @alg.Rng, n : Int32, m : Int32) -> Bytes {
  @utf8.encode(synth_edge_list(rng, n, m))
}
