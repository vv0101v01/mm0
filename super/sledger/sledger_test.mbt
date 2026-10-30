///| sledger 測試：SHA-256 向量、雜湊鏈、冪等性、防篡改、JSONL 往返。

///|
test "[S-Ax-Ledger] SHA-256 標準測試向量" {
  assert_eq(
    @sledger.sha256_hex("abc"),
    "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad",
  )
  assert_eq(
    @sledger.sha256_hex(""),
    "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
  )
  assert_eq(
    @sledger.sha256_hex("The quick brown fox jumps over the lazy dog"),
    "d7a8fbb307d7809469ca9abcb0082e4f8d5651e46d3cdb762d02d0bf37c9e592",
  )
}

///|
test "[S-D-Ledger] 帳本記錄、冪等性與鏈頭" {
  let l = @sledger.sled_new()
  assert_eq(@sledger.sled_len(l), 1)
  assert_true(@sledger.sled_record(l, "[S-T-demo]", "theorem", "rank=3"))
  assert_true(@sledger.sled_record(l, "[S-T-demo2]", "experiment", "rows=10"))
  assert_false(@sledger.sled_record(l, "[S-T-demo]", "theorem", "rank=3"))
  assert_eq(@sledger.sled_len(l), 3)
  assert_true(@sledger.sled_verify(l))
}

///|
test "[S-P-Ledger] 篡改任何欄位都會被驗證拒絕" {
  let l = @sledger.sled_new()
  let _ = @sledger.sled_record(l, "[S-T-x]", "theorem", "payload_v1")
  let _ = @sledger.sled_record(l, "[S-T-y]", "corollary", "payload_v2")
  assert_true(@sledger.sled_verify(l))
  // 模擬篡改：改動 payload 後雜湊不再相符
  let l2 = @sledger.sled_tamper(l, "[S-T-y]", "TAMPERED")
  assert_false(@sledger.sled_verify(l2))
  // 原帳本仍通過
  assert_true(@sledger.sled_verify(l))
}

///|
test "[S-E-Ledger] JSONL 往返：序列化 → 剖析 → 驗鏈；篡改被拒" {
  let l = @sledger.sled_new()
  let _ = @sledger.sled_record(l, "[S-T-a]", "theorem", "det=6")
  let _ = @sledger.sled_record(l, "[S-NEG-b]", "negative", "conjecture_refuted")
  let jsonl = @sledger.sled_jsonl(l)
  let lines : Array[String] = []
  let mut cur = ""
  for c in jsonl {
    if c == '\n' {
      let _ = lines.push(cur)
      cur = ""
    } else {
      cur = "\{cur}\{c}"
    }
  }
  let tail : Array[String] = []
  for i = 1; i < lines.length(); i = i + 1 {
    let _ = tail.push(lines[i])
  }
  let (ok, count) = @sledger.sled_parse_lines(tail)
  assert_true(ok)
  assert_eq(count, 2)
  // 篡改一行後驗證失敗
  tail[0] = "{\"seq\":1,\"tag\":\"[S-T-a]\",\"kind\":\"theorem\",\"payload\":\"det=7\",\"prev\":\"x\",\"hash\":\"y\"}"
  let (ok2, _) = @sledger.sled_parse_lines(tail)
  assert_false(ok2)
}
