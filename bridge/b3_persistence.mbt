///| ## B3 —— 持久層邊界：從純函數抽象位元組到跨執行、可篡改偵測的雜湊鏈帳本
///

///| golden SPEC §四 第三條殘餘邊界：底層儲存介面刻意保持純函數／抽象位元組儲存協議，

///| 不直接耦合 POSIX `flock`／`mmap`／`fsync`，也不含網路共識層。
///

///| 合併動作（突破 + 變化）：

///|  golden 的 `CHWALJRN`（崩潰一致 WAL）是**程序內**的純結構；notebook 的

///|  `sledger` 是**跨執行**的 SHA-256 雜湊鏈，配 shell 的 append/verify 適配器。

///|  合併後：純核心（雜湊、鏈驗證、解析）留在 MoonBit，落盤由 shell 完成，

///|  於是得到「跨程序、可重放、可偵測竄改、可外部錨定」的審計鏈，

///|  而**沒有**把核心綁死在 POSIX 或網路上 ——

///|  邊界不是被無視，而是被切成「純核心 / 宿主適配器」兩層並各自守住。

///|
/// 一次跨執行寫入的結果。
pub struct LedgerRun {
  records : Int32
  head : String
  verify_ok : Bool
  tamper_detected : Bool
  replay_ok : Bool
  jsonl_lines : Int32
  dbg : Int32
}

///| [E-Ledger] 由一組（tag, payload）建立帳本：冪等追加、全鏈驗證、

///|
/// 竄改實驗、以及「外部 JSONL → 解析 → 驗證」的往返。
pub fn ledger_run(entries : Array[(String, String)]) -> LedgerRun {
  let l = @sledger.sled_new()
  for e in entries {
    let _ = @sledger.sled_record(l, e.0, "audit", e.1)
  }
  let ok = @sledger.sled_verify(l)
  let head = @sledger.sled_head(l)
  let jsonl = @sledger.sled_jsonl(l)
  let lines : Array[String] = []
  let mut cur = ""
  for c in jsonl {
    if c == '\n' {
      if cur != "" {
        lines.push(cur)
      }
      cur = ""
    } else {
      cur = "\{cur}\{c}"
    }
  }
  // 驗證器的契約是「創世之後的尾鏈」（seq 從 1 開始）——這種隱含契約
  // 正是合併時必須寫下來的東西，否則兩個庫各自「正確」卻接不起來。
  let tail : Array[String] = []
  for i = 1; i < lines.length(); i = i + 1 {
    tail.push(lines[i])
  }
  let (replay_ok, n_tail) = @sledger.sled_parse_lines(tail)
  let dbg_lines = n_tail
  // 竄改：改掉第一筆非創世記錄的 payload，鏈驗證必須失敗
  let tampered = @sledger.sled_tamper(l, entries[0].0, "TAMPERED")
  let tamper_detected = !@sledger.sled_verify(tampered)
  LedgerRun::{
    records: @sledger.sled_len(l),
    head,
    verify_ok: ok,
    tamper_detected,
    replay_ok,
    jsonl_lines: n_tail,
    dbg: dbg_lines,
  }
}

///|
/// 冪等性：同一批記錄追加兩次，長度不變。
pub fn ledger_idempotent() -> Bool {
  let l = @sledger.sled_new()
  let entries : Array[(String, String)] = [
    ("B1", "levels=ok"),
    ("B2", "clique=ok"),
  ]
  for e in entries {
    let _ = @sledger.sled_record(l, e.0, "audit", e.1)
  }
  let n1 = @sledger.sled_len(l)
  for e in entries {
    let _ = @sledger.sled_record(l, e.0, "audit", e.1)
  }
  @sledger.sled_len(l) == n1
}

///|
/// B3 的實驗輸出。
pub fn b3_probe() -> Array[String] {
  let out : Array[String] = []
  let entries : Array[(String, String)] = [
    ("B1-schema", "levels_decidable=true"),
    ("B2-dsystem", "clique_rank_bound=exact-on-multipartite;h2_basis=generated"),
    ("B4-algebra", "modperm_charpoly=agrees"),
    ("B6-homotopy", "H1(RP2)=Z/2 certified"),
  ]
  let r = ledger_run(entries)
  out.push(
    "帳本: 記錄=\{r.records}（含創世）head=\{substr(r.head, 0, 16)}… 全鏈驗證=\{r.verify_ok} 竄改偵測=\{r.tamper_detected} JSONL 重放=\{r.replay_ok} 行數=\{r.jsonl_lines}",
  )
  out.push(
    "冪等追加（同批記錄兩次不增長）=\{ledger_idempotent()}",
  )
  out.push(
    "跨執行：`sh ledger/audit.sh append` 把本次 JSONL 去重追加到 ledger/BOUNDARY.jsonl；`verify` 用 MoonBit 解析器全鏈重驗 ⇒ 跨程序、無需 fs 綁定、可外部錨定 head",
  )
  out
}

///|
fn substr(s : String, from : Int32, len : Int32) -> String {
  let mut out = ""
  let mut i = 0
  for c in s {
    if i >= from && i < from + len {
      out = "\{out}\{c}"
    }
    i = i + 1
  }
  out
}
