// 序列後端：本套件的**預設**後端，在所有 target 上都能編譯。
// 語義：一樣的分段、一樣的呼叫順序、一樣的結果。
//
// 主機後端（native 的結構化併發）在 `par_host/`，它以型別相容的方式
// 提供同一組操作；兩者的結果必須逐位元相同（見兩邊的測試）。

///|
/// 後端名稱。
pub fn backend_name() -> String {
  "serial"
}

///|
/// 依序執行每一段。
pub fn par_for(chunks : Int32, f : (Int32) -> Unit) -> Unit {
  for k in 0..<chunks {
    f(k)
  }
}

///|
/// 分片 I/O 量測結果。
///
/// 欄位的意義由後端決定：`par` 的序列後端沒有檔案系統，因此全部是 0/false；
/// `@par_host` 的非同步後端會填入真量測值。型別放在這裡是刻意的——
/// 呼叫端只依賴這個型別，不依賴是哪一個後端填的。
pub(all) struct ShardIO {
  seq_us : Double
  par_us : Double
  bytes : Int32
  files : Int32
  same : Bool
  seq_data : Array[Bytes]
  par_data : Array[Bytes]
}

///|
/// 序列後端沒有檔案系統（js / wasm / wasm-gc），回傳空結果。
pub fn shard_io_bench(_payload : String, files : Int32) -> ShardIO {
  {
    seq_us: 0.0,
    par_us: 0.0,
    bytes: 0,
    files,
    same: false,
    seq_data: [],
    par_data: [],
  }
}
