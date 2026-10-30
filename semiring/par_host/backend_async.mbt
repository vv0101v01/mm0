// ===========================================================================
// 主機後端（native）：`moonbitlang/async` 的結構化併發
//
// 這是一個**平台擴充套件**：只有 native 才編譯（`moon.pkg` 的 supported_targets），
// 因此 `par/` 本身不需要依賴 async，所有 target 都能無警告編譯。
// 兩邊共享同一組型別（`@par.ShardIO`）與同一組語義，
// 呼叫端只要換一個 import 就換後端，演算法與結果都不變。
//
// 每一段是一個獨立的 task，掛在同一個 `TaskGroup` 上：
//   * 群組結束時保證所有子任務都已結束（不會有懸掛的工作）；
//   * 任一子任務丟出錯誤 ⇒ 群組取消其餘任務（結構化取消）；
//   * 使用者程式碼仍然是單執行緒，因此不需要鎖 —— 但這也是
//     它不能加速 CPU 密集工作的原因（見 par.mbt 的說明）。
// ===========================================================================

///|
/// 後端名稱。
pub fn backend_name() -> String {
  "async(single-thread, structured)"
}

///|
/// 主機後端是否存在於這個 target 上（編譯期已知：只有 native 有這個套件）。
pub fn is_host_backend() -> Bool {
  true
}

///|
/// 以 task group 併發執行每一段，並等待全部完成。
pub fn par_for(chunks : Int32, f : (Int32) -> Unit) -> Unit {
  if chunks <= 0 {
    return
  }
  @async.run_async_main(async fn() -> Unit {
    @async.with_task_group(fn(g : @async.TaskGroup[Unit]) -> Unit {
      for k in 0..<chunks {
        g.spawn_bg() <| () => { f(k) }
      }
    })
  })
}

// ---------------------------------------------------------------------------
// I/O 重疊：同一個檔案內容寫成 n 份，先循序讀、再併發讀
//
// 這是非同步後端唯一能真正加速的地方：讀檔被丟到內部的 I/O 執行緒池，
// 主執行緒在等待時可以推進其他任務。循序版在同一個事件迴圈上
// 一個 await 完再接下一個，因此兩者的差異完全來自重疊。
// ---------------------------------------------------------------------------

///|
async fn read_shard(path : String) -> Bytes {
  let f = @fs.open(path, mode=@fs.ReadOnly)
  let n = f.size()
  let bytes = f.read_exactly_at(n.to_int(), position=0L)
  f.close()
  bytes
}

///|
/// 一次 I/O 量測結果（時間單位：微秒）。型別定義在 `par/`，兩個後端共用。

///|
/// 把 `payload` 寫成 `files` 份到 `/tmp`，量測循序讀與併發讀。
pub fn shard_io_bench(payload : String, files : Int32) -> @par.ShardIO {
  let out : Array[Double] = Array::make(3, 0.0)
  let flags : Array[Bool] = Array::make(1, false)
  let seq_store : Array[Array[Bytes]] = Array::make(1, [])
  let par_store : Array[Array[Bytes]] = Array::make(1, [])
  @async.run_async_main(async fn() -> Unit {
    let paths : Array[String] = Array::makei(files, fn(k) {
      "/tmp/semiring_shard_\{k}.txt"
    })
    for p in paths {
      @fs.write_file(p, payload) |> ignore
    }
    let t0 = @bench.monotonic_clock_start()
    let seq : Array[Bytes] = []
    for p in paths {
      seq.push(read_shard(p))
    }
    let t1 = @bench.monotonic_clock_end(t0)
    let slots : Array[Bytes] = Array::make(files, b"")
    let t2 = @bench.monotonic_clock_start()
    @async.with_task_group(fn(g : @async.TaskGroup[Unit]) -> Unit {
      for k in 0..<files {
        g.spawn_bg() <| () => { slots[k] = read_shard(paths[k]) }
      }
    })
    let t3 = @bench.monotonic_clock_end(t2)
    let mut same = true
    let mut total = 0
    for k in 0..<files {
      total = total + seq[k].length()
      if seq[k] != slots[k] {
        same = false
      }
    }
    out[0] = t1
    out[1] = t3
    out[2] = total.to_double()
    flags[0] = same
    seq_store[0] = seq
    par_store[0] = slots
  })
  @par.ShardIO::{
    seq_us: out[0],
    par_us: out[1],
    bytes: out[2].to_int(),
    files,
    same: flags[0],
    seq_data: seq_store[0],
    par_data: par_store[0],
  }
}
