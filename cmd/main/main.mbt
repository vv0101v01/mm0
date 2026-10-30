///| ## `cmd/main` —— 定理登記表的入口（116 條）
///
///|  1. 無引數：逐條印 `[PASS]`／`[FAIL]`，最後 `passed n/116`；
///|  2. `--time`：逐條計時（`@mbench`），最後印總時間與最慢的 8 條；
///|  3. `--only <子串>`：只跑名字含該子串的條目（除錯用，省掉 60 秒的全跑）。
///
///| 為什麼要有 `--time`：整張表過去是一口氣跑完、只知道「全部通過」，
///| 不知道**哪一條**在吃時間。有了逐條計時，慢的定理會自己現形 ——
///| 這正是第 9 輪健檢抓到的第一件事（見 `SPEC.md` §4.15）。
///| 一位小數的毫秒字串（wasm-gc 沒有 `{:.1}` 格式插值）。
fn fmt1(x : Double) -> String {
  let scaled = x * 10.0
  let v = if scaled < 0.0 { -1 } else { scaled.to_int() }
  "\{v / 10}.\{v % 10}"
}

fn main {
  let raw = @env.args()
  let args : Array[String] = []
  for i = 1; i < raw.length(); i = i + 1 {
    args.push(raw[i])
  }
  let mut mode = "run"
  let mut filter = ""
  for a in args {
    if a == "--time" {
      mode = "time"
    } else if a == "--only" {
      mode = "only"
    } else if a == "--all" {
      mode = "run"
    } else {
      filter = a
    }
  }
  let reg = @lib.check_registry()
  if mode == "time" {
    let t0 = @mbench.monotonic_clock_start()
    let mut passed = 0
    let names : Array[String] = []
    let times : Array[Double] = []
    for pair in reg {
      let (name, f) = pair
      if filter != "" && !name.contains(filter) {
        continue
      }
      let s = @mbench.monotonic_clock_start()
      let ok = f()
      let ms = @mbench.monotonic_clock_end(s) / 1000.0
      if ok {
        passed = passed + 1
      }
      names.push(name)
      times.push(ms)
      println("\{fmt1(ms)} ms  \{if ok { "PASS" } else { "FAIL" }}  \{name}")
    }
    let total = @mbench.monotonic_clock_end(t0) / 1000.0
    println("")
    println("total \{fmt1(total)} ms；passed \{passed}/\{names.length()}")
    // 最慢的 8 條（插入排序，n 只有一百多）
    let idx : Array[Int] = []
    for i = 0; i < times.length(); i = i + 1 {
      idx.push(i)
    }
    let mut i = 1
    while i < idx.length() {
      let x = idx[i]
      let mut j = i - 1
      while j >= 0 && times[idx[j]] < times[x] {
        idx[j + 1] = idx[j]
        j = j - 1
      }
      idx[j + 1] = x
      i = i + 1
    }
    println("最慢 8 條：")
    let top = if idx.length() < 8 { idx.length() } else { 8 }
    for k = 0; k < top; k = k + 1 {
      println("  \{fmt1(times[idx[k]])} ms  \{names[idx[k]]}")
    }
    return
  }
  let mut passed = 0
  let mut total = 0
  for pair in reg {
    let (name, f) = pair
    if filter != "" && !name.contains(filter) {
      continue
    }
    total = total + 1
    if f() {
      passed = passed + 1
      println("[PASS] \{name}")
    } else {
      println("[FAIL] \{name}")
    }
  }
  println("passed \{passed}/\{total}")
  if passed != total {
    abort("theorem registry failed")
  }
}
