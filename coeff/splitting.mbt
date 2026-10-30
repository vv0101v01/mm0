///| ## B4 的係數環版本：同一個多項式，不同環上的譜完全不同
///

///| 上一輪把 B4 的邊界從「位長牆」改寫成「`k(B)` 個素數的成本曲線」。

///| 但 CRT 重構有一個前提從未被寫下來：**素數不能整除判別式**。

///| 本檔案把這件事做成表：
///

///| 對 `f(x) = x² − D`（整係數），在任何素數 `p` 上恰好三種行為：

///|  - `p | disc(f)` ⇒ **分歧**（`f mod p` 有重根）；

///|  - `D` 是模 `p` 的二次剩餘 ⇒ **分裂**（兩個相異線性因子）；

///|  - 否則 ⇒ **惰性**（不可約）。
///

///| 同一個 `f`、同一個 `F_p`，只有「係數環的選擇」在改變答案。

///| 而壞素數正是判別式的素因子——這就是為什麼模 p 路徑必須先剔除它們。

///|
/// 多項式「在 `F_p` 上的行為」。
pub enum SplitKind {
  Ramified
  Split
  Inert
}

///|
pub fn split_show(k : SplitKind) -> String {
  match k {
    Ramified => "分歧"
    Split => "分裂"
    Inert => "惰性"
  }
}

///|
/// `x² − d` 在 `F_p` 上的行為（`d` 為整數，可負）。
pub fn quadratic_kind(d : Int32, p : Int32) -> SplitKind {
  let dd = (d % p + p) % p
  if p == 2 || dd == 0 {
    return Ramified
  }
  let mut is_sq = false
  for r = 1; r < p; r = r + 1 {
    if r * r % p == dd {
      is_sq = true
    }
  }
  if is_sq {
    Split
  } else {
    Inert
  }
}

///| 判別式的素因子集合（= 模 p 路徑的壞素數）。

///|
/// `x² − d` 的判別式是 `4d`，所以壞素數 = `{|d| 的素因子} ∪ {2}`（`4d` 的奇素因子即 `d` 的）。
pub fn bad_primes(d : Int32) -> Array[Int32] {
  let n = if d < 0 { 0 - d } else { d }
  let out : Array[Int32] = [2]
  let mut k = 3
  while k <= n && k < 1000000 {
    if n % k == 0 && @core.is_prime(k) {
      let mut dup = false
      for x in out {
        if x == k {
          dup = true
        }
      }
      if !dup {
        out.push(k)
      }
    }
    k = k + 2
  }
  out
}

///| 二次剩餘理論的可驗證形式：

///| `d` 是模奇素數 `p`（`p ∤ d`）的二次剩餘 ⟺ `d^{(p−1)/2} ≡ 1 (mod p)`。

///|
/// 與「枚舉平方」的暴力結果對照——兩條獨立路徑。
pub fn qr_rule_agrees(d : Int32, p : Int32) -> Bool {
  if p == 2 || (d % p + p) % p == 0 {
    return true
  }
  let brute = match quadratic_kind(d, p) {
    Split => true
    _ => false
  }
  let e = (p - 1) / 2
  let pow = @core.mod_pow((d % p + p) % p, e, p)
  let euler = pow == 1
  brute == euler
}

///|
/// 一個（模型多項式 × 素數）的分裂表列。
pub struct SplitRow {
  name : String
  d : Int32
  over_q_irreducible : Bool
  pieces : Array[(Int32, SplitKind)]
  bad : Array[Int32]
}

///| 建一列：`f = x² − d`。`over_q_irreducible` 由 golden 的

///|
/// `qpoly_is_irreducible`（精確 ℚ 判定）給出，`pieces` 由暴力求根給出。
pub fn split_row(d : Int32, primes : Array[Int32]) -> SplitRow {
  // f(x) = x² − d（低次到高次的係數）
  let f = @algebra.qpoly_normalize([
    @algebra.rat_int(0 - d),
    @algebra.rat_int(0),
    @algebra.rat_int(1),
  ])
  let irr = @algebra.qpoly_is_irreducible(f)
  let pieces : Array[(Int32, SplitKind)] = []
  for q in primes {
    pieces.push((q, quadratic_kind(d, q)))
  }
  SplitRow::{
    name: "x^2-\{d}",
    d,
    over_q_irreducible: irr,
    pieces,
    bad: bad_primes(d),
  }
}

///|
pub fn split_row_show(r : SplitRow) -> String {
  let mut s = "\{r.name}: 在 Q 上不可約=\{r.over_q_irreducible}；壞素數=\{bad_show(r.bad)}；"
  for pc in r.pieces {
    s = "\{s} p=\{pc.0}:\{split_show(pc.1)}"
  }
  s
}

///|
/// B4 的實驗輸出。
pub fn splitting_probe() -> Array[String] {
  let out : Array[String] = []
  let primes : Array[Int32] = [2, 3, 5, 7, 11, 13, 17, 23, 29, 31]
  for d in [2, 3, 5, -1] {
    out.push(split_row_show(split_row(d, primes)))
  }
  // 二次互反的兩個古典判據，用計算逐點驗證
  let mut ok2 = 0
  let mut n2 = 0
  let mut ok1 = 0
  let mut n1 = 0
  let mut euler_ok = 0
  let mut euler_n = 0
  for p = 3; p <= 97; p = p + 2 {
    if @core.is_prime(p) {
      n2 = n2 + 1
      let pred = p % 8 == 1 || p % 8 == 7
      let act = match quadratic_kind(2, p) {
        Split => true
        _ => false
      }
      if pred == act {
        ok2 = ok2 + 1
      }
      n1 = n1 + 1
      let pred1 = p % 4 == 1
      let act1 = match quadratic_kind(0 - 1, p) {
        Split => true
        _ => false
      }
      if pred1 == act1 {
        ok1 = ok1 + 1
      }
      euler_n = euler_n + 1
      if qr_rule_agrees(2, p) && qr_rule_agrees(0 - 1, p) {
        euler_ok = euler_ok + 1
      }
    }
  }
  out.push(
    "判據驗證 (p ≤ 97)：2 是二次剩餘 ⟺ p ≡ ±1 (mod 8)：\{ok2}/\{n2}；−1 是二次剩餘 ⟺ p ≡ 1 (mod 4)：\{ok1}/\{n1}；Euler 判準(d^((p−1)/2)) 與暴力枚舉一致：\{euler_ok}/\{euler_n}",
  )
  out.push(
    "結論：同一個 f，係數環從 Q 換到 F_p，譜就從「不可約」變成「分裂/惰性/分歧」；CRT 的充分性條件 p ∤ disc 因此是係數環語句，不是技術細節",
  )
  out
}

///| 壞素數清單顯示（不用 `Show`）。
fn bad_show(a : Array[Int32]) -> String {
  let mut out = "["
  for i = 0; i < a.length(); i = i + 1 {
    let t = a[i].to_string()
    out = if i == 0 {
      out + t
    } else {
      out + ", " + t
    }
  }
  out + "]"
}
