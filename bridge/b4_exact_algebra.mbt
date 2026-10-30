///| ## B4 —— 精確代數邊界：位元長度牆的量化與模 p + CRT 的位移
///

///| golden SPEC §四 第四條殘餘邊界：超越數不在 `Q̄` 內；極高維稠密不可約 Hermitian

///| 矩陣的特徵多項式係數位長仍受精確有理算術本質成長制約。
///

///| 合併動作（推遠 + 變化）：

///|  (a) 把「位長成長」從一堵牆改寫成一條**成本曲線**：

///|      模 p 的 Newton 恆等式／Faddeev–LeVerrier（`super/spec`）給出 「charpoly mod p」；

///|      Hadamard 界給出係數位長 `B(n)`；於是只要 `∏ p_i > 2·B` 個素數，

///|      逐素數比對即**證明**模路徑與 golden 精確路徑得到同一個多項式（CRT 單射）。

///|      成本 = k(n) × O(n⁴)，k(n) ∝ B(n) —— 對位長**線性**，而 BigInt 路徑對位長是超線性。

///|  (b) 「超越數」不可剔除，但可以把它換成一個誠實的判別器：

///|      有界高度整數關係搜尋（`integer_relation`）對 `{1, √2, 2+√2}` 給出關係，

///|      對 `{1, π, π²}` 一無所獲 —— 檢測器不會捏造關係，所以「不在 `Q̄`」仍可被報告。

// ------------------------------------------------------- 稠密 0/1 矩陣 ----

///|
/// 稠密 0/1 隨機矩陣（固定 LCG 種子，可重現）：係數會真正長大。
pub fn dense01(n : Int32) -> Array[Array[Int32]] {
  let rng = @core.rng_seed(20261029)
  let rows : Array[Array[Int32]] = []
  for _i = 0; _i < n; _i = _i + 1 {
    rows.push(Array::make(n, 0))
  }
  for i = 0; i < n; i = i + 1 {
    for j = i; j < n; j = j + 1 {
      let v = @core.rng_below(rng, 2)
      rows[i][j] = v
      rows[j][i] = v
    }
  }
  rows
}

///|
/// 十進位字串對 p 取模（長除法；BigInt 不必進場）。
fn dec_mod_p(s : String, p : Int32) -> Int32 {
  let mut v : Int32 = 0
  let mut start = 0
  if s.length() > 0 && s.code_unit_at(0) == 45 {
    start = 1
  }
  for i = start; i < s.length(); i = i + 1 {
    let c = s.code_unit_at(i).to_int()
    if c >= 48 && c <= 57 {
      v = (v * 10 + (c - 48)) % p
    }
  }
  if start == 1 && v != 0 {
    p - v
  } else {
    v
  }
}

///| 位長上界：Hadamard 界對 0/1 矩陣給 |c_k| ≤ C(n,k)·n^{k/2}；

///| 取 log2 的保守上界 B ≤ n·(log2 n)/2 + n·log2(e·?)… 這裡直接用

///|
/// log2 B = k·log2(n)/2 + log2 C(n,k) 的最大值（取 k = n/2 附近的上一整數）。
pub fn coeff_bit_bound(n : Int32) -> Double {
  let mut lg_choose : Double = 0.0
  for i = 1; i <= n; i = i + 1 {
    lg_choose = lg_choose + (log2f(n - i + 1) - log2f(i))
  }
  // 只用 k = n 的上界過寬；取 C(n, n) = 1 但 n^{n/2} 主導；
  // 保守做法：k 從 0..n 取最大值
  let mut best : Double = 0.0
  let mut lgc : Double = 0.0
  for k = 0; k <= n; k = k + 1 {
    if k > 0 {
      lgc = lgc + log2f(n - k + 1) - log2f(k)
    }
    let v = lgc + k.to_double() / 2.0 * log2f(n)
    if v > best {
      best = v
    }
  }
  best
}

///|
fn log2f(x : Int32) -> Double {
  log2d(x.to_double())
}

///|
fn log2d(x : Double) -> Double {
  let mut y = x
  let mut k = 0.0
  while y >= 2.0 {
    y = y / 2.0
    k = k + 1.0
  }
  while y < 1.0 {
    y = y * 2.0
    k = k - 1.0
  }
  // log2(y) 的收斂級數：log2(y) = ln(y)/ln2，以 atanh 展開
  let z = (y - 1.0) / (y + 1.0)
  let z2 = z * z
  let mut term = z
  let mut sum = 0.0
  for i = 0; i < 24; i = i + 1 {
    sum = sum + term / (2.0 * i.to_double() + 1.0)
    term = term * z2
  }
  k + 2.0 * sum / 0.6931471805599453
}

///|
/// 一個特徵多項式的量測紀錄。
pub struct CharpolyRun {
  n : Int32
  max_digits : Int32
  bit_bound : Int32
  primes_needed : Int32
  primes_used : Int32
  residues_match : Bool
  cayley_hamilton_mod : Bool
}

///| [E-ModCharpoly] 模 p 路徑與 golden 精確路徑的逐係數比對。

///|
/// 只要 `∏ p_i > 2·2^{B}`，逐素數相等即推出多項式相等（CRT 單射）。
pub fn charpoly_probe(n : Int32, use_primes : Int32) -> CharpolyRun {
  let rows = dense01(n)
  let exact = @algebra.qmat_charpoly(@algebra.qmat_from_int_rows(rows))
  // 精確係數的十進位字串（不解析成整數，只取長度與模 p 餘數）
  let big = @algebra.qpoly_integer_coeffs_big(exact)
  let strs : Array[String] = []
  let mut max_digits : Int32 = 0
  for b in big {
    let s = b.to_string()
    let d = if s.length() > 0 && s.code_unit_at(0) == 45 {
      s.length() - 1
    } else {
      s.length()
    }
    if d > max_digits {
      max_digits = d
    }
    strs.push(s)
  }
  let ps : Array[Int32] = [10007, 20011, 30011, 46327, 46309, 40009]
  let mut used : Int32 = 0
  let mut match_all = true
  let mut ch_ok = true
  let mut logprod : Double = 0.0
  let bits = coeff_bit_bound(n)
  // 自適應：累積素數直到 ∏p > 2·2^B（CRT 單射的充分條件）
  while used < use_primes && used < ps.length() && logprod <= bits + 1.0 {
    let p = ps[used]
    if @core.is_prime(p) {
      let m = @core.mat_from_rows(rows)
      let cp = @spec.charpoly(m, p)
      let ch = @spec.check_cayley_hamilton(m, p)
      if !ch {
        ch_ok = false
      }
      for k = 0; k <= n; k = k + 1 {
        let ex = dec_mod_p(strs[k], p)
        if ex != (cp[k] % p + p) % p {
          match_all = false
        }
      }
      logprod = logprod + log2f(p)
    }
    used = used + 1
  }
  let primes_needed = ((bits + 1.0) / log2f(30011)).to_int() + 1
  let enough = logprod > bits + 1.0
  CharpolyRun::{
    n,
    max_digits,
    bit_bound: bits.to_int(),
    primes_needed,
    primes_used: used,
    residues_match: match_all && enough,
    cayley_hamilton_mod: ch_ok,
  }
}

///|
/// B4 的實驗輸出。
pub fn b4_probe() -> Array[String] {
  let out : Array[String] = []
  for n = 8; n <= 24; n = n + 4 {
    let r = charpoly_probe(n, 6)
    out.push(
      "n=\{r.n}: 精確係數最大十進位位數=\{r.max_digits} Hadamard 位界=\{r.bit_bound} bit 需素數≈\{r.primes_needed} 用=\{r.primes_used} 逐素數一致(含 CRT 充分性)=\{r.residues_match} mod-p Cayley–Hamilton=\{r.cayley_hamilton_mod}",
    )
  }
  // 超越數方向的「誠實判別器」
  let r1 = @core.integer_relation(
    [1.0, 1.4142135623730951, 3.414213562373095],
    3,
    1024,
    1.0e-7,
  )
  let r2 = @core.integer_relation(
    [1.0, 3.141592653589793, 9.869604401089358],
    3,
    1024,
    1.0e-7,
  )
  let s1 = match r1 {
    Some(r) => "\{r.coeffs.length()} 個係數 \{rat_list_show(r.coeffs)}（殘差=\{r.residual}）"
    None => "無"
  }
  let s2 = match r2 {
    Some(r) => "\{r.coeffs.length()} 個係數 \{rat_list_show(r.coeffs)}（殘差=\{r.residual}）"
    None => "無（誠實拒絕）"
  }
  out.push("整數關係 (1,√2,2+√2) → \{s1}")
  out.push(
    "整數關係 (1,π,π²) → \{s2}：有界高度搜尋不會捏造超越數關係",
  )
  out
}

///| 有理係數清單顯示（不用 `Show`）。
fn rat_list_show(a : Array[Int32]) -> String {
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
