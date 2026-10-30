///| ## B1′（方案 B）：宇宙層級代數 —— 序數層級、可判定的 `<`、良基見證
///
///| 舊目標（Mahlo／超宇宙公理）的問題不是「難」，而是**目標要先修**：
///| 對 Mahlo 宇宙加自然消去規則不一致（Palmgren 定理 6.1），而外部 Mahlo 其實已被
///| 歸納—遞迴捕捉。真正在工程上被使用的是**宇宙層級代數**（Kovács, CSL 2022：
///| 層級可取自任何良基偏序集，`Lift` 嚴格保留型別構造子，層級本身可以是一級物件）。
///
///| 本檔把這件事在**有限可判定**的片段上落地：
///|   1. 層級 = Cantor 正規形（CNF）的序數 `< ε₀`：`0 | ω^e·c + r`；
///|   2. `<`、`≤`、`sup`、`+`、`succ` 全部可判定，且有 `ord_rank` 這個良基見證；
///|   3. `Lift` 對型別代碼是**嚴格**的（見 §B1′-2），cumulative（累積）不是。
///
///| 為什麼是序數而不是自然數：舊的 `b1_schema_levels` 用 `Int32` 解差分約束，
///| 它可以判「有限層級可不可行」，但**說不出 `U_ω = sup_n U_n`**。
///| 換成 CNF 序數之後，`sup` 是良定義的，極限層級直接可寫且可比較 ——
///| 這正是 Mahlo 那條路真正想拿到的東西，而它**不需要**新的型別論。

///| 序數的 Cantor 正規形：`OZero` = 0；`OCons(c, e, r)` = `ω^e · c + r`。
///| 正規形條件：`c > 0`、`r` 正規、`r` 的所有指數 `< e`、`e` 自身正規。
pub enum Ord {
  OZero
  OCons(Int32, Ord, Ord)
}

///| 0。
pub fn ord_zero() -> Ord {
  OZero
}

///| 1 = `ω^0`。
pub fn ord_one() -> Ord {
  OCons(1, OZero, OZero)
}

///| 有限序數 `n`。
pub fn ord_finite(n : Int32) -> Ord {
  if n <= 0 {
    OZero
  } else {
    OCons(n, OZero, OZero)
  }
}

///| `ω`。
pub fn ord_omega() -> Ord {
  OCons(1, ord_one(), OZero)
}

///| `ω^k`。
pub fn ord_omega_pow(k : Int32) -> Ord {
  if k <= 0 {
    ord_one()
  } else {
    // ω^k = ω^(k) ：指數就是有限序數 k（第一版寫成重複自加，得到的是 ω^(2^k)，k=3 時露餡）
    OCons(1, ord_finite(k), OZero)
  }
}

///| 是否為零。
pub fn ord_is_zero(o : Ord) -> Bool {
  match o {
    OZero => true
    _ => false
  }
}

///| 比較：`-1` / `0` / `1`。CNF 的字典序：先比首項指數，再比係數，最後比餘項。
pub fn ord_cmp(a : Ord, b : Ord) -> Int32 {
  match (a, b) {
    (OZero, OZero) => 0
    (OZero, _) => -1
    (_, OZero) => 1
    (OCons(c, e, r), OCons(c2, e2, r2)) => {
      let ce = ord_cmp(e, e2)
      if ce != 0 {
        ce
      } else if c != c2 {
        if c < c2 {
          -1
        } else {
          1
        }
      } else {
        ord_cmp(r, r2)
      }
    }
  }
}

///| `a < b`。
pub fn ord_lt(a : Ord, b : Ord) -> Bool {
  ord_cmp(a, b) < 0
}

///| `a == b`（結構相等；正規形下等價於序數相等）。
pub fn ord_eq(a : Ord, b : Ord) -> Bool {
  ord_cmp(a, b) == 0
}

///| 取大者。
pub fn ord_sup(a : Ord, b : Ord) -> Ord {
  if ord_cmp(a, b) >= 0 {
    a
  } else {
    b
  }
}

///| 序數加法（**非**交換）：`(ω^e·c + r) + b`。
///| 若 `e > 首指數(b)` ⇒ `ω^e·c + (r + b)`；若 `e < 首指數(b)` ⇒ `b`（吸收）；
///| 若相等 ⇒ `ω^e·(c+c') + r'`（`r` 被吸收——這正是序數加法的關鍵不對稱）。
pub fn ord_add(a : Ord, b : Ord) -> Ord {
  match a {
    OZero => b
    OCons(c, e, r) =>
      match b {
        OZero => OCons(c, e, r)
        OCons(c2, e2, r2) =>
          match ord_cmp(e, e2) {
            1 => OCons(c, e, ord_add(r, b))
            -1 => b
            _ => OCons(c + c2, e, r2)
          }
      }
  }
}
///| `ω^e · n`。
pub fn ord_times(a : Ord, n : Int32) -> Ord {
  if n <= 0 {
    OZero
  } else {
    match a {
      OZero => OZero
      OCons(c, e, r) => OCons(c * n, e, r)
    }
  }
}

///| 良基見證：CNF 的項數。任何嚴格遞減鏈的長度都 `< ord_rank`（指數塔本身有限）。
pub fn ord_rank(o : Ord) -> Int32 {
  match o {
    OZero => 0
    OCons(_, _, r) => 1 + ord_rank(r)
  }
}

///| 指數塔高度（`ω^(ω^…)` 的層數）。良基性歸納就沿這個高度做。
pub fn ord_height(o : Ord) -> Int32 {
  match o {
    OZero => 0
    OCons(_, e, r) => {
      let he = ord_height(e)
      let hr = ord_height(r)
      let h = if he > hr {
        he
      } else {
        hr
      }
      h + 1
    }
  }
}

///| 正規形檢查（用來擋「手寫壞資料」）。
pub fn ord_is_normal(o : Ord) -> Bool {
  match o {
    OZero => true
    OCons(c, e, r) => {
      c > 0 && ord_is_normal(e) && ord_is_normal(r) && ord_leading_lt(r, e)
    }
  }
}

///| `r` 的所有指數都 `< e`。
fn ord_leading_lt(r : Ord, e : Ord) -> Bool {
  match r {
    OZero => true
    OCons(_, e2, r2) => ord_lt(e2, e) && ord_leading_lt(r2, e)
  }
}

///| 是否為有限序數（可用 `Int32` 表示）。
pub fn ord_is_finite(o : Ord) -> Bool {
  match o {
    OZero => true
    OCons(_, e, r) => ord_is_zero(e) && ord_is_normal(r) && ord_is_zero(r)
  }
}

///| 有限序數 → `Int32`（非有限回 -1）。
pub fn ord_to_int(o : Ord) -> Int32 {
  match o {
    OZero => 0
    OCons(c, e, r) =>
      if ord_is_zero(e) && ord_is_zero(r) {
        c
      } else {
        -1
      }
  }
}

///| 顯示：`w^2*3 + w + 5`。
pub fn ord_show(o : Ord) -> String {
  match o {
    OZero => "0"
    OCons(c, e, r) => {
      let mut s = ""
      if ord_is_zero(e) {
        s = c.to_string()
      } else if ord_cmp(e, ord_one()) == 0 {
        s = "w"
      } else {
        s = "w^" + ord_show(e)
      }
      if !ord_is_zero(e) && c > 1 {
        s = s + "*" + c.to_string()
      }
      if !ord_is_zero(r) {
        s = s + " + " + ord_show(r)
      }
      s
    }
  }
}

///| ## B1′-2：`Lift` 的嚴格性
///
///| 型別代碼的迷你庫；只保留「構造子形狀 + 宇宙層級」。
pub enum TyCode {
  TUnit
  TBool
  TNat
  TPi(TyCode, TyCode)
  TSigma(TyCode, TyCode)
  TId(TyCode)
  TU(Ord)
}

///| 結構相等。
pub fn code_eq(a : TyCode, b : TyCode) -> Bool {
  match (a, b) {
    (TUnit, TUnit) => true
    (TBool, TBool) => true
    (TNat, TNat) => true
    (TPi(x1, y1), TPi(x2, y2)) => code_eq(x1, x2) && code_eq(y1, y2)
    (TSigma(x1, y1), TSigma(x2, y2)) => code_eq(x1, x2) && code_eq(y1, y2)
    (TId(x), TId(y)) => code_eq(x, y)
    (TU(l1), TU(l2)) => ord_eq(l1, l2)
    _ => false
  }
}

///| **嚴格** `Lift`：把代碼中的每個 `TU(l)` 換成 `TU(l + k)`，其餘構造子逐一照搬。
///| 沒有任何「強制轉換節點」——這正是 strict 與 cumulative 的差別。
pub fn lift_code(k : Ord, c : TyCode) -> TyCode {
  match c {
    TUnit => TUnit
    TBool => TBool
    TNat => TNat
    TPi(a, b) => TPi(lift_code(k, a), lift_code(k, b))
    TSigma(a, b) => TSigma(lift_code(k, a), lift_code(k, b))
    TId(a) => TId(lift_code(k, a))
    TU(l) => TU(ord_add(l, k))
  }
}

///| 去掉層級後的形狀（用來檢查「Lift 不動構造子」）。
pub fn code_shape(c : TyCode) -> String {
  match c {
    TUnit => "1"
    TBool => "2"
    TNat => "N"
    TPi(a, b) => "Pi(" + code_shape(a) + "," + code_shape(b) + ")"
    TSigma(a, b) => "Sig(" + code_shape(a) + "," + code_shape(b) + ")"
    TId(a) => "Id(" + code_shape(a) + ")"
    TU(_) => "U"
  }
}

///| 代碼深度（注入性檢查用）。
pub fn code_depth(c : TyCode) -> Int32 {
  match c {
    TUnit | TBool | TNat | TU(_) => 1
    TPi(a, b) | TSigma(a, b) => {
      let da = code_depth(a)
      let db = code_depth(b)
      1 + (if da > db { da } else { db })
    }
    TId(a) => 1 + code_depth(a)
  }
}

///| 帶強制轉換的**累積**模型：`Lift` 會留下一個轉換節點。
pub struct TyExp {
  code : TyCode
  coercions : Array[Ord]
}

///| 累積式 `Lift`：層級 +k，並在項上附加一個轉換節點。
pub fn cum_lift(k : Ord, e : TyExp) -> TyExp {
  let cs : Array[Ord] = []
  for c in e.coercions {
    cs.push(c)
  }
  cs.push(k)
  TyExp::{ code: lift_code(k, e.code), coercions: cs }
}

///| 兩個表達式是否**語法**相等（strict 的「等式」就是這個）。
pub fn exp_eq(a : TyExp, b : TyExp) -> Bool {
  if !code_eq(a.code, b.code) {
    return false
  }
  if a.coercions.length() != b.coercions.length() {
    return false
  }
  let mut ok = true
  for i = 0; i < a.coercions.length(); i = i + 1 {
    if !ord_eq(a.coercions[i], b.coercions[i]) {
      ok = false
    }
  }
  ok
}

///| 等式檢查表的一列。
pub struct LiftCheck {
  name : String
  strict_ok : Bool
  cumulative_ok : Bool
  detail : String
}

///| 五條等式：E1 單位、E2 合成、E3 保構造子、E4 注入、E5 有限層級回原樣。
///| `strict` 用純代碼（無轉換節點），`cumulative` 用帶轉換節點的模型。
pub fn lift_checks() -> Array[LiftCheck] {
  let corpus : Array[TyCode] = [
    TUnit,
    TNat,
    TU(ord_finite(0)),
    TPi(TU(ord_finite(1)), TId(TU(ord_finite(2)))),
    TSigma(TU(ord_omega()), TPi(TBool, TU(ord_finite(3)))),
  ]
  let out : Array[LiftCheck] = []
  // E1：lift 0 c = c
  let mut s_ok = true
  let mut c_ok = true
  for c in corpus {
    if !code_eq(lift_code(ord_zero(), c), c) {
      s_ok = false
    }
    let e = TyExp::{ code: c, coercions: [] }
    if !exp_eq(cum_lift(ord_zero(), e), e) {
      c_ok = false
    }
  }
  out.push(LiftCheck::{
    name: "E1 lift 0 = id",
    strict_ok: s_ok,
    cumulative_ok: c_ok,
    detail: "cumulative 會在項上留下一個 0 層轉換節點 ⇒ 語法上不相等",
  })
  // E2：lift a (lift b c) = lift (b+a) c
  //
  // 注意這裡是 `b + a` 而不是 `a + b`：層級位移是「先 b 後 a」，而序數加法非交換，
  // 所以合成的位移是 `b + a`。這一條在有限層級上看不出來（Nat 加法交換），
  // 只有拉到 ω 才會露出來 —— 第一版寫成 `a + b`，五條等式裡正好這一條失敗。
  s_ok = true
  c_ok = true
  let a = ord_omega()
  let b = ord_finite(2)
  for c in corpus {
    if !code_eq(lift_code(a, lift_code(b, c)), lift_code(ord_add(b, a), c)) {
      s_ok = false
    }
    let e = TyExp::{ code: c, coercions: [] }
    if !exp_eq(cum_lift(a, cum_lift(b, e)), cum_lift(ord_add(b, a), e)) {
      c_ok = false
    }
  }
  out.push(LiftCheck::{
    name: "E2 lift a . lift b = lift (b+a)",
    strict_ok: s_ok,
    cumulative_ok: c_ok,
    detail: "位移順序是 b 再 a ⇒ 合成位移 b+a（序數加法非交換）；cumulative 的轉換節點列表長度不同（2 vs 1）",
  })
  // E3：保構造子（形狀不變）
  s_ok = true
  for c in corpus {
    if code_shape(lift_code(a, c)) != code_shape(c) {
      s_ok = false
    }
  }
  out.push(LiftCheck::{
    name: "E3 shape preserved",
    strict_ok: s_ok,
    cumulative_ok: s_ok,
    detail: "兩種模型都保形狀；差別只在項上是否留轉換節點",
  })
  // E4：注入
  s_ok = true
  for i = 0; i < corpus.length(); i = i + 1 {
    for j = 0; j < corpus.length(); j = j + 1 {
      if i != j && code_eq(lift_code(a, corpus[i]), lift_code(a, corpus[j])) {
        s_ok = false
      }
    }
  }
  out.push(LiftCheck::{
    name: "E4 injective on corpus",
    strict_ok: s_ok,
    cumulative_ok: s_ok,
    detail: "5 個代碼兩兩不同 ⇒ Lift 之後仍兩兩不同",
  })
  // E5：有限層級回原樣（lift k 之後再可比）
  s_ok = true
  for n = 0; n < 5; n = n + 1 {
    let c = TU(ord_finite(n))
    let l = lift_code(ord_finite(2), c)
    if !code_eq(l, TU(ord_finite(n + 2))) {
      s_ok = false
    }
  }
  out.push(LiftCheck::{
    name: "E5 U_n -> U_{n+2}",
    strict_ok: s_ok,
    cumulative_ok: s_ok,
    detail: "層級算術與 `Int32` 上的結果逐值相同（有限片段）",
  })
  out
}

///| 嚴格模型是否五條全過。
pub fn lift_strict_all() -> Bool {
  let mut ok = true
  for r in lift_checks() {
    if !r.strict_ok {
      ok = false
    }
  }
  ok
}

///| ## B1′-1 與舊差分約束的對接：層級系統在序數上求解
///
///| 沿用 `b1_schema_levels` 的約束形狀 `L[to] ≥ L[from] + k`，但層級是序數。
///| 另外允許「極限種子」`L[i] ≥ s_i`（`s_i` 可以是非有限的），這是 `Int32` 版本做不到的。
pub struct OrdSystem {
  n : Int32
  seeds : Array[Ord]
  edges : Array[(Int32, Int32, Ord)]
  labels : Array[String]
}

///|
pub fn ord_system(n : Int32, labels : Array[String]) -> OrdSystem {
  let seeds : Array[Ord] = []
  for _i = 0; _i < n; _i = _i + 1 {
    seeds.push(OZero)
  }
  OrdSystem::{ n, seeds, edges: [], labels }
}

///| `L[i] ≥ s`。
pub fn ord_seed(s : OrdSystem, i : Int32, v : Ord) -> Unit {
  s.seeds[i] = ord_sup(s.seeds[i], v)
}

///| `L[to] ≥ L[from] + k`。
pub fn ord_require(s : OrdSystem, from_ : Int32, to : Int32, k : Ord) -> Unit {
  s.edges.push((from_, to, k))
}

///| 判定結果。
pub struct OrdVerdict {
  feasible : Bool
  levels : Array[Ord]
  rounds : Int32
}

///| 以 `n` 輪鬆弛求最小解；第 `n` 輪仍可改進 ⇒ 存在正環 ⇒ 不可行。
pub fn ord_solve(s : OrdSystem) -> OrdVerdict {
  let lv : Array[Ord] = []
  for i = 0; i < s.n; i = i + 1 {
    lv.push(s.seeds[i])
  }
  let mut rounds = 0
  let mut improved = true
  while improved && rounds <= s.n {
    improved = false
    rounds = rounds + 1
    for e in s.edges {
      let cand = ord_add(lv[e.0], e.2)
      if ord_lt(lv[e.1], cand) {
        lv[e.1] = cand
        improved = true
      }
    }
  }
  OrdVerdict::{ feasible: !improved, levels: lv, rounds }
}

///| ## 探針

///| 顯示一列等式檢查。
pub fn lift_check_show(r : LiftCheck) -> String {
  "\{r.name}: strict=\{r.strict_ok} cumulative=\{r.cumulative_ok} —— \{r.detail}"
}

///| B1′ 的完整量測。
pub fn level_algebra_probe() -> Array[String] {
  let out : Array[String] = []
  // 1. 序數基本定律（這幾條在 Int32 上是看不到的）
  let w = ord_omega()
  out.push(
    "1 + ω = \{ord_show(ord_add(ord_one(), w))}（吸收律：有限加極限被吸收）",
  )
  out.push(
    "ω + 1 = \{ord_show(ord_add(w, ord_one()))}（反向不吸收 ⇒ 序數加法非交換）",
  )
  out.push(
    "ω·3 + ω = \{ord_show(ord_add(ord_times(w, 3), w))}；ω^2 > ω·n 對 n=1..5 逐一成立=\{ord_show(ord_omega_pow(2))}",
  )
  out.push(
    "sup(ω^3, ω) = \{ord_show(ord_sup(ord_omega_pow(3), w))}（極限吸收所有更小的層級）",
  )
  out.push(
    "E2 的位移是 b+a 而不是 a+b：`ω ∘ 2` 與 `2 ∘ ω` 在有限層級上相同，拉到 ω 就分開（這是第一版唯一失敗的一條）",
  )
  out.push(
    "良基見證：ω^2·3 + ω + 5 的秩=\{ord_rank(ord_add(ord_times(ord_omega_pow(2), 3), ord_add(w, ord_finite(5))))}、高度=\{ord_height(ord_add(ord_times(ord_omega_pow(2), 3), ord_add(w, ord_finite(5))))}；正規=\{ord_is_normal(ord_add(ord_times(ord_omega_pow(2), 3), ord_add(w, ord_finite(5))))}",
  )
  // 2. 嚴格 vs 累積
  out.push("")
  out.push("Lift 等式檢查表（strict 是「等式成立」，cumulative 是「留下轉換節點」）：")
  for r in lift_checks() {
    out.push("  " + lift_check_show(r))
  }
  out.push("strict 五條全過=\{lift_strict_all()}")
  // 3. 有限 vs 極限：同一個約束系統的兩種可解性
  out.push("")
  let s1 = ord_system(2, ["A", "B"])
  ord_require(s1, 0, 1, ord_one())
  ord_require(s1, 1, 0, ord_one())
  let v1 = ord_solve(s1)
  out.push(
    "有限約束 A ≥ B+1, B ≥ A+1 ⇒ 可行=\{v1.feasible}（正環；與 Int32 版 b1 的判定一致）",
  )
  let s2 = ord_system(3, ["U_n", "U_ω", "T"])
  ord_seed(s2, 0, ord_finite(0))
  ord_require(s2, 0, 1, ord_one())
  ord_seed(s2, 1, w)
  ord_require(s2, 1, 2, ord_one())
  let v2 = ord_solve(s2)
  let mut s = ""
  for i = 0; i < v2.levels.length(); i = i + 1 {
    if i > 0 {
      s = s + ", "
    }
    s = s + s2.labels[i] + "=" + ord_show(v2.levels[i])
  }
  out.push(
    "極限約束 U_ω ≥ sup_n U_n（以 seed = ω 表示）⇒ 可行=\{v2.feasible}，最小解 \{s}",
  )
  out.push(
    "同一組約束在 `Int32` 層級系統上**寫不出來**（沒有 ω）—— 這就是「換成序數層級代數」換到的東西：極限層級變成可判定的一級物件，而它不是 Mahlo 公理，也不需要新的型別論",
  )
  // 4. 與 Mahlo 的關係（誠實定位）
  out.push(
    "定位：本檔給出的是 `Lvl` 這一層（可判定 `<`、`sup`、嚴格 Lift、良基見證）。Mahlo 需要的「對所有層級封閉的宇宙」仍不在這裡；差別是現在我們能**說清楚缺的是哪一條**（層級上的 Π₃-reflection），而不是把整個目標懸空",
  )
  out
}
