///| ## B7 —— HOU 與模組邊界：有限載體上的合一化歸為整數消元
///

///| golden SPEC §四 第七條殘餘邊界：三階以上一般高階合一受 Goldfarb 定理限制本質

///| 不可判定；模組連結仍針對靜態非循環 DAG 而非執行期熱載入。
///

///| 合併動作（變化 + 推遠）：

///|  (a) Goldfarb 的不可判定性是關於**無限項代數** `λΠΣ` 的。golden 的核心在

///|      有限宇宙／有限型別片段上工作；在**有限載體**（`Fin n`、`ℤ/p`）上，

///|      合一問題的搜尋空間有限 ⇒ **可判定**，而且仿射片段由秩與 SNF 直接給出

///|      解的個數 `p^{k−rank}`。於是「不可判定」這條邊界被限制在

///|      「無限項代數 + 非仿射約束」這一角，其餘部分變成消元問題。

///|  (b) 模組的「執行期熱載入」由 `super/sledger` 的跨執行雜湊鏈補上：

///|      連結事件成為可重放、可驗證、可撤銷的帳本記錄（見 B3）。

///|
/// 有限載體合一的判定結果。
pub struct FinUnify {
  vars : Int32
  modulus : Int32
  rank : Int32
  solvable : Bool
  count_formula : Int32
  count_bruteforce : Int32
  witness : Array[Int32]
}

///| [E-FinUnify] 在 `(ℤ/p)^k` 上解 `A x = b`：

///|  rank(A) = rank([A|b]) ⇒ 可解且解數 = p^{k−rank}（有限群上的秩–零化度）。

///|
///  暴力枚舉只用作對照（p^k ≤ 10^5）。
pub fn fin_unify(
  a : Array[Array[Int32]],
  b : Array[Int32],
  p : Int32,
) -> FinUnify {
  let fld = @core.mk_field(p)
  let k = if a.length() > 0 { a[0].length() } else { 0 }
  let aug : Array[Array[Int32]] = []
  for i = 0; i < a.length(); i = i + 1 {
    let row : Array[Int32] = []
    for x in a[i] {
      row.push((x % p + p) % p)
    }
    row.push((b[i] % p + p) % p)
    aug.push(row)
  }
  let anorm : Array[Array[Int32]] = []
  for row in a {
    let r : Array[Int32] = []
    for x in row {
      r.push((x % p + p) % p)
    }
    anorm.push(r)
  }
  let ra = @core.gauss_jordan(@core.mat_from_rows(anorm), fld).rank
  let rb = @core.gauss_jordan(@core.mat_from_rows(aug), fld).rank
  let sat = ra == rb
  let mut formula : Int32 = 0
  if sat {
    formula = int_pow_p(p, k - ra)
  }
  // 暴力對照
  let total = int_pow_p(p, k)
  let witness : Array[Int32] = []
  let mut bf : Int32 = 0
  if total <= 200000 {
    let mut code = 0
    while code < total {
      let x : Array[Int32] = []
      let mut t = code
      for _i = 0; _i < k; _i = _i + 1 {
        x.push(t % p)
        t = t / p
      }
      let mut ok = true
      for i = 0; i < a.length(); i = i + 1 {
        let mut acc : Int32 = 0
        for j = 0; j < k; j = j + 1 {
          acc = acc + anorm[i][j] * x[j]
        }
        if acc % p != (b[i] % p + p) % p {
          ok = false
        }
      }
      if ok {
        bf = bf + 1
      }
      code = code + 1
    }
  }
  FinUnify::{
    vars: k,
    modulus: p,
    rank: ra,
    solvable: sat,
    count_formula: formula,
    count_bruteforce: bf,
    witness,
  }
}

///|
fn int_pow_p(p : Int32, k : Int32) -> Int32 {
  let mut v : Int32 = 1
  for _i = 0; _i < k; _i = _i + 1 {
    v = v * p
  }
  v
}

///|
/// B7 的實驗輸出。
pub fn b7_probe() -> Array[String] {
  let out : Array[String] = []
  // 三個「樣式合一」實例，寫成 ℤ/5 上的線性約束
  let instances : Array[(String, Array[Array[Int32]], Array[Int32], Int32)] = [
    (
      "f(x)+f(y)=3, f(x)−f(z)=1 (3 變元, mod 5)",
      [[1, 1, 0], [1, 0, -1]],
      [3, 1],
      5,
    ),
    ("相容但欠定：f(x)+f(y)=0 (mod 7)", [[1, 1]], [0], 7),
    ("不相容：2f(x)=1 且 2f(x)=3 (mod 5)", [[2], [2]], [1, 3], 5),
  ]
  for inst in instances {
    let name = inst.0
    let a = inst.1
    let b = inst.2
    let p = inst.3
    let r = fin_unify(a, b, p)
    out.push(
      "\{name}: rank=\{r.rank} sat=\{r.solvable} 解數公式=\{r.count_formula} 暴力=\{r.count_bruteforce} 一致=\{r.count_formula == r.count_bruteforce}",
    )
  }
  out.push(
    "Goldfarb 邊界的收窄：不可判定性屬「無限項代數 + 非仿射約束」；有限載體上的仿射片段由秩與 p^{k−rank} 完全決定",
  )
  out
}
