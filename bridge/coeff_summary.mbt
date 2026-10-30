///| ## 係數環摘要 —— 給審計與帳本用的**單一真相**
///

///| 這些數字以前手寫在 `cmd/audit` 的 payload 字串裡。手寫的數字會過期，

///| 而且過期的數字沒有任何東西會發現。現在它們由 `coeff/` 現算：

///| 帳本裡的每一筆都必須是「這次真的算出來的」。
///

///| 副產品：`bridge` 對 `coeff` 的依賴從「只有測試用到」變成「生產代碼用到」，

///| 套件依賴不再需要 test-only import（moon 0.1 沒有這個語法）。

///|
/// UCT 交叉驗證：通過數 / 總數。
pub fn coeff_uct_pass() -> (Int32, Int32) {
  let mut ok : Int32 = 0
  let mut total : Int32 = 0
  for m in @coeff.models() {
    for p in [2, 3, 5, 7] {
      total = total + 1
      if @coeff.uct_check(m.1, p).ok {
        ok = ok + 1
      }
    }
  }
  (ok, total)
}

///|
/// Bockstein 在撓率模型上非零、在無撓率模型上為零的檢查。
pub fn coeff_bockstein_ok() -> (Int32, Int32) {
  let mut ok : Int32 = 0
  let mut total : Int32 = 0
  let cases : Array[(String, @coeff.ChainComplex, Int32, Int32, Bool)] = [
    ("RP^2", @coeff.cw_rp2(), 2, 2, true),
    ("M(Z/3,1)", @coeff.moore_space(3), 3, 2, true),
    ("S^2", @coeff.simplex_cc(@coeff.s2()), 2, 2, false),
    ("T^2", @coeff.simplex_cc(@coeff.torus()), 2, 2, false),
  ]
  for c in cases {
    total = total + 1
    let r = @coeff.bockstein_report(c.1, c.2, c.3)
    let nonzero = r.dim_cycles_with_beta > 0
    if nonzero == c.4 {
      ok = ok + 1
    }
  }
  (ok, total)
}

///|
/// 杯積分離度：`(T² 非零對數, 楔和非零對數)`。
pub fn coeff_cup_split() -> (Int32, Int32) {
  let t = @coeff.cup_scan(@coeff.torus(), "T^2")
  let w = @coeff.cup_scan(@coeff.wedge(), "wedge")
  (t.nonzero_cup, w.nonzero_cup)
}
