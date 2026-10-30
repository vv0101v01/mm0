///|
/// # CSP — 約束滿足 = 極限（範疇式求解器）
///
/// 把 CSP 寫成一個圖（diagram）之極限：
/// `lim [ Π_v D_v →(proj) D_i×D_j ←(incl) R_k ]`；
/// 因 `incl` 為單態射，極限化簡為 `{ a ∈ Π_v D_v : proj_k(a) ∈ R_k ∀k }`。
///
/// 這給出與單子式回溯（`monad.mbt` 之 `search_nd`）**同一解集**的第二條求解路徑，
/// 兩者互為驗證（`theorem.mbt` 之 `csp-limit-vs-monad` 證書、4/5-皇后與隨機 CSP 測試）。

///|
/// 約束滿足 = 極限（單態射可消去之化簡）。
/// `domains[v]` = 變數 v 之定義域大小；`cons` = (i, j, 允許對列表)。
/// 解集 = lim [ Π_v D_v →(proj) D_i×D_j ←(incl) R_k ]，
/// 因 incl 為單態射，極限可化簡為 { a ∈ Π D : proj_k(a) ∈ R_k ∀k }。
pub fn csp_limit(
  domains : Array[Int32],
  cons : Array[(Int32, Int32, Array[(Int32, Int32)])],
  cap : Int32,
) -> Array[Array[Int32]] {
  let nv = domains.length()
  let mut vol = 1
  for d in domains {
    guard vol <= cap / d else { abort("csp_limit: domain product too large") }
    vol = vol * d
  }
  // 允許對之查表
  let tables : Array[Array[Array[Bool]]] = []
  for c in cons {
    let (i, j, allowed) = c
    let tbl = Array::make(domains[i], Array::make(domains[j], false))
    for a in 0..<domains[i] {
      tbl[a] = Array::make(domains[j], false)
    }
    for p in allowed {
      let (x, y) = p
      tbl[x][y] = true
    }
    tables.push(tbl)
  }
  let out : Array[Array[Int32]] = []
  let cur = Array::make(nv, 0)
  fn rec(v : Int32) -> Unit {
    if v == nv {
      out.push(cur.copy())
      return
    }
    for x in 0..<domains[v] {
      cur[v] = x
      let mut ok = true
      for t, c in cons {
        let (i, j, _) = c
        // 只檢查兩端皆已賦值者
        if i <= v && j <= v {
          if !tables[t][cur[i]][cur[j]] {
            ok = false
            break
          }
        }
      }
      if ok {
        rec(v + 1)
      }
    }
  }
  rec(0)
  guard out.length() <= cap else { abort("csp_limit: too many solutions") }
  out
}

///|
/// n 皇后之允許對表（變數 = 列，定義域 = 行）。
pub fn queen_constraints(
  n : Int32,
) -> Array[(Int32, Int32, Array[(Int32, Int32)])] {
  let cons : Array[(Int32, Int32, Array[(Int32, Int32)])] = []
  for i in 0..<n {
    for j in (i + 1)..<n {
      let allowed : Array[(Int32, Int32)] = []
      for a in 0..<n {
        for b in 0..<n {
          let da = a - b
          let dd = i - j
          let ad = if da < 0 { 0 - da } else { da }
          let ad2 = if dd < 0 { 0 - dd } else { dd }
          if a != b && ad != ad2 {
            allowed.push((a, b))
          }
        }
      }
      cons.push((i, j, allowed))
    }
  }
  cons
}
