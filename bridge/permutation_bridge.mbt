///|
/// 置換矩陣：列 i 的 1 位於欄 `p(i)`。
/// 這是 symlib 的有限置換在 cubical 複矩陣世界中的表示。
pub fn permutation_matrix(p : @sym.Perm) -> @cub.CMat {
  let rows : Array[Array[@cub.Complex]] = []
  for i in 0..<p.size() {
    let row : Array[@cub.Complex] = []
    for j in 0..<p.size() {
      row.push(if p.apply(i) == j { @cub.cx_real(1.0) } else { @cub.cx_zero() })
    }
    rows.push(row)
  }
  @cub.mat_from_rows(rows)
}

///|
/// 一組置換矩陣的平均。當輸入是完整有限置換群時，結果是到
/// 群不變子空間的正交投影；不完整枚舉不作此宣稱。
pub fn average_permutation_matrices(perms : Array[@sym.Perm]) -> Result[
  @cub.CMat, String,
] {
  if perms.length() == 0 {
    return Err("average_permutation_matrices: 空輸入沒有平均")
  }
  let n = perms[0].size()
  let rows : Array[Array[@cub.Complex]] = []
  for i in 0..<n {
    let row : Array[@cub.Complex] = []
    for j in 0..<n {
      let mut count = 0
      for p in perms {
        // 長度已在上面檢查過（所有元素同尺寸）；這裡不再中止
        if p.apply(i) == j {
          count = count + 1
        }
      }
      row.push(@cub.cx_real(count.to_double() / perms.length().to_double()))
    }
    rows.push(row)
  }
  Ok(@cub.mat_from_rows(rows))
}

///|
/// 右巢狀 Bool 積型別 `Bool × (Bool × (... × Bool))`；n=1 時就是 Bool。
pub fn bool_tuple_type(n : Int32) -> @cub.Ty {
  // 全函數：`n ≤ 1` 一律是 `Bool`（空積在 cubical 宇宙裡沒有代表元，取單位型別）。
  if n <= 1 {
    return @cub.ty_bool()
  }
  @cub.ty_prod(@cub.ty_bool(), bool_tuple_type(n - 1))
}

///|
fn adjacent_swap_wiring(pos : Int32, n : Int32) -> @cub.Wiring? {
  if !(n >= 2 && pos >= 0 && pos + 1 < n) {
    return None
  }
  if pos > 0 {
    let inner = match adjacent_swap_wiring(pos - 1, n - 1) {
      None => return None
      Some(w) => w
    }
    return Some(@cub.wiring_prod(@cub.wiring_id(@cub.ty_bool()), inner))
  }
  if n == 2 {
    return Some(@cub.wiring_swap(@cub.ty_bool(), @cub.ty_bool()))
  }
  let rest = bool_tuple_type(n - 2)
  let assoc = @cub.wiring_assoc(@cub.ty_bool(), @cub.ty_bool(), rest)
  let swapped_pair = @cub.wiring_prod(
    @cub.wiring_swap(@cub.ty_bool(), @cub.ty_bool()),
    @cub.wiring_id(rest),
  )
  Some(
    @cub.wiring_comp(
      @cub.wiring_comp(@cub.wiring_inv(assoc), swapped_pair),
      assoc,
    ),
  )
}

///|
fn not_at_wiring(pos : Int32, n : Int32) -> @cub.Wiring? {
  if !(n >= 1 && pos >= 0 && pos < n) {
    return None
  }
  if n == 1 {
    return Some(@cub.wiring_not())
  }
  if pos == 0 {
    return Some(
      @cub.wiring_prod(@cub.wiring_not(), @cub.wiring_id(bool_tuple_type(n - 1))),
    )
  }
  let inner = match not_at_wiring(pos - 1, n - 1) {
    None => return None
    Some(w) => w
  }
  Some(@cub.wiring_prod(@cub.wiring_id(@cub.ty_bool()), inner))
}

///|
/// symlib `Perm` → cubical 有限宇宙的 wiring。
/// 約定與 `wiring_apply` 一致：輸入第 i 個 Bool 葉會出現在輸出
/// 位置 `p(i)`；因此輸出位置 j 的來源是 `p⁻¹(j)`。
/// 實作只用既有 wiring 生成元（id/prod/swap/assoc/inv/comp）
/// 做相鄰交換網絡，不繞過 cubical 的公開構造邊界。
pub fn perm_wiring(p : @sym.Perm) -> Result[@cub.Wiring, String] {
  let n = p.size()
  if n < 1 {
    return Err("perm_wiring: 空置換沒有 Bool 巢狀積的代表元（size = 0）")
  }
  let target = Array::make(n, 0)
  let inv = p.inverse()
  for j in 0..<n {
    target[j] = inv.apply(j)
  }
  let current = Array::make(n, 0)
  for i in 0..<n {
    current[i] = i
  }
  let mut w = @cub.wiring_id(bool_tuple_type(n))
  for i in 0..<n {
    let mut k = i
    while k < n && current[k] != target[i] {
      k = k + 1
    }
    if k >= n {
      return Err("perm_wiring: 目標影像不是置換（缺少 \{target[i]}）")
    }
    while k > i {
      let step = match adjacent_swap_wiring(k - 1, n) {
        None => return Err("perm_wiring: 相鄰交換位置越界（k−1 = \{k - 1}, n = \{n}）")
        Some(s) => s
      }
      w = @cub.wiring_comp(w, step)
      let tmp = current[k - 1]
      current[k - 1] = current[k]
      current[k] = tmp
      k = k - 1
    }
  }
  Ok(w)
}

///|
/// 帶號置換 → wiring。`signs[j]=true` 表示輸出位置 j 再套 Bool 否定。
pub fn signed_perm_wiring(
  p : @sym.Perm,
  signs : Array[Bool],
) -> Result[@cub.Wiring, String] {
  if signs.length() != p.size() {
    return Err(
      "signed_perm_wiring: 號列長度 \{signs.length()} ≠ 置換大小 \{p.size()}",
    )
  }
  let mut w = match perm_wiring(p) {
    Err(e) => return Err(e)
    Ok(v) => v
  }
  for j = 0; j < p.size(); j = j + 1 {
    if signs[j] {
      let nn = match not_at_wiring(j, p.size()) {
        None => return Err("signed_perm_wiring: 否定位置越界（j = \{j}）")
        Some(x) => x
      }
      w = @cub.wiring_comp(w, nn)
    }
  }
  Ok(w)
}

///|
/// wiring → symlib `Perm`。只接受正規右巢狀全 Bool 型別上的
/// 無號 wiring；帶否定者回傳 None（用 `wiring_output_signs` 讀號）。
pub fn perm_of_wiring(w : @cub.Wiring) -> @sym.Perm? {
  let n = @cub.leaf_count(w.src)
  guard n >= 1 &&
    w.src == bool_tuple_type(n) &&
    w.dst == bool_tuple_type(n) &&
    @cub.wiring_wf(w) else {
    return None
  }
  let img = Array::make(n, 0)
  for j in 0..<n {
    let m = w.mapping[j]
    if m.neg || m.src_index < 0 {
      return None
    }
    img[m.src_index] = j
  }
  Some(@sym.Perm::from_img(img))
}

///|
/// 讀取 wiring 在各輸出位置的否定旗標。
pub fn wiring_output_signs(w : @cub.Wiring) -> Array[Bool] {
  let out : Array[Bool] = []
  for m in w.mapping {
    out.push(m.neg)
  }
  out
}

///|
/// symlib 置換提升為 cubical 有限宇宙的一等等價。
pub fn perm_equiv(p : @sym.Perm) -> Result[@cub.Equiv, String] {
  match perm_wiring(p) {
    Err(e) => Err(e)
    Ok(w) => Ok(@cub.equiv_of_wiring(w))
  }
}

///|
/// 穿越檢查：S4 的全部 24 個置換均可編成 well-formed wiring，
/// 在全部 16 個四 Bool 值上逐葉實現同一置換，再讀回同一置換；
/// 帶號版的號列與底置換各自由對應讀取器還原。
pub fn check_perm_wiring_bridge() -> Bool {
  let all = @sym.PermGroup::symmetric(4).elements(24)
  let values = @cub.elems_of(bool_tuple_type(4))
  if all.length() != 24 {
    return false
  }
  for p in all {
    let pm = permutation_matrix(p)
    let p_inv_m = permutation_matrix(p.inverse())
    if !@cub.mat_approx_eq(@cub.mat_adjoint(pm), p_inv_m) ||
      !@cub.mat_approx_eq(@cub.mat_mul(pm, p_inv_m), @cub.mat_identity(4)) {
      return false
    }
    let w = match perm_wiring(p) {
      Err(_) => return false
      Ok(v) => v
    }
    if !@cub.wiring_wf(w) {
      return false
    }
    match perm_of_wiring(w) {
      Some(q) => if !q.equal(p) { return false }
      None => return false
    }
    let eq = match perm_equiv(p) {
      Err(_) => return false
      Ok(v) => v
    }
    if !@cub.wiring_eq(eq.wiring, w) {
      return false
    }
    for value in values {
      let input = @cub.flatten_pval(value)
      let output = @cub.flatten_pval(@cub.wiring_apply(w, value))
      for i in 0..<4 {
        if output[p.apply(i)] != input[i] {
          return false
        }
      }
    }
  }
  let p = @sym.Perm::from_img([2, 0, 3, 1])
  let signs = [true, false, true, false]
  let sw = match signed_perm_wiring(p, signs) {
    Err(_) => return false
    Ok(v) => v
  }
  let got = wiring_output_signs(sw)
  for i in 0..<4 {
    if got[i] != signs[i] {
      return false
    }
  }
  true
}
