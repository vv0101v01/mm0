///| ## 精確有理 LP（殘餘 3 的地基）
///
///| B2 的殘餘是「一般稠密圖上秩界鬆」。要收窄它需要的不是更強的定理，
///| 而是**更好的上界**：線性規劃鬆弛。但浮點 LP 給不出「已證明」的上界
///| （對偶間隙 + 捨入誤差會讓界差一點點），所以要**精確有理數**的單純形法。
///
///| 這裡的形式：`max c·x  s.t.  Ax ≤ b, x ≥ 0, b ≥ 0`。
///| 因為 `b ≥ 0`，原點可行，不需要相位一。用 Bland 規則保證不循環。

///| 單純形法（Bland 規則）。回傳 (最優值, 最優解, 是否找到)。
pub fn lp_max(
  n : Int32,
  a : Array[Array[@algebra.Rat]],
  b : Array[@algebra.Rat],
  c : Array[@algebra.Rat],
) -> (@algebra.Rat, Array[@algebra.Rat], Bool) {
  let (v, x, ok, _it) = lp_max_iter(n, a, b, c)
  (v, x, ok)
}

///| 同上，另外回報用了幾次樞軸（迭代數）。收斂判據是 `ok`，**呼叫者必須檢查**：
///| 不收斂時的目標值只是某個可行解的值，不是上界。
pub fn lp_max_iter(
  n : Int32,
  a : Array[Array[@algebra.Rat]],
  b : Array[@algebra.Rat],
  c : Array[@algebra.Rat],
) -> (@algebra.Rat, Array[@algebra.Rat], Bool, Int32) {
  let m = b.length()
  let width = n + m + 1
  // 表格：(m+1) × width
  let t : Array[Array[@algebra.Rat]] = []
  for i = 0; i <= m; i = i + 1 {
    let row : Array[@algebra.Rat] = []
    for j = 0; j < width; j = j + 1 {
      row.push(@algebra.rat_zero())
    }
    t.push(row)
  }
  for i = 0; i < m; i = i + 1 {
    for j = 0; j < n; j = j + 1 {
      t[i][j] = a[i][j]
    }
    t[i][n + i] = @algebra.rat_one()
    t[i][width - 1] = b[i]
  }
  for j = 0; j < n; j = j + 1 {
    t[m][j] = @algebra.rat_neg(c[j])
  }
  let basis : Array[Int32] = []
  for i = 0; i < m; i = i + 1 {
    basis.push(n + i)
  }
  let mut iter : Int32 = 0
  let limit = 200000
  while iter < limit {
    iter = iter + 1
    // 進入列：最小的（Bland）
    let mut enter : Int32 = -1
    for j = 0; j < n + m; j = j + 1 {
      if @algebra.rat_sign(t[m][j]) < 0 && enter < 0 {
        enter = j
      }
    }
    if enter < 0 {
      break
    }
    // 離開列：最小比值；平手取 basis 最小
    let mut leave : Int32 = -1
    let mut best : @algebra.Rat = @algebra.rat_zero()
    for i = 0; i < m; i = i + 1 {
      if @algebra.rat_sign(t[i][enter]) > 0 {
        let ratio = @algebra.rat_div(t[i][width - 1], t[i][enter])
        if leave < 0 || @algebra.rat_sign(@algebra.rat_sub(ratio, best)) < 0 ||
          (@algebra.rat_is_zero(@algebra.rat_sub(ratio, best)) && basis[i] < basis[leave]) {
          leave = i
          best = ratio
        }
      }
    }
    if leave < 0 {
      // 無界
      return (@algebra.rat_zero(), [], false, iter)
    }
    // 樞軸
    let piv = t[leave][enter]
    for j = 0; j < width; j = j + 1 {
      t[leave][j] = @algebra.rat_div(t[leave][j], piv)
    }
    for i = 0; i <= m; i = i + 1 {
      if i == leave {
        continue
      }
      let f = t[i][enter]
      if !@algebra.rat_is_zero(f) {
        for j = 0; j < width; j = j + 1 {
          t[i][j] = @algebra.rat_sub(t[i][j], @algebra.rat_mul(f, t[leave][j]))
        }
      }
    }
    basis[leave] = enter
  }
  let x : Array[@algebra.Rat] = []
  for _j = 0; _j < n; _j = _j + 1 {
    x.push(@algebra.rat_zero())
  }
  for i = 0; i < m; i = i + 1 {
    if basis[i] < n {
      x[basis[i]] = t[i][width - 1]
    }
  }
  (t[m][width - 1], x, iter < limit, iter)
}
