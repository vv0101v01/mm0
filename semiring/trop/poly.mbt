// ===========================================================================
// 熱帶幾何 I：單變數熱帶多項式、牛頓多邊形、熱帶根
//
// 熱帶多項式（min 版）：
//   f(x) = min_i ( c_i + i·x )
// 它是 ℝ 上的一條凹分段線性函數（下包絡），分段斜率正好是各單項式的指數。
//
// 幾何側的定義：
//   把 (i, c_i) 畫在平面上，取**下凸包**。下凸包的每條邊對應一個熱帶根，
//   根的值 = −(邊的斜率)，重數 = 邊的水平投影長度。
//
// 這個檔案的三個可驗證結論（測試與報告都會實際檢查）：
//   1. Σ 重數 = deg f（沒有根憑空消失）。
//   2. 在根 r 上，**恰好**是該下凸包邊的兩個端點同時達到最小值（重根以外）；
//      在非根上只有一個單項式達到最小值。
//   3. 根的乘法定理：roots(f ⊗ g) = roots(f) ⊔ roots(g)（含重數），
//      其中 ⊗ 是 min-plus 卷積——即熱帶多項式半環的乘法。
// ===========================================================================

///|
/// 最大公因數（Int64，避免 Int32 溢位）。
fn gcd64(a : Int64, b : Int64) -> Int64 {
  let mut x = if a < 0L { -a } else { a }
  let mut y = if b < 0L { -b } else { b }
  while y != 0L {
    let t = x % y
    x = y
    y = t
  }
  x
}

///|
/// 有理數（熱帶根的精確表示）：`n / d`，`d > 0`，已約分。
///
/// 熱帶根一般不是整數（例：`min(0, 2x + 1)` 的根是 −1/2），
/// 用有理數表示才能做**精確**的比較與乘法定理驗證。
pub(all) struct Rat {
  n : Int64
  d : Int64
} derive(Eq)

///|
pub extend Rat with Eq::{equal, not_equal}

///|
pub fn Rat::new(n : Int64, d : Int64) -> Rat {
  if d == 0L {
    return { n: 0L, d: 1L, }
  }
  let mut nn = n
  let mut dd = d
  if dd < 0L {
    nn = -nn
    dd = -dd
  }
  let g = gcd64(nn, dd)
  if g == 0L {
    { n: 0L, d: 1L, }
  } else {
    { n: nn / g, d: dd / g, }
  }
}

///|
pub fn Rat::of_int(v : Int32) -> Rat {
  { n: v.to_int64(), d: 1L, }
}

///|
pub fn Rat::to_double(self : Rat) -> Double {
  self.n.to_double() / self.d.to_double()
}

///|
pub impl Show for Rat with fn output(self, logger) {
  if self.d == 1L {
    logger.write_string(self.n.to_string())
  } else {
    logger.write_string("\{self.n}/\{self.d}")
  }
}

///|
pub extend Rat with Show::{output, to_string}

///|
/// 飽和加法（+∞ 吸收，對齊 `Trop` 的語義）。
pub fn sat_add_i32(a : Int32, b : Int32) -> Int32 {
  if a >= @alg.trop_inf || b >= @alg.trop_inf {
    @alg.trop_inf
  } else {
    let s = a.to_int64() + b.to_int64()
    if s >= @alg.trop_inf.to_int64() {
      @alg.trop_inf
    } else {
      s.to_int()
    }
  }
}

///|
/// 飽和乘法（指數 × 座標）。
pub fn sat_mul_i32(a : Int32, b : Int32) -> Int32 {
  let p = a.to_int64() * b.to_int64()
  let lim = @alg.trop_inf.to_int64()
  if p >= lim {
    @alg.trop_inf
  } else if p <= -lim {
    -@alg.trop_inf
  } else {
    p.to_int()
  }
}

///|
/// 單變數熱帶多項式：`coeffs[i]` 是 `x^i` 的係數（`+∞` 表示缺項）。
pub(all) struct UniPoly {
  coeffs : Array[Int32]
}

///|
pub fn UniPoly::new(coeffs : Array[Int32]) -> UniPoly {
  { coeffs, }
}

///|
/// 次數 = 最高非 +∞ 指數；空多項式回 −1。
pub fn UniPoly::degree(self : UniPoly) -> Int32 {
  let mut d = -1
  for i in 0..<self.coeffs.length() {
    if self.coeffs[i] < @alg.trop_inf {
      d = i
    }
  }
  d
}

///|
/// 求值：`min_i (c_i + i·x)`。
pub fn UniPoly::eval(self : UniPoly, x : Int32) -> Int32 {
  let mut best = @alg.trop_inf
  for i in 0..<self.coeffs.length() {
    let c = self.coeffs[i]
    if c < @alg.trop_inf {
      let v = sat_add_i32(c, sat_mul_i32(i, x))
      if v < best {
        best = v
      }
    }
  }
  best
}

///|
/// 在有理點 `x` 上，哪些單項式達到最小值（回傳指數）。
///
/// 以 `x = n/d` 代入並同乘 `d > 0`：比較 `c_i·d + i·n`，全程整數，無浮點誤差。
pub fn UniPoly::argmin_at(self : UniPoly, x : Rat) -> Array[Int32] {
  let out : Array[Int32] = []
  let mut best = 0L
  let mut first = true
  for i in 0..<self.coeffs.length() {
    let c = self.coeffs[i]
    if c < @alg.trop_inf {
      let v = c.to_int64() * x.d + i.to_int64() * x.n
      if first || v < best {
        best = v
        first = false
        out.clear()
        out.push(i)
      } else if v == best {
        out.push(i)
      }
    }
  }
  out
}

///|
/// 下凸包（牛頓多邊形的下側）：回傳 `(指數, 係數)` 的頂點序列，x 嚴格遞增。
///
/// Andrew 單調鏈的下半部：保留左轉（cross > 0），遇到右轉或共線就彈出。
pub fn UniPoly::lower_hull(self : UniPoly) -> Array[(Int32, Int32)] {
  let pts : Array[(Int32, Int32)] = []
  for i in 0..<self.coeffs.length() {
    if self.coeffs[i] < @alg.trop_inf {
      pts.push((i, self.coeffs[i]))
    }
  }
  let hull : Array[(Int32, Int32)] = []
  for p in pts {
    while hull.length() >= 2 {
      let a = hull[hull.length() - 2]
      let b = hull[hull.length() - 1]
      let cross = (b.0 - a.0).to_int64() * (p.1 - a.1).to_int64() -
        (b.1 - a.1).to_int64() * (p.0 - a.0).to_int64()
      if cross <= 0L {
        let _ = hull.pop()
      } else {
        break
      }
    }
    hull.push(p)
  }
  hull
}

///|
/// 熱帶根（含重數）：下凸包每條邊 `(i,c_i)→(j,c_j)` 給出
///   根 = −(c_j − c_i)/(j − i) = (c_i − c_j)/(j − i)，重數 = j − i。
pub fn UniPoly::roots_with_mult(self : UniPoly) -> Array[(Rat, Int32)] {
  let h = self.lower_hull()
  let out : Array[(Rat, Int32)] = []
  for k in 1..<h.length() {
    let (i, ci) = h[k - 1]
    let (j, cj) = h[k]
    out.push((Rat::new((ci - cj).to_int64(), (j - i).to_int64()), j - i))
  }
  out
}

///|
/// 熱帶根（按重數展開，遞增排序）。
pub fn UniPoly::roots(self : UniPoly) -> Array[Rat] {
  let pairs = self.roots_with_mult()
  let out : Array[Rat] = []
  for p in pairs {
    for _ in 0..<p.1 {
      out.push(p.0)
    }
  }
  // 插入排序：根數量很小，且下凸包的根本來就遞增
  let mut i = 1
  while i < out.length() {
    let key = out[i]
    let mut j = i
    while j > 0 && out[j - 1].to_double() > key.to_double() {
      out[j] = out[j - 1]
      j = j - 1
    }
    out[j] = key
    i = i + 1
  }
  out
}

///|
/// 重數總和（應該等於次數）。
pub fn UniPoly::multiplicity_sum(self : UniPoly) -> Int32 {
  let mut s = 0
  for p in self.roots_with_mult() {
    s = s + p.1
  }
  s
}

///|
/// 熱帶多項式乘法 = min-plus 卷積：
///   (f ⊗ g)_k = min_{i+j=k} (f_i + g_j)
///
/// 這就是「min-plus 卷積」，也是多項式環上的 ⊗；有了它才能陳述根的乘法定理。
pub fn trop_poly_mul(f : UniPoly, g : UniPoly) -> UniPoly {
  // 熱帶乘法中 x^i ⊗ x^j = x^(i+j)，所以結果次數是兩個次數之和
  let n = f.coeffs.length() + g.coeffs.length() - 1
  let cs : Array[Int32] = Array::make(n, @alg.trop_inf)
  for i in 0..<f.coeffs.length() {
    if f.coeffs[i] >= @alg.trop_inf {
      continue
    }
    for j in 0..<g.coeffs.length() {
      if g.coeffs[j] >= @alg.trop_inf {
        continue
      }
      let v = sat_add_i32(f.coeffs[i], g.coeffs[j])
      let k = i + j
      if k < n && v < cs[k] {
        cs[k] = v
      }
    }
  }
  { coeffs: cs, }
}

///|
/// 兩個根序列是否為同一個重數多重集（已排序的有理數序列逐項比較）。
pub fn roots_equal(a : Array[Rat], b : Array[Rat]) -> Bool {
  if a.length() != b.length() {
    return false
  }
  let sa = sort_rats(a)
  let sb = sort_rats(b)
  for i in 0..<sa.length() {
    if sa[i] != sb[i] {
      return false
    }
  }
  true
}

///|
/// 有理數序列排序（插入排序，逐項精確比較 `n1·d2` vs `n2·d1`）。
pub fn sort_rats(a : Array[Rat]) -> Array[Rat] {
  let out : Array[Rat] = []
  for v in a {
    out.push(v)
  }
  let mut i = 1
  while i < out.length() {
    let key = out[i]
    let mut j = i
    while j > 0 && rat_gt(out[j - 1], key) {
      out[j] = out[j - 1]
      j = j - 1
    }
    out[j] = key
    i = i + 1
  }
  out
}

///|
pub fn rat_gt(a : Rat, b : Rat) -> Bool {
  a.n * b.d > b.n * a.d
}
