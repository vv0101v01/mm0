///|
/// # Perm — 有限置換
///
/// {0..n-1} 上的置換，`img[i]` 為 i 的像。乘法約定為函數複合：
/// `a.compose(b)(x) = a(b(x))`（先施 b，後施 a）。
/// 群論基礎層：group / action / aut 等模組全部建立在 Perm 之上。

///|
/// 有限置換。
pub(all) struct Perm {
  n : Int32
  img : Array[Int32]
}

///|
/// 恆等置換。
pub fn Perm::identity(n : Int32) -> Perm {
  guard n >= 0 else { abort("Perm::identity: negative size") }
  let img = Array::make(n, 0)
  for i in 0..<n {
    img[i] = i
  }
  { n, img, }
}

///|
/// 由像陣列建構（會驗證雙射性）。
pub fn Perm::from_img(img : Array[Int32]) -> Perm {
  let n = img.length()
  let seen = Array::make(n, false)
  for i in 0..<n {
    let v = img[i]
    guard v >= 0 && v < n else { abort("Perm::from_img: image out of range") }
    guard !seen[v] else { abort("Perm::from_img: not injective") }
    seen[v] = true
  }
  { n, img: img.copy(), }
}

///|
/// 由不交輪分解建構，`cycles` 中每個子陣列為一個輪（長度 ≥ 2）。
pub fn Perm::from_cycles(n : Int32, cycles : Array[Array[Int32]]) -> Perm {
  let p = Perm::identity(n)
  for c in cycles {
    guard c.length() >= 2 else { abort("Perm::from_cycles: cycle too short") }
    for i in 0..<c.length() {
      let a = c[i]
      let b = c[(i + 1) % c.length()]
      guard a >= 0 && a < n && b >= 0 && b < n else {
        abort("Perm::from_cycles: point out of range")
      }
      p.img[a] = b
    }
  }
  Perm::from_img(p.img)
}

///|
/// 階（底集合大小）。
pub fn Perm::size(self : Perm) -> Int32 {
  self.n
}

///|
/// 施於一點。
pub fn Perm::apply(self : Perm, i : Int32) -> Int32 {
  guard i >= 0 && i < self.n else { abort("Perm::apply: point out of range") }
  self.img[i]
}

///|
/// 複合 `self ∘ other`（先 other 後 self）。
pub fn Perm::compose(self : Perm, other : Perm) -> Perm {
  guard self.n == other.n else { abort("Perm::compose: size mismatch") }
  let img = Array::make(self.n, 0)
  for i in 0..<self.n {
    img[i] = self.img[other.img[i]]
  }
  { n: self.n, img, }
}

///|
/// 逆置換。
pub fn Perm::inverse(self : Perm) -> Perm {
  let img = Array::make(self.n, 0)
  for i in 0..<self.n {
    img[self.img[i]] = i
  }
  { n: self.n, img, }
}

///|
/// 冪（二進制冪；負指數先求逆）。
pub fn Perm::pow(self : Perm, k : Int32) -> Perm {
  let mut base = if k < 0 { self.inverse() } else { self }
  let mut e = if k < 0 { -k } else { k }
  let mut acc = Perm::identity(self.n)
  while e > 0 {
    if e % 2 == 1 {
      acc = acc.compose(base)
    }
    base = base.compose(base)
    e = e / 2
  }
  acc
}

///|
/// 是否恆等。
pub fn Perm::is_identity(self : Perm) -> Bool {
  for i in 0..<self.n {
    guard self.img[i] == i else { return false }
  }
  true
}

///|
/// 被移動的點（遞增）。
pub fn Perm::moved_points(self : Perm) -> Array[Int32] {
  let out : Array[Int32] = []
  for i in 0..<self.n {
    if self.img[i] != i {
      out.push(i)
    }
  }
  out
}

///|
/// 不動點個數。
pub fn Perm::fixed_point_count(self : Perm) -> Int32 {
  let mut c = 0
  for i in 0..<self.n {
    if self.img[i] == i {
      c = c + 1
    }
  }
  c
}

///|
/// 完整輪分解（含不動點）。
pub fn Perm::cycles(self : Perm) -> Array[Array[Int32]] {
  let seen = Array::make(self.n, false)
  let out : Array[Array[Int32]] = []
  for i in 0..<self.n {
    if !seen[i] {
      let cyc : Array[Int32] = []
      let mut j = i
      while !seen[j] {
        seen[j] = true
        cyc.push(j)
        j = self.img[j]
      }
      out.push(cyc)
    }
  }
  out
}

///|
/// 非平凡輪（長度 ≥ 2）。
pub fn Perm::nontrivial_cycles(self : Perm) -> Array[Array[Int32]] {
  let out : Array[Array[Int32]] = []
  for c in self.cycles() {
    if c.length() >= 2 {
      out.push(c)
    }
  }
  out
}

///|
/// 階（乘法週期）：各輪長度之最小公倍數。
pub fn Perm::order(self : Perm) -> Int32 {
  fn gcd(a : Int32, b : Int32) -> Int32 {
    let mut x = a
    let mut y = b
    while y != 0 {
      let t = x % y
      x = y
      y = t
    }
    x
  }
  let mut o = 1
  for c in self.cycles() {
    let l = c.length()
    o = o / gcd(o, l) * l
  }
  o
}

///|
/// 奇偶性：偶置換為 1，奇置換為 -1。
pub fn Perm::sign(self : Perm) -> Int32 {
  // 輪分解中，長度 l 的輪貢獻 (l-1) 個對換
  let mut transpositions = 0
  for c in self.cycles() {
    transpositions = transpositions + (c.length() - 1)
  }
  if transpositions % 2 == 0 {
    1
  } else {
    -1
  }
}

///|
/// 共軛 `p ∘ self ∘ p^{-1}`。
pub fn Perm::conjugate_by(self : Perm, p : Perm) -> Perm {
  p.compose(self).compose(p.inverse())
}

///|
/// 單點軌道（循環 ⟨self⟩ 作用於 `x`）。
pub fn Perm::orbit_of(self : Perm, x : Int32) -> Array[Int32] {
  let out : Array[Int32] = []
  let mut j = x
  while true {
    out.push(j)
    j = self.img[j]
    if j == x {
      break
    }
  }
  out
}

///|
pub impl Eq for Perm with fn equal(self : Perm, other : Perm) -> Bool {
  guard self.n == other.n else { return false }
  for i in 0..<self.n {
    guard self.img[i] == other.img[i] else { return false }
  }
  true
}

///|
pub extend Perm with Eq::{equal, not_equal}

///|
pub impl Show for Perm with fn to_string(self) {
  let cycs = self.nontrivial_cycles()
  if cycs.length() == 0 {
    return "id"
  }
  let mut s = ""
  for c in cycs {
    s = s + "("
    for i, v in c {
      if i > 0 {
        s = s + " "
      }
      s = s + v.to_string()
    }
    s = s + ")"
  }
  s
}

///|
pub extend Perm with Show::{to_string, output}

///|
/// Debug（供 `assert_eq` / `inspect` 之結構化差異顯示）。
pub impl Debug for Perm with fn to_repr(self) {
  Repr::literal(self.to_string())
}

///|
pub extend Perm with Debug::{to_repr}
