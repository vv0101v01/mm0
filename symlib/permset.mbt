///|
/// # PermSet — 置換集（非群）之規範形式與同構判定
///
/// `PermSet { n, gens }` 只是一組置換（**不必**封閉），代表「有向標號結構」之自同構候選集；
/// 其規範形式 = 在所有重標號 λ 下取字典序最小之編碼 ⇒ 兩個置換集共軛 iff 規範形式相同。
///
/// 注意：`permset_canon` 內部窮舉 n! 個重標號 ⇒ 每項成本 O(n!)；
/// 與逐對暴力比較之交叉點約在 n=6 之 41 項 / n=7 之 23 項（見 bench E 節）。

///|
/// G-集之編碼（給定標號 λ 下之生成元像串接）：G-集規範形式之原料。
pub(all) struct PermSet {
  n : Int32
  gens : Array[Perm]
}

///|
/// 由生成元建構 G-集（同一抽象群、不同作用）。
pub fn permset(n : Int32, gens : Array[Perm]) -> PermSet {
  for p in gens {
    guard p.size() == n else { abort("permset: generator size mismatch") }
  }
  { n, gens, }
}

///|
/// 標號 λ（位置 → 原點）下之編碼：逐生成元串接 λ^{-1}∘p∘λ 之像。
pub fn permset_encoding(ps : PermSet, lambda : Perm) -> Array[Int32] {
  let linv = lambda.inverse()
  let out : Array[Int32] = []
  for p in ps.gens {
    let q = linv.compose(p).compose(lambda)
    for i in 0..<ps.n {
      out.push(q.apply(i))
    }
  }
  out
}

///|
/// G-集之規範形式：全部標號下編碼之字典序最小者（n ≤ 8 暴力）。
pub fn permset_canon(ps : PermSet, cap : Int32) -> Array[Int32] {
  let perms = all_perms(ps.n, cap)
  let mut best : Array[Int32] = []
  for l in perms {
    let enc = permset_encoding(ps, l)
    if best.length() == 0 || cmp_arr(enc, best) < 0 {
      best = enc
    }
  }
  best
}

///|
/// G-集同構判定（規範形式相等）：需同維度、同生成元個數。
pub fn permset_isomorphic(a : PermSet, b : PermSet, cap : Int32) -> Bool {
  guard a.n == b.n && a.gens.length() == b.gens.length() else { return false }
  cmp_arr(permset_canon(a, cap), permset_canon(b, cap)) == 0
}

///|
/// G-集規範形式之機器證書：
/// (a) 重標號不變性；(b) 冪等性（規範化後再規範化不變）；
/// (c) 與「共軛」判準一致：b = λ^{-1}∘a∘λ ⇒ 同構。
pub fn permset_cert(
  ps : PermSet,
  lambda : Perm,
  cap : Int32,
) -> (Bool, Bool, Bool) {
  let c0 = permset_canon(ps, cap)
  let relab : Array[Perm] = []
  let linv = lambda.inverse()
  for p in ps.gens {
    relab.push(linv.compose(p).compose(lambda))
  }
  let ps2 = permset(ps.n, relab)
  let a = cmp_arr(c0, permset_canon(ps2, cap)) == 0
  // 冪等：以 c0 反推之 G-集（生成元 = 編碼切片）再規範化
  let k = ps.gens.length()
  let gens0 : Array[Perm] = []
  for j in 0..<k {
    let img = Array::make(ps.n, 0)
    for i in 0..<ps.n {
      img[i] = c0[j * ps.n + i]
    }
    gens0.push(Perm::from_img(img))
  }
  let b = cmp_arr(permset_canon(permset(ps.n, gens0), cap), c0) == 0
  let c = permset_isomorphic(ps, ps2, cap)
  (a, b, c)
}
