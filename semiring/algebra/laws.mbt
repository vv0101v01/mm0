// ===========================================================================
// 半環定律檢查器
//
// 用途：任何一個新實例（熱帶、瓶頸、Pareto、計數、機率、循環群…）
// 都必須通過這裡的定律檢查，演算法才能安全地只依賴這些定律。
// 檢查器本身也接受「故意壞掉的實例」，測試會斷言它**必須**報錯
// （negative control，避免恆真測試）。
// ===========================================================================

///|
/// 定律檢查結果。
pub(all) struct LawReport {
  mut checks : Int32
  violations : Array[String]
}

///|
pub fn LawReport::ok(self : LawReport) -> Bool {
  self.violations.length() == 0
}

///|
pub fn LawReport::summary(self : LawReport) -> String {
  if self.ok() {
    "PASS (\{self.checks} checks)"
  } else {
    let sb = StringBuilder()
    sb.write_string("FAIL \{self.violations.length()}/\{self.checks}: ")
    let n = self.violations.length().min(3)
    for i in 0..<n {
      if i > 0 {
        sb.write_string(" | ")
      }
      sb.write_string(self.violations[i])
    }
    sb.to_string()
  }
}

///|
fn[S : Semiring + Show] law_check(
  name : String,
  gen : () -> S,
  samples : Int32,
) -> LawReport {
  let r = { checks: 0, violations: [], }
  let mut checks = 0
  for _ in 0..<samples {
    let a = gen()
    let b = gen()
    let c = gen()
    let z = Semiring::zero()
    let o = Semiring::one()
    checks = checks + 1
    if Semiring::plus(Semiring::plus(a, b), c) !=
      Semiring::plus(a, Semiring::plus(b, c)) {
      r.violations.push("\{name}: ⊕ 結合律 a=\{a} b=\{b} c=\{c}")
    }
    checks = checks + 1
    if Semiring::plus(a, b) != Semiring::plus(b, a) {
      r.violations.push("\{name}: ⊕ 交換律 a=\{a} b=\{b}")
    }
    checks = checks + 1
    if Semiring::plus(a, z) != a {
      r.violations.push("\{name}: 0 為 ⊕ 單位元 a=\{a}")
    }
    checks = checks + 1
    if Semiring::times(Semiring::times(a, b), c) !=
      Semiring::times(a, Semiring::times(b, c)) {
      r.violations.push("\{name}: ⊗ 結合律 a=\{a} b=\{b} c=\{c}")
    }
    checks = checks + 1
    if Semiring::times(a, o) != a || Semiring::times(o, a) != a {
      r.violations.push("\{name}: 1 為 ⊗ 單位元 a=\{a}")
    }
    checks = checks + 1
    if Semiring::times(a, z) != z || Semiring::times(z, a) != z {
      r.violations.push("\{name}: 0 為 ⊗ 吸收元 a=\{a}")
    }
    checks = checks + 1
    if Semiring::times(a, Semiring::plus(b, c)) !=
      Semiring::plus(Semiring::times(a, b), Semiring::times(a, c)) {
      r.violations.push("\{name}: 左分配律 a=\{a} b=\{b} c=\{c}")
    }
    checks = checks + 1
    if Semiring::times(Semiring::plus(a, b), c) !=
      Semiring::plus(Semiring::times(a, c), Semiring::times(b, c)) {
      r.violations.push("\{name}: 右分配律 a=\{a} b=\{b} c=\{c}")
    }
  }
  r.checks = checks
  r
}

///|
/// 冪等半環的額外定律：x ⊕ x = x、自然序與 ⊕ 一致。
fn[S : IdempotentSemiring + Show] law_check_idem(
  name : String,
  gen : () -> S,
  samples : Int32,
) -> LawReport {
  let r = law_check(name, gen, samples)
  let mut checks = r.checks
  for _ in 0..<samples {
    let a = gen()
    let b = gen()
    checks = checks + 1
    if Semiring::plus(a, a) != a {
      r.violations.push("\{name}: ⊕ 冪等律")
    }
    checks = checks + 1
    if !IdempotentSemiring::le(a, Semiring::plus(a, b)) {
      r.violations.push("\{name}: a ≤ a ⊕ b")
    }
    checks = checks + 1
    if IdempotentSemiring::le(a, b) != (Semiring::plus(a, b) == b) {
      r.violations.push("\{name}: 自然序定義不一致")
    }
  }
  r.checks = checks
  r
}

///|
/// 星閉定律：a* = 1 ⊕ a·a*、a* = 1 ⊕ a*·a。
///
/// 這些展開式對任何「封閉半環」都成立（不需要冪等）；
/// 需要冪等的額外定律（a*·a* = a*、(a*)* = a*）見 `law_check_star_idem`。
fn[S : StarSemiring + Show] law_check_star(
  name : String,
  gen : () -> S,
  samples : Int32,
) -> LawReport {
  let r = law_check(name, gen, samples)
  let mut checks = r.checks
  for _ in 0..<samples {
    let a = gen()
    let sa = StarSemiring::star(a)
    checks = checks + 1
    if sa != Semiring::plus(Semiring::one(), Semiring::times(a, sa)) {
      r.violations.push("\{name}: a* = 1 ⊕ a·a*")
    }
    checks = checks + 1
    if sa != Semiring::plus(Semiring::one(), Semiring::times(sa, a)) {
      r.violations.push("\{name}: a* = 1 ⊕ a*·a")
    }
  }
  r.checks = checks
  r
}

///|
/// 冪等 + 星閉的完整定律集。
fn[S : StarSemiring + IdempotentSemiring + Show] law_check_star_idem(
  name : String,
  gen : () -> S,
  samples : Int32,
) -> LawReport {
  let r = law_check_idem(name, gen, samples)
  let mut checks = r.checks
  for _ in 0..<samples {
    let a = gen()
    let sa = StarSemiring::star(a)
    checks = checks + 1
    if sa != Semiring::plus(Semiring::one(), Semiring::times(a, sa)) {
      r.violations.push("\{name}: a* = 1 ⊕ a·a*")
    }
    checks = checks + 1
    if sa != Semiring::plus(Semiring::one(), Semiring::times(sa, a)) {
      r.violations.push("\{name}: a* = 1 ⊕ a*·a")
    }
    checks = checks + 1
    if Semiring::times(sa, sa) != sa {
      r.violations.push("\{name}: a* 冪等 (a*·a* = a*)")
    }
    checks = checks + 1
    if StarSemiring::star(sa) != sa {
      r.violations.push("\{name}: (a*)* = a*")
    }
  }
  r.checks = checks
  r
}

///|
/// 對外 API：檢查半環定律。
pub fn[S : Semiring + Show] check_semiring(
  name : String,
  gen : () -> S,
  samples~ : Int32 = 32,
) -> LawReport {
  law_check(name, gen, samples)
}

///|
/// 對外 API：檢查冪等半環定律。
pub fn[S : IdempotentSemiring + Show] check_idempotent(
  name : String,
  gen : () -> S,
  samples~ : Int32 = 32,
) -> LawReport {
  law_check_idem(name, gen, samples)
}

///|
/// 對外 API：檢查星閉半環定律（不需要冪等）。
pub fn[S : StarSemiring + Show] check_star(
  name : String,
  gen : () -> S,
  samples~ : Int32 = 32,
) -> LawReport {
  law_check_star(name, gen, samples)
}

///|
/// 對外 API：檢查冪等星閉半環的完整定律集。
pub fn[S : StarSemiring + IdempotentSemiring + Show] check_star_idem(
  name : String,
  gen : () -> S,
  samples~ : Int32 = 32,
) -> LawReport {
  law_check_star_idem(name, gen, samples)
}

///|
/// 對外 API：檢查么半群定律。
pub fn[M : Monoid + Show] check_monoid(
  name : String,
  gen : () -> M,
  samples~ : Int32 = 32,
) -> LawReport {
  let r = { checks: 0, violations: [], }
  let mut checks = 0
  for _ in 0..<samples {
    let a = gen()
    let b = gen()
    let c = gen()
    checks = checks + 1
    if Monoid::combine(Monoid::combine(a, b), c) !=
      Monoid::combine(a, Monoid::combine(b, c)) {
      r.violations.push("\{name}: ⊗ 結合律 a=\{a} b=\{b} c=\{c}")
    }
    checks = checks + 1
    if Monoid::combine(a, Monoid::empty()) != a ||
      Monoid::combine(Monoid::empty(), a) != a {
      r.violations.push("\{name}: e 為單位元")
    }
  }
  r.checks = checks
  r
}

///|
/// 完全正則定律：a ⊗ a° ⊗ a = a、a ⊗ a° 冪等、a^m = e_a。
pub fn[G : GroupElement + Show] check_group_element(
  name : String,
  gen : () -> G,
  samples~ : Int32 = 32,
) -> LawReport {
  let r = law_check(name, gen, samples)
  let mut checks = r.checks
  for _ in 0..<samples {
    let a = gen()
    let inv = GroupElement::group_inv(a)
    checks = checks + 1
    if Semiring::times(Semiring::times(a, inv), a) != a {
      r.violations.push("\{name}: a·a°·a = a")
    }
    checks = checks + 1
    let e = GroupElement::group_id(a)
    if Semiring::times(a, inv) != e || Semiring::times(inv, a) != e {
      r.violations.push("\{name}: a·a° = a°·a = e")
    }
    checks = checks + 1
    if Semiring::times(e, e) != e {
      r.violations.push("\{name}: e 冪等")
    }
    let m = GroupElement::order_bound(a)
    if m > 0 && m <= 4096 {
      checks = checks + 1
      if pow_squaring(a, m) != e {
        r.violations.push("\{name}: a^m = e（m = \{m}）")
      }
    }
  }
  r.checks = checks
  r
}

///|
/// 浮點半環的定律檢查：以距離函數 `dist` 與容差 `eps` 判定相等。
///
/// 之所以需要這個入口：IEEE 754 的加法/乘法不滿足嚴格結合律，
/// 若用嚴格等值檢查，`Prob`、`LogSumExp` 等浮點半環會被誤判為「壞掉的實例」。
/// 半環的**結構**仍然正確，只是等值判定必須是有容差的等價關係。
fn[S : Semiring] law_check_approx(
  name : String,
  gen : () -> S,
  dist : (S, S) -> Double,
  eps : Double,
  samples : Int32,
) -> LawReport {
  let r = { checks: 0, violations: [], }
  let eq = fn(a : S, b : S) { dist(a, b) <= eps }
  let mut checks = 0
  for _ in 0..<samples {
    let a = gen()
    let b = gen()
    let c = gen()
    let z = Semiring::zero()
    let o = Semiring::one()
    checks = checks + 1
    if !eq(
        Semiring::plus(Semiring::plus(a, b), c),
        Semiring::plus(a, Semiring::plus(b, c)),
      ) {
      r.violations.push("\{name}: ⊕ 結合律")
    }
    checks = checks + 1
    if !eq(Semiring::plus(a, b), Semiring::plus(b, a)) {
      r.violations.push("\{name}: ⊕ 交換律")
    }
    checks = checks + 1
    if !eq(Semiring::plus(a, z), a) {
      r.violations.push("\{name}: 0 為 ⊕ 單位元")
    }
    checks = checks + 1
    if !eq(
        Semiring::times(Semiring::times(a, b), c),
        Semiring::times(a, Semiring::times(b, c)),
      ) {
      r.violations.push("\{name}: ⊗ 結合律")
    }
    checks = checks + 1
    if !eq(Semiring::times(a, o), a) || !eq(Semiring::times(o, a), a) {
      r.violations.push("\{name}: 1 為 ⊗ 單位元")
    }
    checks = checks + 1
    if !eq(Semiring::times(a, z), z) || !eq(Semiring::times(z, a), z) {
      r.violations.push("\{name}: 0 為 ⊗ 吸收元")
    }
    checks = checks + 1
    if !eq(
        Semiring::times(a, Semiring::plus(b, c)),
        Semiring::plus(Semiring::times(a, b), Semiring::times(a, c)),
      ) {
      r.violations.push("\{name}: 左分配律")
    }
    checks = checks + 1
    if !eq(
        Semiring::times(Semiring::plus(a, b), c),
        Semiring::plus(Semiring::times(a, c), Semiring::times(b, c)),
      ) {
      r.violations.push("\{name}: 右分配律")
    }
  }
  r.checks = checks
  r
}

///|
/// 對外 API：有容差的半環定律檢查。
pub fn[S : Semiring] check_semiring_approx(
  name : String,
  gen : () -> S,
  dist : (S, S) -> Double,
  eps~ : Double = 1.0e-9,
  samples~ : Int32 = 32,
) -> LawReport {
  law_check_approx(name, gen, dist, eps, samples)
}
