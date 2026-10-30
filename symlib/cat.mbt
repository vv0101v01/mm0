///|
/// # Cat — 範疇化（Categorification）
///
/// 把「計數/集合層面」的結構提升到「範疇層面」：
/// 1. **FinSet / FinMap**：有限集範疇（態射 = 全函數），id / 複合 / 單射 / 滿射 / 同構。
/// 2. **冪集單子 P**：單子 = 內函子範疇中的幺半群（η : Id → P，μ : P² → P），
///    並驗證自然性與單子律（範疇層面的「乘法結構」）。
/// 3. **Kleisli 範疇**：ListM 的 Kleisli 範疇（對象 = 型別，態射 = A → ListM[B]）。
/// 4. **Aut 函子**：圖同構 φ ↦ 共軛 σ ↦ φσφ^{-1}（函子性：保持 id 與複合）。
/// 5. **作用廣群 G-Set**：群作用 = 廣群；hom(x,y) = { g : g·x = y }，
///    連通分量 = 軌道（軌道折疊 = 廣群骨架），穩定子 = 迷向群；
///    廣群基數 |X//G| = Σ_{軌道代表 x} 1/|G_x| 把「計數」提升為「範疇基數」。

///|
/// 有限集（以基數表示）。
pub(all) struct FinSet {
  size : Int32
}

///|
/// 有限集之間的態射（全函數）：img[x] 為 x 的像。
pub(all) struct FinMap {
  dom : Int32
  cod : Int32
  img : Array[Int32]
}

///|
/// 建構態射（驗證像範圍）。
pub fn FinMap::new(dom : Int32, cod : Int32, img : Array[Int32]) -> FinMap {
  guard dom >= 0 && cod >= 0 else { abort("FinMap::new: negative size") }
  guard img.length() == dom else { abort("FinMap::new: image length mismatch") }
  for x in 0..<dom {
    guard img[x] >= 0 && img[x] < cod else {
      abort("FinMap::new: image out of range")
    }
  }
  { dom, cod, img, }
}

///|
/// 恆等態射。
pub fn FinMap::id(n : Int32) -> FinMap {
  let img = Array::make(n, 0)
  for i in 0..<n {
    img[i] = i
  }
  { dom: n, cod: n, img, }
}

///|
/// 複合 `self ∘ other`（other : A→B，self : B→C）。
pub fn FinMap::compose(self : FinMap, other : FinMap) -> FinMap {
  guard self.dom == other.cod else { abort("FinMap::compose: domain mismatch") }
  let img = Array::make(other.dom, 0)
  for x in 0..<other.dom {
    img[x] = self.img[other.img[x]]
  }
  FinMap::new(other.dom, self.cod, img)
}

///|
/// 是否單射。
pub fn FinMap::is_mono(self : FinMap) -> Bool {
  let seen = Array::make(self.cod, false)
  for x in 0..<self.dom {
    let y = self.img[x]
    guard !seen[y] else { return false }
    seen[y] = true
  }
  true
}

///|
/// 是否滿射。
pub fn FinMap::is_epi(self : FinMap) -> Bool {
  let seen = Array::make(self.cod, false)
  for x in 0..<self.dom {
    seen[self.img[x]] = true
  }
  for y in 0..<self.cod {
    guard seen[y] else { return false }
  }
  true
}

///|
/// 是否同構（雙射）。
pub fn FinMap::is_iso(self : FinMap) -> Bool {
  self.dom == self.cod && self.is_mono() && self.is_epi()
}

///|
/// 逆態射（非雙射則 abort）。
pub fn FinMap::inverse(self : FinMap) -> FinMap {
  guard self.is_iso() else { abort("FinMap::inverse: not an isomorphism") }
  let img = Array::make(self.cod, 0)
  for x in 0..<self.dom {
    img[self.img[x]] = x
  }
  FinMap::new(self.cod, self.dom, img)
}

///|
/// 態射相等。
pub fn FinMap::equal(self : FinMap, other : FinMap) -> Bool {
  guard self.dom == other.dom && self.cod == other.cod else { return false }
  for x in 0..<self.dom {
    guard self.img[x] == other.img[x] else { return false }
  }
  true
}

///|
/// 冪集函子之對象映射：P(X) = 2^|X|（子集以位遮罩表示，|X| ≤ 20）。
pub fn pow_obj(n : Int32) -> Int32 {
  guard n >= 0 && n <= 20 else { abort("pow_obj: need 0 <= n <= 20") }
  1 << n
}

///|
/// 冪集函子之態射映射：P(f)(S) = f(S)（像子集）。
pub fn pow_fmap(f : FinMap) -> FinMap {
  guard f.dom <= 20 && f.cod <= 20 else { abort("pow_fmap: set too large") }
  let d = pow_obj(f.dom)
  let c = pow_obj(f.cod)
  let img = Array::make(d, 0)
  for s in 0..<d {
    let mut t = 0
    for x in 0..<f.dom {
      if (s & (1 << x)) != 0 {
        t = t | (1 << f.img[x])
      }
    }
    img[s] = t
  }
  FinMap::new(d, c, img)
}

///|
/// 單子單位 η_X : X → P(X)，x ↦ {x}。
pub fn pow_unit(n : Int32) -> FinMap {
  guard n <= 20 else { abort("pow_unit: set too large") }
  let img = Array::make(n, 0)
  for x in 0..<n {
    img[x] = 1 << x
  }
  FinMap::new(n, pow_obj(n), img)
}

///|
/// 單子乘法 μ_X : P(P(X)) → P(X)，S ↦ ∪S（需 |X| ≤ 3 以控制 2^(2^n)）。
pub fn pow_mult(n : Int32) -> FinMap {
  guard n >= 0 && n <= 3 else { abort("pow_mult: need 0 <= n <= 3") }
  let pn = pow_obj(n)
  let ppn = pow_obj(pn)
  let img = Array::make(ppn, 0)
  for t in 0..<ppn {
    let mut u = 0
    for s in 0..<pn {
      if (t & (1 << s)) != 0 {
        u = u | s
      }
    }
    img[t] = u
  }
  FinMap::new(ppn, pn, img)
}

///|
/// 冪集單子之自然性：μ_Y ∘ P(P(f)) = P(f) ∘ μ_X。
pub fn pow_naturality(f : FinMap) -> Bool {
  guard f.dom <= 3 && f.cod <= 3 else { abort("pow_naturality: set too large") }
  let lhs = pow_mult(f.cod).compose(pow_fmap(pow_fmap(f)))
  let rhs = pow_fmap(f).compose(pow_mult(f.dom))
  lhs.equal(rhs)
}

///|
/// 冪集單子律（FinSet 層面）：
/// - 左單位：μ_X ∘ P(η_X) = id
/// - 右單位：μ_X ∘ η_{P(X)} = id
/// - 結合：μ_X ∘ P(μ_X) = μ_X ∘ μ_{P(X)}
pub fn pow_monad_laws(n : Int32) -> Bool {
  guard n >= 0 && n <= 3 else { abort("pow_monad_laws: need 0 <= n <= 3") }
  let pn = pow_obj(n)
  let mu = pow_mult(n)
  // 左單位：μ ∘ P(η) = id_{P(X)}
  let peta = pow_fmap(pow_unit(n))
  let left = mu.compose(peta)
  // 右單位：μ ∘ η_{P(X)} = id_{P(X)}
  let etap = pow_unit(pn)
  let right = mu.compose(etap)
  let units_ok = left.equal(FinMap::id(pn)) && right.equal(FinMap::id(pn))
  // 結合律：μ ∘ P(μ) = μ ∘ μ_{P(X)}；μ_{P(X)} 需 2^(2^n) ≤ 2^8 ⇒ 僅 n ≤ 1 可驗
  if pn > 3 {
    return units_ok
  }
  let pmu = pow_fmap(mu)
  let assoc_l = mu.compose(pmu)
  let mup = pow_mult(pn)
  let assoc_r = mu.compose(mup)
  units_ok && assoc_l.equal(assoc_r)
}

///|
/// Kleisli 範疇之恆等態射（ListM）。
pub fn[A] kleisli_id() -> (A) -> ListM[A] {
  fn(a) { ListM::pure(a) }
}

///|
/// Aut 函子之態射映射：圖同構 φ : G1 → G2 誘導共軛 Aut(G1) → Aut(G2)，
/// σ ↦ φ ∘ σ ∘ φ^{-1}。
pub fn aut_map(iso : Perm, group : PermGroup) -> PermGroup {
  group.conjugate_by(iso)
}

///|
/// Aut 函子性驗證：aut_map(φ2∘φ1)(σ) = aut_map(φ2)(aut_map(φ1)(σ))。
/// （以生成元共軛像比較；用於測試。）
pub fn aut_functorial(
  p1 : Perm,
  p2 : Perm,
  group : PermGroup,
) -> (PermGroup, PermGroup) {
  let composed = aut_map(p2.compose(p1), group)
  let stepped = aut_map(p2, aut_map(p1, group))
  (composed, stepped)
}

///|
/// 作用廣群 G-Set：群 G ↷ {0..n-1} 視為廣群，對象 = 點，
/// hom(x,y) = { g ∈ G : g·x = y }。
pub(all) struct GSet {
  group : PermGroup
}

///|
/// 由置換群建構作用廣群。
pub fn GSet::of(group : PermGroup) -> GSet {
  { group, }
}

///|
/// 態射集 hom(x, y)（列舉群元素版，僅限小群）。
pub fn GSet::hom(self : GSet, x : Int32, y : Int32, cap : Int32) -> Array[Perm] {
  let out : Array[Perm] = []
  for g in self.group.elements(cap) {
    if g.apply(x) == y {
      out.push(g)
    }
  }
  out
}

///|
/// 迷向群（isotropy / stabilizer）G_x = hom(x,x)。
pub fn GSet::isotropy(self : GSet, x : Int32) -> PermGroup {
  self.group.stabilizer(x)
}

///|
/// 連通分量 = 軌道（軌道折疊即廣群之骨架 skeleton）。
pub fn GSet::components(self : GSet) -> Array[Array[Int32]] {
  self.group.orbit_partition()
}

///|
/// 廣群基數 |X//G| = Σ_{軌道代表 x} 1/|G_x|（把計數提升為範疇基數）。
/// 平凡群時 = |X|；可遷作用時 = 1/|G_x|。
pub fn GSet::groupoid_cardinality(self : GSet) -> Double {
  let gorder = self.group.order().to_double()
  let mut sum = 0.0
  for orb in self.group.orbit_partition() {
    // |G_x| = |G| / |Orb(x)|（軌道-穩定子定理）
    let stab = gorder / orb.length().to_double()
    sum = sum + 1.0 / stab
  }
  sum
}

///|
/// Burnside 軌道計數：Σ_{x∈X} 1/|Orb(x)| = #軌道數
/// （廣群基數 |X//G| = |X|/|G| 之「骨架計數」對偶形式 — 測試用）。
pub fn GSet::orbit_sum_cardinality(self : GSet) -> Double {
  let n = self.group.size()
  let mut sum = 0.0
  for x in 0..<n {
    sum = sum + 1.0 / self.group.orbit(x).length().to_double()
  }
  sum
}
