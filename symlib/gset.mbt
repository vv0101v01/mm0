///|
/// # GSet — G-集之建構、軌道、Burnside 計數、Cayley 圖、軌道折疊、自由 G-集單子
///
/// `GSetOf { x, imgs }` 是 G-集之表格式表示（x = 點數，imgs[g][i] = g·i），
/// 由 `PermGroup` 之元素表（`PermGroup::elements`）一次建構，之後所有作用皆為 O(1) 查表。
///
/// - 建構：`gset_points`（G 作用於自身 = 左正則）、`gset_pairs`、`gset_edges`、
///   `gset_from_action`（任意 FinAction）、`gset_induced` = G×X（自由）、
///   `gset_coinduced` = X^G（`(coinduced)^G = X`）
/// - 軌道：`gset_orbits`（union-find 式閉包）、`gset_orbit_sizes`、`gset_fixed_points`
/// - Burnside：`gset_burnside` = (軌道數, Σ_g fix(g)) ⇒ 軌道數 = (1/|G|)Σ fix(g)；
///   `gset_global_fixed` = 全局不動點
/// - Cayley：`symmetric_gen_set`（對稱生成集）、`cayley_graph`、`regular_perm`（左正則表示）、
///   `cayley_cert`（Cay(G) 之 Aut ⊇ 左正則像，且與引擎算得之 |Aut| 相符）
/// - 軌道折疊之規範形式：`fold_canonical`（以引擎之規範標號定折疊，與折疊代表元之選法無關）、
///   `fold_equal`、`fold_canonical_cert`
/// - 自由 G-集單子 T = G×−：`gset_monad_eta/map/mu/laws/naturality`（η、μ 之單子律逐點成立）
///
/// 相關檔案：`marks.mbt`（子群共軛類、標記向量、table of marks、Frobenius 互反）、
/// `permset.mbt`（置換集之規範形式）、`yoneda.mbt`（歸納/上歸納之態射層面）。

///|
/// G-集：X = {0..x-1}，`imgs[i]` = 第 i 個群元素（依 `PermGroup::elements` 之序）之像陣列。
pub(all) struct GSetOf {
  x : Int32
  imgs : Array[Array[Int32]]
}

///|
/// 列舉 {0..n-1} 之全部置換（n ≤ cap_n；用於 G-集規範形式之暴力最小化）。
pub fn all_perms(n : Int32, cap : Int32) -> Array[Perm] {
  guard n >= 0 else { abort("all_perms: negative n") }
  let out : Array[Perm] = []
  let cur = Array::make(n, 0)
  let used = Array::make(n, false)
  fn rec(d : Int32) -> Unit {
    if d == n {
      out.push(Perm::from_img(cur.copy()))
      guard out.length() <= cap else { abort("all_perms: too many") }
      return
    }
    for v in 0..<n {
      if !used[v] {
        used[v] = true
        cur[d] = v
        rec(d + 1)
        used[v] = false
      }
    }
  }
  rec(0)
  out
}

///|
/// 點作用 G-集（X = {0..n-1}）。
pub fn gset_points(group : PermGroup, cap : Int32) -> GSetOf {
  let elems = group.elements(cap)
  let imgs : Array[Array[Int32]] = []
  for e in elems {
    imgs.push(e.img.copy())
  }
  { x: group.size(), imgs, }
}

///|
/// 序對作用 G-集（X = V×V）。
pub fn gset_pairs(group : PermGroup, cap : Int32) -> GSetOf {
  let act = FinAction::on_pairs(group)
  gset_from_action(act, group, cap)
}

///|
/// 邊作用 G-集（X = E(G)）。
pub fn gset_edges(group : PermGroup, graph : Graph, cap : Int32) -> GSetOf {
  let act = FinAction::on_edges(group, graph)
  gset_from_action(act, group, cap)
}

///|
/// 由推導作用建構 G-集（逐元素提升）。
pub fn gset_from_action(
  act : FinAction,
  group : PermGroup,
  cap : Int32,
) -> GSetOf {
  let elems = group.elements(cap)
  let imgs : Array[Array[Int32]] = []
  for e in elems {
    imgs.push(act.lift(e))
  }
  { x: act.card(), imgs, }
}

///|
/// 歸納（induction）G-集：G × X（見 yoneda.mbt 之 Kan 擴張）。
pub fn gset_induced(group : PermGroup, x : Int32, cap : Int32) -> GSetOf {
  let elems = group.elements(cap)
  let imgs : Array[Array[Int32]] = []
  for e in elems {
    imgs.push(induced_lift(group, x, cap, e))
  }
  { x: elems.length() * x, imgs, }
}

///|
/// 上歸納（coinduction）G-集：X^G。
pub fn gset_coinduced(group : PermGroup, x : Int32, cap : Int32) -> GSetOf {
  let elems = group.elements(cap)
  let imgs : Array[Array[Int32]] = []
  for e in elems {
    imgs.push(coinduced_lift(group, x, cap, e))
  }
  { x: coinduced_card(group, x, cap), imgs, }
}

///|
/// G-集之軌道分割。
pub fn gset_orbits(gs : GSetOf) -> Array[Array[Int32]] {
  let seen = Array::make(gs.x, false)
  let out : Array[Array[Int32]] = []
  for s in 0..<gs.x {
    if !seen[s] {
      let orb : Array[Int32] = []
      let stack : Array[Int32] = [s]
      seen[s] = true
      while stack.length() > 0 {
        let v = stack.pop().unwrap()
        orb.push(v)
        for img in gs.imgs {
          let w = img[v]
          if !seen[w] {
            seen[w] = true
            stack.push(w)
          }
        }
      }
      orb.sort()
      out.push(orb)
    }
  }
  out
}

///|
/// 軌道大小（升冪）。
pub fn gset_orbit_sizes(gs : GSetOf) -> Array[Int32] {
  let s : Array[Int32] = []
  for o in gset_orbits(gs) {
    s.push(o.length())
  }
  s.sort()
  s
}

///|
/// 單一元素之不動點數。
pub fn gset_fixed_points(gs : GSetOf, i : Int32) -> Int32 {
  let mut c = 0
  for y in 0..<gs.x {
    if gs.imgs[i][y] == y {
      c = c + 1
    }
  }
  c
}

///|
/// Burnside 軌道計數（由 G-集直接計算）：#軌道 = (1/|G|) Σ_g |Fix(g)|。
pub fn gset_burnside(gs : GSetOf) -> (Int32, Int32) {
  let mut sum = 0
  for i in 0..<gs.imgs.length() {
    sum = sum + gset_fixed_points(gs, i)
  }
  let ng = gs.imgs.length()
  (gset_orbits(gs).length(), sum / ng)
}

///|
/// G-集之廣域不動點 |X^G|（= 標記 m_G）。
pub fn gset_global_fixed(gs : GSetOf) -> Int32 {
  let mut c = 0
  for y in 0..<gs.x {
    let mut ok = true
    for img in gs.imgs {
      if img[y] != y {
        ok = false
        break
      }
    }
    if ok {
      c = c + 1
    }
  }
  c
}

///|
/// 對稱生成集：群生成元 ∪ 其逆，去除恆等（Cayley 圖用）。
pub fn symmetric_gen_set(group : PermGroup) -> Array[Perm] {
  let out : Array[Perm] = []
  for s in group.generators() {
    if !s.is_identity() {
      out.push(s)
      let si = s.inverse()
      if !si.is_identity() {
        let mut dup = false
        for t in out {
          if t == si {
            dup = true
            break
          }
        }
        if !dup {
          out.push(si)
        }
      }
    }
  }
  out
}

///|
/// Cayley 圖 Cay(G,S)：頂點 = 群元素（依 elements 之序），邊 = {g, g∘s}。
pub fn cayley_graph(group : PermGroup, cap : Int32) -> Graph {
  let elems = group.elements(cap)
  let ng = elems.length()
  let lut = elem_lut_fast(elems)
  let s = symmetric_gen_set(group)
  let edges : Array[(Int32, Int32)] = []
  for gi in 0..<ng {
    for t in s {
      let prod = elems[gi].compose(t)
      let hi = lut.at(perm_key64(prod))
      edges.push((gi, hi))
    }
  }
  Graph::from_edges(ng, edges)
}

///|
/// 左正則表示：λ_h 在元素索引上之置換（λ_h(g) = h∘g）。
pub fn regular_perm(group : PermGroup, cap : Int32, h : Perm) -> Perm {
  let elems = group.elements(cap)
  let ng = elems.length()
  let lut = elem_lut_fast(elems)
  let img = Array::make(ng, 0)
  for gi in 0..<ng {
    let prod = h.compose(elems[gi])
    img[gi] = lut.at(perm_key64(prod))
  }
  Perm::from_img(img)
}

///|
/// Cayley 圖定理之機器證書：
/// (a) 每個 λ_h 確為 Cay(G,S) 之自同構（左正則表示 ↪ Aut）；
/// (b) λ 單射（h ≠ h' ⇒ λ_h ≠ λ_h'）；
/// (c) |Aut(Cay(G,S))| ≥ |G|，且 λ(G) ⊆ Aut（以引擎求得之群包含性驗證）。
/// 回傳 (a, b, c, |Aut(Cay)|, |G|)。
pub fn cayley_cert(
  group : PermGroup,
  cap : Int32,
) -> (Bool, Bool, Bool, Int64, Int64) {
  let cay = cayley_graph(group, cap)
  let elems = group.elements(cap)
  let mut a = true
  let keys : Array[Array[Int32]] = []
  for h in elems {
    let l = regular_perm(group, cap, h)
    if !is_automorphism(cay, l) {
      a = false
    }
    keys.push(l.img.copy())
  }
  // (b) 單射
  let mut b = true
  for i in 0..<keys.length() {
    for j in (i + 1)..<keys.length() {
      if cmp_arr(keys[i], keys[j]) == 0 {
        b = false
      }
    }
  }
  // (c)
  let aut = automorphism_group(cay)
  let mut c = aut.order() >= group.order()
  for h in elems {
    let l = regular_perm(group, cap, h)
    if !aut.contains(l) {
      c = false
      break
    }
  }
  (a, b, c, aut.order(), group.order())
}

///|
/// **規範軌道折疊**：先取圖之規範形式，再按 Aut 之軌道折疊。
/// 因規範形式只依賴同構類，折疊結果（含軌道順序、重數矩陣）亦只依賴同構類 ⇒
/// 這是「軌道折疊」之**規範化**版本（一般 `fold_graph` 之軌道順序依賴原標號）。
///
/// **衍生演算法加速**：搜索一次即得 (規範標號, 自同構生成元)；生成元以
/// 共軛 σ∘p∘σ⁻¹ 搬到規範標號下（O(|gens|·n)），**免第二次搜索**
/// （`automorphism_group(canonical_form(g))` 需再搜一次 ⇒ 約 2× 成本）。
pub fn fold_canonical(g : Graph) -> FoldedGraph {
  let res = search_graph(g, true)
  let sigma = labeling_perm(res.canon_lab)
  let cf = g.relabel(sigma)
  let gens : Array[Perm] = []
  for p in res.aut_gens {
    gens.push(p.conjugate_by(sigma))
  }
  let grp = PermGroup::new(g.order(), gens)
  fold_graph(cf, grp)
}

///|
/// 折疊結果相等（n, m, k, 軌道大小, 重數矩陣逐項相等）。
pub fn fold_equal(f1 : FoldedGraph, f2 : FoldedGraph) -> Bool {
  guard f1.n == f2.n && f1.m == f2.m && f1.k == f2.k else { return false }
  guard f1.edge_total == f2.edge_total else { return false }
  guard cmp_arr(f1.orbit_size, f2.orbit_size) == 0 else { return false }
  guard cmp_arr(f1.rep, f2.rep) == 0 else { return false }
  for i in 0..<f1.k {
    guard cmp_arr(f1.mul[i], f2.mul[i]) == 0 else { return false }
  }
  true
}

///|
/// 規範折疊之機器證書：fold_canonical 與 fold_canonical∘relabel 逐項相等。
pub fn fold_canonical_cert(g : Graph, sigma : Perm) -> Bool {
  fold_equal(fold_canonical(g), fold_canonical(g.relabel(sigma)))
}

///|
/// 自由 G-集單子 T(X) = G × X 之單位 η_X(x) = (e, x)。
pub fn gset_monad_eta(
  group : PermGroup,
  x : Int32,
  cap : Int32,
) -> Array[Int32] {
  let elems = group.elements(cap)
  let e = elem_lut_fast(elems).at(perm_key64(Perm::identity(group.size())))
  let img = Array::make(x, 0)
  for v in 0..<x {
    img[v] = e * x + v
  }
  img
}

///|
/// T 之態射映射 T(f)(g, v) = (g, f(v))。
pub fn gset_monad_map(
  group : PermGroup,
  f : FinMap,
  cap : Int32,
) -> Array[Int32] {
  let ng = group.elements(cap).length()
  let img = Array::make(ng * f.dom, 0)
  for gi in 0..<ng {
    for v in 0..<f.dom {
      img[gi * f.dom + v] = gi * f.cod + f.img[v]
    }
  }
  img
}

///|
/// 自由 G-集單子之乘法 μ_X(g, (h, v)) = (g∘h, v)。
pub fn gset_monad_mu(group : PermGroup, x : Int32, cap : Int32) -> Array[Int32] {
  let elems = group.elements(cap)
  let ng = elems.length()
  let lut = elem_lut_fast(elems)
  let img = Array::make(ng * ng * x, 0)
  for g1 in 0..<ng {
    let i1 = elems[g1].img
    for g2 in 0..<ng {
      let t = lut.at(compose_key64(i1, elems[g2].img))
      for v in 0..<x {
        img[g1 * (ng * x) + g2 * x + v] = t * x + v
      }
    }
  }
  img
}

///|
/// 自由 G-集單子律（逐點驗證）：
/// 左單位 μ∘T(η) = id、右單位 μ∘η_{T(X)} = id、結合 μ∘T(μ) = μ∘μ_{T(X)}。
pub fn gset_monad_laws(group : PermGroup, x : Int32, cap : Int32) -> Bool {
  let elems = group.elements(cap)
  let ng = elems.length()
  let lut = elem_lut_fast(elems)
  let e = lut.at(perm_key64(Perm::identity(group.size())))
  let tx = ng * x
  let ttx = ng * tx
  let mu = gset_monad_mu(group, x, cap)
  // T(η) : T(X) → T(T(X))，(g,v) ↦ (g, (e,v))
  let teta = Array::make(tx, 0)
  for g in 0..<ng {
    for v in 0..<x {
      teta[g * x + v] = g * tx + e * x + v
    }
  }
  // 左單位
  for i in 0..<tx {
    if mu[teta[i]] != i {
      return false
    }
  }
  // η_{T(X)} : T(X) → T(T(X))，(g,v) ↦ (e,(g,v))
  let etat = Array::make(tx, 0)
  for g in 0..<ng {
    for v in 0..<x {
      etat[g * x + v] = e * tx + g * x + v
    }
  }
  for i in 0..<tx {
    if mu[etat[i]] != i {
      return false
    }
  }
  // 結合：μ_X ∘ T(μ_X) == μ_X ∘ μ_{T(X)}
  let mu_t = gset_monad_mu(group, tx, cap) // μ_{T(X)} : T(T(T(X))) → T(T(X))
  let t_mu = Array::make(ng * ttx, 0) // T(μ_X) : T(T(T(X))) → T(T(X))
  for g in 0..<ng {
    for i in 0..<ttx {
      t_mu[g * ttx + i] = g * tx + mu[i]
    }
  }
  for i in 0..<(ng * ttx) {
    if mu[mu_t[i]] != mu[t_mu[i]] {
      return false
    }
  }
  true
}

///|
/// 自由 G-集單子之自然性：T(f)∘η_X = η_Y∘f 且 μ_Y∘T(T(f)) = T(f)∘μ_X。
pub fn gset_monad_naturality(
  group : PermGroup,
  f : FinMap,
  cap : Int32,
) -> Bool {
  let ng = group.elements(cap).length()
  let x = f.dom
  let y = f.cod
  let eta_x = gset_monad_eta(group, x, cap)
  let eta_y = gset_monad_eta(group, y, cap)
  let tf = gset_monad_map(group, f, cap)
  // η 自然性
  for v in 0..<x {
    if tf[eta_x[v]] != eta_y[f.img[v]] {
      return false
    }
  }
  // μ 自然性
  let mu_x = gset_monad_mu(group, x, cap)
  let mu_y = gset_monad_mu(group, y, cap)
  let ttf = Array::make(ng * ng * x, 0)
  for g1 in 0..<ng {
    for g2 in 0..<ng {
      for v in 0..<x {
        ttf[g1 * (ng * x) + g2 * x + v] = g1 * (ng * y) + g2 * y + f.img[v]
      }
    }
  }
  for i in 0..<(ng * ng * x) {
    if mu_y[ttf[i]] != tf[mu_x[i]] {
      return false
    }
  }
  true
}
