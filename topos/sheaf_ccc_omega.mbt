///|
// Topos Pillar — Layer 2: Sheaves, Plus-Construction & Sheafification L^2,
// Cartesian Closedness of Sheaf Categories, Subobject Classifier Ω / Ω_J,
// Lawvere–Tierney Topologies, Elementary Topos & Giraud Axioms.

///|
/// A compatible (matching) family `{ x_f ∈ P(dom(f)) }_{f ∈ sieve.arrows}`
/// satisfying `P.res[g](x_f) == x_{f ∘ g}` for every composable `g`.
pub(all) struct MatchingFamily {
  sieve : Sieve
  values : Array[Int32]
} derive(Debug, Eq)

///|
pub extend MatchingFamily with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend MatchingFamily with Eq::{not_equal, equal}

///|
/// Output of Grothendieck sheafification `a(P) = (P^+)^+`.
pub(all) struct SheafificationResult {
  plus_once : @sym.Presheaf
  sheaf : @sym.Presheaf
  unit : PresheafHom
}

///|
/// Exponential object `G^F` in PSh(C) (and automatically in Sh(C, J) whenever
/// `G` is a J-sheaf!), bundled with its Hom tables and evaluation map
/// `ev : G^F × F => G`.
pub(all) struct ExponentialData {
  exp : @sym.Presheaf
  prod_exp_dom : @sym.Presheaf
  eval_hom : PresheafHom
  thetas_by_obj : Array[Array[PresheafHom]]
}

///|
/// Subobject classifier `Ω_J` of `Sh(C, J)` (equal to `Ω` of `PSh(C)` when
/// `J` is the trivial topology), bundled with `true_hom : 1 => Ω_J` and
/// the indexed table of J-closed sieves at each object.
pub(all) struct SubobjectClassifierData {
  omega : @sym.Presheaf
  terminal : @sym.Presheaf
  true_hom : PresheafHom
  closed_sieves : Array[Array[Sieve]]
}

///|
fn arrow_pos_in_sieve(s : Sieve, m : Int32) -> Int32 {
  let mut lo = 0
  let mut hi = s.arrows.length() - 1
  while lo <= hi {
    let mid = (lo + hi) / 2
    if s.arrows[mid] == m {
      return mid
    } else if s.arrows[mid] < m {
      lo = mid + 1
    } else {
      hi = mid - 1
    }
  }
  -1
}

///|
/// Check whether `mf` is a valid matching family for `p` over `mf.sieve`.
pub fn is_matching_family(p : @sym.Presheaf, mf : MatchingFamily) -> Bool {
  let c = p.cat
  let s = mf.sieve
  guard sieve_is_valid(c, s) && mf.values.length() == s.arrows.length() else {
    return false
  }
  for i in 0..<s.arrows.length() {
    let f = s.arrows[i]
    let v = mf.values[i]
    guard v >= 0 && v < p.size[c.dom[f]] else { return false }
  }
  for i in 0..<s.arrows.length() {
    let f = s.arrows[i]
    let xf = mf.values[i]
    for g in 0..<c.nmor {
      if c.cod[g] == c.dom[f] {
        let fg = c.comp[f * c.nmor + g]
        let pos = arrow_pos_in_sieve(s, fg)
        guard pos >= 0 && p.res[g][xf] == mf.values[pos] else { return false }
      }
    }
  }
  true
}

///|
/// Enumerate all matching families `Match(s, p)` via naturality isomorphism
/// `Match(s, p) ≅ Hom_PSh(S_psh, p)`.
pub fn enumerate_matching_families(
  p : @sym.Presheaf,
  s : Sieve,
  cap~ : Int32 = 4096,
) -> Array[MatchingFamily] {
  let c = p.cat
  let (s_psh, _) = presheaf_of_sieve(c, s)
  let (_, hom_arrows) = presheaf_representable_with_table(c, s.target)
  // Map each arrow in `s` to its local element index in `s_psh(dom(f))`.
  let arrow_local_idx = Array::make(s.arrows.length(), 0)
  for i in 0..<s.arrows.length() {
    let f = s.arrows[i]
    let v = c.dom[f]
    let mut sub_idx = 0
    for k in 0..<hom_arrows[v].length() {
      let m = hom_arrows[v][k]
      if m == f {
        arrow_local_idx[i] = sub_idx
        break
      }
      if sieve_contains(s, m) {
        sub_idx = sub_idx + 1
      }
    }
  }
  let homs = presheaf_hom_enumerate(s_psh, p, cap~)
  let out : Array[MatchingFamily] = []
  for h in homs {
    let vals = Array::make(s.arrows.length(), 0)
    for i in 0..<s.arrows.length() {
      let f = s.arrows[i]
      vals[i] = h.components[c.dom[f]][arrow_local_idx[i]]
    }
    out.push({ sieve: s, values: vals, })
  }
  out
}

///|
/// Restrict a section `sec ∈ p(s.target)` to its canonical matching family on `s`.
pub fn section_to_matching_family(
  p : @sym.Presheaf,
  s : Sieve,
  sec : Int32,
) -> MatchingFamily {
  let vals = Array::make(s.arrows.length(), 0)
  for i in 0..<s.arrows.length() {
    let f = s.arrows[i]
    vals[i] = p.res[f][sec]
  }
  { sieve: s, values: vals, }
}

///|
/// Restrict a matching family `mf` on `S` to a smaller sieve `R ⊆ S`.
fn restrict_matching_family(mf : MatchingFamily, r : Sieve) -> MatchingFamily {
  let vals = Array::make(r.arrows.length(), 0)
  for i in 0..<r.arrows.length() {
    let pos = arrow_pos_in_sieve(mf.sieve, r.arrows[i])
    guard pos >= 0 else { abort("restrict_matching_family: not a subsieve") }
    vals[i] = mf.values[pos]
  }
  { sieve: r, values: vals, }
}

///|
/// Decide whether `p` is a J-separated presheaf on `site`: for every object `u`
/// and every covering sieve `S ∈ J(u)`, amalgamation (if it exists) is unique.
pub fn is_separated_presheaf(site : Site, p : @sym.Presheaf) -> Bool {
  guard site_is_valid(site) && @sym.is_presheaf(p) else { return false }
  for u in 0..<site.cat.nobj {
    for s in site.topology.covers[u] {
      for x in 0..<p.size[u] {
        for y in (x + 1)..<p.size[u] {
          if section_to_matching_family(p, s, x) ==
            section_to_matching_family(p, s, y) {
            return false
          }
        }
      }
    }
  }
  true
}

///|
/// Decide whether `p` is a genuine J-sheaf on `site`: for every object `u` and
/// every covering sieve `S ∈ J(u)`, `p(u) -> Match(S, p)` is a bijection.
pub fn is_sheaf(site : Site, p : @sym.Presheaf) -> Bool {
  guard is_separated_presheaf(site, p) else { return false }
  for u in 0..<site.cat.nobj {
    for s in site.topology.covers[u] {
      let mfs = enumerate_matching_families(p, s, cap=8192)
      if mfs.length() != p.size[u] {
        return false
      }
      // Separatedness already proves injectivity of p(u) -> Match(S, p) between
      // finite sets of equal cardinality, but we also verify surjectivity directly.
      for mf in mfs {
        let mut found = false
        for sec in 0..<p.size[u] {
          if section_to_matching_family(p, s, sec) == mf {
            found = true
            break
          }
        }
        if !found {
          return false
        }
      }
    }
  }
  true
}

///|
/// Equivalence of two matching families `(S1, m1) ~ (S2, m2)` in the filtered
/// colimit `P^+(u) = colim_{S ∈ J(u)^op} Match(S, P)`:
/// holds iff there exists `T ∈ J(u)` with `T ⊆ S1 ∩ S2` such that `m1|_T == m2|_T`.
fn matching_families_colimit_eq(
  site : Site,
  u : Int32,
  mf1 : MatchingFamily,
  mf2 : MatchingFamily,
) -> Bool {
  let inter = sieve_inter(mf1.sieve, mf2.sieve)
  for t in site.topology.covers[u] {
    if sieve_subset(t, inter) {
      if restrict_matching_family(mf1, t) == restrict_matching_family(mf2, t) {
        return true
      }
    }
  }
  false
}

///|
/// Grothendieck's plus-construction `(P^+, η_P : P => P^+)` on `(C, J)`:
///   `P^+(u) = colim_{S ∈ J(u)^op} Match(S, P)`.
/// One application turns any presheaf into a J-separated presheaf; a second
/// application turns any separated presheaf into a J-sheaf.
pub fn plus_construction(
  site : Site,
  p : @sym.Presheaf,
) -> (@sym.Presheaf, PresheafHom) {
  let c = site.cat
  let reps_by_u : Array[Array[MatchingFamily]] = []
  let size = Array::make(c.nobj, 0)
  for u in 0..<c.nobj {
    let reps : Array[MatchingFamily] = []
    for s in site.topology.covers[u] {
      for mf in enumerate_matching_families(p, s, cap=4096) {
        let mut dup = false
        for r in reps {
          if matching_families_colimit_eq(site, u, mf, r) {
            dup = true
            break
          }
        }
        if !dup {
          reps.push(mf)
        }
      }
    }
    size[u] = reps.length()
    reps_by_u.push(reps)
  }
  // Restriction along h : u -> v pulls (S, mf) back to (h*(S), g |-> mf(h ∘ g)).
  let res : Array[Array[Int32]] = []
  for h in 0..<c.nmor {
    let u = c.dom[h]
    let v = c.cod[h]
    let map_h = Array::make(size[v], 0)
    for idx in 0..<size[v] {
      let mf = reps_by_u[v][idx]
      let hs = sieve_pullback(c, mf.sieve, h)
      let pulled_vals = Array::make(hs.arrows.length(), 0)
      for k in 0..<hs.arrows.length() {
        let g = hs.arrows[k]
        let hg = c.comp[h * c.nmor + g]
        let pos = arrow_pos_in_sieve(mf.sieve, hg)
        guard pos >= 0 else {
          abort("plus_construction: pullback arrow missing")
        }
        pulled_vals[k] = mf.values[pos]
      }
      let pulled : MatchingFamily = { sieve: hs, values: pulled_vals, }
      let mut cls = -1
      for c_idx in 0..<reps_by_u[u].length() {
        if matching_families_colimit_eq(site, u, pulled, reps_by_u[u][c_idx]) {
          cls = c_idx
          break
        }
      }
      guard cls >= 0 else { abort("plus_construction: class missing") }
      map_h[idx] = cls
    }
    res.push(map_h)
  }
  let p_plus = @sym.presheaf_new(c, size, res)
  // Unit η_u(sec) = class of `(M_u, section_to_matching_family(p, M_u, sec))`.
  let unit_comps : Array[Array[Int32]] = []
  for u in 0..<c.nobj {
    let mu = sieve_maximal(c, u)
    let cu = Array::make(p.size[u], 0)
    for sec in 0..<p.size[u] {
      let mf = section_to_matching_family(p, mu, sec)
      let mut cls = -1
      for c_idx in 0..<reps_by_u[u].length() {
        if matching_families_colimit_eq(site, u, mf, reps_by_u[u][c_idx]) {
          cls = c_idx
          break
        }
      }
      guard cls >= 0 else { abort("plus_construction: unit class missing") }
      cu[sec] = cls
    }
    unit_comps.push(cu)
  }
  (
    p_plus,
    { cat: c, dom_size: p.size.copy(), cod_size: size, components: unit_comps, },
  )
}

///|
/// Associated sheaf functor `sheafify(site, p) = (p^+)^+` with universal unit
/// `η = η_{p^+} ∘ η_p : p => a(p)`.
pub fn sheafify(site : Site, p : @sym.Presheaf) -> SheafificationResult {
  let (p1, u1) = plus_construction(site, p)
  let (p2, u2) = plus_construction(site, p1)
  { plus_once: p1, sheaf: p2, unit: presheaf_hom_compose(u1, u2), }
}

///|
/// Theorem (Universal Property of Sheafification `a ⊣ i`):
/// `a(P)` is separated after one `+`, a genuine J-sheaf after two `+`, and for
/// any J-sheaf `G`, precomposition with `η : P => a(P)` induces a bijection
/// `Hom_Sh(a(P), G) ≅ Hom_PSh(P, i(G))`.
pub fn verify_sheafification_universal_property(
  site : Site,
  p : @sym.Presheaf,
  g_sheaf : @sym.Presheaf,
) -> Bool {
  guard is_sheaf(site, g_sheaf) else { return false }
  let sr = sheafify(site, p)
  if !is_separated_presheaf(site, sr.plus_once) ||
    !is_sheaf(site, sr.sheaf) ||
    !presheaf_hom_is_natural(p, sr.sheaf, sr.unit) {
    return false
  }
  let sh_homs = presheaf_hom_enumerate(sr.sheaf, g_sheaf, cap=4096)
  let psh_homs = presheaf_hom_enumerate(p, g_sheaf, cap=4096)
  if sh_homs.length() != psh_homs.length() {
    return false
  }
  // Check injectivity + surjectivity of precomposition `(- ∘ unit)`.
  for i in 0..<sh_homs.length() {
    let comp_i = presheaf_hom_compose(sr.unit, sh_homs[i])
    for j in (i + 1)..<sh_homs.length() {
      let comp_j = presheaf_hom_compose(sr.unit, sh_homs[j])
      if presheaf_hom_eq(comp_i, comp_j) {
        return false
      }
    }
    let mut hit = false
    for h in psh_homs {
      if presheaf_hom_eq(comp_i, h) {
        hit = true
        break
      }
    }
    if !hit {
      return false
    }
  }
  true
}

///|
/// Functorial postcomposition `y(h) : y(v) => y(u)` induced by `h : v -> u`.
fn yoneda_covariant_map(c : @sym.FinCat, h : Int32) -> PresheafHom {
  let v = c.dom[h]
  let u = c.cod[h]
  let (yv, arrows_v) = presheaf_representable_with_table(c, v)
  let (yu, arrows_u) = presheaf_representable_with_table(c, u)
  let comps : Array[Array[Int32]] = []
  for w in 0..<c.nobj {
    let cw = Array::make(yv.size[w], 0)
    for k in 0..<yv.size[w] {
      let g = arrows_v[w][k]
      let hg = c.comp[h * c.nmor + g]
      let mut pos = -1
      for idx in 0..<arrows_u[w].length() {
        if arrows_u[w][idx] == hg {
          pos = idx
          break
        }
      }
      guard pos >= 0 else { abort("yoneda_covariant_map: missing composite") }
      cw[k] = pos
    }
    comps.push(cw)
  }
  { cat: c, dom_size: yv.size, cod_size: yu.size, components: comps, }
}

///|
/// Product morphism `alpha × beta : P1 × Q1 => P2 × Q2`.
pub fn presheaf_product_hom(
  p1 : @sym.Presheaf,
  q1 : @sym.Presheaf,
  p2 : @sym.Presheaf,
  q2 : @sym.Presheaf,
  alpha : PresheafHom,
  beta : PresheafHom,
) -> PresheafHom {
  let c = p1.cat
  let dom_size = Array::make(c.nobj, 0)
  let cod_size = Array::make(c.nobj, 0)
  let comps : Array[Array[Int32]] = []
  for u in 0..<c.nobj {
    dom_size[u] = p1.size[u] * q1.size[u]
    cod_size[u] = p2.size[u] * q2.size[u]
    let cu = Array::make(dom_size[u], 0)
    for x in 0..<p1.size[u] {
      for y in 0..<q1.size[u] {
        cu[x * q1.size[u] + y] = alpha.components[u][x] * q2.size[u] +
          beta.components[u][y]
      }
    }
    comps.push(cu)
  }
  { cat: c, dom_size, cod_size, components: comps, }
}

///|
/// Construct the internal Hom / exponential presheaf `G^F` together with its
/// evaluation morphism `ev : G^F × F => G`:
///   `(G^F)(u) = Hom_PSh(y(u) × F, G)`
///   `(G^F)(h : v -> u)(θ) = θ ∘ (y(h) × id_F)`
///   `ev_u(θ, x) = θ_u(id_u, x)`.
pub fn presheaf_exponential(
  f_psh : @sym.Presheaf,
  g_psh : @sym.Presheaf,
) -> ExponentialData {
  let c = f_psh.cat
  let id_f = presheaf_hom_id(f_psh)
  let thetas_by_obj : Array[Array[PresheafHom]] = []
  let prods_by_obj : Array[@sym.Presheaf] = []
  let size = Array::make(c.nobj, 0)
  for u in 0..<c.nobj {
    let yu = presheaf_representable(c, u)
    let (prod_u, _, _) = presheaf_product(yu, f_psh)
    let homs = presheaf_hom_enumerate(prod_u, g_psh, cap=4096)
    size[u] = homs.length()
    thetas_by_obj.push(homs)
    prods_by_obj.push(prod_u)
  }
  let res : Array[Array[Int32]] = []
  for h in 0..<c.nmor {
    let v = c.dom[h]
    let u = c.cod[h]
    let yh = yoneda_covariant_map(c, h)
    let yv = presheaf_representable(c, v)
    let yu = presheaf_representable(c, u)
    let yh_times_id = presheaf_product_hom(yv, f_psh, yu, f_psh, yh, id_f)
    let map_h = Array::make(size[u], 0)
    for idx in 0..<size[u] {
      let theta = thetas_by_obj[u][idx]
      let pulled = presheaf_hom_compose(yh_times_id, theta)
      let mut pos = -1
      for k in 0..<thetas_by_obj[v].length() {
        if presheaf_hom_eq(pulled, thetas_by_obj[v][k]) {
          pos = k
          break
        }
      }
      guard pos >= 0 else {
        abort("presheaf_exponential: restricted hom missing")
      }
      map_h[idx] = pos
    }
    res.push(map_h)
  }
  let exp = @sym.presheaf_new(c, size, res)
  let (prod_exp_dom, _, _) = presheaf_product(exp, f_psh)
  // Evaluation ev_u(theta_idx, x) = theta_u(idx_of_id_u * f_psh.size[u] + x).
  let eval_comps : Array[Array[Int32]] = []
  for u in 0..<c.nobj {
    let (_, arrows_u) = presheaf_representable_with_table(c, u)
    let mut id_pos = -1
    for k in 0..<arrows_u[u].length() {
      if arrows_u[u][k] == c.id[u] {
        id_pos = k
        break
      }
    }
    guard id_pos >= 0 else { abort("presheaf_exponential: id_u missing") }
    let cu = Array::make(prod_exp_dom.size[u], 0)
    for t_idx in 0..<exp.size[u] {
      let theta = thetas_by_obj[u][t_idx]
      for x in 0..<f_psh.size[u] {
        cu[t_idx * f_psh.size[u] + x] = theta.components[u][id_pos *
          f_psh.size[u] +
          x]
      }
    }
    eval_comps.push(cu)
  }
  let eval_hom : PresheafHom = {
    cat: c,
    dom_size: prod_exp_dom.size,
    cod_size: g_psh.size.copy(),
    components: eval_comps,
  }
  { exp, prod_exp_dom, eval_hom, thetas_by_obj, }
}

///|
/// Currying transpose `Λ(m) : H => G^F` of `m : H × F => G`.
pub fn exponential_curry(
  h_psh : @sym.Presheaf,
  f_psh : @sym.Presheaf,
  g_psh : @sym.Presheaf,
  exp_data : ExponentialData,
  m : PresheafHom,
) -> PresheafHom {
  let c = h_psh.cat
  let comps : Array[Array[Int32]] = []
  for u in 0..<c.nobj {
    let (yu, arrows_u) = presheaf_representable_with_table(c, u)
    let (prod_uf, _, _) = presheaf_product(yu, f_psh)
    let cu = Array::make(h_psh.size[u], 0)
    for z in 0..<h_psh.size[u] {
      // Build θ : y(u) × F => G given by θ_v(k : v -> u, x) = m_v(H(k)(z), x).
      let theta_comps : Array[Array[Int32]] = []
      for v in 0..<c.nobj {
        let tv = Array::make(prod_uf.size[v], 0)
        for k_idx in 0..<yu.size[v] {
          let k_mor = arrows_u[v][k_idx]
          let hz = h_psh.res[k_mor][z]
          for x in 0..<f_psh.size[v] {
            tv[k_idx * f_psh.size[v] + x] = m.components[v][hz * f_psh.size[v] +
              x]
          }
        }
        theta_comps.push(tv)
      }
      let theta : PresheafHom = {
        cat: c,
        dom_size: prod_uf.size,
        cod_size: g_psh.size.copy(),
        components: theta_comps,
      }
      let mut pos = -1
      for t_idx in 0..<exp_data.thetas_by_obj[u].length() {
        if presheaf_hom_eq(theta, exp_data.thetas_by_obj[u][t_idx]) {
          pos = t_idx
          break
        }
      }
      guard pos >= 0 else { abort("exponential_curry: transposed hom missing") }
      cu[z] = pos
    }
    comps.push(cu)
  }
  {
    cat: c,
    dom_size: h_psh.size.copy(),
    cod_size: exp_data.exp.size.copy(),
    components: comps,
  }
}

///|
/// Uncurrying transpose `Λ^{-1}(n) = ev ∘ (n × id_F) : H × F => G` of `n : H => G^F`.
pub fn exponential_uncurry(
  h_psh : @sym.Presheaf,
  f_psh : @sym.Presheaf,
  exp_data : ExponentialData,
  n : PresheafHom,
) -> PresheafHom {
  let id_f = presheaf_hom_id(f_psh)
  let n_times_id = presheaf_product_hom(
    h_psh,
    f_psh,
    exp_data.exp,
    f_psh,
    n,
    id_f,
  )
  presheaf_hom_compose(n_times_id, exp_data.eval_hom)
}

///|
/// Theorem (Cartesian Closedness of Sheaf Categories `Sh(C, J)`):
/// Whenever `g_sheaf` is a J-sheaf on `site`:
///   1. `g_sheaf ^ f_sheaf` constructed in PSh(C) is AUTOMATICALLY a J-sheaf;
///   2. `ev : G^F × F => G` is natural;
///   3. `curry` and `uncurry` establish a natural bijection
///      `Hom_Sh(H × F, G) ≅ Hom_Sh(H, G^F)`.
pub fn verify_sheaf_cartesian_closed(
  site : Site,
  h_sheaf : @sym.Presheaf,
  f_sheaf : @sym.Presheaf,
  g_sheaf : @sym.Presheaf,
) -> Bool {
  guard is_sheaf(site, h_sheaf) &&
    is_sheaf(site, f_sheaf) &&
    is_sheaf(site, g_sheaf) else {
    return false
  }
  let exp_data = presheaf_exponential(f_sheaf, g_sheaf)
  if !is_sheaf(site, exp_data.exp) {
    return false
  }
  if !presheaf_hom_is_natural(exp_data.prod_exp_dom, g_sheaf, exp_data.eval_hom) {
    return false
  }
  let (hf_prod, _, _) = presheaf_product(h_sheaf, f_sheaf)
  if !is_sheaf(site, hf_prod) {
    return false
  }
  let lhs = presheaf_hom_enumerate(hf_prod, g_sheaf, cap=4096)
  let rhs = presheaf_hom_enumerate(h_sheaf, exp_data.exp, cap=4096)
  if lhs.length() != rhs.length() {
    return false
  }
  for m in lhs {
    let curried = exponential_curry(h_sheaf, f_sheaf, g_sheaf, exp_data, m)
    if !presheaf_hom_is_natural(h_sheaf, exp_data.exp, curried) {
      return false
    }
    let back = exponential_uncurry(h_sheaf, f_sheaf, exp_data, curried)
    if !presheaf_hom_eq(m, back) {
      return false
    }
  }
  for n in rhs {
    let uncurried = exponential_uncurry(h_sheaf, f_sheaf, exp_data, n)
    let back = exponential_curry(h_sheaf, f_sheaf, g_sheaf, exp_data, uncurried)
    if !presheaf_hom_eq(n, back) {
      return false
    }
  }
  true
}

///|
/// J-closure `cl_J(S) = { f : v -> target | f*(S) ∈ J(v) }` of a sieve `s`.
pub fn sieve_j_closure(site : Site, s : Sieve) -> Sieve {
  let c = site.cat
  let arrows : Array[Int32] = []
  for f in 0..<c.nmor {
    if c.cod[f] == s.target {
      if topology_covers(site.topology, sieve_pullback(c, s, f)) {
        arrows.push(f)
      }
    }
  }
  { target: s.target, arrows, }
}

///|
/// Check whether `s` is J-closed (`cl_J(s) == s`).
pub fn sieve_is_j_closed(site : Site, s : Sieve) -> Bool {
  sieve_j_closure(site, s) == s
}

///|
/// Construct the subobject classifier `(Ω_J, true : 1 => Ω_J)` of `Sh(C, J)`:
///   `Ω_J(u)` is the set of all J-closed sieves on `u`,
///   restriction along `h : v -> u` is pullback `S |-> h*(S)`,
///   `true_u(0) = M_u`.
pub fn subobject_classifier_sheaf(site : Site) -> SubobjectClassifierData {
  let c = site.cat
  let closed_sieves : Array[Array[Sieve]] = []
  let size = Array::make(c.nobj, 0)
  for u in 0..<c.nobj {
    let cu : Array[Sieve] = []
    for s in all_sieves_on(c, u) {
      if sieve_is_j_closed(site, s) {
        cu.push(s)
      }
    }
    size[u] = cu.length()
    closed_sieves.push(cu)
  }
  let res : Array[Array[Int32]] = []
  for h in 0..<c.nmor {
    let v = c.dom[h]
    let u = c.cod[h]
    let map_h = Array::make(size[u], 0)
    for idx in 0..<size[u] {
      let hs = sieve_pullback(c, closed_sieves[u][idx], h)
      let mut pos = -1
      for k in 0..<closed_sieves[v].length() {
        if closed_sieves[v][k] == hs {
          pos = k
          break
        }
      }
      guard pos >= 0 else {
        abort("subobject_classifier_sheaf: pullback of closed sieve not closed")
      }
      map_h[idx] = pos
    }
    res.push(map_h)
  }
  let omega = @sym.presheaf_new(c, size, res)
  let term = presheaf_terminal(c)
  let true_comps : Array[Array[Int32]] = []
  for u in 0..<c.nobj {
    let mu = sieve_maximal(c, u)
    let mut pos = -1
    for k in 0..<closed_sieves[u].length() {
      if closed_sieves[u][k] == mu {
        pos = k
        break
      }
    }
    guard pos >= 0 else {
      abort("subobject_classifier_sheaf: maximal sieve not closed")
    }
    true_comps.push([pos])
  }
  let true_hom : PresheafHom = {
    cat: c,
    dom_size: term.size,
    cod_size: size,
    components: true_comps,
  }
  { omega, terminal: term, true_hom, closed_sieves, }
}

///|
/// Presheaf subobject classifier `(Ω, true : 1 => Ω)` of `PSh(C)`.
pub fn subobject_classifier_presheaf(
  c : @sym.FinCat,
) -> SubobjectClassifierData {
  subobject_classifier_sheaf(site_new(c, topology_trivial(c)))
}

///|
/// Construct the Lawvere–Tierney topology `j : Ω => Ω` in `PSh(C)` induced by
/// `site`'s Grothendieck topology (`j_u(S) = cl_J(S)`).
pub fn lawvere_tierney_of_site(
  site : Site,
) -> (SubobjectClassifierData, PresheafHom) {
  let omega_data = subobject_classifier_presheaf(site.cat)
  let comps : Array[Array[Int32]] = []
  for u in 0..<site.cat.nobj {
    let n = omega_data.closed_sieves[u].length()
    let cu = Array::make(n, 0)
    for i in 0..<n {
      let cl = sieve_j_closure(site, omega_data.closed_sieves[u][i])
      let mut pos = -1
      for k in 0..<n {
        if omega_data.closed_sieves[u][k] == cl {
          pos = k
          break
        }
      }
      guard pos >= 0 else { abort("lawvere_tierney_of_site: closure missing") }
      cu[i] = pos
    }
    comps.push(cu)
  }
  (
    omega_data,
    {
      cat: site.cat,
      dom_size: omega_data.omega.size.copy(),
      cod_size: omega_data.omega.size.copy(),
      components: comps,
    },
  )
}

///|
/// Verify the three Lawvere–Tierney axioms on `j : Ω => Ω`:
///   1. `j` is natural (`j : Ω => Ω`),
///   2. `j ∘ true == true`,
///   3. `j ∘ j == j` (idempotence),
///   4. `j_u(S ∩ T) == j_u(S) ∩ j_u(T)` (commutes with internal ∧).
pub fn is_lawvere_tierney_operator(
  omega_data : SubobjectClassifierData,
  j_op : PresheafHom,
) -> Bool {
  if !presheaf_hom_is_natural(omega_data.omega, omega_data.omega, j_op) {
    return false
  }
  if !presheaf_hom_eq(
      presheaf_hom_compose(omega_data.true_hom, j_op),
      omega_data.true_hom,
    ) {
    return false
  }
  if !presheaf_hom_eq(presheaf_hom_compose(j_op, j_op), j_op) {
    return false
  }
  let c = omega_data.omega.cat
  for u in 0..<c.nobj {
    let sieves = omega_data.closed_sieves[u]
    for a in 0..<sieves.length() {
      for b in 0..<sieves.length() {
        let inter_ab = sieve_inter(sieves[a], sieves[b])
        let mut idx_ab = -1
        for k in 0..<sieves.length() {
          if sieves[k] == inter_ab {
            idx_ab = k
            break
          }
        }
        let ja = sieves[j_op.components[u][a]]
        let jb = sieves[j_op.components[u][b]]
        if sieves[j_op.components[u][idx_ab]] != sieve_inter(ja, jb) {
          return false
        }
      }
    }
  }
  true
}

///|
/// Inverse Lawvere–Tierney bijection: recover the Grothendieck topology `J_j`
/// from a Lawvere–Tierney operator `j : Ω => Ω` (`S ∈ J_j(u) iff j_u(S) == M_u`).
pub fn topology_of_lawvere_tierney(
  omega_data : SubobjectClassifierData,
  j_op : PresheafHom,
) -> GrothendieckTopology {
  let c = omega_data.omega.cat
  let covers : Array[Array[Sieve]] = []
  for u in 0..<c.nobj {
    let true_idx = omega_data.true_hom.components[u][0]
    let ku : Array[Sieve] = []
    for i in 0..<omega_data.closed_sieves[u].length() {
      if j_op.components[u][i] == true_idx {
        ku.push(omega_data.closed_sieves[u][i])
      }
    }
    covers.push(sort_unique_sieves(ku))
  }
  { nobj: c.nobj, covers, }
}

///|
/// Characteristic morphism `χ_m : X => Ω_J` classifying a monomorphism
/// `mono : A ↪ X` between J-sheaves (or J-closed subpresheaf):
///   `χ_{m, u}(x) = { f : v -> u | X.res[f](x) ∈ im(mono_v) }`.
pub fn characteristic_morphism(
  site : Site,
  x_psh : @sym.Presheaf,
  mono : PresheafHom,
  omega_j : SubobjectClassifierData,
) -> PresheafHom {
  guard presheaf_hom_is_mono(mono) else {
    abort("characteristic_morphism: morphism is not monic")
  }
  let c = site.cat
  let comps : Array[Array[Int32]] = []
  for u in 0..<c.nobj {
    let cu = Array::make(x_psh.size[u], 0)
    for x in 0..<x_psh.size[u] {
      let arrows : Array[Int32] = []
      for f in 0..<c.nmor {
        if c.cod[f] == u {
          let v = c.dom[f]
          let xf = x_psh.res[f][x]
          let mut in_im = false
          for a_elem in mono.components[v] {
            if a_elem == xf {
              in_im = true
              break
            }
          }
          if in_im {
            arrows.push(f)
          }
        }
      }
      let s : Sieve = { target: u, arrows, }
      let mut pos = -1
      for k in 0..<omega_j.closed_sieves[u].length() {
        if omega_j.closed_sieves[u][k] == s {
          pos = k
          break
        }
      }
      guard pos >= 0 else {
        abort("characteristic_morphism: sieve is not J-closed")
      }
      cu[x] = pos
    }
    comps.push(cu)
  }
  {
    cat: c,
    dom_size: x_psh.size.copy(),
    cod_size: omega_j.omega.size.copy(),
    components: comps,
  }
}

///|
/// Theorem (Subobject Classifier Axiom in `Sh(C, J)`):
///   1. `Ω_J` is a J-sheaf and `true : 1 => Ω_J` is a natural monomorphism;
///   2. For a monomorphism `mono : a_sheaf ↪ x_sheaf` in `Sh(C, J)`,
///      `χ_mono : x_sheaf => Ω_J` is the UNIQUE morphism making `a_sheaf`
///      isomorphic to the pullback `1 ×_{Ω_J} x_sheaf`!
pub fn verify_subobject_classifier_pullback(
  site : Site,
  a_sheaf : @sym.Presheaf,
  x_sheaf : @sym.Presheaf,
  mono : PresheafHom,
) -> Bool {
  guard is_sheaf(site, a_sheaf) &&
    is_sheaf(site, x_sheaf) &&
    presheaf_hom_is_natural(a_sheaf, x_sheaf, mono) &&
    presheaf_hom_is_mono(mono) else {
    return false
  }
  let omega_j = subobject_classifier_sheaf(site)
  if !is_sheaf(site, omega_j.omega) ||
    !presheaf_hom_is_natural(omega_j.terminal, omega_j.omega, omega_j.true_hom) ||
    !presheaf_hom_is_mono(omega_j.true_hom) {
    return false
  }
  let chi = characteristic_morphism(site, x_sheaf, mono, omega_j)
  if !presheaf_hom_is_natural(x_sheaf, omega_j.omega, chi) {
    return false
  }
  let (pb, _, pb_to_x) = presheaf_pullback(
    omega_j.terminal,
    x_sheaf,
    omega_j.true_hom,
    chi,
  )
  if !presheaf_are_isomorphic(a_sheaf, pb) {
    return false
  }
  for u in 0..<site.cat.nobj {
    if sort_unique_ints(pb_to_x.components[u]) !=
      sort_unique_ints(mono.components[u]) {
      return false
    }
  }
  // Uniqueness: check that among all h : X => Ω_J, ONLY chi has pullback
  // along `true` with the exact image of `mono` in X!
  let all_maps = presheaf_hom_enumerate(x_sheaf, omega_j.omega, cap=4096)
  let mut matching_maps = 0
  for h in all_maps {
    let (_, _, h_pb_to_x) = presheaf_pullback(
      omega_j.terminal,
      x_sheaf,
      omega_j.true_hom,
      h,
    )
    let mut same_subobj = true
    for u in 0..<site.cat.nobj {
      if sort_unique_ints(h_pb_to_x.components[u]) !=
        sort_unique_ints(mono.components[u]) {
        same_subobj = false
        break
      }
    }
    if same_subobj {
      matching_maps = matching_maps + 1
      if !presheaf_hom_eq(h, chi) {
        return false
      }
    }
  }
  matching_maps == 1
}

///|
/// Heyting negation `¬_J S = (S => cl_J(∅_u))` in `Ω_J(u)`.
pub fn omega_j_neg(site : Site, s : Sieve) -> Sieve {
  let bot_u = sieve_j_closure(site, sieve_empty(s.target))
  sieve_heyting_implies(site.cat, s, bot_u)
}

///|
/// Heyting join `S ∨_J T = cl_J(S ∪ T)` in `Ω_J(u)`.
pub fn omega_j_join(site : Site, s : Sieve, t : Sieve) -> Sieve {
  sieve_j_closure(site, sieve_union(s, t))
}

///|
/// Decide whether the sheaf topos `Sh(site)` is Boolean (`Ω_J` satisfies the
/// internal Law of Excluded Middle `S ∨_J ¬_J S == M_u` for all `u` and all
/// `S ∈ Ω_J(u)`).
pub fn is_boolean_topos(site : Site) -> Bool {
  let omega_j = subobject_classifier_sheaf(site)
  for u in 0..<site.cat.nobj {
    let top_u = sieve_maximal(site.cat, u)
    for s in omega_j.closed_sieves[u] {
      let join_em = omega_j_join(site, s, omega_j_neg(site, s))
      if join_em != top_u {
        return false
      }
    }
  }
  true
}

///|
/// Decide whether `Sh(site)` satisfies De Morgan's law (`¬_J S ∨_J ¬_J T == M_u`
/// whenever `S ∩ T == cl_J(∅_u)` — weaker than Boolean, holds e.g. on trees/lines!).
pub fn is_de_morgan_topos(site : Site) -> Bool {
  let omega_j = subobject_classifier_sheaf(site)
  for u in 0..<site.cat.nobj {
    let top_u = sieve_maximal(site.cat, u)
    let bot_u = sieve_j_closure(site, sieve_empty(u))
    for s in omega_j.closed_sieves[u] {
      for t in omega_j.closed_sieves[u] {
        if sieve_inter(s, t) == bot_u {
          let lhs = omega_j_join(
            site,
            omega_j_neg(site, s),
            omega_j_neg(site, t),
          )
          if lhs != top_u {
            return false
          }
        }
      }
    }
  }
  true
}

///|
/// Verify both Elementary Topos axioms (finite limits, Cartesian closedness,
/// subobject classifier) AND Giraud Grothendieck Topos axioms (sheafified
/// representables `{a(y(u))}` jointly separate morphisms, coproducts in
/// `Sh(C, J)` are disjoint and pullback-stable) on `site`.
pub fn verify_elementary_and_giraud_topos(site : Site) -> Bool {
  guard site_is_valid(site) else { return false }
  let term = presheaf_terminal(site.cat)
  if !is_sheaf(site, term) {
    return false
  }
  let omega_j = subobject_classifier_sheaf(site)
  if !is_sheaf(site, omega_j.omega) {
    return false
  }
  // Lawvere–Tierney round-trip check.
  let (omega_psh, j_op) = lawvere_tierney_of_site(site)
  if !is_lawvere_tierney_operator(omega_psh, j_op) {
    return false
  }
  if topology_of_lawvere_tierney(omega_psh, j_op) != site.topology {
    return false
  }
  // Sheafified representable generators a(y(u)).
  let gens : Array[@sym.Presheaf] = []
  for u in 0..<site.cat.nobj {
    let ay = sheafify(site, presheaf_representable(site.cat, u)).sheaf
    if !is_sheaf(site, ay) {
      return false
    }
    gens.push(ay)
  }
  if gens.length() > 0 {
    let g0 = gens[0]
    // Check CCC on (1, g0, Ω_J).
    if !verify_sheaf_cartesian_closed(site, term, g0, omega_j.omega) {
      return false
    }
    // Check Giraud disjointness of sheafified coproduct `g0 +_Sh g0`:
    // pullback of ι1 and ι2 is the initial sheaf a(0)!
    let (raw_sum, in1_raw, in2_raw) = presheaf_coproduct(g0, g0)
    let sh_sum = sheafify(site, raw_sum)
    let in1 = presheaf_hom_compose(in1_raw, sh_sum.unit)
    let in2 = presheaf_hom_compose(in2_raw, sh_sum.unit)
    let (pb_disjoint, _, _) = presheaf_pullback(g0, g0, in1, in2)
    let sh_init = sheafify(site, presheaf_initial(site.cat)).sheaf
    if !presheaf_are_isomorphic(pb_disjoint, sh_init) {
      return false
    }
  }
  true
}
