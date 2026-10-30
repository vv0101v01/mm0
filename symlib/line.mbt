///|
/// 線圖 L(G)：頂點 = G 之邊；兩頂點相鄰 ⇔ 兩邊共用端點。
pub fn line_graph(g : Graph) -> Graph {
  let es = g.edge_list()
  let m = es.length()
  let edges : Array[(Int32, Int32)] = []
  for i in 0..<m {
    let (a1, b1) = es[i]
    for j in (i + 1)..<m {
      let (a2, b2) = es[j]
      if a1 == a2 || a1 == b2 || b1 == a2 || b1 == b2 {
        edges.push((i, j))
      }
    }
  }
  Graph::from_edges(m, edges)
}

///|
/// 頂點之星團：與 v 關聯之邊索引（升冪）。
fn star_of(g : Graph, v : Int32) -> Array[Int32] {
  let out : Array[Int32] = []
  for i, e in g.edge_list() {
    let (a, b) = e
    if a == v || b == v {
      out.push(i)
    }
  }
  out
}

///|
/// 孤立頂點個數（ker Φ 之 S 因子）。
pub fn isolated_count(g : Graph) -> Int32 {
  let mut c = 0
  for v in 0..<g.order() {
    if g.degree(v) == 0 {
      c = c + 1
    }
  }
  c
}

///|
/// K₂ 分量個數（ker Φ 之 (ℤ/2) 因子）。
pub fn k2_component_count(g : Graph) -> Int32 {
  let mut c = 0
  for comp in g.components() {
    if comp.length() == 2 {
      c = c + 1
    }
  }
  c
}

///|
/// ker Φ 之階 = (孤立點數)! · 2^(K₂分量數)。
pub fn line_kernel_order(g : Graph) -> Int64 {
  let mut r = 1L
  for i in 2..<(isolated_count(g) + 1) {
    r = r * i.to_int64()
  }
  for _ in 0..<k2_component_count(g) {
    r = r * 2L
  }
  r
}

///|
/// 提升定理之 Φ：把 Aut(G) 經邊作用提升為 L(G) 上之置換群。
pub fn aut_on_line(g : Graph) -> PermGroup {
  let aut = automorphism_group(g)
  let act = FinAction::on_edges(aut, g)
  let m = g.size()
  let lifted : Array[Perm] = []
  for img in act.gens {
    let p = Perm::from_img(img)
    if !p.is_identity() {
      lifted.push(p)
    }
  }
  PermGroup::new(m, lifted)
}

///|
/// 提升定理之機器證書：
/// (a) 每個提升像確為 L(G) 之自同構（Φ 之良定義性）；
/// (b) |Im Φ| · (孤立點數)! · 2^(K₂分量數) == |Aut(G)|（核之刻畫）；
/// (c) Φ 為群同態：提升後之複合 == 複合後之提升（以生成元抽驗）。
/// 回傳 (a, b, c)。
pub fn line_embed_cert(g : Graph) -> (Bool, Bool, Bool) {
  let lg = line_graph(g)
  let aut = automorphism_group(g)
  let img = aut_on_line(g)
  // (a)
  let mut a = true
  for p in img.generators() {
    if !is_automorphism(lg, p) {
      a = false
      break
    }
  }
  // (b)
  let kf = line_kernel_order(g)
  let b = img.order() * kf == aut.order()
  // (c) 同態性：Φ(σ∘τ) == Φ(σ)∘Φ(τ)
  let act = FinAction::on_edges(aut, g)
  let gs = aut.generators()
  let mut c = true
  if gs.length() >= 2 {
    let s = gs[0]
    let t = gs[1]
    let st = s.compose(t)
    let lhs = Perm::from_img(act.lift(st))
    let rhs = Perm::from_img(act.lift(s)).compose(Perm::from_img(act.lift(t)))
    c = lhs == rhs
  }
  (a, b, c)
}

///|
/// 是否為 K₃。
fn is_k3(g : Graph) -> Bool {
  g.order() == 3 && g.size() == 3
}

///|
/// 是否為 K₁,₃（爪）。
fn is_claw(g : Graph) -> Bool {
  guard g.order() == 4 && g.size() == 3 else { return false }
  let mut center = 0
  let mut found = false
  for v in 0..<4 {
    if g.degree(v) == 3 {
      center = v
      found = true
    }
  }
  guard found else { return false }
  for u in 0..<4 {
    for v in (u + 1)..<4 {
      if u != center && v != center && g.has_edge(u, v) {
        return false
      }
    }
  }
  true
}

///|
/// Whitney 例外對 {K₃, K₁,₃}：線圖同構但原圖不同構。
pub fn whitney_exception(g1 : Graph, g2 : Graph) -> Bool {
  (is_k3(g1) && is_claw(g2)) || (is_claw(g1) && is_k3(g2))
}

///|
/// 線圖判定是否適用 Whitney 定理：兩圖皆連通、無孤立點、非例外對。
pub fn whitney_applies(g1 : Graph, g2 : Graph) -> Bool {
  guard g1.order() >= 2 && g2.order() >= 2 else { return false }
  guard g1.components().length() == 1 && g2.components().length() == 1 else {
    return false
  }
  guard isolated_count(g1) == 0 && isolated_count(g2) == 0 else { return false }
  !whitney_exception(g1, g2)
}

///|
/// 衍生同構判定（Whitney）：連通無孤立點時 G ≅ H ⇔ L(G) ≅ L(H)。
/// 例外對 {K₃,K₁,₃} 直接判否（其線圖同構但原圖不同構）。
/// 不適用時退回引擎判定。
pub fn isomorphic_line(g1 : Graph, g2 : Graph) -> Bool {
  if whitney_exception(g1, g2) {
    return false
  }
  if whitney_applies(g1, g2) {
    return isomorphic(line_graph(g1), line_graph(g2))
  }
  isomorphic(g1, g2)
}

///|
/// 星團回提：由 ψ : L(G) → L(H) 重建頂點同構 σ : G → H。
/// 條件：S_v 之像必為某 S_w；所得 σ 需為雙射且逐邊驗證。失敗回 None。
pub fn isomorphism_via_line(g1 : Graph, g2 : Graph) -> Perm? {
  guard g1.order() == g2.order() && g1.size() == g2.size() else { return None }
  let n = g1.order()
  guard whitney_applies(g1, g2) else { return None }
  let phi = match isomorphism(line_graph(g1), line_graph(g2)) {
    Some(p) => p
    None => return None
  }
  // H 之星團表
  let stars2 : Array[Array[Int32]] = []
  for w in 0..<g2.order() {
    let s = star_of(g2, w)
    s.sort()
    stars2.push(s)
  }
  let img = Array::make(n, -1)
  let used = Array::make(n, false)
  for v in 0..<n {
    let sv = star_of(g1, v)
    let tv : Array[Int32] = []
    for i in sv {
      tv.push(phi.apply(i))
    }
    tv.sort()
    // 尋找 w 使 S_w == tv
    let mut hit = -1
    for w in 0..<n {
      if !used[w] && cmp_arr(stars2[w], tv) == 0 {
        hit = w
        break
      }
    }
    guard hit >= 0 else { return None }
    img[v] = hit
    used[hit] = true
  }
  let sigma = Perm::from_img(img)
  // 證書：逐邊驗證
  for e in g1.edge_list() {
    let (u, v) = e
    guard g2.has_edge(sigma.apply(u), sigma.apply(v)) else { return None }
  }
  Some(sigma)
}

///|
/// Whitney 衍生演算法之機器證書（一對圖）：
/// (a) 若 ψ : L(G)→L(H) 存在，星團回提必成功且所得 σ 為真同構；
/// (b) 回提結果與引擎直接求得之同構一致（同構類層面：皆存在或皆不存在）；
/// (c) 線圖同構判定與原圖同構判定一致。
/// 回傳 (a, b, c)。
pub fn whitney_cert(g1 : Graph, g2 : Graph) -> (Bool, Bool, Bool) {
  guard whitney_applies(g1, g2) else { return (true, true, true) }
  let lifted = isomorphism_via_line(g1, g2)
  let direct = isomorphism(g1, g2)
  let line_iso = isomorphic(line_graph(g1), line_graph(g2))
  let a = match lifted {
    Some(_) => true
    None => !line_iso // 線圖不同構 ⇒ 無 ψ ⇒ 回提失敗是正確的
  }
  let mut got_lift = false
  match lifted {
    Some(_) => got_lift = true
    None => ()
  }
  let mut got_direct = false
  match direct {
    Some(_) => got_direct = true
    None => ()
  }
  let b = got_lift == got_direct
  let c = line_iso == got_direct
  (a, b, c)
}
