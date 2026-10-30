///|
/// # FinCat — 有限範疇、圖（diagram）、極限與餘極限
///
/// 範疇化之第一層機器：把「對象/態射/恆等/複合」編碼為有限表格，
/// 於是範疇公理、(co)limit 之泛性質都能**窮舉驗證**（`is_category`、`is_functor`、
/// `limit`/`colimit` 與暴力計數對照）。
///
/// - `FinCat`：nobj / nmor / dom / cod / id / comp（複合表）
/// - 建構子：`cat_thin` / `cat_discrete` / `cat_terminal` / `cat_arrow` / `cat_cospan` /
///   `cat_span` / `cat_poset`（傳遞閉包）/ `cat_parallel` / `cat_group`（**BG**：單對象範疇，
///   態射 = 群元素）
/// - `FinDiagram`：圖 = 對象像 + 態射像（`img` 以**態射**為索引，含全部恆等態射 ⇒
///   建構時必須提供 `id_map(n)` 之恆等像）
/// - 極限：`limit` / `limit_card`（錐之窮舉）、`equalizer_set`、`pullback_set`、`product_set`
/// - 餘極限：`colimit` / `colimit_card`（union-find 餘等化子）、`coequalizer_card`、
///   `pushout_card`（需 **span**：共同定義域）、`coproduct_card`
/// - 便利圖：`arrow_diagram`（limit = A、colimit = B）、`parallel_diagram`、
///   `cospan_diagram`、`span_diagram`
///
/// 相關檔案：`yoneda.mbt`（預層 / 米田 / comma / Kan 擴張 / 歸納與上歸納）、
/// `csp.mbt`（約束滿足 = 極限）、`gset.mbt`（G-集 / 標記 / Cayley）。

///|
/// 有限範疇：態射以索引表示，`comp[f*nmor+g] = f ∘ g`（先 g 後 f），不可複合為 -1。
pub(all) struct FinCat {
  nobj : Int32
  nmor : Int32
  dom : Array[Int32]
  cod : Array[Int32]
  id : Array[Int32]
  comp : Array[Int32]
}

///|
/// 範疇公理之機器驗證：恆等律 + 結合律（窮舉所有可複合三元組）。
pub fn is_category(c : FinCat) -> Bool {
  guard c.id.length() == c.nobj && c.comp.length() == c.nmor * c.nmor else {
    return false
  }
  for a in 0..<c.nobj {
    let ia = c.id[a]
    guard c.dom[ia] == a && c.cod[ia] == a else { return false }
  }
  for f in 0..<c.nmor {
    // 恆等律
    let ia = c.id[c.dom[f]]
    let ib = c.id[c.cod[f]]
    guard c.comp[f * c.nmor + ia] == f else { return false }
    guard c.comp[ib * c.nmor + f] == f else { return false }
  }
  // 結合律
  for f in 0..<c.nmor {
    for g in 0..<c.nmor {
      let fg = c.comp[f * c.nmor + g]
      if fg < 0 {
        continue
      }
      for h in 0..<c.nmor {
        let gh = c.comp[g * c.nmor + h]
        if gh < 0 {
          continue
        }
        let l = c.comp[fg * c.nmor + h]
        let r = c.comp[f * c.nmor + gh]
        guard l == r && l >= 0 else { return false }
      }
    }
  }
  true
}

///|
/// 薄範疇（每個 (dom,cod) 至多一個態射）：偏序、箭頭、span/cospan、離散皆屬之。
pub fn cat_thin(nobj : Int32, arrows : Array[(Int32, Int32)]) -> FinCat {
  let idx = Map([])
  let dom : Array[Int32] = []
  let cod : Array[Int32] = []
  fn add(a : Int32, b : Int32) -> Unit {
    let key = a * nobj + b
    match idx.get(key) {
      Some(_) => ()
      None => {
        idx.set(key, dom.length())
        dom.push(a)
        cod.push(b)
      }
    }
  }
  for a in 0..<nobj {
    add(a, a)
  }
  for ar in arrows {
    let (a, b) = ar
    guard a >= 0 && a < nobj && b >= 0 && b < nobj else {
      abort("cat_thin: object out of range")
    }
    add(a, b)
  }
  let nmor = dom.length()
  let id = Array::make(nobj, 0)
  for a in 0..<nobj {
    id[a] = idx.get(a * nobj + a).unwrap()
  }
  let comp = Array::make(nmor * nmor, -1)
  for f in 0..<nmor {
    for g in 0..<nmor {
      if cod[g] == dom[f] {
        comp[f * nmor + g] = idx.get(dom[g] * nobj + cod[f]).unwrap()
      }
    }
  }
  { nobj, nmor, dom, cod, id, comp, }
}

///|
/// 離散範疇（只有恆等態射）。
pub fn cat_discrete(nobj : Int32) -> FinCat {
  cat_thin(nobj, [])
}

///|
/// 終端範疇 1。
pub fn cat_terminal() -> FinCat {
  cat_thin(1, [])
}

///|
/// 走動箭頭 (0 → 1)。
pub fn cat_arrow() -> FinCat {
  cat_thin(2, [(0, 1)])
}

///|
/// 共 span (0 → 2 ← 1)：拉回之索引範疇。
pub fn cat_cospan() -> FinCat {
  cat_thin(3, [(0, 2), (1, 2)])
}

///|
/// span (0 ← 2 → 1)：推出之索引範疇。
pub fn cat_span() -> FinCat {
  cat_thin(3, [(2, 0), (2, 1)])
}

///|
/// 偏序範疇：`le` 為 (a,b) 對之列表（表示 a ≤ b），自動加入自反與傳遞閉包。
pub fn cat_poset(nobj : Int32, le : Array[(Int32, Int32)]) -> FinCat {
  let reach = Array::make(nobj * nobj, false)
  for a in 0..<nobj {
    reach[a * nobj + a] = true
  }
  for p in le {
    let (a, b) = p
    reach[a * nobj + b] = true
  }
  // 傳遞閉包（Floyd–Warshall）
  for k in 0..<nobj {
    for a in 0..<nobj {
      for b in 0..<nobj {
        if reach[a * nobj + k] && reach[k * nobj + b] {
          reach[a * nobj + b] = true
        }
      }
    }
  }
  let arrows : Array[(Int32, Int32)] = []
  for a in 0..<nobj {
    for b in 0..<nobj {
      if a != b && reach[a * nobj + b] {
        arrows.push((a, b))
      }
    }
  }
  cat_thin(nobj, arrows)
}

///|
/// 平行對範疇 (0 ⇉ 1)：等化子／餘等化子之索引範疇（非薄範疇）。
pub fn cat_parallel() -> FinCat {
  let nobj = 2
  let dom = [0, 1, 0, 0]
  let cod = [0, 1, 1, 1]
  let nmor = 4
  let id = [0, 1]
  let comp = Array::make(nmor * nmor, -1)
  for f in 0..<nmor {
    for g in 0..<nmor {
      if cod[g] == dom[f] {
        let r = if g == id[dom[g]] {
          f
        } else if f == id[cod[f]] {
          g
        } else {
          -1 // 兩個非恆等態射不可複合
        }
        comp[f * nmor + g] = r
      }
    }
  }
  { nobj, nmor, dom, cod, id, comp, }
}

///|
/// 群之單對象範疇 BG：態射 = 群元素（列舉，上限 cap），複合 = 群乘法。
pub fn cat_group(group : PermGroup, cap : Int32) -> FinCat {
  let elems = group.elements(cap)
  let nmor = elems.length()
  let lut = Map([])
  for i, e in elems {
    lut.set(perm_key64(e), i)
  }
  let dom = Array::make(nmor, 0)
  let cod = Array::make(nmor, 0)
  let id = [0]
  let idp = Perm::identity(group.size())
  let idi = lut.get(perm_key64(idp)).unwrap()
  id[0] = idi
  let comp = Array::make(nmor * nmor, -1)
  for f in 0..<nmor {
    for g in 0..<nmor {
      let prod = elems[f].compose(elems[g])
      comp[f * nmor + g] = lut.get(perm_key64(prod)).unwrap()
    }
  }
  { nobj: 1, nmor, dom, cod, id, comp, }
}

///|
/// 有限集 valued 圖（函子 C → FinSet）：`size[a]` = F(a) 之基數，
/// `img[m]` = F(m) 之像陣列（長度 size[dom m]，值 < size[cod m]）。
pub(all) struct FinDiagram {
  cat : FinCat
  size : Array[Int32]
  img : Array[Array[Int32]]
}

///|
/// 建構圖（驗證型別正確性）。
pub fn diagram_new(
  cat : FinCat,
  size : Array[Int32],
  img : Array[Array[Int32]],
) -> FinDiagram {
  guard size.length() == cat.nobj else { abort("diagram_new: object count") }
  guard img.length() == cat.nmor else { abort("diagram_new: morphism count") }
  for m in 0..<cat.nmor {
    guard img[m].length() == size[cat.dom[m]] else {
      abort("diagram_new: image length")
    }
    for x in img[m] {
      guard x >= 0 && x < size[cat.cod[m]] else {
        abort("diagram_new: image range")
      }
    }
  }
  { cat, size, img, }
}

///|
/// 函子性驗證：保持恆等與複合。
pub fn is_functor(d : FinDiagram) -> Bool {
  let c = d.cat
  for a in 0..<c.nobj {
    let m = c.id[a]
    for x in 0..<d.size[a] {
      guard d.img[m][x] == x else { return false }
    }
  }
  for f in 0..<c.nmor {
    for g in 0..<c.nmor {
      let fg = c.comp[f * c.nmor + g]
      if fg < 0 {
        continue
      }
      for x in 0..<d.size[c.dom[g]] {
        let lhs = d.img[fg][x]
        let rhs = d.img[f][d.img[g][x]]
        guard lhs == rhs else { return false }
      }
    }
  }
  true
}

///|
/// 圖之總規模 Π size[a]（溢位回 -1）。
fn diagram_volume(d : FinDiagram) -> Int32 {
  let mut v = 1
  for s in d.size {
    if s == 0 {
      return 0
    }
    if v > 100000000 / s {
      return -1
    }
    v = v * s
  }
  v
}

///|
/// 極限 = 相容錐之集合：{ (x_a) ∈ Π F(a) : ∀m:a→b, F(m)(x_a) = x_b }。
/// 以 DFS 逐對象賦值並在可判定時立即剪枝（約束傳播）。cap 為錐數上限。
pub fn limit(d : FinDiagram, cap : Int32) -> Array[Array[Int32]] {
  let c = d.cat
  let vol = diagram_volume(d)
  guard vol >= 0 && vol <= cap else { abort("limit: diagram too large") }
  let out : Array[Array[Int32]] = []
  let cur = Array::make(c.nobj, -1)
  fn rec(a : Int32) -> Unit {
    if a == c.nobj {
      out.push(cur.copy())
      guard out.length() <= cap else { abort("limit: too many cones") }
      return
    }
    for x in 0..<d.size[a] {
      cur[a] = x
      // 剪枝：所有兩端皆已賦值之態射需相容
      let mut ok = true
      for m in 0..<c.nmor {
        let u = c.dom[m]
        let v = c.cod[m]
        if cur[u] >= 0 && cur[v] >= 0 {
          if d.img[m][cur[u]] != cur[v] {
            ok = false
            break
          }
        }
      }
      if ok {
        rec(a + 1)
      }
    }
    cur[a] = -1
  }
  rec(0)
  out
}

///|
/// 極限之基數。
pub fn limit_card(d : FinDiagram, cap : Int32) -> Int32 {
  limit(d, cap).length()
}

///|
/// 餘極限 = 不交併 Σ F(a) 模「x ~ F(m)(x)」之商集。
/// 回傳 (class_of, nclass)：class_of 以不交併索引（offset[a] + x）給出規範類號
///（類號依首次出現順序規範化 ⇒ 決定性）。
pub fn colimit(d : FinDiagram) -> (Array[Int32], Int32) {
  let c = d.cat
  let offset = Array::make(c.nobj, 0)
  let mut tot = 0
  for a in 0..<c.nobj {
    offset[a] = tot
    tot = tot + d.size[a]
  }
  let parent = Array::make(tot, 0)
  for i in 0..<tot {
    parent[i] = i
  }
  fn find(x : Int32) -> Int32 {
    let mut r = x
    while parent[r] != r {
      r = parent[r]
    }
    // 路徑壓縮
    let mut y = x
    while parent[y] != y {
      let nx = parent[y]
      parent[y] = r
      y = nx
    }
    r
  }
  for m in 0..<c.nmor {
    let u = c.dom[m]
    let v = c.cod[m]
    for x in 0..<d.size[u] {
      let a = find(offset[u] + x)
      let b = find(offset[v] + d.img[m][x])
      if a != b {
        parent[b] = a
      }
    }
  }
  // 規範化類號（依首次出現）
  let class_of = Array::make(tot, -1)
  let lut = Map([])
  let mut nc = 0
  for i in 0..<tot {
    let r = find(i)
    match lut.get(r) {
      Some(v) => class_of[i] = v
      None => {
        lut.set(r, nc)
        class_of[i] = nc
        nc = nc + 1
      }
    }
  }
  (class_of, nc)
}

///|
/// 餘極限之基數。
pub fn colimit_card(d : FinDiagram) -> Int32 {
  colimit(d).1
}

///|
/// 恆等函數之像陣列（建構 (co)limit 圖時需要恆等態射之像）。
pub fn id_map(n : Int32) -> Array[Int32] {
  let a = Array::make(n, 0)
  for i in 0..<n {
    a[i] = i
  }
  a
}

///|
/// 平行對之圖（等化子／餘等化子用）：態射序 = [id_A, id_B, f, g]。
fn parallel_diagram(f : FinMap, g : FinMap) -> FinDiagram {
  guard f.dom == g.dom && f.cod == g.cod else {
    abort("parallel_diagram: shape mismatch")
  }
  diagram_new(cat_parallel(), [f.dom, f.cod], [
    id_map(f.dom),
    id_map(f.cod),
    f.img,
    g.img,
  ])
}

///|
/// 等化子 eq(f,g) = { x : f(x) = g(x) }（極限之導出演算法）。
pub fn equalizer_set(f : FinMap, g : FinMap) -> Array[Int32] {
  let d = parallel_diagram(f, g)
  let cones = limit(d, 1000000)
  let out : Array[Int32] = []
  for c in cones {
    out.push(c[0])
  }
  out
}

///|
/// 餘等化子 coeq(f,g) 之基數（餘極限）。
pub fn coequalizer_card(f : FinMap, g : FinMap) -> Int32 {
  colimit_card(parallel_diagram(f, g))
}

///|
/// 共 span 之圖（拉回用）：f : A → C，g : B → C。
fn cospan_diagram(f : FinMap, g : FinMap) -> FinDiagram {
  guard f.cod == g.cod else { abort("cospan_diagram: shape mismatch") }
  diagram_new(cat_cospan(), [f.dom, g.dom, f.cod], [
    id_map(f.dom),
    id_map(g.dom),
    id_map(f.cod),
    f.img,
    g.img,
  ])
}

///|
/// 拉回 pb(f,g) = { (x,y) : f(x) = g(y) }（纖維積）。
pub fn pullback_set(f : FinMap, g : FinMap) -> Array[(Int32, Int32)] {
  let d = cospan_diagram(f, g)
  let cones = limit(d, 1000000)
  let out : Array[(Int32, Int32)] = []
  for c in cones {
    out.push((c[0], c[1]))
  }
  out
}

///|
/// span 之圖（推出用）：f : C → A，g : C → B。
fn span_diagram(f : FinMap, g : FinMap) -> FinDiagram {
  guard f.dom == g.dom else { abort("span_diagram: shape mismatch") }
  diagram_new(cat_span(), [f.cod, g.cod, f.dom], [
    id_map(f.cod),
    id_map(g.cod),
    id_map(f.dom),
    f.img,
    g.img,
  ])
}

///|
/// 推出 po(f,g) 之基數。
pub fn pushout_card(f : FinMap, g : FinMap) -> Int32 {
  colimit_card(span_diagram(f, g))
}

///|
/// 積 A × B（離散圖之極限）。
pub fn product_set(a : Int32, b : Int32) -> Array[(Int32, Int32)] {
  let d = diagram_new(cat_discrete(2), [a, b], [id_map(a), id_map(b)])
  let out : Array[(Int32, Int32)] = []
  for c in limit(d, 1000000) {
    out.push((c[0], c[1]))
  }
  out
}

///|
/// 餘積 A ⊔ B（離散圖之餘極限）。
pub fn coproduct_card(a : Int32, b : Int32) -> Int32 {
  colimit_card(diagram_new(cat_discrete(2), [a, b], [id_map(a), id_map(b)]))
}

///|
/// 箭頭圖 (f : A → B) 之極限 = A（圖形之「全域截面」）、餘極限 = B。
pub fn arrow_diagram(f : FinMap) -> FinDiagram {
  diagram_new(cat_arrow(), [f.dom, f.cod], [id_map(f.dom), id_map(f.cod), f.img])
}
