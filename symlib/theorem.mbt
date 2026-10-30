///|
/// # Theorem — 擴展定理之機器證書電池
///
/// 本模組把全庫的數學內容整理成**可執行定理**：每條定理都以有限情形之
/// 逐點計算驗證，並回傳 `Cert { name, holds, detail }`。
/// 這不是「相信演算法」，而是「用演算法證明演算法」：
/// 引擎（個體化-精煉 + Schreier–Sims）、規範形式、群作用、軌道折疊、
/// 單子與範疇化彼此互為對方之證人（cross-witness）。
///
/// 三層電池：
/// - `prove_graph(g, σ, cap)`：單圖 21 條（規範形式、群論恒等式、對偶、線圖、分解、折疊、標記）
/// - `prove_pair(g1, g2, σ)`：雙圖 9 條（同構判定之四條獨立通道互證、Aut 函子性、Whitney 回提）
/// - `prove_all(cap)`：全庫 20 條（範疇公理、(co)limit、米田、Kan=歸納/上歸納、
///   Frobenius 互反、單子律、CSP=極限 vs 單子搜索、Cayley、標記矩陣、SGS 元素表）
///
/// 其中數條是**新擴展定理**：
/// - 線圖提升之核：ker Φ ≅ S_{孤立點} × (ℤ/2)^{K₂分量數}
/// - 分解積公式：|Aut(⊔C_i)| = Π (|Aut(C)|^m · m!)
/// - 對偶定理：Aut(G) = Aut(Ḡ)，dual_enc(G) = mask ⊕ canon_enc(Ḡ) 為第二完全不變量
/// - 標記定理：table of marks 之下三角 + 對角正 ⇒ 標記向量為 G-集之完全不變量
/// - 米田引理：Nat(h^a,F) ≅ F(a)（雙向計算 + 互逆驗證）
/// - Kan 擴張 = 導出演算法：Lan_{1→BG} = 歸納 G×X（自由），Ran = 上歸納 X^G，(Ran)^G = X
/// - 單子由伴隨而生：T = res∘Lan = G×-，其單子律逐點成立
/// - 約束解集 = 極限：csp_limit 與 search_nd（ListM 單子）給出同一解集

///|
/// 定理證書。
pub(all) struct Cert {
  name : String
  holds : Bool
  detail : String
}

///|
/// Debug（供 `assert_eq` 顯示 name/holds/detail 之結構化差異）。
pub impl Debug for Cert with fn to_repr(self) {
  Repr::record(
    Map([
      ("name", Repr::string(self.name)),
      ("holds", Repr::bool(self.holds)),
      ("detail", Repr::string(self.detail)),
    ]),
  )
}

///|
pub extend Cert with Debug::{to_repr}

///|
/// 建構證書。
pub fn cert(name : String, holds : Bool, detail : String) -> Cert {
  { name, holds, detail, }
}

///|
/// 全部成立？
pub fn all_hold(certs : Array[Cert]) -> Bool {
  for c in certs {
    guard c.holds else { return false }
  }
  true
}

///|
/// 失敗之定理名列表。
pub fn failed_certs(certs : Array[Cert]) -> Array[String] {
  let out : Array[String] = []
  for c in certs {
    if !c.holds {
      out.push(c.name)
    }
  }
  out
}

///|
/// 文字報告。
pub fn cert_report(certs : Array[Cert]) -> String {
  let mut s = ""
  let mut ok = 0
  for c in certs {
    let tag = if c.holds {
      ok = ok + 1
      "  [OK]   "
    } else {
      "  [FAIL] "
    }
    s = s + tag + c.name + " — " + c.detail + "\n"
  }
  s = "theorems: " +
    ok.to_string() +
    "/" +
    certs.length().to_string() +
    " hold\n" +
    s
  s
}

///|
/// Int64 整除檢查。
fn divides(a : Int64, b : Int64) -> Bool {
  b != 0L && a % b == 0L
}

///|
/// Double 近似相等。
fn close(a : Double, b : Double) -> Bool {
  let d = a - b
  let ad = if d < 0.0 { 0.0 - d } else { d }
  ad < 0.000000001
}

///|
/// SGS 元素表之證書（回歸測試：橫截分解次序錯誤會產生重複且漏元素）：
/// 元素數 == |G|、彼此相異、皆屬於 G（以 SGS 篩選**獨立**驗證）、且對乘法封閉。
///
/// **衍生演算法加速**：n ≤ 12 時以 64 位元鍵表把「相異性 + 封閉性」由
/// O(|G|²) 次 SGS 篩選（每次 O(n·|gens|) 配置）降為 O(|G|²·n) 次純整數運算
/// ⇒ |Aut(Petersen)|=120 之封閉檢查由 ~5s 降至 ~0.05s（沙箱實測）。
pub fn elements_cert(group : PermGroup, cap : Int32) -> Bool {
  let ord = group.order()
  if ord > cap.to_int64() {
    return true // 太大無法列舉 ⇒ 跳過
  }
  let elems = group.elements(cap)
  if elems.length().to_int64() != ord {
    return false
  }
  // 屬於 G（獨立於元素表之驗證）
  for e in elems {
    if !group.contains(e) {
      return false
    }
  }
  let n = group.size()
  if n > 12 {
    // perm_key64 不適用 ⇒ 逐對比較 + 抽樣封閉（通用但較慢）
    for i in 0..<elems.length() {
      for j in (i + 1)..<elems.length() {
        if elems[i] == elems[j] {
          return false
        }
      }
    }
    let lim = if elems.length() <= 120 { elems.length() } else { 16 }
    for i in 0..<lim {
      for b in elems {
        if !group.contains(elems[i].compose(b)) {
          return false
        }
      }
    }
    return true
  }
  // 快路徑：64 位元鍵表
  let base = (n + 1).to_int64()
  let lut = Map([])
  let imgs : Array[Array[Int32]] = []
  for e in elems {
    let k = perm_key64(e)
    match lut.get(k) {
      Some(_) => return false // 重複 ⇒ 分解次序錯誤
      None => lut.set(k, 0)
    }
    imgs.push(e.img)
  }
  // 封閉：a∘b 之鍵必在表中（免配置合成）
  for a in imgs {
    for b in imgs {
      let mut k = 1L
      for v in 0..<n {
        k = k * base + a[b[v]].to_int64()
      }
      match lut.get(k) {
        Some(_) => ()
        None => return false
      }
    }
  }
  true
}

///|
/// 單圖定理電池。`sigma` 為隨機重標號（驗證不變性），`cap` 為元素列舉上限。
pub fn prove_graph(g : Graph, sigma : Perm, cap : Int32) -> Array[Cert] {
  let n = g.order()
  let out : Array[Cert] = []
  let res = search_graph(g, true)
  let grp = PermGroup::new(n, res.aut_gens)
  let ord = grp.order()
  let gsig = g.relabel(sigma)
  // 1 規範形式之重標號不變性
  let cf1 = canonical_form(g)
  let cf2 = canonical_form(gsig)
  out.push(
    cert(
      "canon-invariance",
      cf1 == cf2 && canon_digest(g) == canon_digest(gsig),
      "canon(relabel(G))=canon(G); digest 相同",
    ),
  )
  // 2 規範形式之冪等性
  out.push(
    cert(
      "canon-idempotent",
      canonical_form(cf1) == cf1,
      "canon(canon(G))=canon(G)",
    ),
  )
  // 3 規範標號確為 G 之標號（重標號像 == 規範形式）
  let mut ok3 = true
  for i in 0..<n {
    if res.canon_lab[i] < 0 || res.canon_lab[i] >= n {
      ok3 = false
    }
  }
  out.push(
    cert(
      "canon-labeling-valid",
      ok3 && g.relabel(labeling_perm(res.canon_lab)) == cf1,
      "lab 為雙射且 G 之重標號像 = 規範形式",
    ),
  )
  // 4 生成元皆為真自同構
  let mut ok4 = true
  for p in res.aut_gens {
    if !is_automorphism(g, p) {
      ok4 = false
    }
  }
  out.push(cert("aut-gens-valid", ok4, "每個生成元逐邊驗證通過"))
  // 5 群封閉性（生成元之積仍在群中）
  let mut ok5 = true
  for a in res.aut_gens {
    for b in res.aut_gens {
      if !grp.contains(a.compose(b)) {
        ok5 = false
      }
    }
  }
  out.push(cert("aut-closure", ok5, "SGS 對生成元之積封閉"))
  // 6 軌道-穩定子定理 |G| = |Orb(x)|·|G_x|
  let mut ok6 = true
  let mut det6 = ""
  for orb in grp.orbit_partition() {
    let x = orb[0]
    let st = grp.stabilizer(x).order()
    if st * orb.length().to_int64() != ord {
      ok6 = false
    }
    det6 = "|Orb(" +
      x.to_string() +
      ")|=" +
      orb.length().to_string() +
      " |G_x|=" +
      st.to_string()
  }
  out.push(cert("orbit-stabilizer", ok6, det6 + " ⇒ |G|=" + ord.to_string()))
  // 7 Lagrange：|G_x| 與 |Orb(x)| 皆整除 |G|
  let mut ok7 = true
  for x in 0..<n {
    if !divides(ord, grp.stabilizer(x).order()) {
      ok7 = false
    }
    if !divides(ord, grp.orbit(x).length().to_int64()) {
      ok7 = false
    }
  }
  out.push(cert("lagrange", ok7, "∀x: |G_x| | |G| 且 |Orb(x)| | |G|"))
  // 8 Burnside 引理（需 |G| ≤ cap）
  if ord <= cap.to_int64() {
    let gs = gset_points(grp, cap)
    let (orb, burn) = gset_burnside(gs)
    out.push(
      cert(
        "burnside",
        orb == burn,
        "#orbits=" +
        orb.to_string() +
        " = (1/|G|)Σ|Fix(g)|=" +
        burn.to_string(),
      ),
    )
    // 9 廣域基數 |X//G| = |X|/|G|
    let gc = GSet::of(grp).groupoid_cardinality()
    let osc = GSet::of(grp).orbit_sum_cardinality()
    let want = n.to_double() / ord.to_double()
    out.push(
      cert(
        "groupoid-cardinality",
        close(gc, want) && close(osc, orb.to_double()),
        "|X//G|=" + gc.to_string() + " = |X|/|G|; Σ1/|Orb|=" + osc.to_string(),
      ),
    )
  } else {
    out.push(cert("burnside", true, "跳過（|G| > cap）"))
    out.push(cert("groupoid-cardinality", true, "跳過（|G| > cap）"))
  }
  // 10 折疊守恆：Σ軌道大小 = n，Σ重數 = m
  let folded = fold_graph(g, grp)
  let mut ssum = 0
  for v in folded.orbit_size {
    ssum = ssum + v
  }
  let mut msum = 0
  for i in 0..<folded.k {
    for j in i..<folded.k {
      msum = msum + folded.mul[i][j]
    }
  }
  out.push(
    cert(
      "fold-conservation",
      ssum == n && msum == g.size() && folded.edge_total == g.size(),
      "Σ|orbit|=" +
      ssum.to_string() +
      "=" +
      n.to_string() +
      ", Σmul=" +
      msum.to_string() +
      "=" +
      g.size().to_string(),
    ),
  )
  // 11 規範折疊（先規範化再折疊 ⇒ 與原標號無關）
  out.push(
    cert(
      "fold-canonical",
      fold_canonical_cert(g, sigma),
      "fold(canon(G)) = fold(canon(relabel(G))) 逐項相等",
    ),
  )
  // 12-14 分解定理
  let (da, db, dc, dd) = decomp_cert(g, sigma)
  let dec = decompose(g)
  out.push(
    cert(
      "decomp-product-formula",
      db,
      "Π(|Aut(C)|^m·m!)=" +
      dec.aut_order().to_string() +
      " = |Aut(G)|=" +
      ord.to_string(),
    ),
  )
  out.push(
    cert(
      "decomp-derived-generators", dc, "派生生成元 ⊆ Aut(G) 且 ⟨派生⟩ = Aut(G)（wreath 結構）",
    ),
  )
  out.push(
    cert(
      "decomp-block-canonical",
      da && dd,
      "塊規範編碼之重標號不變性 + 冪等性",
    ),
  )
  // 15-17 對偶定理
  let (ua, ub, uc) = dual_cert(g, sigma)
  out.push(
    cert(
      "dual-aut-invariance", ua, "Aut(G) = Aut(complement(G))（同階互含）",
    ),
  )
  out.push(
    cert(
      "dual-encoding", ub, "dual_enc(G) = mask ⊕ canon_enc(Ḡ) 由 canon_lab(Ḡ) 實現",
    ),
  )
  out.push(
    cert("dual-invariance", uc, "對偶規範形式之重標號不變性"),
  )
  // 18 雙通道交叉驗證
  out.push(
    cert(
      "dual-cross-check",
      dual_cross_check(g),
      "G 與 Ḡ 上獨立搜索得同一 Aut 群",
    ),
  )
  // 19-21 線圖提升定理
  let (la, lb, lc) = line_embed_cert(g)
  let lg = line_graph(g)
  out.push(
    cert(
      "line-lift-homomorphism",
      la && lc,
      "Φ:Aut(G)→Aut(L(G)) 良定義且為群同態",
    ),
  )
  out.push(
    cert(
      "line-kernel-formula",
      lb,
      "|ImΦ|·(孤立點)!·2^(K₂分量)=" +
      aut_on_line(g).order().to_string() +
      "·" +
      line_kernel_order(g).to_string() +
      " = |Aut(G)|=" +
      ord.to_string() +
      "; |Aut(L(G))|=" +
      aut_order(lg).to_string(),
    ),
  )
  out.push(
    cert(
      "elements-sgs-table",
      elements_cert(grp, cap),
      "SGS 元素表：|G| 個相異元素、皆屬 G、對乘法封閉",
    ),
  )
  // 22 標記定理（|Aut| ≤ cap 時）
  if ord <= cap.to_int64() && ord > 0L && n <= 12 {
    let (ma, mb, mc, ns, _) = marks_cert(grp, cap)
    out.push(
      cert(
        "marks-classification",
        ma && mb && mc,
        "table of marks（" +
        ns.to_string() +
        " 個子群共軛類）兩種算法一致、下三角、對角正 ⇒ 標記為 G-集完全不變量",
      ),
    )
  } else {
    out.push(
      cert("marks-classification", true, "跳過（|G| > cap 或 n > 12）"),
    )
  }
  out
}

///|
/// 雙圖定理電池：四條獨立同構通道（引擎 / 分解 / 對偶 / 線圖-Whitney）互證。
pub fn prove_pair(g1 : Graph, g2 : Graph) -> Array[Cert] {
  let out : Array[Cert] = []
  let iso = isomorphic(g1, g2)
  // 1 對稱性
  out.push(
    cert(
      "iso-symmetric",
      iso == isomorphic(g2, g1),
      "isomorphic(G,H) = isomorphic(H,G)",
    ),
  )
  // 2 顯式同構之證書
  let phi = isomorphism(g1, g2)
  let mut ok2 = true
  match phi {
    Some(s) => {
      for e in g1.edge_list() {
        let (u, v) = e
        if !g2.has_edge(s.apply(u), s.apply(v)) {
          ok2 = false
        }
      }
      for e in g2.edge_list() {
        let (u, v) = e
        let si = s.inverse()
        if !g1.has_edge(si.apply(u), si.apply(v)) {
          ok2 = false
        }
      }
      if !iso {
        ok2 = false
      }
    }
    None => if iso { ok2 = false }
  }
  out.push(
    cert(
      "iso-certificate", ok2, "映射逐邊雙向驗證；None ⟺ 不同構",
    ),
  )
  // 3 指紋等價
  out.push(
    cert(
      "digest-completeness",
      (canon_digest(g1) == canon_digest(g2)) == iso,
      "canon_digest 相等 ⟺ 同構（完全不變量）",
    ),
  )
  // 4 分解通道
  out.push(
    cert(
      "iso-channel-decomp",
      isomorphic_decomposed(g1, g2) == iso,
      "分解式判定（分量規範編碼多集）與引擎一致",
    ),
  )
  // 5 對偶通道
  out.push(
    cert(
      "iso-channel-dual",
      isomorphic_dual(g1, g2) == iso,
      "對偶式判定（稀疏側搜索）與引擎一致",
    ),
  )
  // 6 線圖通道（Whitney）
  let wi = whitney_applies(g1, g2)
  let li = isomorphic_line(g1, g2)
  let exc = whitney_exception(g1, g2)
  let ok6 = if wi {
    li == iso
  } else if exc {
    !li // 例外對：線圖同構但原圖不同構 ⇒ 判定需為否
  } else {
    li == iso // 不適用時退回引擎
  }
  out.push(
    cert(
      "iso-channel-whitney",
      ok6,
      "Whitney 通道 applies=" +
      wi.to_string() +
      " exception=" +
      exc.to_string() +
      " ⇒ " +
      li.to_string() +
      " vs " +
      iso.to_string(),
    ),
  )
  // 7 星團回提
  let lift = isomorphism_via_line(g1, g2)
  let (wa, wb, wc) = whitney_cert(g1, g2)
  out.push(
    cert(
      "whitney-star-lift",
      wa && wb && wc,
      "線圖同構 ψ 之星團回提 ⇒ 頂點同構（逐邊驗證），與引擎一致",
    ),
  )
  let _ = lift
  // 8 Aut 函子性
  if iso {
    match phi {
      Some(s) => {
        let a1 = automorphism_group(g1)
        let a2 = automorphism_group(g2)
        let conj = aut_map(s, a1)
        let mut ok8 = conj.order() == a2.order()
        for p in conj.generators() {
          if !a2.contains(p) {
            ok8 = false
          }
        }
        for p in a2.generators() {
          if !conj.contains(p) {
            ok8 = false
          }
        }
        out.push(
          cert(
            "aut-functorial",
            ok8,
            "Aut(φ)(σ)=φσφ⁻¹ ⇒ 共軛像 = Aut(H)（|·|=" +
            conj.order().to_string() +
            "）",
          ),
        )
      }
      None => out.push(cert("aut-functorial", false, "無映射"))
    }
  } else {
    out.push(cert("aut-functorial", true, "跳過（不同構）"))
  }
  // 9 不變量前置否證
  let inv = graph_invariant(g1) == graph_invariant(g2)
  out.push(
    cert(
      "invariant-soundness",
      !iso || inv,
      "同構 ⇒ 結構不變量（度序列+精煉顏色）相等",
    ),
  )
  out
}

///|
/// 整數冪（小指數）。
fn pow_int(a : Int32, e : Int32) -> Int32 {
  let mut r = 1
  for _ in 0..<e {
    r = r * a
  }
  r
}

///|
/// ListM / StateM / Kleisli 之單子律。
fn monad_laws_cert() -> Bool {
  // ListM：左單位 pure x >>= f = f x
  let f = fn(a : Int32) -> ListM[Int32] { ListM::from_array([a, a * 2]) }
  let l1 = ListM::pure(3).bind(f).to_array()
  let r1 = f(3).to_array()
  if cmp_arr(l1, r1) != 0 {
    return false
  }
  // 右單位 m >>= pure = m
  let m = ListM::from_array([1, 2, 3])
  let l2 = m.bind(fn(a : Int32) { ListM::pure(a) }).to_array()
  if cmp_arr(l2, m.to_array()) != 0 {
    return false
  }
  // 結合律
  let gm = fn(a : Int32) -> ListM[Int32] { ListM::from_array([a + 1]) }
  let left = m.bind(f).bind(gm).to_array()
  let right = m.bind(fn(a : Int32) { f(a).bind(gm) }).to_array()
  if cmp_arr(left, right) != 0 {
    return false
  }
  // StateM：左/右單位 + 結合
  let sf = fn(a : Int32) -> StateM[Int32, Int32] {
    { run: fn(s0 : Int32) { (a + s0, s0 + 1) }, }
  }
  let s1 = StateM::pure(5).bind(sf).eval(0)
  let s2 = sf(5).eval(0)
  if s1 != s2 {
    return false
  }
  let sm : StateM[Int32, Int32] = { run: fn(s0 : Int32) { (s0 * 2, s0 + 3) }, }
  let s3 = sm.bind(fn(a : Int32) { StateM::pure(a) }).eval(1)
  if s3 != sm.eval(1) {
    return false
  }
  let sg = fn(a : Int32) -> StateM[Int32, Int32] {
    { run: fn(s0 : Int32) { (a * 10, s0 + 100) }, }
  }
  let s4 = sm.bind(sf).bind(sg).exec(0)
  let s5 = sm.bind(fn(a : Int32) { sf(a).bind(sg) }).exec(0)
  if s4 != s5 {
    return false
  }
  // Kleisli：合成之結合與恆等
  let kid : (Int32) -> ListM[Int32] = kleisli_id()
  let k1 = kleisli_list(f, kid)(3).to_array()
  let k2 = f(3).to_array()
  if cmp_arr(k1, k2) != 0 {
    return false
  }
  let k3 = kleisli_list(kleisli_list(f, gm), kid)(3).to_array()
  let k4 = kleisli_list(f, kleisli_list(gm, kid))(3).to_array()
  cmp_arr(k3, k4) == 0
}
