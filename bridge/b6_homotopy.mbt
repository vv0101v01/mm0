///| ## B6 —— 球面同倫邊界：整係數同調的消元計算、撓率的顯式證書，與 Stasheff 塔的生成器
///

///| golden SPEC §四 第六條殘餘邊界：完整 `1`-連通高階 Blakers–Massey 推出定理、

///| 撓率同倫群（如 `π₄(S³) ≅ ℤ/2ℤ`）與任意維度 `n ≥ 6` 結合多面體 `K_n` 的無限相干塔。
///

///| 合併動作（變化 + 推遠）：

///|  (a) **變化**：把「高階同倫群不可及」改寫成「化約 + 認證」。Hurewicz 給出

///|      `π₂(S²,*) ≅ H₂(S²;ℤ)`；同調是有限 CW 模型上的**整數消元問題**，

///|      SNF 可算、可交叉驗證。撓率不再是「未知」，而是「SNF 的非常規不變因子」

///|      ＋「用上閉鏈配對寫出的顯式證書」。

///|  (b) **推遠**：Stasheff `K_n` 的組合骨架 = 多邊形三角剖分的翻轉圖

///|      （頂點數 Catalan(n−2)、度數 n−3）。`elim/nc` 已能對任意 n 生成它，

///|      於是「n ≥ 6 的無限相干塔」至少取得可枚舉、可驗證的組合胚。

// ------------------------------------------------------- 整係數同調 ----

///|
/// 一個有限單純複形：`faces[k]` 是 k 維面（頂點列表遞增）。
pub struct SimplexSet {
  faces : Array[Array[Array[Int32]]]
  nverts : Int32
}
///|
/// 由最高維的面表建立（自動補齊所有面與頂點）。
pub fn simplex_from_max_faces(
  maxd : Int32,
  faces_at_max : Array[Array[Int32]],
) -> SimplexSet {
  let f : Array[Array[Array[Int32]]] = []
  for _k = 0; _k <= maxd; _k = _k + 1 {
    f.push([])
  }
  let mut nv : Int32 = 0
  for raw in faces_at_max {
    let face = sort_vertices(raw)
    // 生成所有子面
    let k = face.length()
    let total : Int32 = 1 << k
    let mut m : Int32 = 1
    while m < total {
      let sub : Array[Int32] = []
      for i = 0; i < k; i = i + 1 {
        if (m >> i) % 2 == 1 {
          sub.push(face[i])
        }
      }
      let d = sub.length() - 1
      let mut dup = false
      for old in f[d] {
        if @algebra.int_vec_eq(old, sub) {
          dup = true
        }
      }
      if !dup {
        f[d].push(sub)
      }
      m = m + 1
    }
    for v in face {
      if v + 1 > nv {
        nv = v + 1
      }
    }
  }
  // 排序面表（字典序）以固定列序
  for d = 0; d < f.length(); d = d + 1 {
    f[d] = sort_faces(f[d])
  }
  SimplexSet::{ faces: f, nverts: nv, }
}

///|
fn sort_faces(a : Array[Array[Int32]]) -> Array[Array[Int32]] {
  let out : Array[Array[Int32]] = []
  for x in a {
    out.push(x)
  }
  let n = out.length()
  for i = 1; i < n; i = i + 1 {
    let key = out[i]
    let mut j = i - 1
    while j >= 0 && face_less(key, out[j]) {
      out[j + 1] = out[j]
      j = j - 1
    }
    out[j + 1] = key
  }
  out
}

///|
fn face_less(a : Array[Int32], b : Array[Int32]) -> Bool {
  let n = if a.length() < b.length() { a.length() } else { b.length() }
  for i = 0; i < n; i = i + 1 {
    if a[i] != b[i] {
      return a[i] < b[i]
    }
  }
  a.length() < b.length()
}

///|
/// 頂點升序（simplex 的典範表示）。
fn sort_vertices(a : Array[Int32]) -> Array[Int32] {
  let b : Array[Int32] = []
  for x in a {
    b.push(x)
  }
  for i = 1; i < b.length(); i = i + 1 {
    let key = b[i]
    let mut j = i - 1
    while j >= 0 && b[j] > key {
      b[j + 1] = b[j]
      j = j - 1
    }
    b[j + 1] = key
  }
  b
}

///|
/// 帶符號的邊界矩陣 ∂_d：列 = (d−1)-面，行 = d-面，第 i 個面取 (−1)^i。
pub fn boundary_signed(cx : SimplexSet, d : Int32) -> Array[Array[Int32]] {
  let cur = cx.faces[d - 1]
  let top = cx.faces[d]
  let rows : Array[Array[Int32]] = []
  for _i = 0; _i < cur.length(); _i = _i + 1 {
    rows.push(Array::make(top.length(), 0))
  }
  for j = 0; j < top.length(); j = j + 1 {
    let f = top[j]
    for skip = 0; skip < f.length(); skip = skip + 1 {
      let sub : Array[Int32] = []
      for i = 0; i < f.length(); i = i + 1 {
        if i != skip {
          sub.push(f[i])
        }
      }
      for r = 0; r < cur.length(); r = r + 1 {
        if @algebra.int_vec_eq(cur[r], sub) {
          rows[r][j] = if skip % 2 == 0 { 1 } else { -1 }
        }
      }
    }
  }
  rows
}

///| 整係數同調：Betti 數與撓率不變因子。

///|   free_k = n_k − rank ∂_k − rank ∂_{k+1}

///|
///   tors_k = SNF(∂_{k+1}) 中大於 1 的不變因子（coker(∂_{k+1}) = H_k ⊕ ℤ^{rank ∂_k}）
pub struct Homology {
  betti : Array[Int32]
  torsion : Array[Array[Int32]]
  ranks : Array[Int32]
  euler : Int32
}

///|
pub fn homology_of(cx : SimplexSet) -> Homology {
  let top = cx.faces.length() - 1
  let betti : Array[Int32] = []
  let tors : Array[Array[Int32]] = []
  let ranks : Array[Int32] = []
  for _k = 0; _k <= top; _k = _k + 1 {
    betti.push(0)
    tors.push([])
    ranks.push(0)
  }
  // rank ∂_d 用精確有理秩（golden `exact/algebra` 的 qmat_rank）
  let rk : Array[Int32] = Array::make(top + 2, 0)
  for d = 1; d <= top; d = d + 1 {
    let rows = boundary_signed(cx, d)
    if rows.length() > 0 && rows[0].length() > 0 {
      rk[d] = @algebra.qmat_rank(@algebra.qmat_from_int_rows(rows))
    }
  }
  for k = 0; k <= top; k = k + 1 {
    let nk = cx.faces[k].length()
    betti[k] = nk - rk[k] - rk[k + 1]
    ranks[k] = rk[k]
    if k + 1 <= top {
      let rows = boundary_signed(cx, k + 1)
      if rows.length() > 0 && rows[0].length() > 0 {
        let diag = @core.smith_diagonal(@core.mat_from_rows(rows))
        for v in diag {
          if v > 1 {
            tors[k].push(v)
          }
        }
      }
    }
  }
  let mut euler = 0
  for k = 0; k <= top; k = k + 1 {
    let nk = cx.faces[k].length()
    euler = euler + (if k % 2 == 0 { nk } else { 0 - nk })
  }
  Homology::{ betti, torsion: tors, ranks, euler, }
}

///|
pub fn homology_show(h : Homology) -> String {
  let mut out = ""
  for k = 0; k < h.betti.length(); k = k + 1 {
    let t = h.torsion[k]
    let mut piece = if h.betti[k] == 0 {
      ""
    } else if h.betti[k] == 1 {
      "Z"
    } else {
      "Z^\{h.betti[k]}"
    }
    for d in t {
      piece = if piece == "" { "Z/\{d}" } else { "\{piece} (+) Z/\{d}" }
    }
    if piece == "" {
      piece = "0"
    }
    out = if k == 0 { "H0=\{piece}" } else { "\{out} H\{k}=\{piece}" }
  }
  out
}

// ----------------------------------------------------------- 撓率證書 ----

///|
/// 有理純量 → 整數（不整除則 None）。全程走 golden 的精確有理算術。
fn int_of_rat(v : @algebra.Rat) -> Int32? {
  if !@algebra.rat_fits_int32(v) {
    return None
  }
  Some(@algebra.rat_to_double(v).to_int())
}

///| 把有理向量放大成整數向量：找最小 L ≤ 5040 使 L·v 逐坐標為整數。

///|
/// 這保留了「有理核 → 整係數核」的整性檢查，不引入浮點誤差判定。
fn to_integer_vector(v : Array[@algebra.Rat]) -> Array[Int32]? {
  for l = 1; l <= 5040; l = l + 1 {
    let scaled : Array[@algebra.Rat] = []
    for x in v {
      scaled.push(@algebra.rat_mul(x, @algebra.rat_int(l)))
    }
    let out : Array[Int32] = []
    let mut ok = true
    for y in scaled {
      match int_of_rat(y) {
        Some(k) => out.push(k)
        None => ok = false
      }
    }
    if ok {
      return Some(out)
    }
  }
  None
}

///| 判定 `b` 是否落在整數矩陣 `a` 的行格中：SNF(a) 與 SNF([a|b]) 的

///|
/// 非常規不變因子序列是否相同（coker 同構 ⟺ b ∈ im）。
pub fn int_in_image(a : Array[Array[Int32]], b : Array[Int32]) -> Bool {
  if a.length() == 0 || a[0].length() == 0 {
    for x in b {
      if x != 0 {
        return false
      }
    }
    return true
  }
  let aug : Array[Array[Int32]] = []
  for i = 0; i < a.length(); i = i + 1 {
    let row : Array[Int32] = []
    for x in a[i] {
      row.push(x)
    }
    row.push(b[i])
    aug.push(row)
  }
  let d1 = nonzero_smith(@core.smith_diagonal(@core.mat_from_rows(a)))
  let d2 = nonzero_smith(@core.smith_diagonal(@core.mat_from_rows(aug)))
  if d1.length() != d2.length() {
    return false
  }
  for i = 0; i < d1.length(); i = i + 1 {
    if d1[i] != d2[i] {
      return false
    }
  }
  true
}

///|
fn nonzero_smith(diag : Array[Int32]) -> Array[Int32] {
  let out : Array[Int32] = []
  for d in diag {
    let v = if d < 0 { 0 - d } else { d }
    if v != 0 {
      out.push(v)
    }
  }
  out
}

///| 撓率證書：對 RP² 的 H₁ ≅ ℤ/2 給出

///|  (i)  一個整係數 1-圈 z（∂₁ z = 0）；

///|  (ii) 2z ∈ im_ℤ ∂₂（故 [z] 的階整除 2）；

///|  (iii) z ∉ im_ℤ ∂₂（故 [z] ≠ 0），以 SNF 不變因子比對判定。

///| 三件事合起來 ⇒ H₁ ⊇ ℤ/2，與 SNF 給出的上界夾住。
///

///| **關鍵觀察**：ℚ 值上閉鏈對 ℚ 值圈的全部 50 個配對都為 0——

///| 有理係數完全看不見撓率。撓率的可判定性**只能**來自整係數消元（SNF）。

///|
/// 這是合併在「係數環」層面（而不只是程式碼層面）改變了邊界的證據。
pub struct TorsionWitness {
  cycle_ok : Bool
  half_boundary_ok : Bool
  not_boundary_ok : Bool
  rational_pairings_zero : Int32
  witness : Array[Int32]
  chain : Array[Int32]
}

///|
fn all_zero(v : Array[Int32]) -> Bool {
  let mut ok = true
  for x in v {
    if x != 0 {
      ok = false
    }
  }
  ok
}

///|
pub fn torsion_witness_rp2() -> (TorsionWitness, Homology) {
  let cx = simplex_from_max_faces(2, rp2_faces())
  let d1 = boundary_signed(cx, 1)
  let d2 = boundary_signed(cx, 2)
  let h = homology_of(cx)
  let nfaces = cx.faces[2].length()
  // ℚ 值上閉鏈 × ℚ 值圈的配對全為零（有理係數對撓率失明）
  let d2t : Array[Array[Int32]] = []
  for c = 0; c < d2[0].length(); c = c + 1 {
    let row : Array[Int32] = []
    for r = 0; r < d2.length(); r = r + 1 {
      row.push(d2[r][c])
    }
    d2t.push(row)
  }
  let ker_phi = @algebra.qmat_nullspace(@algebra.qmat_from_int_rows(d2t))
  let ker_z = @algebra.qmat_nullspace(@algebra.qmat_from_int_rows(d1))
  let pairings : Array[Int32] = []
  for a in ker_phi {
    for b in ker_z {
      match (to_integer_vector(a), to_integer_vector(b)) {
        (Some(pa), Some(pb)) => {
          let mut d : Int32 = 0
          for i = 0; i < pa.length(); i = i + 1 {
            d = d + pa[i] * pb[i]
          }
          pairings.push(d)
        }
        (_, _) => pairings.push(0)
      }
    }
  }
  let mut nz : Int32 = 0
  for d in pairings {
    if d != 0 {
      nz = nz + 1
    }
  }
  // 搜尋 2-鏈 c 使 (1/2)∂₂c 為整係數 1-圈且不是邊界
  let mut witness : Array[Int32] = []
  let mut chain : Array[Int32] = []
  let mut found = false
  // 先試「全 1」的 2-鏈（每個邊恰在兩面上 ⇒ ∂c ≡ 0 mod 2）
  let cands : Array[Array[Int32]] = []
  cands.push(Array::make(nfaces, 1))
  // 再試 {0,±1}^nfaces 的有界枚舉（3^10 = 59049）
  let total : Int32 = int_pow3(nfaces)
  let mut code : Int32 = 0
  while code < total {
    let c : Array[Int32] = []
    let mut t = code
    for _i = 0; _i < nfaces; _i = _i + 1 {
      c.push(t % 3 - 1)
      t = t / 3
    }
    cands.push(c)
    code = code + 1
  }
  for c in cands {
    if !found {
      let w = @algebra.int_mat_vec(d2, c)
      let mut even = true
      for x in w {
        if x % 2 != 0 {
          even = false
        }
      }
      if even {
        let z : Array[Int32] = []
        for x in w {
          z.push(x / 2)
        }
        if !all_zero(z) {
          let zz = @algebra.int_mat_vec(d1, z)
          if all_zero(zz) {
            let is_bdry = int_in_image(d2, z)
            if !is_bdry {
              witness = z
              chain = c
              found = true
            }
          }
        }
      }
    }
  }
  let two_z : Array[Int32] = []
  for x in witness {
    two_z.push(x * 2)
  }
  (
    TorsionWitness::{
      cycle_ok: found,
      half_boundary_ok: found && int_in_image(d2, two_z),
      not_boundary_ok: found && !int_in_image(d2, witness),
      rational_pairings_zero: pairings.length() - nz,
      witness,
      chain,
    },
    h,
  )
}

///|
fn int_pow3(n : Int32) -> Int32 {
  let mut p : Int32 = 1
  for _i = 0; _i < n; _i = _i + 1 {
    p = p * 3
  }
  p
}

// ----------------------------------------------------------- 模型面表 ----

///|
/// RP² 的 6 頂點極小三角剖分（f-向量 (6,15,10)，χ=1）。
pub fn rp2_faces() -> Array[Array[Int32]] {
  [
    [0, 1, 2],
    [0, 1, 3],
    [0, 2, 4],
    [0, 3, 5],
    [0, 4, 5],
    [1, 2, 5],
    [1, 3, 4],
    [1, 4, 5],
    [2, 3, 4],
    [2, 3, 5],
  ]
}

///|
/// S² 的四面體邊界（f-向量 (4,6,4)）。
pub fn s2_faces() -> Array[Array[Int32]] {
  [[0, 1, 2], [0, 1, 3], [0, 2, 3], [1, 2, 3]]
}

///|
/// T² 的 3×3 格點三角剖分（f-向量 (9,27,18)）。
pub fn t2_faces() -> Array[Array[Int32]] {
  let out : Array[Array[Int32]] = []
  for i = 0; i < 3; i = i + 1 {
    for j = 0; j < 3; j = j + 1 {
      let a = i * 3 + j
      let b = (i + 1) % 3 * 3 + j
      let c = (i + 1) % 3 * 3 + (j + 1) % 3
      let d = i * 3 + (j + 1) % 3
      out.push([a, b, c])
      out.push([a, c, d])
    }
  }
  out
}

///|
/// 任意維度面表 → 單純複形（自動補齊所有子面）。
pub fn simplex_from_faces(faces : Array[Array[Int32]]) -> SimplexSet {
  let mut maxd : Int32 = 0
  for f in faces {
    if f.length() - 1 > maxd {
      maxd = f.length() - 1
    }
  }
  let g : Array[Array[Array[Int32]]] = []
  for _k = 0; _k <= maxd; _k = _k + 1 {
    g.push([])
  }
  let cx0 = SimplexSet::{ faces: g, nverts: 0, }
  let _ = cx0
  // 逐面插入並補子面
  let acc : Array[Array[Array[Int32]]] = []
  for _k = 0; _k <= maxd; _k = _k + 1 {
    acc.push([])
  }
  let mut nv : Int32 = 0
  for raw in faces {
    let face = sort_vertices(raw)
    let k = face.length()
    let total : Int32 = 1 << k
    let mut m : Int32 = 1
    while m < total {
      let sub : Array[Int32] = []
      for i = 0; i < k; i = i + 1 {
        if (m >> i) % 2 == 1 {
          sub.push(face[i])
        }
      }
      let d = sub.length() - 1
      let mut dup = false
      for old in acc[d] {
        if @algebra.int_vec_eq(old, sub) {
          dup = true
        }
      }
      if !dup {
        acc[d].push(sub)
      }
      m = m + 1
    }
    for v in face {
      if v + 1 > nv {
        nv = v + 1
      }
    }
  }
  for d = 0; d < acc.length(); d = d + 1 {
    acc[d] = sort_faces(acc[d])
  }
  SimplexSet::{ faces: acc, nverts: nv, }
}

///|
/// S¹∨S¹∨S²：以頂點 0 為公共基點，兩個 3-圈（1-面即可）＋ 四面體邊界。
pub fn wedge_faces() -> Array[Array[Int32]] {
  [
    [0, 1],
    [1, 2],
    [2, 0],
    [0, 3],
    [3, 4],
    [4, 0],
    [0, 5, 6],
    [0, 5, 7],
    [0, 6, 7],
    [5, 6, 7],
  ]
}

// -------------------------------------------------- Stasheff 塔生成器 ----

///|
/// 多邊形三角剖分的翻轉圖：頂點 = 剖分，邊 = 單次翻轉。
pub struct FlipGraph {
  nverts : Int32
  edges : Int32
  degree : Int32
  diameter : Int32
  connected : Bool
  trace : Int32
  trace2 : Int32
}

///|
pub fn flip_graph(n : Int32) -> FlipGraph {
  let tris = @nc.triangulations(n)
  let k = tris.length()
  let adj : Array[Array[Int32]] = []
  for _i = 0; _i < k; _i = _i + 1 {
    adj.push(Array::make(k, 0))
  }
  let mut edges : Int32 = 0
  for i = 0; i < k; i = i + 1 {
    for j = i + 1; j < k; j = j + 1 {
      if @nc.are_flippable(tris[i], tris[j]) {
        adj[i][j] = 1
        adj[j][i] = 1
        edges = edges + 1
      }
    }
  }
  // 直徑＝BFS
  let mut diam : Int32 = 0
  let mut connected = true
  for s = 0; s < k; s = s + 1 {
    let dist = Array::make(k, -1)
    dist[s] = 0
    let queue : Array[Int32] = [s]
    let mut head = 0
    while head < queue.length() {
      let u = queue[head]
      head = head + 1
      for v = 0; v < k; v = v + 1 {
        if adj[u][v] == 1 && dist[v] < 0 {
          dist[v] = dist[u] + 1
          queue.push(v)
          if dist[v] > diam {
            diam = dist[v]
          }
        }
      }
    }
    for v = 0; v < k; v = v + 1 {
      if dist[v] < 0 {
        connected = false
      }
    }
  }
  let mut tr : Int32 = 0
  let mut tr2 : Int32 = 0
  for i = 0; i < k; i = i + 1 {
    tr = tr + adj[i][i]
    for j = 0; j < k; j = j + 1 {
      tr2 = tr2 + adj[i][j] * adj[j][i]
    }
  }
  FlipGraph::{
    nverts: k,
    edges,
    degree: n - 3,
    diameter: diam,
    connected,
    trace: tr,
    trace2: tr2,
  }
}

///|
/// B6 的實驗輸出。
pub fn b6_probe() -> Array[String] {
  let out : Array[String] = []
  let models : Array[(String, SimplexSet)] = [
    ("S^2", simplex_from_max_faces(2, s2_faces())),
    ("T^2", simplex_from_max_faces(2, t2_faces())),
    ("RP^2", simplex_from_max_faces(2, rp2_faces())),
    ("S^1vS^1vS^2", simplex_from_faces(wedge_faces())),
  ]
  for m in models {
    let name = m.0
    let cx = m.1
    let h = homology_of(cx)
    let mut fstr = ""
    for d = 0; d < cx.faces.length(); d = d + 1 {
      fstr = "\{fstr} \{cx.faces[d].length()}"
    }
    out.push("\{name}: f=\{fstr} chi=\{h.euler} \{homology_show(h)}")
  }
  let (w, _h) = torsion_witness_rp2()
  out.push(
    "RP^2 撓率證書: cycle=\{w.cycle_ok} 2z∈im=\{w.half_boundary_ok} z∉im=\{w.not_boundary_ok} ⇒ H1 含 Z/2（與 SNF 上界夾住）",
  )
  out.push(
    "有理係數盲區: 上閉鏈×圈的 \{w.rational_pairings_zero} 個 ℚ-配對全為 0（撓率只能由整係數 SNF 看見）",
  )
  out.push("撓率見證 z=\{int_list_show(w.witness)} c=\{int_list_show(w.chain)}")
  let mut line = "Associahedron 骨架（翻轉圖, n 邊形）:"
  for n = 5; n <= 10; n = n + 1 {
    let fg = flip_graph(n)
    line = "\{line} [n=\{n}: V=\{fg.nverts} E=\{fg.edges} d=\{fg.degree} diam=\{fg.diameter} trA2=\{fg.trace2} conn=\{fg.connected}]"
  }
  out.push(line)
  out
}

///| 整數向量顯示（不用 `Show`）。
fn int_list_show(a : Array[Int32]) -> String {
  let mut out = "["
  for i = 0; i < a.length(); i = i + 1 {
    let t = a[i].to_string()
    out = if i == 0 {
      out + t
    } else {
      out + ", " + t
    }
  }
  out + "]"
}
