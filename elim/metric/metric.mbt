///| ## metric —— 有限度量空間、Gromov–Hausdorff 距離與 Vietoris–Rips 同調

///|

///| * [Ax-Metric] 度量公理由枚舉驗證；

///| * [D-GH] 以「對應 (correspondence)」的離散度定義 2·d_GH(X,Y) = min_R dis(R)，

///|   有限情形可枚舉全部對應精確計算；驗證對稱性、三角不等式、d_GH=0 ⟺ 雙射等距；

///| * [T-GH-Lip] 1-Lipschitz 不變量：|diam X - diam Y| ≤ 2 d_GH(X,Y)；

///| * [T-GH-Sub] 子空間界：若 Y ⊂ X 且每點距 Y 不超過 ε，則 2 d_GH(X,Y) ≤ 2ε；

///| * [D-VR] Vietoris–Rips（flag）複形：枚舉 all cliques，造邊界矩陣，

///|
///   用 @core 消元算 Betti 數；驗證 Euler 恆等式 [T-VR-Euler] 與圈圖定理 [T-VR-Cycle]。
/// [D-MSpace] n 點有限度量：d 為長度 n² 的扁平整數表（d[i*n+j]）。
pub struct MSpace {
  n : Int32
  d : Array[Int32]
}

///|
/// [D-Mk] 由上三角距離構造（要求 vals.length() = n(n-1)/2，逐對 (i<j) 依序給值）。
pub fn mspace_build(n : Int32, vals : Array[Int32]) -> MSpace {
  let d = Array::make(n * n, 0)
  let mut k = 0
  let mut i = 0
  while i < n {
    let mut j = i + 1
    while j < n {
      d[i * n + j] = vals[k]
      d[j * n + i] = vals[k]
      k = k + 1
      j = j + 1
    }
    i = i + 1
  }
  MSpace::{ n, d, }
}

///|
pub fn mspace_get(m : MSpace, i : Int32, j : Int32) -> Int32 {
  m.d[i * m.n + j]
}

///|
/// [Ax-Metric] 度量公理：正定（區辨點）、對稱、三角不等式。
pub fn check_metric(m : MSpace) -> Bool {
  let n = m.n
  let mut ok = true
  let mut i = 0
  while i < n {
    if mspace_get(m, i, i) != 0 {
      ok = false
    }
    let mut j = 0
    while j < n {
      if i != j && mspace_get(m, i, j) <= 0 {
        ok = false
      }
      if mspace_get(m, i, j) != mspace_get(m, j, i) {
        ok = false
      }
      let mut k = 0
      while k < n {
        if mspace_get(m, i, j) > mspace_get(m, i, k) + mspace_get(m, k, j) {
          ok = false
        }
        k = k + 1
      }
      j = j + 1
    }
    i = i + 1
  }
  ok
}

///|
/// [D-Diam] 圓周/直徑。
pub fn diam(m : MSpace) -> Int32 {
  let mut best = 0
  let mut i = 0
  while i < m.n {
    let mut j = 0
    while j < m.n {
      let v = mspace_get(m, i, j)
      if v > best {
        best = v
      }
      j = j + 1
    }
    i = i + 1
  }
  best
}

///|
/// [D-Cyc] 循環圖度量：點 0..n-1，d(i,j) = min(|i-j|, n-|i-j|)·step。
pub fn mspace_cycle(n : Int32, step : Int32) -> MSpace {
  let vals : Array[Int32] = []
  let mut i = 0
  while i < n {
    let mut j = i + 1
    while j < n {
      let raw = j - i
      let v = if raw * step > (n - raw) * step {
        (n - raw) * step
      } else {
        raw * step
      }
      let _ = vals.push(v)
      j = j + 1
    }
    i = i + 1
  }
  mspace_build(n, vals)
}

///|
/// [D-Sub] 取子集（誘導度量）。
pub fn mspace_sub(m : MSpace, keep : Array[Int32]) -> MSpace {
  let k = keep.length()
  let vals : Array[Int32] = []
  let mut i = 0
  while i < k {
    let mut j = i + 1
    while j < k {
      let _ = vals.push(mspace_get(m, keep[i], keep[j]))
      j = j + 1
    }
    i = i + 1
  }
  mspace_build(k, vals)
}

///|
/// [D-Perm] 是否存在雙射等距 X → Y（枚舉所有置換）。
pub fn is_isometric(a : MSpace, b : MSpace) -> Bool {
  if a.n != b.n {
    false
  } else {
    let n = a.n
    let perm = Array::makei(n, i => i)
    let mut ok = false
    let mut counter = 0
    while counter < fact(n) {
      perm_at_index(n, counter, perm)
      if match_iso(a, b, perm) {
        ok = true
      }
      counter = counter + 1
    }
    ok
  }
}

///|
fn fact(k : Int32) -> Int32 {
  let mut r = 1
  let mut i = 2
  while i <= k {
    r = r * i
    i = i + 1
  }
  r
}

// 以階乘數系把 index 展開成置換

///|
fn perm_at_index(n : Int32, idx : Int32, out : Array[Int32]) -> Unit {
  let pool : Array[Int32] = Array::makei(n, i => i)
  let mut k = idx
  let mut i = 0
  while i < n {
    let rem = n - i
    let pick = k % rem
    out[i] = pool[pick]
    let _ = pool.remove(pick)
    k = k / rem
    i = i + 1
  }
}

///|
fn match_iso(a : MSpace, b : MSpace, perm : Array[Int32]) -> Bool {
  let n = a.n
  let mut i = 0
  while i < n {
    let mut j = 0
    while j < n {
      if mspace_get(a, i, j) != mspace_get(b, perm[i], perm[j]) {
        return false
      }
      j = j + 1
    }
    i = i + 1
  }
  true
}

// ===================== Gromov–Hausdorff（對應的離散度）=====================

///|
/// [D-Dis] 對應 R（以 bitmask 編碼 X×Y 的格子）的離散度：
///   dis(R) = max{|d_X(x,x') - d_Y(y,y')| : (x,y),(x',y') ∈ R}。
fn disp(a : MSpace, b : MSpace, mask : Int32) -> Int32 {
  let na = a.n
  let nb = b.n
  let cells = na * nb
  let mut best = 0
  let mut c = 0
  while c < cells {
    if (mask >> c) % 2 == 1 {
      let x = c % na
      let y = c / na
      let mut c2 = 0
      while c2 < cells {
        if (mask >> c2) % 2 == 1 {
          let x2 = c2 % na
          let y2 = c2 / na
          let da = mspace_get(a, x, x2)
          let db = mspace_get(b, y, y2)
          let diff = if da > db { da - db } else { db - da }
          if diff > best {
            best = diff
          }
        }
        c2 = c2 + 1
      }
    }
    c = c + 1
  }
  best
}

///|
fn covers_all(na : Int32, nb : Int32, mask : Int32) -> Bool {
  let mut i = 0
  while i < na {
    let mut found = false
    let mut j = 0
    while j < nb {
      if (mask >> (i + j * na)) % 2 == 1 {
        found = true
      }
      j = j + 1
    }
    if !found {
      return false
    }
    i = i + 1
  }
  let mut j = 0
  while j < nb {
    let mut found = false
    let mut i = 0
    while i < na {
      if (mask >> (i + j * na)) % 2 == 1 {
        found = true
      }
      i = i + 1
    }
    if !found {
      return false
    }
    j = j + 1
  }
  true
}

///|
/// [D-GH] 2·d_GH(X,Y) = min_R dis(R)（枚舉全部對應；|X|·|Y| ≤ 16 可負擔）。
///   無對應存在時回傳 -1（空間為空）。
pub fn gh2(a : MSpace, b : MSpace) -> Int32 {
  let cells = a.n * b.n
  if cells == 0 || cells > 16 {
    return -1
  }
  let total = 1 << cells
  let mut best = -1
  let mut mask = 0
  while mask < total {
    if covers_all(a.n, b.n, mask) {
      let d = disp(a, b, mask)
      if best < 0 || d < best {
        best = d
      }
    }
    mask = mask + 1
  }
  best
}

///|
/// [T-GH-Metric] 在一組空間上驗證：自反為 0、對稱、三角不等式、
///   且 d_GH(X,Y) = 0 ⟺ 存在雙射等距。
pub fn check_gh_axioms(spaces : Array[MSpace]) -> Bool {
  let k = spaces.length()
  let mut ok = true
  let mut i = 0
  while i < k {
    let mut j = 0
    while j < k {
      let g = gh2(spaces[i], spaces[j])
      let h = gh2(spaces[j], spaces[i])
      if g != h {
        ok = false
      }
      if i == j && g != 0 {
        ok = false
      }
      if g == 0 && !is_isometric(spaces[i], spaces[j]) {
        ok = false
      }
      if g > 0 && is_isometric(spaces[i], spaces[j]) {
        ok = false
      }
      let mut t = 0
      while t < k {
        let g2 = gh2(spaces[j], spaces[t])
        let g3 = gh2(spaces[i], spaces[t])
        if g3 > g + g2 {
          ok = false
        }
        t = t + 1
      }
      j = j + 1
    }
    i = i + 1
  }
  ok
}

///|
/// [T-GH-Lip] 1-Lipschitz 性：|diam X - diam Y| ≤ 2 d_GH(X,Y)。
pub fn check_diam_lipschitz(a : MSpace, b : MSpace) -> Bool {
  let g = gh2(a, b)
  let da = diam(a)
  let db = diam(b)
  let diff = if da > db { da - db } else { db - da }
  g < 0 || diff <= g
}

///|
/// [T-GH-Sub] 子空間界：ε = max_x min_{y∈Y} d_X(x,y) ⟹ 2 d_GH(X,Y) ≤ 2ε。
pub fn check_subspace_bound(m : MSpace, keep : Array[Int32]) -> Bool {
  let sub = mspace_sub(m, keep)
  let k = sub.n
  let mut eps = 0
  let mut x = 0
  while x < m.n {
    let mut best = -1
    let mut t = 0
    while t < k {
      let v = mspace_get(m, x, keep[t])
      if best < 0 || v < best {
        best = v
      }
      t = t + 1
    }
    if best > eps {
      eps = best
    }
    x = x + 1
  }
  let g = gh2(m, sub)
  g >= 0 && g <= 2 * eps
}

// ===================== Vietoris–Rips 複形與 Betti 數 =====================

///|
/// [D-VR] 回傳 VR 複形的所有單纯形（每個以升序頂點陣列表示），尺度 r：
///   一個頂點集是單纯形 ⟺ 其中任意兩點距離 ≤ r（flag complex）。
pub fn vr_simplices(m : MSpace, r : Int32) -> Array[Array[Int32]] {
  let n = m.n
  let out : Array[Array[Int32]] = []
  let total = 1 << n
  let mut mask = 1
  while mask < total {
    let vs : Array[Int32] = []
    let mut i = 0
    while i < n {
      if (mask >> i) % 2 == 1 {
        let _ = vs.push(i)
      }
      i = i + 1
    }
    let mut clique = true
    let a = vs.length()
    let mut p = 0
    while p < a {
      let mut q = p + 1
      while q < a {
        if mspace_get(m, vs[p], vs[q]) > r {
          clique = false
        }
        q = q + 1
      }
      p = p + 1
    }
    if clique {
      let _ = out.push(vs)
    }
    mask = mask + 1
  }
  out
}

///|
pub fn simplices_of_dim(
  sims : Array[Array[Int32]],
  dim : Int32,
) -> Array[Int32] {
  // 回傳在 sims 中的索引
  let out : Array[Int32] = []
  let mut i = 0
  while i < sims.length() {
    if sims[i].length() - 1 == dim {
      let _ = out.push(i)
    }
    i = i + 1
  }
  out
}

///|
/// [D-Bdry] 邊界矩陣 ∂_{dim+1} : C_{dim+1} → C_{dim}（F_2 係數）。
pub fn boundary_matrix(sims : Array[Array[Int32]], dim : Int32) -> @core.Mat {
  let cur = simplices_of_dim(sims, dim)
  let nxt = simplices_of_dim(sims, dim + 1)
  let rows : Array[Array[Int32]] = Array::makei(cur.length(), _ => {
    Array::make(nxt.length(), 0)
  })
  let mut j = 0
  while j < nxt.length() {
    let sig = sims[nxt[j]]
    let slen = sig.length()
    let mut i = 0
    while i < slen {
      let face : Array[Int32] = of_iter_drop(sig, i)
      // 找 face 在 cur 中的位置
      let mut kk = 0
      let mut found = -1
      while kk < cur.length() {
        if @algebra.int_vec_eq(sims[cur[kk]], face) {
          found = kk
        }
        kk = kk + 1
      }
      if found >= 0 {
        rows[found][j] = 1
      }
      i = i + 1
    }
    j = j + 1
  }
  @core.mat_from_rows(rows)
}

///|
fn of_iter_drop(a : Array[Int32], skip : Int32) -> Array[Int32] {
  let out : Array[Int32] = []
  let mut i = 0
  while i < a.length() {
    if i != skip {
      let _ = out.push(a[i])
    }
    i = i + 1
  }
  out
}

///|
/// [D-Fvec] f-向量：f_k = #k-單纯形。
pub fn vr_f_vector(sims : Array[Array[Int32]], maxdim : Int32) -> Array[Int32] {
  Array::makei(maxdim + 1, k => simplices_of_dim(sims, k).length())
}

///|
/// [D-BdryAll] 全部邊界矩陣的秩：rank[k] = rank(∂_k : C_k → C_{k-1})，∂_0 = 0。
pub fn boundary_ranks(
  sims : Array[Array[Int32]],
  maxdim : Int32,
) -> Array[Int32] {
  let fld = @core.mk_field(2)
  Array::makei(maxdim + 1, k => {
    if k == 0 {
      0
    } else {
      @core.rank_mod(boundary_matrix(sims, k - 1), fld)
    }
  })
}

///|
/// [D-Betti] Betti 數 β_k = (f_k − rank ∂_k) − rank ∂_{k+1}，全部由消元算出。
pub fn vr_betti_all(m : MSpace, r : Int32) -> Array[Int32] {
  let sims = vr_simplices(m, r)
  let maxdim = if m.n == 0 { 0 } else { m.n - 1 }
  let f = vr_f_vector(sims, maxdim)
  let rk = boundary_ranks(sims, maxdim)
  Array::makei(maxdim + 1, k => {
    let next_rank = if k + 1 > maxdim { 0 } else { rk[k + 1] }
    f[k] - rk[k] - next_rank
  })
}

///|
/// [D-AltSum] 交錯和 Σ (-1)^i v[i]。
/// [D-AltSum] 交錯和（公開給 evolve 使用）。
pub fn alt_sum(v : Array[Int32]) -> Int32 {
  let mut s = 0
  let mut i = 0
  while i < v.length() {
    s = s + (if i % 2 == 0 { v[i] } else { 0 - v[i] })
    i = i + 1
  }
  s
}

///|
/// [D-Nth] 越界回傳 0。
fn nth(v : Array[Int32], i : Int32) -> Int32 {
  if i < v.length() {
    v[i]
  } else {
    0
  }
}

///|
/// [T-VR-Euler] Euler 恆等式：Σ_k (-1)^k f_k = Σ_k (-1)^k β_k（對所有維數求和）。
pub fn check_euler(m : MSpace, r : Int32) -> Bool {
  let sims = vr_simplices(m, r)
  let maxdim = if m.n == 0 { 0 } else { m.n - 1 }
  let f = vr_f_vector(sims, maxdim)
  let b = vr_betti_all(m, r)
  alt_sum(f) == alt_sum(b)
}

///|
/// [T-VR-Cycle] 圈圖度量的 Vietoris–Rips：n ≥ 4 時
///   (i) r = 1：複形就是 n-圈圖（無三角形），β = (1,1,0,…)，
///       且 β1 = E - V + 1（圖論公式，與消元結果獨立對照）；
///   (ii) r ≥ ⌊n/2⌋：所有兩兩距離 ≤ r，複形為完整純形，可縮：β_k = 0 (k ≥ 1)；
///   (iii) 每個 r 都滿足 [T-VR-Euler]。
pub fn check_cycle_theorem(n : Int32) -> Bool {
  let m = mspace_cycle(n, 1)
  if !check_metric(m) || n < 4 {
    return false
  }
  let half = n / 2
  let mut ok = true
  let sims1 = vr_simplices(m, 1)
  let v1 = simplices_of_dim(sims1, 0).length()
  let e1 = simplices_of_dim(sims1, 1).length()
  let t1 = simplices_of_dim(sims1, 2).length()
  let b1v = vr_betti_all(m, 1)
  if !(v1 == n && e1 == n && t1 == 0) {
    ok = false
  }
  if !(nth(b1v, 0) == 1 && nth(b1v, 1) == 1 && nth(b1v, 2) == 0) {
    ok = false
  }
  if nth(b1v, 1) != e1 - v1 + 1 {
    ok = false
  }
  if !check_euler(m, 1) {
    ok = false
  }
  let mut r = half
  while r <= half + 2 {
    let sims = vr_simplices(m, r)
    let full = 1 << n
    if sims.length() != full - 1 {
      ok = false
    }
    let bv = vr_betti_all(m, r)
    let mut kk = 0
    while kk < bv.length() {
      let expect = if kk == 0 { 1 } else { 0 }
      if bv[kk] != expect {
        ok = false
      }
      kk = kk + 1
    }
    if !check_euler(m, r) {
      ok = false
    }
    r = r + 1
  }
  let mut rr = 1
  while rr <= n {
    if !check_euler(m, rr) {
      ok = false
    }
    rr = rr + 1
  }
  ok
}

///|
/// [D-Points] 由直線上的整數座標構造路徑度量。
pub fn mspace_from_points(xs : Array[Int32]) -> MSpace {
  let n = xs.length()
  let vals : Array[Int32] = []
  let mut i = 0
  while i < n {
    let mut j = i + 1
    while j < n {
      let raw = xs[i] - xs[j]
      let _ = vals.push(if raw < 0 { 0 - raw } else { raw })
      j = j + 1
    }
    i = i + 1
  }
  mspace_build(n, vals)
}

///|
/// [T-VR-Fill] n=3 的圈圖在 r=1 時被實心三角形填滿：β1 = 0（邊界成為週迹）。
pub fn check_fill_edge_case() -> Bool {
  let m = mspace_cycle(3, 1)
  let b = vr_betti_all(m, 1)
  let ok_euler = check_euler(m, 1)
  ok_euler &&
  b.length() >= 3 &&
  b[0] == 1 &&
  b[1] == 0 &&
  b[2] == 0 &&
  diam(m) == 1
}
