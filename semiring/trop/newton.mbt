// ===========================================================================
// 熱帶幾何 II：雙變數牛頓多邊形、正則細分、對偶熱帶曲線、平衡條件
//
// 這一段是「熱帶幾何基本定理」在本庫裡可執行的版本：
//
//   熱帶多項式  f(x,y) = min_{a∈A} ( c_a + a₁x + a₂y )
//   的熱帶超曲面，等於「把支撐集 A 按係數 c_a 抬升後，取**下凸包**，
//   再投影回平面」所得正則細分的**對偶圖**。
//
// 為什麼值得寫成程式：
//   * 抬升 + 下凸包是純整數運算（平面法向量取交叉積、以點積驗證「全部在上方」），
//     沒有任何浮點決策，所以細分是精確的、可重現的。
//   * 對偶圖的每個面 ↔ 熱帶曲線的一個頂點；共享邊 ↔ 熱帶曲線的邊；
//     邊的方向 = 細分邊的法向、邊的權重 = 細分邊的格長。
//   * 於是**平衡條件** Σ w_e · ν_e = 0 變成一個可以直接算出來並檢查的整數恆等式，
//     而不是一句「滿足平衡條件」的宣稱。
//
// 本檔案另外驗證三件事（測試與報告都實際執行）：
//   1. 對每個面 F（法向 (nx,ny,nz)），以整數權重 (nx,ny,nz) 求 argmin
//      恰好得到 F 的成員集合 ⇒ F 是法扇的一個格，且該格對應熱帶曲線的一個頂點。
//   2. 細分的三角形面積和 = 牛頓多邊形面積 ⇒ 細分真的覆蓋了整個多邊形。
//   3. 平衡條件殘差全為 0。
// ===========================================================================

///|
/// 平面整點。
pub(all) struct Pt2 {
  x : Int32
  y : Int32
} derive(Eq)

///|
pub extend Pt2 with Eq::{equal, not_equal}

///|
pub fn Pt2::new(x : Int32, y : Int32) -> Pt2 {
  { x, y, }
}

///|
/// 叉積 `a × b = a.x·b.y − a.y·b.x`。
pub fn Pt2::cross(a : Pt2, b : Pt2) -> Int64 {
  a.x.to_int64() * b.y.to_int64() - a.y.to_int64() * b.x.to_int64()
}

///|
/// 原始化（除以 gcd），保留方向。
pub fn Pt2::prim(self : Pt2) -> Pt2 {
  let g = gcd64(self.x.to_int64(), self.y.to_int64())
  if g == 0L {
    { x: 0, y: 0, }
  } else {
    {
      x: (self.x.to_int64() / g).to_int(),
      y: (self.y.to_int64() / g).to_int(),
    }
  }
}

///|
/// 格長（= 向量除以原始向量後的倍數）：`gcd(|x|, |y|)`。
pub fn Pt2::lattice_len(self : Pt2) -> Int32 {
  gcd64(self.x.to_int64(), self.y.to_int64()).to_int()
}

///|
/// 逆時針 90° 旋轉（`(x,y) ↦ (−y,x)`）。
pub fn Pt2::rot90(self : Pt2) -> Pt2 {
  { x: -self.y, y: self.x, }
}

///|
pub impl Show for Pt2 with fn output(self, logger) {
  logger.write_string("(\{self.x},\{self.y})")
}

///|
pub extend Pt2 with Show::{output, to_string}

///|
/// 雙變數熱帶單項式：`c + i·x + j·y`。
pub(all) struct BTerm {
  c : Int32
  i : Int32
  j : Int32
}

///|
pub fn BTerm::new(c : Int32, i : Int32, j : Int32) -> BTerm {
  { c, i, j, }
}

///|
/// 雙變數熱帶多項式。
pub(all) struct BPoly {
  terms : Array[BTerm]
}

///|
pub fn BPoly::new(terms : Array[BTerm]) -> BPoly {
  { terms, }
}

///|
/// 求值 `min_a (c_a + i_a·x + j_a·y)`。
pub fn BPoly::eval(self : BPoly, wx : Int32, wy : Int32) -> Int32 {
  let mut best = @alg.trop_inf
  for t in self.terms {
    let v = sat_add_i32(
      sat_add_i32(t.c, sat_mul_i32(t.i, wx)),
      sat_mul_i32(t.j, wy),
    )
    if v < best {
      best = v
    }
  }
  best
}

///|
/// 以整數權重求 argmin：`min_a (scale·c_a + i_a·wx + j_a·wy)`。
///
/// 之所以帶 `scale`：一個面的法向量是 `(nx, ny, nz)`，它代表的熱帶方向是
/// `w = (nx/nz, ny/nz)`。乘以正數 `nz` 不改變 argmin，於是整個檢查可以留在整數上。
pub fn BPoly::minima_scaled(
  self : BPoly,
  wx : Int64,
  wy : Int64,
  scale : Int64,
) -> Array[Int32] {
  let out : Array[Int32] = []
  let mut best = 0L
  let mut first = true
  for k in 0..<self.terms.length() {
    let t = self.terms[k]
    let v = scale * t.c.to_int64() + t.i.to_int64() * wx + t.j.to_int64() * wy
    if first || v < best {
      best = v
      first = false
      out.clear()
      out.push(k)
    } else if v == best {
      out.push(k)
    }
  }
  out
}

///|
/// 支撐集的凸包（Andrew 單調鏈，逆時針，無共線點）。
pub fn BPoly::newton_hull(self : BPoly) -> Array[Pt2] {
  let pts : Array[Pt2] = []
  for t in self.terms {
    pts.push(Pt2::new(t.i, t.j))
  }
  // 依 (x, y) 字典序插入排序
  let mut i = 1
  while i < pts.length() {
    let key = pts[i]
    let mut j = i
    while j > 0 && pt_gt(pts[j - 1], key) {
      pts[j] = pts[j - 1]
      j = j - 1
    }
    pts[j] = key
    i = i + 1
  }
  // 去重
  let uniq : Array[Pt2] = []
  for p in pts {
    if uniq.length() == 0 || uniq[uniq.length() - 1] != p {
      uniq.push(p)
    }
  }
  if uniq.length() < 3 {
    return uniq
  }
  let lower : Array[Pt2] = []
  for p in uniq {
    while lower.length() >= 2 {
      let a = lower[lower.length() - 2]
      let b = lower[lower.length() - 1]
      let ax = (b.x - a.x).to_int64()
      let ay = (b.y - a.y).to_int64()
      let bx = (p.x - a.x).to_int64()
      let by = (p.y - a.y).to_int64()
      if ax * by - ay * bx <= 0L {
        let _ = lower.pop()
      } else {
        break
      }
    }
    lower.push(p)
  }
  let upper : Array[Pt2] = []
  let mut k = uniq.length() - 1
  while k >= 0 {
    let p = uniq[k]
    while upper.length() >= 2 {
      let a = upper[upper.length() - 2]
      let b = upper[upper.length() - 1]
      let ax = (b.x - a.x).to_int64()
      let ay = (b.y - a.y).to_int64()
      let bx = (p.x - a.x).to_int64()
      let by = (p.y - a.y).to_int64()
      if ax * by - ay * bx <= 0L {
        let _ = upper.pop()
      } else {
        break
      }
    }
    upper.push(p)
    k = k - 1
  }
  // 去掉兩端重複
  let out : Array[Pt2] = []
  for q in lower {
    out.push(q)
  }
  for q in upper {
    if out.length() > 0 && out[out.length() - 1] == q {
      continue
    }
    out.push(q)
  }
  if out.length() > 1 && out[0] == out[out.length() - 1] {
    let _ = out.pop()
  }
  out
}

///|
fn pt_gt(a : Pt2, b : Pt2) -> Bool {
  if a.x != b.x {
    a.x > b.x
  } else {
    a.y > b.y
  }
}

///|
/// 牛頓多邊形面積的兩倍（鞋帶公式，逆時針取正）。
pub fn BPoly::newton_area2(self : BPoly) -> Int64 {
  let h = self.newton_hull()
  let mut s = 0L
  for i in 0..<h.length() {
    let a = h[i]
    let b = h[(i + 1) % h.length()]
    s = s + a.x.to_int64() * b.y.to_int64() - b.x.to_int64() * a.y.to_int64()
  }
  if s < 0L {
    -s
  } else {
    s
  }
}

///|
/// 抬升平面的法向量：`nx·x + ny·y + nz·z = d`，且 `nz > 0`（下凸包）。
pub(all) struct Plane {
  nx : Int64
  ny : Int64
  nz : Int64
  d : Int64
} derive(Eq)

///|
pub extend Plane with Eq::{equal, not_equal}

///|
/// 正則細分的一個面（投影回平面後的凸多邊形）。
pub(all) struct Face {
  plane : Plane
  /// 落在該平面上的支撐點索引（= 該面在法扇中的格的 argmin 集合）
  members : Array[Int32]
  /// 面的邊界多邊形（成員索引，逆時針凸環）
  polygon : Array[Int32]
  /// 多邊形的邊（成員索引對），即細分的邊
  boundary : Array[(Int32, Int32)]
}

///|
/// 正則細分：抬升所有支撐點 → 取「下凸包」的面 → 投影回平面。
///
/// 下凸包的判據：三點決定的平面 `N = (nx,ny,nz)`（必要時整體變號使 `nz > 0`），
/// 且**所有**支撐點都滿足 `N·p ≥ D`。這正是「以帶正 z 分量的線性泛函最小化」，
/// 也就是由熱帶方向 `w = (nx/nz, ny/nz)` 所選出的面。
pub fn BPoly::subdivision(self : BPoly) -> Array[Face] {
  let n = self.terms.length()
  let planes : Array[Plane] = []
  let tris : Array[Array[(Int32, Int32, Int32)]] = []
  for a in 0..<n {
    for b in (a + 1)..<n {
      for c in (b + 1)..<n {
        let pa = self.terms[a]
        let pb = self.terms[b]
        let pc = self.terms[c]
        let ux = (pb.i - pa.i).to_int64()
        let uy = (pb.j - pa.j).to_int64()
        let uz = (pb.c - pa.c).to_int64()
        let vx = (pc.i - pa.i).to_int64()
        let vy = (pc.j - pa.j).to_int64()
        let vz = (pc.c - pa.c).to_int64()
        // N = u × v
        let mut nx = uy * vz - uz * vy
        let mut ny = uz * vx - ux * vz
        let mut nz = ux * vy - uy * vx
        if nz == 0L {
          continue
        }
        let mut d = nx * pa.i.to_int64() +
          ny * pa.j.to_int64() +
          nz * pa.c.to_int64()
        if nz < 0L {
          nx = -nx
          ny = -ny
          nz = -nz
          d = -d
        }
        // 全部點都要在平面上方
        let mut ok = true
        for k in 0..<n {
          let t = self.terms[k]
          let val = nx * t.i.to_int64() +
            ny * t.j.to_int64() +
            nz * t.c.to_int64()
          if val < d {
            ok = false
            break
          }
        }
        if !ok {
          continue
        }
        let g = gcd64(gcd64(nx, ny), gcd64(nz, d))
        let gg = if g == 0L { 1L } else { g }
        let pl = { nx: nx / gg, ny: ny / gg, nz: nz / gg, d: d / gg, }
        // 找同一個平面
        let mut idx = -1
        for k in 0..<planes.length() {
          if planes[k] == pl {
            idx = k
            break
          }
        }
        if idx < 0 {
          planes.push(pl)
          tris.push([])
          idx = planes.length() - 1
        }
        tris[idx].push((a, b, c))
      }
    }
  }
  let faces : Array[Face] = []
  for k in 0..<planes.length() {
    let pl = planes[k]
    // 成員：落在平面上
    let members : Array[Int32] = []
    for i in 0..<n {
      let t = self.terms[i]
      let val = pl.nx * t.i.to_int64() +
        pl.ny * t.j.to_int64() +
        pl.nz * t.c.to_int64()
      if val == pl.d {
        members.push(i)
      }
    }
    // 面是凸的 ⇒ 邊界 = 成員點的凸包
    let polygon = self.hull_of(members)
    let boundary : Array[(Int32, Int32)] = []
    if polygon.length() >= 2 {
      for q in 0..<polygon.length() {
        boundary.push((polygon[q], polygon[(q + 1) % polygon.length()]))
      }
    }
    faces.push({ plane: pl, members, polygon, boundary, })
  }
  faces
}

///|
/// 給定成員索引，取它們在平面座標上的凸包（逆時針，回傳成員索引序列）。
///
/// 為什麼不從三角形收集邊界：一個面可能有多於三個成員（共面），
/// 三點組合會互相重疊，用「只出現一次的邊」判邊界就會全部落空。
/// 直接對成員取凸包是唯一穩健的做法。
pub fn BPoly::hull_of(self : BPoly, idx : Array[Int32]) -> Array[Int32] {
  if idx.length() <= 2 {
    return idx
  }
  let pts : Array[Int32] = []
  for v in idx {
    pts.push(v)
  }
  // 依 (i, j) 排序
  let mut a = 1
  while a < pts.length() {
    let key = pts[a]
    let kp = self.terms[key]
    let mut b = a
    while b > 0 {
      let q = self.terms[pts[b - 1]]
      let gt = if q.i != kp.i { q.i > kp.i } else { q.j > kp.j }
      if gt {
        pts[b] = pts[b - 1]
        b = b - 1
      } else {
        break
      }
    }
    pts[b] = key
    a = a + 1
  }
  let cross = fn(o : Int32, p : Int32, q : Int32) -> Int64 {
    let oo = self.terms[o]
    let pp = self.terms[p]
    let qq = self.terms[q]
    (pp.i - oo.i).to_int64() * (qq.j - oo.j).to_int64() -
    (pp.j - oo.j).to_int64() * (qq.i - oo.i).to_int64()
  }
  let lower : Array[Int32] = []
  for p in pts {
    while lower.length() >= 2 &&
          cross(lower[lower.length() - 2], lower[lower.length() - 1], p) <= 0L {
      let _ = lower.pop()
    }
    lower.push(p)
  }
  let upper : Array[Int32] = []
  let mut k = pts.length() - 1
  while k >= 0 {
    let p = pts[k]
    while upper.length() >= 2 &&
          cross(upper[upper.length() - 2], upper[upper.length() - 1], p) <= 0L {
      let _ = upper.pop()
    }
    upper.push(p)
    k = k - 1
  }
  let out : Array[Int32] = []
  for v in lower {
    if out.length() == 0 || out[out.length() - 1] != v {
      out.push(v)
    }
  }
  for v in upper {
    if out.length() == 0 || out[out.length() - 1] != v {
      out.push(v)
    }
  }
  if out.length() > 1 && out[0] == out[out.length() - 1] {
    let _ = out.pop()
  }
  out
}

///|
/// 面的面積兩倍（對面的邊界環用鞋帶公式）。
///
/// 注意不能用「該面的三角形面積和」：一個面可能有多於 3 個成員點，
/// 三點組合會互相重疊，面積會被重複計算。
pub fn BPoly::face_area2(self : BPoly, f : Face) -> Int64 {
  let ring = f.polygon
  if ring.length() < 3 {
    return 0L
  }
  let mut s = 0L
  for k in 0..<ring.length() {
    let a = self.terms[ring[k]]
    let b = self.terms[ring[(k + 1) % ring.length()]]
    s = s + a.i.to_int64() * b.j.to_int64() - b.i.to_int64() * a.j.to_int64()
  }
  if s < 0L {
    -s
  } else {
    s
  }
}

///|
/// 面的重心（支撐點的座標平均），用於決定外法向。
fn face_centroid(poly : BPoly, f : Face) -> (Double, Double) {
  let mut sx = 0.0
  let mut sy = 0.0
  for m in f.members {
    sx = sx + poly.terms[m].i.to_double()
    sy = sy + poly.terms[m].j.to_double()
  }
  let k = f.members.length().to_double()
  (sx / k, sy / k)
}

///|
/// 對偶熱帶曲線的一條邊。
///
/// 細分的每一條邊（包含落在牛頓多邊形邊界上的邊）都對偶到熱帶曲線的一條邊；
/// 只屬於一個面的邊對偶到**無界射線**（`face_b = -1`）。
/// 這一點很容易漏：少了射線，頂點的平衡條件就不會成立。
pub(all) struct DualEdge {
  face_a : Int32
  /// 另一個面；`-1` 表示這是射線（只屬於 `face_a`）
  face_b : Int32
  /// 對偶（細分）邊的端點：支撐點索引
  from_term : Int32
  to_term : Int32
  /// 熱帶曲線邊的原始方向（由 `face_a` 向外）
  dir : Pt2
  /// 權重 = 對偶邊的格長
  weight : Int32
}

///|
/// 由正則細分取對偶圖。
///
/// 對每一條細分邊（格點線段），決定它被哪些面共享：
///   * 兩個面 → 熱帶曲線的**有界邊**，方向 = 該線段的原始法向（由 `face_a` 向外）；
///   * 一個面 → 熱帶曲線的**射線**（延伸到無窮）。
/// 權重一律是該線段的格長（= 原始方向上的倍數），這正是平衡條件的係數。
pub fn BPoly::dual_curve(self : BPoly, faces : Array[Face]) -> Array[DualEdge] {
  // 1. 收集所有細分邊，以及它出現在哪些面
  let e_lo : Array[Int32] = []
  let e_hi : Array[Int32] = []
  let e_owners : Array[Array[Int32]] = []
  for fi in 0..<faces.length() {
    for k in 0..<faces[fi].boundary.length() {
      let u = faces[fi].boundary[k].0
      let w = faces[fi].boundary[k].1
      let lo = if u < w { u } else { w }
      let hi = if u < w { w } else { u }
      let mut found = -1
      for q in 0..<e_lo.length() {
        if e_lo[q] == lo && e_hi[q] == hi {
          found = q
          break
        }
      }
      if found < 0 {
        e_lo.push(lo)
        e_hi.push(hi)
        e_owners.push([fi])
      } else {
        let owners = e_owners[found]
        let mut dup = false
        for o in owners {
          if o == fi {
            dup = true
          }
        }
        if !dup {
          owners.push(fi)
        }
      }
    }
  }
  // 2. 產生對偶邊
  let out : Array[DualEdge] = []
  for q in 0..<e_lo.length() {
    let owners = e_owners[q]
    let p = self.terms[e_lo[q]]
    let t2 = self.terms[e_hi[q]]
    let v = Pt2::new(t2.i - p.i, t2.j - p.j)
    let base = v.rot90().prim()
    let fa = owners[0]
    let fb = if owners.length() > 1 { owners[1] } else { -1 }
    // 方向：由 face_a 的重心指向外
    let (cx, cy) = face_centroid(self, faces[fa])
    let mx = p.i.to_double() + v.x.to_double() / 2.0
    let my = p.j.to_double() + v.y.to_double() / 2.0
    let dir = if base.x.to_double() * (mx - cx) + base.y.to_double() * (my - cy) <
      0.0 {
      Pt2::new(-base.x, -base.y)
    } else {
      base
    }
    out.push({
      face_a: fa,
      face_b: fb,
      from_term: e_lo[q],
      to_term: e_hi[q],
      dir,
      weight: v.lattice_len(),
    })
  }
  out
}

///|
/// 平衡條件檢查：對每個面（= 熱帶曲線的一個頂點）計算
///   Σ_{入射邊 e} weight_e · ν_e
/// 其中 ν_e 是由該面指向外的原始方向（對射線同樣成立）。
/// 回傳 `(面索引, 殘差 x, 殘差 y)`；全部 `(0,0)` 才滿足平衡條件。
///
/// 這個恆等式不是巧合：把每個面想成一個多邊形，邊界上每條邊貢獻
/// 「格長 × 外法向」，取和後由離散格林公式必為零。
/// 反過來說，如果細分或對偶有任何一步算錯（少了射線、法向定向反了、
/// 權重算錯），殘差就會立刻非零——所以這是一個真正的檢查。
pub fn balancing_residuals(
  edges : Array[DualEdge],
  nfaces : Int32,
) -> Array[(Int32, Int64, Int64)] {
  let out : Array[(Int32, Int64, Int64)] = []
  for f in 0..<nfaces {
    let mut sx = 0L
    let mut sy = 0L
    for e in edges {
      if e.face_a == f {
        sx = sx + e.weight.to_int64() * e.dir.x.to_int64()
        sy = sy + e.weight.to_int64() * e.dir.y.to_int64()
      } else if e.face_b == f {
        sx = sx - e.weight.to_int64() * e.dir.x.to_int64()
        sy = sy - e.weight.to_int64() * e.dir.y.to_int64()
      }
    }
    out.push((f, sx, sy))
  }
  out
}

///|
/// 細分的面積總和（各面多邊形面積兩倍之和）。
pub fn BPoly::subdivision_area2(self : BPoly, faces : Array[Face]) -> Int64 {
  let mut s = 0L
  for f in faces {
    s = s + self.face_area2(f)
  }
  s
}

///|
/// 對偶性檢查（精確版）：對每個面 F，用其法向 `(nx,ny,nz)` 當作熱帶方向，
/// 求 `min_a (nz·c_a + nx·i_a + ny·j_a)` 的 argmin，應該**恰好**是 F 的成員集合。
///
/// 通過 ⇒ F 是法扇的一個格，而且該格對應熱帶超曲面上的一個頂點
/// （在該方向至少有 |F| ≥ 3 個單項式同時達到最小值）。
pub fn BPoly::check_duality(
  self : BPoly,
  faces : Array[Face],
) -> (Int32, Int32) {
  let mut ok = 0
  let mut bad = 0
  for f in faces {
    let got = self.minima_scaled(f.plane.nx, f.plane.ny, f.plane.nz)
    if same_index_set(got, f.members) {
      ok = ok + 1
    } else {
      bad = bad + 1
    }
  }
  (ok, bad)
}

///|
fn same_index_set(a : Array[Int32], b : Array[Int32]) -> Bool {
  if a.length() != b.length() {
    return false
  }
  for i in 0..<a.length() {
    let mut found = false
    for j in 0..<b.length() {
      if a[i] == b[j] {
        found = true
        break
      }
    }
    if !found {
      return false
    }
  }
  true
}

///|
/// 抽樣檢查：對隨機整數方向 `w`，若 `|argmin| ≥ 2`（即在熱帶曲線上），
/// 則該 argmin 必須是某個面成員集合的子集（即落在細分的某個閉面上）。
///
/// 這是對偶定理的獨立取樣驗證：任何「多於一個單項式打平」的方向，
/// 都必須被細分中的某個面所解釋，不會有額外的打平方向。
pub fn BPoly::check_ties_on_faces(
  self : BPoly,
  faces : Array[Face],
  samples : Int32,
  seed : UInt64,
) -> (Int32, Int32, Int32) {
  let rng = @alg.Rng::new(seed)
  let mut ties = 0
  let mut explained = 0
  let mut unexplained = 0
  for _ in 0..<samples {
    let wx = rng.range(-40, 40)
    let wy = rng.range(-40, 40)
    let got = self.minima_scaled(wx.to_int64(), wy.to_int64(), 1L)
    if got.length() < 2 {
      continue
    }
    ties = ties + 1
    let mut hit = false
    for f in faces {
      let mut subset = true
      for g in got {
        let mut in_face = false
        for m in f.members {
          if g == m {
            in_face = true
            break
          }
        }
        if !in_face {
          subset = false
          break
        }
      }
      if subset {
        hit = true
        break
      }
    }
    if hit {
      explained = explained + 1
    } else {
      unexplained = unexplained + 1
    }
  }
  (ties, explained, unexplained)
}
