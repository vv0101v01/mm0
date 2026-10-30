///| ## 杯積：同調看不見、上同調看得見
///

///| 上一輪留下的殘餘：`T²` 與 `S¹∨S¹∨S²` **同調完全相同**卻不同倫，

///| 所以「把高階同倫化約成同調」這條路線到此為止。本檔案把那條殘餘收掉：

///| Alexander–Whitney 杯積在 `F₂` 上把兩者分開。
///

///| 為什麼這件事屬於「係數環」主軸：杯積在 ℚ 與 `F_p` 上是不同的環

///|（`H^*(T²;ℚ)` 是外代數、`H^*(T²;F₂)` 是 `F₂[α,β]/(α²,β²)`），

///| 而**符號**只在 ℤ 係數下才存在 —— 換環不只換「看得見甚麼」，還換「乘起來是甚麼」。

///| 模 2 的上邊界矩陣 `δ^k: C^k → C^{k+1}`：列 = (k+1)-面，行 = k-面，

///|
/// 由「面是餘面的子面」決定（`F₂` 上符號消失）。
pub fn coboundary_f2(sx : Simplex, k : Int32) -> Array[Array[Int32]] {
  let low = sx.faces[k]
  let high = sx.faces[k + 1]
  let rows : Array[Array[Int32]] = []
  for f in high {
    let row = Array::make(low.length(), 0)
    for skip = 0; skip < f.length(); skip = skip + 1 {
      let sub : Array[Int32] = []
      for i = 0; i < f.length(); i = i + 1 {
        if i != skip {
          sub.push(f[i])
        }
      }
      for j = 0; j < low.length(); j = j + 1 {
        if @algebra.int_vec_eq(low[j], sub) {
          row[j] = 1
        }
      }
    }
    rows.push(row)
  }
  rows
}

///|
/// 面在該維面表中的索引；不存在回 −1。
pub fn face_index(sx : Simplex, dim : Int32, sub : Array[Int32]) -> Int32 {
  if dim < 0 || dim >= sx.faces.length() {
    return -1
  }
  let table = sx.faces[dim]
  for i = 0; i < table.length(); i = i + 1 {
    if @algebra.int_vec_eq(table[i], sub) {
      return i
    }
  }
  -1
}

///| Alexander–Whitney 杯積（`F₂`）：

///|
/// `(a ⌣ b)(σ) = a(σ|_{v₀..v_p}) · b(σ|_{v_p..v_{p+q}})`。
pub fn cup_f2(
  sx : Simplex,
  pdeg : Int32,
  a : Array[Int32],
  qdeg : Int32,
  b : Array[Int32],
) -> Array[Int32] {
  let top = pdeg + qdeg
  let out = Array::make(sx.faces[top].length(), 0)
  let cells = sx.faces[top]
  for i = 0; i < cells.length(); i = i + 1 {
    let sig = cells[i]
    let front : Array[Int32] = []
    for t = 0; t <= pdeg; t = t + 1 {
      front.push(sig[t])
    }
    let back : Array[Int32] = []
    for t = pdeg; t <= top; t = t + 1 {
      back.push(sig[t])
    }
    let ia = face_index(sx, pdeg, front)
    let ib = face_index(sx, qdeg, back)
    if ia >= 0 && ib >= 0 {
      out[i] = a[ia] * b[ib] % 2
    }
  }
  out
}

///|
/// `δ c`（模 2）。
pub fn delta_f2(sx : Simplex, k : Int32, c : Array[Int32]) -> Array[Int32] {
  let m = coboundary_f2(sx, k)
  let out = Array::make(m.length(), 0)
  for i = 0; i < m.length(); i = i + 1 {
    let mut acc : Int32 = 0
    for j = 0; j < m[i].length(); j = j + 1 {
      acc = acc + m[i][j] * c[j]
    }
    out[i] = acc % 2
  }
  out
}

///|
/// `c` 是否為 `k`-餘圈。
pub fn is_cocycle_f2(sx : Simplex, k : Int32, c : Array[Int32]) -> Bool {
  if k + 1 > simplex_top(sx) {
    return true
  }
  let d = delta_f2(sx, k, c)
  for x in d {
    if x % 2 != 0 {
      return false
    }
  }
  true
}

///|
/// `k`-餘圈 `c` 是否代表**非零**上同調類（即不是 `(k−1)`-上邊界）。
pub fn is_nontrivial_class_f2(
  sx : Simplex,
  k : Int32,
  c : Array[Int32],
) -> Bool {
  if k == 0 {
    // H^0 非零 ⟺ c 有非零分量（且為餘圈）
    for x in c {
      if x % 2 != 0 {
        return true
      }
    }
    return false
  }
  let m = coboundary_f2(sx, k - 1)
  if m.length() == 0 || m[0].length() == 0 {
    for x in c {
      if x % 2 != 0 {
        return true
      }
    }
    return false
  }
  !in_image_f2(m, c)
}

///|
fn in_image_f2(m : Array[Array[Int32]], v : Array[Int32]) -> Bool {
  let aug : Array[Array[Int32]] = []
  for i = 0; i < m.length(); i = i + 1 {
    let row : Array[Int32] = []
    for x in m[i] {
      row.push(x)
    }
    row.push(v[i])
    aug.push(row)
  }
  rank_f2(m) == rank_f2(aug)
}

///|
fn rank_f2(m : Array[Array[Int32]]) -> Int32 {
  if m.length() == 0 || m[0].length() == 0 {
    return 0
  }
  rank_fp(m, 2)
}

///|
/// 上同調的一個可乘結構摘要。
pub struct CupReport {
  name : String
  h1_dim : Int32
  h2_dim : Int32
  nonzero_cup : Int32
  witness : String
}

///| 對 `H¹ × H¹ → H²` 做完整掃描：取 `Z¹` 的基底，逐對做杯積，

///|
/// 判定是否非零上同調類。
pub fn cup_scan(sx : Simplex, name : String) -> CupReport {
  let z1 = nullspace_f2(sx, 1)
  let z2_dim = if simplex_top(sx) >= 2 {
    let z2 = nullspace_f2(sx, 2)
    let b2 = rank_f2(coboundary_f2(sx, 1))
    z2.length() - b2
  } else {
    0
  }
  let mut count : Int32 = 0
  let mut wit = ""
  for i = 0; i < z1.length(); i = i + 1 {
    for j = i; j < z1.length(); j = j + 1 {
      let c = cup_f2(sx, 1, z1[i], 1, z1[j])
      if is_nontrivial_class_f2(sx, 2, c) {
        count = count + 1
        if wit == "" {
          wit = "([z\{i}]∪[z\{j}]) ≠ 0 in H^2"
        }
      }
    }
  }
  CupReport::{
    name,
    h1_dim: z1.length() - rank_f2(coboundary_f2(sx, 0)),
    h2_dim: z2_dim,
    nonzero_cup: count,
    witness: wit,
  }
}

///|
/// `k`-餘圈空間的基底（`F₂`）。
pub fn nullspace_f2(sx : Simplex, k : Int32) -> Array[Array[Int32]] {
  if k + 1 > simplex_top(sx) {
    // 最高維餘圈 = 全部餘鏈
    let n = sx.faces[k].length()
    let out : Array[Array[Int32]] = []
    for i = 0; i < n; i = i + 1 {
      let e = Array::make(n, 0)
      e[i] = 1
      out.push(e)
    }
    return out
  }
  let m = coboundary_f2(sx, k)
  if m.length() == 0 || m[0].length() == 0 {
    let n = sx.faces[k].length()
    let out : Array[Array[Int32]] = []
    for i = 0; i < n; i = i + 1 {
      let e = Array::make(n, 0)
      e[i] = 1
      out.push(e)
    }
    return out
  }
  @core.nullspace_basis(@core.mat_from_rows(m), @core.mk_field(2))
}
