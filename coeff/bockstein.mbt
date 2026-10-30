///| ## Bockstein：讓撓率的**階**在係數環上「顯形」
///

///| 短正合列 `0 → ℤ/p →^{×p} ℤ/p² → ℤ/p → 0` 給出長正合列，其連接映射

///| β: `H_k(C; ℤ/p) → H_{k−1}(C; ℤ/p)` 就是（同調版）Bockstein。
///

///| 演算法（完全是整數算術，可精確驗證）：

///|   給定模 p 的圈 `z`（係數取 `0..p−1` 的代表），把它當成 ℤ/p² 上的鏈 `z̃`；

///|   `∂z̃` 的每一項都被 p 整除（因為 `z` 是模 p 的圈），於是

///|   `β(z) := ∂z̃ / p  mod p`  是 `C_{k−1}` 中的模 p 圈。

///| 良定義性：換提升 `z̃ + p·u` 只把 `β(z)` 改變 `∂u`，即相差一個邊界。
///

///| 這個映射把「`H_{k−1}` 中的撓率」變成「`H_k` 上的一個算子」，

///| 所以它是本輪「係數環」主軸的算術核心：

///| **秩看不見撓率，秩只看得見自由部分；Bockstein 看得見撓率。**

///| 把模 p 向量 `z`（`C_k` 的座標）提升到 ℤ/p² 後的邊界除以 p，再模 p。

///|
/// 回傳 `C_{k−1}` 上的模 p 鏈（未必是邊界，但必定是圈）。
pub fn bockstein_of_cycle(
  cx : ChainComplex,
  p : Int32,
  k : Int32,
  z : Array[Int32],
) -> Array[Int32] {
  let d = cc_boundary(cx, k)
  let rows = if d.length() > 0 && d[0].length() > 0 {
    d.length()
  } else {
    cx.cells[k - 1]
  }
  let out = Array::make(rows, 0)
  if d.length() == 0 || d[0].length() == 0 {
    return out
  }
  for i = 0; i < d.length(); i = i + 1 {
    let mut acc : Int32 = 0
    for j = 0; j < d[i].length(); j = j + 1 {
      acc = acc + d[i][j] * z[j]
    }
    // acc 必被 p 整除
    out[i] = (acc / p % p + p) % p
  }
  out
}

///|
/// 一個模 p 圈 basis 向量在 Bockstein 下的像是否為**非零同調類**。
pub fn bockstein_nontrivial(
  cx : ChainComplex,
  p : Int32,
  k : Int32,
  z : Array[Int32],
) -> Bool {
  let beta = bockstein_of_cycle(cx, p, k, z)
  let mut nonzero = false
  for x in beta {
    if x % p != 0 {
      nonzero = true
    }
  }
  if !nonzero {
    return false
  }
  // β(z) 必須是圈（∂_{k−1} β(z) ≡ 0 mod p）
  let dm = cc_boundary(cx, k - 1)
  if dm.length() > 0 && dm[0].length() > 0 {
    for i = 0; i < dm.length(); i = i + 1 {
      let mut acc : Int32 = 0
      for j = 0; j < dm[i].length(); j = j + 1 {
        acc = acc + dm[i][j] * beta[j]
      }
      if acc % p != 0 {
        return false
      }
    }
  }
  // 是否為邊界（在 im ∂_k 中）
  !in_image_fp(cc_boundary(cx, k), beta, p)
}

///|
/// `F_p` 上 `v` 是否落在 `m` 的行空間（用秩比較，不用求逆）。
pub fn in_image_fp(
  m : Array[Array[Int32]],
  v : Array[Int32],
  p : Int32,
) -> Bool {
  if m.length() == 0 || m[0].length() == 0 {
    for x in v {
      if x % p != 0 {
        return false
      }
    }
    return true
  }
  let aug : Array[Array[Int32]] = []
  for i = 0; i < m.length(); i = i + 1 {
    let row : Array[Int32] = []
    for x in m[i] {
      row.push(x)
    }
    row.push(v[i])
    aug.push(row)
  }
  rank_fp(m, p) == rank_fp(aug, p)
}

///| Bockstein 在整維度上的總效果：`H_k` 的模 p 圈中，

///|
/// 有多少個獨立類的 β 非零（= 該維度上「階恰好為 p 的可分性障礙」的秩）。
pub struct BocksteinReport {
  p : Int32
  k : Int32
  dim_cycles : Int32
  dim_cycles_with_beta : Int32
  witness : Array[Int32]
}

///|
pub fn bockstein_report(
  cx : ChainComplex,
  p : Int32,
  k : Int32,
) -> BocksteinReport {
  let fld = @core.mk_field(p)
  let dm = cc_boundary(cx, k)
  let nk = cx.cells[k]
  let mut basis : Array[Array[Int32]] = []
  if dm.length() > 0 && dm[0].length() > 0 {
    basis = @core.nullspace_basis(@core.mat_from_rows(dm), fld)
  } else {
    for i = 0; i < nk; i = i + 1 {
      let e = Array::make(nk, 0)
      e[i] = 1
      basis.push(e)
    }
  }
  // 以 β 的像的秩（模掉邊界）計數
  let boundary_cols : Array[Array[Int32]] = []
  let dk = cc_boundary(cx, k)
  if dk.length() > 0 && dk[0].length() > 0 {
    for j = 0; j < dk[0].length(); j = j + 1 {
      let col : Array[Int32] = []
      for i = 0; i < dk.length(); i = i + 1 {
        col.push((dk[i][j] % p + p) % p)
      }
      boundary_cols.push(col)
    }
  }
  let mut witness : Array[Int32] = []
  let mut r = 0
  let is_cycle : Array[Array[Int32]] = []
  for z in basis {
    let beta = bockstein_of_cycle(cx, p, k, z)
    let mut nz = false
    for x in beta {
      if x % p != 0 {
        nz = true
      }
    }
    if nz {
      is_cycle.push(beta)
    }
  }
  // 兩者都住在 C_{k−1} = F_p^{n}：直接以「向量為列」建矩陣求張成維數
  let all_rows : Array[Array[Int32]] = []
  for row in boundary_cols {
    all_rows.push(row)
  }
  for row in is_cycle {
    all_rows.push(row)
  }
  let r0 = rank_fp(boundary_cols, p)
  let r1 = rank_fp(all_rows, p)
  r = r1 - r0
  if is_cycle.length() > 0 {
    witness = is_cycle[0]
  }
  BocksteinReport::{
    p,
    k,
    dim_cycles: basis.length(),
    dim_cycles_with_beta: r,
    witness,
  }
}
