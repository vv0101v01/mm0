// ===========================================================================
// 範疇化 I：集合值矩陣與自由範疇
//
// 範疇化的具體內容，在矩陣這一層可以寫得非常明確：
//
//   數字 a          ↦  集合 A（「a 的見證」）
//   加 a + b        ↦  不交併 A ⊔ B          （基數相加）
//   乘 a · b        ↦  笛卡兒積 A × B        （基數相乘）
//   矩陣 (M[i][j])  ↦  每一格是一個集合 M[i][j]
//
// 而「解範疇化（decategorification）」= 取基數：|A ⊔ B| = |A| + |B|、
// |A × B| = |A| · |B|。換句話說 **基數是從集合半環到 ℕ 半環的半環同態**。
// 這不是裝飾：它保證了「先在範疇層算、再取基數」與「先取基數、再用半環算」
// 這兩條路徑必然得到同一個答案——本檔的測試就是逐一比對這兩條路。
//
// 更有內容的例子是**自由範疇**：
//   圖 G 的自由範疇 Hom(i,j) = 從 i 到 j 的所有路徑（含長度 0 的那條）。
//   它的基數 |Hom(i,j)| 正是計數半環 ℕ 上 (I ⊕ A ⊕ A² ⊕ …)[i][j]
//   也就是 ℕ-半環的 Kleene 星 A*。
// 於是「自由範疇的存在 ⇒ 星在 ℕ 上可算（對 DAG）」變成一個可驗證的等式，
// 而且有三條獨立路徑可以互相對照（見 free.mbt / 測試）。
// ===========================================================================

///|
/// 集合值矩陣（「範疇化的矩陣」）：每一格是一組見證。
///
/// 見證用 `Array[Int32]` 表示（在這裡就是路徑的標籤序列），
/// 所以「這一格有幾個元素」是集合的基數，而不是半環收縮後的一個數。
pub(all) struct SetMat {
  rows : Int32
  cols : Int32
  /// 大小 rows*cols 的格子，每格是見證清單
  cells : Array[Array[Array[Int32]]]
}

///|
pub fn SetMat::new(rows : Int32, cols : Int32) -> SetMat {
  let cells : Array[Array[Array[Int32]]] = []
  for _ in 0..<(rows * cols) {
    cells.push([])
  }
  { rows, cols, cells, }
}

///|
pub fn SetMat::get(self : SetMat, i : Int32, j : Int32) -> Array[Array[Int32]] {
  self.cells[i * self.cols + j]
}

///|
/// 把一個見證加入 (i,j)。
pub fn SetMat::add(
  self : SetMat,
  i : Int32,
  j : Int32,
  w : Array[Int32],
) -> Unit {
  self.cells[i * self.cols + j].push(w)
}

///|
/// 範疇化的乘法：`(A ⊗ B)[i][j] = ⊔_k A[i][k] × B[k][j]`。
///
/// 見證是**串接**：`u ++ v`。這一點很重要——乘積的基數是乘積，
/// 而串接正好保留了「兩段路徑相接」的結構資訊。
pub fn smat_mul(a : SetMat, b : SetMat) -> SetMat {
  if a.cols != b.rows {
    abort("smat_mul: shape mismatch")
  }
  let out = SetMat::new(a.rows, b.cols)
  for i in 0..<a.rows {
    for k in 0..<a.cols {
      let left = a.get(i, k)
      if left.length() == 0 {
        continue
      }
      for j in 0..<b.cols {
        let right = b.get(k, j)
        if right.length() == 0 {
          continue
        }
        for u in left {
          for v in right {
            let w : Array[Int32] = []
            for x in u {
              w.push(x)
            }
            for x in v {
              w.push(x)
            }
            out.add(i, j, w)
          }
        }
      }
    }
  }
  out
}

///|
/// 範疇化的加法：不交併（基數相加）。
pub fn smat_plus(a : SetMat, b : SetMat) -> SetMat {
  if a.rows != b.rows || a.cols != b.cols {
    abort("smat_plus: shape mismatch")
  }
  let out = SetMat::new(a.rows, a.cols)
  for i in 0..<a.rows {
    for j in 0..<a.cols {
      for w in a.get(i, j) {
        out.add(i, j, w)
      }
      for w in b.get(i, j) {
        out.add(i, j, w)
      }
    }
  }
  out
}

///|
/// 解範疇化：取基數，得到 ℕ 上的矩陣（以 `Counting` 表示）。
pub fn decategorify(m : SetMat) -> @mat.Mat[@alg.Counting] {
  let out = @mat.Mat::zero(m.rows, m.cols)
  for i in 0..<m.rows {
    for j in 0..<m.cols {
      let k = m.get(i, j).length()
      if k > 0 {
        out.set(i, j, @alg.Counting::new(k.to_int64()))
      }
    }
  }
  out
}

///|
/// 兩條路徑是否為同一個見證（用於偵測重複計數）。
pub fn witness_equal(a : Array[Int32], b : Array[Int32]) -> Bool {
  if a.length() != b.length() {
    return false
  }
  for i in 0..<a.length() {
    if a[i] != b[i] {
      return false
    }
  }
  true
}

///|
/// 見證清單去重後的大小（若 `smat_mul` 產生重複，這裡會抓出來）。
pub fn distinct_witnesses(ws : Array[Array[Int32]]) -> Int32 {
  let uniq : Array[Array[Int32]] = []
  for w in ws {
    let mut seen = false
    for u in uniq {
      if witness_equal(u, w) {
        seen = true
        break
      }
    }
    if !seen {
      uniq.push(w)
    }
  }
  uniq.length()
}
