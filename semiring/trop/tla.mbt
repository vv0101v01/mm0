// ===========================================================================
// 熱帶幾何 III：熱帶線性代數（熱帶行列式 = 最佳指派）
//
// 熱帶行列式（min-plus 版）：
//     tropdet(A) = min_{σ ∈ S_n} Σ_i A[i][σ(i)]
//
// 這個定義本身是 O(n!)；但它同時也是**最小成本完美匹配**的問題，
// 因此可用匈牙利演算法的 O(n³) 版本計算。這是一個典型的
// 「代數定義 → 組合演算法」的推導：
//
//   熱帶行列式  ≡  指派問題  ≡  匈牙利演算法
//
// 本檔案提供三個**獨立**實作，互相對照：
//   * `trop_det`            匈牙利 O(n³)
//   * `trop_det_dp`         子集 DP O(n·2ⁿ)（不用匈牙利，用位元遮罩）
//   * `trop_det_bruteforce` 直接列舉 n!（只用於 n ≤ 8 的對照）
//
// 另外提供 `trop_det_tie_count`：達到最小值的排列個數。
// 熱帶幾何的用語是「矩陣是否熱帶奇異」——最小值被**多於一個**排列達成時，
// 對應的熱帶超曲面在此處不光滑（tropdet 的牛頓多面體在該方向上退化）。
// ===========================================================================

///|
/// 內部哨兵（比任何合法成本都大，且相加不會溢位）。
fn tla_inf() -> Int64 {
  1_000_000_000_000_000_000L
}

///|
/// 匈牙利演算法（最小成本完美匹配），O(n³)。
///
/// 前提：`a` 是 n×n、元素有限（`+∞` 條目請先以足夠大的有限值代替）。
/// 回傳最小總成本；同時可取得指派（見 `trop_assignment`）。
fn hungarian(
  a : Array[Array[Int64]],
  want_perm : Bool,
) -> (Int64, Array[Int32]) {
  let n = a.length()
  let inf = tla_inf()
  let u : Array[Int64] = Array::make(n + 1, 0L)
  let v : Array[Int64] = Array::make(n + 1, 0L)
  let p : Array[Int32] = Array::make(n + 1, 0)
  let way : Array[Int32] = Array::make(n + 1, 0)
  let mut i = 1
  while i <= n {
    p[0] = i
    let mut j0 = 0
    let minv : Array[Int64] = Array::make(n + 1, inf)
    let used : Array[Bool] = Array::make(n + 1, false)
    let mut alive = true
    while alive {
      used[j0] = true
      let i0 = p[j0]
      let mut delta = inf
      let mut j1 = 0
      let mut j = 1
      while j <= n {
        if !used[j] {
          let cur = a[i0 - 1][j - 1] - u[i0] - v[j]
          if cur < minv[j] {
            minv[j] = cur
            way[j] = j0
          }
          if minv[j] < delta {
            delta = minv[j]
            j1 = j
          }
        }
        j = j + 1
      }
      let mut k = 0
      while k <= n {
        if used[k] {
          u[p[k]] = u[p[k]] + delta
          v[k] = v[k] - delta
        } else {
          minv[k] = minv[k] - delta
        }
        k = k + 1
      }
      j0 = j1
      if p[j0] == 0 {
        alive = false
      }
    }
    // 沿交替路回推
    let mut run = true
    while run {
      let j1 = way[j0]
      p[j0] = p[j1]
      j0 = j1
      if j0 == 0 {
        run = false
      }
    }
    i = i + 1
  }
  let perm : Array[Int32] = Array::make(n, 0)
  if want_perm {
    let mut j = 1
    while j <= n {
      perm[p[j] - 1] = j - 1
      j = j + 1
    }
  }
  (-v[0], perm)
}

///|
/// 熱帶行列式：`min_σ Σ_i A[i][σ(i)]`，以匈牙利演算法 O(n³) 計算。
pub fn trop_det(a : Array[Array[Int64]]) -> Int64 {
  let (cost, _) = hungarian(a, false)
  cost
}

///|
/// 熱帶行列式 + 達到最小值的排列（一個 witness）。
pub fn trop_assignment(a : Array[Array[Int64]]) -> (Int64, Array[Int32]) {
  hungarian(a, true)
}

///|
/// 子集 DP 版本：`dp[mask] = 已用掉 mask 這些欄位、處理完前 popcount(mask) 列`的最小成本。
/// O(n·2ⁿ)，n ≤ 20 實用。與匈牙利演算法完全獨立。
pub fn trop_det_dp(a : Array[Array[Int64]]) -> Int64 {
  let n = a.length()
  if n == 0 {
    return 0L
  }
  if n > 22 {
    abort("trop_det_dp: n 太大（2^n 記憶體），請用 trop_det")
  }
  let size = 1 << n
  let inf = tla_inf()
  let dp : Array[Int64] = Array::make(size, inf)
  dp[0] = 0L
  let mut mask = 0
  while mask < size {
    if dp[mask] < inf {
      let row = popcount32(mask)
      if row < n {
        let mut j = 0
        while j < n {
          let bit = 1 << j
          if (mask & bit) == 0 {
            let cand = dp[mask] + a[row][j]
            if cand < dp[mask | bit] {
              dp[mask | bit] = cand
            }
          }
          j = j + 1
        }
      }
    }
    mask = mask + 1
  }
  dp[size - 1]
}

///|
/// 位元計數。
fn popcount32(x : Int32) -> Int32 {
  let mut v = x
  let mut c = 0
  while v != 0 {
    v = v & (v - 1)
    c = c + 1
  }
  c
}

///|
/// 全排列遞迴（box 存放目前最小值）。
fn perm_walk(
  a : Array[Array[Int64]],
  n : Int32,
  row : Int32,
  used : Array[Bool],
  acc : Int64,
  best : Array[Int64],
) -> Unit {
  if row == n {
    if acc < best[0] {
      best[0] = acc
    }
    return
  }
  for j in 0..<n {
    if !used[j] {
      used[j] = true
      perm_walk(a, n, row + 1, used, acc + a[row][j], best)
      used[j] = false
    }
  }
}

///|
/// 暴力列舉所有排列（n ≤ 8）。純對照用：不做任何剪枝，直接 n! 條路徑。
pub fn trop_det_bruteforce(a : Array[Array[Int64]]) -> Int64 {
  let n = a.length()
  if n == 0 {
    return 0L
  }
  if n > 8 {
    abort("trop_det_bruteforce: n ≤ 8")
  }
  let used : Array[Bool] = Array::make(n, false)
  let best : Array[Int64] = [tla_inf()]
  perm_walk(a, n, 0, used, 0L, best)
  best[0]
}

///|
/// 達到最小值的排列個數（「熱帶奇異」的判據：> 1 表示退化）。
///
/// 以子集 DP 同時計算「最小值」與「達到最小值的排列數」，O(n·2ⁿ)。
/// 用 Int64 計數（n ≤ 20 時 n! < 2.6e18 會接近上限，實務上用 n ≤ 12 對照）。
pub fn trop_det_tie_count(a : Array[Array[Int64]]) -> Int32 {
  let n = a.length()
  if n == 0 {
    return 1
  }
  if n > 20 {
    abort("trop_det_tie_count: n 太大")
  }
  let size = 1 << n
  let inf = tla_inf()
  let dp : Array[Int64] = Array::make(size, inf)
  let cnt : Array[Int32] = Array::make(size, 0)
  dp[0] = 0L
  cnt[0] = 1
  let mut mask = 0
  while mask < size {
    if dp[mask] < inf {
      let row = popcount32(mask)
      if row < n {
        let mut j = 0
        while j < n {
          let bit = 1 << j
          if (mask & bit) == 0 {
            let cand = dp[mask] + a[row][j]
            let m2 = mask | bit
            if cand < dp[m2] {
              dp[m2] = cand
              cnt[m2] = cnt[mask]
            } else if cand == dp[m2] {
              cnt[m2] = cnt[m2] + cnt[mask]
            }
          }
          j = j + 1
        }
      }
    }
    mask = mask + 1
  }
  cnt[size - 1]
}
