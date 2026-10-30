///| spec —— 譜化核心（spectral core）：把消元不變量升級為譜物件。

///|

///|  * `[S-D-charpoly]` F_p 上的特徵多項式（Faddeev–LeVerrier，精確）

///|    ＋ Cayley–Hamilton 的矩陣級驗證；

///|  * `[S-D-jacobi]` Double 循環 Jacobi 對稱特徵值解算器（譜化的數值引擎）；

///|  * `[S-D-flow]` 譜流：沿對稱矩陣路徑數零交叉；

///|  * `[S-D-susy]` 超對稱結構 Q（奇）、H = Q²（偶）：Witten 指標 = ind D，

///|    全部以 F_p 精確驗證（冪跡恆等式、特徵多項式關係、指標的形變不變性）。

///|

///| 本套件依賴 core（F_p 消元）——與 tensorlab 的單向依賴規則一致。

// ------------------------------------------------------------ F_p 譜論 ----

///| [S-D-charpoly] 特徵多項式 det(xI − A) 的係數 [c0..cn]（c_k 為 x^k 係數）。

///| 以 Newton 恆等式實作：p_k = tr(A^k)；k·e_k = Σ_{i=1..k} (−1)^{i−1} e_{k−i} p_i；

///|
/// c_k = (−1)^{n−k} e_{n−k}。精確 mod p（p > n 保證 k 可逆）。
pub fn charpoly(a : @core.Mat, p : Int32) -> Array[Int32] {
  let n = a.rows
  // p_k = tr(A^k)，k = 1..n
  let pows : Array[Int32] = [0] // pows[k] = tr(A^k)，索引 0 不用
  let mut cur = copy_mat(a)
  for k = 1; k <= n; k = k + 1 {
    if k > 1 {
      cur = @core.mat_mul(cur, a, p)
    }
    let mut tr = 0
    for i = 0; i < n; i = i + 1 {
      tr = (tr + cur.data[i * n + i]) % p
    }
    let _ = pows.push(tr)
  }
  // e_k（索引 0..n）
  let es : Array[Int32] = [1]
  for k = 1; k <= n; k = k + 1 {
    let mut acc = 0
    for i = 1; i <= k; i = i + 1 {
      let sign = if i % 2 == 1 { 1 } else { -1 }
      let term = es[k - i] * pows[i] % p * sign % p
      acc = (acc + term) % p
    }
    let ek = acc * @algebra.int_mod_inv(k, p) % p
    let _ = es.push((ek % p + p) % p)
  }
  // c_k = (−1)^{n−k} e_{n−k}
  let coeffs : Array[Int32] = []
  for k = 0; k <= n; k = k + 1 {
    let e = es[n - k]
    let c = if (n - k) % 2 == 0 { e } else { (p - e) % p }
    let _ = coeffs.push(c)
  }
  coeffs
}

///|
fn copy_mat(a : @core.Mat) -> @core.Mat {
  @core.mat_build(a.rows, a.cols, (i, j) => a.data[i * a.cols + j])
}

///|
fn diag_scale(c : Int32, n : Int32, p : Int32) -> @core.Mat {
  let m = @core.mat_make(n, n, 0)
  for i = 0; i < n; i = i + 1 {
    m.data[i * n + i] = (c % p + p) % p
  }
  m
}

///|
/// charpoly 的根 0 重數（第一個非零係數的下標；全零回傳 n+1 不該發生）。
pub fn root_zero_mult(cp : Array[Int32]) -> Int32 {
  for k = 0; k < cp.length(); k = k + 1 {
    if cp[k] != 0 {
      return k
    }
  }
  cp.length()
}

///|
/// [S-T-CayleyHamilton] 的檢驗器：p_A(A) ≡ 0 (mod p)？
pub fn check_cayley_hamilton(a : @core.Mat, p : Int32) -> Bool {
  let n = a.rows
  let cp = charpoly(a, p)
  // 由高次到低次 Horner 累積矩陣多項式
  let mut acc = @core.mat_make(n, n, 0)
  for k = cp.length() - 1; k >= 0; k = k - 1 {
    acc = @core.mat_mul(acc, a, p)
    acc = @core.mat_add(acc, diag_scale(cp[k], n, p), p)
  }
  @core.mat_is_zero(acc)
}

///|
/// 矩陣冪的跡（mod p）：tr(A^k)。
pub fn trace_pow(a : @core.Mat, k : Int32, p : Int32) -> Int32 {
  let n = a.rows
  let mut acc = @core.mat_identity(n)
  for i = 0; i < k; i = i + 1 {
    acc = @core.mat_mul(acc, a, p)
  }
  let mut tr = 0
  for i = 0; i < n; i = i + 1 {
    tr = (tr + acc.data[i * n + i]) % p
  }
  tr
}

///| [S-D-jacobi] 循環 Jacobi 對稱特徵值解算器。

///|
/// 回傳 (排序後特徵值, 對應特徵向量為行)。
pub fn jacobi_eigen(
  a_in : Array[Array[Double]],
) -> (Array[Double], Array[Array[Double]]) {
  let n = a_in.length()
  // 複製
  let a : Array[Array[Double]] = []
  for i = 0; i < n; i = i + 1 {
    let row : Array[Double] = Array::make(n, 0.0)
    for j = 0; j < n; j = j + 1 {
      row[j] = a_in[i][j]
    }
    let _ = a.push(row)
  }
  let v : Array[Array[Double]] = []
  for i = 0; i < n; i = i + 1 {
    let row : Array[Double] = Array::make(n, 0.0)
    row[i] = 1.0
    let _ = v.push(row)
  }
  let mut sweeps = 0
  let mut off = offdiag(a)
  while off > 0.00000000001 && sweeps < 60 {
    sweeps = sweeps + 1
    for pe = 0; pe < n - 1; pe = pe + 1 {
      for q = pe + 1; q < n; q = q + 1 {
        if a[pe][q].abs() > 0.00000000000001 {
          let theta = (a[q][q] - a[pe][pe]) / (2.0 * a[pe][q])
          let tsign = if theta >= 0.0 { 1.0 } else { -1.0 }
          let t = tsign / (theta.abs() + (theta * theta + 1.0).sqrt())
          let c = 1.0 / (t * t + 1.0).sqrt()
          let s = t * c
          // 旋轉 A 與 V
          for k = 0; k < n; k = k + 1 {
            let akp = a[k][pe]
            let akq = a[k][q]
            a[k][pe] = c * akp - s * akq
            a[k][q] = s * akp + c * akq
          }
          for k = 0; k < n; k = k + 1 {
            let apk = a[pe][k]
            let aqk = a[q][k]
            a[pe][k] = c * apk - s * aqk
            a[q][k] = s * apk + c * aqk
          }
          for k = 0; k < n; k = k + 1 {
            let vkp = v[k][pe]
            let vkq = v[k][q]
            v[k][pe] = c * vkp - s * vkq
            v[k][q] = s * vkp + c * vkq
          }
        }
      }
    }
    off = offdiag(a)
  }
  // 抽取特徵值並排序（連同特徵向量行）
  let vals : Array[Double] = []
  for i = 0; i < n; i = i + 1 {
    let _ = vals.push(a[i][i])
  }
  // 選擇排序
  for i = 0; i < n; i = i + 1 {
    for j = i + 1; j < n; j = j + 1 {
      if vals[j] < vals[i] {
        let tv = vals[i]
        vals[i] = vals[j]
        vals[j] = tv
        for k = 0; k < n; k = k + 1 {
          let tvv = v[k][i]
          v[k][i] = v[k][j]
          v[k][j] = tvv
        }
      }
    }
  }
  (vals, v)
}

///|
fn offdiag(a : Array[Array[Double]]) -> Double {
  let n = a.length()
  let mut s = 0.0
  for i = 0; i < n; i = i + 1 {
    for j = 0; j < n; j = j + 1 {
      if i != j {
        s = s + a[i][j] * a[i][j]
      }
    }
  }
  s.sqrt()
}

///|
/// 行列式的符號（經特徵值乘積；對稱矩陣適用）：回傳 −1/0/+1。
pub fn det_sign(a : Array[Array[Double]]) -> Int32 {
  let (vals, _) = jacobi_eigen(a)
  let mut sgn = 1
  for v in vals {
    if v.abs() < 0.000000001 {
      return 0
    }
    if v < 0.0 {
      sgn = -sgn
    }
  }
  sgn
}

///| [S-D-flow] 譜流：沿 H(t) = (1−t)H₀ + tH₁（對稱）數特徵值分支的零交叉（帶號）。

///|
/// 排序特徵值曲線連續，故按排序索引配對分支；以死區（|λ|≤ε）追蹤
///「最後非零符號」——精確落在 0 的樣本不影響計數。
pub fn spectral_flow(
  h0 : Array[Array[Double]],
  h1 : Array[Array[Double]],
  samples : Int32,
) -> Int32 {
  let n = h0.length()
  let eps = 0.0000001
  let (prev, _) = jacobi_eigen(h0)
  // last_sign[i]：第 i 分支最後一次離開死區的符號（0 表示尚未離開）
  let last_sign : Array[Int32] = Array::make(n, 0)
  let mut flow = 0
  for i = 0; i < n; i = i + 1 {
    if prev[i] > eps {
      last_sign[i] = 1
    }
    if prev[i] < -eps {
      last_sign[i] = -1
    }
  }
  for s = 1; s <= samples; s = s + 1 {
    let t = s.to_double() / samples.to_double()
    let ht : Array[Array[Double]] = []
    for i = 0; i < n; i = i + 1 {
      let row : Array[Double] = Array::make(n, 0.0)
      for j = 0; j < n; j = j + 1 {
        row[j] = (1.0 - t) * h0[i][j] + t * h1[i][j]
      }
      let _ = ht.push(row)
    }
    let (cur, _) = jacobi_eigen(ht)
    for i = 0; i < n; i = i + 1 {
      let v = cur[i]
      if v > eps {
        if last_sign[i] == -1 {
          flow = flow + 1
        }
        last_sign[i] = 1
      }
      if v < -eps {
        if last_sign[i] == 1 {
          flow = flow - 1
        }
        last_sign[i] = -1
      }
      // 死區內不更新
    }
    for i = 0; i < n; i = i + 1 {
      prev[i] = cur[i]
    }
  }
  flow
}

///|
/// [S-C-SuperFlow] 超譜流 = 偶方塊流 − 奇方塊流。
pub fn spectral_flow_super(
  a0 : Array[Array[Double]],
  a1 : Array[Array[Double]],
  d0 : Array[Array[Double]],
  d1 : Array[Array[Double]],
  samples : Int32,
) -> Int32 {
  spectral_flow(a0, a1, samples) - spectral_flow(d0, d1, samples)
}

// ------------------------------------------------------- 超對稱 / Witten ---

///| [S-D-susy] 超對稱結構：D : V₀ → V₁（n×m 矩陣 over F_p），

///| Q = [[0, Dᵀ],[D, 0]]（奇），H = Q² = diag(DDᵀ, DᵀD)（偶）。

///|
/// Witten 指標 = dim ker D − dim ker Dᵀ（= m − n，與 D 無關）。
pub struct Susy {
  d : @core.Mat // n×m
  p : Int32
}

///|
pub fn susy_of(d : @core.Mat, p : Int32) -> Susy {
  Susy::{ d, p, }
}

///|
/// H 的偶方塊（m×m）：DDᵀ。
pub fn susy_he(s : Susy) -> @core.Mat {
  @core.mat_mul(s.d, @core.mat_transpose(s.d), s.p)
}

///|
/// H 的奇方塊（n×n）：DᵀD。
pub fn susy_ho(s : Susy) -> @core.Mat {
  @core.mat_mul(@core.mat_transpose(s.d), s.d, s.p)
}

///|
/// 分階冪跡差：str(H^k) = tr((DDᵀ)^k) − tr((DᵀD)^k) (mod p)。
pub fn susy_str_pow(s : Susy, k : Int32) -> Int32 {
  let te = trace_pow(susy_he(s), k, s.p)
  let to = trace_pow(susy_ho(s), k, s.p)
  ((te - to) % s.p + s.p) % s.p
}

///|
/// Witten 指標（精確）：nullity(D) − nullity(Dᵀ)。
pub fn susy_index(s : Susy) -> Int32 {
  let f = @core.mk_field(s.p)
  let rank_d = @core.rank_mod(s.d, f)
  let m = s.d.cols
  let n = s.d.rows
  m - rank_d - (n - rank_d)
}

///|
/// 核維數對（供「跳動 vs 不變」實驗）。
pub fn susy_kernel_dims(s : Susy) -> (Int32, Int32) {
  let f = @core.mk_field(s.p)
  let rank_d = @core.rank_mod(s.d, f)
  let m = s.d.cols
  let n = s.d.rows
  (m - rank_d, n - rank_d)
}

///| [S-T-ChPolyRel] 檢驗器：det(xI_n − DDᵀ) = x^{n−m} det(xI_m − DᵀD)（n ≥ m）。

///|
/// （DDᵀ 是 n×n、DᵀD 是 m×m——維度以矩陣本身為準。）
pub fn check_chpoly_rel(s : Susy) -> Bool {
  let cpe = charpoly(susy_he(s), s.p) // det(xI_n − DDᵀ)：n+1 個係數
  let cpo = charpoly(susy_ho(s), s.p) // det(xI_m − DᵀD)：m+1 個係數
  let de = cpe.length() - 1 // n
  let dco = cpo.length() - 1 // m
  let cbig : Array[Int32] = if de >= dco { cpe } else { cpo }
  let csmall : Array[Int32] = if de >= dco { cpo } else { cpe }
  let big = if de >= dco { de } else { dco }
  let small = if de >= dco { dco } else { de }
  let diff = big - small
  for k = 0; k < diff; k = k + 1 {
    if cbig[k] != 0 {
      return false
    }
  }
  for k = 0; k <= small; k = k + 1 {
    if cbig[k + diff] != csmall[k] {
      return false
    }
  }
  true
}
