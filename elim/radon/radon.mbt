///| ## radon —— 有限場上的離散拉東變換（Radon field / transform）

///|

///| 空間 X = Z_n²（n 為素數），函數 f : X → F_p；直線 ℓ = {x : <u,x> = t}。

///|   R f(u,t) = Σ_{x : <u,x> = t} f(x)，u ∈ 方向集（斜率 m ∈ Z_n 加竖直方向）。

///| 本模块把 R 寫成矩陣（|X|² 行 × |X| 列），因此秩、像、核、反演全部由

///| `@core` 的消元引擎算出，並驗證下列定理：

///|   [T-Radon-Gram]  RᵀR = n·I + J（任意兩點恰決定一條線）；

///|   [T-Radon-Inj]   p ∤ n(n+1) 時 R 單射（故離散拉東變換可反演）；

///|   [T-Radon-Inv]   (n·I + J)^{-1} = (1/n)·(I − J/(n+1))，給出顯式反演公式；

///|   [T-Radon-Slice] 切片定理：F_1(Rf)(u,·) = F_2(f)|_{垂直於 u 的直線}（用 F_p 中的 n 次根實現）。
// ---- 資料結構 ----

///|
/// [D-Radon] 參數：n = 網格邊長（素數），p = 特徵（需 p ≫ n，且 p ≠ n）。
pub struct Radon {
  n : Int32
  p : Int32
  /// 方向數 = n+1：前 n 個為斜率 m（點 (x,y) 滿足 y = m·x + t），最後一個為豎直線 x = t。
  dirs : Int32
}

///|
pub fn mk_radon(n : Int32, p : Int32) -> Radon {
  Radon::{ n, p, dirs: n + 1, }
}

///|
pub fn rdim(r : Radon) -> Int32 {
  r.n * r.n
}

///|
/// [D-Line] 第 (dir, t) 條線上的點編碼清單（點 (x,y) 編碼 x·n + y）。
pub fn line_points(r : Radon, dir : Int32, t : Int32) -> Array[Int32] {
  let n = r.n
  let out : Array[Int32] = []
  if dir == n {
    let mut y = 0
    while y < n {
      let _ = out.push(t * n + y)
      y = y + 1
    }
  } else {
    let m = dir
    let mut x = 0
    while x < n {
      let yy = ((m * x + t) % n + n) % n
      let _ = out.push(x * n + yy)
      x = x + 1
    }
  }
  out
}

///|
pub fn line_count(r : Radon) -> Int32 {
  r.dirs * r.n
}

///|
/// [D-RadMat] Radon 矩陣：行 = 線 (dir,t)，列 = 點； entry = 1（mod p）。
pub fn radon_matrix(r : Radon) -> @core.Mat {
  let nr = line_count(r)
  let nc = rdim(r)
  let rows : Array[Array[Int32]] = Array::makei(nr, i => {
    let dir = i / r.n
    let t = i % r.n
    let row = Array::make(nc, 0)
    for q in line_points(r, dir, t) {
      row[q] = 1
    }
    row
  })
  @core.mat_from_rows(rows)
}

///|
/// [D-Gram] RᵀR（對稱 |X|×|X| 矩陣）。
pub fn gram_matrix(r : Radon) -> @core.Mat {
  let m = radon_matrix(r)

  @core.mat_mul(@core.mat_transpose(m), m, r.p)
}

///|
/// [T-Radon-Gram] 驗證 RᵀR = n·I + J (mod p)，等價於
///   「對角線元 = 每點所在線數 = n+1；非對角線元 = 兩點共線數 = 1」。
pub fn check_gram(r : Radon) -> Bool {
  let g = gram_matrix(r)
  let nc = rdim(r)
  let n = r.n
  let p = r.p
  let mut ok = true
  let mut i = 0
  while i < nc {
    let mut j = 0
    while j < nc {
      let expect = if i == j { ((n + 1) % p + p) % p } else { 1 }
      if @core.mat_get(g, i, j) != expect {
        ok = false
      }
      j = j + 1
    }
    i = i + 1
  }
  ok
}

///|
/// [D-Rank] 由消元給出 rank R 與 nullity R。
pub fn radon_rank(r : Radon) -> (Int32, Int32) {
  let m = radon_matrix(r)
  let fld = @core.mk_field(r.p)
  let rk = @core.rank_mod(m, fld)
  (rk, rdim(r) - rk)
}

///|
/// [T-Radon-Inj] R 單射 ⟺ nullity = 0。回傳是否成立。
pub fn check_injective(r : Radon) -> Bool {
  let (_, nullity) = radon_rank(r)
  nullity == 0
}

///|
/// [D-InvGram] (n·I + J)^{-1} = (1/n)(I − J/(n+1))，作用在向量上：
///   (nI+J)^{-1} v = (1/n)·(v − (Σv)/(n²+n))。
pub fn gram_apply_inv(r : Radon, v : Array[Int32]) -> Array[Int32] {
  let n = r.n
  let p = r.p
  let f = @core.mk_field(p)
  let nc = rdim(r)
  let mut s = 0
  for x in v {
    s = @core.fld_add(f, s, x)
  }
  // (n·I + J)^{-1} = (1/n)(I − J/(n²+n))：先減掉 (Σv)/(n²+n)，再乘 1/n
  let denom = @core.fld_inv(f, @core.fld_norm(f, n * n + n))
  let inv_n = @core.fld_inv(f, n)
  let corr = @core.fld_mul(f, s, denom)
  Array::makei(nc, j => @core.fld_mul(f, @core.fld_sub(f, v[j], corr), inv_n))
}

///|
/// [T-Radon-Inv] 驗證反演公式：對隨機 f，gram_apply_inv(Rᵀ(Rf)) = f。
pub fn check_inversion(r : Radon, f : Array[Int32]) -> Bool {
  let m = radon_matrix(r)
  let fld = @core.mk_field(r.p)
  let mf = @core.mat_mul_vec(m, f, r.p)
  let mt = @core.mat_transpose(m)
  let g = @core.mat_mul_vec(mt, mf, r.p)
  let back = gram_apply_inv(r, g)
  let nc = rdim(r)
  let mut ok = true
  let mut i = 0
  while i < nc && ok {
    if @core.fld_sub(fld, back[i], f[i]) != 0 {
      ok = false
    }
    i = i + 1
  }
  ok
}

///|
/// [D-Total] 所有線上的總和 Σ_{dir,t} Rf(dir,t) = (n+1)·Σ_x f(x)。
pub fn check_total_weight(r : Radon, f : Array[Int32]) -> Bool {
  let m = radon_matrix(r)
  let mf = @core.mat_mul_vec(m, f, r.p)
  let fld = @core.mk_field(r.p)
  let mut s1 = 0
  for x in mf {
    s1 = @core.fld_add(fld, s1, x)
  }
  let mut s0 = 0
  for x in f {
    s0 = @core.fld_add(fld, s0, x)
  }
  s1 == @core.fld_mul(fld, r.n + 1, s0)
}

///|
/// [T-Radon-Quad] 二次型恆等式（對任意 f）：
///   Σ_{lines} (Rf)² = n·Σ_x f(x)² + (Σ_x f(x))²。
///   推論：f 零均值時 R 保範數（差一個因子 n）——離散 Radon 變換的 Plancherel 型關係。
pub fn check_quad_identity(r : Radon, f : Array[Int32]) -> Bool {
  let m = radon_matrix(r)
  let mf = @core.mat_mul_vec(m, f, r.p)
  let fld = @core.mk_field(r.p)
  let mut s1 = 0
  for x in mf {
    s1 = @core.fld_add(fld, s1, @core.fld_mul(fld, x, x))
  }
  let mut s0 = 0
  let mut s = 0
  for x in f {
    s0 = @core.fld_add(fld, s0, @core.fld_mul(fld, x, x))
    s = @core.fld_add(fld, s, x)
  }
  let rhs = @core.fld_add(
    fld,
    @core.fld_mul(fld, r.n, s0),
    @core.fld_mul(fld, s, s),
  )
  s1 == rhs
}

// ---- 切片定理（Fourier slice）----

///|
/// [D-RootN] 在 F_p^× 中找 n 次本原單位根（需 n | p-1）。
pub fn root_of_unity(n : Int32, p : Int32) -> Int32 {
  let mut g = 2
  while g < p {
    if @core.mod_pow(g, n, p) == 1 && n > 1 {
      let mut ok = true
      let mut j = 1
      while j < n {
        if @core.mod_pow(g, j, p) == 1 {
          ok = false
        }
        j = j + 1
      }
      if ok {
        return g
      }
    }
    g = g + 1
  }
  1
}

///|
/// [D-Fourier] F(v)(k) = Σ_j ω^{jk} v(j)，ω = 本原 n 次根；v 長度 n。
pub fn fourier(v : Array[Int32], w : Int32, p : Int32) -> Array[Int32] {
  let n = v.length()
  let f = @core.mk_field(p)
  Array::makei(n, k => {
    let mut s = 0
    let mut j = 0
    while j < n {
      s = @core.fld_add(
        f,
        s,
        @core.fld_mul(f, v[j], @core.mod_pow(w, j * k, p)),
      )
      j = j + 1
    }
    s
  })
}

///|
/// [T-Radon-Slice] 對方向 m（含豎直），沿該方向的 1-維 Fourier 變換
///   等於 2-維 Fourier 變換在對應「垂直線」上的取值。逐 k 驗證。
pub fn check_slice(r : Radon, f : Array[Int32]) -> Bool {
  let n = r.n
  let p = r.p
  let w = root_of_unity(n, p)
  if w == 1 && n > 1 {
    return false
  }
  let fld = @core.mk_field(p)
  // 2-D Fourier: F2(a,b) = Σ_{x,y} f(x,y)·(ω^{a x} ω^{b y})
  let f2 : Array[Int32] = Array::makei(n * n, i => {
    let a = i / n
    let b = i % n
    let mut s = 0
    let mut x = 0
    while x < n {
      let mut y = 0
      while y < n {
        let va = @core.mod_pow(w, a * x, p)
        let vb = @core.mod_pow(w, b * y, p)
        s = @core.fld_add(
          fld,
          s,
          @core.fld_mul(fld, @core.fld_mul(fld, f[x * n + y], va), vb),
        )
        y = y + 1
      }
      x = x + 1
    }
    s
  })
  let mut ok = true
  let mut dir = 0
  while dir < r.dirs {
    let mut t = 0
    while t < n {
      // Rf(dir, ·) 的 Fourier（對 t）
      let rf : Array[Int32] = Array::makei(n, tt => {
        let pts = line_points(r, dir, tt)
        let mut s = 0
        for q in pts {
          s = @core.fld_add(fld, s, f[q])
        }
        s
      })
      let fr = fourier(rf, w, p)
      // 2-D：對 fixed dir=m，垂直線由 (a,b) = (k·m, -k)（mod n）給出；豎直 dir=n: (a,b)=(k,0)... 用 (1·k, 0)
      let mut k = 0
      while k < n {
        let (a, b) = if dir == n { (k, 0) } else { ((-dir * k % n + n) % n, k) }
        if fr[k] != f2[a * n + b] {
          ok = false
        }
        k = k + 1
      }
      t = t + 1
    }
    dir = dir + 1
  }
  ok
}
