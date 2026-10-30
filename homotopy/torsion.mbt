///| ## 殘餘 1 的下半：Reidemeister 撓率分開 `L(7,1)` 與 `L(7,2)`
///
///| 上一輪把 Hopf 纖維化的同調算完了，殘餘寫得很準：**同調分不出 `+d` 與 `−d`**
///| （`L(7,1)` 與 `L(7,2)` 的 `H_*` 一模一樣）。這一輪把那個「分不出」補上。
///
///| 工具是 Franz–de Rham 的 Reidemeister 撓率：對非平凡特徵 `ρ_a: t ↦ ζ^a`，
///| 透鏡空間 `L(p,q)` 的扭鏈複形（每維一個胞腔）給出
///
///|   `τ_a(L(p,q)) = 1 / ((ζ^a − 1)(ζ^{a·s} − 1))`，`s ∈ {q, q^{−1}}`，
///
///| 而 `s` 的兩種取法對應**同一個空間的兩種胞腔結構**，撓率只能定到「單位 `±ζ^k`」與
///| 「`s` 的二選一」為止。因此不變量是**無序對** `{family(q), family(q^{−1})}`，
///| 比較時允許指標內乘任一單位。
///
///| 這個檔案就在 `ℚ(ζ_p)` 裡**精確**算這件事（不浮點、不近似）：
///| 元素是 `p−1` 個有理係數，乘法用 `Φ_p(ζ) = 1 + ζ + … + ζ^{p−1} = 0` 約化。
///
///| 結果（見 `torsion_probe`）：`p = 5, 7, 11, 13` 上算出來的分類
///| **與代數判據 `q' ≡ ±q^{±1} (mod p)` 完全一致**，而對 `p = 7` 這正好把
///| `{1,6}` 與 `{2,3,4,5}` 分開 —— `L(7,1) ≁ L(7,2)`，`π₁`、`H_*`、`ℤ/7` 全部相同。

///| `ℚ(ζ_p)` 的元素：`p−1` 個有理係數（`1, ζ, …, ζ^{p−2}` 的係數）。
pub struct Cyc {
  p : Int32
  c : Array[@algebra.Rat]
}

///|

pub fn cyc_zero(p : Int32) -> Cyc {
  let c : Array[@algebra.Rat] = []
  for _i = 0; _i < p - 1; _i = _i + 1 {
    c.push(@algebra.rat_zero())
  }
  Cyc::{ p, c }
}

///|

pub fn cyc_const(p : Int32, v : Int32) -> Cyc {
  let z = cyc_zero(p)
  z.c[0] = @algebra.rat_int(v)
  z
}

///| `ζ^k`（`0 ≤ k < p`），用 `ζ^{p−1} = −(1 + ζ + … + ζ^{p−2})`。
pub fn cyc_pow_zeta(p : Int32, k : Int32) -> Cyc {
  let z = cyc_zero(p)
  if k < p - 1 {
    z.c[k] = @algebra.rat_one()
  } else {
    // k = p − 1：所有係數 −1
    for i = 0; i < p - 1; i = i + 1 {
      z.c[i] = @algebra.rat_int(0 - 1)
    }
  }
  z
}

///|

pub fn cyc_add(a : Cyc, b : Cyc) -> Cyc {
  let z = cyc_zero(a.p)
  for i = 0; i < a.p - 1; i = i + 1 {
    z.c[i] = @algebra.rat_add(a.c[i], b.c[i])
  }
  z
}

///|

pub fn cyc_sub(a : Cyc, b : Cyc) -> Cyc {
  let z = cyc_zero(a.p)
  for i = 0; i < a.p - 1; i = i + 1 {
    z.c[i] = @algebra.rat_sub(a.c[i], b.c[i])
  }
  z
}

///| 乘法：先做長度 `2p−3` 的摺積，再由 `ζ^{p−1} = −Σ` 從高次往下攤平。
pub fn cyc_mul(a : Cyc, b : Cyc) -> Cyc {
  let p = a.p
  let n = p - 1
  let tmp : Array[@algebra.Rat] = []
  for _i = 0; _i < 2 * n - 1; _i = _i + 1 {
    tmp.push(@algebra.rat_zero())
  }
  for i = 0; i < n; i = i + 1 {
    if @algebra.rat_sign(a.c[i]) == 0 {
      continue
    }
    for j = 0; j < n; j = j + 1 {
      if @algebra.rat_sign(b.c[j]) == 0 {
        continue
      }
      tmp[i + j] = @algebra.rat_add(tmp[i + j], @algebra.rat_mul(a.c[i], b.c[j]))
    }
  }
  // ζ^d（d ≥ n = p−1）= −Σ_{i<n} ζ^{d−n+i}
  for d = 2 * n - 2; d >= n; d = d - 1 {
    let v = tmp[d]
    if @algebra.rat_sign(v) == 0 {
      continue
    }
    tmp[d] = @algebra.rat_zero()
    for i = 0; i < n; i = i + 1 {
      tmp[d - n + i] = @algebra.rat_sub(tmp[d - n + i], v)
    }
  }
  let z = cyc_zero(p)
  for i = 0; i < n; i = i + 1 {
    z.c[i] = tmp[i]
  }
  z
}

///| 取負。
pub fn cyc_neg(a : Cyc) -> Cyc {
  let z = cyc_zero(a.p)
  for i = 0; i < a.p - 1; i = i + 1 {
    z.c[i] = @algebra.rat_neg(a.c[i])
  }
  z
}

///|

pub fn cyc_is_zero(a : Cyc) -> Bool {
  for i = 0; i < a.p - 1; i = i + 1 {
    if @algebra.rat_sign(a.c[i]) != 0 {
      return false
    }
  }
  true
}

///| 精確相等（`ℚ(ζ_p)` 的基底表示唯一，所以逐係數比即可）。
pub fn cyc_eq(a : Cyc, b : Cyc) -> Bool {
  for i = 0; i < a.p - 1; i = i + 1 {
    if !@algebra.rat_eq(a.c[i], b.c[i]) {
      return false
    }
  }
  true
}

///| `a == u·b`，其中 `u` 取遍單位群 `{±ζ^k}`（撓率的合法模糊度）。
pub fn unit_related(a : Cyc, b : Cyc) -> Bool {
  let p = a.p
  for k = 0; k < p; k = k + 1 {
    let u = cyc_pow_zeta(p, k)
    let ub = cyc_mul(u, b)
    if cyc_eq(a, ub) {
      return true
    }
    if cyc_eq(a, cyc_neg(ub)) {
      return true
    }
  }
  false
}

///| 扭鏈複形的分母 `D_a(s) = (ζ^a − 1)(ζ^{a s} − 1)`（撓率是它的倒數）。
pub fn torsion_den(p : Int32, a : Int32, s : Int32) -> Cyc {
  let za = cyc_pow_zeta(p, a)
  let one = cyc_const(p, 1)
  let f1 = cyc_sub(za, one)
  let zas = cyc_pow_zeta(p, (a * s) % p)
  let f2 = cyc_sub(zas, one)
  cyc_mul(f1, f2)
}

///| 兩個「族」是否模單位相等：逐 `a` 檢查 `D_a(s1)` 與 `D_a(s2)` 單位相關。
pub fn family_match(p : Int32, s1 : Int32, s2 : Int32) -> Bool {
  for a = 1; a < p; a = a + 1 {
    if !unit_related(torsion_den(p, a, s1), torsion_den(p, a, s2)) {
      return false
    }
  }
  true
}

///| `q` 在 `Z/p` 下的乘法逆。
pub fn inv_mod(p : Int32, q : Int32) -> Int32 {
  let mut v = 1
  for k = 1; k < p; k = k + 1 {
    if (q * k) % p == 1 {
      v = k
    }
  }
  v
}

///| 撓率不變量是否把 `q1`、`q2` 判成同一個透鏡空間。
///| 允許 `s ∈ {q, q^{−1}}` 的無序二選一。
pub fn torsion_same(p : Int32, q1 : Int32, q2 : Int32) -> Bool {
  let same_orient = family_match(p, q1, q2)
  let crossed1 = family_match(p, q1, inv_mod(p, q2))
  let crossed2 = family_match(p, inv_mod(p, q1), q2)
  let crossed3 = family_match(p, inv_mod(p, q1), inv_mod(p, q2))
  (same_orient && crossed3) || (crossed1 && crossed2)
}

///| `x mod p` 的正規化（MoonBit 的 `%` 對負數會回負餘數，這裡統一成 `0..p−1`）。
pub fn modp(x : Int32, p : Int32) -> Int32 {
  let r = x % p
  if r < 0 {
    r + p
  } else {
    r
  }
}

///| 代數判據：`q2 ≡ ±q1^{±1} (mod p)`。
pub fn algebraically_same(p : Int32, q1 : Int32, q2 : Int32) -> Bool {
  let inv = modp(inv_mod(p, q1), p)
  let a = modp(q2, p)
  let cands = [modp(q1, p), modp(0 - q1, p), inv, modp(0 - inv, p)]
  let mut hit = false
  for c in cands {
    if a == c {
      hit = true
    }
  }
  hit
}

///| 用撓率把 `q = 1..p−1` 分類，回傳每個 `q` 的代表元。
pub fn classes_by_torsion(p : Int32) -> Array[Int32] {
  let reps : Array[Int32] = []
  let out : Array[Int32] = []
  for q = 1; q < p; q = q + 1 {
    let mut found = 0
    for r in reps {
      if found == 0 && torsion_same(p, r, q) {
        found = r
      }
    }
    if found == 0 {
      reps.push(q)
      out.push(q)
    } else {
      out.push(found)
    }
  }
  out
}

///| 用代數判據分類（作為對照組）。
pub fn classes_by_algebra(p : Int32) -> Array[Int32] {
  let reps : Array[Int32] = []
  let out : Array[Int32] = []
  for q = 1; q < p; q = q + 1 {
    let mut found = 0
    for r in reps {
      if found == 0 && algebraically_same(p, r, q) {
        found = r
      }
    }
    if found == 0 {
      reps.push(q)
      out.push(q)
    } else {
      out.push(found)
    }
  }
  out
}

///|

pub fn classes_show(cls : Array[Int32]) -> String {
  let mut s = ""
  for i = 0; i < cls.length(); i = i + 1 {
    if i > 0 {
      s = s + " "
    }
    s = s + "\{i + 1}~\{cls[i]}"
  }
  s
}

///| 兩個分類是否**同一個分割**（代表元可以不同，分割必須相同）。
pub fn same_partition(a : Array[Int32], b : Array[Int32]) -> Bool {
  if a.length() != b.length() {
    return false
  }
  for i = 0; i < a.length(); i = i + 1 {
    for j = 0; j < a.length(); j = j + 1 {
      let same_a = a[i] == a[j]
      let same_b = b[i] == b[j]
      if same_a != same_b {
        return false
      }
    }
  }
  true
}

///|

pub struct TorsionRow {
  p : Int32
  n_classes_torsion : Int32
  n_classes_algebra : Int32
  agrees : Bool
  partition : String
}

///|

pub fn torsion_row(p : Int32) -> TorsionRow {
  let t = classes_by_torsion(p)
  let a = classes_by_algebra(p)
  let mut nt = 0
  for i = 0; i < t.length(); i = i + 1 {
    if t[i] == i + 1 {
      nt = nt + 1
    }
  }
  let mut na = 0
  for i = 0; i < a.length(); i = i + 1 {
    if a[i] == i + 1 {
      na = na + 1
    }
  }
  TorsionRow::{ p, n_classes_torsion: nt, n_classes_algebra: na, agrees: same_partition(t, a), partition: classes_show(t) }
}

///|

pub fn torsion_show(r : TorsionRow) -> String {
  "p=\{r.p}: 撓率分類 \{r.n_classes_torsion} 類 / 代數判據 \{r.n_classes_algebra} 類 一致=\{r.agrees} | \{r.partition}"
}

///| 殘餘 1 的收官探針。
pub fn torsion_probe() -> Array[String] {
  let out : Array[String] = []
  for p in [5, 7, 11, 13] {
    out.push(torsion_show(torsion_row(p)))
  }
  out.push(
    "p=7 上撓率把 q=1,6 與 q=2,3,4,5 分成兩類 ⇒ L(7,1) 與 L(7,2) 不同胚，而它們的 π₁、H_*、ℤ/7 完全一樣",
  )
  out.push(
    "⇒ 上一輪「同調分不出 ±d」的殘餘被撓率收掉：**同調看不見定向，撓率看得見**。所有計算都在 ℚ(ζ_p) 內精確完成（無浮點）",
  )
  out
}
