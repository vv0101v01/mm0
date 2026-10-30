///| ## 整數小工具的唯一一份（第九輪去重）
///
///| 合併後整棵樹上有 **10 個函式名各被寫了兩份以上**（`int_pow`、`sort_ints`、`binom`、
///| `mod_inv`、`lsr32`、`same_face`、`same_set`、`vec_scale`、`vec_zero`、`mat_vec`）。
///| 兩份實作最危險的地方不是浪費行數，而是**會分岔**：`binom` 的兩份只有一份用 `Int64`
///| （另一份在 `C(20,8)` 上靜默溢位，被選擇器交叉點表抓出來），`sort_ints` 一份是冒泡、
///| 一份是插入排序。所以把它們收進 `exact/algebra`（每個套件都已經或可以依賴的葉子），
///| 只留一份，並讓所有呼叫點指向這裡。
///
///| 命名用 `int_` 前綴，避免與 golden 既有的 `rat_*`／`qvec_*`／`bigint_*` 混淆。

///| `base^e`（`e ≥ 0`；`Int32` 的溢位行為與原本兩份一致）。
pub fn int_pow(base : Int32, e : Int32) -> Int32 {
  let mut acc = 1
  for _i = 0; _i < e; _i = _i + 1 {
    acc = acc * base
  }
  acc
}

///| 二項係數，用 `Int64` 逐步乘除（每步整除），超過 `2·10^9` 飽和。
///
///| `Int32` 版本在 `C(20,8)` 上會**靜默溢位**（算成 `19447`）；這裡是唯一一份，不會再分岔。
pub fn int_binom(n : Int32, k : Int32) -> Int32 {
  // 次序有講究：`k = 0` 必須先回 1，連 `n = −1` 也一樣（`C(−1,0) = 1`）。
  // `super/score` 的「展平對稱性」測試就是靠這條：`m = 0, d = j` 時會問 `C(−1, 0)`。
  // 兩份舊實作在這裡**行為不同**（bridge 版回 0、score 版回 1），合併時被測試抓出來 ——
  // 這正是「同一個名字兩份實作」的真正代價。
  if k < 0 {
    return 0
  }
  if k == 0 {
    return 1
  }
  if k > n || n < 0 {
    return 0
  }
  let kk = if k > n - k { n - k } else { k }
  let mut res : Int64 = 1
  for i = 1; i <= kk; i = i + 1 {
    res = res * (n - kk + i).to_int64() / i.to_int64()
  }
  if res > 2000000000L {
    2000000000
  } else {
    res.to_int()
  }
}

///| 整數陣列的升冪排序（插入排序；穩定、不改輸入）。
pub fn int_sort(xs : Array[Int32]) -> Array[Int32] {
  let out : Array[Int32] = []
  for x in xs {
    out.push(x)
  }
  let mut i = 1
  while i < out.length() {
    let x = out[i]
    let mut j = i - 1
    while j >= 0 && out[j] > x {
      out[j + 1] = out[j]
      j = j - 1
    }
    out[j + 1] = x
    i = i + 1
  }
  out
}

///| 邏輯右移（`Int32` 是帶號的，`>>` 是算術右移；雜湊需要的是邏輯右移）。
pub fn int_lsr(x : Int32, n : Int32) -> Int32 {
  (x.reinterpret_as_uint() >> (n % 32)).reinterpret_as_int()
}

///| 模逆（`p` 為素數，用 Fermat）；`Int64` 中介避免 `p` 接近上界時溢位。
pub fn int_mod_inv(a0 : Int32, p : Int32) -> Int32 {
  if p <= 1 {
    return 0
  }
  let mut a = ((a0 % p) + p) % p
  let mut result = 1
  let mut exponent = p - 2
  while exponent > 0 {
    if exponent % 2 == 1 {
      result = ((result.to_int64() * a.to_int64()) % p.to_int64()).to_int()
    }
    a = ((a.to_int64() * a.to_int64()) % p.to_int64()).to_int()
    exponent = exponent / 2
  }
  result
}

///| 兩個整數陣列是否逐項相等（`same_face`／`same_set` 的共同內容）。
pub fn int_vec_eq(a : Array[Int32], b : Array[Int32]) -> Bool {
  if a.length() != b.length() {
    return false
  }
  for i = 0; i < a.length(); i = i + 1 {
    if a[i] != b[i] {
      return false
    }
  }
  true
}

///| 整數向量是否全零。
pub fn int_vec_is_zero(v : Array[Int32]) -> Bool {
  for x in v {
    if x != 0 {
      return false
    }
  }
  true
}

///| 整數向量乘純量。
pub fn int_vec_scale(v : Array[Int32], k : Int32) -> Array[Int32] {
  let out : Array[Int32] = []
  for x in v {
    out.push(x * k)
  }
  out
}

///| 整數矩陣乘整數向量（列數 = 矩陣列數；行長與向量長取較短者，與原 `mat_vec` 一致）。
pub fn int_mat_vec(m : Array[Array[Int32]], v : Array[Int32]) -> Array[Int32] {
  let out : Array[Int32] = []
  for row in m {
    let mut s : Int32 = 0
    let lim = if row.length() < v.length() { row.length() } else { v.length() }
    for j = 0; j < lim; j = j + 1 {
      s = s + row[j] * v[j]
    }
    out.push(s)
  }
  out
}
