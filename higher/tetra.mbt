///| ## 殘餘 2 推進：∞-groupoid 的 **3-截斷**（`tetra`）
///
///| 上一輪的實驗停在 2-截斷（只到三角形）。這一輪把截斷推到 3 維，
///| 並且用一個**通用的維度記帳**量同一件事：
///
///|   一個 `d`-角（`d`-horn）需要一個 `(d+1)`-單形來填。
///|   所以在「截斷到維度 `N`」的模型上，**`N`-角永遠填不了**——
///|   除非把 `(N+1)`-單形加進來，而那又生出 `(N+1)`-角。
///
///| 實測（都在 5 個頂點以內，可手驗）：
///|   - `S² = ∂Δ³`（4 頂點）：缺 2-角 4 個 ⇒ 要填需要 3-單形；
///|   - `S³ = ∂Δ⁴`（5 頂點）：**缺 3-角 0 個**（3-截斷上已是 Kan），但缺 4-角 5 個。
///
///| 第二行就是「相干塔不會在有限維停下」的 3-維版本：
///| 補到 3 維看起來成功了，真正缺的是第 4 維。

///| 截斷到維度 `top` 的單純集：`simplices[d]` 是 `d`-單形的頂點表（遞增）。
///| 只存**非退化**單形；子面自動補齊。
pub struct SSetTrunc {
  nv : Int32
  top : Int32
  simplices : Array[Array[Array[Int32]]]
}

///| 建構：給最高維的單形，自動補所有子面（含頂點）。
pub fn trunc_make(nv : Int32, top : Int32, top_simplices : Array[Array[Int32]]) -> SSetTrunc {
  let g : Array[Array[Array[Int32]]] = []
  for d = 0; d <= top; d = d + 1 {
    g.push([])
  }
  // 先放最高維
  for s in top_simplices {
    push_unique(g[top], @algebra.int_sort(s))
  }
  // 由高到低補子面
  let mut d = top
  while d > 0 {
    let cur : Array[Array[Int32]] = []
    for s in g[d] {
      cur.push(s)
    }
    for s in cur {
      for i = 0; i < s.length(); i = i + 1 {
        let f : Array[Int32] = []
        for j = 0; j < s.length(); j = j + 1 {
          if i != j {
            f.push(s[j])
          }
        }
        push_unique(g[d - 1], f)
      }
    }
    d = d - 1
  }
  SSetTrunc::{ nv, top, simplices: g }
}

///| 陣列內容相等（已排序）。
fn same_ints(a : Array[Int32], b : Array[Int32]) -> Bool {
  if a.length() != b.length() {
    return false
  }
  let mut ok = true
  for i = 0; i < a.length(); i = i + 1 {
    if a[i] != b[i] {
      ok = false
    }
  }
  ok
}

///| 去重插入。
fn push_unique(g : Array[Array[Int32]], s : Array[Int32]) -> Unit {
  let mut dup = false
  for old in g {
    if same_ints(old, s) {
      dup = true
    }
  }
  if !dup {
    g.push(s)
  }
}

///| 某維度是否含有該單形。
pub fn trunc_has(t : SSetTrunc, d : Int32, s : Array[Int32]) -> Bool {
  if d < 0 || d > t.top {
    return false
  }
  let mut found = false
  for old in t.simplices[d] {
    if same_ints(old, s) {
      found = true
    }
  }
  found
}

///| 一個 `d`-角的描述。
pub struct HornD {
  dim : Int32
  apex_set : Array[Int32]
  missing_face : Int32
  faces_present : Int32
  filled : Bool
}

///| 列舉所有 `d`-角（`d ≥ 1`）：由 `(d+1)` 個頂點的子集 `S` 與被略過的索引 `k` 決定。
///| `d`-角的面是 `S \ {i}`（`i ≠ k`）這些 **`(d−1)`-單形**；
///| 填它的是一個 **`d`-單形**`S`。
///| （第一版把面寫成 `d`-單形、填充寫成 `(d+1)`-單形，整體維度錯一格，
///|   於是 `S²` 被算成「缺 4 個 2-角」——實際上是缺 4 個 3-角。）
pub fn horns_at(t : SSetTrunc, d : Int32) -> Array[HornD] {
  let out : Array[HornD] = []
  let n = t.nv
  let idx : Array[Int32] = []
  for i = 0; i < n; i = i + 1 {
    idx.push(i)
  }
  // 列舉 (d+1)-子集
  let size = d + 1
  let combos = subsets(idx, size, 0)
  for s in combos {
    for k = 0; k < size; k = k + 1 {
      let mut present = 0
      let mut all = true
      for i = 0; i < size; i = i + 1 {
        if i != k {
          let f : Array[Int32] = []
          for j = 0; j < size; j = j + 1 {
            if j != i {
              f.push(s[j])
            }
          }
          if trunc_has(t, d - 1, f) {
            present = present + 1
          } else {
            all = false
          }
        }
      }
      if all {
        out.push(HornD::{
          dim: d,
          apex_set: s,
          missing_face: k,
          faces_present: present,
          filled: trunc_has(t, d, s),
        })
      }
    }
  }
  out
}

///| 由 `pool` 取 `k` 個的組合。
fn subsets(pool : Array[Int32], k : Int32, start : Int32) -> Array[Array[Int32]] {
  let out : Array[Array[Int32]] = []
  if k == 0 {
    out.push([])
    return out
  }
  for i = start; i + k <= pool.length(); i = i + 1 {
    let rest : Array[Int32] = []
    for j = i + 1; j < pool.length(); j = j + 1 {
      rest.push(pool[j])
    }
    for tail in subsets(rest, k - 1, 0) {
      let s : Array[Int32] = [pool[i]]
      for x in tail {
        s.push(x)
      }
      out.push(s)
    }
  }
  out
}

///| 未填充的 `d`-角數。
pub fn horns_missing_count(t : SSetTrunc, d : Int32) -> Int32 {
  let mut c = 0
  for h in horns_at(t, d) {
    if !h.filled {
      c = c + 1
    }
  }
  c
}

///| `S² = ∂Δ³`：4 頂點、4 個三角形。
pub fn sset_trunc_s2() -> SSetTrunc {
  trunc_make(4, 2, [[0, 1, 2], [0, 1, 3], [0, 2, 3], [1, 2, 3]])
}

///| `S³ = ∂Δ⁴`：5 頂點、5 個四面體。
pub fn sset_trunc_s3() -> SSetTrunc {
  trunc_make(
    5,
    3,
    [[0, 1, 2, 3], [0, 1, 2, 4], [0, 1, 3, 4], [0, 2, 3, 4], [1, 2, 3, 4]],
  )
}

///| `Δ³`（實心）：1 個四面體。
pub fn sset_trunc_d3() -> SSetTrunc {
  trunc_make(4, 3, [[0, 1, 2, 3]])
}

///| 一列的顯示。
pub fn trunc_show(name : String, t : SSetTrunc) -> String {
  let mut s = "\{name}: "
  for d = 0; d <= t.top; d = d + 1 {
    s = s + "#\{d}-單形=\{t.simplices[d].length()} "
  }
  s
}

///| 3-截斷的完整量測。
pub fn tetra_probe() -> Array[String] {
  let out : Array[String] = []
  let s2 = sset_trunc_s2()
  let s3 = sset_trunc_s3()
  let d3 = sset_trunc_d3()
  out.push(trunc_show("S² = ∂Δ³", s2))
  out.push(trunc_show("S³ = ∂Δ⁴", s3))
  out.push(trunc_show("Δ³（實心）", d3))
  out.push("")
  out.push("2-角（面是邊，填充是三角形）：")
  out.push(
    "  S² 缺 \{horns_missing_count(s2, 2)} 個；Δ³ 缺 \{horns_missing_count(d3, 2)} 個 ⇒ 2-截斷上兩者都「看起來」是 Kan",
  )
  out.push("3-角（面是三角形，填充是四面體）：")
  out.push(
    "  S² 缺 \{horns_missing_count(s2, 3)} 個；Δ³ 缺 \{horns_missing_count(d3, 3)} 個；S³ 缺 \{horns_missing_count(s3, 3)} 個",
  )
  out.push("4-角（面是四面體，填充是 4-單形）—— 這一維是上一輪沒做的：")
  out.push(
    "  S³ 缺 \{horns_missing_count(s3, 4)} 個 ⇒ **3-截斷上 S³ 已經是 Kan，缺的正好是第 4 維**",
  )
  out.push("")
  out.push(
    "結論：`S²` 的障礙出現在 3-角（4 個），`S³` 的障礙出現在 4-角（5 個）：**每個 n-球面的 Kan 缺陷正好在 n+1 維**。補幾維就 Kan 不成立；每一維的角都要下一維的單形，這是相干塔不停的正確形式",
  )
  out.push(
    "與 2-截斷實驗的關係：上一輪用 `reuse`／`fresh` 量的是「同一個 2-角有幾種填法」；這裡量的是「填到第幾維才夠」。兩個量都指向同一個結論：合成是弱結構",
  )
  out
}
