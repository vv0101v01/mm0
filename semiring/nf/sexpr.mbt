// ===========================================================================
// 規範形式 III：半環表示式的多項式正規形（等式判定程序）
//
// 自由**冪等**半環上的元素，可以用「有限語言」表示：
//   變數          ↔ 單一字母 {a}
//   ⊕            ↔ 聯集（冪等！）
//   ⊗            ↔ 串接
//   0 / 1        ↔ ∅ / {ε}
//
// 所以「兩個半環表示式是否在所有冪等半環中相等」等價於「兩個有限語言的
// 是否相同」。本檔給出兩條完全不同的判定路徑：
//
//   路徑 A（代數）：把表示式化為**單項式集合的排序正規形**，結構比較。
//   路徑 B（自動機）：把它翻譯成無星的表示式，交給 nf/dfa.mbt 求最小 DFA
//                     的正規形字串，字串比較。
//
// 兩條路徑都完備（對有限語言），而且必須永遠給出同一個答案；
// 這個一致性本身就是測試項目（見 nf_wbtest.mbt）。
//
// 注意範圍：只有 ⊕ 冪等的半環才適用（ℕ、ℝ 的加法不冪等）。
// 對非冪等半環，`a ⊕ a = a` 不成立，本判定程序會給出「相等」而實際不相等
// ——因此本模組的介面名稱一律帶 `idempotent`。
// ===========================================================================

///|
/// 半環表示式的語法樹（⊕ ⊗ 0 1 變數）。
pub(all) enum SExpr {
  SZero
  SOne
  SVar(Int32)
  SSum(SExpr, SExpr)
  SProd(SExpr, SExpr)
}

///|
/// 單項式比較：逐項比較變數索引，短者在前（字典序）。
pub fn mono_cmp(a : Array[Int32], b : Array[Int32]) -> Int32 {
  let n = if a.length() < b.length() { a.length() } else { b.length() }
  for i in 0..<n {
    if a[i] != b[i] {
      return if a[i] < b[i] { -1 } else { 1 }
    }
  }
  if a.length() == b.length() {
    0
  } else if a.length() < b.length() {
    -1
  } else {
    1
  }
}

///|
fn sort_monos(m : Array[Array[Int32]]) -> Array[Array[Int32]] {
  let out : Array[Array[Int32]] = []
  for v in m {
    out.push(v)
  }
  let mut i = 1
  while i < out.length() {
    let key = out[i]
    let mut j = i
    while j > 0 && mono_cmp(out[j - 1], key) > 0 {
      out[j] = out[j - 1]
      j = j - 1
    }
    out[j] = key
    i = i + 1
  }
  // 去重（⊕ 冪等）
  let uniq : Array[Array[Int32]] = []
  for v in out {
    if uniq.length() == 0 || mono_cmp(uniq[uniq.length() - 1], v) != 0 {
      uniq.push(v)
    }
  }
  uniq
}

///|
/// 單項式乘法：直接串接。
///
/// **不可以排序**：⊗ 不假設交換，`ab` 與 `ba` 是兩個不同的單項式。
/// （⊕ 才需要排序去重，因為 ⊕ 冪等且交換。）
fn mono_mul(a : Array[Int32], b : Array[Int32]) -> Array[Int32] {
  let out : Array[Int32] = []
  for v in a {
    out.push(v)
  }
  for v in b {
    out.push(v)
  }
  out
}

///|
/// 多項式正規形：排序去重後的單項式集合。
pub fn normalize(e : SExpr) -> Array[Array[Int32]] {
  match e {
    SZero => []
    SOne => [[]]
    SVar(v) => [[v]]
    SSum(a, b) => {
      let pa = normalize(a)
      let pb = normalize(b)
      let all : Array[Array[Int32]] = []
      for m in pa {
        all.push(m)
      }
      for m in pb {
        all.push(m)
      }
      sort_monos(all)
    }
    SProd(a, b) => {
      let pa = normalize(a)
      let pb = normalize(b)
      let all : Array[Array[Int32]] = []
      for x in pa {
        for y in pb {
          all.push(mono_mul(x, y))
        }
      }
      sort_monos(all)
    }
  }
}

///|
/// 判定：兩個表示式在**自由冪等半環**上是否相等。
pub fn idempotent_identity_holds(a : SExpr, b : SExpr) -> Bool {
  let na = normalize(a)
  let nb = normalize(b)
  if na.length() != nb.length() {
    return false
  }
  for i in 0..<na.length() {
    if mono_cmp(na[i], nb[i]) != 0 {
      return false
    }
  }
  true
}

///|
/// 同一判定，走自動機路線：翻譯成無星表示式後比對最小 DFA 的正規形。
///
/// 這條路徑不假設任何代數定律，只做「語言是否相同」的判定，
/// 因此可以獨立驗證路徑 A。
pub fn idempotent_identity_holds_via_dfa(a : SExpr, b : SExpr) -> Bool {
  let alphabet : Array[Int32] = []
  collect_vars(a, alphabet)
  collect_vars(b, alphabet)
  let ra = sexpr_to_regex(a)
  let rb = sexpr_to_regex(b)
  regex_equiv(ra, rb, sorted_vars(alphabet))
}

///|
fn collect_vars(e : SExpr, out : Array[Int32]) -> Unit {
  match e {
    SZero => ()
    SOne => ()
    SVar(v) => {
      let mut found = false
      for x in out {
        if x == v {
          found = true
        }
      }
      if !found {
        out.push(v)
      }
    }
    SSum(a, b) => {
      collect_vars(a, out)
      collect_vars(b, out)
    }
    SProd(a, b) => {
      collect_vars(a, out)
      collect_vars(b, out)
    }
  }
}

///|
fn sorted_vars(v : Array[Int32]) -> Array[Int32] {
  let out : Array[Int32] = []
  for x in v {
    out.push(x)
  }
  let mut i = 1
  while i < out.length() {
    let key = out[i]
    let mut j = i
    while j > 0 && out[j - 1] > key {
      out[j] = out[j - 1]
      j = j - 1
    }
    out[j] = key
    i = i + 1
  }
  out
}

///|
/// 翻譯：半環表示式 → 正規表示式（不含 *）。
pub fn sexpr_to_regex(e : SExpr) -> Regex {
  match e {
    SZero => RZero
    SOne => ROne
    SVar(v) => RChar(v)
    SSum(a, b) => r_sum(sexpr_to_regex(a), sexpr_to_regex(b))
    SProd(a, b) => r_prod(sexpr_to_regex(a), sexpr_to_regex(b))
  }
}
