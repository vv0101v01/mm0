// ===========================================================================
// 規範形式 II：最小 DFA 作為 Myhill–Nerode 正規形
//
// 定理（Myhill–Nerode）：每個正則語言的「最小完整 DFA」在同構意義下唯一。
// 若再把狀態按 BFS 首次到達的順序編號、符號按固定順序展開，就得到一個
// **逐位元可比對的字串**——這就是本庫所稱的「正規形」：
//
//     語言 L 的正規形 = canonical(minimal(complete(DFA(L))))
//
// 三個操作因此可以互相驗證：
//   * `dfa_of_regex`   由導數直接建 DFA（狀態 = ACI 正規形表示式）
//   * `dfa_minimize`   Moore 分割細化（等價類合併）
//   * `dfa_canonical`  BFS 正規化字串
//
// `regex_equiv(a,b)` 判定的就是 canonical(a) == canonical(b)，
// 而且另外用「乘積自動機」獨立再判一次（兩條路必須一致）。
// ===========================================================================

///|
/// 完整 DFA（每個狀態的每個符號都有轉移；`-1` 表示尚未建邊）。
pub(all) struct Dfa {
  nsym : Int32
  alphabet : Array[Int32]
  start : Int32
  accept : Array[Bool]
  /// 大小 `nstates * nsym`，`trans[s*nsym + k]`
  trans : Array[Int32]
}

///|
pub fn Dfa::nstates(self : Dfa) -> Int32 {
  // 以 accept 的長度為準：`nsym = 0`（空字母表）時轉移表是空的，
  // 用 trans.length()/nsym 會除以零。
  self.accept.length()
}

///|
/// 由正規表示式建 DFA：狀態就是導數（的 ACI 正規形）。
///
/// 探索過程是 BFS：每次對一個狀態與每個符號算導數，若沒見過就加入。
/// 因為 ACI 正規形讓可能的導數有限，這個迴圈保證終止。
pub fn dfa_of_regex(r : Regex, alphabet : Array[Int32]) -> Dfa {
  let states : Array[Regex] = [r]
  let trans : Array[Int32] = []
  let mut head = 0
  let nsym = alphabet.length()
  while head < states.length() {
    let cur = states[head]
    for k in 0..<nsym {
      let d = deriv(cur, alphabet[k])
      let mut idx = -1
      for q in 0..<states.length() {
        if regex_cmp(states[q], d) == 0 {
          idx = q
          break
        }
      }
      if idx < 0 {
        idx = states.length()
        states.push(d)
      }
      trans.push(idx)
    }
    head = head + 1
  }
  let n = states.length()
  let accept : Array[Bool] = Array::make(n, false)
  for i in 0..<n {
    accept[i] = nullable(states[i])
  }
  { nsym, alphabet, start: 0, accept, trans, }
}

///|
/// 是否接受符號序列。
pub fn Dfa::accepts(self : Dfa, w : Array[Int32]) -> Bool {
  let mut s = self.start
  for c in w {
    let mut k = -1
    for i in 0..<self.nsym {
      if self.alphabet[i] == c {
        k = i
        break
      }
    }
    if k < 0 {
      return false
    }
    s = self.trans[s * self.nsym + k]
  }
  self.accept[s]
}

///|
/// Moore 分割細化：反覆把「接受性相同、且每個符號的轉移落在同一區塊」的狀態併為一類。
///
/// 收斂時，每個區塊就是 Myhill–Nerode 的一個等價類 ⇒ 最小 DFA。
/// 複雜度 O(n²·|Σ|·輪數)，狀態數在數百以內足夠；正確性比常數重要。
pub fn dfa_minimize(d : Dfa) -> Dfa {
  let n = d.nstates()
  let nsym = d.nsym
  // 初始分割：接受 / 不接受
  let block : Array[Int32] = Array::make(n, 0)
  let mut nblocks = 2
  for i in 0..<n {
    block[i] = if d.accept[i] { 1 } else { 0 }
  }
  let mut changed = true
  while changed {
    changed = false
    // 以 (block, 各符號目的區塊) 當簽名重新分類
    let sigs : Array[Array[Int32]] = []
    let newblock : Array[Int32] = Array::make(n, -1)
    let mut nb = 0
    for i in 0..<n {
      let sig : Array[Int32] = [block[i]]
      for k in 0..<nsym {
        sig.push(block[d.trans[i * nsym + k]])
      }
      let mut idx = -1
      for q in 0..<sigs.length() {
        if sigs[q] == sig {
          idx = q
          break
        }
      }
      if idx < 0 {
        sigs.push(sig)
        idx = sigs.length() - 1
        nb = nb + 1
      }
      newblock[i] = idx
    }
    if nb != nblocks {
      changed = true
    }
    for i in 0..<n {
      block[i] = newblock[i]
    }
    nblocks = nb
  }
  // 以區塊為狀態重建（只保留可達區塊，並以 BFS 順序編號）
  let start_block = block[d.start]
  let order : Array[Int32] = [start_block]
  let mapping : Array[Int32] = Array::make(nblocks + 1, -1)
  mapping[start_block] = 0
  let new_trans : Array[Int32] = []
  let new_accept : Array[Bool] = []
  let mut head = 0
  while head < order.length() {
    let b = order[head]
    // 代表狀態
    let mut rep = -1
    for i in 0..<n {
      if block[i] == b {
        rep = i
        break
      }
    }
    new_accept.push(d.accept[rep])
    for k in 0..<nsym {
      let t = block[d.trans[rep * nsym + k]]
      if mapping[t] < 0 {
        mapping[t] = order.length()
        order.push(t)
      }
      new_trans.push(mapping[t])
    }
    head = head + 1
  }
  {
    nsym,
    alphabet: d.alphabet,
    start: 0,
    accept: new_accept,
    trans: new_trans,
  }
}

///|
/// 正規形字串：BFS 順序（起點先、符號按字母表順序）下的
/// 「接受位元序列 + 轉移表」。最小完整 DFA 的這個字串對語言是唯一的。
pub fn dfa_canonical(d : Dfa) -> String {
  let sb = StringBuilder()
  let n = d.nstates()
  let nsym = d.nsym
  // BFS 重新編號
  let order : Array[Int32] = [d.start]
  let seen : Array[Int32] = Array::make(n, -1)
  seen[d.start] = 0
  let mut head = 0
  while head < order.length() {
    let s = order[head]
    for k in 0..<nsym {
      let t = d.trans[s * nsym + k]
      if seen[t] < 0 {
        seen[t] = order.length()
        order.push(t)
      }
    }
    head = head + 1
  }
  sb.write_string("n=\{order.length()};")
  for s in order {
    sb.write_string(if d.accept[s] { "1" } else { "0" })
  }
  sb.write_string(";")
  for s in order {
    for k in 0..<nsym {
      let t = d.trans[s * nsym + k]
      sb.write_string("\{seen[t]},")
    }
    sb.write_string("|")
  }
  sb.to_string()
}

///|
/// 乘積自動機的語言等價判定（不經過最小化，獨立於 `dfa_canonical`）。
pub fn dfa_equiv(a : Dfa, b : Dfa) -> Bool {
  if a.nsym != b.nsym {
    return false
  }
  let na = a.nstates()
  let nb = b.nstates()
  let visited : Array[Bool] = Array::make(na * nb, false)
  let qx : Array[Int32] = [a.start]
  let qy : Array[Int32] = [b.start]
  visited[a.start * nb + b.start] = true
  let mut head = 0
  while head < qx.length() {
    let s = qx[head]
    let t = qy[head]
    if a.accept[s] != b.accept[t] {
      return false
    }
    for k in 0..<a.nsym {
      let s2 = a.trans[s * a.nsym + k]
      let t2 = b.trans[t * b.nsym + k]
      if !visited[s2 * nb + t2] {
        visited[s2 * nb + t2] = true
        qx.push(s2)
        qy.push(t2)
      }
    }
    head = head + 1
  }
  true
}

///|
/// 兩個表示式是否描述同一語言：比對最小 DFA 的正規形字串。
pub fn regex_equiv(a : Regex, b : Regex, alphabet : Array[Int32]) -> Bool {
  let ca = dfa_canonical(dfa_minimize(dfa_of_regex(a, alphabet)))
  let cb = dfa_canonical(dfa_minimize(dfa_of_regex(b, alphabet)))
  ca == cb
}

///|
/// 最小 DFA 的狀態數（Myhill–Nerode 等價類個數）。
pub fn regex_state_count(r : Regex, alphabet : Array[Int32]) -> Int32 {
  dfa_minimize(dfa_of_regex(r, alphabet)).nstates()
}

///|
/// 反向語言：把 DFA 的邊反向，起點 = 原接受集，接受集 = 原起點。
/// 得到的是 NFA（多起點），這裡以「集合狀態」表示成完整 DFA。
pub fn dfa_reverse(d : Dfa) -> Dfa {
  let n = d.nstates()
  let nsym = d.nsym
  // 子集構造：一個狀態 = 原狀態的集合（以位元向量表示，n ≤ 64）
  let sets : Array[Array[Bool]] = [d.accept]
  let trans : Array[Int32] = []
  let mut head = 0
  while head < sets.length() {
    let cur = sets[head]
    for k in 0..<nsym {
      // 反向：若 s --k--> t 且 t 在當前集合中，則 s 進入下一個集合
      let nxt : Array[Bool] = Array::make(n, false)
      for t in 0..<n {
        if !cur[t] {
          continue
        }
        for s in 0..<n {
          if d.trans[s * nsym + k] == t {
            nxt[s] = true
          }
        }
      }
      let mut idx = -1
      for q in 0..<sets.length() {
        if sets[q] == nxt {
          idx = q
          break
        }
      }
      if idx < 0 {
        idx = sets.length()
        sets.push(nxt)
      }
      trans.push(idx)
    }
    head = head + 1
  }
  let m = sets.length()
  let accept : Array[Bool] = Array::make(m, false)
  for i in 0..<m {
    accept[i] = sets[i][d.start]
  }
  { nsym, alphabet: d.alphabet, start: 0, accept, trans, }
}
