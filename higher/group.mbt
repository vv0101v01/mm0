///| ## 有限群的同態計數：量測「線性化丟掉了多少」
///
///| `|Hom(π₁(X), G)|` 對 `π₁` 的非阿貝爾結構敏感；`|Hom(H₁(X), G)|` 只看得到阿貝爾化。
///| 兩者之差就是「把 ∞-groupoid 壓成鏈複形」這一步丟掉的資訊量。

///| 有限群（乘法表 + 反元素表）。
pub struct FinGroup {
  n : Int32
  mul : Array[Int32]
  inv : Array[Int32]
  id : Int32
}

///| 由 `k` 個點的排列群建構：列舉全部 `k!` 個排列，乘法 = 合成。
pub fn perm_group(k : Int32) -> FinGroup {
  let perms : Array[Array[Int32]] = []
  let cur : Array[Int32] = []
  for i = 0; i < k; i = i + 1 {
    cur.push(i)
  }
  permute_into(cur, 0, perms)
  let n = perms.length()
  let mul : Array[Int32] = []
  for i = 0; i < n * n; i = i + 1 {
    mul.push(0)
  }
  for i = 0; i < n; i = i + 1 {
    for j = 0; j < n; j = j + 1 {
      // (perms[i] ∘ perms[j])(x) = perms[i][perms[j][x]]
      let comp : Array[Int32] = []
      for x = 0; x < k; x = x + 1 {
        comp.push(perms[i][perms[j][x]])
      }
      mul[i * n + j] = index_of(perms, comp)
    }
  }
  let ident = index_of(perms, identity_perm(k))
  let inv : Array[Int32] = []
  for i = 0; i < n; i = i + 1 {
    let mut t = -1
    for j = 0; j < n; j = j + 1 {
      if mul[i * n + j] == ident {
        t = j
      }
    }
    inv.push(t)
  }
  FinGroup::{ n, mul, inv, id: ident }
}

///|

fn identity_perm(k : Int32) -> Array[Int32] {
  let out : Array[Int32] = []
  for i = 0; i < k; i = i + 1 {
    out.push(i)
  }
  out
}

///|

fn index_of(perms : Array[Array[Int32]], p : Array[Int32]) -> Int32 {
  for i = 0; i < perms.length(); i = i + 1 {
    let mut eq = true
    for x = 0; x < p.length(); x = x + 1 {
      if perms[i][x] != p[x] {
        eq = false
      }
    }
    if eq {
      return i
    }
  }
  -1
}

///| 遞迴列舉排列。
fn permute_into(cur : Array[Int32], pos : Int32, out : Array[Array[Int32]]) -> Unit {
  if pos == cur.length() {
    let copy : Array[Int32] = []
    for x in cur {
      copy.push(x)
    }
    out.push(copy)
    return
  }
  for i = pos; i < cur.length(); i = i + 1 {
    let t = cur[pos]
    cur[pos] = cur[i]
    cur[i] = t
    permute_into(cur, pos + 1, out)
    let t2 = cur[pos]
    cur[pos] = cur[i]
    cur[i] = t2
  }
}

///| 整數次冪。
fn ipow(base : Int32, e : Int32) -> Int32 {
  let mut out : Int32 = 1
  for _i = 0; _i < e; _i = _i + 1 {
    out = out * base
  }
  out
}

///| 同態個數 `|Hom(Pres, G)|`：暴力列舉所有指派並檢查每條關係。
///| 生成元 ≤ 3、`|G| ≤ 6` 時為 216 次檢查，可接受。
pub fn hom_count(p : Pres, g : FinGroup) -> Int32 {
  if p.ngen == 0 {
    return 1
  }
  let mut count : Int32 = 0
  let idx : Array[Int32] = []
  for _i = 0; _i < p.ngen; _i = _i + 1 {
    idx.push(0)
  }
  let total = ipow(g.n, p.ngen)
  for _c = 0; _c < total; _c = _c + 1 {
    let mut ok = true
    for r in p.relators {
      let mut acc = g.id
      for w in r {
        let a = dec_abs(w)
        let e = if dec_rev(w) {
          g.inv[idx[a]]
        } else {
          idx[a]
        }
        acc = g.mul[acc * g.n + e]
      }
      if acc != g.id {
        ok = false
      }
    }
    if ok {
      count = count + 1
    }
    // 里程錶進位
    let mut k = p.ngen - 1
    while k >= 0 {
      idx[k] = idx[k] + 1
      if idx[k] < g.n {
        break
      }
      idx[k] = 0
      k = k - 1
    }
  }
  count
}

///| 帶剪枝的同態計數：生成元按「首次出現於關係的順序」排列，DFS 指派；
///| 某條關係的所有生成元一旦都被指派就立刻檢查。
///| 這把 6^19 壓成 6^(treewidth)——直接里程錶枚舉在 `T²`（19 生成元）上會整數溢位。
pub fn hom_count_pruned(p : Pres, g : FinGroup) -> (Int32, Int32) {
  let n = p.ngen
  if n == 0 {
    return (1, 1)
  }
  let seen : Array[Bool] = []
  for _i = 0; _i < n; _i = _i + 1 {
    seen.push(false)
  }
  let order : Array[Int32] = []
  for r in p.relators {
    for w in r {
      let a = dec_abs(w)
      if !seen[a] {
        seen[a] = true
        order.push(a)
      }
    }
  }
  for i = 0; i < n; i = i + 1 {
    if !seen[i] {
      order.push(i)
    }
  }
  let layer : Array[Array[Int32]] = []
  for _k = 0; _k < n; _k = _k + 1 {
    layer.push([])
  }
  for ri = 0; ri < p.relators.length(); ri = ri + 1 {
    let mut last = -1
    for w in p.relators[ri] {
      let a = dec_abs(w)
      for k = 0; k < n; k = k + 1 {
        if order[k] == a && k > last {
          last = k
        }
      }
    }
    if last >= 0 {
      layer[last].push(ri)
    }
  }
  let val : Array[Int32] = []
  for _i = 0; _i < n; _i = _i + 1 {
    val.push(g.id)
  }
  dfs_count(p, g, order, layer, val, 0)
}

///|

fn relator_ok(r : Array[Int32], val : Array[Int32], g : FinGroup) -> Bool {
  let mut acc = g.id
  for w in r {
    let a = dec_abs(w)
    let e = if dec_rev(w) {
      g.inv[val[a]]
    } else {
      val[a]
    }
    acc = g.mul[acc * g.n + e]
  }
  acc == g.id
}

///|

fn dfs_count(
  p : Pres,
  g : FinGroup,
  order : Array[Int32],
  layer : Array[Array[Int32]],
  val : Array[Int32],
  k : Int32,
) -> (Int32, Int32) {
  if k == order.length() {
    return (1, 1)
  }
  let mut total : Int32 = 0
  let mut nodes : Int32 = 1
  for v = 0; v < g.n; v = v + 1 {
    val[order[k]] = v
    let mut ok = true
    for ri in layer[k] {
      if !relator_ok(p.relators[ri], val, g) {
        ok = false
      }
    }
    if ok {
      let (c, nd) = dfs_count(p, g, order, layer, val, k + 1)
      total = total + c
      nodes = nodes + nd
    }
  }
  (total, nodes)
}

///| `|Hom(A, G)|`，其中 `A = Z^r ⊕ Z/d₁ ⊕ …`，`G` 一般有限群（可非阿貝爾）。
///| 做法：把 `A` 寫成群表現（自由生成元 + 撓率生成元 + 全部交換子 + `d_k·e_k`），
///| 再用 `hom_count` 暴力數。非阿貝爾時 `Hom(Z²,G)` **不等於** `|G|²`（要交換）。
pub fn hom_count_ab(ab : @coeff.Ab, g : FinGroup) -> Int32 {
  let r = ab.free
  let t = ab.tors.length()
  let ngen = r + t
  let relators : Array[Array[Int32]] = []
  // 全交換
  for i = 0; i < ngen; i = i + 1 {
    for j = i + 1; j < ngen; j = j + 1 {
      relators.push([enc(i, false), enc(j, false), enc(i, true), enc(j, true)])
    }
  }
  // 撓率關係
  for k = 0; k < t; k = k + 1 {
    let w : Array[Int32] = []
    for _c = 0; _c < ab.tors[k]; _c = _c + 1 {
      w.push(enc(r + k, false))
    }
    relators.push(w)
  }
  hom_count(Pres::{ ngen, relators }, g)
}
