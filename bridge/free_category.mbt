///|
fn path_index(paths : Array[Array[Int32]], needle : Array[Int32]) -> Int32? {
  for i = 0; i < paths.length(); i = i + 1 {
    if paths[i] == needle {
      return Some(i)
    }
  }
  None
}

///|
/// semiring-cat 的 DAG 自由範疇 → symlib 的有限表格範疇。
/// 每條路徑（包括長度 0 路徑）成為一個態射，合成是路徑串接：
/// `comp[f][g] = f ∘ g`，故串接次序是先 g、後 f。
/// 非 DAG 會使自由範疇無限，因此拒絕。
pub fn free_category_to_fincat(g : @scat.DiGraph) -> Result[@sym.FinCat, String] {
  if !g.is_dag() {
    return Err("free_category_to_fincat: 圖不是 DAG（自由範疇會無限）")
  }
  let homs = g.hom_sets()
  let paths : Array[Array[Int32]] = []
  for i in 0..<g.n {
    for j in 0..<g.n {
      for path in homs[i][j] {
        paths.push(path)
      }
    }
  }
  let nmor = paths.length()
  let dom = Array::make(nmor, 0)
  let cod = Array::make(nmor, 0)
  for k in 0..<nmor {
    let path = paths[k]
    dom[k] = path[0]
    cod[k] = path[path.length() - 1]
  }
  let id = Array::make(g.n, 0)
  for v in 0..<g.n {
    id[v] = match path_index(paths, [v]) {
      None => return Err("free_category_to_fincat: 缺少單位路徑 [\{v}]")
      Some(k) => k
    }
  }
  let comp = Array::make(nmor * nmor, -1)
  for f in 0..<nmor {
    for h in 0..<nmor {
      if cod[h] == dom[f] {
        let joined = paths[h].copy()
        for k in 1..<paths[f].length() {
          joined.push(paths[f][k])
        }
        comp[f * nmor + h] = match path_index(paths, joined) {
          None => return Err("free_category_to_fincat: 合成路徑不在路徑表內")
          Some(k) => k
        }
      }
    }
  }
  Ok({ nobj: g.n, nmor, dom, cod, id, comp })
}

///|
/// 從 symlib FinCat 表格逐態射數出的 Hom 基數矩陣。
pub fn fincat_hom_counts(c : @sym.FinCat) -> Array[Array[Int64]] {
  let out : Array[Array[Int64]] = []
  for _ in 0..<c.nobj {
    out.push(Array::make(c.nobj, 0L))
  }
  for mor in 0..<c.nmor {
    let i = c.dom[mor]
    let j = c.cod[mor]
    out[i][j] = out[i][j] + 1L
  }
  out
}

///|
/// 菱形 DAG 加一條直達邊：0→1→3、0→2→3、0→3。
/// semiring 的列舉、拓撲 DP、半環星閉包與 symlib 的
/// FinCat 公理/Hom 計數必須全數一致。
pub fn check_free_category_bridge() -> Bool {
  let g = @scat.DiGraph::new(4)
  g.edge(0, 1)
  g.edge(0, 2)
  g.edge(1, 3)
  g.edge(2, 3)
  g.edge(0, 3)
  let c = match free_category_to_fincat(g) {
    Err(_) => return false
    Ok(v) => v
  }
  if !@sym.is_category(c) || c.nmor != 11 {
    return false
  }
  let from_cat = fincat_hom_counts(c)
  let by_dp = g.path_counts()
  let by_star = g.path_counts_by_closure()
  for i in 0..<4 {
    for j in 0..<4 {
      if from_cat[i][j] != by_dp[i][j] || from_cat[i][j] != by_star[i][j] {
        return false
      }
    }
  }
  from_cat[0][3] == 3L
}
