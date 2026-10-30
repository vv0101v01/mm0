///| ## B1 —— Schema 邊界：宇宙層級約束作為整數差約束系統
///

///| golden SPEC §四 第一條殘餘邊界：跨越超限序數層級的無界宇宙多態大歸納—遞迴

///|（Mahlo／超宇宙公理）與一般高階索引容器不在有限層級核心內。
///

///| 合併動作（推遠 + 變化）：把「層級賦值是層級指派函子的像」這一類**有限**約束

///| 從「搜尋／啟發式」改寫成**可判定**問題：

///|   約束 L(a) ≥ L(b) + k  構成差分約束系統（difference constraints），

///|   以 Bellman–Ford 最長路徑 O(V·E) 決定可行性，並輸出

///|   (a) 最小解（逐點最小是解，故解集有最小元）；(b) 不可行時的正環見證。

///| 這把「宇宙多態」的可行性判定變成消元引擎的一次閉包計算。

///| 一條層級約束：`from` 是下界來源，`to` 是被約束者，`k` 是位移；

///|
/// 語義為 `L[to] ≥ L[from] + k`。
pub struct LevelEdge {
  from_ : Int32
  to : Int32
  k : Int32
}

///|
pub struct LevelSystem {
  n : Int32
  edges : Array[LevelEdge]
  labels : Array[String]
}

///|
pub fn level_system(n : Int32, labels : Array[String]) -> LevelSystem {
  LevelSystem::{ n, edges: [], labels, }
}

///|
pub fn level_require(
  s : LevelSystem,
  from_ : Int32,
  to : Int32,
  k : Int32,
) -> Unit {
  s.edges.push(LevelEdge::{ from_, to, k, })
}

///|
/// 判定結果：是否可行、最小解、以及不可行時的正環見證。
pub struct LevelVerdict {
  feasible : Bool
  levels : Array[Int32]
  cycle : Array[Int32]
  relaxations : Int32
}

///| [E-Levels] Bellman–Ford 最長路徑閉包。

///| 初始化 L ≡ 0（這是「最小」候選，因為約束全為下界），鬆弛 n 輪；

///|
/// 第 n 輪仍可鬆弛 ⟺ 存在正環 ⟺ 約束不可行。
pub fn level_solve(s : LevelSystem) -> LevelVerdict {
  let n = s.n
  let lv = Array::make(n, 0)
  let par = Array::make(n, -1)
  let mut relax = 0
  let mut improved = true
  let mut rounds = 0
  while improved && rounds <= n {
    improved = false
    rounds = rounds + 1
    for e in s.edges {
      let cand = lv[e.from_] + e.k
      if cand > lv[e.to] {
        lv[e.to] = cand
        par[e.to] = e.from_
        improved = true
        relax = relax + 1
      }
    }
  }
  if !improved {
    return LevelVerdict::{
      feasible: true,
      levels: lv,
      cycle: [],
      relaxations: relax,
    }
  }
  // 正環見證：從任一仍被鬆弛的節點沿父指標走 n 步，取其後 n 步的軌跡。
  let mut start = 0
  for i = 0; i < n; i = i + 1 {
    if par[i] >= 0 {
      start = i
    }
  }
  let mut cur = start
  for _i = 0; _i < n; _i = _i + 1 {
    if par[cur] >= 0 {
      cur = par[cur]
    }
  }
  let cycl : Array[Int32] = []
  let mut p = cur
  for _i = 0; _i < n + 1; _i = _i + 1 {
    cycl.push(p)
    if par[p] >= 0 {
      p = par[p]
    }
    if p == cur {
      break
    }
  }
  LevelVerdict::{
    feasible: false,
    levels: lv,
    cycle: cycl,
    relaxations: relax,
  }
}

///|
pub fn level_show(v : LevelVerdict, s : LevelSystem) -> String {
  if v.feasible {
    let mut out = "feasible, least solution"
    for i = 0; i < s.n; i = i + 1 {
      out = "\{out} \{s.labels[i]}=\{v.levels[i]}"
    }
    out
  } else {
    let mut out = "INFEASIBLE, positive cycle"
    for i in v.cycle {
      out = "\{out} -> \{s.labels[i]}"
    }
    out
  }
}

///| B1 的實驗：三個層級系統。

///|  (E1) `Type_i : Type_{i+1}` 塔 + 一個嚴格升格函子 → 可行；

///|  (E2) 同層互歸納（互相依賴但不升格）→ 可行，最小解相等；

///|  (E3) 「A 的層級嚴格低於 B，B 又嚴格低於 A」這類循環升格 → 不可行，

///|       這正是 golden 拒絕非法同時宣告時要抓的東西，

///|
///       而現在它是**消元產物**（正環見證）而不是手寫檢查。
pub fn b1_probe() -> Array[String] {
  let out : Array[String] = []
  let s1 = level_system(5, ["Type0", "Type1", "Type2", "F", "muF"])
  level_require(s1, 0, 1, 1) // Type1 > Type0
  level_require(s1, 1, 2, 1) // Type2 > Type1
  level_require(s1, 0, 3, 1) // F 高於其參數層
  level_require(s1, 3, 4, 0) // muF 不動點不升格
  let v1 = level_solve(s1)
  out.push("E1 塔+互歸納: \{level_show(v1, s1)}  [relax=\{v1.relaxations}]")
  let s2 = level_system(3, ["A", "B", "C"])
  level_require(s2, 0, 1, 0)
  level_require(s2, 1, 2, 0)
  level_require(s2, 2, 0, 0)
  let v2 = level_solve(s2)
  out.push("E2 同層互遞迴: \{level_show(v2, s2)}")
  let s3 = level_system(2, ["A", "B"])
  level_require(s3, 0, 1, 1)
  level_require(s3, 1, 0, 1)
  let v3 = level_solve(s3)
  out.push("E3 循環升格: \{level_show(v3, s3)}")
  out
}
