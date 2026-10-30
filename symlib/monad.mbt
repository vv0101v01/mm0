///|
/// # Monad — 單子（代數效應的組合介面）
///
/// MoonBit 無高階型構造子（HKT），故以「具體單子 + 單子律測試」方式實現：
/// 每個單子型別提供 `pure` / `bind` / `map`，並以 `kleisli` 組合。
/// 與演算法的交互：
/// - ListM（非決定性/冪集單子）：同構列舉、搜索空間代數
/// - StateM（狀態單子）：規範形式管線的統計/最優值線程化
/// - OptionM：搜索中的失敗傳播
/// 三個單子皆由本庫演算法實際使用（見 isomorphisms_m / canonical_form_m）。

///|
/// 非決定性（清單）單子：搜索空間的代數封裝。
pub(all) struct ListM[A] {
  arr : Array[A]
}

///|
/// 單子單位 η。
pub fn[A] ListM::pure(x : A) -> ListM[A] {
  { arr: [x], }
}

///|
/// 連結 bind（concatMap）：搜索樹的順序合成。
pub fn[A, B] ListM::bind(self : ListM[A], f : (A) -> ListM[B]) -> ListM[B] {
  let out : Array[B] = []
  for a in self.arr {
    for b in f(a).arr {
      out.push(b)
    }
  }
  { arr: out, }
}

///|
/// 函子映射。
pub fn[A, B] ListM::map(self : ListM[A], f : (A) -> B) -> ListM[B] {
  let out : Array[B] = []
  for a in self.arr {
    out.push(f(a))
  }
  { arr: out, }
}

///|
/// 選擇（mplus）：搜索分支的併集。
pub fn[A] ListM::mplus(self : ListM[A], other : ListM[A]) -> ListM[A] {
  let out = self.arr.copy()
  for a in other.arr {
    out.push(a)
  }
  { arr: out, }
}

///|
/// 過濾。
pub fn[A] ListM::filter(self : ListM[A], f : (A) -> Bool) -> ListM[A] {
  let out : Array[A] = []
  for a in self.arr {
    if f(a) {
      out.push(a)
    }
  }
  { arr: out, }
}

///|
/// 守衛（失敗 = 空列表）。`guard` 為保留字，故命名為 nd_guard。
pub fn nd_guard(cond : Bool) -> ListM[Unit] {
  if cond {
    ListM::pure(())
  } else {
    { arr: [], }
  }
}

///|
/// 由陣列入單子。
pub fn[A] ListM::from_array(a : Array[A]) -> ListM[A] {
  { arr: a.copy(), }
}

///|
/// 出單子。
pub fn[A] ListM::to_array(self : ListM[A]) -> Array[A] {
  self.arr.copy()
}

///|
/// 全列舉（fold）。
pub fn[A, B] ListM::fold(self : ListM[A], init : B, f : (B, A) -> B) -> B {
  let mut acc = init
  for a in self.arr {
    acc = f(acc, a)
  }
  acc
}

///|
/// 狀態單子：計算 (S) -> (A, S)，管線中線程化統計狀態。
pub(all) struct StateM[S, A] {
  run : (S) -> (A, S)
}

///|
/// 單子單位。
pub fn[S, A] StateM::pure(x : A) -> StateM[S, A] {
  { run: fn(s) { (x, s) }, }
}

///|
/// 連結 bind。
pub fn[S, A, B] StateM::bind(
  self : StateM[S, A],
  f : (A) -> StateM[S, B],
) -> StateM[S, B] {
  {
    run: fn(s) {
      let (a, s1) = (self.run)(s)
      (f(a).run)(s1)
    },
  }
}

///|
/// 函子映射。
pub fn[S, A, B] StateM::map(self : StateM[S, A], f : (A) -> B) -> StateM[S, B] {
  {
    run: fn(s) {
      let (a, s1) = (self.run)(s)
      (f(a), s1)
    },
  }
}

///|
/// 讀取狀態。
pub fn[S] StateM::get() -> StateM[S, S] {
  { run: fn(s) { (s, s) }, }
}

///|
/// 寫入狀態。
pub fn[S] StateM::put(s0 : S) -> StateM[S, Unit] {
  { run: fn(_) { ((), s0) }, }
}

///|
/// 修改狀態。
pub fn[S] StateM::modify(f : (S) -> S) -> StateM[S, Unit] {
  { run: fn(s) { ((), f(s)) }, }
}

///|
/// 只取值。
pub fn[S, A] StateM::eval(self : StateM[S, A], init : S) -> A {
  let (a, _) = (self.run)(init)
  a
}

///|
/// 只取狀態。
pub fn[S, A] StateM::exec(self : StateM[S, A], init : S) -> S {
  let (_, s) = (self.run)(init)
  s
}

///|
/// Option 單子單位。
pub fn[A] opt_pure(x : A) -> A? {
  Some(x)
}

///|
/// Option 單子連結。
pub fn[A, B] opt_bind(m : A?, f : (A) -> B?) -> B? {
  match m {
    Some(x) => f(x)
    None => None
  }
}

///|
/// ListM 的 Kleisli 組合：(A -> M[B]) ⋆ (B -> M[C]) = A -> M[C]。
pub fn[A, B, C] kleisli_list(
  f : (A) -> ListM[B],
  g : (B) -> ListM[C],
) -> (A) -> ListM[C] {
  fn(a) { f(a).bind(g) }
}

///|
/// StateM 的 Kleisli 組合。
pub fn[S, A, B, C] kleisli_state(
  f : (A) -> StateM[S, B],
  g : (B) -> StateM[S, C],
) -> (A) -> StateM[S, C] {
  fn(a) { f(a).bind(g) }
}

///|
/// 非決定性搜索：在候選集上分支 + 守衛約束（回溯搜索的單子形式）。
pub fn[A] search_nd(
  candidates : Array[Array[A]],
  accept : (Array[A]) -> Bool,
) -> ListM[Array[A]] {
  fn build(chosen : Array[A], depth : Int32) -> ListM[Array[A]] {
    if depth == candidates.length() {
      if accept(chosen) {
        ListM::pure(chosen.copy())
      } else {
        { arr: [], }
      }
    } else {
      let mut acc : ListM[Array[A]] = { arr: [], }
      for v in candidates[depth] {
        chosen.push(v)
        acc = acc.mplus(build(chosen, depth + 1))
        let _ = chosen.pop()
      }
      acc
    }
  }
  build([], 0)
}
