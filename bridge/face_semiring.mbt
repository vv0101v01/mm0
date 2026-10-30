///|
/// Face 公式商去語義等價後的一個類，以 cubical 的 canonical ROBDD
/// 儲存。從 Face 建構時必須先過 `bdd_of_face`；裸 Face AST 的
/// 結構相等不是語義相等（例如 `φ ∨ φ` 與 `φ`）。
pub(all) struct FaceClass {
  bdd : @cub.Bdd
} derive(Eq)

///|
pub extend FaceClass with Eq::{equal, not_equal}

///|
pub fn FaceClass::of_face(face : @cub.Face, nvars : Int32) -> Self {
  { bdd: @cub.bdd_of_face(face, nvars), }
}

///|
pub fn FaceClass::bottom() -> Self {
  { bdd: @cub.bdd_of_face(@cub.face_bot(), 0), }
}

///|
pub fn FaceClass::top() -> Self {
  { bdd: @cub.bdd_of_face(@cub.face_top(), 0), }
}

///|
pub fn FaceClass::join(self : Self, other : Self) -> Self {
  { bdd: @cub.bdd_or(self.bdd, other.bdd), }
}

///|
pub fn FaceClass::meet(self : Self, other : Self) -> Self {
  { bdd: @cub.bdd_and(self.bdd, other.bdd), }
}

///|
pub fn FaceClass::complement(self : Self) -> Self {
  { bdd: @cub.bdd_not(self.bdd), }
}

///|
pub fn FaceClass::is_bottom(self : Self) -> Bool {
  self == FaceClass::bottom()
}

///|
pub fn FaceClass::is_top(self : Self) -> Bool {
  self == FaceClass::top()
}

///|
/// Face 蕴含序：a ≤ b 當且僅當 a ∨ b = b。
pub fn FaceClass::le(self : Self, other : Self) -> Bool {
  self.join(other) == other
}

///|
pub impl Show for FaceClass with fn to_string(self) {
  if self.is_bottom() {
    "⊥"
  } else if self.is_top() {
    "⊤"
  } else {
    "<face-class>"
  }
}

///|
pub impl @semialg.Semiring for FaceClass with fn zero() {
  FaceClass::bottom()
}

///|
pub impl @semialg.Semiring for FaceClass with fn one() {
  FaceClass::top()
}

///|
/// ⊕ is face disjunction.
pub impl @semialg.Semiring for FaceClass with fn plus(a, b) {
  a.join(b)
}

///|
/// ⊗ is face conjunction.
pub impl @semialg.Semiring for FaceClass with fn times(a, b) {
  a.meet(b)
}

///|
pub impl @semialg.IdempotentSemiring for FaceClass with fn le(a, b) {
  a.le(b)
}

///|
/// In this bounded lattice semiring, a* = 1 ⊕ a ⊕ a² ⊕ … = ⊤.
pub impl @semialg.StarSemiring for FaceClass with fn star(_a) {
  FaceClass::top()
}

///|
pub impl @semialg.OrderedSemiring for FaceClass with fn meet(a, b) {
  a.meet(b)
}

///|
pub impl @semialg.OrderedSemiring for FaceClass with fn top() {
  FaceClass::top()
}

///|
pub extend FaceClass with Show::{to_string, output}

///|
pub extend FaceClass with @semialg.Semiring::{
  zero,
  is_one,
  plus,
  one,
  times,
  is_zero,
}

///|
pub extend FaceClass with @semialg.StarSemiring::{star}

///|
fn face_class_samples() -> Array[FaceClass] {
  let x = FaceClass::of_face(@cub.face_var1(0), 2)
  let y = FaceClass::of_face(@cub.face_var1(1), 2)
  [
    FaceClass::bottom(),
    FaceClass::top(),
    x,
    x.complement(),
    y,
    y.complement(),
    x.meet(y),
    x.join(y),
    x.complement().join(y),
    x.meet(y.complement()),
  ]
}

///|
/// 以 semiring-algebra 自己的定律檢查器核驗 Face 商格的
/// 幪等星閉半環定律，並特別釘住 `bdd_of_face` 的商作用：
/// `φ∨φ = φ`、`⊤∧φ = φ`、` (i=0) = ¬(i=1)`。
pub fn face_semiring_law_report() -> @semialg.LawReport {
  let pool = face_class_samples()
  let rng = @semialg.Rng::new(0xFACE_2026UL)
  @semialg.check_star_idem(
    "FaceClass(BDD quotient)",
    fn() { pool[rng.next_int(pool.length())] },
    samples=48,
  )
}

///|
pub fn check_face_semiring_bridge() -> Bool {
  let f = @cub.face_var1(0)
  let repeated = FaceClass::of_face(@cub.face_or(f, f), 2)
  let single = FaceClass::of_face(f, 2)
  let i0 = FaceClass::of_face(@cub.face_var0(0), 2)
  if repeated != single ||
    FaceClass::top().meet(single) != single ||
    i0 != single.complement() ||
    !single.le(single.join(FaceClass::of_face(@cub.face_var1(1), 2))) {
    return false
  }
  face_semiring_law_report().ok()
}
