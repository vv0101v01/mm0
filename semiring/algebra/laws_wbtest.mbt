///|
priv struct BrokenSr {
  v : Int32
} derive(Eq)

///|
impl Show for BrokenSr with output(self, logger) {
  logger.write_string("Broken(\{self.v})")
}

///|
impl Semiring for BrokenSr with zero() {
  { v: 0 }
}

///|
impl Semiring for BrokenSr with one() {
  { v: 1 }
}

///|
impl Semiring for BrokenSr with plus(a, b) {
  // Deliberately non-associative / non-commutative addition (a - b) for negative control.
  { v: a.v - b.v }
}

///|
impl Semiring for BrokenSr with times(a, b) {
  { v: a.v * b.v }
}

///|
priv struct AddModMonoid {
  v : Int32
} derive(Eq)

///|
impl Show for AddModMonoid with output(self, logger) {
  logger.write_string("Mod7(\{self.v})")
}

///|
impl Monoid for AddModMonoid with empty() {
  { v: 0 }
}

///|
impl Monoid for AddModMonoid with combine(a, b) {
  { v: (a.v + b.v) % 7 }
}

///|
test "semiring, star-semiring, and monoid law checkers with negative control" {
  let rng = Rng::new(20261028UL)
  let trop_rep = check_star_idem(
    "Trop",
    () => if rng.chance(0.15) { Trop::inf() } else { Trop::new(rng.range(0, 25)) },
    samples=40,
  )
  assert_true(trop_rep.ok())
  let bool_rep = check_star(
    "BoolSr",
    () => BoolSr::of(rng.chance(0.5)),
    samples=32,
  )
  assert_true(bool_rep.ok())
  let count_rep = check_semiring(
    "Counting",
    () => Counting::new(rng.range(0, 12).to_int64()),
    samples=32,
  )
  assert_true(count_rep.ok())
  let mon_rep = check_monoid(
    "AddMod7",
    () => AddModMonoid::{ v: rng.range(0, 6) },
    samples=32,
  )
  assert_true(mon_rep.ok())
  // Negative control: broken non-commutative/non-associative semiring MUST fail.
  let mut k = 1
  let bad_rep = check_semiring(
    "BrokenSr",
    () => {
      k = k % 5 + 1
      BrokenSr::{ v: k }
    },
    samples=16,
  )
  assert_true(!bad_rep.ok())
}
