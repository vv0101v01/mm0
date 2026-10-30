///|
test "symlib native proof suite and Schreier-Sims invariants" {
  let certs = prove_all(200)
  assert_true(certs.length() > 0)
  for c in certs {
    assert_true(c.holds)
  }
}

///|
test "symlib G-set and finite powerset monad laws" {
  let s3 = PermGroup::symmetric(3)
  assert_eq(s3.order(), 6L)
  assert_true(gset_monad_laws(s3, 3, 24))
  assert_true(pow_monad_laws(3))
}

///|
test "symlib canonical graph isomorphism positive and negative control" {
  let c4 = Graph::from_edges(4, [(0, 1), (1, 2), (2, 3), (3, 0)])
  let c4_relabeled = Graph::from_edges(4, [(0, 2), (2, 1), (1, 3), (3, 0)])
  let k13 = Graph::from_edges(4, [(0, 1), (0, 2), (0, 3)])
  assert_true(isomorphic(c4, c4_relabeled))
  assert_true(!isomorphic(c4, k13))
}
