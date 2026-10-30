///|
test "cubical theorem registry, spec soundness, and phase 16 regressions" {
  assert_true(spec_registry_sound())
  assert_eq(spec_registry().length(), 127)
  assert_true(all_checks_pass())
}

///|
test "lazy DValue forcing on dbool_not, dvalue_to_pval, and hash bounds" {
  // Regression for unforced DVThunk arguments in kan_dep.mbt and conv_case_split.mbt.
  let thunk_true = DVThunk(DThunk::{
    forced: None,
    compute: () => DVBool(true),
    force_count: 0,
  })
  let thunk_pair = DVThunk(DThunk::{
    forced: None,
    compute: () =>
      DVPair(
        thunk_true,
        DVThunk(DThunk::{
          forced: None,
          compute: () => DVBool(false),
          force_count: 0,
        }),
      ),
    force_count: 0,
  })
  assert_true(conv_at(0, 0, DVBoolTy, dbool_not(thunk_true), DVBool(false)))
  assert_eq(dvalue_to_pval(thunk_pair), PVPair(PVBool(true), PVBool(false)))
  // Non-negative BDD & schema hash buckets even on extremal signed Int32 inputs.
  let h1 = bdd_node_hash(100000000, 200000000, 300000000, 1024)
  let h2 = bdd_apply_hash(3, 700000000, 900000000, 1024)
  let h3 = registry_string_hash(
    "long_schema_repr_overflow_probe_0123456789_abcdefghijklmnopqrstuvwxyz",
  )
  assert_true(h1 >= 0 && h1 < 1024)
  assert_true(h2 >= 0 && h2 < 1024)
  assert_true(h3 >= 0 && h3 < 1000003)
}

///|
test "glued circle square cap winding orientation and negative control" {
  let base_fn = (_ : Dim) => DVCirclePoint(DZero)
  let loop_fn = (r : Dim) => DVCirclePoint(r)
  let r_neg = circle_square_glued_cap(loop_fn, base_fn, base_fn, base_fn, dlevel=4)
  assert_eq(r_neg.net_boundary_winding, -1)
  assert_true(r_neg.filler is None)
  let r_zero = circle_square_glued_cap(loop_fn, loop_fn, loop_fn, loop_fn, dlevel=4)
  assert_eq(r_zero.net_boundary_winding, 0)
  assert_true(!(r_zero.filler is None))
}
