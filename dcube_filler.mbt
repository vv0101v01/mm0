///|
/// Phase 11: n-dimensional open boxes, assembled fillers, and
/// whole-boundary verification.
///
/// A cube is represented extensionally as a function from one
/// dimension expression per axis to a value.  An open box of arity
/// `n` in a constant type supplies every face except the cap
/// `(axis n-1) = 1`.  The filler is assembled by a single
/// homogeneous composition along the last axis: the side faces
/// become the branches of a `DSystem` (branch face `x_k = e`,
/// branch path the side cube with the composition parameter
/// inserted on the last axis) and the `(n-1) = 0` face is the
/// base.  `dcube_box_validate` checks completeness and all
/// pairwise overlap compatibilities; `dcube_filler_faces_ok`
/// verifies, at generic interior dimensions, that the assembled
/// filler restricts to *every* supplied face -- the whole
/// boundary, not just vertices or a single segment.

///|
pub struct DCubeFunction {
  arity : Int32
  at : (Array[Dim]) -> DValue
}

///|
pub fn dcube_function(
  arity : Int32,
  at : (Array[Dim]) -> DValue,
) -> DCubeFunction {
  { arity, at, }
}

///|
/// Evaluate a cube.  A dimension list of the wrong length yields
/// the defensive value `DVUnit`.
pub fn dcube_at(cube : DCubeFunction, dims : Array[Dim]) -> DValue {
  if dims.length() != cube.arity {
    DVUnit
  } else {
    (cube.at)(dims)
  }
}

///|
pub fn dcube_constant(arity : Int32, value : DValue) -> DCubeFunction {
  { arity, at: _ => value, }
}

///|
pub fn dcube_of_path(path : (Dim) -> DValue) -> DCubeFunction {
  { arity: 1, at: dims => path(dims[0]), }
}

///|
pub fn dcube_of_point(value : DValue) -> DCubeFunction {
  { arity: 0, at: _ => value, }
}

///|
fn dcube_without_axis(dims : Array[Dim], axis : Int32) -> Array[Dim] {
  let out : Array[Dim] = []
  for i in 0..<dims.length() {
    if i != axis {
      out.push(dims[i])
    }
  }
  out
}

///|
fn dcube_with_axis(dims : Array[Dim], axis : Int32, value : Dim) -> Array[Dim] {
  let out : Array[Dim] = []
  for i in 0..<dims.length() {
    out.push(if i == axis { value } else { dims[i] })
  }
  out
}

///|
/// Restrict `axis` to the endpoint dimension (`DZero` or `DOne`).
pub fn dcube_face(
  cube : DCubeFunction,
  axis : Int32,
  endpoint : Dim,
) -> DCubeFunction {
  {
    arity: cube.arity - 1,
    at: dims => {
      let full : Array[Dim] = []
      for i in 0..<cube.arity {
        if i == axis {
          full.push(endpoint)
        } else if i < axis {
          full.push(dims[i])
        } else {
          full.push(dims[i - 1])
        }
      }
      dcube_at(cube, full)
    },
  }
}

///|
/// Insert a degenerate (unused) axis at position `axis`.
pub fn dcube_degenerate(cube : DCubeFunction, axis : Int32) -> DCubeFunction {
  {
    arity: cube.arity + 1,
    at: dims => dcube_at(cube, dcube_without_axis(dims, axis)),
  }
}

///|
pub struct DCubeBoxFace {
  axis : Int32
  hi : Bool
  cube : DCubeFunction
}

///|
pub fn dcube_box_face(
  axis : Int32,
  hi : Bool,
  cube : DCubeFunction,
) -> DCubeBoxFace {
  { axis, hi, cube, }
}

///|
/// An open box of arity `arity` in the constant type `ty`, in an
/// ambient context of `ambient_dlevel` dimensions.  The missing
/// face is `(axis arity-1) = 1` (the cap).
pub struct DCubeOpenBox {
  ty : DValue
  arity : Int32
  ambient_dlevel : Int32
  faces : Array[DCubeBoxFace]
}

///|
pub fn dcube_open_box(
  ty : DValue,
  arity : Int32,
  ambient_dlevel : Int32,
  faces : Array[DCubeBoxFace],
) -> DCubeOpenBox {
  { ty, arity, ambient_dlevel, faces, }
}

///|
pub fn dcube_box_face_of(
  box : DCubeOpenBox,
  axis : Int32,
  hi : Bool,
) -> DCubeFunction? {
  for i in 0..<box.faces.length() {
    let f = box.faces[i]
    if f.axis == axis && f.hi == hi {
      return Some(f.cube)
    }
  }
  None
}

///|
/// Every required face present, with the right arity: all side
/// faces on axes `< arity-1` and the base face `(arity-1) = 0`.
pub fn dcube_box_complete(box : DCubeOpenBox) -> Bool {
  if box.arity < 1 {
    return false
  }
  let last_axis = box.arity - 1
  for axis in 0..<last_axis {
    for hi in [false, true] {
      match dcube_box_face_of(box, axis, hi) {
        Some(cube) => if cube.arity != box.arity - 1 { return false }
        None => return false
      }
    }
  }
  match dcube_box_face_of(box, box.arity - 1, false) {
    Some(cube) => cube.arity == box.arity - 1
    None => false
  }
}

///|
/// Fresh generic dimensions for `n` axes above an ambient context.
pub fn dcube_generic_dims(ambient_dlevel : Int32, n : Int32) -> Array[Dim] {
  let out : Array[Dim] = []
  for i in 0..<n {
    out.push(DVar(ambient_dlevel + i))
  }
  out
}

///|
/// Convertibility of two `n`-cubes at generic interior dimensions.
pub fn dcube_cubes_conv(
  level : Int32,
  ambient_dlevel : Int32,
  ty : DValue,
  f : DCubeFunction,
  g : DCubeFunction,
) -> Bool {
  if f.arity != g.arity {
    return false
  }
  let gd = dcube_generic_dims(ambient_dlevel, f.arity)
  conv_at(level, ambient_dlevel + f.arity, ty, dcube_at(f, gd), dcube_at(g, gd))
}

///|
fn dcube_overlap_axis(axis : Int32, removed : Int32) -> Int32 {
  if axis < removed {
    axis
  } else {
    axis - 1
  }
}

///|
pub struct DCubeBoxReport {
  complete : Bool
  overlaps_ok : Bool
  failed_overlaps : Int32
}

///|
/// Validate an open box: completeness, plus compatibility of
/// every pair of faces on distinct axes along their common edge
/// (checked at generic dimensions of the remaining axes).
pub fn dcube_box_validate(box : DCubeOpenBox, level : Int32) -> DCubeBoxReport {
  let complete = dcube_box_complete(box)
  let mut failed = 0
  if complete && box.arity >= 2 {
    for i in 0..<box.faces.length() {
      for j in (i + 1)..<box.faces.length() {
        let a = box.faces[i]
        let b = box.faces[j]
        if a.axis == b.axis {
          continue
        }
        let a_edge = dcube_face(
          a.cube,
          dcube_overlap_axis(b.axis, a.axis),
          if b.hi {
            DOne
          } else {
            DZero
          },
        )
        let b_edge = dcube_face(
          b.cube,
          dcube_overlap_axis(a.axis, b.axis),
          if a.hi {
            DOne
          } else {
            DZero
          },
        )
        if !dcube_cubes_conv(level, box.ambient_dlevel, box.ty, a_edge, b_edge) {
          failed = failed + 1
        }
      }
    }
  }
  { complete, overlaps_ok: complete && failed == 0, failed_overlaps: failed, }
}

///|
/// Assemble the filler of a complete open box by composing along
/// the last axis.  Returns `None` for an incomplete box.  (Overlap
/// compatibility is the caller's concern -- see
/// `dcube_box_validate`; composition of an incompatible system is
/// still defined by first-match semantics but will not pass
/// `dcube_filler_faces_ok`.)
pub fn dcube_box_fill(box : DCubeOpenBox) -> DCubeFunction? {
  if !dcube_box_complete(box) {
    return None
  }
  let n = box.arity
  let base_cube = match dcube_box_face_of(box, n - 1, false) {
    Some(cube) => cube
    None => return None
  }
  let side_faces : Array[DCubeBoxFace] = []
  for i in 0..<box.faces.length() {
    let f = box.faces[i]
    if f.axis < n - 1 {
      side_faces.push(f)
    }
  }
  let ty = box.ty
  let fill_dlevel = box.ambient_dlevel + n
  Some({
    arity: n,
    at: dims => {
      if dims.length() != n {
        return DVUnit
      }
      let others = dcube_without_axis(dims, n - 1)
      let last = dims[n - 1]
      let branches : Array[DTubeBranch] = []
      for i in 0..<side_faces.length() {
        let sf = side_faces[i]
        let axis = sf.axis
        let side_cube = sf.cube
        let branch_face = face_simplify(
          if sf.hi {
            FEq1(dims[axis])
          } else {
            FEq0(dims[axis])
          },
        )
        branches.push(
          tube_branch(branch_face, (j : Dim) => {
            let full = dcube_with_axis(dims, n - 1, j)
            dcube_at(side_cube, dcube_without_axis(full, axis))
          }),
        )
      }
      let base = dcube_at(base_cube, others)
      hfill_value(ty, dsystem_of(branches), base, fill_dlevel)(last)
    },
  })
}

///|
/// The cap: the assembled filler's missing face `(arity-1) = 1`.
pub fn dcube_box_cap(box : DCubeOpenBox) -> DCubeFunction? {
  match dcube_box_fill(box) {
    Some(filler) => Some(dcube_face(filler, box.arity - 1, DOne))
    None => None
  }
}

///|
/// Whole-boundary verification: the filler restricts to every
/// supplied face, checked at generic interior dimensions.
pub fn dcube_filler_faces_ok(
  box : DCubeOpenBox,
  filler : DCubeFunction,
  level : Int32,
) -> Bool {
  if filler.arity != box.arity {
    return false
  }
  for i in 0..<box.faces.length() {
    let f = box.faces[i]
    let restricted = dcube_face(filler, f.axis, if f.hi { DOne } else { DZero })
    if !dcube_cubes_conv(level, box.ambient_dlevel, box.ty, restricted, f.cube) {
      return false
    }
  }
  true
}

///|
/// Fill and verify in one step: validate the box, assemble the
/// filler, and check the whole boundary.
pub fn dcube_box_fill_verified(
  box : DCubeOpenBox,
  level : Int32,
) -> DCubeFunction? {
  let report = dcube_box_validate(box, level)
  if !report.overlaps_ok {
    return None
  }
  match dcube_box_fill(box) {
    Some(filler) =>
      if dcube_filler_faces_ok(box, filler, level) {
        Some(filler)
      } else {
        None
      }
    None => None
  }
}

// ---------------------------------------------------------------------------
// Phase 12: stratified extensionality for host cube functions.
//
// `dcube_cubes_conv` probes one generic interior point, but a
// host cube is an arbitrary function on dimension expressions:
// it can branch on an axis being an endpoint, on two axes
// coinciding, or on connection structure (`i ∧ j`, `i ∨ j`,
// `¬i`), none of which a single generic probe sees.  The
// stratified checker evaluates both cubes on four tiers of
// dimension assignments:
//
//   A. every axis in {0, 1, fresh var} -- all faces' interiors;
//   B. every axis in {0, 1, s, t} for two shared dimensions
//      `s` (an ambient variable when one exists) and `t` --
//      diagonals and ambient collisions;
//   C. every axis in {s, ¬s, s ∧ t, s ∨ t} -- connection
//      strata;
//   D. axis-specific deep connections mixing that axis' fresh
//      variable `a` with shared/ambient dimensions `s`, `t`,
//      and `u`: `a∧s`, `a∨¬t`, `¬(a∧t)`, `(a∨s)∧¬t`,
//      `(a∧t)∨(¬a∧s)`, `¬(a∨(s∧t))`, `(s∧t)∨(a∧u)`, and
//      `(a∧(s∨u))∧¬t`.
//
// This is still a finite probe set (a host function could in
// principle hide behaviour on expressions outside it), but it
// covers every stratum of the cube's face lattice, the standard
// connection/diagonal degenerations, and the first layer of
// nested named-dimension interactions.  Tiers whose probe
// count exceeds 4096 are skipped and reported through
// `complete = false`.
// ---------------------------------------------------------------------------

///|
pub struct DCubeStratifiedReport {
  equal : Bool
  probes : Int32
  failed : Int32
  complete : Bool
}

///|
fn dcube_stratified_tier(
  level : Int32,
  dlevel : Int32,
  ty : DValue,
  f : DCubeFunction,
  g : DCubeFunction,
  pools : Array[Array[Dim]],
  stats : Array[Int32],
) -> Bool {
  let n = pools.length()
  let indices : Array[Int32] = []
  for _i in 0..<n {
    indices.push(0)
  }
  while true {
    let dims : Array[Dim] = []
    for i in 0..<n {
      dims.push(pools[i][indices[i]])
    }
    stats[0] = stats[0] + 1
    if !conv_at(level, dlevel, ty, dcube_at(f, dims), dcube_at(g, dims)) {
      stats[1] = stats[1] + 1
      return false
    }
    let mut pos = n - 1
    while pos >= 0 {
      indices[pos] = indices[pos] + 1
      if indices[pos] < pools[pos].length() {
        break
      }
      indices[pos] = 0
      pos = pos - 1
    }
    if pos < 0 {
      break
    }
  }
  true
}

///|
pub fn dcube_cubes_conv_stratified_report(
  level : Int32,
  ambient_dlevel : Int32,
  ty : DValue,
  f : DCubeFunction,
  g : DCubeFunction,
) -> DCubeStratifiedReport {
  if f.arity != g.arity {
    return { equal: false, probes: 0, failed: 0, complete: false, }
  }
  let n = f.arity
  if n == 0 {
    let eq = conv_at(
      level,
      ambient_dlevel,
      ty,
      dcube_at(f, []),
      dcube_at(g, []),
    )
    return {
      equal: eq,
      probes: 1,
      failed: if eq {
        0
      } else {
        1
      },
      complete: true,
    }
  }
  let dlevel = ambient_dlevel + n + 2
  let shared_s = DVar(0)
  let shared_t = DVar(ambient_dlevel + n)
  let shared_u = DVar(ambient_dlevel + n + 1)
  let tiers : Array[Array[Array[Dim]]] = []
  let tier_a : Array[Array[Dim]] = []
  for i in 0..<n {
    tier_a.push([DZero, DOne, DVar(ambient_dlevel + i)])
  }
  tiers.push(tier_a)
  let tier_b : Array[Array[Dim]] = []
  for _i in 0..<n {
    tier_b.push([DZero, DOne, shared_s, shared_t])
  }
  tiers.push(tier_b)
  let tier_c : Array[Array[Dim]] = []
  for _i in 0..<n {
    tier_c.push([
      shared_s,
      DNeg(shared_s),
      DAnd(shared_s, shared_t),
      DOr(shared_s, shared_t),
    ])
  }
  tiers.push(tier_c)
  let tier_d : Array[Array[Dim]] = []
  for i in 0..<n {
    tier_d.push(
      dcube_deep_axis_pool(
        DVar(ambient_dlevel + i),
        shared_s,
        shared_t,
        shared_u,
      ),
    )
  }
  tiers.push(tier_d)
  let stats = [0, 0]
  let mut complete = true
  for t in 0..<tiers.length() {
    let pools = tiers[t]
    let mut count = 1
    for i in 0..<pools.length() {
      count = count * pools[i].length()
    }
    if count > 4096 {
      complete = false
      continue
    }
    if !dcube_stratified_tier(level, dlevel, ty, f, g, pools, stats) {
      return { equal: false, probes: stats[0], failed: stats[1], complete, }
    }
  }
  { equal: true, probes: stats[0], failed: 0, complete, }
}

///|
pub fn dcube_cubes_conv_stratified(
  level : Int32,
  ambient_dlevel : Int32,
  ty : DValue,
  f : DCubeFunction,
  g : DCubeFunction,
) -> Bool {
  dcube_cubes_conv_stratified_report(level, ambient_dlevel, ty, f, g).equal
}

///|
/// Report of high-arity `GF(8)` orthogonal-array (`OA(8^strength, m, 8, strength)`)
/// deep-connection host-cube probing.
pub struct DCubeCoveringReport {
  equal : Bool
  probes : Int32
  failed : Int32
  interaction_strength : Int32
  complete_for_strength : Bool
}

///|
/// Multiplication in `GF(8) = GF(2)[x] / (x^3 + x + 1)` on elements `0..7`.
fn gf8_mul(a0 : Int32, b0 : Int32) -> Int32 {
  let mut a = a0 & 7
  let mut b = b0 & 7
  let mut res = 0
  for _bit in 0..<3 {
    if (b & 1) != 0 {
      res = res ^ a
    }
    let hi = a & 4
    a = (a << 1) & 7
    if hi != 0 {
      a = a ^ 3 // x^3 == x + 1
    }
    b = b >> 1
  }
  res
}

///|
fn dcube_deep_axis_pool(
  axis_var : Dim,
  shared_s : Dim,
  shared_t : Dim,
  shared_u : Dim,
) -> Array[Dim] {
  [
    DAnd(axis_var, shared_s),
    DOr(axis_var, DNeg(shared_t)),
    DNeg(DAnd(axis_var, shared_t)),
    DAnd(DOr(axis_var, shared_s), DNeg(shared_t)),
    DOr(DAnd(axis_var, shared_t), DAnd(DNeg(axis_var), shared_s)),
    DNeg(DOr(axis_var, DAnd(shared_s, shared_t))),
    DOr(DAnd(shared_s, shared_t), DAnd(axis_var, shared_u)),
    DAnd(DAnd(axis_var, DOr(shared_s, shared_u)), DNeg(shared_t)),
  ]
}

///|
/// Projective `P^1(GF(8))` Reed–Solomon orthogonal-array host-cube
/// checker (`strength = 2` -> `64` deep probes, `strength = 3` -> `512`
/// deep probes, `strength = 4` -> `4096` deep probes for any arity
/// `1 <= m <= 9`), unified via arbitrary-degree `< strength` polynomial
/// evaluation over `GF(8)` with projective infinity `[1 : 0] -> c_{t-1}`.
/// Every `t`-subset of axes (`t = strength`) visits all `8^t`
/// deep-connection symbol tuples in exact balance.
pub fn dcube_cubes_conv_covering_report(
  level : Int32,
  ambient_dlevel : Int32,
  ty : DValue,
  f : DCubeFunction,
  g : DCubeFunction,
  strength~ : Int32 = 2,
) -> DCubeCoveringReport {
  if f.arity != g.arity || strength < 2 || strength > 4 {
    return DCubeCoveringReport::{
      equal: false,
      probes: 0,
      failed: 0,
      interaction_strength: strength,
      complete_for_strength: false,
    }
  }
  let n = f.arity
  let base_rep = dcube_cubes_conv_stratified_report(
    level, ambient_dlevel, ty, f, g,
  )
  if !base_rep.equal {
    return DCubeCoveringReport::{
      equal: false,
      probes: base_rep.probes,
      failed: base_rep.failed,
      interaction_strength: strength,
      complete_for_strength: base_rep.complete,
    }
  }
  if n <= 1 {
    return DCubeCoveringReport::{
      equal: true,
      probes: base_rep.probes,
      failed: 0,
      interaction_strength: strength,
      complete_for_strength: true,
    }
  }
  if n > 9 {
    return DCubeCoveringReport::{
      equal: true,
      probes: base_rep.probes,
      failed: 0,
      interaction_strength: strength,
      complete_for_strength: false,
    }
  }
  let dlevel = ambient_dlevel + n + 2
  let shared_s = DVar(0)
  let shared_t = DVar(ambient_dlevel + n)
  let shared_u = DVar(ambient_dlevel + n + 1)
  let pools : Array[Array[Dim]] = []
  for i in 0..<n {
    pools.push(
      dcube_deep_axis_pool(
        DVar(ambient_dlevel + i),
        shared_s,
        shared_t,
        shared_u,
      ),
    )
  }
  let mut total_rows = 1
  for _d in 0..<strength {
    total_rows = total_rows * 8
  }
  let mut probes = base_rep.probes
  for row in 0..<total_rows {
    let coeffs : Array[Int32] = []
    let mut tmp = row
    for _d in 0..<strength {
      coeffs.push(tmp & 7)
      tmp = tmp >> 3
    }
    let dims : Array[Dim] = []
    for axis in 0..<n {
      let sym = if axis < 8 {
        // Horner evaluation c_0 + x*(c_1 + x*(...)) over GF(8).
        let mut acc = 0
        let mut deg = strength - 1
        while deg >= 0 {
          acc = gf8_mul(acc, axis) ^ coeffs[deg]
          deg = deg - 1
        }
        acc
      } else {
        coeffs[strength - 1] // point at infinity [1 : 0] on P^1(GF(8))
      }
      dims.push(pools[axis][sym])
    }
    probes = probes + 1
    if !conv_at(level, dlevel, ty, dcube_at(f, dims), dcube_at(g, dims)) {
      return DCubeCoveringReport::{
        equal: false,
        probes,
        failed: 1,
        interaction_strength: strength,
        complete_for_strength: true,
      }
    }
  }
  DCubeCoveringReport::{
    equal: true,
    probes,
    failed: 0,
    interaction_strength: strength,
    complete_for_strength: true,
  }
}

///|
/// Multiplication in `GF(4) = GF(2)[a] / (a^2 + a + 1)` represented on `0..3`.
fn gf4_mul(a0 : Int32, b0 : Int32) -> Int32 {
  let mut a = a0 & 3
  let mut b = b0 & 3
  let mut res = 0
  for _k in 0..<2 {
    if (b & 1) != 0 {
      res = res ^ a
    }
    let hi = a & 2
    a = (a << 1) & 3
    if hi != 0 {
      a = a ^ 3 // a^2 == a + 1
    }
    b = b >> 1
  }
  res
}

///|
fn dcube_four_stratum_pool(
  axis_var : Dim,
  shared_s : Dim,
  shared_t : Dim,
) -> Array[Dim] {
  [
    DZero,
    DOne,
    axis_var,
    DAnd(DOr(axis_var, shared_s), DNeg(shared_t)),
  ]
}

///|
fn dcube_enum_t_subsets(
  n : Int32,
  t : Int32,
  start : Int32,
  cur : Array[Int32],
  out : Array[Array[Int32]],
) -> Unit {
  if cur.length() == t {
    let copy : Array[Int32] = []
    for i in 0..<cur.length() {
      copy.push(cur[i])
    }
    out.push(copy)
    return
  }
  let rem = t - cur.length()
  for v in start..<(n - rem + 1) {
    cur.push(v)
    dcube_enum_t_subsets(n, t, v + 1, cur, out)
    let _ = cur.pop()
  }
}

///|
fn dcube_subset_is_rainbow(coloring : Array[Int32], sub : Array[Int32]) -> Bool {
  let mut mask = 0
  for i in 0..<sub.length() {
    let c = coloring[sub[i]]
    let bit = 1 << c
    if (mask & bit) != 0 {
      return false
    }
    mask = mask | bit
  }
  true
}

///|
/// Deterministic greedy Perfect Hash Family `PHF(M; n, 5, t)`: constructs
/// `5`-colorings of `0..<n` such that every `t`-subset (`2 <= t <= 4`)
/// receives `t` distinct colors in `0..<5` under at least one coloring.
/// Composing `PHF(M; n, 5, t)` with Bush's `OA(4^t; t, 5, 4)` over
/// `P^1(GF(4))` yields a certified `100%`-complete strength-`t` covering
/// array in `<= M * 4^t` rows across up to `n <= 16` cube dimensions.
pub fn dcube_phf_5colors(n : Int32, strength : Int32) -> Array[Array[Int32]] {
  if n <= 0 || strength < 2 || strength > 4 {
    return []
  }
  if n <= 5 {
    let id_col : Array[Int32] = []
    for i in 0..<n {
      id_col.push(i)
    }
    return [id_col]
  }
  let eff_t = if strength > n { n } else { strength }
  let subsets : Array[Array[Int32]] = []
  dcube_enum_t_subsets(n, eff_t, 0, [], subsets)
  let uncovered : Array[Bool] = []
  for _i in 0..<subsets.length() {
    uncovered.push(true)
  }
  let mut rem_count = subsets.length()
  let colorings : Array[Array[Int32]] = []

  while rem_count > 0 {
    // Pick the first uncovered subset to seed `eff_t` distinct colors, then
    // assign each remaining element `v` the color in `0..<5` maximizing newly
    // rainbow uncovered `t`-subsets completed at `v`.
    let mut seed_idx = 0
    for si in 0..<subsets.length() {
      if uncovered[si] {
        seed_idx = si
        break
      }
    }
    let col : Array[Int32] = []
    for _v in 0..<n {
      col.push(-1)
    }
    let seed_sub = subsets[seed_idx]
    for k in 0..<seed_sub.length() {
      col[seed_sub[k]] = k
    }
    for v in 0..<n {
      if col[v] >= 0 {
        continue
      }
      let mut best_c = 0
      let mut best_gain = -1
      for cand_c in 0..<5 {
        col[v] = cand_c
        let mut gain = 0
        for si in 0..<subsets.length() {
          if !uncovered[si] {
            continue
          }
          let sub = subsets[si]
          let mut all_assigned = true
          let mut mask = 0
          let mut clash = false
          for k in 0..<sub.length() {
            let cv = col[sub[k]]
            if cv < 0 {
              all_assigned = false
            } else {
              let bit = 1 << cv
              if (mask & bit) != 0 {
                clash = true
                break
              }
              mask = mask | bit
            }
          }
          if !clash {
            gain = gain + (if all_assigned { 16 } else { 1 })
          }
        }
        if gain > best_gain {
          best_gain = gain
          best_c = cand_c
        }
      }
      col[v] = best_c
    }
    colorings.push(col)
    for si in 0..<subsets.length() {
      if uncovered[si] && dcube_subset_is_rainbow(col, subsets[si]) {
        uncovered[si] = false
        rem_count = rem_count - 1
      }
    }
  }
  colorings
}

///|
/// High-strength (`2 <= strength <= 4`, including `t = 4` four-way axis
/// interaction!) host-cube covering checker up to `arity <= 16` via
/// `PHF(M; n, 5, t) (x) Bush-OA(4^t; t, 5, 4)` over `P^1(GF(4))`.
///
/// For `n = 8, strength = 4`, covers all `C(8, 4) * 4^4 = 17,920` four-way
/// `{0, 1, r_i, (r_i v s) ^ ~t}` interactions in ~`1024` probes (`> 60x`
/// smaller than the `4^8 = 65,536` full Cartesian grid), catching 4-axis
/// simultaneous rogue branches that evade `strength = 3`.
pub fn dcube_cubes_conv_covering_phf_report(
  level : Int32,
  ambient_dlevel : Int32,
  ty : DValue,
  f : DCubeFunction,
  g : DCubeFunction,
  strength~ : Int32 = 4,
) -> DCubeCoveringReport {
  if f.arity != g.arity || strength < 2 || strength > 4 {
    return DCubeCoveringReport::{
      equal: false,
      probes: 0,
      failed: 0,
      interaction_strength: strength,
      complete_for_strength: false,
    }
  }
  let n = f.arity
  if n == 0 {
    let ok = conv_at(level, ambient_dlevel, ty, dcube_at(f, []), dcube_at(g, []))
    return DCubeCoveringReport::{
      equal: ok,
      probes: 1,
      failed: if ok { 0 } else { 1 },
      interaction_strength: strength,
      complete_for_strength: true,
    }
  }
  if n == 1 {
    let rep = dcube_cubes_conv_stratified_report(level, ambient_dlevel, ty, f, g)
    return DCubeCoveringReport::{
      equal: rep.equal,
      probes: rep.probes,
      failed: rep.failed,
      interaction_strength: strength,
      complete_for_strength: true,
    }
  }
  if n > 16 {
    let rep = dcube_cubes_conv_stratified_report(level, ambient_dlevel, ty, f, g)
    return DCubeCoveringReport::{
      equal: rep.equal,
      probes: rep.probes,
      failed: rep.failed,
      interaction_strength: strength,
      complete_for_strength: false,
    }
  }
  let eff_t = if strength > n { n } else { strength }
  let colorings = dcube_phf_5colors(n, eff_t)
  let dlevel = ambient_dlevel + n + 2
  let shared_s = DVar(ambient_dlevel + n)
  let shared_t = DVar(ambient_dlevel + n + 1)
  let pools : Array[Array[Dim]] = []
  for i in 0..<n {
    pools.push(
      dcube_four_stratum_pool(DVar(ambient_dlevel + i), shared_s, shared_t),
    )
  }
  let mut bush_rows = 1
  for _d in 0..<eff_t {
    bush_rows = bush_rows * 4
  }
  let seen_keys : Array[Int32] = []
  let mut probes = 0
  for ci in 0..<colorings.length() {
    let col = colorings[ci]
    for row in 0..<bush_rows {
      let coeffs : Array[Int32] = []
      let mut tmp = row
      for _d in 0..<eff_t {
        coeffs.push(tmp & 3)
        tmp = tmp >> 2
      }
      // Deduplicate rows when `n <= 15` (2 bits per axis fits in 30-bit Int32).
      let syms : Array[Int32] = []
      let mut packed = 0
      for axis in 0..<n {
        let c = col[axis]
        let sym = if c < 4 {
          let mut acc = 0
          let mut deg = eff_t - 1
          while deg >= 0 {
            acc = gf4_mul(acc, c) ^ coeffs[deg]
            deg = deg - 1
          }
          acc
        } else {
          coeffs[eff_t - 1] // point at infinity [1 : 0] on P^1(GF(4))
        }
        syms.push(sym)
        if n <= 15 {
          packed = (packed << 2) | sym
        }
      }
      if n <= 15 {
        if seen_keys.contains(packed) {
          continue
        }
        seen_keys.push(packed)
      }
      let dims : Array[Dim] = []
      for axis in 0..<n {
        dims.push(pools[axis][syms[axis]])
      }
      probes = probes + 1
      if !conv_at(level, dlevel, ty, dcube_at(f, dims), dcube_at(g, dims)) {
        return DCubeCoveringReport::{
          equal: false,
          probes,
          failed: 1,
          interaction_strength: eff_t,
          complete_for_strength: true,
        }
      }
    }
  }
  DCubeCoveringReport::{
    equal: true,
    probes,
    failed: 0,
    interaction_strength: eff_t,
    complete_for_strength: true,
  }
}

///|
/// A kernel-checked, presheaf-natural `n`-cube (`Hom(y[n], ty)` in the
/// De Morgan cubical CwF).  Unlike an arbitrary host closure
/// `(Array[Dim]) -> DValue` which could inspect dimension syntax and break
/// functoriality, `CheckedDCube` stores a kernel type-checked `DTerm`
/// body under `arity` fresh dimension binders; evaluating at `dims` IS
/// syntactic dimension substitution, guaranteeing naturality across all
/// cube morphisms `sigma : []^m -> []^arity`.
pub struct CheckedDCube {
  arity : Int32
  body : DTerm
  ty : DValue
  ctx : DEnv
  env : DEnv
  denv : DDimEnv
  cube : DCubeFunction
}

///|
/// Validate `body : ty` under `arity` fresh dimension variables above
/// `(ctx, env, denv)` and package it as a natural `CheckedDCube`.
pub fn checked_dcube_make(
  arity : Int32,
  body : DTerm,
  ty : DValue,
  ctx : DEnv,
  env : DEnv,
  denv : DDimEnv,
) -> CheckedDCube? {
  if arity < 0 {
    return None
  }
  let base_dlevel = ddim_len(denv)
  let fresh_dims : Array[Dim] = []
  for i in 0..<arity {
    fresh_dims.push(DVar(base_dlevel + i))
  }
  let check_denv = ddim_extend(fresh_dims, denv)
  match d_check(body, ty, ctx, env, check_denv) {
    Some(_) => {
      let cube = dcube_function(arity, dims => {
        deval_dim(body, env, ddim_extend(dims, denv))
      })
      Some(CheckedDCube::{ arity, body, ty, ctx, env, denv, cube, })
    }
    None => None
  }
}

///|
pub fn checked_dcube_closed(
  arity : Int32,
  body : DTerm,
  ty_term : DTerm,
) -> CheckedDCube? {
  match d_as_type(ty_term, denv_empty(), denv_empty(), ddim_empty()) {
    Some(tv) =>
      checked_dcube_make(
        arity,
        body,
        tv.value,
        denv_empty(),
        denv_empty(),
        ddim_empty(),
      )
    None => None
  }
}

///|
/// Cubical Yoneda Universal Extensionality Theorem:
/// By the Yoneda Lemma on the De Morgan cube category `[]`, two natural
/// `n`-cubes `c1, c2 : y[n] -> ty` in matching ambient contexts are equal
/// at **every** dimension substitution `sigma : []^m -> []^n` (`0`, `1`,
/// diagonals, connections, reversals, arbitrary `m`) **if and only if**
/// they are convertible at the **single** generic point `(i_0, ..., i_{n-1})`!
/// Decides exact universal extensionality in `O(1)` (`1` kernel conversion
/// check) for arbitrary arity `n = 16, 32, ...` with zero grid blowup.
pub fn checked_dcube_extensional_eq(c1 : CheckedDCube, c2 : CheckedDCube) -> Bool {
  if c1.arity != c2.arity ||
    denv_len(c1.ctx) != denv_len(c2.ctx) ||
    ddim_len(c1.denv) != ddim_len(c2.denv) {
    return false
  }
  let level = denv_len(c1.ctx)
  let base_dlevel = ddim_len(c1.denv)
  if !conv_ty(level, base_dlevel, c1.ty, c2.ty) {
    return false
  }
  let gen_dims : Array[Dim] = []
  for i in 0..<c1.arity {
    gen_dims.push(DVar(base_dlevel + i))
  }
  conv_at(
    level,
    base_dlevel + c1.arity,
    c1.ty,
    dcube_at(c1.cube, gen_dims),
    dcube_at(c2.cube, gen_dims),
  )
}

///|
pub(all) struct DCubeYonedaReport {
  natural : Bool
  generic_reified_term : DTerm
  audited_substitutions : Int32
  failed_substitutions : Int32
} derive(Debug, Eq)

///|
pub extend DCubeYonedaReport with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend DCubeYonedaReport with Eq::{not_equal, equal}

///|
/// Reify a host `DCubeFunction` at its Yoneda generic `n`-cube
/// `(i_0, ..., i_{n-1})` via `quote_at` into a syntactic `DTerm`
/// `t_yoneda`, and audit presheaf naturality
///   `sigma*(f(id_[n])) == f(sigma(id_[n]))`
/// across faces, vertices, diagonals, reversals, and strength-4 `PHF (x)
/// Bush` covering morphisms (`arity <= 16`).  Every natural / kernel-checked
/// cube satisfies `natural == true`; rogue host closures that branch on
/// syntactic dimension shapes violate naturality and are caught with
/// `natural == false`.
pub fn dcube_yoneda_audit_report(
  level : Int32,
  ambient_dlevel : Int32,
  ty : DValue,
  f : DCubeFunction,
) -> DCubeYonedaReport {
  let n = f.arity
  if n < 0 || level < 0 || ambient_dlevel < 0 {
    return DCubeYonedaReport::{
      natural: false,
      generic_reified_term: DUnitLit,
      audited_substitutions: 0,
      failed_substitutions: 1,
    }
  }
  let gen_dims : Array[Dim] = []
  for i in 0..<n {
    gen_dims.push(DVar(ambient_dlevel + i))
  }
  let v_gen = dcube_at(f, gen_dims)
  let t_yoneda = quote_at(level, ambient_dlevel + n, ty, v_gen)
  let term_vars : Array[DValue] = []
  for k in 0..<level {
    term_vars.push(DVNeutral(DNVar(k)))
  }
  let term_env = denv_extend(term_vars, denv_empty())
  let yoneda_cube = dcube_function(n, dims => {
    let env_dims : Array[Dim] = []
    for a in 0..<ambient_dlevel {
      env_dims.push(DVar(a))
    }
    for i in 0..<n {
      env_dims.push(dims[i])
    }
    deval_dim(t_yoneda, term_env, ddim_extend(env_dims, ddim_empty()))
  })

  if n == 0 {
    let ok = conv_at(
      level,
      ambient_dlevel,
      ty,
      dcube_at(yoneda_cube, []),
      dcube_at(f, []),
    )
    return DCubeYonedaReport::{
      natural: ok,
      generic_reified_term: t_yoneda,
      audited_substitutions: 1,
      failed_substitutions: if ok { 0 } else { 1 },
    }
  }
  let strat = dcube_cubes_conv_stratified_report(
    level, ambient_dlevel, ty, yoneda_cube, f,
  )
  if !strat.equal {
    return DCubeYonedaReport::{
      natural: false,
      generic_reified_term: t_yoneda,
      audited_substitutions: strat.probes,
      failed_substitutions: strat.failed,
    }
  }
  if n >= 2 && n <= 16 {
    let phf = dcube_cubes_conv_covering_phf_report(
      level,
      ambient_dlevel,
      ty,
      yoneda_cube,
      f,
      strength=4,
    )
    return DCubeYonedaReport::{
      natural: phf.equal,
      generic_reified_term: t_yoneda,
      audited_substitutions: strat.probes + phf.probes,
      failed_substitutions: phf.failed,
    }
  }
  DCubeYonedaReport::{
    natural: true,
    generic_reified_term: t_yoneda,
    audited_substitutions: strat.probes,
    failed_substitutions: 0,
  }
}

///|
/// Stratified box validation: pairwise face overlaps are
/// compared on all strata of the shared edge, not only at its
/// generic interior.
pub fn dcube_box_validate_stratified(
  box : DCubeOpenBox,
  level : Int32,
) -> DCubeBoxReport {
  let complete = dcube_box_complete(box)
  let mut failed = 0
  if complete && box.arity >= 2 {
    for i in 0..<box.faces.length() {
      for j in (i + 1)..<box.faces.length() {
        let a = box.faces[i]
        let b = box.faces[j]
        if a.axis == b.axis {
          continue
        }
        let a_edge = dcube_face(
          a.cube,
          dcube_overlap_axis(b.axis, a.axis),
          if b.hi {
            DOne
          } else {
            DZero
          },
        )
        let b_edge = dcube_face(
          b.cube,
          dcube_overlap_axis(a.axis, b.axis),
          if a.hi {
            DOne
          } else {
            DZero
          },
        )
        if !dcube_cubes_conv_stratified(
            level,
            box.ambient_dlevel,
            box.ty,
            a_edge,
            b_edge,
          ) {
          failed = failed + 1
        }
      }
    }
  }
  { complete, overlaps_ok: complete && failed == 0, failed_overlaps: failed, }
}

///|
pub fn dcube_filler_faces_ok_stratified(
  box : DCubeOpenBox,
  filler : DCubeFunction,
  level : Int32,
) -> Bool {
  if filler.arity != box.arity {
    return false
  }
  for i in 0..<box.faces.length() {
    let f = box.faces[i]
    let restricted = dcube_face(filler, f.axis, if f.hi { DOne } else { DZero })
    if !dcube_cubes_conv_stratified(
        level,
        box.ambient_dlevel,
        box.ty,
        restricted,
        f.cube,
      ) {
      return false
    }
  }
  true
}

///|
/// Fill and verify with stratified extensionality throughout.
pub fn dcube_box_fill_verified_stratified(
  box : DCubeOpenBox,
  level : Int32,
) -> DCubeFunction? {
  let report = dcube_box_validate_stratified(box, level)
  if !report.overlaps_ok {
    return None
  }
  match dcube_box_fill(box) {
    Some(filler) =>
      if dcube_filler_faces_ok_stratified(box, filler, level) {
        Some(filler)
      } else {
        None
      }
    None => None
  }
}
