///|
/// Phase 11: n-dimensional polynomial cubes over Q.
///
/// Semantic cubes elsewhere in the project are opaque host
/// functions (`(Array[Double]) -> CVec`, `(Array[Dim]) -> DValue`):
/// they can be evaluated but not inspected, compared only by
/// sampling or by a conversion oracle.  A *polynomial cube*
/// instead is a vector of multivariate polynomials (`Poly`) in
/// the cube atoms `0 .. dim-1` with rational coefficients: face
/// restriction, degeneracy and composition are polynomial
/// substitutions, equality is decidable (`poly_eq`), and the
/// cubical identities hold as exact polynomial identities.
///
/// Open boxes are filled by the iterated connection blend
///
///   F := base
///   F := F + w_{k,e} * (S_{k,e} - F|_{x_k = e})
///        for each side face (k, e), w_{k,0} = 1 - x_k, w_{k,1} = x_k
///
/// For a compatible box this restricts to every supplied face:
/// updating face `(l, f)` changes `F` on an earlier face `(k, e)`
/// by a multiple of `S_{l,f} - F|_{x_l=f}` restricted to
/// `x_k = e`, which vanishes by box compatibility on the common
/// edge; the opposite face of the same axis is preserved because
/// `w_{k,1-e}` vanishes at `x_k = e`; and the base `t = 0` is
/// preserved because each side face starts at the base's face.
/// All of this is verified below by exact polynomial equality.

// ---------------------------------------------------------------------------
// Polynomial substitution helpers
// ---------------------------------------------------------------------------

///|
fn rat_pow_int32(base : Rat, exp : Int32) -> Rat {
  let mut out = rat_one()
  for _i in 0..<exp {
    out = rat_mul(out, base)
  }
  out
}

///|
fn poly_exp_at(term : PolyTerm, atom : Int32) -> Int32 {
  if atom < term.exps.length() {
    term.exps[atom]
  } else {
    0
  }
}

///|
/// Substitute a rational for one atom, keeping atom numbering.
pub fn poly_eval_var(p : Poly, atom : Int32, value : Rat) -> Poly {
  let raw : Array[PolyTerm] = []
  for ti in 0..<p.terms.length() {
    let t = p.terms[ti]
    let e = poly_exp_at(t, atom)
    let exps : Array[Int32] = []
    for i in 0..<t.exps.length() {
      exps.push(if i == atom { 0 } else { t.exps[i] })
    }
    raw.push({ coeff: rat_mul(t.coeff, rat_pow_int32(value, e)), exps, })
  }
  poly_normalize(raw)
}

///|
/// Insert a fresh atom at position `at`: atoms `>= at` shift up
/// by one, the new atom does not occur.
pub fn poly_insert_atom(p : Poly, at : Int32) -> Poly {
  let raw : Array[PolyTerm] = []
  for ti in 0..<p.terms.length() {
    let t = p.terms[ti]
    let exps : Array[Int32] = []
    for i in 0..<t.exps.length() {
      if i == at {
        exps.push(0)
      }
      exps.push(t.exps[i])
    }
    if at >= t.exps.length() {
      exps.push(0)
    }
    raw.push({ coeff: t.coeff, exps, })
  }
  poly_normalize(raw)
}

///|
/// Drop atom position `at` from the numbering (atoms above shift
/// down).  Terms containing the atom map it to `1`, so callers
/// first substitute its value (`poly_eval_var`).
pub fn poly_drop_atom(p : Poly, at : Int32) -> Poly {
  let raw : Array[PolyTerm] = []
  for ti in 0..<p.terms.length() {
    let t = p.terms[ti]
    let exps : Array[Int32] = []
    for i in 0..<t.exps.length() {
      if i != at {
        exps.push(t.exps[i])
      }
    }
    raw.push({ coeff: t.coeff, exps, })
  }
  poly_normalize(raw)
}

///|
/// Simultaneous substitution: atom `i` is replaced by
/// `replacements[i]` (atoms past the list are kept).
pub fn poly_subst_all(p : Poly, replacements : Array[Poly]) -> Poly {
  let mut out = poly_zero()
  for ti in 0..<p.terms.length() {
    let t = p.terms[ti]
    let mut term_poly = poly_const(t.coeff)
    for v in 0..<t.exps.length() {
      let e = t.exps[v]
      if e > 0 {
        let base = if v < replacements.length() {
          replacements[v]
        } else {
          poly_var(v)
        }
        for _k in 0..<e {
          term_poly = poly_mul(term_poly, base)
        }
      }
    }
    out = poly_add(out, term_poly)
  }
  out
}

///|
/// Evaluate at a rational point (atoms past the point are `0`).
pub fn poly_eval_point(p : Poly, point : Array[Rat]) -> Rat {
  let mut sum = rat_zero()
  for ti in 0..<p.terms.length() {
    let t = p.terms[ti]
    let mut value = t.coeff
    for v in 0..<t.exps.length() {
      if t.exps[v] > 0 {
        let base = if v < point.length() { point[v] } else { rat_zero() }
        value = rat_mul(value, rat_pow_int32(base, t.exps[v]))
      }
    }
    sum = rat_add(sum, value)
  }
  sum
}

// ---------------------------------------------------------------------------
// Polynomial cubes
// ---------------------------------------------------------------------------

///|
/// An `dim`-cube in `Q^coords.length()`: coordinate polynomials
/// in the cube atoms `0 .. dim-1`.
pub struct PolyCube {
  dim : Int32
  coords : Array[Poly]
}

///|
pub fn poly_cube(dim : Int32, coords : Array[Poly]) -> PolyCube {
  { dim, coords, }
}

///|
pub fn poly_cube_const(dim : Int32, point : Array[Rat]) -> PolyCube {
  let coords : Array[Poly] = []
  for i in 0..<point.length() {
    coords.push(poly_const(point[i]))
  }
  { dim, coords, }
}

///|
/// The identity `n`-cube in `Q^n`.
pub fn poly_cube_identity(n : Int32) -> PolyCube {
  let coords : Array[Poly] = []
  for i in 0..<n {
    coords.push(poly_var(i))
  }
  { dim: n, coords, }
}

///|
pub fn poly_cube_eq(a : PolyCube, b : PolyCube) -> Bool {
  if a.dim != b.dim || a.coords.length() != b.coords.length() {
    return false
  }
  for i in 0..<a.coords.length() {
    if !poly_eq(a.coords[i], b.coords[i]) {
      return false
    }
  }
  true
}

///|
pub fn poly_cube_eval(c : PolyCube, point : Array[Rat]) -> Array[Rat] {
  let out : Array[Rat] = []
  for i in 0..<c.coords.length() {
    out.push(poly_eval_point(c.coords[i], point))
  }
  out
}

///|
/// Face restriction: set atom `axis` to the endpoint and renumber
/// the remaining atoms down, giving a `(dim-1)`-cube.
pub fn poly_cube_face(c : PolyCube, axis : Int32, hi : Bool) -> PolyCube {
  let value = if hi { rat_one() } else { rat_zero() }
  let coords : Array[Poly] = []
  for i in 0..<c.coords.length() {
    coords.push(poly_drop_atom(poly_eval_var(c.coords[i], axis, value), axis))
  }
  { dim: c.dim - 1, coords, }
}

///|
/// Degeneracy: insert a dummy atom at position `axis`.
pub fn poly_cube_degeneracy(c : PolyCube, axis : Int32) -> PolyCube {
  let coords : Array[Poly] = []
  for i in 0..<c.coords.length() {
    coords.push(poly_insert_atom(c.coords[i], axis))
  }
  { dim: c.dim + 1, coords, }
}

///|
/// Composition of cubes as polynomial maps: if `f` is a `k`-cube
/// in `Q^n` and `g` an `n`-cube in `Q^m`, the composite is the
/// `k`-cube in `Q^m` substituting `f`'s coordinates for `g`'s
/// atoms.  A dimension mismatch yields the constant zero cube of
/// `f`'s dimension and `g`'s codimension.
pub fn poly_cube_compose(f : PolyCube, g : PolyCube) -> PolyCube {
  if f.coords.length() != g.dim {
    let zeros : Array[Rat] = []
    for _i in 0..<g.coords.length() {
      zeros.push(rat_zero())
    }
    return poly_cube_const(f.dim, zeros)
  }
  let coords : Array[Poly] = []
  for i in 0..<g.coords.length() {
    coords.push(poly_subst_all(g.coords[i], f.coords))
  }
  { dim: f.dim, coords, }
}

///|
/// Pointwise sum/difference (in the ambient affine space `Q^m`).
pub fn poly_cube_add(a : PolyCube, b : PolyCube) -> PolyCube {
  let coords : Array[Poly] = []
  for i in 0..<a.coords.length() {
    coords.push(poly_add(a.coords[i], b.coords[i]))
  }
  { dim: a.dim, coords, }
}

///|
pub fn poly_cube_sub(a : PolyCube, b : PolyCube) -> PolyCube {
  let coords : Array[Poly] = []
  for i in 0..<a.coords.length() {
    coords.push(poly_sub(a.coords[i], b.coords[i]))
  }
  { dim: a.dim, coords, }
}

///|
/// Scalar (polynomial) multiple of a cube.
pub fn poly_cube_scale(s : Poly, c : PolyCube) -> PolyCube {
  let coords : Array[Poly] = []
  for i in 0..<c.coords.length() {
    coords.push(poly_mul(s, c.coords[i]))
  }
  { dim: c.dim, coords, }
}

// ---------------------------------------------------------------------------
// Open boxes and the connection-blend filler
// ---------------------------------------------------------------------------

///|
pub struct PolyBoxFace {
  axis : Int32
  hi : Bool
  cube : PolyCube
}

///|
pub fn poly_box_face(axis : Int32, hi : Bool, cube : PolyCube) -> PolyBoxFace {
  { axis, hi, cube, }
}

///|
/// An open box of dimension `dim`, missing the cap
/// `(axis dim-1) = 1`.
pub struct PolyOpenBox {
  dim : Int32
  faces : Array[PolyBoxFace]
}

///|
pub fn poly_open_box(dim : Int32, faces : Array[PolyBoxFace]) -> PolyOpenBox {
  { dim, faces, }
}

///|
pub fn poly_box_face_of(
  box : PolyOpenBox,
  axis : Int32,
  hi : Bool,
) -> PolyCube? {
  for i in 0..<box.faces.length() {
    let f = box.faces[i]
    if f.axis == axis && f.hi == hi {
      return Some(f.cube)
    }
  }
  None
}

///|
fn poly_box_complete(box : PolyOpenBox) -> Bool {
  if box.dim < 1 {
    return false
  }
  let last = box.dim - 1
  for axis in 0..<last {
    for hi in [false, true] {
      match poly_box_face_of(box, axis, hi) {
        Some(cube) => if cube.dim != box.dim - 1 { return false }
        None => return false
      }
    }
  }
  match poly_box_face_of(box, last, false) {
    Some(cube) => cube.dim == box.dim - 1
    None => false
  }
}

///|
/// Completeness plus exact pairwise edge compatibility (faces of
/// faces agree as polynomials).
pub fn poly_box_validate(box : PolyOpenBox) -> Bool {
  if !poly_box_complete(box) {
    return false
  }
  for i in 0..<box.faces.length() {
    for j in (i + 1)..<box.faces.length() {
      let a = box.faces[i]
      let b = box.faces[j]
      if a.axis == b.axis {
        continue
      }
      let a_axis_in_b = if a.axis < b.axis { a.axis } else { a.axis - 1 }
      let b_axis_in_a = if b.axis < a.axis { b.axis } else { b.axis - 1 }
      let a_edge = poly_cube_face(a.cube, b_axis_in_a, b.hi)
      let b_edge = poly_cube_face(b.cube, a_axis_in_b, a.hi)
      if !poly_cube_eq(a_edge, b_edge) {
        return false
      }
    }
  }
  true
}

///|
/// Restrict a cube to `x_axis = e` *without* renumbering (an
/// `dim`-cube in which `axis` no longer occurs).
fn poly_cube_restrict_keep(c : PolyCube, axis : Int32, hi : Bool) -> PolyCube {
  let value = if hi { rat_one() } else { rat_zero() }
  let coords : Array[Poly] = []
  for i in 0..<c.coords.length() {
    coords.push(poly_eval_var(c.coords[i], axis, value))
  }
  { dim: c.dim, coords, }
}

///|
/// Fill a complete open box by the iterated connection blend.
/// The box need not be pre-validated, but the filler is only
/// guaranteed (and checkable by `poly_box_filler_faces_ok`) to
/// restrict to the given faces when the box is compatible.
pub fn poly_box_fill(box : PolyOpenBox) -> PolyCube? {
  if !poly_box_complete(box) {
    return None
  }
  let n = box.dim
  let base = match poly_box_face_of(box, n - 1, false) {
    Some(cube) => cube
    None => return None
  }
  // Lift the base to an n-cube, constant in the last atom.
  let mut filler : PolyCube = { dim: n, coords: base.coords, }
  for fi in 0..<box.faces.length() {
    let f = box.faces[fi]
    if f.axis >= n - 1 {
      continue
    }
    // Lift the side face to an n-cube by inserting its missing
    // atom position; the face's last atom becomes the filler's
    // last atom (the composition direction).
    let side = poly_cube_degeneracy(f.cube, f.axis)
    let on_face = poly_cube_restrict_keep(filler, f.axis, f.hi)
    let weight = if f.hi {
      poly_var(f.axis)
    } else {
      poly_sub(poly_one(), poly_var(f.axis))
    }
    filler = poly_cube_add(
      filler,
      poly_cube_scale(weight, poly_cube_sub(side, on_face)),
    )
  }
  Some(filler)
}

///|
/// The cap of the assembled filler.
pub fn poly_box_cap(box : PolyOpenBox) -> PolyCube? {
  match poly_box_fill(box) {
    Some(filler) => Some(poly_cube_face(filler, box.dim - 1, true))
    None => None
  }
}

///|
/// Exact whole-boundary verification: every face of the filler
/// equals the supplied face as polynomials.
pub fn poly_box_filler_faces_ok(box : PolyOpenBox, filler : PolyCube) -> Bool {
  if filler.dim != box.dim {
    return false
  }
  for i in 0..<box.faces.length() {
    let f = box.faces[i]
    if !poly_cube_eq(poly_cube_face(filler, f.axis, f.hi), f.cube) {
      return false
    }
  }
  true
}

///|
/// Validate, fill, and verify in one step.
pub fn poly_box_fill_verified(box : PolyOpenBox) -> PolyCube? {
  if !poly_box_validate(box) {
    return None
  }
  match poly_box_fill(box) {
    Some(filler) =>
      if poly_box_filler_faces_ok(box, filler) {
        Some(filler)
      } else {
        None
      }
    None => None
  }
}

// ---------------------------------------------------------------------------
// Checks
// ---------------------------------------------------------------------------

///|
/// Phase 11 checks: cubical identities as polynomial identities,
/// cube composition, and the connection-blend filler (including
/// the classical square filler with its hand-computed cap, and a
/// 3-dimensional box whose faces come from a known cube).
pub fn check_poly_cubes() -> Bool {
  let x = poly_var(0)
  let y = poly_var(1)
  let t = poly_var(2)
  // A 3-cube in Q^2: (x + t*y, y^2 - t).
  let cube3 : PolyCube = {
    dim: 3,
    coords: [poly_add(x, poly_mul(t, y)), poly_sub(poly_mul(y, y), t)],
  }
  // Cubical identity: d_i d_j = d_{j-1} d_i for i < j, all
  // endpoint combinations.
  for hi_i in [false, true] {
    for hi_j in [false, true] {
      let lhs = poly_cube_face(poly_cube_face(cube3, 2, hi_j), 0, hi_i)
      let rhs = poly_cube_face(poly_cube_face(cube3, 0, hi_i), 1, hi_j)
      if !poly_cube_eq(lhs, rhs) {
        return false
      }
      let lhs2 = poly_cube_face(poly_cube_face(cube3, 2, hi_j), 1, hi_i)
      let rhs2 = poly_cube_face(poly_cube_face(cube3, 1, hi_i), 1, hi_j)
      if !poly_cube_eq(lhs2, rhs2) {
        return false
      }
    }
  }
  // Degeneracy-face laws.
  let square = poly_cube_face(cube3, 2, true)
  let deg = poly_cube_degeneracy(square, 1)
  if !poly_cube_eq(poly_cube_face(deg, 1, false), square) ||
    !poly_cube_eq(poly_cube_face(deg, 1, true), square) {
    return false
  }
  // Composition: reverse the path parameter of a path in Q^2.
  let path : PolyCube = { dim: 1, coords: [x, poly_mul(x, x)], }
  let rev : PolyCube = { dim: 1, coords: [poly_sub(poly_one(), x)], }
  let reversed = poly_cube_compose(rev, path)
  let expected_rev : PolyCube = {
    dim: 1,
    coords: [
      poly_sub(poly_one(), x),
      poly_mul(poly_sub(poly_one(), x), poly_sub(poly_one(), x)),
    ],
  }
  if !poly_cube_eq(reversed, expected_rev) {
    return false
  }
  // Evaluation agrees with face restriction at corners.
  let corner = poly_cube_eval(cube3, [rat_zero(), rat_one(), rat_one()])
  let corner_face = poly_cube_face(
    poly_cube_face(poly_cube_face(cube3, 0, false), 0, true),
    0,
    true,
  )
  if corner_face.coords.length() != 2 ||
    !rat_eq(poly_eval_point(corner_face.coords[0], []), corner[0]) ||
    !rat_eq(poly_eval_point(corner_face.coords[1], []), corner[1]) {
    return false
  }
  // The classical square: bottom (i, i^2), left (0, t),
  // right (1, 1 + t).  Cap is (i, i^2 + 1).
  let bottom : PolyCube = { dim: 1, coords: [x, poly_mul(x, x)], }
  let left : PolyCube = { dim: 1, coords: [poly_zero(), x], }
  let right : PolyCube = {
    dim: 1,
    coords: [poly_one(), poly_add(poly_one(), x)],
  }
  let box2 = poly_open_box(2, [
    poly_box_face(0, false, left),
    poly_box_face(0, true, right),
    poly_box_face(1, false, bottom),
  ])
  if !poly_box_validate(box2) {
    return false
  }
  match poly_box_fill_verified(box2) {
    Some(filler) => {
      let cap = poly_cube_face(filler, 1, true)
      let expected_cap : PolyCube = {
        dim: 1,
        coords: [x, poly_add(poly_mul(x, x), poly_one())],
      }
      if !poly_cube_eq(cap, expected_cap) {
        return false
      }
    }
    None => return false
  }
  // An incompatible square (left starts at 1, bottom at 0).
  let bad_left : PolyCube = { dim: 1, coords: [poly_one(), x], }
  let bad_box = poly_open_box(2, [
    poly_box_face(0, false, bad_left),
    poly_box_face(0, true, right),
    poly_box_face(1, false, bottom),
  ])
  if poly_box_validate(bad_box) {
    return false
  }
  // A 3-box from the faces of cube3 (minus its cap).
  let box3 = poly_open_box(3, [
    poly_box_face(0, false, poly_cube_face(cube3, 0, false)),
    poly_box_face(0, true, poly_cube_face(cube3, 0, true)),
    poly_box_face(1, false, poly_cube_face(cube3, 1, false)),
    poly_box_face(1, true, poly_cube_face(cube3, 1, true)),
    poly_box_face(2, false, poly_cube_face(cube3, 2, false)),
  ])
  if !poly_box_validate(box3) {
    return false
  }
  match poly_box_fill_verified(box3) {
    Some(filler) => poly_box_filler_faces_ok(box3, filler)
    None => false
  }
}
