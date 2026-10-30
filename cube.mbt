///|
// Cubes over the interval and Kan composition (comp) by retraction.
//
// A semantic n-cube in Cᵐ is a function Iⁿ → Cᵐ.  A path is a 1-cube, a
// square a 2-cube.  Face restriction inserts an endpoint for a dimension.
//
// Kan filling for the ambient (affine) space is explicit.  Given an open
// box — bottom b(i), left l(j), right r(j) with l(0)=b(0), r(0)=b(1) — the
// filler
//     F(i,j) = b(i) + (1−i)·(l(j) − b(0)) + i·(r(j) − b(1))
// restricts to b, l, r on the three given faces, and its top face
// F(−,1) is the composition of the box: a path l(1) ~ r(1).
// Path transitivity is the special case l = refl.
//
// For an eigenspace im(P) the Kan structure is obtained by *pruning*
// (Kan 纖維化剪枝): fill in the ambient space, then apply the retraction P
// pointwise.  Boundary data lying in the eigenspace is fixed by P, so the
// pruned filler still restricts to the given box, while every interior
// point now lies in the eigenspace.  This is the theorem "a retract of a
// Kan fibration is Kan", with P the retraction and P² = P the proof.

///|
pub struct Cube {
  dim : Int32
  cell : (Array[Double]) -> CVec
}

///|
pub fn cube_const(v : CVec, dim : Int32) -> Cube {
  Cube::{ dim, cell: _pt => v, }
}

///|
pub fn cube_eval(c : Cube, pt : Array[Double]) -> CVec {
  (c.cell)(pt)
}

///|
pub fn path_eval(p : Cube, t : Double) -> CVec {
  (p.cell)([t])
}

///|
pub fn path_start(p : Cube) -> CVec {
  path_eval(p, 0.0)
}

///|
pub fn path_end(p : Cube) -> CVec {
  path_eval(p, 1.0)
}

///|
fn line_formula(a : CVec, b : CVec, pt : Array[Double]) -> CVec {
  vec_add(a, vec_scale(pt[0], vec_sub(b, a)))
}

///|
/// The straight-line path a ~ b in Cⁿ.
pub fn path_line(a : CVec, b : CVec) -> Cube {
  Cube::{ dim: 1, cell: pt => line_formula(a, b, pt), }
}

///|
/// Reflexivity: the constant path.
pub fn path_refl(a : CVec) -> Cube {
  Cube::{ dim: 1, cell: _pt => a, }
}

///|
fn sym_formula(p : Cube, pt : Array[Double]) -> CVec {
  path_eval(p, 1.0 - pt[0])
}

///|
/// Symmetry of paths, using interval reversal ¬i = 1 − i.
pub fn path_sym(p : Cube) -> Cube {
  Cube::{ dim: 1, cell: pt => sym_formula(p, pt), }
}

///|
fn restrict_formula(
  c : Cube,
  idx : Int32,
  endpoint : Double,
  pt : Array[Double],
) -> CVec {
  let full : Array[Double] = []
  for i in 0..<c.dim {
    if i == idx {
      full.push(endpoint)
    } else if i < idx {
      full.push(pt[i])
    } else {
      full.push(pt[i - 1])
    }
  }
  (c.cell)(full)
}

///|
/// Face map: set dimension `idx` to `endpoint` (0 or 1), dropping it.
pub fn restrict_face(c : Cube, idx : Int32, endpoint : Double) -> Cube {
  Cube::{ dim: c.dim - 1, cell: pt => restrict_formula(c, idx, endpoint, pt), }
}

///|
/// Cubical face identity: restricting two different faces in either order
/// gives the same corner value (the interval dimensions commute).
pub fn face_maps_commute(f : Cube, a : Double, b : Double) -> Bool {
  let corner1 = cube_eval(restrict_face(restrict_face(f, 0, a), 0, b), [])
  let corner2 = cube_eval(restrict_face(restrict_face(f, 1, b), 0, a), [])
  vec_approx_eq(corner1, corner2) &&
  vec_approx_eq(corner1, cube_eval(f, [a, b]))
}

///|
/// An open box is well-formed when the sides meet the bottom corners.
pub fn open_box_wf(bottom : Cube, left : Cube, right : Cube) -> Bool {
  vec_approx_eq(path_eval(left, 0.0), path_eval(bottom, 0.0)) &&
  vec_approx_eq(path_eval(right, 0.0), path_eval(bottom, 1.0))
}

///|
fn square_formula(
  bottom : Cube,
  left : Cube,
  right : Cube,
  pt : Array[Double],
) -> CVec {
  let i = pt[0]
  let j = pt[1]
  let b_i = path_eval(bottom, i)
  let left_dev = vec_sub(path_eval(left, j), path_eval(bottom, 0.0))
  let right_dev = vec_sub(path_eval(right, j), path_eval(bottom, 1.0))
  vec_add(b_i, vec_add(vec_scale(1.0 - i, left_dev), vec_scale(i, right_dev)))
}

///|
/// The ambient Kan filler of an open box.
pub fn square_fill(bottom : Cube, left : Cube, right : Cube) -> Cube {
  Cube::{ dim: 2, cell: pt => square_formula(bottom, left, right, pt), }
}

///|
/// Does a square restrict to the given box on bottom/left/right faces?
pub fn filler_respects_box(
  f : Cube,
  bottom : Cube,
  left : Cube,
  right : Cube,
  samples : Array[Double],
) -> Bool {
  for s in 0..<samples.length() {
    let t = samples[s]
    if !vec_approx_eq(cube_eval(f, [t, 0.0]), path_eval(bottom, t)) {
      return false
    }
    if !vec_approx_eq(cube_eval(f, [0.0, t]), path_eval(left, t)) {
      return false
    }
    if !vec_approx_eq(cube_eval(f, [1.0, t]), path_eval(right, t)) {
      return false
    }
  }
  true
}

///|
/// Composition (comp): the missing top face of the filler,
/// a path from left(1) to right(1).
pub fn kan_comp_path(bottom : Cube, left : Cube, right : Cube) -> Cube {
  restrict_face(square_fill(bottom, left, right), 1, 1.0)
}

///|
/// Transitivity of paths, derived from comp with a reflexive left face:
/// p : a ~ b and q : b ~ c give p⋅q : a ~ c.
pub fn path_trans(p : Cube, q : Cube) -> Cube {
  kan_comp_path(p, path_refl(path_start(p)), q)
}

///|
pub fn path_trans_endpoints(p : Cube, q : Cube) -> Bool {
  let pq = path_trans(p, q)
  vec_approx_eq(path_start(pq), path_start(p)) &&
  vec_approx_eq(path_end(pq), path_end(q))
}

///|
fn prune_formula(p : CMat, c : Cube, pt : Array[Double]) -> CVec {
  prune_to_eigenspace(p, (c.cell)(pt))
}

///|
/// Prune a cube into the eigenspace im(P), pointwise.
pub fn prune_cube(p : CMat, c : Cube) -> Cube {
  Cube::{ dim: c.dim, cell: pt => prune_formula(p, c, pt), }
}

///|
/// Sample the cube on a grid and check every value lies in im(P).
pub fn cube_in_eigenspace(p : CMat, c : Cube, samples : Array[Double]) -> Bool {
  let m = samples.length()
  let total = @algebra.int_pow(m, c.dim)
  for code in 0..<total {
    let pt : Array[Double] = []
    let mut rest = code
    for _d in 0..<c.dim {
      pt.push(samples[rest % m])
      rest = rest / m
    }
    if !in_image(p, cube_eval(c, pt)) {
      return false
    }
  }
  true
}

///|
/// Kan composition for the eigenspace: ambient-fill then prune.
pub fn kan_fill_eigenspace(
  p : CMat,
  bottom : Cube,
  left : Cube,
  right : Cube,
) -> Cube {
  prune_cube(p, square_fill(bottom, left, right))
}

///|
/// The eigenspace comp: top face of the pruned filler.
pub fn kan_comp_eigenspace(
  p : CMat,
  bottom : Cube,
  left : Cube,
  right : Cube,
) -> Cube {
  restrict_face(kan_fill_eigenspace(p, bottom, left, right), 1, 1.0)
}

///|
/// Soundness of eigenspace Kan filling on a sample grid:
/// the box is well-formed, its data lies in the eigenspace, the pruned
/// filler still restricts to the box, lies entirely in the eigenspace,
/// and its cap connects the correct endpoints inside the eigenspace.
pub fn eigenspace_kan_sound(
  p : CMat,
  bottom : Cube,
  left : Cube,
  right : Cube,
  samples : Array[Double],
) -> Bool {
  if !open_box_wf(bottom, left, right) {
    return false
  }
  if !cube_in_eigenspace(p, bottom, samples) {
    return false
  }
  if !cube_in_eigenspace(p, left, samples) {
    return false
  }
  if !cube_in_eigenspace(p, right, samples) {
    return false
  }
  let filler = kan_fill_eigenspace(p, bottom, left, right)
  if !filler_respects_box(filler, bottom, left, right, samples) {
    return false
  }
  if !cube_in_eigenspace(p, filler, samples) {
    return false
  }
  let cap = kan_comp_eigenspace(p, bottom, left, right)
  vec_approx_eq(path_start(cap), path_end(left)) &&
  vec_approx_eq(path_end(cap), path_end(right)) &&
  cube_in_eigenspace(p, cap, samples)
}

///|
fn bump_formula(f : Cube, normal : CVec, pt : Array[Double]) -> CVec {
  let i = pt[0]
  let j = pt[1]
  // i(1−i)j vanishes on the bottom (j=0), left (i=0) and right (i=1) faces.
  vec_add(cube_eval(f, pt), vec_scale(i * (1.0 - i) * j, normal))
}

///|
/// A "bad" ambient filler: same prescribed faces, but it leaves the
/// eigenspace in the interior by adding a normal bump.
pub fn bumped_filler(f : Cube, normal : CVec) -> Cube {
  Cube::{ dim: 2, cell: pt => bump_formula(f, normal, pt), }
}

///|
/// Pruning repairs a bad filler: after applying P, the filler lies in the
/// eigenspace, still restricts to the original box, and the repair is
/// genuinely needed (the bumped filler does leave the eigenspace when the
/// bump direction has a kernel component).
pub fn pruning_repairs_filler(
  p : CMat,
  bottom : Cube,
  left : Cube,
  right : Cube,
  normal : CVec,
  samples : Array[Double],
) -> Bool {
  let bad = bumped_filler(square_fill(bottom, left, right), normal)
  let fixed = prune_cube(p, bad)
  let bump_leaves = !cube_in_eigenspace(p, bad, samples)
  let bump_has_kernel_part = !vec_approx_eq(
    prune_to_eigenspace(p, normal),
    normal,
  )
  filler_respects_box(fixed, bottom, left, right, samples) &&
  cube_in_eigenspace(p, fixed, samples) &&
  (!bump_has_kernel_part || bump_leaves)
}
