///|
// General Glue composition (comp), in two models.
//
// (1) Finite universe, endpoint algorithm — fully general over the data:
// lines A (a_line) and T (t_line) of finite types, equivalences e₀, e₁ at
// the ends, faces φ₀, φ₁.  A *line of equivalences* is a morphism in the
// arrow category: the square
//        coe_T
//   T₀ ───────▶ T₁
//   │e₀          │e₁          e₁ ∘ coe_T  =  coe_A ∘ e₀
//   ▼            ▼
//   A₀ ───────▶ A₁
//        coe_A
// must commute (decided symbolically by wiring equality).  Composition of
// a Glue element along the line follows the standard Glue-comp scheme:
//   a_raw = coe_A(a₀)                        (compose the unglued part in A)
//   t₁    = coe_T(t₀)        if φ₀ held      (compose the partial part in T)
//         = e₁⁻¹(a_raw)      if φ only at 1  (φ "switches on": create part)
//   a₁    = e₁(t₁)           if φ₁ holds     (the correction: cap in A is
//         = a_raw            otherwise        adjusted to meet e₁(t₁))
// When φ held at both ends, coherence + well-formedness yield a₁ = a_raw,
// i.e. the correction path is constant — checked, not assumed.  Incoherent
// line data (not a genuine equivalence line) is rejected with None.
//
// (2) Eigenspace lines, open-box algorithm — the continuous analogue with
// a non-trivial correction.  A "type line" is j ↦ im(P(j)) for hermitian
// idempotents P(j); an equivalence line is j ↦ U(j) (partial isometries).
// Given compatible open boxes in T and A:
//   fill both boxes in the ambient space and prune point-wise by P(j)
//   (Kan structure of a retract, now along a *varying* projector line);
//   the raw caps satisfy U(1)(t_cap) ≠ a_cap in general, so form the
//   correction square in A(1):  (i,k) ↦ (1−k)·a_cap(i) + k·U(1)(t_cap(i)),
//   whose k=1 edge is the corrected cap.  On the side faces the
//   discrepancy vanishes (box compatibility), so correction does not move
//   the prescribed endpoints.  This square is exactly the hcomp in A that
//   the textbook Glue composition performs, made affine-explicit.

// ---------------------------------------------------------------------------
// (1) Finite Glue comp
// ---------------------------------------------------------------------------

///|
pub struct GlueLineFinite {
  a_line : UPath
  t_line : UPath
  e0 : Equiv
  e1 : Equiv
  face0 : Face
  face1 : Face
}

///|
pub fn glue_data_at0(line : GlueLineFinite) -> GlueData {
  GlueData::{
    base_ty: line.a_line.equiv.src,
    partial_ty: line.t_line.equiv.src,
    equiv: line.e0,
    face: line.face0,
  }
}

///|
pub fn glue_data_at1(line : GlueLineFinite) -> GlueData {
  GlueData::{
    base_ty: line.a_line.equiv.dst,
    partial_ty: line.t_line.equiv.dst,
    equiv: line.e1,
    face: line.face1,
  }
}

///|
/// Coherence of an equivalence line: endpoint typing, all four maps are
/// equivalences, and the naturality square commutes (symbolically).
pub fn glue_line_coherent(line : GlueLineFinite) -> Bool {
  let a = line.a_line.equiv
  let t = line.t_line.equiv
  line.e0.src == t.src &&
  line.e0.dst == a.src &&
  line.e1.src == t.dst &&
  line.e1.dst == a.dst &&
  equiv_wf(a) &&
  equiv_wf(t) &&
  equiv_wf(line.e0) &&
  equiv_wf(line.e1) &&
  equiv_ext_eq(equiv_comp(t, line.e1), equiv_comp(line.e0, a))
}

///|
/// The Glue composition algorithm (endpoint form), as described above.
pub fn glue_comp_finite(
  line : GlueLineFinite,
  elem : GlueElem,
  nvars : Int32,
) -> GlueElem? {
  if !glue_line_coherent(line) {
    return None
  }
  if !glue_wf(glue_data_at0(line), elem, nvars) {
    return None
  }
  let a_raw = coe_upath(line.a_line, 0, 1, elem.base)
  let t_coe = coe_upath(line.t_line, 0, 1, elem.partial)
  let (t1, a1) = if !face_sat(line.face1, nvars) {
    (t_coe, a_raw)
  } else {
    let t_candidate = if face_sat(line.face0, nvars) {
      t_coe
    } else {
      (line.e1.bwd)(a_raw) // φ switches on: create the partial part
    }
    (t_candidate, (line.e1.fwd)(t_candidate)) // correction of the A-cap
  }
  let out = GlueElem::{ partial: t1, base: a1, }
  if glue_wf(glue_data_at1(line), out, nvars) {
    Some(out)
  } else {
    None
  }
}

///|
/// Correctness of finite Glue comp on a given input: the output is a
/// well-formed Glue element at 1; when φ holds at both ends the correction
/// is constant (output base = coe_A of input base — the coherence theorem);
/// when φ switches on, the created partial part maps to coe_A(a₀).
pub fn glue_comp_finite_correct(
  line : GlueLineFinite,
  elem : GlueElem,
  nvars : Int32,
) -> Bool {
  match glue_comp_finite(line, elem, nvars) {
    None => false
    Some(out) => {
      if !glue_wf(glue_data_at1(line), out, nvars) {
        return false
      }
      let a_raw = coe_upath(line.a_line, 0, 1, elem.base)
      let both = face_sat(line.face0, nvars) && face_sat(line.face1, nvars)
      let switch_on = !face_sat(line.face0, nvars) &&
        face_sat(line.face1, nvars)
      (
        !both ||
        (
          out.base == a_raw &&
          out.partial == coe_upath(line.t_line, 0, 1, elem.partial)
        )
      ) &&
      (!switch_on || out.base == a_raw)
    }
  }
}

///|
pub fn check_glue_comp_finite() -> Bool {
  // Coherent square by conjugation: e₁ = coe_A ∘ e₀ ∘ coe_T⁻¹.
  let line1 = GlueLineFinite::{
    a_line: ua(equiv_bool_not()),
    t_line: ua(equiv_id(TyBool)),
    e0: equiv_id(TyBool),
    e1: equiv_bool_not(),
    face0: FTop,
    face1: FTop,
  }
  let elem1 = GlueElem::{ partial: PVBool(true), base: PVBool(true), }
  if !glue_comp_finite_correct(line1, elem1, 1) {
    return false
  }
  // φ switches on: bottom face at 0, top at 1; the dummy partial is ignored.
  let line2 = GlueLineFinite::{
    a_line: ua(equiv_id(TyBool)),
    t_line: ua(equiv_id(TyBool)),
    e0: equiv_bool_not(),
    e1: equiv_bool_not(),
    face0: FBot,
    face1: FTop,
  }
  let elem2 = GlueElem::{ partial: PVBool(true), base: PVBool(true), }
  if !glue_comp_finite_correct(line2, elem2, 1) {
    return false
  }
  // Swap square over product types.
  let prod_ty = TyProd(TyBool, TyUnit)
  let line3 = GlueLineFinite::{
    a_line: ua(equiv_swap(TyBool, TyUnit)),
    t_line: ua(equiv_id(prod_ty)),
    e0: equiv_id(prod_ty),
    e1: equiv_swap(TyBool, TyUnit),
    face0: FTop,
    face1: FTop,
  }
  let elem3 = GlueElem::{
    partial: PVPair(PVBool(false), PVUnit),
    base: PVPair(PVBool(false), PVUnit),
  }
  if !glue_comp_finite_correct(line3, elem3, 1) {
    return false
  }
  // Incoherent data is not an equivalence line: rejected.
  let bad_line = GlueLineFinite::{
    a_line: ua(equiv_id(TyBool)),
    t_line: ua(equiv_id(TyBool)),
    e0: equiv_id(TyBool),
    e1: equiv_bool_not(),
    face0: FTop,
    face1: FTop,
  }
  match glue_comp_finite(bad_line, elem1, 1) {
    None => true
    Some(_) => false
  }
}

// ---------------------------------------------------------------------------
// (2) Glue comp along eigenspace lines (open boxes, hcomp correction)
// ---------------------------------------------------------------------------

///|
/// A line of eigenspaces: j ↦ im(P(j)).
pub struct SubLine {
  proj : (Double) -> CMat
}

///|
pub fn subline_const(p : CMat) -> SubLine {
  SubLine::{ proj: _j => p, }
}

///|
pub fn subline_from_unit_path(unit : (Double) -> CVec) -> SubLine {
  SubLine::{ proj: j => outer(unit(j)), }
}

///|
/// Rank-one operator a·b†.
pub fn outer2(a : CVec, b : CVec) -> CMat {
  let n = a.length()
  let rows : Array[Array[Complex]] = []
  for i in 0..<n {
    let row : Array[Complex] = []
    for j in 0..<n {
      row.push(cx_mul(a[i], cx_conj(b[j])))
    }
    rows.push(row)
  }
  CMat::{ n, rows, }
}

///|
/// A line of linear equivalences between eigenspaces.
pub struct LinEquivLine {
  fwd : (Double) -> CMat
  bwd : (Double) -> CMat
}

///|
/// The partial isometry sending the T-unit path to the A-unit path:
/// U(j) = a(j)·t(j)†, with inverse (on the subspaces) U(j)†.
pub fn lin_equiv_from_unit_paths(
  t_unit : (Double) -> CVec,
  a_unit : (Double) -> CVec,
) -> LinEquivLine {
  LinEquivLine::{
    fwd: j => outer2(a_unit(j), t_unit(j)),
    bwd: j => outer2(t_unit(j), a_unit(j)),
  }
}

///|
pub struct GlueLineVec {
  base_line : SubLine
  part_line : SubLine
  equiv : LinEquivLine
  face_active : Bool
}

///|
pub struct VecBox {
  bottom : Cube
  left : Cube
  right : Cube
}

///|
pub fn vec_box(bottom : Cube, left : Cube, right : Cube) -> VecBox {
  VecBox::{ bottom, left, right, }
}

///|
pub fn cube_in_subline(
  line : SubLine,
  c : Cube,
  line_idx : Int32,
  samples : Array[Double],
) -> Bool {
  let m = samples.length()
  let total = @algebra.int_pow(m, c.dim)
  for code in 0..<total {
    let pt : Array[Double] = []
    let mut rest = code
    for _d in 0..<c.dim {
      pt.push(samples[rest % m])
      rest = rest / m
    }
    if !in_image((line.proj)(pt[line_idx]), cube_eval(c, pt)) {
      return false
    }
  }
  true
}

///|
fn prune_subline_formula(
  line : SubLine,
  c : Cube,
  line_idx : Int32,
  pt : Array[Double],
) -> CVec {
  mat_vec((line.proj)(pt[line_idx]), cube_eval(c, pt))
}

///|
/// Pointwise pruning into a *varying* eigenspace line.
pub fn prune_cube_subline(line : SubLine, c : Cube, line_idx : Int32) -> Cube {
  Cube::{
    dim: c.dim,
    cell: pt => prune_subline_formula(line, c, line_idx, pt),
  }
}

///|
/// Kan filler along a subline: ambient fill, then prune by P(j).
pub fn fill_subline(line : SubLine, box : VecBox) -> Cube {
  prune_cube_subline(line, square_fill(box.bottom, box.left, box.right), 1)
}

///|
fn map_matrix_formula(m : CMat, c : Cube, pt : Array[Double]) -> CVec {
  mat_vec(m, cube_eval(c, pt))
}

///|
pub fn map_cube_matrix(m : CMat, c : Cube) -> Cube {
  Cube::{ dim: c.dim, cell: pt => map_matrix_formula(m, c, pt), }
}

///|
fn map_equiv_formula(
  e : LinEquivLine,
  c : Cube,
  line_idx : Int32,
  pt : Array[Double],
) -> CVec {
  mat_vec((e.fwd)(pt[line_idx]), cube_eval(c, pt))
}

///|
/// Transport a cube through an equivalence line.
pub fn map_cube_equiv_line(
  e : LinEquivLine,
  c : Cube,
  line_idx : Int32,
) -> Cube {
  Cube::{ dim: c.dim, cell: pt => map_equiv_formula(e, c, line_idx, pt), }
}

///|
/// Boxes are Glue-compatible when U maps each given T-face to the
/// corresponding A-face (whenever the face is active).
pub fn glue_box_compatible(
  gl : GlueLineVec,
  tbox : VecBox,
  abox : VecBox,
  samples : Array[Double],
) -> Bool {
  if !open_box_wf(tbox.bottom, tbox.left, tbox.right) ||
    !open_box_wf(abox.bottom, abox.left, abox.right) {
    return false
  }
  if !gl.face_active {
    return true
  }
  for s in 0..<samples.length() {
    let t = samples[s]
    let u0 = (gl.equiv.fwd)(0.0)
    if !vec_approx_eq(
        mat_vec(u0, path_eval(tbox.bottom, t)),
        path_eval(abox.bottom, t),
      ) {
      return false
    }
    let uj = (gl.equiv.fwd)(t)
    if !vec_approx_eq(
        mat_vec(uj, path_eval(tbox.left, t)),
        path_eval(abox.left, t),
      ) {
      return false
    }
    if !vec_approx_eq(
        mat_vec(uj, path_eval(tbox.right, t)),
        path_eval(abox.right, t),
      ) {
      return false
    }
  }
  true
}

///|
pub struct GlueCompVecResult {
  t_fill : Cube
  a_fill_raw : Cube
  t_cap : Cube
  a_cap_raw : Cube
  a_cap : Cube
  correction : Cube // (i,k): path in A(1) from raw cap to U(1)(t cap)
}

///|
fn correction_formula(
  a_fill : Cube,
  t_fill : Cube,
  u1 : CMat,
  active : Bool,
  pt : Array[Double],
) -> CVec {
  let i = pt[0]
  let k = pt[1]
  let a = cube_eval(a_fill, [i, 1.0])
  if !active {
    return a
  }
  let target = mat_vec(u1, cube_eval(t_fill, [i, 1.0]))
  vec_add(vec_scale(1.0 - k, a), vec_scale(k, target))
}

///|
/// The Glue composition: fill both, correct the A-cap by hcomp in A(1).
pub fn glue_comp_vec(
  gl : GlueLineVec,
  tbox : VecBox,
  abox : VecBox,
) -> GlueCompVecResult {
  let t_fill = fill_subline(gl.part_line, tbox)
  let a_fill = fill_subline(gl.base_line, abox)
  let u1 = (gl.equiv.fwd)(1.0)
  let correction = Cube::{
    dim: 2,
    cell: pt => correction_formula(a_fill, t_fill, u1, gl.face_active, pt),
  }
  GlueCompVecResult::{
    t_fill,
    a_fill_raw: a_fill,
    t_cap: restrict_face(t_fill, 1, 1.0),
    a_cap_raw: restrict_face(a_fill, 1, 1.0),
    a_cap: restrict_face(correction, 1, 1.0),
    correction,
  }
}

///|
/// Soundness of the whole construction on a sample grid.
pub fn glue_comp_vec_sound(
  gl : GlueLineVec,
  tbox : VecBox,
  abox : VecBox,
  samples : Array[Double],
) -> Bool {
  if !glue_box_compatible(gl, tbox, abox, samples) {
    return false
  }
  // Box data lie in the lines: bottoms at j=0, sides along the line.
  if !cube_in_eigenspace((gl.part_line.proj)(0.0), tbox.bottom, samples) ||
    !cube_in_eigenspace((gl.base_line.proj)(0.0), abox.bottom, samples) ||
    !cube_in_subline(gl.part_line, tbox.left, 0, samples) ||
    !cube_in_subline(gl.part_line, tbox.right, 0, samples) ||
    !cube_in_subline(gl.base_line, abox.left, 0, samples) ||
    !cube_in_subline(gl.base_line, abox.right, 0, samples) {
    return false
  }
  let r = glue_comp_vec(gl, tbox, abox)
  if !filler_respects_box(r.t_fill, tbox.bottom, tbox.left, tbox.right, samples) ||
    !filler_respects_box(
      r.a_fill_raw,
      abox.bottom,
      abox.left,
      abox.right,
      samples,
    ) {
    return false
  }
  if !cube_in_subline(gl.part_line, r.t_fill, 1, samples) ||
    !cube_in_subline(gl.base_line, r.a_fill_raw, 1, samples) {
    return false
  }
  // Correction lives in A(1), starts at the raw cap, ends at a_cap,
  // and caps have the prescribed endpoints.
  let pa1 = (gl.base_line.proj)(1.0)
  let pt1 = (gl.part_line.proj)(1.0)
  if !cube_in_eigenspace(pa1, r.correction, samples) ||
    !cube_in_eigenspace(pa1, r.a_cap, samples) ||
    !cube_in_eigenspace(pt1, r.t_cap, samples) {
    return false
  }
  if !vec_approx_eq(path_start(r.t_cap), path_end(tbox.left)) ||
    !vec_approx_eq(path_end(r.t_cap), path_end(tbox.right)) ||
    !vec_approx_eq(path_start(r.a_cap), path_end(abox.left)) ||
    !vec_approx_eq(path_end(r.a_cap), path_end(abox.right)) {
    return false
  }
  for s in 0..<samples.length() {
    let t = samples[s]
    if !vec_approx_eq(
        cube_eval(r.correction, [t, 0.0]),
        path_eval(r.a_cap_raw, t),
      ) ||
      !vec_approx_eq(cube_eval(r.correction, [t, 1.0]), path_eval(r.a_cap, t)) {
      return false
    }
    if gl.face_active {
      let u1 = (gl.equiv.fwd)(1.0)
      if !vec_approx_eq(
          mat_vec(u1, path_eval(r.t_cap, t)),
          path_eval(r.a_cap, t),
        ) {
        return false
      }
    }
  }
  true
}

///|
pub fn vec_normalize(v : CVec) -> CVec {
  let n = vec_norm2(v).sqrt()
  vec_scale(1.0 / n, v)
}

///|
fn unit_a_example(j : Double) -> CVec {
  vec_normalize([cx_real(1.0 - j), cx_real(j), cx_zero()])
}

///|
fn unit_t_example(j : Double) -> CVec {
  vec_normalize([cx_zero(), cx_real(1.0 - j), cx_real(j)])
}

///|
fn unit_path_scaled(unit : (Double) -> CVec, scale : Double) -> Cube {
  Cube::{ dim: 1, cell: pt => vec_scale(scale, unit(pt[0])), }
}

///|
pub fn check_glue_comp_vec() -> Bool {
  let t_line = subline_from_unit_path(unit_t_example)
  let a_line = subline_from_unit_path(unit_a_example)
  let e = lin_equiv_from_unit_paths(unit_t_example, unit_a_example)
  let gl = GlueLineVec::{
    base_line: a_line,
    part_line: t_line,
    equiv: e,
    face_active: true,
  }
  let t_bottom = path_line(
    unit_t_example(0.0),
    vec_scale(2.0, unit_t_example(0.0)),
  )
  let tbox = vec_box(
    t_bottom,
    unit_path_scaled(unit_t_example, 1.0),
    unit_path_scaled(unit_t_example, 2.0),
  )
  let abox = vec_box(
    map_cube_matrix(e_fwd_at(e, 0.0), t_bottom),
    map_cube_equiv_line(e, unit_path_scaled(unit_t_example, 1.0), 0),
    map_cube_equiv_line(e, unit_path_scaled(unit_t_example, 2.0), 0),
  )
  glue_comp_vec_sound(gl, tbox, abox, [0.0, 0.25, 0.5, 0.75, 1.0])
}

///|
fn e_fwd_at(e : LinEquivLine, j : Double) -> CMat {
  (e.fwd)(j)
}

///|
pub fn check_glue_comp_all() -> Bool {
  check_glue_comp_finite() && check_glue_comp_vec()
}
