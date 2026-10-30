///|
// Categorifications, made executable.
//
// Every structure in this project is the shadow of a category; this file
// names those categories and checks their laws on concrete instances:
//
//  1. Karoubi envelope (idempotent splitting) of finite-dimensional
//     Hilbert spaces: objects are hermitian idempotents P (projectors),
//     a morphism P→Q is a matrix A with Q·A·P = A; identity on P is P
//     itself; composition is matrix multiplication; adjoint is a dagger.
//     Eigenspaces are exactly the split objects, and pruning is the
//     inclusion/projection pair of the splitting.
//
//  2. The face lattice as a poset category: objects are faces modulo BDD
//     equality, the (unique) morphism φ→ψ exists iff φ ≤ ψ; ∧ is the
//     categorical product, ∨ the coproduct, ⊤ terminal, ⊥ initial.
//
//  3. The cube category □: face maps (restrict_face) and degeneracies
//     (degenerate_cube, new below) generating its morphisms, subject to
//     the cubical identities (face–face, face–degeneracy).
//
//  4. The syntactic Cartesian closed category of the λ× fragment: objects
//     are LTy, morphisms are closed function terms modulo βπη equality,
//     with η-normal forms (nf_eta) as canonical representatives;
//     composition and identity are tm_comp_closed / tm_id_at, and ua(swap)
//     coe arrows are isomorphisms with definitional inverse laws.

// ---------------------------------------------------------------------------
// 1. Karoubi envelope of hermitian idempotents
// ---------------------------------------------------------------------------

///|
/// A is a Karoubi morphism P→Q iff Q·A·P = A (A lives between the images).
pub fn karoubi_morphism(p : CMat, q : CMat, a : CMat) -> Bool {
  is_projector(p) &&
  is_projector(q) &&
  mat_approx_eq(mat_mul(q, mat_mul(a, p)), a)
}

///|
/// Every matrix X wraps to a Karoubi morphism Q·X·P : P→Q.
pub fn karoubi_wrap(p : CMat, q : CMat, x : CMat) -> CMat {
  mat_mul(q, mat_mul(x, p))
}

///|
/// The identity morphism on the split object P is P itself.
pub fn karoubi_id(p : CMat) -> CMat {
  p
}

///|
/// Composition: first f : P→Q, then g : Q→R.
pub fn karoubi_comp(f : CMat, g : CMat) -> CMat {
  mat_mul(g, f)
}

///|
pub fn check_karoubi_category() -> Bool {
  let p = example_projector()
  let q = outer(vec_e3())
  let r = mat_identity(3)
  let x = mat_from_rows([
    [cx_real(1.0), cx(0.0, 1.0), cx_real(2.0)],
    [cx_real(0.0), cx_real(1.0), cx(-1.0, 0.5)],
    [cx_real(3.0), cx_zero(), cx_real(1.0)],
  ])
  let y = mat_from_rows([
    [cx_zero(), cx_real(1.0), cx_real(0.0)],
    [cx_real(2.0), cx_zero(), cx(0.0, -1.0)],
    [cx_real(1.0), cx_real(1.0), cx_zero()],
  ])
  let f = karoubi_wrap(p, q, x) // P→Q
  let g = karoubi_wrap(q, r, y) // Q→R (= C³ with identity idempotent)
  let h = karoubi_wrap(r, p, x) // R→P
  karoubi_morphism(p, q, f) &&
  karoubi_morphism(q, r, g) &&
  karoubi_morphism(p, r, karoubi_comp(f, g)) &&
  karoubi_morphism(p, p, karoubi_id(p)) &&
  mat_approx_eq(karoubi_comp(karoubi_id(p), f), f) &&
  mat_approx_eq(karoubi_comp(f, karoubi_id(q)), f) &&
  mat_approx_eq(
    karoubi_comp(karoubi_comp(f, g), h),
    karoubi_comp(f, karoubi_comp(g, h)),
  ) &&
  // dagger: the adjoint of a morphism P→Q is a morphism Q→P
  karoubi_morphism(q, p, mat_adjoint(f))
}

// ---------------------------------------------------------------------------
// 2. Face lattice as poset category
// ---------------------------------------------------------------------------

///|
/// ∧ is the product: x ≤ f∧g iff x ≤ f and x ≤ g.
pub fn face_meet_universal(f : Face, g : Face, x : Face, n : Int32) -> Bool {
  face_le(x, FAnd(f, g), n) == (face_le(x, f, n) && face_le(x, g, n))
}

///|
/// ∨ is the coproduct: f∨g ≤ x iff f ≤ x and g ≤ x.
pub fn face_join_universal(f : Face, g : Face, x : Face, n : Int32) -> Bool {
  face_le(FOr(f, g), x, n) == (face_le(f, x, n) && face_le(g, x, n))
}

///|
pub fn check_face_poset_category() -> Bool {
  let i0 = face_var0(0)
  let j1 = face_var1(1)
  let forms = [FTop, FBot, i0, j1, FAnd(i0, j1), FOr(i0, j1), face_var1(0)]
  for a in 0..<forms.length() {
    let f = forms[a]
    if !face_le(f, f, 2) {
      return false // identity morphisms
    }
    if !face_le(f, FTop, 2) || !face_le(FBot, f, 2) {
      return false // ⊤ terminal, ⊥ initial
    }
    for b in 0..<forms.length() {
      let g = forms[b]
      if !face_meet_universal(f, g, FAnd(f, g), 2) ||
        !face_meet_universal(f, g, FBot, 2) ||
        !face_meet_universal(f, g, f, 2) {
        return false
      }
      if !face_join_universal(f, g, FOr(f, g), 2) ||
        !face_join_universal(f, g, FTop, 2) {
        return false
      }
      for c in 0..<forms.length() {
        let h = forms[c]
        // transitivity of morphism existence (composition)
        if face_le(f, g, 2) && face_le(g, h, 2) && !face_le(f, h, 2) {
          return false
        }
      }
    }
  }
  true
}

// ---------------------------------------------------------------------------
// 3. Cube category: degeneracies and cubical identities
// ---------------------------------------------------------------------------

///|
fn degenerate_formula(c : Cube, idx : Int32, pt : Array[Double]) -> CVec {
  let dropped : Array[Double] = []
  for i in 0..<pt.length() {
    if i != idx {
      dropped.push(pt[i])
    }
  }
  cube_eval(c, dropped)
}

///|
/// Degeneracy: insert a dummy dimension at `idx` (the cube ignores it).
pub fn degenerate_cube(c : Cube, idx : Int32) -> Cube {
  Cube::{ dim: c.dim + 1, cell: pt => degenerate_formula(c, idx, pt), }
}

///|
/// Extensional equality of cubes on a sample grid.
pub fn cube_ext_eq(a : Cube, b : Cube, samples : Array[Double]) -> Bool {
  if a.dim != b.dim {
    return false
  }
  let m = samples.length()
  let total = @algebra.int_pow(m, a.dim)
  for code in 0..<total {
    let pt : Array[Double] = []
    let mut rest = code
    for _d in 0..<a.dim {
      pt.push(samples[rest % m])
      rest = rest / m
    }
    if !vec_approx_eq(cube_eval(a, pt), cube_eval(b, pt)) {
      return false
    }
  }
  true
}

///|
/// Cubical identities for a path p:
///   ∂(ε, 0) ∘ σ₀ = id  and  ∂(ε, 1) ∘ σ₀ p = σ₀(∂ε p)  (constant path).
pub fn check_cubical_identities(p : Cube, samples : Array[Double]) -> Bool {
  let sp = degenerate_cube(p, 0)
  cube_ext_eq(restrict_face(sp, 0, 0.0), p, samples) &&
  cube_ext_eq(restrict_face(sp, 0, 1.0), p, samples) &&
  cube_ext_eq(
    restrict_face(sp, 1, 0.0),
    cube_const(path_eval(p, 0.0), 1),
    samples,
  ) &&
  cube_ext_eq(
    restrict_face(sp, 1, 1.0),
    cube_const(path_eval(p, 1.0), 1),
    samples,
  )
}

// ---------------------------------------------------------------------------
// 4. Syntactic Cartesian closed category (arrows modulo βπη)
// ---------------------------------------------------------------------------

///|
pub fn check_syntactic_category() -> Bool {
  let a_ty = LProd(LBool, LUnit) // object A
  let b_ty = LProd(LUnit, LBool) // object B
  let f = tm_swap_at(LBool, LUnit) // A → B
  let g = tm_swap_at(LUnit, LBool) // B → A
  let ctx : Array[LTy] = []
  // identity laws
  if !def_eq_eta(
      tm_comp_at(tm_id_at(b_ty), f, a_ty, b_ty, b_ty),
      f,
      LFun(a_ty, b_ty),
      ctx,
    ) {
    return false
  }
  if !def_eq_eta(
      tm_comp_at(f, tm_id_at(a_ty), a_ty, a_ty, b_ty),
      f,
      LFun(a_ty, b_ty),
      ctx,
    ) {
    return false
  }
  // f and g are inverse isomorphisms
  if !def_eq_eta(
      tm_comp_at(g, f, a_ty, b_ty, a_ty),
      tm_id_at(a_ty),
      LFun(a_ty, a_ty),
      ctx,
    ) {
    return false
  }
  if !def_eq_eta(
      tm_comp_at(f, g, b_ty, a_ty, b_ty),
      tm_id_at(b_ty),
      LFun(b_ty, b_ty),
      ctx,
    ) {
    return false
  }
  // associativity: (f∘g)∘f = f∘(g∘f)
  let fg = tm_comp_at(f, g, b_ty, a_ty, b_ty)
  let gf = tm_comp_at(g, f, a_ty, b_ty, a_ty)
  let left = tm_comp_at(fg, f, a_ty, b_ty, b_ty)
  let right = tm_comp_at(f, gf, a_ty, a_ty, b_ty)
  if !def_eq_eta(left, right, LFun(a_ty, b_ty), ctx) {
    return false
  }
  // coe arrows are the same isomorphisms, with definitional inverse laws
  let cf = tm_coe_swap_at(LBool, LUnit)
  let cg = tm_coe_swap_at(LUnit, LBool)
  def_eq_eta(cf, f, LFun(a_ty, b_ty), ctx) &&
  def_eq_eta(
    tm_comp_at(cg, cf, a_ty, b_ty, a_ty),
    TmCoeRefl,
    LFun(a_ty, a_ty),
    ctx,
  )
}

///|
pub fn check_categories_all() -> Bool {
  check_karoubi_category() &&
  check_face_poset_category() &&
  check_cubical_identities(
    path_line([cx_real(1.0), cx_zero(), cx_zero()], [
      cx_zero(),
      cx_real(1.0),
      cx(0.0, 1.0),
    ]),
    [0.0, 0.5, 1.0],
  ) &&
  check_syntactic_category()
}
