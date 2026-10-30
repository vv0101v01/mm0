///|
// Homotopy representatives for the iterated-suspension spheres.
//
// This file deliberately separates three kinds of data:
//
//   * kernel-level representatives: loop-space and based-map types,
//     integer degree maps obtained by iterating the suspension functor,
//     and the usual point-to-loop unit for a suspension;
//   * an explicit equivalence datum between `S^3` and the same sphere
//     presented with its two poles interchanged;
//   * the classical Hopf map on the unit sphere in `C^2`, including a
//     numerical linking-number computation for two Hopf fibers.
//
// These are concrete representatives and invariants.  Phase 10 adds
// an internal integer type, quotient presentations of `pi_3`, and a
// canonical spherical-loop representative calculus in
// `sphere_classification.mbt`.  Even together, those constructions
// do not constitute internal encode/decode proofs of the
// classifications `pi_3(S^3) ~= Z` or `pi_3(S^2) ~= Z`; those remain
// synthetic-homotopy theorems beyond this component.

// ---------------------------------------------------------------------------
// Closed-term loop spaces and based maps
// ---------------------------------------------------------------------------

///|
/// The canonical point of an iterated loop space: reflexivity iterated
/// `n` times.  For `n <= 0` this is just `base`.
pub fn iterated_refl_term(base : DTerm, n : Int32) -> DTerm {
  if n <= 0 {
    base
  } else {
    DLamDim(iterated_refl_term(base, n - 1))
  }
}

///|
/// The closed term for the `n`-fold loop space `Omega^n(a, base)`.
/// `Omega^0` is `a`, and
/// `Omega^(n+1)(a,base) =
///   Path(Omega^n(a,base), refl^n(base), refl^n(base))`.
pub fn loop_space_type_term(a : DTerm, base : DTerm, n : Int32) -> DTerm {
  if n <= 0 {
    a
  } else {
    let previous = loop_space_type_term(a, base, n - 1)
    let point = iterated_refl_term(base, n - 1)
    DPath(previous, point, point)
  }
}

///|
/// The type of based maps, represented as a dependent pair of a function
/// and a path identifying the image of the source base point with the
/// target base point.  All four type/point terms are expected to be
/// closed.
pub fn based_map_type_term(
  source : DTerm,
  target : DTerm,
  source_base : DTerm,
  target_base : DTerm,
) -> DTerm {
  DSigma(
    DPi(source, target),
    DPath(target, DApp(DTVar(0), source_base), target_base),
  )
}

// ---------------------------------------------------------------------------
// Circle powers and spherical degree maps
// ---------------------------------------------------------------------------

///|
/// The base point of the schema circle.
pub fn circle_hit_base_value() -> DValue {
  DVHitCell(circle_schema(), 0, [], [], [])
}

///|
/// The generating loop of the schema circle, as a semantic path.
pub fn circle_hit_loop_path_value() -> DValue {
  let circle = circle_schema()
  DVPathLam(d => hit_cell_value(circle, 1, [], [], [d]))
}

///|
/// The `n`-fold composite of the circle loop.  Positive powers compose
/// the loop with itself by path transitivity; negative powers reverse
/// the corresponding positive power.
pub fn circle_hit_loop_power_value(n : Int32) -> DValue {
  let circle_ty : DValue = DVHitType(circle_schema(), [], [])
  if n == 0 {
    dpath_refl_value(circle_hit_base_value())
  } else if n < 0 {
    dpath_sym_value(circle_hit_loop_power_value(0 - n))
  } else {
    let mut power = circle_hit_loop_path_value()
    let mut k = 1
    while k < n {
      power = dpath_trans_value(
        circle_ty,
        power,
        circle_hit_loop_path_value(),
        0,
      )
      k = k + 1
    }
    power
  }
}

///|
/// The degree-`n` endomap of the schema circle, applied to a point.  It
/// fixes the base point and sends the generating loop to its `n`-th
/// power.
pub fn circle_degree_value(n : Int32, point : DValue, dlevel : Int32) -> DValue {
  let circle = circle_schema()
  let circle_ty : DValue = DVHitType(circle, [], [])
  eval_hit_elim(
    circle,
    (_, _) => circle_ty,
    [circle_hit_base_value(), circle_hit_loop_power_value(n)],
    [],
    [],
    point,
    dlevel,
  )
}

///|
/// Apply a map on suspension bases to a point of a suspension sphere.
/// North goes to north, south to south, and a meridian over `x` goes to
/// the meridian over `base_map(x)`.
pub fn suspension_map_value(
  source : DHitSpec,
  target : DHitSpec,
  base_map : (DValue) -> DValue,
  point : DValue,
  dlevel : Int32,
) -> DValue {
  let target_ty : DValue = DVHitType(target, [], [])
  eval_hit_elim(
    source,
    (_, _) => target_ty,
    [
      DVHitCell(target, 0, [], [], []),
      DVHitCell(target, 1, [], [], []),
      DVLam(x => {
        DVPathLam(d => hit_cell_value(target, 2, [], [base_map(x)], [d]))
      }),
    ],
    [],
    [],
    point,
    dlevel,
  )
}

///|
/// The degree-`n` map on the `dimension`-sphere, applied to a point.
/// It is the circle degree map iterated through the suspension functor.
pub fn sphere_degree_value(
  dimension : Int32,
  n : Int32,
  point : DValue,
  dlevel : Int32,
) -> DValue {
  if dimension <= 1 {
    circle_degree_value(n, point, dlevel)
  } else {
    let spec = sphere_schema(dimension)
    suspension_map_value(
      spec,
      spec,
      x => sphere_degree_value(dimension - 1, n, x, dlevel),
      point,
      dlevel,
    )
  }
}

///|
/// The degree-`n` spherical endomap as a semantic function value.
pub fn sphere_degree_function_value(dimension : Int32, n : Int32) -> DValue {
  DVLam(point => sphere_degree_value(dimension, n, point, dimension + 2))
}

// ---------------------------------------------------------------------------
// The suspension-to-loop unit
// ---------------------------------------------------------------------------

///|
/// A meridian of a suspension sphere, as a semantic path.
pub fn suspension_meridian_path_value(
  spec : DHitSpec,
  point : DValue,
) -> DValue {
  DVPathLam(d => hit_cell_value(spec, 2, [], [point], [d]))
}

///|
/// The loop at the north pole associated with a point `point` of the
/// suspension base:
///
/// `meridian(point) . sym(meridian(base_point))`.
///
/// This is the pointwise representative of the unit
/// `X -> Omega(Susp X)` for the based suspension/loop-space adjunction.
pub fn suspension_unit_loop_value(
  spec : DHitSpec,
  base_point : DValue,
  point : DValue,
  dlevel : Int32,
) -> DValue {
  dpath_trans_value(
    DVHitType(spec, [], []),
    suspension_meridian_path_value(spec, point),
    dpath_sym_value(suspension_meridian_path_value(spec, base_point)),
    dlevel,
  )
}

// ---------------------------------------------------------------------------
// `S^3` with its poles interchanged
// ---------------------------------------------------------------------------

///|
/// Another presentation of `S^3`: the zeroth cell is the south pole, the
/// first cell is the north pole, and the meridian still runs from north
/// to south.  The underlying suspension base is the usual `S^2`.
pub fn sphere3_swapped_schema() -> DHitSpec {
  let base = sphere2_schema()
  dhit_spec("Sphere3SwappedS", base.level, base.params, [], [
    dhit_cell_spec("south", 0, [], []),
    dhit_cell_spec("north", 0, [], []),
    dhit_cell_spec(
      "meridian",
      1,
      [
        darg_external(
          "point",
          DHitType(base, suspension_parameter_terms(base.params.length())),
        ),
      ],
      [dhit_face(1, [], []), dhit_face(0, [], [])],
    ),
  ])
}

///|
/// The pole-swapped `S^3` type.
pub fn sphere3_swapped_type_term() -> DTerm {
  DHitType(sphere3_swapped_schema(), [])
}

///|
/// The north pole (cell 1) of the swapped presentation.
pub fn sphere3_swapped_north_value() -> DValue {
  DVHitCell(sphere3_swapped_schema(), 1, [], [], [])
}

///|
/// The south pole (cell 0) of the swapped presentation.
pub fn sphere3_swapped_south_value() -> DValue {
  DVHitCell(sphere3_swapped_schema(), 0, [], [], [])
}

///|
/// A meridian point in the swapped presentation.
pub fn sphere3_swapped_meridian_value(point : DValue, dim : Dim) -> DValue {
  hit_cell_value(sphere3_swapped_schema(), 2, [], [point], [dim])
}

///|
/// The canonical map from the usual `S^3` to the swapped presentation,
/// applied to a point.
pub fn sphere3_to_swapped_value(point : DValue, dlevel : Int32) -> DValue {
  let swapped = sphere3_swapped_schema()
  let target_ty : DValue = DVHitType(swapped, [], [])
  eval_hit_elim(
    sphere3_schema(),
    (_, _) => target_ty,
    [
      sphere3_swapped_north_value(),
      sphere3_swapped_south_value(),
      DVLam(x => DVPathLam(d => hit_cell_value(swapped, 2, [], [x], [d]))),
    ],
    [],
    [],
    point,
    dlevel,
  )
}

///|
/// The canonical map back from the swapped presentation, applied to a
/// point.
pub fn sphere3_from_swapped_value(point : DValue, dlevel : Int32) -> DValue {
  let sphere3 = sphere3_schema()
  let target_ty : DValue = DVHitType(sphere3, [], [])
  eval_hit_elim(
    sphere3_swapped_schema(),
    (_, _) => target_ty,
    [
      sphere3_south_value(),
      sphere3_north_value(),
      DVLam(x => DVPathLam(d => hit_cell_value(sphere3, 2, [], [x], [d]))),
    ],
    [],
    [],
    point,
    dlevel,
  )
}

///|
/// Retraction data for the pole-swapped equivalence: for a point of the
/// usual presentation, a path from its round trip back to itself.  The
/// path is defined by dependent HIT elimination; on meridians the
/// two-dimensional case is constant in the path direction because the
/// round trip computes to the same meridian point.
pub fn sphere3_swapped_retr_value(point : DValue, dlevel : Int32) -> DValue {
  let spec = sphere3_schema()
  let ty : DValue = DVHitType(spec, [], [])
  eval_hit_elim(
    spec,
    (_, point) => {
      DVPathTy(
        _ => ty,
        sphere3_from_swapped_value(
          sphere3_to_swapped_value(point, dlevel),
          dlevel,
        ),
        point,
      )
    },
    [
      dpath_refl_value(sphere3_north_value()),
      dpath_refl_value(sphere3_south_value()),
      DVLam(x => DVPathLam(i => DVPathLam(_ => sphere3_meridian_value(x, i)))),
    ],
    [],
    [],
    point,
    dlevel,
  )
}

///|
/// Section data for the pole-swapped equivalence: for a point of the
/// swapped presentation, a path from its round trip back to itself.
pub fn sphere3_swapped_sect_value(point : DValue, dlevel : Int32) -> DValue {
  let spec = sphere3_swapped_schema()
  let ty : DValue = DVHitType(spec, [], [])
  eval_hit_elim(
    spec,
    (_, point) => {
      DVPathTy(
        _ => ty,
        sphere3_to_swapped_value(
          sphere3_from_swapped_value(point, dlevel),
          dlevel,
        ),
        point,
      )
    },
    [
      dpath_refl_value(sphere3_swapped_south_value()),
      dpath_refl_value(sphere3_swapped_north_value()),
      DVLam(x => {
        DVPathLam(i => DVPathLam(_ => sphere3_swapped_meridian_value(x, i)))
      }),
    ],
    [],
    [],
    point,
    dlevel,
  )
}

///|
/// The assembled semantic equivalence datum between the two `S^3`
/// presentations.  Its section and retraction fields are the dependent
/// eliminations above.
pub fn sphere3_swapped_equiv_value() -> DValue {
  DVEquiv(
    DVHitType(sphere3_schema(), [], []),
    DVHitType(sphere3_swapped_schema(), [], []),
    DVLam(point => sphere3_to_swapped_value(point, 4)),
    DVLam(point => sphere3_from_swapped_value(point, 4)),
    DVLam(point => sphere3_swapped_sect_value(point, 4)),
    DVLam(point => sphere3_swapped_retr_value(point, 4)),
  )
}

// ---------------------------------------------------------------------------
// The classical Hopf map and its numerical linking invariant
// ---------------------------------------------------------------------------

///|
/// The Hopf map `S^3 -> S^2` in complex coordinates.  A point is stored
/// as `[Re z, Im z, Re w, Im w]`, and the map is
///
/// `(z,w) |-> (2 Re(z conj(w)), 2 Im(z conj(w)), |z|^2 - |w|^2)`.
pub fn hopf_map_s3_to_s2(q : Array[Double]) -> Array[Double] {
  if q.length() != 4 {
    return [0.0, 0.0, 0.0]
  }
  let x1 = q[0]
  let x2 = q[1]
  let x3 = q[2]
  let x4 = q[3]
  [
    2.0 * (x1 * x3 + x2 * x4),
    2.0 * (x2 * x3 - x1 * x4),
    x1 * x1 + x2 * x2 - x3 * x3 - x4 * x4,
  ]
}

///|
/// Simultaneously multiply both complex coordinates by `e^(i theta)`.
/// This moves along the Hopf fiber through `q`.
pub fn hopf_phase_rotate(q : Array[Double], theta : Double) -> Array[Double] {
  if q.length() != 4 {
    return [0.0, 0.0, 0.0, 0.0]
  }
  let c = @math.cos(theta)
  let s = @math.sin(theta)
  [
    c * q[0] - s * q[1],
    s * q[0] + c * q[1],
    c * q[2] - s * q[3],
    s * q[2] + c * q[3],
  ]
}

///|
/// The Hopf fiber over the north pole, parameterized by its phase.
pub fn hopf_north_fiber(theta : Double) -> Array[Double] {
  [@math.cos(theta), @math.sin(theta), 0.0, 0.0]
}

///|
/// The Hopf fiber over the south pole, parameterized by its phase.
pub fn hopf_south_fiber(theta : Double) -> Array[Double] {
  [0.0, 0.0, @math.cos(theta), @math.sin(theta)]
}

///|
fn hopf_dot4(a : Array[Double], b : Array[Double]) -> Double {
  a[0] * b[0] + a[1] * b[1] + a[2] * b[2] + a[3] * b[3]
}

///|
/// Stereographic projection from the pole
/// `(1/sqrt(2), 0, 1/sqrt(2), 0)`, together with the derivative of the
/// projected curve.  The chosen pole does not meet either canonical
/// Hopf fiber.
fn hopf_stereographic_with_derivative(
  x : Array[Double],
  dx : Array[Double],
) -> (Array[Double], Array[Double]) {
  let s = 0.7071067811865476
  let pole = [s, 0.0, s, 0.0]
  let basis = [
    [0.0, 1.0, 0.0, 0.0],
    [0.0, 0.0, 0.0, 1.0],
    [s, 0.0, 0.0 - s, 0.0],
  ]
  let a = hopf_dot4(x, pole)
  let da = hopf_dot4(dx, pole)
  let denom = 1.0 - a
  let y : Array[Double] = []
  let dy : Array[Double] = []
  for i in 0..<3 {
    let numerator = hopf_dot4(x, basis[i])
    let dnumerator = hopf_dot4(dx, basis[i])
    y.push(numerator / denom)
    dy.push(dnumerator / denom + numerator * da / (denom * denom))
  }
  (y, dy)
}

///|
/// A numerical Gauss linking integral for the north and south Hopf
/// fibers, after stereographic projection to `R^3`.  The parameter is
/// the number of midpoint samples on each circle.  With the conventions
/// above the value is plus or minus one up to quadrature error; its
/// absolute value is the Hopf invariant of the classical Hopf map.
pub fn hopf_linking_number_numeric(samples : Int32) -> Double {
  if samples <= 0 {
    return 0.0
  }
  let pi = 3.141592653589793
  let step = 2.0 * pi / samples.to_double()
  let first_points : Array[Array[Double]] = []
  let first_derivatives : Array[Array[Double]] = []
  let second_points : Array[Array[Double]] = []
  let second_derivatives : Array[Array[Double]] = []
  for i in 0..<samples {
    let t = (i.to_double() + 0.5) * step
    let (p1, v1) = hopf_stereographic_with_derivative(hopf_north_fiber(t), [
      0.0 - @math.sin(t),
      @math.cos(t),
      0.0,
      0.0,
    ])
    let (p2, v2) = hopf_stereographic_with_derivative(hopf_south_fiber(t), [
      0.0,
      0.0,
      0.0 - @math.sin(t),
      @math.cos(t),
    ])
    first_points.push(p1)
    first_derivatives.push(v1)
    second_points.push(p2)
    second_derivatives.push(v2)
  }
  let mut total = 0.0
  for i in 0..<samples {
    for j in 0..<samples {
      let r = [
        first_points[i][0] - second_points[j][0],
        first_points[i][1] - second_points[j][1],
        first_points[i][2] - second_points[j][2],
      ]
      let a = first_derivatives[i]
      let b = second_derivatives[j]
      let cross = [
        a[1] * b[2] - a[2] * b[1],
        a[2] * b[0] - a[0] * b[2],
        a[0] * b[1] - a[1] * b[0],
      ]
      let triple = r[0] * cross[0] + r[1] * cross[1] + r[2] * cross[2]
      let dist2 = r[0] * r[0] + r[1] * r[1] + r[2] * r[2]
      if dist2 > 0.0 {
        total = total + triple / (dist2 * dist2.sqrt())
      }
    }
  }
  total * step * step / (4.0 * pi)
}

// ---------------------------------------------------------------------------
// Representative checks
// ---------------------------------------------------------------------------

///|
fn hopf_vector_close(
  a : Array[Double],
  b : Array[Double],
  tolerance : Double,
) -> Bool {
  if a.length() != b.length() {
    return false
  }
  for i in 0..<a.length() {
    let difference = a[i] - b[i]
    if difference * difference > tolerance * tolerance {
      return false
    }
  }
  true
}

///|
/// Checks for the classical Hopf representatives: unit-sphere values,
/// phase/fiber invariance, constant canonical fibers and numerical
/// linking number one.
pub fn check_hopf_numeric() -> Bool {
  let samples = [
    [1.0, 0.0, 0.0, 0.0],
    [0.5, 0.5, 0.5, 0.5],
    [0.6, 0.0, 0.8, 0.0],
    [0.0, 0.6, 0.0, 0.8],
  ]
  for i in 0..<samples.length() {
    let image = hopf_map_s3_to_s2(samples[i])
    let norm2 = image[0] * image[0] + image[1] * image[1] + image[2] * image[2]
    let err = norm2 - 1.0
    if err * err > 0.000000001 {
      return false
    }
    let rotated_image = hopf_map_s3_to_s2(hopf_phase_rotate(samples[i], 0.7))
    if !hopf_vector_close(image, rotated_image, 0.000001) {
      return false
    }
  }
  let north_image = hopf_map_s3_to_s2(hopf_north_fiber(1.3))
  let south_image = hopf_map_s3_to_s2(hopf_south_fiber(2.1))
  if !hopf_vector_close(north_image, [0.0, 0.0, 1.0], 0.000001) {
    return false
  }
  if !hopf_vector_close(south_image, [0.0, 0.0, -1.0], 0.000001) {
    return false
  }
  let linking = hopf_linking_number_numeric(48)
  let magnitude_error = linking.abs() - 1.0
  magnitude_error * magnitude_error < 0.0064
}

///|
/// Aggregated checks for the spherical homotopy representatives in this
/// file: formations of iterated loop spaces, identity/zero degree maps
/// on generating meridian points, suspension-unit endpoints and the
/// pole-swapped round trips.
pub fn check_sphere_homotopy_representatives() -> Bool {
  // Closed formations: Omega^3(S^3) at the north pole and the type of
  // based endomaps of S^3.
  let s3_ty = sphere3_type_term()
  let north = sphere3_north_term()
  if !dep_check_closed(loop_space_type_term(s3_ty, north, 3), DUniv(0)) {
    return false
  }
  if !dep_check_closed(
      based_map_type_term(s3_ty, s3_ty, north, north),
      DUniv(0),
    ) {
    return false
  }

  let circle = circle_schema()
  let s2 = sphere2_schema()
  let s3 = sphere3_schema()
  let circle_ty : DValue = DVHitType(circle, [], [])
  let s2_ty : DValue = DVHitType(s2, [], [])
  let s3_value_ty : DValue = DVHitType(s3, [], [])
  let swapped_ty : DValue = DVHitType(sphere3_swapped_schema(), [], [])

  // Generating points with genuinely free dimensions at every stage.
  let circle_point : DValue = DVHitCell(circle, 1, [], [], [DVar(0)])
  let s2_point : DValue = DVHitCell(s2, 2, [], [circle_point], [DVar(1)])
  let s3_point : DValue = DVHitCell(s3, 2, [], [s2_point], [DVar(2)])

  // Degree one is the identity on these generators; degree zero sends
  // the base point at every stage to the chosen base point.
  if !conv_at(
      0,
      1,
      circle_ty,
      circle_degree_value(1, circle_point, 2),
      circle_point,
    ) {
    return false
  }
  if !conv_at(
      0,
      1,
      circle_ty,
      circle_degree_value(0, circle_point, 2),
      circle_hit_base_value(),
    ) {
    return false
  }
  if !conv_at(0, 2, s2_ty, sphere_degree_value(2, 1, s2_point, 3), s2_point) {
    return false
  }
  let s2_degree0_point : DValue = DVHitCell(
    s2,
    2,
    [],
    [circle_hit_base_value()],
    [DVar(1)],
  )
  if !conv_at(
      0,
      2,
      s2_ty,
      sphere_degree_value(2, 0, s2_point, 3),
      s2_degree0_point,
    ) {
    return false
  }
  if !conv_at(
      0,
      3,
      s3_value_ty,
      sphere_degree_value(3, 1, s3_point, 4),
      s3_point,
    ) {
    return false
  }
  let s3_degree0_point : DValue = DVHitCell(s3, 2, [], [s2_degree0_point], [
    DVar(2),
  ])
  if !conv_at(
      0,
      3,
      s3_value_ty,
      sphere_degree_value(3, 0, s3_point, 4),
      s3_degree0_point,
    ) {
    return false
  }

  // Degree maps are based at both suspension poles.
  if !conv_at(
      0,
      0,
      s3_value_ty,
      sphere_degree_value(3, -2, sphere3_north_value(), 2),
      sphere3_north_value(),
    ) {
    return false
  }
  if !conv_at(
      0,
      0,
      s3_value_ty,
      sphere_degree_value(3, 5, sphere3_south_value(), 2),
      sphere3_south_value(),
    ) {
    return false
  }

  // The suspension unit at the generic circle point is a loop at the
  // north pole of S^2.
  let unit_loop = suspension_unit_loop_value(
    s2,
    circle_hit_base_value(),
    circle_point,
    2,
  )
  if !conv_at(
      0,
      1,
      s2_ty,
      dapp_dim(unit_loop, DZero),
      DVHitCell(s2, 0, [], [], []),
    ) {
    return false
  }
  if !conv_at(
      0,
      1,
      s2_ty,
      dapp_dim(unit_loop, DOne),
      DVHitCell(s2, 0, [], [], []),
    ) {
    return false
  }

  // Pole-swapped round trips and the endpoints of their dependent
  // retraction/section paths on a fully generic meridian point.
  let round_trip = sphere3_from_swapped_value(
    sphere3_to_swapped_value(s3_point, 4),
    4,
  )
  if !conv_at(0, 3, s3_value_ty, round_trip, s3_point) {
    return false
  }
  let retr = sphere3_swapped_retr_value(s3_point, 4)
  if !conv_at(0, 3, s3_value_ty, dapp_dim(retr, DZero), round_trip) {
    return false
  }
  if !conv_at(0, 3, s3_value_ty, dapp_dim(retr, DOne), s3_point) {
    return false
  }
  let swapped_point = sphere3_swapped_meridian_value(s2_point, DVar(2))
  let swapped_round_trip = sphere3_to_swapped_value(
    sphere3_from_swapped_value(swapped_point, 4),
    4,
  )
  if !conv_at(0, 3, swapped_ty, swapped_round_trip, swapped_point) {
    return false
  }
  let sect = sphere3_swapped_sect_value(swapped_point, 4)
  if !conv_at(0, 3, swapped_ty, dapp_dim(sect, DZero), swapped_round_trip) {
    return false
  }
  if !conv_at(0, 3, swapped_ty, dapp_dim(sect, DOne), swapped_point) {
    return false
  }

  // The assembled equivalence datum has the expected source and target.
  match sphere3_swapped_equiv_value() {
    DVEquiv(source, target, _, _, _, _) =>
      conv_ty(0, 0, source, s3_value_ty) && conv_ty(0, 0, target, swapped_ty)
    _ => false
  }
}

// ---------------------------------------------------------------------------
// Phase 12: the Hopf map in exact rational arithmetic.
//
// The numerical layer above samples the Hopf map in floating
// point.  The same formulas are polynomial, so on rational
// points of `S^3` and rational phase rotations
// (`u^2 + v^2 = 1` in Q) the defining identities -- landing
// on `S^2`, invariance along fibers, and the pole fibers --
// hold as *exact* rational equalities, checked with the
// algebra package's `Rat`.  Rational points are dense in
// `S^3` and rational rotations are dense in the circle
// group, so this is the exact representative-level shadow of
// the fibration identities; it is not a proof about the
// internal Hopf map (which is not constructed).
// ---------------------------------------------------------------------------

///|
pub fn hopf_map_rat(q : Array[Rat]) -> Array[Rat] {
  if q.length() != 4 {
    return [rat_zero(), rat_zero(), rat_zero()]
  }
  let two = rat_int(2)
  [
    rat_mul(two, rat_add(rat_mul(q[0], q[2]), rat_mul(q[1], q[3]))),
    rat_mul(two, rat_sub(rat_mul(q[1], q[2]), rat_mul(q[0], q[3]))),
    rat_sub(
      rat_add(rat_mul(q[0], q[0]), rat_mul(q[1], q[1])),
      rat_add(rat_mul(q[2], q[2]), rat_mul(q[3], q[3])),
    ),
  ]
}

///|
/// Multiply both complex coordinates by `u + i v` exactly.
pub fn hopf_rotate_rat(q : Array[Rat], u : Rat, v : Rat) -> Array[Rat] {
  if q.length() != 4 {
    return [rat_zero(), rat_zero(), rat_zero(), rat_zero()]
  }
  [
    rat_sub(rat_mul(u, q[0]), rat_mul(v, q[1])),
    rat_add(rat_mul(v, q[0]), rat_mul(u, q[1])),
    rat_sub(rat_mul(u, q[2]), rat_mul(v, q[3])),
    rat_add(rat_mul(v, q[2]), rat_mul(u, q[3])),
  ]
}

///|
fn hopf_rat_eq(a : Array[Rat], b : Array[Rat]) -> Bool {
  if a.length() != b.length() {
    return false
  }
  for i in 0..<a.length() {
    if !rat_is_zero(rat_sub(a[i], b[i])) {
      return false
    }
  }
  true
}

///|
fn hopf_rat_norm2(q : Array[Rat]) -> Rat {
  let mut acc = rat_zero()
  for i in 0..<q.length() {
    acc = rat_add(acc, rat_mul(q[i], q[i]))
  }
  acc
}

///|
fn hopf_rat_point(
  a : Int32,
  b : Int32,
  c : Int32,
  d : Int32,
  den : Int32,
) -> Array[Rat] {
  [rat_make(a, den), rat_make(b, den), rat_make(c, den), rat_make(d, den)]
}

///|
/// Exact rational verification of the Hopf identities: every
/// listed rational point lies on `S^3`, its image lies on
/// `S^2`, rational phase rotations stay inside one fiber
/// (same image, exactly), the pole fibers map to the poles,
/// and two distinct sampled fibers have no sampled point in
/// common.
pub fn check_hopf_exact_rational() -> Bool {
  let one = rat_one()
  let points = [
    hopf_rat_point(1, 0, 0, 0, 1),
    hopf_rat_point(0, 0, 1, 0, 1),
    hopf_rat_point(3, 0, 4, 0, 5),
    hopf_rat_point(1, 2, 2, 0, 3),
    hopf_rat_point(1, 1, 1, 1, 2),
    hopf_rat_point(2, 3, 6, 0, 7),
    hopf_rat_point(4, 4, 7, 0, 9),
    hopf_rat_point(2, 6, 3, 0, 7),
  ]
  let rotations : Array[(Rat, Rat)] = [
    (rat_make(1, 1), rat_make(0, 1)),
    (rat_make(0, 1), rat_make(1, 1)),
    (rat_make(3, 5), rat_make(4, 5)),
    (rat_make(5, 13), rat_make(12, 13)),
    (rat_make(8, 17), rat_make(-15, 17)),
    (rat_make(-7, 25), rat_make(24, 25)),
  ]
  for r in 0..<rotations.length() {
    let (u, v) = rotations[r]
    if !rat_is_zero(rat_sub(hopf_rat_norm2([u, v]), one)) {
      return false
    }
  }
  for p in 0..<points.length() {
    let q = points[p]
    if !rat_is_zero(rat_sub(hopf_rat_norm2(q), one)) {
      return false
    }
    let image = hopf_map_rat(q)
    if !rat_is_zero(rat_sub(hopf_rat_norm2(image), one)) {
      return false
    }
    for r in 0..<rotations.length() {
      let (u, v) = rotations[r]
      let rotated = hopf_rotate_rat(q, u, v)
      if !rat_is_zero(rat_sub(hopf_rat_norm2(rotated), one)) ||
        !hopf_rat_eq(hopf_map_rat(rotated), image) {
        return false
      }
    }
  }
  // Pole fibers, exactly.
  let zero = rat_zero()
  for r in 0..<rotations.length() {
    let (u, v) = rotations[r]
    if !hopf_rat_eq(hopf_map_rat([u, v, zero, zero]), [zero, zero, one]) ||
      !hopf_rat_eq(hopf_map_rat([zero, zero, u, v]), [zero, zero, rat_int(-1)]) {
      return false
    }
  }
  // Two distinct fibers: different images, and no sampled
  // rotation of one point equals a sampled rotation of the
  // other.
  let fiber_a = points[2]
  let fiber_b = points[4]
  if hopf_rat_eq(hopf_map_rat(fiber_a), hopf_map_rat(fiber_b)) {
    return false
  }
  for r in 0..<rotations.length() {
    let (u, v) = rotations[r]
    let ra = hopf_rotate_rat(fiber_a, u, v)
    for s in 0..<rotations.length() {
      let (u2, v2) = rotations[s]
      if hopf_rat_eq(ra, hopf_rotate_rat(fiber_b, u2, v2)) {
        return false
      }
    }
  }
  true
}

// ---------------------------------------------------------------------------
// Phase 14: Internal univalent Hopf fibration `Hopf : S^2 -> Type_0` and
// synthetic Hopf invariant `Omega^2(S^2) -> IntegerS`
// ---------------------------------------------------------------------------

///|
/// Dependent loop family `(y : S^1) -> Path S^1 y y` on the schema circle:
/// sends `base` to `loop`, and over `y = loop(i)` builds the conjugated
/// path `sym(loop_{<= i}) ⬝ (loop ⬝ loop_{<= i})` adjusted on `i = 0, 1`
/// to `loop` by unit/inverse 3-cells.
pub fn circle_self_loop_value(y : DValue, dlevel : Int32) -> DValue {
  let s1 = circle_hit_type_value()
  let lp = circle_hit_loop_path_value()
  // Direct Cavallo–Mörtberg / Cubical Agda `rotLoop` square:
  // base at `k = 0` is `lp(i ∨ j)`, with corner `(i=1, j=1)` traversing `lp(k)`.
  let loop_case : DValue = DVPathLam(i => {
    DVPathLam(j => {
      let branches = dsystem_of([
        tube_branch(face_simplify(FEq0(i)), _ => dapp_dim(lp, j)),
        tube_branch(face_simplify(FEq1(i)), k => {
          dapp_dim(lp, dim_simplify(DAnd(j, k)))
        }),
        tube_branch(face_simplify(FEq0(j)), _ => dapp_dim(lp, i)),
        tube_branch(face_simplify(FEq1(j)), k => {
          dapp_dim(lp, dim_simplify(DAnd(i, k)))
        }),
      ])
      hcomp_value(
        s1,
        branches,
        dapp_dim(lp, dim_simplify(DOr(i, j))),
        dlevel + 2,
      )
    })
  })

  eval_hit_elim(
    circle_schema(),
    (_idx, pt) => DVPathTy(_ => s1, pt, pt),
    [lp, loop_case],
    [],
    [],
    y,
    dlevel,
  )
}

///|
/// H-space rotation equivalence `(x : S^1) -> (S^1 ≃ S^1)` on the schema
/// circle: sends `base` to `id_equiv(S^1)` and `loop` to the rotation
/// loop `i ↦ (y ↦ self_loop(y)(i))`.
pub fn circle_rot_equiv_value(x : DValue, dlevel : Int32) -> DValue {
  let s1 = circle_hit_type_value()
  let id_eq = equiv_id_value(s1)
  // Along `x = loop(i)`: forward map rotates by `+i`, backward map by `-i`.
  // At `i = 0` and `i = 1`, both `fwd` and `bwd` compute to the identity `λy. y`.
  let loop_equiv_path : DValue = DVPathLam(i => {
    let fwd = DVLam(y => dapp_dim(circle_self_loop_value(y, dlevel), i))
    let bwd = DVLam(y => dapp_dim(circle_self_loop_value(y, dlevel), DNeg(i)))
    // Section `fwd(bwd(y)) = y` and retraction `bwd(fwd(y)) = y`:
    // contract along `i` on endpoints via connection with `self_loop`.
    let sect = DVLam(y => {
      let ly = circle_self_loop_value(y, dlevel)
      let fby = dapp_dim(
        circle_self_loop_value(dapp_dim(ly, DNeg(i)), dlevel),
        i,
      )
      // Connect `fby` to `y` on `S^1`: at `i=0` and `i=1`, `fby == y`,
      // and at `y = base` let's use singleton / loop cancellation!
      DVPathLam(k => {
        let step_back = dapp_dim(ly, dim_simplify(DAnd(DNeg(i), DNeg(k))))
        let raw = dapp_dim(
          circle_self_loop_value(step_back, dlevel),
          dim_simplify(DAnd(i, DNeg(k))),
        )
        ignore(fby)
        raw
      })
    })
    let retr = DVLam(y => {
      let ly = circle_self_loop_value(y, dlevel)
      DVPathLam(k => {
        let step_fwd = dapp_dim(ly, dim_simplify(DAnd(i, DNeg(k))))
        dapp_dim(
          circle_self_loop_value(step_fwd, dlevel),
          dim_simplify(DAnd(DNeg(i), DNeg(k))),
        )
      })
    })
    DVEquiv(s1, s1, fwd, bwd, sect, retr)
  })
  eval_hit_elim(
    circle_schema(),
    (_idx, _pt) => DVEquivTy(s1, s1, 0),
    [id_eq, loop_equiv_path],
    [],
    [],
    x,
    dlevel,
  )
}

///|
/// Brunerie's univalent Hopf fibration family `Hopf : S^2 -> Type_0`
/// defined internally by suspension elimination on `sphere2_schema()`:
/// fibers over `north` and `south` are `S^1`, and `meridian(x)` maps to
/// `ua(circle_rot_equiv(x))`.
pub fn hopf_family_value(pt : DValue, dlevel~ : Int32 = 16) -> DValue {
  let s1 = circle_hit_type_value()
  eval_hit_elim(
    sphere2_schema(),
    (_idx, _p) => DVUniv(0),
    [s1, s1, DVLam(x => ua_value(circle_rot_equiv_value(x, dlevel), s1, s1, 0))],
    [],
    [],
    pt,
    dlevel + 2,
  )
}

///|
/// Connecting map `∂_Hopf : Omega^2(S^2, north) -> Omega^1(S^1, base)`
/// of the Hopf fibration long exact sequence: transports `base : S^1`
/// in `Hopf` along each slice `alpha(i) : Omega^1(S^2, north)`.
pub fn hopf_connecting_loop_value(
  alpha : DValue,
  dlevel~ : Int32 = 16,
) -> DValue {
  let base_s1 = circle_hit_base_value()
  DVPathLam(
    memo_dim_line(i => {
      subst_value(
        pt => hopf_family_value(pt, dlevel~),
        dapp_dim(alpha, i),
        base_s1,
        dlevel + 6,
      )
    }),
  )
}

///|
/// Synthetic Hopf / degree invariant `Omega^2(S^2, north) -> IntegerS`
/// computed purely inside the cubical kernel by composing `∂_Hopf` with
/// the circle helix encoder `circle_encode_value`.
pub fn hopf_invariant_value(alpha : DValue, dlevel~ : Int32 = 16) -> DValue {
  circle_encode_value(hopf_connecting_loop_value(alpha, dlevel~), dlevel + 10)
}

// ---------------------------------------------------------------------------
// Phase 15: Polymorphic Suspension `SuspS`, Bidirectional Loop–Suspension
// Adjunction, Wedge Connectivity & Freudenthal Suspension Theorem
// ---------------------------------------------------------------------------

///|
/// Universe-polymorphic suspension HIT schema `SuspS(A : Type_level)`:
///   `north : SuspS(A)`
///   `south : SuspS(A)`
///   `meridian (point : A) : north = south`.
pub fn susp_type_schema_at(level : Int32) -> DHitSpec {
  dhit_spec("SuspS", level, [dtelescope_entry("A", DUniv(level))], [], [
    dhit_cell_spec("north", 0, [], []),
    dhit_cell_spec("south", 0, [], []),
    dhit_cell_spec(
      "meridian",
      1,
      [darg_external("point", DTVar(0))],
      [dhit_face(0, [], []), dhit_face(1, [], [])],
    ),
  ])
}

///|
pub fn susp_type_schema() -> DHitSpec {
  susp_type_schema_at(0)
}

///|
pub fn susp_type_value(a_ty : DValue, level~ : Int32 = 0) -> DValue {
  DVHitType(susp_type_schema_at(level), [a_ty], [])
}

///|
pub fn susp_north_value(a_ty : DValue, level~ : Int32 = 0) -> DValue {
  DVHitCell(susp_type_schema_at(level), 0, [a_ty], [], [])
}

///|
pub fn susp_south_value(a_ty : DValue, level~ : Int32 = 0) -> DValue {
  DVHitCell(susp_type_schema_at(level), 1, [a_ty], [], [])
}

///|
pub fn susp_merid_path_value(
  a_ty : DValue,
  point : DValue,
  level~ : Int32 = 0,
) -> DValue {
  let spec = susp_type_schema_at(level)
  DVPathLam(i => hit_cell_value(spec, 2, [a_ty], [point], [i]))
}

///|
/// Semantic based-map type `Map*(A, a0; B, b0) := Σ(f : A -> B). Path B (f a0) b0`.
pub fn based_map_type_value(
  src_ty : DValue,
  dst_ty : DValue,
  src_base : DValue,
  dst_base : DValue,
) -> DValue {
  DVSigma(
    DVPi(src_ty, _ => dst_ty),
    f => DVPathTy(_ => dst_ty, dapp_typed(f, src_base, src_ty), dst_base),
  )
}

///|
/// Forward map `SuspS(BoolS) -> S^1` sending both poles to `base`,
/// `meridian(false)` to `refl_base`, and `meridian(true)` to `loop`.
pub fn susp_bool_to_circle_value(z : DValue, dlevel : Int32) -> DValue {
  let b_spec = bool_schema()
  let b_ty = DVInductive(b_spec, [], [])
  let c_ty = circle_hit_type_value()
  let base = circle_hit_base_value()
  let lp = circle_hit_loop_path_value()
  let merid_fn = DVLam(b => {
    eval_inductive_elim(
      b_spec,
      (_, _) => DVPathTy(_ => c_ty, base, base),
      [dpath_refl_value(base), lp],
      [],
      [],
      b,
      dlevel,
    )
  })
  eval_hit_elim(
    susp_type_schema(),
    (_, _) => c_ty,
    [base, base, merid_fn],
    [b_ty],
    [],
    z,
    dlevel,
  )
}

///|
/// Inverse map `S^1 -> SuspS(BoolS)` sending `base` to `north` and `loop`
/// to `meridian(true) ⬝ sym(meridian(false))`.
pub fn circle_to_susp_bool_value(y : DValue, dlevel : Int32) -> DValue {
  let b_spec = bool_schema()
  let b_ty = DVInductive(b_spec, [], [])
  let sb_ty = susp_type_value(b_ty)
  let north = susp_north_value(b_ty)
  let bfalse = DVIntro(b_spec, 0, [], [])
  let btrue = DVIntro(b_spec, 1, [], [])
  let m_false = susp_merid_path_value(b_ty, bfalse)
  let m_true = susp_merid_path_value(b_ty, btrue)
  let bwd_loop = dpath_trans_value(
    sb_ty,
    m_true,
    dpath_sym_value(m_false),
    dlevel,
  )
  eval_hit_elim(
    circle_schema(),
    (_, _) => sb_ty,
    [north, bwd_loop],
    [],
    [],
    y,
    dlevel,
  )
}

///|
/// Full bidirectional equivalence `Equiv (SuspS BoolS) S^1` (`Susp S^0 ≃ S^1`),
/// certified on open reflected variables of both `SuspS(BoolS)` and `S^1`.
pub fn susp_bool_equiv_circle_value(dlevel : Int32) -> DValue {
  let b_spec = bool_schema()
  let b_ty = DVInductive(b_spec, [], [])
  let bfalse = DVIntro(b_spec, 0, [], [])
  let btrue = DVIntro(b_spec, 1, [], [])
  let sb_spec = susp_type_schema()
  let sb_ty = susp_type_value(b_ty)
  let north = susp_north_value(b_ty)
  let m_false = susp_merid_path_value(b_ty, bfalse)
  let m_true = susp_merid_path_value(b_ty, btrue)
  let c_spec = circle_schema()
  let c_ty = circle_hit_type_value()
  let base = circle_hit_base_value()
  let lp = circle_hit_loop_path_value()

  let sq_c = dpath_trans_square_value(
    c_ty,
    lp,
    dpath_refl_value(base),
    dlevel,
  )
  let loop_sect : DValue = DVPathLam(i => {
    DVPathLam(t => dapp_dim(dapp_dim(sq_c, i), DNeg(t)))
  })
  let sect = DVLam(y => {
    eval_hit_elim(
      c_spec,
      (_, pt) => {
        DVPathTy(
          _ => c_ty,
          susp_bool_to_circle_value(circle_to_susp_bool_value(pt, dlevel), dlevel),
          pt,
        )
      },
      [dpath_refl_value(base), loop_sect],
      [],
      [],
      y,
      dlevel,
    )
  })

  let false_sq : DValue = DVPathLam(i => {
    DVPathLam(j => dapp_dim(m_false, dim_simplify(DAnd(i, j))))
  })
  let sq_sb = dpath_trans_square_value(
    sb_ty,
    m_true,
    dpath_sym_value(m_false),
    dlevel,
  )
  let true_sq : DValue = DVPathLam(i => {
    DVPathLam(j => dapp_dim(dapp_dim(sq_sb, i), DNeg(j)))
  })
  let merid_retr = DVLam(b => {
    eval_inductive_elim(
      b_spec,
      (_, bv) => {
        DVPathTy(
          i => {
            let pt = hit_cell_value(sb_spec, 2, [b_ty], [bv], [i])
            DVPathTy(
              _ => sb_ty,
              circle_to_susp_bool_value(
                susp_bool_to_circle_value(pt, dlevel),
                dlevel,
              ),
              pt,
            )
          },
          dpath_refl_value(north),
          m_false,
        )
      },
      [false_sq, true_sq],
      [],
      [],
      b,
      dlevel,
    )
  })
  let retr = DVLam(z => {
    eval_hit_elim(
      sb_spec,
      (_, pt) => {
        DVPathTy(
          _ => sb_ty,
          circle_to_susp_bool_value(
            susp_bool_to_circle_value(pt, dlevel),
            dlevel,
          ),
          pt,
        )
      },
      [dpath_refl_value(north), m_false, merid_retr],
      [b_ty],
      [],
      z,
      dlevel,
    )
  })

  equiv_make_value(
    sb_ty,
    c_ty,
    DVLam(z => susp_bool_to_circle_value(z, dlevel)),
    DVLam(y => circle_to_susp_bool_value(y, dlevel)),
    sect,
    retr,
  )
}

///|
/// Unpointed suspension cocone type `SuspCocone(A, B) := Σ(n : B). Σ(s : B). (A -> Path B n s)`.
pub fn susp_cocone_type_value(a_ty : DValue, b_ty : DValue) -> DValue {
  DVSigma(b_ty, n => {
    DVSigma(b_ty, s => DVPi(a_ty, _ => DVPathTy(_ => b_ty, n, s)))
  })
}

///|
/// Universal cocone bidirectional equivalence
///   `Equiv (SuspS A -> B) (SuspCocone A B)`.
/// Notice that while `sect` holds definitionally on reflected `Σ`/`Π`/`Path`
/// cocones, `retr` genuinely requires function extensionality + dependent
/// `SuspS` elimination (HITs lack definitional η on neutral points).
pub fn susp_universal_equiv_value(
  a_ty : DValue,
  b_ty : DValue,
  dlevel : Int32,
  level~ : Int32 = 0,
) -> DValue {
  let spec = susp_type_schema_at(level)
  let susp_ty = susp_type_value(a_ty, level~)
  let north = susp_north_value(a_ty, level~)
  let south = susp_south_value(a_ty, level~)
  let fn_ty = DVPi(susp_ty, _ => b_ty)
  let cocone_ty = susp_cocone_type_value(a_ty, b_ty)
  let inner_fam = (n : DValue) => {
    DVSigma(b_ty, s => DVPi(a_ty, _ => DVPathTy(_ => b_ty, n, s)))
  }

  let fwd_one = (f : DValue) => {
    let fn_n = dapp_typed(f, north, susp_ty)
    let fn_s = dapp_typed(f, south, susp_ty)
    let fn_m = DVLam(a => {
      DVPathLam(i => {
        dapp_typed(f, hit_cell_value(spec, 2, [a_ty], [a], [i]), susp_ty)
      })
    })
    DVPair(fn_n, DVPair(fn_s, fn_m))
  }
  let bwd_one = (c : DValue) => {
    let n = dfst_typed(c, inner_fam)
    let rest = dsnd_typed(c, b_ty, inner_fam)
    let rest_fam = (s : DValue) => DVPi(a_ty, _ => DVPathTy(_ => b_ty, n, s))
    let s = dfst_typed(rest, rest_fam)
    let m = dsnd_typed(rest, b_ty, rest_fam)
    DVLam(z => {
      eval_hit_elim(spec, (_, _) => b_ty, [n, s, m], [a_ty], [], z, dlevel)
    })
  }
  let sect = DVLam(c => dpath_refl_value(c))
  let retr = DVLam(f => {
    let bf = bwd_one(fwd_one(f))
    let pw = DVLam(z => {
      eval_hit_elim(
        spec,
        (_, pt) => {
          DVPathTy(_ => b_ty, dapp_typed(bf, pt, susp_ty), dapp_typed(f, pt, susp_ty))
        },
        [
          dpath_refl_value(dapp_typed(f, north, susp_ty)),
          dpath_refl_value(dapp_typed(f, south, susp_ty)),
          DVLam(a => {
            DVPathLam(i => {
              let f_mer = dapp_typed(
                f,
                hit_cell_value(spec, 2, [a_ty], [a], [i]),
                susp_ty,
              )
              DVPathLam(_ => f_mer)
            })
          }),
        ],
        [a_ty],
        [],
        z,
        dlevel,
      )
    })
    dpath_funext_value(pw, susp_ty)
  })
  equiv_make_value(
    fn_ty,
    cocone_ty,
    DVLam(f => fwd_one(f)),
    DVLam(c => bwd_one(c)),
    sect,
    retr,
  )
}

///|
/// First factor of the pointed Loop–Suspension Adjunction:
///   `Map*(SuspS A, north; B, b0)  ≃  Σ(s : B). (A -> Path B s b0)`.
pub fn susp_based_to_cocone_equiv_value(
  a_ty : DValue,
  b_ty : DValue,
  b0 : DValue,
  dlevel : Int32,
  level~ : Int32 = 0,
) -> DValue {
  let spec = susp_type_schema_at(level)
  let susp_ty = susp_type_value(a_ty, level~)
  let north = susp_north_value(a_ty, level~)
  let south = susp_south_value(a_ty, level~)
  let fn_ty = DVPi(susp_ty, _ => b_ty)
  let map_star_ty = based_map_type_value(susp_ty, b_ty, north, b0)
  let map_fam = (f : DValue) => {
    DVPathTy(_ => b_ty, dapp_typed(f, north, susp_ty), b0)
  }
  let cocone_fam = (s : DValue) => DVPi(a_ty, _ => DVPathTy(_ => b_ty, s, b0))
  let cocone_ty = DVSigma(b_ty, cocone_fam)

  let fwd_one = (fp : DValue) => {
    let f = dfst_typed(fp, map_fam)
    let p = dsnd_typed(fp, fn_ty, map_fam)
    let s = dapp_typed(f, south, susp_ty)
    let m = DVLam(a => {
      let sym_fa : DValue = DVPathLam(i => {
        dapp_typed(f, hit_cell_value(spec, 2, [a_ty], [a], [DNeg(i)]), susp_ty)
      })
      dpath_trans_value(b_ty, sym_fa, p, dlevel)
    })
    DVPair(s, m)
  }
  let bwd_one = (sm : DValue) => {
    let s = dfst_typed(sm, cocone_fam)
    let m = dsnd_typed(sm, b_ty, cocone_fam)
    let merid_case = DVLam(a => dpath_sym_value(dapp_typed(m, a, a_ty)))
    let f = DVLam(z => {
      eval_hit_elim(
        spec,
        (_, _) => b_ty,
        [b0, s, merid_case],
        [a_ty],
        [],
        z,
        dlevel,
      )
    })
    DVPair(f, dpath_refl_value(b0))
  }
  let sect = DVLam(sm => {
    let s = dfst_typed(sm, cocone_fam)
    let m = dsnd_typed(sm, b_ty, cocone_fam)
    DVPathLam(t => {
      let m_t = DVLam(a => {
        let ma = dapp_typed(m, a, a_ty)
        let sq = dpath_trans_square_value(
          b_ty,
          ma,
          dpath_refl_value(b0),
          dlevel,
        )
        DVPathLam(i => dapp_dim(dapp_dim(sq, i), DNeg(t)))
      })
      DVPair(s, m_t)
    })
  })
  let retr = DVLam(fp => {
    let f = dfst_typed(fp, map_fam)
    let p = dsnd_typed(fp, fn_ty, map_fam)
    let bf_pair = bwd_one(fwd_one(fp))
    let bf = dfst_typed(bf_pair, map_fam)
    let north_line : DValue = DVPathLam(t => dapp_dim(p, DNeg(t)))
    let south_line = dpath_refl_value(dapp_typed(f, south, susp_ty))
    let merid_sq = DVLam(a => {
      let sym_fa : DValue = DVPathLam(k => {
        dapp_typed(f, hit_cell_value(spec, 2, [a_ty], [a], [DNeg(k)]), susp_ty)
      })
      let sq = dpath_trans_square_value(b_ty, sym_fa, p, dlevel)
      DVPathLam(i => {
        DVPathLam(t => dapp_dim(dapp_dim(sq, DNeg(i)), DNeg(t)))
      })
    })
    let pw = DVLam(z => {
      eval_hit_elim(
        spec,
        (_, pt) => {
          DVPathTy(
            _ => b_ty,
            dapp_typed(bf, pt, susp_ty),
            dapp_typed(f, pt, susp_ty),
          )
        },
        [north_line, south_line, merid_sq],
        [a_ty],
        [],
        z,
        dlevel,
      )
    })
    let f_homotopy = dpath_funext_value(pw, susp_ty)
    DVPathLam(t => {
      let p_t : DValue = DVPathLam(j => {
        dapp_dim(p, dim_simplify(DOr(DNeg(t), j)))
      })
      DVPair(dapp_dim(f_homotopy, t), p_t)
    })
  })
  equiv_make_value(
    map_star_ty,
    cocone_ty,
    DVLam(fp => fwd_one(fp)),
    DVLam(sm => bwd_one(sm)),
    sect,
    retr,
  )
}

///|
/// Second factor of the pointed Loop–Suspension Adjunction:
///   `Σ(s : B). (A -> Path B s b0)  ≃  Map*(A, a0; Ω(B, b0), refl_{b0})`.
pub fn cocone_to_based_loop_equiv_value(
  a_ty : DValue,
  a0 : DValue,
  b_ty : DValue,
  b0 : DValue,
  dlevel : Int32,
) -> DValue {
  let cocone_fam = (s : DValue) => DVPi(a_ty, _ => DVPathTy(_ => b_ty, s, b0))
  let cocone_ty = DVSigma(b_ty, cocone_fam)
  let loop_b_ty = DVPathTy(_ => b_ty, b0, b0)
  let refl_b0 = dpath_refl_value(b0)
  let fn_loop_ty = DVPi(a_ty, _ => loop_b_ty)
  let rhs_fam = (g : DValue) => {
    DVPathTy(_ => loop_b_ty, dapp_typed(g, a0, a_ty), refl_b0)
  }
  let rhs_ty = based_map_type_value(a_ty, loop_b_ty, a0, refl_b0)

  let l_fill = (m0 : DValue, ma : DValue, i : Dim, k : Dim) => {
    let ks = dim_simplify(k)
    if dim_eq_sem(ks, DZero) {
      dapp_dim(ma, i)
    } else {
      let sys = dsystem_of([
        tube_branch(face_simplify(FEq0(i)), j => {
          dapp_dim(m0, dim_simplify(DAnd(j, ks)))
        }),
        tube_branch(face_simplify(FEq1(i)), _ => b0),
        tube_branch(face_simplify(FEq0(ks)), _ => dapp_dim(ma, i)),
      ])
      hcomp_value(b_ty, sys, dapp_dim(ma, i), dlevel)
    }
  }
  let cancel = (m0 : DValue) => {
    DVPathLam(u => {
      DVPathLam(i => {
        let sys = dsystem_of([
          tube_branch(face_simplify(FEq0(i)), j => {
            dapp_dim(m0, dim_simplify(DOr(j, u)))
          }),
          tube_branch(face_simplify(FEq1(i)), _ => b0),
          tube_branch(face_simplify(FEq1(u)), _ => b0),
        ])
        hcomp_value(b_ty, sys, dapp_dim(m0, dim_simplify(DOr(i, u))), dlevel)
      })
    })
  }
  let h_loop_at = (ga : DValue, q : DValue, t : Dim) => {
    DVPathLam(i => {
      let sys = dsystem_of([
        tube_branch(face_simplify(FEq0(i)), j => {
          dapp_dim(dapp_dim(q, t), j)
        }),
        tube_branch(face_simplify(FEq1(i)), _ => b0),
        tube_branch(face_simplify(FEq1(t)), _ => dapp_dim(ga, i)),
      ])
      hcomp_value(b_ty, sys, dapp_dim(ga, i), dlevel)
    })
  }

  let fwd_one = (sm : DValue) => {
    let m = dsnd_typed(sm, b_ty, cocone_fam)
    let m0 = dapp_typed(m, a0, a_ty)
    let g = DVLam(a => {
      let ma = dapp_typed(m, a, a_ty)
      DVPathLam(i => l_fill(m0, ma, i, DOne))
    })
    DVPair(g, cancel(m0))
  }
  let bwd_one = (gq : DValue) => {
    let g = dfst_typed(gq, rhs_fam)
    DVPair(b0, g)
  }
  let base_sq : DValue = DVPathLam(t => {
    DVPathLam(u => {
      DVPathLam(i => {
        let sys = dsystem_of([
          tube_branch(face_simplify(FEq0(i)), _ => b0),
          tube_branch(face_simplify(FEq1(i)), _ => b0),
          tube_branch(
            face_simplify(FEq1(dim_simplify(DOr(t, u)))),
            _ => b0,
          ),
        ])
        hcomp_value(b_ty, sys, b0, dlevel)
      })
    })
  })
  let sect = DVLam(gq => {
    let g = dfst_typed(gq, rhs_fam)
    let q = dsnd_typed(gq, fn_loop_ty, rhs_fam)
    let sq_q = dj_singleton_elim_value(
      (p0, sym_q) => {
        let q1 = dpath_sym_value(sym_q)
        DVPathTy(
          t => DVPathTy(_ => loop_b_ty, h_loop_at(p0, q1, t), refl_b0),
          cancel(p0),
          q1,
        )
      },
      base_sq,
      dpath_sym_value(q),
      dlevel + 4,
    )
    DVPathLam(t => {
      let g_t = DVLam(a => h_loop_at(dapp_typed(g, a, a_ty), q, t))
      DVPair(g_t, dapp_dim(sq_q, t))
    })
  })
  let retr = DVLam(sm => {
    let m = dsnd_typed(sm, b_ty, cocone_fam)
    let m0 = dapp_typed(m, a0, a_ty)
    DVPathLam(t => {
      let m_t = DVLam(a => {
        let ma = dapp_typed(m, a, a_ty)
        DVPathLam(i => l_fill(m0, ma, i, DNeg(t)))
      })
      DVPair(dapp_dim(m0, DNeg(t)), m_t)
    })
  })
  equiv_make_value(
    cocone_ty,
    rhs_ty,
    DVLam(sm => fwd_one(sm)),
    DVLam(gq => bwd_one(gq)),
    sect,
    retr,
  )
}

///|
/// Full bidirectional pointed Loop–Suspension Adjunction Equivalence
///   `Equiv (Map*(SuspS A, north; B, b0)) (Map*(A, a0; Ω(B, b0), refl_{b0}))`
/// valid uniformly over arbitrary pointed types `(A, a0)` and `(B, b0)`.
pub fn loop_suspension_adjunction_equiv_value(
  a_ty : DValue,
  a0 : DValue,
  b_ty : DValue,
  b0 : DValue,
  dlevel : Int32,
  level~ : Int32 = 0,
) -> DValue {
  let susp_ty = susp_type_value(a_ty, level~)
  let north = susp_north_value(a_ty, level~)
  let lhs_ty = based_map_type_value(susp_ty, b_ty, north, b0)
  let mid_ty = DVSigma(b_ty, s => DVPi(a_ty, _ => DVPathTy(_ => b_ty, s, b0)))
  let loop_b_ty = DVPathTy(_ => b_ty, b0, b0)
  let rhs_ty = based_map_type_value(a_ty, loop_b_ty, a0, dpath_refl_value(b0))
  let e1 = susp_based_to_cocone_equiv_value(a_ty, b_ty, b0, dlevel, level~)
  let e2 = cocone_to_based_loop_equiv_value(a_ty, a0, b_ty, b0, dlevel)
  equiv_compose_value(e1, e2, lhs_ty, mid_ty, rhs_ty, dlevel + 6)
}

// ---------------------------------------------------------------------------
// Internal 0-Connectedness & General Freudenthal Suspension Theorem (`n = 0`)
// ---------------------------------------------------------------------------

///|
/// Internal 0-connectedness of `S^1`: `(x : S^1) -> ‖Path S^1 base x‖₋₁`.
pub fn circle_0_connected_value(x : DValue, dlevel : Int32) -> DValue {
  let c_spec = circle_schema()
  let c_ty = circle_hit_type_value()
  let base = circle_hit_base_value()
  let mot = (pt : DValue) => {
    prop_trunc_type_value(DVPathTy(_ => c_ty, base, pt))
  }
  let base_inc = prop_trunc_point_value(
    DVPathTy(_ => c_ty, base, base),
    dpath_refl_value(base),
  )
  let loop_line = memo_dim_line(i => {
    mot(hit_cell_value(c_spec, 1, [], [], [i]))
  })
  let tr = transport_value(loop_line, base_inc, dlevel)
  let sq_eq = prop_trunc_squash_path_value(
    DVPathTy(_ => c_ty, base, base),
    tr,
    base_inc,
  )
  let loop_case = dpathp_of_transport_eq_value(
    loop_line,
    base_inc,
    base_inc,
    sq_eq,
    dlevel,
  )
  eval_hit_elim(
    c_spec,
    (_, pt) => mot(pt),
    [base_inc, loop_case],
    [],
    [],
    x,
    dlevel,
  )
}

///|
/// Every suspension `SuspS(A)` of a pointed (inhabited) type `(A, a0)` is
/// internally 0-connected: `(z : SuspS A) -> ‖Path (SuspS A) north z‖₋₁`.
pub fn susp_0_connected_of_pointed_value(
  a_ty : DValue,
  a0 : DValue,
  z : DValue,
  dlevel : Int32,
  level~ : Int32 = 0,
) -> DValue {
  let spec = susp_type_schema_at(level)
  let susp_ty = susp_type_value(a_ty, level~)
  let north = susp_north_value(a_ty, level~)
  let south = susp_south_value(a_ty, level~)
  let mot = (pt : DValue) => {
    prop_trunc_type_value(DVPathTy(_ => susp_ty, north, pt))
  }
  let north_inc = prop_trunc_point_value(
    DVPathTy(_ => susp_ty, north, north),
    dpath_refl_value(north),
  )
  let south_inc = prop_trunc_point_value(
    DVPathTy(_ => susp_ty, north, south),
    susp_merid_path_value(a_ty, a0, level~),
  )
  let merid_case = DVLam(a => {
    let m_line = memo_dim_line(i => {
      mot(hit_cell_value(spec, 2, [a_ty], [a], [i]))
    })
    let tr = transport_value(m_line, north_inc, dlevel)
    let sq_eq = prop_trunc_squash_path_value(
      DVPathTy(_ => susp_ty, north, south),
      tr,
      south_inc,
    )
    dpathp_of_transport_eq_value(m_line, north_inc, south_inc, sq_eq, dlevel)
  })
  eval_hit_elim(
    spec,
    (_, pt) => mot(pt),
    [north_inc, south_inc, merid_case],
    [a_ty],
    [],
    z,
    dlevel,
  )
}

///|
/// **General Freudenthal Suspension Theorem at Connectivity `k = 0`**:
/// For ANY pointed 0-connected type `(A, a0, conn : (a : A) -> ‖Path A a0 a‖₋₁)`,
/// its suspension `SuspS(A)` is 1-connected — i.e., its 0-truncated fundamental
/// group is bidirectionally equivalent to `Unit`:
///   `Equiv ‖Ω¹(SuspS A, north)‖₀ Unit`.
/// Proved internally by dependent suspension encode-decode into
/// `z ↦ ‖Path (SuspS A) north z‖₀` (using `conn(a)` + `prop_trunc_elim_prop_value`
/// + `set_trunc_is_set_value` on meridians) followed by `set_trunc_elim_set_value`
/// and singleton contraction `J`.
pub fn freudenthal_pi1_susp_connected_equiv_unit_value(
  a_ty : DValue,
  a0 : DValue,
  conn : (DValue) -> DValue,
  dlevel : Int32,
  level~ : Int32 = 0,
) -> DValue {
  let spec = susp_type_schema_at(level)
  let susp_ty = susp_type_value(a_ty, level~)
  let north = susp_north_value(a_ty, level~)
  let south = susp_south_value(a_ty, level~)
  let ns_ty = DVPathTy(_ => susp_ty, north, south)
  let st_ns_ty = set_trunc_type_value(ns_ty)
  let loop_ty = DVPathTy(_ => susp_ty, north, north)
  let st_loop_ty = set_trunc_type_value(loop_ty)

  let mot_center = (pt : DValue) => {
    set_trunc_type_value(DVPathTy(_ => susp_ty, north, pt))
  }
  let c_north = set_trunc_point_value(loop_ty, dpath_refl_value(north))
  let c_south = set_trunc_point_value(
    ns_ty,
    susp_merid_path_value(a_ty, a0, level~),
  )
  let merid_center = DVLam(a => {
    let ma_pt = set_trunc_point_value(
      ns_ty,
      susp_merid_path_value(a_ty, a, level~),
    )
    let p_prefix : DValue = DVPathLam(i => {
      let pt_i = hit_cell_value(spec, 2, [a_ty], [a], [i])
      set_trunc_point_value(
        DVPathTy(_ => susp_ty, north, pt_i),
        DVPathLam(j => {
          hit_cell_value(spec, 2, [a_ty], [a], [dim_simplify(DAnd(i, j))])
        }),
      )
    })
    let eq_goal = DVPathTy(_ => st_ns_ty, ma_pt, c_south)
    let ma_eq_m0 = prop_trunc_elim_prop_value(
      DVPathTy(_ => a_ty, a0, a),
      _ => eq_goal,
      (_z, u, v) => {
        set_trunc_is_set_value(ns_ty, ma_pt, c_south, u, v, dlevel + 2)
      },
      pa => {
        DVPathLam(k => {
          set_trunc_point_value(
            ns_ty,
            susp_merid_path_value(a_ty, dapp_dim(pa, DNeg(k)), level~),
          )
        })
      },
      conn(a),
      dlevel + 2,
    )
    let m_line = memo_dim_line(i => {
      mot_center(hit_cell_value(spec, 2, [a_ty], [a], [i]))
    })
    let tr_eq = dpath_trans_value(
      st_ns_ty,
      dpath_of_pathp_value(m_line, p_prefix, dlevel + 2),
      ma_eq_m0,
      dlevel + 4,
    )
    dpathp_of_transport_eq_value(m_line, c_north, c_south, tr_eq, dlevel + 4)
  })

  let center_at = (z : DValue) => {
    eval_hit_elim(
      spec,
      (_, pt) => mot_center(pt),
      [c_north, c_south, merid_center],
      [a_ty],
      [],
      z,
      dlevel + 4,
    )
  }

  let retr_at_north = (w : DValue) => {
    let mot_w = (u : DValue) => DVPathTy(_ => st_loop_ty, c_north, u)
    set_trunc_elim_prop_value(
      loop_ty,
      mot_w,
      (u, q1, q2, dl) => {
        set_trunc_is_set_value(loop_ty, c_north, u, q1, q2, dl)
      },
      q => {
        dj_singleton_elim_value(
          (z1, q1) => {
            let p_ty = DVPathTy(_ => susp_ty, north, z1)
            let st_z1 = set_trunc_type_value(p_ty)
            DVPathTy(
              _ => st_z1,
              center_at(z1),
              set_trunc_point_value(p_ty, q1),
            )
          },
          dpath_refl_value(c_north),
          q,
          dlevel + 8,
        )
      },
      w,
      dlevel + 12,
    )
  }

  equiv_make_value(
    st_loop_ty,
    DVUnitTy,
    DVLam(_ => DVUnit),
    DVLam(_ => c_north),
    DVLam(_ => dpath_refl_value(DVUnit)),
    DVLam(w => retr_at_north(w)),
  )
}

///|
/// Instantiation 1 of General Freudenthal (`k = 0`) at `A = S^1`:
///   `Equiv ‖Ω¹(SuspS S^1, north)‖₀ Unit` (`π₁(S²) ≃ 1`).
pub fn pi1_susp_circle_equiv_unit_value(dlevel : Int32) -> DValue {
  freudenthal_pi1_susp_connected_equiv_unit_value(
    circle_hit_type_value(),
    circle_hit_base_value(),
    x => circle_0_connected_value(x, dlevel),
    dlevel + 2,
  )
}

///|
/// Instantiation 2 of General Freudenthal (`k = 0`) at `A = SuspS(S^1)` (`S^2`):
///   `Equiv ‖Ω¹(SuspS (SuspS S^1), north)‖₀ Unit` (`π₁(S³) ≃ 1`).
pub fn pi1_susp2_circle_equiv_unit_value(dlevel : Int32) -> DValue {
  let c_ty = circle_hit_type_value()
  let base = circle_hit_base_value()
  let s2_ty = susp_type_value(c_ty)
  let s2_north = susp_north_value(c_ty)
  freudenthal_pi1_susp_connected_equiv_unit_value(
    s2_ty,
    s2_north,
    z => susp_0_connected_of_pointed_value(c_ty, base, z, dlevel),
    dlevel + 2,
  )
}

// ---------------------------------------------------------------------------
// Wedge Connectivity Lemma (`m = n = 0`) on `S^1 ∨ S^1 -> S^1 × S^1` &
// Freudenthal Open-Loop Suspension Homomorphism
// ---------------------------------------------------------------------------

///|
/// Wedge Connectivity Extension Lemma (HoTT Lemma 8.6.2 at `m = n = 0`) on
/// `S^1 × S^1`: extends any dependent h-Set family `P : S^1 -> S^1 -> Type_0`
/// from the wedge `S^1 ∨ S^1` (`f_left : (x : S^1) -> P(x, base)`,
/// `f_right : (y : S^1) -> P(base, y)`, `glue_pt : Path (P(base, base)) (f_left base) (f_right base)`)
/// to all `(x, y : S^1) -> P(x, y)`.
/// On the right axis `x = base`, `ext(base, y)` reduces **definitionally** to
/// `f_right(y)`; on the left axis `y = base`, `wedge_connectivity_circle_left_coh_value`
/// witnesses `Path (P(x, base)) (ext(x, base)) (f_left x)`.
pub fn wedge_connectivity_circle_set_ext_value(
  p_fam : (DValue, DValue) -> DValue,
  is_set_p : (DValue, DValue, DValue, DValue, DValue, DValue) -> DValue,
  f_left : (DValue) -> DValue,
  f_right : (DValue) -> DValue,
  glue_pt : DValue,
  x : DValue,
  y : DValue,
  dlevel : Int32,
) -> DValue {
  let c_spec = circle_schema()
  match force_value(x) {
    DVHitCell(s, 0, _, _, _) if s == c_spec => return f_right(y)
    _ => ()
  }
  let c_ty = circle_hit_type_value()
  let base = circle_hit_base_value()
  let p00 = p_fam(base, base)

  let mot_x = (xv : DValue) => DVPi(c_ty, yv => p_fam(xv, yv))
  let base_fn = DVLam(yv => f_right(yv))
  let loop_x_line = memo_dim_line(i => {
    mot_x(hit_cell_value(c_spec, 1, [], [], [i]))
  })
  let tr_base_fn = transport_value(loop_x_line, base_fn, dlevel + 2)

  // At `y = base`, reconcile `(tr_base_fn)(base)` with `f_right(base)` via
  // `f_left(loop i)` and `glue_pt : f_left(base) = f_right(base)`.
  let line_x_at_base = memo_dim_line(i => {
    p_fam(hit_cell_value(c_spec, 1, [], [], [i]), base)
  })
  let fl_loop : DValue = DVPathLam(i => {
    f_left(hit_cell_value(c_spec, 1, [], [], [i]))
  })
  let fl_tr_eq = dpath_of_pathp_value(line_x_at_base, fl_loop, dlevel + 4)
  // Note `(tr_base_fn)(base)` transports `f_right(coe_{1->0} base)` along `line_x_at_base`:
  let coe_base = dpath_cong_value(
    DVLam(yv => f_right(yv)),
    c_ty,
    transport_pathp_value(_ => c_ty, base, dlevel + 4),
  )
  let tr_glue = dpath_cong_value(
    DVLam(v => transport_value(line_x_at_base, v, dlevel + 12)),
    p00,
    dpath_trans_value(p00, dpath_sym_value(coe_base), dpath_sym_value(glue_pt), dlevel + 8),
  )
  let base_y_eq = dpath_trans_value(
    p00,
    tr_glue,
    dpath_trans_value(p00, fl_tr_eq, glue_pt, dlevel + 10),
    dlevel + 16,
  )

  let mot_y = (yv : DValue) => {
    DVPathTy(_ => p_fam(base, yv), dapp_typed(tr_base_fn, yv, c_ty), f_right(yv))
  }
  let loop_y_line = memo_dim_line(j => {
    mot_y(hit_cell_value(c_spec, 1, [], [], [j]))
  })
  let tr_y = transport_value(loop_y_line, base_y_eq, dlevel + 20)
  let set_eq_y = is_set_p(
    base,
    base,
    dapp_typed(tr_base_fn, base, c_ty),
    f_right(base),
    tr_y,
    base_y_eq,
  )
  let loop_y_case = dpathp_of_transport_eq_value(
    loop_y_line,
    base_y_eq,
    base_y_eq,
    set_eq_y,
    dlevel + 28,
  )
  let pw_y = DVLam(yv => {
    eval_hit_elim(
      c_spec,
      (_, pt) => mot_y(pt),
      [base_y_eq, loop_y_case],
      [],
      [],
      yv,
      dlevel + 32,
    )
  })
  let loop_x_case = dpathp_of_transport_eq_value(
    loop_x_line,
    base_fn,
    base_fn,
    dpath_funext_value(pw_y, c_ty),
    dlevel + 36,
  )
  let fn_at_x = eval_hit_elim(
    c_spec,
    (_, pt) => mot_x(pt),
    [base_fn, loop_x_case],
    [],
    [],
    x,
    dlevel + 40,
  )
  dapp_typed(fn_at_x, y, c_ty)
}

///|
/// Right-axis computation path `Path (P(base, y)) (ext(base, y)) (f_right y)`
/// (definitionally `refl` for all open `y : S^1`).
pub fn wedge_connectivity_circle_right_coh_value(
  f_right : (DValue) -> DValue,
  y : DValue,
) -> DValue {
  dpath_refl_value(f_right(y))
}

///|
/// Left-axis computation path `(x : S^1) -> Path (P(x, base)) (ext(x, base)) (f_left x)`.
pub fn wedge_connectivity_circle_left_coh_value(
  p_fam : (DValue, DValue) -> DValue,
  is_set_p : (DValue, DValue, DValue, DValue, DValue, DValue) -> DValue,
  f_left : (DValue) -> DValue,
  f_right : (DValue) -> DValue,
  glue_pt : DValue,
  x : DValue,
  dlevel : Int32,
) -> DValue {
  let c_spec = circle_schema()
  let base = circle_hit_base_value()
  let ext_x = (xv : DValue) => {
    wedge_connectivity_circle_set_ext_value(
      p_fam, is_set_p, f_left, f_right, glue_pt, xv, base, dlevel,
    )
  }
  let mot = (xv : DValue) => DVPathTy(_ => p_fam(xv, base), ext_x(xv), f_left(xv))
  let base_case = dpath_sym_value(glue_pt)
  let loop_line = memo_dim_line(i => {
    mot(hit_cell_value(c_spec, 1, [], [], [i]))
  })
  let tr_base = transport_value(loop_line, base_case, dlevel + 46)
  let set_eq = is_set_p(
    base,
    base,
    f_right(base),
    f_left(base),
    tr_base,
    base_case,
  )
  let loop_case = dpathp_of_transport_eq_value(
    loop_line,
    base_case,
    base_case,
    set_eq,
    dlevel + 54,
  )
  eval_hit_elim(
    c_spec,
    (_, pt) => mot(pt),
    [base_case, loop_case],
    [],
    [],
    x,
    dlevel + 58,
  )
}

///|
/// General Freudenthal 1-loop suspension map
///   `σ₁ : Ω¹(A, a0) -> Ω²(SuspS A, north)`
/// defined uniformly on arbitrary (closed or open/neutral) 1-loops `p : Path A a0 a0`:
/// caps the meridian loop square `t ↦ merid(p t) ⬝ sym(merid a0)` on `t = 0`
/// and `t = 1` with `dpath_trans_sym_cancel_value` (using CCHM reflection
/// `p(0) ≡ a0` and `p(1) ≡ a0`).
pub fn freudenthal_susp_loop1_to_loop2_value(
  a_ty : DValue,
  a0 : DValue,
  p : DValue,
  dlevel : Int32,
  level~ : Int32 = 0,
) -> DValue {
  let susp_ty = susp_type_value(a_ty, level~)
  let north = susp_north_value(a_ty, level~)
  let loop1_ty = DVPathTy(_ => susp_ty, north, north)
  let m0 = susp_merid_path_value(a_ty, a0, level~)
  let canc = dpath_trans_sym_cancel_value(susp_ty, m0, north, dlevel)
  DVPathLam(t => {
    let pt = dapp_dim(p, t)
    let unit_t = dpath_trans_value(
      susp_ty,
      susp_merid_path_value(a_ty, pt, level~),
      dpath_sym_value(m0),
      dlevel,
    )
    let sys = dsystem_of([
      tube_branch(face_simplify(FEq0(t)), j => dapp_dim(canc, j)),
      tube_branch(face_simplify(FEq1(t)), j => dapp_dim(canc, j)),
    ])
    hcomp_value(loop1_ty, sys, unit_t, dlevel + 4)
  })
}

///|
/// Internal Freudenthal homomorphism identity coherence `Path (Ω²(SuspS A, north))
/// (freudenthal_susp_loop1_to_loop2_value A a0 (refl a0)) (refl (refl north))`:
/// slides the constant cap `unit(a0)` along `canc(j ∨ s)` so all boundaries stay
/// fixed at `refl_north`.
pub fn freudenthal_susp_loop1_preserves_refl_value(
  a_ty : DValue,
  a0 : DValue,
  dlevel : Int32,
  level~ : Int32 = 0,
) -> DValue {
  let susp_ty = susp_type_value(a_ty, level~)
  let north = susp_north_value(a_ty, level~)
  let loop1_ty = DVPathTy(_ => susp_ty, north, north)
  let m0 = susp_merid_path_value(a_ty, a0, level~)
  let canc = dpath_trans_sym_cancel_value(susp_ty, m0, north, dlevel)
  DVPathLam(s => {
    DVPathLam(t => {
      let sys = dsystem_of([
        tube_branch(face_simplify(FEq0(t)), j => {
          dapp_dim(canc, dim_simplify(DOr(j, s)))
        }),
        tube_branch(face_simplify(FEq1(t)), j => {
          dapp_dim(canc, dim_simplify(DOr(j, s)))
        }),
        tube_branch(face_simplify(FEq1(s)), _ => dpath_refl_value(north)),
      ])
      hcomp_value(loop1_ty, sys, dapp_dim(canc, s), dlevel + 4)
    })
  })
}

// ---------------------------------------------------------------------------
// Phase 16 (Track 5): Hopf Fiber-Sequence Loop Classification, Open-Variable
// Hopf-Freudenthal Retraction `∂_Hopf(σ_{S^2}(p)) = p`, and Split-Retract
// Certification of `ℤ` inside `π_2(S^2) = ‖Ω^2(S^2, north)‖_0`
// ---------------------------------------------------------------------------

///|
/// Schema `S^2` HIT type value (`sphere2_schema()`).
pub fn sphere2_type_value() -> DValue {
  DVHitType(sphere2_schema(), [], [])
}

///|
/// Meridian path `merid(x) : Path S^2 north south` on `sphere2_schema()`.
pub fn sphere2_meridian_path_value(x : DValue) -> DValue {
  let spec = sphere2_schema()
  DVPathLam(i => hit_cell_value(spec, 2, [], [x], [i]))
}

///|
/// Total space `E_Hopf = Σ (x : S^2), Hopf(x)` of Brunerie's Hopf fibration
/// (`S^1 -> E_Hopf -> S^2`, homotopically `S^3`).
pub fn hopf_total_space_type_value(dlevel~ : Int32 = 16) -> DValue {
  DVSigma(sphere2_type_value(), pt => hopf_family_value(pt, dlevel~))
}

///|
/// First-class bidirectional Hopf fiber-sequence loop space equivalence
///   `Equiv (Ω¹(E_Hopf, (north, base))) (Σ (p : Ω¹(S^2, north)), Path S^1 (subst Hopf p base) base)`.
pub fn hopf_total_loop_equiv_fiber_seq_value(dlevel~ : Int32 = 16) -> DValue {
  fibration_loop_equiv_fiber_path_value(
    sphere2_type_value(),
    pt => hopf_family_value(pt, dlevel~),
    sphere2_north_value(),
    circle_hit_base_value(),
    dlevel + 6,
  )
}

///|
/// Open-variable circle elimination proving `fwd(circle_rot_equiv(x))(base) = x`
/// for arbitrary (closed or neutral) `x : S^1`.
pub fn circle_rot_eval_base_eq_value(x : DValue, dlevel : Int32) -> DValue {
  let c_spec = circle_schema()
  let s1 = circle_hit_type_value()
  let base = circle_hit_base_value()
  eval_hit_elim(
    c_spec,
    (_idx, pt) => {
      DVPathTy(
        _ => s1,
        equiv_fun_value(circle_rot_equiv_value(pt, dlevel), s1, s1, base),
        pt,
      )
    },
    [
      dpath_refl_value(base),
      DVPathLam(i => dpath_refl_value(hit_cell_value(c_spec, 1, [], [], [i]))),
    ],
    [],
    [],
    x,
    dlevel,
  )
}

///|
/// Freudenthal suspension map `σ_{S^2} : Ω¹(S^1, base) -> Ω²(S^2, north)` on
/// `sphere2_schema()`, defined uniformly on arbitrary open/neutral loops `p`.
pub fn sphere2_susp_loop1_to_loop2_value(
  p : DValue,
  dlevel~ : Int32 = 16,
) -> DValue {
  let s2 = sphere2_type_value()
  let north = sphere2_north_value()
  let base_s1 = circle_hit_base_value()
  let loop1_ty = DVPathTy(_ => s2, north, north)
  let m0 = sphere2_meridian_path_value(base_s1)
  let canc = dpath_trans_sym_cancel_value(s2, m0, north, dlevel)
  DVPathLam(t => {
    let pt = dapp_dim(p, t)
    let unit_t = dpath_trans_value(
      s2,
      sphere2_meridian_path_value(pt),
      dpath_sym_value(m0),
      dlevel,
    )
    let sys = dsystem_of([
      tube_branch(face_simplify(FEq0(t)), j => dapp_dim(canc, j)),
      tube_branch(face_simplify(FEq1(t)), j => dapp_dim(canc, j)),
    ])
    hcomp_value(loop1_ty, sys, unit_t, dlevel + 4)
  })
}

///|
/// Open-variable computation of Hopf meridian-loop transport:
/// for arbitrary `x : S^1`, constructs
///   `Path S^1 (subst Hopf (merid(x) ⬝ sym(merid(base))) base) x`
/// by chaining `subst_trans_eq_value`, `ua_beta_path_value` on
/// `circle_rot_equiv(x)`, `circle_rot_eval_base_eq_value(x)`, and
/// `ua_beta_back_path_value` on `equiv_id(S^1)`.
pub fn hopf_unit_subst_eq_value(
  x : DValue,
  dlevel~ : Int32 = 16,
) -> DValue {
  let s1 = circle_hit_type_value()
  let base = circle_hit_base_value()
  let s2 = sphere2_type_value()
  let hopf_fam = (pt : DValue) => hopf_family_value(pt, dlevel~)
  let mx = sphere2_meridian_path_value(x)
  let m0_inv = dpath_sym_value(sphere2_meridian_path_value(base))
  let step_split = subst_trans_eq_value(
    hopf_fam,
    s2,
    mx,
    m0_inv,
    base,
    dlevel + 6,
  )
  let rot_x = circle_rot_equiv_value(x, dlevel)
  let ua_fwd = dpath_sym_value(
    ua_beta_path_value(rot_x, s1, s1, 0, base, dlevel + 5),
  )
  let eval_x = circle_rot_eval_base_eq_value(x, dlevel)
  let mx_to_x = dpath_trans_value(s1, ua_fwd, eval_x, dlevel + 6)
  let step_mid : DValue = DVPathLam(
    memo_dim_line(k => {
      subst_value(hopf_fam, m0_inv, dapp_dim(mx_to_x, k), dlevel + 6)
    }),
  )
  let ua_bwd = dpath_sym_value(
    ua_beta_back_path_value(equiv_id_value(s1), s1, s1, 0, x, dlevel + 5),
  )
  dpath_trans_value(
    s1,
    dpath_trans_value(s1, step_split, step_mid, dlevel + 8),
    ua_bwd,
    dlevel + 8,
  )
}

///|
/// Open-variable Hopf–Freudenthal retraction theorem:
/// for arbitrary (closed or neutral) `p : Ω¹(S^1, base)`, constructs a
/// pointed 2-path
///   `Path (Ω¹(S^1, base)) (hopf_connecting_loop (sphere2_susp_loop1_to_loop2 p)) p`
/// purely inside the cubical kernel.
pub fn hopf_freudenthal_retraction_value(
  p : DValue,
  dlevel~ : Int32 = 16,
) -> DValue {
  let s1 = circle_hit_type_value()
  let base = circle_hit_base_value()
  let s2 = sphere2_type_value()
  let north = sphere2_north_value()
  let loop1_s2_ty = DVPathTy(_ => s2, north, north)
  let hopf_fam = (pt : DValue) => hopf_family_value(pt, dlevel~)
  let m0 = sphere2_meridian_path_value(base)
  let m0_sym = dpath_sym_value(m0)
  let canc = dpath_trans_sym_cancel_value(s2, m0, north, dlevel)
  let lhs_loop = hopf_connecting_loop_value(
    sphere2_susp_loop1_to_loop2_value(p, dlevel~),
    dlevel~,
  )
  let psi_at = memo_dim_line(t => {
    let pt = dapp_dim(p, t)
    let unit_t = dpath_trans_value(
      s2,
      sphere2_meridian_path_value(pt),
      m0_sym,
      dlevel,
    )
    let sys = dsystem_of([
      tube_branch(face_simplify(FEq0(t)), j => dapp_dim(canc, j)),
      tube_branch(face_simplify(FEq1(t)), j => dapp_dim(canc, j)),
    ])
    let cap_fill = fill_value(_ => loop1_s2_ty, sys, unit_t, dlevel + 4)
    let uncap : DValue = DVPathLam(
      memo_dim_line(s => {
        subst_value(hopf_fam, cap_fill(DNeg(s)), base, dlevel + 6)
      }),
    )
    let unit_eq = hopf_unit_subst_eq_value(pt, dlevel~)
    dpath_trans_value(s1, uncap, unit_eq, dlevel + 8)
  })
  let theta0 = psi_at(DZero)
  // `theta0 : Ω¹(S^1, base)` is closed and never traverses `loop`, so its
  // helix winding is definitionally `0` (`circle_decode(0) ≡ refl_base`).
  let lid0 = dpath_sym_value(circle_decode_encode_retr_value(theta0, dlevel + 10))
  let lid0_at = memo_dim_line(k => dapp_dim(lid0, k))
  DVPathLam(
    memo_dim_line(r => {
      DVPathLam(
        memo_dim_line(t => {
          let mid = psi_at(t)
          let sys = dsystem_of([
            tube_branch(face_simplify(FEq0(r)), _ => dapp_dim(lhs_loop, t)),
            tube_branch(face_simplify(FEq1(r)), _ => dapp_dim(p, t)),
            tube_branch(face_simplify(FEq0(t)), k => dapp_dim(lid0_at(k), r)),
            tube_branch(face_simplify(FEq1(t)), k => dapp_dim(lid0_at(k), r)),
          ])
          hcomp_value(s1, sys, dapp_dim(mid, r), dlevel + 14)
        }),
      )
    }),
  )
}

///|
/// Open-variable integer retraction witness
///   `Path IntegerS (hopf_invariant (sphere2_susp_loop1_to_loop2 (circle_decode z))) z`
/// valid for arbitrary neutral `z : IntegerS`.
pub fn hopf_invariant_susp_retraction_value(
  z : DValue,
  dlevel~ : Int32 = 16,
) -> DValue {
  let z_ty = integer_type_value()
  let loop_s1_ty = circle_loop_space_type_value()
  let dec_z = circle_decode_value(z, dlevel)
  let retr_p = hopf_freudenthal_retraction_value(dec_z, dlevel~)
  let step1 = dpath_cong_value(
    DVLam(q => circle_encode_value(q, dlevel + 10)),
    loop_s1_ty,
    retr_p,
  )
  let step2 = circle_encode_decode_sect_value(z, dlevel + 10)
  dpath_trans_value(z_ty, step1, step2, dlevel + 12)
}

///|
/// 0-truncated second homotopy group `π_2(S^2) = ‖Ω²(S^2, north)‖_0`.
pub fn pi2_s2_type_value() -> DValue {
  set_trunc_type_value(
    loop_space_type_value(sphere2_type_value(), sphere2_north_value(), 2),
  )
}

///|
/// 0-truncated Hopf invariant homomorphism `π_2(S^2) -> IntegerS`, induced on
/// `‖Ω²(S^2, north)‖_0` via `set_trunc_rec_value` and `integer_is_set_value`.
pub fn pi2_s2_hopf_hom_value(
  elem : DValue,
  dlevel~ : Int32 = 16,
) -> DValue {
  let omega2_ty = loop_space_type_value(
    sphere2_type_value(),
    sphere2_north_value(),
    2,
  )
  set_trunc_rec_set_value(
    omega2_ty,
    integer_type_value(),
    (a, b, p1, p2) => integer_is_set_value(a, b, p1, p2, dlevel + 12),
    alpha => hopf_invariant_value(alpha, dlevel~),
    elem,
    dlevel + 14,
  )
}

///|
/// Canonical Freudenthal generator map `IntegerS -> π_2(S^2)` sending `z` to
/// `|σ_{S^2}(circle_decode(z))|_0`.
pub fn integer_to_pi2_s2_value(
  z : DValue,
  dlevel~ : Int32 = 16,
) -> DValue {
  let omega2_ty = loop_space_type_value(
    sphere2_type_value(),
    sphere2_north_value(),
    2,
  )
  set_trunc_point_value(
    omega2_ty,
    sphere2_susp_loop1_to_loop2_value(circle_decode_value(z, dlevel), dlevel~),
  )
}

///|
/// Open-variable split-retract section certificate for `π_2(S^2)`:
/// for arbitrary `z : IntegerS`, `pi2_s2_hopf_hom(integer_to_pi2_s2(z))`
/// computes definitionally on `|·|_0` to `hopf_invariant(σ_{S^2}(decode z))`,
/// so `hopf_invariant_susp_retraction_value(z)` directly inhabits
///   `Path IntegerS (pi2_s2_hopf_hom (integer_to_pi2_s2 z)) z`,
/// certifying `IntegerS` as a split retract of `π_2(S^2)`.
pub fn pi2_s2_hopf_retract_sect_value(
  z : DValue,
  dlevel~ : Int32 = 16,
) -> DValue {
  hopf_invariant_susp_retraction_value(z, dlevel~)
}



