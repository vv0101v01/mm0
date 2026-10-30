///|
// Spheres by iterated suspension.
//
// For an unindexed HIT `X`, its suspension is the HIT with two point
// constructors `north` and `south` and, for every `x : X`, a meridian
// path from north to south.  Iterating this construction from the
// generated circle gives
//
//   S^2 = Susp(S^1),     S^3 = Susp(S^2) = Susp(Susp(S^1)).
//
// The schema generator therefore supplies formation, typed checking,
// dependent elimination, conversion, quoting and Kan composition for
// S^3 from the same generic HIT machinery as Circle and Torus.

///|
fn suspension_parameter_terms(count : Int32) -> Array[DTerm] {
  let out : Array[DTerm] = []
  for i in 0..<count {
    // Telescope arrays are in declaration order, while de Bruijn
    // index 0 denotes the last parameter.
    out.push(DTVar(count - 1 - i))
  }
  out
}

///|
fn suspension_schema_unchecked(name : String, base : DHitSpec) -> DHitSpec {
  dhit_spec(name, base.level, base.params, [], [
    dhit_cell_spec("north", 0, [], []),
    dhit_cell_spec("south", 0, [], []),
    dhit_cell_spec(
      "meridian",
      1,
      [
        darg_external(
          "point",
          DHitType(base, suspension_parameter_terms(base.params.length())),
        ),
      ],
      [dhit_face(0, [], []), dhit_face(1, [], [])],
    ),
  ])
}

///|
/// Checked suspension of an unindexed HIT schema.  Parameters of the
/// base HIT are inherited.  Indexed base HITs are rejected because a
/// constructor argument cannot refer to the result indices in this
/// schema language.
pub fn suspension_schema(name : String, base : DHitSpec) -> DHitSpec? {
  if name.length() == 0 ||
    base.indices.length() != 0 ||
    !hit_schema_validate(base) {
    return None
  }
  let out = suspension_schema_unchecked(name, base)
  if hit_schema_validate(out) {
    Some(out)
  } else {
    None
  }
}

///|
/// The generated 2-sphere, presented as the suspension of S^1.
pub fn sphere2_schema() -> DHitSpec {
  suspension_schema_unchecked("Sphere2S", circle_schema())
}

///|
/// The generated 3-sphere, presented as the suspension of S^2.
pub fn sphere3_schema() -> DHitSpec {
  suspension_schema_unchecked("Sphere3S", sphere2_schema())
}

///|
/// Spheres by iterated suspension.  Dimension 1 is the generated
/// circle; non-positive dimensions also return the circle as the
/// total function's base case.
pub fn sphere_schema(dim : Int32) -> DHitSpec {
  if dim <= 1 {
    circle_schema()
  } else {
    suspension_schema_unchecked("Sphere\{dim}S", sphere_schema(dim - 1))
  }
}

///|
pub fn sphere3_type_term() -> DTerm {
  DHitType(sphere3_schema(), [])
}

///|
pub fn sphere3_type_value() -> DValue {
  DVHitType(sphere3_schema(), [], [])
}

///|
pub fn sphere3_north_term() -> DTerm {
  hit_intro_term(sphere3_schema(), 0, [], [], [])
}

///|
pub fn sphere3_south_term() -> DTerm {
  hit_intro_term(sphere3_schema(), 1, [], [], [])
}

///|
pub fn sphere3_north_value() -> DValue {
  DVHitCell(sphere3_schema(), 0, [], [], [])
}

///|
pub fn sphere3_south_value() -> DValue {
  DVHitCell(sphere3_schema(), 1, [], [], [])
}

///|
/// A point on the meridian over `point : S^2`; at dimension 0 it is
/// north and at dimension 1 it is south.
pub fn sphere3_meridian_term(point : DTerm, dim : Dim) -> DTerm {
  hit_intro_term(sphere3_schema(), 2, [], [point], [dim])
}

///|
/// The semantic meridian point, with endpoint faces reduced by the
/// generic HIT cell smart constructor.
pub fn sphere3_meridian_value(point : DValue, dim : Dim) -> DValue {
  hit_cell_value(sphere3_schema(), 2, [], [point], [dim])
}

///|
pub fn sphere2_north_term() -> DTerm {
  hit_intro_term(sphere2_schema(), 0, [], [], [])
}

///|
pub fn sphere2_north_value() -> DValue {
  DVHitCell(sphere2_schema(), 0, [], [], [])
}

///|
pub fn check_sphere3() -> Bool {
  let s2 = sphere2_schema()
  let s3 = sphere3_schema()
  if !hit_schema_validate(s2) || !hit_schema_validate(s3) {
    return false
  }
  if sphere_schema(3) != s3 {
    return false
  }
  let ty = sphere3_type_term()
  let north = sphere3_north_term()
  let south = sphere3_south_term()
  let point2 = sphere2_north_term()
  if dep_check_closed(point2, DHitType(s2, [])) == false {
    return false
  }
  if dep_nf_closed(sphere3_meridian_term(point2, DZero), ty) != Some(north) ||
    dep_nf_closed(sphere3_meridian_term(point2, DOne), ty) != Some(south) {
    return false
  }
  let tyv = sphere3_type_value()
  let north_v = sphere3_north_value()
  let south_v = sphere3_south_value()
  let point2_v = sphere2_north_value()
  if conv_at(0, 0, tyv, north_v, south_v) {
    return false
  }
  if !conv_at(0, 0, tyv, sphere3_meridian_value(point2_v, DZero), north_v) ||
    !conv_at(0, 0, tyv, sphere3_meridian_value(point2_v, DOne), south_v) {
    return false
  }
  // Dependent elimination into a constant motive computes on every
  // generating cell, including a meridian at a generic dimension.
  let meridian : DValue = DVHitCell(s3, 2, [], [point2_v], [DVar(0)])
  let const_elim = eval_hit_elim(
    s3,
    (_, _) => DVBoolTy,
    [DVBool(true), DVBool(true), DVLam(_ => DVPathLam(_ => DVBool(true)))],
    [],
    [],
    meridian,
    1,
  )
  if !dv_is_bool_dep(const_elim, true) {
    return false
  }
  // The identity eliminator: north and south are fixed and every
  // meridian is sent to itself.
  let identity = eval_hit_elim(
    s3,
    (_, _) => tyv,
    [north_v, south_v, DVLam(x => DVPathLam(d => sphere3_meridian_value(x, d)))],
    [],
    [],
    meridian,
    1,
  )
  if !conv_at(0, 1, tyv, identity, meridian) {
    return false
  }
  // A constant meridian system composes to the same meridian point.
  let composed = hcomp_value(
    tyv,
    dsystem_singleton(FEq0(DVar(1)), _ => meridian),
    meridian,
    2,
  )
  conv_at(0, 2, tyv, composed, meridian)
}
