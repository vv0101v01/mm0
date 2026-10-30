///|
fn check_checked_lines() -> Bool {
  let invalid = match checked_type_line_closed(DBoolLit(true)) {
    Some(_) => false
    None => true
  }
  let constant_ok = match checked_constant_type_line_closed(DBoolTy) {
    Some(line) => {
      let (a, b) = checked_line_endpoints(line)
      checked_line_is_constant(line) &&
      conv_ty(0, 0, a, DVBoolTy) &&
      conv_ty(0, 0, b, DVBoolTy) &&
      cubical_bool_is(
        checked_coe_value(line, DZero, DOne, DVBool(true), 0),
        true,
      )
    }
    None => false
  }
  let ua_ok = match
    checked_ua_line(
      bool_not_equiv_term(),
      denv_empty(),
      denv_empty(),
      ddim_empty(),
    ) {
    Some(line) => {
      let (a, b) = checked_line_endpoints(line)
      conv_ty(0, 0, a, DVBoolTy) &&
      conv_ty(0, 0, b, DVBoolTy) &&
      cubical_bool_is(
        checked_coe_value(line, DZero, DOne, DVBool(true), 0),
        false,
      ) &&
      cubical_bool_is(
        checked_coe_value(line, DOne, DZero, DVBool(true), 0),
        false,
      ) &&
      checked_line_quote_body(0, 0, line) ==
      quote_ty(0, 1, checked_line_at(line, DVar(0)))
    }
    None => false
  }
  let reify_ok = match
    d_infer(bool_not_equiv_term(), denv_empty(), denv_empty(), ddim_empty()) {
    Some(ev) =>
      match
        checked_line_reify_closed(
          ua_line_value(ev.value, DVBoolTy, DVBoolTy, 0),
        ) {
        Some(line) =>
          cubical_bool_is(
            checked_coe_value(line, DZero, DOne, DVBool(true), 0),
            false,
          )
        None => false
      }
    None => false
  }
  // A host line which inspects whether its dimension is a variable
  // is not a substitutable type line and is rejected by reification.
  let non_natural = (d : Dim) => {
    match d {
      DVar(_) => DVBoolTy
      _ => DVUnitTy
    }
  }
  let rejected = match checked_line_reify_closed(non_natural) {
    Some(_) => false
    None => true
  }
  invalid && constant_ok && ua_ok && reify_ok && rejected
}

///|
fn check_schema_registry() -> Bool {
  let registry = schema_registry_new()
  let spec = vec_schema()
  let first = schema_registry_register_inductive(registry, spec)
  let second = schema_registry_register_inductive(registry, vec_schema())
  let hit = schema_registry_register_hit(registry, circle_schema())
  let by_name = match schema_registry_inductive_by_name(registry, spec.name) {
    Some(plan) => plan.id == first.id
    None => false
  }
  let by_id = match schema_registry_hit_by_id(registry, hit.id) {
    Some(plan) => plan.spec == circle_schema()
    None => false
  }
  let params = inductive_param_types_cached(registry, spec, [DVBoolTy])
  let params2 = inductive_param_types_cached(registry, spec, [DVBoolTy])
  let indices = inductive_index_types_cached(registry, spec, [DVBoolTy], [
    DVZeroNat,
  ])
  let telescope = [
    dtelescope_entry("A", DUniv(0)),
    dtelescope_entry("x", DTVar(0)),
  ]
  let types = telescope_type_values_cached(registry, telescope, [], [], [
    DVBoolTy,
    DVBool(true),
  ])
  let types2 = telescope_type_values_cached(registry, telescope, [], [], [
    DVBoolTy,
    DVBool(true),
  ])
  first.valid &&
  second.id == first.id &&
  hit.valid &&
  by_name &&
  by_id &&
  registry.validation_misses == 2 &&
  registry.validation_hits == 1 &&
  registry.telescope_hits >= 2 &&
  registry.telescope_misses >= 2 &&
  params.length() == 1 &&
  conv_ty(0, 0, params[0], DVUniv(0)) &&
  conv_ty(0, 0, params2[0], DVUniv(0)) &&
  indices.length() == 1 &&
  conv_ty(0, 0, indices[0], DVNatTy) &&
  types.length() == 2 &&
  conv_ty(0, 0, types[1], DVBoolTy) &&
  conv_ty(0, 0, types2[1], DVBoolTy) &&
  inductive_plan_type_term(first, [DBoolTy, DNatZero]) ==
  DInductive(spec, [DBoolTy, DNatZero])
}

///|
pub fn check_phase6_infrastructure() -> Bool {
  check_checked_lines() &&
  check_schema_registry() &&
  check_semantic_dimension_substitution() &&
  check_schema_registry_persistence()
}

///|
pub fn check_schema_registry_persistence() -> Bool {
  let registry = schema_registry_new()
  let plans = schema_registry_register_inductives(registry, [
    nat_schema(),
    list_schema(),
    nat_schema(),
  ])
  // Hash-consing: the duplicate descriptor returns the interned plan.
  if plans.length() != 3 || plans[0].id != plans[2].id {
    return false
  }
  ignore(schema_registry_register_hit(registry, circle_schema()))
  let (ni, nh, _, hits1, misses1, _, _) = schema_registry_stats(registry)
  if ni != 2 || nh != 1 || misses1 != 3 || hits1 != 1 {
    return false
  }
  // Snapshot/restore preserves plans and validity without
  // revalidation (restored misses stay at zero).
  let restored = schema_registry_restore(schema_registry_snapshot(registry))
  let (ri, rh, _, rhits, rmisses, _, _) = schema_registry_stats(restored)
  if ri != 2 || rh != 1 || rmisses != 0 || rhits != 3 {
    return false
  }
  match schema_registry_inductive_plan(restored, list_schema()) {
    Some(plan) => if !plan.valid { return false }
    None => return false
  }
  // Incremental merge adds only the missing descriptors.
  let other = schema_registry_new()
  ignore(
    schema_registry_register_inductives(other, [list_schema(), vec_schema()]),
  )
  if schema_registry_merge_into(restored, other) != 1 {
    return false
  }
  let (mi, _, _, _, mmisses, _, _) = schema_registry_stats(restored)
  mi == 3 &&
  mmisses == 0 &&
  schema_registry_manifest(restored).length() > 0 &&
  schema_registry_manifest(registry) != schema_registry_manifest(restored)
}
