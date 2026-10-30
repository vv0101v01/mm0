///|
// Schema registration, validation caching, and telescope-elaboration
// caching.
//
// A registry interns inductive and HIT descriptors as *plans*: the
// descriptor is validated once, its parameter/index telescopes are
// elaborated once at generic values, and later registrations of a
// structurally equal descriptor return the existing plan.  Concrete
// telescope elaborations are cached semantically: a cached request
// is reused when prefix types, prefix values, and telescope values
// are convertible stepwise, so no telescope type is recomputed on a
// hit.  The public `inductive_schema_validate` /
// `hit_schema_validate` entry points go through a shared default
// registry, which removes the repeated validation that AST
// evaluation/inference would otherwise perform for every embedded
// descriptor occurrence.

///|
pub struct DInductivePlan {
  id : Int32
  key : String
  spec : DInductiveSpec
  valid : Bool
  generic_param_types : Array[DValue]
  generic_index_types : Array[DValue]
}

///|
pub struct DHitPlan {
  id : Int32
  key : String
  spec : DHitSpec
  valid : Bool
  generic_param_types : Array[DValue]
  generic_index_types : Array[DValue]
}

///|
pub struct DTelescopeCacheEntry {
  entries : Array[DTelescopeEntry]
  prefix_types : Array[DValue]
  prefix_values : Array[DValue]
  values : Array[DValue]
  types : Array[DValue]
}

///|
pub struct DSchemaRegistry {
  inductives : Array[DInductivePlan]
  hits : Array[DHitPlan]
  inductive_buckets : Array[Array[Int32]]
  hit_buckets : Array[Array[Int32]]
  telescopes : Array[DTelescopeCacheEntry]
  mut validation_hits : Int32
  mut validation_misses : Int32
  mut telescope_hits : Int32
  mut telescope_misses : Int32
}

///|
fn registry_empty_buckets() -> Array[Array[Int32]] {
  let buckets : Array[Array[Int32]] = []
  for _i in 0..<64 {
    buckets.push([])
  }
  buckets
}

///|
fn registry_string_hash(key : String) -> Int32 {
  let mut h = 7U
  for i in 0..<key.length() {
    h = (h * 31U + key[i].to_int().reinterpret_as_uint()) % 1000003U
  }
  h.reinterpret_as_int()
}

///|
pub fn schema_registry_new() -> DSchemaRegistry {
  DSchemaRegistry::{
    inductives: [],
    hits: [],
    inductive_buckets: registry_empty_buckets(),
    hit_buckets: registry_empty_buckets(),
    telescopes: [],
    validation_hits: 0,
    validation_misses: 0,
    telescope_hits: 0,
    telescope_misses: 0,
  }
}

///|
/// The shared registry used by the descriptor-embedding AST forms.
pub let default_schema_registry : DSchemaRegistry = schema_registry_new()

///|
pub fn inductive_schema_key(spec : DInductiveSpec) -> String {
  Repr(spec).to_string()
}

///|
pub fn hit_schema_key(spec : DHitSpec) -> String {
  Repr(spec).to_string()
}

///|
fn copy_values(values : Array[DValue]) -> Array[DValue] {
  schema_concat_values([], values)
}

///|
pub fn schema_registry_register_inductive(
  registry : DSchemaRegistry,
  spec : DInductiveSpec,
) -> DInductivePlan {
  match schema_registry_inductive_plan(registry, spec) {
    Some(plan) => {
      registry.validation_hits = registry.validation_hits + 1
      plan
    }
    None => {
      registry.validation_misses = registry.validation_misses + 1
      registry_add_inductive_plan(
        registry,
        spec,
        inductive_schema_validate_uncached(spec),
      )
    }
  }
}

///|
/// The generic (fresh-variable) parameter and index telescope
/// types shared by inductive and HIT registry plans; both are
/// empty when the schema failed validation.
fn registry_generic_telescope_types(
  params : Array[DTelescopeEntry],
  indices : Array[DTelescopeEntry],
  valid : Bool,
) -> (Array[DValue], Array[DValue]) {
  let pv = schema_fresh_values(params.length(), 8200)
  let param_types = if valid {
    telescope_type_values(params, [], [], pv)
  } else {
    []
  }
  let iv = schema_fresh_values(indices.length(), 8300)
  let index_types = if valid {
    telescope_type_values(indices, param_types, pv, iv)
  } else {
    []
  }
  (param_types, index_types)
}

///|
fn registry_add_inductive_plan(
  registry : DSchemaRegistry,
  spec : DInductiveSpec,
  valid : Bool,
) -> DInductivePlan {
  let (param_types, index_types) = registry_generic_telescope_types(
    spec.params,
    spec.indices,
    valid,
  )
  let key = inductive_schema_key(spec)
  let plan = DInductivePlan::{
    id: registry.inductives.length(),
    key,
    spec,
    valid,
    generic_param_types: param_types,
    generic_index_types: index_types,
  }
  registry.inductives.push(plan)
  let bucket = registry_string_hash(key) % registry.inductive_buckets.length()
  registry.inductive_buckets[bucket].push(plan.id)
  plan
}

///|
pub fn schema_registry_register_hit(
  registry : DSchemaRegistry,
  spec : DHitSpec,
) -> DHitPlan {
  match schema_registry_hit_plan(registry, spec) {
    Some(plan) => {
      registry.validation_hits = registry.validation_hits + 1
      plan
    }
    None => {
      registry.validation_misses = registry.validation_misses + 1
      registry_add_hit_plan(registry, spec, hit_schema_validate_uncached(spec))
    }
  }
}

///|
fn registry_add_hit_plan(
  registry : DSchemaRegistry,
  spec : DHitSpec,
  valid : Bool,
) -> DHitPlan {
  let (param_types, index_types) = registry_generic_telescope_types(
    spec.params,
    spec.indices,
    valid,
  )
  let key = hit_schema_key(spec)
  let plan = DHitPlan::{
    id: registry.hits.length(),
    key,
    spec,
    valid,
    generic_param_types: param_types,
    generic_index_types: index_types,
  }
  registry.hits.push(plan)
  let bucket = registry_string_hash(key) % registry.hit_buckets.length()
  registry.hit_buckets[bucket].push(plan.id)
  plan
}

///|
pub fn schema_registry_inductive_plan(
  registry : DSchemaRegistry,
  spec : DInductiveSpec,
) -> DInductivePlan? {
  let bucket = registry_string_hash(inductive_schema_key(spec)) %
    registry.inductive_buckets.length()
  let ids = registry.inductive_buckets[bucket]
  for k in 0..<ids.length() {
    let plan = registry.inductives[ids[k]]
    if plan.spec == spec {
      return Some(plan)
    }
  }
  None
}

///|
pub fn schema_registry_hit_plan(
  registry : DSchemaRegistry,
  spec : DHitSpec,
) -> DHitPlan? {
  let bucket = registry_string_hash(hit_schema_key(spec)) %
    registry.hit_buckets.length()
  let ids = registry.hit_buckets[bucket]
  for k in 0..<ids.length() {
    let plan = registry.hits[ids[k]]
    if plan.spec == spec {
      return Some(plan)
    }
  }
  None
}

///|
pub fn schema_registry_inductive_by_id(
  registry : DSchemaRegistry,
  id : Int32,
) -> DInductivePlan? {
  if id >= 0 && id < registry.inductives.length() {
    Some(registry.inductives[id])
  } else {
    None
  }
}

///|
pub fn schema_registry_hit_by_id(
  registry : DSchemaRegistry,
  id : Int32,
) -> DHitPlan? {
  if id >= 0 && id < registry.hits.length() {
    Some(registry.hits[id])
  } else {
    None
  }
}

///|
pub fn schema_registry_inductive_by_name(
  registry : DSchemaRegistry,
  name : String,
) -> DInductivePlan? {
  for i in 0..<registry.inductives.length() {
    if registry.inductives[i].spec.name == name {
      return Some(registry.inductives[i])
    }
  }
  None
}

///|
pub fn schema_registry_hit_by_name(
  registry : DSchemaRegistry,
  name : String,
) -> DHitPlan? {
  for i in 0..<registry.hits.length() {
    if registry.hits[i].spec.name == name {
      return Some(registry.hits[i])
    }
  }
  None
}

///|
pub fn schema_registry_validate_inductive(
  registry : DSchemaRegistry,
  spec : DInductiveSpec,
) -> Bool {
  schema_registry_register_inductive(registry, spec).valid
}

///|
pub fn schema_registry_validate_hit(
  registry : DSchemaRegistry,
  spec : DHitSpec,
) -> Bool {
  schema_registry_register_hit(registry, spec).valid
}

///|
/// Validate an inductive descriptor through the shared registry:
/// each structurally distinct descriptor is validated once.
pub fn inductive_schema_validate(spec : DInductiveSpec) -> Bool {
  schema_registry_validate_inductive(default_schema_registry, spec)
}

///|
pub fn hit_schema_validate(spec : DHitSpec) -> Bool {
  schema_registry_validate_hit(default_schema_registry, spec)
}

///|
pub fn schema_registry_stats(
  registry : DSchemaRegistry,
) -> (Int32, Int32, Int32, Int32, Int32, Int32, Int32) {
  (
    registry.inductives.length(),
    registry.hits.length(),
    registry.telescopes.length(),
    registry.validation_hits,
    registry.validation_misses,
    registry.telescope_hits,
    registry.telescope_misses,
  )
}

///|
fn telescope_cache_matches(
  entry : DTelescopeCacheEntry,
  prefix_types : Array[DValue],
  prefix_values : Array[DValue],
  values : Array[DValue],
) -> Bool {
  if entry.prefix_types.length() != prefix_types.length() ||
    entry.values.length() != values.length() {
    return false
  }
  for i in 0..<prefix_types.length() {
    if !conv_ty(10000, 0, entry.prefix_types[i], prefix_types[i]) ||
      !conv_at(
        10000,
        0,
        entry.prefix_types[i],
        entry.prefix_values[i],
        prefix_values[i],
      ) {
      return false
    }
  }
  for i in 0..<values.length() {
    if i >= entry.types.length() ||
      !conv_at(10000, 0, entry.types[i], entry.values[i], values[i]) {
      return false
    }
  }
  true
}

///|
/// `telescope_type_values` with semantic caching in a registry.
pub fn telescope_type_values_cached(
  registry : DSchemaRegistry,
  entries : Array[DTelescopeEntry],
  prefix_types : Array[DValue],
  prefix_values : Array[DValue],
  values : Array[DValue],
) -> Array[DValue] {
  for i in 0..<registry.telescopes.length() {
    let entry = registry.telescopes[i]
    if entry.entries == entries &&
      telescope_cache_matches(entry, prefix_types, prefix_values, values) {
      registry.telescope_hits = registry.telescope_hits + 1
      return copy_values(entry.types)
    }
  }
  registry.telescope_misses = registry.telescope_misses + 1
  let types = telescope_type_values(
    entries, prefix_types, prefix_values, values,
  )
  registry.telescopes.push(DTelescopeCacheEntry::{
    entries,
    prefix_types: copy_values(prefix_types),
    prefix_values: copy_values(prefix_values),
    values: copy_values(values),
    types: copy_values(types),
  })
  types
}

///|
pub fn inductive_param_types_cached(
  registry : DSchemaRegistry,
  spec : DInductiveSpec,
  params : Array[DValue],
) -> Array[DValue] {
  telescope_type_values_cached(registry, spec.params, [], [], params)
}

///|
pub fn inductive_index_types_cached(
  registry : DSchemaRegistry,
  spec : DInductiveSpec,
  params : Array[DValue],
  indices : Array[DValue],
) -> Array[DValue] {
  telescope_type_values_cached(
    registry,
    spec.indices,
    inductive_param_types_cached(registry, spec, params),
    params,
    indices,
  )
}

///|
pub fn hit_param_types_cached(
  registry : DSchemaRegistry,
  spec : DHitSpec,
  params : Array[DValue],
) -> Array[DValue] {
  telescope_type_values_cached(registry, spec.params, [], [], params)
}

///|
pub fn hit_index_types_cached(
  registry : DSchemaRegistry,
  spec : DHitSpec,
  params : Array[DValue],
  indices : Array[DValue],
) -> Array[DValue] {
  telescope_type_values_cached(
    registry,
    spec.indices,
    hit_param_types_cached(registry, spec, params),
    params,
    indices,
  )
}

///|
/// AST terms built from a registered plan share the plan's one
/// descriptor rather than reconstructing it at each use.
pub fn inductive_plan_type_term(
  plan : DInductivePlan,
  args : Array[DTerm],
) -> DTerm {
  DInductive(plan.spec, args)
}

///|
pub fn hit_plan_type_term(plan : DHitPlan, args : Array[DTerm]) -> DTerm {
  DHitType(plan.spec, args)
}

// ---------------------------------------------------------------------------
// Persistence, snapshots, and incremental registration
// ---------------------------------------------------------------------------

///|
/// A persistent snapshot of a registry: the descriptors and their
/// validation outcomes, in plan order.  Restoring a snapshot does
/// not revalidate (validation is the expensive step); generic
/// telescope types are recomputed and hash buckets are rebuilt.
pub struct DSchemaRegistrySnapshot {
  inductive_specs : Array[DInductiveSpec]
  inductive_valid : Array[Bool]
  hit_specs : Array[DHitSpec]
  hit_valid : Array[Bool]
}

///|
pub fn schema_registry_snapshot(
  registry : DSchemaRegistry,
) -> DSchemaRegistrySnapshot {
  let inductive_specs : Array[DInductiveSpec] = []
  let inductive_valid : Array[Bool] = []
  for i in 0..<registry.inductives.length() {
    inductive_specs.push(registry.inductives[i].spec)
    inductive_valid.push(registry.inductives[i].valid)
  }
  let hit_specs : Array[DHitSpec] = []
  let hit_valid : Array[Bool] = []
  for i in 0..<registry.hits.length() {
    hit_specs.push(registry.hits[i].spec)
    hit_valid.push(registry.hits[i].valid)
  }
  DSchemaRegistrySnapshot::{
    inductive_specs,
    inductive_valid,
    hit_specs,
    hit_valid,
  }
}

///|
pub fn schema_registry_restore(
  snapshot : DSchemaRegistrySnapshot,
) -> DSchemaRegistry {
  let registry = schema_registry_new()
  for i in 0..<snapshot.inductive_specs.length() {
    let valid = if i < snapshot.inductive_valid.length() {
      snapshot.inductive_valid[i]
    } else {
      false
    }
    ignore(
      registry_add_inductive_plan(registry, snapshot.inductive_specs[i], valid),
    )
  }
  for i in 0..<snapshot.hit_specs.length() {
    let valid = if i < snapshot.hit_valid.length() {
      snapshot.hit_valid[i]
    } else {
      false
    }
    ignore(registry_add_hit_plan(registry, snapshot.hit_specs[i], valid))
  }
  registry.validation_hits = snapshot.inductive_specs.length() +
    snapshot.hit_specs.length()
  registry
}

///|
/// Incrementally merge another registry's descriptors into this
/// one: descriptors already present are hits (no revalidation),
/// missing ones are added with their recorded validity.  Returns
/// the number of newly added plans.
pub fn schema_registry_merge_into(
  registry : DSchemaRegistry,
  other : DSchemaRegistry,
) -> Int32 {
  let mut added = 0
  for i in 0..<other.inductives.length() {
    let plan = other.inductives[i]
    match schema_registry_inductive_plan(registry, plan.spec) {
      Some(_) => registry.validation_hits = registry.validation_hits + 1
      None => {
        ignore(registry_add_inductive_plan(registry, plan.spec, plan.valid))
        added = added + 1
      }
    }
  }
  for i in 0..<other.hits.length() {
    let plan = other.hits[i]
    match schema_registry_hit_plan(registry, plan.spec) {
      Some(_) => registry.validation_hits = registry.validation_hits + 1
      None => {
        ignore(registry_add_hit_plan(registry, plan.spec, plan.valid))
        added = added + 1
      }
    }
  }
  added
}

///|
/// Batch registration: register many descriptors, returning their
/// plans in order (duplicates resolve to the interned plan).
pub fn schema_registry_register_inductives(
  registry : DSchemaRegistry,
  specs : Array[DInductiveSpec],
) -> Array[DInductivePlan] {
  let out : Array[DInductivePlan] = []
  for i in 0..<specs.length() {
    out.push(schema_registry_register_inductive(registry, specs[i]))
  }
  out
}

///|
/// A textual manifest of the registry's plans (id, name, validity,
/// and hash of the structural key), suitable as an external
/// fingerprint of a snapshot.
pub fn schema_registry_manifest(registry : DSchemaRegistry) -> String {
  let mut out = ""
  for i in 0..<registry.inductives.length() {
    let plan = registry.inductives[i]
    out = out +
      "inductive \{plan.id} \{plan.spec.name} \{plan.valid} \{registry_string_hash(plan.key)}\n"
  }
  for i in 0..<registry.hits.length() {
    let plan = registry.hits[i]
    out = out +
      "hit \{plan.id} \{plan.spec.name} \{plan.valid} \{registry_string_hash(plan.key)}\n"
  }
  out
}
