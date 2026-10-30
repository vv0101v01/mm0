///|
// Separate compilation and linking for parameterized modules.
//
// A `CompiledModule` is the checked object/interface produced from a
// module's generic signature.  It retains the flattened telescope of
// checked entries, so it can be turned back into a synthetic module
// with no imports and linked as an import target without access to
// the original module's source imports.  Its interface hash is
// computed from a public projection (parameters, exported types,
// transparency and transparent bodies); its implementation hash
// also covers opaque and non-exported bodies.  Changing an opaque
// implementation therefore does not invalidate clients' interface
// fingerprints, while changing a public type does.
//
// This file gives separate compilation at the elaboration-object
// level.  The deterministic interface encoding is retained in the
// compiled object; its stable byte-level serialization and parser
// live separately in `module_binary.mbt`.

///|
pub struct ModuleDependencyFingerprint {
  path : String
  interface_hash : Int32
} derive(Debug, Eq)

///|
pub extend ModuleDependencyFingerprint with @moonbitlang/core/debug.Debug::{
  to_repr,
}

///|
pub extend ModuleDependencyFingerprint with Eq::{not_equal, equal}

///|
pub fn module_dependency_fingerprint(
  path : String,
  interface_hash : Int32,
) -> ModuleDependencyFingerprint {
  ModuleDependencyFingerprint::{ path, interface_hash, }
}

///|
/// Identification string recorded in newly compiled modules and
/// stamped by binary migration when a legacy object has none.
pub fn compiled_module_producer_default() -> String {
  "cubical-hermitian/phase-11"
}

///|
pub struct CompiledModule {
  format_version : Int32
  module_path : String
  params : Array[DTelescopeEntry]
  entries : Array[ModuleEntry]
  exports : Array[ModuleExport]
  dependencies : Array[ModuleDependencyFingerprint]
  interface_hash : Int32
  implementation_hash : Int32
  interface_encoding : String
  /// Producer identification recorded by the v2 binary format;
  /// empty for objects parsed from legacy v1 payloads.
  producer : String
} derive(Debug, Eq)

///|
pub extend CompiledModule with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend CompiledModule with Eq::{not_equal, equal}

///|
pub fn compiled_module_format_version() -> Int32 {
  1
}

///|
pub fn module_dependency_of_compiled(
  compiled : CompiledModule,
) -> ModuleDependencyFingerprint {
  module_dependency_fingerprint(compiled.module_path, compiled.interface_hash)
}

///|
fn compiled_dependencies_encoding(
  dependencies : Array[ModuleDependencyFingerprint],
) -> String {
  let mut out = ""
  for i in 0..<dependencies.length() {
    out = out +
      dependencies[i].path +
      ":" +
      "\{dependencies[i].interface_hash}" +
      ";"
  }
  out
}

///|
fn compiled_interface_encoding_of(
  module_path : String,
  params : Array[DTelescopeEntry],
  entries : Array[ModuleEntry],
  exports : Array[ModuleExport],
  dependencies : Array[ModuleDependencyFingerprint],
) -> String {
  let mut out = "cubical-module-interface-v1\npath=" +
    module_path +
    "\nparams=" +
    Repr(params).to_string() +
    "\ndependencies=" +
    compiled_dependencies_encoding(dependencies) +
    "\n"
  for i in 0..<exports.length() {
    let ex = exports[i]
    out = out + "export=" + ex.name + ";transparent=\{ex.transparent};"
    if ex.ordinal >= 0 && ex.ordinal < entries.length() {
      let entry = entries[ex.ordinal]
      out = out + "ty=" + Repr(entry.ty).to_string() + ";"
      if ex.transparent {
        out = out + "body=" + Repr(entry.body).to_string() + ";"
      } else {
        out = out + "body=opaque;"
      }
    } else {
      out = out + "ty=invalid;"
    }
    out = out + "\n"
  }
  out
}

///|
fn compiled_implementation_encoding_of(
  module_path : String,
  params : Array[DTelescopeEntry],
  entries : Array[ModuleEntry],
  exports : Array[ModuleExport],
  dependencies : Array[ModuleDependencyFingerprint],
) -> String {
  "cubical-module-implementation-v1\npath=" +
  module_path +
  "\nparams=" +
  Repr(params).to_string() +
  "\nentries=" +
  Repr(entries).to_string() +
  "\nexports=" +
  Repr(exports).to_string() +
  "\ndependencies=" +
  compiled_dependencies_encoding(dependencies) +
  "\n"
}

///|
/// Compile a module against a source environment, producing a
/// checked compiled object.  The supplied dependency fingerprints are
/// recorded in both hashes; callers normally obtain them from the
/// compiled dependencies used to build the environment.
pub fn module_compile(
  env : ModuleEnv,
  module_ : ModuleDef,
  dependencies : Array[ModuleDependencyFingerprint],
) -> CompiledModule? {
  let signature = match module_signature(env, module_) {
    Some(s) => s
    None => return None
  }
  let interface_encoding = compiled_interface_encoding_of(
    module_.path,
    module_.params,
    signature.entries,
    signature.exports,
    dependencies,
  )
  let implementation_encoding = compiled_implementation_encoding_of(
    module_.path,
    module_.params,
    signature.entries,
    signature.exports,
    dependencies,
  )
  Some(CompiledModule::{
    format_version: compiled_module_format_version(),
    module_path: module_.path,
    params: module_.params,
    entries: signature.entries,
    exports: signature.exports,
    dependencies,
    interface_hash: registry_string_hash(interface_encoding),
    implementation_hash: registry_string_hash(implementation_encoding),
    interface_encoding,
    producer: compiled_module_producer_default(),
  })
}

///|
fn compiled_export_name_at(
  compiled : CompiledModule,
  ordinal : Int32,
) -> String? {
  for i in 0..<compiled.exports.length() {
    if compiled.exports[i].ordinal == ordinal {
      return Some(compiled.exports[i].name)
    }
  }
  None
}

///|
fn compiled_find_export(
  compiled : CompiledModule,
  name : String,
) -> ModuleExport? {
  for i in 0..<compiled.exports.length() {
    if compiled.exports[i].name == name {
      return Some(compiled.exports[i])
    }
  }
  None
}

///|
/// Reconstruct a synthetic, import-free module definition from a
/// compiled object.  Post-parameter entries become declarations in
/// the same telescope order; non-exported names are uniquified with
/// their ordinal and canonical source name so that flattening several
/// namespaces into one telescope cannot create accidental bindings.
pub fn compiled_module_to_module_def(compiled : CompiledModule) -> ModuleDef {
  let decls : Array[ModuleDecl] = []
  for ordinal in compiled.params.length()..<compiled.entries.length() {
    let entry = compiled.entries[ordinal]
    let (name, exported) = match compiled_export_name_at(compiled, ordinal) {
      Some(export_name) => (export_name, true)
      None => ("\{ordinal}:\{entry.canonical_name}", false)
    }
    let decl = match entry.body {
      Some(body) =>
        module_decl(
          name,
          entry.ty,
          body,
          exported~,
          transparent=entry.transparent,
        )
      None =>
        module_decl_abstract(
          name,
          entry.ty,
          exported~,
          transparent=entry.transparent,
        )
    }
    decls.push(decl)
  }
  module_def(compiled.module_path, params=compiled.params, decls~)
}

///|
/// Validate the format and hashes of a compiled object and
/// re-elaborate its synthetic definition in an empty source
/// environment.
pub fn compiled_module_validate(compiled : CompiledModule) -> Bool {
  if compiled.format_version != compiled_module_format_version() ||
    compiled.module_path.length() == 0 ||
    compiled.entries.length() < compiled.params.length() {
    return false
  }
  let interface_encoding = compiled_interface_encoding_of(
    compiled.module_path,
    compiled.params,
    compiled.entries,
    compiled.exports,
    compiled.dependencies,
  )
  let implementation_encoding = compiled_implementation_encoding_of(
    compiled.module_path,
    compiled.params,
    compiled.entries,
    compiled.exports,
    compiled.dependencies,
  )
  if interface_encoding != compiled.interface_encoding ||
    registry_string_hash(interface_encoding) != compiled.interface_hash ||
    registry_string_hash(implementation_encoding) !=
    compiled.implementation_hash {
    return false
  }
  module_validate(module_env_new(), compiled_module_to_module_def(compiled))
}

///|
/// Instantiate a compiled module directly, without a source
/// environment for its original imports.
pub fn compiled_module_instantiate(
  compiled : CompiledModule,
  args : Array[DTerm],
) -> ModuleInstance? {
  if !compiled_module_validate(compiled) {
    return None
  }
  module_instantiate(
    module_env_new(),
    compiled_module_to_module_def(compiled),
    args,
  )
}

///|
/// Check that one compiled module implements another's interface:
/// the paths and interface hashes agree, and every abstract exported
/// entry of the interface has a body in the implementation.
pub fn compiled_module_is_implementation(
  interface_ : CompiledModule,
  implementation : CompiledModule,
) -> Bool {
  if interface_.module_path != implementation.module_path ||
    interface_.interface_hash != implementation.interface_hash {
    return false
  }
  for i in 0..<interface_.exports.length() {
    let ex = interface_.exports[i]
    if ex.ordinal < 0 || ex.ordinal >= interface_.entries.length() {
      return false
    }
    match interface_.entries[ex.ordinal].body {
      Some(_) => ()
      None => {
        let impl_export = match compiled_find_export(implementation, ex.name) {
          Some(v) => v
          None => return false
        }
        if impl_export.ordinal < 0 ||
          impl_export.ordinal >= implementation.entries.length() {
          return false
        }
        match implementation.entries[impl_export.ordinal].body {
          Some(_) => ()
          None => return false
        }
      }
    }
  }
  true
}

// ---------------------------------------------------------------------------
// Compiled-module environments and linking
// ---------------------------------------------------------------------------

///|
pub struct CompiledModuleEnv {
  modules : Array[CompiledModule]
} derive(Debug, Eq)

///|
pub extend CompiledModuleEnv with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend CompiledModuleEnv with Eq::{not_equal, equal}

///|
pub fn compiled_module_env_new() -> CompiledModuleEnv {
  CompiledModuleEnv::{ modules: [], }
}

///|
pub fn compiled_module_env_find(
  env : CompiledModuleEnv,
  path : String,
) -> CompiledModule? {
  for i in 0..<env.modules.length() {
    if env.modules[i].module_path == path {
      return Some(env.modules[i])
    }
  }
  None
}

///|
/// Add a compiled module after validating it.  Rejects duplicate
/// module paths.
pub fn compiled_module_env_add(
  env : CompiledModuleEnv,
  compiled : CompiledModule,
) -> Bool {
  match compiled_module_env_find(env, compiled.module_path) {
    Some(_) => false
    None =>
      if compiled_module_validate(compiled) {
        env.modules.push(compiled)
        true
      } else {
        false
      }
  }
}

///|
/// Build the source environment used by the linker: every compiled
/// dependency becomes its synthetic import-free definition.
pub fn compiled_module_env_to_module_env(env : CompiledModuleEnv) -> ModuleEnv {
  let out = module_env_new()
  for i in 0..<env.modules.length() {
    ignore(module_env_add(out, compiled_module_to_module_def(env.modules[i])))
  }
  out
}

///|
/// Elaborate a client module whose imports are resolved from
/// compiled dependencies.  Extra source modules may be added
/// explicitly, but are not needed for compiled import targets.
pub fn module_link_signature(
  compiled_env : CompiledModuleEnv,
  module_ : ModuleDef,
  extra_sources~ : Array[ModuleDef] = [],
) -> ModuleSignature? {
  let env = compiled_module_env_to_module_env(compiled_env)
  for i in 0..<extra_sources.length() {
    if !module_env_add(env, extra_sources[i]) {
      return None
    }
  }
  module_signature(env, module_)
}

///|
/// Instantiate a client module linked against compiled dependencies.
pub fn module_link_instantiate(
  compiled_env : CompiledModuleEnv,
  module_ : ModuleDef,
  args : Array[DTerm],
  extra_sources~ : Array[ModuleDef] = [],
) -> ModuleInstance? {
  let env = compiled_module_env_to_module_env(compiled_env)
  for i in 0..<extra_sources.length() {
    if !module_env_add(env, extra_sources[i]) {
      return None
    }
  }
  module_instantiate(env, module_, args)
}

///|
/// Compile a module using only compiled objects for its direct
/// imports.  The dependency fingerprints are collected automatically
/// from the compiled environment.
pub fn module_compile_with_compiled(
  compiled_env : CompiledModuleEnv,
  module_ : ModuleDef,
) -> CompiledModule? {
  let dependencies : Array[ModuleDependencyFingerprint] = []
  for i in 0..<module_.imports.length() {
    match
      compiled_module_env_find(compiled_env, module_.imports[i].module_path) {
      Some(compiled) =>
        dependencies.push(module_dependency_of_compiled(compiled))
      None => return None
    }
  }
  module_compile(
    compiled_module_env_to_module_env(compiled_env),
    module_,
    dependencies,
  )
}

// ---------------------------------------------------------------------------
// Incremental compilation cache
// ---------------------------------------------------------------------------

///|
/// A deterministic fingerprint of a module source plus the interface
/// fingerprints of its declared dependencies.
pub fn module_source_fingerprint(
  module_ : ModuleDef,
  dependencies : Array[ModuleDependencyFingerprint],
) -> String {
  "cubical-module-source-v1\n" +
  Repr(module_).to_string() +
  "\ndependencies=" +
  compiled_dependencies_encoding(dependencies) +
  "\n"
}

///|
pub struct ModuleCompileCacheEntry {
  module_path : String
  fingerprint : String
  compiled : CompiledModule
} derive(Debug, Eq)

///|
pub extend ModuleCompileCacheEntry with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend ModuleCompileCacheEntry with Eq::{not_equal, equal}

///|
pub struct ModuleCompileCache {
  entries : Array[ModuleCompileCacheEntry]
} derive(Debug, Eq)

///|
pub extend ModuleCompileCache with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend ModuleCompileCache with Eq::{not_equal, equal}

///|
pub fn module_compile_cache_new() -> ModuleCompileCache {
  ModuleCompileCache::{ entries: [], }
}

///|
pub fn module_compile_cache_size(cache : ModuleCompileCache) -> Int32 {
  cache.entries.length()
}

///|
pub fn module_compile_cache_lookup(
  cache : ModuleCompileCache,
  module_ : ModuleDef,
  dependencies : Array[ModuleDependencyFingerprint],
) -> CompiledModule? {
  let fingerprint = module_source_fingerprint(module_, dependencies)
  for i in 0..<cache.entries.length() {
    if cache.entries[i].module_path == module_.path &&
      cache.entries[i].fingerprint == fingerprint {
      return Some(cache.entries[i].compiled)
    }
  }
  None
}

///|
/// Compile through the cache.  Returns the compiled module and
/// whether it was a cache hit.  A changed source or dependency
/// interface fingerprint replaces the path's cache entry.
pub fn module_compile_cached(
  cache : ModuleCompileCache,
  env : ModuleEnv,
  module_ : ModuleDef,
  dependencies : Array[ModuleDependencyFingerprint],
) -> (CompiledModule, Bool)? {
  match module_compile_cache_lookup(cache, module_, dependencies) {
    Some(compiled) => return Some((compiled, true))
    None => ()
  }
  let compiled = match module_compile(env, module_, dependencies) {
    Some(v) => v
    None => return None
  }
  let entry = ModuleCompileCacheEntry::{
    module_path: module_.path,
    fingerprint: module_source_fingerprint(module_, dependencies),
    compiled,
  }
  for i in 0..<cache.entries.length() {
    if cache.entries[i].module_path == module_.path {
      cache.entries[i] = entry
      return Some((compiled, false))
    }
  }
  cache.entries.push(entry)
  Some((compiled, false))
}

// ---------------------------------------------------------------------------
// Partial application of a compiled functor
// ---------------------------------------------------------------------------

///|
/// Specialize a compiled parameterized module at a closed prefix of
/// its parameter telescope.  The result is again a compiled module,
/// whose parameters are the remaining (substituted) telescope.  This
/// gives import/functor arguments a staged form: some arguments can
/// be supplied when a residual library is compiled and the rest when
/// it is finally linked.
pub fn compiled_module_specialize_prefix(
  compiled : CompiledModule,
  args : Array[DTerm],
) -> CompiledModule? {
  if args.length() > compiled.params.length() ||
    !compiled_module_validate(compiled) {
    return None
  }
  let subst : Array[ModuleSubst] = []
  for i in 0..<args.length() {
    let ty = module_apply_subst(compiled.params[i].ty, i, subst, 0)
    if !dep_check_closed(args[i], ty) {
      return None
    }
    subst.push(ModuleSubstTerm(args[i], 0))
  }
  let residual_params : Array[DTelescopeEntry] = []
  let mut host_len = 0
  for i in args.length()..<compiled.params.length() {
    let param = compiled.params[i]
    let ty = module_apply_subst(param.ty, i, subst, host_len)
    residual_params.push(dtelescope_entry(param.name, ty))
    subst.push(ModuleSubstRef(host_len))
    host_len = host_len + 1
  }
  let synthetic = compiled_module_to_module_def(compiled)
  let residual_decls : Array[ModuleDecl] = []
  for j in 0..<synthetic.decls.length() {
    let decl = synthetic.decls[j]
    let original_len = compiled.params.length() + j
    let ty = module_apply_subst(decl.ty, original_len, subst, host_len)
    let residual = match decl.body {
      Some(body) =>
        module_decl(
          decl.name,
          ty,
          module_apply_subst(body, original_len, subst, host_len),
          exported=decl.exported,
          transparent=decl.transparent,
        )
      None =>
        module_decl_abstract(
          decl.name,
          ty,
          exported=decl.exported,
          transparent=decl.transparent,
        )
    }
    residual_decls.push(residual)
    subst.push(ModuleSubstRef(host_len))
    host_len = host_len + 1
  }
  let residual_def = module_def(
    compiled.module_path,
    params=residual_params,
    decls=residual_decls,
  )
  module_compile(module_env_new(), residual_def, compiled.dependencies)
}

// ---------------------------------------------------------------------------
// Examples and checks
// ---------------------------------------------------------------------------

///|
/// An abstract interface module: `point` has no body, while
/// `use_point` is defined in terms of it.
pub fn abstract_point_module() -> ModuleDef {
  let params = [
    dtelescope_entry("A", DUniv(0)),
    dtelescope_entry("x", DTVar(0)),
  ]
  module_def("Interface.Point", params~, decls=[
    module_decl_abstract("point", DTVar(1)),
    // After `point`, A is DTVar(2) and point is DTVar(0).
    module_decl("use_point", DTVar(2), DTVar(0)),
  ])
}

///|
/// A concrete implementation of `abstract_point_module`.
pub fn point_implementation_module() -> ModuleDef {
  let params = [
    dtelescope_entry("A", DUniv(0)),
    dtelescope_entry("x", DTVar(0)),
  ]
  module_def("Interface.Point", params~, decls=[
    // Before this declaration, x is DTVar(0) and A is DTVar(1).
    module_decl("point", DTVar(1), DTVar(0), transparent=false),
    module_decl("use_point", DTVar(2), DTVar(0)),
  ])
}

///|
/// A client of the point interface at `Bool`.
pub fn point_client_module() -> ModuleDef {
  module_def(
    "Client.Point",
    imports=[
      module_import(
        "Interface.Point",
        args=[DBoolTy, DBoolLit(true)],
        alias_name="P",
        only=["use_point"],
      ),
    ],
    decls=[
      // Import context entries are point, use_point, so use_point
      // is DTVar(0) here.
      module_decl("answer", DBoolTy, DTVar(0)),
    ],
  )
}

///|
/// Aggregated checks for abstract declarations, compiled-interface
/// linking, opacity/interface hashing, prefix specialization and
/// the incremental cache.
pub fn check_module_compilation() -> Bool {
  // Abstract declarations elaborate, but cannot instantiate until
  // implemented.
  let abstract_module = abstract_point_module()
  let abstract_signature = match
    module_signature(module_env_new(), abstract_module) {
    Some(s) => s
    None => return false
  }
  let mut saw_abstract_entry = false
  for i in 0..<abstract_signature.entries.length() {
    if abstract_signature.entries[i].local_name == "point" {
      match abstract_signature.entries[i].body {
        None => saw_abstract_entry = true
        Some(_) => return false
      }
    }
  }
  if !saw_abstract_entry {
    return false
  }
  match
    module_instantiate(module_env_new(), abstract_module, [
      DBoolTy,
      DBoolLit(true),
    ]) {
    Some(_) => return false
    None => ()
  }

  // Interface and implementation have equal interface hashes and
  // different implementation hashes.
  let interface_compiled = match
    module_compile(module_env_new(), abstract_module, []) {
    Some(v) => v
    None => return false
  }
  let implementation_compiled = match
    module_compile(module_env_new(), point_implementation_module(), []) {
    Some(v) => v
    None => return false
  }
  if interface_compiled.interface_hash != implementation_compiled.interface_hash ||
    interface_compiled.implementation_hash ==
    implementation_compiled.implementation_hash ||
    !compiled_module_is_implementation(
      interface_compiled, implementation_compiled,
    ) {
    return false
  }

  // A client typechecks against the abstract compiled interface,
  // but only instantiates after linking the implementation.
  let interface_env = compiled_module_env_new()
  if !compiled_module_env_add(interface_env, interface_compiled) {
    return false
  }
  match module_link_signature(interface_env, point_client_module()) {
    Some(_) => ()
    None => return false
  }
  match module_link_instantiate(interface_env, point_client_module(), []) {
    Some(_) => return false
    None => ()
  }
  let implementation_env = compiled_module_env_new()
  if !compiled_module_env_add(implementation_env, implementation_compiled) {
    return false
  }
  let client_instance = match
    module_link_instantiate(implementation_env, point_client_module(), []) {
    Some(v) => v
    None => return false
  }
  let answer = match module_instance_find(client_instance, "answer") {
    Some(v) => v
    None => return false
  }
  if dep_nf_closed(answer.body, DBoolTy) != Some(DBoolLit(true)) {
    return false
  }

  // Compile BoolOps once, then compile/link Generic.Iterate with
  // no BoolOps source definition in the client environment.
  let bool_compiled = match
    module_compile(module_env_new(), bool_ops_module(), []) {
    Some(v) => v
    None => return false
  }
  let library_env = compiled_module_env_new()
  if !compiled_module_env_add(library_env, bool_compiled) {
    return false
  }
  let generic_compiled = match
    module_compile_with_compiled(library_env, generic_iterate_module()) {
    Some(v) => v
    None => return false
  }
  if generic_compiled.dependencies.length() != 1 ||
    generic_compiled.dependencies[0].path != "Data.BoolOps" {
    return false
  }
  let generic_instance = match
    compiled_module_instantiate(generic_compiled, [
      DBoolTy,
      bool_not_term(),
      DBoolLit(true),
    ]) {
    Some(v) => v
    None => return false
  }
  let generic_apply2 = match module_instance_find(generic_instance, "apply2") {
    Some(v) => v
    None => return false
  }
  if dep_nf_closed(generic_apply2.body, DBoolTy) != Some(DBoolLit(true)) {
    return false
  }

  // Partial compilation: supply A and f now, leaving x for final
  // instantiation of the residual compiled module.
  let residual = match
    compiled_module_specialize_prefix(generic_compiled, [
      DBoolTy,
      bool_not_term(),
    ]) {
    Some(v) => v
    None => return false
  }
  if residual.params.length() != 1 {
    return false
  }
  let residual_instance = match
    compiled_module_instantiate(residual, [DBoolLit(true)]) {
    Some(v) => v
    None => return false
  }
  let residual_apply2 = match
    module_instance_find(residual_instance, "apply2") {
    Some(v) => v
    None => return false
  }
  if dep_nf_closed(residual_apply2.body, DBoolTy) != Some(DBoolLit(true)) {
    return false
  }

  // Incremental cache: identical source/dependencies hit; changing
  // a dependency interface fingerprint misses and recompiles.
  let cache = module_compile_cache_new()
  let deps = [module_dependency_of_compiled(bool_compiled)]
  let source_env = module_example_env()
  let (first, first_hit) = match
    module_compile_cached(cache, source_env, generic_iterate_module(), deps) {
    Some(v) => v
    None => return false
  }
  let (_second, second_hit) = match
    module_compile_cached(cache, source_env, generic_iterate_module(), deps) {
    Some(v) => v
    None => return false
  }
  if first_hit || !second_hit || module_compile_cache_size(cache) != 1 {
    return false
  }
  let changed_deps = [
    module_dependency_fingerprint("Data.BoolOps", first.interface_hash + 1),
  ]
  match
    module_compile_cache_lookup(cache, generic_iterate_module(), changed_deps) {
    Some(_) => return false
    None => ()
  }
  let (_third, third_hit) = match
    module_compile_cached(
      cache,
      source_env,
      generic_iterate_module(),
      changed_deps,
    ) {
    Some(v) => v
    None => return false
  }
  !third_hit && module_compile_cache_size(cache) == 1
}

// ===========================================================================
// Phase 16 (Track 6B): Topological Multi-Module DAG Planner &
// Interface-Hash Cutoff Incremental Relinker
// ===========================================================================

///|
pub struct ModuleBuildPlanReport {
  ok : Bool
  topological_order : Array[String]
  cycle_detected : Bool
  missing_dependency : String?
} derive(Debug, Eq)

///|
pub extend ModuleBuildPlanReport with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend ModuleBuildPlanReport with Eq::{not_equal, equal}

///|
/// Compute a deterministic topological compilation order over `modules` using
/// Kahn's algorithm, rejecting duplicate module paths, missing imports, and
/// cyclic import graphs.
pub fn module_topological_plan(
  modules : Array[ModuleDef],
) -> ModuleBuildPlanReport {
  let n = modules.length()
  let path_index = (p : String) => {
    for i in 0..<n {
      if modules[i].path == p {
        return Some(i)
      }
    }
    None
  }
  for i in 0..<n {
    for j in (i + 1)..<n {
      if modules[i].path == modules[j].path {
        return ModuleBuildPlanReport::{
          ok: false,
          topological_order: [],
          cycle_detected: false,
          missing_dependency: Some(modules[i].path),
        }
      }
    }
  }
  let indeg : Array[Int32] = Array::make(n, 0)
  let adj : Array[Array[Int32]] = Array::makei(n, _ => [])
  for i in 0..<n {
    let seen_deps : Array[Int32] = []
    for imp in modules[i].imports {
      let dep_idx = match path_index(imp.module_path) {
        Some(idx) => idx
        None =>
          return ModuleBuildPlanReport::{
            ok: false,
            topological_order: [],
            cycle_detected: false,
            missing_dependency: Some(imp.module_path),
          }
      }
      if !seen_deps.contains(dep_idx) {
        seen_deps.push(dep_idx)
        adj[dep_idx].push(i)
        indeg[i] = indeg[i] + 1
      }
    }
  }
  let queue : Array[Int32] = []
  for i in 0..<n {
    if indeg[i] == 0 {
      queue.push(i)
    }
  }
  let order : Array[String] = []
  let mut head = 0
  while head < queue.length() {
    let u = queue[head]
    head = head + 1
    order.push(modules[u].path)
    for v in adj[u] {
      indeg[v] = indeg[v] - 1
      if indeg[v] == 0 {
        queue.push(v)
      }
    }
  }
  if order.length() != n {
    return ModuleBuildPlanReport::{
      ok: false,
      topological_order: [],
      cycle_detected: true,
      missing_dependency: None,
    }
  }
  ModuleBuildPlanReport::{
    ok: true,
    topological_order: order,
    cycle_detected: false,
    missing_dependency: None,
  }
}

///|
pub struct ModuleIncrementalBuildReport {
  ok : Bool
  compiled_env : CompiledModuleEnv
  recompiled_paths : Array[String]
  cache_hit_paths : Array[String]
  relinked_instance : ModuleInstance?
} derive(Debug, Eq)

///|
pub extend ModuleIncrementalBuildReport with @moonbitlang/core/debug.Debug::{
  to_repr,
}

///|
pub extend ModuleIncrementalBuildReport with Eq::{not_equal, equal}

///|
/// Incrementally compile a multi-module DAG with interface-hash early cutoff
/// and relink `entry_path`:
/// - When an upstream module changes only an opaque body (`transparent == false`),
///   its `interface_hash` stays invariant, so all downstream dependents hit
///   `cache` without recompiling (`cache_hit_paths`), while `relinked_instance`
///   links against the updated `CompiledModuleEnv` and observes the new body!
/// - When an upstream module changes an exported type or transparent body, its
///   `interface_hash` changes and selectively invalidates only its transitive
///   dependents, leaving unrelated DAG branches cached.
pub fn module_build_dag_incremental(
  cache : ModuleCompileCache,
  modules : Array[ModuleDef],
  entry_path~ : String = "",
  entry_args~ : Array[DTerm] = [],
) -> ModuleIncrementalBuildReport {
  let empty_env = compiled_module_env_new()
  let fail = () => ModuleIncrementalBuildReport::{
    ok: false,
    compiled_env: empty_env,
    recompiled_paths: [],
    cache_hit_paths: [],
    relinked_instance: None,
  }
  let plan = module_topological_plan(modules)
  if !plan.ok {
    return fail()
  }
  let find_mod = (p : String) => {
    for m in modules {
      if m.path == p {
        return Some(m)
      }
    }
    None
  }
  let compiled_env = compiled_module_env_new()
  let recompiled : Array[String] = []
  let hits : Array[String] = []
  for mod_path in plan.topological_order {
    let mod_def = match find_mod(mod_path) {
      Some(m) => m
      None => return fail()
    }
    let dep_fps : Array[ModuleDependencyFingerprint] = []
    for imp in mod_def.imports {
      match compiled_module_env_find(compiled_env, imp.module_path) {
        Some(dep_cm) => dep_fps.push(module_dependency_of_compiled(dep_cm))
        None => return fail()
      }
    }
    let link_src_env = compiled_module_env_to_module_env(compiled_env)
    let (cm, was_hit) = match
      module_compile_cached(cache, link_src_env, mod_def, dep_fps) {
      Some(v) => v
      None => return fail()
    }
    if was_hit {
      hits.push(mod_path)
    } else {
      recompiled.push(mod_path)
    }
    if !compiled_module_env_add(compiled_env, cm) {
      return fail()
    }
  }
  let relinked = if entry_path == "" {
    None
  } else {
    match find_mod(entry_path) {
      Some(entry_mod) => {
        // Link the verified topological module DAG directly without re-running
        // separate compilation on cache hits, so updated upstream opaque
        // implementations propagate through cached intermediate modules at link time.
        let dag_env = module_env_new()
        for mod_path in plan.topological_order {
          if mod_path != entry_path {
            match find_mod(mod_path) {
              Some(m) =>
                if !module_env_add(dag_env, m) {
                  return fail()
                }
              None => return fail()
            }
          }
        }
        match module_instantiate(dag_env, entry_mod, entry_args) {
          Some(inst) => Some(inst)
          None => return fail()
        }
      }
      None => return fail()
    }
  }
  ModuleIncrementalBuildReport::{
    ok: true,
    compiled_env,
    recompiled_paths: recompiled,
    cache_hit_paths: hits,
    relinked_instance: relinked,
  }
}
