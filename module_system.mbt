///|
// Parameterized modules (functors), imports/opens and namespaces.
//
// A module is a telescope of parameters, followed by imports and
// local declarations.  Declaration and import-argument terms are
// DTerms whose de Bruijn variables refer to that telescope in order.
// Elaboration inlines an imported module into the host telescope:
//
//   * target parameters are replaced by the import arguments;
//   * target imports are elaborated recursively (with cycle checks);
//   * every target local declaration becomes a host entry, so later
//     declarations refer to it by an ordinary de Bruijn variable;
//   * each mapped declaration is checked with the dependent checker.
//
// Name bindings are separate from telescope entries: one entry may
// be bound by its canonical qualified name, an import alias, and (for
// opened imports) an unqualified/renamed name.  Ambiguous unqualified
// bindings are rejected.  Opaque exports are replaced by a fresh
// neutral in the importer's semantic environment after the target
// module has been elaborated, so importers cannot unfold them during
// conversion; transparent exports retain their checked values.
//
// `module_instantiate` is functor application.  It elaborates with
// concrete parameter arguments and then simultaneously substitutes
// every telescope definition, yielding closed DTerm declarations.
// Abstract (bodyless) declarations elaborate to neutral entries;
// instantiation correctly fails until such an entry is supplied by
// a linked implementation (see `module_compilation.mbt`).

///|
pub struct ModuleRename {
  from_name : String
  to_name : String
} derive(Debug, Eq)

///|
pub extend ModuleRename with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend ModuleRename with Eq::{not_equal, equal}

///|
pub fn module_rename(from_name : String, to_name : String) -> ModuleRename {
  ModuleRename::{ from_name, to_name, }
}

///|
pub struct ModuleImport {
  module_path : String
  alias_name : String
  args : Array[DTerm]
  only : Array[String]
  hiding : Array[String]
  opened : Bool
  renames : Array[ModuleRename]
} derive(Debug, Eq)

///|
pub extend ModuleImport with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend ModuleImport with Eq::{not_equal, equal}

///|
pub fn module_import(
  module_path : String,
  args~ : Array[DTerm] = [],
  alias_name~ : String = "",
  only~ : Array[String] = [],
  hiding~ : Array[String] = [],
  opened~ : Bool = false,
  renames~ : Array[ModuleRename] = [],
) -> ModuleImport {
  ModuleImport::{
    module_path,
    alias_name,
    args,
    only,
    hiding,
    opened,
    renames,
  }
}

///|
pub struct ModuleDecl {
  name : String
  ty : DTerm
  // `None` is an abstract declaration: it contributes a neutral
  // telescope entry and can describe an interface, but a module
  // containing it cannot be fully instantiated until linked to an
  // implementation that supplies a body.
  body : DTerm?
  exported : Bool
  transparent : Bool
} derive(Debug, Eq)

///|
pub extend ModuleDecl with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend ModuleDecl with Eq::{not_equal, equal}

///|
pub fn module_decl(
  name : String,
  ty : DTerm,
  body : DTerm,
  exported~ : Bool = true,
  transparent~ : Bool = true,
) -> ModuleDecl {
  ModuleDecl::{ name, ty, body: Some(body), exported, transparent, }
}

///|
/// An exported-by-default abstract declaration, with no body.  It is
/// opaque by default because there is no definition to unfold.
pub fn module_decl_abstract(
  name : String,
  ty : DTerm,
  exported~ : Bool = true,
  transparent~ : Bool = false,
) -> ModuleDecl {
  ModuleDecl::{ name, ty, body: None, exported, transparent, }
}

///|
/// One step of a module's elaboration program.  A module's items
/// determine the order in which its imports and local declarations
/// are elaborated, hence the module telescope against which the
/// de Bruijn indices in declaration types, bodies, and import
/// arguments are written: parameters first, then the context
/// entries contributed by each item in item order.  Interleaving a
/// local declaration before an import is what allows that import's
/// functor arguments to mention the local declaration.
pub enum ModuleItem {
  ModuleItemImport(Int32)
  ModuleItemDecl(Int32)
} derive(Debug, Eq)

///|
pub extend ModuleItem with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend ModuleItem with Eq::{not_equal, equal}

///|
pub struct ModuleDef {
  path : String
  params : Array[DTelescopeEntry]
  imports : Array[ModuleImport]
  opens : Array[String]
  decls : Array[ModuleDecl]
  /// Elaboration order of imports and declarations.  The empty
  /// list selects the legacy order (all imports, then all
  /// declarations); a nonempty list must mention every import and
  /// every declaration index exactly once.
  items : Array[ModuleItem]
} derive(Debug, Eq)

///|
pub extend ModuleDef with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend ModuleDef with Eq::{not_equal, equal}

///|
pub fn module_def(
  path : String,
  params~ : Array[DTelescopeEntry] = [],
  imports~ : Array[ModuleImport] = [],
  opens~ : Array[String] = [],
  decls~ : Array[ModuleDecl] = [],
  items~ : Array[ModuleItem] = [],
) -> ModuleDef {
  ModuleDef::{ path, params, imports, opens, decls, items, }
}

///|
pub struct ModuleEnv {
  modules : Array[ModuleDef]
} derive(Debug, Eq)

///|
pub extend ModuleEnv with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend ModuleEnv with Eq::{not_equal, equal}

///|
pub fn module_env_new() -> ModuleEnv {
  ModuleEnv::{ modules: [], }
}

///|
pub fn module_env_add(env : ModuleEnv, module_ : ModuleDef) -> Bool {
  if module_.path.length() == 0 {
    return false
  }
  for i in 0..<env.modules.length() {
    if env.modules[i].path == module_.path {
      return false
    }
  }
  env.modules.push(module_)
  true
}

///|
pub fn module_env_find(env : ModuleEnv, path : String) -> ModuleDef? {
  for i in 0..<env.modules.length() {
    if env.modules[i].path == path {
      return Some(env.modules[i])
    }
  }
  None
}

///|
pub struct ModuleEntry {
  canonical_name : String
  local_name : String
  source_module : String
  ty : DTerm
  body : DTerm?
  exported : Bool
  transparent : Bool
} derive(Debug, Eq)

///|
pub extend ModuleEntry with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend ModuleEntry with Eq::{not_equal, equal}

///|
pub struct ModuleBinding {
  name : String
  ordinal : Int32
} derive(Debug, Eq)

///|
pub extend ModuleBinding with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend ModuleBinding with Eq::{not_equal, equal}

///|
pub struct ModuleExport {
  name : String
  ordinal : Int32
  transparent : Bool
} derive(Debug, Eq)

///|
pub extend ModuleExport with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend ModuleExport with Eq::{not_equal, equal}

///|
pub struct ModuleSignature {
  module_path : String
  entries : Array[ModuleEntry]
  bindings : Array[ModuleBinding]
  exports : Array[ModuleExport]
} derive(Debug, Eq)

///|
pub extend ModuleSignature with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend ModuleSignature with Eq::{not_equal, equal}

///|
pub struct ModuleInstanceDecl {
  name : String
  canonical_name : String
  ty : DTerm
  body : DTerm
  exported : Bool
  transparent : Bool
} derive(Debug, Eq)

///|
pub extend ModuleInstanceDecl with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend ModuleInstanceDecl with Eq::{not_equal, equal}

///|
pub struct ModuleInstance {
  module_path : String
  decls : Array[ModuleInstanceDecl]
  bindings : Array[ModuleBinding]
} derive(Debug, Eq)

///|
pub extend ModuleInstance with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend ModuleInstance with Eq::{not_equal, equal}

///|
priv enum ModuleSubst {
  ModuleSubstRef(Int32)
  ModuleSubstTerm(DTerm, Int32)
}

///|
priv struct ModuleSegment {
  context_ordinals : Array[Int32]
  local_ordinals : Array[Int32]
  exports : Array[ModuleExport]
}

///|
priv struct ModuleElabState {
  entries : Array[ModuleEntry]
  types : Array[DValue]
  values : Array[DValue]
  bindings : Array[ModuleBinding]
}

///|
fn module_state_new() -> ModuleElabState {
  ModuleElabState::{ entries: [], types: [], values: [], bindings: [], }
}

///|
fn module_contains(names : Array[String], name : String) -> Bool {
  for i in 0..<names.length() {
    if names[i] == name {
      return true
    }
  }
  false
}

///|
fn module_add_binding(
  state : ModuleElabState,
  name : String,
  ordinal : Int32,
) -> Bool {
  if name.length() == 0 {
    return true
  }
  for i in 0..<state.bindings.length() {
    if state.bindings[i].name == name {
      return state.bindings[i].ordinal == ordinal
    }
  }
  state.bindings.push(ModuleBinding::{ name, ordinal, })
  true
}

///|
fn module_subst_to_term(s : ModuleSubst, host_len : Int32) -> DTerm {
  match s {
    ModuleSubstRef(ordinal) => DTVar(host_len - 1 - ordinal)
    ModuleSubstTerm(term, valid_len) =>
      dterm_shift(term, 0, host_len - valid_len)
  }
}

///|
fn module_apply_subst(
  t : DTerm,
  target_len : Int32,
  subst : Array[ModuleSubst],
  host_len : Int32,
) -> DTerm {
  dterm_map_vars_at(t, 0, (i, depth) => {
    if i < depth {
      DTVar(i)
    } else {
      let ordinal = target_len - 1 - (i - depth)
      if ordinal < 0 || ordinal >= subst.length() {
        DTVar(i)
      } else {
        dterm_shift(module_subst_to_term(subst[ordinal], host_len), 0, depth)
      }
    }
  })
}

///|
fn module_append_entry(
  state : ModuleElabState,
  canonical_name : String,
  local_name : String,
  source_module : String,
  ty : DTerm,
  body : DTerm?,
  exported : Bool,
  transparent : Bool,
) -> Int32? {
  let ordinal = state.entries.length()
  let tv = match
    d_as_type(
      ty,
      schema_env(state.types),
      schema_env(state.values),
      ddim_empty(),
    ) {
    Some(v) => v
    None => return None
  }
  let value = match body {
    Some(term) =>
      match
        d_check(
          term,
          tv.value,
          schema_env(state.types),
          schema_env(state.values),
          ddim_empty(),
        ) {
        Some(v) => v
        None => return None
      }
    None => DVNeutral(DNVar(12000 + ordinal))
  }
  state.entries.push(ModuleEntry::{
    canonical_name,
    local_name,
    source_module,
    ty,
    body,
    exported,
    transparent,
  })
  state.types.push(tv.value)
  state.values.push(value)
  Some(ordinal)
}

///|
fn module_validate_param_args(
  target : ModuleDef,
  subst : Array[ModuleSubst],
  state : ModuleElabState,
) -> Bool {
  if subst.length() != target.params.length() {
    return false
  }
  let host_len = state.entries.length()
  for i in 0..<target.params.length() {
    let prefix : Array[ModuleSubst] = []
    for j in 0..<i {
      prefix.push(subst[j])
    }
    let ty = module_apply_subst(target.params[i].ty, i, prefix, host_len)
    let arg = module_subst_to_term(subst[i], host_len)
    let tv = match
      d_as_type(
        ty,
        schema_env(state.types),
        schema_env(state.values),
        ddim_empty(),
      ) {
      Some(v) => v
      None => return false
    }
    match
      d_check(
        arg,
        tv.value,
        schema_env(state.types),
        schema_env(state.values),
        ddim_empty(),
      ) {
      Some(_) => ()
      None => return false
    }
  }
  true
}

///|
fn module_renamed(import_ : ModuleImport, name : String) -> String {
  for i in 0..<import_.renames.length() {
    if import_.renames[i].from_name == name {
      return import_.renames[i].to_name
    }
  }
  name
}

///|
fn module_import_selected(import_ : ModuleImport, name : String) -> Bool {
  if module_contains(import_.hiding, name) {
    return false
  }
  import_.only.length() == 0 || module_contains(import_.only, name)
}

///|

///|
/// The effective elaboration program of a module: its declared
/// item order when present (validated to be a permutation of the
/// import and declaration lists), or the legacy imports-then-
/// declarations order.
fn module_effective_items(module_ : ModuleDef) -> Array[ModuleItem]? {
  if module_.items.length() == 0 {
    let out : Array[ModuleItem] = []
    for i in 0..<module_.imports.length() {
      out.push(ModuleItemImport(i))
    }
    for i in 0..<module_.decls.length() {
      out.push(ModuleItemDecl(i))
    }
    return Some(out)
  }
  if module_.items.length() != module_.imports.length() + module_.decls.length() {
    return None
  }
  let seen_imports : Array[Bool] = []
  for _i in 0..<module_.imports.length() {
    seen_imports.push(false)
  }
  let seen_decls : Array[Bool] = []
  for _i in 0..<module_.decls.length() {
    seen_decls.push(false)
  }
  for i in 0..<module_.items.length() {
    match module_.items[i] {
      ModuleItemImport(index) =>
        if index < 0 || index >= seen_imports.length() || seen_imports[index] {
          return None
        } else {
          seen_imports[index] = true
        }
      ModuleItemDecl(index) =>
        if index < 0 || index >= seen_decls.length() || seen_decls[index] {
          return None
        } else {
          seen_decls[index] = true
        }
    }
  }
  Some(module_.items)
}

///|
fn module_elaborate_into(
  env : ModuleEnv,
  module_ : ModuleDef,
  state : ModuleElabState,
  param_subst : Array[ModuleSubst]?,
  stack : Array[String],
  bind_locals : Bool,
) -> ModuleSegment? {
  if module_contains(stack, module_.path) {
    return None
  }
  let stack2 : Array[String] = []
  for i in 0..<stack.length() {
    stack2.push(stack[i])
  }
  stack2.push(module_.path)
  let subst : Array[ModuleSubst] = []
  match param_subst {
    Some(args) => {
      if !module_validate_param_args(module_, args, state) {
        return None
      }
      for i in 0..<args.length() {
        subst.push(args[i])
      }
    }
    None =>
      for i in 0..<module_.params.length() {
        let p = module_.params[i]
        let ordinal = match
          module_append_entry(
            state,
            module_.path + "." + p.name,
            p.name,
            module_.path,
            p.ty,
            None,
            false,
            true,
          ) {
          Some(v) => v
          None => return None
        }
        subst.push(ModuleSubstRef(ordinal))
        if bind_locals &&
          (
            !module_add_binding(state, p.name, ordinal) ||
            !module_add_binding(state, module_.path + "." + p.name, ordinal)
          ) {
          return None
        }
      }
  }
  let segment = ModuleSegment::{
    context_ordinals: [],
    local_ordinals: [],
    exports: [],
  }
  let items = match module_effective_items(module_) {
    Some(v) => v
    None => return None
  }
  for item_index in 0..<items.length() {
    match items[item_index] {
      ModuleItemImport(import_index) => {
        let import_ = module_.imports[import_index]
        let target = match module_env_find(env, import_.module_path) {
          Some(m) => m
          None => return None
        }
        if import_.args.length() != target.params.length() {
          return None
        }
        let host_len = state.entries.length()
        let target_args : Array[ModuleSubst] = []
        for i in 0..<import_.args.length() {
          let mapped = module_apply_subst(
            import_.args[i],
            subst.length(),
            subst,
            host_len,
          )
          target_args.push(ModuleSubstTerm(mapped, host_len))
        }
        let target_segment = match
          module_elaborate_into(
            env,
            target,
            state,
            Some(target_args),
            stack2,
            false,
          ) {
          Some(seg) => seg
          None => return None
        }
        for i in 0..<target_segment.context_ordinals.length() {
          let ordinal = target_segment.context_ordinals[i]
          subst.push(ModuleSubstRef(ordinal))
          segment.context_ordinals.push(ordinal)
        }
        // Cross the module boundary: opaque exports become neutral
        // constants for all subsequent importer checking.
        for i in 0..<target_segment.exports.length() {
          let ex = target_segment.exports[i]
          if !ex.transparent {
            state.values[ex.ordinal] = DVNeutral(DNVar(13000 + ex.ordinal))
          }
        }
        let opened = import_.opened ||
          module_contains(module_.opens, import_.module_path) ||
          (
            import_.alias_name.length() > 0 &&
            module_contains(module_.opens, import_.alias_name)
          )
        for i in 0..<target_segment.exports.length() {
          let ex = target_segment.exports[i]
          if module_import_selected(import_, ex.name) {
            let canonical = import_.module_path + "." + ex.name
            if !module_add_binding(state, canonical, ex.ordinal) {
              return None
            }
            if import_.alias_name.length() > 0 &&
              !module_add_binding(
                state,
                import_.alias_name + "." + ex.name,
                ex.ordinal,
              ) {
              return None
            }
            if opened &&
              !module_add_binding(
                state,
                module_renamed(import_, ex.name),
                ex.ordinal,
              ) {
              return None
            }
          }
        }
      }
      ModuleItemDecl(decl_index) => {
        let decl = module_.decls[decl_index]
        let host_len = state.entries.length()
        let ty = module_apply_subst(decl.ty, subst.length(), subst, host_len)
        let body = match decl.body {
          Some(term) =>
            Some(module_apply_subst(term, subst.length(), subst, host_len))
          None => None
        }
        let ordinal = match
          module_append_entry(
            state,
            module_.path + "." + decl.name,
            decl.name,
            module_.path,
            ty,
            body,
            decl.exported,
            decl.transparent,
          ) {
          Some(v) => v
          None => return None
        }
        subst.push(ModuleSubstRef(ordinal))
        segment.context_ordinals.push(ordinal)
        segment.local_ordinals.push(ordinal)
        if decl.exported {
          segment.exports.push(ModuleExport::{
            name: decl.name,
            ordinal,
            transparent: decl.transparent,
          })
        }
        if bind_locals &&
          (
            !module_add_binding(state, decl.name, ordinal) ||
            !module_add_binding(state, module_.path + "." + decl.name, ordinal)
          ) {
          return None
        }
      }
    }
  }
  Some(segment)
}

///|
/// Open (generic) elaboration of a parameterized module.  Parameters
/// remain variables; imports and local declarations are checked in
/// that generic telescope.
pub fn module_signature(
  env : ModuleEnv,
  module_ : ModuleDef,
) -> ModuleSignature? {
  let state = module_state_new()
  match module_elaborate_into(env, module_, state, None, [], true) {
    Some(segment) =>
      Some(ModuleSignature::{
        module_path: module_.path,
        entries: state.entries,
        bindings: state.bindings,
        exports: segment.exports,
      })
    None => None
  }
}

///|
pub fn module_validate(env : ModuleEnv, module_ : ModuleDef) -> Bool {
  match module_signature(env, module_) {
    Some(_) => true
    None => false
  }
}

///|
pub fn module_resolve(signature : ModuleSignature, name : String) -> Int32? {
  for i in 0..<signature.bindings.length() {
    if signature.bindings[i].name == name {
      return Some(signature.bindings[i].ordinal)
    }
  }
  None
}

///|
/// A reference to a resolved entry in the full signature telescope.
pub fn module_ref(signature : ModuleSignature, name : String) -> DTerm? {
  match module_resolve(signature, name) {
    Some(ordinal) => Some(DTVar(signature.entries.length() - 1 - ordinal))
    None => None
  }
}

///|
/// Functor application: instantiate every local declaration at the
/// supplied (closed) parameter arguments.  Imported modules are
/// instantiated recursively at their substituted arguments.
pub fn module_instantiate(
  env : ModuleEnv,
  module_ : ModuleDef,
  args : Array[DTerm],
) -> ModuleInstance? {
  if args.length() != module_.params.length() {
    return None
  }
  let state = module_state_new()
  let subst : Array[ModuleSubst] = []
  for i in 0..<args.length() {
    subst.push(ModuleSubstTerm(args[i], 0))
  }
  let segment = match
    module_elaborate_into(env, module_, state, Some(subst), [], true) {
    Some(seg) => seg
    None => return None
  }
  // Simultaneously substitute each entry by the closed definitions
  // of all preceding entries.
  let closed_bodies : Array[DTerm] = []
  let closed_types : Array[DTerm] = []
  for ordinal in 0..<state.entries.length() {
    let prefix : Array[ModuleSubst] = []
    for i in 0..<closed_bodies.length() {
      prefix.push(ModuleSubstTerm(closed_bodies[i], 0))
    }
    let entry = state.entries[ordinal]
    let body0 = match entry.body {
      Some(b) => b
      None => return None
    }
    closed_types.push(module_apply_subst(entry.ty, ordinal, prefix, 0))
    closed_bodies.push(module_apply_subst(body0, ordinal, prefix, 0))
  }
  let decls : Array[ModuleInstanceDecl] = []
  for i in 0..<segment.local_ordinals.length() {
    let ordinal = segment.local_ordinals[i]
    let entry = state.entries[ordinal]
    let ty = closed_types[ordinal]
    let body = closed_bodies[ordinal]
    if !dep_check_closed(body, ty) {
      return None
    }
    decls.push(ModuleInstanceDecl::{
      name: entry.local_name,
      canonical_name: entry.canonical_name,
      ty,
      body,
      exported: entry.exported,
      transparent: entry.transparent,
    })
  }
  Some(ModuleInstance::{
    module_path: module_.path,
    decls,
    bindings: state.bindings,
  })
}

///|
pub fn module_instance_find(
  instance : ModuleInstance,
  name : String,
) -> ModuleInstanceDecl? {
  for i in 0..<instance.decls.length() {
    if instance.decls[i].name == name ||
      instance.decls[i].canonical_name == name {
      return Some(instance.decls[i])
    }
  }
  None
}

///|
pub fn bool_ops_module() -> ModuleDef {
  module_def("Data.BoolOps", decls=[
    module_decl("not", DPi(DBoolTy, DBoolTy), bool_not_term()),
    module_decl("id", DPi(DBoolTy, DBoolTy), DLam(DBoolTy, DTVar(0))),
  ])
}

///|
/// A proof/program segment abstracted over a type, an endofunction
/// and a point.  It also imports Bool operations under an alias and
/// re-exports `not` through a local transparent definition.
pub fn generic_iterate_module() -> ModuleDef {
  // Telescope before local declarations:
  //   A (ordinal 0), f (1), x (2), BoolOps.not (3), BoolOps.id (4).
  // Hence, at a local declaration, not is DTVar(1), x DTVar(2),
  // f DTVar(3), and A DTVar(4).
  let params = [
    dtelescope_entry("A", DUniv(0)),
    dtelescope_entry("f", DPi(DTVar(0), DTVar(1))),
    dtelescope_entry("x", DTVar(1)),
  ]
  module_def(
    "Generic.Iterate",
    params~,
    imports=[module_import("Data.BoolOps", alias_name="B", only=["not"])],
    decls=[
      module_decl("apply2", DTVar(4), DApp(DTVar(3), DApp(DTVar(3), DTVar(2)))),
      // After apply2 (ordinal 5), A is DTVar(5) at this decl.
      module_decl(
        "iterate",
        DPi(DPi(DTVar(5), DTVar(6)), DPi(DTVar(6), DTVar(7))),
        DLam(
          DPi(DTVar(5), DTVar(6)),
          DLam(DTVar(6), DApp(DTVar(1), DApp(DTVar(1), DTVar(0)))),
        ),
      ),
      // After iterate (ordinal 6), BoolOps.not is DTVar(3).
      module_decl("neg", DPi(DBoolTy, DBoolTy), DTVar(3)),
    ],
  )
}

///|
pub fn module_example_env() -> ModuleEnv {
  let env = module_env_new()
  ignore(module_env_add(env, bool_ops_module()))
  ignore(module_env_add(env, generic_iterate_module()))
  env
}

///|
pub fn check_module_system() -> Bool {
  let env = module_example_env()
  let generic = generic_iterate_module()
  let signature = match module_signature(env, generic) {
    Some(s) => s
    None => return false
  }
  // Qualified and alias resolution see the selected import; the
  // hidden (non-selected) id has neither alias nor open binding.
  let not_ordinal = match module_resolve(signature, "B.not") {
    Some(v) => v
    None => return false
  }
  if module_resolve(signature, "Data.BoolOps.not") != Some(not_ordinal) ||
    module_resolve(signature, "B.id") != None ||
    module_resolve(signature, "apply2") == None {
    return false
  }
  // Functor application at Bool.
  let instance = match
    module_instantiate(env, generic, [DBoolTy, bool_not_term(), DBoolLit(true)]) {
    Some(v) => v
    None => return false
  }
  let apply2 = match module_instance_find(instance, "apply2") {
    Some(d) => d
    None => return false
  }
  if dep_nf_closed(apply2.body, DBoolTy) != Some(DBoolLit(true)) {
    return false
  }
  let iterate = match module_instance_find(instance, "iterate") {
    Some(d) => d
    None => return false
  }
  let neg = match module_instance_find(instance, "neg") {
    Some(d) => d
    None => return false
  }
  if dep_nf_closed(
      DApp(DApp(iterate.body, bool_not_term()), DBoolLit(false)),
      DBoolTy,
    ) !=
    Some(DBoolLit(false)) ||
    dep_nf_closed(DApp(neg.body, DBoolLit(true)), DBoolTy) !=
    Some(DBoolLit(false)) {
    return false
  }
  // The same abstract segment instantiates at Nat with successor.
  let nat_instance = match
    module_instantiate(env, generic, [
      DNatTy,
      DLam(DNatTy, DSucc(DTVar(0))),
      d_nat_lit(2),
    ]) {
    Some(v) => v
    None => return false
  }
  let nat_apply2 = match module_instance_find(nat_instance, "apply2") {
    Some(d) => d
    None => return false
  }
  if dep_nf_closed(nat_apply2.body, DNatTy) != Some(d_nat_lit(4)) {
    return false
  }
  // Opening two modules that both export `not` is ambiguous.
  let other = module_def("Data.OtherBoolOps", decls=[
    module_decl("not", DPi(DBoolTy, DBoolTy), DLam(DBoolTy, DTVar(0))),
  ])
  let env2 = module_env_new()
  if !module_env_add(env2, bool_ops_module()) || !module_env_add(env2, other) {
    return false
  }
  let ambiguous = module_def(
    "Client.Ambiguous",
    imports=[
      module_import("Data.BoolOps", opened=true),
      module_import("Data.OtherBoolOps", opened=true),
    ],
    decls=[],
  )
  if module_validate(env2, ambiguous) {
    return false
  }
  // Renaming resolves the ambiguity.
  let renamed = module_def(
    "Client.Renamed",
    imports=[
      module_import("Data.BoolOps", opened=true),
      module_import("Data.OtherBoolOps", opened=true, renames=[
        module_rename("not", "other_not"),
      ]),
    ],
    decls=[],
  )
  let renamed_sig = match module_signature(env2, renamed) {
    Some(s) => s
    None => return false
  }
  module_resolve(renamed_sig, "not") != None &&
  module_resolve(renamed_sig, "other_not") != None &&
  module_resolve(renamed_sig, "not") != module_resolve(renamed_sig, "other_not")
}

///|
/// Phase 11 verification of interleaved module items.  The
/// client module first declares a local seed, then imports a
/// parameterized holder *applied to that seed* -- impossible
/// under the legacy imports-first order, whose failure is also
/// asserted -- and finally exports the imported value.  Malformed
/// item programs (wrong length, duplicate, out of range) are
/// rejected.
pub fn check_module_interleaved_items() -> Bool {
  let holder = module_def(
    "Generic.Holder",
    params=[dtelescope_entry("A", DUniv(0)), dtelescope_entry("a", DTVar(0))],
    decls=[module_decl("held", DTVar(1), DTVar(0))],
  )
  let two = DSucc(DSucc(DNatZero))
  let top_decls = [
    module_decl("seed", DNatTy, two),
    module_decl("answer", DNatTy, DTVar(0)),
  ]
  let top_imports = [module_import("Generic.Holder", args=[DNatTy, DTVar(0)])]
  let top = module_def(
    "Demo.Interleaved",
    imports=top_imports,
    decls=top_decls,
    items=[ModuleItemDecl(0), ModuleItemImport(0), ModuleItemDecl(1)],
  )
  let env = module_env_new()
  if !module_env_add(env, holder) || !module_env_add(env, top) {
    return false
  }
  let signature = match module_signature(env, top) {
    Some(s) => s
    None => return false
  }
  if module_resolve(signature, "answer") == None ||
    module_resolve(signature, "Generic.Holder.held") == None {
    return false
  }
  let instance = match module_instantiate(env, top, []) {
    Some(v) => v
    None => return false
  }
  let answer = match module_instance_find(instance, "answer") {
    Some(d) => d
    None => return false
  }
  if dep_nf_closed(answer.body, DNatTy) != Some(two) {
    return false
  }
  // The legacy order cannot elaborate the same module: the
  // import argument mentions `seed` before it exists.
  let legacy = module_def(
    "Demo.Interleaved",
    imports=top_imports,
    decls=top_decls,
  )
  match module_signature(env, legacy) {
    Some(_) => return false
    None => ()
  }
  // Malformed item programs are rejected.
  let bad_programs = [
    [ModuleItemDecl(0)],
    [ModuleItemDecl(0), ModuleItemDecl(0), ModuleItemImport(0)],
    [ModuleItemDecl(0), ModuleItemImport(3), ModuleItemDecl(1)],
    [ModuleItemImport(0), ModuleItemDecl(1), ModuleItemDecl(1)],
  ]
  for program in bad_programs {
    let bad = module_def(
      "Demo.Interleaved",
      imports=top_imports,
      decls=top_decls,
      items=program,
    )
    match module_signature(env, bad) {
      Some(_) => return false
      None => ()
    }
  }
  true
}
