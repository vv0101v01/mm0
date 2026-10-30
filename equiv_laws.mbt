///|
fn check_equiv_basic() -> Bool {
  let e = bool_not_equiv_term()
  match d_infer(e, denv_empty(), denv_empty(), ddim_empty()) {
    Some(inferred) => {
      let fwd = equiv_fwd_value(inferred.value, DVBoolTy, DVBoolTy)
      let bwd = equiv_bwd_value(inferred.value, DVBoolTy, DVBoolTy)
      let sect = equiv_sect_value(inferred.value, DVBoolTy, DVBoolTy)
      let sect_true = dapp_typed(sect, DVBool(true), DVBoolTy)
      let quoted = quote_at(0, 0, inferred.ty, inferred.value)
      let roundtrip = match
        d_check(quoted, inferred.ty, denv_empty(), denv_empty(), ddim_empty()) {
        Some(v) => conv_at(0, 0, inferred.ty, v, inferred.value)
        None => false
      }
      conv_ty(0, 0, inferred.ty, DVEquivTy(DVBoolTy, DVBoolTy, 0)) &&
      cubical_bool_is(dapp_typed(fwd, DVBool(true), DVBoolTy), false) &&
      cubical_bool_is(dapp_typed(bwd, DVBool(false), DVBoolTy), true) &&
      cubical_bool_is(dapp_dim(sect_true, DZero), true) &&
      cubical_bool_is(dapp_dim(sect_true, DOne), true) &&
      roundtrip
    }
    None => false
  }
}

///|
fn check_equiv_ua_and_glue() -> Bool {
  let e = bool_not_equiv_term()
  match d_infer(DUa(e), denv_empty(), denv_empty(), ddim_empty()) {
    Some(inferred) => {
      let line_term = DAppDim(DUa(e), DVar(0))
      let fwd = DCoe(line_term, DZero, DOne, DBoolLit(true))
      let bwd = DCoe(line_term, DOne, DZero, DBoolLit(true))
      let path = DLamDim(
        DCoe(DAppDim(DUa(e), DVar(0)), DZero, DVar(0), DBoolLit(true)),
      )
      let pathp = DPathP(line_term, DBoolLit(true), DBoolLit(false))
      let fwd_ok = match
        d_infer(fwd, denv_empty(), denv_empty(), ddim_empty()) {
        Some(r) =>
          conv_ty(0, 0, r.ty, DVBoolTy) && cubical_bool_is(r.value, false)
        None => false
      }
      let bwd_ok = match
        d_infer(bwd, denv_empty(), denv_empty(), ddim_empty()) {
        Some(r) =>
          conv_ty(0, 0, r.ty, DVBoolTy) && cubical_bool_is(r.value, false)
        None => false
      }
      let path_ok = match
        d_as_type(pathp, denv_empty(), denv_empty(), ddim_empty()) {
        Some(tv) =>
          match
            d_check(path, tv.value, denv_empty(), denv_empty(), ddim_empty()) {
            Some(v) =>
              cubical_bool_is(dapp_dim(v, DZero), true) &&
              cubical_bool_is(dapp_dim(v, DOne), false)
            None => false
          }
        None => false
      }
      conv_ty(0, 0, dapp_dim(inferred.value, DZero), DVBoolTy) &&
      conv_ty(0, 0, dapp_dim(inferred.value, DOne), DVBoolTy) &&
      fwd_ok &&
      bwd_ok &&
      path_ok
    }
    None => false
  }
}

///|
fn check_equiv_glue_pair() -> Bool {
  let e = bool_not_equiv_term()
  let glue_ty = DGlueEquiv(DBoolTy, [d_equiv_branch(FEq0(DVar(0)), DBoolTy, e)])
  let denv = ddim_from_array([DVar(0)])
  match d_as_type(glue_ty, denv_empty(), denv_empty(), denv) {
    Some(tv) =>
      match
        d_check(
          DPair(DBoolLit(true), DBoolLit(false)),
          tv.value,
          denv_empty(),
          denv_empty(),
          denv,
        ) {
        Some(v) => {
          let parts = as_glue_equiv(tv.value)
          match parts {
            Some(g) => {
              let values = glue_equiv_partial_values(g, v)
              let quoted_ok = match
                d_as_type(
                  quote_ty(0, 1, tv.value),
                  denv_empty(),
                  denv_empty(),
                  denv,
                ) {
                Some(quoted) => conv_ty(0, 1, quoted.value, tv.value)
                None => false
              }
              values.length() == 1 &&
              cubical_bool_is(values[0], true) &&
              cubical_bool_is(glue_equiv_base_of(g, v), false) &&
              quoted_ok
            }
            None => false
          }
        }
        None => false
      }
    None => false
  }
}

///|
fn check_equiv_neutral_and_comp() -> Bool {
  let ety = DVEquivTy(DVBoolTy, DVBoolTy, 0)
  let ctx = denv_from_array([ety])
  let env = denv_from_array([DVNeutral(DNVar(0))])
  let projection_ok = match
    d_infer(DEquivFwd(DTVar(0)), ctx, env, ddim_empty()) {
    Some(r) => {
      let applied = dapp_typed(r.value, DVBool(true), DVBoolTy)
      quote_at(1, 0, DVBoolTy, applied) ==
      DApp(DEquivFwd(DTVar(0)), DBoolLit(true))
    }
    None => false
  }
  let e = deval_dim(bool_not_equiv_term(), denv_empty(), ddim_empty())
  let composed = comp_value(_ => ety, dsystem_of([]), e, 0)
  projection_ok &&
  cubical_bool_is(
    equiv_fun_value(composed, DVBoolTy, DVBoolTy, DVBool(true)),
    false,
  ) &&
  cubical_bool_is(
    equiv_inv_fun_value(composed, DVBoolTy, DVBoolTy, DVBool(false)),
    true,
  )
}

///|
pub fn check_equiv_ast() -> Bool {
  check_equiv_basic() &&
  check_equiv_ua_and_glue() &&
  check_equiv_glue_pair() &&
  check_equiv_neutral_and_comp()
}
