///|
// Phase 16 Law Suite:
// - Track 1: `check_phase16_schema_large_open_positivity`
// - Track 2: `check_phase16_dsatur_and_glued_cubical_comp`
// - Track 3: `check_phase16_crypto_ed25519_and_wal`
// - Track 5: `check_phase16_sphere_homotopy_and_k5`
// - Track 6: `check_phase16_hou_stream_and_module_merge`

///|
fn hex_nibble(c : Int32) -> Int32 {
  if c >= 48 && c <= 57 {
    c - 48
  } else if c >= 97 && c <= 102 {
    c - 87
  } else if c >= 65 && c <= 70 {
    c - 55
  } else {
    -1
  }
}

///|
fn hex_to_bytes_p16(hex : String) -> Array[Int32] {
  let out : Array[Int32] = []
  let n = hex.length()
  let mut i = 0
  while i + 1 < n {
    let hi = hex_nibble(hex[i].to_int())
    let lo = hex_nibble(hex[i + 1].to_int())
    if hi < 0 || lo < 0 {
      return []
    }
    out.push((hi << 4) | lo)
    i = i + 2
  }
  out
}

///|
fn ascii_bytes_p16(s : String) -> Array[Int32] {
  let out : Array[Int32] = []
  for i in 0..<s.length() {
    out.push(s[i].to_int() & 255)
  }
  out
}

///|
/// Track 1: Cumulative large-universe `simultaneous_ir_compile_joint_block`,
/// Dybjer–Setzer open multi-decoder simultaneous IR (`DOpenSimultaneousIRSpec`),
/// and semantic covariant/container positivity certificates.
pub fn check_phase16_schema_large_open_positivity() -> Bool {
  // 1A. Large-universe cross-dependent simultaneous IR:
  //     `code_interpretation_ir(true)` pairs `El : Code -> Type_0` (codomain
  //     in `Type_1`) with `size : Code -> Nat`, and `El`'s pair clause depends
  //     on `size a`! Previously rejected by both `compile_decode` and
  //     `compile_eliminator_block`; now compiled at `joint_level == 1`.
  let ir_spec = code_interpretation_ir(true)
  if simultaneous_ir_compile_decode(ir_spec, 0) != None ||
    simultaneous_ir_compile_eliminator(ir_spec, 0) != None ||
    simultaneous_ir_joint_motive_level(ir_spec) != 1 {
    return false
  }
  let joint_block = simultaneous_ir_compile_joint_block(ir_spec)
  if joint_block.length() != 2 {
    return false
  }
  let el_term = match joint_block[0] {
    Some(t) => t
    None => return false
  }
  let size_term = match joint_block[1] {
    Some(t) => t
    None => return false
  }
  let code_schema = code_schema_for_simultaneous()
  let empty_terms : Array[DTerm] = []
  let nat_code = DIntro(code_schema, 0, empty_terms, empty_terms)
  let bool_code = DIntro(code_schema, 1, empty_terms, empty_terms)
  let pair_code = DIntro(code_schema, 2, empty_terms, [bool_code, nat_code])
  if dep_nf_closed(DApp(el_term, pair_code), DUniv(0)) !=
    Some(DSigma(DBoolTy, DNatTy)) ||
    dep_nf_closed(DApp(size_term, pair_code), DNatTy) !=
    Some(DSucc(DSucc(DNatZero))) {
    return false
  }

  // 1B. Dybjer–Setzer open multi-decoder simultaneous IR (`m = 2` decoders):
  //     `U` has constructors `bool_c : U` and `dep_pair_c : (a : U) -> (El a -> U) -> U`
  //     decoded simultaneously by `El : U -> Type_0` and `Obs : U -> Type_0`.
  let open_spec = dopen_simultaneous_ir_spec(
    "OpenDualU",
    0,
    [
      dopen_ir_constructor("bool_c", []),
      dopen_ir_constructor("dep_pair_c", [
        dopen_arg_code("a"),
        dopen_arg_decoded_code_fn("b", 0, 0),
      ]),
    ],
    [
      dopen_ir_decoder("El", 0, [
        DBoolTy,
        DSigma(DTVar(4), DApp(DTVar(2), DTVar(0))),
      ]),
      dopen_ir_decoder("Obs", 0, [
        DUnitTy,
        DPi(DTVar(3), DPi(DTVar(5), DApp(DTVar(2), DTVar(0)))),
      ]),
    ],
  )
  if !open_ir_validate(open_spec) {
    return false
  }
  let c_bool = dopen_ir_intro(0, [])
  let c_pair = dopen_ir_intro(1, [
    dopen_val_code(c_bool),
    dopen_val_code_fn(_b => c_bool),
  ])
  if !open_ir_check_code(open_spec, c_pair) {
    return false
  }
  let el_pair = match open_ir_eval_decode(open_spec, 0, c_pair) {
    Some(v) => v
    None => return false
  }
  let obs_pair = match open_ir_eval_decode(open_spec, 1, c_pair) {
    Some(v) => v
    None => return false
  }
  if !conv_ty(0, 0, el_pair, DVSigma(DVBoolTy, _ => DVBoolTy)) {
    return false
  }
  if !conv_ty(0, 0, obs_pair, DVPi(DVUnitTy, _ => DVPi(DVBoolTy, _ => DVUnitTy))) {
    return false
  }
  let depth_val = match
    open_ir_elim_value(
      open_spec,
      [_ => DVSucc(DVZeroNat), args => DVSucc(args[0])],
      c_pair,
    ) {
    Some(v) => v
    None => return false
  }
  if !conv_at(0, 0, DVNatTy, depth_val, DVSucc(DVSucc(DVZeroNat))) {
    return false
  }

  // Single-decoder lowering to kernel `DInductiveSpec` (`inductive_schema_validate`).
  let single_open = dopen_simultaneous_ir_spec(
    "OpenSingleU",
    0,
    [
      dopen_ir_constructor("bool_c", []),
      dopen_ir_constructor("sigma_c", [
        dopen_arg_code("a"),
        dopen_arg_decoded_code_fn("b", 0, 0),
      ]),
    ],
    [
      dopen_ir_decoder("El", 0, [
        DBoolTy,
        DSigma(DTVar(2), DApp(DTVar(1), DTVar(0))),
      ]),
    ],
  )
  match open_ir_lower_single_decoder(single_open) {
    Some(ind) =>
      if !inductive_schema_validate(ind) {
        return false
      }
    None => return false
  }

  // Negative check: ill-scoped open IR decoder reference (`decoder_idx = 2 >= m`).
  let bad_open = dopen_simultaneous_ir_spec(
    "BadOpenU",
    0,
    [
      dopen_ir_constructor("bad_c", [
        dopen_arg_code("a"),
        dopen_arg_decoded_code_fn("b", 0, 2),
      ]),
    ],
    [dopen_ir_decoder("El", 0, [DBoolTy])],
  )
  if open_ir_validate(bad_open) {
    return false
  }

  // 1C. Semantic functorial & container positivity certificates:
  //     Ambient context: `[F : Type_0 -> Type_0, eq_wit : Π X, Equiv (F X) (Σ (_ : Unit), Unit -> X)]`.
  let rec_spec = dinductive_spec("Rec", 0, [], [], [])
  let rec_ref = DInductive(rec_spec, [])
  let f_op_ty = DPi(DUniv(0), DUniv(0))
  let cont_ext = DSigma(DUnitTy, DPi(DUnitTy, DTVar(2)))
  let eq_wit_ty = DPi(DUniv(0), DEquivTy(DApp(DTVar(1), DTVar(0)), cont_ext))
  let ambient_cont = [f_op_ty, eq_wit_ty]
  let cont_cert = dfunctorial_positivity_container_cert(
    0,
    0,
    DUnitTy,
    DLam(DUnitTy, DUnitTy),
    DTVar(0),
  )
  if dfunctorial_positivity_verify(ambient_cont, cont_cert) == None {
    return false
  }
  let f_rec = DApp(DTVar(1), rec_ref)
  if !dterm_family_strictly_positive_functorial(
      ambient_cont,
      f_rec,
      "Rec",
      [cont_cert],
    ) {
    return false
  }
  if dterm_family_strictly_positive_functorial(
      ambient_cont,
      DPi(f_rec, DBoolTy),
      "Rec",
      [cont_cert],
    ) {
    return false
  }
  // Circular container smuggling (`shape_ty = F Unit`) MUST be rejected!
  let smuggled_cert = dfunctorial_positivity_container_cert(
    0,
    0,
    DApp(DTVar(1), DUnitTy),
    DLam(DApp(DTVar(1), DUnitTy), DUnitTy),
    DTVar(0),
  )
  if dfunctorial_positivity_verify(ambient_cont, smuggled_cert) != None {
    return false
  }

  // Covariant-laws certificate grants `positive_args = [0]` (non-strict), so
  // `F Rec` is NOT accepted as *strictly* positive under covariant laws alone!
  let map_ty = DPi(
    DUniv(0),
    DPi(
      DUniv(0),
      DPi(
        DPi(DTVar(1), DTVar(1)),
        DPi(DApp(DTVar(3), DTVar(2)), DApp(DTVar(4), DTVar(2))),
      ),
    ),
  )
  let map_s2 = DTVar(2)
  let id_fn = DLam(DTVar(1), DTVar(0))
  let map_id_lhs = DApp(
    DApp(DApp(DApp(map_s2, DTVar(1)), DTVar(1)), id_fn),
    DTVar(0),
  )
  let map_id_ty = DPi(
    DUniv(0),
    DPi(
      DApp(DTVar(2), DTVar(0)),
      DPath(DApp(DTVar(3), DTVar(1)), map_id_lhs, DTVar(0)),
    ),
  )
  let map_s6 = DTVar(7)
  let gf_fn = DLam(DTVar(5), DApp(DTVar(3), DApp(DTVar(2), DTVar(0))))
  let comp_lhs = DApp(
    DApp(DApp(DApp(map_s6, DTVar(5)), DTVar(3)), gf_fn),
    DTVar(0),
  )
  let inner_fx = DApp(
    DApp(DApp(DApp(map_s6, DTVar(5)), DTVar(4)), DTVar(1)),
    DTVar(0),
  )
  let comp_rhs = DApp(
    DApp(DApp(DApp(map_s6, DTVar(4)), DTVar(3)), DTVar(2)),
    inner_fx,
  )
  let map_comp_ty = DPi(
    DUniv(0),
    DPi(
      DUniv(0),
      DPi(
        DUniv(0),
        DPi(
          DPi(DTVar(1), DTVar(1)),
          DPi(
            DPi(DTVar(3), DTVar(3)),
            DPi(
              DApp(DTVar(7), DTVar(4)),
              DPath(DApp(DTVar(8), DTVar(3)), comp_lhs, comp_rhs),
            ),
          ),
        ),
      ),
    ),
  )
  let ambient_cov = [f_op_ty, map_ty, map_id_ty, map_comp_ty]
  let cov_cert = dfunctorial_positivity_covariant_cert(
    0,
    0,
    DTVar(2),
    DTVar(1),
    DTVar(0),
  )
  let cov_decl = match dfunctorial_positivity_verify(ambient_cov, cov_cert) {
    Some(d) => d
    None => return false
  }
  let f_rec_cov = DApp(DTVar(3), rec_ref)
  cov_decl.strict_args.length() == 0 &&
  cov_decl.positive_args == [0] &&
  !dterm_family_strictly_positive_functorial(
    ambient_cov,
    f_rec_cov,
    "Rec",
    [cov_cert],
  )
}

///|
/// Track 2: DSATUR chromatic upper-bound max-clique repair and higher-dimensional
/// endpoint-glued `0 ~ 1` Circle & Torus open-box composition + 2-cocycle
/// winding obstruction rejection.
pub fn check_phase16_dsatur_and_glued_cubical_comp() -> Bool {
  let di = DVar(0)
  let dj = DVar(1)
  let dk = DVar(2)
  let dm = DVar(3)
  let raw_sys = dsystem_of([
    tube_branch(FEq0(di), k => DVCirclePoint(k)),
    tube_branch(FEq0(dj), k => DVCirclePoint(k)),
    tube_branch(FEq0(dk), k => DVCirclePoint(k)),
    tube_branch(FEq1(di), _k => DVCirclePoint(DZero)),
    tube_branch(FEq1(dj), _k => DVCirclePoint(DZero)),
    tube_branch(FEq0(dm), _k => DVCirclePoint(DZero)),
  ])
  let ds_rep = dsystem_repair_all_maxima_dsatur(
    0,
    4,
    _ => DVCircleTy,
    raw_sys,
    DVCirclePoint(DZero),
    [],
  )
  if ds_rep.chromatic_root_bound < 3 ||
    ds_rep.result.max_branch_count != 3 ||
    !ds_rep.result.all_compatible ||
    ds_rep.result.systems.length() != 2 {
    return false
  }
  for s in ds_rep.result.systems {
    if s.branches.length() != 3 {
      return false
    }
  }

  // 2B. Endpoint-glued `0 ~ 1` 2D Circle open-box composition:
  let cap_rep = circle_square_glued_cap(
    d => DVCirclePoint(d),
    d => DVCirclePoint(d),
    d => DVCirclePoint(d),
    d => DVCirclePoint(d),
    dlevel=4,
  )
  let sq = match cap_rep.filler {
    Some(v) => v
    None => return false
  }
  if !cap_rep.corners_compatible ||
    cap_rep.net_boundary_winding != 0 ||
    !cap_rep.used_hspace_glue {
    return false
  }
  if !conv_at(0, 4, DVCircleTy, dapp_dim(dapp_dim(sq, DZero), dj), DVCirclePoint(dj)) ||
    !conv_at(0, 4, DVCircleTy, dapp_dim(dapp_dim(sq, DOne), dj), DVCirclePoint(dj)) ||
    !conv_at(0, 4, DVCircleTy, dapp_dim(dapp_dim(sq, di), DZero), DVCirclePoint(di)) ||
    !conv_at(0, 4, DVCircleTy, dapp_dim(dapp_dim(sq, di), DOne), DVCirclePoint(di)) {
    return false
  }

  // 2C. Endpoint-glued 2D Torus square (`T^2 = S^1 × S^1`):
  let (t_opt, net_a, net_b) = torus_square_glued_cap(
    d => DVTorusPoint(d, d),
    d => DVTorusPoint(d, d),
    d => DVTorusPoint(d, d),
    d => DVTorusPoint(d, d),
    dlevel=4,
  )
  let t_sq = match t_opt {
    Some(v) => v
    None => return false
  }
  if net_a != 0 || net_b != 0 {
    return false
  }
  if !conv_at(
      0,
      4,
      DVTorusTy,
      dapp_dim(dapp_dim(t_sq, DZero), dj),
      DVTorusPoint(dj, dj),
    ) ||
    !conv_at(
      0,
      4,
      DVTorusTy,
      dapp_dim(dapp_dim(t_sq, di), DOne),
      DVTorusPoint(di, di),
    ) {
    return false
  }

  // 2D. Negative topological obstruction check (`δw != 0`):
  let bad_rep = circle_square_glued_cap(
    d => DVCirclePoint(d),
    d => DVCirclePoint(DNeg(d)),
    _d => DVCirclePoint(DZero),
    _d => DVCirclePoint(DZero),
    dlevel=4,
  )
  bad_rep.corners_compatible &&
  bad_rep.filler is None &&
  bad_rep.net_boundary_winding != 0
}

///|
/// Track 3: FIPS 180-4 SHA-256/SHA-512, RFC 8032 Pure-Ed25519 asymmetric
/// repository signatures (`CHARTSIG` v1), and crash-consistent WAL journal
/// (`CHWALJRN` v1).
pub fn check_phase16_crypto_ed25519_and_wal() -> Bool {
  if crypto_sha256_hex([]) !=
    "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855" {
    return false
  }
  let abc = ascii_bytes_p16("abc")
  if crypto_sha256_hex(abc) !=
    "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad" {
    return false
  }
  if crypto_sha512_hex(abc) !=
    "ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f" {
    return false
  }

  let tv1_seed = hex_to_bytes_p16(
    "9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60",
  )
  let tv1_pub_expected = hex_to_bytes_p16(
    "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a",
  )
  let tv1_sig_expected = hex_to_bytes_p16(
    "e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e065224901555fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b",
  )
  let kp1 = match ed25519_keypair_from_seed(tv1_seed) {
    Some(kp) => kp
    None => return false
  }
  if kp1.public_key.bytes != tv1_pub_expected {
    return false
  }
  let sig1 = match ed25519_sign(kp1, []) {
    Some(s) => s
    None => return false
  }
  if sig1.bytes != tv1_sig_expected || !ed25519_verify(kp1.public_key, [], sig1) {
    return false
  }
  if ed25519_verify(kp1.public_key, [0x72], sig1) {
    return false
  }

  // Asymmetric `CHARTSIG` v1 repository sealing & tamper rejection.
  let raw_store = artifact_memory_byte_store_new()
  let journal_key = "p16-wal/journal.bin"
  let wal = match artifact_wal_store_open(raw_store, wal_key=journal_key) {
    Some((w, _)) => w
    None => return false
  }
  let repo = artifact_repository_new(artifact_wal_byte_store(wal), prefix="repo")
  if artifact_repository_put(repo, "blob", "alpha", [10, 20, 30]) == None {
    return false
  }
  if !artifact_repository_seal_ed25519(repo, kp1) {
    return false
  }
  if !artifact_repository_verify_ed25519(repo, kp1.public_key) {
    return false
  }
  let tv2_seed = hex_to_bytes_p16(
    "4ccd089b28ff96da9db6c346ec114e0f5b8a319f35aba624da8cf6ed4fb8a6fb",
  )
  let kp2 = match ed25519_keypair_from_seed(tv2_seed) {
    Some(kp) => kp
    None => return false
  }
  if artifact_repository_verify_ed25519(repo, kp2.public_key) {
    return false
  }

  // Crash-consistent WAL recovery: uncommitted `tx` + torn tail bytes!
  if artifact_wal_begin_tx(wal) == None {
    return false
  }
  if !artifact_wal_put(wal, "repo/uncommitted-ghost", [99, 98, 97]) {
    return false
  }
  match (raw_store.read)(journal_key) {
    Some(cur_log) => {
      let torn : Array[Int32] = []
      for b in cur_log {
        torn.push(b)
      }
      torn.push(1)
      torn.push(0)
      torn.push(255)
      if !(raw_store.write)(journal_key, torn) {
        return false
      }
    }
    None => return false
  }
  let (wal_recovered, rec_rep) = match
    artifact_wal_store_open(raw_store, wal_key=journal_key) {
    Some(p) => p
    None => return false
  }
  if rec_rep.replayed_transactions <= 0 ||
    rec_rep.discarded_torn_bytes <= 0 {
    return false
  }
  let recovered_bs = artifact_wal_byte_store(wal_recovered)
  if (recovered_bs.read)("repo/uncommitted-ghost") != None {
    return false
  }
  let repo_after = artifact_repository_new(recovered_bs, prefix="repo")
  if !artifact_repository_verify_ed25519(repo_after, kp1.public_key) {
    return false
  }
  artifact_wal_checkpoint(wal_recovered)
}

///|
/// Track 5: Open-context `PathP`/`Σ`-path/fibration loop equivalences, Hopf
/// total-space loop equivalence, open-variable Hopf–Freudenthal retraction
/// `∂_Hopf(σ_{S^2}(p)) = p`, `π_2(S^2)` split retract of `ℤ`, and 5D Stasheff
/// associahedron `K_5` coherence cell.
pub fn check_phase16_sphere_homotopy_and_k5() -> Bool {
  // 5A. Open-context `fibration_loop_equiv_fiber_path_value` certified by
  //     `equiv_bidirectional_certified_in` over neutral `(B, P, b0, e0)`.
  let b_ty = reflect_var(0, DVUniv(0))
  let p_pi_ty = DVPi(b_ty, _ => DVUniv(0))
  let p_var = reflect_var(1, p_pi_ty)
  let p_fam = (x : DValue) => dapp_typed(p_var, x, b_ty)
  let b0 = reflect_var(2, b_ty)
  let e0 = reflect_var(3, p_fam(b0))
  let mut ctx4 = denv_empty()
  ctx4 = denv_cons(DVUniv(0), ctx4)
  ctx4 = denv_cons(p_pi_ty, ctx4)
  ctx4 = denv_cons(b_ty, ctx4)
  ctx4 = denv_cons(p_fam(b0), ctx4)
  let mut env4 = denv_empty()
  env4 = denv_cons(b_ty, env4)
  env4 = denv_cons(p_var, env4)
  env4 = denv_cons(b0, env4)
  env4 = denv_cons(e0, env4)
  let pathp_eq_open = pathp_equiv_transport_eq_value(
    i => p_fam(dapp_dim(reflect_var(4, DVPathTy(_ => b_ty, b0, b0)), i)),
    e0,
    e0,
    16,
  )
  let mut ctx5 = ctx4
  ctx5 = denv_cons(DVPathTy(_ => b_ty, b0, b0), ctx5)
  let mut env5 = env4
  env5 = denv_cons(reflect_var(4, DVPathTy(_ => b_ty, b0, b0)), env5)
  if !equiv_bidirectional_certified_in(
      ctx4,
      env4,
      ddim_empty(),
      sigma_path_equiv_value(b_ty, p_fam, DVPair(b0, e0), DVPair(b0, e0), 16),
    ) ||
    !equiv_bidirectional_certified_in(ctx5, env5, ddim_empty(), pathp_eq_open) {
    return false
  }
  let fib_loop_eq = fibration_loop_equiv_fiber_path_value(b_ty, p_fam, b0, e0, 16)
  if !equiv_bidirectional_certified_in(ctx4, env4, ddim_empty(), fib_loop_eq) {
    return false
  }

  // 5B. Concrete Hopf fibration loop equivalence `Ω¹(E_Hopf) ≃ Σ (p : Ω¹(S²)), ...`.
  let hopf_loop_eq = hopf_total_loop_equiv_fiber_seq_value()
  if !equiv_bidirectional_certified(hopf_loop_eq) {
    return false
  }

  // 5C. Open-variable Hopf–Freudenthal retraction `∂_Hopf(σ_{S^2}(p)) = p`
  //     verified over neutral `p : Ω¹(S^1, base)`!
  let s1_ty = circle_hit_type_value()
  let base_s1 = circle_hit_base_value()
  let loop_s1_ty = circle_loop_space_type_value()
  let p_open = reflect_neutral_at_type(DNVar(0), loop_s1_ty)
  let retr_2path = hopf_freudenthal_retraction_value(p_open)
  let expected_lhs = hopf_connecting_loop_value(
    sphere2_susp_loop1_to_loop2_value(p_open),
  )
  if !conv_at(1, 0, loop_s1_ty, dapp_dim(retr_2path, DZero), expected_lhs) ||
    !conv_at(1, 0, loop_s1_ty, dapp_dim(retr_2path, DOne), p_open) {
    return false
  }
  let dr = DVar(0)
  if !conv_at(1, 1, s1_ty, dapp_dim(dapp_dim(retr_2path, dr), DZero), base_s1) ||
    !conv_at(1, 1, s1_ty, dapp_dim(dapp_dim(retr_2path, dr), DOne), base_s1) {
    return false
  }

  // 5D. Open-variable `π_2(S^2)` split-retract section certificate over
  //     neutral `z : IntegerS`, plus closed evaluations at `-2, 0, +2`.
  let z_ty = integer_type_value()
  let z_open = reflect_neutral_at_type(DNVar(0), z_ty)
  let sect_z = pi2_s2_hopf_retract_sect_value(z_open)
  let composed_z = pi2_s2_hopf_hom_value(integer_to_pi2_s2_value(z_open))
  if !conv_at(1, 0, z_ty, dapp_dim(sect_z, DZero), composed_z) ||
    !conv_at(1, 0, z_ty, dapp_dim(sect_z, DOne), z_open) {
    return false
  }
  for k in [-2, 0, 2] {
    let zk = integer_value(k)
    let got = pi2_s2_hopf_hom_value(integer_to_pi2_s2_value(zk))
    if !conv_at(0, 0, z_ty, got, zk) {
      return false
    }
  }

  // 5E. Stasheff's 5D associahedron `K_5` coherence 5-cell on 5 non-trivial
  //     schema-circle loops `(loop, loop, sym(loop), loop, loop)`.
  let c0 = base_s1
  let lp = circle_hit_loop_path_value()
  let lp_inv = dpath_sym_value(lp)
  let k5 = dpath_associahedron_k5_cell5_value(
    s1_ty,
    c0,
    lp,
    lp,
    lp_inv,
    lp,
    lp,
    2,
  )
  let north4 = dpath_k5_hemi_north4_value(
    s1_ty,
    c0,
    lp,
    lp,
    lp_inv,
    lp,
    lp,
    2,
  )
  let south4 = dpath_k5_hemi_south4_value(
    s1_ty,
    c0,
    lp,
    lp,
    lp_inv,
    lp,
    lp,
    2,
  )
  let lhs1 = dpath_k5_lhs1_value(s1_ty, lp, lp, lp_inv, lp, lp, 2)
  let rhs1 = dpath_k5_rhs1_value(s1_ty, lp, lp, lp_inv, lp, lp, 2)
  let out3 = dpath_k5_route_outer3_value(s1_ty, lp, lp, lp_inv, lp, lp, 2)
  let inn3 = dpath_k5_route_inner3_value(s1_ty, lp, lp, lp_inv, lp, lp, 2)
  let path1_ty = DVPathTy(_ => s1_ty, c0, c0)
  let path2_ty = DVPathTy(_ => path1_ty, lhs1, rhs1)
  let path3_ty = DVPathTy(_ => path2_ty, out3, inn3)
  conv_at(0, 0, path3_ty, dapp_dim(k5, DZero), north4) &&
  conv_at(0, 0, path3_ty, dapp_dim(k5, DOne), south4) &&
  !conv_at(0, 0, loop_s1_ty, lp, dpath_refl_value(c0))
}

///|
/// Track 6: Huet delayed flex-flex constraint graph + pull-based lazy stream
/// unifier iterator, topological multi-module DAG incremental relinking, and
/// deterministic three-way repository merge.
pub fn check_phase16_hou_stream_and_module_merge() -> Bool {
  let c_fn = UConst("c")
  let a_tm = UConst("a")
  let b_tm = UConst("b")
  let u_pre = unifier_new()
  ignore(hou_fresh_meta(u_pre, 0))
  ignore(hou_fresh_meta(u_pre, 0))
  ignore(hou_fresh_meta(u_pre, 0))
  let eq_fr = HouConstraint::{
    lhs: UMeta(0, [a_tm]),
    rhs: UApp(c_fn, UMeta(1, [a_tm])),
    depth: 0,
  }
  let eq_ff = HouConstraint::{
    lhs: UMeta(1, [b_tm]),
    rhs: UMeta(2, [b_tm]),
    depth: 0,
  }
  let pre_rep = hou_solve_with_delayed_flex_flex(
    [eq_fr, eq_ff],
    u_pre,
    reify_flex_flex=false,
  )
  if pre_rep.status != HouDelayedPreUnifier ||
    pre_rep.delayed_edges.length() != 2 {
    return false
  }
  let u_reify = unifier_new()
  ignore(hou_fresh_meta(u_reify, 0))
  ignore(hou_fresh_meta(u_reify, 0))
  ignore(hou_fresh_meta(u_reify, 0))
  let reify_rep = hou_solve_with_delayed_flex_flex(
    [eq_fr, eq_ff],
    u_reify,
    reify_flex_flex=true,
  )
  if reify_rep.status != HouDelayedSolved ||
    reify_rep.delayed_edges.length() != 0 {
    return false
  }

  let u_stream = unifier_new()
  ignore(hou_fresh_meta(u_stream, 0))
  let ca = UApp(c_fn, a_tm)
  let eq_multi = HouConstraint::{ lhs: UMeta(0, [ca, ca]), rhs: ca, depth: 0 }
  let stream = hou_unifier_stream_new(
    [eq_multi],
    u_stream,
    max_depth=3,
    max_projection_args=1,
  )
  let first_sol = hou_unifier_stream_next(stream)
  let nodes_after_one = hou_unifier_stream_nodes(stream)
  if first_sol == None || hou_unifier_stream_is_exhausted(stream) {
    return false
  }
  let mut count = 1
  while true {
    match hou_unifier_stream_next(stream) {
      Some(_) => count = count + 1
      None => break
    }
  }
  if count < 2 ||
    !hou_unifier_stream_is_exhausted(stream) ||
    hou_unifier_stream_nodes(stream) <= nodes_after_one {
    return false
  }

  // 6B. Multi-module DAG incremental relinking with interface-hash cutoff:
  let mk_core = (flag_val : Bool, flag_transparent : Bool) => {
    module_def("Core.Flag", decls=[
      module_decl(
        "flag",
        DBoolTy,
        DBoolLit(flag_val),
        transparent=flag_transparent,
      ),
    ])
  }
  let mid_mod = module_def(
    "Mid.Relay",
    imports=[module_import("Core.Flag", opened=true)],
    decls=[module_decl("relayed", DBoolTy, DTVar(0), transparent=false)],
  )
  let app_mod = module_def(
    "App.Entry",
    imports=[module_import("Mid.Relay", opened=true)],
    decls=[
      module_decl(
        "negated",
        DBoolTy,
        DApp(bool_not_term(), DTVar(0)),
        transparent=true,
      ),
    ],
  )
  let cache = module_compile_cache_new()
  let b1 = module_build_dag_incremental(
    cache,
    [app_mod, mid_mod, mk_core(false, false)],
    entry_path="App.Entry",
  )
  if !b1.ok ||
    b1.recompiled_paths != ["Core.Flag", "Mid.Relay", "App.Entry"] ||
    b1.cache_hit_paths.length() != 0 {
    return false
  }
  let v1 = match b1.relinked_instance {
    Some(inst) =>
      match module_instance_find(inst, "negated") {
        Some(e) => dep_nf_closed(e.body, DBoolTy)
        None => None
      }
    None => None
  }
  if v1 != Some(DBoolLit(true)) {
    return false
  }
  let b2 = module_build_dag_incremental(
    cache,
    [app_mod, mid_mod, mk_core(true, false)],
    entry_path="App.Entry",
  )
  if !b2.ok ||
    b2.recompiled_paths != ["Core.Flag"] ||
    b2.cache_hit_paths != ["Mid.Relay", "App.Entry"] {
    return false
  }
  let v2 = match b2.relinked_instance {
    Some(inst) =>
      match module_instance_find(inst, "negated") {
        Some(e) => dep_nf_closed(e.body, DBoolTy)
        None => None
      }
    None => None
  }
  if v2 != Some(DBoolLit(false)) {
    return false
  }
  let b3 = module_build_dag_incremental(
    cache,
    [app_mod, mid_mod, mk_core(true, true)],
    entry_path="App.Entry",
  )
  if !b3.ok || !b3.recompiled_paths.contains("Mid.Relay") {
    return false
  }
  let cyc_a = module_def("Cyc.A", imports=[module_import("Cyc.B")])
  let cyc_b = module_def("Cyc.B", imports=[module_import("Cyc.A")])
  if !module_topological_plan([cyc_a, cyc_b]).cycle_detected {
    return false
  }

  // 6C. Deterministic Three-Way Repository Merge:
  let key = ArtifactAuthKey::{
    key_id: "p16-merge-key",
    secret_a: 13579,
    secret_b: 24681,
  }
  let base_repo = artifact_repository_new(artifact_memory_byte_store_new())
  let left_repo = artifact_repository_new(artifact_memory_byte_store_new())
  let right_repo = artifact_repository_new(artifact_memory_byte_store_new())
  if artifact_repository_put(base_repo, "mod", "shared", [1, 2]) == None ||
    artifact_repository_put(base_repo, "mod", "obsolete", [9, 9]) == None ||
    !artifact_repository_seal_authenticated(base_repo, key) {
    return false
  }
  if !artifact_repository_sync_incremental(base_repo, left_repo, key).ok ||
    !artifact_repository_sync_incremental(base_repo, right_repo, key).ok {
    return false
  }
  if artifact_repository_put(left_repo, "mod", "shared", [1, 2, 3]) == None ||
    !artifact_repository_remove(left_repo, "mod", "obsolete") ||
    artifact_repository_put(left_repo, "mod", "conv", [42]) == None ||
    !artifact_repository_seal_authenticated(left_repo, key) {
    return false
  }
  if artifact_repository_put(right_repo, "mod", "right_only", [8, 8]) == None ||
    artifact_repository_put(right_repo, "mod", "conv", [42]) == None ||
    !artifact_repository_seal_authenticated(right_repo, key) {
    return false
  }
  let merged_repo = artifact_repository_new(artifact_memory_byte_store_new())
  let m_rep = artifact_repository_merge_three_way(
    left_repo,
    right_repo,
    merged_repo,
    policy=artifact_merge_policy_abort(),
    auth_key=Some(key),
  )
  if !m_rep.ok ||
    m_rep.lca_entries != 2 ||
    m_rep.merged_records != 3 ||
    m_rep.convergent_merges != 1 ||
    m_rep.tombstones_applied != 1 ||
    m_rep.conflicts.length() != 0 ||
    !artifact_repository_verify_authenticated(merged_repo, key) ||
    artifact_repository_record(merged_repo, "mod", "obsolete") != None {
    return false
  }

  if artifact_repository_put(right_repo, "mod", "shared", [99, 100]) == None ||
    !artifact_repository_seal_authenticated(right_repo, key) {
    return false
  }
  let conflict_target = artifact_repository_new(artifact_memory_byte_store_new())
  let c_abort = artifact_repository_merge_three_way(
    left_repo,
    right_repo,
    conflict_target,
    policy=artifact_merge_policy_abort(),
    auth_key=Some(key),
  )
  if c_abort.ok ||
    c_abort.conflicts.length() != 1 ||
    artifact_repository_list(conflict_target).length() != 0 {
    return false
  }
  let c_left = artifact_repository_merge_three_way(
    left_repo,
    right_repo,
    conflict_target,
    policy=artifact_merge_policy_prefer_left(),
    auth_key=Some(key),
  )
  let c_right_target = artifact_repository_new(artifact_memory_byte_store_new())
  let c_right = artifact_repository_merge_three_way(
    left_repo,
    right_repo,
    c_right_target,
    policy=artifact_merge_policy_prefer_right(),
    auth_key=Some(key),
  )
  c_left.ok &&
  c_right.ok &&
  artifact_repository_get(conflict_target, "mod", "shared") == Some([1, 2, 3]) &&
  artifact_repository_get(c_right_target, "mod", "shared") == Some([99, 100])
}
