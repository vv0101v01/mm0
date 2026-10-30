// ---------------------------------------------------------------------------
// Phase 11, item 7: encode/decode for the schema circle.
//
// The universal cover (helix) of the HIT circle `circle_schema()` is
// defined internally by circle induction into the universe: the fibre
// over `base` is the integer type and the fibre over `loop` is the
// `ua` line of the successor equivalence.  Encoding a loop is
// substitution in this family; decoding an integer is integer
// elimination into iterated loop powers.
//
// What is verified by conversion (see
// `check_circle_encode_decode`): the fibre over `base` is the
// integers, encode computes on `refl`, the generating loop and its
// inverse, decode computes on `0`, `1`, `-1`, and the two round
// trips hold by conversion on those representatives.  Since
// Phase 12 a *single* substitution also computes the windings of
// `trans`-composite loops (`loop^2`, `loop^3`, `loop^-2`, and a
// cancelling composite, all in the check): composition in the
// universe over a composite point yields a generic Glue line
// whose endpoint Glue structure has reduced away, and
// `comp_glue_value` now reconstructs that structure from the
// generic point (`glue_endpoint_parts`), deriving target partial
// values for source-inactive branches from the composed base --
// which is exactly what chains the successor equivalence once
// per factor.  The subdivided encoder remains as an independent
// cross-check of the same windings.
//
// The primitive circle type cannot serve as the object of this
// classification: its point conversion only compares the boolean
// zero-faces of point coordinates, under which `loop` composed with
// `loop` is pointwise convertible to `loop`.  The schema circle's
// cell values keep the composites distinct.  A full internal
// `pi_1(S^1) ≃ ℤ` equivalence statement for arbitrary neutral loops
// would additionally need quotient/function-extensionality machinery
// for loop equality; that is out of scope, as in the header of
// `sphere_classification.mbt`.
// ---------------------------------------------------------------------------

///|
/// The schema circle as a type value.
pub fn circle_hit_type_value() -> DValue {
  DVHitType(circle_schema(), [], [])
}

///|
/// The loop space of the schema circle at its base point, as a type
/// value.
pub fn circle_loop_space_type_value() -> DValue {
  loop_space_type_value(circle_hit_type_value(), circle_hit_base_value(), 1)
}

///|
/// Internal `IntegerS` elimination proving `succ(pred(n)) = n` uniformly on
/// all closed and open/neutral `n : IntegerS`.
pub fn integer_succ_pred_sect_value(n : DValue) -> DValue {
  let z_spec = integer_schema()
  let z_ty = integer_type_value()
  let n_spec = nat_schema()
  eval_inductive_elim(
    z_spec,
    (_, num) => {
      DVPathTy(_ => z_ty, integer_succ_value(integer_pred_value(num)), num)
    },
    [
      dpath_refl_value(integer_value(0)),
      DVLam(k => {
        eval_inductive_elim(
          n_spec,
          (_, kv) => {
            let pos_k = DVIntro(z_spec, 1, [], [kv])
            DVPathTy(
              _ => z_ty,
              integer_succ_value(integer_pred_value(pos_k)),
              pos_k,
            )
          },
          [
            dpath_refl_value(integer_value(1)),
            DVLam(m => {
              DVLam(_ih => {
                dpath_refl_value(
                  DVIntro(z_spec, 1, [], [DVIntro(n_spec, 1, [], [m])]),
                )
              })
            }),
          ],
          [],
          [],
          k,
          0,
        )
      }),
      DVLam(k => dpath_refl_value(DVIntro(z_spec, 2, [], [k]))),
    ],
    [],
    [],
    n,
    0,
  )
}

///|
/// Internal `IntegerS` elimination proving `pred(succ(n)) = n` uniformly on
/// all closed and open/neutral `n : IntegerS`.
pub fn integer_pred_succ_retr_value(n : DValue) -> DValue {
  let z_spec = integer_schema()
  let z_ty = integer_type_value()
  let n_spec = nat_schema()
  eval_inductive_elim(
    z_spec,
    (_, num) => {
      DVPathTy(_ => z_ty, integer_pred_value(integer_succ_value(num)), num)
    },
    [
      dpath_refl_value(integer_value(0)),
      DVLam(k => dpath_refl_value(DVIntro(z_spec, 1, [], [k]))),
      DVLam(k => {
        eval_inductive_elim(
          n_spec,
          (_, kv) => {
            let neg_k = DVIntro(z_spec, 2, [], [kv])
            DVPathTy(
              _ => z_ty,
              integer_pred_value(integer_succ_value(neg_k)),
              neg_k,
            )
          },
          [
            dpath_refl_value(integer_value(-1)),
            DVLam(m => {
              DVLam(_ih => {
                dpath_refl_value(
                  DVIntro(z_spec, 2, [], [DVIntro(n_spec, 1, [], [m])]),
                )
              })
            }),
          ],
          [],
          [],
          k,
          0,
        )
      }),
    ],
    [],
    [],
    n,
    0,
  )
}

///|
/// The successor equivalence of the integers, with genuine internal inductive
/// section and retraction proofs verified on open/neutral `n : IntegerS`.
pub fn integer_succ_equiv_value() -> DValue {
  let z = integer_type_value()
  DVEquiv(
    z,
    z,
    DVLam(n => integer_succ_value(n)),
    DVLam(n => integer_pred_value(n)),
    DVLam(n => integer_succ_pred_sect_value(n)),
    DVLam(n => integer_pred_succ_retr_value(n)),
  )
}

///|
/// The universal cover of the schema circle: circle induction into
/// the universe with fibre `ℤ` over `base` and the `ua` line of the
/// successor equivalence over `loop`.
pub fn circle_cover_value(x : DValue) -> DValue {
  let z = integer_type_value()
  eval_hit_elim(
    circle_schema(),
    (_, _) => DVUniv(0),
    [z, ua_value(integer_succ_equiv_value(), z, z, 0)],
    [],
    [],
    x,
    0,
  )
}

///|
/// Encode a loop of the schema circle as its winding number:
/// substitution of `0` in the universal cover along the loop.
pub fn circle_encode_value(p : DValue, dlevel : Int32) -> DValue {
  subst_value(x => circle_cover_value(x), p, integer_value(0), dlevel)
}

///|
/// Encode a composite loop given by its factors: iterated
/// substitution in the universal cover (transport functoriality
/// by hand).  Single substitutions over composites compute the
/// same windings directly since Phase 12; this factored form is
/// retained as a cross-check.
pub fn circle_encode_pieces_value(
  pieces : Array[DValue],
  dlevel : Int32,
) -> DValue {
  let mut acc = integer_value(0)
  for piece in pieces {
    acc = subst_value(x => circle_cover_value(x), piece, acc, dlevel)
  }
  acc
}

///|
/// The `(k+1)`-fold composite of a generating loop `step` with
/// itself, by natural-number elimination: `nat_loop_power_value`
/// at `0` is `step` itself.
fn nat_loop_power_value(step : DValue, k : DValue, dlevel : Int32) -> DValue {
  let circle_ty = circle_hit_type_value()
  eval_inductive_elim(
    nat_schema(),
    (_, _) => circle_loop_space_type_value(),
    [
      step,
      DVLam(_ => DVLam(ih => dpath_trans_value(circle_ty, step, ih, dlevel))),
    ],
    [],
    [],
    k,
    dlevel,
  )
}

///|
/// Decode an integer as a loop of the schema circle: integer
/// elimination sending `0` to reflexivity, positive integers to
/// composites of the generating loop and negative integers to
/// composites of its inverse.  The integer constructors store
/// `|n| - 1` as a natural, recovered by `nat_loop_power_value`.
pub fn circle_decode_value(n : DValue, dlevel : Int32) -> DValue {
  let lp = circle_hit_loop_path_value()
  let base = circle_hit_base_value()
  eval_inductive_elim(
    integer_schema(),
    (_, _) => circle_loop_space_type_value(),
    [
      dpath_refl_value(base),
      DVLam(pa => nat_loop_power_value(lp, pa, dlevel)),
      DVLam(pa => nat_loop_power_value(dpath_sym_value(lp), pa, dlevel)),
    ],
    [],
    [],
    n,
    dlevel,
  )
}

///|
/// Encode/decode for the schema circle computes as expected on the
/// standard representatives, including single-substitution
/// windings of composite loops, and the round trips hold by
/// conversion there.  See the file header for what a full
/// internal `pi_1(S^1) ≃ Z` statement would still require.
pub fn check_circle_encode_decode() -> Bool {
  let z = integer_type_value()
  let base = circle_hit_base_value()
  let lp = circle_hit_loop_path_value()
  let lpi = dpath_sym_value(lp)
  let refl = dpath_refl_value(base)
  let loop_ty = circle_loop_space_type_value()
  let circle_ty = circle_hit_type_value()
  let loop2 = dpath_trans_value(circle_ty, lp, lp, 2)
  let loop3 = dpath_trans_value(circle_ty, loop2, lp, 2)
  let loopm2 = dpath_trans_value(circle_ty, lpi, lpi, 2)
  let loop_cancel = dpath_trans_value(circle_ty, lp, lpi, 2)
  // The fibre of the cover over the base point is the integer type.
  if !conv_at(0, 0, DVUniv(0), circle_cover_value(base), z) {
    return false
  }
  // The cover over a generic loop point is the ua line of successor.
  if !conv_at(
      0,
      0,
      DVUniv(0),
      circle_cover_value(dapp_dim(lp, DVar(0))),
      ua_type_at(integer_succ_equiv_value(), z, z, 0, DVar(0)),
    ) {
    return false
  }
  // Encode computes on refl, the generator and its inverse.
  if !conv_at(0, 0, z, circle_encode_value(refl, 2), integer_value(0)) {
    return false
  }
  if !conv_at(0, 0, z, circle_encode_value(lp, 2), integer_value(1)) {
    return false
  }
  if !conv_at(0, 0, z, circle_encode_value(lpi, 2), integer_value(-1)) {
    return false
  }
  // A single substitution computes composite windings: the
  // successor equivalence chains once per `trans` factor.
  if !conv_at(0, 0, z, circle_encode_value(loop2, 2), integer_value(2)) {
    return false
  }
  if !conv_at(0, 0, z, circle_encode_value(loop3, 2), integer_value(3)) {
    return false
  }
  if !conv_at(0, 0, z, circle_encode_value(loopm2, 2), integer_value(-2)) {
    return false
  }
  if !conv_at(0, 0, z, circle_encode_value(loop_cancel, 2), integer_value(0)) {
    return false
  }
  // Composite windings by subdivision over the factors.
  if !conv_at(0, 0, z, circle_encode_pieces_value([], 2), integer_value(0)) {
    return false
  }
  if !conv_at(
      0,
      0,
      z,
      circle_encode_pieces_value([lp, lp], 2),
      integer_value(2),
    ) {
    return false
  }
  if !conv_at(
      0,
      0,
      z,
      circle_encode_pieces_value([lp, lp, lp], 2),
      integer_value(3),
    ) {
    return false
  }
  if !conv_at(
      0,
      0,
      z,
      circle_encode_pieces_value([lpi, lpi], 2),
      integer_value(-2),
    ) {
    return false
  }
  if !conv_at(
      0,
      0,
      z,
      circle_encode_pieces_value([lp, lpi, lp], 2),
      integer_value(1),
    ) {
    return false
  }
  // Decode computes on 0, 1 and -1, by conversion in the loop space.
  if !conv_at(0, 0, loop_ty, circle_decode_value(integer_value(0), 2), refl) {
    return false
  }
  if !conv_at(0, 0, loop_ty, circle_decode_value(integer_value(1), 2), lp) {
    return false
  }
  if !conv_at(0, 0, loop_ty, circle_decode_value(integer_value(-1), 2), lpi) {
    return false
  }
  // Round trip: encode after decode by a single substitution,
  // on windings -2..3.
  for n in [0, 1, -1, 2, -2, 3] {
    if !conv_at(
        0,
        0,
        z,
        circle_encode_value(circle_decode_value(integer_value(n), 2), 2),
        integer_value(n),
      ) {
      return false
    }
  }
  if !conv_at(
      0,
      0,
      z,
      circle_encode_pieces_value([lp, lp], 2),
      integer_value(2),
    ) {
    return false
  }
  // Round trip: decode after encode on refl, the generator, its
  // inverse and the two-fold composite, by conversion in the
  // loop space.  (Three-fold composites in the other
  // association are not claimed: path composition is not
  // definitionally associative.)
  let reps : Array[DValue] = [refl, lp, lpi, loop2]
  for p in reps {
    if !conv_at(
        0,
        0,
        loop_ty,
        circle_decode_value(circle_encode_value(p, 2), 2),
        p,
      ) {
      return false
    }
  }
  true
}

// ---------------------------------------------------------------------------
// Phase 14: Internal dependent section family `(n : IntegerS) -> encode(decode(n)) = n`
// ---------------------------------------------------------------------------

///|
/// Right-unit path `p ⬝ refl(b) = p` for an arbitrary path `p : a = b` in `ty`.
pub fn dpath_right_unit_general_value(
  ty : DValue,
  p : DValue,
  dlevel : Int32,
) -> DValue {
  let b = dapp_dim(p, DOne)
  let sq = dpath_trans_square_value(ty, p, dpath_refl_value(b), dlevel)
  DVPathLam(t => DVPathLam(i => dapp_dim(dapp_dim(sq, i), DNeg(t))))
}

///|
/// Transport functoriality (`subst fam (p ⬝ q) v = subst fam q (subst fam p v)`)
/// constructed internally by cubical singleton contraction along `q`.
pub fn dpath_subst_trans_value(
  ty : DValue,
  fam : (DValue) -> DValue,
  p : DValue,
  q : DValue,
  v : DValue,
  dlevel : Int32,
) -> DValue {
  let b = dapp_dim(p, DOne)
  let pv = subst_value(fam, p, v, dlevel)
  let ru = dpath_right_unit_general_value(ty, p, dlevel)
  let lhs_to_pv : DValue = DVPathLam(t => {
    subst_value(fam, dapp_dim(ru, t), v, dlevel + 2)
  })
  let pv_to_rhs = transport_pathp_value(_ => fam(b), pv, dlevel + 2)
  let base_eq = dpath_trans_value(fam(b), lhs_to_pv, pv_to_rhs, dlevel + 4)
  transport_value(
    w => {
      let qw = dpath_prefix_value(q, w)
      let xw = dapp_dim(q, w)
      let pqw = dpath_trans_value(ty, p, qw, dlevel + 2)
      DVPathTy(
        _ => fam(xw),
        subst_value(fam, pqw, v, dlevel + 2),
        subst_value(fam, qw, pv, dlevel + 2),
      )
    },
    base_eq,
    dlevel + 6,
  )
}

///|
fn nat_loop_power_comm_value(
  step : DValue,
  k : DValue,
  dlevel : Int32,
) -> DValue {
  let c_ty = circle_hit_type_value()
  let base = circle_hit_base_value()
  let loop_ty = circle_loop_space_type_value()
  let motive = (_idx : Array[DValue], n : DValue) => {
    let pk = nat_loop_power_value(step, n, dlevel)
    DVPathTy(
      _ => loop_ty,
      dpath_trans_value(c_ty, step, pk, dlevel),
      dpath_trans_value(c_ty, pk, step, dlevel),
    )
  }
  let zero_case = dpath_refl_value(dpath_trans_value(c_ty, step, step, dlevel))
  let succ_case = DVLam(m => {
    DVLam(ih_comm => {
      let pm = nat_loop_power_value(step, m, dlevel)
      let s1 : DValue = DVPathLam(t => {
        dpath_trans_value(c_ty, step, dapp_dim(ih_comm, t), dlevel)
      })
      let s2 = dpath_sym_value(
        dpath_assoc3_value(c_ty, base, step, pm, step, dlevel),
      )
      dpath_trans_value(loop_ty, s1, s2, dlevel + 2)
    })
  })
  eval_inductive_elim(
    nat_schema(),
    motive,
    [zero_case, succ_case],
    [],
    [],
    k,
    dlevel,
  )
}

///|
/// Internal `IntegerS` elimination proving the full decode-encode section
/// `(n : IntegerS) -> Path IntegerS (circle_encode_value (circle_decode_value n)) n`
/// uniformly over all closed and open/neutral `n : IntegerS`.
pub fn circle_encode_decode_sect_value(n : DValue, dlevel : Int32) -> DValue {
  let z = integer_type_value()
  let c_ty = circle_hit_type_value()
  let lp = circle_hit_loop_path_value()
  let lpi = dpath_sym_value(lp)
  let zero_z = integer_value(0)

  let pos_motive = (_idx : Array[DValue], k : DValue) => {
    let target = DVIntro(integer_schema(), 1, [], [k])
    let encoded = circle_encode_value(
      nat_loop_power_value(lp, k, dlevel),
      dlevel,
    )
    DVPathTy(_ => z, encoded, target)
  }
  let pos_zero = dpath_refl_value(integer_value(1))
  let pos_succ = DVLam(m => {
    DVLam(ih_eq => {
      let pm = nat_loop_power_value(lp, m, dlevel)
      let comm = nat_loop_power_comm_value(lp, m, dlevel)
      let p1 : DValue = DVPathLam(t => {
        circle_encode_value(dapp_dim(comm, t), dlevel)
      })
      let p2 = dpath_subst_trans_value(
        c_ty,
        x => circle_cover_value(x),
        pm,
        lp,
        zero_z,
        dlevel,
      )
      let p3 : DValue = DVPathLam(t => {
        subst_value(x => circle_cover_value(x), lp, dapp_dim(ih_eq, t), dlevel)
      })
      dpath_trans_value(
        z,
        p1,
        dpath_trans_value(z, p2, p3, dlevel + 2),
        dlevel + 2,
      )
    })
  })

  let neg_motive = (_idx : Array[DValue], k : DValue) => {
    let target = DVIntro(integer_schema(), 2, [], [k])
    let encoded = circle_encode_value(
      nat_loop_power_value(lpi, k, dlevel),
      dlevel,
    )
    DVPathTy(_ => z, encoded, target)
  }
  let neg_zero = dpath_refl_value(integer_value(-1))
  let neg_succ = DVLam(m => {
    DVLam(ih_eq => {
      let pm = nat_loop_power_value(lpi, m, dlevel)
      let comm = nat_loop_power_comm_value(lpi, m, dlevel)
      let p1 : DValue = DVPathLam(t => {
        circle_encode_value(dapp_dim(comm, t), dlevel)
      })
      let p2 = dpath_subst_trans_value(
        c_ty,
        x => circle_cover_value(x),
        pm,
        lpi,
        zero_z,
        dlevel,
      )
      let p3 : DValue = DVPathLam(t => {
        subst_value(x => circle_cover_value(x), lpi, dapp_dim(ih_eq, t), dlevel)
      })
      dpath_trans_value(
        z,
        p1,
        dpath_trans_value(z, p2, p3, dlevel + 2),
        dlevel + 2,
      )
    })
  })

  eval_inductive_elim(
    integer_schema(),
    (_idx, num) => {
      DVPathTy(
        _ => z,
        circle_encode_value(circle_decode_value(num, dlevel), dlevel),
        num,
      )
    },
    [
      dpath_refl_value(zero_z),
      DVLam(k => {
        eval_inductive_elim(
          nat_schema(),
          pos_motive,
          [pos_zero, pos_succ],
          [],
          [],
          k,
          dlevel,
        )
      }),
      DVLam(k => {
        eval_inductive_elim(
          nat_schema(),
          neg_motive,
          [neg_zero, neg_succ],
          [],
          [],
          k,
          dlevel,
        )
      }),
    ],
    [],
    [],
    n,
    dlevel,
  )
}

// ---------------------------------------------------------------------------
// Phase 15: Full Bidirectional Equivalence `Omega(S^1) ≃ Z` and `pi_1(S^1) ≃ Z`
// ---------------------------------------------------------------------------

///|
/// Internal step coherence `(n : IntegerS) -> Path (Omega S^1) (decode(pred n) . lp) (decode n)`
/// proved uniformly over all closed and open/neutral `n : IntegerS` by
/// `IntegerS` + `Nat` induction and cubical 3-cells (`left_inverse3`,
/// `left_unit3`, `nat_loop_power_comm`, `assoc3`, `right_unit3`).
pub fn circle_decode_step_value(n : DValue, dlevel : Int32) -> DValue {
  let c_ty = circle_hit_type_value()
  let base = circle_hit_base_value()
  let lp = circle_hit_loop_path_value()
  let lpi = dpath_sym_value(lp)
  let loop_ty = circle_loop_space_type_value()
  let z_spec = integer_schema()
  let n_spec = nat_schema()

  let zero_branch = dpath_left_inverse3_value(c_ty, base, lp, dlevel)

  let pos_motive = (_idx : Array[DValue], k : DValue) => {
    let pos_k = DVIntro(z_spec, 1, [], [k])
    let lhs = dpath_trans_value(
      c_ty,
      circle_decode_value(integer_pred_value(pos_k), dlevel),
      lp,
      dlevel,
    )
    DVPathTy(_ => loop_ty, lhs, circle_decode_value(pos_k, dlevel))
  }
  let pos_zero = dpath_left_unit3_value(c_ty, base, lp, dlevel)
  let pos_succ = DVLam(m => {
    DVLam(_ih => dpath_sym_value(nat_loop_power_comm_value(lp, m, dlevel)))
  })

  let neg_branch = DVLam(k => {
    let pk = nat_loop_power_value(lpi, k, dlevel)
    let comm_k = nat_loop_power_comm_value(lpi, k, dlevel)
    let s1 : DValue = DVPathLam(t => {
      dpath_trans_value(c_ty, dapp_dim(comm_k, t), lp, dlevel)
    })
    let s2 = dpath_assoc3_value(c_ty, base, pk, lpi, lp, dlevel)
    let li = dpath_left_inverse3_value(c_ty, base, lp, dlevel)
    let s3 : DValue = DVPathLam(t => {
      dpath_trans_value(c_ty, pk, dapp_dim(li, t), dlevel)
    })
    let s4 = dpath_right_unit3_value(c_ty, base, pk, dlevel)
    dpath_trans_value(
      loop_ty,
      s1,
      dpath_trans_value(
        loop_ty,
        s2,
        dpath_trans_value(loop_ty, s3, s4, dlevel + 2),
        dlevel + 2,
      ),
      dlevel + 2,
    )
  })

  eval_inductive_elim(
    z_spec,
    (_idx, num) => {
      let lhs = dpath_trans_value(
        c_ty,
        circle_decode_value(integer_pred_value(num), dlevel),
        lp,
        dlevel,
      )
      DVPathTy(_ => loop_ty, lhs, circle_decode_value(num, dlevel))
    },
    [
      zero_branch,
      DVLam(k => {
        eval_inductive_elim(
          n_spec,
          pos_motive,
          [pos_zero, pos_succ],
          [],
          [],
          k,
          dlevel,
        )
      }),
      neg_branch,
    ],
    [],
    [],
    n,
    dlevel,
  )
}

///|
/// Fiberwise universal-cover encoder `(x : S^1) -> Path S^1 base x -> Cover(x)`.
pub fn circle_encode_x_value(
  _x : DValue,
  p : DValue,
  dlevel : Int32,
) -> DValue {
  subst_value(y => circle_cover_value(y), p, integer_value(0), dlevel)
}

///|
/// Licata–Shulman dependent universal-cover decoder
/// `(x : S^1) -> Cover(x) -> Path S^1 base x`, constructed by HIT
/// elimination over `circle_schema()` into `Cover(x) -> Path S^1 base x`.
/// Over `base` it reduces definitionally to `circle_decode_value`; over
/// `loop` it reconciles backward `ua(succ)` transport with right path
/// composition via `circle_decode_step_value`.
pub fn circle_decode_x_value(
  x : DValue,
  c : DValue,
  dlevel : Int32,
) -> DValue {
  let c_spec = circle_schema()
  let c_ty = circle_hit_type_value()
  let base = circle_hit_base_value()
  let lp = circle_hit_loop_path_value()

  let motive_x = (pt : DValue) => {
    DVPi(circle_cover_value(pt), _ => DVPathTy(_ => c_ty, base, pt))
  }
  let base_fn = DVLam(n => circle_decode_value(n, dlevel))
  // Direct CCHM dependent path over `i ↦ Cover(loop i) -> Path S¹ base (loop i)`:
  // for `g : Glue [i=0 ↦ (Z, succ)] Z`, `m = unglue(g) : Z` is total across `i`,
  // and `un_ua_g = hcomp_Z [i=0 ↦ k. retr_succ(g)(k)] (pred(m))` reduces
  // definitionally to `g` at `i = 0` and `pred(g)` at `i = 1`.
  let loop_branch : DValue = DVPathLam(i => {
    let loop_i = hit_cell_value(c_spec, 1, [], [], [i])
    let cov_i = circle_cover_value(loop_i)
    DVLam(g => {
      let m = match as_glue_equiv(cov_i) {
        Some(parts) => glue_equiv_base_of(parts, g)
        None => g
      }
      let dec_pred_m = circle_decode_value(integer_pred_value(m), dlevel)
      let sq = dpath_trans_square_value(c_ty, dec_pred_m, lp, dlevel + 2)
      DVPathLam(j => {
        let base_pt = dapp_dim(dapp_dim(sq, j), i)
        let sys = dsystem_of([
          tube_branch(face_simplify(FEq0(j)), _ => base),
          tube_branch(face_simplify(FEq1(j)), _ => loop_i),
          tube_branch(face_simplify(FEq0(i)), k => {
            dapp_dim(
              circle_decode_value(
                dapp_dim(integer_pred_succ_retr_value(g), k),
                dlevel,
              ),
              j,
            )
          }),
          tube_branch(face_simplify(FEq1(i)), k => {
            dapp_dim(dapp_dim(circle_decode_step_value(m, dlevel), k), j)
          }),
        ])
        hcomp_value(c_ty, sys, base_pt, dlevel + 4)
      })
    })
  })
  let fn_at_x = eval_hit_elim(
    c_spec,
    (_, pt) => motive_x(pt),
    [base_fn, loop_branch],
    [],
    [],
    x,
    dlevel + 8,
  )
  dapp_typed(fn_at_x, c, circle_cover_value(x))
}

///|
/// Dependent retraction `(x : S^1) (p : Path S^1 base x) ->
/// Path (Path S^1 base x) (circle_decode_x_value x (circle_encode_x_value x p)) p`
/// proved on open/neutral `(x, p)` by cubical singleton contraction (`J`).
/// At `(base, refl_base)`, `decode_x(base, encode_x(base, refl))` reduces
/// definitionally to `refl_base`.
pub fn circle_decode_encode_x_retr_value(
  _x : DValue,
  p : DValue,
  dlevel : Int32,
) -> DValue {
  let c_ty = circle_hit_type_value()
  let base = circle_hit_base_value()
  dj_singleton_elim_value(
    (y, q) => {
      let p_ty = DVPathTy(_ => c_ty, base, y)
      DVPathTy(
        _ => p_ty,
        circle_decode_x_value(y, circle_encode_x_value(y, q, dlevel), dlevel),
        q,
      )
    },
    dpath_refl_value(dpath_refl_value(base)),
    p,
    dlevel + 6,
  )
}

///|
/// Dependent fiberwise section parameterized by an arbitrary `IntegerS` h-Set
/// witness `is_set_z : (x y : Z) -> (p q : Path Z x y) -> Path (Path Z x y) p q`.
pub fn circle_encode_decode_x_sect_with_zset_value(
  x : DValue,
  c : DValue,
  is_set_z : (DValue, DValue, DValue, DValue) -> DValue,
  dlevel : Int32,
) -> DValue {
  let c_spec = circle_schema()
  let z_ty = integer_type_value()
  let motive_x = (pt : DValue) => {
    let cov = circle_cover_value(pt)
    DVPi(cov, v => {
      DVPathTy(
        _ => cov,
        circle_encode_x_value(pt, circle_decode_x_value(pt, v, dlevel), dlevel),
        v,
      )
    })
  }
  let base_fn = DVLam(n => circle_encode_decode_sect_value(n, dlevel))
  let loop_line = memo_dim_line(i => {
    motive_x(hit_cell_value(c_spec, 1, [], [], [i]))
  })
  let tr_base = transport_value(loop_line, base_fn, dlevel + 6)
  let pw_eq = DVLam(n => {
    let lhs_path = dapp_typed(tr_base, n, z_ty)
    let rhs_path = circle_encode_decode_sect_value(n, dlevel)
    let enc_dec_n = circle_encode_value(circle_decode_value(n, dlevel), dlevel)
    is_set_z(enc_dec_n, n, lhs_path, rhs_path)
  })
  let fn_eq = dpath_funext_value(pw_eq, z_ty)
  let loop_branch = dpathp_of_transport_eq_value(
    loop_line,
    base_fn,
    base_fn,
    fn_eq,
    dlevel + 8,
  )
  let fn_at_x = eval_hit_elim(
    c_spec,
    (_, pt) => motive_x(pt),
    [base_fn, loop_branch],
    [],
    [],
    x,
    dlevel + 8,
  )
  dapp_typed(fn_at_x, c, circle_cover_value(x))
}

///|
/// Dependent fiberwise section `(x : S^1) (c : Cover x) ->
/// Path (Cover x) (circle_encode_x_value x (circle_decode_x_value x c)) c`,
/// proved by `circle_schema()` elimination on `x` (over `base` it is
/// `circle_encode_decode_sect_value`, and over `loop` each fiber `Cover(base) = Z`
/// is an h-Set via `integer_is_set_value`).
pub fn circle_encode_decode_x_sect_value(
  x : DValue,
  c : DValue,
  dlevel : Int32,
) -> DValue {
  circle_encode_decode_x_sect_with_zset_value(
    x,
    c,
    (a, b, p1, p2) => integer_is_set_value(a, b, p1, p2, dlevel + 8),
    dlevel,
  )
}

///|
/// Loop-space retraction `(p : Omega(S^1)) -> Path (Omega(S^1)) (decode (encode p)) p`
/// on **arbitrary open/neutral loops** `p : Path S^1 base base`, obtained by
/// specializing `circle_decode_encode_x_retr_value` to `x = base` (where
/// `circle_decode_x_value(base, -)` reduces definitionally to `circle_decode_value`).
pub fn circle_decode_encode_retr_value(p : DValue, dlevel : Int32) -> DValue {
  circle_decode_encode_x_retr_value(circle_hit_base_value(), p, dlevel)
}

///|
/// First-class full bidirectional equivalence
///   `Equiv (Path S^1 base base) IntegerS`
/// (`Omega(S^1, base) ≃ Z`), whose section AND retraction hold by kernel
/// conversion on arbitrary open/neutral integers `n : IntegerS` and arbitrary
/// open/neutral loops `p : Omega(S^1, base)`.
pub fn circle_loop_space_equiv_integer_value(dlevel : Int32) -> DValue {
  let loop_ty = circle_loop_space_type_value()
  let z_ty = integer_type_value()
  equiv_make_value(
    loop_ty,
    z_ty,
    DVLam(p => circle_encode_value(p, dlevel)),
    DVLam(n => circle_decode_value(n, dlevel)),
    DVLam(n => circle_encode_decode_sect_value(n, dlevel)),
    DVLam(p => circle_decode_encode_retr_value(p, dlevel)),
  )
}

///|
/// Fiberwise universal cover equivalence parameterized by an arbitrary
/// `IntegerS` h-Set witness `is_set_z`.
pub fn circle_path_equiv_cover_with_zset_value(
  x : DValue,
  is_set_z : (DValue, DValue, DValue, DValue) -> DValue,
  dlevel : Int32,
) -> DValue {
  let c_ty = circle_hit_type_value()
  let base = circle_hit_base_value()
  let path_ty = DVPathTy(_ => c_ty, base, x)
  let cov_ty = circle_cover_value(x)
  equiv_make_value(
    path_ty,
    cov_ty,
    DVLam(p => circle_encode_x_value(x, p, dlevel)),
    DVLam(c => circle_decode_x_value(x, c, dlevel)),
    DVLam(c => circle_encode_decode_x_sect_with_zset_value(x, c, is_set_z, dlevel)),
    DVLam(p => circle_decode_encode_x_retr_value(x, p, dlevel)),
  )
}

///|
/// Fiberwise universal cover equivalence `(x : S^1) -> Equiv (Path S^1 base x) (Cover x)`.
pub fn circle_path_equiv_cover_value(x : DValue, dlevel : Int32) -> DValue {
  circle_path_equiv_cover_with_zset_value(
    x,
    (a, b, p1, p2) => integer_is_set_value(a, b, p1, p2, dlevel + 8),
    dlevel,
  )
}

// ---------------------------------------------------------------------------
// Internal Hedberg / Encode-Decode Set-hood of `IntegerS` & `pi_1(S^1) ≃ Z`
// ---------------------------------------------------------------------------

///|
pub fn empty_inductive_schema() -> DInductiveSpec {
  dinductive_spec("EmptyS", 0, [], [], [])
}

///|
pub fn empty_inductive_type_value() -> DValue {
  DVInductive(empty_inductive_schema(), [], [])
}

///|
pub fn empty_inductive_elim_value(
  target_ty : DValue,
  scrut : DValue,
  dlevel : Int32,
) -> DValue {
  eval_inductive_elim(
    empty_inductive_schema(),
    (_, _) => target_ty,
    [],
    [],
    [],
    scrut,
    dlevel,
  )
}

///|
fn nat_s_code_value(a : DValue, b : DValue, dlevel : Int32) -> DValue {
  let n_spec = nat_schema()
  let n_ty = DVInductive(n_spec, [], [])
  let emp = empty_inductive_type_value()
  let fn_ty = DVPi(n_ty, _ => DVUniv(0))
  let zero_fn = DVLam(b0 => {
    eval_inductive_elim(
      n_spec,
      (_, _) => DVUniv(0),
      [DVUnitTy, DVLam(_ => DVLam(_ => emp))],
      [],
      [],
      b0,
      dlevel,
    )
  })
  let succ_fn = DVLam(_m => {
    DVLam(ih_m => {
      DVLam(b0 => {
        eval_inductive_elim(
          n_spec,
          (_, _) => DVUniv(0),
          [emp, DVLam(k => DVLam(_ => dapp_typed(ih_m, k, n_ty)))],
          [],
          [],
          b0,
          dlevel,
        )
      })
    })
  })
  let f_a = eval_inductive_elim(
    n_spec,
    (_, _) => fn_ty,
    [zero_fn, succ_fn],
    [],
    [],
    a,
    dlevel,
  )
  dapp_typed(f_a, b, n_ty)
}

///|
fn nat_s_code_refl_value(a : DValue, dlevel : Int32) -> DValue {
  eval_inductive_elim(
    nat_schema(),
    (_, av) => nat_s_code_value(av, av, dlevel),
    [DVUnit, DVLam(_ => DVLam(ih => ih))],
    [],
    [],
    a,
    dlevel,
  )
}

///|
fn nat_s_diag_code_is_prop_value(
  a : DValue,
  u : DValue,
  v : DValue,
  dlevel : Int32,
) -> DValue {
  let c_aa = nat_s_code_value(a, a, dlevel)
  let unit_prop = DVLam(_ => DVLam(_ => dpath_refl_value(DVUnit)))
  let fn_a = eval_inductive_elim(
    nat_schema(),
    (_, av) => {
      let c = nat_s_code_value(av, av, dlevel)
      DVPi(c, u0 => DVPi(c, v0 => DVPathTy(_ => c, u0, v0)))
    },
    [unit_prop, DVLam(_ => DVLam(ih => ih))],
    [],
    [],
    a,
    dlevel,
  )
  dapp_typed(dapp_typed(fn_a, u, c_aa), v, c_aa)
}

///|
fn nat_s_decode_value(
  a : DValue,
  b : DValue,
  c : DValue,
  dlevel : Int32,
) -> DValue {
  let n_spec = nat_schema()
  let n_ty = DVInductive(n_spec, [], [])
  let n0 = DVIntro(n_spec, 0, [], [])
  let succ_ctor = DVLam(v => DVIntro(n_spec, 1, [], [v]))
  let dec_ty = (av : DValue, bv : DValue) => {
    DVPi(nat_s_code_value(av, bv, dlevel), _ => DVPathTy(_ => n_ty, av, bv))
  }
  let zero_fn = DVLam(b0 => {
    eval_inductive_elim(
      n_spec,
      (_, bv) => dec_ty(n0, bv),
      [
        DVLam(_ => dpath_refl_value(n0)),
        DVLam(k => {
          DVLam(_ => {
            DVLam(u0 => {
              empty_inductive_elim_value(
                DVPathTy(_ => n_ty, n0, DVIntro(n_spec, 1, [], [k])),
                u0,
                dlevel,
              )
            })
          })
        }),
      ],
      [],
      [],
      b0,
      dlevel,
    )
  })
  let succ_fn = DVLam(m => {
    let sm = DVIntro(n_spec, 1, [], [m])
    DVLam(ih_m => {
      DVLam(b0 => {
        eval_inductive_elim(
          n_spec,
          (_, bv) => dec_ty(sm, bv),
          [
            DVLam(u0 => {
              empty_inductive_elim_value(DVPathTy(_ => n_ty, sm, n0), u0, dlevel)
            }),
            DVLam(k => {
              DVLam(_ => {
                let dec_mk = dapp_typed(ih_m, k, n_ty)
                let c_mk = nat_s_code_value(m, k, dlevel)
                DVLam(u0 => {
                  dpath_cong_value(
                    succ_ctor,
                    n_ty,
                    dapp_typed(dec_mk, u0, c_mk),
                  )
                })
              })
            }),
          ],
          [],
          [],
          b0,
          dlevel,
        )
      })
    })
  })
  let f_a = eval_inductive_elim(
    n_spec,
    (_, av) => DVPi(n_ty, bv => dec_ty(av, bv)),
    [zero_fn, succ_fn],
    [],
    [],
    a,
    dlevel,
  )
  let c_ab = nat_s_code_value(a, b, dlevel)
  dapp_typed(dapp_typed(f_a, b, n_ty), c, c_ab)
}

///|
fn nat_s_decode_refl_value(a : DValue, dlevel : Int32) -> DValue {
  let n_spec = nat_schema()
  let n_ty = DVInductive(n_spec, [], [])
  let n0 = DVIntro(n_spec, 0, [], [])
  let succ_ctor = DVLam(v => DVIntro(n_spec, 1, [], [v]))
  eval_inductive_elim(
    n_spec,
    (_, av) => {
      let loop_av = DVPathTy(_ => n_ty, av, av)
      DVPathTy(
        _ => loop_av,
        nat_s_decode_value(av, av, nat_s_code_refl_value(av, dlevel), dlevel),
        dpath_refl_value(av),
      )
    },
    [
      dpath_refl_value(dpath_refl_value(n0)),
      DVLam(_m => {
        DVLam(ih => {
          DVPathLam(t => dpath_cong_value(succ_ctor, n_ty, dapp_dim(ih, t)))
        })
      }),
    ],
    [],
    [],
    a,
    dlevel,
  )
}

///|
fn integer_eq_code_value(x : DValue, y : DValue, dlevel : Int32) -> DValue {
  let z_spec = integer_schema()
  let emp = empty_inductive_type_value()
  eval_inductive_elim(
    z_spec,
    (_, _) => DVUniv(0),
    [
      eval_inductive_elim(
        z_spec,
        (_, _) => DVUniv(0),
        [DVUnitTy, DVLam(_ => emp), DVLam(_ => emp)],
        [],
        [],
        y,
        dlevel,
      ),
      DVLam(a => {
        eval_inductive_elim(
          z_spec,
          (_, _) => DVUniv(0),
          [emp, DVLam(b => nat_s_code_value(a, b, dlevel)), DVLam(_ => emp)],
          [],
          [],
          y,
          dlevel,
        )
      }),
      DVLam(a => {
        eval_inductive_elim(
          z_spec,
          (_, _) => DVUniv(0),
          [emp, DVLam(_ => emp), DVLam(b => nat_s_code_value(a, b, dlevel))],
          [],
          [],
          y,
          dlevel,
        )
      }),
    ],
    [],
    [],
    x,
    dlevel,
  )
}

///|
fn integer_eq_code_refl_value(x : DValue, dlevel : Int32) -> DValue {
  eval_inductive_elim(
    integer_schema(),
    (_, xv) => integer_eq_code_value(xv, xv, dlevel),
    [
      DVUnit,
      DVLam(a => nat_s_code_refl_value(a, dlevel)),
      DVLam(a => nat_s_code_refl_value(a, dlevel)),
    ],
    [],
    [],
    x,
    dlevel,
  )
}

///|
fn integer_diag_code_is_prop_value(
  x : DValue,
  u : DValue,
  v : DValue,
  dlevel : Int32,
) -> DValue {
  let c_xx = integer_eq_code_value(x, x, dlevel)
  let unit_prop = DVLam(_ => DVLam(_ => dpath_refl_value(DVUnit)))
  let fn_x = eval_inductive_elim(
    integer_schema(),
    (_, xv) => {
      let c = integer_eq_code_value(xv, xv, dlevel)
      DVPi(c, u0 => DVPi(c, v0 => DVPathTy(_ => c, u0, v0)))
    },
    [
      unit_prop,
      DVLam(a => {
        DVLam(u0 => DVLam(v0 => nat_s_diag_code_is_prop_value(a, u0, v0, dlevel)))
      }),
      DVLam(a => {
        DVLam(u0 => DVLam(v0 => nat_s_diag_code_is_prop_value(a, u0, v0, dlevel)))
      }),
    ],
    [],
    [],
    x,
    dlevel,
  )
  dapp_typed(dapp_typed(fn_x, u, c_xx), v, c_xx)
}

///|
fn integer_eq_decode_value(
  x : DValue,
  y : DValue,
  c : DValue,
  dlevel : Int32,
) -> DValue {
  let z_spec = integer_schema()
  let z_ty = integer_type_value()
  let n_ty = DVInductive(nat_schema(), [], [])
  let z0 = integer_value(0)
  let pos_ctor = DVLam(v => DVIntro(z_spec, 1, [], [v]))
  let neg_ctor = DVLam(v => DVIntro(z_spec, 2, [], [v]))
  let dec_ty = (xv : DValue, yv : DValue) => {
    DVPi(integer_eq_code_value(xv, yv, dlevel), _ => DVPathTy(_ => z_ty, xv, yv))
  }
  let f_xy = eval_inductive_elim(
    z_spec,
    (_, xv) => dec_ty(xv, y),
    [
      eval_inductive_elim(
        z_spec,
        (_, yv) => dec_ty(z0, yv),
        [
          DVLam(_ => dpath_refl_value(z0)),
          DVLam(b => {
            DVLam(u0 => {
              empty_inductive_elim_value(
                DVPathTy(_ => z_ty, z0, DVIntro(z_spec, 1, [], [b])),
                u0,
                dlevel,
              )
            })
          }),
          DVLam(b => {
            DVLam(u0 => {
              empty_inductive_elim_value(
                DVPathTy(_ => z_ty, z0, DVIntro(z_spec, 2, [], [b])),
                u0,
                dlevel,
              )
            })
          }),
        ],
        [],
        [],
        y,
        dlevel,
      ),
      DVLam(a => {
        let pa = DVIntro(z_spec, 1, [], [a])
        eval_inductive_elim(
          z_spec,
          (_, yv) => dec_ty(pa, yv),
          [
            DVLam(u0 => {
              empty_inductive_elim_value(DVPathTy(_ => z_ty, pa, z0), u0, dlevel)
            }),
            DVLam(b => {
              DVLam(u0 => {
                dpath_cong_value(
                  pos_ctor,
                  n_ty,
                  nat_s_decode_value(a, b, u0, dlevel),
                )
              })
            }),
            DVLam(b => {
              DVLam(u0 => {
                empty_inductive_elim_value(
                  DVPathTy(_ => z_ty, pa, DVIntro(z_spec, 2, [], [b])),
                  u0,
                  dlevel,
                )
              })
            }),
          ],
          [],
          [],
          y,
          dlevel,
        )
      }),
      DVLam(a => {
        let na = DVIntro(z_spec, 2, [], [a])
        eval_inductive_elim(
          z_spec,
          (_, yv) => dec_ty(na, yv),
          [
            DVLam(u0 => {
              empty_inductive_elim_value(DVPathTy(_ => z_ty, na, z0), u0, dlevel)
            }),
            DVLam(b => {
              DVLam(u0 => {
                empty_inductive_elim_value(
                  DVPathTy(_ => z_ty, na, DVIntro(z_spec, 1, [], [b])),
                  u0,
                  dlevel,
                )
              })
            }),
            DVLam(b => {
              DVLam(u0 => {
                dpath_cong_value(
                  neg_ctor,
                  n_ty,
                  nat_s_decode_value(a, b, u0, dlevel),
                )
              })
            }),
          ],
          [],
          [],
          y,
          dlevel,
        )
      }),
    ],
    [],
    [],
    x,
    dlevel,
  )
  dapp_typed(f_xy, c, integer_eq_code_value(x, y, dlevel))
}

///|
fn integer_eq_decode_refl_value(x : DValue, dlevel : Int32) -> DValue {
  let z_spec = integer_schema()
  let z_ty = integer_type_value()
  let n_ty = DVInductive(nat_schema(), [], [])
  let pos_ctor = DVLam(v => DVIntro(z_spec, 1, [], [v]))
  let neg_ctor = DVLam(v => DVIntro(z_spec, 2, [], [v]))
  let z0 = integer_value(0)
  eval_inductive_elim(
    z_spec,
    (_, xv) => {
      let loop_xv = DVPathTy(_ => z_ty, xv, xv)
      DVPathTy(
        _ => loop_xv,
        integer_eq_decode_value(
          xv,
          xv,
          integer_eq_code_refl_value(xv, dlevel),
          dlevel,
        ),
        dpath_refl_value(xv),
      )
    },
    [
      dpath_refl_value(dpath_refl_value(z0)),
      DVLam(a => {
        let nr = nat_s_decode_refl_value(a, dlevel)
        DVPathLam(t => dpath_cong_value(pos_ctor, n_ty, dapp_dim(nr, t)))
      }),
      DVLam(a => {
        let nr = nat_s_decode_refl_value(a, dlevel)
        DVPathLam(t => dpath_cong_value(neg_ctor, n_ty, dapp_dim(nr, t)))
      }),
    ],
    [],
    [],
    x,
    dlevel,
  )
}

///|
fn integer_loop_trivial_value(
  x : DValue,
  p0 : DValue,
  dlevel : Int32,
) -> DValue {
  let z_ty = integer_type_value()
  let encode_at = (r1 : DValue) => {
    subst_value(
      w => integer_eq_code_value(x, w, dlevel),
      r1,
      integer_eq_code_refl_value(x, dlevel),
      dlevel + 2,
    )
  }
  let c_xx = integer_eq_code_value(x, x, dlevel)
  let cr_x = integer_eq_code_refl_value(x, dlevel)
  let coe_code = dpath_sym_value(
    transport_pathp_value(_ => c_xx, cr_x, dlevel + 2),
  )
  let step_coe : DValue = DVPathLam(t => {
    integer_eq_decode_value(x, x, dapp_dim(coe_code, t), dlevel)
  })
  let dr_x = integer_eq_decode_refl_value(x, dlevel)
  let base_retr = dpath_trans_value(
    DVPathTy(_ => z_ty, x, x),
    step_coe,
    dr_x,
    dlevel + 4,
  )
  let rp0 = dj_singleton_elim_value(
    (y1, r1) => {
      let eq_ty = DVPathTy(_ => z_ty, x, y1)
      DVPathTy(
        _ => eq_ty,
        integer_eq_decode_value(x, y1, encode_at(r1), dlevel),
        r1,
      )
    },
    base_retr,
    p0,
    dlevel + 6,
  )
  let code_eq = integer_diag_code_is_prop_value(
    x,
    encode_at(p0),
    cr_x,
    dlevel,
  )
  DVPathLam(t => {
    DVPathLam(i => {
      let base_z = dapp_dim(
        integer_eq_decode_value(x, x, dapp_dim(code_eq, t), dlevel),
        i,
      )
      let sys = dsystem_of([
        tube_branch(face_simplify(FEq0(t)), k => dapp_dim(dapp_dim(rp0, k), i)),
        tube_branch(face_simplify(FEq1(t)), k => dapp_dim(dapp_dim(dr_x, k), i)),
        tube_branch(face_simplify(FEq0(i)), _ => x),
        tube_branch(face_simplify(FEq1(i)), _ => x),
      ])
      hcomp_value(z_ty, sys, base_z, dlevel + 8)
    })
  })
}

///|
/// Internal Hedberg / Axiom-K proof that `IntegerS` is an h-Set:
/// contracts `(y, q)` via singleton elimination to diagonal self-loops
/// `p0 : Path IntegerS x x`, then contracts `p0` to `refl_x` via 1-variable
/// diagonal equality-code propositionality and one 4-face composition cube.
pub fn integer_is_set_value(
  x : DValue,
  y : DValue,
  p : DValue,
  q : DValue,
  dlevel : Int32,
) -> DValue {
  let z_ty = integer_type_value()
  let fam = (y1 : DValue, q1 : DValue) => {
    let p_ty = DVPathTy(_ => z_ty, x, y1)
    DVPi(p_ty, p1 => DVPathTy(_ => p_ty, p1, q1))
  }
  let refl_case = DVLam(p0 => integer_loop_trivial_value(x, p0, dlevel + 2))
  let fn_at_q = dj_singleton_elim_value(fam, refl_case, q, dlevel + 1)
  dapp_typed(fn_at_q, p, DVPathTy(_ => z_ty, x, y))
}

///|
/// First-class full bidirectional 0-truncated fundamental group isomorphism
///   `Equiv ‖Omega(S^1, base)‖_0 IntegerS` (`pi_1(S^1) ≃ Z`),
/// obtained by instantiating the universal 0-truncation equivalence theorem
/// `set_trunc_equiv_of_equiv_set_value` with `circle_loop_space_equiv_integer_value`
/// and `integer_is_set_value`.
pub fn pi1_set_circle_equiv_integer_value(dlevel : Int32) -> DValue {
  set_trunc_equiv_of_equiv_set_value(
    circle_loop_space_type_value(),
    integer_type_value(),
    circle_loop_space_equiv_integer_value(dlevel),
    (a, b, p1, p2) => integer_is_set_value(a, b, p1, p2, dlevel + 2),
    dlevel,
  )
}
