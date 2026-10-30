///|
pub fn d_nat_lit(n : Int32) -> DTerm {
  if n <= 0 {
    DNatZero
  } else {
    DSucc(d_nat_lit(n - 1))
  }
}

///|
pub fn dv_nat_lit(n : Int32) -> DValue {
  if n <= 0 {
    DVZeroNat
  } else {
    DVSucc(dv_nat_lit(n - 1))
  }
}

///|
fn dv_is_nat(v : DValue, n : Int32) -> Bool {
  conv_at(0, 0, DVNatTy, v, dv_nat_lit(n))
}

///|
fn dv_is_bool_dep(v : DValue, b : Bool) -> Bool {
  conv_at(0, 0, DVBoolTy, v, DVBool(b))
}

///|
// Capture-avoiding variable maps for the dependent cubical AST.
//
// The map below is the single place which knows the term-binder
// structure of every AST constructor.  Dimension binders do not bind
// term variables.  The motives of the primitive Bool/Nat/List/Circle/
// Torus eliminators are bodies under one term binder; the motives of
// generated eliminators are ordinary function terms.  Embedded
// schema descriptors are closed schema-local data and are not
// traversed as ambient terms.

///|
fn dterm_map_vars_list(
  terms : Array[DTerm],
  depth : Int32,
  f : (Int32, Int32) -> DTerm,
) -> Array[DTerm] {
  let out : Array[DTerm] = []
  for i in 0..<terms.length() {
    out.push(dterm_map_vars_at(terms[i], depth, f))
  }
  out
}

///|
fn dterm_map_vars_at(
  t : DTerm,
  depth : Int32,
  f : (Int32, Int32) -> DTerm,
) -> DTerm {
  match t {
    DTVar(i) => f(i, depth)
    DPi(a, b) =>
      DPi(dterm_map_vars_at(a, depth, f), dterm_map_vars_at(b, depth + 1, f))
    DSigma(a, b) =>
      DSigma(dterm_map_vars_at(a, depth, f), dterm_map_vars_at(b, depth + 1, f))
    DLam(a, b) =>
      DLam(dterm_map_vars_at(a, depth, f), dterm_map_vars_at(b, depth + 1, f))
    DApp(x, y) =>
      DApp(dterm_map_vars_at(x, depth, f), dterm_map_vars_at(y, depth, f))
    DPair(x, y) =>
      DPair(dterm_map_vars_at(x, depth, f), dterm_map_vars_at(y, depth, f))
    DFst(x) => DFst(dterm_map_vars_at(x, depth, f))
    DSnd(x) => DSnd(dterm_map_vars_at(x, depth, f))
    DBoolElim(m, x, y, z) =>
      DBoolElim(
        dterm_map_vars_at(m, depth + 1, f),
        dterm_map_vars_at(x, depth, f),
        dterm_map_vars_at(y, depth, f),
        dterm_map_vars_at(z, depth, f),
      )
    DAnn(x, y) =>
      DAnn(dterm_map_vars_at(x, depth, f), dterm_map_vars_at(y, depth, f))
    DPartial(branches) => {
      let out : Array[DFaceTerm] = []
      for i in 0..<branches.length() {
        out.push(
          d_face_term(
            branches[i].face,
            dterm_map_vars_at(branches[i].body, depth, f),
          ),
        )
      }
      DPartial(out)
    }
    DPathP(line, l, r) =>
      DPathP(
        dterm_map_vars_at(line, depth, f),
        dterm_map_vars_at(l, depth, f),
        dterm_map_vars_at(r, depth, f),
      )
    DPath(a, l, r) =>
      DPath(
        dterm_map_vars_at(a, depth, f),
        dterm_map_vars_at(l, depth, f),
        dterm_map_vars_at(r, depth, f),
      )
    DLamDim(body) => DLamDim(dterm_map_vars_at(body, depth, f))
    DAppDim(x, r) => DAppDim(dterm_map_vars_at(x, depth, f), r)
    DCoe(line, r, s, v) =>
      DCoe(
        dterm_map_vars_at(line, depth, f),
        r,
        s,
        dterm_map_vars_at(v, depth, f),
      )
    DComp(line, tubes, base) =>
      DComp(
        dterm_map_vars_at(line, depth, f),
        dterm_map_tubes(tubes, depth, f),
        dterm_map_vars_at(base, depth, f),
      )
    DHComp(a, tubes, base) =>
      DHComp(
        dterm_map_vars_at(a, depth, f),
        dterm_map_tubes(tubes, depth, f),
        dterm_map_vars_at(base, depth, f),
      )
    DHFill(a, tubes, base, r) =>
      DHFill(
        dterm_map_vars_at(a, depth, f),
        dterm_map_tubes(tubes, depth, f),
        dterm_map_vars_at(base, depth, f),
        r,
      )
    DSucc(x) => DSucc(dterm_map_vars_at(x, depth, f))
    DNatElim(m, x, y, z) =>
      DNatElim(
        dterm_map_vars_at(m, depth + 1, f),
        dterm_map_vars_at(x, depth, f),
        dterm_map_vars_at(y, depth, f),
        dterm_map_vars_at(z, depth, f),
      )
    DListTy(a) => DListTy(dterm_map_vars_at(a, depth, f))
    DCons(x, y) =>
      DCons(dterm_map_vars_at(x, depth, f), dterm_map_vars_at(y, depth, f))
    DListElim(m, x, y, z) =>
      DListElim(
        dterm_map_vars_at(m, depth + 1, f),
        dterm_map_vars_at(x, depth, f),
        dterm_map_vars_at(y, depth, f),
        dterm_map_vars_at(z, depth, f),
      )
    DCircleElim(m, x, y, z) =>
      DCircleElim(
        dterm_map_vars_at(m, depth + 1, f),
        dterm_map_vars_at(x, depth, f),
        dterm_map_vars_at(y, depth, f),
        dterm_map_vars_at(z, depth, f),
      )
    DTorusElim(m, x, z) =>
      DTorusElim(
        dterm_map_vars_at(m, depth + 1, f),
        dterm_map_vars_at(x, depth, f),
        dterm_map_vars_at(z, depth, f),
      )
    DInductive(spec, args) =>
      DInductive(spec, dterm_map_vars_list(args, depth, f))
    DIntro(spec, ctor, params, args) =>
      DIntro(
        spec,
        ctor,
        dterm_map_vars_list(params, depth, f),
        dterm_map_vars_list(args, depth, f),
      )
    DInductiveElim(spec, m, cases, params, indices, scrut) =>
      DInductiveElim(
        spec,
        dterm_map_vars_at(m, depth, f),
        dterm_map_vars_list(cases, depth, f),
        dterm_map_vars_list(params, depth, f),
        dterm_map_vars_list(indices, depth, f),
        dterm_map_vars_at(scrut, depth, f),
      )
    DHitType(spec, args) => DHitType(spec, dterm_map_vars_list(args, depth, f))
    DHitIntro(spec, cell, params, args, dims) =>
      DHitIntro(
        spec,
        cell,
        dterm_map_vars_list(params, depth, f),
        dterm_map_vars_list(args, depth, f),
        dims,
      )
    DHitElim(spec, m, cases, params, indices, scrut) =>
      DHitElim(
        spec,
        dterm_map_vars_at(m, depth, f),
        dterm_map_vars_list(cases, depth, f),
        dterm_map_vars_list(params, depth, f),
        dterm_map_vars_list(indices, depth, f),
        dterm_map_vars_at(scrut, depth, f),
      )
    DDecode(spec, params, indices, code) =>
      DDecode(
        spec,
        dterm_map_vars_list(params, depth, f),
        dterm_map_vars_list(indices, depth, f),
        dterm_map_vars_at(code, depth, f),
      )
    DEquivTy(a, b) =>
      DEquivTy(dterm_map_vars_at(a, depth, f), dterm_map_vars_at(b, depth, f))
    DMkEquiv(a, b, fwd, bwd, sect, retr) =>
      DMkEquiv(
        dterm_map_vars_at(a, depth, f),
        dterm_map_vars_at(b, depth, f),
        dterm_map_vars_at(fwd, depth, f),
        dterm_map_vars_at(bwd, depth, f),
        dterm_map_vars_at(sect, depth, f),
        dterm_map_vars_at(retr, depth, f),
      )
    DEquivFwd(e) => DEquivFwd(dterm_map_vars_at(e, depth, f))
    DEquivBwd(e) => DEquivBwd(dterm_map_vars_at(e, depth, f))
    DEquivSect(e) => DEquivSect(dterm_map_vars_at(e, depth, f))
    DEquivRetr(e) => DEquivRetr(dterm_map_vars_at(e, depth, f))
    DGlueEquiv(base, branches) => {
      let out : Array[DEquivBranch] = []
      for i in 0..<branches.length() {
        out.push(
          d_equiv_branch(
            branches[i].face,
            dterm_map_vars_at(branches[i].ty, depth, f),
            dterm_map_vars_at(branches[i].equiv, depth, f),
          ),
        )
      }
      DGlueEquiv(dterm_map_vars_at(base, depth, f), out)
    }
    DUnglueEquiv(term, base, branches) => {
      let out : Array[DEquivBranch] = []
      for i in 0..<branches.length() {
        out.push(
          d_equiv_branch(
            branches[i].face,
            dterm_map_vars_at(branches[i].ty, depth, f),
            dterm_map_vars_at(branches[i].equiv, depth, f),
          ),
        )
      }
      DUnglueEquiv(
        dterm_map_vars_at(term, depth, f),
        dterm_map_vars_at(base, depth, f),
        out,
      )
    }
    DUa(e) => DUa(dterm_map_vars_at(e, depth, f))
    other => other
  }
}

///|
fn dterm_map_tubes(
  tubes : Array[DTubeTerm],
  depth : Int32,
  f : (Int32, Int32) -> DTerm,
) -> Array[DTubeTerm] {
  let out : Array[DTubeTerm] = []
  for i in 0..<tubes.length() {
    out.push(d_tube(tubes[i].face, dterm_map_vars_at(tubes[i].body, depth, f)))
  }
  out
}

///|
/// Shift free variables at or above `cutoff` by `delta`.
pub fn dterm_shift(t : DTerm, cutoff : Int32, delta : Int32) -> DTerm {
  dterm_map_vars_at(t, 0, (i, depth) => {
    if i >= cutoff + depth {
      DTVar(i + delta)
    } else {
      DTVar(i)
    }
  })
}

///|
/// Capture-avoiding substitution of one de Bruijn variable.
pub fn dterm_substitute(t : DTerm, index : Int32, replacement : DTerm) -> DTerm {
  dterm_map_vars_at(t, 0, (i, depth) => {
    if i == index + depth {
      dterm_shift(replacement, 0, depth)
    } else if i > index + depth {
      DTVar(i - 1)
    } else {
      DTVar(i)
    }
  })
}

///|
/// Immediate ambient subterms of an AST node.  Embedded schema
/// descriptors are not expanded: their internal terms have
/// schema-local scopes.
pub fn dterm_children(t : DTerm) -> Array[DTerm] {
  match t {
    DPi(a, b)
    | DSigma(a, b)
    | DLam(a, b)
    | DApp(a, b)
    | DPair(a, b)
    | DAnn(a, b)
    | DCons(a, b) => [a, b]
    DFst(a) | DSnd(a) | DLamDim(a) | DSucc(a) | DListTy(a) => [a]
    DBoolElim(a, b, c, d)
    | DNatElim(a, b, c, d)
    | DListElim(a, b, c, d)
    | DCircleElim(a, b, c, d) => [a, b, c, d]
    DPartial(branches) => {
      let out : Array[DTerm] = []
      for i in 0..<branches.length() {
        out.push(branches[i].body)
      }
      out
    }
    DPathP(a, b, c) | DPath(a, b, c) => [a, b, c]
    DAppDim(a, _) => [a]
    DCoe(a, _, _, b) => [a, b]
    DComp(a, tubes, b) | DHComp(a, tubes, b) => {
      let out = [a, b]
      for i in 0..<tubes.length() {
        out.push(tubes[i].body)
      }
      out
    }
    DHFill(a, tubes, b, _) => {
      let out = [a, b]
      for i in 0..<tubes.length() {
        out.push(tubes[i].body)
      }
      out
    }
    DTorusElim(a, b, c) => [a, b, c]
    DInductive(_, args) | DHitType(_, args) => args
    DIntro(_, _, params, args) | DHitIntro(_, _, params, args, _) => {
      let out : Array[DTerm] = []
      for i in 0..<params.length() {
        out.push(params[i])
      }
      for i in 0..<args.length() {
        out.push(args[i])
      }
      out
    }
    DInductiveElim(_, m, cases, params, indices, scrut)
    | DHitElim(_, m, cases, params, indices, scrut) => {
      let out = [m, scrut]
      for i in 0..<cases.length() {
        out.push(cases[i])
      }
      for i in 0..<params.length() {
        out.push(params[i])
      }
      for i in 0..<indices.length() {
        out.push(indices[i])
      }
      out
    }
    DEquivTy(a, b) => [a, b]
    DMkEquiv(a, b, f, g, sect, retr) => [a, b, f, g, sect, retr]
    DEquivFwd(e) | DEquivBwd(e) | DEquivSect(e) | DEquivRetr(e) | DUa(e) => [e]
    DGlueEquiv(base, branches) => {
      let out = [base]
      for i in 0..<branches.length() {
        out.push(branches[i].ty)
        out.push(branches[i].equiv)
      }
      out
    }
    DUnglueEquiv(term, base, branches) => {
      let out = [term, base]
      for i in 0..<branches.length() {
        out.push(branches[i].ty)
        out.push(branches[i].equiv)
      }
      out
    }
    DDecode(_, params, indices, code) => {
      let out = [code]
      for i in 0..<params.length() {
        out.push(params[i])
      }
      for i in 0..<indices.length() {
        out.push(indices[i])
      }
      out
    }
    _ => []
  }
}

///|
fn dterm_dim_vars_into(t : DTerm, acc : Array[Int32]) -> Unit {
  match t {
    DPartial(branches) =>
      for i in 0..<branches.length() {
        face_vars_into(branches[i].face, acc)
      }
    DAppDim(_, d) => dim_vars_into(d, acc)
    DCoe(_, r, s2, _) => {
      dim_vars_into(r, acc)
      dim_vars_into(s2, acc)
    }
    DComp(_, tubes, _) | DHComp(_, tubes, _) =>
      for i in 0..<tubes.length() {
        face_vars_into(tubes[i].face, acc)
      }
    DHFill(_, tubes, _, d) => {
      for i in 0..<tubes.length() {
        face_vars_into(tubes[i].face, acc)
      }
      dim_vars_into(d, acc)
    }
    DHitIntro(_, _, _, _, dims) =>
      for i in 0..<dims.length() {
        dim_vars_into(dims[i], acc)
      }
    DGlueEquiv(_, branches) | DUnglueEquiv(_, _, branches) =>
      for i in 0..<branches.length() {
        face_vars_into(branches[i].face, acc)
      }
    _ => ()
  }
  let children = dterm_children(t)
  for i in 0..<children.length() {
    dterm_dim_vars_into(children[i], acc)
  }
}

///|
/// Dimension variables occurring in dimension and face positions
/// of a term, sorted increasingly.  Embedded schema descriptors
/// are not expanded (their internal dimensions are schema-local,
/// as in `dterm_children`).
pub fn dterm_dim_vars(t : DTerm) -> Array[Int32] {
  let acc : Array[Int32] = []
  dterm_dim_vars_into(t, acc)
  @algebra.int_sort(acc)
}
