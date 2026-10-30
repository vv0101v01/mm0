///|
// Generalized eigenspaces, Jordan chains, and primary spectral
// projectors for exact rational matrices.
//
// For a repeated rational eigenvalue λ of algebraic multiplicity m,
// the generalized eigenspace is `ker (A − λI)^m`; its Jordan block
// sizes are read from the nullity sequence of the powers of
// `A − λI` (the Weyr characteristic), and Jordan chains are built by
// choosing quotient representatives in
// `ker N^k / ker N^(k−1)` level by level.  The projector onto a
// primary component `ker f(A)` for a coprime factorization
// `χ_A = f·g` is the CRT idempotent `(t·g)(A)` from a Bezout identity
// `s·f + t·g = 1`, which is the repeated-root replacement for the
// distinct-eigenvalue Lagrange projector formula.

///|
pub struct QGeneralizedEigenspace {
  eigenvalue : Rat
  algebraic_multiplicity : Int32
  geometric_multiplicity : Int32
  index : Int32
  nullities : Array[Int32]
  block_sizes : Array[Int32]
  basis : Array[QVec]
}

///|
fn block_sizes_of_nullities(nullities : Array[Int32]) -> Array[Int32] {
  let sizes : Array[Int32] = []
  let m = nullities.length()
  // w[k] = dim ker N^k − dim ker N^(k−1) = #blocks of size ≥ k.
  let w : Array[Int32] = []
  let mut prev = 0
  for i in 0..<m {
    w.push(nullities[i] - prev)
    prev = nullities[i]
  }
  for s = m; s >= 1; s = s - 1 {
    let next_w = if s < m { w[s] } else { 0 }
    let exact = w[s - 1] - next_w
    for _i in 0..<exact {
      sizes.push(s)
    }
  }
  sizes
}

///|
pub fn qmat_eigenvalue_multiplicity(a : QMat, lambda : Rat) -> Int32 {
  qpoly_root_multiplicity(qmat_charpoly(a), lambda)
}

///|
fn qmat_shifted(a : QMat, lambda : Rat) -> QMat {
  qmat_sub(a, qmat_scalar(lambda, a.n))
}

///|
/// Nullities of `(A − λI)^k` for `k = 1, 2, …` until the algebraic
/// multiplicity is reached.
pub fn qmat_eigen_nullities(a : QMat, lambda : Rat) -> Array[Int32] {
  let alg = qmat_eigenvalue_multiplicity(a, lambda)
  let out : Array[Int32] = []
  if alg == 0 {
    return out
  }
  let shifted = qmat_shifted(a, lambda)
  let mut power = qmat_identity(a.n)
  for _k in 0..<a.n {
    power = qmat_mul(power, shifted)
    let nullity = qmat_nullity(power)
    out.push(nullity)
    if nullity >= alg {
      break
    }
  }
  out
}

///|
pub fn qmat_generalized_eigenspace(
  a : QMat,
  lambda : Rat,
) -> QGeneralizedEigenspace {
  let alg = qmat_eigenvalue_multiplicity(a, lambda)
  if alg == 0 {
    return QGeneralizedEigenspace::{
      eigenvalue: lambda,
      algebraic_multiplicity: 0,
      geometric_multiplicity: 0,
      index: 0,
      nullities: [],
      block_sizes: [],
      basis: [],
    }
  }
  let nullities = qmat_eigen_nullities(a, lambda)
  let index = nullities.length()
  let power = qmat_pow(qmat_shifted(a, lambda), index)
  QGeneralizedEigenspace::{
    eigenvalue: lambda,
    algebraic_multiplicity: alg,
    geometric_multiplicity: if index > 0 {
      nullities[0]
    } else {
      0
    },
    index,
    nullities,
    block_sizes: block_sizes_of_nullities(nullities),
    basis: qmat_nullspace(power),
  }
}

///|
pub fn qmat_Jordan_block_sizes(a : QMat, lambda : Rat) -> Array[Int32] {
  qmat_generalized_eigenspace(a, lambda).block_sizes
}

///|
pub fn qmat_diagonalizable_at(a : QMat, lambda : Rat) -> Bool {
  let g = qmat_generalized_eigenspace(a, lambda)
  g.geometric_multiplicity == g.algebraic_multiplicity
}

///|
fn qvec_copy_all(vecs : Array[QVec]) -> Array[QVec] {
  let out : Array[QVec] = []
  for i in 0..<vecs.length() {
    out.push(vecs[i])
  }
  out
}

///|
fn quotient_representatives(
  kernel : Array[QVec],
  lower_kernel : Array[QVec],
  existing : Array[QVec],
) -> Array[QVec] {
  let forbidden = qvec_copy_all(lower_kernel)
  for i in 0..<existing.length() {
    forbidden.push(existing[i])
  }
  let chosen : Array[QVec] = []
  for i in 0..<kernel.length() {
    let span_test = qvec_copy_all(forbidden)
    for j in 0..<chosen.length() {
      span_test.push(chosen[j])
    }
    if !qvec_in_span(span_test, kernel[i]) {
      chosen.push(kernel[i])
    }
  }
  chosen
}

///|
/// Jordan chains for `lambda`, each listed from its head (a
/// generalized eigenvector of maximal height for that chain) down to
/// its eigenvector.
pub fn qmat_Jordan_chains(a : QMat, lambda : Rat) -> Array[Array[QVec]] {
  let info = qmat_generalized_eigenspace(a, lambda)
  let chains : Array[Array[QVec]] = []
  if info.index == 0 {
    return chains
  }
  let shifted = qmat_shifted(a, lambda)
  // kernels[k] is a basis of ker N^k; kernels[0] is empty.
  let kernels : Array[Array[QVec]] = [[]]
  let mut power = qmat_identity(a.n)
  for _k in 0..<info.index {
    power = qmat_mul(power, shifted)
    kernels.push(qmat_nullspace(power))
  }
  let m = info.index
  let heads = quotient_representatives(kernels[m], kernels[m - 1], [])
  for i in 0..<heads.length() {
    chains.push([heads[i]])
  }
  for k = m - 1; k >= 1; k = k - 1 {
    // Push every existing chain one step down by N.
    for c in 0..<chains.length() {
      let chain = chains[c]
      chain.push(qmat_vec(shifted, chain[chain.length() - 1]))
    }
    let tails : Array[QVec] = []
    for c in 0..<chains.length() {
      tails.push(chains[c][chains[c].length() - 1])
    }
    let fresh = quotient_representatives(kernels[k], kernels[k - 1], tails)
    for i in 0..<fresh.length() {
      chains.push([fresh[i]])
    }
  }
  chains
}

///|
pub struct QJordanDecomposition {
  p : QMat
  j : QMat
  eigenvalues : Array[Rat]
  block_sizes : Array[Array[Int32]]
}

///|
/// An exact Jordan decomposition `A·P = P·J` over Q for the given
/// distinct rational eigenvalues, when they exhaust the spectrum.
pub fn qmat_Jordan_decomposition(
  a : QMat,
  eigenvalues : Array[Rat],
) -> QJordanDecomposition? {
  let columns : Array[QVec] = []
  let all_blocks : Array[Array[Int32]] = []
  let jordan = qmat_zero(a.n)
  let mut offset = 0
  for e in 0..<eigenvalues.length() {
    let lambda = eigenvalues[e]
    let chains = qmat_Jordan_chains(a, lambda)
    let sizes : Array[Int32] = []
    for c in 0..<chains.length() {
      let chain = chains[c]
      sizes.push(chain.length())
      // Basis order: eigenvector first, then up the chain.  This
      // gives ones on the superdiagonal of each Jordan block.
      for idx = chain.length() - 1; idx >= 0; idx = idx - 1 {
        columns.push(chain[idx])
      }
      for t in 0..<chain.length() {
        jordan.rows[offset + t][offset + t] = lambda
        if t + 1 < chain.length() {
          jordan.rows[offset + t][offset + t + 1] = rat_one()
        }
      }
      offset = offset + chain.length()
    }
    all_blocks.push(sizes)
  }
  if offset != a.n || columns.length() != a.n {
    return None
  }
  let p = qmat_from_columns(columns)
  if qmat_rank(p) != a.n {
    return None
  }
  if !qmat_eq(qmat_mul(a, p), qmat_mul(p, jordan)) {
    return None
  }
  Some(QJordanDecomposition::{
    p,
    j: jordan,
    eigenvalues,
    block_sizes: all_blocks,
  })
}

///|
/// Jordan decomposition with eigenvalues found by factoring the
/// characteristic polynomial over Q; fails when a nonrational
/// irreducible factor remains.
pub fn qmat_Jordan_decomposition_auto(a : QMat) -> QJordanDecomposition? {
  let factored = qpoly_factor_rational_roots(qmat_charpoly(a))
  if qpoly_degree(factored.residual) > 0 {
    return None
  }
  qmat_Jordan_decomposition(a, factored.roots)
}

///|
pub fn qmat_is_diagonalizable_rational(a : QMat) -> Bool {
  match qmat_Jordan_decomposition_auto(a) {
    Some(dec) => {
      for e in 0..<dec.block_sizes.length() {
        for i in 0..<dec.block_sizes[e].length() {
          if dec.block_sizes[e][i] != 1 {
            return false
          }
        }
      }
      true
    }
    None => false
  }
}

// ---------------------------------------------------------------------------
// Primary decomposition and generalized spectral projectors
// ---------------------------------------------------------------------------

///|
pub struct QPrimaryProjector {
  factor : QPoly
  cofactor : QPoly
  polynomial : QPoly
  projector : QMat
  complement : QMat
}

///|
/// The projector onto the primary component `ker f(A)` along
/// `ker g(A)`, for a factorization `χ_A = f·g` with coprime factors.
/// From `s·f + t·g = 1`, the projector is `(t·g)(A)`: it is 1 modulo
/// `f` and 0 modulo `g`.
pub fn qmat_primary_projector(a : QMat, factor : QPoly) -> QPrimaryProjector? {
  if qpoly_degree(factor) <= 0 {
    return None
  }
  let chi = qmat_charpoly(a)
  let f = qpoly_monic(factor)
  let dm = qpoly_divmod(chi, f)
  if !qpoly_is_zero(dm.remainder) {
    return None
  }
  let g = qpoly_monic(dm.quotient)
  let ext = qpoly_extgcd(f, g)
  if !qpoly_is_one(ext.g) {
    return None
  }
  let polynomial = qpoly_mod(qpoly_mul(ext.t, g), chi)
  let projector = qmat_poly_eval(polynomial, a)
  Some(QPrimaryProjector::{
    factor: f,
    cofactor: g,
    polynomial,
    projector,
    complement: qmat_sub(qmat_identity(a.n), projector),
  })
}

///|
/// The generalized spectral projector for a (possibly repeated)
/// rational eigenvalue: the primary projector for `(X − λ)^m`, where
/// `m` is the algebraic multiplicity.
pub fn qmat_generalized_projector(a : QMat, lambda : Rat) -> QPrimaryProjector? {
  let m = qmat_eigenvalue_multiplicity(a, lambda)
  if m == 0 {
    return None
  }
  qmat_primary_projector(a, qpoly_pow(qpoly_root_factor(lambda), m))
}

///|
/// A basis of the primary subspace `ker f(A)`.
pub fn qmat_primary_subspace_basis(a : QMat, factor : QPoly) -> Array[QVec] {
  qmat_nullspace(qmat_poly_eval(factor, a))
}

///|
/// A basis of the column space of a rational matrix.
pub fn qmat_column_basis(a : QMat) -> Array[QVec] {
  let cols : Array[QVec] = []
  let ncols = if a.rows.length() == 0 { 0 } else { a.rows[0].length() }
  for j in 0..<ncols {
    let col : QVec = []
    for i in 0..<a.rows.length() {
      col.push(a.rows[i][j])
    }
    cols.push(col)
  }
  qvec_independent_subset(cols)
}

///|
pub struct QRationalSpectrum {
  eigenvalues : Array[Rat]
  multiplicities : Array[Int32]
  residual : QPoly
}

///|
/// The rational part of the spectrum, with the remaining
/// no-rational-root factor of the characteristic polynomial.
pub fn qmat_rational_spectrum(a : QMat) -> QRationalSpectrum {
  let factored = qpoly_factor_rational_roots(qmat_charpoly(a))
  QRationalSpectrum::{
    eigenvalues: factored.roots,
    multiplicities: factored.multiplicities,
    residual: factored.residual,
  }
}
