/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module
public import LogNarayana.Lorentzian.MConvex.Basic
public import LogNarayana.Lorentzian.MConvex.Defs
public import LogNarayana.Lorentzian.PositiveIndex.Defs
public import LogNarayana.AuxiliaryDefinitions

/-!
# Hessians and Lorentzian polynomials

The definitions documented here are stated in `LogNarayana.Definitions` and
`LogNarayana.AuxiliaryDefinitions`, which this module imports.

For a polynomial `g ∈ R[z_i : i ∈ σ]`, its Hessian at the origin is the `σ × σ` matrix
`Hess(g)` with entries `Hess(g)_{ij} = [z^0] ∂^(e_i + e_j) g`, the matrix of second partial
derivatives of `g` evaluated at `z = 0`. It depends only on the degree-two part of `g`: it is
the symmetric matrix of the quadratic form `2 · g₂`.

A polynomial `f ∈ ℝ[z_i : i ∈ σ]` is *Lorentzian* if `f = 0`, or `f` is homogeneous of some
degree `d` with nonnegative coefficients and either `d ≤ 1`, or `d ≥ 2`, the support of `f` is
M-convex, and for every multi-index `α` with `|α| = d - 2` the Hessian `Hess(∂^α f)` of the
quadratic form `∂^α f` has at most one positive eigenvalue. This is the characterization of
Lorentzian polynomials of Brändén–Huh [BH, Theorem 2.25], together with the conventions that
the zero polynomial and the nonnegative constants and linear forms are Lorentzian.

## Main definitions

* `MvPolynomial.hessianAtZero g`: the matrix `Hess(g) : Matrix σ σ R`.
* `MvPolynomial.IsLorentzian`: the polynomial `f` is Lorentzian.

## Implementation notes

The entries of `hessianAtZero g` are the constant coefficients (`MvPolynomial.constantCoeff`)
of the iterated partial derivatives
`MvPolynomial.iteratedPDeriv (Finsupp.single i 1 + Finsupp.single j 1) g`. The Hessian is
defined over an arbitrary commutative semiring `R` and index type `σ`; for `R = ℝ` and finite
`σ` it is the paper's matrix.

The paper works over `ℝ`; `IsLorentzian` is stated over any partially ordered commutative
ring, the generality of `Matrix.posIndex`. The variable type `σ` is finite, so that the Hessian
is a square matrix with a positive index. The support `supp f` is `MvPolynomial.support f`,
viewed as a set of multi-indices; `|α|` is `Finsupp.degree α`, and the condition
`|α| = d - 2` is only imposed when `2 ≤ d`, so the truncated subtraction is exact.

## References

* [BH] P. Brändén, J. Huh, *Lorentzian polynomials*, Ann. of Math. 192 (2020), Theorem 2.25.
-/

namespace MvPolynomial

section Hessian

variable {σ R : Type*} [CommSemiring R]

end Hessian

section Lorentzian

variable {σ R : Type*} [Fintype σ] [CommRing R] [PartialOrder R]

end Lorentzian

end MvPolynomial
