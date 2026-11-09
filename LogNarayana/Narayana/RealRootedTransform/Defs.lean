/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib
public import LogNarayana.Attr
public import LogNarayana.Narayana.SignedAppell.Defs
public import LogNarayana.Narayana.Polynomials.Defs
public import LogNarayana.AuxiliaryDefinitions

/-!
# The diagonal, gamma and deformed Narayana transforms

The definitions documented here are stated in `LogNarayana.Definitions` and
`LogNarayana.AuxiliaryDefinitions`, which this module imports.

Three linear maps from polynomials in the variables `z_i`, `i ∈ σ`, to univariate polynomials,
each sending a monomial `z^α` to a product over the variables of a univariate polynomial indexed
by `α_i`:

* the *diagonal Appell transform* `𝓗 : R[z_σ] → R[t]`, `z^α ↦ ∏_i η_{α_i}(t)`, with `η_m` the
  signed Appell polynomial;
* the *gamma transform* `Γ : R[z_σ] → R[u]`, `z^α ↦ ∏_i M_{α_i}(u)`, with
  `M_m(u) = ∑_{j=0}^{⌊m/2⌋} C_j (m choose 2j) u^j`;
* the *deformed Narayana transform* `𝒩_λ : R[z_σ] → R[x]`, `z^α ↦ ∏_i Q_{α_i}(1 + x, λ x)`.

## Main definitions

* `MvPolynomial.appellDiagonal σ R` : the diagonal Appell transform.
* `MvPolynomial.gammaTransform σ R` : the gamma transform.
* `MvPolynomial.deformedNarayanaTransform R lam σ` : the deformed Narayana transform.

## Implementation notes

Each transform is the linear map `Basis.constr` determined by its values on the monomial basis
`MvPolynomial.basisMonomials`, so linearity is built in and its value on a monomial is
`Basis.constr_basis`. The product over the variables is the product over the support of the
exponent (`Finsupp.prod`); since `η_0 = M_0 = Q_0 = 1`, this agrees with the product over all of
`σ` when `σ` is finite, and needs no finiteness of `σ`. The paper works over `ℝ`; the
transforms are defined over any commutative ring (`𝓗`) or semiring (`Γ`, `𝒩_λ`).

## References

* [LogNarayana], Section 6 (the diagonal and gamma transforms).
-/

namespace MvPolynomial

open Polynomial

end MvPolynomial
