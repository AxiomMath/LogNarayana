/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module
public import LogNarayana.Narayana.Polynomials.Defs
public import LogNarayana.AuxiliaryDefinitions

/-!
# The Narayana transform

The definitions documented here are stated in `LogNarayana.Definitions` and
`LogNarayana.AuxiliaryDefinitions`, which this module imports.

For a type `σ` of variables, the Narayana transform is the `ℝ`-linear map
`𝒩 : ℝ[z_σ] → ℝ[x]` sending a monomial `z^α` to `∏_{i} Ñ_{α_i}(x)`, where `Ñ_m` is the shifted
Narayana polynomial `shiftedNarayanaPolynomial m`. Thus
`𝒩(F)(x) = ∑_{α ∈ supp F} [z^α]F · ∏_{i ∈ σ} Ñ_{α_i}(x)`.

## Main definitions

* `MvPolynomial.narayanaTransform σ` : the Narayana transform `MvPolynomial σ ℝ →ₗ[ℝ] ℝ[X]`.

## Implementation notes

The transform is defined as the linear map `Basis.constr` determined by its values on the
monomial basis `MvPolynomial.basisMonomials`, so linearity is built in and its value on a monomial
is `Basis.constr_basis`. The product over the variables is the product over the
support of the exponent `α` (`Finsupp.prod`); since `Ñ_0 = 1` this equals the product over all of
`σ` when `σ` is finite, and it makes sense for an arbitrary (possibly infinite) set of variables,
as in the paper's eq. (1.5).

## References

* [LogNarayana], eq. (1.5) and Section 6.
-/

namespace MvPolynomial

end MvPolynomial
