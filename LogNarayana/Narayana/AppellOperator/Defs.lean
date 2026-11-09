/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib
public import LogNarayana.Attr
public import LogNarayana.Narayana.SignedAppell.Defs
public import LogNarayana.AuxiliaryDefinitions

/-!
# The Appell operator

The definitions documented here are stated in `LogNarayana.Definitions` and
`LogNarayana.AuxiliaryDefinitions`, which this module imports.

The *Appell operator* is the linear map `𝔄` on polynomials in the variables `z_i`, `i ∈ σ`, that
sends the monomial `z^α` to `∏_{i ∈ σ} η_{α_i}(z_i)`, where `η_m` is the signed Appell polynomial
`Polynomial.signedAppell`. Extended linearly,
`𝔄(F) = ∑_{α ∈ supp F} ([z^α] F) ∏_{i ∈ σ} η_{α_i}(z_i)`.

## Main definitions

* `MvPolynomial.appellOperator R σ`: the Appell operator on `MvPolynomial σ R`.

## Implementation notes

The paper works over `ℝ` with `σ` finite. The definition is over any commutative ring `R`, and
`σ` is arbitrary: the product is the `Finsupp.prod` over the support of `α`, which agrees with the
product over all of `σ` because `η_0 = 1`. The operator is defined on the monomial basis
`MvPolynomial.basisMonomials` and extended linearly by `Basis.constr`.

For `κ : σ →₀ ℕ`, the restriction `𝔄_κ` to the polynomials of degree at most `κ i` in each `z_i`
is `(MvPolynomial.appellOperator R σ).domRestrict (MvPolynomial.restrictSupport R (Set.Iic κ))`,
the space `MvPolynomial.restrictSupport R (Set.Iic κ)` being the one used throughout for
`ℝ_κ[z]`.

## References

* [LogNarayana], Section 6 (the Appell operator).
-/

namespace MvPolynomial

variable (R : Type*) [CommRing R] (σ : Type*)

end MvPolynomial
