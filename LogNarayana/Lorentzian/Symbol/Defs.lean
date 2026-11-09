/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module
public import LogNarayana.Lorentzian.MConvex.Basic
public import LogNarayana.AuxiliaryDefinitions

/-!
# Linear operators on polynomials: symbols and normalizations

The definitions documented here are stated in `LogNarayana.Definitions` and
`LogNarayana.AuxiliaryDefinitions`, which this module imports.

For `κ : σ →₀ ℕ`, let `R_κ[z]` be the space of polynomials whose degree in `z i` is at most
`κ i`, realised as `MvPolynomial.restrictSupport R (Set.Iic κ)`, the span of the monomials
`z ^ α` with `α ≤ κ`. A linear operator `T : R_κ[z] → R[x]` is *homogeneous of degree `ℓ : ℤ`*
if every monomial `z ^ α` is sent either to `0` or to a homogeneous polynomial of degree
`|α| + ℓ`. The *algebraic symbol* of `T` is the polynomial
`Sym_κ(T)(x, w) = ∑_{α ≤ κ} (κ choose α) T(z ^ α) w ^ (κ - α)`
in the variables `x_j` and new variables `w_i`.

Three further linear operators and polynomials are defined through their values on monomials:
the full factorial normalization `𝓔(z^α) = z^α / α!`, the normalized support polynomial
`E_J(z) = ∑_{α ∈ J} z^α / α!` of a finite set `J` of multi-indices, and the antiderivative
`∫₀ᵗ F ds` in one variable, `z^α ↦ z^(α + e_t) / (α_t + 1)`, a right inverse of
`MvPolynomial.pderiv t`.

## Main definitions

* `MvPolynomial.IsHomogeneousOperator`: the linear map `T` is homogeneous of degree `ℓ`.
* `MvPolynomial.algebraicSymbol`: the algebraic symbol `Sym_κ(T)`, a polynomial in
  `MvPolynomial (τ ⊕ σ) R`, whose variables `Sum.inl j` are the `x_j` and `Sum.inr i` the `w_i`.
* `MvPolynomial.fullFactorialNormalization`: the `R`-linear map with `z^α ↦ (1 / α!) • z^α`.
* `MvPolynomial.normalizedSupportPoly`: the polynomial `∑ α ∈ J, (1 / α!) • z^α`.
* `MvPolynomial.antiderivative`: the `R`-linear map with
  `z^α ↦ (1 / (α_t + 1)) • z^(α + e_t)`.

## Implementation notes

The paper works over `ℝ`. The operators on bounded-degree spaces and the symbol are defined
over an arbitrary commutative semiring `R`; the definitions dividing by `α!` or `α_t + 1` are
defined over any commutative semiring that is a `ℚ`-algebra, with the scalar the rational
number mapped into `R`, as for `PowerSeries.exp`.

The monomial `z ^ α` in the domain of a homogeneous operator is quantified as an element `f`
whose underlying polynomial is `monomial α 1`, so that definition carries no membership proof;
the condition `|α| + ℓ ≥ 0` together with homogeneity of degree `|α| + ℓ` is homogeneity of
some degree `n : ℕ` with `(n : ℤ) = |α| + ℓ`.

The joint polynomial ring `R[x_j, w_i]` of the symbol is `MvPolynomial (τ ⊕ σ) R`; `T (z ^ α)`
is embedded by `rename Sum.inl` and `w ^ (κ - α)` by `rename Sum.inr`. For an operator on
polynomials in `z` (`τ = σ`) the symbol lies in `MvPolynomial (σ ⊕ σ) R`. The multinomial
coefficient is `Finsupp.choose`, and the sum over `Finset.Iic κ` is formed classically, so no
decidable equality on `σ` is assumed.

`fullFactorialNormalization` and `antiderivative` are defined through the monomial basis
`MvPolynomial.basisMonomials`, so `Basis.constr_basis` gives their values on `z^α`, which
characterise them.

## References

* [P. Brändén and J. Huh, *Lorentzian polynomials*][BH], Section 3.
-/

@[expose] public section

namespace MvPolynomial

section BoundedDegree

variable {R σ τ : Type*} [CommSemiring R]

end BoundedDegree

section Rational

variable (σ : Type*) (R : Type*) [CommSemiring R] [Algebra ℚ R]

variable {σ}

variable {R}

end Rational

end MvPolynomial

end
