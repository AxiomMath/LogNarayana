/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module
public import Mathlib
public import LogNarayana.Attr
public import LogNarayana.AuxiliaryDefinitions

/-!
# M-convex sets of multi-indices and polynomials with nonnegative coefficients

The definitions documented here are stated in `LogNarayana.Definitions` and
`LogNarayana.AuxiliaryDefinitions`, which this module imports.

A set `J` of multi-indices `α : σ →₀ ℕ` is *M-convex* if it is finite and nonempty, all its
elements have the same total degree `|α| = ∑ i, α i`, and it satisfies the *symmetric exchange
property*: whenever `α, β ∈ J` and `β i < α i`, there is `j` with `α j < β j` such that both
`α - e_i + e_j` and `β - e_j + e_i` lie in `J`.

A polynomial `f` in the variables `z_i`, `i ∈ σ`, has *nonnegative coefficients* if the
coefficient `[z^α] f` is nonnegative for every exponent vector `α : σ →₀ ℕ`.

## Main definitions

* `Set.IsMConvex`: the set `J ⊆ σ →₀ ℕ` is M-convex.
* `MvPolynomial.HasNonnegCoeffs`: every coefficient of `f` is nonnegative.

## Implementation notes

Multi-indices are finitely supported functions `σ →₀ ℕ`, the total degree `|α|` is
`Finsupp.degree`, and `e_i` is `Finsupp.single i 1`. Since `β i < α i` forces `1 ≤ α i`
(and `α j < β j` forces `1 ≤ β j`), the truncated subtraction `α - single i 1` agrees with
the subtraction in `ℤ^σ`. The index type `σ` is arbitrary.

The paper works over `ℝ`. Nonnegativity of coefficients only needs an order on the
coefficients, so it is stated for any commutative semiring `R` carrying a relation `≤`.

## References

* [BH] P. Brändén, J. Huh, *Lorentzian polynomials*, Ann. of Math. 192 (2020), §2.
-/

namespace Set

variable {σ : Type*}

end Set

namespace MvPolynomial

variable {σ : Type*} {R : Type*} [CommSemiring R] [LE R]

end MvPolynomial
