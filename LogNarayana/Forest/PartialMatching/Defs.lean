/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module
public import LogNarayana.Forest.LaminarMatroid.Defs
public import LogNarayana.AuxiliaryDefinitions

/-!
# Partial matchings and factorial normalization

The definitions documented here are stated in `LogNarayana.Definitions` and
`LogNarayana.AuxiliaryDefinitions`, which this module imports.

This file collects three definitions used to study the open-matching polynomial.

For a variable `t` of `MvPolynomial σ R`, the *factorial normalization* in `t` is the linear
operator `𝓝_t` dividing each monomial by the factorial of its `t`-exponent:
`𝓝_t(z^α t^h) = z^α t^h / h!`. Writing `f = ∑_h f_h(z) t^h`, this is
`𝓝_t f = ∑_h f_h(z) t^h / h!`.

Let `par` be a parent map on `[N]` and `L ⊆ [N]`. The *open-matching polynomial* is
`P_{par,L}(x, y, t) = ∑_{(M,O)} t^{|O|} ∏_{v ∈ R(M)} x_v y_v ∏_{v ∈ U(M) \ O} (x_v + y_v)`,
the sum over all open pairs `(M, O)` for `(par, L)`, where `R(M)` is the set of right endpoints
of `M` and `U(M)` its set of unmatched vertices.

For a matroid `M` and a natural number `r`, the family `M.truncationFamily r` consists of the
independent sets of `M` with at most `r` elements; it is the family of independent sets of the
truncation of `M` to rank `r`.

## Main definitions

* `MvPolynomial.factorialNormalization`: the `R`-linear map with
  `z^α ↦ (1 / (α_t)!) • z^α`.
* `forestOpenPoly R N par L`: the polynomial `P_{par,L}(x, y, t)`.
* `Matroid.truncationFamily`: the independent sets of `M` of size at most `r`.

## Implementation notes

The paper works over `ℝ` in the polynomial ring `ℝ[z_e, t : e ∈ X]`. Here `t` is one of the
variables of `MvPolynomial σ R`, the remaining ones playing the role of the `z_e`; the paper's
ring is the case `σ = Option X` with `t = none`. The factorial normalization only needs division
by `(α_t)!`, so it is defined over any commutative semiring `R` that is a `ℚ`-algebra, with the
scalar `algebraMap ℚ R (1 / (α_t)!)`. It is defined through the monomial basis
`MvPolynomial.basisMonomials`, so `Basis.constr_basis` gives its value on each monomial, which
is the characterising property of the paper.

For the open-matching polynomial the variables are indexed by `Option (Bool × ℕ)`:
`t = X none`, `x_v = X (some (true, v))` and `y_v = X (some (false, v))`, following the encoding
of `{x, y} × [N]` in `Bool × ℕ` of `forestGroundSet`. The coefficients are taken in any
commutative semiring `R`, since the definition only uses sums and products. Every open pair
`(M, O)` has `M ⊆ [N] × [N]` and `O ⊆ [N]`, so the sum is taken over the finite set of such
pairs satisfying `IsOpenPair N par L M O`. The right endpoints `R(M)` are the image
`M.image Prod.snd`, as in `Finset.unmatchedVertices`.

The paper works with a matroid on a finite ground set. `Matroid.truncationFamily` is defined
for an arbitrary `M : Matroid α`, with sizes measured by `Set.encard`; on finite sets this is
the cardinality.

## References

* [LogNarayana] *Log-Concavity in Narayana Transforms and Stack-Sorting Fibers*, Section 3.
-/

namespace MvPolynomial

variable {σ : Type*} {R : Type*} [CommSemiring R] [Algebra ℚ R]

end MvPolynomial

namespace Matroid

variable {α : Type*}

end Matroid
