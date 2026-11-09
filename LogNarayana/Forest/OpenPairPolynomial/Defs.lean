/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib
public import LogNarayana.Attr
public import LogNarayana.Lorentzian.Symbol.Defs
public import LogNarayana.StackSorting.Matchings.Defs
public import LogNarayana.Forest.LaminarMatroid.Defs
public import LogNarayana.StackSorting.AdoptableForest.Defs
public import LogNarayana.AuxiliaryDefinitions

/-!
# The weighted open-pair polynomial and its operators

The definitions documented here are stated in `LogNarayana.Definitions` and
`LogNarayana.AuxiliaryDefinitions`, which this module imports.

For polynomials `A, B` and a distinguished variable `t`, the *root operator* `𝓡_{A,B}` acts on
polynomials `U(x, t)` by `𝓡_{A,B}(U) = A U + ∫₀ᵗ U(x, s) ds + B ∂_t U`. For a polynomial
`f = ∑_{h=0}^H f_h t^h` with `f_h` free of `t`, the polynomial `δ_t f = ∑_{h=1}^H f_h t^(h-1)`
discards the `t`-free part and divides the rest by `t`.

Let `(par, L)` be a marked postorder forest on `[N] = {1, …, N}` and let `A = (A_v)`,
`B = (B_v)` be families of polynomials in `R[x]`. The *vertex-weighted open-pair polynomial* is
`P^{A,B}_{par,L}(x, t) = ∑_{(M,O)} t^{|O|} ∏_{(a,b) ∈ M} B_b(x) ∏_{v ∈ U(M) \ O} A_v(x)`,
the sum running over the open pairs `(M, O)` of `(par, L)` (see `IsOpenPair`), where `U(M)` is
the set of vertices of `[N]` unmatched by `M` (see `Finset.unmatchedVertices`). For constant
families `A_v = A`, `B_v = B` it is the *weighted open-pair polynomial*
`P^{A,B}_{par,L}(x, t) = ∑_{(M,O)} t^{|O|} B(x)^{|M|} A(x)^{|U(M) \ O|}`.

## Main definitions

* `MvPolynomial.rootOperator`: the `R`-linear map `U ↦ A U + ∫₀ᵗ U ds + B ∂_t U` on
  `MvPolynomial σ R`.
* `MvPolynomial.divX`: the polynomial `δ_t f`, the multivariate analogue of `Polynomial.divX`.
* `vertexWeightedOpenPairPolynomial N par L A B`: the vertex-weighted open-pair polynomial.
* `weightedOpenPairPolynomial N par L A B`: the weighted open-pair polynomial.

## Implementation notes

The paper works over `ℝ` in `ℝ[x, t]`. For the root operator and `δ_t`, the ring is
`MvPolynomial σ R` with `t : σ` one of its variables, as for `MvPolynomial.antiderivative`; the
paper's ring is the case `σ = Option X` with `t = none`. The root operator is defined over any
commutative semiring that is a `ℚ`-algebra, with arbitrary coefficients `A, B`; the paper's case
is that in which they do not involve `t`. The integral `∫₀ᵗ` is `MvPolynomial.antiderivative t`
and `∂_t` is `MvPolynomial.pderiv t`. The operation `δ_t` is Mathlib's division by the monomial
`t`, `MvPolynomial.divMonomial f (Finsupp.single t 1)`, whose coefficient formula
`MvPolynomial.coeff_divMonomial` is the paper's definition coefficientwise.

For the open-pair polynomials the ring `R[x, t]` is `MvPolynomial (Option σ) R`: the variable
`t` is `X none` and `x_i` is `X (some i)`, and a polynomial of `R[x] = MvPolynomial σ R` is
embedded by `rename some`. The families are functions `ℕ → MvPolynomial σ R`; only their values
on `[N]` enter. Every open pair `(M, O)` has `M ⊆ [N] × [N]` and `O ⊆ [N]`, so the sum is over
the finite set of such pairs satisfying `IsOpenPair`. The definitions make sense for every
`par : ℕ → Option ℕ`, every finite `L ⊆ ℕ` and every commutative semiring `R`; the paper's
setting is a marked postorder forest and `R = ℝ`, with `A` a linear form and `B` a homogeneous
quadratic in the constant case.

## References

* [P. Brändén and J. Huh, *Lorentzian polynomials*][BH]
* [LogNarayana] *Log-Concavity in Narayana Transforms and Stack-Sorting Fibers*, Section 7.
-/

noncomputable section

namespace MvPolynomial

section RootOperator

variable {σ R : Type*} [CommSemiring R] [Algebra ℚ R]

end RootOperator

end MvPolynomial

end

namespace MvPolynomial

variable {σ : Type*} {R : Type*} [CommSemiring R]

end MvPolynomial

@[expose] public section

open MvPolynomial

end
