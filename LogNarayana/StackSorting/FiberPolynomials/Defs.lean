/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module
public import LogNarayana.StackSorting.Descents.Defs
public import LogNarayana.StackSorting.StackSort.Defs
public import LogNarayana.AuxiliaryDefinitions

/-!
# The fiber polynomials

The definitions documented here are stated in `LogNarayana.Definitions` and
`LogNarayana.AuxiliaryDefinitions`, which this module imports.

For a permutation `π ∈ S_n`, the stack-sorting fiber `s⁻¹(π)` carries the statistics `des`
(number of descents), `peak` (number of peaks), `DT` (descent tops) and `AT` (ascent tops).
Summing monomials in these statistics over the fiber gives four generating polynomials:

* the *fiber descent polynomial* `D_π(x) = ∑_{σ ∈ s⁻¹(π)} x^{des(σ)}`, whose value at `x = 1` is
  the fertility `|s⁻¹(π)|`;
* the *homogeneous fiber polynomial* `H_π(x, y) = ∑_{σ ∈ s⁻¹(π)} x^{des(σ)} y^{n - 1 - des(σ)}`,
  homogeneous of degree `n - 1` (every `σ ∈ S_n` has `des(σ) ≤ n - 1`), the degree `n - 1`
  homogenization of `D_π`;
* the *peak-weighted homogeneous fiber polynomial*
  `H^λ_π(x, y) = ∑_{σ ∈ s⁻¹(π)} λ^{peak(σ)} x^{des(σ)} y^{n - 1 - des(σ)}`, which is `H_π` at
  `λ = 1` and, with the convention `λ⁰ = 1`, counts the peakless permutations of the fiber at
  `λ = 0`;
* the *fiber top polynomial* `𝒟_π(x, y) = ∑_{σ ∈ s⁻¹(π)} ∏_{a ∈ DT(σ)} x_a ∏_{b ∈ AT(σ)} y_b`,
  in the variables `x_a, y_a` (`a ∈ [n]`), recording the descent and ascent tops.

## Main definitions

* `List.fiberDescentPolynomial R π`: the polynomial `D_π(x) ∈ R[X]`.
* `List.fiberHomogPolynomial R π`: the polynomial `H_π(x, y) ∈ R[x, y]`.
* `List.fiberPeakPolynomial R λ π`: the polynomial `H^λ_π(x, y) ∈ R[x, y]`.
* `List.fiberTopPolynomial R π`: the polynomial `𝒟_π(x, y)` with coefficients in `R`.

## Implementation notes

The paper works over `ℝ`; the coefficients are natural numbers (for `H^λ_π`, sums of powers of
`λ`), so each polynomial is defined over an arbitrary (commutative) semiring `R`, and the paper's
polynomials are the instances `R = ℝ`. As for `List.stackFiber`, each is defined for every list
`π`, and is `0` unless `π` is a permutation in one-line notation.

The two variables of `H_π` and `H^λ_π` are those of `MvPolynomial (Fin 2) R`, with `x = X 0` and
`y = X 1`, the convention of `Polynomial.homogenize`. The integer `n` is `π.length`, and the
exponent `n - 1 - des(σ)` is truncated subtraction in `ℕ`; for `σ ∈ s⁻¹(π)` with `n ≥ 1` it is
the true difference because `des(σ) ≤ n - 1`. The weight `λ^{peak(σ)}` enters as the constant
`C (λ ^ _)`; the convention `0⁰ = 1` is that of `Monoid.npow`.

The variables of `𝒟_π` are indexed by `Bool × ℕ`, as in `forestGroundSet` and
`positionRelabelMap`: `x_a = X (true, a)` and `y_a = X (false, a)`. Only the variables indexed by
`{x, y} × [n]` occur, since `DT(σ), AT(σ) ⊆ Let(σ) = [n]`.

## References

* [LogNarayana], Section 2.
-/


namespace List

open MvPolynomial

end List
