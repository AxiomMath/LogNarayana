/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib
public import LogNarayana.Attr
public import LogNarayana.StackSorting.Descents.Defs
public import LogNarayana.StackSorting.StackSort.Defs
public import LogNarayana.AuxiliaryDefinitions

/-!
# Position relabelling and conditional top polynomials

The definitions documented here are stated in `LogNarayana.Definitions` and
`LogNarayana.AuxiliaryDefinitions`, which this module imports.

For a permutation `π ∈ S_n` in one-line notation, the *position relabelling*
`ρ_π : {x, y} × [n-1] → {x, y} × [n]`, `(s, v) ↦ (s, π_{v+1})`, sends a position `v` to the letter
of `π` in the next position; it induces the renaming of variables `x_v ↦ x_{π_{v+1}}`,
`y_v ↦ y_{π_{v+1}}`, also written `ρ_π`.

Fix subsets `A_d, B_d, A_a, B_a, J_d, J_a ⊆ [n]`, and let `Ω` be the set of `σ ∈ s⁻¹(π)` with
`A_d ⊆ DT(σ) ⊆ [n] ∖ B_d` and `A_a ⊆ AT(σ) ⊆ [n] ∖ B_a`. Given weights `α, β` on `[n]`, put
`wt(σ) = ∏_{a ∈ DT(σ)} α_a ∏_{b ∈ AT(σ)} β_b`. The *conditional top polynomial* is
`F(x) = ∑_{σ ∈ Ω} wt(σ) x^{|DT(σ) ∩ J_d| + |AT(σ) ∩ J_a|}`.

## Main definitions

* `List.positionRelabelMap π`: the map `(s, v) ↦ (s, π_{v+1})` on `Bool × ℕ`.
* `List.positionRelabel R π`: the induced `R`-algebra map on polynomials, `MvPolynomial.rename`
  along `List.positionRelabelMap π`.
* `List.conditionalTopPolynomial`: the polynomial `F(x)`.

## Implementation notes

As in `forestGroundSet`, the set `{x, y} × [N]` is encoded inside `Bool × ℕ`, with
`x_v = (true, v)` and `y_v = (false, v)`; both polynomial rings are then subrings of
`MvPolynomial (Bool × ℕ) R`, and `ρ_π` is a single endomorphism of it. Positions are `1`-indexed,
so `π_{v+1}` is the entry of `π` at the `0`-based index `v`, i.e. `π.getD v 0`. The definition
makes sense for any word `π` and any commutative semiring `R`; the paper uses `π ∈ permWords n`
and `R = ℝ`, where `ρ_π` is injective on `{x, y} × [n-1]`.

The constraint `DT(σ) ⊆ [n] ∖ B_d` is stated as `Disjoint DT(σ) B_d` (and likewise for ascent
tops): for `σ ∈ s⁻¹(π)` one has `DT(σ), AT(σ) ⊆ Let(σ) = [n]`, so the two agree, and the disjoint
form needs no reference to `n`. The subsets are arbitrary finite sets of natural numbers and the
weights arbitrary functions `ℕ → R` into a commutative semiring `R`; only the values of `α, β` on
`[n]` enter. The positivity of the weights and the conditions `J_d ∩ (A_d ∪ B_d) = ∅`,
`J_a ∩ (A_a ∪ B_a) = ∅` are hypotheses of the results about `F`, not of its definition. The
paper's polynomial is `List.conditionalTopPolynomial ℝ π A_d B_d A_a B_a J_d J_a α β`.

## References

* [LogNarayana] *Log-Concavity in Narayana Transforms and Stack-Sorting Fibers*, Section 3,
  Corollary 3.6.
-/


namespace List

end List


section ConditionalTopPolynomial

open Polynomial

namespace List

end List

end ConditionalTopPolynomial
