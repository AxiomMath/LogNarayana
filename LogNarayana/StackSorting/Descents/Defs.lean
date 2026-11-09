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
# Descents, descent tops, ascent tops and peaks of a word

The definitions documented here are stated in `LogNarayana.Definitions` and
`LogNarayana.AuxiliaryDefinitions`, which this module imports.

For a word `σ = σ₁ ⋯ σ_ℓ`, with `[ℓ - 1] = ∅` when `ℓ ≤ 1`:

* the *descent set* is `Des(σ) = {i ∈ [ℓ - 1] : σᵢ > σᵢ₊₁}`, and `des(σ) = |Des(σ)|` is the
  number of descents;
* the *descent tops* are `DT(σ) = {σᵢ : i ∈ [ℓ - 1], σᵢ > σᵢ₊₁}`, the letters immediately
  followed by a smaller letter;
* the *ascent tops* are `AT(σ) = {σᵢ₊₁ : i ∈ [ℓ - 1], σᵢ < σᵢ₊₁}`, the letters immediately
  preceded by a smaller letter;
* a *peak* is an index `i` with `2 ≤ i ≤ ℓ - 1` and `σᵢ₋₁ < σᵢ > σᵢ₊₁`, and `peak(σ)` is the
  number of peaks.

## Main definitions

* `List.descentSet σ`: the descent set, as a `Finset ℕ` of `1`-based positions.
* `List.numDescents σ`: the number of descents, the cardinality of `List.descentSet σ`.
* `List.descentTops σ`: the finite set of entries of `σ` immediately followed by a smaller entry.
* `List.ascentTops σ`: the finite set of entries of `σ` immediately preceded by a smaller entry.
* `List.peakCount σ`: the number of peaks of `σ`.

## Implementation notes

The definitions are made for an arbitrary list over a type with a decidable `<` (and decidable
equality, for the sets of letters), not only for words, i.e. lists of distinct positive integers;
distinctness and positivity play no role.

Positions are `1`-based as in the paper: `i ∈ descentSet σ` iff `1 ≤ i < ℓ` and
`σ[i] < σ[i - 1]` in Lean's `0`-based indexing, and the peak range `[2, ℓ - 1]` is written
`Finset.Ico 2 ℓ`, the condition at `i` reading `σ[i - 2] < σ[i - 1]` and `σ[i] < σ[i - 1]`.

The consecutive pairs `(σᵢ, σᵢ₊₁)`, `i ∈ [ℓ - 1]`, are the entries of `σ.zip σ.tail`;
`DT(σ)` is the set of first components of those pairs with `σᵢ₊₁ < σᵢ`, and `AT(σ)` the set of
second components of those with `σᵢ < σᵢ₊₁`.

`List.numDescents` is an `abbrev` for `σ.descentSet.card`, so the `Finset.card` API applies to
it directly.

## References

* [LogNarayana], Section 2.
-/


namespace List

variable {α : Type*} [LT α] [DecidableRel (α := α) (· < ·)]

variable [DecidableEq α]

end List
