/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module
public import LogNarayana.StackSorting.Descents.Defs
public import LogNarayana.AuxiliaryDefinitions

/-!
# Hooks, valid hook configurations and valid compositions

The definitions documented here are stated in `LogNarayana.Definitions` and
`LogNarayana.AuxiliaryDefinitions`, which this module imports.

A composition of `N` into `m` parts is a tuple `q : Fin m → ℕ` of positive integers with
`∑ i, q i = N`.

For a permutation `π = π₁ ⋯ π_n`, the *plot* of `π` is the set of points `(i, πᵢ)`, `i ∈ [n]`.
A *hook* of `π` is a pair `(i, j)` of indices with `1 ≤ i < j ≤ n` and `πᵢ < πⱼ`; the point
`(i, πᵢ)` is its *southwest endpoint* and `(j, πⱼ)` its *northeast endpoint*. As a subset of the
plane the hook is `Γ_π(i, j) = [(i, πᵢ), (i, πⱼ)] ∪ [(i, πⱼ), (j, πⱼ)]`, a vertical segment
followed by a horizontal one.

A *valid hook configuration* of `π` is a set `𝓗` of hooks of `π` such that

* (V1) `|𝓗| = des(π)` and the southwest endpoints of the hooks of `𝓗` are exactly the descents
  of `π`: `{i : (i, j) ∈ 𝓗} = Des(π)`;
* (V2) no horizontal segment of a hook lies below a point of the plot: for every `(i, j) ∈ 𝓗`
  and every `k` with `i ≤ k ≤ j`, `πₖ ≤ πⱼ`;
* (V3) two distinct hooks of `𝓗` whose regions `Γ_π(i, j)` and `Γ_π(i', j')` meet satisfy
  `j = i'` or `j' = i`: they only touch when the northeast endpoint of one is the southwest
  endpoint of the other.

Let `k = des(π)` and `d₁ < ⋯ < d_k` be the descents. A position `u ∈ [n]` is *free* for `𝓗` if
it is not the northeast endpoint of a hook of `𝓗`, and a hook `(i, j) ∈ 𝓗` *covers* `u` if
`i < u < j`. Colour the hooks with distinct colours other than sky blue; each free point
`(u, πᵤ)` looks straight up and receives the colour of the lowest hook covering it (the one with
smallest `πⱼ`), or blue if no hook covers it. Then `q₀` is the number of blue points, and `qₜ`,
`t ∈ [k]`, the number of free points coloured like a hook with southwest endpoint `dₜ`. The tuple
`𝐪_𝓗 = (q₀, q₁, …, q_k) ∈ ℤ_{≥0}^{k+1}` is the composition induced by `𝓗`, and the set of
*valid compositions* of `π` is `𝒱(π) = {𝐪_𝓗 : 𝓗 ∈ VHC(π)}`.

## Main definitions

* `Finset.Nat.compositionTuple m N`: the compositions of `N` into `m` parts, as tuples.
* `List.hooks σ`: the set of hooks of a list `σ`, as pairs of `1`-based positions `(i, j)`.
* `List.hookRegion σ p`: the subset `Γ_σ(p.1, p.2)` of `ℝ × ℝ`.
* `List.validHookConfigurations π`: the finite set `VHC(π)` of valid hook configurations.
* `List.hookComposition π 𝓗`: the tuple `𝐪_𝓗 : Fin (des(π) + 1) → ℕ`.
* `List.validCompositions π`: the finite set `𝒱(π)` of valid compositions.

## Implementation notes

The paper writes `Comp(N, k+1)` for compositions into `k + 1` parts indexed by `0, …, k`; this
is `Finset.Nat.compositionTuple (k + 1) N`, the subset of
`Finset.Nat.antidiagonalTuple (k + 1) N` cut out by positivity of every entry. Unlike Mathlib's
`Composition N`, which records the parts as a list of unspecified length, the number of parts is
fixed here and the parts form a function on `Fin m`, which is the shape in which the tuples are
indexed and summed.

All definitions on words are made for arbitrary lists, not only for permutations of `[n]`; for a
permutation they are the paper's notions. `List.hooks` needs only a decidable `<` on letters;
the others are stated for words `List ℕ`, as permutation words (`List.permWords`) are. Positions
are `1`-based as in the paper, so `(i, j) ∈ σ.hooks` iff `1 ≤ i < j ≤ ℓ` and
`σ[i - 1] < σ[j - 1]` in Lean's `0`-based indexing. Outside `List.hooks`, letters are read with
`List.getD` at the `0`-based index (default `0`) so that the definitions are total; at the
positions that matter for a hook this agrees with `σ[i - 1]`. `List.hookRegion` is defined for
every pair of positions, and is the region of a hook when the pair lies in `σ.hooks`.

`VHC(π)` is the powerset of `π.hooks` filtered by (V1)–(V3). Nonemptiness of the intersection
of two hook regions is not decidable in general, so the filter uses classical decidability. In
[Fertilitopes] a valid hook configuration is recorded as the tuple `(H₁, …, H_k)` of its hooks
listed by their southwest endpoints `d₁ < ⋯ < d_k`; by (V1) this tuple carries the same
information as the set.

`List.hookComposition π 𝓗` is indexed by `Fin (π.numDescents + 1)`, entry `0` being `q₀` and
entry `t + 1` being `q_{t+1}`; the `t`-th descent (`0`-based) is
`π.descentSet.orderEmbOfFin rfl t`. It is defined for every finite set `𝓗` of pairs, and
`List.validCompositions π` is the image of `List.validHookConfigurations π` under it.

## References

* [LogNarayana], Section 2.3.
* [Fertilitopes], Section 2.1.
-/

namespace Finset.Nat

end Finset.Nat

namespace List

end List
