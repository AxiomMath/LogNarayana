/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module
public import LogNarayana.StackSorting.Matchings.Defs
public import LogNarayana.AuxiliaryDefinitions

/-!
# Parent maps, postorder forests and the adoptable forest

The definitions documented here are stated in `LogNarayana.Definitions` and
`LogNarayana.AuxiliaryDefinitions`, which this module imports.

A *parent map* on `[N] = {1, …, N}` assigns to every vertex `v ∈ [N]` either a parent
`par(v) ∈ [v + 1, N]` or `⊥`. It encodes a rooted forest on `[N]` in which every vertex carries a
smaller label than its parent; the roots are the vertices with `par(v) = ⊥`. Its iterates are
`par⁰(v) = v` and `parᵏ⁺¹(v) = par(parᵏ(v))`, with `parᵏ⁺¹(v) = ⊥` once `parᵏ(v) = ⊥`; a vertex
`u` is an *ancestor-or-self* of `v`, written `u ⪰ v`, if `parᵏ(v) = u` for some `k ≥ 0`, and a
*strict ancestor* if moreover `u ≠ v`. A *leaf* is a vertex with no children, and the vertex set of
the subtree rooted at `v` is `V_v = {u ∈ [N] : v ⪰ u}`. The parent map is a *postorder forest* if
`V_v = [v - |V_v| + 1, v]` for every `v ∈ [N]`: it then encodes a rooted plane forest labelled in
postorder, the children of a vertex being ordered by their labels.

For a set `L ⊆ [N]` of marked vertices, a noncrossing partial matching `M` on `[N]` is
*admissible* for `(par, L)` if `b` is a strict ancestor of `a` for every `(a, b) ∈ M`, and every
marked vertex is a left endpoint of `M`.

Fix `π = π₁ ⋯ π_n ∈ S_n`. A pair `(a, b)` with `1 ≤ a < b ≤ n - 1` is *adoptable* with respect to
`π` if `π_b = max {π_{a+1}, …, π_b}` and `π_{b+1} > max {π_a, …, π_b}`. The left bound `ℓ_b` is
`min ({a ∈ [b - 1] : (a, b) adoptable} ∪ {b})`, the *adoptable interval* is `I_b = [ℓ_b, b]`, and
the *adoptable forest* `𝓕_π` is the parent map on `[n - 1]` sending `a` to the least
`b ∈ [a + 1, n - 1]` with `a ∈ I_b`, and to `⊥` if there is none.

## Main definitions

* `IsParentMap N par`: the map `par : ℕ → Option ℕ` is a parent map on `[N]`.
* `IsAncestorOrSelf par u v`: `u` is an ancestor of `v` or `u = v` in the forest of `par`.
* `IsStrictAncestor par u v`: `u` is a strict ancestor of `v` in the forest of `par`.
* `IsLeaf par v`: the vertex `v` has no child in the forest of `par`.
* `subtreeVertices N par v`: the vertex set `V_v ⊆ [N]` of the subtree rooted at `v`.
* `IsPostorderForest N par`: the parent map `par` on `[N]` is a postorder forest.
* `IsAdmissibleMatching N par L M`: `M` is an admissible matching on `[N]` for `(par, L)`.
* `List.IsAdoptablePair π a b`: the pair `(a, b)` is adoptable with respect to `π`.
* `List.adoptableLeftBound π b`: the left bound `ℓ_b`.
* `List.adoptableInterval π b`: the interval `I_b = [ℓ_b, b]`, as a `Finset ℕ`.
* `List.adoptableForest π`: the parent map `par_π : ℕ → Option ℕ` of the adoptable forest.

## Implementation notes

Vertex labels are natural numbers, `[N] = Finset.Icc 1 N`, the value `⊥` is `none` and a parent
`p` is `some p`. A parent map is a function on all of `ℕ` that is `none` outside `[N]`; with this
normalisation parent maps on `[N]` in the paper's sense correspond bijectively to functions
satisfying `IsParentMap N par`, so that sets of parent maps can be counted directly. The iterate
`parᵏ(v)` is `(fun o => o.bind par)^[k] (some v)`: `Option.bind` sends `none` to `none` and
`some w` to `par w`, which is the paper's recursion.

The relations `IsAncestorOrSelf`, `IsStrictAncestor`, `IsLeaf`, `subtreeVertices` and
`IsAdmissibleMatching` are defined for every `par : ℕ → Option ℕ`; the hypothesis that `par` is a
parent map on `[N]`, and that the vertices lie in `[N]`, only restrict the domain on which they
are the paper's notions. For a parent map, `par u = some v` already forces `u ∈ [N]`, so `IsLeaf`
may quantify over all `u : ℕ`. The paper takes the marked set `L` of an admissible matching to be
a set of leaves; no result uses this, and any finite `L ⊆ ℕ` is allowed.

In `IsPostorderForest` the interval `[v - |V_v| + 1, v]_ℤ` is `Finset.Icc (v + 1 - #V_v) v` in `ℕ`.
This loses nothing: if `#V_v > v` the truncated interval contains `0`, which never lies in
`V_v ⊆ [N]`, so the equality fails exactly as it does over `ℤ`.

The adoptable notions are defined for an arbitrary list over a preorder; on `permWords n` they are
the paper's. Positions are `1`-indexed, so `π_i` is `π[i - 1]`, and `b ≤ n - 1` is written
`b < π.length`, which makes `π_{b+1} = π[b]` defined. The two maxima are expressed pointwise. The
set `[b - 1]` is `Finset.Ico 1 b`. The adoptable forest is applied to every `a : ℕ`; it is `none`
outside `[n - 1]`, since for `a ≥ n - 1` the range `[a + 1, n - 1]` is empty and no `I_b` with
`b ≥ 1` contains `0`.

## References

* [LogNarayana] *Log-Concavity in Narayana Transforms and Stack-Sorting Fibers*, Sections 3 and 6.
-/

@[expose] public section

namespace List

variable {α : Type*} [Preorder α]

end List

end
