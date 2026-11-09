/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module
public import LogNarayana.StackSorting.Descents.Defs
public import LogNarayana.BinaryTree.Decreasing.Defs
public import LogNarayana.AuxiliaryDefinitions

/-!
# Matchings and decreasing binary plane trees with fixed postorder

Let `N ≥ 0`. A *noncrossing partial matching on `[N]`* is a finite set `M` of pairs `(a, b)` with
`1 ≤ a < b ≤ N` such that no integer is an entry of two distinct pairs of `M`, and there are no
two pairs `(a, b), (c, d) ∈ M` with `a < c < b < d`. For `(a, b) ∈ M`, `a` is its *left endpoint*
and `b` its *right endpoint*; `LE(M)` is the set of left endpoints, and the *unmatched vertices*
of `M` are `U(M) = [N] \ (LE(M) ∪ R(M))`.

For `π ∈ S_n`, the set `𝒜(π)` of *matchings of `π`* consists of the noncrossing partial
matchings `M` on `[n - 1]` with `Des(π) ⊆ LE(M)` and `π_a < π_{b+1}` for every `(a, b) ∈ M`, and
`Γ_π(z) = ∑_{M ∈ 𝒜(π)} z^{|M|}` is its generating polynomial by number of arcs.

On the tree side, for a decreasing binary plane tree `T` with postorder reading `𝒫(T) = π`, the
*matching* `M(T)` of `T` is the set of pairs `(a, b)` such that the vertex labelled `π_{b+1}` has
two children and its left child is labelled `π_a`, and `C(T)` is the set of unmatched vertices
`j ∈ U(M(T))` in `[n - 1]` with `π_{j+1} ∈ RC(T)`.

## Main definitions

* `IsNoncrossingPartialMatching N M`: `M ⊆ ℕ × ℕ` is a noncrossing partial matching on `[N]`.
* `Finset.leftEndpoints M`: the left endpoints `LE(M)` of a finite set `M ⊆ α × β`.
* `Finset.unmatchedVertices N M`: the unmatched vertices `U(M)` of `M` in `[N]`.
* `List.fiberMatchings π`: the set `𝒜(π)` of matchings of the word `π`.
* `List.fiberMatchingPolynomial R π`: the polynomial `Γ_π ∈ R[z]`.
* `BinaryTree.treeMatching T`: the matching `M(T)` of a binary plane tree.
* `BinaryTree.treeRightChoices T`: the set `C(T) ⊆ [n - 1]`.

## Main results

* `List.fiberMatchings_finite`: the set `𝒜(π)` is finite.

## Implementation notes

Pairs are elements `p : ℕ × ℕ`, with left endpoint `p.1` and right endpoint `p.2`; condition (i)
of a matching is phrased as: two pairs sharing an entry (in any position) are equal. The interval
`[N]` is `Finset.Icc 1 N`, and `R(M)` is the image `M.image Prod.snd`.

Positions in words are `1`-based as in the paper, so `π_a` is `π[a - 1]` and `π_{b+1}` is
`π[b]`; the index bounds are carried as witnesses. The definitions on words are made for an
arbitrary list over a type with a decidable `<`, and those on trees for trees with labels in an
arbitrary type, with `π := T.postorder` and `n := |π|`; the paper's hypotheses (`π ∈ S_n`,
`T` decreasing with `𝒫(T) = π`) only fix the setting. A vertex of `T` is a subtree of `T`,
expressed through the reflexive-transitive closure of "is a child subtree of the root of"; the
vertex labelled `π_{b+1}` has two children with left child labelled `π_a` exactly when `T` has a
subtree `⟨π_{b+1}; ⟨π_a; L₁, L₂⟩, ⟨d; R₁, R₂⟩⟩`, which for a decreasing tree (distinct labels) is
the paper's condition.

The polynomial `Γ_π` is defined over any commutative semiring (the paper's is the case `ℝ`) as
a `finsum` over `𝒜(π)`; that set is finite (`List.fiberMatchings_finite`), so this is the
finite sum of the paper.

## References

* [LogNarayana] *Log-Concavity in Narayana Transforms and Stack-Sorting Fibers*, Sections 3
  and 5.
-/

@[expose] public section

namespace List

variable {α : Type*} [LT α] [DecidableRel (α := α) (· < ·)]

/-- The set `𝒜(π)` is finite: every pair of a member lies in `[0, |π|] × [0, |π|)`. -/
theorem fiberMatchings_finite (π : List α) : π.fiberMatchings.Finite := by
  refine ((Finset.range (π.length + 1) ×ˢ Finset.range π.length).powerset : Set _).toFinite.subset
    fun M hM => ?_
  simp only [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff, Finset.coe_subset]
  intro p hp
  obtain ⟨ha, hb, -⟩ := hM.2.2 p hp
  simp only [Finset.mem_product, Finset.mem_range]
  omega

end List

namespace BinaryTree

variable {α : Type*}

end BinaryTree

end
