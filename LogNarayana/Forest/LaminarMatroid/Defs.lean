/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module
public import LogNarayana.StackSorting.AdoptableForest.Defs
public import LogNarayana.StackSorting.Matchings.Defs
public import LogNarayana.AuxiliaryDefinitions

/-!
# The laminar matroid of a marked forest

The definitions documented here are stated in `LogNarayana.Definitions` and
`LogNarayana.AuxiliaryDefinitions`, which this module imports.

Let `par` be a parent map on `[N] = {1, …, N}` and `L ⊆ [N]` a set of marked vertices. Every
unmarked vertex `v` gets two copies `v⁺ = (x, v)` and `v⁻ = (y, v)`, forming the ground set
`E_{N,L} = {x, y} × ([N] \ L)`. The subtree `V_v` rooted at `v` contributes the block
`E_v = {x, y} × (V_v \ L)`, and the independent sets are
`𝕀_{par,L} = {I ⊆ E_{N,L} : |I ∩ E_v| ≤ |V_v| for every v ∈ [N]}`, the capacity-bounded sets of
the laminar family of blocks.

Its basis generating polynomial is compared with the *forest matching polynomial*
`Z_{par,L}(x, y) = ∑_M ∏_{v ∈ R(M)} x_v y_v ∏_{v ∈ U(M)} (x_v + y_v)`, a sum over admissible
matchings `M`. Expanding a term of the open forest polynomial selects a *choice set*
`I(M, O, S) = {v⁺, v⁻ : v ∈ R(M)} ∪ {v⁺ : v ∈ S} ∪ {v⁻ : v ∈ U(M) \ (O ∪ S)}` attached to an
*open pair* `(M, O)`. Conversely, a subset `I` of the doubled ground set is read back by a stack:
with `c_v = |I ∩ {v⁺, v⁻}|`, the vertices `v = 1, 2, …` are processed in order, a vertex with
`c_v = 0` is pushed, one with `c_v = 1` is skipped, and one with `c_v = 2` pops the top `u` and
records the pair `(u, v)`. The final state gives the *reconstruction* `(M_I, O_I, S_I)`.

## Main definitions

* `forestGroundSet N L`: the ground set `E_{N,L}`.
* `forestBlock N par L v`: the block `E_v` of the subtree rooted at `v`.
* `forestIndepFamily N par L`: the family `𝕀_{par,L}`.
* `forestMatchingPoly R N par L`: the polynomial `Z_{par,L}(x, y)`.
* `Finset.openChoiceSet N M O S`: the choice set `I(M, O, S)`.
* `IsOpenPair N par L M O`: `(M, O)` is an open pair for `(par, L)` on `[N]`.
* `reconstructionStates I v`: the stack state `(λ_v, M_v)` after processing `1, …, v`.
* `stackReconstruction N I`: the reconstruction `(M_I, O_I, S_I)`.

## Implementation notes

Vertices are natural numbers and `[N] = Finset.Icc 1 N`. The labels `{x, y}` are `Bool`, with
`v⁺ = (true, v)` the `x`-copy and `v⁻ = (false, v)` the `y`-copy; accordingly the polynomial
variables are indexed by `Bool × ℕ`, with `x_v = X (true, v)` and `y_v = X (false, v)`, and the
paper's ring `ℝ[z_e : e ∈ {x, y} × [N]]` is the subring of `MvPolynomial (Bool × ℕ) ℝ` in the
variables it uses. The coefficients of `forestMatchingPoly` lie in any commutative semiring.

All definitions make sense for every `par : ℕ → Option ℕ` and every finite `L ⊆ ℕ`: the
hypotheses that `par` is a parent map and `L ⊆ [N]` only restrict the domain on which they are
the paper's notions. The right endpoints `R(M)` of a matching are `M.image Prod.snd` and its
unmatched vertices `U(M)` are `Finset.unmatchedVertices N M`.

The capacity of the block `E_v` is the number `|V_v|` of all vertices of the subtree, marked or
not. Every admissible matching is a subset of `[N] × [N]`, so `forestMatchingPoly` sums over the
subsets of `[N] × [N]` that are admissible. The stack of `reconstructionStates` is a `List ℕ`
whose last entry is its top; the recursion does not depend on `N`, and the paper's sequence
`(λ_v, M_v)_{v=0}^N` is its restriction to `v ≤ N`.

## References

* [LogNarayana] *Log-Concavity in Narayana Transforms and Stack-Sorting Fibers*, Section 3.
-/

