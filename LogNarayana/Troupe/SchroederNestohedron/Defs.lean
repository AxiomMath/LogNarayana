/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module
public import Mathlib
public import LogNarayana.Attr
public import LogNarayana.BinaryTree.Colored.Defs
public import LogNarayana.Troupe.PostorderPolynomial.Defs
public import LogNarayana.StackSorting.Descents.Defs
public import LogNarayana.StackSorting.StackSort.Defs
public import LogNarayana.Troupe.LocalRules.Defs
public import LogNarayana.StackSorting.ValidHookConfigurations.Defs
public import LogNarayana.Troupe.PostorderPolynomial.Basic
public import LogNarayana.AuxiliaryDefinitions

/-!
# Schröder factors

The definitions documented here are stated in `LogNarayana.Definitions` and
`LogNarayana.AuxiliaryDefinitions`, which this module imports.

For `q ≥ 0` the *Schröder factor* is the polynomial
`R_q(z) = ∑_{j=0}^{q} binom(q+j, q-j) C_j z^j`, where `C_j` is the `j`-th Catalan number.
Its coefficient of `z^j` counts the Schröder two-coloured binary trees with `q` vertices of
which `j` are black. This file also records, as propositions to be taken as hypotheses, the two
results of Defant on Schröder trees used in this section: the enumeration of Schröder trees by
black vertices, and the refined tree fertility formula for the troupe of Schröder trees.

## Main definitions

* `Polynomial.schroederFactor R q`: the polynomial `R_q` with coefficients in a semiring `R`.
* `SchroederTreesBlackGenFunEq`: the sum of `X ^ T.numBlackNodes` over the Schröder trees with
  `q` vertices is `Polynomial.schroederFactor R q`.
* `SchroederRefinedFertilityFormula`: for every `n ≥ 1` and `π ∈ S_n`,
  `∑_{𝒯 ∈ ↓𝐒↓, 𝒫(𝒯) = π} z^{black(𝒯)+1} = ∑_{q ∈ 𝒱(π)} ∏_{i=0}^{k} ∑_{T ∈ 𝐒, |T| = q_i}
  z^{black(T)+1}`, where `k = des(π)`.

## Implementation notes

The paper works in `ℝ[z]` with the color set `{black, white}`. The coefficients are natural
numbers, so the polynomial is defined over an arbitrary semiring `R`, through the cast `ℕ → R`;
the paper's `R_q` is `Polynomial.schroederFactor ℝ q`. The two cited identities are likewise
stated over an arbitrary (commutative) semiring and any color type `C` with
`BinaryTree.TreeColors C`, the extra colors being excluded by the local rule defining
`BinaryTree.schroederTrees`.

A decreasing labeling `𝒯 : BinaryTree (ℕ × C)` has postorder reading
`(𝒯.map Prod.fst).postorder` and `black(𝒯) = 𝒯.skeleton.numBlackNodes`. The sums are `finsum`s
over sets, the left one of the fertility formula exactly as in `List.schroederFiberPolynomial`
and the inner ones exactly as in `SchroederTreesBlackGenFunEq`, so that the statements line up.
The sets summed over are finite (`BinaryTree.finite_setOf_numNodes_eq`), so the `finsum`s are
honest finite sums.

## References

* [LogNarayana], Section 8 (Schröder factors and integral binary nestohedra).
* [Troupes] C. Defant, *Troupes, cumulants, and stack-sorting*, Theorem 4.5, Remark 4.4 and
  Example 4.12, citing Corollary 4.2 of [Gu].
-/

namespace Polynomial

variable (R : Type*) [Semiring R]

end Polynomial

open Polynomial

