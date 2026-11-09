/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module
public import Mathlib
public import LogNarayana.Attr
public import LogNarayana.StackSorting.AdoptableForest.Defs
public import LogNarayana.AuxiliaryDefinitions

/-!
# Operations on marked forests

The definitions documented here are stated in `LogNarayana.Definitions` and
`LogNarayana.AuxiliaryDefinitions`, which this module imports.

A *marked forest* on `[N] = {1, …, N}` is a pair `(par, L)` of a parent map `par` on `[N]` and a
set `L ⊆ [N]` of marked vertices. This file defines three operations on marked forests.

* The *concatenation* of `(par, L)` on `[N]` and `(par', L')` on `[N']` places the second forest
  to the right of the first: it is the parent map `par''` on `[N + N']` with `par'' v = par v` for
  `v ∈ [N]`, `par'' (N + v) = N + par' v` when `par' v ≠ ⊥` and `par'' (N + v) = ⊥` when
  `par' v = ⊥`, together with the marked set `L ∪ {N + v : v ∈ L'}`.
* *Adjoining a root* to `(par, L)` gives the tree `root(par, L)` on `[N + 1]`: its parent map
  `par°` sends `v ∈ [N]` to `par v` when `par v ≠ ⊥` and to the new root `N + 1` otherwise, and
  `par° (N + 1) = ⊥`. The marked set is `L` itself.
* The *marked singleton* `𝒮` is the forest on `[1]` whose parent map sends `1` to `⊥`, with
  marked set `{1}`.

## Main definitions

* `forestConcatParent N par par'`: the parent map of the concatenation.
* `forestConcatMarked N L L'`: the marked set of the concatenation.
* `forestAdjoinRootParent N par`: the parent map `par°` of the tree obtained by adjoining a root.
* `markedSingleton`: the pair `(par, L)` of the parent map of `𝒮` on `[1]` and `L = {1}`.

## Implementation notes

A marked forest is a pair (parent map, marked set) and the operations are defined componentwise.
No hypothesis on the inputs is needed to define them. The marked set of `root(par, L)` is `L`
unchanged, so only its parent map needs a definition. When the inputs are parent maps
(`IsParentMap`), so are the outputs: the concatenated parent map is `none` at `0` (it is
`par 0 = none`) and above `N + N'` (it is `par' (v - N) = none`), and `par°` is `none` at `0`, at
`N + 1` and above, whatever `par` is. As for every parent map in this library,
`par : ℕ → Option ℕ` is total, with `none` playing the role of `⊥`; the parent map of `𝒮` is
therefore the constant map `none`.

## References

* [LogNarayana] *Log-Concavity in Narayana Transforms and Stack-Sorting Fibers*, Section 4.
-/

@[expose] public section

end
