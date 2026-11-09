/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib
public import LogNarayana.Attr
public import LogNarayana.BinaryTree.Decreasing.Defs
public import LogNarayana.BinaryTree.Colored.Defs
public import LogNarayana.StackSorting.Descents.Defs
public import LogNarayana.StackSorting.StackSort.Defs
public import LogNarayana.AuxiliaryDefinitions

/-!
# Decreasing colored binary plane trees and their fiber descent polynomials

The definitions documented here are stated in `LogNarayana.Definitions` and
`LogNarayana.AuxiliaryDefinitions`, which this module imports.

For a finite set `A` of labels, a *decreasing colored binary plane tree on `A`* is a decreasing
binary plane tree `𝒯°` on `A` together with a coloring `χ : V(𝒯°) → C` of its vertices; its
vertices, labels, vertex types and readings `ℐ(𝒯) = ℐ(𝒯°)`, `𝒫(𝒯) = 𝒫(𝒯°)` are those of `𝒯°`.
Its *skeleton* `sk(𝒯) = (T°, χ)` is the colored binary plane tree obtained by forgetting the
labels, and a function `f` on colored binary plane trees is evaluated on `𝒯` through its
skeleton, `f(𝒯) = f(sk(𝒯))`.

For a colored binary plane tree `T` with `n` vertices, `↓T↓` is the set of decreasing colored
binary plane trees on `[n] = {1, …, n}` whose skeleton is `T`, and for a set `U` of colored
binary plane trees `↓U↓ = ⋃_{T ∈ U} ↓T↓`. For a permutation `π ∈ S_n`, the *fiber descent
polynomial* of `U` is `D_{π,U}(x) = ∑ x^{des(ℐ(𝒯))}`, the sum running over the trees `𝒯 ∈ ↓U↓`
with `𝒫(𝒯) = π`.

## Main definitions

* `BinaryTree.decreasingColoredTrees C A`: the set of decreasing colored binary plane trees on
  `A` with colors in `C`.
* `BinaryTree.skeleton T`: the colored binary plane tree obtained by forgetting the labels.
* `BinaryTree.decreasingLabelings T`: the set `↓T↓`.
* `BinaryTree.familyDecreasingLabelings U`: the set `↓U↓ = ⋃ T ∈ U, ↓T↓`.
* `List.familyFiberDescentPolynomial R U π`: the polynomial `D_{π,U}(x)`.

## Implementation notes

A pair `(𝒯°, χ)` is encoded as a single tree `T : BinaryTree (α × C)` storing at each vertex the
pair (label, color): the underlying decreasing tree is `T.map Prod.fst` and the coloring is read
off as `T.map Prod.snd`. This is a bijection between pairs `(𝒯°, χ)` with `χ` a map on the vertex
set of `𝒯°` and trees `T` with `T.map Prod.fst = 𝒯°`, and it avoids a separate type of vertices.
Accordingly the label set, the vertex types and the readings of `T` are those of
`T.map Prod.fst`, and the skeleton is `T.map Prod.snd`. The convention `f(𝒯) = f(sk(𝒯))` is not
a separate declaration: one writes `f T.skeleton`, e.g. `T.skeleton.numBlackNodes`.

The paper takes labels in `ℤ` and colors in a fixed finite set carrying the distinguished colors
of `BinaryTree.TreeColors`; the definitions need neither, and are stated for any label type and
any type of colors. In `↓T↓` the labels are natural numbers on `[n] = Finset.Icc 1 n`, and the
number of vertices `n` is `T.numNodes`, not a parameter.

A tree on `[n]` has postorder reading in `S_n`, so in `D_{π,U}` the condition `𝒫(𝒯) = π` forces
`n = π.length`; neither `n` nor the hypothesis `π ∈ S_n` is a parameter, and off `S_n` the
polynomial is `0`. The paper defines `D_{π,U}` for a troupe `U`; the definition makes sense for
every set `U`. The sum is a `finsum`: for a finite set of colors, as in the paper, the trees in
`↓U↓` on `[n]` are finitely many, and the `finsum` is the paper's sum. Coefficients are taken in
an arbitrary semiring `R`; the paper's `ℝ[x]` is `R = ℝ`.

## References

* [LogNarayana] *Log-Concavity in Narayana Transforms and Stack-Sorting Fibers*, Section 6.3.
-/

@[expose] public section

open Polynomial

namespace BinaryTree

section DecreasingColoredTrees

variable {α : Type*} [DecidableEq α] [LT α] (C : Type*)

end DecreasingColoredTrees

section Skeleton

variable {α C : Type*}

end Skeleton

section DecreasingLabelings

variable {C : Type*}

end DecreasingLabelings

end BinaryTree

namespace List

variable {C : Type*}

end List

end
