/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib
public import LogNarayana.Attr

/-!
# Names for objects spelled through Mathlib

Three objects of the paper are, in this library, written directly as Mathlib terms of a
particular shape. This file gives each of them a name, reducibly equal to that term, so that
every occurrence of the term in the development is an occurrence of the named object.

## Main definitions

* `BinaryTree.ColoredBinaryTree C`: the colored binary plane trees with colors in `C`, that is,
  `BinaryTree C`, the color of a vertex being its label.
* `Finset.rightEndpoints M`: the right endpoints `R(M) = {b : (a, b) ∈ M}` of a finite set of
  pairs, that is, `M.image Prod.snd`.
* `Matrix.NegSemidef C`: the matrix `C` is negative semidefinite, that is, `(-C).PosSemidef`.

## Implementation notes

All three are `abbrev`s, so the development's own spellings (`BinaryTree C`,
`M.image Prod.snd`, `(-C).PosSemidef`) unfold to them by reducible unfolding.

The distinguished colors `black` and `white` are the class `BinaryTree.TreeColors C`, assumed
alongside `ColoredBinaryTree C` where they are used; the finiteness of the color set is assumed
as `[Finite C]` or `[Fintype C]` where it is used. A binary plane tree with labels in `α` is
regarded as a colored one by `BinaryTree.map (fun _ => TreeColors.black)`.

## References

* [LogNarayana] *Log-Concavity in Narayana Transforms and Stack-Sorting Fibers*, Sections 3, 4
  and 5.
-/

@[expose] public section

namespace BinaryTree

/-- The type of *colored binary plane trees* with colors in `C`: a (possibly empty) binary plane
tree together with a color in `C` at each vertex, encoded as `BinaryTree C`, the label of a
vertex being its color. -/
@[lognarayana "def_colored_binary_tree"]
abbrev ColoredBinaryTree (C : Type*) : Type _ := BinaryTree C

end BinaryTree

namespace Finset

/-- The set `R(M) = {b : (a, b) ∈ M for some a}` of *right endpoints* of a finite set `M` of
pairs. -/
@[lognarayana "def_matching_right_endpoints"]
abbrev rightEndpoints {α β : Type*} [DecidableEq β] (M : Finset (α × β)) : Finset β :=
  M.image Prod.snd

end Finset

namespace Matrix

/-- A square matrix `C` is *negative semidefinite*, `C ⪯ 0`, if `-C` is positive semidefinite.
For a real matrix this says that `C` is symmetric and `wᵀ C w ≤ 0` for every vector `w`. -/
@[lognarayana "def_neg_semidef"]
abbrev NegSemidef {n R : Type*} [Ring R] [PartialOrder R] [StarRing R] (C : Matrix n n R) :
    Prop :=
  (-C).PosSemidef

end Matrix

end
