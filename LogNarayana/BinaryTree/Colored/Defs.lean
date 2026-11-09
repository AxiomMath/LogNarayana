/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module
public import Mathlib
public import LogNarayana.Attr
public import LogNarayana.BinaryTree.Decreasing.Defs
public import LogNarayana.AuxiliaryDefinitions

/-!
# Colored binary plane trees and insertion

A *colored binary plane tree* with colors in `C` is a binary plane tree each of whose vertices
carries a color in `C`; it is an element of `BinaryTree C`, the label of a vertex being its color.
Two distinct colors `black` and `white` are distinguished. Every vertex `v = node a l r` has one of
four *types* `leaf`, `lu`, `ru`, `bin`, according to which of its subtrees `l`, `r` are nonempty.
This file defines the counts of vertices by type, by color, and of right edges, and the
*insertion* `∇_v(T₁, T₂)` of a colored binary plane tree `T₂` into `T₁` at a vertex `v` of `T₁`:
the subtree `S` of `T₁` rooted at `v` is replaced by a new black vertex with left subtree `S` and
right subtree `T₂`. A statistic `f` is *insertion-additive* if
`f (∇_v(T₁, T₂)) = f T₁ + f T₂` whenever `T₂` is nonempty.

## Main definitions

* `BinaryTree.TreeColors C`: a choice of two distinct colors `TreeColors.black` and
  `TreeColors.white` in `C`.
* `BinaryTree.VertexType`: the four-element set `𝔗 = {leaf, lu, ru, bin}` of vertex types.
* `BinaryTree.vertexType`: the type of the vertex whose left and right subtrees are `l` and `r`.
* `BinaryTree.numNodesOfType`: the number `n_τ(T)` of vertices of `T` of type `τ`.
* `BinaryTree.numRightEdges`: the number of right edges of `T`.
* `BinaryTree.numBlackNodes`, `BinaryTree.numWhiteNodes`: the numbers `black(T)` and `white(T)`
  of black and of white vertices of `T`.
* `BinaryTree.insertion T₁ v T₂`: the insertion `∇_v(T₁, T₂)`, for `v : Fin T₁.numNodes`.
* `BinaryTree.IsInsertionAdditive f`: the statistic `f` is insertion-additive.

## Implementation notes

The paper fixes a finite set of colors. Finiteness is not part of `TreeColors`: following
Mathlib's convention of unbundled finiteness, results that count colors assume `[Fintype C]`
alongside `[TreeColors C]`.

A vertex of a `BinaryTree α` is a node `node a l r`; its type is a function `vertexType l r` of
its two subtrees alone. Since `vertexType` is defined for every label type, the type of a vertex
of a colored or of a decreasing binary plane tree is literally its type in the underlying tree.
The counts are defined by structural recursion, as Mathlib's `BinaryTree.numNodes`.

The vertices of `T₁` are indexed by `Fin T₁.numNodes` in preorder: index `0` is the root of
`node a l r`, indices `1, …, |l|` are the vertices of `l` and the remaining indices those of `r`.
Thus "every vertex `v` of `T₁`" is `∀ v : Fin T₁.numNodes`, and the nonemptiness of `T₁` is
automatic once a vertex is given; that of `T₂` is the hypothesis `T₂ ≠ nil` where it is needed.
The paper takes insertion-additive statistics with values in `ℤ`; the definition is made for
values in any type with an addition.

## References

* [LogNarayana] *Log-Concavity in Narayana Transforms and Stack-Sorting Fibers*, Sections 5–6.
* [Troupes] C. Defant, *Troupes, cumulants, and stack-sorting*, Section 2.1.
-/

@[expose] public section

namespace BinaryTree

section VertexTypes

variable {α : Type*}

/-- The number of *right edges* of `T`, the edges from a vertex to its right child; equivalently
the number of vertices of `T` with a nonempty right subtree. -/
@[lognarayana "def_vertex_type_count", simp]
public def numRightEdges : BinaryTree α → ℕ
  | nil => 0
  | node _ l r =>
      numRightEdges l + numRightEdges r +
        match r with
        | nil => 0
        | node _ _ _ => 1

end VertexTypes

section ColorCounts

variable {C : Type*} [TreeColors C] [DecidableEq C]

end ColorCounts

section Insertion

variable {C : Type*} [TreeColors C]

variable {M : Type*} [Add M]

end Insertion

end BinaryTree

end
