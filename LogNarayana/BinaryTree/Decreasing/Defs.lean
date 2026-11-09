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
# Binary plane trees, decreasing trees, inorder and postorder readings

The definitions documented here are stated in `LogNarayana.Definitions` and
`LogNarayana.AuxiliaryDefinitions`, which this module imports.

Binary plane trees with labels in `X` are Mathlib's `BinaryTree X`: a tree is empty (`∅`) or
`⟨m; T_L, T_R⟩`, a root labelled `m` with left and right subtrees `T_L` and `T_R`. This file
defines the statistics and readings of such trees used throughout the paper, each by recursion
on the tree.

* The number `bin(T)` of *binary* vertices, those whose left and right subtrees are both
  nonempty.
* The *inorder reading* `I(∅) = ∅`, `I(⟨m; T_L, T_R⟩) = I(T_L) m I(T_R)`, and the *postorder
  reading* `𝒫(∅) = ∅`, `𝒫(⟨m; T_L, T_R⟩) = 𝒫(T_L) 𝒫(T_R) m`.
* The label set `Lab(T)`, and the sets `LC(T)` and `RC(T)` of labels of vertices having a
  nonempty left, respectively right, subtree.
* Decreasing trees: `T` is decreasing if its labels are pairwise distinct and every vertex
  carries a larger label than every vertex below it; `DBT(A)` is the set of decreasing trees
  with label set `A`.

## Main definitions

* `BinaryTree.numBinaryNodes`: the number of vertices having two nonempty subtrees.
* `BinaryTree.inorder`, `BinaryTree.postorder`: the inorder and postorder readings, as lists.
* `BinaryTree.labels`: the finite set of labels occurring in a tree.
* `BinaryTree.leftChildLabels`, `BinaryTree.rightChildLabels`: the labels of vertices having a
  left, respectively right, child.
* `BinaryTree.IsDecreasing`: the predicate `dec` on binary plane trees.
* `BinaryTree.decreasingTrees`: the set `DBT(A)` of decreasing binary plane trees on `A`.

## Implementation notes

The paper labels its trees by integers; every definition here is stated for an arbitrary label
type, assuming only decidable equality (to form label sets in `Finset α`) and `<` (to compare
labels), and the paper's notions are the case `α = ℤ`. Case distinctions on whether a subtree
is empty are matches on its constructor. The condition that every label below a vertex is
smaller than it is imposed against the whole label sets of the subtrees, which for distinct
labels is equivalent to the paper's parent-larger-than-children condition by transitivity
along paths. The name `numBinaryNodes` follows Mathlib's `BinaryTree.numNodes` and
`BinaryTree.numLeaves`.

## References

* [LogNarayana] *Log-Concavity in Narayana Transforms and Stack-Sorting Fibers*, Sections 1–2.
-/

@[expose] public section

namespace BinaryTree

variable {α : Type*}

variable [DecidableEq α]

variable [LT α]

end BinaryTree

end
