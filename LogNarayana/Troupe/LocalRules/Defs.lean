/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module
public import LogNarayana.BinaryTree.Colored.Defs
public import LogNarayana.AuxiliaryDefinitions

/-!
# Troupes defined by local rules

The definitions documented here are stated in `LogNarayana.Definitions` and
`LogNarayana.AuxiliaryDefinitions`, which this module imports.

A *local rule* is a set `P ⊆ 𝔗 × C` of admissible pairs (vertex type, color). The family
`𝐔_P` it cuts out consists of the colored binary plane trees `T = (T°, χ)` such that
`(type_T(v), χ(v)) ∈ P` for every vertex `v` of `T`. The empty tree has no vertex, so it
belongs to `𝐔_P` for every `P`.

Three families of this form are used later:

* the binary plane trees, regarded as colored binary plane trees all of whose vertices are
  `black`: `𝐁 = 𝐔_{𝔗 × {black}}`;
* for sets of colors `X_L, X_a, X_b ⊆ 𝐂`, the family `𝐔_{X_L,X_a,X_b}` of trees in which every
  leaf has a color in `X_L`, every unary vertex with a left child a color in `X_a`, every unary
  vertex with a right child a color in `X_b`, and every binary vertex is black, cut out by
  `P = ({leaf} × X_L) ∪ ({lu} × X_a) ∪ ({ru} × X_b) ∪ {(bin, black)}`; when `|X_L| = L`,
  `|X_a| = a`, `|X_b| = b` the paper writes `𝐔_{L,a,b}`;
* the *Schröder two-colored binary trees* `𝐒 = 𝖲𝖼𝗁`, whose vertices are `black` or `white` and
  in which every vertex having a left child (of type `lu` or `bin`) is `black`, cut out by
  `P = (𝔗 × {black}) ∪ {(leaf, white), (ru, white)}`.

## Main definitions

* `BinaryTree.localRuleFamily P`: the family `𝐔_P` cut out by the local rule `P`.
* `BinaryTree.blackTrees C`: the family `𝐁` of trees all of whose vertices are black.
* `BinaryTree.localColorFamily X_L X_a X_b`: the family `𝐔_{X_L,X_a,X_b}`.
* `BinaryTree.schroederTrees C`: the family `𝐒` of Schröder two-colored binary trees.

## Implementation notes

A colored binary plane tree with colors in `C` is an element of `BinaryTree C`, the color of
a vertex `node a l r` being its label `a` and its type being `BinaryTree.vertexType l r`. The
condition "every vertex satisfies the rule" is defined by structural recursion: the empty tree
satisfies it, and `node a l r` satisfies it iff its root does and both subtrees `l`, `r` do.
The defining equations hold by `rfl`.

Colors range over an arbitrary type `C`; the three concrete families need a distinguished
`black` (and `white`), supplied by `[TreeColors C]`. Colors of `C` other than those a rule
names are excluded by it, so the families agree with the paper's for its finite color set.
Each concrete family is defined as `localRuleFamily` of its rule, so that results about
families cut out by local rules apply to it directly.

## References

* [LogNarayana] *Log-Concavity in Narayana Transforms and Stack-Sorting Fibers*, Section 5.
* [Troupes] C. Defant, *Troupes, cumulants, and stack-sorting*, Section 2.1.
-/

@[expose] public section

namespace BinaryTree

end BinaryTree

end
