/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module
public import Mathlib
public import LogNarayana.Attr
public import LogNarayana.BinaryTree.Colored.Defs
public import LogNarayana.Troupe.LocalRules.Defs
public import LogNarayana.AuxiliaryDefinitions

/-!
# Colored binary plane trees and insertion

Let `T₁`, `T₂` be colored binary plane trees and `v` a vertex of `T₁`. The vertices of the
insertion `∇_v(T₁, T₂)` are those of `T₁`, those of `T₂` and one new black vertex `v*`, with left
subtree the subtree of `T₁` at `v` and right subtree `T₂`. Every old vertex keeps its color and its
type. Consequently `black(∇_v(T₁, T₂)) = black(T₁) + black(T₂) + 1`, and, for nonempty `T₂`, the
number of right edges `n_ru + n_bin` grows by `n_ru(T₂) + n_bin(T₂) + 1`; so the statistics
`T ↦ black(T) + 1` and `T ↦ n_ru(T) + n_bin(T) + 1` are insertion-additive.

A *troupe* is a set `𝐓` of colored binary plane trees which is *black-peaked* (every vertex of
type `bin` of a tree in `𝐓` is `black`) and *insertion-closed and decomposition-closed*: for all
nonempty `T₁`, `T₂` and every vertex `v` of `T₁`, both `T₁` and `T₂` lie in `𝐓` if and only if
`∇_v(T₁, T₂)` lies in `𝐓`.

## Main definitions

* `BinaryTree.IsTroupe 𝒯`: the set `𝒯 ⊆ BinaryTree C` is a troupe.

## Main results

* `BinaryTree.vertexType_insertion`: the type of a vertex of `T₁` or of `T₂` in
  `BinaryTree.insertion T₁ v T₂` equals its type in `T₁`, resp. `T₂`.
* `BinaryTree.isInsertionAdditive_numBlackNodes_add_one`: `T ↦ black(T) + 1` is
  insertion-additive.
* `BinaryTree.isInsertionAdditive_numRightEdges_add_one`: `T ↦ n_ru(T) + n_bin(T) + 1` is
  insertion-additive.

## Implementation notes

Vertices of a tree `T` are indexed in preorder by `Fin T.numNodes`, as in
`BinaryTree.insertion`. In preorder, `∇_v(T₁, T₂)` lists the vertices of `T₁` before `v`, then
`v*`, then the `s` vertices of the subtree of `T₁` at `v`, then the vertices of `T₂`, then the
remaining vertices of `T₁`; this is the identification of vertices made in the paper, and
`vertexType_insertion` is stated on the preorder list of vertex types. The paper's hypothesis
that `T₂` is nonempty is not needed there.

The paper takes the insertion-additive statistics with values in `ℤ`; they are stated here for
their image under the cast `ℕ → M` into any additive monoid with one.

`IsTroupe` is defined here rather than with the other definitions because black-peakedness is
phrased with `BinaryTree.localRuleFamily`, the family cut out by the local rule of pairs `(t, c)`
with `t = bin → c = black`.

## References

* [LogNarayana] *Log-Concavity in Narayana Transforms and Stack-Sorting Fibers*, Section 6.
* [Troupes] C. Defant, *Troupes, cumulants, and stack-sorting*, Definition 2.1.
-/

public section

namespace BinaryTree

section Troupe

variable {C : Type*} [TreeColors C]

end Troupe

section VertexTypes

variable {C : Type*} [TreeColors C]

/-- Preorder list of vertex types. -/
private def types (T : BinaryTree C) : List VertexType :=
  BinaryTree.rec (motive := fun _ => List VertexType) []
    (fun _ l r ihl ihr => vertexType l r :: (ihl ++ ihr)) T

/-- Preorder list of subtree sizes. -/
private def sizes (T : BinaryTree C) : List ℕ :=
  BinaryTree.rec (motive := fun _ => List ℕ) []
    (fun _ l r ihl ihr => (l.numNodes + r.numNodes + 1) :: (ihl ++ ihr)) T

omit [TreeColors C] in
private lemma types_node (a : C) (l r : BinaryTree C) :
    types (node a l r) = vertexType l r :: (types l ++ types r) := rfl

omit [TreeColors C] in
private lemma sizes_node (a : C) (l r : BinaryTree C) :
    sizes (node a l r) = (l.numNodes + r.numNodes + 1) :: (sizes l ++ sizes r) := rfl

omit [TreeColors C] in
private lemma length_types (T : BinaryTree C) : (types T).length = T.numNodes := by
  induction T with
  | nil => rfl
  | node a l r ihl ihr => simp [types_node, ihl, ihr, numNodes]

omit [TreeColors C] in
private lemma length_sizes (T : BinaryTree C) : (sizes T).length = T.numNodes := by
  induction T with
  | nil => rfl
  | node a l r ihl ihr => simp [sizes_node, ihl, ihr, numNodes]

omit [TreeColors C] in
private lemma add_sizes_le (T : BinaryTree C) (i : ℕ) (hi : i < T.numNodes) :
    i + ((sizes T)[i]?).getD 0 ≤ T.numNodes := by
  induction T generalizing i with
  | nil => simp [numNodes] at hi
  | node a l r ihl ihr =>
    simp only [numNodes] at hi ⊢
    rcases i with _ | k
    · simp [sizes_node]
    · rw [sizes_node, List.getElem?_cons_succ]
      by_cases hk : k < l.numNodes
      · rw [List.getElem?_append_left (by rw [length_sizes]; exact hk)]
        have := ihl k hk; omega
      · rw [List.getElem?_append_right (by rw [length_sizes]; omega), length_sizes]
        have := ihr (k - l.numNodes) (by omega); omega

/-- An insertion is never the empty tree. -/
private lemma insertion_ne_nil (T : BinaryTree C) (v : Fin T.numNodes) (T₂ : BinaryTree C) :
    insertion T v T₂ ≠ nil := by
  cases T with
  | nil => exact v.elim0
  | node a l r =>
    simp only [insertion]
    split_ifs <;> simp

omit [TreeColors C] in
private lemma vertexType_congr {l r l' r' : BinaryTree C} (hl : l = nil ↔ l' = nil)
    (hr : r = nil ↔ r' = nil) : vertexType l r = vertexType l' r' := by
  cases l <;> cases r <;> cases l' <;> cases r' <;> simp_all

private lemma types_insertion (T : BinaryTree C) (v : Fin T.numNodes) (T₂ : BinaryTree C) :
    ∃ x, types (insertion T v T₂) = (types T).take v ++ x ::
      (((types T).drop v).take (((sizes T)[v.val]?).getD 0) ++ types T₂ ++
        (types T).drop (v + ((sizes T)[v.val]?).getD 0)) := by
  induction T with
  | nil => exact v.elim0
  | node a l r ihl ihr =>
    obtain ⟨v, hv⟩ := v
    simp only [numNodes] at hv
    simp only [insertion]
    split_ifs with h₀ h
    · subst h₀
      refine ⟨vertexType (node a l r) T₂, ?_⟩
      have := length_types (node a l r)
      simp only [numNodes] at this
      simp only [types_node, vertexType, List.length_cons, List.length_append,
        Nat.add_right_cancel_iff, List.cons_append, List.append_assoc, List.take_zero, sizes_node,
        lt_add_iff_pos_left, Order.lt_add_one_iff, zero_le, getElem?_pos, List.getElem_cons_zero,
        Option.getD_some, List.drop_zero, List.take_succ_cons, zero_add, List.drop_succ_cons,
        List.nil_append, List.cons.injEq, true_and] at this ⊢
      rw [List.take_of_length_le (by simp [length_types]),
        List.drop_eq_nil_of_le (by simp [length_types])]
      simp
    · obtain ⟨k, rfl⟩ : ∃ k, v = k + 1 := ⟨v - 1, by omega⟩
      simp only [Nat.add_sub_cancel] at h ⊢
      obtain ⟨x, hx⟩ := ihl ⟨k, h⟩
      refine ⟨x, ?_⟩
      have hb := add_sizes_le l k h
      have hl := length_types l
      have hsl : (sizes l)[k]? = (sizes l ++ sizes r)[k]? :=
        (List.getElem?_append_left (by rw [length_sizes]; exact h)).symm
      rw [types_node, types_node, sizes_node, hx,
        vertexType_congr (r' := r) (l' := l)
          (by simp only [insertion_ne_nil, false_iff]; rintro rfl; simp [numNodes] at h) Iff.rfl]
      simp only [List.getElem?_cons_succ, ← hsl] at hb ⊢
      generalize ((sizes l)[k]?).getD 0 = s at hb ⊢
      rw [Nat.add_right_comm k 1 s, List.take_succ_cons, List.drop_succ_cons, List.drop_succ_cons,
        List.take_append_of_le_length (by omega), List.drop_append_of_le_length (by omega),
        List.drop_append_of_le_length (by omega),
        List.take_append_of_le_length (by simp; omega)]
      simp
    · obtain ⟨k, rfl⟩ : ∃ k, v = (types l).length + k + 1 := ⟨v - 1 - l.numNodes, by
        rw [length_types]; omega⟩
      have hl := length_types l
      have hk : k < r.numNodes := by omega
      obtain ⟨x, hx⟩ := ihr ⟨k, hk⟩
      refine ⟨x, ?_⟩
      have hsr : (sizes l ++ sizes r)[(types l).length + k]? = (sizes r)[k]? := by
        rw [List.getElem?_append_right (by rw [length_sizes]; omega), length_sizes]
        congr 1; omega
      have hidx : (types l).length + k + 1 - 1 - l.numNodes = k := by omega
      simp only [hidx]
      rw [types_node, types_node, sizes_node, hx,
        vertexType_congr (r' := r) (l' := l) Iff.rfl
          (by simp only [insertion_ne_nil, false_iff]; rintro rfl; simp [numNodes] at hk),
        List.getElem?_cons_succ, hsr]
      generalize ((sizes r)[k]?).getD 0 = s
      rw [Nat.add_right_comm _ 1 s, List.take_succ_cons, List.drop_succ_cons, List.drop_succ_cons,
        List.take_append, List.drop_append, Nat.add_assoc, List.drop_append]
      simp [List.take_of_length_le, List.drop_eq_nil_of_le]

private lemma types_insertion_getElem? (T₁ : BinaryTree C) (v : Fin T₁.numNodes)
    (T₂ : BinaryTree C) :
    let s : ℕ := ((sizes T₁)[v.val]?).getD 0
    (∀ u : Fin T₁.numNodes,
      (types (insertion T₁ v T₂))[if u.val < v.val then u.val
          else if u.val < v.val + s then u.val + 1 else u.val + 1 + T₂.numNodes]? =
        (types T₁)[u.val]?) ∧
    (∀ u : Fin T₂.numNodes,
      (types (insertion T₁ v T₂))[v.val + 1 + s + u.val]? = (types T₂)[u.val]?) := by
  intro s
  have hs : ((sizes T₁)[v.val]?).getD 0 = s := rfl
  clear_value s
  obtain ⟨x, hx⟩ := types_insertion T₁ v T₂
  have hb := add_sizes_le T₁ v v.isLt
  have hl := length_types T₁
  have hl₂ := length_types T₂
  rw [hs] at hx hb
  rw [hx]
  refine ⟨fun u => ?_, fun u => ?_⟩ <;> have hu := u.isLt <;> try split_ifs
  all_goals
    simp only [List.getElem?_append, List.getElem?_take, List.getElem?_cons, List.getElem?_drop,
      List.length_take, List.length_append, List.length_drop, hl, hl₂]
    split_ifs <;> first | omega | rfl | (congr 1; omega)

/-- Insertion preserves the types of the old vertices: for colored binary plane trees `T₁`, `T₂`
and a vertex `v` of `T₁`, every vertex of `T₁` and every vertex of `T₂` has the same type
(`BinaryTree.vertexType`) in `insertion T₁ v T₂` as in `T₁`, resp. `T₂`. Vertices are preorder
indices; `types T` is the list of vertex types of `T` in preorder, and `s` is the size of the
subtree of `T₁` rooted at `v`. -/
@[lognarayana "lem_insertion_vertex_type"]
public theorem vertexType_insertion (T₁ : BinaryTree C) (v : Fin T₁.numNodes)
    (T₂ : BinaryTree C) :
    let types : BinaryTree C → List VertexType := fun T =>
      BinaryTree.rec (motive := fun _ => List VertexType) []
        (fun _ l r ihl ihr => vertexType l r :: (ihl ++ ihr)) T
    let sizes : BinaryTree C → List ℕ := fun T =>
      BinaryTree.rec (motive := fun _ => List ℕ) []
        (fun _ l r ihl ihr => (l.numNodes + r.numNodes + 1) :: (ihl ++ ihr)) T
    let s : ℕ := ((sizes T₁)[v.val]?).getD 0
    (∀ u : Fin T₁.numNodes,
      (types (insertion T₁ v T₂))[if u.val < v.val then u.val
          else if u.val < v.val + s then u.val + 1 else u.val + 1 + T₂.numNodes]? =
        (types T₁)[u.val]?) ∧
    (∀ u : Fin T₂.numNodes,
      (types (insertion T₁ v T₂))[v.val + 1 + s + u.val]? = (types T₂)[u.val]?) :=
        types_insertion_getElem? T₁ v T₂

omit [TreeColors C] in
private lemma vertexType_congr_left {l l' r : BinaryTree C} (hl : l ≠ nil) (hl' : l' ≠ nil) :
    vertexType l' r = vertexType l r := by
  cases l <;> cases l' <;> cases r <;> simp_all

omit [TreeColors C] in
private lemma vertexType_congr_right {l r r' : BinaryTree C} (hr : r ≠ nil) (hr' : r' ≠ nil) :
    vertexType l r' = vertexType l r := by
  cases l <;> cases r <;> cases r' <;> simp_all

/-- Inserting a nonempty `T₂` into `T₁` adds the vertex-type counts and one new binary vertex:
`n_τ(∇_v(T₁, T₂)) = n_τ(T₁) + n_τ(T₂) + [τ = bin]`. -/
private lemma numNodesOfType_insertion (τ : VertexType) :
    ∀ (T₁ : BinaryTree C) (v : Fin T₁.numNodes) (T₂ : BinaryTree C), T₂ ≠ nil →
      (insertion T₁ v T₂).numNodesOfType τ =
        T₁.numNodesOfType τ + T₂.numNodesOfType τ + if VertexType.binary = τ then 1 else 0
  | nil, v, _, _ => v.elim0
  | node a l r, v, T₂, h₂ => by
    unfold insertion
    by_cases h₀ : v.val = 0
    · rw [dif_pos h₀]
      have : vertexType (node a l r) T₂ = .binary := by cases T₂ <;> simp_all
      simp only [numNodesOfType, this]
    rw [dif_neg h₀]
    by_cases h : v.val - 1 < l.numNodes
    · rw [dif_pos h]
      have ih := numNodesOfType_insertion τ l ⟨v.val - 1, h⟩ T₂ h₂
      have hl : l ≠ nil := by rintro rfl; simp at h
      rw [numNodesOfType, numNodesOfType, ih,
        vertexType_congr_left hl (insertion_ne_nil _ _ _)]
      omega
    · rw [dif_neg h]
      have hv : v.val < l.numNodes + r.numNodes + 1 := v.isLt
      have ih := numNodesOfType_insertion τ r ⟨v.val - 1 - l.numNodes, by omega⟩ T₂ h₂
      have hr : r ≠ nil := by rintro rfl; simp at hv; omega
      rw [numNodesOfType, numNodesOfType, ih,
        vertexType_congr_right hr (insertion_ne_nil _ _ _)]
      omega

/-- The statistic `T ↦ n_ru(T) + n_bin(T) + 1`, the number of right edges of `T` plus one, is
insertion-additive on colored binary plane trees, with values in any additive monoid with one. -/
@[lognarayana "lem_right_edges_insertion_additive"]
public theorem isInsertionAdditive_numRightEdges_add_one (M : Type*) [AddMonoidWithOne M] :
    IsInsertionAdditive (fun T : BinaryTree C =>
      ((T.numNodesOfType .rightUnary + T.numNodesOfType .binary + 1 : ℕ) : M)) := by
  intro T₁ v T₂ h₂
  simp only [← Nat.cast_add, numNodesOfType_insertion _ T₁ v T₂ h₂, reduceCtorEq, if_false,
    if_true]
  congr 1
  omega

end VertexTypes

section BlackCount

variable {C : Type*} [TreeColors C] [DecidableEq C]

/-- Inserting `T₂` into `T₁` adds the black counts and one new black vertex. -/
private lemma numBlackNodes_insertion :
    ∀ (T₁ : BinaryTree C) (v : Fin T₁.numNodes) (T₂ : BinaryTree C),
      (insertion T₁ v T₂).numBlackNodes = T₁.numBlackNodes + T₂.numBlackNodes + 1
  | nil, v, _ => v.elim0
  | node a l r, v, T₂ => by
    unfold insertion
    split_ifs with h₀ h
    · simp
    · simp only [numBlackNodes, numBlackNodes_insertion l]
      omega
    · simp only [numBlackNodes, numBlackNodes_insertion r]
      omega

/-- The statistic `T ↦ black(T) + 1`, the number of black vertices plus one, is insertion-additive
on colored binary plane trees, with values in any additive monoid with one. -/
@[lognarayana "lem_black_insertion_additive"]
public theorem isInsertionAdditive_numBlackNodes_add_one (M : Type*) [AddMonoidWithOne M] :
    IsInsertionAdditive (fun T : BinaryTree C => ((T.numBlackNodes + 1 : ℕ) : M)) := by
  intro T₁ v T₂ _
  simp only [← Nat.cast_add, numBlackNodes_insertion]
  congr 1
  omega

end BlackCount

end BinaryTree

end
