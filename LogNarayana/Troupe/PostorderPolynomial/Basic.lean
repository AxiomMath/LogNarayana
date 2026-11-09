/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib
public import LogNarayana.Attr
public import LogNarayana.Troupe.PostorderPolynomial.Defs
public import LogNarayana.BinaryTree.Decreasing.Defs
public import LogNarayana.BinaryTree.Colored.Defs
public import LogNarayana.StackSorting.Descents.Defs
public import LogNarayana.StackSorting.FiberPolynomials.Defs
public import LogNarayana.Troupe.LocalRules.Defs
public import LogNarayana.StackSorting.StackSort.Defs
public import LogNarayana.BinaryTree.Decreasing.Basic
public import LogNarayana.StackSorting.Descents.Basic
public import LogNarayana.StackSorting.StackSort.Basic

/-!
# Decreasing colored trees and postorder generating polynomials

In a nonempty binary plane tree the leaves outnumber the binary vertices by one, and in a
decreasing binary plane tree `T` the descents of the inorder reading `ℐ(T)` correspond to the
vertices having a right child: `des(ℐ(T)) = n_ru(T) + n_bin(T)`.

A permutation `σ ∈ S_n` is the inorder reading of exactly one decreasing binary plane tree on
`[n]`, whose postorder reading is `s(σ)`, so a sum over the stack-sorting fiber `s⁻¹(π)` is a sum
over the decreasing trees on `[n]` with postorder reading `π`. There are `n! |C|ⁿ` decreasing
colored binary plane trees on `[n]` with colors in a finite set `C`, and hence only finitely many
colored binary plane trees of each size.

For a local rule `P ⊆ 𝔗 × C`, the decreasing labelings of the trees of the troupe `𝐔_P` with
postorder reading `π` are the decreasing trees on `[n]` with postorder reading `π`, each vertex
colored by an admissible color, so a weighted sum over them factors vertex by vertex. For the
troupe `𝐁` of all-black trees this recovers the fiber descent polynomial: `D_{π,𝐁} = D_π`.

## Main results

* `BinaryTree.numNodesOfType_leaf_eq_numNodesOfType_binary_add_one`: `n_leaf(T) = n_bin(T) + 1`
  for `T ≠ nil`.
* `BinaryTree.numDescents_inorder_of_isDecreasing`: `des(ℐ(T)) = n_ru(T) + n_bin(T)` for a
  decreasing tree `T`.
* `List.sum_stackFiber_eq_finsum_decreasingTrees`: reindexing a sum over `s⁻¹(π)` by decreasing
  binary plane trees.
* `BinaryTree.finite_decreasingColoredTrees_and_ncard`: the decreasing colored trees on `[n]`
  are finitely many, `n! * |C| ^ n` of them.
* `BinaryTree.finite_setOf_numNodes_eq`: finitely many colored binary plane trees of each size.
* `BinaryTree.finsum_familyDecreasingLabelings_localRuleFamily`: summing over the colorings
  allowed by a local rule.
* `List.familyFiberDescentPolynomial_blackTrees`: `D_{π,𝐁}(x) = D_π(x)`.

## Implementation notes

A decreasing colored tree is a `BinaryTree (ℕ × C)` whose underlying decreasing tree is
`𝒯.map Prod.fst`; a product over the vertices of a tree is written by structural recursion
(`BinaryTree.rec`), the factor at a vertex `node a l r` depending on its entry `a` and on its type
`vertexType l r`.

Several hypotheses of the paper are dropped as unused. The reindexing identity holds for every
list `π`, with `n` its length: off `S_n` both sides are empty sums, and for `n = 0` both are
`g []`; its values lie in any additive commutative monoid. The local rule identity needs only
that each fiber `P_τ = {c | (τ, c) ∈ P}` is finite, holds over a commutative semiring, and holds
for `n = 0`. The identity `D_{π,𝐁} = D_π` holds for `n = 0` too, over any semiring; it is first
proved over `ℕ`, where the coefficients commute, and transported along `ℕ → R`. The descent count
holds for every decreasing tree over a preorder, and finiteness of the colored trees of a given
size needs only `Finite C`, not the distinguished colors.

## References

* [LogNarayana] *Log-Concavity in Narayana Transforms and Stack-Sorting Fibers*, Sections 5, 6.1
  and 6.3.
-/

open BinaryTree Polynomial

/-! ### Leaves and right children of binary plane trees -/

namespace BinaryTree

/-- For every binary plane tree, `n_leaf(T) = n_bin(T) + [T ≠ nil]`. -/
private theorem numNodesOfType_leaf_eq {α : Type*} :
    ∀ T : BinaryTree α, T.numNodesOfType .leaf =
      T.numNodesOfType .binary + (match T with | nil => 0 | node _ _ _ => 1)
  | nil => rfl
  | node _ l r => by
    have := numNodesOfType_leaf_eq l
    have := numNodesOfType_leaf_eq r
    cases l <;> cases r <;> simp_all [numNodesOfType, vertexType]
    all_goals omega

/-- In a nonempty binary plane tree, `n_leaf(T) = n_bin(T) + 1`. -/
@[lognarayana "lem_tree_leaf_count"]
public theorem numNodesOfType_leaf_eq_numNodesOfType_binary_add_one {α : Type*}
    (T : BinaryTree α) (hT : T ≠ nil) :
    T.numNodesOfType .leaf = T.numNodesOfType .binary + 1 := by
  cases T with
  | nil => exact absurd rfl hT
  | node a l r => exact numNodesOfType_leaf_eq (node a l r)

/-- Every plane tree has `n_ru + n_bin` right edges. -/
private theorem numRightEdges_eq {α : Type*} (T : BinaryTree α) :
    T.numRightEdges = T.numNodesOfType .rightUnary + T.numNodesOfType .binary := by
  induction T with
  | nil => rfl
  | node m l r ihl ihr =>
    simp only [numRightEdges, numNodesOfType, ihl, ihr]
    cases l <;> cases r <;> simp [vertexType] <;> omega

private theorem toFinset_inorder {α : Type*} [DecidableEq α] (T : BinaryTree α) :
    T.inorder.toFinset = T.labels := by
  induction T with
  | nil => rfl
  | node m l r ihl ihr =>
    simp only [inorder, List.toFinset_append, List.toFinset_cons, ihl, ihr, labels]
    ext
    simp

private theorem rightChildLabels_subset {α : Type*} [DecidableEq α] (T : BinaryTree α) :
    T.rightChildLabels ⊆ T.labels := by
  induction T with
  | nil => simp
  | node m l r ihl ihr =>
    refine Finset.union_subset (Finset.union_subset_union
      (ihl.trans Finset.subset_union_right) ihr) ?_
    cases r <;> simp [labels]

private theorem nodup_inorder {α : Type*} [DecidableEq α] [Preorder α] {T : BinaryTree α}
    (hT : T.IsDecreasing) : T.inorder.Nodup := by
  induction T with
  | nil => exact List.nodup_nil
  | node m l r ihl ihr =>
    obtain ⟨hl, hr, hdisj, hlt⟩ := hT
    simp only [← toFinset_inorder, Finset.mem_union, List.mem_toFinset,
      List.disjoint_toFinset_iff_disjoint] at hlt hdisj
    rw [inorder, List.nodup_append, List.nodup_cons]
    refine ⟨ihl hl, ⟨fun h => (hlt m (.inr h)).false, ihr hr⟩, ?_⟩
    rintro a ha b hb rfl
    rcases List.mem_cons.1 hb with rfl | hb
    · exact (hlt a (.inl ha)).false
    · exact hdisj ha hb

/-- In a decreasing tree the labels are distinct, so `|RC(T)|` is the number of right edges. -/
private theorem card_rightChildLabels {α : Type*} [DecidableEq α] [Preorder α]
    {T : BinaryTree α} (hT : T.IsDecreasing) : T.rightChildLabels.card = T.numRightEdges := by
  induction T with
  | nil => rfl
  | node m l r ihl ihr =>
    obtain ⟨hl, hr, hdisj, hlt⟩ := hT
    have hm : m ∉ l.rightChildLabels ∪ r.rightChildLabels := fun h =>
      (hlt m (Finset.union_subset_union (rightChildLabels_subset l)
        (rightChildLabels_subset r) h)).false
    have hd := hdisj.mono (rightChildLabels_subset l) (rightChildLabels_subset r)
    cases r with
    | nil => simpa [Finset.card_union_of_disjoint hd] using congr($(ihl hl) + $(ihr hr))
    | node b rl rr =>
      rw [rightChildLabels, Finset.card_union_of_disjoint (Finset.disjoint_singleton_right.2 hm),
        Finset.card_union_of_disjoint hd, ihl hl, ihr hr, Finset.card_singleton, numRightEdges]

/-- For a decreasing binary plane tree `T`, the number of descents of its inorder reading equals
`n_ru(T) + n_bin(T)`, the number of its vertices having a right child. -/
@[lognarayana "lem_right_child_count_eq_des"]
public theorem numDescents_inorder_of_isDecreasing {α : Type*} [Preorder α] [DecidableEq α]
    [DecidableLT α] {T : BinaryTree α} (hT : T.IsDecreasing) :
    T.inorder.numDescents =
      T.numNodesOfType .rightUnary + T.numNodesOfType .binary := by
  rw [← _root_.card_descentTops (nodup_inorder hT),
    descentTops_inorder_of_mem_decreasingTrees (A := T.labels) ⟨hT, rfl⟩,
    card_rightChildLabels hT, numRightEdges_eq]

end BinaryTree

/-! ### Reindexing a stack-sorting fiber by decreasing trees -/

namespace List

/-- The stack-sorting fiber `s⁻¹(π)` is the set of `σ ∈ S_n` with `s(σ) = π`. -/
private lemma mem_stackFiber_iff' {π σ : List ℕ} :
    σ ∈ List.stackFiber π ↔ σ ∈ permWords π.length ∧ σ.stackSort = π := by
  simp [List.stackFiber, mem_permWords_iff_perm]

/-- The inorder reading is a bijection from the decreasing trees on `[n]` with postorder reading
`π` onto the stack-sorting fiber `s⁻¹(π)`, where `n` is the length of `π`. -/
private lemma bijOn_inorder_stackFiber (π : List ℕ) :
    Set.BijOn inorder
      {T | T ∈ decreasingTrees (Finset.Icc 1 π.length) ∧ T.postorder = π}
      ↑(List.stackFiber π) := by
  have hbij := bijOn_inorder_decreasingTrees_Icc π.length
  refine ⟨fun T ⟨hT, hp⟩ => ?_, hbij.injOn.mono fun T hT => hT.1, fun σ hσ => ?_⟩
  · rw [Finset.mem_coe, mem_stackFiber_iff', stackSort_inorder_of_mem_decreasingTrees hT]
    exact ⟨hbij.mapsTo hT, hp⟩
  · rw [Finset.mem_coe, mem_stackFiber_iff'] at hσ
    obtain ⟨T, hT, rfl⟩ := hbij.surjOn hσ.1
    exact ⟨T, ⟨hT, (stackSort_inorder_of_mem_decreasingTrees hT).symm.trans hσ.2⟩, rfl⟩

/-- Reindexing a sum over the stack-sorting fiber `s⁻¹(π)` by decreasing binary plane trees:
`∑_{σ ∈ s⁻¹(π)} g(σ)` equals the sum of `g(𝓘(T))` over the decreasing binary plane trees `T` on
`[n]`, `n = |π|`, with postorder reading `𝒫(T) = π`. -/
@[lognarayana "lem_fiber_tree_reindex"]
public theorem sum_stackFiber_eq_finsum_decreasingTrees {M : Type*} [AddCommMonoid M]
    (π : List ℕ) (g : List ℕ → M) :
    ∑ σ ∈ stackFiber π, g σ =
      ∑ᶠ (T : BinaryTree ℕ) (_ : T ∈ decreasingTrees (Finset.Icc 1 π.length) ∧
        T.postorder = π), g T.inorder := by
  rw [← finsum_mem_coe_finset]
  exact (finsum_mem_eq_of_bijOn inorder (bijOn_inorder_stackFiber π) fun _ _ => rfl).symm

end List

/-! ### Counting decreasing colored binary plane trees -/

namespace BinaryTree

/-- The trees obtained from `S` by attaching an element of `C` to each vertex form a finite set
with `|C| ^ (number of vertices of S)` elements. -/
private lemma finite_and_ncard_fiber {β : Type*} (C : Type*) [Finite C] (S : BinaryTree β) :
    {T : BinaryTree (β × C) | T.map Prod.fst = S}.Finite ∧
      {T : BinaryTree (β × C) | T.map Prod.fst = S}.ncard = Nat.card C ^ S.numNodes := by
  induction S with
  | nil =>
    have : {T : BinaryTree (β × C) | T.map Prod.fst = nil} = {nil} := by
      ext T
      cases T <;> simp [BinaryTree.map]
    simp [this]
  | node m l r ihl ihr =>
    have : {T : BinaryTree (β × C) | T.map Prod.fst = node m l r} =
        (fun p : C × BinaryTree (β × C) × BinaryTree (β × C) => node (m, p.1) p.2.1 p.2.2) ''
          (Set.univ ×ˢ {T | T.map Prod.fst = l} ×ˢ {T | T.map Prod.fst = r}) := by
      ext T
      cases T with
      | nil => simp [BinaryTree.map]
      | node a Tl Tr =>
        obtain ⟨a, c⟩ := a
        simp only [BinaryTree.map, node.injEq, Set.mem_ofPred_eq, Set.mem_image, Set.mem_prod,
          Set.mem_univ, true_and, Prod.exists, Prod.mk.injEq]
        constructor
        · rintro ⟨rfl, h₁, h₂⟩
          exact ⟨c, Tl, Tr, ⟨h₁, h₂⟩, ⟨rfl, rfl⟩, rfl, rfl⟩
        · rintro ⟨c', Tl', Tr', ⟨h₁, h₂⟩, ⟨rfl, rfl⟩, rfl, rfl⟩
          exact ⟨rfl, h₁, h₂⟩
    have hinj : Function.Injective
        (fun p : C × BinaryTree (β × C) × BinaryTree (β × C) => node (m, p.1) p.2.1 p.2.2) := by
      rintro ⟨c, a, b⟩ ⟨c', a', b'⟩ h
      simp only [node.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨-, rfl⟩, rfl, rfl⟩ := h
      rfl
    rw [this]
    refine ⟨(Set.finite_univ.prod (ihl.1.prod ihr.1)).image _, ?_⟩
    rw [Set.ncard_image_of_injective _ hinj, Set.ncard_prod, Set.ncard_prod, Set.ncard_univ,
      ihl.2, ihr.2, BinaryTree.numNodes]
    ring

private lemma length_inorder {α : Type*} (S : BinaryTree α) : S.inorder.length = S.numNodes := by
  induction S with
  | nil => rfl
  | node m l r ihl ihr =>
    simp [BinaryTree.inorder, BinaryTree.numNodes, ihl, ihr]
    ring

/-- `S_n` is the set of rearrangements of `1 2 ⋯ n`. -/
private lemma permWords_eq (n : ℕ) :
    permWords n = ↑(List.range' 1 n).permutations.toFinset := by
  ext σ
  simp only [Finset.mem_coe, List.mem_toFinset, List.mem_permutations]
  have hr : (List.range' 1 n).toFinset = Finset.Icc 1 n := by
    ext a
    simp only [List.mem_toFinset, List.mem_range'_1, Finset.mem_Icc]
    omega
  constructor
  · rintro ⟨⟨hnd, -⟩, -, hl⟩
    exact List.perm_of_nodup_nodup_toFinset_eq hnd List.nodup_range' (hl.trans hr.symm)
  · intro hp
    refine ⟨⟨hp.nodup_iff.2 List.nodup_range', fun a ha => ?_⟩, by simp [hp.length_eq], ?_⟩
    · have := hp.subset ha
      simp [List.mem_range'] at this
      omega
    · rw [List.letters, List.toFinset_eq_of_perm _ _ hp, hr]

/-- There are `n!` decreasing binary plane trees on `[n]`, transported from `|S_n| = n!` along
the inorder reading. -/
private lemma finite_and_ncard_decreasingTrees_Icc (n : ℕ) :
    (decreasingTrees (Finset.Icc 1 n)).Finite ∧
      (decreasingTrees (Finset.Icc 1 n)).ncard = n.factorial := by
  have hbij := bijOn_inorder_decreasingTrees_Icc n
  refine ⟨Set.Finite.of_finite_image
    (hbij.image_eq ▸ permWords_eq n ▸ Finset.finite_toSet _) hbij.injOn, ?_⟩
  rw [← Set.InjOn.ncard_image hbij.injOn, hbij.image_eq, permWords_eq, Set.ncard_coe_finset,
    List.toFinset_card_of_nodup (List.nodup_permutations _ List.nodup_range'),
    List.length_permutations, List.length_range']

/-- A decreasing tree on `[n]` has `n` vertices. -/
private lemma numNodes_of_mem_decreasingTrees_Icc {n : ℕ} {S : BinaryTree ℕ}
    (hS : S ∈ decreasingTrees (Finset.Icc 1 n)) : S.numNodes = n := by
  rw [← length_inorder]
  exact ((bijOn_inorder_decreasingTrees_Icc n).mapsTo hS).2.1

/-- For every `n`, the set of decreasing colored binary plane trees on `[n]` with colors in a
finite type `C` is finite, of cardinality `n! * |C| ^ n`. -/
@[lognarayana "lem_decreasing_colored_finite"]
public theorem finite_decreasingColoredTrees_and_ncard (C : Type*) [Finite C] (n : ℕ) :
    (decreasingColoredTrees C (Finset.Icc 1 n)).Finite ∧
      (decreasingColoredTrees C (Finset.Icc 1 n)).ncard = n.factorial * Nat.card C ^ n := by
  obtain ⟨hD, hDcard⟩ := finite_and_ncard_decreasingTrees_Icc n
  have hU : decreasingColoredTrees C (Finset.Icc 1 n) =
      ⋃ S ∈ decreasingTrees (Finset.Icc 1 n), {T : BinaryTree (ℕ × C) | T.map Prod.fst = S} := by
    ext T
    simp [decreasingColoredTrees]
  have hfin S := (finite_and_ncard_fiber C (β := ℕ) S).1
  rw [hU, hD.ncard_biUnion (fun S _ => hfin S)
    fun S _ S' _ h => Set.disjoint_left.2 fun T h₁ h₂ => h (h₁.symm.trans h₂)]
  refine ⟨hD.biUnion fun S _ => hfin S, ?_⟩
  rw [finsum_mem_congr rfl fun S hS => by
      rw [(finite_and_ncard_fiber C S).2, numNodes_of_mem_decreasingTrees_Icc hS],
    finsum_mem_eq_finite_toFinset_sum _ hD, Finset.sum_const, smul_eq_mul,
    ← Set.ncard_eq_toFinset_card _ hD, hDcard]

/-- Label the vertices of `t` by `k + 1, …, k + t.numNodes` in postorder. -/
private def postLabel {C : Type*} : BinaryTree C → ℕ → BinaryTree (ℕ × C)
  | nil, _ => nil
  | node c l r, k =>
      node (k + l.numNodes + r.numNodes + 1, c) (postLabel l k) (postLabel r (k + l.numNodes))

private lemma skeleton_postLabel {C : Type*} (t : BinaryTree C) (k : ℕ) :
    (postLabel t k).skeleton = t := by
  induction t generalizing k with
  | nil => rfl
  | node c l r ihl ihr => simp [postLabel, BinaryTree.map, ihl, ihr]

private lemma labels_postLabel {C : Type*} (t : BinaryTree C) (k : ℕ) :
    ((postLabel t k).map Prod.fst).labels = Finset.Ioc k (k + t.numNodes) := by
  induction t generalizing k with
  | nil => simp [postLabel, BinaryTree.map]
  | node c l r ihl ihr =>
    simp only [postLabel, BinaryTree.map, labels, ihl, ihr, numNodes]
    ext x
    simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_Ioc]
    omega

private lemma isDecreasing_postLabel {C : Type*} (t : BinaryTree C) (k : ℕ) :
    ((postLabel t k).map Prod.fst).IsDecreasing := by
  induction t generalizing k with
  | nil => simp [postLabel, BinaryTree.map]
  | node c l r ihl ihr =>
    simp only [postLabel, BinaryTree.map, IsDecreasing, ihl, ihr, labels_postLabel, true_and,
      Finset.disjoint_left, Finset.mem_union, Finset.mem_Ioc]
    exact ⟨fun x hx hx' => by omega, fun x hx => by omega⟩

/-- The postorder labelling of `t` is a decreasing colored tree on `[t.numNodes]`. -/
private lemma postLabel_mem_decreasingColoredTrees {C : Type*} (t : BinaryTree C) :
    postLabel t 0 ∈ decreasingColoredTrees C (Finset.Icc 1 t.numNodes) := by
  refine ⟨isDecreasing_postLabel t 0, ?_⟩
  rw [labels_postLabel, zero_add]
  rfl

/-- For a finite color set `C` and every `q`, the set of colored binary plane trees with colors
in `C` and with `q` vertices is finite. -/
@[lognarayana "lem_colored_trees_finite"]
public theorem finite_setOf_numNodes_eq (C : Type*) [Finite C] (q : ℕ) :
    {t : BinaryTree C | t.numNodes = q}.Finite := by
  refine ((finite_decreasingColoredTrees_and_ncard C q).1.image skeleton).subset ?_
  rintro t rfl
  exact ⟨postLabel t 0, postLabel_mem_decreasingColoredTrees t, skeleton_postLabel t 0⟩

/-! ### Summing over the colorings allowed by a local rule -/

section LocalRule

variable {C : Type*}

private lemma vertexType_map {α β : Type*} (f : α → β) (l r : BinaryTree α) :
    vertexType (l.map f) (r.map f) = vertexType l r := by
  cases l <;> cases r <;> rfl

private lemma numNodes_map {α β : Type*} (f : α → β) (T : BinaryTree α) :
    (T.map f).numNodes = T.numNodes := by
  induction T with
  | nil => rfl
  | node a l r ihl ihr => simp [BinaryTree.map, BinaryTree.numNodes, ihl, ihr]

private lemma length_postorder_map {α β : Type*} (f : α → β) (T : BinaryTree α) :
    (T.map f).postorder.length = T.numNodes := by
  induction T with
  | nil => rfl
  | node a l r ihl ihr =>
    simp [BinaryTree.map, postorder, BinaryTree.numNodes, ihl, ihr]
    omega

private lemma map_fst_map_pair {α β : Type*} (b : β) (S : BinaryTree α) :
    (S.map fun a => (a, b)).map Prod.fst = S := by
  induction S with
  | nil => rfl
  | node a l r ihl ihr => simp only [BinaryTree.map, ihl, ihr]

/-- The colorings of `S` admitted by `P`. -/
private noncomputable def colorings (P : Set (VertexType × C))
    (hP : ∀ τ : VertexType, {c : C | (τ, c) ∈ P}.Finite) :
    BinaryTree ℕ → Finset (BinaryTree (ℕ × C))
  | .nil => {.nil}
  | .node a l r => by
    classical
    exact ((hP (vertexType l r)).toFinset ×ˢ (colorings P hP l ×ˢ colorings P hP r)).image
      fun x => .node (a, x.1) x.2.1 x.2.2

private lemma mem_colorings (P : Set (VertexType × C))
    (hP : ∀ τ : VertexType, {c : C | (τ, c) ∈ P}.Finite) (S : BinaryTree ℕ)
    (𝒯 : BinaryTree (ℕ × C)) :
    𝒯 ∈ colorings P hP S ↔ 𝒯.map Prod.fst = S ∧ 𝒯.map Prod.snd ∈ localRuleFamily P := by
  induction S generalizing 𝒯 with
  | nil =>
    cases 𝒯 with
    | nil => exact iff_of_true (Finset.mem_singleton_self _) ⟨rfl, trivial⟩
    | node => simp [colorings, BinaryTree.map]
  | node a l r ihl ihr =>
    cases 𝒯 with
    | nil => simp [colorings, BinaryTree.map]
    | node b tl tr =>
      classical
      simp only [colorings, Finset.mem_image, Finset.mem_product, Set.Finite.mem_toFinset,
        Set.mem_ofPred_eq, BinaryTree.map, BinaryTree.node.injEq, ihl, ihr]
      constructor
      · rintro ⟨⟨c, tl', tr'⟩, ⟨hc, ⟨rfl, hl⟩, ⟨rfl, hr⟩⟩, rfl, rfl, rfl⟩
        rw [vertexType_map] at hc
        exact ⟨⟨rfl, rfl, rfl⟩, by rwa [vertexType_map], hl, hr⟩
      · rintro ⟨⟨rfl, rfl, rfl⟩, hc, hl, hr⟩
        rw [vertexType_map] at hc
        exact ⟨⟨b.2, tl, tr⟩, ⟨by rwa [vertexType_map], ⟨rfl, hl⟩, ⟨rfl, hr⟩⟩, rfl, rfl, rfl⟩

/-- The distributive law: summing the vertex product of the colors over the colorings of `S`
admitted by `P` gives the product over the vertices of `S` of the sums of the admissible
weights. -/
private lemma sum_colorings {R : Type*} [CommSemiring R] (P : Set (VertexType × C))
    (hP : ∀ τ : VertexType, {c : C | (τ, c) ∈ P}.Finite) (ω : C → R) (S : BinaryTree ℕ) :
    ∑ 𝒯 ∈ colorings P hP S,
        BinaryTree.rec (motive := fun _ => R) 1 (fun a _ _ ihl ihr => ω a.2 * ihl * ihr) 𝒯 =
      BinaryTree.rec (motive := fun _ => R) 1
        (fun _ l r ihl ihr => (∑ᶠ (c : C) (_ : (vertexType l r, c) ∈ P), ω c) * ihl * ihr) S := by
  induction S with
  | nil => simp [colorings]
  | node a l r ihl ihr =>
    classical
    simp only [colorings]
    rw [Finset.sum_image fun x _ y _ hxy => by
        simp only [BinaryTree.node.injEq, Prod.mk.injEq] at hxy
        exact Prod.ext hxy.1.2 (Prod.ext hxy.2.1 hxy.2.2),
      show (∑ᶠ (c : C) (_ : (vertexType l r, c) ∈ P), ω c) =
        ∑ c ∈ (hP (vertexType l r)).toFinset, ω c from
          finsum_mem_eq_finite_toFinset_sum _ (hP (vertexType l r)), ← ihl, ← ihr,
      Finset.sum_mul, Finset.sum_mul, Finset.sum_product]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp_rw [Finset.sum_product, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]

/-- The decreasing trees on `[n]` with a given postorder reading form a finite set. -/
private lemma finite_decreasingTrees_postorder (n : ℕ) (π : List ℕ) :
    {S : BinaryTree ℕ | S ∈ decreasingTrees (Finset.Icc 1 n) ∧ S.postorder = π}.Finite := by
  refine ((finite_decreasingColoredTrees_and_ncard Unit n).1.image (BinaryTree.map Prod.fst)).subset
    fun S hS => ⟨S.map fun a => (a, ()), ?_, map_fst_map_pair () S⟩
  change (S.map fun a => (a, ())).map Prod.fst ∈ decreasingTrees (Finset.Icc 1 n)
  rw [map_fst_map_pair]
  exact hS.1

/-- A decreasing labeling of a tree of `𝐔_P` with postorder reading `π ∈ S_n` is a coloring
admitted by `P` of a decreasing tree on `[n]` with postorder reading `π`. -/
private lemma setOf_familyDecreasingLabelings_eq (P : Set (VertexType × C))
    (hP : ∀ τ : VertexType, {c : C | (τ, c) ∈ P}.Finite) {n : ℕ} {π : List ℕ}
    (hlen : π.length = n) :
    {𝒯 : BinaryTree (ℕ × C) | 𝒯 ∈ familyDecreasingLabelings (localRuleFamily P) ∧
        (𝒯.map Prod.fst).postorder = π} =
      ⋃ S ∈ {S : BinaryTree ℕ | S ∈ decreasingTrees (Finset.Icc 1 n) ∧ S.postorder = π},
        ↑(colorings P hP S) := by
  ext 𝒯
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_coe, mem_colorings, exists_prop]
  have hn (hpost : (𝒯.map Prod.fst).postorder = π) : (𝒯.map Prod.snd).numNodes = n := by
    rw [← hlen, ← hpost, length_postorder_map, numNodes_map]
  constructor
  · rintro ⟨⟨U, hU, h𝒯, rfl⟩, hpost⟩
    exact ⟨_, ⟨hn hpost ▸ h𝒯, hpost⟩, rfl, hU⟩
  · rintro ⟨S, ⟨hS, hpost⟩, rfl, hU⟩
    exact ⟨⟨_, hU, (hn hpost).symm ▸ hS, rfl⟩, hpost⟩

end LocalRule

/-- **Summing over the colorings allowed by a local rule.** For a local rule `P ⊆ 𝔗 × C` with
finite fibers, `π ∈ S_n`, weights `ω : C → R` and `h` on trees, the sum of
`h(𝒯°) ∏_v ω(χ(v))` over the decreasing labelings `(𝒯°, χ)` of trees in `𝐔_P` with
`𝒫(𝒯°) = π` equals the sum over decreasing binary plane trees `𝒯°` on `[n]` with `𝒫(𝒯°) = π`
of `h(𝒯°) ∏_v ∑_{c, (type(v), c) ∈ P} ω(c)`. -/
@[lognarayana "lem_local_rule_color_sum"]
public theorem finsum_familyDecreasingLabelings_localRuleFamily {C R : Type*} [CommSemiring R]
    (P : Set (VertexType × C)) (hP : ∀ τ : VertexType, {c : C | (τ, c) ∈ P}.Finite)
    {n : ℕ} {π : List ℕ} (hπ : π ∈ permWords n) (ω : C → R) (h : BinaryTree ℕ → R) :
    (∑ᶠ (𝒯 : BinaryTree (ℕ × C))
        (_ : 𝒯 ∈ familyDecreasingLabelings (localRuleFamily P) ∧
          (𝒯.map Prod.fst).postorder = π),
      h (𝒯.map Prod.fst) *
        BinaryTree.rec (motive := fun _ => R) 1 (fun a _ _ ihl ihr => ω a.2 * ihl * ihr) 𝒯) =
      ∑ᶠ (𝒯 : BinaryTree ℕ) (_ : 𝒯 ∈ decreasingTrees (Finset.Icc 1 n) ∧ 𝒯.postorder = π),
        h 𝒯 * BinaryTree.rec (motive := fun _ => R) 1
          (fun _ l r ihl ihr => (∑ᶠ (c : C) (_ : (vertexType l r, c) ∈ P), ω c) * ihl * ihr) 𝒯 := by
  classical
  have hfin := finite_decreasingTrees_postorder n π
  have hdisj : (hfin.toFinset : Set (BinaryTree ℕ)).PairwiseDisjoint (colorings P hP) :=
    fun S _ S' _ hne => Finset.disjoint_left.mpr fun 𝒯 h₁ h₂ => hne <| by
      rw [← ((mem_colorings P hP S 𝒯).mp h₁).1, ← ((mem_colorings P hP S' 𝒯).mp h₂).1]
  calc _ = ∑ᶠ 𝒯 ∈ (hfin.toFinset.biUnion (colorings P hP) : Set (BinaryTree (ℕ × C))),
        h (𝒯.map Prod.fst) *
        BinaryTree.rec (motive := fun _ => R) 1 (fun a _ _ ihl ihr => ω a.2 * ihl * ihr) 𝒯 := by
        rw [Finset.coe_biUnion, hfin.coe_toFinset,
          ← setOf_familyDecreasingLabelings_eq P hP hπ.2.1]
        rfl
    _ = ∑ S ∈ hfin.toFinset, h S * BinaryTree.rec (motive := fun _ => R) 1
          (fun _ l r ihl ihr => (∑ᶠ (c : C) (_ : (vertexType l r, c) ∈ P), ω c) * ihl * ihr) S := by
        rw [finsum_mem_coe_finset, Finset.sum_biUnion hdisj]
        refine Finset.sum_congr rfl fun S _ => ?_
        rw [← sum_colorings P hP ω S, Finset.mul_sum]
        exact Finset.sum_congr rfl fun 𝒯 h𝒯 => by rw [((mem_colorings P hP S 𝒯).mp h𝒯).1]
    _ = _ := by
        rw [← finsum_mem_coe_finset, hfin.coe_toFinset]
        rfl

/-! ### The troupe of binary plane trees -/

section BlackTrees

variable {C : Type*}

/-- A tree of pairs whose colors are all `b` is its tree of labels, colored `b`. -/
private lemma eq_map_pair_of_mem_localRuleFamily {α β : Type*} (b : β) (𝒯 : BinaryTree (α × β))
    (h : 𝒯.map Prod.snd ∈ localRuleFamily (Set.univ ×ˢ {b})) :
    𝒯 = (𝒯.map Prod.fst).map fun a => (a, b) := by
  induction 𝒯 with
  | nil => rfl
  | node a l r ihl ihr =>
    obtain ⟨⟨-, ha : a.2 = b⟩, hl, hr⟩ := h
    simp only [BinaryTree.map, ← ihl hl, ← ihr hr]
    rw [← ha]

/-- The decreasing labelings of the all-black trees with postorder reading `π` are finitely
many. -/
private lemma finite_familyDecreasingLabelings_blackTrees [TreeColors C] (π : List ℕ) :
    {𝒯 : BinaryTree (ℕ × C) | 𝒯 ∈ familyDecreasingLabelings (blackTrees C) ∧
      (𝒯.map Prod.fst).postorder = π}.Finite := by
  refine ((finite_decreasingTrees_postorder π.length π).image
    (BinaryTree.map fun a => (a, TreeColors.black))).subset ?_
  rintro 𝒯 ⟨h𝒯, hpost⟩
  simp only [familyDecreasingLabelings, Set.mem_iUnion, exists_prop] at h𝒯
  obtain ⟨U, hU, hdec, rfl⟩ := h𝒯
  refine ⟨𝒯.map Prod.fst, ⟨?_, hpost⟩, (eq_map_pair_of_mem_localRuleFamily _ 𝒯 hU).symm⟩
  rwa [← hpost, length_postorder_map, ← numNodes_map Prod.snd]

private lemma rec_mul {R : Type*} [CommSemiring R] {α : Type*} (𝒯 : BinaryTree α) :
    BinaryTree.rec (motive := fun _ => R) 1 (fun _ _ _ ihl ihr => ihl * ihr) 𝒯 = 1 := by
  induction 𝒯 with
  | nil => rfl
  | node a l r ihl ihr => simp only [ihl, ihr, mul_one]

private lemma finsum_black [TreeColors C] {R : Type*} [CommSemiring R] (τ : VertexType) :
    (∑ᶠ (c : C) (_ : (τ, c) ∈ (Set.univ ×ˢ {TreeColors.black} : Set (VertexType × C))),
      (1 : R)) = 1 := by
  rw [finsum_eq_single _ TreeColors.black (fun c hc => by simp [hc])]
  simp

/-- The identity `D_{π,𝐁} = D_π` over `ℕ`. -/
private lemma familyFiberDescentPolynomial_blackTrees_nat [TreeColors C] {n : ℕ} {π : List ℕ}
    (hπ : π ∈ permWords n) :
    List.familyFiberDescentPolynomial ℕ (blackTrees C) π = List.fiberDescentPolynomial ℕ π := by
  have key := finsum_familyDecreasingLabelings_localRuleFamily (R := ℕ[X])
    (Set.univ ×ˢ {(TreeColors.black : C)})
    (fun _ => (Set.finite_singleton _).subset fun _ hc => hc.2) hπ (fun _ => 1)
    (fun T => X ^ T.inorder.numDescents)
  simp only [finsum_black, one_mul, rec_mul, mul_one] at key
  rwa [List.familyFiberDescentPolynomial, List.fiberDescentPolynomial,
    List.sum_stackFiber_eq_finsum_decreasingTrees, hπ.2.1]

/-- The fiber descent polynomial of `𝐁` is the image of the one over `ℕ`. -/
private lemma familyFiberDescentPolynomial_blackTrees_eq_map [TreeColors C] (R : Type*)
    [Semiring R] (π : List ℕ) :
    List.familyFiberDescentPolynomial R (blackTrees C) π =
      (List.familyFiberDescentPolynomial ℕ (blackTrees C) π).map (Nat.castRingHom R) := by
  have := (mapRingHom (Nat.castRingHom R)).toAddMonoidHom.map_finsum_mem
    (fun 𝒯 : BinaryTree (ℕ × C) => (X : ℕ[X]) ^ (𝒯.map Prod.fst).inorder.numDescents)
    (finite_familyDecreasingLabelings_blackTrees π)
  simp only [RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, coe_mapRingHom,
    Polynomial.map_pow, map_X] at this
  exact this.symm

end BlackTrees

end BinaryTree

namespace List

/-- The troupe `𝐁` of binary plane trees recovers the fiber descent polynomial:
`D_{π,𝐁}(x) = D_π(x)` for every permutation `π ∈ S_n`. -/
@[lognarayana "lem_black_troupe_fiber_poly"]
public theorem familyFiberDescentPolynomial_blackTrees (R : Type*) [Semiring R]
    (C : Type*) [BinaryTree.TreeColors C] {n : ℕ} {π : List ℕ} (hπ : π ∈ permWords n) :
    familyFiberDescentPolynomial R (BinaryTree.blackTrees C) π = fiberDescentPolynomial R π := by
  rw [familyFiberDescentPolynomial_blackTrees_eq_map,
    familyFiberDescentPolynomial_blackTrees_nat hπ]
  simp [List.fiberDescentPolynomial, Polynomial.map_sum]

end List
