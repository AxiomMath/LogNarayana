/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module
public import LogNarayana.StackSorting.Matchings.Defs
public import LogNarayana.StackSorting.Descents.Basic
public import LogNarayana.BinaryTree.Decreasing.Basic
public import LogNarayana.StackSorting.FiberPolynomials.Defs

/-!
# Matchings and decreasing binary plane trees with fixed postorder

Let `π ∈ S_n` with `n ≥ 1`. A decreasing binary plane tree `T` on `[n]` with postorder reading
`𝒫(T) = π` is encoded by a pair `(M(T), C(T))`: a noncrossing partial matching `M(T)` on
`[n - 1]`, whose pairs `(a, b)` record the vertices `π_{b+1}` with two children and their left
children `π_a`, and the set `C(T)` of unmatched positions whose vertex has a right child. The
map `T ↦ (M(T), C(T))` is a bijection onto the pairs `(M, C)` with `M ∈ 𝒜(π)` and
`C ⊆ U(M)`. Under it, peaks, descents and descent and ascent tops of the inorder reading are
read off `(M, C)`, which expands the fiber polynomials of the stack-sorting map over the
matchings `𝒜(π)` of `π`, and gives the gamma form of the fiber descent polynomial.

The file first collects facts on subtrees and postorder readings, then the matching encoding,
then the polynomial identities.

## Main results

* `IsNoncrossingPartialMatching.card_unmatchedVertices_add_two_mul_card`:
  `#(unmatchedVertices N M) + 2 * #M = N`.
* `BinaryTree.postorder_subtree_eq_drop_take`: the postorder reading of the subtree rooted at
  `wⱼ` is `(𝒫(T).take j).drop (j - s)`, with `s ≤ j`.
* `BinaryTree.postorder_getElem?_pred_eq_last_child`: the letter preceding a vertex with a child
  in the postorder is its right child if it has one, and its left child otherwise.
* `BinaryTree.labels_right_eq_toFinset_postorder_drop_take`: the label set of the right subtree
  of a vertex `wⱼ` with two children and left child `wᵢ` is `{w_{i+1}, …, w_{j-1}}`.
* `BinaryTree.isLeaf_postorder_getElem_of_mem_treeMatching`: for `(a, b) ∈ M(T)`, the vertex
  labelled `π_{a+1}` is a leaf of `T`.
* `BinaryTree.parent_postorder_getElem_of_not_mem_leftEndpoints`: for `j ∈ [n-1]` with
  `j ∉ LE(M(T))`, the vertex `π_{j+1}` is the parent of the vertex `π_j`.
* `BinaryTree.treeMatching_mem_fiberMatchings`: `M(T) ∈ 𝒜(𝒫(T))`.
* `BinaryTree.bijOn_treeMatching_treeRightChoices`: the map `T ↦ (M(T), C(T))` is a bijection
  from `{T ∈ DBT([n]) : 𝒫(T) = π}` onto `{(M, C) : M ∈ 𝒜(π), C ⊆ U(M)}`.
* `BinaryTree.mem_rightChildLabels_iff_mem_treeMatching_or_treeRightChoices`: for `j ∈ [n - 1]`,
  `π_{j+1} ∈ RC(T)` if and only if `j ∈ R(M(T)) ∪ C(T)`.
* `BinaryTree.card_rightChildLabels_eq_card_treeMatching_add_card_treeRightChoices`:
  `|RC(T)| = |M(T)| + |C(T)|`.
* `BinaryTree.numDescents_inorder_eq_card_treeMatching_add_card_treeRightChoices`:
  `des(ℐ(T)) = |M(T)| + |C(T)|`.
* `BinaryTree.mem_leftChildLabels_iff_mem_treeMatching_or_unmatchedVertices_sdiff`: for
  `j ∈ [n - 1]`, `π_{j+1} ∈ LC(T)` if and only if `j ∈ R(M(T)) ∪ (U(M(T)) \ C(T))`.
* `BinaryTree.numBinaryNodes_eq_card_treeMatching`: `bin(T) = |M(T)|`.
* `BinaryTree.peakCount_inorder_eq_card_treeMatching`: `peak(I(T)) = |M(T)|`.
* `List.fiberPeakPolynomial_eq_finsum_fiberMatchings`:
  `H^λ_π(x, y) = ∑_{M ∈ 𝒜(π)} (λ x y)^{|M|} (x + y)^{n - 1 - 2|M|}`.
* `List.fiberHomogPolynomial_eq_finsum_fiberMatchings`:
  `H_π(x, y) = ∑_{M ∈ 𝒜(π)} (x y)^{|M|} (x + y)^{n - 1 - 2|M|}`.
* `List.fiberTopPolynomial_eq_finsum_fiberMatchings`: the expansion of the fiber top
  polynomial `𝒟_π` over `𝒜(π)`.
* `List.fiberDescentPolynomial_eq_finsum_fiberMatchings`:
  `D_π(x) = ∑_{M ∈ 𝒜(π)} x^{|M|} (1 + x)^{n - 1 - 2|M|}`.
* `List.eval_fiberDescentPolynomial_eq_pow_mul_eval_fiberMatchingPolynomial`:
  `D_π(x) = (1 + x)^{n - 1} Γ_π(x / (1 + x)^2)` for `x ≠ -1`.

## References

* [LogNarayana] *Log-Concavity in Narayana Transforms and Stack-Sorting Fibers*, Sections 3
  and 5.
-/

/-!
## Counting the unmatched vertices of a noncrossing partial matching

Let `M` be a noncrossing partial matching on `[N] = {1, …, N}`. Each pair of `M` covers two
elements of `[N]`, distinct pairs cover disjoint sets, and the remaining elements are the
unmatched vertices `U(M)`. Hence `|U(M)| + 2|M| = N`.
-/

section

namespace Proof_lem_matching_unmatched_card

/-- The left and right endpoints of a partial matching are `2|M|` distinct numbers. -/
private lemma card_endpoints {N : ℕ} {M : Finset (ℕ × ℕ)} (hM : IsNoncrossingPartialMatching N M) :
    (M.image Prod.fst ∪ M.image Prod.snd).card = 2 * M.card := by
  rw [Finset.card_union_of_disjoint, Finset.card_image_of_injOn, Finset.card_image_of_injOn]
  · omega
  · exact fun p hp q hq h => hM.eq_of_mem_of_mem p hp q hq p.2 (.inr rfl) (.inr h)
  · exact fun p hp q hq h => hM.eq_of_mem_of_mem p hp q hq p.1 (.inl rfl) (.inl h)
  · simp only [Finset.disjoint_left, Finset.mem_image, not_exists, not_and]
    rintro _ ⟨p, hp, rfl⟩ q hq hqp
    obtain rfl := hM.eq_of_mem_of_mem p hp q hq p.1 (.inl rfl) (.inr hqp.symm)
    exact (hM.fst_lt_snd p hp).ne hqp.symm

/-- The endpoints of a partial matching on `[N]` lie in `[N]`. -/
private lemma endpoints_subset {N : ℕ} {M : Finset (ℕ × ℕ)}
    (hM : IsNoncrossingPartialMatching N M) :
    M.image Prod.fst ∪ M.image Prod.snd ⊆ Finset.Icc 1 N := by
  simp only [Finset.union_subset_iff, Finset.image_subset_iff, Finset.mem_Icc]
  exact ⟨fun p hp => ⟨hM.one_le_fst p hp, ((hM.fst_lt_snd p hp).trans_le (hM.snd_le p hp)).le⟩,
    fun p hp => ⟨(hM.one_le_fst p hp).trans (hM.fst_lt_snd p hp).le, hM.snd_le p hp⟩⟩

end Proof_lem_matching_unmatched_card

open Proof_lem_matching_unmatched_card in
/-- For a noncrossing partial matching `M` on `[N]`, `|U(M)| + 2|M| = N`. -/
@[lognarayana "lem_matching_unmatched_card"]
public theorem IsNoncrossingPartialMatching.card_unmatchedVertices_add_two_mul_card
    {N : ℕ} {M : Finset (ℕ × ℕ)} (hM : IsNoncrossingPartialMatching N M) :
    (Finset.unmatchedVertices N M).card + 2 * M.card = N := by
  have hle := Finset.card_le_card (endpoints_subset hM)
  rw [card_endpoints hM, Nat.card_Icc] at hle
  rw [Finset.unmatchedVertices, Finset.leftEndpoints, Finset.card_sdiff_of_subset
    (endpoints_subset hM), card_endpoints hM, Nat.card_Icc]
  omega

end

/-!
## Subtrees occupy intervals of the postorder

Let `T` be a decreasing binary plane tree on a finite set `A` of labels in a preorder `α`, with
postorder reading `𝒫(T) = w₁ ⋯ wₘ`. For every position `j`, the subtree `T₍ⱼ₎`
rooted at the vertex labelled `wⱼ`
has `s ≤ j` vertices, and its postorder reading is the factor `w_{j-s+1} ⋯ wⱼ` of `𝒫(T)`
ending at position `j`.

A subtree of `T` is a tree reachable from `T` by repeatedly passing to the left or right
subtree of a root, i.e. a tree related to `T` by the reflexive-transitive closure of the
relation "is the left or right subtree of the root of". The subtree rooted at the vertex
labelled `wⱼ` is a subtree of this form whose root label is `wⱼ`; since the labels of a
decreasing tree are distinct it is unique. Positions are `1`-indexed as in the paper: the
letter `wⱼ` is `𝒫(T)[j - 1]`, and the condition `𝒫(T)[j - 1]? = some a` with `1 ≤ j` encodes
`j ∈ [m]` together with `wⱼ = a`. The number of vertices is `BinaryTree.numNodes`.
-/

/-!
## Postorder readings
-/

/-- A permutation word has no repeated letter. -/
private lemma nodup_of_mem_permWords {n : ℕ} {π : List ℕ} (hπ : π ∈ permWords n) : π.Nodup := by
  obtain ⟨-, hlen, hlet⟩ := hπ
  have hc : π.dedup.length = π.length := by
    simp only [List.letters] at hlet
    simp [← List.card_toFinset, hlet, hlen]
  exact List.dedup_eq_self.1 ((List.dedup_sublist π).eq_of_length hc)

namespace BinaryTree

/-- The letters of the postorder reading are the labels. -/
private theorem mem_postorder_iff {α : Type*} [DecidableEq α] {T : BinaryTree α} {x : α} :
    x ∈ T.postorder ↔ x ∈ T.labels := by
  induction T with
  | nil => simp
  | node m l r ihl ihr => simp [ihl, ihr]; tauto

/-- The postorder reading of a decreasing tree has no repeated letters. -/
private theorem nodup_postorder {α : Type*} [DecidableEq α] [Preorder α] {T : BinaryTree α}
    (hT : T.IsDecreasing) : T.postorder.Nodup := by
  induction T with
  | nil => simp
  | node m l r ihl ihr =>
    obtain ⟨hl, hr, hd, hm⟩ := hT
    simp only [postorder, List.nodup_append, List.mem_append, mem_postorder_iff,
      List.mem_singleton]
    refine ⟨⟨ihl hl, ihr hr, fun x hx y hy => ?_⟩, by simp, ?_⟩
    · rintro rfl; exact Finset.disjoint_left.mp hd hx hy
    · rintro x hx _ rfl rfl
      exact lt_irrefl _ (hm x (Finset.mem_union.mpr hx))

/-- The postorder reading has one letter per vertex. -/
private theorem length_postorder {α : Type*} (T : BinaryTree α) :
    T.postorder.length = T.numNodes := by
  induction T with
  | nil => rfl
  | node a l r ihl ihr => simp [ihl, ihr]; omega

end BinaryTree

section

open BinaryTree

namespace Proof_lem_postorder_subtree_interval

/-- The postorder reading of a subtree is an infix of the postorder reading. -/
private theorem postorder_infix {α : Type*} {S T : BinaryTree α}
    (h : Relation.ReflTransGen
      (fun S U : BinaryTree α => ∃ b L R, U = node b L R ∧ (S = L ∨ S = R)) S T) :
    ∃ u v, T.postorder = u ++ S.postorder ++ v := by
  induction h with
  | refl => exact ⟨[], [], by simp⟩
  | tail _ hbc ih =>
    obtain ⟨u, v, huv⟩ := ih
    obtain ⟨x, L, R, rfl, rfl | rfl⟩ := hbc
    · exact ⟨u, v ++ R.postorder ++ [x], by simp [huv]⟩
    · exact ⟨L.postorder ++ u, v ++ [x], by simp [huv]⟩

/-- In a nodup list `L = u ++ (P ++ [a]) ++ v` in which `a` sits at the (1-indexed) position `j`,
the factor `P ++ [a]` ends at position `j`. -/
private theorem infix_eq_drop_take_of_nodup {α : Type*} {L u P v : List α} {a : α} {j : ℕ}
    (hnd : L.Nodup) (hL : L = u ++ (P ++ [a]) ++ v) (hj : 1 ≤ j) (hw : L[j - 1]? = some a) :
    (P ++ [a]).length ≤ j ∧ P ++ [a] = (L.take j).drop (j - (P ++ [a]).length) := by
  have ha : L[u.length + P.length]? = some a := by
    subst hL; simp
  obtain ⟨h1, e1⟩ := List.getElem?_eq_some_iff.mp hw
  obtain ⟨h2, e2⟩ := List.getElem?_eq_some_iff.mp ha
  have hij := hnd.getElem_inj_iff.mp (e1.trans e2.symm)
  have hj' : j = u.length + (P.length + 1) := by omega
  subst hL hj'
  simp [List.take_append]

end Proof_lem_postorder_subtree_interval

namespace BinaryTree

open Proof_lem_postorder_subtree_interval in
/-- **Subtrees occupy intervals of the postorder.** Let `T ∈ DBT(A)` with postorder reading
`𝒫(T) = w₁ ⋯ wₘ`, and let `j ∈ [m]`. If `node a l r` is the subtree of `T` rooted at the vertex
labelled `wⱼ = a`, with `s` vertices, then `s ≤ j` and its postorder reading is
`w_{j-s+1} ⋯ wⱼ`. -/
@[lognarayana "lem_postorder_subtree_interval"]
public theorem postorder_subtree_eq_drop_take {α : Type*} [DecidableEq α] [Preorder α]
    {A : Finset α} {T : BinaryTree α}
    (hT : T ∈ decreasingTrees A) {j : ℕ} (hj : 1 ≤ j) {a : α} {l r : BinaryTree α}
    (hw : T.postorder[j - 1]? = some a)
    (hS : Relation.ReflTransGen
      (fun S U : BinaryTree α => ∃ b L R, U = node b L R ∧ (S = L ∨ S = R)) (node a l r) T) :
    (node a l r).numNodes ≤ j ∧
      (node a l r).postorder = (T.postorder.take j).drop (j - (node a l r).numNodes) := by
  obtain ⟨u, v, huv⟩ := postorder_infix hS
  rw [← length_postorder]
  exact infix_eq_drop_take_of_nodup (P := l.postorder ++ r.postorder) (nodup_postorder hT.1) huv
    hj hw

end BinaryTree

end

/-!
## The letter before a vertex in the postorder is its last child

Let `T` be a decreasing binary plane tree on a finite set `A` of labels, with postorder reading
`𝒫(T) = w₁ ⋯ wₘ`. If the vertex labelled `wⱼ` has at least one child, then `j ≥ 2`, and the
letter `w_{j-1}` is the right child of `wⱼ` when `wⱼ` has a right child, and its left child
otherwise.

As for `BinaryTree.postorder_subtree_eq_drop_take`, the subtree rooted at the vertex labelled
`wⱼ` is a tree `node a l r` related to `T` by the reflexive-transitive closure of the relation
"is the left or right subtree of the root of", with `a = wⱼ`. The vertex `wⱼ` has a child iff
`l ≠ nil ∨ r ≠ nil`; its right child is the root label `b` of `r = node b _ _`, and its left child
the root label of `l`. Positions are `1`-indexed: `wⱼ = 𝒫(T)[j - 1]` and `w_{j-1} = 𝒫(T)[j - 2]`.
-/

section

open BinaryTree

namespace Proof_lem_postorder_last_child

/-- The postorder reading is empty only for the empty tree. -/
private theorem postorder_eq_nil_iff {α : Type*} {T : BinaryTree α} :
    T.postorder = [] ↔ T = nil := by
  cases T <;> simp

/-- If the factor of `L` of length `|P| + 1` ending at (1-indexed) position `j` is `P ++ [a]`
with `P` nonempty, then the last letter of `P` is the letter of `L` at position `j - 1`. -/
private theorem getLast?_eq_getElem?_of_append_singleton_eq_drop_take {α : Type*}
    {L P : List α} {a : α} {j : ℕ} (hne : P ≠ []) (hs : P.length + 1 ≤ j)
    (h : P ++ [a] = (L.take j).drop (j - (P.length + 1))) :
    P.getLast? = L[j - 2]? := by
  have hpos := List.length_pos_iff.2 hne
  have := congrArg (·[P.length - 1]?) h
  rw [List.getElem?_append_left (by omega), List.getElem?_drop, List.getElem?_take,
    if_pos (by omega)] at this
  rw [List.getLast?_eq_getElem?, this]
  congr 1
  omega

end Proof_lem_postorder_last_child

namespace BinaryTree

open Proof_lem_postorder_last_child in
/-- **The letter before a vertex in the postorder is its last child.** Let `T ∈ DBT(A)` with
postorder reading `𝒫(T) = w₁ ⋯ wₘ`, let `j ∈ [m]`, and let `node a l r` be the subtree of `T`
rooted at the vertex labelled `wⱼ = a`. If `wⱼ` has at least one child, then `j ≥ 2`, and
`w_{j-1}` is the right child of `wⱼ` if `wⱼ` has a right child, and its left child otherwise. -/
@[lognarayana "lem_postorder_last_child"]
public theorem postorder_getElem?_pred_eq_last_child {α : Type*} [DecidableEq α] [Preorder α]
    {A : Finset α} {T : BinaryTree α}
    (hT : T ∈ decreasingTrees A) {j : ℕ} (hj : 1 ≤ j) {a : α} {l r : BinaryTree α}
    (hw : T.postorder[j - 1]? = some a)
    (hS : Relation.ReflTransGen
      (fun S U : BinaryTree α => ∃ b L R, U = node b L R ∧ (S = L ∨ S = R)) (node a l r) T)
    (hc : l ≠ nil ∨ r ≠ nil) :
    2 ≤ j ∧
      (∀ b R₁ R₂, r = node b R₁ R₂ → T.postorder[j - 2]? = some b) ∧
      (r = nil → ∀ b L₁ L₂, l = node b L₁ L₂ → T.postorder[j - 2]? = some b) := by
  obtain ⟨hs, hP⟩ := postorder_subtree_eq_drop_take hT hj hw hS
  have hne : l.postorder ++ r.postorder ≠ [] := by
    simpa [postorder_eq_nil_iff, or_iff_not_and_not] using hc
  have hlen : (node a l r).numNodes = (l.postorder ++ r.postorder).length + 1 := by
    simp [length_postorder]
  rw [hlen] at hs hP
  have key := getLast?_eq_getElem?_of_append_singleton_eq_drop_take hne hs hP
  refine ⟨by have := List.length_pos_iff.2 hne; omega, ?_, ?_⟩
  · rintro b R₁ R₂ rfl
    simp [← key]
  · rintro rfl b L₁ L₂ rfl
    simp [← key]

end BinaryTree

end

/-!
## The right subtree of a binary vertex in the postorder

Let `T` be a decreasing binary plane tree on a finite set `A ⊆ ℤ`, with postorder reading
`𝒫(T) = w₁ ⋯ wₘ`. If the vertex labelled `wⱼ` has two children and its left child is `wᵢ`,
then the labels of the right subtree of `wⱼ` are exactly the letters `w_{i+1}, …, w_{j-1}`
strictly between the two in the postorder.

As for `BinaryTree.postorder_subtree_eq_drop_take`, the subtree rooted at the vertex labelled
`wⱼ` is a tree `node a l r` related to `T` by the reflexive-transitive closure of the relation
"is the left or right subtree of the root of", with `a = wⱼ`. The vertex has two children iff
`l` and `r` are nonempty; its left child is the root label `b` of `l = node b L₁ L₂`, and its
right subtree is `r`. Positions are `1`-indexed: `wⱼ = 𝒫(T)[j - 1]`, and the factor
`w_{i+1} ⋯ w_{j-1}` is `(𝒫(T).take (j - 1)).drop i`.
-/

section

open BinaryTree

namespace Proof_lem_postorder_binary_right_subtree

/-- If the factor of the nodup list `L` ending at (1-indexed) position `j` is `P ++ b :: Q ++ [a]`
and `b` sits at position `i`, then the letters strictly between positions `i` and `j` form `Q`. -/
private theorem drop_take_eq_of_nodup {α : Type*} {L P Q : List α} {a b : α} {i j : ℕ}
    (hnd : L.Nodup) (hs : P.length + Q.length + 2 ≤ j)
    (h : P ++ b :: Q ++ [a] = (L.take j).drop (j - (P.length + Q.length + 2)))
    (hi : 1 ≤ i) (hb : L[i - 1]? = some b) :
    (L.take (j - 1)).drop i = Q := by
  have hb' := congrArg (·[P.length]?) h
  simp only [List.append_assoc, List.getElem?_append_right le_rfl, Nat.sub_self,
    List.cons_append, List.getElem?_cons_zero, List.getElem?_drop, List.getElem?_take] at hb'
  rw [if_pos (by omega)] at hb'
  obtain ⟨_, e1⟩ := List.getElem?_eq_some_iff.mp hb
  obtain ⟨_, e2⟩ := List.getElem?_eq_some_iff.mp hb'.symm
  have hi' := hnd.getElem_inj_iff.mp (e1.trans e2.symm)
  have := congrArg (fun M => (M.take (P ++ b :: Q).length).drop (P ++ [b]).length) h
  simp only [List.take_left', List.take_drop, List.drop_drop, List.take_take] at this
  rw [show (P ++ b :: Q).drop (P ++ [b]).length = Q by simp] at this
  rw [this]
  congr 2 <;> simp <;> omega

end Proof_lem_postorder_binary_right_subtree

namespace BinaryTree

open Proof_lem_postorder_binary_right_subtree in
/-- **The right subtree of a binary vertex in the postorder.** Let `T ∈ DBT(A)` with postorder
reading `𝒫(T) = w₁ ⋯ wₘ`, let `j ∈ [m]`, and let `node a l r` be the subtree of `T` rooted at the
vertex labelled `wⱼ = a`. If the left child of `wⱼ` is `wᵢ`, then the set of labels of the right
subtree of `wⱼ` (empty if `wⱼ` has no right child) is `{w_{i+1}, …, w_{j-1}}`. -/
@[lognarayana "lem_postorder_binary_right_subtree"]
public theorem labels_right_eq_toFinset_postorder_drop_take {A : Finset ℤ} {T : BinaryTree ℤ}
    (hT : T ∈ decreasingTrees A) {j : ℕ} (hj : 1 ≤ j) {a : ℤ} {l r : BinaryTree ℤ}
    (hw : T.postorder[j - 1]? = some a)
    (hS : Relation.ReflTransGen
      (fun S U : BinaryTree ℤ => ∃ b L R, U = node b L R ∧ (S = L ∨ S = R)) (node a l r) T)
    {b : ℤ} {L₁ L₂ : BinaryTree ℤ} (hl : l = node b L₁ L₂)
    {i : ℕ} (hi : 1 ≤ i) (hb : T.postorder[i - 1]? = some b) :
    r.labels = ((T.postorder.take (j - 1)).drop i).toFinset := by
  subst hl
  obtain ⟨hs, hP⟩ := postorder_subtree_eq_drop_take hT hj hw hS
  have hlen : (node a (node b L₁ L₂) r).numNodes =
      (L₁.postorder ++ L₂.postorder).length + r.postorder.length + 2 := by
    simp [length_postorder]; omega
  rw [hlen] at hs hP
  rw [drop_take_eq_of_nodup (nodup_postorder hT.1) hs (by simpa using hP) hi hb]
  ext
  simp [mem_postorder_iff]

end BinaryTree

end

/-!
## The vertex after a left endpoint of the tree matching is a leaf

Let `T` be a decreasing binary plane tree on `[n]` with postorder reading `𝒫(T) = π ∈ S_n`. If
`(a, b) ∈ M(T)`, then the vertex labelled `π_{a+1}` is a leaf of `T`: it is the first vertex
read in the right subtree of the vertex labelled `π_{b+1}`.

Labels are in `ℕ`, `S_n` is `permWords n` and `[n]` is `Finset.Icc 1 n`. Positions are
`1`-based, so `π_{a+1} = π[a]`. A vertex of `T` is a subtree of `T`, given by the
reflexive-transitive closure of the relation "is the left or right subtree of the root of", as
in `BinaryTree.treeMatching`; the vertex labelled `π_{a+1}` is a leaf when `⟨π_{a+1}; ∅, ∅⟩` is
a subtree of `T`. The index bound `a < |π|` is part of the conclusion.
-/

section

open BinaryTree

namespace Proof_lem_tree_left_endpoint_leaf


/-- The postorder reading of a subtree of `T` is a factor of the postorder reading of `T`. -/
private theorem postorder_infix_of_reflTransGen {α : Type*} {S T : BinaryTree α}
    (h : Relation.ReflTransGen
      (fun S U : BinaryTree α => ∃ m L R, U = node m L R ∧ (S = L ∨ S = R)) S T) :
    S.postorder <:+: T.postorder := by
  induction h with
  | refl => exact List.infix_refl _
  | tail _ hUV ih =>
    obtain ⟨m, L, R, rfl, hL | hR⟩ := hUV
    · subst hL
      exact ih.trans ⟨[], postorder R ++ [m], by simp [postorder]⟩
    · subst hR
      exact ih.trans ⟨postorder L, [m], by simp [postorder]⟩

/-- The first letter of the postorder reading of a nonempty tree is the label of a leaf. -/
private theorem exists_leaf_postorder_eq_cons {α : Type*} :
    ∀ R : BinaryTree α, R ≠ nil → ∃ x rest, R.postorder = x :: rest ∧
      Relation.ReflTransGen
        (fun S U : BinaryTree α => ∃ m L R, U = node m L R ∧ (S = L ∨ S = R)) (node x nil nil) R
  | nil, h => absurd rfl h
  | node d l r, _ => by
    by_cases hl : l = nil
    · subst hl
      by_cases hr : r = nil
      · subst hr
        exact ⟨d, [], rfl, Relation.ReflTransGen.refl⟩
      · obtain ⟨x, rest, hx, hs⟩ := exists_leaf_postorder_eq_cons r hr
        exact ⟨x, rest ++ [d], by simp [postorder, hx], hs.tail ⟨d, nil, r, rfl, Or.inr rfl⟩⟩
    · obtain ⟨x, rest, hx, hs⟩ := exists_leaf_postorder_eq_cons l hl
      exact ⟨x, rest ++ postorder r ++ [d], by simp [postorder, hx],
        hs.tail ⟨d, l, r, rfl, Or.inl rfl⟩⟩

/-- In a word without repeated letters containing the factor `y x`, the letter after any
occurrence of `y` is `x`. -/
private theorem getElem_succ_eq_of_nodup {α : Type*} {l P Q : List α} {x y : α} (hl : l.Nodup)
    (h : l = P ++ y :: x :: Q) {i : ℕ} (hi : i < l.length) (hy : l[i] = y) :
    ∃ h : i + 1 < l.length, l[i + 1] = x := by
  subst h
  obtain rfl : i = P.length :=
    hl.getElem_inj_iff.1 (hy.trans (by simp : (P ++ y :: x :: Q)[P.length] = y).symm)
  exact ⟨by simp, by simp [List.getElem_append_right]⟩

end Proof_lem_tree_left_endpoint_leaf

namespace BinaryTree

open Proof_lem_tree_left_endpoint_leaf in
/-- **The vertex after a left endpoint is a leaf.** Let `π ∈ S_n` and let `T` be a binary tree with
`𝒫(T) = π`, and `(a, b) ∈ M(T)`. Then the vertex labelled `π_{a+1}` is a leaf of `T`. -/
@[lognarayana "lem_tree_left_endpoint_leaf"]
public theorem isLeaf_postorder_getElem_of_mem_treeMatching {n : ℕ}
    {π : List ℕ} (hπS : π ∈ permWords n) {T : BinaryTree ℕ}
    (hπ : T.postorder = π) {a b : ℕ}
    (hab : (a, b) ∈ T.treeMatching) :
    ∃ h : a < π.length,
      Relation.ReflTransGen
        (fun S U : BinaryTree ℕ => ∃ m L R, U = node m L R ∧ (S = L ∨ S = R))
        (node π[a] nil nil) T := by
  subst hπ
  simp only [treeMatching, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hab
  obtain ⟨⟨⟨ha1, -⟩, -⟩, ha, hb, L₁, L₂, d, R₁, R₂, hS⟩ := hab
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le' ha1
  simp only [Nat.add_sub_cancel] at ha hS
  obtain ⟨x, rest, hx, hleaf⟩ := exists_leaf_postorder_eq_cons (node d R₁ R₂) (by simp)
  obtain ⟨s, t, hst⟩ := postorder_infix_of_reflTransGen hS
  obtain ⟨h, hxa⟩ := getElem_succ_eq_of_nodup hπS.1.1 (P := s ++ (postorder L₁ ++ postorder L₂))
    (Q := rest ++ [T.postorder[b]] ++ t) (x := x)
    (by rw [postorder, hx, postorder] at hst; simpa using hst.symm) ha rfl
  exact ⟨h, hxa ▸ (hleaf.tail ⟨_, _, _, rfl, Or.inr rfl⟩).trans hS⟩

end BinaryTree

end

/-!
## A vertex not starting a right subtree has the next vertex as parent

Let `T` be a decreasing binary plane tree on `[n]` with postorder reading `𝒫(T) = π ∈ S_n`. If
`j ∈ [n - 1]` is not a left endpoint of the matching `M(T)`, then the vertex labelled `π_{j+1}`
is the parent of the vertex labelled `π_j`.

Labels are in `ℕ`, `S_n` is `permWords n` and `[n]` is `Finset.Icc 1 n`. Positions are
`1`-based, so `π_j = π[j - 1]` and `π_{j+1} = π[j]`. A vertex of `T` is a subtree of `T`, given
by the reflexive-transitive closure of the relation "is the left or right subtree of the root
of", as in `BinaryTree.treeMatching`; the vertex labelled `π_{j+1}` is the parent of the vertex
labelled `π_j` when `T` has a subtree `⟨π_{j+1}; L, R⟩` in which `L` or `R` has root `π_j`.
-/

section

open BinaryTree

namespace Proof_lem_tree_parent_next

/-- `S` is a subtree of `T`: the reflexive-transitive closure of "is a child subtree of the root
of", as in `BinaryTree.treeMatching`. -/
private abbrev IsSubtree {α : Type*} (S T : BinaryTree α) : Prop :=
  Relation.ReflTransGen (fun S U : BinaryTree α => ∃ m L R, U = node m L R ∧ (S = L ∨ S = R)) S T

private theorem getElem?_postorder_node_left {α : Type*} (m : α) (l r : BinaryTree α) {i : ℕ}
    (h : i < l.postorder.length) : (node m l r).postorder[i]? = l.postorder[i]? := by
  rw [postorder, List.append_assoc, List.getElem?_append_left h]

private theorem getElem?_postorder_node_right {α : Type*} (m : α) (l r : BinaryTree α) {k : ℕ}
    (h : k < r.postorder.length) :
    (node m l r).postorder[l.postorder.length + k]? = r.postorder[k]? := by
  rw [postorder, List.getElem?_append_left (by simpa using h),
    List.getElem?_append_right (by omega)]
  simp

/-- Evaluates `getElem?` on concatenations of postorder readings by splitting on the index. -/
local macro "idx_tac" : tactic => `(tactic| (
  simp only [postorder, List.append_assoc, List.getElem?_append, List.length_append,
    List.length_singleton, List.getElem?_singleton, List.length_nil, List.append_nil,
    List.nil_append]
  first | omega | (split_ifs <;> first | rfl | omega)))

/-- Consecutive letters `x = 𝒫(S)[i]`, `y = 𝒫(S)[i+1]` of the postorder reading of a subtree `S`
of `T`: either `y` is the parent of `x` in `T`, or `x` is the left child of a vertex `m` with two
children, `m` occurring later than `x` in `𝒫(S)`. -/
private theorem parent_or_left_child_of_binary {α : Type*} (T : BinaryTree α) :
    ∀ (S : BinaryTree α), IsSubtree S T → ∀ i, i + 1 < S.postorder.length →
      (∃ x y L R, S.postorder[i]? = some x ∧ S.postorder[i + 1]? = some y ∧
        IsSubtree (node y L R) T ∧ ((∃ L₁ L₂, L = node x L₁ L₂) ∨ ∃ R₁ R₂, R = node x R₁ R₂)) ∨
      (∃ b x m L₁ L₂ d R₁ R₂, i < b ∧ b < S.postorder.length ∧ S.postorder[i]? = some x ∧
        S.postorder[b]? = some m ∧ IsSubtree (node m (node x L₁ L₂) (node d R₁ R₂)) T) := by
  intro S
  induction S with
  | nil => intro _ i hi; simp at hi
  | node m l r ihl ihr =>
    intro hS i hi
    have hl := Relation.ReflTransGen.head ⟨m, l, r, rfl, Or.inl rfl⟩ hS
    have hr := Relation.ReflTransGen.head ⟨m, l, r, rfl, Or.inr rfl⟩ hS
    have hlen : (node m l r).postorder.length = l.postorder.length + r.postorder.length + 1 := by
      simp [postorder]; omega
    rw [hlen] at hi ⊢
    rcases lt_trichotomy (i + 1) l.postorder.length with h | h | h
    · simp only [getElem?_postorder_node_left m l r (by omega : i < _),
        getElem?_postorder_node_left m l r h]
      rcases ihl hl i h with ⟨x, y, L, R, hx, hy, h1, h2⟩ | ⟨b, x, m', L₁, L₂, d, R₁, R₂, hib, hb,
        hx, hm, h1⟩
      · exact .inl ⟨x, y, L, R, hx, hy, h1, h2⟩
      · exact .inr ⟨b, x, m', L₁, L₂, d, R₁, R₂, hib, by omega, hx,
          by rwa [getElem?_postorder_node_left m l r hb], h1⟩
    · cases l with
      | nil => simp at h
      | node x l₁ l₂ =>
        simp only [postorder, List.length_append, List.length_singleton] at h
        cases r with
        | nil =>
          exact .inl ⟨x, m, node x l₁ l₂, nil, by idx_tac, by idx_tac, hS, .inl ⟨l₁, l₂, rfl⟩⟩
        | node d r₁ r₂ =>
          exact .inr ⟨(node x l₁ l₂).postorder.length + (node d r₁ r₂).postorder.length, x, m, l₁,
            l₂, d, r₁, r₂, by idx_tac, by omega, by idx_tac, by idx_tac, hS⟩
    · by_cases hq : i + 1 < l.postorder.length + r.postorder.length
      · obtain ⟨k, rfl⟩ : ∃ k, i = l.postorder.length + k := ⟨i - l.postorder.length, by omega⟩
        rw [Nat.add_assoc, getElem?_postorder_node_right m l r (by omega),
          getElem?_postorder_node_right m l r (by omega)]
        rcases ihr hr k (by omega) with
          ⟨x, y, L, R, hx, hy, h1, h2⟩ | ⟨b, x, m', L₁, L₂, d, R₁, R₂, hib, hb, hx, hm, h1⟩
        · exact .inl ⟨x, y, L, R, hx, hy, h1, h2⟩
        · exact .inr ⟨l.postorder.length + b, x, m', L₁, L₂, d, R₁, R₂, by omega, by omega, hx,
            by rwa [getElem?_postorder_node_right m l r hb], h1⟩
      · cases r with
        | nil => simp only [postorder, List.length_nil] at hq h hi; omega
        | node x r₁ r₂ =>
          simp only [postorder, List.length_append, List.length_singleton] at hq hi
          exact .inl ⟨x, m, l, node x r₁ r₂, by idx_tac, by idx_tac, hS, .inr ⟨r₁, r₂, rfl⟩⟩

end Proof_lem_tree_parent_next

namespace BinaryTree

open Proof_lem_tree_parent_next in
/-- **A vertex not starting a right subtree has the next vertex as parent.** Let `n ≥ 1`, `π ∈ S_n`,
`T` a binary tree with `𝒫(T) = π`, and `j ∈ [n - 1]` with `j ∉ LE(M(T))`. Then the vertex labelled
`π_{j+1}` is the parent of the vertex labelled `π_j`. -/
@[lognarayana "lem_tree_parent_next"]
public theorem parent_postorder_getElem_of_not_mem_leftEndpoints {n : ℕ} (hn : 1 ≤ n)
    {π : List ℕ} (hπS : π ∈ permWords n) {T : BinaryTree ℕ}
    (hπ : T.postorder = π) {j : ℕ} (hj₁ : 1 ≤ j)
    (hj₂ : j ≤ n - 1) (hj : j ∉ T.treeMatching.leftEndpoints) :
    ∃ (h : j < π.length) (L R : BinaryTree ℕ),
      Relation.ReflTransGen
        (fun S U : BinaryTree ℕ => ∃ m L R, U = node m L R ∧ (S = L ∨ S = R))
        (node π[j] L R) T ∧
      ((∃ L₁ L₂, L = node π[j - 1] L₁ L₂) ∨ ∃ R₁ R₂, R = node π[j - 1] R₁ R₂) := by
  have hlen : π.length = n := hπS.2.1
  subst hπ
  have hjl : j < T.postorder.length := by omega
  refine ⟨hjl, ?_⟩
  rcases parent_or_left_child_of_binary T T .refl (j - 1) (by omega) with
    ⟨x, y, L, R, hx, hy, h1, h2⟩ | ⟨b, x, m, L₁, L₂, d, R₁, R₂, hib, hb, hx, hm, h1⟩
  · rw [show j - 1 + 1 = j by omega, List.getElem?_eq_getElem hjl, Option.some_inj] at hy
    rw [List.getElem?_eq_getElem (by omega), Option.some_inj] at hx
    subst hx hy
    exact ⟨L, R, h1, h2⟩
  · refine absurd (Finset.mem_image.2 ⟨(j, b), ?_, rfl⟩) hj
    rw [List.getElem?_eq_getElem (by omega), Option.some_inj] at hx hm
    simp only [treeMatching, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
    refine ⟨⟨⟨hj₁, by omega⟩, by omega, by omega⟩, by omega, hb, L₁, L₂, d, R₁, R₂, ?_⟩
    simpa [hx, hm] using h1

end BinaryTree

end

/-!
## The matching of a tree lies in the matchings of its postorder reading

Let `n ≥ 1`, `π ∈ S_n`, and let `T` be a decreasing binary plane tree on `[n]` with postorder
reading `𝒫(T) = π`. Then the matching `M(T)` of `T` is a matching of `π`: `M(T) ∈ 𝒜(π)`.

Labels are in `ℕ`, `S_n` is `permWords n` and `[n]` is `Finset.Icc 1 n`, as in
`BinaryTree.parent_postorder_getElem_of_not_mem_leftEndpoints`.
-/

section

open BinaryTree

variable {α : Type*}

namespace Proof_lem_tree_matching_mem


/-- `S` is a subtree of `T`. -/
private abbrev IsSubtree (S T : BinaryTree α) : Prop :=
  Relation.ReflTransGen (fun S U : BinaryTree α => ∃ m L R, U = node m L R ∧ (S = L ∨ S = R)) S T

private theorem isSubtree_node {S : BinaryTree α} {m : α} {l r : BinaryTree α}
    (h : IsSubtree S (node m l r)) : S = node m l r ∨ IsSubtree S l ∨ IsSubtree S r := by
  rcases Relation.ReflTransGen.cases_tail h with h | ⟨c, hc, m', L, R, he, hcLR⟩
  · exact Or.inl h.symm
  · cases he
    rcases hcLR with rfl | rfl
    · exact Or.inr (Or.inl hc)
    · exact Or.inr (Or.inr hc)

private theorem isSubtree_left {m : α} {l r T : BinaryTree α}
    (h : IsSubtree (node m l r) T) : IsSubtree l T :=
  Relation.ReflTransGen.head ⟨_, _, _, rfl, Or.inl rfl⟩ h

private theorem isSubtree_right {m : α} {l r T : BinaryTree α}
    (h : IsSubtree (node m l r) T) : IsSubtree r T :=
  Relation.ReflTransGen.head ⟨_, _, _, rfl, Or.inr rfl⟩ h

private theorem labels_subset [DecidableEq α] {S T : BinaryTree α} (h : IsSubtree S T) :
    S.labels ⊆ T.labels := by
  induction h with
  | refl => exact subset_rfl
  | tail _ hUV ih =>
    obtain ⟨m, L, R, rfl, rfl | rfl⟩ := hUV
    · exact ih.trans (by intro x; simp; tauto)
    · exact ih.trans (by intro x; simp; tauto)

private theorem isDecreasing_of_isSubtree [DecidableEq α] [LT α] {S T : BinaryTree α}
    (h : IsSubtree S T) (hT : T.IsDecreasing) : S.IsDecreasing := by
  induction h with
  | refl => exact hT
  | tail _ hUV ih =>
    obtain ⟨m, L, R, rfl, rfl | rfl⟩ := hUV
    · exact ih hT.1
    · exact ih hT.2.1

private theorem lt_root [DecidableEq α] [LT α] {m z : α} {l r : BinaryTree α}
    (h : (node m l r).IsDecreasing) (hz : z ∈ l.labels ∨ z ∈ r.labels) : z < m :=
  h.2.2.2 z (Finset.mem_union.2 hz)

private theorem mem_postorder [DecidableEq α] {z : α} :
    ∀ {S : BinaryTree α}, z ∈ S.postorder ↔ z ∈ S.labels
  | nil => by simp
  | node m l r => by simp [mem_postorder (S := l), mem_postorder (S := r)]; tauto

/-- Two subtrees of a decreasing tree with a common label are nested. -/
private theorem isSubtree_or_isSubtree [DecidableEq α] [Preorder α] {z : α} :
    ∀ {T S₁ S₂ : BinaryTree α}, T.IsDecreasing → IsSubtree S₁ T → IsSubtree S₂ T →
      z ∈ S₁.labels → z ∈ S₂.labels → IsSubtree S₁ S₂ ∨ IsSubtree S₂ S₁
  | nil, S₁, S₂, _, h₁, _, hz₁, _ => by
    rcases Relation.ReflTransGen.cases_tail h₁ with rfl | ⟨_, _, _, _, _, he, _⟩
    · simp at hz₁
    · cases he
  | node m l r, S₁, S₂, hT, h₁, h₂, hz₁, hz₂ => by
    rcases isSubtree_node h₁ with rfl | h₁' | h₁'
    · exact Or.inr h₂
    all_goals rcases isSubtree_node h₂ with rfl | h₂' | h₂'
    · exact Or.inl h₁
    · exact isSubtree_or_isSubtree hT.1 h₁' h₂' hz₁ hz₂
    · exact absurd (Finset.disjoint_left.1 hT.2.2.1 (labels_subset h₁' hz₁)
        (labels_subset h₂' hz₂)) (by simp)
    · exact Or.inl h₁
    · exact absurd (Finset.disjoint_left.1 hT.2.2.1 (labels_subset h₂' hz₂)
        (labels_subset h₁' hz₁)) (by simp)
    · exact isSubtree_or_isSubtree hT.2.1 h₁' h₂' hz₁ hz₂

/-- In a decreasing tree, the subtree rooted at a given label is unique. -/
private theorem eq_of_isSubtree_node [DecidableEq α] [Preorder α] {T A B C D : BinaryTree α}
    {x : α} (hT : T.IsDecreasing) (h₁ : IsSubtree (node x A B) T)
    (h₂ : IsSubtree (node x C D) T) : node x A B = node x C D := by
  have key : ∀ {A B C D : BinaryTree α}, IsSubtree (node x C D) T →
      IsSubtree (node x A B) (node x C D) → node x A B = node x C D := by
    intro A B C D h₂ h
    have hd := isDecreasing_of_isSubtree h₂ hT
    rcases isSubtree_node h with h | h | h
    · exact h
    · exact absurd (lt_root hd (Or.inl (labels_subset h (by simp)))) (lt_irrefl x)
    · exact absurd (lt_root hd (Or.inr (labels_subset h (by simp)))) (lt_irrefl x)
  rcases isSubtree_or_isSubtree (z := x) hT h₁ h₂ (by simp) (by simp) with h | h
  · exact key h₂ h
  · exact (key h₁ h).symm

/-- In a decreasing tree, a vertex is the left child of at most one vertex. -/
private theorem eq_of_isSubtree_left [DecidableEq α] [Preorder α] {T A B C D E F : BinaryTree α}
    {x y y' : α} (hT : T.IsDecreasing) (h₁ : IsSubtree (node y (node x A B) E) T)
    (h₂ : IsSubtree (node y' (node x C D) F) T) : y = y' := by
  have key : ∀ {y y' : α} {A B C D E F : BinaryTree α}, IsSubtree (node y' (node x C D) F) T →
      IsSubtree (node y (node x A B) E) T →
      IsSubtree (node y (node x A B) E) (node y' (node x C D) F) → y = y' := by
    intro y y' A B C D E F h₂ h₁ h
    have hd₁ := isDecreasing_of_isSubtree h₁ hT
    have hd₂ := isDecreasing_of_isSubtree h₂ hT
    have hxy : x < y := lt_root hd₁ (Or.inl (by simp))
    rcases isSubtree_node h with h | h | h
    · cases h; rfl
    · have hy := labels_subset h (by simp : y ∈ (node y (node x A B) E).labels)
      have hdx := isDecreasing_of_isSubtree (isSubtree_left h₂) hT
      simp only [labels, Finset.mem_union, Finset.mem_singleton] at hy
      rcases hy with (rfl | hy) | hy
      · exact absurd hxy (lt_irrefl _)
      · exact absurd (lt_root hdx (Or.inl hy)) (not_lt_of_gt hxy)
      · exact absurd (lt_root hdx (Or.inr hy)) (not_lt_of_gt hxy)
    · have hx := labels_subset h (by simp : x ∈ (node y (node x A B) E).labels)
      exact absurd (Finset.disjoint_left.1 hd₂.2.2.1 (by simp) hx) (by simp)
  rcases isSubtree_or_isSubtree (z := x) hT h₁ h₂ (by simp) (by simp) with h | h
  · exact key h₂ h₁ h
  · exact (key h₁ h₂ h).symm

/-- The postorder reading of a subtree of `T` is a factor of the postorder reading of `T`. -/
private theorem postorder_infix {S T : BinaryTree α} (h : IsSubtree S T) :
    S.postorder <:+: T.postorder := by
  induction h with
  | refl => exact List.infix_refl _
  | tail _ hUV ih =>
    obtain ⟨m, L, R, rfl, hL | hR⟩ := hUV
    · subst hL
      exact ih.trans ⟨[], postorder R ++ [m], by simp [postorder]⟩
    · subst hR
      exact ih.trans ⟨postorder L, [m], by simp [postorder]⟩

/-- In a word without repeated letters, an occurrence of `u` after the prefix `P` is at
position `|P|`. -/
private theorem eq_length_of_nodup {l P Q : List α} {u : α} (hl : l.Nodup)
    (h : l = P ++ u :: Q) {i : ℕ} (hi : i < l.length) (hu : l[i] = u) : i = P.length := by
  subst h
  exact hl.getElem_inj_iff.1 (hu.trans (by simp : (P ++ u :: Q)[P.length] = u).symm)

/-- In a word without repeated letters with factor `M` after the prefix `X`, the letters of
`M` are exactly the letters at positions `|X|, …, |X| + |M| - 1`. -/
private theorem getElem_mem_iff_of_nodup {l X M Y : List α} (hl : l.Nodup)
    (h : l = X ++ M ++ Y) {i : ℕ} (hi : i < l.length) :
    l[i] ∈ M ↔ X.length ≤ i ∧ i < X.length + M.length := by
  constructor
  · intro hm
    obtain ⟨M₁, M₂, rfl⟩ := List.append_of_mem hm
    have := eq_length_of_nodup hl (P := X ++ M₁) (Q := M₂ ++ Y) (h.trans (by simp)) hi rfl
    simp at this ⊢
    omega
  · rintro ⟨h₁, h₂⟩
    subst h
    have : (X ++ M ++ Y)[i] = M[i - X.length] := by
      rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by omega)]
    rw [this]
    exact List.getElem_mem _

/-- The data of a pair `(a, b) ∈ M(T)`: the bounds `1 ≤ a < b ≤ |π| - 1`, and the right subtree
`R` of the vertex `π_{b+1}`, whose letters occupy exactly the positions `a + 1, …, b` of `π`. -/
private theorem pair_facts {T : BinaryTree α} (hl : T.postorder.Nodup) {a b : ℕ}
    (hab : (a, b) ∈ T.treeMatching) :
    1 ≤ a ∧ a < b ∧ b ≤ T.postorder.length - 1 ∧
      ∃ (ha : a - 1 < T.postorder.length) (hb : b < T.postorder.length) (L₁ L₂ R : BinaryTree α),
        IsSubtree (node T.postorder[b] (node T.postorder[a - 1] L₁ L₂) R) T ∧
        ∀ (i : ℕ) (hi : i < T.postorder.length), T.postorder[i] ∈ R.postorder ↔ a ≤ i ∧ i < b := by
  simp only [treeMatching, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hab
  obtain ⟨⟨⟨ha1, -⟩, -, hbn⟩, ha, hb, L₁, L₂, d, R₁, R₂, hS⟩ := hab
  obtain ⟨s, t, hst⟩ := postorder_infix hS
  simp only [postorder] at hst
  set R := node d R₁ R₂ with hR
  have hRp : R.postorder = R₁.postorder ++ R₂.postorder ++ [d] := rfl
  have e₁ := eq_length_of_nodup hl (P := s ++ L₁.postorder ++ L₂.postorder)
    (Q := R.postorder ++ T.postorder[b] :: t) (hst.symm.trans (by simp [hRp])) ha rfl
  have e₂ := eq_length_of_nodup hl
    (P := s ++ L₁.postorder ++ L₂.postorder ++ T.postorder[a - 1] :: R.postorder)
    (Q := t) (hst.symm.trans (by simp [hRp])) hb rfl
  have hRl : R.postorder.length = R₁.postorder.length + R₂.postorder.length + 1 := by
    rw [hRp]; simp; omega
  simp only [List.length_append, List.length_cons] at e₁ e₂
  refine ⟨ha1, by omega, hbn, ha, hb, L₁, L₂, R, hS, fun i hi => ?_⟩
  rw [getElem_mem_iff_of_nodup hl
    (X := s ++ L₁.postorder ++ L₂.postorder ++ [T.postorder[a - 1]])
    (Y := T.postorder[b] :: t) (hst.symm.trans (by simp [hRp])) hi]
  simp only [List.length_append, List.length_singleton]
  omega

/-- In a decreasing tree with a repetition-free postorder reading, the pairs of `M(T)` do not
cross: the right subtrees witnessing two pairs are nested, since they share a label, so their
position intervals are nested too. -/
private theorem not_crossing_of_mem_treeMatching [DecidableEq α] [Preorder α] {T : BinaryTree α}
    (hl : T.postorder.Nodup) (hdec : T.IsDecreasing) {a b c d : ℕ}
    (hp : (a, b) ∈ T.treeMatching) (hq : (c, d) ∈ T.treeMatching) :
    ¬ (a < c ∧ c < b ∧ b < d) := by
  rintro ⟨h₁, h₂, h₃⟩
  obtain ⟨-, hab, -, _, hb, _, _, R, hS, hR⟩ := pair_facts hl hp
  obtain ⟨-, hcd, -, _, hd, _, _, R', hS', hR'⟩ := pair_facts hl hq
  have hcR := (hR c (by omega)).2 ⟨by omega, h₂⟩
  have hcR' := (hR' c (by omega)).2 ⟨le_rfl, hcd⟩
  rcases isSubtree_or_isSubtree hdec (isSubtree_right hS) (isSubtree_right hS')
    (mem_postorder.1 hcR) (mem_postorder.1 hcR') with h | h
  · have := (hR a (by omega)).2 ⟨le_rfl, hab⟩
    have := (hR' a (by omega)).1 (mem_postorder.2 (labels_subset h (mem_postorder.1 this)))
    omega
  · have := (hR' (d - 1) (by omega)).2 ⟨by omega, by omega⟩
    have := (hR (d - 1) (by omega)).1 (mem_postorder.2 (labels_subset h (mem_postorder.1 this)))
    omega

/-- Two pairs of `M(T)` sharing an entry are equal: a common left endpoint `a` has a unique
parent `π_{b+1}`, a common right endpoint `b` has a unique left child `π_a`, and `π_{a+1}` is
a leaf, so it is never a right endpoint. -/
private theorem eq_of_mem_treeMatching {n : ℕ} {T : BinaryTree ℕ}
    (hπS : T.postorder ∈ permWords n) (hT : T ∈ decreasingTrees (Finset.Icc 1 n))
    {p q : ℕ × ℕ} (hp : p ∈ T.treeMatching) (hq : q ∈ T.treeMatching) {x : ℕ}
    (hx : x = p.1 ∨ x = p.2) (hx' : x = q.1 ∨ x = q.2) : p = q := by
  have hl : T.postorder.Nodup := hπS.1.1
  obtain ⟨a, b⟩ := p
  obtain ⟨a', b'⟩ := q
  obtain ⟨-, -, -, _, _, _, _, _, hS, -⟩ := pair_facts hl hp
  obtain ⟨-, -, -, _, _, _, _, _, hS', -⟩ := pair_facts hl hq
  simp only at hx hx'
  rcases hx with rfl | rfl <;> rcases hx' with h | h <;> subst h
  · rw [hl.getElem_inj_iff.1 (eq_of_isSubtree_left hT.1 hS hS')]
  · obtain ⟨_, hleaf⟩ := isLeaf_postorder_getElem_of_mem_treeMatching hπS rfl hp
    simpa using eq_of_isSubtree_node hT.1 hleaf hS'
  · obtain ⟨_, hleaf⟩ := isLeaf_postorder_getElem_of_mem_treeMatching hπS rfl hq
    simpa using eq_of_isSubtree_node hT.1 hleaf hS
  · have := hl.getElem_inj_iff.1 (node.inj (node.inj (eq_of_isSubtree_node hT.1 hS hS')).2.1).1
    have := (pair_facts hl hp).1
    have := (pair_facts hl hq).1
    exact Prod.ext (by omega) rfl

end Proof_lem_tree_matching_mem

namespace BinaryTree

open Proof_lem_tree_matching_mem in
/-- **The matching of a tree is a matching of its postorder reading.** Let `n ≥ 1`, `π ∈ S_n`,
and `T ∈ DBT([n])` with `𝒫(T) = π`. Then `M(T) ∈ 𝒜(π)`. -/
@[lognarayana "lem_tree_matching_mem"]
public theorem treeMatching_mem_fiberMatchings {n : ℕ} (hn : 1 ≤ n)
    {π : List ℕ} (hπS : π ∈ permWords n) {T : BinaryTree ℕ}
    (hT : T ∈ decreasingTrees (Finset.Icc 1 n)) (hπ : T.postorder = π) :
    T.treeMatching ∈ π.fiberMatchings := by
  subst hπ
  have hl : T.postorder.Nodup := hπS.1.1
  refine ⟨⟨fun _ hp => (pair_facts hl hp).1, fun _ hp => (pair_facts hl hp).2.1,
    fun _ hp => (pair_facts hl hp).2.2.1, fun _ hp _ hq _ => eq_of_mem_treeMatching hπS hT hp hq,
    fun _ hp _ hq => not_crossing_of_mem_treeMatching hl hT.1 hp hq⟩, ?_, ?_⟩
  · intro j hj
    simp only [List.descentSet, Finset.mem_filter, Finset.mem_Ico] at hj
    obtain ⟨⟨hj1, hj2⟩, hjl, hdes⟩ := hj
    by_contra hjM
    obtain ⟨_, _, _, hS, hLR⟩ := parent_postorder_getElem_of_not_mem_leftEndpoints hn hπS rfl
      hj1 (by have := hπS.2.1; omega) hjM
    have hd := isDecreasing_of_isSubtree hS hT.1
    refine hdes.not_gt ?_
    rcases hLR with ⟨L₁, L₂, rfl⟩ | ⟨R₁, R₂, rfl⟩
    · exact lt_root hd (Or.inl (by simp))
    · exact lt_root hd (Or.inr (by simp))
  · rintro ⟨a, b⟩ hp
    obtain ⟨-, -, -, ha, hb, _, _, _, hS, -⟩ := pair_facts hl hp
    exact ⟨ha, hb, lt_root (isDecreasing_of_isSubtree hS hT.1) (Or.inl (by simp))⟩

end BinaryTree

end

/-!
## Matchings with choices and trees with fixed postorder

Let `n ≥ 1` and `π ∈ S_n`. A decreasing binary plane tree `T` on `[n]` with postorder reading
`𝒫(T) = π` is determined by its matching `M(T)` and its set of right choices `C(T)`, and every
pair `(M, C)` with `M ∈ 𝒜(π)` and `C ⊆ U(M)` (unmatched vertices in `[n - 1]`) arises in this
way: the map `T ↦ (M(T), C(T))` is a bijection between the two sets.

Labels are in `ℕ`, `S_n` is `permWords n` and `[n]` is `Finset.Icc 1 n`. Bijectivity onto the
target is `Set.BijOn` (maps-to, injective-on, surjective-on).
-/

section

open BinaryTree

variable {α : Type*}

namespace Proof_lem_matching_tree_bijection

/-- `S` is a subtree of `T`. -/
private abbrev IsSubtree (S T : BinaryTree α) : Prop :=
  Relation.ReflTransGen (fun S U : BinaryTree α => ∃ m L R, U = node m L R ∧ (S = L ∨ S = R)) S T

private theorem isSubtree_node {S : BinaryTree α} {m : α} {l r : BinaryTree α}
    (h : IsSubtree S (node m l r)) : S = node m l r ∨ IsSubtree S l ∨ IsSubtree S r := by
  rcases Relation.ReflTransGen.cases_tail h with h | ⟨c, hc, m', L, R, he, hcLR⟩
  · exact Or.inl h.symm
  · cases he
    rcases hcLR with rfl | rfl
    · exact Or.inr (Or.inl hc)
    · exact Or.inr (Or.inr hc)

private theorem labels_subset [DecidableEq α] {S T : BinaryTree α} (h : IsSubtree S T) :
    S.labels ⊆ T.labels := by
  induction h with
  | refl => exact subset_rfl
  | tail _ hUV ih =>
    obtain ⟨m, L, R, rfl, rfl | rfl⟩ := hUV
    · exact ih.trans (by intro x; simp; tauto)
    · exact ih.trans (by intro x; simp; tauto)

private theorem isDecreasing_of_isSubtree [DecidableEq α] [LT α] {S T : BinaryTree α}
    (h : IsSubtree S T) (hT : T.IsDecreasing) : S.IsDecreasing := by
  induction h with
  | refl => exact hT
  | tail _ hUV ih =>
    obtain ⟨m, L, R, rfl, rfl | rfl⟩ := hUV
    · exact ih hT.1
    · exact ih hT.2.1

private theorem lt_root [DecidableEq α] [LT α] {m z : α} {l r : BinaryTree α}
    (h : (node m l r).IsDecreasing) (hz : z ∈ l.labels ∨ z ∈ r.labels) : z < m :=
  h.2.2.2 z (Finset.mem_union.2 hz)

/-- Two subtrees of a decreasing tree with a common label are nested. -/
private theorem isSubtree_or_isSubtree [DecidableEq α] [Preorder α] {z : α} :
    ∀ {T S₁ S₂ : BinaryTree α}, T.IsDecreasing → IsSubtree S₁ T → IsSubtree S₂ T →
      z ∈ S₁.labels → z ∈ S₂.labels → IsSubtree S₁ S₂ ∨ IsSubtree S₂ S₁
  | nil, S₁, S₂, _, h₁, _, hz₁, _ => by
    rcases Relation.ReflTransGen.cases_tail h₁ with rfl | ⟨_, _, _, _, _, he, _⟩
    · simp at hz₁
    · cases he
  | node m l r, S₁, S₂, hT, h₁, h₂, hz₁, hz₂ => by
    rcases isSubtree_node h₁ with rfl | h₁' | h₁'
    · exact Or.inr h₂
    all_goals rcases isSubtree_node h₂ with rfl | h₂' | h₂'
    · exact Or.inl h₁
    · exact isSubtree_or_isSubtree hT.1 h₁' h₂' hz₁ hz₂
    · exact absurd (Finset.disjoint_left.1 hT.2.2.1 (labels_subset h₁' hz₁)
        (labels_subset h₂' hz₂)) (by simp)
    · exact Or.inl h₁
    · exact absurd (Finset.disjoint_left.1 hT.2.2.1 (labels_subset h₂' hz₂)
        (labels_subset h₁' hz₁)) (by simp)
    · exact isSubtree_or_isSubtree hT.2.1 h₁' h₂' hz₁ hz₂

/-- In a decreasing tree, the subtree rooted at a given label is unique. -/
private theorem eq_of_isSubtree_node [DecidableEq α] [Preorder α] {T A B C D : BinaryTree α}
    {x : α} (hT : T.IsDecreasing) (h₁ : IsSubtree (node x A B) T)
    (h₂ : IsSubtree (node x C D) T) : node x A B = node x C D := by
  have key : ∀ {A B C D : BinaryTree α}, IsSubtree (node x C D) T →
      IsSubtree (node x A B) (node x C D) → node x A B = node x C D := by
    intro A B C D h₂ h
    have hd := isDecreasing_of_isSubtree h₂ hT
    rcases isSubtree_node h with h | h | h
    · exact h
    · exact absurd (lt_root hd (Or.inl (labels_subset h (by simp)))) (lt_irrefl x)
    · exact absurd (lt_root hd (Or.inr (labels_subset h (by simp)))) (lt_irrefl x)
  rcases isSubtree_or_isSubtree (z := x) hT h₁ h₂ (by simp) (by simp) with h | h
  · exact key h₂ h
  · exact (key h₁ h).symm

/-- Whether a tree is nonempty. -/
private def isNode : BinaryTree α → Bool
  | nil => false
  | node _ _ _ => true

/-- The postorder reading of `T`, each letter annotated with whether its vertex has a left
child and whether it has a right child. -/
private def kinds : BinaryTree α → List (α × Bool × Bool)
  | nil => []
  | node m l r => kinds l ++ kinds r ++ [(m, isNode l, isNode r)]

/-- One step of the reconstruction of a forest from annotated postorder letters; the head of
the list is the last tree. -/
private def step : List (BinaryTree α) → α × Bool × Bool → List (BinaryTree α)
  | S, (x, false, false) => node x nil nil :: S
  | t :: S, (x, true, false) => node x t nil :: S
  | t :: S, (x, false, true) => node x nil t :: S
  | t :: u :: S, (x, true, true) => node x u t :: S
  | S, _ => S

/-- Push a tree on a stack, unless it is empty. -/
private def push : BinaryTree α → List (BinaryTree α) → List (BinaryTree α)
  | nil, S => S
  | node m l r, S => node m l r :: S

private theorem foldl_step_kinds : ∀ (T : BinaryTree α) (S : List (BinaryTree α)),
    (kinds T).foldl step S = push T S
  | nil, S => rfl
  | node m l r, S => by
    simp only [kinds, List.foldl_append, foldl_step_kinds l, foldl_step_kinds r,
      List.foldl_cons, List.foldl_nil]
    cases l <;> cases r <;> rfl

private theorem postorder_eq_map_kinds : ∀ T : BinaryTree α, T.postorder = (kinds T).map Prod.fst
  | nil => rfl
  | node m l r => by simp [kinds, postorder_eq_map_kinds l, postorder_eq_map_kinds r]

private theorem kinds_injective {T T' : BinaryTree α} (hT : T ≠ nil) (hT' : T' ≠ nil)
    (h : kinds T = kinds T') : T = T' := by
  have h1 := foldl_step_kinds T []
  rw [h, foldl_step_kinds] at h1
  cases T <;> cases T' <;> simp_all [push]

private theorem exists_of_mem_kinds {e : α × Bool × Bool} : ∀ {T : BinaryTree α},
    e ∈ kinds T → ∃ L R, IsSubtree (node e.1 L R) T ∧ e.2 = (isNode L, isNode R)
  | nil, h => by simp [kinds] at h
  | node m l r, h => by
    simp only [kinds, List.mem_append, List.mem_singleton] at h
    rcases h with (h | h) | rfl
    · obtain ⟨L, R, hS, he⟩ := exists_of_mem_kinds h
      exact ⟨L, R, hS.tail ⟨_, _, _, rfl, Or.inl rfl⟩, he⟩
    · obtain ⟨L, R, hS, he⟩ := exists_of_mem_kinds h
      exact ⟨L, R, hS.tail ⟨_, _, _, rfl, Or.inr rfl⟩, he⟩
    · exact ⟨l, r, Relation.ReflTransGen.refl, rfl⟩

private theorem labels_eq_toFinset [DecidableEq α] : ∀ T : BinaryTree α,
    T.labels = T.postorder.toFinset
  | nil => rfl
  | node m l r => by
    ext x; simp [labels_eq_toFinset l, labels_eq_toFinset r]

private theorem le_root [DecidableEq α] [Preorder α] {m z : α} {l r : BinaryTree α}
    (h : (node m l r).IsDecreasing) (hz : z ∈ (node m l r).labels) : z ≤ m := by
  simp only [labels, Finset.mem_union, Finset.mem_singleton] at hz
  rcases hz with (rfl | hz) | hz
  · exact le_rfl
  · exact (lt_root h (Or.inl hz)).le
  · exact (lt_root h (Or.inr hz)).le

private theorem mem_rightChildLabels_of_isSubtree [DecidableEq α] {x : α}
    {L R T : BinaryTree α} (h : IsSubtree (node x L R) T) (hR : R ≠ nil) :
    x ∈ T.rightChildLabels := by
  have key : ∀ {S T : BinaryTree α}, IsSubtree S T → S.rightChildLabels ⊆ T.rightChildLabels := by
    intro S T h
    induction h with
    | refl => exact subset_rfl
    | tail _ hUV ih =>
      obtain ⟨m, L, R, rfl, rfl | rfl⟩ := hUV
      · exact ih.trans (by intro x; simp only [rightChildLabels]; intro; simp_all)
      · exact ih.trans (by intro x; simp only [rightChildLabels]; intro; simp_all)
  apply key h
  cases R with
  | nil => exact absurd rfl hR
  | node => simp

private theorem exists_of_mem_rightChildLabels [DecidableEq α] {x : α} : ∀ {T : BinaryTree α},
    x ∈ T.rightChildLabels → ∃ L R, IsSubtree (node x L R) T ∧ R ≠ nil
  | nil, h => by simp at h
  | node m l r, h => by
    simp only [rightChildLabels, Finset.mem_union] at h
    rcases h with (h | h) | h
    · obtain ⟨L, R, hS, hR⟩ := exists_of_mem_rightChildLabels h
      exact ⟨L, R, hS.tail ⟨_, _, _, rfl, Or.inl rfl⟩, hR⟩
    · obtain ⟨L, R, hS, hR⟩ := exists_of_mem_rightChildLabels h
      exact ⟨L, R, hS.tail ⟨_, _, _, rfl, Or.inr rfl⟩, hR⟩
    · cases r with
      | nil => simp at h
      | node =>
        simp only [Finset.mem_singleton] at h
        subst h
        exact ⟨l, _, Relation.ReflTransGen.refl, by simp⟩

private theorem exists_of_mem_leftEndpoints {M : Finset (ℕ × ℕ)} {a : ℕ}
    (h : a ∈ M.leftEndpoints) : ∃ b, (a, b) ∈ M := by
  obtain ⟨⟨x, y⟩, hx, rfl⟩ := Finset.mem_image.1 h
  exact ⟨y, hx⟩

private theorem exists_of_mem_image_snd {M : Finset (ℕ × ℕ)} {b : ℕ}
    (h : b ∈ M.image Prod.snd) : ∃ a, (a, b) ∈ M := by
  obtain ⟨⟨x, y⟩, hx, rfl⟩ := Finset.mem_image.1 h
  exact ⟨x, hx⟩

/-- If two noncrossing partial matchings have the same left endpoints and the same right
endpoints, then every pair of the first is a pair of the second. Induction on the length of the
pair `(a, b)`: the partners of `a` and of `b` in `M'` would otherwise cross a shorter pair. -/
private theorem subset_of_leftEndpoints_eq {N N' : ℕ} {M M' : Finset (ℕ × ℕ)}
    (hM : IsNoncrossingPartialMatching N M) (hM' : IsNoncrossingPartialMatching N' M')
    (hL : M.leftEndpoints = M'.leftEndpoints) (hR : M.image Prod.snd = M'.image Prod.snd) :
    M ⊆ M' := by
  suffices ∀ k a b, b - a = k → (a, b) ∈ M → (a, b) ∈ M' by
    rintro ⟨a, b⟩ h; exact this _ a b rfl h
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro a b hk hab
  have hab' := hM.fst_lt_snd _ hab
  obtain ⟨b', h₁⟩ := exists_of_mem_leftEndpoints
    (show a ∈ M'.leftEndpoints from hL ▸ Finset.mem_image_of_mem Prod.fst hab)
  obtain ⟨a', h₂⟩ := exists_of_mem_image_snd
    (show b ∈ M'.image Prod.snd from hR ▸ Finset.mem_image_of_mem Prod.snd hab)
  have h₁' := hM'.fst_lt_snd _ h₁
  have h₂' := hM'.fst_lt_snd _ h₂
  dsimp only at h₁' h₂' hab'
  rcases lt_trichotomy b' b with hb | hb | hb
  · obtain ⟨c, h₃⟩ := exists_of_mem_image_snd
      (show b' ∈ M.image Prod.snd from hR ▸ Finset.mem_image_of_mem Prod.snd h₁)
    have h₃' := hM.fst_lt_snd _ h₃
    dsimp only at h₃'
    have hca : c ≠ a := by
      rintro rfl
      have := hM.eq_of_mem_of_mem _ h₃ _ hab c (Or.inl rfl) (Or.inl rfl)
      simp at this; omega
    rcases lt_or_gt_of_ne hca with hc | hc
    · exact absurd ⟨hc, by omega, hb⟩ (hM.noncrossing _ h₃ _ hab)
    · have := ih (b' - c) (by omega) c b' rfl h₃
      have := hM'.eq_of_mem_of_mem _ this _ h₁ b' (Or.inr rfl) (Or.inr rfl)
      simp at this; omega
  · exact hb ▸ h₁
  · have haa : a' ≠ a := by
      rintro rfl
      have := hM'.eq_of_mem_of_mem _ h₁ _ h₂ a' (Or.inl rfl) (Or.inl rfl)
      simp at this; omega
    rcases lt_or_gt_of_ne haa with hc | hc
    · exact absurd ⟨hc, by omega, hb⟩ (hM'.noncrossing _ h₂ _ h₁)
    · obtain ⟨d, h₃⟩ := exists_of_mem_leftEndpoints
        (show a' ∈ M.leftEndpoints from hL ▸ Finset.mem_image_of_mem Prod.fst h₂)
      have h₃' := hM.fst_lt_snd _ h₃
      dsimp only at h₃'
      have hdb : d ≠ b := by
        rintro rfl
        have := hM.eq_of_mem_of_mem _ h₃ _ hab d (Or.inr rfl) (Or.inr rfl)
        simp at this; omega
      rcases lt_or_gt_of_ne hdb with hd | hd
      · have := ih (d - a') (by omega) a' d rfl h₃
        have := hM'.eq_of_mem_of_mem _ this _ h₂ a' (Or.inl rfl) (Or.inl rfl)
        simp at this; omega
      · exact absurd ⟨hc, by omega, hd⟩ (hM.noncrossing _ hab _ h₃)

/-- Whether the vertex at position `j` (`0`-based) has a left child, read off a matching `M`
and a set `C` of right choices. -/
private def hasLeft (N : ℕ) (M : Finset (ℕ × ℕ)) (C : Finset ℕ) (j : ℕ) : Bool :=
  decide (j ∈ M.image Prod.snd ∨ (j ∈ Finset.unmatchedVertices N M ∧ j ∉ C))

/-- Whether the vertex at position `j` (`0`-based) has a right child, read off `M` and `C`. -/
private def hasRight (M : Finset (ℕ × ℕ)) (C : Finset ℕ) (j : ℕ) : Bool :=
  decide (j ∈ M.image Prod.snd ∨ j ∈ C)

section decode

variable {N : ℕ} {M : Finset (ℕ × ℕ)} {C : Finset ℕ}

private theorem mem_image_snd_iff {j : ℕ} :
    j ∈ M.image Prod.snd ↔ hasLeft N M C j = true ∧ hasRight M C j = true := by
  simp only [hasLeft, hasRight, decide_eq_true_eq]
  tauto

private theorem mem_C_iff (hC : C ⊆ Finset.unmatchedVertices N M) {j : ℕ} :
    j ∈ C ↔ hasRight M C j = true ∧ hasLeft N M C j = false := by
  have h1 : j ∈ C → j ∉ M.image Prod.snd := fun h hj => by
    have := hC h
    simp only [Finset.unmatchedVertices, Finset.mem_sdiff, Finset.mem_union] at this
    tauto
  simp only [hasLeft, hasRight, decide_eq_true_eq, decide_eq_false_iff_not]
  tauto

private theorem mem_leftEndpoints_iff (hM : IsNoncrossingPartialMatching N M)
    (hC : C ⊆ Finset.unmatchedVertices N M) {j : ℕ} :
    j ∈ M.leftEndpoints ↔
      (1 ≤ j ∧ j ≤ N) ∧ hasLeft N M C j = false ∧ hasRight M C j = false := by
  have hCU : j ∈ C → j ∈ Finset.unmatchedVertices N M := fun h => hC h
  simp only [hasLeft, hasRight, decide_eq_false_iff_not, Finset.unmatchedVertices,
    Finset.mem_sdiff, Finset.mem_union, Finset.mem_Icc] at hCU ⊢
  constructor
  · intro hj
    obtain ⟨b, hb⟩ := exists_of_mem_leftEndpoints hj
    have h1 := hM.one_le_fst _ hb
    have h2 := hM.fst_lt_snd _ hb
    have h3 := hM.snd_le _ hb
    have hR : j ∉ M.image Prod.snd := fun h => by
      obtain ⟨a, ha⟩ := exists_of_mem_image_snd h
      have := hM.eq_of_mem_of_mem _ hb _ ha j (Or.inl rfl) (Or.inr rfl)
      simp at this; dsimp at h2; omega
    dsimp at h1 h2 h3
    refine ⟨⟨h1, by omega⟩, ?_, ?_⟩ <;> tauto
  · rintro ⟨hj, h1, h2⟩
    tauto

private theorem hasLeft_hasRight_eq_false_of_lt (hM : IsNoncrossingPartialMatching N M)
    (hC : C ⊆ Finset.unmatchedVertices N M) {j : ℕ} (hj : N < j) :
    hasLeft N M C j = false ∧ hasRight M C j = false := by
  have hR : j ∉ M.image Prod.snd := fun h => by
    obtain ⟨a, ha⟩ := exists_of_mem_image_snd h
    have := hM.snd_le _ ha
    dsimp at this; omega
  have hU : j ∉ Finset.unmatchedVertices N M := fun h => by
    simp only [Finset.unmatchedVertices, Finset.mem_sdiff, Finset.mem_Icc] at h
    omega
  have hCj : j ∉ C := fun h => hU (hC h)
  simp only [hasLeft, hasRight, decide_eq_false_iff_not]
  tauto

/-- A noncrossing partial matching `M` on `[N]` and a set `C ⊆ U(M)` are determined by the
child annotations `hasLeft` and `hasRight` at the positions `j ≤ N`. -/
private theorem eq_of_hasLeft_hasRight {M' : Finset (ℕ × ℕ)} {C' : Finset ℕ}
    (hM : IsNoncrossingPartialMatching N M) (hC : C ⊆ Finset.unmatchedVertices N M)
    (hM' : IsNoncrossingPartialMatching N M') (hC' : C' ⊆ Finset.unmatchedVertices N M')
    (h : ∀ j ≤ N, hasLeft N M C j = hasLeft N M' C' j ∧ hasRight M C j = hasRight M' C' j) :
    M = M' ∧ C = C' := by
  have key : ∀ j, hasLeft N M C j = hasLeft N M' C' j ∧ hasRight M C j = hasRight M' C' j := by
    intro j
    by_cases hj : j ≤ N
    · exact h j hj
    · have h1 := hasLeft_hasRight_eq_false_of_lt hM hC (not_le.1 hj)
      have h2 := hasLeft_hasRight_eq_false_of_lt hM' hC' (not_le.1 hj)
      rw [h1.1, h1.2, h2.1, h2.2]; exact ⟨rfl, rfl⟩
  have hR : M.image Prod.snd = M'.image Prod.snd := by
    ext j; rw [mem_image_snd_iff (N := N) (C := C), mem_image_snd_iff (N := N) (C := C'),
      (key j).1, (key j).2]
  have hL : M.leftEndpoints = M'.leftEndpoints := by
    ext j; rw [mem_leftEndpoints_iff hM hC, mem_leftEndpoints_iff hM' hC', (key j).1, (key j).2]
  refine ⟨(subset_of_leftEndpoints_eq hM hM' hL hR).antisymm
    (subset_of_leftEndpoints_eq hM' hM hL.symm hR.symm), ?_⟩
  ext j; rw [mem_C_iff hC, mem_C_iff hC', (key j).1, (key j).2]

end decode

private theorem isNode_eq_true_iff {T : BinaryTree α} : isNode T = true ↔ T ≠ nil := by
  cases T <;> simp [isNode]

private theorem mem_treeMatching_iff {T : BinaryTree α} {a b : ℕ} :
    (a, b) ∈ T.treeMatching ↔ ((1 ≤ a ∧ a ≤ T.postorder.length) ∧
      1 ≤ b ∧ b ≤ T.postorder.length - 1) ∧
      ∃ (ha : a - 1 < T.postorder.length) (hb : b < T.postorder.length)
        (L₁ L₂ : BinaryTree α) (d : α) (R₁ R₂ : BinaryTree α),
        IsSubtree (node T.postorder[b] (node T.postorder[a - 1] L₁ L₂) (node d R₁ R₂)) T := by
  classical
  simp only [treeMatching, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]

private theorem treeRightChoices_subset [DecidableEq α] (T : BinaryTree α) :
    T.treeRightChoices ⊆ Finset.unmatchedVertices (T.postorder.length - 1) T.treeMatching :=
  Finset.filter_subset _ _

/-- In a tree of the source set, the child annotations of the vertex at position `j` are the
ones read off `M(T)` and `C(T)`. -/
private theorem isNode_eq_hasLeft_hasRight {n : ℕ} (hn : 1 ≤ n) {T : BinaryTree ℕ}
    (hπS : T.postorder ∈ permWords n) (hT : T ∈ decreasingTrees (Finset.Icc 1 n)) {j : ℕ}
    (hj : j < T.postorder.length) {L R : BinaryTree ℕ}
    (hS : IsSubtree (node T.postorder[j] L R) T) :
    isNode L = hasLeft (n - 1) T.treeMatching T.treeRightChoices j ∧
      isNode R = hasRight T.treeMatching T.treeRightChoices j := by
  have hlen : T.postorder.length = n := hπS.2.1
  have hMm := treeMatching_mem_fiberMatchings hn hπS hT rfl
  have hNC : IsNoncrossingPartialMatching (n - 1) T.treeMatching := hlen ▸ hMm.1
  have huniq : ∀ {L' R'}, IsSubtree (node T.postorder[j] L' R') T → L = L' ∧ R = R' := by
    intro L' R' h'
    have := eq_of_isSubtree_node hT.1 hS h'
    simpa using this
  have hCU := hlen ▸ treeRightChoices_subset T
  by_cases hR : j ∈ T.treeMatching.image Prod.snd
  · obtain ⟨a, ha⟩ := exists_of_mem_image_snd hR
    obtain ⟨-, _, hb, L₁, L₂, d, R₁, R₂, hS'⟩ := mem_treeMatching_iff.1 ha
    obtain ⟨rfl, rfl⟩ := huniq hS'
    simp [isNode, hasLeft, hasRight, hR]
  have hnU : j ∉ Finset.unmatchedVertices (n - 1) T.treeMatching →
      hasLeft (n - 1) T.treeMatching T.treeRightChoices j = false ∧
      hasRight T.treeMatching T.treeRightChoices j = false := fun hU => by
    have : j ∉ T.treeRightChoices := fun h => hU (hCU h)
    simp only [hasLeft, hasRight, decide_eq_false_iff_not]
    tauto
  by_cases hj0 : j = 0
  · subst hj0
    have hU : 0 ∉ Finset.unmatchedVertices (n - 1) T.treeMatching := by
      simp [Finset.unmatchedVertices]
    rw [(hnU hU).1, (hnU hU).2]
    by_contra hc
    have hc' : L ≠ nil ∨ R ≠ nil := by
      by_contra h; push Not at h; obtain ⟨rfl, rfl⟩ := h; simp [isNode] at hc
    have := postorder_getElem?_pred_eq_last_child hT (j := 1) le_rfl
      (by simp [List.getElem?_eq_getElem hj]) hS hc'
    omega
  by_cases hLE : j ∈ T.treeMatching.leftEndpoints
  · obtain ⟨b, hb⟩ := exists_of_mem_leftEndpoints hLE
    obtain ⟨h, hS'⟩ := isLeaf_postorder_getElem_of_mem_treeMatching hπS rfl hb
    obtain ⟨rfl, rfl⟩ := huniq hS'
    have hU : j ∉ Finset.unmatchedVertices (n - 1) T.treeMatching := by
      simp only [Finset.unmatchedVertices, Finset.mem_sdiff, Finset.mem_union]; tauto
    rw [(hnU hU).1, (hnU hU).2]
    exact ⟨rfl, rfl⟩
  have hU : j ∈ Finset.unmatchedVertices (n - 1) T.treeMatching := by
    simp only [Finset.unmatchedVertices, Finset.mem_sdiff, Finset.mem_union, Finset.mem_Icc]
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    tauto
  obtain ⟨_, L', R', hS', hch⟩ := parent_postorder_getElem_of_not_mem_leftEndpoints hn hπS rfl
    (by omega) (by omega) hLE
  obtain ⟨rfl, rfl⟩ := huniq hS'
  have hex : L ≠ nil ∨ R ≠ nil := by
    rcases hch with ⟨L₁, L₂, rfl⟩ | ⟨R₁, R₂, rfl⟩
    · exact Or.inl (by simp)
    · exact Or.inr (by simp)
  have hnb : ¬ (L ≠ nil ∧ R ≠ nil) := by
    rintro ⟨hL, hR'⟩
    obtain ⟨y, L₁, L₂, rfl⟩ : ∃ y L₁ L₂, L = node y L₁ L₂ := by
      cases L with
      | nil => exact absurd rfl hL
      | node y L₁ L₂ => exact ⟨y, L₁, L₂, rfl⟩
    obtain ⟨d, R₁, R₂, rfl⟩ : ∃ d R₁ R₂, R = node d R₁ R₂ := by
      cases R with
      | nil => exact absurd rfl hR'
      | node d R₁ R₂ => exact ⟨d, R₁, R₂, rfl⟩
    have hy : y ∈ T.postorder := by
      rw [← List.mem_toFinset, ← labels_eq_toFinset]
      exact labels_subset hS (by simp)
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hy
    apply hR
    refine Finset.mem_image.2 ⟨(i + 1, j), mem_treeMatching_iff.2 ⟨⟨⟨by omega, by omega⟩,
      by omega, by omega⟩, by simpa using hi, hj, L₁, L₂, d, R₁, R₂, by simpa using hS⟩, rfl⟩
  have hC : j ∈ T.treeRightChoices ↔ R ≠ nil := by
    have hU' : j ∈ Finset.unmatchedVertices (T.postorder.length - 1) T.treeMatching := by
      rw [hlen]; exact hU
    unfold treeRightChoices
    rw [Finset.mem_filter]
    constructor
    · rintro ⟨-, _, h⟩
      obtain ⟨L', R', hS', hR'⟩ := exists_of_mem_rightChildLabels h
      obtain ⟨-, rfl⟩ := huniq hS'
      exact hR'
    · intro h
      exact ⟨hU', hj, mem_rightChildLabels_of_isSubtree hS h⟩
  simp only [hasLeft, hasRight, hR, hU, false_or, true_and, hC]
  cases L <;> cases R <;> simp_all [isNode]

/-- The annotated letter at position `j` of `π`, read off `M` and `C`. -/
private def code (π : List ℕ) (M : Finset (ℕ × ℕ)) (C : Finset ℕ) (j : ℕ) : ℕ × Bool × Bool :=
  (π.getD j 0, hasLeft (π.length - 1) M C j, hasRight M C j)

private theorem length_kinds (T : BinaryTree α) : (kinds T).length = T.postorder.length := by
  rw [postorder_eq_map_kinds, List.length_map]

/-- The annotated postorder reading of a tree of the source set is the one read off `M(T)` and
`C(T)`. -/
private theorem kinds_eq_map_code {n : ℕ} (hn : 1 ≤ n) {T : BinaryTree ℕ}
    (hπS : T.postorder ∈ permWords n) (hT : T ∈ decreasingTrees (Finset.Icc 1 n)) :
    kinds T = (List.range n).map (code T.postorder T.treeMatching T.treeRightChoices) := by
  have hlen : T.postorder.length = n := hπS.2.1
  apply List.ext_getElem
  · simp [length_kinds, hlen]
  intro j h1 h2
  have hj : j < T.postorder.length := by rwa [← length_kinds]
  have key : T.postorder[j] = ((kinds T)[j]).1 := by
    rw [List.getElem_of_eq (postorder_eq_map_kinds T), List.getElem_map]
  obtain ⟨L, R, hS, he⟩ := exists_of_mem_kinds (List.getElem_mem h1)
  rw [← key] at hS
  obtain ⟨hl, hr⟩ := isNode_eq_hasLeft_hasRight hn hπS hT hj hS
  rw [List.getElem_map, List.getElem_range]
  refine Prod.ext ?_ ?_
  · rw [← key]; simp [code, List.getElem?_eq_getElem hj]
  · rw [he, hl, hr, code, hlen]

/-- The root label of a tree (`0` for the empty tree). -/
private def rootLabel : BinaryTree ℕ → ℕ
  | nil => 0
  | node m _ _ => m

private theorem forall_lt_of_rootLabel_lt {t : BinaryTree ℕ} (ht : t.IsDecreasing) {x : ℕ}
    (h : rootLabel t < x) : ∀ a ∈ t.labels, a < x := by
  cases t with
  | nil => simp
  | node m l r => exact fun a ha => lt_of_le_of_lt (le_root ht ha) h

private theorem nodup_map_range_getD {π : List ℕ} (hnd : π.Nodup) {j : ℕ} (hj : j ≤ π.length) :
    ((List.range j).map fun i => π.getD i 0).Nodup := by
  refine List.Nodup.map_on ?_ List.nodup_range
  intro x hx y hy hxy
  simp only [List.mem_range] at hx hy
  rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)] at hxy
  exact (hnd.getElem_inj_iff).1 hxy

section construction

variable {π : List ℕ} {M : Finset (ℕ × ℕ)} {C : Finset ℕ}

/-- The invariant of the construction after the first `j` letters: a stack `S` of decreasing
trees (last tree first) whose annotated postorder readings concatenate to the first `j` codes;
the last tree has root `π_j`, and the others have roots `π_a` for the left endpoints `a` of the
pairs `(a, b) ∈ M` with `a < j ≤ b`, listed in `os` in decreasing order. -/
private def Inv (π : List ℕ) (M : Finset (ℕ × ℕ)) (C : Finset ℕ) (j : ℕ)
    (S : List (BinaryTree ℕ)) (os : List ℕ) : Prop :=
  S.length = os.length + 1 ∧
  S.reverse.flatMap kinds = (List.range j).map (code π M C) ∧
  (∀ t ∈ S, t.IsDecreasing ∧ t ≠ nil) ∧
  S.map rootLabel = π.getD (j - 1) 0 :: os.map (fun a => π.getD (a - 1) 0) ∧
  os.Pairwise (· > ·) ∧ ∀ x, x ∈ os ↔ ∃ b, (x, b) ∈ M ∧ x < j ∧ j ≤ b

private theorem flatMap_postorder_eq {j : ℕ} {S : List (BinaryTree ℕ)}
    (h : S.reverse.flatMap kinds = (List.range j).map (code π M C)) :
    S.reverse.flatMap postorder = (List.range j).map fun i => π.getD i 0 := by
  have : S.reverse.flatMap postorder = (S.reverse.flatMap kinds).map Prod.fst := by
    rw [List.map_flatMap]
    congr 1
    funext t
    exact postorder_eq_map_kinds t
  rw [this, h, List.map_map]
  rfl

private theorem inv_one (hM : M ∈ π.fiberMatchings)
    (hC : C ⊆ Finset.unmatchedVertices (π.length - 1) M) :
    Inv π M C 1 [node (π.getD 0 0) nil nil] [] := by
  have hNC := hM.1
  have h0R : 0 ∉ M.image Prod.snd := fun h => by
    obtain ⟨a, ha⟩ := exists_of_mem_image_snd h
    have := hNC.fst_lt_snd _ ha; dsimp at this; omega
  have h0U : 0 ∉ Finset.unmatchedVertices (π.length - 1) M := by
    simp [Finset.unmatchedVertices]
  have h0C : 0 ∉ C := fun h => h0U (hC h)
  refine ⟨rfl, ?_, ?_, rfl, List.Pairwise.nil, ?_⟩
  · simp [kinds, isNode, code, hasLeft, hasRight, h0R, h0U, h0C]
  · simp
  · intro x
    simp only [List.not_mem_nil, false_iff, not_exists, not_and]
    intro b hb hx
    have := hNC.one_le_fst _ hb; dsimp at this; omega

private theorem getD_pred_lt_getD (hnd : π.Nodup) (hM : M ∈ π.fiberMatchings) {j : ℕ}
    (hj1 : 1 ≤ j) (hj : j < π.length) (hLE : j ∉ M.leftEndpoints) :
    π.getD (j - 1) 0 < π.getD j 0 := by
  rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ hj]
  have hD : j ∉ π.descentSet := fun h => hLE (hM.2.1 h)
  simp only [List.descentSet, Finset.mem_filter, Finset.mem_Ico, not_and, not_exists] at hD
  have h1' := hD ⟨hj1, hj⟩ hj
  have h2' : π[j] ≠ π[j - 1] := fun he => by
    have := (hnd.getElem_inj_iff).1 he
    omega
  omega

private theorem inv_step_of_mem_leftEndpoints (hM : M ∈ π.fiberMatchings)
    (hC : C ⊆ Finset.unmatchedVertices (π.length - 1) M) {j : ℕ} {S : List (BinaryTree ℕ)}
    {os : List ℕ} (h : Inv π M C j S os) (hLE : j ∈ M.leftEndpoints) :
    ∃ os', Inv π M C (j + 1) (step S (code π M C j)) os' := by
  have hNC := hM.1
  obtain ⟨h1, h6, h3, h4, h5, h5'⟩ := h
  obtain ⟨hjN, hl, hr⟩ := (mem_leftEndpoints_iff hNC hC).1 hLE
  have hc : code π M C j = (π.getD j 0, false, false) := by simp [code, hl, hr]
  obtain ⟨b, hb⟩ := exists_of_mem_leftEndpoints hLE
  have hjR : j ∉ M.image Prod.snd := fun h' => by
    rw [mem_image_snd_iff (N := π.length - 1) (C := C), hl] at h'
    simp at h'
  rw [hc]
  refine ⟨j :: os, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [step, h1]
  · simp [step, List.range_succ, h6, kinds, isNode, hc]
  · simp only [step, List.mem_cons, forall_eq_or_imp]
    exact ⟨⟨by simp, by simp⟩, h3⟩
  · simp [step, h4, rootLabel]
  · refine List.Pairwise.cons (fun x hx => ?_) h5
    obtain ⟨_, _, hx, _⟩ := (h5' x).1 hx
    exact hx
  · intro x
    simp only [List.mem_cons, h5']
    constructor
    · rintro (rfl | ⟨b', hb', hx, hb''⟩)
      · exact ⟨b, hb, by omega, by have := hNC.fst_lt_snd _ hb; dsimp at this; omega⟩
      · refine ⟨b', hb', by omega, ?_⟩
        rcases eq_or_lt_of_le hb'' with rfl | h'
        · exact absurd (Finset.mem_image_of_mem Prod.snd hb') hjR
        · omega
    · rintro ⟨b', hb', hx, hb''⟩
      rcases eq_or_lt_of_le (Nat.lt_succ_iff.1 hx) with rfl | h'
      · exact Or.inl rfl
      · exact Or.inr ⟨b', hb', h', by omega⟩

/-- If `(a, j) ∈ M` and `os` lists, in decreasing order, the left endpoints of the pairs open at
`j`, then `a` is the head of `os`. -/
private theorem exists_eq_cons_of_mem {N j a : ℕ} {os : List ℕ}
    (hNC : IsNoncrossingPartialMatching N M) (h5 : os.Pairwise (· > ·))
    (h5' : ∀ x, x ∈ os ↔ ∃ b, (x, b) ∈ M ∧ x < j ∧ j ≤ b) (ha : (a, j) ∈ M) (hao : a ∈ os) :
    ∃ os'', os = a :: os'' := by
  cases os with
  | nil => simp at hao
  | cons a' os'' =>
    refine ⟨os'', ?_⟩
    by_contra hne
    have hne' : a' ≠ a := fun h => hne (by rw [h])
    have ha' : a ∈ os'' := (List.mem_cons.1 hao).resolve_left (Ne.symm hne')
    have hgt : a' > a := List.rel_of_pairwise_cons h5 ha'
    obtain ⟨b', hb', ha'j, hjb'⟩ := (h5' a').1 (by simp)
    have hb'j : b' ≠ j := by
      rintro rfl
      have := hNC.eq_of_mem_of_mem _ hb' _ ha b' (Or.inr rfl) (Or.inr rfl)
      simp at this
      omega
    exact hNC.noncrossing _ ha _ hb' ⟨hgt, ha'j, by omega⟩

private theorem mem_tail_iff_of_mem {N j a : ℕ} {os : List ℕ}
    (hNC : IsNoncrossingPartialMatching N M) (h5 : (a :: os).Pairwise (· > ·))
    (h5' : ∀ x, x ∈ a :: os ↔ ∃ b, (x, b) ∈ M ∧ x < j ∧ j ≤ b) (ha : (a, j) ∈ M)
    (hLE : j ∉ M.leftEndpoints) (x : ℕ) :
    x ∈ os ↔ ∃ b, (x, b) ∈ M ∧ x < j + 1 ∧ j + 1 ≤ b := by
  constructor
  · intro hx
    have hxa : a > x := List.rel_of_pairwise_cons h5 hx
    obtain ⟨b', hb', hxj, hjb'⟩ := (h5' x).1 (by simp [hx])
    refine ⟨b', hb', by omega, ?_⟩
    rcases eq_or_lt_of_le hjb' with he | h'
    · rw [← he] at hb'
      have := hNC.eq_of_mem_of_mem _ hb' _ ha j (Or.inr rfl) (Or.inr rfl)
      simp at this
      omega
    · omega
  · rintro ⟨b', hb', hx, hb''⟩
    have hxj : x ≠ j := by
      rintro rfl
      exact hLE (Finset.mem_image_of_mem Prod.fst hb')
    have hxo := (h5' x).2 ⟨b', hb', by omega, by omega⟩
    rcases List.mem_cons.1 hxo with rfl | hxo
    · have := hNC.eq_of_mem_of_mem _ hb' _ ha x (Or.inl rfl) (Or.inl rfl)
      simp at this
      omega
    · exact hxo

private theorem inv_step_of_mem_image_snd (hnd : π.Nodup) (hM : M ∈ π.fiberMatchings)
    {j : ℕ} (hj1 : 1 ≤ j) (hj : j < π.length) {S : List (BinaryTree ℕ)} {os : List ℕ}
    (h : Inv π M C j S os) (hLE : j ∉ M.leftEndpoints) (hR : j ∈ M.image Prod.snd) :
    ∃ os', Inv π M C (j + 1) (step S (code π M C j)) os' := by
  have hprev := getD_pred_lt_getD hnd hM hj1 hj hLE
  obtain ⟨hNC, -, hlt⟩ := hM
  obtain ⟨h1, h6, h3, h4, h5, h5'⟩ := h
  have hnodup := flatMap_postorder_eq h6 ▸ nodup_map_range_getD hnd hj.le
  obtain ⟨hl, hr⟩ := (mem_image_snd_iff (N := π.length - 1) (C := C)).1 hR
  have hc : code π M C j = (π.getD j 0, true, true) := by simp [code, hl, hr]
  obtain ⟨a, ha⟩ := exists_of_mem_image_snd hR
  have haj := hNC.fst_lt_snd _ ha
  dsimp at haj
  obtain ⟨os'', rfl⟩ :=
    exists_eq_cons_of_mem hNC h5 h5' ha ((h5' a).2 ⟨j, ha, haj, le_rfl⟩)
  obtain ⟨top, u, rest, rfl⟩ : ∃ top u rest, S = top :: u :: rest := by
    match S, h1 with
    | top :: u :: rest, _ => exact ⟨top, u, rest, rfl⟩
  simp only [List.map_cons, List.cons.injEq] at h4
  obtain ⟨hrtop, hru, hrest⟩ := h4
  have htop := h3 top (by simp)
  have hu := h3 u (by simp)
  obtain ⟨ha1, hab, hlt'⟩ := hlt _ ha
  dsimp only at ha1 hab hlt'
  have hun : rootLabel u < π.getD j 0 := by
    rw [hru, List.getD_eq_getElem _ _ ha1, List.getD_eq_getElem _ _ hab]
    exact hlt'
  have htn : rootLabel top < π.getD j 0 := hrtop ▸ hprev
  have hdisj : Disjoint u.labels top.labels := by
    rw [labels_eq_toFinset, labels_eq_toFinset, List.disjoint_toFinset_iff_disjoint]
    have : (top :: u :: rest).reverse.flatMap postorder =
        rest.reverse.flatMap postorder ++ (u.postorder ++ top.postorder) := by simp
    rw [this] at hnodup
    exact List.disjoint_of_nodup_append (List.Nodup.of_append_right hnodup)
  rw [hc]
  refine ⟨os'', ?_, ?_, ?_, ?_, h5.of_cons, mem_tail_iff_of_mem hNC h5 h5' ha hLE⟩
  · simp only [step, List.length_cons] at h1 ⊢
    omega
  · simp only [step, List.range_succ, List.map_append, ← h6, List.reverse_cons,
      List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, kinds,
      List.append_assoc, List.map_cons, List.map_nil, hc]
    rw [(isNode_eq_true_iff).2 hu.2, (isNode_eq_true_iff).2 htop.2]
  · simp only [step, List.mem_cons, forall_eq_or_imp]
    refine ⟨⟨⟨hu.1, htop.1, hdisj, ?_⟩, by simp⟩, fun t ht => h3 t (by simp [ht])⟩
    intro x hx
    rcases Finset.mem_union.1 hx with hx | hx
    · exact forall_lt_of_rootLabel_lt hu.1 hun x hx
    · exact forall_lt_of_rootLabel_lt htop.1 htn x hx
  · simp [step, rootLabel, hrest]

private theorem mem_iff_succ_of_unmatched {j : ℕ} {os : List ℕ}
    (h5' : ∀ x, x ∈ os ↔ ∃ b, (x, b) ∈ M ∧ x < j ∧ j ≤ b) (hLE : j ∉ M.leftEndpoints)
    (hR : j ∉ M.image Prod.snd) (x : ℕ) :
    x ∈ os ↔ ∃ b, (x, b) ∈ M ∧ x < j + 1 ∧ j + 1 ≤ b := by
  rw [h5']
  constructor
  · rintro ⟨b', hb', hx, hb''⟩
    refine ⟨b', hb', by omega, ?_⟩
    rcases eq_or_lt_of_le hb'' with rfl | h'
    · exact absurd (Finset.mem_image_of_mem Prod.snd hb') hR
    · omega
  · rintro ⟨b', hb', hx, hb''⟩
    have hxj : x ≠ j := by
      rintro rfl
      exact hLE (Finset.mem_image_of_mem Prod.fst hb')
    exact ⟨b', hb', by omega, by omega⟩

private theorem inv_step_of_unmatched (hnd : π.Nodup) (hM : M ∈ π.fiberMatchings) {j : ℕ}
    (hj1 : 1 ≤ j) (hj : j < π.length) {S : List (BinaryTree ℕ)} {os : List ℕ}
    (h : Inv π M C j S os) (hLE : j ∉ M.leftEndpoints) (hR : j ∉ M.image Prod.snd) :
    ∃ os', Inv π M C (j + 1) (step S (code π M C j)) os' := by
  have hprev := getD_pred_lt_getD hnd hM hj1 hj hLE
  obtain ⟨h1, h6, h3, h4, h5, h5'⟩ := h
  have hU : j ∈ Finset.unmatchedVertices (π.length - 1) M := by
    simp only [Finset.unmatchedVertices, Finset.mem_sdiff, Finset.mem_union, Finset.mem_Icc]
    exact ⟨⟨hj1, by omega⟩, by tauto⟩
  obtain ⟨top, rest, rfl⟩ : ∃ top rest, S = top :: rest := by
    match S, h1 with
    | top :: rest, _ => exact ⟨top, rest, rfl⟩
  simp only [List.map_cons, List.cons.injEq] at h4
  obtain ⟨hrtop, hrest⟩ := h4
  have htop := h3 top (by simp)
  have htn : rootLabel top < π.getD j 0 := hrtop ▸ hprev
  have hos := mem_iff_succ_of_unmatched h5' hLE hR
  have hlab : ∀ x ∈ top.labels ∪ (nil : BinaryTree ℕ).labels, x < π.getD j 0 := by
    intro x hx
    simp only [labels, Finset.union_empty] at hx
    exact forall_lt_of_rootLabel_lt htop.1 htn x hx
  have hlab' : ∀ x ∈ (nil : BinaryTree ℕ).labels ∪ top.labels, x < π.getD j 0 := by
    rw [Finset.union_comm]
    exact hlab
  by_cases hjC : j ∈ C
  · have hc : code π M C j = (π.getD j 0, false, true) := by
      simp [code, hasLeft, hasRight, hjC, hR]
    rw [hc]
    refine ⟨os, ?_, ?_, ?_, ?_, h5, hos⟩
    · simpa [step] using h1
    · simp only [step, List.range_succ, List.map_append, ← h6, List.reverse_cons,
        List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, kinds,
        List.append_assoc, List.map_cons, List.map_nil, hc]
      rw [(isNode_eq_true_iff).2 htop.2]
      rfl
    · simp only [step, List.mem_cons, forall_eq_or_imp]
      exact ⟨⟨⟨trivial, htop.1, by simp, hlab'⟩, by simp⟩, fun t ht => h3 t (by simp [ht])⟩
    · simp [step, rootLabel, hrest]
  · have hc : code π M C j = (π.getD j 0, true, false) := by
      simp [code, hasLeft, hasRight, hjC, hR, hU]
    rw [hc]
    refine ⟨os, ?_, ?_, ?_, ?_, h5, hos⟩
    · simpa [step] using h1
    · simp only [step, List.range_succ, List.map_append, ← h6, List.reverse_cons,
        List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, kinds,
        List.append_assoc, List.map_cons, List.map_nil, hc]
      rw [(isNode_eq_true_iff).2 htop.2]
      rfl
    · simp only [step, List.mem_cons, forall_eq_or_imp]
      exact ⟨⟨⟨htop.1, trivial, by simp, hlab⟩, by simp⟩, fun t ht => h3 t (by simp [ht])⟩
    · simp [step, rootLabel, hrest]

private theorem inv_step (hnd : π.Nodup) (hM : M ∈ π.fiberMatchings)
    (hC : C ⊆ Finset.unmatchedVertices (π.length - 1) M) {j : ℕ} (hj1 : 1 ≤ j)
    (hj : j < π.length) {S : List (BinaryTree ℕ)} {os : List ℕ} (h : Inv π M C j S os) :
    ∃ os', Inv π M C (j + 1) (step S (code π M C j)) os' := by
  by_cases hLE : j ∈ M.leftEndpoints
  · exact inv_step_of_mem_leftEndpoints hM hC h hLE
  by_cases hR : j ∈ M.image Prod.snd
  · exact inv_step_of_mem_image_snd hnd hM hj1 hj h hLE hR
  · exact inv_step_of_unmatched hnd hM hj1 hj h hLE hR

private theorem inv_foldl (hnd : π.Nodup) (hM : M ∈ π.fiberMatchings)
    (hC : C ⊆ Finset.unmatchedVertices (π.length - 1) M) :
    ∀ j, 1 ≤ j → j ≤ π.length →
      ∃ os, Inv π M C j (((List.range j).map (code π M C)).foldl step []) os
  | 0, h, _ => absurd h (by omega)
  | 1, _, _ => by
    have h := inv_one hM hC
    have h0 : code π M C 0 = (π.getD 0 0, false, false) := by
      have := h.2.1
      simpa [kinds, isNode] using this.symm
    exact ⟨[], by simpa [h0, step] using h⟩
  | j + 2, _, hj => by
    obtain ⟨os, hos⟩ := inv_foldl hnd hM hC (j + 1) (by omega) (by omega)
    rw [List.range_succ, List.map_append, List.foldl_append]
    exact inv_step hnd hM hC (by omega) (by omega) hos

/-- The construction: for `M ∈ 𝒜(π)` and `C ⊆ U(M)` there is a decreasing tree on `[n]` with
postorder reading `π` whose annotated postorder reading is the one read off `M` and `C`. -/
private theorem exists_tree {n : ℕ} (hn : 1 ≤ n) (hπS : π ∈ permWords n)
    (hM : M ∈ π.fiberMatchings) (hC : C ⊆ Finset.unmatchedVertices (π.length - 1) M) :
    ∃ T : BinaryTree ℕ, T ∈ decreasingTrees (Finset.Icc 1 n) ∧ T.postorder = π ∧
      kinds T = (List.range n).map (code π M C) := by
  have hlen : π.length = n := hπS.2.1
  obtain ⟨os, h1, h6, h3, -, -, h5'⟩ := inv_foldl hπS.1.1 hM hC π.length (by omega) le_rfl
  have hos : os = [] := by
    cases os with
    | nil => rfl
    | cons x os =>
      obtain ⟨b, hb, -, hnb⟩ := (h5' x).1 (by simp)
      have := hM.1.snd_le _ hb; dsimp at this; omega
  subst hos
  set S := ((List.range π.length).map (code π M C)).foldl step [] with hS
  obtain ⟨T, hT⟩ : ∃ T, S = [T] := by
    match S, h1 with
    | [T], _ => exact ⟨T, rfl⟩
  rw [hT] at h6 h3
  simp only [List.reverse_singleton, List.flatMap_singleton] at h6
  have hpo : T.postorder = π := by
    rw [postorder_eq_map_kinds, h6, List.map_map]
    apply List.ext_getElem (by simp)
    intro i h1 h2
    simp [code, List.getElem?_eq_getElem h2]
  refine ⟨T, ⟨(h3 T (by simp)).1, ?_⟩, hpo, hlen ▸ h6⟩
  rw [labels_eq_toFinset, hpo, ← hπS.2.2]

end construction

end Proof_lem_matching_tree_bijection

namespace BinaryTree

open Proof_lem_matching_tree_bijection in
/-- **Matchings with choices and trees with fixed postorder.** Let `n ≥ 1` and `π ∈ S_n`. The map
`T ↦ (M(T), C(T))` is a bijection from `{T ∈ DBT([n]) : 𝒫(T) = π}` onto the set of pairs
`(M, C)` with `M ∈ 𝒜(π)` and `C ⊆ U(M)`, the unmatched vertices of `M` in `[n - 1]`. -/
@[lognarayana "lem_matching_tree_bijection"]
public theorem bijOn_treeMatching_treeRightChoices {n : ℕ} (hn : 1 ≤ n) {π : List ℕ}
    (hπS : π ∈ permWords n) :
    Set.BijOn (fun T : BinaryTree ℕ => (T.treeMatching, T.treeRightChoices))
      {T | T ∈ decreasingTrees (Finset.Icc 1 n) ∧ T.postorder = π}
      {p : Finset (ℕ × ℕ) × Finset ℕ |
        p.1 ∈ π.fiberMatchings ∧ p.2 ⊆ Finset.unmatchedVertices (n - 1) p.1} := by
  have hlen : π.length = n := hπS.2.1
  refine ⟨?_, ?_, ?_⟩
  · rintro T ⟨hT, rfl⟩
    exact ⟨treeMatching_mem_fiberMatchings hn hπS hT rfl, hlen ▸ treeRightChoices_subset _⟩
  · rintro T₁ ⟨hT₁, rfl⟩ T₂ ⟨hT₂, hπ₂⟩ h
    simp only [Prod.mk.injEq] at h
    have hne : ∀ T : BinaryTree ℕ, T.postorder.length = n → T ≠ nil := by
      rintro T hT rfl; simp at hT; omega
    apply kinds_injective (hne T₁ hlen) (hne T₂ (hπ₂ ▸ hlen))
    rw [kinds_eq_map_code hn hπS hT₁, kinds_eq_map_code hn (hπ₂ ▸ hπS) hT₂, hπ₂, h.1, h.2]
  · rintro ⟨M, C⟩ ⟨hM, hC⟩
    dsimp only at hM hC
    rw [← hlen] at hC
    obtain ⟨T, hT, hpo, hk⟩ := exists_tree hn hπS hM hC
    refine ⟨T, ⟨hT, hpo⟩, ?_⟩
    have hk' := kinds_eq_map_code hn (hpo ▸ hπS) hT
    rw [hk, hpo, List.map_inj_left] at hk'
    have hMT := treeMatching_mem_fiberMatchings hn hπS hT hpo
    obtain ⟨h1, h2⟩ := eq_of_hasLeft_hasRight hMT.1 (hpo ▸ treeRightChoices_subset T) hM.1 hC
      fun j hj => by
        have := hk' j (List.mem_range.2 (by omega))
        simp only [code, Prod.mk.injEq] at this
        exact ⟨this.2.1.symm, this.2.2.symm⟩
    simp only [h1, h2]

end BinaryTree

end

/-!
## Subtrees of a binary tree

A subtree of `T` is a tree related to `T` by the reflexive-transitive closure of "is the left or
right subtree of the root of". In a decreasing tree a subtree is determined by its root label,
and a label lies in `RC(T)` (resp. `LC(T)`) exactly when it is the root of a subtree with a
nonempty right (resp. left) subtree.
-/

namespace BinaryTree

variable {α : Type*}

/-- `S` is a subtree of `U`: the reflexive-transitive closure of "is a child subtree of". -/
private abbrev IsSubtree (S U : BinaryTree α) : Prop :=
  Relation.ReflTransGen (fun S U : BinaryTree α => ∃ m L R, U = node m L R ∧ (S = L ∨ S = R)) S U

private lemma isSubtree_nil_iff {S : BinaryTree α} : IsSubtree S nil ↔ S = nil := by
  refine ⟨fun h => ?_, fun h => h ▸ .refl⟩
  rcases (Relation.ReflTransGen.cases_tail_iff _ _ _).1 h with h | ⟨c, -, m, L, R, h, -⟩
  · exact h.symm
  · cases h

private lemma isSubtree_node_iff {S l r : BinaryTree α} {m : α} :
    IsSubtree S (node m l r) ↔ S = node m l r ∨ IsSubtree S l ∨ IsSubtree S r := by
  constructor
  · intro h
    rcases (Relation.ReflTransGen.cases_tail_iff _ _ _).1 h with h | ⟨c, hc, m', L, R, h, hcLR⟩
    · exact Or.inl h.symm
    · cases h
      rcases hcLR with rfl | rfl
      · exact Or.inr (Or.inl hc)
      · exact Or.inr (Or.inr hc)
  · rintro (rfl | h | h)
    · exact Relation.ReflTransGen.refl
    · exact h.tail ⟨m, l, r, rfl, Or.inl rfl⟩
    · exact h.tail ⟨m, l, r, rfl, Or.inr rfl⟩

variable [DecidableEq α]

private lemma mem_labels_of_isSubtree {m : α} {A B T : BinaryTree α}
    (h : IsSubtree (node m A B) T) : m ∈ T.labels := by
  induction T with
  | nil => cases isSubtree_nil_iff.1 h
  | node m' l r ihl ihr =>
    rcases isSubtree_node_iff.1 h with h | h | h
    · cases h; simp [labels]
    · simp [labels, ihl h]
    · simp [labels, ihr h]

/-- In a decreasing tree, a subtree is determined by the label of its root. -/
private lemma eq_of_isSubtree_of_isDecreasing [Preorder α] {m : α} {A B C D T : BinaryTree α}
    (hT : T.IsDecreasing) (h₁ : IsSubtree (node m A B) T) (h₂ : IsSubtree (node m C D) T) :
    node m A B = node m C D := by
  induction T with
  | nil => cases isSubtree_nil_iff.1 h₁
  | node m' l r ihl ihr =>
    obtain ⟨hl, hr, hdisj, hlt⟩ := hT
    have irrefl {X Y : BinaryTree α} (h : IsSubtree (node m X Y) l ∨ IsSubtree (node m X Y) r)
        (e : m = m') : False := by
      subst e
      exact lt_irrefl m <| hlt m <| by
        rcases h with h | h <;> simp [mem_labels_of_isSubtree h]
    have disj {X Y U V : BinaryTree α} (h : IsSubtree (node m X Y) l)
        (h' : IsSubtree (node m U V) r) : False :=
      Finset.disjoint_left.1 hdisj (mem_labels_of_isSubtree h) (mem_labels_of_isSubtree h')
    rcases isSubtree_node_iff.1 h₁ with e₁ | e₁ | e₁ <;>
      rcases isSubtree_node_iff.1 h₂ with e₂ | e₂ | e₂
    · rw [e₁, e₂]
    all_goals first
      | exact ihl hl e₁ e₂
      | exact ihr hr e₁ e₂
      | exact (disj e₁ e₂).elim
      | exact (disj e₂ e₁).elim
      | exact (irrefl (.inl e₂) (node.inj e₁).1).elim
      | exact (irrefl (.inr e₂) (node.inj e₁).1).elim
      | exact (irrefl (.inl e₁) (node.inj e₂).1).elim
      | exact (irrefl (.inr e₁) (node.inj e₂).1).elim

/-- A label lies in `RC(T)` exactly when it is the root of a subtree with nonempty right
subtree. -/
private lemma mem_rightChildLabels_iff {m : α} {T : BinaryTree α} :
    m ∈ T.rightChildLabels ↔ ∃ L d R₁ R₂, IsSubtree (node m L (node d R₁ R₂)) T := by
  induction T with
  | nil => simp [isSubtree_nil_iff]
  | node m' l r ihl ihr =>
    cases r with
    | nil => simp [isSubtree_node_iff, isSubtree_nil_iff, ihl]
    | node d R₁ R₂ =>
      simp only [rightChildLabels, Finset.mem_union, Finset.mem_singleton] at ihr ⊢
      simp only [ihl, ihr, isSubtree_node_iff, exists_or, node.injEq]
      simp only [exists_and_left, exists_eq_left, exists_eq, and_true]
      exact or_comm

/-- A label lies in `LC(T)` exactly when it is the root of a subtree with nonempty left
subtree. -/
private lemma mem_leftChildLabels_iff {m : α} {T : BinaryTree α} :
    m ∈ T.leftChildLabels ↔ ∃ c L₁ L₂ R, IsSubtree (node m (node c L₁ L₂) R) T := by
  induction T with
  | nil => simp [isSubtree_nil_iff]
  | node m' l r ihl ihr =>
    cases l with
    | nil => simp [isSubtree_node_iff, isSubtree_nil_iff, ihr]
    | node c L₁ L₂ =>
      simp only [leftChildLabels, Finset.mem_union, Finset.mem_singleton] at ihl ⊢
      simp only [ihl, ihr, isSubtree_node_iff, exists_or, node.injEq]
      simp only [exists_and_left, exists_eq, and_true]
      exact or_comm

end BinaryTree

/-!
## Right children in the matching encoding

Let `T` be a decreasing binary plane tree on `[n]` with postorder reading `𝒫(T) = π ∈ S_n`,
and let `j ∈ [n - 1]`. The vertex labelled `π_{j+1}` has a right child exactly when `j` is a
right endpoint of a pair of the matching `M(T)` or `j` lies in the set `C(T)` of right choices.

Labels are in `ℕ`, `S_n` is `permWords n` and `[n]` is `Finset.Icc 1 n`. Positions are
`1`-based, so `π_{j+1} = π[j]`; the index bound `j < |π|` is carried inside the left-hand side,
as in `BinaryTree.treeRightChoices`. The set of right endpoints `R(M)` of a set of pairs `M` is
its image `M.image Prod.snd` under the second projection.
-/

section

open BinaryTree

variable {α : Type*}
variable [DecidableEq α]

namespace Proof_lem_tree_matching_right_child

/-- In a decreasing tree, the label of a leaf is not the label of a vertex with a right
child. -/
private lemma not_mem_rightChildLabels_of_isSubtree_leaf [Preorder α] {m : α}
    {T : BinaryTree α} (hT : T.IsDecreasing) (h : IsSubtree (node m nil nil) T) :
    m ∉ T.rightChildLabels := fun hm => by
  obtain ⟨L, d, R₁, R₂, h'⟩ := mem_rightChildLabels_iff.1 hm
  cases eq_of_isSubtree_of_isDecreasing hT h h'

end Proof_lem_tree_matching_right_child

namespace BinaryTree

open Proof_lem_tree_matching_right_child in
/-- **Right children in the matching encoding.** Let `π ∈ S_n`, `T ∈ DBT([n])` with `𝒫(T) = π`, and
`j ∈ [n - 1]`. Then `π_{j+1} ∈ RC(T)` if and only if `j ∈ R(M(T)) ∪ C(T)`. -/
@[lognarayana "lem_tree_matching_right_child"]
public theorem mem_rightChildLabels_iff_mem_treeMatching_or_treeRightChoices {n : ℕ}
    {π : List ℕ} (hπS : π ∈ permWords n) {T : BinaryTree ℕ}
    (hT : T ∈ decreasingTrees (Finset.Icc 1 n)) (hπ : T.postorder = π) {j : ℕ}
    (hj : j ∈ Finset.Icc 1 (n - 1)) :
    (∃ h : j < π.length, π[j] ∈ T.rightChildLabels) ↔
      j ∈ T.treeMatching.image Prod.snd ∪ T.treeRightChoices := by
  classical
  subst hπ
  rw [Finset.mem_union]
  refine ⟨fun hRC => or_iff_not_imp_left.2 fun hR => ?_, ?_⟩
  · -- `j` is not a left endpoint, since `π_{j+1}` would then be a leaf.
    have hL : j ∉ T.treeMatching.leftEndpoints := by
      rintro hL
      obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.1 hL
      obtain ⟨h, hleaf⟩ := isLeaf_postorder_getElem_of_mem_treeMatching hπS rfl hab
      exact not_mem_rightChildLabels_of_isSubtree_leaf hT.1 hleaf hRC.2
    refine Finset.mem_filter.2 ⟨?_, hRC⟩
    rw [Finset.unmatchedVertices, Finset.mem_sdiff, Finset.mem_union, hπS.2.1]
    exact ⟨hj, by tauto⟩
  · rintro (hR | hC)
    · obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.1 hR
      obtain ⟨-, ⟨ha, hb, L₁, L₂, d, R₁, R₂, hsub⟩⟩ := Finset.mem_filter.1 hab
      exact ⟨hb, mem_rightChildLabels_iff.2 ⟨_, d, R₁, R₂, hsub⟩⟩
    · exact (Finset.mem_filter.1 hC).2

end BinaryTree

end

/-!
## Counting right children through the matching encoding

Let `T` be a decreasing binary plane tree on `[n]` with postorder reading `𝒫(T) = π ∈ S_n`.
The number of vertices of `T` having a right child equals the number of pairs of the matching
`M(T)` plus the number of right choices `C(T)`: `|RC(T)| = |M(T)| + |C(T)|`.

Labels are in `ℕ`, `S_n` is `permWords n` and `[n]` is `Finset.Icc 1 n`, as in
`BinaryTree.mem_rightChildLabels_iff_mem_treeMatching_or_treeRightChoices`.
-/

section

open BinaryTree

namespace Proof_lem_matching_tree_right_count

private lemma mem_rightChildLabels_node_iff {α : Type*} [DecidableEq α] {x m : α}
    {l r : BinaryTree α} : x ∈ (node m l r).rightChildLabels ↔
      x ∈ l.rightChildLabels ∨ x ∈ r.rightChildLabels ∨ (x = m ∧ r ≠ nil) := by
  cases r <;> simp
  tauto

/-- A vertex with a right child is the root of a subtree `node m L (node d R₁ R₂)`. -/
private lemma exists_isSubtree_of_mem_rightChildLabels {α : Type*} [DecidableEq α] :
    ∀ {T : BinaryTree α} {m : α}, m ∈ T.rightChildLabels →
      ∃ (L : BinaryTree α) (d : α) (R₁ R₂ : BinaryTree α),
        Relation.ReflTransGen (fun S U : BinaryTree α => ∃ b L R, U = node b L R ∧ (S = L ∨ S = R))
          (node m L (node d R₁ R₂)) T
  | nil, _, h => by simp at h
  | node a l r, m, h => by
    rcases mem_rightChildLabels_node_iff.1 h with h | h | ⟨rfl, hr⟩
    · obtain ⟨L, d, R₁, R₂, hS⟩ := exists_isSubtree_of_mem_rightChildLabels h
      exact ⟨L, d, R₁, R₂, hS.tail ⟨a, l, r, rfl, .inl rfl⟩⟩
    · obtain ⟨L, d, R₁, R₂, hS⟩ := exists_isSubtree_of_mem_rightChildLabels h
      exact ⟨L, d, R₁, R₂, hS.tail ⟨a, l, r, rfl, .inr rfl⟩⟩
    · obtain _ | ⟨d, R₁, R₂⟩ := r
      · exact absurd rfl hr
      · exact ⟨l, d, R₁, R₂, .refl⟩

/-- Every vertex with a right child is a vertex: `RC(T) ⊆ Lab(T)`. -/
private lemma rightChildLabels_subset_labels {α : Type*} [DecidableEq α] :
    ∀ T : BinaryTree α, T.rightChildLabels ⊆ T.labels
  | nil => by simp
  | node a l r => fun x hx => by
    have := @rightChildLabels_subset_labels _ _ l x
    have := @rightChildLabels_subset_labels _ _ r x
    rw [mem_rightChildLabels_node_iff] at hx
    simp only [labels, Finset.mem_union, Finset.mem_singleton]
    tauto

/-- Every index in `R(M(T)) ∪ C(T)` lies in `[n - 1]`. -/
private lemma mem_Icc_of_mem_union {n : ℕ} {π : List ℕ} (hlen : π.length = n)
    {T : BinaryTree ℕ} (hπ : T.postorder = π) {j : ℕ}
    (hj : j ∈ T.treeMatching.image Prod.snd ∪ T.treeRightChoices) :
    j ∈ Finset.Icc 1 (n - 1) := by
  classical
  rcases Finset.mem_union.1 hj with h | h
  · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 h
    have := (Finset.mem_filter.1 hp).1
    rw [Finset.mem_product, hπ, hlen] at this
    exact this.2
  · simpa [hπ, hlen] using (Finset.mem_sdiff.1 (Finset.mem_filter.1 h).1).1

/-- **The right children through the matching encoding.** `RC(T)` is the image of
`R(M(T)) ∪ C(T)` under `j ↦ π[j]`. -/
private lemma rightChildLabels_eq_image {n : ℕ} (hn : 1 ≤ n) {π : List ℕ}
    (hπS : π ∈ permWords n) {T : BinaryTree ℕ} (hT : T ∈ decreasingTrees (Finset.Icc 1 n))
    (hπ : T.postorder = π) :
    T.rightChildLabels =
      (T.treeMatching.image Prod.snd ∪ T.treeRightChoices).image (π.getD · 0) := by
  ext x
  constructor
  · intro hx
    have hxl : x ∈ π := by
      have := rightChildLabels_subset_labels T hx
      rw [hT.2, ← hπS.2.2] at this
      simpa using this
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hxl
    obtain rfl | hipos := Nat.eq_zero_or_pos i
    · obtain ⟨L, d, R₁, R₂, hS⟩ := exists_isSubtree_of_mem_rightChildLabels hx
      have := (postorder_getElem?_pred_eq_last_child hT (j := 1) le_rfl
        (by simp [hπ]) hS (Or.inr (by simp))).1
      omega
    · have hj : i ∈ Finset.Icc 1 (n - 1) := by grind [permWords]
      exact Finset.mem_image.2 ⟨i,
        (mem_rightChildLabels_iff_mem_treeMatching_or_treeRightChoices hπS hT hπ hj).1 ⟨hi, hx⟩,
        by simp [hi]⟩
  · intro hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨hjl, hm⟩ := (mem_rightChildLabels_iff_mem_treeMatching_or_treeRightChoices
      hπS hT hπ (mem_Icc_of_mem_union hπS.2.1 hπ hj)).2 hj
    simpa [hjl] using hm

end Proof_lem_matching_tree_right_count

namespace BinaryTree

open Proof_lem_matching_tree_right_count in
/-- **Counting right children.** Let `n ≥ 1`, `π ∈ S_n` and `T ∈ DBT([n])` with `𝒫(T) = π`.
Then `|RC(T)| = |M(T)| + |C(T)|`. -/
@[lognarayana "lem_matching_tree_right_count"]
public theorem card_rightChildLabels_eq_card_treeMatching_add_card_treeRightChoices {n : ℕ}
    (hn : 1 ≤ n) {π : List ℕ} (hπS : π ∈ permWords n) {T : BinaryTree ℕ}
    (hT : T ∈ decreasingTrees (Finset.Icc 1 n)) (hπ : T.postorder = π) :
    T.rightChildLabels.card = T.treeMatching.card + T.treeRightChoices.card := by
  classical
  have hinj : Set.InjOn (π.getD · 0) ↑(T.treeMatching.image Prod.snd ∪ T.treeRightChoices) := by
    intro i hi j hj hij
    have hi' := Finset.mem_Icc.1 (mem_Icc_of_mem_union hπS.2.1 hπ hi)
    have hj' := Finset.mem_Icc.1 (mem_Icc_of_mem_union hπS.2.1 hπ hj)
    have hlen := hπS.2.1
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i < π.length by omega),
      List.getElem?_eq_getElem (show j < π.length by omega), Option.getD_some] at hij
    exact (nodup_of_mem_permWords hπS).getElem_inj_iff.1 hij
  have hdisj : Disjoint (T.treeMatching.image Prod.snd) T.treeRightChoices :=
    Finset.disjoint_left.2 fun j hjR hjC => by
      have := (Finset.mem_filter.1 hjC).1
      simp only [Finset.unmatchedVertices, Finset.mem_sdiff, Finset.mem_union] at this
      exact this.2 (Or.inr hjR)
  have hM := (treeMatching_mem_fiberMatchings hn hπS hT hπ).1
  rw [rightChildLabels_eq_image hn hπS hT hπ, Finset.card_image_of_injOn hinj,
    Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injOn fun p hp q hq hpq =>
      hM.eq_of_mem_of_mem p hp q hq p.2 (Or.inr rfl) (Or.inr hpq)]

end BinaryTree

end

/-!
## Descents of the inorder reading through the matching encoding

Let `T` be a decreasing binary plane tree on `[n]` with postorder reading `𝒫(T) = π ∈ S_n`.
The number of descents of the inorder reading `ℐ(T)` equals the number of pairs of the matching
`M(T)` plus the number of right choices `C(T)`: `des(ℐ(T)) = |M(T)| + |C(T)|`.

Labels are in `ℕ`, `S_n` is `permWords n` and `[n]` is `Finset.Icc 1 n`, as in
`BinaryTree.card_rightChildLabels_eq_card_treeMatching_add_card_treeRightChoices`.
-/

section

open List

namespace BinaryTree

/-- **Descents of the inorder reading.** Let `n ≥ 1`, `π ∈ S_n` and `T ∈ DBT([n])` with
`𝒫(T) = π`. Then `des(ℐ(T)) = |M(T)| + |C(T)|`. -/
@[lognarayana "lem_matching_tree_descents"]
public theorem numDescents_inorder_eq_card_treeMatching_add_card_treeRightChoices {n : ℕ}
    (hn : 1 ≤ n) {π : List ℕ} (hπS : π ∈ permWords n) {T : BinaryTree ℕ}
    (hT : T ∈ decreasingTrees (Finset.Icc 1 n)) (hπ : T.postorder = π) :
    T.inorder.numDescents = T.treeMatching.card + T.treeRightChoices.card := by
  have hnd : T.inorder.Nodup :=
    (isWord_inorder_of_mem_decreasingTrees
      (fun a ha => (Finset.mem_Icc.1 ha).1) hT).1.1
  rw [← card_descentTops hnd, descentTops_inorder_of_mem_decreasingTrees hT,
    card_rightChildLabels_eq_card_treeMatching_add_card_treeRightChoices hn hπS hT hπ]

end BinaryTree

end

/-!
## Left children in the matching encoding

Let `T` be a decreasing binary plane tree on `[n]` with postorder reading `𝒫(T) = π ∈ S_n`,
and let `j ∈ [n - 1]`. The vertex labelled `π_{j+1}` has a left child exactly when `j` is a
right endpoint of a pair of the matching `M(T)`, or `j` is an unmatched vertex of `M(T)` that
does not lie in the set `C(T)` of right choices.

Labels are in `ℕ`, `S_n` is `permWords n` and `[n]` is `Finset.Icc 1 n`. Positions are
`1`-based, so `π_{j+1} = π[j]`; the index bound `j < |π|` is carried inside the left-hand side,
as in `BinaryTree.treeRightChoices`. The set of right endpoints `R(M)` of a set of pairs `M` is
its image `M.image Prod.snd`, and the unmatched vertices `U(M(T))` are taken in `[n - 1]`, as in
`BinaryTree.treeRightChoices`.
-/

section

open BinaryTree

variable {α : Type*}
variable [DecidableEq α]

namespace Proof_lem_tree_matching_left_child

private lemma mem_postorder_iff {a : α} {T : BinaryTree α} : a ∈ T.postorder ↔ a ∈ T.labels := by
  induction T with
  | nil => simp [postorder, labels]
  | node m l r ihl ihr => simp [postorder, labels, ihl, ihr]; tauto

/-- In a decreasing tree, if the postorder letter `π_{j+1}` (with `j ≥ 1`) has both a left and a
right child, then `j` is a right endpoint of `M(T)`: it is matched with the position of its left
child. -/
private lemma mem_image_snd_treeMatching [Preorder α] {T : BinaryTree α} (hT : T.IsDecreasing)
    {j : ℕ} (hj : 1 ≤ j) (h : j < T.postorder.length) (hLC : T.postorder[j] ∈ T.leftChildLabels)
    (hRC : T.postorder[j] ∈ T.rightChildLabels) : j ∈ T.treeMatching.image Prod.snd := by
  classical
  obtain ⟨c, L₁, L₂, R, hsub⟩ := mem_leftChildLabels_iff.1 hLC
  obtain ⟨L, d, R₁, R₂, hsub'⟩ := mem_rightChildLabels_iff.1 hRC
  cases eq_of_isSubtree_of_isDecreasing hT hsub hsub'
  obtain ⟨i, hi, hc⟩ := List.getElem_of_mem <| mem_postorder_iff.2 <|
    mem_labels_of_isSubtree (.head ⟨_, _, _, rfl, .inl rfl⟩ hsub)
  refine Finset.mem_image.2 ⟨(i + 1, j), Finset.mem_filter.2 ⟨?_, by simpa using hi, h,
    L₁, L₂, d, R₁, R₂, by simpa [hc] using hsub⟩, rfl⟩
  simp only [Finset.mem_product, Finset.mem_Icc]; omega

end Proof_lem_tree_matching_left_child

namespace BinaryTree

open Proof_lem_tree_matching_left_child in
/-- **Left children in the matching encoding.** Let `n ≥ 1`, `π ∈ S_n`, `T ∈ DBT([n])` with
`𝒫(T) = π`, and `j ∈ [n - 1]`. Then `π_{j+1} ∈ LC(T)` if and only if
`j ∈ R(M(T)) ∪ (U(M(T)) \ C(T))`. -/
@[lognarayana "lem_tree_matching_left_child"]
public theorem mem_leftChildLabels_iff_mem_treeMatching_or_unmatchedVertices_sdiff {n : ℕ}
    (hn : 1 ≤ n) {π : List ℕ} (hπS : π ∈ permWords n) {T : BinaryTree ℕ}
    (hT : T ∈ decreasingTrees (Finset.Icc 1 n)) (hπ : T.postorder = π) {j : ℕ}
    (hj : j ∈ Finset.Icc 1 (n - 1)) :
    (∃ h : j < π.length, π[j] ∈ T.leftChildLabels) ↔
      j ∈ T.treeMatching.image Prod.snd ∪
        (Finset.unmatchedVertices (n - 1) T.treeMatching \ T.treeRightChoices) := by
  classical
  subst hπ
  have hlen : T.postorder.length = n := hπS.2.1
  have hj' := Finset.mem_Icc.1 hj
  rw [Finset.mem_union, Finset.mem_sdiff, Finset.unmatchedVertices, Finset.mem_sdiff,
    Finset.mem_union]
  refine ⟨fun ⟨h, hLC⟩ => or_iff_not_imp_left.2 fun hR => ?_, ?_⟩
  · -- `j` is not a left endpoint, since `π_{j+1}` would then be a leaf.
    have hL : j ∉ T.treeMatching.leftEndpoints := by
      rintro hL
      obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.1 hL
      obtain ⟨h', hleaf⟩ := isLeaf_postorder_getElem_of_mem_treeMatching hπS rfl hab
      obtain ⟨c, L₁, L₂, R, hsub⟩ := mem_leftChildLabels_iff.1 hLC
      cases eq_of_isSubtree_of_isDecreasing hT.1 hleaf hsub
    refine ⟨⟨hj, by tauto⟩, fun hC => hR ?_⟩
    obtain ⟨-, _, hRC⟩ := Finset.mem_filter.1 hC
    exact mem_image_snd_treeMatching hT.1 hj'.1 h hLC hRC
  · rintro (hR | ⟨hU, hC⟩)
    · obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.1 hR
      obtain ⟨-, ⟨ha, hb, L₁, L₂, d, R₁, R₂, hsub⟩⟩ := Finset.mem_filter.1 hab
      exact ⟨hb, mem_leftChildLabels_iff.2 ⟨_, L₁, L₂, _, hsub⟩⟩
    · obtain ⟨h, L, R, hsub, ⟨L₁, L₂, rfl⟩ | ⟨R₁, R₂, rfl⟩⟩ :=
        parent_postorder_getElem_of_not_mem_leftEndpoints hn hπS rfl hj'.1 hj'.2
          fun hL => hU.2 (.inl hL)
      · exact ⟨h, mem_leftChildLabels_iff.2 ⟨_, L₁, L₂, R, hsub⟩⟩
      · refine absurd (Finset.mem_filter.2 ⟨?_, h, ?_⟩) hC
        · rw [Finset.unmatchedVertices, Finset.mem_sdiff, Finset.mem_union, hlen]; exact hU
        · exact mem_rightChildLabels_iff.2 ⟨L, _, R₁, R₂, hsub⟩

end BinaryTree

end

/-!
## Counting binary vertices through the matching encoding

Let `T` be a decreasing binary plane tree on `[n]` with postorder reading `𝒫(T) = π ∈ S_n`.
The pairs of the matching `M(T)` are in bijection with the binary vertices of `T`, so the
number of binary vertices equals the size of the matching: `bin(T) = |M(T)|`.

Labels are in `ℕ`, `S_n` is `permWords n` and `[n]` is `Finset.Icc 1 n`, as in
`BinaryTree.card_rightChildLabels_eq_card_treeMatching_add_card_treeRightChoices`.
-/

section

open BinaryTree

namespace Proof_lem_matching_tree_binary_count

private lemma mem_leftChildLabels_node_iff {α : Type*} [DecidableEq α] {x m : α}
    {l r : BinaryTree α} : x ∈ (node m l r).leftChildLabels ↔
      x ∈ l.leftChildLabels ∨ x ∈ r.leftChildLabels ∨ (x = m ∧ l ≠ nil) := by
  cases l <;> simp
  tauto

private lemma mem_rightChildLabels_node_iff {α : Type*} [DecidableEq α] {x m : α}
    {l r : BinaryTree α} : x ∈ (node m l r).rightChildLabels ↔
      x ∈ l.rightChildLabels ∨ x ∈ r.rightChildLabels ∨ (x = m ∧ r ≠ nil) := by
  cases r <;> simp
  tauto

/-- A vertex with a right child is the root of a subtree `node m L (node d R₁ R₂)`. -/
private lemma exists_isSubtree_of_mem_rightChildLabels {α : Type*} [DecidableEq α] :
    ∀ {T : BinaryTree α} {m : α}, m ∈ T.rightChildLabels →
      ∃ (L : BinaryTree α) (d : α) (R₁ R₂ : BinaryTree α),
        Relation.ReflTransGen (fun S U : BinaryTree α => ∃ b L R, U = node b L R ∧ (S = L ∨ S = R))
          (node m L (node d R₁ R₂)) T
  | nil, _, h => by simp at h
  | node a l r, m, h => by
    rcases mem_rightChildLabels_node_iff.1 h with h | h | ⟨rfl, hr⟩
    · obtain ⟨L, d, R₁, R₂, hS⟩ := exists_isSubtree_of_mem_rightChildLabels h
      exact ⟨L, d, R₁, R₂, hS.tail ⟨a, l, r, rfl, .inl rfl⟩⟩
    · obtain ⟨L, d, R₁, R₂, hS⟩ := exists_isSubtree_of_mem_rightChildLabels h
      exact ⟨L, d, R₁, R₂, hS.tail ⟨a, l, r, rfl, .inr rfl⟩⟩
    · obtain _ | ⟨d, R₁, R₂⟩ := r
      · exact absurd rfl hr
      · exact ⟨l, d, R₁, R₂, .refl⟩

/-- Every vertex with a right child is a vertex: `RC(T) ⊆ Lab(T)`. -/
private lemma rightChildLabels_subset_labels {α : Type*} [DecidableEq α] :
    ∀ T : BinaryTree α, T.rightChildLabels ⊆ T.labels
  | nil => by simp
  | node a l r => fun x hx => by
    have := @rightChildLabels_subset_labels _ _ l x
    have := @rightChildLabels_subset_labels _ _ r x
    rw [mem_rightChildLabels_node_iff] at hx
    simp only [labels, Finset.mem_union, Finset.mem_singleton]
    tauto

/-- Every vertex with a left child is a vertex: `LC(T) ⊆ Lab(T)`. -/
private lemma leftChildLabels_subset_labels {α : Type*} [DecidableEq α] :
    ∀ T : BinaryTree α, T.leftChildLabels ⊆ T.labels
  | nil => by simp
  | node a l r => fun x hx => by
    have := @leftChildLabels_subset_labels _ _ l x
    have := @leftChildLabels_subset_labels _ _ r x
    rw [mem_leftChildLabels_node_iff] at hx
    simp only [labels, Finset.mem_union, Finset.mem_singleton]
    tauto

private lemma numBinaryNodes_node {α : Type*} [DecidableEq α] {m : α} {l r : BinaryTree α} :
    (node m l r).numBinaryNodes =
      l.numBinaryNodes + r.numBinaryNodes + if l ≠ nil ∧ r ≠ nil then 1 else 0 := by
  cases l <;> cases r <;> simp

/-- The two-child labels of `node m l r`: those of `l`, those of `r`, and `m` itself when both
subtrees are nonempty, provided the root and the two subtrees carry disjoint labels. -/
private lemma leftChildLabels_inter_rightChildLabels_node {α : Type*} [DecidableEq α] {m : α}
    {l r : BinaryTree α} (hdisj : Disjoint l.labels r.labels) (hml : m ∉ l.labels)
    (hmr : m ∉ r.labels) :
    (node m l r).leftChildLabels ∩ (node m l r).rightChildLabels =
      (l.leftChildLabels ∩ l.rightChildLabels ∪ r.leftChildLabels ∩ r.rightChildLabels) ∪
        if l ≠ nil ∧ r ≠ nil then {m} else ∅ := by
  ext x
  have := @leftChildLabels_subset_labels _ _ l x
  have := @rightChildLabels_subset_labels _ _ l x
  have := @leftChildLabels_subset_labels _ _ r x
  have := @rightChildLabels_subset_labels _ _ r x
  have : x ∈ l.labels → x ∉ r.labels := fun h => Finset.disjoint_left.1 hdisj h
  have : x = m → x ∉ l.labels ∧ x ∉ r.labels := by rintro rfl; exact ⟨hml, hmr⟩
  have : x ∈ (if l ≠ nil ∧ r ≠ nil then ({m} : Finset α) else ∅) ↔
      x = m ∧ l ≠ nil ∧ r ≠ nil := by split_ifs with h <;> simp [h]
  rw [Finset.mem_inter, mem_leftChildLabels_node_iff, mem_rightChildLabels_node_iff,
    Finset.mem_union, Finset.mem_union, Finset.mem_inter, Finset.mem_inter, this]
  clear hdisj hml hmr
  tauto

/-- In a decreasing tree, the binary vertices are the labels having both a left and a right
child: `bin(T) = |LC(T) ∩ RC(T)|`. -/
private lemma numBinaryNodes_eq_card_inter {α : Type*} [DecidableEq α] [Preorder α] :
    ∀ T : BinaryTree α, T.IsDecreasing →
      T.numBinaryNodes = (T.leftChildLabels ∩ T.rightChildLabels).card
  | nil, _ => by simp
  | node m l r, ⟨hl, hr, hdisj, hlt⟩ => by
    have hml : m ∉ l.labels := fun h => lt_irrefl m (hlt m (Finset.mem_union_left _ h))
    have hmr : m ∉ r.labels := fun h => lt_irrefl m (hlt m (Finset.mem_union_right _ h))
    have hsub (U : BinaryTree α) : U.leftChildLabels ∩ U.rightChildLabels ⊆ U.labels :=
      Finset.inter_subset_left.trans (leftChildLabels_subset_labels U)
    rw [leftChildLabels_inter_rightChildLabels_node hdisj hml hmr, numBinaryNodes_node,
      numBinaryNodes_eq_card_inter l hl, numBinaryNodes_eq_card_inter r hr,
      ← Finset.card_union_of_disjoint (hdisj.mono (hsub l) (hsub r))]
    split_ifs
    · rw [Finset.card_union_of_disjoint (Finset.disjoint_singleton_right.2 fun h =>
        (Finset.mem_union.1 h).elim (fun h => hml (hsub l h)) (fun h => hmr (hsub r h))),
        Finset.card_singleton]
    · simp

/-- The labels with two children are the letters of `π` at the right endpoints of `M(T)`:
`LC(T) ∩ RC(T) = {π[j] : j ∈ R(M(T))}`. -/
private lemma leftChildLabels_inter_rightChildLabels_eq_image {n : ℕ} (hn : 1 ≤ n)
    {π : List ℕ} (hπS : π ∈ permWords n) {T : BinaryTree ℕ}
    (hT : T ∈ decreasingTrees (Finset.Icc 1 n)) (hπ : T.postorder = π) :
    T.leftChildLabels ∩ T.rightChildLabels =
      (T.treeMatching.image Prod.snd).image (fun j => π.getD j 0) := by
  classical
  have hR : ∀ j ∈ T.treeMatching.image Prod.snd, j ∈ Finset.Icc 1 (n - 1) := by
    intro j hj
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hj
    have := (Finset.mem_filter.1 hp).1
    rw [Finset.mem_product, hπ, hπS.2.1] at this
    exact this.2
  ext x
  constructor
  · rintro hx
    obtain ⟨hxL, hxR⟩ := Finset.mem_inter.1 hx
    have hxl : x ∈ π := by
      simpa [hT.2, ← hπS.2.2] using rightChildLabels_subset_labels T hxR
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hxl
    obtain rfl | hipos := Nat.eq_zero_or_pos i
    · obtain ⟨L, d, R₁, R₂, hS⟩ := exists_isSubtree_of_mem_rightChildLabels hxR
      have := (postorder_getElem?_pred_eq_last_child hT (j := 1) le_rfl
        (by simp [hπ]) hS (Or.inr (by simp))).1
      omega
    have hj : i ∈ Finset.Icc 1 (n - 1) := by have := hπS.2.1; simp only [Finset.mem_Icc]; omega
    have hA := (mem_leftChildLabels_iff_mem_treeMatching_or_unmatchedVertices_sdiff hn hπS hT hπ
      hj).1 ⟨hi, hxL⟩
    have hB := (mem_rightChildLabels_iff_mem_treeMatching_or_treeRightChoices hπS hT hπ
      hj).1 ⟨hi, hxR⟩
    refine Finset.mem_image.2 ⟨i, ?_, by simp [List.getD_eq_getElem?_getD, hi]⟩
    simp only [Finset.mem_union, Finset.mem_sdiff] at hA hB
    tauto
  · rintro hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨hjl, hmL⟩ := (mem_leftChildLabels_iff_mem_treeMatching_or_unmatchedVertices_sdiff hn
      hπS hT hπ (hR j hj)).2 (Finset.mem_union_left _ hj)
    obtain ⟨_, hmR⟩ := (mem_rightChildLabels_iff_mem_treeMatching_or_treeRightChoices
      hπS hT hπ (hR j hj)).2 (Finset.mem_union_left _ hj)
    simpa [List.getD_eq_getElem?_getD, hjl] using Finset.mem_inter.2 ⟨hmL, hmR⟩

end Proof_lem_matching_tree_binary_count

namespace BinaryTree

open Proof_lem_matching_tree_binary_count in
/-- **Counting binary vertices.** Let `n ≥ 1`, `π ∈ S_n` and `T ∈ DBT([n])` with `𝒫(T) = π`.
Then `bin(T) = |M(T)|`. -/
@[lognarayana "lem_matching_tree_binary_count"]
public theorem numBinaryNodes_eq_card_treeMatching {n : ℕ}
    (hn : 1 ≤ n) {π : List ℕ} (hπS : π ∈ permWords n) {T : BinaryTree ℕ}
    (hT : T ∈ decreasingTrees (Finset.Icc 1 n)) (hπ : T.postorder = π) :
    T.numBinaryNodes = T.treeMatching.card := by
  classical
  have hM := (treeMatching_mem_fiberMatchings hn hπS hT hπ).1
  rw [numBinaryNodes_eq_card_inter T hT.1,
    leftChildLabels_inter_rightChildLabels_eq_image hn hπS hT hπ,
    Finset.card_image_of_injOn, Finset.card_image_of_injOn
      fun p hp q hq hpq => hM.eq_of_mem_of_mem p hp q hq p.2 (Or.inr rfl) (Or.inr hpq)]
  intro i hi j hj hij
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hi
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hj
  have hi := (Finset.mem_filter.1 hp).1
  have hj := (Finset.mem_filter.1 hq).1
  simp only [Finset.mem_product, Finset.mem_Icc, hπ] at hi hj
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show p.2 < π.length by omega),
    List.getElem?_eq_getElem (show q.2 < π.length by omega), Option.getD_some] at hij
  exact (nodup_of_mem_permWords hπS).getElem_inj_iff.1 hij

end BinaryTree

end

/-!
## Peaks of the inorder reading through the matching encoding

Let `T` be a decreasing binary plane tree on `[n]` with postorder reading `𝒫(T) = π ∈ S_n`.
The peaks of the inorder reading `I(T)` are exactly the vertices of `T` having two children,
and these are counted by the matching `M(T)`: `peak(I(T)) = |M(T)|`.

Labels are in `ℕ`, `S_n` is `permWords n` and `[n]` is `Finset.Icc 1 n`, as in
`BinaryTree.card_rightChildLabels_eq_card_treeMatching_add_card_treeRightChoices`.
-/

section

open BinaryTree

namespace BinaryTree

/-- **Peaks of the inorder reading.** Let `n ≥ 1`, `π ∈ S_n` and `T ∈ DBT([n])` with
`𝒫(T) = π`. Then `peak(I(T)) = |M(T)|`. -/
@[lognarayana "lem_matching_tree_peaks"]
public theorem peakCount_inorder_eq_card_treeMatching {n : ℕ}
    (hn : 1 ≤ n) {π : List ℕ} (hπS : π ∈ permWords n) {T : BinaryTree ℕ}
    (hT : T ∈ decreasingTrees (Finset.Icc 1 n)) (hπ : T.postorder = π) :
    T.inorder.peakCount = T.treeMatching.card := by
  rw [peakCount_inorder_of_mem_decreasingTrees hT,
    numBinaryNodes_eq_card_treeMatching hn hπS hT hπ]

end BinaryTree

end

/-!
## Finite sums over matchings
-/


/-- A sum over the pairs `(a, b)` with `a` in a finite set `S` and `b ∈ t a` is an iterated
sum. -/
private lemma finsum_mem_sigma_eq {α β M : Type*} [AddCommMonoid M] {S : Set α} (hS : S.Finite)
    (t : α → Finset β) (f : α × β → M) :
    ∑ᶠ p ∈ {p : α × β | p.1 ∈ S ∧ p.2 ∈ t p.1}, f p = ∑ᶠ a ∈ S, ∑ b ∈ t a, f (a, b) := by
  classical
  lift S to Finset α using hS
  have hmem : ∀ p : α × β, p ∈ (S ×ˢ S.biUnion t).filter (fun p => p.2 ∈ t p.1) ↔
      p.1 ∈ S ∧ p.2 ∈ t p.1 := fun p => by
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_biUnion]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, p.1, h.1, h.2⟩, h.2⟩⟩
  rw [show {p : α × β | p.1 ∈ (S : Set α) ∧ p.2 ∈ t p.1} = ↑((S ×ˢ S.biUnion t).filter
      (fun p => p.2 ∈ t p.1)) by ext p; rw [Finset.mem_coe, hmem]; rfl, finsum_mem_coe_finset,
    finsum_mem_coe_finset, Finset.sum_finset_product _ S t hmem]

/-!
## The peak-weighted fiber polynomial as a sum over matchings

For `n ≥ 1`, `π ∈ S_n` and `λ` in a commutative semiring `R`, the peak-weighted homogeneous
fiber polynomial expands over the matchings of `π`:
`H^λ_π(x, y) = ∑_{M ∈ 𝒜(π)} (λ x y)^{|M|} (x + y)^{n - 1 - 2|M|}`.

The variables are `x = X 0` and `y = X 1` of `MvPolynomial (Fin 2) R`, as for
`List.fiberPeakPolynomial`. The paper takes `λ ∈ ℝ`; the identity is stated over any
commutative semiring `R`, the paper's case being `R = ℝ`. Since `List.fiberMatchings π` is a
set (finite, being a set of matchings on `[n - 1]`), the sum is a `finsum`.
The exponent `n - 1 - 2|M|` is truncated
subtraction in `ℕ`, which is the true difference because a partial matching on `[n - 1]` has
`2|M| ≤ n - 1`. The convention `0⁰ = 1` is that of `Monoid.npow`.
-/

section

open MvPolynomial
open MvPolynomial BinaryTree

namespace Proof_lem_matching_homog_peak_poly

/-- The weighted subset binomial theorem behind each matching: if `|U| + 2k = N`, then
`∑_{D ⊆ U} a^k x^{k + |D|} y^{N - (k + |D|)} = (a x y)^k (x + y)^{N - 2k}`. -/
private lemma sum_powerset_pow_mul_pow_eq {S β : Type*} [CommSemiring S]
    (U : Finset β) {k N : ℕ} (hU : U.card + 2 * k = N) (a x y : S) :
    ∑ D ∈ U.powerset, a ^ k * x ^ (k + D.card) * y ^ (N - (k + D.card)) =
      (a * x * y) ^ k * (x + y) ^ (N - 2 * k) := by
  classical
  rw [show N - 2 * k = U.card by omega, ← Finset.prod_const, Finset.prod_add, Finset.mul_sum]
  refine Finset.sum_congr rfl fun D hD => ?_
  have hD := Finset.mem_powerset.1 hD
  rw [Finset.prod_const, Finset.prod_const, Finset.card_sdiff_of_subset hD,
    show N - (k + D.card) = k + (U.card - D.card) by have := Finset.card_le_card hD; omega]
  ring

end Proof_lem_matching_homog_peak_poly

namespace List


open Proof_lem_matching_homog_peak_poly in
/-- For `n ≥ 1`, `π ∈ S_n` and `λ ∈ R`,
`H^λ_π(x, y) = ∑_{M ∈ 𝒜(π)} (λ x y)^{|M|} (x + y)^{n - 1 - 2|M|}`. -/
@[lognarayana "lem_matching_homog_peak_poly"]
public theorem fiberPeakPolynomial_eq_finsum_fiberMatchings (R : Type*) [CommSemiring R] {n : ℕ}
    (hn : 1 ≤ n) {π : List ℕ} (hπ : π ∈ permWords n) (lam : R) :
    fiberPeakPolynomial R lam π =
      ∑ᶠ M ∈ π.fiberMatchings,
        (C lam * X 0 * X 1) ^ M.card * (X 0 + X 1) ^ (n - 1 - 2 * M.card) := by
  classical
  have hlen : π.length = n := hπ.2.1
  rw [List.fiberPeakPolynomial, ← finsum_mem_coe_finset,
    ← finsum_mem_eq_of_bijOn _ (bijOn_inorder_postorder_eq_stackFiber hπ) (fun _ _ => rfl),
    finsum_mem_congr rfl fun T hT => by
      rw [peakCount_inorder_eq_card_treeMatching hn hπ hT.1 hT.2,
        numDescents_inorder_eq_card_treeMatching_add_card_treeRightChoices hn hπ hT.1 hT.2],
    finsum_mem_eq_of_bijOn _ (BinaryTree.bijOn_treeMatching_treeRightChoices hn hπ)
      (g := fun p => C (lam ^ p.1.card) * X 0 ^ (p.1.card + p.2.card) *
        X 1 ^ (π.length - 1 - (p.1.card + p.2.card))) (fun _ _ => rfl),
    show {p : Finset (ℕ × ℕ) × Finset ℕ |
        p.1 ∈ π.fiberMatchings ∧ p.2 ⊆ Finset.unmatchedVertices (n - 1) p.1} =
      {p | p.1 ∈ π.fiberMatchings ∧ p.2 ∈ (Finset.unmatchedVertices (n - 1) p.1).powerset} by
      simp,
    finsum_mem_sigma_eq (fiberMatchings_finite π)
      fun M => (Finset.unmatchedVertices (n - 1) M).powerset]
  refine finsum_mem_congr rfl fun M hM => ?_
  simp only [map_pow, hlen]
  exact sum_powerset_pow_mul_pow_eq _ (hlen ▸ hM.1.card_unmatchedVertices_add_two_mul_card) _ _ _

end List

end

/-!
## The homogeneous fiber polynomial as a sum over matchings

For `n ≥ 1` and `π ∈ S_n`, the homogeneous fiber polynomial expands over the matchings of `π`:
`H_π(x, y) = ∑_{M ∈ 𝒜(π)} (x y)^{|M|} (x + y)^{n - 1 - 2|M|}`.

The variables are `x = X 0` and `y = X 1` of `MvPolynomial (Fin 2) R`, as for
`List.fiberHomogPolynomial`. The paper works over `ℝ`; both sides have natural-number
coefficients, so the identity is stated over any commutative semiring `R`, the paper's being
`R = ℝ`. Since `List.fiberMatchings π` is a set (finite, being a set of matchings on
`[n - 1]`), the sum is a `finsum`. The exponent `n - 1 - 2|M|` is truncated subtraction in `ℕ`,
which is the true difference because a partial matching on `[n - 1]` has `2|M| ≤ n - 1`.
-/

namespace List


open MvPolynomial in
/-- For `n ≥ 1` and `π ∈ S_n`,
`H_π(x, y) = ∑_{M ∈ 𝒜(π)} (x y)^{|M|} (x + y)^{n - 1 - 2|M|}`. -/
@[lognarayana "lem_matching_homog_poly"]
public theorem fiberHomogPolynomial_eq_finsum_fiberMatchings (R : Type*) [CommSemiring R]
    {n : ℕ} (hn : 1 ≤ n) {π : List ℕ} (hπ : π ∈ permWords n) :
    fiberHomogPolynomial R π =
      ∑ᶠ M ∈ π.fiberMatchings,
        (X 0 * X 1 : MvPolynomial (Fin 2) R) ^ M.card * (X 0 + X 1) ^ (n - 1 - 2 * M.card) := by
  simpa [List.fiberPeakPolynomial, List.fiberHomogPolynomial] using
    List.fiberPeakPolynomial_eq_finsum_fiberMatchings R hn hπ 1

end List

/-!
## The fiber top polynomial as a sum over matchings

For `n ≥ 1` and `π ∈ S_n`, the fiber top polynomial expands over the matchings of `π`:
`𝒟_π(x, y) = ∑_{M ∈ 𝒜(π)} ∏_{v ∈ R(M)} x_{π_{v+1}} y_{π_{v+1}}
  ∏_{v ∈ U(M)} (x_{π_{v+1}} + y_{π_{v+1}})`,
where `R(M)` is the set of right endpoints of `M` and `U(M)` the set of unmatched vertices of
`M` in `[n - 1]`.

As in `List.fiberTopPolynomial`, `x_a = X (true, a)` and `y_a = X (false, a)`, and the
coefficients lie in an arbitrary commutative semiring (the paper's is `ℝ`). Positions are
`1`-based, so the letter `π_{v+1}` is `π[v]` with `0`-based indexing; it is written `π[v]!`,
which agrees with `π[v]` because every `v ∈ R(M) ∪ U(M)` lies in `[n - 1]`. The right endpoints
`R(M)` are `M.image Prod.snd`, as in `Finset.unmatchedVertices`. The set `𝒜(π)` is finite, and
the sum is a `finsum` over it.
-/

section

open MvPolynomial
open MvPolynomial BinaryTree

namespace Proof_lem_top_poly_matching

/-- A set `K` of letters of `π ∈ S_n` not containing `π_1`, whose members `π_{j+1}`
(`j ∈ [n - 1]`) are exactly those with `j ∈ S ⊆ [n - 1]`, is the image of `S` under
`j ↦ π_{j+1}`. -/
private lemma eq_image_of_mem_iff {n : ℕ} {π : List ℕ} (hπ : π ∈ permWords n)
    {K S : Finset ℕ} (hK : ∀ a ∈ K, a ∈ π) (h0 : ∀ h : 0 < π.length, π[0] ∉ K)
    (hS : S ⊆ Finset.Icc 1 (n - 1))
    (hiff : ∀ j ∈ Finset.Icc 1 (n - 1), (∃ h : j < π.length, π[j] ∈ K) ↔ j ∈ S) :
    K = S.image (fun v => π[v]!) := by
  have hlen := hπ.2.1
  ext a
  constructor
  · intro ha
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem (hK a ha)
    rcases Nat.eq_zero_or_pos i with rfl | hipos
    · exact (h0 hi ha).elim
    · have hj : i ∈ Finset.Icc 1 (n - 1) := by simp only [Finset.mem_Icc]; omega
      exact Finset.mem_image.2 ⟨i, (hiff i hj).1 ⟨hi, ha⟩, by simp [hi]⟩
  · intro ha
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 ha
    obtain ⟨hjl, hm⟩ := (hiff j (hS hj)).2 hj
    simpa [hjl] using hm

/-- The letters of `π ∈ S_n` are distinct, so `j ↦ π_{j+1}` is injective on `[n - 1]`. -/
private lemma injOn_getElem_Icc {n : ℕ} {π : List ℕ} (hπ : π ∈ permWords n) :
    Set.InjOn (fun v => π[v]!) (↑(Finset.Icc 1 (n - 1)) : Set ℕ) := by
  have hlen := hπ.2.1
  intro i hi j hj hij
  simp only [Finset.coe_Icc, Set.mem_Icc] at hi hj
  simp only [getElem!_pos π i (show i < π.length by omega),
    getElem!_pos π j (show j < π.length by omega)] at hij
  exact (nodup_of_mem_permWords hπ).getElem_inj_iff.1 hij

/-- `∏` over the image of a disjoint union `A ∪ B ⊆ [n - 1]` under `j ↦ π_{j+1}` splits as a
product over `A` times a product over `B`. -/
private lemma prod_image_union {M : Type*} [CommMonoid M] {n : ℕ} {π : List ℕ}
    (hπ : π ∈ permWords n) {A B : Finset ℕ} (hA : A ⊆ Finset.Icc 1 (n - 1))
    (hB : B ⊆ Finset.Icc 1 (n - 1)) (hAB : Disjoint A B) (g : ℕ → M) :
    ∏ a ∈ (A ∪ B).image (fun v => π[v]!), g a = (∏ v ∈ A, g π[v]!) * ∏ v ∈ B, g π[v]! := by
  rw [Finset.prod_image fun i hi j hj => injOn_getElem_Icc hπ (Finset.union_subset hA hB hi)
    (Finset.union_subset hA hB hj), Finset.prod_union hAB]

/-- In a decreasing tree on `[n]` with postorder `π`, a vertex with a child is a letter of `π`
other than the first letter `π_1`, which is a leaf. -/
private lemma mem_and_ne_head_of_isSubtree {n : ℕ} {π : List ℕ} (hπ : π ∈ permWords n)
    {T : BinaryTree ℕ} (hT : T ∈ decreasingTrees (Finset.Icc 1 n)) (hTπ : T.postorder = π)
    {m : ℕ} {l r : BinaryTree ℕ} (hS : IsSubtree (node m l r) T) (hc : l ≠ nil ∨ r ≠ nil) :
    m ∈ π ∧ ∀ h : 0 < π.length, π[0] ≠ m := by
  refine ⟨?_, fun h hm => ?_⟩
  · have := mem_labels_of_isSubtree hS
    rw [hT.2, ← hπ.2.2] at this
    simpa [List.letters] using this
  · have hw : T.postorder[1 - 1]? = some m := by simp [hTπ, ← hm, List.getElem?_eq_getElem h]
    have := (postorder_getElem?_pred_eq_last_child hT le_rfl hw hS hc).1
    omega

/-- **The monomial of a tree in the fiber.** For a decreasing tree `T` on `[n]` with postorder
`π`, with `M = M(T)` and `C = C(T)`, the monomial `∏_{DT(I(T))} x ∏_{AT(I(T))} y` is
`∏_{R(M)} x y · ∏_{C} x · ∏_{U(M) \ C} y`, letters read through `v ↦ π_{v+1}`. -/
private lemma inorder_monomial_eq (R : Type*) [CommSemiring R] {n : ℕ} (hn : 1 ≤ n)
    {π : List ℕ} (hπ : π ∈ permWords n) {T : BinaryTree ℕ}
    (hT : T ∈ decreasingTrees (Finset.Icc 1 n)) (hTπ : T.postorder = π) :
    (∏ a ∈ T.inorder.descentTops, (X (true, a) : MvPolynomial (Bool × ℕ) R)) *
        ∏ b ∈ T.inorder.ascentTops, X (false, b) =
      (∏ v ∈ T.treeMatching.image Prod.snd, X (true, π[v]!) * X (false, π[v]!)) *
        ((∏ v ∈ T.treeRightChoices, X (true, π[v]!)) *
          ∏ v ∈ Finset.unmatchedVertices (n - 1) T.treeMatching \ T.treeRightChoices,
            X (false, π[v]!)) := by
  classical
  have hC := ((BinaryTree.bijOn_treeMatching_treeRightChoices hn hπ).mapsTo ⟨hT, hTπ⟩).2
  have hUI : Finset.unmatchedVertices (n - 1) T.treeMatching ⊆ Finset.Icc 1 (n - 1) :=
    Finset.sdiff_subset
  have hRI : T.treeMatching.image Prod.snd ⊆ Finset.Icc 1 (n - 1) := by
    intro j hj
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hj
    have := (Finset.mem_filter.1 hp).1
    rw [Finset.mem_product, hTπ, hπ.2.1] at this
    exact this.2
  have hRU : Disjoint (T.treeMatching.image Prod.snd)
      (Finset.unmatchedVertices (n - 1) T.treeMatching) :=
    Finset.disjoint_right.2 fun _ hj => by
      simp only [Finset.unmatchedVertices, Finset.mem_sdiff, Finset.mem_union] at hj
      exact fun h => hj.2 (Or.inr h)
  have hRC := eq_image_of_mem_iff hπ
    (fun a ha => by
      obtain ⟨L, d, R₁, R₂, hS⟩ := mem_rightChildLabels_iff.1 ha
      exact (mem_and_ne_head_of_isSubtree hπ hT hTπ hS (Or.inr (by simp))).1)
    (fun h ha => by
      obtain ⟨L, d, R₁, R₂, hS⟩ := mem_rightChildLabels_iff.1 ha
      exact (mem_and_ne_head_of_isSubtree hπ hT hTπ hS (Or.inr (by simp))).2 h rfl)
    (Finset.union_subset hRI (hC.trans hUI))
    (fun j hj => BinaryTree.mem_rightChildLabels_iff_mem_treeMatching_or_treeRightChoices
      hπ hT hTπ hj)
  have hLC := eq_image_of_mem_iff hπ
    (fun a ha => by
      obtain ⟨c, L₁, L₂, R', hS⟩ := mem_leftChildLabels_iff.1 ha
      exact (mem_and_ne_head_of_isSubtree hπ hT hTπ hS (Or.inl (by simp))).1)
    (fun h ha => by
      obtain ⟨c, L₁, L₂, R', hS⟩ := mem_leftChildLabels_iff.1 ha
      exact (mem_and_ne_head_of_isSubtree hπ hT hTπ hS (Or.inl (by simp))).2 h rfl)
    (Finset.union_subset hRI (Finset.sdiff_subset.trans hUI))
    (fun j hj => BinaryTree.mem_leftChildLabels_iff_mem_treeMatching_or_unmatchedVertices_sdiff
      hn hπ hT hTπ hj)
  rw [descentTops_inorder_of_mem_decreasingTrees hT, ascentTops_inorder_of_mem_decreasingTrees hT,
    hRC, hLC, prod_image_union hπ hRI (hC.trans hUI) (hRU.mono_right hC),
    prod_image_union hπ hRI (Finset.sdiff_subset.trans hUI) (hRU.mono_right Finset.sdiff_subset),
    Finset.prod_mul_distrib]
  ring

end Proof_lem_top_poly_matching

namespace List


open Proof_lem_top_poly_matching in
/-- For `n ≥ 1` and `π ∈ S_n`,
`𝒟_π(x, y) = ∑_{M ∈ 𝒜(π)} ∏_{v ∈ R(M)} x_{π_{v+1}} y_{π_{v+1}}
∏_{v ∈ U(M)} (x_{π_{v+1}} + y_{π_{v+1}})`, with `U(M)` the unmatched vertices in `[n - 1]`. -/
@[lognarayana "lem_top_poly_matching"]
public theorem fiberTopPolynomial_eq_finsum_fiberMatchings (R : Type*) [CommSemiring R]
    {n : ℕ} (hn : 1 ≤ n) {π : List ℕ} (hπ : π ∈ permWords n) :
    fiberTopPolynomial R π =
      ∑ᶠ M ∈ π.fiberMatchings,
        (∏ v ∈ M.image Prod.snd, (X (true, π[v]!) * X (false, π[v]!) :
            MvPolynomial (Bool × ℕ) R)) *
          ∏ v ∈ Finset.unmatchedVertices (n - 1) M, (X (true, π[v]!) + X (false, π[v]!)) := by
  classical
  rw [List.fiberTopPolynomial, ← finsum_mem_coe_finset,
    ← finsum_mem_eq_of_bijOn _ (bijOn_inorder_postorder_eq_stackFiber hπ) (fun _ _ => rfl),
    finsum_mem_congr rfl fun T hT => inorder_monomial_eq R hn hπ hT.1 hT.2,
    finsum_mem_eq_of_bijOn _ (BinaryTree.bijOn_treeMatching_treeRightChoices hn hπ)
      (g := fun p => (∏ v ∈ p.1.image Prod.snd, X (true, π[v]!) * X (false, π[v]!)) *
        ((∏ v ∈ p.2, X (true, π[v]!)) *
          ∏ v ∈ Finset.unmatchedVertices (n - 1) p.1 \ p.2, X (false, π[v]!))) (fun _ _ => rfl),
    show {p : Finset (ℕ × ℕ) × Finset ℕ |
        p.1 ∈ π.fiberMatchings ∧ p.2 ⊆ Finset.unmatchedVertices (n - 1) p.1} =
      {p | p.1 ∈ π.fiberMatchings ∧ p.2 ∈ (Finset.unmatchedVertices (n - 1) p.1).powerset} by
      simp,
    finsum_mem_sigma_eq (fiberMatchings_finite π)
      fun M => (Finset.unmatchedVertices (n - 1) M).powerset]
  exact finsum_mem_congr rfl fun M _ => by
    dsimp only
    rw [← Finset.mul_sum, Finset.prod_add]

end List

end

/-!
## The fiber descent polynomial as a sum over matchings

For `n ≥ 1` and `π ∈ S_n`, the fiber descent polynomial `D_π(x)` of `π` expands over the set
`𝒜(π)` of matchings of `π`:
`D_π(x) = ∑_{M ∈ 𝒜(π)} x^{|M|} (1 + x)^{n - 1 - 2|M|}`.

The polynomial is taken over an arbitrary commutative semiring `R`; the paper's statement is
the case `R = ℝ`. The set `𝒜(π)` is a `Set`, so the sum is a `finsum`; `𝒜(π)` is finite (it
consists of subsets of `[n - 1] × [n - 1]`). The exponent `n - 1 - 2|M|` is a natural-number
subtraction, which is exact since `2|M| ≤ n - 1` for a partial matching on `[n - 1]`.
-/

section

open Polynomial

namespace Proof_prop_matching_descent_poly

/-- The substitution `x ↦ x`, `y ↦ 1` from `R[x, y]` to `R[x]`. -/
private noncomputable abbrev setYOne (R : Type*) [CommSemiring R] :
    MvPolynomial (Fin 2) R →+* R[X] :=
  MvPolynomial.eval₂Hom Polynomial.C ![Polynomial.X, 1]

private lemma setYOne_fiberHomogPolynomial (R : Type*) [CommSemiring R] (π : List ℕ) :
    setYOne R (List.fiberHomogPolynomial R π) = List.fiberDescentPolynomial R π := by
  simp [List.fiberHomogPolynomial, List.fiberDescentPolynomial, map_sum]

end Proof_prop_matching_descent_poly

namespace List


open Proof_prop_matching_descent_poly in
/-- For `n ≥ 1` and `π ∈ S_n`,
`D_π(x) = ∑_{M ∈ 𝒜(π)} x^{|M|} (1 + x)^{n - 1 - 2|M|}`. -/
@[lognarayana "prop_matching_descent_poly"]
public theorem fiberDescentPolynomial_eq_finsum_fiberMatchings (R : Type*) [CommSemiring R]
    {n : ℕ} (hn : 1 ≤ n) {π : List ℕ} (hπ : π ∈ permWords n) :
    fiberDescentPolynomial R π =
      ∑ᶠ M ∈ π.fiberMatchings, (X : R[X]) ^ M.card * (1 + X) ^ (n - 1 - 2 * M.card) := by
  rw [← setYOne_fiberHomogPolynomial, List.fiberHomogPolynomial_eq_finsum_fiberMatchings R hn hπ,
    finsum_mem_eq_finite_toFinset_sum _ (fiberMatchings_finite π),
    finsum_mem_eq_finite_toFinset_sum _ (fiberMatchings_finite π), map_sum]
  simp [add_comm]

end List

end

/-!
## The gamma form of the fiber descent polynomial

For `n ≥ 1` and `π ∈ S_n`, the fiber descent polynomial `D_π` is determined by the matching
polynomial `Γ_π`: for every `x ≠ -1`,
`D_π(x) = (1 + x)^{n - 1} Γ_π(x / (1 + x)^2)`.

The paper states the identity for real `x`; it is stated here for `x` in an arbitrary field
`K`, the paper's statement being the case `K = ℝ`. The hypothesis `x ≠ -1` is written
`1 + x ≠ 0`, which is what makes the division meaningful.
-/

section

open Polynomial

namespace Proof_prop_matching_gamma_form

/-- The substitution `z = x / (1 + x)²` turns `(1 + x)^N z^k` into `x^k (1 + x)^(N - 2k)`. -/
private lemma one_add_pow_mul_div_sq_pow {K : Type*} [Field K] {x : K} (hx : 1 + x ≠ 0)
    {k N : ℕ} (h : 2 * k ≤ N) :
    (1 + x) ^ N * (x / (1 + x) ^ 2) ^ k = x ^ k * (1 + x) ^ (N - 2 * k) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_sub_cancel_left, div_pow, ← pow_mul, pow_add]
  field_simp

end Proof_prop_matching_gamma_form

namespace List


open Proof_prop_matching_gamma_form in
/-- For `n ≥ 1`, `π ∈ S_n` and `x ≠ -1`, `D_π(x) = (1 + x)^{n - 1} Γ_π(x / (1 + x)^2)`. -/
@[lognarayana "prop_matching_gamma_form"]
public theorem eval_fiberDescentPolynomial_eq_pow_mul_eval_fiberMatchingPolynomial
    {K : Type*} [Field K] {n : ℕ} (hn : 1 ≤ n) {π : List ℕ} (hπ : π ∈ permWords n)
    {x : K} (hx : 1 + x ≠ 0) :
    (fiberDescentPolynomial K π).eval x =
      (1 + x) ^ (n - 1) * (fiberMatchingPolynomial K π).eval (x / (1 + x) ^ 2) := by
  rw [List.fiberDescentPolynomial_eq_finsum_fiberMatchings K hn hπ, List.fiberMatchingPolynomial,
    finsum_mem_eq_finite_toFinset_sum _ (fiberMatchings_finite π),
    finsum_mem_eq_finite_toFinset_sum _ (fiberMatchings_finite π), eval_finsetSum,
    eval_finsetSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun M hM => ?_
  have hcard := ((Set.Finite.mem_toFinset _).1 hM).1.card_unmatchedVertices_add_two_mul_card
  rw [hπ.2.1] at hcard
  simp only [eval_mul, eval_pow, eval_X, eval_add, eval_one]
  rw [one_add_pow_mul_div_sq_pow hx (by omega)]

end List

end
