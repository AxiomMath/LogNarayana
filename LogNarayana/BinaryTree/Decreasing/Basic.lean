/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module
public import LogNarayana.BinaryTree.Decreasing.Defs
public import LogNarayana.StackSorting.StackSort.Defs
public import LogNarayana.StackSorting.Descents.Defs

/-!
# Inorder and postorder readings of decreasing binary plane trees

A decreasing binary plane tree `T = ⟨m; T_L, T_R⟩` has its largest label `m` at the root, so its
inorder reading `I(T) = I(T_L) m I(T_R)` is split by its maximum into the readings of the two
subtrees. Every result of this file is an induction on the tree along that splitting.

* `I(T)` is a word with letter set `A` for `T ∈ DBT(A)`, and `I` is a bijection from `DBT(A)`
  onto such words; for `A = [n]` it is a bijection `DBT([n]) → S_n`.
* The ascent tops of `I(T)` are the labels with a left child, its descent tops are the labels
  with a right child, and its peaks are the binary vertices of `T`.
* West's stack-sorting map sends `I(T)` to the postorder reading `𝒫(T)`. Hence `I` restricts to
  a bijection from the trees in `DBT([n])` with postorder `π` onto the fiber `s⁻¹(π)`; the
  postorder reading itself is not injective on `DBT([2])`.
* The running example: `peak(2751364) = 2` and `s(2751364) = 2135467`.

## Main results

* `BinaryTree.isWord_inorder_of_mem_decreasingTrees`: `I(T)` is a word with `Let(I(T)) = A`.
* `BinaryTree.bijOn_inorder_decreasingTrees`: `I` is a bijection from `DBT(A)` onto
  `{σ ∈ 𝒲 | Let(σ) = A}`.
* `BinaryTree.bijOn_inorder_decreasingTrees_Icc`: `I` is a bijection from `DBT([n])` onto `S_n`.
* `BinaryTree.ascentTops_inorder_of_mem_decreasingTrees`: `AT(I(T)) = LC(T)`.
* `BinaryTree.descentTops_inorder_of_mem_decreasingTrees`: `DT(I(T)) = RC(T)`.
* `BinaryTree.peakCount_inorder_of_mem_decreasingTrees`: `peak(I(T)) = bin(T)`.
* `BinaryTree.stackSort_inorder_of_mem_decreasingTrees`: `s(I(T)) = 𝒫(T)`.
* `BinaryTree.bijOn_inorder_postorder_eq_stackFiber`: the bijection
  `{T ∈ DBT([n]) : 𝒫(T) = π} → s⁻¹(π)`, `T ↦ I(T)`.
* `BinaryTree.exists_ne_postorder_eq_decreasingTrees_Icc_two`: `𝒫` is not injective on
  `DBT([2])`.
* `List.peakCount_2751364`, `List.stackSort_2751364`: the running example.

## Implementation notes

Words are lists of natural numbers with positive, pairwise distinct entries (`IsWord`), so the
results about words take `A : Finset ℕ` with positive elements and `[n] = Finset.Icc 1 n`. The
paper takes all label sets to be finite sets of positive integers; where positivity plays no
role — ascent and descent tops, peaks and stack-sorting — the statements are made for an
arbitrary preorder (for stack-sorting, linear order) of labels, the paper's case being `α = ℕ`
or `α = ℤ`. The paper's pointwise forms "`b` is an ascent (descent) top of `I(T)` iff the
vertex labelled `b` has a left (right) child" are `Finset.ext_iff` of the equalities of sets.

## References

* [LogNarayana] *Log-Concavity in Narayana Transforms and Stack-Sorting Fibers*, Sections 2–3.
-/

/-! ### Peeling off the first letter of a list -/

namespace List

variable {α : Type*} [LT α] [DecidableRel (α := α) (· < ·)]

private theorem ascentTops_cons_cons [DecidableEq α] (a b : α) (l : List α) :
    (a :: b :: l).ascentTops = (if a < b then {b} else ∅) ∪ (b :: l).ascentTops := by
  unfold List.ascentTops
  ext x
  by_cases h : a < b <;> simp [h]

private theorem descentTops_cons_cons [DecidableEq α] (a b : α) (l : List α) :
    (a :: b :: l).descentTops = (if b < a then {a} else ∅) ∪ (b :: l).descentTops := by
  unfold List.descentTops
  ext x
  by_cases h : b < a <;> simp [h]

private theorem peakCount_of_length_le {l : List α} (h : l.length ≤ 2) : l.peakCount = 0 := by
  simp [List.peakCount, Finset.Ico_eq_empty_of_le h]

private theorem peakCount_cons_cons_cons (a b c : α) (l : List α) :
    (a :: b :: c :: l).peakCount =
      (if a < b ∧ c < b then 1 else 0) + (b :: c :: l).peakCount := by
  unfold List.peakCount
  rw [Finset.card_filter, Finset.card_filter]
  simp only [List.length_cons]
  rw [Finset.sum_eq_sum_Ico_succ_bot (by omega), ← Finset.sum_Ico_add' (c := 1)]
  congr 1
  · simp
  · refine Finset.sum_congr rfl fun i hi => ?_
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 2 := ⟨i - 2, by simp at hi; omega⟩
    simp [show j + 2 + 1 - 2 = j + 1 by omega, show j + 2 + 1 - 1 = j + 2 by omega]

end List

/-! ### Splitting a list at a letter exceeding its neighbours -/

namespace List

variable {α : Type*} [Preorder α] [DecidableRel (α := α) (· < ·)]

/-- Splitting a list at a letter `m` exceeding every letter before it: the position just before
`m` is an ascent with top `m`, provided `u` is nonempty. -/
private theorem ascentTops_append_cons [DecidableEq α] {m : α} {u : List α}
    (hu : ∀ a ∈ u, a < m) (v : List α) :
    (u ++ m :: v).ascentTops =
      u.ascentTops ∪ (if u = [] then ∅ else {m}) ∪ (m :: v).ascentTops := by
  induction u with
  | nil => simp [List.ascentTops]
  | cons a u ih =>
    cases u with
    | nil => simp [List.ascentTops, hu a (by simp)]
    | cons b u =>
      rw [List.cons_append, List.cons_append, ascentTops_cons_cons, ← List.cons_append,
        ih (fun x hx => hu x (List.mem_cons_of_mem _ hx)), ascentTops_cons_cons]
      simp only [reduceCtorEq, if_false, Finset.union_assoc]

/-- The ascent tops of `m v` when `m` exceeds every letter of `v`. -/
private theorem ascentTops_cons_of_lt [DecidableEq α] {m : α} {v : List α}
    (hv : ∀ a ∈ v, a < m) : (m :: v).ascentTops = v.ascentTops := by
  cases v with
  | nil => rfl
  | cons b v =>
    rw [ascentTops_cons_cons, if_neg (not_lt_of_gt (hv b (by simp))), Finset.empty_union]

/-- Splitting a list at a letter `m` exceeding every letter before it creates no descent. -/
private theorem descentTops_append_cons [DecidableEq α] {m : α} {u : List α}
    (hu : ∀ a ∈ u, a < m) (v : List α) :
    (u ++ m :: v).descentTops = u.descentTops ∪ (m :: v).descentTops := by
  induction u with
  | nil => simp [List.descentTops]
  | cons a u ih =>
    cases u with
    | nil =>
      simp [List.descentTops, not_lt_of_gt (hu a (by simp))]
    | cons b u =>
      rw [List.cons_append, List.cons_append, descentTops_cons_cons, ← List.cons_append,
        ih (fun x hx => hu x (List.mem_cons_of_mem _ hx)), descentTops_cons_cons,
        Finset.union_assoc]

/-- The descent tops of `m v` when `m` exceeds every letter of `v`: the position of `m` is a
descent with top `m`, provided `v` is nonempty. -/
private theorem descentTops_cons_of_lt [DecidableEq α] {m : α} {v : List α}
    (hv : ∀ a ∈ v, a < m) :
    (m :: v).descentTops = v.descentTops ∪ (if v = [] then ∅ else {m}) := by
  cases v with
  | nil => rfl
  | cons b v =>
    rw [descentTops_cons_cons, if_pos (hv b (by simp)), if_neg (by simp), Finset.union_comm]

/-- A letter larger than every later letter is not a peak and does not create one. -/
private theorem peakCount_cons_of_lt {m : α} {v : List α} (hv : ∀ a ∈ v, a < m) :
    (m :: v).peakCount = v.peakCount := by
  match v with
  | [] => rfl
  | [b] => rw [peakCount_of_length_le (by simp), peakCount_of_length_le (by simp)]
  | b :: c :: l =>
    rw [peakCount_cons_cons_cons, if_neg, zero_add]
    rintro ⟨h, -⟩
    exact lt_asymm h (hv b (by simp))

/-- Splitting a list at a letter `m` exceeding every other letter: the position of `m` is a peak
exactly when both sides are nonempty, and the other peaks are those of the two sides. -/
private theorem peakCount_append_cons {m : α} {u v : List α} (hu : ∀ a ∈ u, a < m)
    (hv : ∀ a ∈ v, a < m) :
    (u ++ m :: v).peakCount =
      u.peakCount + v.peakCount + (if u ≠ [] ∧ v ≠ [] then 1 else 0) := by
  induction u with
  | nil => simp [peakCount_cons_of_lt hv, peakCount_of_length_le (l := ([] : List α))]
  | cons a t ih =>
    have ih := ih (fun x hx => hu x (by simp [hx]))
    match t, ih with
    | [], _ =>
      rw [peakCount_of_length_le (l := [a]) (by simp)]
      match v, hv with
      | [], _ => rfl
      | c :: l, hv =>
        simp only [List.nil_append, List.cons_append]
        rw [peakCount_cons_cons_cons, if_pos ⟨hu a (by simp), hv c (by simp)⟩,
          peakCount_cons_of_lt hv]
        simp
        omega
    | [b], ih =>
      simp only [List.cons_append, List.nil_append] at ih ⊢
      rw [peakCount_cons_cons_cons, if_neg (fun h => lt_asymm h.2 (hu b (by simp))), ih,
        peakCount_of_length_le (l := [a, b]) (by simp),
        peakCount_of_length_le (l := [b]) (by simp)]
      simp
    | b :: c :: w, ih =>
      simp only [List.cons_append] at ih ⊢
      rw [peakCount_cons_cons_cons, ih, peakCount_cons_cons_cons]
      simp
      omega

/-- A right fold of `max` over `a :: l` is the maximum `m` of `a :: l`. -/
private theorem foldr_max_eq {α : Type*} [LinearOrder α] {a m : α} {l : List α}
    (hm : m ∈ a :: l) (hle : ∀ x ∈ a :: l, x ≤ m) : l.foldr max a = m := by
  refine le_antisymm ?_ ?_
  · clear hm
    induction l <;> simp_all
  · clear hle
    induction l with
    | nil => simp_all
    | cons b l ih =>
      simp only [List.mem_cons, List.foldr_cons, le_max_iff] at *
      rcases hm with h | rfl | h
      · exact .inr (ih (.inl h))
      · exact .inl le_rfl
      · exact .inr (ih (.inr h))

/-- The stack-sorting map splits a list at its maximum `m` when `m` follows only smaller
entries: `s(L m R) = s(L) s(R) m`. -/
private theorem stackSort_append_cons {α : Type*} [LinearOrder α] {L R : List α} {m : α}
    (hL : ∀ x ∈ L, x < m) (hR : ∀ x ∈ R, x ≤ m) :
    (L ++ m :: R).stackSort = L.stackSort ++ R.stackSort ++ [m] := by
  obtain ⟨a, l, hal⟩ : ∃ a l, L ++ m :: R = a :: l := by
    cases L with
    | nil => exact ⟨m, R, rfl⟩
    | cons a L => exact ⟨a, L ++ m :: R, rfl⟩
  have hf : l.foldr max a = m := foldr_max_eq (by simp [← hal]) <| hal ▸ by
    simpa [or_imp, forall_and] using ⟨fun x hx => (hL x hx).le, hR⟩
  have hidx : (L ++ m :: R).idxOf m = L.length := by
    rw [List.idxOf_append_of_notMem (fun h => lt_irrefl _ (hL m h))]
    simp
  rw [hal, List.stackSort.eq_2, hf, ← hal, hidx, List.take_left, ← List.drop_drop,
    List.drop_left]
  rfl

end List

namespace BinaryTree

/-! ### The entries of the inorder reading -/

section Inorder

variable {α : Type*}

/-- The entries of the inorder reading of any tree are exactly its labels. -/
private theorem toFinset_inorder [DecidableEq α] (T : BinaryTree α) :
    T.inorder.toFinset = T.labels := by
  induction T with
  | nil => rfl
  | node m l r ihl ihr =>
    simp only [inorder, labels, List.toFinset_append, List.toFinset_cons, ihl, ihr]
    ext
    simp

private theorem mem_inorder [DecidableEq α] {T : BinaryTree α} {a : α} :
    a ∈ T.inorder ↔ a ∈ T.labels := by
  rw [← toFinset_inorder, List.mem_toFinset]

private theorem inorder_eq_nil {T : BinaryTree α} : T.inorder = [] ↔ T = .nil := by
  cases T <;> simp [inorder]

/-- The inorder reading of a decreasing tree has no repeated entries. -/
private theorem nodup_inorder [DecidableEq α] [Preorder α] {T : BinaryTree α}
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

/-- Every non-root entry of the inorder reading of a decreasing tree is below the root. -/
private theorem lt_root [DecidableEq α] [LT α] {m a : α} {l r : BinaryTree α}
    (hd : (node m l r).IsDecreasing) (ha : a ∈ l.inorder ∨ a ∈ r.inorder) : a < m :=
  hd.2.2.2 a (by simpa [mem_inorder] using ha)

/-- The root of a decreasing tree is the largest entry of its inorder reading. -/
private theorem le_root [DecidableEq α] [Preorder α] {m a : α} {l r : BinaryTree α}
    (hd : (node m l r).IsDecreasing) (ha : a ∈ (node m l r).inorder) : a ≤ m := by
  rw [inorder, List.mem_append, List.mem_cons] at ha
  rcases ha with ha | rfl | ha
  · exact (lt_root hd (.inl ha)).le
  · exact le_rfl
  · exact (lt_root hd (.inr ha)).le

/-- A decreasing tree is determined by its inorder reading. -/
private theorem inorder_injective [DecidableEq α] [PartialOrder α] {T T' : BinaryTree α}
    (hT : T.IsDecreasing) (hT' : T'.IsDecreasing) (h : T.inorder = T'.inorder) : T = T' := by
  induction T generalizing T' with
  | nil => cases T' <;> simp_all [inorder]
  | node m l r ihl ihr =>
    cases T' with
    | nil => simp [inorder] at h
    | node m' l' r' =>
      obtain rfl : m = m' :=
        le_antisymm (le_root hT' (h ▸ by simp [inorder])) (le_root hT (h ▸ by simp [inorder]))
      obtain ⟨hl, -, hr⟩ := (List.append_cons_inj_of_notMem
        (fun hm => (lt_root hT (.inl hm)).false) (fun hm => (lt_root hT (.inr hm)).false)).1 h
      rw [ihl hT.1 hT'.1 hl, ihr hT.2.1 hT'.2.1 hr]

/-- Every list of distinct entries is the inorder reading of a decreasing tree: split it at its
maximum and recurse on the two sides. -/
private theorem exists_inorder_eq [LinearOrder α] (σ : List α) (hσ : σ.Nodup) :
    ∃ T : BinaryTree α, T.IsDecreasing ∧ T.inorder = σ := by
  rcases eq_or_ne σ [] with rfl | hne
  · exact ⟨nil, trivial, rfl⟩
  have hpos := List.length_pos_iff.2 hne
  set m := σ.maximum_of_length_pos hpos
  obtain ⟨L, R, hLR⟩ := List.append_of_mem (σ.maximum_of_length_pos_mem hpos)
  have hle : ∀ a ∈ L ++ m :: R, a ≤ m :=
    hLR ▸ fun a ha => List.le_maximum_of_length_pos_of_mem ha hpos
  have : L.length < σ.length := by
    rw [hLR]
    simp
  have : R.length < σ.length := by
    rw [hLR]
    simp
    omega
  rw [hLR, List.nodup_middle, List.nodup_cons, List.nodup_append'] at hσ
  obtain ⟨hm, hL, hR, hdisj⟩ := hσ
  obtain ⟨TL, hTL, rfl⟩ := exists_inorder_eq L hL
  obtain ⟨TR, hTR, rfl⟩ := exists_inorder_eq R hR
  refine ⟨node m TL TR, ⟨hTL, hTR, ?_, fun a ha => ?_⟩, hLR.symm⟩
  · rwa [← toFinset_inorder, ← toFinset_inorder, List.disjoint_toFinset_iff_disjoint]
  · rw [Finset.mem_union, ← mem_inorder, ← mem_inorder] at ha
    exact (hle a (List.mem_append.2 (ha.imp_right (.tail _)))).lt_of_ne
      (by rintro rfl; exact hm (List.mem_append.2 ha))
termination_by σ.length

end Inorder

/-! ### The inorder reading as a bijection onto words -/

/-- The inorder reading of a decreasing binary plane tree on a finite set `A` of positive
integers is a word whose set of letters is `A`. -/
@[lognarayana "lem_inorder_word"]
public theorem isWord_inorder_of_mem_decreasingTrees {A : Finset ℕ} (hA : ∀ a ∈ A, 0 < a)
    {T : BinaryTree ℕ} (hT : T ∈ decreasingTrees A) :
    IsWord T.inorder ∧ T.inorder.letters = A := by
  have hlet : T.inorder.letters = A := (toFinset_inorder T).trans hT.2
  exact ⟨⟨nodup_inorder hT.1, fun a ha => hA a (hlet ▸ List.mem_toFinset.2 ha)⟩, hlet⟩

/-- For a finite set `A` of positive integers, the inorder reading is a bijection from the
decreasing binary plane trees with label set `A` onto the words with set of letters `A`. -/
@[lognarayana "lem_inorder_bijective_on"]
public theorem bijOn_inorder_decreasingTrees (A : Finset ℕ) (hA : ∀ a ∈ A, 0 < a) :
    Set.BijOn inorder (decreasingTrees A) {σ | σ ∈ words ∧ σ.letters = A} := by
  refine ⟨fun T hT => isWord_inorder_of_mem_decreasingTrees hA hT,
    fun T hT T' hT' h => inorder_injective hT.1 hT'.1 h, ?_⟩
  rintro σ ⟨hσ, hlet⟩
  obtain ⟨T, hT, rfl⟩ := exists_inorder_eq σ hσ.1
  exact ⟨T, ⟨hT, (toFinset_inorder T).symm.trans hlet⟩, rfl⟩

/-- `S_n` is the set of words whose set of letters is `[n]`: the length condition is implied. -/
private theorem permWords_eq (n : ℕ) :
    permWords n = {σ | σ ∈ words ∧ σ.letters = Finset.Icc 1 n} := by
  ext σ
  refine ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, ?_, h.2⟩⟩
  simpa [List.letters, List.toFinset_card_of_nodup h.1.1] using congrArg Finset.card h.2

/-- For every `n`, the inorder reading is a bijection from the decreasing binary plane trees
with label set `[n] = {1, …, n}` onto the permutations `S_n` in one-line notation. -/
@[lognarayana "lem_inorder_bijective"]
public theorem bijOn_inorder_decreasingTrees_Icc (n : ℕ) :
    Set.BijOn inorder (decreasingTrees (Finset.Icc 1 n)) (permWords n) := by
  rw [permWords_eq]
  exact bijOn_inorder_decreasingTrees _ fun a ha => (Finset.mem_Icc.mp ha).1

/-! ### Ascent tops, descent tops and peaks of the inorder reading -/

section Statistics

variable {α : Type*} [Preorder α] [DecidableEq α] [DecidableRel (α := α) (· < ·)]

/-- For a decreasing binary plane tree `T` on `A`, the ascent tops of the inorder reading of
`T` are the labels of the vertices of `T` having a left child: `AT(I(T)) = LC(T)`. -/
@[lognarayana "lem_ascent_top_iff_left_child"]
public theorem ascentTops_inorder_of_mem_decreasingTrees {A : Finset α} {T : BinaryTree α}
    (hT : T ∈ decreasingTrees A) :
    T.inorder.ascentTops = T.leftChildLabels := by
  obtain ⟨hT, -⟩ := hT
  induction T with
  | nil => rfl
  | node m l r ihl ihr =>
    obtain ⟨hl, hr, -, hlt⟩ := hT
    simp only [Finset.mem_union] at hlt
    rw [inorder, List.ascentTops_append_cons (fun a ha => hlt a (.inl (mem_inorder.1 ha))),
      List.ascentTops_cons_of_lt (fun a ha => hlt a (.inr (mem_inorder.1 ha))), ihl hl, ihr hr]
    cases l with
    | nil => simp [inorder]
    | node a l' r' =>
      simp only [inorder, leftChildLabels, List.append_eq_nil_iff, reduceCtorEq, and_false,
        if_false]
      exact Finset.union_right_comm _ _ _

/-- For a decreasing binary plane tree `T` on `A`, the descent tops of the inorder reading of
`T` are the labels of the vertices of `T` having a right child: `DT(I(T)) = RC(T)`. -/
@[lognarayana "lem_descent_top_iff_right_child"]
public theorem descentTops_inorder_of_mem_decreasingTrees {A : Finset α} {T : BinaryTree α}
    (hT : T ∈ decreasingTrees A) :
    T.inorder.descentTops = T.rightChildLabels := by
  obtain ⟨hT, -⟩ := hT
  induction T with
  | nil => rfl
  | node m l r ihl ihr =>
    obtain ⟨hl, hr, -, hlt⟩ := hT
    simp only [Finset.mem_union] at hlt
    rw [inorder, List.descentTops_append_cons (fun a ha => hlt a (.inl (mem_inorder.1 ha))),
      List.descentTops_cons_of_lt (fun a ha => hlt a (.inr (mem_inorder.1 ha))), ihl hl,
      ihr hr]
    cases r <;> simp [inorder, Finset.union_assoc]

/-- For a decreasing binary plane tree `T` on `A`, the number of peaks of the inorder reading of
`T` is the number of binary vertices of `T`: `peak(I(T)) = bin(T)`. -/
@[lognarayana "lem_peak_count_eq_binary"]
public theorem peakCount_inorder_of_mem_decreasingTrees {A : Finset α} {T : BinaryTree α}
    (hT : T ∈ decreasingTrees A) :
    T.inorder.peakCount = T.numBinaryNodes := by
  obtain ⟨hT, -⟩ := hT
  induction T with
  | nil => rfl
  | node m l r ihl ihr =>
    obtain ⟨hl, hr, -, hlt⟩ := hT
    simp only [Finset.mem_union] at hlt
    rw [inorder, List.peakCount_append_cons (fun a ha => hlt a (.inl (mem_inorder.1 ha)))
      (fun a ha => hlt a (.inr (mem_inorder.1 ha))), ihl hl, ihr hr]
    simp only [ne_eq, inorder_eq_nil, numBinaryNodes]
    cases l <;> cases r <;> simp

end Statistics

/-! ### Stack-sorting and the postorder reading -/

/-- West's stack-sorting map sends the inorder reading of a decreasing binary plane tree to its
postorder reading: `s(I(T)) = 𝒫(T)` for `T ∈ DBT(A)`. -/
@[lognarayana "lem_stack_sort_tree"]
public theorem stackSort_inorder_of_mem_decreasingTrees {α : Type*} [LinearOrder α]
    {A : Finset α} {T : BinaryTree α} (hT : T ∈ decreasingTrees A) :
    T.inorder.stackSort = T.postorder := by
  obtain ⟨hT, -⟩ := hT
  induction T with
  | nil => simp [inorder, List.stackSort.eq_1]
  | node m l r ihl ihr =>
    obtain ⟨hl, hr, -, hlt⟩ := hT
    simp only [Finset.mem_union] at hlt
    rw [inorder, List.stackSort_append_cons (fun x hx => hlt x (.inl (mem_inorder.1 hx)))
      (fun x hx => (hlt x (.inr (mem_inorder.1 hx))).le), ihl hl, ihr hr, postorder]

/-- The identity `ι_n` lies in `S_n`. -/
private lemma idPermWord_mem_permWords (n : ℕ) : idPermWord n ∈ permWords n := by
  refine ⟨⟨List.nodup_range' .., fun a ha => ?_⟩, by simp [idPermWord], ?_⟩
  · simp [idPermWord, List.mem_range'_1] at ha
    omega
  · ext a
    simp [idPermWord, List.mem_range'_1]
    omega

/-- Membership in `S_n` is being a rearrangement of the identity `ι_n`. -/
private lemma mem_permWords_iff_perm {n : ℕ} {σ : List ℕ} :
    σ ∈ permWords n ↔ σ.Perm (idPermWord n) := by
  have hid := idPermWord_mem_permWords n
  refine ⟨fun hσ => List.perm_of_nodup_nodup_toFinset_eq hσ.1.1 hid.1.1
    (hσ.2.2.trans hid.2.2.symm), fun h => ?_⟩
  exact ⟨⟨h.nodup_iff.2 hid.1.1, fun a ha => hid.1.2 a (h.subset ha)⟩,
    h.length_eq.trans hid.2.1, (List.toFinset_eq_of_perm _ _ h).trans hid.2.2⟩

/-- For `π ∈ S_n`, the fiber `s⁻¹(π)` consists of the `σ ∈ S_n` with `s(σ) = π`. -/
private lemma mem_stackFiber_iff {n : ℕ} {π σ : List ℕ} (hπ : π ∈ permWords n) :
    σ ∈ List.stackFiber π ↔ σ ∈ permWords n ∧ σ.stackSort = π := by
  simp [List.stackFiber, hπ.2.1, mem_permWords_iff_perm]

/-- For `π ∈ S_n`, the inorder reading is a bijection from the decreasing binary plane trees on
`[n]` with postorder reading `π` onto the stack-sorting fiber `s⁻¹(π)`. -/
@[lognarayana "lem_fiber_tree_bijection"]
public theorem bijOn_inorder_postorder_eq_stackFiber {n : ℕ} {π : List ℕ}
    (hπ : π ∈ permWords n) :
    Set.BijOn inorder {T | T ∈ decreasingTrees (Finset.Icc 1 n) ∧ T.postorder = π}
      ↑(List.stackFiber π) := by
  have B := bijOn_inorder_decreasingTrees_Icc n
  refine ⟨fun T hT => ?_, B.injOn.mono fun T hT => hT.1, fun σ hσ => ?_⟩
  · rw [Finset.mem_coe, mem_stackFiber_iff hπ]
    exact ⟨B.mapsTo hT.1, (stackSort_inorder_of_mem_decreasingTrees hT.1).trans hT.2⟩
  · rw [Finset.mem_coe, mem_stackFiber_iff hπ] at hσ
    obtain ⟨T, hT, rfl⟩ := B.surjOn hσ.1
    exact ⟨T, ⟨hT, (stackSort_inorder_of_mem_decreasingTrees hT).symm.trans hσ.2⟩, rfl⟩

/-- The postorder reading is not injective on decreasing trees: there are two distinct trees
`T₁ T₂ ∈ DBT([2])` with `𝒫(T₁) = 𝒫(T₂)`, namely `⟨2; ⟨1; ∅, ∅⟩, ∅⟩` and `⟨2; ∅, ⟨1; ∅, ∅⟩⟩`,
which both read `1 2`. -/
@[lognarayana "lem_postorder_not_injective"]
public theorem exists_ne_postorder_eq_decreasingTrees_Icc_two :
    ∃ T₁ ∈ decreasingTrees (Finset.Icc 1 2 : Finset ℕ),
      ∃ T₂ ∈ decreasingTrees (Finset.Icc 1 2 : Finset ℕ),
        T₁ ≠ T₂ ∧ T₁.postorder = T₂.postorder :=
  ⟨node 2 (node 1 nil nil) nil, ⟨by simp, by decide⟩, node 2 nil (node 1 nil nil),
    ⟨by simp, by decide⟩, by simp, rfl⟩

end BinaryTree

/-! ### The running example `2751364` -/

namespace List

/-- The word `2751364` has exactly two peaks, the entries `7` and `6`: `peak(2751364) = 2`. -/
@[lognarayana "lem_peak_count_example"]
public theorem peakCount_2751364 : peakCount [2, 7, 5, 1, 3, 6, 4] = 2 := by
  decide

/-- West's stack-sorting map on the running example: the maximum `7` splits `2751364` as
`2 · 7 · 51364`, and `s(51364) = 13546`, so `s(2751364) = 2135467`. -/
@[lognarayana "lem_stack_sort_example_tree"]
public theorem stackSort_2751364 :
    ([2, 7, 5, 1, 3, 6, 4] : List ℕ).stackSort = [2, 1, 3, 5, 4, 6, 7] := by
  simp [List.stackSort.eq_2, List.stackSort.eq_1]

end List
