/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module
public import LogNarayana.Matroid.Laminar.Defs
import Mathlib.Combinatorics.Matroid.IndepAxioms
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Set.Finite.Lemmas

/-!
# Laminar capacities define a matroid

Let `𝒜 = (A_k)_{k ∈ K}` be a laminar family of subsets and `c : K → ℕ` a family of capacities.
On a finite ground set `E`, the capacity-bounded sets
`𝕀_{𝒜,c} = {I ⊆ E : |I ∩ A_k| ≤ c(k) for every k}` are the independent sets of a matroid on `E`,
a *laminar matroid*; this is due to Fife and Oxley.

The heart of the matter is the augmentation axiom: if `I, J ∈ 𝕀_{𝒜,c}` with `|I| < |J|`, then
some `e ∈ J \ I` has `I ∪ {e} ∈ 𝕀_{𝒜,c}`. Suppose instead every `e ∈ J \ I` has a *tight*
index `k`, i.e. `e ∈ A k` and `|I ∩ A k| = c k`. Choosing for each `e` a tight index whose trace
`A k ∩ E` is as large as possible, laminarity makes these traces pairwise equal or disjoint.
Counting `I` and `J` blockwise on these traces and identically off them gives `|J| ≤ |I|`.
The remaining independence axioms are immediate.

## Main results

* `capacityBoundedSets_augment`: the augmentation property of `capacityBoundedSets E A c` for a
  laminar family `A`.
* `IsLaminar.exists_matroid_indep_iff`: for a finite `E` and a laminar family `A`, there is a
  matroid `M` with ground set `E` whose independent sets are exactly `capacityBoundedSets E A c`.

## Implementation notes

Cardinality is `Set.encard`, as in `capacityBoundedSets`. The paper takes the index set `K`
finite and every `A_k` contained in `E`. Neither is needed: only the traces `A_k ∩ E` matter for
subsets of `E`, these are again laminar, and a finite `E` has finitely many of them. So `ι` is
arbitrary and the `A k` are arbitrary subsets of `α`. For the same reason the tight index in the
proof of augmentation is maximised by the size of its trace on `E` rather than of `A k` itself.

The characterisation of independent sets is stated for every `I : Set α`; for `I ⊄ E` both sides
are false, so this is equivalent to the paper's quantification over `I ⊆ E`.

## References

* [LogNarayana], Section 4; [FifeOxley].
-/


open Finset

open Classical in
/-- Counting with blocks: if every `e ∈ J \ I` lies in a block `T e`, the blocks are pairwise
equal or disjoint, and each block meets `J` at most as often as it meets `I`, then `#J ≤ #I`. -/
private lemma card_le_of_blocks {α : Type*} (I J : Finset α) (T : α → Set α)
    (h1 : ∀ e ∈ J \ I, e ∈ T e)
    (h2 : ∀ e ∈ J \ I, #(J.filter (· ∈ T e)) ≤ #(I.filter (· ∈ T e)))
    (h3 : ∀ e ∈ J \ I, ∀ e' ∈ J \ I, (T e ∩ T e').Nonempty → T e = T e') :
    #J ≤ #I := by
  set 𝒰 : Finset (Set α) := (J \ I).image T with h𝒰
  have hdisj : ∀ s : Finset α,
      (𝒰 : Set (Set α)).PairwiseDisjoint (fun U => s.filter (· ∈ U)) := by
    intro s U hU U' hU' hne
    simp only [h𝒰, coe_image, Set.mem_image, mem_coe] at hU hU'
    obtain ⟨e, he, rfl⟩ := hU
    obtain ⟨e', he', rfl⟩ := hU'
    rw [Function.onFun, Finset.disjoint_left]
    intro x hx hx'
    simp only [mem_filter] at hx hx'
    exact hne (h3 e he e' he' ⟨x, hx.2, hx'.2⟩)
  have hsum : ∀ s : Finset α, #(s.filter (fun x => ∃ U ∈ 𝒰, x ∈ U)) =
      ∑ U ∈ 𝒰, #(s.filter (· ∈ U)) := by
    intro s
    rw [← card_biUnion (hdisj s)]
    congr 1
    ext x
    simp only [mem_filter, mem_biUnion]
    tauto
  have hin : #(J.filter (fun x => ∃ U ∈ 𝒰, x ∈ U)) ≤
      #(I.filter (fun x => ∃ U ∈ 𝒰, x ∈ U)) := by
    rw [hsum, hsum]
    refine sum_le_sum fun U hU => ?_
    obtain ⟨e, he, rfl⟩ := mem_image.1 hU
    exact h2 e he
  have hout : #(J.filter (fun x => ¬ ∃ U ∈ 𝒰, x ∈ U)) ≤
      #(I.filter (fun x => ¬ ∃ U ∈ 𝒰, x ∈ U)) := by
    refine card_le_card fun x hx => ?_
    simp only [mem_filter] at hx ⊢
    refine ⟨?_, hx.2⟩
    by_contra hxI
    have hx' : x ∈ J \ I := mem_sdiff.2 ⟨hx.1, hxI⟩
    exact hx.2 ⟨T x, mem_image_of_mem T hx', h1 x hx'⟩
  rw [← card_filter_add_card_filter_not (s := J) (fun x => ∃ U ∈ 𝒰, x ∈ U),
    ← card_filter_add_card_filter_not (s := I) (fun x => ∃ U ∈ 𝒰, x ∈ U)]
  omega

open Classical in
/-- For `s ⊆ E`, the size of `s ∩ A` is the number of elements of `s` in the trace `A ∩ E`. -/
private lemma encard_inter_eq {α : Type*} {E : Set α} (A : Set α) (s : Finset α)
    (hs : (s : Set α) ⊆ E) : ((s : Set α) ∩ A).encard = #(s.filter (· ∈ A ∩ E)) := by
  rw [← Set.encard_coe_eq_coe_finsetCard]
  congr 1
  ext x
  simp only [Set.mem_inter_iff, mem_coe, coe_filter, Set.mem_ofPred_eq]
  exact ⟨fun ⟨hx, hA⟩ => ⟨hx, hA, hs hx⟩, fun ⟨hx, hA, _⟩ => ⟨hx, hA⟩⟩

/-- If `insert e I` violates a capacity although `I` does not, the violated capacity is *tight*:
`e ∈ A k` and `|I ∩ A k| = c k`. -/
private lemma exists_tight {ι α : Type*} {E : Set α} {A : ι → Set α} {c : ι → ℕ} {I : Set α}
    {e : α} (hI : I ∈ capacityBoundedSets E A c) (heE : e ∈ E) (heI : e ∉ I)
    (h : insert e I ∉ capacityBoundedSets E A c) : ∃ k, e ∈ A k ∧ (I ∩ A k).encard = c k := by
  simp only [capacityBoundedSets, Set.mem_ofPred_eq, not_and, not_forall, not_le] at h
  obtain ⟨k, hk⟩ := h (Set.insert_subset heE hI.1)
  have heA : e ∈ A k := by
    by_contra heA
    rw [Set.insert_inter_of_notMem heA] at hk
    exact (hI.2 k).not_gt hk
  rw [Set.insert_inter_of_mem heA, Set.encard_insert_of_notMem (fun h => heI h.1)] at hk
  exact ⟨k, heA, le_antisymm (hI.2 k) ((ENat.lt_add_one_iff' (by simp)).1 hk)⟩

/-- Among the indices satisfying `P`, one has a trace on the finite set `E` of maximal size. -/
private lemma exists_max_trace {ι α : Type*} {E : Set α} (hE : E.Finite) (A : ι → Set α)
    {P : ι → Prop} (hP : ∃ k, P k) :
    ∃ k, P k ∧ ∀ k', P k' → (A k' ∩ E).ncard ≤ (A k ∩ E).ncard := by
  obtain ⟨-, ⟨k, hk, rfl⟩, hmax⟩ := Set.exists_max_image ((fun k => A k ∩ E) '' {k | P k})
    Set.ncard (hE.finite_subsets.subset (by rintro _ ⟨k, -, rfl⟩; exact Set.inter_subset_right))
    (Set.Nonempty.image _ hP)
  exact ⟨k, hk, fun k' hk' => hmax _ (Set.mem_image_of_mem _ hk')⟩

/-- **Augmentation for laminar capacity-bounded sets.** For a laminar family `A` on a finite
ground set `E` with capacities `c`, if `I, J ∈ capacityBoundedSets E A c` and
`I.encard < J.encard`, then some `e ∈ J \ I` has `insert e I ∈ capacityBoundedSets E A c`. -/
@[lognarayana "lem_laminar_indep_augment"]
public theorem capacityBoundedSets_augment {ι α : Type*} {E : Set α} (hE : E.Finite)
    {A : ι → Set α} (hA : IsLaminar A) (c : ι → ℕ) {I J : Set α}
    (hI : I ∈ capacityBoundedSets E A c) (hJ : J ∈ capacityBoundedSets E A c)
    (hIJ : I.encard < J.encard) :
    ∃ e ∈ J \ I, insert e I ∈ capacityBoundedSets E A c := by
  classical
  by_contra hcon
  push Not at hcon
  -- for each `e ∈ J \ I`, a tight index `k e` containing `e` with maximal trace
  have hmax : ∀ e ∈ J \ I, ∃ k, (e ∈ A k ∧ (I ∩ A k).encard = c k) ∧
      ∀ k', e ∈ A k' ∧ (I ∩ A k').encard = c k' → (A k' ∩ E).ncard ≤ (A k ∩ E).ncard :=
    fun e he => exists_max_trace hE A (exists_tight hI (hJ.1 he.1) he.2 (hcon e he))
  obtain ⟨e₀, he₀⟩ := Set.sdiff_nonempty.2 fun h => (Set.encard_le_encard h).not_gt hIJ
  have : Nonempty ι := ⟨(hmax e₀ he₀).choose⟩
  choose! k hk hkmax using hmax
  -- a tight index containing `A (k e)` has the same trace
  have hnest : ∀ e ∈ J \ I, ∀ k', (I ∩ A k').encard = c k' → A (k e) ⊆ A k' →
      A (k e) ∩ E = A k' ∩ E := fun e he k' hc hsub =>
    Set.eq_of_subset_of_ncard_le (Set.inter_subset_inter_left _ hsub)
      (hkmax e he k' ⟨hsub (hk e he).1, hc⟩) (hE.subset Set.inter_subset_right)
  obtain ⟨If, rfl⟩ := (hE.subset hI.1).exists_finset_coe
  obtain ⟨Jf, rfl⟩ := (hE.subset hJ.1).exists_finset_coe
  rw [Set.encard_coe_eq_coe_finsetCard, Set.encard_coe_eq_coe_finsetCard, Nat.cast_lt] at hIJ
  have hD : ∀ {e}, e ∈ Jf \ If → e ∈ (Jf : Set α) \ If := fun he => by simpa using he
  refine (card_le_of_blocks If Jf (fun e => A (k e) ∩ E) (fun e he => ?_) (fun e he => ?_)
    (fun e he e' he' hmeet => ?_)).not_gt hIJ
  · exact ⟨(hk e (hD he)).1, hJ.1 (hD he).1⟩
  · have hJk := hJ.2 (k e)
    rw [encard_inter_eq _ _ hJ.1] at hJk
    have hc := (hk e (hD he)).2
    rw [encard_inter_eq _ _ hI.1] at hc
    convert (Nat.cast_le (α := ℕ∞)).1 (hJk.trans hc.ge)
  · obtain ⟨x, hx, hx'⟩ := hmeet
    rcases hA (k e) (k e') ⟨x, hx.1, hx'.1⟩ with hsub | hsub
    · exact hnest e (hD he) _ (hk e' (hD he')).2 hsub
    · exact (hnest e' (hD he') _ (hk e (hD he)).2 hsub).symm

/-- **Fife–Oxley.** For a laminar family `A` of subsets and capacities `c`, the capacity-bounded
subsets of a finite set `E` are the independent sets of a matroid on `E`. -/
@[lognarayana "lem_laminar_matroid_exists"]
public theorem IsLaminar.exists_matroid_indep_iff {ι α : Type*} {E : Set α} (hE : E.Finite)
    {A : ι → Set α} (hA : IsLaminar A) (c : ι → ℕ) :
    ∃ M : Matroid α, M.E = E ∧ ∀ I : Set α, M.Indep I ↔ I ∈ capacityBoundedSets E A c := by
  refine ⟨(IndepMatroid.ofFinite hE (· ∈ capacityBoundedSets E A c) ?_ ?_ ?_ ?_).matroid,
    rfl, fun I => Iff.rfl⟩
  · exact ⟨Set.empty_subset _, fun k => by simp⟩
  · rintro I J ⟨hJE, hJc⟩ hIJ
    exact ⟨hIJ.trans hJE, fun k =>
      (Set.encard_le_encard (Set.inter_subset_inter_left _ hIJ)).trans (hJc k)⟩
  · intro I J hI hJ hIJ
    obtain ⟨e, ⟨heJ, heI⟩, he⟩ := capacityBoundedSets_augment hE hA c hI hJ <| by
      rwa [← (hE.subset hI.1).cast_ncard_eq, ← (hE.subset hJ.1).cast_ncard_eq, Nat.cast_lt]
    exact ⟨e, heJ, heI, he⟩
  · exact fun I hI => hI.1
