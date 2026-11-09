/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module
public import LogNarayana.StackSorting.StackSort.Defs

/-!
# Words and the stack-sorting map

West's stack-sorting map `s` only reorders the letters of a sequence: `s(σ)` is a rearrangement
of `σ`. Consequently `s` sends `S_n` to itself, and a word sent by `s` to a permutation
`π ∈ S_n` is itself in `S_n`, so the fiber `s⁻¹(π) ⊆ S_n` is the full preimage of `π` among all
words. We also record the worked example `s(416352) = 143256`.

## Main results

* `List.stackSort_perm`: `List.stackSort l` is a permutation of `l`.
* `List.stackSort_example`: `s(416352) = 143256`.
* `stackSort_mem_permWords`: if `σ ∈ S_n`, then `s(σ) ∈ S_n`.
* `List.mem_permWords_of_stackSort_eq`: a word `σ` with `s(σ) = π ∈ S_n` lies in `S_n`, and
  `s⁻¹(π)` is the set of all words `σ` with `s(σ) = π`.

## Implementation notes

The paper states that `s` rearranges its input for words `σ ∈ 𝒲`. The argument (induction on
the decomposition `σ = L m R`) uses neither distinctness nor positivity of the letters, so
`List.stackSort_perm` is stated for an arbitrary list over a linear order. "Rearrangement by a
bijection `τ : [ℓ] → [ℓ]`" is `List.Perm`.

## References

* [LogNarayana], Sections 1 and 2.
-/

namespace List

/-- The right fold of `max` starting at `a` over `l` is a member of `a :: l`. -/
private lemma foldr_max_mem {α : Type*} [LinearOrder α] (a : α) (l : List α) :
    l.foldr max a ∈ a :: l := by
  induction l with
  | nil => simp
  | cons b l ih =>
    rcases max_choice b (l.foldr max a) with h | h <;>
      simp only [foldr_cons, h, mem_cons] at ih ⊢ <;> tauto

/-- Splitting a list at the first occurrence of a member `m` gives
`take p ++ m :: drop (p + 1)`. -/
private lemma take_append_cons_drop_idxOf {α : Type*} [DecidableEq α] {m : α} {l : List α}
    (hm : m ∈ l) : l.take (l.idxOf m) ++ m :: l.drop (l.idxOf m + 1) = l := by
  nth_rw 2 [← getElem_idxOf (idxOf_lt_length_of_mem hm)]
  rw [getElem_cons_drop, take_append_drop]

/-- The stack-sorting map rearranges its input: `stackSort l` is a permutation of `l`, since
`s(L m R) = s(L) s(R) m ~ L R m ~ L m R`. -/
@[lognarayana "lem_stack_sort_rearrangement"]
public theorem stackSort_perm {α : Type*} [LinearOrder α] : ∀ l : List α, l.stackSort ~ l
  | [] => by simp [stackSort]
  | a :: l => by
    have hm := foldr_max_mem a l
    have hlt := idxOf_lt_length_of_mem hm
    rw [stackSort, append_assoc]
    conv_rhs => rw [← take_append_cons_drop_idxOf hm]
    exact ((stackSort_perm _).append ((stackSort_perm _).append_right _)).trans
      ((perm_append_singleton _ _).append_left _)
termination_by l => l.length
decreasing_by all_goals simp only [length_take, length_drop]; omega

/-- The stack-sorting map sends `416352` to `143256`: `s(416352) = s(41) s(352) 6 = 14 · 325 · 6`.
-/
@[lognarayana "lem_stack_sort_example"]
public theorem stackSort_example : stackSort [4, 1, 6, 3, 5, 2] = ([1, 4, 3, 2, 5, 6] : List ℕ) :=
  by simp [stackSort.eq_1, stackSort.eq_2]

end List

/-- Being a word is invariant under rearrangement. -/
private lemma mem_words_of_perm {σ τ : List ℕ} (h : σ.Perm τ) (hτ : τ ∈ words) : σ ∈ words :=
  ⟨h.nodup_iff.2 hτ.1, fun a ha => hτ.2 a (h.subset ha)⟩

/-- A rearrangement of `π ∈ S_n` lies in `S_n`. -/
private lemma mem_permWords_of_perm {n : ℕ} {π σ : List ℕ} (hπ : π ∈ permWords n)
    (h : σ.Perm π) : σ ∈ permWords n :=
  ⟨mem_words_of_perm h hπ.1, h.length_eq.trans hπ.2.1,
    (List.toFinset_eq_of_perm _ _ h).trans hπ.2.2⟩

/-- The identity `ι_n` lies in `S_n`. -/
public lemma idPermWord_mem_permWords (n : ℕ) : idPermWord n ∈ permWords n := by
  refine ⟨⟨List.nodup_range' .., fun a ha => ?_⟩, by simp [idPermWord], ?_⟩
  · simp [idPermWord, List.mem_range'_1] at ha; omega
  · ext a; simp [idPermWord, List.mem_range'_1]; omega

/-- Membership in `S_n` is being a rearrangement of the identity `ι_n`. -/
public lemma mem_permWords_iff_perm {n : ℕ} {σ : List ℕ} :
    σ ∈ permWords n ↔ σ.Perm (idPermWord n) := by
  refine ⟨fun hσ => ?_, mem_permWords_of_perm (idPermWord_mem_permWords n)⟩
  exact List.perm_of_nodup_nodup_toFinset_eq hσ.1.1 (idPermWord_mem_permWords n).1.1
    (hσ.2.2.trans (idPermWord_mem_permWords n).2.2.symm)

/-- The stack-sorting map sends `S_n` to itself: `s(σ)` is a rearrangement of `σ ∈ S_n`. -/
@[lognarayana "lem_stack_sort_perm"]
public theorem stackSort_mem_permWords {n : ℕ} {σ : List ℕ} (hσ : σ ∈ permWords n) :
    σ.stackSort ∈ permWords n :=
  mem_permWords_of_perm hσ σ.stackSort_perm

namespace List

/-- If `π ∈ S_n` and `σ` is any list with `s(σ) = π`, then `σ ∈ S_n`, since `σ` is a rearrangement
of `π`; consequently the stack-sorting fiber `s⁻¹(π)` is the set of all words `σ` with `s(σ) = π`.
-/
@[lognarayana "lem_stack_fiber_in_perm"]
public theorem mem_permWords_of_stackSort_eq {n : ℕ} {π σ : List ℕ} (hπ : π ∈ permWords n)
    (hs : σ.stackSort = π) :
    σ ∈ permWords n ∧ (↑(stackFiber π) : Set (List ℕ)) = {τ | τ ∈ words ∧ τ.stackSort = π} := by
  have hperm {τ : List ℕ} (h : τ.stackSort = π) : τ ∈ permWords n :=
    mem_permWords_of_perm hπ (h ▸ (stackSort_perm τ).symm)
  refine ⟨hperm hs, Set.ext fun τ => ?_⟩
  simp only [stackFiber, Finset.coe_filter, mem_toFinset, mem_permutations, Set.mem_ofPred_eq,
    hπ.2.1, ← mem_permWords_iff_perm]
  exact ⟨fun ⟨h, h'⟩ => ⟨h.1, h'⟩, fun ⟨_, h'⟩ => ⟨hperm h', h'⟩⟩

end List
