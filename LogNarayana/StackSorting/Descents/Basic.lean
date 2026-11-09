/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module
public import LogNarayana.StackSorting.Descents.Defs

/-!
# The number of descent tops and ascent tops of a word

For a word `σ` of length `ℓ` (a sequence with no repeated letters), the descent at position `i`
is sent to the letter `σᵢ` and the ascent at position `i` to the letter `σᵢ₊₁`; both maps are
injective because letters are not repeated. Hence `|DT(σ)| = des(σ)`. Over a linear order each of
the `ℓ - 1` consecutive pairs is either an ascent or a descent, so `|AT(σ)| = ℓ - 1 - des(σ)`.

## Main results

* `card_descentTops`: for a list `σ` without repeated entries,
  `σ.descentTops.card = σ.numDescents`.
* `card_ascentTops`: for a list `σ` without repeated entries over a linear order,
  `σ.ascentTops.card = σ.length - 1 - σ.numDescents`.

## Implementation notes

The paper's words are lists of positive integers without repeated letters. The statements are
made for any duplicate-free list (`List.Nodup`); positivity of the letters plays no role. Without
distinctness both fail: `[2, 1, 2, 1]` has two descents but one descent top. The descent-top
count needs only a decidable `<`; the ascent-top count needs a linear order, so that every
consecutive pair is comparable. The paper's hypothesis `ℓ ≥ 1` is dropped: for the empty list
both sides are `0` (subtraction on `ℕ` is truncated, and `des(σ) ≤ ℓ - 1` always, so no
truncation occurs for `ℓ ≥ 1`).

## References

* [LogNarayana], Section 2.
-/


namespace List

section LT

variable {α : Type*} [DecidableEq α] [LT α] [DecidableRel (α := α) (· < ·)]

/-- `a` is a descent top of `σ` iff it is the entry at the (`0`-based) position `i - 1` for some
descent `i` of `σ`. -/
private lemma mem_descentTops_iff {σ : List α} {a : α} :
    a ∈ σ.descentTops ↔ ∃ i ∈ σ.descentSet, ∃ h : i - 1 < σ.length, σ[i - 1] = a := by
  simp only [descentTops, descentSet, mem_toFinset, mem_map, mem_filter,
    decide_eq_true_eq, Finset.mem_filter, Finset.mem_Ico]
  constructor
  · rintro ⟨_, ⟨hp, hlt⟩, rfl⟩
    obtain ⟨j, hj, rfl⟩ := mem_iff_getElem.1 hp
    simp only [length_zip, length_tail, getElem_zip, getElem_tail] at hj hlt ⊢
    exact ⟨j + 1, ⟨⟨by omega, by omega⟩, by omega, by simpa using hlt⟩, by omega, by simp⟩
  · rintro ⟨i, ⟨⟨h1, h2⟩, h3, h4⟩, h5, rfl⟩
    refine ⟨_, ⟨mem_iff_getElem.2 ⟨i - 1, by simp; omega, rfl⟩, ?_⟩, by simp⟩
    simpa [getElem_zip, show i - 1 + 1 = i by omega] using h4

/-- `a` is an ascent top of `σ` iff it is the entry at a (`0`-based) position `i ≥ 1` with
`σ[i - 1] < σ[i]`. -/
private lemma mem_ascentTops_iff {σ : List α} {a : α} :
    a ∈ σ.ascentTops ↔ ∃ i, 1 ≤ i ∧ ∃ h : i < σ.length, σ[i - 1] < σ[i] ∧ σ[i] = a := by
  simp only [ascentTops, mem_toFinset, mem_map, mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨_, ⟨hp, hlt⟩, rfl⟩
    obtain ⟨j, hj, rfl⟩ := mem_iff_getElem.1 hp
    simp only [length_zip, length_tail, getElem_zip, getElem_tail] at hj hlt ⊢
    exact ⟨j + 1, by omega, by omega, by simpa using hlt, rfl⟩
  · rintro ⟨i, h1, h2, h4, rfl⟩
    refine ⟨_, ⟨mem_iff_getElem.2 ⟨i - 1, by simp; omega, rfl⟩, ?_⟩, by
      simp [show i - 1 + 1 = i by omega]⟩
    simpa [getElem_zip, show i - 1 + 1 = i by omega] using h4

/-- For a list with distinct entries, the ascent tops are counted by the ascents: the positions
`i ∈ [ℓ - 1]` with `σ[i - 1] < σ[i]` (`0`-based), via `i ↦ σ[i]`. -/
private lemma card_ascentTops_eq_card_ascents {σ : List α} (hσ : σ.Nodup) :
    σ.ascentTops.card =
      {i ∈ Finset.Ico 1 σ.length | ∃ h : i < σ.length, σ[i - 1] < σ[i]}.card := by
  refine (Finset.card_bij (fun i hi => σ[i]'(Finset.mem_Ico.1 (Finset.mem_filter.1 hi).1).2)
    (fun i hi => ?_) (fun i _ j _ hij => hσ.getElem_inj_iff.1 hij) (fun a ha => ?_)).symm
  · obtain ⟨hi, h, hlt⟩ := Finset.mem_filter.1 hi
    exact mem_ascentTops_iff.2 ⟨i, (Finset.mem_Ico.1 hi).1, h, hlt, rfl⟩
  · obtain ⟨i, h1, h2, h3, rfl⟩ := mem_ascentTops_iff.1 ha
    exact ⟨i, by simp [h1, h2, h3], rfl⟩

end LT

end List

section

variable {α : Type*} [DecidableEq α] [LT α] [DecidableRel (α := α) (· < ·)]

/-- For a list `σ` without repeated entries (in particular a word), the number of descent tops
equals the number of descents: `|DT(σ)| = des(σ)`. -/
@[lognarayana "lem_card_descent_tops"]
public theorem card_descentTops {σ : List α} (hσ : σ.Nodup) :
    σ.descentTops.card = σ.numDescents := by
  have hlen {i} (hi : i ∈ σ.descentSet) : i - 1 < σ.length := by
    simp only [List.descentSet, Finset.mem_filter, Finset.mem_Ico] at hi
    omega
  refine (Finset.card_bij (fun i hi => σ[i - 1]'(hlen hi))
    (fun i hi => List.mem_descentTops_iff.2 ⟨i, hi, hlen hi, rfl⟩) (fun i hi j hj hij => ?_)
    (fun a ha => ?_)).symm
  · simp only [List.descentSet, Finset.mem_filter, Finset.mem_Ico] at hi hj
    have := hσ.getElem_inj_iff.1 hij
    omega
  · obtain ⟨i, hi, _, rfl⟩ := List.mem_descentTops_iff.1 ha
    exact ⟨i, hi, rfl⟩

end

/-- For a list `σ` without repeated entries (in particular a word) of length `ℓ`, the number of
ascent tops is `|AT(σ)| = ℓ - 1 - des(σ)`. -/
@[lognarayana "lem_card_ascent_tops"]
public theorem card_ascentTops {α : Type*} [LinearOrder α] {σ : List α} (hσ : σ.Nodup) :
    σ.ascentTops.card = σ.length - 1 - σ.numDescents := by
  have hsplit := Finset.card_filter_add_card_filter_not (s := Finset.Ico 1 σ.length)
    fun i => ∃ h : i < σ.length, σ[i] < σ[i - 1]
  -- Distinct entries over a linear order: a position that is not a descent is an ascent.
  rw [Finset.filter_congr (p := fun i => ¬∃ h : i < σ.length, σ[i] < σ[i - 1])
    (q := fun i => ∃ h : i < σ.length, σ[i - 1] < σ[i]) fun i hi => by
    have hi := Finset.mem_Ico.1 hi
    simp only [hi.2, exists_true_left, not_lt]
    exact ⟨fun h => h.lt_of_ne fun e => absurd (hσ.getElem_inj_iff.1 e) (by omega), le_of_lt⟩,
    ← List.card_ascentTops_eq_card_ascents hσ, Nat.card_Ico] at hsplit
  simp only [List.numDescents, List.descentSet]
  omega
