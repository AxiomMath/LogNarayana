/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module
public import LogNarayana.Polynomial.LogConcave.Defs

/-!
# Log-concave and ultra-log-concave polynomials

A real polynomial `f` is ultra-log-concave of order `d` if it has degree at most `d` and the
normalized coefficients `([x^j] f / (d choose j))_{j=0}^{d}` form a nonnegative log-concave
sequence without internal zeros. This file proves two basic facts about this notion.

Since the binomial coefficients are themselves log-concave,
`(d choose j) (d choose (j + 2)) ≤ (d choose (j + 1))²`, multiplying the normalized coefficients
back by them shows that an ultra-log-concave polynomial is log-concave.

The normalized coefficient sequence of `x f` of order `d + 1` is `0` at index `0` and
`(j + 1) / (d + 1)` times the normalized sequence of `f` of order `d` at index `j + 1`. Shifting a
sequence one place to the right and weighting it termwise by a positive log-concave sequence
preserves log-concavity and the absence of internal zeros, so `x f` is ultra-log-concave of order
`d + 1`.

## Main results

* `Polynomial.IsUltraLogConcave.isLogConcave`: an ultra-log-concave polynomial is log-concave.
* `Polynomial.IsUltraLogConcave.mul_X`: if `f` is ultra-log-concave of order `d`, then `f * X`
  is ultra-log-concave of order `d + 1`.

## References

* [LogNarayana], Introduction.
-/

open Polynomial

/-- The binomial coefficients `(d choose j)_j` are log-concave. -/
private lemma choose_mul_choose_add_two_le (d j : ℕ) :
    d.choose j * d.choose (j + 2) ≤ d.choose (j + 1) ^ 2 := by
  rcases Nat.lt_or_ge d (j + 2) with h | h
  · simp [Nat.choose_eq_zero_of_lt h]
  refine Nat.le_of_mul_le_mul_right ?_
    (Nat.mul_pos (by omega : 0 < j + 2) (by omega : 0 < d - j))
  calc d.choose j * d.choose (j + 2) * ((j + 2) * (d - j))
      = (d.choose (j + 2) * (j + 2)) * (d.choose j * (d - j)) := by ring
    _ = d.choose (j + 1) ^ 2 * ((d - (j + 1)) * (j + 1)) := by
        rw [Nat.choose_succ_right_eq d (j + 1), ← Nat.choose_succ_right_eq d j]
        ring
    _ ≤ d.choose (j + 1) ^ 2 * ((d - j) * (j + 2)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) (by omega))
    _ = _ := by ring

/-- A termwise product of two log-concave triples, the second with nonnegative outer product,
is log-concave. -/
private lemma mul_mul_mul_le_sq {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    {c₀ c₁ c₂ a₀ a₁ a₂ : R} (hc : c₀ * c₂ ≤ c₁ ^ 2) (ha : a₀ * a₂ ≤ a₁ ^ 2)
    (ha0 : 0 ≤ a₀ * a₂) : c₀ * a₀ * (c₂ * a₂) ≤ (c₁ * a₁) ^ 2 :=
  calc c₀ * a₀ * (c₂ * a₂) = c₀ * c₂ * (a₀ * a₂) := by ring
    _ ≤ c₁ ^ 2 * a₁ ^ 2 := mul_le_mul hc ha ha0 (sq_nonneg _)
    _ = (c₁ * a₁) ^ 2 := by ring

/-- An ultra-log-concave polynomial of any order `d` is log-concave. -/
@[lognarayana "lem_ulc_log_concave"]
public theorem Polynomial.IsUltraLogConcave.isLogConcave {d : ℕ} {f : ℝ[X]}
    (hf : f.IsUltraLogConcave d) : f.IsLogConcave := by
  obtain ⟨hdeg, ⟨hnn, hlc⟩, _⟩ := hf
  have hzero : ∀ j, d < j → f.coeff j = 0 := fun j hj =>
    coeff_eq_zero_of_natDegree_lt (hdeg.trans_lt hj)
  have hb : ∀ j ≤ d, f.coeff j = (d.choose j : ℝ) * (f.coeff j / d.choose j) := fun j hj =>
    (mul_div_cancel₀ _ (by exact_mod_cast (Nat.choose_pos hj).ne')).symm
  refine ⟨fun j => ?_, fun j => ?_⟩
  · rcases le_or_gt j d with hj | hj
    · rw [hb j hj]
      exact mul_nonneg (Nat.cast_nonneg _) (hnn j hj)
    · rw [hzero j hj]
  · rcases le_or_gt (j + 2) d with hj | hj
    · rw [hb j (by omega), hb (j + 2) hj, hb (j + 1) (by omega)]
      exact mul_mul_mul_le_sq (by exact_mod_cast choose_mul_choose_add_two_le d j) (hlc j hj)
        (mul_nonneg (hnn j (by omega)) (hnn (j + 2) hj))
    · rw [hzero (j + 2) hj, mul_zero]
      exact sq_nonneg _

section Shift

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

/-- Shifting a log-concave sequence one place to the right (with `0` in front) and weighting it
termwise by a nonnegative log-concave sequence gives a log-concave sequence. -/
private lemma isLogConcaveSeq_shift_mul {d : ℕ} {b b' c : ℕ → R} (hb : IsLogConcaveSeq d b)
    (hc0 : ∀ j, 0 ≤ c j) (hc : ∀ j, c j * c (j + 2) ≤ c (j + 1) ^ 2)
    (h0 : b' 0 = 0) (hs : ∀ j, b' (j + 1) = c j * b j) : IsLogConcaveSeq (d + 1) b' := by
  obtain ⟨hnn, hlc⟩ := hb
  refine ⟨fun j hj => ?_, fun j hj => ?_⟩
  · rcases j with _ | j
    · exact h0.ge
    · exact hs j ▸ mul_nonneg (hc0 j) (hnn j (by omega))
  · rcases j with _ | j
    · rw [h0, zero_mul]
      exact sq_nonneg _
    · rw [hs, hs, hs]
      exact mul_mul_mul_le_sq (hc j) (hlc j (by omega))
        (mul_nonneg (hnn j (by omega)) (hnn (j + 2) (by omega)))

/-- Shifting a sequence with no internal zeros one place to the right (with `0` in front) and
weighting it termwise by a positive sequence gives a sequence with no internal zeros. -/
private lemma hasNoInternalZeros_shift_mul {d : ℕ} {b b' c : ℕ → R}
    (hb : HasNoInternalZeros d b) (hc : ∀ j, 0 < c j) (h0 : b' 0 = 0)
    (hs : ∀ j, b' (j + 1) = c j * b j) : HasNoInternalZeros (d + 1) b' := by
  intro i j k hij hjk hk hi hk'
  rcases i with _ | i
  · exact absurd hi (by simp [h0])
  obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [hs] at hi hk' ⊢
  exact mul_pos (hc j) (hb i j k (by omega) (by omega) (by omega)
    ((pos_iff_pos_of_mul_pos hi).1 (hc i)) ((pos_iff_pos_of_mul_pos hk').1 (hc k)))

end Shift

/-- The normalized coefficients of `f * X` of order `d + 1`, shifted by one, are those of `f`
of order `d`, scaled by `(j + 1) / (d + 1)`. -/
private lemma coeff_mul_X_succ_div (d : ℕ) (f : ℝ[X]) (j : ℕ) :
    (f * X).coeff (j + 1) / ((d + 1).choose (j + 1) : ℝ) =
      ((j + 1 : ℝ) / (d + 1)) * (f.coeff j / (d.choose j : ℝ)) := by
  rw [coeff_mul_X]
  rcases lt_or_ge d j with hj | hj
  · simp [Nat.choose_eq_zero_of_lt, hj]
  have h : ((d + 1).choose (j + 1) : ℝ) * (j + 1) = (d + 1) * d.choose j := by
    exact_mod_cast (Nat.add_one_mul_choose_eq d j).symm
  have : (0 : ℝ) < d.choose j := by exact_mod_cast Nat.choose_pos hj
  have : (0 : ℝ) < (d + 1).choose (j + 1) := by exact_mod_cast Nat.choose_pos (by omega)
  field_simp
  linear_combination -f.coeff j * h

/-- If `f` is ultra-log-concave of order `d`, then `x f` is ultra-log-concave of order `d + 1`. -/
@[lognarayana "lem_ulc_mul_x"]
public theorem Polynomial.IsUltraLogConcave.mul_X {d : ℕ} {f : ℝ[X]}
    (hf : f.IsUltraLogConcave d) : (f * X).IsUltraLogConcave (d + 1) := by
  obtain ⟨hdeg, hlc, hnz⟩ := hf
  have hc : ∀ j : ℕ, (0 : ℝ) < (j + 1) / (d + 1) := fun j => by positivity
  have h0 : (f * X).coeff 0 / ((d + 1).choose 0 : ℝ) = 0 := by simp
  refine ⟨natDegree_mul_le.trans (add_le_add hdeg natDegree_X_le),
    isLogConcaveSeq_shift_mul hlc (fun j => (hc j).le) (fun j => ?_) h0
      (coeff_mul_X_succ_div d f),
    hasNoInternalZeros_shift_mul hnz hc h0 (coeff_mul_X_succ_div d f)⟩
  rw [div_mul_div_comm, div_pow, ← sq]
  gcongr
  push_cast
  nlinarith
