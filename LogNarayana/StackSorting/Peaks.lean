/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib
public import LogNarayana.Attr
public import LogNarayana.StackSorting.AdoptableForest.Defs
public import LogNarayana.StackSorting.FiberPolynomials.Defs
public import LogNarayana.Lorentzian.Hessian.Defs
public import LogNarayana.Lorentzian.QuadraticKernel.Defs
public import LogNarayana.StackSorting.StackSort.Defs
public import LogNarayana.StackSorting.Matchings.Defs
public import LogNarayana.Lorentzian.Hessian.Basic
public import LogNarayana.Lorentzian.QuadraticKernel.Basic
public import LogNarayana.StackSorting.AdoptableForest.Basic
public import LogNarayana.StackSorting.Matchings.Basic
public import LogNarayana.Forest.Weighted.Basic
public import LogNarayana.Lorentzian.BrandenHuh.Basic
public import LogNarayana.Lorentzian.Symbol.Basic

/-!
# Peaks in stack-sorting fibers

For `n ≥ 1`, a permutation `π ∈ S_n` and `λ ∈ ℝ`, the peak-weighted homogeneous fiber
polynomial is `H^λ_π(x, y) = ∑_{σ ∈ s⁻¹(π)} λ^{peak(σ)} x^{des(σ)} y^{n - 1 - des(σ)}`. It is
the weighted admissible-matching polynomial `∑_M (λ x y)^{|M|} (x + y)^{n - 1 - 2|M|}` of the
adoptable forest of `π`, with `A = x + y` and `B = λ x y`. The kernel condition
`Hess B - a aᵀ ⪯ 0`, `a = (1, 1)`, holds exactly when `0 ≤ λ ≤ 2`, equivalently the peak
kernel `λ x y + (x + y) t + t² / 2` is Lorentzian, and then `H^λ_π` is Lorentzian.

## Main results

* `MvPolynomial.posSemidef_neg_hessianAtZero_sub_vecMulVec`: for `0 ≤ λ ≤ 2`,
  `Hess(λ x y) - a aᵀ ⪯ 0`.
* `MvPolynomial.isLorentzian_peakKernel_iff`: `λ x y + (x + y) t + t² / 2` is Lorentzian if and
  only if `0 ≤ λ ≤ 2`.
* `List.fiberPeakPolynomial_2135467`: `H^λ_{2135467}(x, y) = 5 λ² x² y² (x + y)² + 2 λ³ x³ y³`.
* `List.X_mul_aeval_fiberPeakPolynomial_two_2135467`:
  `x H²_{2135467}(x, 1) = 20 x³ + 56 x⁴ + 20 x⁵`.
* `List.isLorentzian_fiberPeakPolynomial`: `H^λ_π` is Lorentzian for `λ ∈ [0, 2]`.

## Implementation notes

Negative semidefiniteness `C ⪯ 0` is spelled `(-C).PosSemidef`, and `a aᵀ` is
`Matrix.vecMulVec a a`. In the peak kernel the variables are indexed by `Option (Fin 2)`:
`x = X (some 0)`, `y = X (some 1)` and `t = X none`, the convention of
`MvPolynomial.quadraticKernel`. The permutation `2135467` is the list `[2, 1, 3, 5, 4, 6, 7]`,
and `H(x, 1)` is the evaluation `MvPolynomial.aeval ![Polynomial.X, 1]`.

Five results of Brändén–Huh are cited, not proved, and enter the main theorem as hypotheses,
each for every finite variable type: nonnegative linear substitutions [BH, Theorem 2.10]
(`MvPolynomial.LorentzianNonnegLinearSubstitution`), nonnegative directional derivatives
[BH, Corollary 2.11] (`MvPolynomial.LorentzianNonnegDerivative`), products [BH, Corollary 2.32]
(`MvPolynomial.LorentzianMul`), normalized support polynomials of M-convex sets
[BH, Theorem 3.10] (`MvPolynomial.NormalizedSupportPolyLorentzianOfMConvex`), and the symbol
theorem [BH, Theorem 3.2] (`MvPolynomial.BrandenHuhSymbolTheorem`).

## References

* [LogNarayana], Sections 3 and 4.
* [BH] P. Brändén, J. Huh, *Lorentzian polynomials*, Ann. of Math. 192 (2020).
-/

open MvPolynomial

namespace MvPolynomial

open Matrix

/-! ### The kernel condition for peaks -/

private lemma hessianAtZero_C_mul_X_zero_mul_X_one (c : ℝ) :
    hessianAtZero (C c * X 0 * X 1 : MvPolynomial (Fin 2) ℝ) = !![0, c; c, 0] := by
  ext i j
  rw [hessianAtZero_apply_eq_constantCoeff_pderiv_pderiv]
  fin_cases i <;> fin_cases j <;> simp

/-- The quadratic form of `-(!![0, c; c, 0] - a aᵀ)`, `a = (1, 1)`, as a sum of squares. -/
private lemma dotProduct_mulVec_peak (c : ℝ) (w : Fin 2 → ℝ) :
    star w ⬝ᵥ ((-(!![0, c; c, 0] - vecMulVec ![1, 1] ![1, 1])) *ᵥ w) =
      ((2 - c) * (w 0 + w 1) ^ 2 + c * (w 0 - w 1) ^ 2) / 2 := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, vecMulVec, vecHead, vecTail]
  ring

/-- For `0 ≤ λ ≤ 2`, the matrix `Hess(λ x y) - a aᵀ` with `a = (1, 1)` is negative semidefinite. -/
@[lognarayana "lem_peak_kernel_condition"]
public theorem posSemidef_neg_hessianAtZero_sub_vecMulVec {c : ℝ} (h₀ : 0 ≤ c) (h₂ : c ≤ 2) :
    (-(hessianAtZero (C c * X 0 * X 1 : MvPolynomial (Fin 2) ℝ) -
      Matrix.vecMulVec ![1, 1] ![1, 1])).PosSemidef := by
  rw [hessianAtZero_C_mul_X_zero_mul_X_one]
  refine .of_dotProduct_mulVec_nonneg ?_ fun w => ?_
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [vecMulVec, vecHead, vecTail]
  · rw [dotProduct_mulVec_peak]
    have : 0 ≤ 2 - c := by linarith
    positivity

/-! ### The peak kernel -/

/-- `c x_i x_j` has nonnegative coefficients when `0 ≤ c`. -/
private lemma hasNonnegCoeffs_C_mul_X_mul_X {τ : Type*} {c : ℝ} (hc : 0 ≤ c) (i j : τ) :
    (C c * X i * X j : MvPolynomial τ ℝ).HasNonnegCoeffs := by
  classical
  intro α
  rw [mul_assoc, X, X, monomial_mul, C_mul_monomial, coeff_monomial]
  split_ifs <;> simp [hc]

/-- A Lorentzian polynomial has nonnegative coefficients (the zero polynomial included). -/
private lemma IsLorentzian.coeff_nonneg {τ S : Type*} [Fintype τ] [CommRing S] [PartialOrder S]
    {f : MvPolynomial τ S} (h : f.IsLorentzian) (α : τ →₀ ℕ) : 0 ≤ f.coeff α := by
  rcases h with rfl | ⟨-, -, hnn, -⟩
  exacts [(coeff_zero α).ge, hnn α]

/-- The coefficient of `x y` in the peak kernel is `λ`. -/
private lemma coeff_peak (c : ℝ) :
    (C c * X (some 0) * X (some 1) + (X (some 0) + X (some 1)) * X none +
        C (1 / 2) * X none ^ 2 : MvPolynomial (Option (Fin 2)) ℝ).coeff
      (Finsupp.single (some 0) 1 + Finsupp.single (some 1) 1) = c := by
  simp only [mul_assoc, add_mul, pow_two, X, monomial_mul, C_mul_monomial, coeff_add,
    coeff_monomial]
  simp [Finsupp.ext_iff, Option.forall]

private lemma peak_eq_quadraticKernel (c : ℝ) :
    (C c * X (some 0) * X (some 1) + (X (some 0) + X (some 1)) * X none +
        C (1 / 2) * X none ^ 2 : MvPolynomial (Option (Fin 2)) ℝ) =
      quadraticKernel (∑ j, C (![1, 1] j) * X j) (C c * X 0 * X 1) := by
  simp [quadraticKernel, Fin.sum_univ_two]

/-- The kernel condition forces `λ ≤ 2`: its quadratic form at `w = (1, 1)` is `2 (2 - λ)`. -/
private lemma le_two_of_posSemidef {c : ℝ}
    (h : (-(hessianAtZero (C c * X 0 * X 1 : MvPolynomial (Fin 2) ℝ) -
      vecMulVec ![1, 1] ![1, 1])).PosSemidef) : c ≤ 2 := by
  have := h.dotProduct_mulVec_nonneg ![1, 1]
  simp [hessianAtZero_C_mul_X_zero_mul_X_one, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    vecMulVec, vecHead, vecTail] at this
  linarith

/-- For `λ ∈ ℝ`, the polynomial `λ x y + (x + y) t + t² / 2` is Lorentzian if and only if
`0 ≤ λ ≤ 2`. -/
@[lognarayana "lem_peak_kernel_lorentzian_iff"]
public theorem isLorentzian_peakKernel_iff (c : ℝ) :
    (C c * X (some 0) * X (some 1) + (X (some 0) + X (some 1)) * X none +
        C (1 / 2) * X none ^ 2 : MvPolynomial (Option (Fin 2)) ℝ).IsLorentzian ↔
      0 ≤ c ∧ c ≤ 2 := by
  have ha : ∀ j, (0 : ℝ) ≤ ![1, 1] j := fun j => by fin_cases j <;> simp
  have hB : (C c * X 0 * X 1 : MvPolynomial (Fin 2) ℝ).IsHomogeneous 2 :=
    (isHomogeneous_C_mul_X c 0).mul (isHomogeneous_X ℝ 1)
  refine ⟨fun h => ?_, fun ⟨h₀, h₂⟩ => ?_⟩
  · have hc : 0 ≤ c := coeff_peak c ▸ IsLorentzian.coeff_nonneg h _
    rw [peak_eq_quadraticKernel,
      isLorentzian_quadraticKernel_iff ha hB (hasNonnegCoeffs_C_mul_X_mul_X hc _ _)] at h
    exact ⟨hc, le_two_of_posSemidef h⟩
  · rw [peak_eq_quadraticKernel,
      isLorentzian_quadraticKernel_iff ha hB (hasNonnegCoeffs_C_mul_X_mul_X h₀ _ _)]
    exact posSemidef_neg_hessianAtZero_sub_vecMulVec h₀ h₂

end MvPolynomial

namespace List

/-! ### The running example `2135467` -/

/-- The seven matchings of `2135467`. -/
private abbrev matchings2135467 : Finset (Finset (ℕ × ℕ)) :=
  {{(1, 2), (4, 5)}, {(1, 2), (3, 6), (4, 5)}, {(1, 3), (4, 5)}, {(1, 6), (4, 5)},
    {(1, 6), (2, 3), (4, 5)}, {(1, 2), (4, 6)}, {(1, 3), (4, 6)}}

/-- The candidate pairs `(a, b)` with `1 ≤ a < b ≤ 6`. -/
private abbrev pairs2135467 : Finset (ℕ × ℕ) :=
  (Finset.Icc 1 6 ×ˢ Finset.Icc 1 6).filter fun p => p.1 < p.2

/-- Two distinct pairs of a noncrossing partial matching share no entry. -/
private lemma disjoint_of_ne {N : ℕ} {M : Finset (ℕ × ℕ)} (h : IsNoncrossingPartialMatching N M)
    {p q : ℕ × ℕ} (hp : p ∈ M) (hq : q ∈ M) (hpq : p ≠ q) :
    p.1 ≠ q.1 ∧ p.1 ≠ q.2 ∧ p.2 ≠ q.1 ∧ p.2 ≠ q.2 :=
  ⟨fun e => hpq (h.eq_of_mem_of_mem p hp q hq _ (Or.inl rfl) (Or.inl e)),
    fun e => hpq (h.eq_of_mem_of_mem p hp q hq _ (Or.inl rfl) (Or.inr e)),
    fun e => hpq (h.eq_of_mem_of_mem p hp q hq _ (Or.inr rfl) (Or.inl e)),
    fun e => hpq (h.eq_of_mem_of_mem p hp q hq _ (Or.inr rfl) (Or.inr e))⟩

/-- The pairs of `pairs2135467` sharing no entry with, and crossing neither of, `p` and `q`. -/
private abbrev compatiblePairs2135467 (p q : ℕ × ℕ) : Finset (ℕ × ℕ) :=
  pairs2135467.filter fun r => (p.1 ≠ r.1 ∧ p.1 ≠ r.2 ∧ p.2 ≠ r.1 ∧ p.2 ≠ r.2) ∧
    (q.1 ≠ r.1 ∧ q.1 ≠ r.2 ∧ q.2 ≠ r.1 ∧ q.2 ≠ r.2) ∧
    ¬ (p.1 < r.1 ∧ r.1 < p.2 ∧ p.2 < r.2) ∧ ¬ (r.1 < p.1 ∧ p.1 < r.2 ∧ r.2 < p.2) ∧
    ¬ (q.1 < r.1 ∧ r.1 < q.2 ∧ q.2 < r.2) ∧ ¬ (r.1 < q.1 ∧ q.1 < r.2 ∧ r.2 < q.2)

/-- The finite case check: the pairs `(1, b)`, `(4, b')` together with any subset of the
pairs compatible with both form one of the matchings in `matchings2135467`. -/
private lemma insert_insert_mem_matchings2135467 : ∀ b ∈ Finset.Icc 2 6,
    ∀ b' ∈ ({5, 6} : Finset ℕ), b ≠ 4 → b ≠ b' → ¬ (1 < 4 ∧ 4 < b ∧ b < b') →
      ∀ T ∈ (compatiblePairs2135467 (1, b) (4, b')).powerset,
        insert (1, b) (insert (4, b') T) ∈ matchings2135467 := by
  decide

private lemma mem_fiberMatchings_2135467_iff (M : Finset (ℕ × ℕ)) :
    M ∈ [2, 1, 3, 5, 4, 6, 7].fiberMatchings ↔ M ∈ matchings2135467 := by
  constructor
  · rintro ⟨h, hdes, -⟩
    change IsNoncrossingPartialMatching 6 M at h
    have hsub : M ⊆ pairs2135467 := fun p hp => by
      have := h.one_le_fst p hp
      have := h.fst_lt_snd p hp
      have := h.snd_le p hp
      simp only [pairs2135467, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
      omega
    have h1 : 1 ∈ M.image Prod.fst := hdes (by decide)
    have h4 : 4 ∈ M.image Prod.fst := hdes (by decide)
    obtain ⟨⟨a, b⟩, hab, rfl : a = 1⟩ := Finset.mem_image.1 h1
    obtain ⟨⟨a', b'⟩, hab', rfl : a' = 4⟩ := Finset.mem_image.1 h4
    have hne : ((1, b) : ℕ × ℕ) ≠ (4, b') := by simp
    obtain ⟨-, -, hb4, hbb'⟩ := disjoint_of_ne h hab hab' hne
    have hb := hsub hab
    have hb' := hsub hab'
    simp only [pairs2135467, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hb hb'
    have hT : (M.erase (1, b)).erase (4, b') ⊆ compatiblePairs2135467 (1, b) (4, b') :=
      fun r hr => by
        obtain ⟨hr4, hr1, hrM⟩ : r ≠ (4, b') ∧ r ≠ (1, b) ∧ r ∈ M := by simpa using hr
        exact Finset.mem_filter.2 ⟨hsub hrM, disjoint_of_ne h hab hrM (Ne.symm hr1),
          disjoint_of_ne h hab' hrM (Ne.symm hr4), h.noncrossing _ hab _ hrM,
          h.noncrossing _ hrM _ hab, h.noncrossing _ hab' _ hrM, h.noncrossing _ hrM _ hab'⟩
    rw [← Finset.insert_erase hab, ← Finset.insert_erase (Finset.mem_erase.2 ⟨hne.symm, hab'⟩)]
    exact insert_insert_mem_matchings2135467 b (by simp; omega) b' (by simp; omega) hb4 hbb'
      (h.noncrossing _ hab _ hab') _ (Finset.mem_powerset.2 hT)
  · intro hM
    have hdes : List.descentSet [2, 1, 3, 5, 4, 6, 7] = {1, 4} := by decide
    simp only [matchings2135467, Finset.mem_insert, Finset.mem_singleton] at hM
    refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    all_goals try rw [hdes]
    all_goals rcases hM with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | decide
      | (intro p hp q hq x
         simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq
         rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl <;> simp <;> omega)

/-- For every real `λ`, the peak-weighted homogeneous fiber polynomial of `2135467` is
`H^λ_{2135467}(x, y) = 5 λ² x² y² (x + y)² + 2 λ³ x³ y³`. -/
@[lognarayana "lem_ex_peak_poly_2135467"]
public theorem fiberPeakPolynomial_2135467 (lam : ℝ) :
    fiberPeakPolynomial ℝ lam [2, 1, 3, 5, 4, 6, 7] =
      C (5 * lam ^ 2) * X 0 ^ 2 * X 1 ^ 2 * (X 0 + X 1) ^ 2 +
        C (2 * lam ^ 3) * X 0 ^ 3 * X 1 ^ 3 := by
  rw [List.fiberPeakPolynomial_eq_finsum_fiberMatchings ℝ (n := 7) (by norm_num)
      (π := [2, 1, 3, 5, 4, 6, 7]) ⟨⟨by decide, by decide⟩, rfl, by decide⟩ lam,
    show [2, 1, 3, 5, 4, 6, 7].fiberMatchings = (matchings2135467 : Set (Finset (ℕ × ℕ))) from
      Set.ext mem_fiberMatchings_2135467_iff, finsum_mem_coe_finset]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  simp [Finset.card_insert_of_notMem, C_mul, map_ofNat C]
  ring

/-- For the permutation `2135467` and weight `λ = 2`,
`x H²_{2135467}(x, 1) = 20 x³ + 56 x⁴ + 20 x⁵`. -/
@[lognarayana "lem_ex_peak_poly_2135467_two"]
public theorem X_mul_aeval_fiberPeakPolynomial_two_2135467 :
    Polynomial.X * aeval ![(Polynomial.X : Polynomial ℝ), 1]
        (fiberPeakPolynomial ℝ 2 [2, 1, 3, 5, 4, 6, 7]) =
      20 * Polynomial.X ^ 3 + 56 * Polynomial.X ^ 4 + 20 * Polynomial.X ^ 5 := by
  simp [List.fiberPeakPolynomial_2135467, Polynomial.C_ofNat]
  ring

/-! ### Peak-weighted fiber polynomials are Lorentzian -/

/-- The admissible matchings for `(par, L)` on `[N]` form the finite set indexing the sum of
`isLorentzian_sum_admissibleMatching_pow_mul_pow`: their pairs satisfy `1 ≤ a < b ≤ N`. -/
private lemma setOf_isAdmissibleMatching_eq_coe_filter (N : ℕ) (par : ℕ → Option ℕ)
    (L : Finset ℕ) [DecidablePred (IsAdmissibleMatching N par L)] :
    {M | IsAdmissibleMatching N par L M} =
      ↑((Finset.Icc 1 N ×ˢ Finset.Icc 1 N).powerset.filter (IsAdmissibleMatching N par L)) := by
  ext M
  simp only [Set.mem_ofPred_eq, Finset.coe_filter, Finset.mem_powerset, iff_and_self]
  intro h p hp
  have hM := h.isNoncrossingPartialMatching
  have := hM.one_le_fst p hp
  have := hM.fst_lt_snd p hp
  have := hM.snd_le p hp
  simp only [Finset.mem_product, Finset.mem_Icc]
  omega

/-- The descents of a word of length `ℓ` are positions in `[1, ℓ - 1]`. -/
private lemma descentSet_subset_Icc (π : List ℕ) :
    π.descentSet ⊆ Finset.Icc 1 (π.length - 1) := by
  intro i hi
  simp only [List.descentSet, Finset.mem_filter, Finset.mem_Ico] at hi
  simp only [Finset.mem_Icc]
  omega

/-- A negative semidefinite real matrix has nonpositive quadratic form. -/
private lemma dotProduct_mulVec_nonpos_of_posSemidef_neg {ι : Type*} [Fintype ι]
    {A : Matrix ι ι ℝ} (hA : (-A).PosSemidef) (w : ι → ℝ) :
    dotProduct w (A.mulVec w) ≤ 0 := by
  simpa [Matrix.neg_mulVec] using hA.dotProduct_mulVec_nonneg w

/-- **Peak-weighted fiber polynomials are Lorentzian.** For `n ≥ 1`, `π ∈ S_n` and
`λ ∈ [0, 2]`, the peak-weighted homogeneous fiber polynomial `H^λ_π(x, y)` is Lorentzian, given
the cited Brändén–Huh theorems on nonnegative linear substitutions, nonnegative derivatives,
products, normalized support polynomials of M-convex sets, and symbols of linear operators. -/
@[lognarayana "thm_peaks_lorentzian"]
public theorem isLorentzian_fiberPeakPolynomial {n : ℕ} (hn : 1 ≤ n) {π : List ℕ}
    (hπ : π ∈ permWords n) {lam : ℝ} (hlam : lam ∈ Set.Icc (0 : ℝ) 2)
    (hsub : ∀ (σ τ : Type) [Fintype σ] [Fintype τ], LorentzianNonnegLinearSubstitution σ τ)
    (hder : ∀ (σ : Type) [Fintype σ], LorentzianNonnegDerivative σ)
    (hmul : ∀ (σ : Type) [Fintype σ], LorentzianMul σ)
    (hBH : ∀ (σ : Type) [Fintype σ], NormalizedSupportPolyLorentzianOfMConvex σ)
    (hsym : ∀ (σ τ : Type) [Fintype σ] [Fintype τ], BrandenHuhSymbolTheorem σ τ) :
    (fiberPeakPolynomial ℝ lam π).IsLorentzian := by
  classical
  obtain rfl : π.length = n := hπ.2.1
  rw [List.fiberPeakPolynomial_eq_finsum_fiberMatchings ℝ hn hπ lam,
    List.fiberMatchings_eq_setOf_isAdmissibleMatching hπ,
    setOf_isAdmissibleMatching_eq_coe_filter, finsum_mem_coe_finset,
    show (X 0 + X 1 : MvPolynomial (Fin 2) ℝ) = ∑ i, (![1, 1] : Fin 2 → ℝ) i • X i by
      simp [Fin.sum_univ_two]]
  exact isLorentzian_sum_admissibleMatching_pow_mul_pow hsub hmul hsym hBH hder
    (List.isPostorderForest_adoptableForest π) (descentSet_subset_Icc π)
    (fun _ hv => List.isLeaf_adoptableForest_of_mem_descentSet π hv) ![1, 1] _
    (fun i => by fin_cases i <;> simp)
    (((isHomogeneous_C _ lam).mul (isHomogeneous_X ℝ 0)).mul (isHomogeneous_X ℝ 1))
    (hasNonnegCoeffs_C_mul_X_mul_X hlam.1 0 1)
    (dotProduct_mulVec_nonpos_of_posSemidef_neg
      (posSemidef_neg_hessianAtZero_sub_vecMulVec hlam.1 hlam.2))

end List
