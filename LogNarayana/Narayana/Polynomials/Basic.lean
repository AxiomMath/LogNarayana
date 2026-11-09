/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module
public import LogNarayana.Narayana.Polynomials.Defs
public import LogNarayana.StackSorting.FiberPolynomials.Defs
public import LogNarayana.AuxiliaryDefinitions

/-!
# Narayana polynomials

This file proves the elementary properties of the Narayana polynomials `N_q` and the shifted
Narayana polynomials `Ñ_m`, and records, as propositions to be taken as hypotheses, the results
on them and on the fiber descent polynomials `D_π` that [LogNarayana] cites.

The shifted polynomial is `N_{m+1}(x) = x · Ñ_m(x)`; its first values are `Ñ_0 = 1`,
`Ñ_1 = 1 + x`, `Ñ_2 = 1 + 3x + x²` and `Ñ_3 = 1 + 6x + 6x² + x³`, and in general `Ñ_m` is
monic of degree `m`, since its coefficient of `x^m` is `(m+1)⁻¹ (m+1 choose m+1) (m+1 choose m)`.
Every summand `C_j (m choose 2j) Bʲ A^(m-2j)` of `Q_m(A, B)` has weight `2j + (m - 2j) = m`, so
`Q_m(F, G)` is homogeneous of degree `m` whenever `F` is homogeneous of degree `1` and `G` of
degree `2`. Evaluating `Q_m` at `A = 1 + x`, `B = x` termwise gives the Catalan γ-expansion of
`Ñ_m`, so `Ñ_m = Q_m(1 + x, x)`.

## Main definitions

The following are cited theorems, each stated as a `Prop` and taken as a hypothesis by the
results that use it.

* `ShiftedNarayanaGammaExpansion`: the Catalan γ-expansion of `Ñ_m` [Actions], [Coker].
* `ShiftedNarayanaNegRealRoots`: `Ñ_m` has exactly `m` distinct negative real zeros [LiuWang].
* `ShiftedNarayanaInterlacing`: the zeros of `Ñ_m` and `Ñ_{m+1}` interlace strictly [LiuWang].
* `ShiftedNarayanaCoeffLogConvex`: the sequence `(Ñ_m)` is coefficientwise log-convex [CWY].
* `NarayanaTransformLogConvex`: the Narayana transformation preserves log-convexity [CWY].
* `BonaFiberDescentSymmetric`, `BonaFiberDescentUnimodal`: `D_π ∈ ℕ[x]` is symmetric with
  respect to `n - 1` and unimodal [BonaStack], [Counting].
* `BrandenFiberDescentGammaNonneg`: the γ-expansion of `D_π` with respect to `n - 1`, whose
  coefficients count the permutations of the fiber by peaks [Actions], [Counting].

## Main results

* `narayanaPolynomial_succ_eq_X_mul`: `N_{m+1} = x · Ñ_m`.
* `shiftedNarayanaPolynomial_zero`, `shiftedNarayanaPolynomial_one`,
  `shiftedNarayanaPolynomial_two`, `shiftedNarayanaPolynomial_three`: `Ñ_0, …, Ñ_3`.
* `isMonicOfDegree_shiftedNarayanaPolynomial`: `Ñ_m` is monic of degree `m`.
* `shiftedNarayanaGammaExpansion_holds`: the γ-expansion `ShiftedNarayanaGammaExpansion` holds.
* `shiftedNarayanaPolynomial_add_two`: `Ñ_{m+2} = (1 + x) Ñ_{m+1} + x ∑_{p+q=m} Ñ_p Ñ_q`.
* `MvPolynomial.IsHomogeneous.aeval_narayanaQ`: `Q_m(F, G)` is homogeneous of degree `m`.
* `shiftedNarayanaPolynomial_eq_aeval_narayanaQ`: `Ñ_m = Q_m(1 + x, x)`.

## Implementation notes

`Q_m(F, G)` is `MvPolynomial.aeval ![F, G] (narayanaQ ℝ m)`. The paper indexes the variables of
`F` and `G` by a finite set; finiteness plays no role, so they are indexed by any type `σ`.

The cited results are stated with their indices shifted so that no truncated subtraction occurs
(`Ñ_{m-1} Ñ_{m+1} - Ñ_m²` for `m ≥ 1` becomes `Ñ_m Ñ_{m+2} - Ñ_{m+1}²` for all `m`), and the
cited hypotheses `m ≥ 1` are dropped where the remaining case holds. The results on `D_π`
are stated as their sources state them: symmetry and unimodality for the fiber descent
polynomial with natural-number coefficients (the counts), and Brändén's γ-expansion over `ℝ`,
with coefficients `|{σ ∈ s⁻¹(π) : peak σ = m}| / 2^(n-1-2m)`. For `n = 0` the fiber is `{[]}`
and `D_π = 1`.

## References

* [LogNarayana], Section 2.
* [Actions] P. Brändén, *Actions on permutations and unimodality of descent polynomials*,
  Europ. J. Combin. 29 (2008).
* [Coker] C. Coker, *Enumerating a class of lattice paths*, Discrete Math. 271 (2003).
* [LiuWang] L. L. Liu, Y. Wang, *A unified approach to polynomial sequences with only real
  zeros*, Adv. in Appl. Math. 38 (2007).
* [CWY] W. Y. C. Chen, L. X. W. Wang, A. L. B. Yang, *Schur positivity and the
  `q`-log-convexity of the Narayana polynomials*, J. Algebraic Combin. 32 (2010).
* [BonaStack] M. Bóna, *Symmetry and unimodality in t-stack sortable permutations*,
  J. Combin. Theory Ser. A 98 (2002).
* [Counting] C. Defant, *Counting 3-stack-sortable permutations*, J. Combin. Theory Ser. A 172
  (2020).
-/


universe u

open Polynomial

/-! ### The cited results -/

/-- **Coefficientwise log-convexity of the shifted Narayana polynomials** (W. Y. C. Chen,
L. X. W. Wang and A. L. B. Yang, *Schur positivity and the `q`-log-convexity of the Narayana
polynomials*, 2010): for every `m`, every coefficient of
`Ñ_m * Ñ_{m+2} - Ñ_{m+1} ^ 2` is nonnegative, where `Ñ_m = shiftedNarayanaPolynomial m`. -/
@[expose, lognarayana "thm_ext_cwy_log_convex"]
public def ShiftedNarayanaCoeffLogConvex : Prop :=
  ∀ (m k : ℕ), 0 ≤ (shiftedNarayanaPolynomial m * shiftedNarayanaPolynomial (m + 2) -
    shiftedNarayanaPolynomial (m + 1) ^ 2).coeff k

/-- **The Narayana transformation preserves log-convexity** (W. Y. C. Chen, L. X. W. Wang and
A. L. B. Yang, *Schur positivity and the `q`-log-convexity of the Narayana polynomials*, 2010,
Theorem 5.3): if `a : ℕ → ℝ` is positive and log-convex and `b 0 = a 0`,
`b (n + 1) = ∑_{k < n + 1} (shiftedNarayanaPolynomial n).coeff k * a k`, then
`b (n + 1) ^ 2 ≤ b n * b (n + 2)` for every `n`. -/
@[expose, lognarayana "thm_ext_cwy_narayana_transformation"]
public def NarayanaTransformLogConvex : Prop :=
  ∀ a b : ℕ → ℝ, (∀ k, 0 < a k) → (∀ k, a (k + 1) ^ 2 ≤ a k * a (k + 2)) →
    b 0 = a 0 →
    (∀ n, b (n + 1) = ∑ k ∈ Finset.range (n + 1), (shiftedNarayanaPolynomial n).coeff k * a k) →
    ∀ n, b (n + 1) ^ 2 ≤ b n * b (n + 2)

/-- **Bóna's symmetry theorem** (M. Bóna, *Symmetry and unimodality in t-stack sortable
permutations*, 2002; as stated by Defant, *Counting 3-stack-sortable permutations*,
Introduction, and *Fertilitopes*, Section 2.4): for every `n` and every permutation `π ∈ S_n`,
the fiber descent polynomial `D_π(x) = ∑_{σ ∈ s⁻¹(π)} x^{des σ} ∈ ℕ[x]` is symmetric with
respect to `n - 1`. -/
@[expose, lognarayana "thm_ext_bona_symmetric"]
public def BonaFiberDescentSymmetric : Prop :=
  ∀ (n : ℕ) (π : List ℕ), π ∈ permWords n →
    IsSymmetricWRT (n - 1) (List.fiberDescentPolynomial ℕ π)

/-- **Bóna's unimodality theorem** (M. Bóna, *Symmetry and unimodality in t-stack sortable
permutations*, 2002, with the corrigendum, J. Combin. Theory Ser. A 99 (2002); as stated by
Defant, *Counting 3-stack-sortable permutations*, Introduction, and *Fertilitopes*,
Section 2.4): for every `n` and every permutation `π ∈ S_n`, the fiber descent polynomial
`D_π(x) ∈ ℕ[x]` is unimodal. -/
@[expose, lognarayana "thm_ext_bona_unimodal"]
public def BonaFiberDescentUnimodal : Prop :=
  ∀ (n : ℕ) (π : List ℕ), π ∈ permWords n → IsUnimodalPolynomial (List.fiberDescentPolynomial ℕ π)

/-- **Brändén's γ-expansion of stack-sorting fibers** (P. Brändén, *Actions on permutations and
unimodality of descent polynomials*, Europ. J. Combin. 29 (2008), Corollary 3.2 applied to the
stack-sorting fiber, which is invariant under the modified Foata–Strehl action by
Corollary 4.2; as stated by C. Defant, *Counting 3-stack-sortable permutations*, 2020,
Theorem 1.3): for every `n` and every permutation `π ∈ S_n`,
`D_π(x) = ∑_{m=0}^{⌊(n-1)/2⌋} (|{σ ∈ s⁻¹(π) : peak(σ) = m}| / 2^{n-1-2m}) x^m (1 + x)^{n-1-2m}`
in `ℝ[x]`. -/
@[expose, lognarayana "thm_ext_branden_gamma_nonneg"]
public def BrandenFiberDescentGammaNonneg : Prop :=
  ∀ (n : ℕ) (π : List ℕ), π ∈ permWords n →
    List.fiberDescentPolynomial ℝ π =
      ∑ m ∈ Finset.range ((n - 1) / 2 + 1),
        C ((((List.stackFiber π).filter fun σ => σ.peakCount = m).card : ℝ) /
          2 ^ (n - 1 - 2 * m)) * X ^ m * (1 + X) ^ (n - 1 - 2 * m)

/-! ### The shift relation and the first values -/

/-- The Narayana polynomial `N_{m+1}` equals `x` times the shifted Narayana polynomial `Ñ_m`:
reindex the sum over `j ∈ [1, m + 1]` by `j = i + 1` and pull out one factor of `x`. -/
@[lognarayana "lem_narayana_shift"]
public theorem narayanaPolynomial_succ_eq_X_mul (m : ℕ) :
    narayanaPolynomial (m + 1) = X * shiftedNarayanaPolynomial m := by
  rw [narayanaPolynomial, if_neg m.succ_ne_zero, ← Finset.Ico_add_one_right_eq_Icc,
    Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel, shiftedNarayanaPolynomial, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [add_comm 1 i, Nat.add_sub_cancel, pow_succ]
  ring

/-- The zeroth shifted Narayana polynomial is `1`. -/
@[lognarayana "lem_shifted_narayana_zero"]
public theorem shiftedNarayanaPolynomial_zero : shiftedNarayanaPolynomial 0 = 1 := by
  simp [shiftedNarayanaPolynomial]

/-- The shifted Narayana polynomial of index one is `1 + x`. -/
@[lognarayana "lem_shifted_narayana_one"]
public theorem shiftedNarayanaPolynomial_one : shiftedNarayanaPolynomial 1 = 1 + X := by
  simp only [shiftedNarayanaPolynomial, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.choose]

/-- The shifted Narayana polynomial of index two is `1 + 3x + x²`. -/
@[lognarayana "lem_shifted_narayana_two"]
public theorem shiftedNarayanaPolynomial_two :
    shiftedNarayanaPolynomial 2 = 1 + 3 * X + X ^ 2 := by
  simp only [shiftedNarayanaPolynomial, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.choose, map_ofNat C]

/-- The shifted Narayana polynomial of index three is `1 + 6x + 6x² + x³`. -/
@[lognarayana "lem_shifted_narayana_three"]
public theorem shiftedNarayanaPolynomial_three :
    shiftedNarayanaPolynomial 3 = 1 + 6 * X + 6 * X ^ 2 + X ^ 3 := by
  simp only [shiftedNarayanaPolynomial, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.choose, map_ofNat C]

/-- For every `m`, the shifted Narayana polynomial `Ñ_m` has degree `m` and `[x^m] Ñ_m = 1`:
every term is a multiple of `x ^ j` with `j ≤ m`, and the coefficient of `x ^ m` is
`(m+1)⁻¹ (m+1 choose m+1) (m+1 choose m) = 1`. -/
@[lognarayana "lem_shifted_narayana_monic"]
public theorem isMonicOfDegree_shiftedNarayanaPolynomial (m : ℕ) :
    IsMonicOfDegree (shiftedNarayanaPolynomial m) m := by
  rw [isMonicOfDegree_iff, shiftedNarayanaPolynomial]
  refine ⟨natDegree_sum_le_of_forall_le _ _ fun j hj =>
    (natDegree_C_mul_X_pow_le _ _).trans (Finset.mem_range_succ_iff.mp hj), ?_⟩
  simp only [finsetSum_coeff, coeff_C_mul_X_pow, Finset.sum_ite_eq, Finset.self_mem_range_succ,
    if_true, Nat.choose_self, Nat.choose_succ_self_right, Nat.cast_one]
  field_simp

/-! ### The polynomials `Q_m` -/

/-- If `F` is homogeneous of degree `1` and `G` is homogeneous of degree `2`, then
`Q_m(F, G) = MvPolynomial.aeval ![F, G] (narayanaQ ℝ m)` is homogeneous of degree `m`: each
summand `C_j (m choose 2j) G^j F^(m - 2j)` has degree `2j + (m - 2j) = m`. -/
@[lognarayana "lem_narayana_q_homogeneous"]
public theorem MvPolynomial.IsHomogeneous.aeval_narayanaQ {σ : Type*} {F G : MvPolynomial σ ℝ}
    (hF : F.IsHomogeneous 1) (hG : G.IsHomogeneous 2) (m : ℕ) :
    (MvPolynomial.aeval ![F, G] (narayanaQ ℝ m)).IsHomogeneous m := by
  simp only [narayanaQ, map_sum, map_mul, map_pow, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
    MvPolynomial.algebraMap_eq, Matrix.cons_val_zero, Matrix.cons_val_one]
  refine MvPolynomial.IsHomogeneous.sum _ _ _ fun j hj => ?_
  convert (((MvPolynomial.isHomogeneous_C σ _).mul (MvPolynomial.isHomogeneous_C σ _)).mul
    (hG.pow j)).mul (hF.pow (m - 2 * j)) using 1
  have := Finset.mem_range.mp hj
  omega

/-! ### The γ-expansion of `Ñ_m` -/

section ShiftedNarayana

open Nat Finset

/-- `C_j = (2j)! / (j! (j + 1)!)`. -/
private theorem catalan_eq_factorial_div (j : ℕ) :
    (catalan j : ℝ) = ((2 * j)! : ℝ) / (j ! * (j + 1)!) := by
  have h1 := succ_mul_catalan_eq_centralBinom j
  rw [centralBinom_eq_two_mul_choose] at h1
  have h2 : ((j + 1 : ℕ) : ℝ) * catalan j = ((2 * j).choose j : ℕ) := by exact_mod_cast h1
  rw [Nat.cast_choose ℝ (by omega), show 2 * j - j = j by omega] at h2
  rw [eq_div_iff (by positivity)]
  rw [eq_div_iff (by positivity)] at h2
  rw [Nat.factorial_succ]; push_cast at h2 ⊢; linarith

/-- The termwise identity `(m + 1) C_j (m choose 2j) (m - 2j choose k - j) =
(m + 1 choose k) (k choose j) (m + 1 - k choose j + 1)`, with `k = j + s` and `m = k + j + r`. -/
private theorem catalan_choose_main_term (j s r : ℕ) :
    ((j + s + j + r + 1 : ℕ) : ℝ) * catalan j * ((j + s + j + r).choose (2 * j) : ℕ) *
        ((s + r).choose s : ℕ) =
      ((j + s + j + r + 1).choose (j + s) : ℕ) * ((j + s).choose j : ℕ) *
        ((j + r + 1).choose (j + 1) : ℕ) := by
  rw [catalan_eq_factorial_div, Nat.cast_choose ℝ (by omega : 2 * j ≤ j + s + j + r),
    Nat.cast_choose ℝ (by omega : s ≤ s + r),
    Nat.cast_choose ℝ (by omega : j + s ≤ j + s + j + r + 1),
    Nat.cast_choose ℝ (by omega : j ≤ j + s), Nat.cast_choose ℝ (by omega : j + 1 ≤ j + r + 1),
    show j + s + j + r - 2 * j = s + r by omega, show s + r - s = r by omega,
    show j + s + j + r + 1 - (j + s) = j + r + 1 by omega, show j + s - j = s by omega,
    show j + r + 1 - (j + 1) = r by omega, Nat.factorial_succ (j + s + j + r)]
  field_simp
  push_cast
  ring

/-- Termwise form of the coefficient identity, multiplied by `m + 1`. -/
private theorem catalan_choose_term_eq (m k j : ℕ) :
    ((m + 1 : ℕ) : ℝ) * ((catalan j : ℝ) * (m.choose (2 * j) : ℝ) *
        (if j ≤ k then ((m - 2 * j).choose (k - j) : ℝ) else 0)) =
      ((m + 1).choose k : ℝ) * (k.choose j : ℝ) * ((m + 1 - k).choose (j + 1) : ℝ) := by
  by_cases hjk : j ≤ k
  · rw [if_pos hjk]
    by_cases hm : k + j ≤ m
    · obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hjk
      obtain ⟨r, rfl⟩ : ∃ r, m = j + s + j + r := ⟨m - (j + s + j), by omega⟩
      rw [show j + s + j + r - 2 * j = s + r by omega, show j + s - j = s by omega,
        show j + s + j + r + 1 - (j + s) = j + r + 1 by omega]
      rw [← mul_assoc, ← mul_assoc]
      exact_mod_cast catalan_choose_main_term j s r
    · have h1 : (m + 1 - k).choose (j + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      have h2 : (m.choose (2 * j) : ℝ) * ((m - 2 * j).choose (k - j) : ℝ) = 0 := by
        by_cases h2j : 2 * j ≤ m
        · rw [Nat.choose_eq_zero_of_lt (by omega : m - 2 * j < k - j)]; simp
        · rw [Nat.choose_eq_zero_of_lt (by omega : m < 2 * j)]; simp
      rw [h1]
      linear_combination ((m + 1 : ℕ) : ℝ) * (catalan j : ℝ) * h2
  · rw [if_neg hjk, Nat.choose_eq_zero_of_lt (by omega : k < j)]
    simp

/-- A Vandermonde identity: `∑_{j < N} (k choose j) (n choose j + 1) = (k + n choose k + 1)`,
for any cutoff `N` past which every term vanishes. -/
private theorem sum_range_choose_mul_choose_succ {k n N : ℕ} (h : k < N ∨ n ≤ N) :
    ∑ j ∈ range N, k.choose j * n.choose (j + 1) = (k + n).choose (k + 1) := by
  have hV : ∑ j ∈ range (k + 1), (k.choose j * n.choose (j + 1) : ℕ) =
      (k + n).choose (k + 1) := by
    symm
    rw [add_comm k n, Nat.add_choose_eq, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      Finset.sum_range_succ']
    simp only [Nat.choose_zero_right, Nat.sub_zero, Nat.choose_succ_self, mul_zero, add_zero]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [mem_range] at hj
    rw [show k + 1 - (j + 1) = k - j by omega, Nat.choose_symm (by omega), mul_comm]
  rw [← hV]
  rcases le_total N (k + 1) with hN | hN
  · refine Finset.sum_subset (range_subset_range.2 hN) fun j _ hj => ?_
    rw [mem_range, not_lt] at hj
    rcases h with h | h
    · rw [Nat.choose_eq_zero_of_lt (by omega : k < j), zero_mul]
    · rw [Nat.choose_eq_zero_of_lt (by omega : n < j + 1), mul_zero]
  · refine (Finset.sum_subset (range_subset_range.2 hN) fun j _ hj => ?_).symm
    rw [mem_range, not_lt] at hj
    rw [Nat.choose_eq_zero_of_lt (by omega : k < j), zero_mul]

/-- The coefficient identity behind the γ-expansion of `Ñ_m`. -/
private theorem sum_catalan_mul_choose (m k : ℕ) :
    ∑ j ∈ range (m / 2 + 1), (catalan j : ℝ) * (m.choose (2 * j) : ℝ) *
        (if j ≤ k then ((m - 2 * j).choose (k - j) : ℝ) else 0) =
      ((m + 1 : ℕ) : ℝ)⁻¹ * ((m + 1).choose (k + 1) : ℝ) * ((m + 1).choose k : ℝ) := by
  rw [mul_assoc, eq_inv_mul_iff_mul_eq₀ (by positivity), Finset.mul_sum]
  simp_rw [catalan_choose_term_eq, mul_assoc, ← Finset.mul_sum]
  rw [mul_comm ((m + 1).choose (k + 1) : ℝ)]
  congr 1
  norm_cast
  rw [sum_range_choose_mul_choose_succ (by omega)]
  rcases le_or_gt k (m + 1) with hk | hk
  · rw [Nat.add_sub_cancel' hk]
  · rw [Nat.choose_eq_zero_of_lt (by omega : k + (m + 1 - k) < k + 1),
      Nat.choose_eq_zero_of_lt (by omega : m + 1 < k + 1)]

/-- The γ-expansion of the shifted Narayana polynomials holds:
`Ñ_m(x) = ∑_{j ≤ ⌊m/2⌋} C_j (m choose 2j) x^j (1+x)^(m-2j)`, proved coefficientwise from a
Vandermonde identity. -/
public theorem shiftedNarayanaGammaExpansion_holds : ShiftedNarayanaGammaExpansion := by
  intro m
  ext i
  rw [shiftedNarayanaPolynomial, finsetSum_coeff, finsetSum_coeff]
  simp_rw [coeff_C_mul_X_pow, mul_assoc, coeff_C_mul, coeff_X_pow_mul', add_comm (1 : ℝ[X]) X,
    coeff_X_add_one_pow]
  rw [Finset.sum_ite_eq, sum_catalan_mul_choose, mul_assoc]
  split_ifs with h
  · rfl
  · rw [mem_range] at h
    rw [Nat.choose_eq_zero_of_lt (by omega : m + 1 < i + 1)]; simp

end ShiftedNarayana

/-- **`Ñ_m(x) = Q_m(1 + x, x)`.** For every `m`, the shifted Narayana polynomial equals the
evaluation of `narayanaQ ℝ m` at `A = 1 + X`, `B = X`: evaluating `Q_m` termwise gives the
γ-expansion `shiftedNarayanaGammaExpansion_holds`. -/
@[lognarayana "lem_shifted_narayana_eq_q"]
public theorem shiftedNarayanaPolynomial_eq_aeval_narayanaQ (m : ℕ) :
    shiftedNarayanaPolynomial m = MvPolynomial.aeval ![1 + X, X] (narayanaQ ℝ m) := by
  simp [shiftedNarayanaGammaExpansion_holds m, narayanaQ]

/-! ### The quadratic recurrence of `Ñ_m` -/

section ShiftedNarayanaRecurrence

open Finset

/-- Upper Vandermonde: `∑_{p+q=m} C(p,r) C(q,s) = C(m+1, r+s+1)`. -/
private theorem sum_antidiagonal_choose_mul_choose (r s m : ℕ) :
    ∑ pq ∈ antidiagonal m, pq.1.choose r * pq.2.choose s = (m + 1).choose (r + s + 1) := by
  have key : ∀ r : ℕ, (PowerSeries.mk fun p => ((p.choose r : ℕ) : ℤ)) =
      PowerSeries.X ^ r * (PowerSeries.mk 1) ^ (r + 1) := by
    intro r
    ext p
    rw [PowerSeries.mk_one_pow_eq_mk_choose_add, PowerSeries.coeff_X_pow_mul',
      PowerSeries.coeff_mk]
    split_ifs with h
    · rw [PowerSeries.coeff_mk, Nat.add_sub_cancel' h]
    · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero]
  have h := congrArg (PowerSeries.coeff (m + 1))
    (show PowerSeries.X * ((PowerSeries.mk fun p => ((p.choose r : ℕ) : ℤ)) *
        (PowerSeries.mk fun p => ((p.choose s : ℕ) : ℤ))) =
      PowerSeries.mk fun p => ((p.choose (r + s + 1) : ℕ) : ℤ) by
      rw [key, key, key]; ring)
  rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mul, PowerSeries.coeff_mk] at h
  simp only [PowerSeries.coeff_mk] at h
  exact_mod_cast h

variable {S : Type*} [CommSemiring S]

/-- `Q_m(A, B) = ∑_{j ≤ m} C_j (m choose 2j) B^j A^(m-2j)`, for `A`, `B` in a commutative
semiring. -/
private noncomputable def catalanSum (A B : S) (m : ℕ) : S :=
  ∑ j ∈ range (m + 1), ((catalan j * m.choose (2 * j) : ℕ) : S) * B ^ j * A ^ (m - 2 * j)

/-- The summand of `catalanSum`. -/
private noncomputable def catalanTerm (A B : S) (m j : ℕ) : S :=
  ((catalan j * m.choose (2 * j) : ℕ) : S) * B ^ j * A ^ (m - 2 * j)

private theorem catalanSum_eq_sum_range (A B : S) {m N : ℕ} (hN : m / 2 < N) :
    catalanSum A B m = ∑ j ∈ range N, catalanTerm A B m j := by
  have h : ∀ M, m / 2 < M →
      ∑ j ∈ range M, catalanTerm A B m j = ∑ j ∈ range (m / 2 + 1), catalanTerm A B m j := by
    intro M hM
    refine (sum_subset (range_subset_range.2 (by omega)) fun j hj hj' => ?_).symm
    simp only [mem_range, not_lt] at hj hj'
    simp [catalanTerm, Nat.choose_eq_zero_of_lt (by omega : m < 2 * j)]
  rw [show catalanSum A B m = ∑ j ∈ range (m + 1), catalanTerm A B m j from rfl,
    h _ (by omega), h _ hN]

/-- `B Q_p Q_q`, expanded as a double sum over `i, k ≤ p + q`. -/
private theorem mul_catalanSum_mul (A B : S) {m p q : ℕ} (hpq : p + q = m) :
    B * (catalanSum A B p * catalanSum A B q) =
      ∑ i ∈ range (m + 1), ∑ k ∈ range (m + 1),
      ((catalan i * catalan k * (p.choose (2 * i) * q.choose (2 * k)) : ℕ) : S) *
        (B ^ (i + k + 1) * A ^ (m - 2 * (i + k))) := by
  rw [catalanSum_eq_sum_range A B (N := m + 1) (by omega),
    catalanSum_eq_sum_range A B (N := m + 1) (by omega), sum_mul_sum, mul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun k _ => ?_
  simp only [catalanTerm]
  by_cases hi : 2 * i ≤ p
  · by_cases hk : 2 * k ≤ q
    · have : m - 2 * (i + k) = (p - 2 * i) + (q - 2 * k) := by omega
      rw [this]; push_cast; ring
    · simp [Nat.choose_eq_zero_of_lt (by omega : q < 2 * k)]
  · simp [Nat.choose_eq_zero_of_lt (by omega : p < 2 * i)]

/-- Regrouping a double sum over a square by antidiagonals, when the terms vanish above the
antidiagonal `i + k = m`. -/
private theorem sum_range_sum_range_eq_sum_antidiagonal {m : ℕ} (F : ℕ → ℕ → S)
    (hF : ∀ i k, m < i + k → F i k = 0) :
    ∑ i ∈ range (m + 1), ∑ k ∈ range (m + 1), F i k =
      ∑ j ∈ range (m + 1), ∑ pq ∈ antidiagonal j, F pq.1 pq.2 := by
  simp_rw [Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have hc : ∑ j ∈ range (m + 1), ∑ i ∈ range (j + 1), F i (j - i) =
      ∑ i ∈ range (m + 1), ∑ j ∈ Ico i (m + 1), F i (j - i) :=
    sum_comm' fun j i => by simp only [mem_range, mem_Ico]; omega
  rw [hc]
  refine sum_congr rfl fun i hi => ?_
  rw [mem_range] at hi
  rw [sum_Ico_eq_sum_range]
  simp_rw [Nat.add_sub_cancel_left]
  refine (sum_subset (range_subset_range.2 (by omega)) fun k _ hk => ?_).symm
  simp only [mem_range, not_lt] at hk
  exact hF i k (by omega)

/-- The convolution `B ∑_{p+q=m} Q_p Q_q`, by Vandermonde and the Catalan recurrence. -/
private theorem mul_sum_antidiagonal_catalanSum (A B : S) (m : ℕ) :
    B * ∑ pq ∈ antidiagonal m, catalanSum A B pq.1 * catalanSum A B pq.2 =
      ∑ j ∈ range (m + 1), ((catalan (j + 1) * (m + 1).choose (2 * j + 1) : ℕ) : S) *
        (B ^ (j + 1) * A ^ (m - 2 * j)) := by
  rw [mul_sum, sum_congr rfl fun pq hpq => mul_catalanSum_mul A B (mem_antidiagonal.1 hpq),
    sum_comm]
  have h1 : ∀ i k, ∑ pq ∈ antidiagonal m,
      ((catalan i * catalan k * (pq.1.choose (2 * i) * pq.2.choose (2 * k)) : ℕ) : S) *
        (B ^ (i + k + 1) * A ^ (m - 2 * (i + k))) =
      ((catalan i * catalan k * (m + 1).choose (2 * (i + k) + 1) : ℕ) : S) *
        (B ^ (i + k + 1) * A ^ (m - 2 * (i + k))) := by
    intro i k
    rw [← sum_mul, ← Nat.cast_sum, ← mul_sum, sum_antidiagonal_choose_mul_choose,
      show 2 * i + 2 * k + 1 = 2 * (i + k) + 1 by ring]
  simp_rw [fun i => (sum_comm (s := antidiagonal m) (t := range (m + 1))
    (f := fun pq k => ((catalan i * catalan k * (pq.1.choose (2 * i) * pq.2.choose (2 * k)) : ℕ) :
      S) * (B ^ (i + k + 1) * A ^ (m - 2 * (i + k))))), h1]
  rw [sum_range_sum_range_eq_sum_antidiagonal (m := m)]
  · refine sum_congr rfl fun j _ => ?_
    rw [catalan_succ', Nat.cast_mul, Nat.cast_sum, sum_mul, sum_mul]
    refine sum_congr rfl fun pq hpq => ?_
    rw [mem_antidiagonal.1 hpq]
    push_cast; ring
  · intro i k hik
    rw [Nat.choose_eq_zero_of_lt (by omega : m + 1 < 2 * (i + k) + 1)]
    simp

/-- `Q_{m+2} - A Q_{m+1}`, by Pascal's rule on the top index. -/
private theorem catalanSum_add_two (A B : S) (m : ℕ) :
    catalanSum A B (m + 2) = A * catalanSum A B (m + 1) +
      ∑ j ∈ range (m + 1), ((catalan (j + 1) * (m + 1).choose (2 * j + 1) : ℕ) : S) *
        (B ^ (j + 1) * A ^ (m - 2 * j)) := by
  have hterm : ∀ j, catalanTerm A B (m + 2) (j + 1) =
      ((catalan (j + 1) * (m + 1).choose (2 * j + 1) : ℕ) : S) * (B ^ (j + 1) * A ^ (m - 2 * j)) +
        A * catalanTerm A B (m + 1) (j + 1) := by
    intro j
    simp only [catalanTerm]
    rw [show m + 2 - 2 * (j + 1) = m - 2 * j by omega,
      show 2 * (j + 1) = 2 * j + 1 + 1 by ring, Nat.choose_succ_succ (m + 1) (2 * j + 1)]
    by_cases h : 2 * j + 1 + 1 ≤ m + 1
    · have : A * A ^ (m + 1 - (2 * j + 1 + 1)) = A ^ (m - 2 * j) := by
        rw [← pow_succ', show m + 1 - (2 * j + 1 + 1) + 1 = m - 2 * j by omega]
      rw [show ∀ c : S, A * (c * B ^ (j + 1) * A ^ (m + 1 - (2 * j + 1 + 1))) =
        c * B ^ (j + 1) * (A * A ^ (m + 1 - (2 * j + 1 + 1))) from fun c => by ring, this]
      push_cast; ring
    · rw [Nat.choose_eq_zero_of_lt (by omega : m + 1 < 2 * j + 1 + 1)]
      push_cast; ring
  rw [catalanSum_eq_sum_range A B (m := m + 2) (N := m + 2 + 1) (by omega),
    sum_range_succ' (fun j => catalanTerm A B (m + 2) j),
    catalanSum_eq_sum_range A B (m := m + 1) (N := m + 2 + 1) (by omega),
    sum_range_succ' (fun j => catalanTerm A B (m + 1) j), sum_congr rfl fun j _ => hterm j,
    sum_add_distrib, ← mul_sum, sum_range_succ (n := m + 1)
      (fun j => ((catalan (j + 1) * (m + 1).choose (2 * j + 1) : ℕ) : S) *
        (B ^ (j + 1) * A ^ (m - 2 * j))),
    Nat.choose_eq_zero_of_lt (by omega : m + 1 < 2 * (m + 1) + 1)]
  simp only [catalanTerm, mul_zero, Nat.cast_zero, zero_mul, add_zero, catalan_zero,
    Nat.choose_zero_right, pow_zero, mul_one, one_mul, Nat.cast_one, Nat.sub_zero]
  ring

/-- The recurrence `Q_{m+2} = A Q_{m+1} + B ∑_{p+q=m} Q_p Q_q`. -/
private theorem catalanSum_add_two_eq (A B : S) (m : ℕ) :
    catalanSum A B (m + 2) = A * catalanSum A B (m + 1) +
      B * ∑ pq ∈ antidiagonal m, catalanSum A B pq.1 * catalanSum A B pq.2 := by
  rw [catalanSum_add_two, mul_sum_antidiagonal_catalanSum]

/-- `Ñ_m = Q_m(1 + x, x)`, from the γ-expansion. -/
private theorem shiftedNarayanaPolynomial_eq_catalanSum (m : ℕ) :
    shiftedNarayanaPolynomial m = catalanSum (1 + X) X m := by
  rw [shiftedNarayanaGammaExpansion_holds m,
    catalanSum_eq_sum_range (1 + X) X (N := m / 2 + 1) (by omega)]
  refine sum_congr rfl fun j _ => ?_
  simp only [catalanTerm]
  rw [← map_natCast C]
  push_cast
  ring

/-- The quadratic recurrence of the shifted Narayana polynomials:
`Ñ_{m+2} = (1 + x) Ñ_{m+1} + x ∑_{p+q=m} Ñ_p Ñ_q`. -/
public theorem shiftedNarayanaPolynomial_add_two (m : ℕ) :
    shiftedNarayanaPolynomial (m + 2) = (1 + X) * shiftedNarayanaPolynomial (m + 1) +
      X * ∑ pq ∈ antidiagonal m,
        shiftedNarayanaPolynomial pq.1 * shiftedNarayanaPolynomial pq.2 := by
  simp only [shiftedNarayanaPolynomial_eq_catalanSum]
  exact catalanSum_add_two_eq _ _ m

end ShiftedNarayanaRecurrence
