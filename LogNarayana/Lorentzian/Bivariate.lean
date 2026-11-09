/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module
public import LogNarayana.Polynomial.LogConcave.Defs
public import LogNarayana.Lorentzian.Hessian.Basic

/-!
# The bivariate criterion

Let `f ∈ ℝ[x]`, `d ∈ ℕ`, and let `hom_d(f) = ∑_{k + l = d} ([x^k] f) x^k y^l` be its
homogenization of degree `d` in the two variables `x, y`. When `f` has nonnegative coefficients
and degree at most `d`, `hom_d(f)` is Lorentzian if and only if `f` is ultra-log-concave of
order `d`.

The proof checks the two clauses of the definition of a Lorentzian polynomial separately.
Writing `b_k = [x^k] f` and `a_k = b_k / (d choose k)`:

* the support of `hom_d(f)` is `{(j, d - j) : j ≤ d, a_j > 0}`, and for nonnegative `a₀, …, a_d`,
  not all zero, this set is M-convex iff `(a_j)` has no internal zeros: an exchange moves one
  unit between the two coordinates;
* for `1 ≤ j ≤ d - 1` the Hessian at the origin of `∂^(j-1, d-j-1) hom_d(f)` is
  ```
  ( (j+1)! (d-j-1)! b_{j+1}    j! (d-j)! b_j           )
  ( j! (d-j)! b_j              (j-1)! (d-j+1)! b_{j-1} )
  ```
  which is `d!` times `!![a_{j+1}, a_j; a_j, a_{j-1}]`, so it has at most one positive
  eigenvalue iff `a_{j-1} a_{j+1} ≤ a_j ^ 2`.

## Main results

* `Polynomial.hessianAtZero_iteratedPDeriv_homogenize`: the Hessian formula above.
* `Set.isMConvex_bivariateSupport_iff_hasNoInternalZeros`: M-convexity of a bivariate support.
* `Polynomial.isLorentzian_homogenize_iff_isUltraLogConcave`: the bivariate criterion.

## Implementation notes

The homogenization is Mathlib's `Polynomial.homogenize f d : MvPolynomial (Fin 2) ℝ`, in which
`x` is `X 0` and `y` is `X 1`; accordingly the multi-index `(a, b)` is
`Finsupp.single 0 a + Finsupp.single 1 b` and Hessians are indexed by `Fin 2`. The Hessian
formula does not need the paper's hypothesis `deg f ≤ d`: `homogenize f d` only involves the
coefficients `[x^k] f` with `k ≤ d`. Nonnegativity of the coefficients is
`∀ i, 0 ≤ f.coeff i`, and `deg f ≤ d` is `f.natDegree ≤ d`.

## References

* [LogNarayana]
-/

open MvPolynomial Finsupp

/-! ### The Hessians of the derivatives of `hom_d(f)` -/

namespace Polynomial

/-- The factorial of the bivariate multi-index `(a, b)` is `a! b!`. -/
private lemma factorial_single_add_single (a b : ℕ) :
    (single (0 : Fin 2) a + single 1 b).factorial = a.factorial * b.factorial := by
  unfold Finsupp.factorial
  rw [Finsupp.prod_fintype _ _ (fun _ => rfl), Fin.prod_univ_two]
  simp

/-- The `(a, b)` coefficient of `homogenize f d` is `[x^a] f` when `a + b = d`. -/
private lemma coeff_homogenize_single (f : ℝ[X]) {a b d : ℕ} (h : a + b = d) :
    MvPolynomial.coeff (single (0 : Fin 2) a + single 1 b) (f.homogenize d) = f.coeff a := by
  rw [coeff_homogenize]
  simp [h]

/-- Adding `e_p + e_q` to the bivariate multi-index `(a, b)` gives `(a', b')`. -/
private lemma single_add_single_add_single_add_single {a b a' b' : ℕ} {p q : Fin 2}
    (h : (if p = 0 then 1 else 0) + (if q = 0 then 1 else 0) + a = a')
    (h' : (if p = 1 then 1 else 0) + (if q = 1 then 1 else 0) + b = b') :
    single (0 : Fin 2) a + single 1 b + single p 1 + single q 1 = single 0 a' + single 1 b' := by
  ext i
  fin_cases i <;> fin_cases p <;> fin_cases q <;> simp_all <;> omega

/-- The `(p, q)` entry of the Hessian of `∂^(a, b) hom_d(f)` is `a'! b'! [x^a'] f`, where
`(a', b') = (a, b) + e_p + e_q` and `a' + b' = d`. -/
private lemma hessianAtZero_iteratedPDeriv_homogenize_apply (f : ℝ[X]) {a b a' b' d : ℕ}
    (p q : Fin 2) (h : (if p = 0 then 1 else 0) + (if q = 0 then 1 else 0) + a = a')
    (h' : (if p = 1 then 1 else 0) + (if q = 1 then 1 else 0) + b = b') (hd : a' + b' = d) :
    hessianAtZero (iteratedPDeriv (single 0 a + single 1 b) (f.homogenize d)) p q =
      (a'.factorial * b'.factorial : ℝ) * f.coeff a' := by
  rw [hessianAtZero_iteratedPDeriv_apply, single_add_single_add_single_add_single h h',
    factorial_single_add_single, coeff_homogenize_single f hd]
  push_cast
  rfl

/-- For `1 ≤ j ≤ d - 1`, the Hessian at the origin of `∂^(j-1, d-j-1)` applied to the degree-`d`
homogenization of `f` is the `2 × 2` matrix with entries `(j+1)! (d-j-1)! b_{j+1}`,
`j! (d-j)! b_j` (off the diagonal) and `(j-1)! (d-j+1)! b_{j-1}`, where `b_k = f.coeff k`. -/
@[lognarayana "lem_bivariate_derivative_hessian"]
public theorem hessianAtZero_iteratedPDeriv_homogenize (f : ℝ[X]) {d j : ℕ} (hj : 1 ≤ j)
    (hjd : j ≤ d - 1) :
    hessianAtZero
        (iteratedPDeriv (Finsupp.single 0 (j - 1) + Finsupp.single 1 (d - j - 1))
          (f.homogenize d)) =
      !![((j + 1).factorial * (d - j - 1).factorial : ℝ) * f.coeff (j + 1),
          (j.factorial * (d - j).factorial : ℝ) * f.coeff j;
        (j.factorial * (d - j).factorial : ℝ) * f.coeff j,
          ((j - 1).factorial * (d - j + 1).factorial : ℝ) * f.coeff (j - 1)] := by
  ext p q
  fin_cases p <;> fin_cases q <;>
    exact hessianAtZero_iteratedPDeriv_homogenize_apply f _ _
      (by simp <;> omega) (by simp <;> omega) (by omega)

end Polynomial

/-! ### M-convexity of a bivariate support -/

/-- A sequence with no internal zeros is positive between any two positive values, endpoints
included. -/
private lemma HasNoInternalZeros.pos_of_le {d : ℕ} {a : ℕ → ℝ} (h : HasNoInternalZeros d a)
    {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) (hkd : k ≤ d) (hi : 0 < a i) (hk : 0 < a k) :
    0 < a j := by
  rcases hij.lt_or_eq with hij | rfl
  · rcases hjk.lt_or_eq with hjk | rfl
    · exact h i j k hij hjk hkd hi hk
    · exact hk
  · exact hi

namespace Set

/-- The bivariate support, described by coordinates. -/
private lemma bivariateSupport_eq (d : ℕ) (a : ℕ → ℝ) :
    {α : Fin 2 →₀ ℕ | ∃ j ≤ d, 0 < a j ∧ α = single 0 j + single 1 (d - j)} =
      {α | α 0 + α 1 = d ∧ 0 < a (α 0)} := by
  ext α
  constructor
  · rintro ⟨j, hj, hpos, rfl⟩
    simp [hpos]
    omega
  · rintro ⟨hd, hpos⟩
    exact ⟨α 0, by omega, hpos, by ext n; fin_cases n <;> simp; omega⟩

/-- The set `{α | α 0 + α 1 = d ∧ 0 < a (α 0)}` is M-convex iff `a` has no internal zeros. -/
private lemma isMConvex_setOf_add_eq_iff (d : ℕ) (a : ℕ → ℝ) (hne : ∃ j ≤ d, 0 < a j) :
    IsMConvex {α : Fin 2 →₀ ℕ | α 0 + α 1 = d ∧ 0 < a (α 0)} ↔ HasNoInternalZeros d a := by
  constructor
  · rintro ⟨-, -, -, hex⟩ i j k hij hjk hkd hi hk
    have step : ∀ q < k, 0 < a q → 0 < a (q + 1) := fun q hq hpos => by
      obtain ⟨n, hn, h, -⟩ := hex (single 0 q + single 1 (d - q)) (by simp [hpos]; omega)
        (single 0 k + single 1 (d - k)) (by simp [hk]; omega) 1 (by simp; omega)
      fin_cases n
      · simpa using h.2
      · simp at hn; omega
    have key : ∀ r, i ≤ r → r < k → 0 < a r := fun r hr => by
      induction r, hr using Nat.le_induction with
      | base => exact fun _ => hi
      | succ r _ ih => exact fun hrk => step r (by omega) (ih (by omega))
    exact key j hij.le hjk
  · intro h
    refine ⟨?_, ?_, ⟨d, fun α hα => by simpa [degree_eq_sum] using hα.1⟩, ?_⟩
    · exact (finite_Iic (single 0 d + single 1 d)).subset fun α ⟨hd, _⟩ n => by
        fin_cases n <;> simp <;> omega
    · obtain ⟨j, hj, hpos⟩ := hne
      exact ⟨single 0 j + single 1 (d - j), by simp [hpos]; omega⟩
    · rintro α ⟨hα, hαa⟩ β ⟨hβ, hβa⟩ i hi
      fin_cases i <;> simp at hi
      · refine ⟨1, by omega, ⟨by simp; omega, ?_⟩, ⟨by simp; omega, ?_⟩⟩ <;>
          simp only [Fin.zero_eta, Fin.isValue, Finsupp.coe_add, coe_tsub, Pi.add_apply,
            Pi.sub_apply, single_eq_same, ne_eq, zero_ne_one, not_false_eq_true, single_eq_of_ne,
            add_zero, tsub_zero] <;>
          exact h.pos_of_le (by omega) (by omega) (by omega) hβa hαa
      · refine ⟨0, by omega, ⟨by simp; omega, ?_⟩, ⟨by simp; omega, ?_⟩⟩ <;>
          simp only [Fin.mk_one, Fin.isValue, Finsupp.coe_add, coe_tsub, Pi.add_apply,
            Pi.sub_apply, single_eq_same, ne_eq, zero_ne_one, not_false_eq_true, single_eq_of_ne,
            add_zero, tsub_zero] <;>
          exact h.pos_of_le (by omega) (by omega) (by omega) hαa hβa

/-- For nonnegative `a₀, …, a_d`, not all zero, the set `{(j, d - j) : j ≤ d, 0 < a_j}` of
exponents in two variables is M-convex iff `(a_j)_{j=0}^d` has no internal zeros. -/
@[lognarayana "lem_bivariate_support_mconvex_iff"]
public theorem isMConvex_bivariateSupport_iff_hasNoInternalZeros (d : ℕ) (a : ℕ → ℝ)
    (ha : ∀ j ≤ d, 0 ≤ a j) (hne : ∃ j ≤ d, a j ≠ 0) :
    IsMConvex {α : Fin 2 →₀ ℕ | ∃ j ≤ d, 0 < a j ∧
        α = Finsupp.single 0 j + Finsupp.single 1 (d - j)} ↔
      HasNoInternalZeros d a := by
  obtain ⟨j, hj, hj0⟩ := hne
  rw [bivariateSupport_eq]
  exact isMConvex_setOf_add_eq_iff d a ⟨j, hj, (ha j hj).lt_of_ne' hj0⟩

end Set

/-! ### The bivariate criterion -/

/-- A nonzero homogeneous polynomial of degree `d` with nonnegative coefficients is Lorentzian
iff it satisfies the degree-`d` clause of the definition. -/
private lemma MvPolynomial.isLorentzian_iff_of_isHomogeneous {σ : Type*} [Fintype σ]
    {g : MvPolynomial σ ℝ} {d : ℕ} (hg : g.IsHomogeneous d) (hg0 : g ≠ 0)
    (hnn : g.HasNonnegCoeffs) :
    g.IsLorentzian ↔ (d ≤ 1 ∨ (2 ≤ d ∧ (g.support : Set (σ →₀ ℕ)).IsMConvex ∧
      ∀ α : σ →₀ ℕ, α.degree = d - 2 →
        (hessianAtZero (iteratedPDeriv α g)).HasAtMostOnePosEigenvalue)) := by
  refine ⟨?_, fun H => Or.inr ⟨d, hg, hnn, H⟩⟩
  rintro (h | ⟨e, he, -, H⟩)
  · exact absurd h hg0
  · rwa [he.inj_right hg hg0] at H

namespace Polynomial

/-- The support of `hom_d(f)` is the set of exponents `(j, d - j)` with
`0 < b_j / (d choose j)`. -/
private lemma support_homogenize (f : ℝ[X]) (hf : ∀ i, 0 ≤ f.coeff i) (d : ℕ) :
    ((f.homogenize d).support : Set (Fin 2 →₀ ℕ)) =
      {α | ∃ j ≤ d, 0 < f.coeff j / (d.choose j : ℝ) ∧ α = single 0 j + single 1 (d - j)} := by
  ext α
  simp only [Finset.mem_coe, MvPolynomial.mem_support_iff, coeff_homogenize, Set.mem_ofPred_eq]
  constructor
  · intro h
    split_ifs at h with hα
    · refine ⟨α 0, by omega, div_pos ((hf _).lt_of_ne' h) (mod_cast Nat.choose_pos (by omega)),
        ?_⟩
      ext i
      fin_cases i <;> simp
      omega
    · exact absurd rfl h
  · rintro ⟨j, hj, hpos, rfl⟩
    simp only [Finsupp.coe_add, Pi.add_apply, single_eq_same, ne_eq, zero_ne_one,
      not_false_eq_true, single_eq_of_ne, add_zero, one_ne_zero, zero_add,
      Nat.add_sub_cancel' hj, ↓reduceIte]
    intro h0
    simp [h0] at hpos

/-- `k! (d - k)! b = d! (b / (d choose k))` for `k ≤ d`. -/
private lemma factorial_mul_factorial_mul_eq {d k : ℕ} (hk : k ≤ d) (b : ℝ) :
    (k.factorial * (d - k).factorial : ℝ) * b = d.factorial * (b / (d.choose k : ℝ)) := by
  have hc : (d.choose k : ℝ) ≠ 0 := mod_cast (Nat.choose_pos hk).ne'
  rw [← Nat.choose_mul_factorial_mul_factorial hk]
  push_cast
  field_simp

/-- The Hessian condition at `∂^(j, d-j-2) hom_d(f)` is the log-concavity inequality
`a_j a_{j+2} ≤ a_{j+1} ^ 2` for `a_i = b_i / (d choose i)`. -/
private lemma hasAtMostOnePosEigenvalue_hessian_homogenize_iff {d : ℕ} (f : ℝ[X])
    (hf : ∀ i, 0 ≤ f.coeff i) {j : ℕ} (hj : j + 2 ≤ d) :
    (hessianAtZero (iteratedPDeriv (single 0 j + single 1 (d - (j + 2)))
      (f.homogenize d))).HasAtMostOnePosEigenvalue ↔
      f.coeff j / (d.choose j : ℝ) * (f.coeff (j + 2) / (d.choose (j + 2) : ℝ)) ≤
        (f.coeff (j + 1) / (d.choose (j + 1) : ℝ)) ^ 2 := by
  have H := hessianAtZero_iteratedPDeriv_homogenize f (d := d) (j := j + 1) (by omega)
    (by omega)
  rw [show j + 1 - 1 = j by omega, show d - (j + 1) - 1 = d - (j + 2) by omega,
    show d - (j + 1) + 1 = d - j by omega] at H
  have e2 := factorial_mul_factorial_mul_eq (k := j + 2) hj (f.coeff (j + 2))
  have e1 := factorial_mul_factorial_mul_eq (d := d) (k := j + 1) (by omega) (f.coeff (j + 1))
  have e0 := factorial_mul_factorial_mul_eq (d := d) (k := j) (by omega) (f.coeff j)
  rw [H, Matrix.hasAtMostOnePosEigenvalue_fin_two_iff (by have := hf (j + 2); positivity),
    e2, e1, e0, mul_pow, mul_mul_mul_comm, mul_comm (_ / _),
    ← sq, mul_le_mul_iff_right₀ (by positivity)]

/-- For `2 ≤ d`, on `hom_d(f)` the Hessian clause of the Lorentzian property is the
log-concavity of `a_j = b_j / (d choose j)`. -/
private lemma forall_hasAtMostOnePosEigenvalue_hessian_homogenize_iff {d : ℕ} (hd : 2 ≤ d)
    (f : ℝ[X]) (hf : ∀ i, 0 ≤ f.coeff i) :
    (∀ α : Fin 2 →₀ ℕ, α.degree = d - 2 →
        (hessianAtZero (iteratedPDeriv α (f.homogenize d))).HasAtMostOnePosEigenvalue) ↔
      ∀ j, j + 2 ≤ d → f.coeff j / (d.choose j : ℝ) *
        (f.coeff (j + 2) / (d.choose (j + 2) : ℝ)) ≤
          (f.coeff (j + 1) / (d.choose (j + 1) : ℝ)) ^ 2 := by
  refine ⟨fun H j hj => (hasAtMostOnePosEigenvalue_hessian_homogenize_iff f hf hj).1
    (H _ ?_), fun H α hα => ?_⟩
  · rw [map_add, degree_single, degree_single]
    omega
  · rw [degree_eq_sum, Fin.sum_univ_two] at hα
    have hαe : α = single 0 (α 0) + single 1 (d - (α 0 + 2)) := by
      ext i; fin_cases i <;> simp; omega
    rw [hαe]
    exact (hasAtMostOnePosEigenvalue_hessian_homogenize_iff f hf (by omega)).2 (H _ (by omega))

/-- For `f ∈ ℝ[x]` with nonnegative coefficients and `deg f ≤ d`, the degree-`d`
homogenization of `f` is Lorentzian if and only if `f` is ultra-log-concave of order `d`. -/
@[lognarayana "lem_bivariate_lorentzian_iff_ulc"]
public theorem isLorentzian_homogenize_iff_isUltraLogConcave {d : ℕ} {f : ℝ[X]}
    (hf : ∀ i, 0 ≤ f.coeff i) (hdeg : f.natDegree ≤ d) :
    (f.homogenize d).IsLorentzian ↔ f.IsUltraLogConcave d := by
  have ha : ∀ j ≤ d, 0 ≤ f.coeff j / (d.choose j : ℝ) := fun j _ =>
    div_nonneg (hf j) (Nat.cast_nonneg _)
  rcases eq_or_ne f 0 with rfl | hf0
  · simp only [homogenize_zero]
    exact ⟨fun _ => ⟨by simp, ⟨fun j _ => by simp, fun j _ => by simp⟩,
      fun i j k _ _ _ h => by simp at h⟩, fun _ => Or.inl rfl⟩
  have hnn : (f.homogenize d).HasNonnegCoeffs := by
    intro α
    rw [coeff_homogenize]
    split_ifs <;> simp [hf]
  rw [isLorentzian_iff_of_isHomogeneous (isHomogeneous_homogenize f)
    (by rwa [Ne, homogenize_eq_zero_iff hdeg]) hnn, IsUltraLogConcave, IsLogConcaveSeq]
  rcases le_or_gt d 1 with hd1 | hd2
  · simp only [hd1, true_or, true_iff]
    exact ⟨hdeg, ⟨ha, fun j hj => by omega⟩, fun i j k hij hjk hkd _ _ => by omega⟩
  · rw [support_homogenize f hf d, Set.isMConvex_bivariateSupport_iff_hasNoInternalZeros d _ ha
      ⟨f.natDegree, hdeg, div_ne_zero (leadingCoeff_ne_zero.mpr hf0)
        (mod_cast (Nat.choose_pos hdeg).ne')⟩,
      forall_hasAtMostOnePosEigenvalue_hessian_homogenize_iff hd2 f hf]
    simp only [show 2 ≤ d from hd2, true_and, hdeg, show ¬ d ≤ 1 by omega, false_or]
    tauto

end Polynomial
