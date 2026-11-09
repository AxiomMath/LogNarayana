/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib
public import LogNarayana.Attr
public import LogNarayana.Narayana.RealRootedTransform.Defs
public import LogNarayana.Narayana.SignedAppell.Defs
public import LogNarayana.Narayana.Polynomials.Defs
public import LogNarayana.Lorentzian.MConvex.Defs
public import LogNarayana.Polynomial.RealStable.Defs
public import LogNarayana.Narayana.AppellOperator.Defs
public import LogNarayana.Narayana.Transform.Defs
public import LogNarayana.Narayana.SignedAppell.Basic
public import LogNarayana.Narayana.Polynomials.Basic
public import LogNarayana.Polynomial.RealStable.Basic
public import LogNarayana.Narayana.AppellOperator.Basic
public import LogNarayana.Narayana.Transform.Basic

/-!
# The diagonal and gamma transforms; proof of Theorem 1.4

The diagonal Appell transform `𝓗`, the Narayana transform `𝒩` and its deformation `𝒩_λ` are all
governed by the gamma transform `Γ`, through the factorwise identities
`η_m(t) = t^m M_m(-t⁻²)`, `Ñ_m(x) = (1 + x)^m M_m(x / (1 + x)²)` and
`Q_m(1 + x, λ x) = (1 + x)^m M_m(λ x / (1 + x)²)`. For `F` homogeneous of degree `D` this gives
`𝓗_F(t) = t^D Γ_F(-t⁻²)`, `𝒩(F)(x) = (1 + x)^D Γ_F(x / (1 + x)²)` and
`𝒩_λ(F)(x) = (1 + x)^D Γ_F(λ x / (1 + x)²)`.

If `F` is moreover real-stable with nonnegative coefficients, `𝓗_F` is real-rooted (the Appell
operator preserves real stability), has parity `(-1)^D` and top coefficient `∑_α [z^α]F`, so it
factors as `c t^{D - 2ℓ} ∏_j (t² - ρ_j²)`. Transporting this through `Γ` gives
`Γ_F(u) = c ∏_j (1 + ρ_j² u)`, hence `𝒩(F)(x) = c (1 + x)^{D - 2ℓ} ∏_j ((1 + x)² + ρ_j² x)`:
the Narayana transform of `F` has only negative real zeros (Theorem 1.4), and likewise
`𝒩_λ(F)` is real-rooted for `λ ≥ 0` (Corollary 6.3).

## Main results

* `narayanaQ_eval_eq_pow_mul_narayanaM_eval` : `Q_m(A, B) = A^m M_m(B / A²)` for `A ≠ 0`.
* `eval_shiftedNarayanaPolynomial_eq_narayanaM` : `Ñ_m(x) = (1 + x)^m M_m(x / (1 + x)²)`.
* `Polynomial.signedAppell_eval_eq_pow_mul_narayanaM_eval` : `η_m(t) = t^m M_m(-t⁻²)`.
* `MvPolynomial.appellDiagonal_comp_neg_X_of_isHomogeneous` : parity of `𝓗_F`.
* `MvPolynomial.coeff_appellDiagonal_of_isHomogeneous` : the top coefficients of `𝓗_F`.
* `MvPolynomial.eval_appellDiagonal_eq_pow_mul_eval_gammaTransform` : `𝓗_F` through `Γ_F`.
* `MvPolynomial.splits_appellDiagonal_of_isRealStable` : `𝓗_F` is real-rooted.
* `MvPolynomial.appellDiagonal_eq_mul_prod_X_sq_sub_of_isRealStable` : factorization of `𝓗_F`.
* `Polynomial.hasOnlyNegativeRoots_C_mul_one_add_X_pow_mul_prod` : negative zeros of
  `c (1 + x)^e ∏_j ((1 + x)² + β_j x)` for `β_j ≥ 0`.
* `Polynomial.eq_C_mul_one_add_X_pow_mul_prod_of_eval_eq_gamma` : clearing denominators in a
  factored gamma polynomial.
* `MvPolynomial.IsHomogeneous.gammaTransform_eq_C_mul_prod` : factorization of `Γ_F`.
* `MvPolynomial.IsHomogeneous.hasOnlyNegativeRoots_gammaTransform` : `Γ_F` has only negative
  zeros.
* `MvPolynomial.IsHomogeneous.eval_deformedNarayanaTransform_eq_mul_eval_gammaTransform` and
  `MvPolynomial.IsHomogeneous.eval_narayanaTransform_eq_mul_eval_gammaTransform` : `𝒩_λ(F)` and
  `𝒩(F)` through `Γ_F`.
* `MvPolynomial.IsHomogeneous.narayanaTransform_eq_of_gammaTransform_eq` : factorization of
  `𝒩(F)`.
* `MvPolynomial.IsHomogeneous.splits_deformedNarayanaTransform` : Corollary 6.3.
* `MvPolynomial.IsHomogeneous.hasOnlyNegativeRoots_narayanaTransform` : Theorem 1.4.
* `MvPolynomial.splits_narayanaTransform_of_isRealStable` : `𝒩(F)` is real-rooted.

## Implementation notes

Real-rootedness is `Polynomial.Splits` over `ℝ`, and "only negative real zeros" is
`Polynomial.HasOnlyNegativeRoots`. The cited results the proofs rest on (the Borcea–Brändén
symbol theorem `MvPolynomial.RealStablePreserverOfSymbol` and the negative real zeros
`ShiftedNarayanaNegRealRoots` of the shifted Narayana polynomials) are taken as hypotheses; the
symbol theorem is used at variable types other than `σ`, so it is quantified over all types of
the universe of `σ`. The γ-expansion `ShiftedNarayanaGammaExpansion` of the shifted Narayana
polynomials is proved (`shiftedNarayanaGammaExpansion_holds`).

## References

* [LogNarayana], Sections 2.1 and 6, Theorem 1.4 and Corollary 6.3.
-/

universe u

open Polynomial

/-! ### `Q_m`, `Ñ_m` and `η_m` through `M_m` -/

/-- Termwise homogenization: `A^m (B / A²)^j = B^j A^(m - 2j)` for `A ≠ 0` and `2j ≤ m`. -/
private lemma pow_mul_div_sq_pow {A : ℝ} (hA : A ≠ 0) (B : ℝ) {m j : ℕ} (h : 2 * j ≤ m) :
    A ^ m * (B / A ^ 2) ^ j = B ^ j * A ^ (m - 2 * j) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_sub_cancel_left, pow_add, pow_mul, div_pow]
  field_simp


/-- For every `m` and real `A ≠ 0`, `B`: `Q_m(A, B) = A^m M_m(B / A²)`. -/
@[lognarayana "lem_narayana_q_eq_m"]
public theorem narayanaQ_eval_eq_pow_mul_narayanaM_eval (m : ℕ) {A : ℝ} (hA : A ≠ 0) (B : ℝ) :
    MvPolynomial.eval ![A, B] (narayanaQ ℝ m) = A ^ m * (narayanaM ℝ m).eval (B / A ^ 2) := by
  simp only [narayanaQ, narayanaM, map_sum, map_mul, map_pow, MvPolynomial.eval_C,
    MvPolynomial.eval_X, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [mul_left_comm, pow_mul_div_sq_pow hA B (by grind), mul_assoc]
  simp


/-- For every `m` and every real `x ≠ -1`, `Ñ_m(x) = (1 + x)^m M_m(x / (1 + x)^2)`. -/
@[lognarayana "lem_shifted_narayana_eq_m"]
public theorem eval_shiftedNarayanaPolynomial_eq_narayanaM (m : ℕ) {x : ℝ} (hx : x ≠ -1) :
    (shiftedNarayanaPolynomial m).eval x =
      (1 + x) ^ m * (narayanaM ℝ m).eval (x / (1 + x) ^ 2) := by
  have hA : 1 + x ≠ 0 := fun h => hx (by linarith)
  rw [← narayanaQ_eval_eq_pow_mul_narayanaM_eval m hA x,
    shiftedNarayanaPolynomial_eq_aeval_narayanaQ m]
  simp [narayanaQ, eval_finsetSum]


namespace Polynomial

/-- `η_m(t) = Q_m(t, -1)`. -/
private lemma signedAppell_eval_eq_narayanaQ_eval (m : ℕ) (t : ℝ) :
    (signedAppell ℝ m).eval t = MvPolynomial.eval ![t, -1] (narayanaQ ℝ m) := by
  simp only [signedAppell, narayanaQ, eval_finsetSum, map_sum, eval_mul, eval_C, eval_pow,
    eval_X, MvPolynomial.eval_C, MvPolynomial.eval_X, map_mul, map_pow]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  ring


/-- For every `m` and every real `t ≠ 0`, `η_m(t) = t^m M_m(-t⁻²)`. -/
@[lognarayana "lem_signed_appell_eq_m"]
public theorem signedAppell_eval_eq_pow_mul_narayanaM_eval (m : ℕ) {t : ℝ} (ht : t ≠ 0) :
    (signedAppell ℝ m).eval t = t ^ m * (narayanaM ℝ m).eval (-(t ^ 2)⁻¹) := by
  rw [signedAppell_eval_eq_narayanaQ_eval, narayanaQ_eval_eq_pow_mul_narayanaM_eval m ht,
    neg_div, one_div]


/-! ### Even and odd real-rooted polynomials; the top coefficients of `η_m` -/

/-- `η_m` has degree at most `m` and coefficient `1` at `t^m`. -/
private lemma signedAppell_natDegree_le_and_coeff (R : Type*) [Ring R] (m : ℕ) :
    (signedAppell R m).natDegree ≤ m ∧ (signedAppell R m).coeff m = 1 := by
  have h := degree_signedAppell_sub_X_pow_lt R m
  have e : signedAppell R m = X ^ m + (signedAppell R m - X ^ m) := by abel
  refine ⟨natDegree_le_of_degree_le ?_, ?_⟩
  · rw [e]; exact (degree_add_le _ _).trans (max_le (degree_X_pow_le _) h.le)
  · rw [e, coeff_add, coeff_X_pow_self, coeff_eq_zero_of_degree_lt h, add_zero]

/-- A product of polynomials `p i` with `natDegree ≤ n i` and `[t^{n i}] p i = 1` has
`natDegree ≤ ∑ n i` and coefficient `1` at `t^{∑ n i}`. -/
private lemma prod_natDegree_le_and_coeff {R ι : Type*} [CommRing R] (s : Finset ι)
    (p : ι → R[X]) (n : ι → ℕ) (hp : ∀ i ∈ s, (p i).natDegree ≤ n i ∧ (p i).coeff (n i) = 1) :
    (∏ i ∈ s, p i).natDegree ≤ ∑ i ∈ s, n i ∧ (∏ i ∈ s, p i).coeff (∑ i ∈ s, n i) = 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    obtain ⟨h1, h2⟩ := ih fun i hi => hp i (Finset.mem_insert_of_mem hi)
    obtain ⟨h3, h4⟩ := hp a (Finset.mem_insert_self a s)
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact ⟨natDegree_mul_le_of_le h3 h1, by
      rw [coeff_mul_add_eq_of_natDegree_le h3 h1, h4, h2, one_mul]⟩

/-- A multiset of reals stable under negation is its zeros, its positive part, and the negation
of its positive part. -/
private lemma eq_zeros_add_pos_add_neg_of_map_neg_eq {s : Multiset ℝ}
    (hs : s.map (fun x => -x) = s) :
    s = Multiset.replicate (s.count 0) 0 + s.filter (0 < ·) +
      (s.filter (0 < ·)).map (fun x => -x) := by
  classical
  have hN : (s.filter (0 < ·)).map (fun x => -x) = s.filter (· < 0) := by
    conv_rhs => rw [← hs]
    rw [Multiset.filter_map]
    exact congrArg _ (Multiset.filter_congr fun x _ => by simp)
  rw [hN, ← Multiset.filter_eq' s 0]
  ext a
  simp only [Multiset.count_add, Multiset.count_filter]
  rcases lt_trichotomy a 0 with h | rfl | h
  · simp [h, h.ne, h.not_gt]
  · simp
  · simp [h, h.ne', h.not_gt]

/-- A real polynomial that splits and satisfies `p(-t) = (-1)^n p(t)` factors as
`lc(p) · t^{deg p - 2ℓ} · ∏ (t² - ρ_j²)` with all `ρ_j > 0`. -/
private lemma exists_eq_C_mul_X_pow_mul_prod_X_sq_sub {p : ℝ[X]} (hp : p.Splits) {n : ℕ}
    (hpar : p.comp (-X) = (-1) ^ n * p) :
    ∃ (ℓ : ℕ) (ρ : Fin ℓ → ℝ), 2 * ℓ ≤ p.natDegree ∧ (∀ j, 0 < ρ j) ∧
      p = C p.leadingCoeff * X ^ (p.natDegree - 2 * ℓ) * ∏ j, (X ^ 2 - C (ρ j ^ 2)) := by
  have hs : p.roots.map (fun x => -x) = p.roots := by
    rw [← roots_comp_neg_X, hpar, show ((-1 : ℝ[X]) ^ n) = C ((-1) ^ n) by simp,
      roots_C_mul _ (by simp)]
  have hdecomp := eq_zeros_add_pos_add_neg_of_map_neg_eq hs
  set L := (p.roots.filter (0 < ·)).toList
  have hcard : p.natDegree = p.roots.count 0 + 2 * L.length := by
    rw [hp.natDegree_eq_card_roots, Multiset.length_toList]
    conv_lhs => rw [hdecomp]
    simp only [Multiset.card_add, Multiset.card_replicate, Multiset.card_map]
    ring
  refine ⟨L.length, fun j => L[(j : ℕ)], by omega, fun j => ?_, ?_⟩
  · exact (Multiset.mem_filter.mp (Multiset.mem_toList.mp (List.getElem_mem j.isLt))).2
  dsimp only
  conv_lhs => rw [hp.eq_prod_roots, hdecomp]
  rw [Fin.prod_univ_fun_getElem L (fun r => (X ^ 2 - C (r ^ 2) : ℝ[X])), ← Multiset.prod_coe,
    ← Multiset.map_coe, Multiset.coe_toList, show p.natDegree - 2 * L.length = p.roots.count 0
    by omega]
  simp only [Multiset.map_add, Multiset.prod_add, Multiset.map_replicate, Multiset.prod_replicate,
    Multiset.map_map, Function.comp_def, map_zero, sub_zero, mul_assoc, ← Multiset.prod_map_mul]
  congr 3
  refine Multiset.map_congr rfl (fun r _ => ?_)
  rw [C_neg, map_pow]
  ring

end Polynomial


namespace MvPolynomial

/-! ### The diagonal Appell transform -/

/-- A linear map built on the monomial basis sends `c z^α` to `c • f α`. -/
private lemma basisMonomials_constr_monomial {σ R M : Type*} [CommSemiring R] [AddCommMonoid M]
    [Module R M] (f : (σ →₀ ℕ) → M) (α : σ →₀ ℕ) (c : R) :
    (basisMonomials σ R).constr R f (monomial α c) = c • f α := by
  rw [← mul_one c, ← smul_eq_mul, ← MvPolynomial.smul_monomial, map_smul,
    ← congrFun (coe_basisMonomials σ R) α, Module.Basis.constr_basis, smul_eq_mul, mul_one]

private lemma appellDiagonal_monomial {σ R : Type*} [CommRing R] (α : σ →₀ ℕ) (c : R) :
    appellDiagonal σ R (monomial α c) = c • α.prod fun _ m => signedAppell R m := by
  rw [← mul_one c, ← smul_eq_mul, ← MvPolynomial.smul_monomial, map_smul,
    ← congrFun (MvPolynomial.coe_basisMonomials σ R) α, MvPolynomial.appellDiagonal,
    Module.Basis.constr_basis, smul_eq_mul, mul_one]

private lemma gammaTransform_monomial {σ : Type*} (α : σ →₀ ℕ) (c : ℝ) :
    gammaTransform σ ℝ (monomial α c) = c • α.prod fun _ m => narayanaM ℝ m := by
  rw [← mul_one c, ← smul_eq_mul, ← MvPolynomial.smul_monomial, map_smul,
    ← congrFun (coe_basisMonomials σ ℝ) α, gammaTransform, Module.Basis.constr_basis,
    smul_eq_mul, mul_one]

/-- The diagonal Appell transform of `c z^α` has the parity of `|α|`. -/
private lemma appellDiagonal_monomial_comp_neg_X {σ R : Type*} [CommRing R] (α : σ →₀ ℕ)
    (c : R) :
    (appellDiagonal σ R (monomial α c)).comp (-Polynomial.X) =
      (-1) ^ α.degree * appellDiagonal σ R (monomial α c) := by
  rw [appellDiagonal_monomial, smul_comp, Finsupp.prod, Polynomial.prod_comp]
  simp_rw [signedAppell_comp_neg_X, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
    Finsupp.degree_apply, mul_smul_comm]

/-- If `F ∈ R[z_σ]` is homogeneous of degree `D`, then the diagonal Appell transform satisfies
`𝓗_F(-t) = (-1)^D 𝓗_F(t)`. -/
@[lognarayana "lem_appell_diagonal_parity"]
public theorem appellDiagonal_comp_neg_X_of_isHomogeneous {σ : Type*} {R : Type*} [CommRing R]
    {D : ℕ} {F : MvPolynomial σ R} (hF : F.IsHomogeneous D) :
    (appellDiagonal σ R F).comp (-Polynomial.X) = (-1) ^ D * appellDiagonal σ R F := by
  rw [F.as_sum, map_sum, Polynomial.sum_comp, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α hα => ?_
  rw [appellDiagonal_monomial_comp_neg_X, (DFunLike.congr_fun Finsupp.degree_eq_weight_one α).trans
    (hF (MvPolynomial.mem_support_iff.mp hα))]


/-- The diagonal Appell transform of `c z^α` has degree at most `|α|`, with coefficient `c`
at `t^{|α|}`. -/
private lemma coeff_appellDiagonal_monomial {σ R : Type*} [CommRing R] (α : σ →₀ ℕ) (c : R)
    {j : ℕ} (hj : α.degree ≤ j) :
    (appellDiagonal σ R (monomial α c)).coeff j = if j = α.degree then c else 0 := by
  obtain ⟨h1, h2⟩ := prod_natDegree_le_and_coeff α.support (fun i => signedAppell R (α i)) α
    fun i _ => signedAppell_natDegree_le_and_coeff R (α i)
  rw [← Finsupp.degree_apply] at h1 h2
  rw [appellDiagonal_monomial, Polynomial.coeff_smul, smul_eq_mul, Finsupp.prod]
  split_ifs with h
  · rw [h, h2, mul_one]
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), mul_zero]

/-- If `F ∈ R[z_σ]` is homogeneous of degree `D`, then for every `j ≥ D` the coefficient of `t^j`
in the diagonal Appell transform `𝓗_F` is `∑_{α ∈ supp F} [z^α]F` when `j = D`, and `0` when
`j > D`. -/
@[lognarayana "lem_appell_diagonal_top_coeff"]
public theorem coeff_appellDiagonal_of_isHomogeneous {σ : Type*} {R : Type*} [CommRing R]
    {D : ℕ} {F : MvPolynomial σ R} (hF : F.IsHomogeneous D) {j : ℕ} (hj : D ≤ j) :
    (appellDiagonal σ R F).coeff j = if j = D then ∑ α ∈ F.support, F.coeff α else 0 := by
  have hdeg : ∀ α ∈ F.support, α.degree = D := fun α hα => by
    rw [Finsupp.degree_eq_weight_one]; exact hF (MvPolynomial.mem_support_iff.mp hα)
  conv_lhs => rw [F.as_sum]
  rw [map_sum, Polynomial.finsetSum_coeff, Finset.sum_congr rfl fun α hα => by
    rw [coeff_appellDiagonal_monomial α _ ((hdeg α hα).trans_le hj), hdeg α hα]]
  split_ifs <;> simp


/-- On a monomial `c z^α`, `𝓗(c z^α)(t) = t^{|α|} Γ(c z^α)(-t⁻²)`: the factorwise identity
`η_m(t) = t^m M_m(-t⁻²)` multiplied over `α.support`. -/
private lemma eval_appellDiagonal_monomial {σ : Type*} (α : σ →₀ ℕ) (c : ℝ) {t : ℝ}
    (ht : t ≠ 0) :
    (appellDiagonal σ ℝ (monomial α c)).eval t =
      t ^ α.degree * (gammaTransform σ ℝ (monomial α c)).eval (-(t⁻¹) ^ 2) := by
  simp only [appellDiagonal, gammaTransform, basisMonomials_constr_monomial, inv_pow,
    Polynomial.eval_smul, smul_eq_mul, Finsupp.prod, Polynomial.eval_prod,
    signedAppell_eval_eq_pow_mul_narayanaM_eval _ ht, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, Finsupp.degree_apply]
  ring

/-- For `F` homogeneous of degree `D` and real `t ≠ 0`, `𝓗_F(t) = t^D Γ_F(-t⁻²)`. -/
@[lognarayana "lem_appell_diagonal_eq_gamma"]
public theorem eval_appellDiagonal_eq_pow_mul_eval_gammaTransform {σ : Type*} {D : ℕ}
    {F : MvPolynomial σ ℝ} (hF : F.IsHomogeneous D) {t : ℝ} (ht : t ≠ 0) :
    (appellDiagonal σ ℝ F).eval t = t ^ D * (gammaTransform σ ℝ F).eval (-(t⁻¹) ^ 2) := by
  conv_lhs => rw [F.as_sum]
  conv_rhs => rw [F.as_sum]
  simp only [map_sum, Polynomial.eval_finsetSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α hα => ?_
  rw [eval_appellDiagonal_monomial _ _ ht, ← hF (mem_support_iff.mp hα),
    Finsupp.degree_eq_weight_one]
  rfl


/-- Identifying all variables in the Appell operator gives the diagonal Appell transform:
`ϕ(𝔄(F)) = 𝓗_F`, with `ϕ` the renaming of every variable to the single variable `z_*`. -/
private lemma toMvPolynomial_appellDiagonal {σ : Type*} (F : MvPolynomial σ ℝ) :
    toMvPolynomial () (appellDiagonal σ ℝ F) =
      rename (fun _ => ()) (appellOperator ℝ σ F) := by
  refine LinearMap.congr_fun (f := (toMvPolynomial ()).toLinearMap ∘ₗ appellDiagonal σ ℝ)
    (g := (rename fun _ : σ => ()).toLinearMap ∘ₗ appellOperator ℝ σ)
    ((basisMonomials σ ℝ).ext fun α => ?_) F
  simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply,
    appellDiagonal, appellOperator, Module.Basis.constr_basis, Finsupp.prod, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← aeval_algHom_apply, rename_X]
  rfl

/-- If `F ∈ ℝ[z_σ]` is real-stable, then its diagonal Appell transform `𝓗_F` is real-rooted. -/
@[lognarayana "lem_appell_diagonal_real_rooted"]
public theorem splits_appellDiagonal_of_isRealStable
    (hLW : ShiftedNarayanaNegRealRoots)
    {σ : Type*} [Finite σ] (hBB : RealStablePreserverOfSymbol σ)
    {F : MvPolynomial σ ℝ} (hF : F.IsRealStable) :
    (appellDiagonal σ ℝ F).Splits := by
  have hs : (toMvPolynomial () (appellDiagonal σ ℝ F)).IsRealStable := by
    rw [toMvPolynomial_appellDiagonal]
    exact (isRealStable_appellOperator hLW hBB hF).rename _
  refine (isRealStable_toMvPolynomial_iff_splits () fun h0 => ?_).1 hs
  rw [h0, map_zero] at hs
  exact hs (fun _ => Complex.I) (fun _ => by simp) (map_zero _)

/-- If `F ∈ ℝ[z_σ]` is homogeneous of degree `D`, real-stable and has nonnegative coefficients,
then `𝓗_F(t) = (∑_{α ∈ supp F} [z^α]F) · t^{D - 2ℓ} · ∏_{j} (t² - ρ_j²)` for some `ℓ` with
`2ℓ ≤ D` and some positive reals `ρ_1, …, ρ_ℓ`. -/
@[lognarayana "lem_appell_diagonal_factorization"]
public theorem appellDiagonal_eq_mul_prod_X_sq_sub_of_isRealStable
    (hBB : ∀ τ : Type u, RealStablePreserverOfSymbol τ)
    (hLW : ShiftedNarayanaNegRealRoots)
    {σ : Type u} [Finite σ] {D : ℕ} {F : MvPolynomial σ ℝ} (hhom : F.IsHomogeneous D)
    (hstab : F.IsRealStable) (hnn : F.HasNonnegCoeffs) :
    ∃ (ℓ : ℕ) (ρ : Fin ℓ → ℝ), 2 * ℓ ≤ D ∧ (∀ j, 0 < ρ j) ∧
      appellDiagonal σ ℝ F = Polynomial.C (∑ α ∈ F.support, F.coeff α) *
        Polynomial.X ^ (D - 2 * ℓ) * ∏ j, (Polynomial.X ^ 2 - Polynomial.C (ρ j ^ 2)) := by
  have hF0 : F ≠ 0 := by
    rintro rfl
    exact hstab (fun _ => Complex.I) (fun _ => by simp) (map_zero _)
  have hc : 0 < ∑ α ∈ F.support, F.coeff α :=
    Finset.sum_pos (fun α hα => (hnn α).lt_of_ne' (MvPolynomial.mem_support_iff.mp hα))
      (MvPolynomial.support_nonempty.mpr hF0)
  have htop := fun j (hj : D ≤ j) => MvPolynomial.coeff_appellDiagonal_of_isHomogeneous hhom hj
  have hcD : (MvPolynomial.appellDiagonal σ ℝ F).coeff D = ∑ α ∈ F.support, F.coeff α := by
    simpa using htop D le_rfl
  have hdeg : (MvPolynomial.appellDiagonal σ ℝ F).natDegree = D :=
    Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
      (Polynomial.natDegree_le_iff_coeff_eq_zero.2 fun j hj => by simpa [hj.ne'] using htop j hj.le)
      (hcD ▸ hc.ne')
  obtain ⟨ℓ, ρ, hℓ, hρ, h⟩ := Polynomial.exists_eq_C_mul_X_pow_mul_prod_X_sq_sub
    (MvPolynomial.splits_appellDiagonal_of_isRealStable hLW (hBB σ) hstab)
    (MvPolynomial.appellDiagonal_comp_neg_X_of_isHomogeneous hhom)
  rw [Polynomial.leadingCoeff, hdeg, hcD] at h
  exact ⟨ℓ, ρ, hdeg ▸ hℓ, hρ, h⟩


end MvPolynomial


namespace Polynomial

/-! ### Negative zeros of products of quadratic factors -/

/-- A product of two polynomials with only negative roots has only negative roots. -/
private lemma hasOnlyNegativeRoots_mul {p q : ℝ[X]} (hp : p.HasOnlyNegativeRoots)
    (hq : q.HasOnlyNegativeRoots) : (p * q).HasOnlyNegativeRoots := by
  refine ⟨hp.1.mul hq.1, fun r hr => ?_⟩
  by_cases h : p * q = 0
  · simp [h] at hr
  · rw [roots_mul h, Multiset.mem_add] at hr
    exact hr.elim (hp.2 r) (hq.2 r)

private lemma hasOnlyNegativeRoots_C (c : ℝ) : (C c).HasOnlyNegativeRoots :=
  ⟨Splits.C c, by simp⟩

private lemma hasOnlyNegativeRoots_X_sub_C {a : ℝ} (ha : a < 0) :
    (X - C a).HasOnlyNegativeRoots :=
  ⟨Splits.X_sub_C a, by simpa using ha⟩

/-- A finite product of polynomials with only negative roots has only negative roots. -/
private lemma hasOnlyNegativeRoots_prod {ι : Type*} (s : Finset ι) (f : ι → ℝ[X])
    (hf : ∀ j ∈ s, (f j).HasOnlyNegativeRoots) : (∏ j ∈ s, f j).HasOnlyNegativeRoots := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hasOnlyNegativeRoots_C 1
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact hasOnlyNegativeRoots_mul (hf a (by simp)) (ih fun j hj => hf j (by simp [hj]))

private lemma hasOnlyNegativeRoots_pow {p : ℝ[X]} (hp : p.HasOnlyNegativeRoots) (n : ℕ) :
    (p ^ n).HasOnlyNegativeRoots := by
  simpa using hasOnlyNegativeRoots_prod (Finset.range n) (fun _ => p) fun _ _ => hp

/-- For `β ≥ 0`, `(1 + X)^2 + β X = (X - r₊)(X - r₋)` with
`r± = (-(2 + β) ± √(β(4 + β)))/2`, both negative. -/
private lemma hasOnlyNegativeRoots_quadratic {β : ℝ} (hβ : 0 ≤ β) :
    ((1 + X) ^ 2 + C β * X).HasOnlyNegativeRoots := by
  set δ := Real.sqrt (β * (4 + β))
  have hδ0 : 0 ≤ δ := Real.sqrt_nonneg _
  have hδsq : δ ^ 2 = β * (4 + β) := Real.sq_sqrt (by positivity)
  have hfac : (1 + X) ^ 2 + C β * X =
      (X - C ((-(2 + β) + δ) / 2)) * (X - C ((-(2 + β) - δ) / 2)) := by
    have hc : (-(2 + β) + δ) / 2 * ((-(2 + β) - δ) / 2) = 1 := by nlinarith
    have hs : (-(2 + β) + δ) / 2 + (-(2 + β) - δ) / 2 = -(2 + β) := by ring
    rw [show ∀ a b : ℝ, (X - C a) * (X - C b) = X ^ 2 - C (a + b) * X + C (a * b) from
      fun a b => by simp only [map_add, map_mul]; ring, hs, hc]
    simp only [map_neg, map_add, C_ofNat, map_one]
    ring
  rw [hfac]
  exact hasOnlyNegativeRoots_mul (hasOnlyNegativeRoots_X_sub_C (by nlinarith))
    (hasOnlyNegativeRoots_X_sub_C (by linarith))

/-- For real `c`, `e : ℕ` and nonnegative reals `β j`, the polynomial
`c (1 + X)^e ∏ j, ((1 + X)^2 + β j X)` has only negative real zeros. -/
@[lognarayana "lem_factorization_negative_zeros"]
public theorem hasOnlyNegativeRoots_C_mul_one_add_X_pow_mul_prod {ι : Type*} [Fintype ι]
    (c : ℝ) (e : ℕ) (β : ι → ℝ) (hβ : ∀ j, 0 ≤ β j) :
    (C c * (1 + X) ^ e * ∏ j, ((1 + X) ^ 2 + C (β j) * X)).HasOnlyNegativeRoots :=
  hasOnlyNegativeRoots_mul (hasOnlyNegativeRoots_mul (hasOnlyNegativeRoots_C c)
    (hasOnlyNegativeRoots_pow (by simpa [add_comm] using
      hasOnlyNegativeRoots_X_sub_C (a := -1) (by norm_num)) e))
    (hasOnlyNegativeRoots_prod _ _ fun j _ => hasOnlyNegativeRoots_quadratic (hβ j))


/-- Clearing denominators in the substitution `y = μx/(1+x)²`: the factor `(1+x)^D` absorbs one
`(1+x)²` into each of the `ℓ` factors `1 + ρⱼ² y`, leaving `(1+x)^(D-2ℓ)`. -/
private lemma pow_mul_prod_one_add_mul_div_sq {x μ : ℝ} {D ℓ : ℕ} (hx : 1 + x ≠ 0)
    (hℓ : 2 * ℓ ≤ D) (ρ : Fin ℓ → ℝ) :
    (1 + x) ^ D * ∏ j, (1 + ρ j ^ 2 * (μ * x / (1 + x) ^ 2)) =
      (1 + x) ^ (D - 2 * ℓ) * ∏ j, ((1 + x) ^ 2 + μ * ρ j ^ 2 * x) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hℓ
  rw [Nat.add_sub_cancel_left, pow_add, mul_comm ((1 + x) ^ (2 * ℓ)), mul_assoc, pow_mul,
    ← Fin.prod_const ℓ ((1 + x) ^ 2), ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  field_simp

/-- If `P(x) = (1 + x)^D · Γ(μ x / (1 + x)^2)` for every real `x ≠ -1`, where
`Γ = c ∏_{j} (1 + ρ_j^2 u)` has `ℓ` factors and `2ℓ ≤ D`, then
`P = c (1 + x)^{D - 2ℓ} ∏_{j} ((1 + x)^2 + μ ρ_j^2 x)` in `ℝ[x]`. -/
@[lognarayana "lem_gamma_substitution_factorization"]
public theorem eq_C_mul_one_add_X_pow_mul_prod_of_eval_eq_gamma
    {P Γ : ℝ[X]} {D ℓ : ℕ} (hℓ : 2 * ℓ ≤ D) {c μ : ℝ} {ρ : Fin ℓ → ℝ}
    (hP : ∀ x : ℝ, x ≠ -1 → P.eval x = (1 + x) ^ D * Γ.eval (μ * x / (1 + x) ^ 2))
    (hΓ : Γ = C c * ∏ j, (1 + C (ρ j ^ 2) * X)) :
    P = C c * (1 + X) ^ (D - 2 * ℓ) * ∏ j, ((1 + X) ^ 2 + C (μ * ρ j ^ 2) * X) := by
  refine eq_of_infinite_eval_eq _ _ ((Set.finite_singleton (-1 : ℝ)).infinite_compl.mono
    fun x (hx : x ≠ -1) => ?_)
  have hx' : 1 + x ≠ 0 := fun h => hx (by linarith)
  simp only [Set.mem_ofPred_eq, hP x hx, hΓ, eval_mul, eval_C, eval_prod, eval_add, eval_one,
    eval_X, eval_pow, mul_left_comm _ c, pow_mul_prod_one_add_mul_div_sq hx' hℓ, mul_assoc]


/-- The change of variables `x = -t⁻²` turning `∏ (1 + r_j x)` into `t^{-2ℓ} ∏ (t² - r_j)`,
scaled by `t^n` for `n ≥ 2ℓ`. -/
private lemma pow_mul_prod_one_add_mul_neg_inv_sq {ι : Type*} (s : Finset ι) (r : ι → ℝ)
    {t : ℝ} (ht : t ≠ 0) {n : ℕ} (hn : 2 * s.card ≤ n) :
    t ^ n * ∏ j ∈ s, (1 + r j * -(t⁻¹) ^ 2) = t ^ (n - 2 * s.card) * ∏ j ∈ s, (t ^ 2 - r j) := by
  rw [← Nat.sub_add_cancel hn, pow_add, Nat.add_sub_cancel, pow_mul, mul_assoc,
    Finset.pow_card_mul_prod]
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  field_simp
  ring

/-- `1 + a X = a (X + a⁻¹)` for `a ≠ 0`. -/
private lemma one_add_C_mul_X {a : ℝ} (ha : a ≠ 0) :
    (1 + C a * X : ℝ[X]) = C a * (X - C (-a⁻¹)) := by
  rw [mul_sub, C_neg, mul_neg, sub_neg_eq_add, ← C_mul, mul_inv_cancel₀ ha, C_1, add_comm]

/-- A nonzero multiple of `∏ᵢ (1 + aᵢ X)` with all `aᵢ > 0` has only negative roots,
namely the `-aᵢ⁻¹`. -/
private lemma hasOnlyNegativeRoots_C_mul_prod_one_add_C_mul_X {ι : Type*} (s : Finset ι)
    {c : ℝ} (hc : c ≠ 0) {a : ι → ℝ} (ha : ∀ i ∈ s, 0 < a i) :
    (C c * ∏ i ∈ s, (1 + C (a i) * X)).HasOnlyNegativeRoots := by
  rw [Finset.prod_congr rfl (fun i hi => one_add_C_mul_X (ha i hi).ne'),
    Finset.prod_mul_distrib, ← map_prod, ← mul_assoc, ← C_mul]
  change (C _ * (s.val.map ((fun b => X - C b) ∘ fun i => -(a i)⁻¹)).prod).HasOnlyNegativeRoots
  rw [← Multiset.map_map]
  have hk : c * ∏ i ∈ s, a i ≠ 0 :=
    mul_ne_zero hc (Finset.prod_ne_zero_iff.mpr fun i hi => (ha i hi).ne')
  refine ⟨(Splits.multisetProd fun p hp => ?_).C_mul _, fun r hr => ?_⟩
  · obtain ⟨b, -, rfl⟩ := Multiset.mem_map.mp hp
    exact Splits.X_sub_C b
  · rw [roots_C_mul _ hk, roots_multiset_prod_X_sub_C] at hr
    obtain ⟨i, hi, rfl⟩ := Multiset.mem_map.mp hr
    exact neg_neg_of_pos (inv_pos.mpr (ha i hi))


end Polynomial


namespace MvPolynomial

/-! ### The gamma transform of a real-stable polynomial -/

/-- The gamma transform of a real-stable polynomial `F ∈ ℝ[z_σ]` with nonnegative coefficients,
homogeneous of degree `D`, factors as `Γ_F(u) = (∑_{α ∈ supp F} [z^α]F) · ∏_{j < ℓ} (1 + ρ_j² u)`
for some `ℓ` with `2ℓ ≤ D` and positive reals `ρ_j`. -/
@[lognarayana "lem_gamma_transform_factorization"]
public theorem IsHomogeneous.gammaTransform_eq_C_mul_prod
    (hBB : ∀ τ : Type u, RealStablePreserverOfSymbol τ)
    (hNR : ShiftedNarayanaNegRealRoots)
    {σ : Type u} [Finite σ] {D : ℕ} {F : MvPolynomial σ ℝ}
    (hD : F.IsHomogeneous D) (hstable : F.IsRealStable)
    (hnonneg : F.HasNonnegCoeffs) :
    ∃ ℓ : ℕ, 2 * ℓ ≤ D ∧ ∃ ρ : Fin ℓ → ℝ, (∀ j, 0 < ρ j) ∧
      gammaTransform σ ℝ F =
        Polynomial.C (∑ α ∈ F.support, F.coeff α) *
          ∏ j, (1 + Polynomial.C (ρ j ^ 2) * Polynomial.X) := by
  obtain ⟨ℓ, ρ, hℓ, hρ, hH⟩ :=
    appellDiagonal_eq_mul_prod_X_sq_sub_of_isRealStable hBB hNR hD hstable hnonneg
  refine ⟨ℓ, hℓ, ρ, hρ, Polynomial.eq_of_infinite_eval_eq _ _
    ((Set.Iio_infinite (0 : ℝ)).mono fun v (hv : v < 0) => ?_)⟩
  -- every `v < 0` is `-(t⁻¹)²` for `t = (√(-v))⁻¹ ≠ 0`
  obtain ⟨t, ht, rfl⟩ : ∃ t : ℝ, t ≠ 0 ∧ -(t⁻¹) ^ 2 = v :=
    ⟨(√(-v))⁻¹, inv_ne_zero (Real.sqrt_pos.2 (neg_pos.2 hv)).ne',
      by rw [inv_inv, Real.sq_sqrt (by linarith), neg_neg]⟩
  have key := eval_appellDiagonal_eq_pow_mul_eval_gammaTransform hD ht
  rw [hH] at key
  apply mul_left_cancel₀ (pow_ne_zero D ht)
  simp only [← key, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_add,
    Polynomial.eval_one]
  rw [mul_left_comm, Polynomial.pow_mul_prod_one_add_mul_neg_inv_sq _ _ ht (by simpa using hℓ)]
  simp [mul_assoc]

/-- The gamma transform of a real-stable polynomial `F ∈ ℝ[z_σ]` with nonnegative coefficients,
homogeneous of degree `D`, has only negative real zeros. -/
@[lognarayana "lem_gamma_transform_negative_zeros"]
public theorem IsHomogeneous.hasOnlyNegativeRoots_gammaTransform
    (hBB : ∀ τ : Type u, RealStablePreserverOfSymbol τ)
    (hNR : ShiftedNarayanaNegRealRoots)
    {σ : Type u} [Finite σ] {D : ℕ} {F : MvPolynomial σ ℝ}
    (hF0 : F ≠ 0) (hD : F.IsHomogeneous D) (hstable : F.IsRealStable)
    (hnonneg : F.HasNonnegCoeffs) :
    (gammaTransform σ ℝ F).HasOnlyNegativeRoots := by
  obtain ⟨ℓ, -, ρ, hρ, hΓ⟩ :=
    hD.gammaTransform_eq_C_mul_prod hBB hNR hstable hnonneg
  obtain ⟨α, hα⟩ := MvPolynomial.support_nonempty.mpr hF0
  rw [hΓ]
  exact Polynomial.hasOnlyNegativeRoots_C_mul_prod_one_add_C_mul_X _
    (Finset.sum_pos' (fun β _ => hnonneg β)
      ⟨α, hα, (hnonneg α).lt_of_ne' (MvPolynomial.mem_support_iff.mp hα)⟩).ne'
    fun j _ => pow_pos (hρ j) 2


/-! ### The Narayana transform and its deformation through the gamma transform -/

private lemma deformedNarayanaTransform_monomial {σ : Type*} (lam : ℝ) (α : σ →₀ ℕ) (c : ℝ) :
    deformedNarayanaTransform ℝ lam σ (monomial α c) =
      c • α.prod fun _ k =>
        aeval ![1 + Polynomial.X, Polynomial.C lam * Polynomial.X] (narayanaQ ℝ k) := by
  rw [← mul_one c, ← smul_eq_mul, ← MvPolynomial.smul_monomial, map_smul,
    ← congrFun (coe_basisMonomials σ ℝ) α, deformedNarayanaTransform, Module.Basis.constr_basis,
    smul_eq_mul, mul_one]

/-- Evaluating `Q_k(1 + X, λ X)` at `x` is `Q_k(1 + x, λ x)`. -/
private lemma eval_aeval_narayanaQ (lam x : ℝ) (k : ℕ) :
    (aeval ![1 + Polynomial.X, Polynomial.C lam * Polynomial.X] (narayanaQ ℝ k)).eval x =
      MvPolynomial.eval ![1 + x, lam * x] (narayanaQ ℝ k) := by
  rw [← Polynomial.coe_aeval_eq_eval, ← AlgHom.comp_apply, MvPolynomial.comp_aeval,
    ← MvPolynomial.coe_aeval_eq_eval]
  exact congrArg (fun f => MvPolynomial.aeval f (narayanaQ ℝ k))
    (_root_.funext fun i => by fin_cases i <;> simp)

private lemma eval_deformedNarayanaTransform_monomial {σ : Type*} (lam : ℝ) (α : σ →₀ ℕ)
    (c : ℝ) {x : ℝ} (hx : x ≠ -1) :
    (deformedNarayanaTransform ℝ lam σ (monomial α c)).eval x =
      (1 + x) ^ α.degree *
        (gammaTransform σ ℝ (monomial α c)).eval (lam * x / (1 + x) ^ 2) := by
  have hA : (1 + x) ≠ 0 := fun h => hx (by linarith)
  simp only [deformedNarayanaTransform_monomial, gammaTransform_monomial, Polynomial.eval_smul,
    smul_eq_mul, Finsupp.prod, Polynomial.eval_prod, eval_aeval_narayanaQ,
    narayanaQ_eval_eq_pow_mul_narayanaM_eval _ hA, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, Finsupp.degree_apply]
  ring

/-- If `F ∈ ℝ[z_σ]` is homogeneous of degree `D` and `λ ∈ ℝ`, then for every real `x ≠ -1`,
`𝒩_λ(F)(x) = (1 + x)^D · Γ_F(λ x / (1 + x)^2)`. -/
@[lognarayana "lem_deformed_transform_eq_gamma"]
public theorem IsHomogeneous.eval_deformedNarayanaTransform_eq_mul_eval_gammaTransform
    {σ : Type*} {D : ℕ} {F : MvPolynomial σ ℝ} (hF : F.IsHomogeneous D) (lam : ℝ) {x : ℝ}
    (hx : x ≠ -1) :
    (deformedNarayanaTransform ℝ lam σ F).eval x =
      (1 + x) ^ D * (gammaTransform σ ℝ F).eval (lam * x / (1 + x) ^ 2) := by
  conv_lhs => rw [F.as_sum]
  conv_rhs => rw [F.as_sum]
  simp only [map_sum, Polynomial.eval_finsetSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α hα => ?_
  rw [eval_deformedNarayanaTransform_monomial _ _ _ hx, ← hF (mem_support_iff.mp hα),
    Finsupp.degree_eq_weight_one]
  rfl


/-- On a monomial `c z^α`, `𝒩(c z^α)(x) = (1 + x)^{|α|} Γ(c z^α)(x / (1 + x)^2)`: the factorwise
identity `Ñ_m(x) = (1 + x)^m M_m(x / (1 + x)^2)` multiplied over `α.support`. -/
private lemma eval_narayanaTransform_monomial {σ : Type*} (α : σ →₀ ℕ) (c : ℝ) {x : ℝ}
    (hx : x ≠ -1) :
    (narayanaTransform σ (monomial α c)).eval x =
      (1 + x) ^ α.degree * (gammaTransform σ ℝ (monomial α c)).eval (x / (1 + x) ^ 2) := by
  simp only [narayanaTransform_monomial, gammaTransform_monomial, Polynomial.eval_smul,
    smul_eq_mul, Finsupp.prod, Polynomial.eval_prod,
    eval_shiftedNarayanaPolynomial_eq_narayanaM _ hx, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, Finsupp.degree_apply]
  ring

/-- If `F ∈ ℝ[z_σ]` is homogeneous of degree `D`, then for every real `x ≠ -1`,
`𝒩(F)(x) = (1 + x)^D · Γ_F(x / (1 + x)^2)`. -/
@[lognarayana "lem_narayana_transform_eq_gamma"]
public theorem IsHomogeneous.eval_narayanaTransform_eq_mul_eval_gammaTransform
    {σ : Type*} {D : ℕ} {F : MvPolynomial σ ℝ}
    (hF : F.IsHomogeneous D) {x : ℝ} (hx : x ≠ -1) :
    (narayanaTransform σ F).eval x =
      (1 + x) ^ D * (gammaTransform σ ℝ F).eval (x / (1 + x) ^ 2) := by
  conv_lhs => rw [F.as_sum]
  conv_rhs => rw [F.as_sum]
  simp only [map_sum, Polynomial.eval_finsetSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α hα => ?_
  rw [eval_narayanaTransform_monomial _ _ hx, ← hF (mem_support_iff.mp hα),
    Finsupp.degree_eq_weight_one]
  rfl

/-- If `F ∈ ℝ[z_σ]` is homogeneous of degree `D`, `2ℓ ≤ D`, and
`Γ_F(u) = c ∏_{j} (1 + ρ_j² u)`, then `𝒩(F)(x) = c (1 + x)^{D - 2ℓ} ∏_j ((1 + x)² + ρ_j² x)`. -/
@[lognarayana "lem_narayana_transform_factorization"]
public theorem IsHomogeneous.narayanaTransform_eq_of_gammaTransform_eq
    {σ : Type*} {D ℓ : ℕ} (hℓ : 2 * ℓ ≤ D)
    {F : MvPolynomial σ ℝ} (hF : F.IsHomogeneous D) (c : ℝ) (ρ : Fin ℓ → ℝ)
    (hΓ : gammaTransform σ ℝ F =
      Polynomial.C c * ∏ j, (1 + Polynomial.C (ρ j ^ 2) * Polynomial.X)) :
    narayanaTransform σ F =
      Polynomial.C c * (1 + Polynomial.X) ^ (D - 2 * ℓ) *
        ∏ j, ((1 + Polynomial.X) ^ 2 + Polynomial.C (ρ j ^ 2) * Polynomial.X) := by
  simpa only [one_mul] using Polynomial.eq_C_mul_one_add_X_pow_mul_prod_of_eval_eq_gamma (μ := 1)
    hℓ (fun _ hx => by simpa only [one_mul] using
      hF.eval_narayanaTransform_eq_mul_eval_gammaTransform hx) hΓ


/-! ### Proof of Theorem 1.4 and Corollary 6.3 -/

/-- **The deformed Narayana transform is real-rooted** (Corollary 6.3): if `F ∈ ℝ[z_σ]` is
homogeneous of degree `D`, real-stable and has nonnegative coefficients, then for every real `λ ≥ 0`
the polynomial `𝒩_λ(F)` is real-rooted. -/
@[lognarayana "thm_stable_deformation_real_rooted"]
public theorem IsHomogeneous.splits_deformedNarayanaTransform
    (hBB : ∀ τ : Type u, RealStablePreserverOfSymbol τ)
    (hNR : ShiftedNarayanaNegRealRoots)
    {σ : Type u} [Finite σ] {D : ℕ} {F : MvPolynomial σ ℝ}
    (hD : F.IsHomogeneous D) (hstable : F.IsRealStable)
    (hnonneg : F.HasNonnegCoeffs) {lam : ℝ} (hlam : 0 ≤ lam) :
    (deformedNarayanaTransform ℝ lam σ F).Splits := by
  obtain ⟨ℓ, hℓ, ρ, -, hΓ⟩ :=
    hD.gammaTransform_eq_C_mul_prod hBB hNR hstable hnonneg
  rw [Polynomial.eq_C_mul_one_add_X_pow_mul_prod_of_eval_eq_gamma hℓ
    (fun x hx => hD.eval_deformedNarayanaTransform_eq_mul_eval_gammaTransform lam hx) hΓ]
  exact (Polynomial.hasOnlyNegativeRoots_C_mul_one_add_X_pow_mul_prod _ _ _
    fun j => mul_nonneg hlam (sq_nonneg (ρ j))).1

/-- The Narayana transform of a real-stable polynomial `F ∈ ℝ[z_σ]` with nonnegative coefficients,
homogeneous of degree `D`, has only negative real zeros. -/
@[lognarayana "thm_stable_transform_negative"]
public theorem IsHomogeneous.hasOnlyNegativeRoots_narayanaTransform
    (hBB : ∀ τ : Type u, RealStablePreserverOfSymbol τ)
    (hNR : ShiftedNarayanaNegRealRoots)
    {σ : Type u} [Finite σ] {D : ℕ} {F : MvPolynomial σ ℝ}
    (hD : F.IsHomogeneous D) (hstable : F.IsRealStable)
    (hnonneg : F.HasNonnegCoeffs) :
    (narayanaTransform σ F).HasOnlyNegativeRoots := by
  obtain ⟨ℓ, hℓ, ρ, -, hΓ⟩ :=
    hD.gammaTransform_eq_C_mul_prod hBB hNR hstable hnonneg
  rw [hD.narayanaTransform_eq_of_gammaTransform_eq hℓ _ ρ hΓ]
  exact Polynomial.hasOnlyNegativeRoots_C_mul_one_add_X_pow_mul_prod _ _ _
    fun j => sq_nonneg (ρ j)

/-- If `F ∈ ℝ[z_σ]` is homogeneous of degree `D`, real-stable and has nonnegative coefficients, then
its Narayana transform `𝒩(F)` is real-rooted. -/
@[lognarayana "thm_stable_transform_real_rooted"]
public theorem splits_narayanaTransform_of_isRealStable
    (hBB : ∀ τ : Type u, RealStablePreserverOfSymbol τ) (hLW : ShiftedNarayanaNegRealRoots)
    {σ : Type u} [Finite σ] {D : ℕ} {F : MvPolynomial σ ℝ}
    (hFhom : F.IsHomogeneous D) (hFst : F.IsRealStable) (hFnn : F.HasNonnegCoeffs) :
    (narayanaTransform σ F).Splits :=
  (hFhom.hasOnlyNegativeRoots_narayanaTransform hBB hLW hFst
    hFnn).1


end MvPolynomial
