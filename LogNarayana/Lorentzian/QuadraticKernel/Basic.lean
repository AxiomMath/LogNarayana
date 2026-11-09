/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module
public import LogNarayana.Lorentzian.QuadraticKernel.Defs
public import LogNarayana.Lorentzian.Hessian.Basic
public import LogNarayana.Forest.OpenPairPolynomial.Defs
public import LogNarayana.Lorentzian.Convolution.Basic
public import LogNarayana.Lorentzian.PositiveIndex.Basic
public import LogNarayana.Lorentzian.Symbol.Basic
public import LogNarayana.Lorentzian.BrandenHuh.Basic

/-!
# The quadratic kernel

For polynomials `A, B` in the variables `x`, the quadratic kernel is
`K_{A,B} = B + A t + t² / 2`. This file proves the two facts about it that the root operator
`𝓡_{A,B}(U) = A U + ∫₀ᵗ U ds + B ∂_t U` rests on.

First, `𝓡_{A,B}(U) = ∂_t² (U * K_{A,B})`: the root operator is the second `t`-derivative of the
convolution with the kernel. Both sides are additive in `U` and the convolution is additive in
the kernel, so the identity splits into `∂_t² (U * B) = B ∂_t U`, `∂_t² (U * (A t)) = A U` and
`∂_t² (U * t² / 2) = ∫₀ᵗ U ds`, each checked on monomials.

Second, for `a ∈ ℝ_{≥0}^p`, `A = aᵀ x` and `B` homogeneous of degree two with nonnegative
coefficients, `K_{A,B}` is Lorentzian if and only if `Hess B - a aᵀ ⪯ 0`. The Hessian of
`K_{A,B}` in the variables `(x, t)` is `[[Hess B, a], [aᵀ, 1]]`, congruent to the block-diagonal
matrix with blocks `Hess B - a aᵀ` and `1` (completing the square
`xᵀ C x + 2 t aᵀ x + t² = xᵀ (C - a aᵀ) x + (t + aᵀ x)²`), so its positive index is that of
`Hess B - a aᵀ` plus one; and a symmetric matrix is negative semidefinite exactly when its
positive index vanishes.

## Main results

* `MvPolynomial.rootOperator_eq_pderiv_pderiv_tConvolution_quadraticKernel`: the identity
  `𝓡_{A,B}(U) = ∂_t² (U * K_{A,B})`.
* `Matrix.posSemidef_neg_iff_posIndex_eq_zero`: for symmetric real `C`,
  `(-C).PosSemidef ↔ C.posIndex = 0`.
* `MvPolynomial.isLorentzian_quadraticKernel_iff`: `K_{A,B}` is Lorentzian if and only if
  `Hess B - a aᵀ` is negative semidefinite.
* `MvPolynomial.isLorentzian_rootOperator`: for `a ∈ ℝ_{≥0}^σ` and `B` as above with
  `Hess B - a aᵀ ⪯ 0`, the root operator `𝓡_{A,B}` maps homogeneous Lorentzian polynomials to
  Lorentzian polynomials.

## Implementation notes

The variables of `R[x, t]` are `Option σ`, with `t = X none` and `x_i = X (some i)`; the
polynomials `A, B ∈ R[x]` enter through `rename some`. The paper works over `ℝ`; the kernel
identity holds over any semifield that is a `ℚ`-algebra, so the additivity and homogeneity of
`MvPolynomial.tConvolution` in each argument are proved here at that generality.

Negative semidefiniteness `M ⪯ 0` is `(-M).PosSemidef`; since `Matrix.PosSemidef` includes the
Hermitian condition, symmetry is a hypothesis of `Matrix.posSemidef_neg_iff_posIndex_eq_zero`.
The Hessian of `K_{A,B}` is indexed by `Option (Fin p)`; it is moved to `Fin p ⊕ Unit` by
`Equiv.optionEquivSumPUnit`, under which the positive index is invariant.

For the root operator the variable index set is an arbitrary finite type `σ`; the kernel is
transported from `Fin p` along `Fintype.equivFin σ`, the Lorentzian property being invariant
under renaming the variables along an equivalence. Since `𝓡_{A,B}(U) = ∂_t² (U * K_{A,B})`,
preservation follows from the Lorentzian property of the convolution and of `∂_t`; the results
of Brändén–Huh it rests on are taken as hypotheses, for all finite variable types in the
universe of `σ`.

## References

* [LogNarayana]
-/

namespace MvPolynomial

section KernelIdentity

variable {σ R : Type*} [Semifield R] [Algebra ℚ R]

private lemma tConv_add_left (F F' G : MvPolynomial (Option σ) R) :
    tConvolution (F + F') G = tConvolution F G + tConvolution F' G := by
  simp [tConvolution, map_add, add_mul]

private lemma tConv_add_right (F G G' : MvPolynomial (Option σ) R) :
    tConvolution F (G + G') = tConvolution F G + tConvolution F G' := by
  simp [tConvolution, map_add, mul_add]

private lemma tConv_smul_left (a : R) (F G : MvPolynomial (Option σ) R) :
    tConvolution (a • F) G = a • tConvolution F G := by
  simp [tConvolution, map_smul]

private lemma tConv_smul_right (a : R) (F G : MvPolynomial (Option σ) R) :
    tConvolution F (a • G) = a • tConvolution F G := by
  simp [tConvolution, map_smul]

private lemma mapDomain_some_none (β : σ →₀ ℕ) : β.mapDomain some none = 0 :=
  Finsupp.mapDomain_of_notMem_range _ _ (by simp)

private lemma eq_single_none_add (s : Option σ →₀ ℕ) :
    s = Finsupp.single none (s none) + s.some.mapDomain some := by
  ext i
  cases i with
  | none => simp [mapDomain_some_none]
  | some i => simp [Finsupp.mapDomain_apply (Option.some_injective _)]

omit [Algebra ℚ R] in
private lemma monomial_congr {s s' : Option σ →₀ ℕ} {a a' : R} (h : s = s') (h' : a = a') :
    monomial s a = monomial s' a' := by rw [h, h']

private lemma tConv_monomial (s β : Option σ →₀ ℕ) (a b : R) :
    tConvolution (monomial s a) (monomial β b) = monomial (s + β + Finsupp.single none 1)
      (a * b * algebraMap ℚ R (((s none).factorial * (β none).factorial : ℚ) /
        ((s none + β none + 1).factorial : ℚ))) := by
  have h1 : monomial s a = a • monomial s (1 : R) := by rw [smul_monomial, smul_eq_mul, mul_one]
  have h2 : monomial β b = b • monomial β (1 : R) := by rw [smul_monomial, smul_eq_mul, mul_one]
  rw [h1, h2, tConv_smul_left, tConv_smul_right]
  conv_lhs => rw [eq_single_none_add s, eq_single_none_add β]
  rw [MvPolynomial.tConvolution_monomial_monomial, smul_monomial, smul_monomial,
    smul_eq_mul, smul_eq_mul, ← mul_assoc]
  refine monomial_congr ?_ rfl
  conv_rhs => rw [eq_single_none_add s, eq_single_none_add β]
  rw [Finsupp.mapDomain_add, Finsupp.single_add, Finsupp.single_add]
  abel

private lemma antiderivative_monomial (s : Option σ →₀ ℕ) (a : R) :
    antiderivative none (monomial s a) =
      monomial (s + Finsupp.single none 1) (a * algebraMap ℚ R (1 / ((s none : ℚ) + 1))) := by
  have h1 : monomial s a = a • basisMonomials (Option σ) R s := by
    rw [coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]
  rw [h1, map_smul, antiderivative, Module.Basis.constr_basis, smul_monomial, smul_eq_mul]

/-- The rational coefficients produced by differentiating a convolution twice: two natural-number
factors after a rational scalar fold into the scalar. -/
private lemma mul_algebraMap_mul_natCast_mul_natCast (x : R) {c q : ℚ} {n m : ℕ}
    (h : c * n * m = q) : x * algebraMap ℚ R c * n * m = x * algebraMap ℚ R q := by
  simp [← h, mul_assoc]

/-- `∂_t² (U * (t² / 2)) = ∫₀ᵗ U`. -/
private lemma pderiv_pderiv_tConv_sq (U : MvPolynomial (Option σ) R) :
    pderiv none (pderiv none (tConvolution U (C 2⁻¹ * X none ^ 2))) = antiderivative none U := by
  induction U using MvPolynomial.induction_on' with
  | monomial s a =>
    rw [C_mul_X_pow_eq_monomial, tConv_monomial, pderiv_monomial, pderiv_monomial,
      antiderivative_monomial]
    refine monomial_congr ?_ ?_
    · ext i; cases i <;> simp
    · simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
        Finsupp.single_eq_same]
      have key : (2⁻¹ : ℚ) * (((s none).factorial * (Nat.factorial 2) : ℚ) /
          ((s none + 2 + 1).factorial : ℚ)) * ((s none + 2 + 1 : ℕ) : ℚ) *
          ((s none + 2 + 1 - 1 : ℕ) : ℚ) = 1 / ((s none : ℚ) + 1) := by
        rw [show s none + 2 + 1 - 1 = s none + 2 by omega]
        simp only [Nat.factorial]
        push_cast
        field_simp
        ring
      rw [← key]
      simp only [map_mul, map_natCast, map_inv₀, map_ofNat, map_div₀]
      ring
  | add p q hp hq => rw [tConv_add_left, map_add, map_add, hp, hq, map_add]

omit [Algebra ℚ R] in
private lemma rename_some_monomial_mul_X (β : σ →₀ ℕ) (b : R) :
    rename some (monomial β b) * X none =
      monomial (β.mapDomain some + Finsupp.single none 1) b := by
  rw [rename_monomial, X, monomial_mul, mul_one]

/-- `∂_t² (U * (A t)) = A U`. -/
private lemma pderiv_pderiv_tConv_mul_X (A : MvPolynomial σ R) (U : MvPolynomial (Option σ) R) :
    pderiv none (pderiv none (tConvolution U (rename some A * X none))) = rename some A * U := by
  induction U using MvPolynomial.induction_on' with
  | monomial s a =>
    induction A using MvPolynomial.induction_on' with
    | monomial β b =>
      rw [rename_some_monomial_mul_X, tConv_monomial, pderiv_monomial, pderiv_monomial,
        rename_monomial, monomial_mul]
      refine monomial_congr ?_ ?_
      · ext i; cases i <;> simp [mapDomain_some_none]
        omega
      · simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
          Finsupp.single_eq_same, mapDomain_some_none]
        rw [mul_algebraMap_mul_natCast_mul_natCast _ (q := 1) ?_, map_one, mul_one, mul_comm]
        simp only [zero_add, Nat.add_sub_cancel, Nat.factorial]
        push_cast
        field_simp
    | add p q hp hq => rw [map_add, add_mul, tConv_add_right, map_add, map_add, hp, hq, add_mul]
  | add p q hp hq => rw [tConv_add_left, map_add, map_add, hp, hq, mul_add]

/-- `∂_t² (U * B) = B ∂_t U`. -/
private lemma pderiv_pderiv_tConv_rename (B : MvPolynomial σ R) (U : MvPolynomial (Option σ) R) :
    pderiv none (pderiv none (tConvolution U (rename some B))) =
      rename some B * pderiv none U := by
  induction U using MvPolynomial.induction_on' with
  | monomial s a =>
    induction B using MvPolynomial.induction_on' with
    | monomial β b =>
      rw [rename_monomial, tConv_monomial, pderiv_monomial, pderiv_monomial, pderiv_monomial,
        monomial_mul]
      rcases Nat.eq_zero_or_pos (s none) with h | h
      · simp [h, mapDomain_some_none]
      refine monomial_congr ?_ ?_
      · ext i; cases i <;> simp [mapDomain_some_none]
        omega
      · simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
          Finsupp.single_eq_same, mapDomain_some_none]
        rw [mul_algebraMap_mul_natCast_mul_natCast _ (q := s none) ?_, map_natCast]
        · ring
        obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt h
        rw [hk]
        simp only [add_zero, zero_add, Nat.add_sub_cancel, Nat.factorial]
        push_cast
        field_simp
    | add p q hp hq => rw [map_add, add_mul, tConv_add_right, map_add, map_add, hp, hq]
  | add p q hp hq => rw [tConv_add_left, map_add, map_add, hp, hq, map_add, mul_add]

/-- The root operator is the second `t`-derivative of convolution with the quadratic kernel:
`𝓡_{A,B}(U) = ∂_t² (U * K_{A,B})`. -/
@[lognarayana "lem_kernel_identity"]
public theorem rootOperator_eq_pderiv_pderiv_tConvolution_quadraticKernel
    (A B : MvPolynomial σ R) (U : MvPolynomial (Option σ) R) :
    rootOperator none (rename some A) (rename some B) U =
      pderiv none (pderiv none (tConvolution U (quadraticKernel A B))) := by
  rw [quadraticKernel, tConv_add_right, tConv_add_right, map_add, map_add, map_add, map_add,
    pderiv_pderiv_tConv_rename, pderiv_pderiv_tConv_mul_X, pderiv_pderiv_tConv_sq, rootOperator]
  simp only [LinearMap.add_apply, LinearMap.mulLeft_apply, LinearMap.coe_comp,
    Function.comp_apply, Derivation.coeFn_coe]
  abel

end KernelIdentity

end MvPolynomial

namespace Matrix

variable {σ : Type*} [Fintype σ]

/-- Every `C`-positive subspace has dimension at most the positive index of `C`. -/
private lemma finrank_le_posIndex {C : Matrix σ σ ℝ} {W : Submodule ℝ (σ → ℝ)}
    (hW : C.IsPositiveSubspace W) : Module.finrank ℝ W ≤ C.posIndex :=
  le_csSup ⟨Fintype.card σ, by rintro n ⟨W, -, rfl⟩; simpa using Submodule.finrank_le W⟩
    ⟨W, hW, rfl⟩

/-- The line spanned by a vector of positive `C`-norm is `C`-positive. -/
private lemma isPositiveSubspace_span_singleton {C : Matrix σ σ ℝ} {x : σ → ℝ}
    (hx : 0 < x ⬝ᵥ (C *ᵥ x)) : C.IsPositiveSubspace (Submodule.span ℝ {x}) := by
  intro v hv hv0
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hv
  have hc : c ≠ 0 := by rintro rfl; simp at hv0
  have : (c • x) ⬝ᵥ (C *ᵥ (c • x)) = c ^ 2 * (x ⬝ᵥ (C *ᵥ x)) := by
    simp [Matrix.mulVec_smul, pow_two, mul_assoc]
  rw [this]
  positivity

/-- The positive index vanishes exactly when the quadratic form is nonpositive. -/
private lemma posIndex_eq_zero_iff {C : Matrix σ σ ℝ} :
    C.posIndex = 0 ↔ ∀ x : σ → ℝ, x ⬝ᵥ (C *ᵥ x) ≤ 0 := by
  constructor
  · intro h x
    by_contra! hx
    have hx0 : x ≠ 0 := by rintro rfl; simp at hx
    have := finrank_le_posIndex (isPositiveSubspace_span_singleton hx)
    rw [finrank_span_singleton hx0, h] at this
    omega
  · intro h
    refine Nat.eq_zero_of_le_zero (csSup_le' ?_)
    rintro n ⟨W, hW, rfl⟩
    rw [Nat.le_zero, Submodule.finrank_eq_zero, eq_bot_iff]
    intro v hv
    by_contra hv0
    exact (hW v hv hv0).not_ge (h v)

/-- A real symmetric matrix `C` is negative semidefinite iff its positive index is zero. -/
@[lognarayana "lem_neg_semidef_iff_pos_index_zero"]
public theorem posSemidef_neg_iff_posIndex_eq_zero {σ : Type*} [Fintype σ]
    {C : Matrix σ σ ℝ} (hC : C.IsSymm) :
    (-C).PosSemidef ↔ C.posIndex = 0 := by
  rw [posIndex_eq_zero_iff, posSemidef_iff_dotProduct_mulVec]
  simp [hC, neg_mulVec]

/-- Relabelling the indices carries positive subspaces to positive subspaces of the same
dimension. -/
private lemma posDims_submatrix_subset {τ ι : Type*} [Fintype τ] [Fintype ι]
    (A : Matrix τ τ ℝ) (e : ι ≃ τ) :
    {n | ∃ W : Submodule ℝ (ι → ℝ), (A.submatrix e e).IsPositiveSubspace W ∧
      Module.finrank ℝ W = n} ⊆
      {n | ∃ W : Submodule ℝ (τ → ℝ), A.IsPositiveSubspace W ∧ Module.finrank ℝ W = n} := by
  rintro n ⟨W, hW, rfl⟩
  let f : (ι → ℝ) ≃ₗ[ℝ] (τ → ℝ) := LinearEquiv.funCongrLeft ℝ ℝ e.symm
  refine ⟨W.map (f : (ι → ℝ) →ₗ[ℝ] (τ → ℝ)), ?_, LinearEquiv.finrank_map_eq f W⟩
  rintro _ ⟨v, hv, rfl⟩ hne
  have h := hW v hv (by rintro rfl; exact hne (map_zero _))
  rwa [submatrix_mulVec_equiv, ← comp_equiv_symm_dotProduct] at h

/-- The positive index is invariant under relabelling the index set. -/
private lemma posIndex_submatrix {τ ι : Type*} [Fintype τ] [Fintype ι] (A : Matrix τ τ ℝ)
    (e : ι ≃ τ) : (A.submatrix e e).posIndex = A.posIndex := by
  refine congrArg sSup ((posDims_submatrix_subset A e).antisymm ?_)
  simpa using posDims_submatrix_subset (A.submatrix e e) e.symm

end Matrix

namespace MvPolynomial

open Matrix

section Hessian

variable {σ R : Type*} [CommSemiring R]

/-- The new variable `none` does not occur in `rename some f`. -/
private lemma pderiv_none_rename_some (f : MvPolynomial σ R) :
    pderiv none (rename some f) = 0 := by
  classical
  refine pderiv_eq_zero_of_notMem_vars fun h => ?_
  obtain ⟨i, -, hi⟩ := Finset.mem_image.1 (vars_rename some f h)
  exact Option.some_ne_none i hi

end Hessian

section NonnegCoeffs

variable {τ S : Type*} [CommSemiring S] [PartialOrder S] [IsOrderedRing S]

private lemma HasNonnegCoeffs.add {f g : MvPolynomial τ S} (hf : f.HasNonnegCoeffs)
    (hg : g.HasNonnegCoeffs) : (f + g).HasNonnegCoeffs := fun α => by
  rw [coeff_add]; exact add_nonneg (hf α) (hg α)

private lemma HasNonnegCoeffs.mul {f g : MvPolynomial τ S} (hf : f.HasNonnegCoeffs)
    (hg : g.HasNonnegCoeffs) : (f * g).HasNonnegCoeffs := fun α => by
  classical
  rw [coeff_mul]; exact Finset.sum_nonneg fun x _ => mul_nonneg (hf _) (hg _)

private lemma HasNonnegCoeffs.sum {ι : Type*} (s : Finset ι) {f : ι → MvPolynomial τ S}
    (hf : ∀ i ∈ s, (f i).HasNonnegCoeffs) : (∑ i ∈ s, f i).HasNonnegCoeffs := fun α => by
  rw [coeff_sum]; exact Finset.sum_nonneg fun i hi => hf i hi α

omit [IsOrderedRing S] in
private lemma hasNonnegCoeffs_C {c : S} (hc : 0 ≤ c) :
    (C c : MvPolynomial τ S).HasNonnegCoeffs := fun α => by
  classical
  rw [coeff_C]
  split_ifs <;> simp [hc]

private lemma hasNonnegCoeffs_X (i : τ) : (X i : MvPolynomial τ S).HasNonnegCoeffs :=
  fun α => by
    classical
    rw [coeff_X]
    split_ifs <;> simp

omit [IsOrderedRing S] in
private lemma HasNonnegCoeffs.rename {υ : Type*} {g : τ → υ} (hg : Function.Injective g)
    {f : MvPolynomial τ S} (hf : f.HasNonnegCoeffs) : (rename g f).HasNonnegCoeffs := by
  intro α
  classical
  by_cases h : ∃ u : τ →₀ ℕ, u.mapDomain g = α
  · obtain ⟨u, rfl⟩ := h
    rw [coeff_rename_mapDomain g hg]; exact hf u
  · rw [coeff_rename_eq_zero g f α fun u hu => (h ⟨u, hu⟩).elim]

end NonnegCoeffs

variable {p : ℕ}

private lemma isHomogeneous_quadraticKernel (a : Fin p → ℝ) {B : MvPolynomial (Fin p) ℝ}
    (hB : B.IsHomogeneous 2) :
    (quadraticKernel (∑ j, C (a j) * X j) B).IsHomogeneous 2 := by
  have hA : (∑ j, C (a j) * X j : MvPolynomial (Fin p) ℝ).IsHomogeneous 1 :=
    IsHomogeneous.sum _ _ _ fun j _ => isHomogeneous_C_mul_X (a j) j
  refine (hB.rename_isHomogeneous.add ?_).add ?_
  · exact (hA.rename_isHomogeneous.mul (isHomogeneous_X ℝ none) :)
  · exact (isHomogeneous_X_pow none 2).C_mul _

private lemma hasNonnegCoeffs_quadraticKernel {a : Fin p → ℝ} (ha : ∀ j, 0 ≤ a j)
    {B : MvPolynomial (Fin p) ℝ} (hBnn : B.HasNonnegCoeffs) :
    (quadraticKernel (∑ j, C (a j) * X j) B).HasNonnegCoeffs := by
  refine HasNonnegCoeffs.add (HasNonnegCoeffs.add
    (HasNonnegCoeffs.rename (Option.some_injective _) hBnn) ?_) ?_
  · refine HasNonnegCoeffs.mul (HasNonnegCoeffs.rename (Option.some_injective _) ?_)
      (hasNonnegCoeffs_X _)
    exact HasNonnegCoeffs.sum _ fun j _ =>
      HasNonnegCoeffs.mul (hasNonnegCoeffs_C (ha j)) (hasNonnegCoeffs_X _)
  · refine HasNonnegCoeffs.mul (hasNonnegCoeffs_C (by norm_num)) ?_
    rw [pow_two]; exact HasNonnegCoeffs.mul (hasNonnegCoeffs_X _) (hasNonnegCoeffs_X _)

private lemma isSymm_hessianAtZero {τ : Type*} (g : MvPolynomial τ ℝ) :
    (hessianAtZero g).IsSymm := by
  ext i j
  simp [hessianAtZero, add_comm]

/-- In the variables `(x, t)`, the Hessian of `K_{A,B}` is congruent to the block-diagonal
matrix with blocks `Hess B - a aᵀ` and `1`. -/
private lemma hessian_quadraticKernel_submatrix (a : Fin p → ℝ) (B : MvPolynomial (Fin p) ℝ) :
    (hessianAtZero (quadraticKernel (∑ j, C (a j) * X j) B)).submatrix
        (Equiv.optionEquivSumPUnit (Fin p)).symm (Equiv.optionEquivSumPUnit (Fin p)).symm =
      (fromBlocks 1 0 (of fun (_ : Unit) j => a j) 1)ᵀ *
        fromBlocks (hessianAtZero B - vecMulVec a a) 0 0 (1 : Matrix Unit Unit ℝ) *
        fromBlocks 1 0 (of fun (_ : Unit) j => a j) 1 := by
  rw [fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply]
  ext (i | i) (j | j) <;>
    simp [hessianAtZero_apply_eq_constantCoeff_pderiv_pderiv, quadraticKernel,
      pderiv_rename (Option.some_injective _), pderiv_none_rename_some, Pi.single_apply,
      vecMulVec_apply, Matrix.mul_apply, map_ofNat]

/-- Let `a ∈ ℝ_{≥0}^p`, `A = ∑ⱼ aⱼ xⱼ`, and `B` homogeneous of degree `2` with
nonnegative coefficients. The kernel `K_{A,B} = B + A t + t² / 2` is Lorentzian if and only if
`Hess B - a aᵀ` is negative semidefinite. -/
@[lognarayana "lem_kernel_lorentzian_iff"]
public theorem isLorentzian_quadraticKernel_iff {p : ℕ} {a : Fin p → ℝ} (ha : ∀ j, 0 ≤ a j)
    {B : MvPolynomial (Fin p) ℝ} (hB : B.IsHomogeneous 2) (hBnn : B.HasNonnegCoeffs) :
    (quadraticKernel (∑ j, C (a j) * X j) B).IsLorentzian ↔
      (-(hessianAtZero B - Matrix.vecMulVec a a)).PosSemidef := by
  rw [isLorentzian_iff_hasAtMostOnePosEigenvalue_of_isHomogeneous_two
      (isHomogeneous_quadraticKernel a hB) (hasNonnegCoeffs_quadraticKernel ha hBnn),
    posSemidef_neg_iff_posIndex_eq_zero
      ((isSymm_hessianAtZero B).sub (by ext i j; simp [vecMulVec_apply, mul_comm])),
    HasAtMostOnePosEigenvalue,
    ← posIndex_submatrix _ (Equiv.optionEquivSumPUnit (Fin p)).symm,
    hessian_quadraticKernel_submatrix, posIndex_transpose_mul_mul, posIndex_fromBlocks_one]
  · omega
  · exact (isUnit_iff_isUnit_det _).2 (by simp)

end MvPolynomial

namespace MvPolynomial

universe u

section RootOperator

section Transfer

variable {α β : Type*}

/-- Renaming along an equivalence reads coefficients through the inverse equivalence. -/
private lemma coeff_rename_equiv {R : Type*} [CommSemiring R] (e : α ≃ β)
    (f : MvPolynomial α R) (γ : β →₀ ℕ) :
    coeff γ (rename e f) = coeff (Finsupp.equivMapDomain e.symm γ) f := by
  have h : γ = Finsupp.mapDomain e (Finsupp.equivMapDomain e.symm γ) := by
    ext b; simp [Finsupp.equivMapDomain_eq_mapDomain, ← Finsupp.mapDomain_comp]
  conv_lhs => rw [h]
  exact coeff_rename_mapDomain _ e.injective _ _

private lemma factorial_equivMapDomain (e : α ≃ β) (γ : α →₀ ℕ) :
    (Finsupp.equivMapDomain e γ).factorial = γ.factorial := by
  simp [Finsupp.factorial, Finsupp.prod_equivMapDomain]

private lemma degree_equivMapDomain (e : α ≃ β) (γ : α →₀ ℕ) :
    (Finsupp.equivMapDomain e γ).degree = γ.degree := by
  rw [Finsupp.degree_apply, Finsupp.degree_apply]
  exact Finsupp.sum_equivMapDomain e γ fun _ n => n

/-- The image of an M-convex set under a relabelling of the coordinates is M-convex. -/
private lemma isMConvex_image_equivMapDomain (e : α ≃ β)
    {J : Set (α →₀ ℕ)} (hJ : J.IsMConvex) :
    (Finsupp.equivMapDomain e '' J).IsMConvex := by
  classical
  obtain ⟨hfin, hne, ⟨D, hD⟩, hex⟩ := hJ
  have key : ∀ (γ : α →₀ ℕ) (i j : α), Finsupp.equivMapDomain e
      (γ - Finsupp.single i 1 + Finsupp.single j 1) =
      Finsupp.equivMapDomain e γ - Finsupp.single (e i) 1 + Finsupp.single (e j) 1 := by
    intro γ i j; ext b
    obtain ⟨a, rfl⟩ := e.surjective b
    simp [Finsupp.single_apply, e.injective.eq_iff]
  refine ⟨hfin.image _, hne.image _, ⟨D, ?_⟩, ?_⟩
  · rintro _ ⟨γ, hγ, rfl⟩; rw [degree_equivMapDomain, hD γ hγ]
  · rintro _ ⟨γ, hγ, rfl⟩ _ ⟨δ, hδ, rfl⟩ i hi
    obtain ⟨i, rfl⟩ := e.surjective i
    simp only [Finsupp.equivMapDomain_apply, Equiv.symm_apply_apply] at hi
    obtain ⟨j, hj, h1, h2⟩ := hex γ hγ δ hδ i hi
    exact ⟨e j, by simpa using hj, ⟨_, h1, key γ i j⟩, ⟨_, h2, key δ j i⟩⟩

private lemma posIndexSet_reindex_subset [Fintype α] [Fintype β] (A : Matrix α α ℝ)
    (e : α ≃ β) :
    {n | ∃ W : Submodule ℝ (β → ℝ), (Matrix.reindex e e A).IsPositiveSubspace W ∧
      Module.finrank ℝ W = n} ⊆
    {n | ∃ W : Submodule ℝ (α → ℝ), A.IsPositiveSubspace W ∧ Module.finrank ℝ W = n} := by
  rintro n ⟨W, hW, rfl⟩
  let L : (β → ℝ) ≃ₗ[ℝ] (α → ℝ) := LinearEquiv.funCongrLeft ℝ ℝ e
  refine ⟨W.map (L : (β → ℝ) →ₗ[ℝ] (α → ℝ)), ?_, LinearEquiv.finrank_map_eq L W⟩
  rintro _ ⟨v, hv, rfl⟩ hv0
  have hv0' : v ≠ 0 := by rintro rfl; exact hv0 (map_zero L)
  have h := hW v hv hv0'
  convert h using 1
  simp only [Matrix.reindex_apply, L, LinearEquiv.coe_coe, LinearEquiv.funCongrLeft_apply,
    LinearMap.funLeft_apply, dotProduct, Matrix.mulVec, Matrix.submatrix_apply]
  refine Fintype.sum_equiv e _ _ fun a => ?_
  simp only [Equiv.symm_apply_apply]
  congr 1
  exact Fintype.sum_equiv e _ _ fun b => by simp

private lemma posIndex_reindex [Fintype α] [Fintype β] (A : Matrix α α ℝ) (e : α ≃ β) :
    (Matrix.reindex e e A).posIndex = A.posIndex :=
  Matrix.posIndex_submatrix A e.symm

/-- The Hessian of `∂^γ (rename e f)` is the reindexed Hessian of `∂^{e⁻¹ γ} f`. -/
private lemma hessianAtZero_iteratedPDeriv_rename_equiv {R : Type*} [CommSemiring R]
    (e : α ≃ β) (f : MvPolynomial α R) (γ : β →₀ ℕ) :
    hessianAtZero (iteratedPDeriv γ (rename e f)) =
      Matrix.reindex e e (hessianAtZero (iteratedPDeriv (Finsupp.equivMapDomain e.symm γ) f)) := by
  ext p q
  have hc : Finsupp.equivMapDomain e.symm (γ + Finsupp.single p 1 + Finsupp.single q 1) =
      Finsupp.equivMapDomain e.symm γ + Finsupp.single (e.symm p) 1 +
        Finsupp.single (e.symm q) 1 := by
    classical
    ext a; simp [Finsupp.single_apply, e.symm_apply_eq]
  rw [Matrix.reindex_apply, Matrix.submatrix_apply, hessianAtZero_iteratedPDeriv_apply,
    hessianAtZero_iteratedPDeriv_apply, coeff_rename_equiv, hc,
    ← factorial_equivMapDomain e.symm, hc]

/-- The Lorentzian property is invariant under renaming the variables along an equivalence. -/
private lemma isLorentzian_rename_equiv [Fintype α] [Fintype β]
    (e : α ≃ β) {f : MvPolynomial α ℝ} (hf : f.IsLorentzian) : (rename e f).IsLorentzian := by
  classical
  rcases hf with rfl | ⟨d, hhom, hnn, hd⟩
  · left; simp
  right
  refine ⟨d, hhom.rename_isHomogeneous, fun γ => by rw [coeff_rename_equiv]; exact hnn _, ?_⟩
  rcases hd with hd | ⟨hd2, hM, hH⟩
  · exact Or.inl hd
  right
  refine ⟨hd2, ?_, fun γ hγ => ?_⟩
  · rw [support_rename_of_injective e.injective, Finset.coe_image]
    have : (Finsupp.mapDomain e : (α →₀ ℕ) → (β →₀ ℕ)) = Finsupp.equivMapDomain e := by
      funext x; exact (Finsupp.equivMapDomain_eq_mapDomain e x).symm
    rw [this]
    exact isMConvex_image_equivMapDomain e hM
  · have hγ' : (Finsupp.equivMapDomain e.symm γ).degree = d - 2 := by
      rw [degree_equivMapDomain, hγ]
    change (hessianAtZero (iteratedPDeriv γ (rename e f))).posIndex ≤ 1
    rw [hessianAtZero_iteratedPDeriv_rename_equiv, posIndex_reindex]
    exact hH _ hγ'

end Transfer

/-- The kernel `K_{A,B}` over an arbitrary finite variable type is Lorentzian, transported from
the case of the variables `Fin p`. -/
private lemma isLorentzian_quadraticKernel {σ : Type*} [Fintype σ] {a : σ → ℝ}
    (ha : ∀ j, 0 ≤ a j) {B : MvPolynomial σ ℝ} (hB : B.IsHomogeneous 2)
    (hBnn : B.HasNonnegCoeffs)
    (hHess : (-(hessianAtZero B - Matrix.vecMulVec a a)).PosSemidef) :
    (quadraticKernel (∑ j, C (a j) * X j) B).IsLorentzian := by
  classical
  let e := Fintype.equivFin σ
  have hK := (isLorentzian_quadraticKernel_iff (a := a ∘ e.symm) (fun j => ha _)
    (B := rename e B) hB.rename_isHomogeneous
    (fun γ => by rw [coeff_rename_equiv]; exact hBnn _)).2 (by
      have hH : hessianAtZero (rename e B) = Matrix.reindex e e (hessianAtZero B) := by
        simpa [iteratedPDeriv_zero_apply] using
          hessianAtZero_iteratedPDeriv_rename_equiv e B 0
      have hv : Matrix.vecMulVec (a ∘ e.symm) (a ∘ e.symm) =
          Matrix.reindex e e (Matrix.vecMulVec a a) := by
        ext i j; simp [Matrix.vecMulVec_apply]
      have hr : -(Matrix.reindex e e (hessianAtZero B) - Matrix.reindex e e (Matrix.vecMulVec a a))
          = Matrix.reindex e e (-(hessianAtZero B - Matrix.vecMulVec a a)) := by
        ext i j; simp
      rw [hH, hv, hr, Matrix.reindex_apply]
      exact hHess.submatrix _)
  convert isLorentzian_rename_equiv (Equiv.optionCongr e.symm) hK using 1
  simp only [quadraticKernel, map_add, map_mul, map_sum, rename_rename, rename_X, rename_C,
    map_pow]
  have h0 : Equiv.optionCongr e.symm none = none := rfl
  have h1 : ∀ x, Equiv.optionCongr e.symm (some x) = some (e.symm x) := fun _ => rfl
  have hc : (Equiv.optionCongr e.symm ∘ some ∘ e : σ → Option σ) = some := by
    funext j; exact congrArg some (e.symm_apply_apply j)
  simp only [h0, h1, hc]
  rw [← Fintype.sum_equiv e (fun x => C (a x) * X (some x))
    (fun x => C ((a ∘ e.symm) x) * X (some (e.symm x))) (fun j => by simp)]

/-- Let `σ` be finite, `a ∈ ℝ_{≥0}^σ`, `A = ∑ⱼ aⱼ xⱼ`, and `B` homogeneous of degree `2` with
nonnegative coefficients such that `Hess B - a aᵀ ⪯ 0`. Then for every Lorentzian `U ∈ ℝ[x, t]`, the
polynomial `𝓡_{A,B}(U)` is Lorentzian. -/
@[lognarayana "lem_kernel_operator_preserves"]
public theorem isLorentzian_rootOperator {σ : Type u} [Fintype σ]
    (hsub : ∀ (τ τ' : Type u) [Fintype τ] [Fintype τ'], LorentzianNonnegLinearSubstitution τ τ')
    (hmul : ∀ (τ : Type u) [Fintype τ], LorentzianMul τ)
    (hBH : ∀ (τ : Type u) [Fintype τ], NormalizedSupportPolyLorentzianOfMConvex τ)
    (hsym : ∀ (τ τ' : Type u) [Fintype τ] [Fintype τ'], BrandenHuhSymbolTheorem τ τ')
    (hder : ∀ (τ : Type u) [Fintype τ], LorentzianNonnegDerivative τ)
    {a : σ → ℝ} (ha : ∀ j, 0 ≤ a j)
    {B : MvPolynomial σ ℝ} (hB : B.IsHomogeneous 2) (hBnn : B.HasNonnegCoeffs)
    (hHess : (-(hessianAtZero B - Matrix.vecMulVec a a)).PosSemidef)
    {U : MvPolynomial (Option σ) ℝ} (hU : U.IsLorentzian) :
    (rootOperator none (rename some (∑ j, C (a j) * X j)) (rename some B) U).IsLorentzian := by
  classical
  have hK := isLorentzian_quadraticKernel ha hB hBnn hHess
  have hconv := IsLorentzian.tConvolution hsub hmul hsym hBH hU hK
  have hdt : ∀ f : MvPolynomial (Option σ) ℝ, f.IsLorentzian → (pderiv none f).IsLorentzian := by
    intro f hf
    have := hder (Option σ) (Pi.single none 1) (fun i => by
      by_cases h : i = none <;> simp [h]) f hf
    simpa [Pi.single_apply] using this
  rw [rootOperator_eq_pderiv_pderiv_tConvolution_quadraticKernel]
  exact hdt _ (hdt _ hconv)

end RootOperator

end MvPolynomial
