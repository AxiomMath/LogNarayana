/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module
public import LogNarayana.Lorentzian.HigherKernel.Defs
public import LogNarayana.Polynomial.RealStable.Basic
public import LogNarayana.Lorentzian.Convolution.Basic

/-!
# Higher-degree kernels

For variables `z = (z_i)_{i ∈ σ}` and one more variable `t`, the elementary kernel
`K_m(z, t) = ∑_{j=0}^m e_j(z) t^{m-j} / (m-j)!` is the coefficientwise limit, as `k → ∞`, of
the approximants `f_{m,k}(z, t) = e_m(z, t/k, …, t/k)`. Expanding `f_{m,k}` by the addition
formula for elementary symmetric functions gives `∑_j e_j(z) binom(k, m-j) (t/k)^{m-j}`, and
`binom(k, h) / k^h → 1 / h!`.

Each `e_m(w)` with `m ≤ |w|` is real-stable: differentiate the real-stable product
`∏ᵢ (y + wᵢ)` `N - m` times in `y` and set `y = 0`. Substituting `w ↦ t/k` keeps the open
upper half-plane in itself, so `f_{m,k}` is real-stable for `m ≤ |σ| + k`; by Hurwitz's theorem
the nonzero limit `K_m` is real-stable, and being homogeneous of degree `m` with nonnegative
coefficients it is Lorentzian by Brändén–Huh.

For a kernel `K` of degree `m` in `t`, the higher kernel operator
`𝓡^{(m)}_K U = ∂_t^m (U * K)` raises degrees of homogeneous polynomials by one, and is expressed
through the kernel coefficients `W_j = (m - j)! K_{m-j}` as
`W_0 ∫₀ᵗ U ds + W_1 U + ∑_{j=2}^m W_j ∂_t^{j-1} U`.

## Main results

* `MvPolynomial.tendsto_coeff_elementaryKernelApproximant`: the coefficients of `f_{m,k}`
  converge to those of `K_m`.
* `MvPolynomial.isRealStable_esymm`: `e_m` is real-stable when `m ≤ |σ|`.
* `MvPolynomial.isRealStable_elementaryKernelApproximant`: `f_{m,k}` is real-stable when
  `m ≤ |σ| + k`.
* `MvPolynomial.isRealStable_elementaryKernel`: `K_m` is real-stable.
* `MvPolynomial.isLorentzian_elementaryKernel`: `K_m` is Lorentzian.
* `MvPolynomial.IsHomogeneous.higherKernelOperator`: `𝓡^{(m)}_K` maps homogeneous polynomials
  of degree `d` to homogeneous polynomials of degree `d + 1`.
* `MvPolynomial.higherKernelOperator_eq_sum_kernelCoeff`: the formula for `𝓡^{(m)}_K` in terms
  of the kernel coefficients.
* `MvPolynomial.isLorentzian_higherKernelOperator`: `𝓡^{(m)}_K` preserves homogeneous
  Lorentzian polynomials, for a Lorentzian kernel `K`, since `U * K` is Lorentzian and each
  `∂_t` preserves the Lorentzian property.

## Implementation notes

The ring `R[z, t]` is `MvPolynomial (Option σ) R` with `t = X none` and `z_i = X (some i)`; the
partial derivative in `t` is `pderiv none`, and under `MvPolynomial.optionEquivLeft` it becomes
`Polynomial.derivative`. The paper assumes `m ≥ 1` throughout; the statements about `K_m` and
`f_{m,k}` hold for every `m` (`K_0 = f_{0,k} = 1`), and the approximants need only
`m ≤ |σ| + k`, which the paper's `k ≥ m` implies.

The cited closure properties of real stability under partial differentiation and under
specialization of a variable to a real number [Wagner, Lemma 2.4], Hurwitz's theorem (whose
consequence for coefficientwise limits of bounded degree is
`MvPolynomial.IsRealStableLimitClosed.eq_zero_or_isRealStable`), and the Brändén–Huh theorem that
homogeneous real-stable
polynomials with nonnegative coefficients are Lorentzian, are hypotheses
(`MvPolynomial.IsRealStablePDerivClosed`, `MvPolynomial.IsRealStableSpecializeClosed`,
`MvPolynomial.IsRealStableLimitClosed`, `MvPolynomial.IsLorentzianOfRealStable`).
The results of Brändén–Huh that `MvPolynomial.isLorentzian_higherKernelOperator` rests on
(nonnegative linear substitutions, products, normalized support polynomials of M-convex sets,
the symbol theorem, and nonnegative derivatives) are likewise hypotheses, for all finite variable
types in the universe of `σ`, since the convolution is computed in auxiliary variables.

## References

* [LogNarayana]
* [Wagner]
-/

open Filter Topology Finset

namespace Multiset

variable {R : Type*} [CommSemiring R]

private lemma esymm_zero_eq_one (s : Multiset R) : s.esymm 0 = 1 := by
  simp [Multiset.esymm]

private lemma esymm_cons_succ (a : R) (s : Multiset R) (n : ℕ) :
    (a ::ₘ s).esymm (n + 1) = s.esymm (n + 1) + a * s.esymm n := by
  simp [Multiset.esymm, Multiset.powersetCard_cons, Multiset.sum_map_mul_left]

/-- The elementary symmetric functions of a sum of multisets. -/
private lemma esymm_add (s t : Multiset R) (n : ℕ) :
    (s + t).esymm n = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, s.esymm p.1 * t.esymm p.2 := by
  induction t using Multiset.induction_on generalizing n with
  | empty =>
    rw [add_zero, sum_eq_single_of_mem (n, 0) (by simp)]
    · simp [esymm_zero_eq_one]
    · rintro ⟨i, _ | j⟩ _ hne
      · simp_all
      · exact mul_zero _
  | cons a t ih =>
    rw [Multiset.add_cons]
    cases n with
    | zero => simp [esymm_zero_eq_one]
    | succ n =>
      rw [esymm_cons_succ, ih, ih, Nat.sum_antidiagonal_succ', Nat.sum_antidiagonal_succ']
      simp only [esymm_zero_eq_one, esymm_cons_succ, mul_add, sum_add_distrib, mul_sum]
      ring_nf

private lemma esymm_map_const {ι : Type*} [Fintype ι] (c : R) (i : ℕ) :
    ((univ : Finset ι).val.map fun _ => c).esymm i = (Fintype.card ι).choose i * c ^ i := by
  rw [Finset.esymm_map_val, Finset.sum_congr rfl (g := fun _ => c ^ i)]
  · simp [Finset.card_powersetCard]
  · intro t ht
    rw [Finset.prod_const, (Finset.mem_powersetCard.mp ht).2]

end Multiset

namespace MvPolynomial

universe u

/-! ### The elementary kernel as a limit of its approximants -/

section Limit

private lemma esymm_map_X_some {σ R : Type*} [CommSemiring R] [Fintype σ] (j : ℕ) :
    ((univ : Finset σ).val.map fun i => (X (some i) : MvPolynomial (Option σ) R)).esymm j =
      rename some (esymm σ R j) := by
  rw [rename_eq_aeval, aeval_esymm_eq_multiset_esymm]
  rfl

/-- The expansion `f_{m,k} = ∑_j e_j(z) binom(k, m-j) (t/k)^{m-j}`. -/
private lemma elementaryKernelApproximant_eq_sum {σ R : Type*} [Fintype σ] [Field R]
    (m k : ℕ) :
    elementaryKernelApproximant σ R m k = ∑ j ∈ range (m + 1),
      C ((k.choose (m - j) : R) * ((k : R)⁻¹) ^ (m - j)) *
        (rename some (esymm σ R j) * X none ^ (m - j)) := by
  rw [elementaryKernelApproximant, aeval_esymm_eq_multiset_esymm, ← Finset.univ_disjSum_univ]
  change (Multiset.map _ (Multiset.disjSum _ _)).esymm m = _
  simp only [Multiset.disjSum, Multiset.map_add, Multiset.map_map, Function.comp_def,
    Sum.elim_inl, Sum.elim_inr]
  rw [Multiset.esymm_add, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [esymm_map_X_some, Multiset.esymm_map_const, Fintype.card_fin]
  simp only [map_mul, map_pow, map_natCast, mul_pow]
  ring

private lemma elementaryKernel_eq_sum {σ R : Type*} [Fintype σ] [Field R] (m : ℕ) :
    elementaryKernel σ R m = ∑ j ∈ range (m + 1),
      C ((m - j).factorial : R)⁻¹ * (rename some (esymm σ R j) * X none ^ (m - j)) :=
  Finset.sum_congr rfl fun j _ => by ring

/-- `binom(k, h) / k^h → 1 / h!` as `k → ∞`. -/
private lemma tendsto_choose_mul_inv_pow (h : ℕ) :
    Tendsto (fun k : ℕ => (k.choose h : ℝ) * ((k : ℝ)⁻¹) ^ h) atTop
      (𝓝 ((h.factorial : ℝ)⁻¹)) := by
  have hr : Tendsto (fun n : ℕ => (n : ℝ) * (n : ℝ)⁻¹) atTop (𝓝 1) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [mul_inv_cancel₀ (by exact_mod_cast (show n ≠ 0 by omega))]
  simpa using ProbabilityTheory.tendsto_choose_mul_pow_atTop h hr

/-- The coefficients of the approximants `e_m(z, t/k, …, t/k)` converge, as `k → ∞`, to the
coefficients of the elementary kernel `K_m(z, t)`. -/
@[lognarayana "lem_elementary_kernel_limit"]
public theorem tendsto_coeff_elementaryKernelApproximant (σ : Type*) [Fintype σ] (m : ℕ)
    (d : Option σ →₀ ℕ) :
    Tendsto (fun k : ℕ => coeff d (elementaryKernelApproximant σ ℝ m k)) atTop
      (𝓝 (coeff d (elementaryKernel σ ℝ m))) := by
  simp only [elementaryKernelApproximant_eq_sum, elementaryKernel_eq_sum, coeff_sum,
    coeff_C_mul]
  exact tendsto_finsetSum _ fun j _ => (tendsto_choose_mul_inv_pow (m - j)).mul_const _

end Limit

/-! ### Real stability of the elementary symmetric polynomials -/

section RealStableEsymm

variable {σ : Type u}

/-- Under `optionEquivLeft`, the partial derivative in `X none` is `Polynomial.derivative`. -/
private lemma optionEquivLeft_pderiv_none (p : MvPolynomial (Option σ) ℝ) :
    optionEquivLeft ℝ σ (pderiv none p) = Polynomial.derivative (optionEquivLeft ℝ σ p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [optionEquivLeft_C]
  | add p q hp hq => simp [hp, hq]
  | mul_X p n hp =>
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul, hp, map_mul,
      Polynomial.derivative_mul]
    cases n with
    | none => simp [optionEquivLeft_X_none, mul_comm, add_comm]
    | some i => simp [optionEquivLeft_X_some, mul_comm]

/-- Specializing `X none ↦ 0` keeps the constant coefficient in `X none`. -/
private lemma aeval_update_none_zero [DecidableEq σ] (p : MvPolynomial (Option σ) ℝ) :
    aeval (Function.update X none (C 0)) p = rename some ((optionEquivLeft ℝ σ p).coeff 0) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [optionEquivLeft_C]
  | add p q hp hq => rw [map_add, map_add, Polynomial.coeff_add, map_add, hp, hq]
  | mul_X p n hp =>
    rw [map_mul, map_mul, hp, aeval_X]
    cases n with
    | none => simp [optionEquivLeft_X_none]
    | some i =>
      rw [Function.update_of_ne (Option.some_ne_none i), optionEquivLeft_X_some,
        Polynomial.coeff_mul_C, map_mul, rename_X]

/-- The product `∏ᵢ (y + wᵢ)` is real-stable. -/
private lemma isRealStable_prod_X_none_add_X_some (s : Finset σ) :
    (∏ i ∈ s, (X none + X (some i)) : MvPolynomial (Option σ) ℝ).IsRealStable := by
  classical
  induction s using Finset.induction_on with
  | empty => intro ζ _; simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    refine IsRealStable.mul (fun ζ hζ h0 => ?_) ih
    have := congrArg Complex.im h0
    simp at this
    linarith [hζ none, hζ (some a)]

/-- Iterated partial derivatives of a real-stable polynomial are real-stable or zero. -/
private lemma iterate_pderiv_eq_zero_or_isRealStable {τ : Type*}
    (hder : IsRealStablePDerivClosed τ)
    {f : MvPolynomial τ ℝ} (hf : f.IsRealStable) (i : τ) (l : ℕ) :
    (pderiv i)^[l] f = 0 ∨ ((pderiv i)^[l] f).IsRealStable := by
  induction l with
  | zero => exact Or.inr hf
  | succ l ih =>
    rw [Function.iterate_succ_apply']
    rcases ih with h | h
    · exact Or.inl (by rw [h, map_zero])
    · exact hder _ h i

/-- Differentiating `∏ᵢ (y + wᵢ)` `N - m` times in `y` and setting `y = 0` leaves
`(N - m)! e_m(w)`. -/
private lemma aeval_update_none_zero_iterate_pderiv_prod [Fintype σ] [DecidableEq σ] {m : ℕ}
    (hm : m ≤ Fintype.card σ) :
    aeval (Function.update X none (C 0))
        ((pderiv none)^[Fintype.card σ - m]
          (∏ i : σ, (X none + X (some i)) : MvPolynomial (Option σ) ℝ)) =
      rename some (C ((Fintype.card σ - m).factorial : ℝ) * esymm σ ℝ m) := by
  have hiter := (Function.Semiconj.iterate_right (f := optionEquivLeft ℝ σ)
    (fun p => optionEquivLeft_pderiv_none p) (Fintype.card σ - m))
  rw [aeval_update_none_zero, hiter.eq]
  simp only [map_prod, map_add, optionEquivLeft_X_none, optionEquivLeft_X_some,
    Polynomial.coeff_iterate_derivative, zero_add, Nat.descFactorial_self]
  rw [MvPolynomial.prod_X_add_C_coeff (R := ℝ) (σ := σ) _ (Nat.sub_le _ _), Nat.sub_sub_self hm,
    nsmul_eq_mul, ← map_natCast C]

private lemma esymm_ne_zero [Fintype σ] {m : ℕ} (hm : m ≤ Fintype.card σ) :
    esymm σ ℝ m ≠ 0 := by
  intro h
  have := congrArg (eval (fun _ => (1 : ℝ))) h
  simp only [esymm, map_sum, map_prod, eval_X, prod_const_one, sum_const, card_powersetCard,
    card_univ, nsmul_eq_mul, mul_one, map_zero, Nat.cast_eq_zero] at this
  exact (Nat.choose_pos hm).ne' this

/-- A polynomial whose image under `rename some` is real-stable is itself real-stable. -/
private lemma isRealStable_of_rename_some {f : MvPolynomial σ ℝ}
    (hf : (rename (some : σ → Option σ) f).IsRealStable) : f.IsRealStable := by
  intro ζ hζ h0
  refine hf (fun o => o.elim Complex.I ζ) (fun o => by cases o <;> simp [hζ]) ?_
  rw [aeval_rename]
  exact h0

/-- Scaling by a constant does not affect real stability. -/
private lemma isRealStable_of_C_mul {f : MvPolynomial σ ℝ} {c : ℝ}
    (hf : (C c * f).IsRealStable) : f.IsRealStable := fun ζ hζ h0 =>
  hf ζ hζ (by rw [map_mul, h0, mul_zero])

/-- For `m ≤ |σ|`, the elementary symmetric polynomial `e_m(wᵢ : i ∈ σ)` is real-stable. -/
@[lognarayana "lem_esymm_real_stable"]
public theorem isRealStable_esymm {σ : Type u} [Fintype σ] {m : ℕ}
    (hm : m ≤ Fintype.card σ)
    (hder : ∀ τ : Type u, IsRealStablePDerivClosed τ)
    (hspec : ∀ (τ : Type u) [DecidableEq τ], IsRealStableSpecializeClosed τ) :
    (esymm σ ℝ m).IsRealStable := by
  classical
  have hF := aeval_update_none_zero_iterate_pderiv_prod (σ := σ) hm
  have hne : rename (some : σ → Option σ) (C ((Fintype.card σ - m).factorial : ℝ) * esymm σ ℝ m)
      ≠ 0 :=
    (map_ne_zero_iff _ (rename_injective _ (Option.some_injective σ))).mpr
      (mul_ne_zero (by simp [Nat.factorial_ne_zero]) (esymm_ne_zero hm))
  rcases iterate_pderiv_eq_zero_or_isRealStable (hder _)
    (isRealStable_prod_X_none_add_X_some (Finset.univ : Finset σ)) none
    (Fintype.card σ - m) with h | h
  · exact absurd (by rw [← hF, h, map_zero]) hne
  · exact isRealStable_of_C_mul <| isRealStable_of_rename_some <|
      hF ▸ (hspec _ _ h none 0).resolve_left (hF ▸ hne)

end RealStableEsymm

/-! ### Real stability of the elementary kernel -/

section RealStableKernel

/-- For `m ≤ |σ| + k`, the approximant `f_{m,k}(z, t) = e_m(z, t/k, …, t/k)` of the elementary
kernel is real-stable: its value at `ζ` is the value of `e_m` at
`(ζ ∘ some, ζ none / k, …, ζ none / k)`, a point of the open upper half-plane. -/
@[lognarayana "lem_esymm_specialized_real_stable"]
public theorem isRealStable_elementaryKernelApproximant {σ : Type u} [Fintype σ] {m k : ℕ}
    (hm : m ≤ Fintype.card σ + k)
    (hder : ∀ τ : Type u, IsRealStablePDerivClosed τ)
    (hspec : ∀ (τ : Type u) [DecidableEq τ], IsRealStableSpecializeClosed τ) :
    (elementaryKernelApproximant σ ℝ m k).IsRealStable := by
  intro ζ hζ
  rw [elementaryKernelApproximant, ← AlgHom.comp_apply, comp_aeval]
  refine isRealStable_esymm (by simpa [Fintype.card_sum] using hm) hder hspec _ ?_
  rintro (i | j)
  · simpa using hζ (some i)
  · simpa [Complex.mul_im] using mul_pos (inv_pos.mpr (Nat.cast_pos.mpr j.pos)) (hζ none)

/-- The elementary symmetric polynomial `e_n` is homogeneous of degree `n`. -/
private lemma isHomogeneous_esymm (σ R : Type*) [Fintype σ] [CommSemiring R] (n : ℕ) :
    (esymm σ R n).IsHomogeneous n := by
  refine IsHomogeneous.sum _ _ _ fun t ht => ?_
  simpa [(Finset.mem_powersetCard.1 ht).2] using
    IsHomogeneous.prod t (fun i => (X i : MvPolynomial σ R)) (fun _ => 1)
      (fun i _ => isHomogeneous_X R i)

/-- For `n ≠ 0` the elementary symmetric polynomial `e_n` has zero constant term. -/
private lemma constantCoeff_esymm (σ R : Type*) [Fintype σ] [CommSemiring R] {n : ℕ}
    (hn : n ≠ 0) : constantCoeff (esymm σ R n) = 0 := by
  simpa [constantCoeff_eq] using
    (isHomogeneous_esymm σ R n).coeff_eq_zero (d := 0) (by simpa using hn.symm)

/-- The approximant `e_m(z, t/k, …, t/k)` is homogeneous of degree `m`. -/
private lemma isHomogeneous_elementaryKernelApproximant (σ : Type*) [Fintype σ] (m k : ℕ) :
    (elementaryKernelApproximant σ ℝ m k).IsHomogeneous m := by
  have h := (isHomogeneous_esymm (σ ⊕ Fin k) ℝ m).aeval
    (Sum.elim (fun i : σ => (X (some i) : MvPolynomial (Option σ) ℝ))
      (fun _ : Fin k => C (k : ℝ)⁻¹ * X none)) (n := 1) (by
        rintro (i | j)
        · exact isHomogeneous_X _ _
        · simpa using (isHomogeneous_C _ _).mul (isHomogeneous_X ℝ (none : Option σ)))
  simpa [elementaryKernelApproximant] using h

/-- The elementary kernel takes the value `1/m!` at `z = 0`, `t = 1`, so it is nonzero. -/
private lemma elementaryKernel_ne_zero (σ : Type*) [Fintype σ] (m : ℕ) :
    elementaryKernel σ ℝ m ≠ 0 := by
  intro h
  have := congrArg (eval (fun o : Option σ => o.elim 1 0)) h
  rw [elementaryKernel, map_sum, Finset.sum_eq_single 0 (fun j _ hj => ?_) (by simp)] at this
  · simp [Nat.factorial_ne_zero] at this
  · simp [eval_rename, Function.comp_def, constantCoeff_esymm σ ℝ hj]

/-- For every finite variable type `σ` and every `m`, the elementary kernel
`K_m(z, t) = ∑_{j=0}^m e_j(z) t^{m-j} / (m-j)!` is real-stable: it is the nonzero
coefficientwise limit of the real-stable approximants `f_{m,k+m}`, all of degree `m`. -/
@[lognarayana "thm_elementary_kernel_real_stable"]
public theorem isRealStable_elementaryKernel {σ : Type u} [Fintype σ] (m : ℕ)
    (hder : ∀ τ : Type u, IsRealStablePDerivClosed τ)
    (hspec : ∀ (τ : Type u) [DecidableEq τ], IsRealStableSpecializeClosed τ)
    (hlim : IsRealStableLimitClosed (Option σ)) :
    (elementaryKernel σ ℝ m).IsRealStable :=
  (MvPolynomial.IsRealStableLimitClosed.eq_zero_or_isRealStable hlim m
    (fun k => elementaryKernelApproximant σ ℝ m (k + m)) _
    (fun k => isRealStable_elementaryKernelApproximant (by omega) hder hspec)
    (fun k => (isHomogeneous_elementaryKernelApproximant σ m (k + m)).totalDegree_le)
    (fun d => (tendsto_coeff_elementaryKernelApproximant σ m d).comp
      (Filter.tendsto_add_atTop_nat m))).resolve_left (elementaryKernel_ne_zero σ m)

end RealStableKernel

/-! ### The elementary kernel is Lorentzian -/

section NonnegCoeffs

variable {τ S : Type*} [CommSemiring S] [PartialOrder S] [IsOrderedRing S]

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
  rw [coeff_C]; split_ifs <;> simp [hc]

private lemma hasNonnegCoeffs_X (i : τ) : (X i : MvPolynomial τ S).HasNonnegCoeffs :=
  fun α => by
    classical
    rw [coeff_X]; split_ifs <;> simp

private lemma HasNonnegCoeffs.prod {ι : Type*} (s : Finset ι) {f : ι → MvPolynomial τ S}
    (hf : ∀ i ∈ s, (f i).HasNonnegCoeffs) : (∏ i ∈ s, f i).HasNonnegCoeffs :=
  Finset.prod_induction _ _ (fun _ _ => HasNonnegCoeffs.mul)
    (by simpa using hasNonnegCoeffs_C (τ := τ) (zero_le_one' S)) hf

private lemma HasNonnegCoeffs.pow {f : MvPolynomial τ S} (hf : f.HasNonnegCoeffs) (n : ℕ) :
    (f ^ n).HasNonnegCoeffs := by
  simpa using HasNonnegCoeffs.prod (Finset.range n) fun _ _ => hf

omit [IsOrderedRing S] in
private lemma HasNonnegCoeffs.rename {υ : Type*} {g : τ → υ} (hg : Function.Injective g)
    {f : MvPolynomial τ S} (hf : f.HasNonnegCoeffs) : (rename g f).HasNonnegCoeffs := by
  intro α
  classical
  by_cases h : ∃ u : τ →₀ ℕ, u.mapDomain g = α
  · obtain ⟨u, rfl⟩ := h
    rw [coeff_rename_mapDomain g hg]; exact hf u
  · rw [coeff_rename_eq_zero g f α fun u hu => (h ⟨u, hu⟩).elim]

private lemma hasNonnegCoeffs_esymm [Fintype τ] (n : ℕ) :
    (esymm τ S n).HasNonnegCoeffs :=
  HasNonnegCoeffs.sum _ fun _ _ => HasNonnegCoeffs.prod _ fun i _ => hasNonnegCoeffs_X i

end NonnegCoeffs

section Lorentzian

variable {σ R : Type*} [Fintype σ] [Semifield R]

/-- `K_m` is homogeneous of degree `m`: its `j`-th term has degree `j + (m - j)`. -/
private lemma isHomogeneous_elementaryKernel (m : ℕ) :
    (elementaryKernel σ R m).IsHomogeneous m := by
  refine IsHomogeneous.sum _ _ _ fun j hj => ?_
  simpa [mul_assoc, Nat.add_sub_cancel' (Finset.mem_range_succ_iff.1 hj)] using
    ((isHomogeneous_esymm σ R j).rename_isHomogeneous (f := some)).mul
      ((isHomogeneous_C _ _).mul (isHomogeneous_X_pow none (m - j)))

/-- Over an ordered semifield, `K_m` has nonnegative coefficients. -/
private lemma hasNonnegCoeffs_elementaryKernel [LinearOrder R] [IsStrictOrderedRing R]
    (m : ℕ) : (elementaryKernel σ R m).HasNonnegCoeffs :=
  HasNonnegCoeffs.sum _ fun j _ => HasNonnegCoeffs.mul (HasNonnegCoeffs.mul
    (HasNonnegCoeffs.rename (Option.some_injective σ) (hasNonnegCoeffs_esymm j))
    (hasNonnegCoeffs_C (by positivity))) (HasNonnegCoeffs.pow (hasNonnegCoeffs_X none) _)

/-- For every finite variable type `σ` and every `m`, the elementary kernel
`K_m(z, t) = ∑_{j=0}^m e_j(z) t^{m-j} / (m-j)!` is Lorentzian: it is homogeneous of degree `m`,
real-stable and has nonnegative coefficients, so Brändén–Huh applies. -/
@[lognarayana "thm_elementary_kernel_lorentzian"]
public theorem isLorentzian_elementaryKernel {σ : Type u} [Fintype σ] (m : ℕ)
    (hder : ∀ τ : Type u, IsRealStablePDerivClosed τ)
    (hspec : ∀ (τ : Type u) [DecidableEq τ], IsRealStableSpecializeClosed τ)
    (hlim : IsRealStableLimitClosed (Option σ))
    (hBH : IsLorentzianOfRealStable (Option σ)) :
    (elementaryKernel σ ℝ m).IsLorentzian :=
  hBH _ ⟨m, isHomogeneous_elementaryKernel m⟩ (isRealStable_elementaryKernel m hder hspec hlim)
    (hasNonnegCoeffs_elementaryKernel m)

end Lorentzian

/-! ### The higher kernel operator -/

section HigherKernelOperator

/-- The `k`-fold partial derivative in `i` of a polynomial homogeneous of degree `n` is
homogeneous of degree `n - k`. -/
private lemma isHomogeneous_iterate_pderiv {σ R : Type*} [CommSemiring R] {i : σ}
    {φ : MvPolynomial σ R} {n : ℕ} (h : φ.IsHomogeneous n) (k : ℕ) :
    ((pderiv i)^[k] φ).IsHomogeneous (n - k) := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    rw [Function.iterate_succ_apply', Nat.sub_succ]
    exact ih.pderiv

/-- **Degree of the higher kernel operator.** If `K ∈ ℝ[x, t]` is homogeneous of degree `m` and `U`
is homogeneous of degree `d`, then `𝓡^{(m)}_K U = ∂_t^m (U * K)` is homogeneous of degree `d + 1`:
the convolution has degree `d + m + 1`. -/
@[lognarayana "prop_higher_kernel_degree"]
public theorem IsHomogeneous.higherKernelOperator {σ : Type*} {m : ℕ}
    {K : MvPolynomial (Option σ) ℝ} (hK : K.IsHomogeneous m)
    {U : MvPolynomial (Option σ) ℝ} {d : ℕ} (hU : U.IsHomogeneous d) :
    (MvPolynomial.higherKernelOperator m K U).IsHomogeneous (d + 1) := by
  have h := isHomogeneous_iterate_pderiv (i := (none : Option σ)) (hU.tConvolution hK) m
  rwa [show d + m + 1 - m = d + 1 by omega] at h

variable {σ R : Type*} [CommSemiring R]

private lemma eq_single_none_add_mapDomain_some (e : Option σ →₀ ℕ) :
    e = Finsupp.single none (e none) + e.some.mapDomain some := by
  ext (_ | i)
  · simp [Finsupp.mapDomain_of_notMem_range]
  · simp [Finsupp.mapDomain_apply (Option.some_injective σ)]

private lemma single_none_add_mapDomain_some_apply_none (h : ℕ) (α : σ →₀ ℕ) :
    (Finsupp.single none h + α.mapDomain some : Option σ →₀ ℕ) none = h := by
  simp [Finsupp.mapDomain_of_notMem_range]

private lemma some_single_none_add_mapDomain_some (h : ℕ) (α : σ →₀ ℕ) :
    (Finsupp.single none h + α.mapDomain some).some = α := by
  ext i
  simp [Finsupp.mapDomain_apply (Option.some_injective σ)]

private lemma monomial_single_none_add_mapDomain_some (h : ℕ) (α : σ →₀ ℕ) (c : R) :
    monomial (Finsupp.single none h + α.mapDomain some) c =
      rename some (monomial α c) * X none ^ h := by
  rw [rename_monomial, X_pow_eq_monomial, monomial_mul, mul_one, add_comm]

private lemma pderiv_none_rename_mul_C_mul_X_pow (f : MvPolynomial σ R) (a : ℕ) (c : R) :
    pderiv none (rename some f * (C c * X none ^ a)) =
      rename some f * (C (c * a) * X none ^ (a - 1)) := by
  have h0 : pderiv none (rename some f) = 0 := by
    induction f using MvPolynomial.induction_on with
    | C r => simp
    | add p q hp hq => simp [hp, hq]
    | mul_X p i hp => simp [hp]
  rw [Derivation.leibniz, h0, smul_zero, add_zero, Derivation.leibniz, pderiv_C, smul_zero,
    add_zero, Derivation.leibniz_pow, pderiv_X_self]
  simp only [smul_eq_mul, map_mul, map_natCast]
  ring

private lemma iterate_pderiv_none_rename_mul_X_pow (f : MvPolynomial σ R) (a n : ℕ) :
    (pderiv none)^[n] (rename some f * X none ^ a) =
      rename some f * (C (a.descFactorial n : R) * X none ^ (a - n)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, pderiv_none_rename_mul_C_mul_X_pow,
      Nat.descFactorial_succ]
    congr 3
    push_cast; ring

private lemma kernelCoeff_monomial (m j k : ℕ) (β : σ →₀ ℕ) :
    kernelCoeff m j (monomial (Finsupp.single none k + β.mapDomain some) (1 : R)) =
      if m - j = k then monomial β ((m - j).factorial : R) else 0 := by
  classical
  simp only [kernelCoeff, LinearMap.smul_apply, LinearMap.coe_comp, Function.comp_apply,
    AlgEquiv.toLinearMap_apply, optionEquivLeft_monomial,
    single_none_add_mapDomain_some_apply_none, some_single_none_add_mapDomain_some,
    LinearMap.coe_restrictScalars, Polynomial.lcoeff_apply, Polynomial.coeff_monomial]
  split_ifs with h1 h2 h2
  · rw [smul_monomial, smul_eq_mul, mul_one]
  · omega
  · omega
  · simp

private lemma antiderivative_none_rename_mul_X_pow [Algebra ℚ R] (h : ℕ) (α : σ →₀ ℕ) :
    antiderivative none (rename some (monomial α (1 : R)) * X none ^ h) =
      rename some (monomial α (1 : R)) *
        (C (algebraMap ℚ R (1 / ((h : ℚ) + 1))) * X none ^ (h + 1)) := by
  rw [← monomial_single_none_add_mapDomain_some, antiderivative,
    show monomial (Finsupp.single none h + α.mapDomain some) (1 : R) =
      basisMonomials _ R (Finsupp.single none h + α.mapDomain some) by simp [coe_basisMonomials],
    Module.Basis.constr_basis, single_none_add_mapDomain_some_apply_none, add_right_comm,
    ← Finsupp.single_add, monomial_single_none_add_mapDomain_some, ← mul_assoc,
    mul_comm _ (C _), mul_assoc, ← smul_eq_C_mul, ← smul_mul_assoc, ← map_smul, smul_monomial,
    smul_eq_mul, mul_one]

private lemma rename_monomial_mul_C_mul (γ : σ →₀ ℕ) (a b : R) (e : ℕ) :
    rename some (monomial γ a) * (C b * X none ^ e) =
      rename some (monomial γ (a * b)) * X none ^ e := by
  rw [← mul_assoc, ← rename_C (f := (some : σ → Option σ)), ← map_mul,
    mul_comm (monomial γ a), C_mul_monomial, mul_comm b]

private lemma rename_monomial_mul_rename_monomial_mul (α β : σ →₀ ℕ) (a b : R) (e : ℕ) :
    rename some (monomial β a) * (rename some (monomial α 1) * (C b * X none ^ e)) =
      rename some (monomial (α + β) (a * b)) * X none ^ e := by
  rw [rename_monomial_mul_C_mul, ← mul_assoc, ← map_mul, monomial_mul, one_mul, add_comm β]

private lemma cast_descFactorial {n k : ℕ} (hk : k ≤ n) :
    (n.descFactorial k : ℚ) = n.factorial / (n - k).factorial := by
  rw [eq_div_iff (by positivity), mul_comm]
  exact_mod_cast Nat.factorial_mul_descFactorial hk

/-- The Beta-integral coefficient `h! k! / (h + k + 1)!` of `t ^ (h + k + 1)` in the
convolution of `t ^ h` with `t ^ k`, after `m > k` derivatives, equals the coefficient
`k! · h.descFactorial (m - k - 1)` produced by `m - k - 1` derivatives of `t ^ h`. -/
private lemma beta_mul_descFactorial {h k m : ℕ} (hkm : k < m) :
    (h.factorial * k.factorial / (h + k + 1).factorial * (h + k + 1).descFactorial m : ℚ) =
      k.factorial * h.descFactorial (m - k - 1) := by
  rcases le_or_gt (m - k - 1) h with hle | hlt
  · rw [cast_descFactorial (by omega), cast_descFactorial hle,
      show h + k + 1 - m = h - (m - k - 1) by omega]
    field_simp
  · rw [Nat.descFactorial_eq_zero_iff_lt.mpr hlt, Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)]
    simp

/-- The case `m = k` of `beta_mul_descFactorial`: the antiderivative term. -/
private lemma beta_mul_descFactorial_self (h k : ℕ) :
    (h.factorial * k.factorial / (h + k + 1).factorial * (h + k + 1).descFactorial k : ℚ) =
      k.factorial * (1 / ((h : ℚ) + 1)) := by
  rw [cast_descFactorial (by omega), show h + k + 1 - k = h + 1 by omega, Nat.factorial_succ h]
  push_cast
  field_simp

/-- The formula for monomials `U = x^α t^h` and `K = x^β t^k` with `k ≤ m`: only the term
`W_{m-k}` is nonzero, and it matches the Beta-integral coefficient of `∂_t^m (U * K)`. -/
private lemma higherKernelOperator_monomial_monomial [Algebra ℚ R] {m k : ℕ} (hm : 1 ≤ m)
    (hk : k ≤ m) (h : ℕ) (α β : σ →₀ ℕ) :
    higherKernelOperator m (monomial (Finsupp.single none k + β.mapDomain some) (1 : R))
        (monomial (Finsupp.single none h + α.mapDomain some) 1) =
      rename some (kernelCoeff m 0 (monomial (Finsupp.single none k + β.mapDomain some) 1)) *
          antiderivative none (monomial (Finsupp.single none h + α.mapDomain some) 1) +
        rename some (kernelCoeff m 1 (monomial (Finsupp.single none k + β.mapDomain some) 1)) *
          monomial (Finsupp.single none h + α.mapDomain some) 1 +
        ∑ j ∈ Finset.Icc 2 m,
          rename some (kernelCoeff m j (monomial (Finsupp.single none k + β.mapDomain some) 1)) *
            (pderiv none)^[j - 1] (monomial (Finsupp.single none h + α.mapDomain some) 1) := by
  rw [show higherKernelOperator m (monomial (Finsupp.single none k + β.mapDomain some) (1 : R))
      (monomial (Finsupp.single none h + α.mapDomain some) 1) = (pderiv none)^[m]
        (tConvolution (monomial (Finsupp.single none h + α.mapDomain some) 1)
          (monomial (Finsupp.single none k + β.mapDomain some) 1)) from rfl,
    tConvolution_monomial_monomial, monomial_single_none_add_mapDomain_some,
    iterate_pderiv_none_rename_mul_X_pow, rename_monomial_mul_C_mul]
  simp only [kernelCoeff_monomial]
  simp only [monomial_single_none_add_mapDomain_some, antiderivative_none_rename_mul_X_pow,
    iterate_pderiv_none_rename_mul_X_pow]
  rcases (show k = m ∨ k = m - 1 ∨ k + 2 ≤ m by omega) with rfl | rfl | hk2
  · rw [if_pos (by simp), if_neg (by omega), Finset.sum_eq_zero (fun j hj => by
      rw [if_neg (by simp at hj; omega)]; simp)]
    simp only [map_zero, zero_mul, add_zero]
    rw [rename_monomial_mul_rename_monomial_mul, show h + k + 1 - k = h + 1 by omega]
    congr 2
    rw [← map_natCast (algebraMap ℚ R), ← map_natCast (algebraMap ℚ R), ← map_mul, ← map_mul,
      beta_mul_descFactorial_self, Nat.sub_zero]
  · rw [if_neg (by omega), if_pos rfl, Finset.sum_eq_zero (fun j hj => by
      rw [if_neg (by simp at hj; omega)]; simp)]
    simp only [map_zero, zero_mul, zero_add, add_zero]
    rw [← one_mul (X none ^ h), ← C_1, rename_monomial_mul_rename_monomial_mul,
      show h + (m - 1) + 1 - m = h by omega]
    congr 2
    rw [← map_natCast (algebraMap ℚ R), ← map_natCast (algebraMap ℚ R), ← map_mul, mul_one,
      beta_mul_descFactorial (by omega), show m - (m - 1) - 1 = 0 by omega]
    simp
  · rw [if_neg (by omega), if_neg (by omega), Finset.sum_eq_single (m - k)
      (fun j hj hne => by rw [if_neg (by simp at hj; omega)]; simp)
      (fun hn => absurd (Finset.mem_Icc.mpr ⟨by omega, by omega⟩) hn),
      if_pos (by omega), show m - (m - k) = k by omega]
    simp only [map_zero, zero_mul, zero_add]
    rw [rename_monomial_mul_rename_monomial_mul, show h - (m - k - 1) = h + k + 1 - m by omega]
    congr 2
    rw [← map_natCast (algebraMap ℚ R), ← map_natCast (algebraMap ℚ R),
      ← map_natCast (algebraMap ℚ R), ← map_mul, ← map_mul, beta_mul_descFactorial (by omega)]

/-- The formula for a monomial `U` and an arbitrary kernel `K` of `t`-degree at most `m`: both
sides are `R`-linear in `K`, so it reduces to `higherKernelOperator_monomial_monomial`. -/
private lemma higherKernelOperator_monomial [Algebra ℚ R] {m : ℕ} (hm : 1 ≤ m)
    {K : MvPolynomial (Option σ) R} (hK : K.degreeOf none ≤ m) (h : ℕ) (α : σ →₀ ℕ) :
    higherKernelOperator m K (monomial (Finsupp.single none h + α.mapDomain some) 1) =
      rename some (kernelCoeff m 0 K) *
          antiderivative none (monomial (Finsupp.single none h + α.mapDomain some) 1) +
        rename some (kernelCoeff m 1 K) * monomial (Finsupp.single none h + α.mapDomain some) 1 +
        ∑ j ∈ Finset.Icc 2 m, rename some (kernelCoeff m j K) *
          (pderiv none)^[j - 1] (monomial (Finsupp.single none h + α.mapDomain some) 1) := by
  set U : MvPolynomial (Option σ) R := monomial (Finsupp.single none h + α.mapDomain some) 1
  let LK : MvPolynomial (Option σ) R →ₗ[R] MvPolynomial (Option σ) R :=
    ((pderiv none).toLinearMap ^ m) ∘ₗ simplexIntegral σ R 2 ∘ₗ
      LinearMap.mulLeft R (rename (fun o : Option σ => o.elim (Sum.inr 0) Sum.inl) U) ∘ₗ
        (rename (fun o : Option σ => o.elim (Sum.inr 1) Sum.inl)).toLinearMap
  let RK : MvPolynomial (Option σ) R →ₗ[R] MvPolynomial (Option σ) R :=
    LinearMap.mulRight R (antiderivative none U) ∘ₗ (rename some).toLinearMap ∘ₗ kernelCoeff m 0 +
      LinearMap.mulRight R U ∘ₗ (rename some).toLinearMap ∘ₗ kernelCoeff m 1 +
      ∑ j ∈ Finset.Icc 2 m, LinearMap.mulRight R ((pderiv none)^[j - 1] U) ∘ₗ
        (rename some).toLinearMap ∘ₗ kernelCoeff m j
  have hL : ∀ K', higherKernelOperator m K' U = LK K' := by
    intro K'
    simp only [LK, LinearMap.comp_apply, Module.End.pow_apply, Derivation.coeFn_coe,
      LinearMap.mulLeft_apply, AlgHom.toLinearMap_apply]
    rfl
  have hR : ∀ K', rename some (kernelCoeff m 0 K') * antiderivative none U +
      rename some (kernelCoeff m 1 K') * U +
      ∑ j ∈ Finset.Icc 2 m, rename some (kernelCoeff m j K') * (pderiv none)^[j - 1] U =
        RK K' := by
    intro K'
    simp [RK, LinearMap.sum_apply]
  rw [hL, hR, K.as_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun u hu => ?_
  rw [← mul_one (coeff u K), ← smul_eq_mul, ← smul_monomial, map_smul, map_smul]
  congr 1
  rw [← hL, ← hR, eq_single_none_add_mapDomain_some u]
  exact higherKernelOperator_monomial_monomial hm ((monomial_le_degreeOf none hu).trans hK) h α _

/-- The higher kernel operator expanded through the kernel coefficients: if `K` has degree at
most `m ≥ 1` in `t`, then
`𝓡^{(m)}_K(U) = W_0 ∫₀ᵗ U ds + W_1 U + ∑_{j=2}^m W_j ∂_t^{j-1} U` with `W_j = kernelCoeff m j K`.
Both sides are `R`-linear in `U`, so it suffices to check monomials. -/
@[lognarayana "prop_higher_kernel_formula"]
public theorem higherKernelOperator_eq_sum_kernelCoeff [Algebra ℚ R] {m : ℕ} (hm : 1 ≤ m)
    {K : MvPolynomial (Option σ) R} (hK : K.degreeOf none ≤ m) (U : MvPolynomial (Option σ) R) :
    higherKernelOperator m K U =
      rename some (kernelCoeff m 0 K) * antiderivative none U +
        rename some (kernelCoeff m 1 K) * U +
        ∑ j ∈ Finset.Icc 2 m, rename some (kernelCoeff m j K) * (pderiv none)^[j - 1] U := by
  let RU : MvPolynomial (Option σ) R →ₗ[R] MvPolynomial (Option σ) R :=
    LinearMap.mulLeft R (rename some (kernelCoeff m 0 K)) ∘ₗ antiderivative none +
      LinearMap.mulLeft R (rename some (kernelCoeff m 1 K)) +
      ∑ j ∈ Finset.Icc 2 m, LinearMap.mulLeft R (rename some (kernelCoeff m j K)) ∘ₗ
        ((pderiv none).toLinearMap ^ (j - 1))
  have hR : ∀ U', rename some (kernelCoeff m 0 K) * antiderivative none U' +
      rename some (kernelCoeff m 1 K) * U' +
      ∑ j ∈ Finset.Icc 2 m, rename some (kernelCoeff m j K) * (pderiv none)^[j - 1] U' =
        RU U' := by
    intro U'
    simp only [RU, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.comp_apply,
      LinearMap.mulLeft_apply, Module.End.pow_apply, Derivation.coeFn_coe]
  rw [hR]
  congr 1
  refine (basisMonomials _ R).ext fun e => ?_
  rw [coe_basisMonomials, ← hR, eq_single_none_add_mapDomain_some e]
  exact higherKernelOperator_monomial hm hK _ _

end HigherKernelOperator

section Lorentzian_preserves

/-- A single partial derivative of a Lorentzian polynomial is Lorentzian, by
`MvPolynomial.LorentzianNonnegDerivative` with the indicator coefficients of `i`. -/
private theorem isLorentzian_pderiv {τ : Type*} [Fintype τ]
    (hder : LorentzianNonnegDerivative τ) (i : τ) {f : MvPolynomial τ ℝ}
    (hf : f.IsLorentzian) : (pderiv i f).IsLorentzian := by
  classical
  have h := hder (fun j => if j = i then 1 else 0) (fun j => by split_ifs <;> norm_num) f hf
  simpa [ite_smul, Finset.sum_ite_eq'] using h

/-- Iterated partial derivatives in one variable preserve the Lorentzian property. -/
private theorem isLorentzian_iterate_pderiv {τ : Type*} [Fintype τ]
    (hder : LorentzianNonnegDerivative τ) (i : τ) (n : ℕ) {f : MvPolynomial τ ℝ}
    (hf : f.IsLorentzian) : ((pderiv i)^[n] f).IsLorentzian :=
  Function.Iterate.rec _ hf (fun _ => isLorentzian_pderiv hder i) n

/-- **Higher kernels preserve the Lorentzian property.** Let `m : ℕ` and let `K ∈ ℝ[x, t]` be
Lorentzian. Then for every Lorentzian `U ∈ ℝ[x, t]`, the polynomial `𝓡^{(m)}_K U = ∂_t^m (U * K)` is
Lorentzian. -/
@[lognarayana "prop_higher_kernel_preserves"]
public theorem isLorentzian_higherKernelOperator {σ : Type u} [Fintype σ]
    (hsub : ∀ (τ τ' : Type u) [Fintype τ] [Fintype τ'], LorentzianNonnegLinearSubstitution τ τ')
    (hmul : ∀ (τ : Type u) [Fintype τ], LorentzianMul τ)
    (hBH : ∀ (τ : Type u) [Fintype τ], NormalizedSupportPolyLorentzianOfMConvex τ)
    (hsym : ∀ (τ τ' : Type u) [Fintype τ] [Fintype τ'], BrandenHuhSymbolTheorem τ τ')
    (hder : ∀ (τ : Type u) [Fintype τ], LorentzianNonnegDerivative τ)
    {m : ℕ} {K : MvPolynomial (Option σ) ℝ} (hK : K.IsLorentzian)
    {U : MvPolynomial (Option σ) ℝ} (hU : U.IsLorentzian) :
    (higherKernelOperator m K U).IsLorentzian := by
  classical
  exact isLorentzian_iterate_pderiv (hder _) none m
    (IsLorentzian.tConvolution hsub hmul hsym hBH hU hK)

end Lorentzian_preserves

end MvPolynomial
