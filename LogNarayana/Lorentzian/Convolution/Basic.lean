/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib
public import LogNarayana.Attr
public import LogNarayana.Lorentzian.Convolution.Defs
public import LogNarayana.Lorentzian.Hessian.Defs
public import LogNarayana.Lorentzian.Symbol.Defs
public import LogNarayana.Lorentzian.Hessian.Basic
public import LogNarayana.Lorentzian.SimplexIntegration.Basic
public import LogNarayana.Lorentzian.Symbol.Basic
public import LogNarayana.Lorentzian.BrandenHuh.Basic

/-!
# Convolution in the variable `t`

For `F G ∈ R[x, t]` the convolution in `t` is `F * G = 𝔍_2 (F(x, u_1) G(x, u_2))`. This file
proves its basic properties. Over `ℝ` it is the continuous convolution
`(F * G)(ξ, θ) = ∫_0^θ F(ξ, s) G(ξ, θ - s) ds`; by `MvPolynomial.eval_simplexIntegral` the value
is an integral over the corner simplex `Δ_1(θ)`, which is the interval `[0, θ]`. It is
`R`-bilinear, being the composite of multiplication, two renamings and the linear map `𝔍_2`;
it raises degrees by one, `F * G` being homogeneous of degree `d₁ + d₂ + 1` when `F` and `G`
are homogeneous of degrees `d₁` and `d₂`; and on monomials it is the beta integral
`(x^α t^a) * (x^β t^b) = (a! b! / (a + b + 1)!) x^(α + β) t^(a + b + 1)`.

Taking `G = 1`, the antiderivative `∫₀ᵗ F ds` is `F * 1`. The antiderivative of a Lorentzian
polynomial is Lorentzian: its support is the translate `supp F + e_t`, and the Hessians of its
derivatives are either Hessians of derivatives of `F` or vanish outside one row and column.
Finally, the convolution of two Lorentzian polynomials is Lorentzian: the renamings
`t ↦ u_i` are nonnegative linear substitutions [BH, Theorem 2.10], the product of Lorentzian
polynomials is Lorentzian [BH, Corollary 2.32], and `𝔍_2` preserves Lorentzian polynomials by
the symbol theorem [BH, Theorem 3.2].

## Main results

* `MvPolynomial.eval_tConvolution`: `(F * G)(ξ, θ) = ∫_0^θ F(ξ, s) G(ξ, θ - s) ds` for `θ ≥ 0`.
* `MvPolynomial.isBilinearMap_tConvolution`: `MvPolynomial.tConvolution` is `R`-bilinear.
* `MvPolynomial.IsHomogeneous.tConvolution`: `F * G` is homogeneous of degree `d₁ + d₂ + 1`.
* `MvPolynomial.tConvolution_monomial_monomial`: the convolution of two monomials.
* `MvPolynomial.antiderivative_none_eq_tConvolution_one`: `∫₀ᵗ F ds = F * 1`.
* `MvPolynomial.IsLorentzian.antiderivative`: antiderivatives preserve the Lorentzian property.
* `MvPolynomial.IsLorentzian.tConvolution`: the convolution of two Lorentzian polynomials is
  Lorentzian.

## Implementation notes

`R[x, t]` is `MvPolynomial (Option σ) R` with `t = X none` and `x_j = X (some j)`, so the point
`(ξ, θ)` is the valuation `fun o => o.elim θ ξ` and `x^α t^a` is
`monomial (single none a + α.mapDomain some) 1`. The paper works over `ℝ`; the algebraic
statements hold over any commutative semiring that is a `ℚ`-algebra and for any variable type.

The paper assumes Lorentzian polynomials homogeneous. A Lorentzian polynomial is either `0`,
homogeneous of every degree, or homogeneous by definition, so that hypothesis is not repeated.
`MvPolynomial.IsLorentzian.antiderivative` checks the definition of `IsLorentzian` directly and
needs no cited result. The results of Brändén–Huh used for `MvPolynomial.IsLorentzian.tConvolution`
are taken as hypotheses, quantified over finite variable types in the universe of `σ`, since the
proof works in auxiliary variable types such as `σ ⊕ Fin 2`.

## References

* [LogNarayana]
* [RSW] J. Ross, H. Süss, T. Wannerer, *Dually Lorentzian polynomials*, Monatsh. Math. 208
  (2025), 495–524, Corollary 5.9.
* [BH] P. Brändén, J. Huh, *Lorentzian polynomials*, Ann. of Math. 192 (2020).
-/

universe u

open Finsupp (single)

namespace MvPolynomial

section Eval

open MeasureTheory

/-- The one-dimensional corner simplex `Δ_1(θ)` is the interval `[0, θ]`: integrating over it is
the interval integral from `0` to `θ`. -/
private lemma setIntegral_cornerSimplex_fin_one (f : (Fin 1 → ℝ) → ℝ) {θ : ℝ} (hθ : 0 ≤ θ) :
    ∫ s in cornerSimplex (Fin 1) θ, f s = ∫ x in (0 : ℝ)..θ, f fun _ => x := by
  have hpre : cornerSimplex (Fin 1) θ =
      MeasurableEquiv.funUnique (Fin 1) ℝ ⁻¹' Set.Icc 0 θ := by
    ext s
    simp [cornerSimplex, MeasurableEquiv.funUnique, Fin.forall_fin_one]
  rw [intervalIntegral.integral_of_le hθ, ← integral_Icc_eq_integral_Ioc, hpre,
    ← (volume_preserving_funUnique (Fin 1) ℝ).setIntegral_preimage_emb
      (MeasurableEquiv.funUnique (Fin 1) ℝ).measurableEmbedding]
  refine setIntegral_congr_fun ((MeasurableEquiv.funUnique (Fin 1) ℝ).measurable
    measurableSet_Icc) fun s _ => congrArg f ?_
  funext i
  simp [MeasurableEquiv.funUnique, Subsingleton.elim i default]

/-- **The convolution in `t` is the continuous convolution.** For `F G ∈ ℝ[x, t]`,
`ξ : σ → ℝ` and `0 ≤ θ`, `(F * G)(ξ, θ) = ∫_0^θ F(ξ, s) G(ξ, θ - s) ds`. -/
@[lognarayana "lem_convolution_eval"]
public theorem eval_tConvolution {σ : Type*} (F G : MvPolynomial (Option σ) ℝ) (ξ : σ → ℝ)
    {θ : ℝ} (hθ : 0 ≤ θ) :
    eval (fun o : Option σ => o.elim θ ξ) (tConvolution F G) =
      ∫ s in (0 : ℝ)..θ,
        eval (fun o : Option σ => o.elim s ξ) F *
          eval (fun o : Option σ => o.elim (θ - s) ξ) G := by
  rw [tConvolution, eval_simplexIntegral le_rfl _ ξ hθ, setIntegral_cornerSimplex_fin_one _ hθ]
  simp only [eval_mul, eval_rename]
  congr! 2 with s
  congr 3 <;> funext o <;> cases o <;> simp

end Eval

section Bilinear

/-- A bundled bilinear map `E →ₗ[R] F →ₗ[R] G`, viewed as a function of two variables, is
bilinear in the unbundled sense of `IsBilinearMap`. -/
private theorem isBilinearMap_coe {R E F G : Type*} [CommSemiring R]
    [AddCommMonoid E] [AddCommMonoid F] [AddCommMonoid G] [Module R E] [Module R F] [Module R G]
    (L : E →ₗ[R] F →ₗ[R] G) : IsBilinearMap R fun x y => L x y where
  add_left x y z := by simp
  smul_left r x y := by simp
  add_right x y z := map_add _ y z
  smul_right r x y := map_smul _ r y

/-- The convolution in `t` on `R[x, t]` is `R`-bilinear: it is the composite of the bilinear
multiplication on `R[x, u_1, u_2]`, the two renamings `t ↦ u_i` and the linear map
`simplexIntegral`. -/
@[lognarayana "lem_convolution_bilinear"]
public theorem isBilinearMap_tConvolution {σ : Type*} {R : Type*} [CommSemiring R]
    [Algebra ℚ R] :
    IsBilinearMap R (tConvolution : MvPolynomial (Option σ) R → MvPolynomial (Option σ) R →
      MvPolynomial (Option σ) R) :=
  isBilinearMap_coe <|
    ((LinearMap.mul R _).compl₁₂
      (rename (fun o : Option σ => o.elim (Sum.inr 0) Sum.inl)).toLinearMap
      (rename (fun o : Option σ => o.elim (Sum.inr 1) Sum.inl)).toLinearMap).compr₂
      (simplexIntegral σ R 2)

end Bilinear

/-- If `F` is homogeneous of degree `d₁` and `G` is homogeneous of degree `d₂`, then their
convolution in `t` is homogeneous of degree `d₁ + d₂ + 1`. -/
@[lognarayana "lem_convolution_homogeneous"]
public theorem IsHomogeneous.tConvolution {σ R : Type*} [CommSemiring R] [Algebra ℚ R]
    {F G : MvPolynomial (Option σ) R} {d₁ d₂ : ℕ} (hF : F.IsHomogeneous d₁)
    (hG : G.IsHomogeneous d₂) : (tConvolution F G).IsHomogeneous (d₁ + d₂ + 1) :=
  ((hF.rename_isHomogeneous (f := fun o : Option σ => o.elim (Sum.inr 0) Sum.inl)).mul
    (hG.rename_isHomogeneous (f := fun o : Option σ => o.elim (Sum.inr 1) Sum.inl))).simplexIntegral
    one_le_two

section Monomial

/-- The renamed product `x^(α+β) u_1^a u_2^b` has exponent `(α + β, single 0 a + single 1 b)`. -/
private lemma exponent_eq {σ : Type*} (α β : σ →₀ ℕ) (a b : ℕ) :
    (Finsupp.single none a + α.mapDomain some).mapDomain
        (fun o : Option σ => o.elim (Sum.inr 0) Sum.inl) +
      (Finsupp.single none b + β.mapDomain some).mapDomain
        (fun o : Option σ => o.elim (Sum.inr 1) Sum.inl) =
    Finsupp.sumFinsuppEquivProdFinsupp.symm
      (α + β, Finsupp.single (0 : Fin 2) a + Finsupp.single (1 : Fin 2) b) := by
  ext (j | i) <;>
    simp only [Finsupp.mapDomain_add, Finsupp.mapDomain_single, ← Finsupp.mapDomain_comp,
      Function.comp_def, Option.elim_none, Option.elim_some, Finsupp.add_apply,
      Finsupp.sumFinsuppEquivProdFinsupp_symm_inl, Finsupp.sumFinsuppEquivProdFinsupp_symm_inr]
  · simp [Finsupp.mapDomain_apply Sum.inl_injective]
  · rw [Finsupp.mapDomain_of_notMem_range _ _ (by simp),
      Finsupp.mapDomain_of_notMem_range _ _ (by simp)]
    fin_cases i <;> simp

/-- `𝔍_m` on the monomial `x^α u^γ`: its value on the basis vector `monomial (α, γ) 1`. -/
private lemma simplexIntegral_monomial_one {σ R : Type*} [CommSemiring R] [Algebra ℚ R] {m : ℕ}
    (α : σ →₀ ℕ) (γ : Fin m →₀ ℕ) :
    simplexIntegral σ R m (monomial (Finsupp.sumFinsuppEquivProdFinsupp.symm (α, γ)) 1) =
      monomial (Finsupp.single none (γ.degree + m - 1) + α.mapDomain some)
        (algebraMap ℚ R ((γ.factorial : ℚ) / ((γ.degree + m - 1).factorial : ℚ))) := by
  rw [show monomial (Finsupp.sumFinsuppEquivProdFinsupp.symm (α, γ)) (1 : R) =
      basisMonomials _ R (Finsupp.sumFinsuppEquivProdFinsupp.symm (α, γ)) by
    simp [coe_basisMonomials], simplexIntegral, Module.Basis.constr_basis, Equiv.apply_symm_apply]

/-- The exponent `u_1^a u_2^b` has total degree `a + b`. -/
private lemma degree_single_add_single (a b : ℕ) :
    (Finsupp.single (0 : Fin 2) a + Finsupp.single 1 b).degree = a + b := by
  simp [Finsupp.degree_eq_sum, Fin.sum_univ_two]

/-- The exponent `u_1^a u_2^b` has multi-index factorial `a! b!`. -/
private lemma factorial_single_add_single (a b : ℕ) :
    (Finsupp.single (0 : Fin 2) a + Finsupp.single 1 b).factorial = a.factorial * b.factorial := by
  rw [Finsupp.factorial, Finsupp.prod_fintype _ _ (fun _ => rfl), Fin.prod_univ_two]
  simp

/-- The convolution in `t` of `x^α t^a` and `x^β t^b` is
`(a! b! / (a + b + 1)!) x^(α + β) t^(a + b + 1)`. -/
@[lognarayana "lem_convolution_monomial"]
public theorem tConvolution_monomial_monomial {σ R : Type*} [CommSemiring R] [Algebra ℚ R]
    (α β : σ →₀ ℕ) (a b : ℕ) :
    tConvolution (monomial (Finsupp.single none a + α.mapDomain some) (1 : R))
        (monomial (Finsupp.single none b + β.mapDomain some) 1) =
      monomial (Finsupp.single none (a + b + 1) + (α + β).mapDomain some)
        (algebraMap ℚ R ((a.factorial * b.factorial : ℚ) / ((a + b + 1).factorial : ℚ))) := by
  rw [tConvolution, rename_monomial, rename_monomial, monomial_mul, one_mul, exponent_eq,
    simplexIntegral_monomial_one, degree_single_add_single, factorial_single_add_single,
    Nat.add_succ_sub_one, Nat.cast_mul]

end Monomial

section AntiderivativeEqConvolutionOne

variable {σ : Type*} {R : Type*} [CommSemiring R] [Algebra ℚ R]

/-- Every exponent on `Option σ` splits as its `none` part plus the image of its `some` part. -/
private lemma single_none_add_mapDomain_some (e : Option σ →₀ ℕ) :
    Finsupp.single none (e none) + e.some.mapDomain some = e := by
  ext (_ | j)
  · simp [Finsupp.mapDomain_of_notMem_range]
  · simp [Finsupp.mapDomain_apply (Option.some_injective σ)]

/-- The convolution of a monomial `z^e` with `1` is its antiderivative
`z^(e + e_t) / (e_t + 1)`. -/
private lemma tConvolution_monomial_one (e : Option σ →₀ ℕ) :
    tConvolution (monomial e (1 : R)) 1 =
      monomial (e + Finsupp.single none 1) (algebraMap ℚ R (1 / ((e none : ℚ) + 1))) := by
  have h := tConvolution_monomial_monomial (R := R) e.some 0 (e none) 0
  rw [single_none_add_mapDomain_some] at h
  simp only [Finsupp.single_zero, Finsupp.mapDomain_zero, add_zero, Nat.factorial_zero,
    Nat.cast_one, mul_one] at h
  rw [← C_1, ← monomial_zero', h, Finsupp.single_add, add_right_comm,
    single_none_add_mapDomain_some, Nat.factorial_succ]
  push_cast
  field_simp

/-- The antiderivative in `t` of `F ∈ R[x, t]` is its convolution with `1`:
`∫₀ᵗ F(x, s) ds = F * 1`. -/
@[lognarayana "lem_antiderivative_eq_convolution_one"]
public theorem antiderivative_none_eq_tConvolution_one (F : MvPolynomial (Option σ) R) :
    antiderivative none F = tConvolution F 1 := by
  let L : MvPolynomial (Option σ) R →ₗ[R] MvPolynomial (Option σ) R :=
    (simplexIntegral σ R 2).comp
      (rename (fun o : Option σ => o.elim (Sum.inr 0) Sum.inl)).toLinearMap
  have hL : ∀ G, tConvolution G 1 = L G := fun G => by simp [L, tConvolution]
  rw [hL]
  congr 1
  refine (basisMonomials (Option σ) R).ext fun e => ?_
  rw [← hL, antiderivative, Module.Basis.constr_basis, coe_basisMonomials,
    tConvolution_monomial_one]

end AntiderivativeEqConvolutionOne

section AntiderivativeLorentzian

variable {σ : Type*}

/-- `∫₀ᵗ c z^δ ds = (c / (δ_t + 1)) z^(δ + e_t)`. -/
private lemma antiderivative_monomial (t : σ) (δ : σ →₀ ℕ) (c : ℝ) :
    antiderivative t (monomial δ c) = monomial (δ + single t 1) (c / ((δ t : ℝ) + 1)) := by
  rw [← mul_one c, ← smul_eq_mul, ← smul_monomial, ← congrFun (coe_basisMonomials σ ℝ) δ,
    map_smul, antiderivative, Module.Basis.constr_basis, smul_monomial]
  congr 1
  simp [div_eq_mul_inv]

/-- `[z^(γ + e_t)] ∫₀ᵗ F ds = [z^γ] F / (γ_t + 1)`. -/
private lemma coeff_add_single_antiderivative (t : σ) (F : MvPolynomial σ ℝ) (γ : σ →₀ ℕ) :
    coeff (γ + single t 1) (antiderivative t F) = coeff γ F / ((γ t : ℝ) + 1) := by
  classical
  induction F using MvPolynomial.induction_on' with
  | monomial δ c =>
    rw [antiderivative_monomial, coeff_monomial, coeff_monomial]
    by_cases h : δ = γ
    · subst h
      simp
    · rw [if_neg (by simpa using h), if_neg h, zero_div]
  | add p q hp hq => simp [hp, hq, add_div]

/-- `[z^γ] ∫₀ᵗ F ds = 0` when `γ_t = 0`. -/
private lemma coeff_antiderivative_of_eq_zero (t : σ) (F : MvPolynomial σ ℝ) {γ : σ →₀ ℕ}
    (hγ : γ t = 0) : coeff γ (antiderivative t F) = 0 := by
  classical
  induction F using MvPolynomial.induction_on' with
  | monomial δ c =>
    rw [antiderivative_monomial, coeff_monomial, if_neg]
    rintro rfl
    simp at hγ
  | add p q hp hq => simp [hp, hq]

private lemma exists_eq_add_single_of_coeff_antiderivative_ne_zero {t : σ}
    {F : MvPolynomial σ ℝ} {γ : σ →₀ ℕ} (h : coeff γ (antiderivative t F) ≠ 0) :
    ∃ δ, γ = δ + single t 1 ∧ coeff δ F ≠ 0 := by
  have hγ : γ - single t 1 + single t 1 = γ := tsub_add_cancel_of_le <| Finsupp.single_le_iff.2 <|
    Nat.one_le_iff_ne_zero.2 fun h0 => h (coeff_antiderivative_of_eq_zero t F h0)
  refine ⟨γ - single t 1, hγ.symm, fun h0 => h ?_⟩
  rw [← hγ, coeff_add_single_antiderivative, h0, zero_div]

private lemma isHomogeneous_antiderivative {t : σ} {F : MvPolynomial σ ℝ} {d : ℕ}
    (hF : F.IsHomogeneous d) : (antiderivative t F).IsHomogeneous (d + 1) := by
  intro γ hγ
  obtain ⟨δ, rfl, hδ⟩ := exists_eq_add_single_of_coeff_antiderivative_ne_zero hγ
  rw [map_add, hF hδ, Finsupp.weight_single]
  simp

private lemma hasNonnegCoeffs_antiderivative {t : σ} {F : MvPolynomial σ ℝ}
    (hF : F.HasNonnegCoeffs) : (antiderivative t F).HasNonnegCoeffs := by
  intro γ
  by_cases h : coeff γ (antiderivative t F) = 0
  · exact h.ge
  obtain ⟨δ, rfl, -⟩ := exists_eq_add_single_of_coeff_antiderivative_ne_zero h
  rw [coeff_add_single_antiderivative]
  exact div_nonneg (hF δ) (by positivity)

private lemma support_antiderivative (t : σ) (F : MvPolynomial σ ℝ) :
    ((antiderivative t F).support : Set (σ →₀ ℕ)) =
      (· + single t 1) '' (F.support : Set (σ →₀ ℕ)) := by
  ext γ
  simp only [Finset.mem_coe, mem_support_iff, Set.mem_image]
  constructor
  · intro h
    obtain ⟨δ, rfl, hδ⟩ := exists_eq_add_single_of_coeff_antiderivative_ne_zero h
    exact ⟨δ, hδ, rfl⟩
  · rintro ⟨δ, hδ, rfl⟩
    rw [coeff_add_single_antiderivative]
    exact div_ne_zero hδ (by positivity)

/-- Moving a unit from `a` to `b` commutes with translation by `κ`. -/
private lemma tsub_single_add_single_add {γ : σ →₀ ℕ} (κ : σ →₀ ℕ) {a : σ} (b : σ)
    (ha : 1 ≤ γ a) : γ - single a 1 + single b 1 + κ = γ + κ - single a 1 + single b 1 := by
  rw [add_right_comm, tsub_add_eq_add_tsub (Finsupp.single_le_iff.2 ha)]

/-- A translate of an M-convex set is M-convex. -/
private lemma isMConvex_image_add_right {J : Set (σ →₀ ℕ)} (hJ : J.IsMConvex)
    (κ : σ →₀ ℕ) : ((· + κ) '' J).IsMConvex := by
  obtain ⟨hfin, hne, ⟨D, hD⟩, hex⟩ := hJ
  refine ⟨hfin.image _, hne.image _, ⟨D + κ.degree, ?_⟩, ?_⟩
  · rintro _ ⟨α, hα, rfl⟩
    simp [hD α hα]
  · rintro _ ⟨α, hα, rfl⟩ _ ⟨β, hβ, rfl⟩ i hi
    simp only [Finsupp.coe_add, Pi.add_apply, add_lt_add_iff_right] at hi
    obtain ⟨j, hj, hα', hβ'⟩ := hex α hα β hβ i hi
    refine ⟨j, by simpa using hj, ⟨_, hα', tsub_single_add_single_add κ j (by omega)⟩,
      ⟨_, hβ', tsub_single_add_single_add κ i (by omega)⟩⟩

/-- `(δ + e_t)! = δ! (δ_t + 1)`. -/
private lemma factorial_add_single_self (δ : σ →₀ ℕ) (t : σ) :
    (δ + single t 1).factorial = δ.factorial * (δ t + 1) := by
  classical
  have h (f : σ →₀ ℕ) : f.factorial = (f t).factorial * (f.erase t).factorial :=
    (Finsupp.mul_prod_erase' f t _ fun _ => rfl).symm
  rw [h, h δ, Finsupp.erase_add, Finsupp.erase_single, add_zero]
  simp [Nat.factorial_succ]
  ring

private lemma hessianAtZero_iteratedPDeriv_add_single_antiderivative (t : σ)
    (F : MvPolynomial σ ℝ) (α : σ →₀ ℕ) :
    hessianAtZero (iteratedPDeriv (α + single t 1) (antiderivative t F)) =
      hessianAtZero (iteratedPDeriv α F) := by
  ext p q
  rw [hessianAtZero_iteratedPDeriv_apply, hessianAtZero_iteratedPDeriv_apply,
    show α + single t 1 + single p 1 + single q 1 =
      (α + single p 1 + single q 1) + single t 1 by abel,
    coeff_add_single_antiderivative, factorial_add_single_self]
  have : (((α + single p 1 + single q 1 : σ →₀ ℕ) t : ℕ) : ℝ) + 1 ≠ 0 := by positivity
  push_cast
  field_simp

private lemma hessianAtZero_iteratedPDeriv_antiderivative_apply_of_ne {t : σ}
    {F : MvPolynomial σ ℝ} {α : σ →₀ ℕ} (hα : α t = 0) {p q : σ} (hp : p ≠ t) (hq : q ≠ t) :
    hessianAtZero (iteratedPDeriv α (antiderivative t F)) p q = 0 := by
  rw [hessianAtZero_iteratedPDeriv_apply, coeff_antiderivative_of_eq_zero, mul_zero]
  simp [hα, hp, hq]

/-- A real matrix whose entries vanish outside row `t` and column `t` has positive index at
most `1`. -/
private lemma posIndex_le_one_of_apply_eq_zero {ι : Type*} [Fintype ι] {H : Matrix ι ι ℝ}
    (t : ι) (hH : ∀ p q, p ≠ t → q ≠ t → H p q = 0) : H.posIndex ≤ 1 := by
  refine csSup_le' ?_
  rintro n ⟨W, hW, rfl⟩
  by_contra hlt
  push Not at hlt
  let φ : W →ₗ[ℝ] ℝ := (LinearMap.proj t).comp W.subtype
  have hrk := LinearMap.finrank_range_add_finrank_ker φ
  have hr : Module.finrank ℝ (LinearMap.range φ) ≤ 1 :=
    (Submodule.finrank_le _).trans (by simp)
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (p := LinearMap.ker φ) (by
    intro h
    rw [h, finrank_bot] at hrk
    omega)
  have hvt : (v : ι → ℝ) t = 0 := hv
  have hpos := hW v v.2 (by simpa using hv0)
  refine hpos.ne' ?_
  simp only [dotProduct, Matrix.mulVec]
  refine Finset.sum_eq_zero fun p _ => ?_
  by_cases hp : p = t
  · simp [hp, hvt]
  · rw [Finset.sum_eq_zero fun q _ => ?_, mul_zero]
    by_cases hq : q = t
    · simp [hq, hvt]
    · simp [hH p q hp hq]

/-- **Antiderivatives preserve the Lorentzian property**: if `F ∈ ℝ[z_i : i ∈ σ]` is
Lorentzian, then its antiderivative `∫₀ᵗ F ds` with respect to the variable `t` is
Lorentzian. -/
@[lognarayana "lem_antiderivative_lorentzian"]
public theorem IsLorentzian.antiderivative {σ : Type*} [Fintype σ] {F : MvPolynomial σ ℝ}
    (hF : F.IsLorentzian) (t : σ) : (MvPolynomial.antiderivative t F).IsLorentzian := by
  rcases hF with rfl | ⟨d, hFd, hFnn, hd1 | ⟨hd2, hMC, hHess⟩⟩
  · exact Or.inl (map_zero _)
  · have hGd := isHomogeneous_antiderivative (t := t) hFd
    have hGnn := hasNonnegCoeffs_antiderivative (t := t) hFnn
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hd1 with rfl | rfl
    · exact IsLorentzian.of_isHomogeneous_of_le_one hGnn hGd le_rfl
    · refine (isLorentzian_iff_hasAtMostOnePosEigenvalue_of_isHomogeneous_two hGd hGnn).2 ?_
      simpa using posIndex_le_one_of_apply_eq_zero t fun p q hp hq =>
        hessianAtZero_iteratedPDeriv_antiderivative_apply_of_ne (F := F) (α := 0) rfl hp hq
  · refine Or.inr ⟨d + 1, isHomogeneous_antiderivative hFd, hasNonnegCoeffs_antiderivative hFnn,
      Or.inr ⟨by omega, ?_, fun α hα => ?_⟩⟩
    · rw [support_antiderivative]
      exact isMConvex_image_add_right hMC _
    · by_cases hαt : α t = 0
      · exact posIndex_le_one_of_apply_eq_zero t fun p q hp hq =>
          hessianAtZero_iteratedPDeriv_antiderivative_apply_of_ne hαt hp hq
      · obtain ⟨β, rfl⟩ : ∃ β, α = β + single t 1 := ⟨α - single t 1,
          (tsub_add_cancel_of_le (Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 hαt))).symm⟩
        rw [hessianAtZero_iteratedPDeriv_add_single_antiderivative]
        exact hHess β (by simp at hα; omega)

end AntiderivativeLorentzian

section ConvolutionLorentzian

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
    intro γ i j
    ext b
    obtain ⟨a, rfl⟩ := e.surjective b
    simp [Finsupp.single_apply, e.injective.eq_iff]
  refine ⟨hfin.image _, hne.image _, ⟨D, ?_⟩, ?_⟩
  · rintro _ ⟨γ, hγ, rfl⟩
    rw [degree_equivMapDomain, hD γ hγ]
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
  convert hW v hv (by rintro rfl; exact hv0 (map_zero L)) using 1
  simp only [Matrix.reindex_apply, L, LinearEquiv.coe_coe, LinearEquiv.funCongrLeft_apply,
    LinearMap.funLeft_apply, dotProduct, Matrix.mulVec, Matrix.submatrix_apply]
  refine Fintype.sum_equiv e _ _ fun a => ?_
  simp only [Equiv.symm_apply_apply]
  congr 1
  exact Fintype.sum_equiv e _ _ fun b => by simp

private lemma posIndex_reindex [Fintype α] [Fintype β] (A : Matrix α α ℝ) (e : α ≃ β) :
    (Matrix.reindex e e A).posIndex = A.posIndex := by
  have h1 := posIndexSet_reindex_subset A e
  have h2 := posIndexSet_reindex_subset (Matrix.reindex e e A) e.symm
  have hA : Matrix.reindex e.symm e.symm (Matrix.reindex e e A) = A := by ext; simp
  rw [hA] at h2
  simp only [Matrix.posIndex]
  rw [Set.Subset.antisymm h1 h2]

/-- The Lorentzian property is invariant under renaming the variables along an equivalence,
across universes. -/
private lemma isLorentzian_rename_equiv [Fintype α] [Fintype β]
    (e : α ≃ β) {f : MvPolynomial α ℝ} (hf : f.IsLorentzian) : (rename e f).IsLorentzian := by
  classical
  rcases hf with rfl | ⟨d, hhom, hnn, hd⟩
  · exact Or.inl (map_zero _)
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
  · set γ' := Finsupp.equivMapDomain e.symm γ
    have hγ' : γ'.degree = d - 2 := by rw [degree_equivMapDomain, hγ]
    have hmat : hessianAtZero (iteratedPDeriv γ (rename e f)) =
        Matrix.reindex e e (hessianAtZero (iteratedPDeriv γ' f)) := by
      ext p q
      have hc : Finsupp.equivMapDomain e.symm (γ + Finsupp.single p 1 + Finsupp.single q 1) =
          γ' + Finsupp.single (e.symm p) 1 + Finsupp.single (e.symm q) 1 := by
        ext a; simp [γ', Finsupp.single_apply, e.symm_apply_eq]
      rw [Matrix.reindex_apply, Matrix.submatrix_apply, hessianAtZero_iteratedPDeriv_apply,
        hessianAtZero_iteratedPDeriv_apply, coeff_rename_equiv, hc,
        ← factorial_equivMapDomain e.symm, hc]
    change (hessianAtZero (iteratedPDeriv γ (rename e f))).posIndex ≤ 1
    rw [hmat, posIndex_reindex]
    exact hH γ' hγ'

/-- Renaming along an equivalence sends the normalized support polynomial of `J` to that of
its relabelled image. -/
private lemma rename_normalizedSupportPoly (e : α ≃ β) (J : Finset (α →₀ ℕ)) :
    rename e (normalizedSupportPoly ℝ J) =
      normalizedSupportPoly ℝ (J.map (Finsupp.equivCongrLeft e).toEmbedding) := by
  simp only [normalizedSupportPoly, map_sum, rename_monomial, Finset.sum_map,
    Equiv.coe_toEmbedding, Finsupp.equivCongrLeft_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [factorial_equivMapDomain, Finsupp.equivMapDomain_eq_mapDomain]

/-- Nonnegative linear substitution transfers along an equivalence of the source variables. -/
private lemma lorentzianNonnegLinearSubstitution_of_equiv {γ : Type*} [Fintype α] [Fintype β]
    [Fintype γ] (e : α ≃ β)
    (h : LorentzianNonnegLinearSubstitution β γ) : LorentzianNonnegLinearSubstitution α γ := by
  intro a ha f hf
  simpa only [aeval_rename, Function.comp_def, Equiv.symm_apply_apply] using
    h (fun i j => a (e.symm i) j) (fun _ _ => ha _ _) (rename e f) (isLorentzian_rename_equiv e hf)

/-- The M-convex support theorem transfers along an equivalence of the variables. -/
private lemma normalizedSupportPolyLorentzianOfMConvex_of_equiv [Fintype α] [Fintype β]
    (e : α ≃ β)
    (h : NormalizedSupportPolyLorentzianOfMConvex β) :
    NormalizedSupportPolyLorentzianOfMConvex α := by
  intro J hJ
  have h' := isLorentzian_rename_equiv e.symm (h (J.map (Finsupp.equivCongrLeft e).toEmbedding)
    (by rw [Finset.coe_map]; exact isMConvex_image_equivMapDomain e hJ))
  rwa [← rename_normalizedSupportPoly, rename_rename, Equiv.symm_comp_self, rename_id,
    AlgHom.id_apply] at h'

end Transfer

/-- Renaming variables is a `{0,1}` nonnegative linear substitution, so it preserves the
Lorentzian property. -/
private lemma isLorentzian_rename {α β : Type*} [Fintype α] [Fintype β]
    (hsub : LorentzianNonnegLinearSubstitution α β) (e : α → β) {f : MvPolynomial α ℝ}
    (hf : f.IsLorentzian) : (rename e f).IsLorentzian := by
  classical
  have h := hsub (fun i j => if j = e i then 1 else 0) (fun i j => by split_ifs <;> norm_num) f hf
  simp only [ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
  rwa [rename_eq_aeval]

/-- **Convolution preserves the Lorentzian property**: if `F G ∈ ℝ[x, t]` are (homogeneous)
Lorentzian polynomials, then their convolution `F * G` in the variable `t` is Lorentzian. -/
@[lognarayana "thm_convolution_lorentzian"]
public theorem IsLorentzian.tConvolution
    (hsub : ∀ (σ τ : Type u) [Fintype σ] [Fintype τ], LorentzianNonnegLinearSubstitution σ τ)
    (hmul : ∀ (σ : Type u) [Fintype σ], LorentzianMul σ)
    (hsym : ∀ (σ τ : Type u) [Fintype σ] [Fintype τ], BrandenHuhSymbolTheorem σ τ)
    (hBH : ∀ (σ : Type u) [Fintype σ], NormalizedSupportPolyLorentzianOfMConvex σ)
    {σ : Type u} [Fintype σ] {F G : MvPolynomial (Option σ) ℝ}
    (hF : F.IsLorentzian) (hG : G.IsLorentzian) :
    (MvPolynomial.tConvolution F G).IsLorentzian := by
  classical
  let u : Fin 2 → Option σ → σ ⊕ Fin 2 := fun k o => o.elim (Sum.inr k) Sum.inl
  exact IsLorentzian.simplexIntegral (le_refl 2)
    (lorentzianNonnegLinearSubstitution_of_equiv Equiv.ulift.{u}.symm (hsub _ _))
    (hmul _) (normalizedSupportPolyLorentzianOfMConvex_of_equiv Equiv.ulift.{u}.symm (hBH _))
    (hsym _ _) (hmul _ _ _ (isLorentzian_rename (hsub _ _) (u 0) hF)
      (isLorentzian_rename (hsub _ _) (u 1) hG))

end ConvolutionLorentzian

end MvPolynomial
