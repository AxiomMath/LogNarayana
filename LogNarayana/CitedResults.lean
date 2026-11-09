/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module
public import Mathlib
public import LogNarayana.Lorentzian.Convolution.Basic
public import LogNarayana.Nestohedron.Fertilitope.Basic
public import LogNarayana.AuxiliaryDefinitions
public import LogNarayana.Noncrossing.RestrictedRefinement.Defs
public import LogNarayana.Noncrossing.SchurTransform.Basic
public import LogNarayana.Lorentzian.Hessian.Basic
public import LogNarayana.StackSorting.ValidHookConfigurations.Basic
public import LogNarayana.Lorentzian.Symbol.Basic
public import LogNarayana.Narayana.Polynomials.Basic
public import LogNarayana.Lorentzian.BrandenHuh.Basic
public import LogNarayana.Polynomial.RealStable.Basic
public import LogNarayana.Lorentzian.PositiveIndex.Basic

/-!
# Cited results: proofs and small instances

The cited results of [LogNarayana] are stated as `Prop`s and taken as hypotheses by the theorems
that use them. This file proves those that follow from the library
(`MvPolynomial.AntiderivativeLorentzian`), and for each of the others proves an instance on a
small concrete case. Nothing here is used by the rest of the library.
-/

/-!
# Cited results on Lorentzian polynomials: proofs and instances

The antiderivative property `MvPolynomial.AntiderivativeLorentzian` [RSW, Corollary 5.9] is
proved for every finite variable type. For each of the other cited propositions on Lorentzian
polynomials [BH, Theorems 2.10, 2.25, 2.30, 3.2, 3.10 and Corollaries 2.11, 2.32, 3.8] and the
Lorentzian property of normalized Schur polynomials [HMMS, Theorem 3], an instance on binary
quadratic forms is proved.
-/

namespace CitedResultsDischarged.Lorentzian

open MvPolynomial Filter Topology

/-- The binary quadratic form `a z₀² + b z₀z₁ + c z₁²`, written with monomials, is homogeneous of
degree `2`. -/
private lemma isHomogeneous_quadratic_fin_two (a b c : ℝ) :
    (monomial (Finsupp.single 0 2) a + monomial (Finsupp.single 0 1 + Finsupp.single 1 1) b +
      monomial (Finsupp.single 1 2) c : MvPolynomial (Fin 2) ℝ).IsHomogeneous 2 :=
  ((isHomogeneous_monomial _ (by simp)).add (isHomogeneous_monomial _ (by simp))).add
    (isHomogeneous_monomial _ (by simp))

/-- A binary quadratic form `a z₀² + b z₀z₁ + c z₁²` with `a, b, c ≥ 0` and `4ac ≤ b²` is
Lorentzian. -/
private lemma isLorentzian_quadratic_fin_two {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : 4 * a * c ≤ b ^ 2) :
    (monomial (Finsupp.single 0 2) a + monomial (Finsupp.single 0 1 + Finsupp.single 1 1) b +
      monomial (Finsupp.single 1 2) c : MvPolynomial (Fin 2) ℝ).IsLorentzian := by
  set g : MvPolynomial (Fin 2) ℝ := monomial (Finsupp.single 0 2) a +
    monomial (Finsupp.single 0 1 + Finsupp.single 1 1) b + monomial (Finsupp.single 1 2) c
  have hnn : g.HasNonnegCoeffs := by
    intro α
    simp only [g, coeff_add, coeff_monomial]
    split_ifs <;> positivity
  rw [isLorentzian_iff_hasAtMostOnePosEigenvalue_of_isHomogeneous_two
    (isHomogeneous_quadratic_fin_two a b c) hnn]
  have hH : hessianAtZero g = !![2 * a, b; b, 2 * c] := by
    ext p q
    have := hessianAtZero_iteratedPDeriv_apply g 0 p q
    simp only [iteratedPDeriv_zero_apply, zero_add] at this
    rw [this, Finsupp.factorial, Finsupp.prod_fintype _ _ (fun _ => by simp)]
    fin_cases p <;> fin_cases q <;>
      simp [g, coeff_add, coeff_monomial, Finsupp.ext_iff, Fin.forall_fin_two, Fin.prod_univ_two]
  rw [hH, Matrix.hasAtMostOnePosEigenvalue_fin_two_iff (by positivity)]
  nlinarith

/-- The binary quadratic form in terms of the variables. -/
private lemma quadratic_fin_two_eq (a b c : ℝ) :
    (C a * X 0 ^ 2 + C b * (X 0 * X 1) + C c * X 1 ^ 2 : MvPolynomial (Fin 2) ℝ) =
      monomial (Finsupp.single 0 2) a + monomial (Finsupp.single 0 1 + Finsupp.single 1 1) b +
        monomial (Finsupp.single 1 2) c := by
  simp only [X_pow_eq_monomial]
  simp only [X, monomial_mul, C_mul_monomial, mul_one]

/-- `isLorentzian_quadratic_fin_two` in terms of the variables. -/
private lemma isLorentzian_quadratic_fin_two' {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (h : 4 * a * c ≤ b ^ 2) :
    (C a * X 0 ^ 2 + C b * (X 0 * X 1) + C c * X 1 ^ 2 : MvPolynomial (Fin 2) ℝ).IsLorentzian := by
  rw [quadratic_fin_two_eq]; exact isLorentzian_quadratic_fin_two ha hb hc h

private lemma factorial_single_add_single :
    (Finsupp.single (0 : Fin 2) 1 + Finsupp.single 1 1 : Fin 2 →₀ ℕ).factorial = 1 := by
  rw [Finsupp.factorial, Finsupp.prod_fintype _ _ (fun _ => by simp)]
  simp [Fin.prod_univ_two]

private lemma factorial_single_two (i : Fin 2) :
    (Finsupp.single i 2 : Fin 2 →₀ ℕ).factorial = 2 := by
  rw [Finsupp.factorial, Finsupp.prod_single_index (by simp)]
  rfl

/-- The full factorial normalization of `c z^α` is `c z^α / α!`. -/
private lemma fullFactorialNormalization_monomial {σ : Type*} (α : σ →₀ ℕ) (c : ℝ) :
    fullFactorialNormalization σ ℝ (monomial α c) =
      monomial α (c * algebraMap ℚ ℝ (1 / (α.factorial : ℚ))) := by
  have h : monomial α c = c • basisMonomials σ ℝ α := by
    simp [coe_basisMonomials, smul_monomial]
  rw [h, map_smul, fullFactorialNormalization, Module.Basis.constr_basis, smul_monomial,
    smul_eq_mul]

/-! ### [BH, Theorem 2.25]: closedness -/

/-- An instance of `MvPolynomial.IsLorentzianClosed (Fin 2)` with `d = 2` in which the support
drops in the limit: `F k = z₀²/(k+1) + z₀z₁` is Lorentzian and homogeneous of degree `2`, the
limit `f = z₀z₁` is homogeneous of degree `2`, the coefficients of `F k` tend to those of `f`,
and `f` is Lorentzian. -/
public theorem isLorentzianClosed_fin_two_example :
    (∀ k : ℕ,
      (monomial (Finsupp.single 0 2) (1 / ((k : ℝ) + 1)) +
        monomial (Finsupp.single 0 1 + Finsupp.single 1 1) 1 + monomial (Finsupp.single 1 2) 0 :
          MvPolynomial (Fin 2) ℝ).IsLorentzian ∧
      (monomial (Finsupp.single 0 2) (1 / ((k : ℝ) + 1)) +
        monomial (Finsupp.single 0 1 + Finsupp.single 1 1) 1 + monomial (Finsupp.single 1 2) 0 :
          MvPolynomial (Fin 2) ℝ).IsHomogeneous 2) ∧
    (monomial (Finsupp.single 0 2) 0 +
        monomial (Finsupp.single 0 1 + Finsupp.single 1 1) 1 + monomial (Finsupp.single 1 2) 0 :
          MvPolynomial (Fin 2) ℝ).IsHomogeneous 2 ∧
    (∀ α : Fin 2 →₀ ℕ, Tendsto (fun k : ℕ ↦
      (monomial (Finsupp.single 0 2) (1 / ((k : ℝ) + 1)) +
        monomial (Finsupp.single 0 1 + Finsupp.single 1 1) 1 + monomial (Finsupp.single 1 2) 0 :
          MvPolynomial (Fin 2) ℝ).coeff α) atTop
      (𝓝 ((monomial (Finsupp.single 0 2) 0 +
        monomial (Finsupp.single 0 1 + Finsupp.single 1 1) 1 + monomial (Finsupp.single 1 2) 0 :
          MvPolynomial (Fin 2) ℝ).coeff α))) ∧
    (monomial (Finsupp.single 0 2) 0 +
        monomial (Finsupp.single 0 1 + Finsupp.single 1 1) 1 + monomial (Finsupp.single 1 2) 0 :
          MvPolynomial (Fin 2) ℝ).IsLorentzian := by
  refine ⟨fun k : ℕ => ⟨isLorentzian_quadratic_fin_two (by positivity)
    zero_le_one le_rfl (by simp), isHomogeneous_quadratic_fin_two _ _ _⟩,
    isHomogeneous_quadratic_fin_two _ _ _, fun α => ?_,
    isLorentzian_quadratic_fin_two le_rfl zero_le_one le_rfl (by norm_num)⟩
  simp only [coeff_add, coeff_monomial]
  refine (Tendsto.add ?_ tendsto_const_nhds).add tendsto_const_nhds
  split_ifs
  · exact tendsto_one_div_add_atTop_nhds_zero_nat
  · exact tendsto_const_nhds

/-! ### [BH, Theorem 2.10]: nonnegative linear substitutions -/

/-- An instance of `MvPolynomial.LorentzianNonnegLinearSubstitution (Fin 2) (Fin 2)`: `z₀z₁` is
Lorentzian, and substituting `z_i = v₀ + v₁` gives the Lorentzian `(v₀ + v₁)²`. -/
public theorem lorentzianNonnegLinearSubstitution_fin_two_example :
    (X 0 * X 1 : MvPolynomial (Fin 2) ℝ).IsLorentzian ∧
      (aeval (fun i : Fin 2 ↦ ∑ j : Fin 2, (fun _ _ ↦ (1 : ℝ)) i j • (X j : MvPolynomial (Fin 2) ℝ))
        (X 0 * X 1 : MvPolynomial (Fin 2) ℝ)).IsLorentzian := by
  refine ⟨?_, ?_⟩
  · convert isLorentzian_quadratic_fin_two' (a := 0) (b := 1) (c := 0) le_rfl zero_le_one le_rfl
      (by norm_num) using 1
    simp
  · convert isLorentzian_quadratic_fin_two' (a := 1) (b := 2) (c := 1) zero_le_one zero_le_two
      zero_le_one (by norm_num) using 1
    simp only [Fin.sum_univ_two, one_smul, map_mul, aeval_X, map_one, map_ofNat]
    ring

/-! ### [BH, Corollary 2.11]: nonnegative combinations of partial derivatives -/

/-- An instance of `MvPolynomial.LorentzianNonnegDerivative (Fin 2)`: for `f = z₀²z₁` and
`a = (1, 1)`, `∂₀f + ∂₁f = z₀² + 2z₀z₁` is Lorentzian. -/
public theorem lorentzianNonnegDerivative_fin_two_example :
    (∑ i : Fin 2, (1 : ℝ) • pderiv i (X 0 ^ 2 * X 1 : MvPolynomial (Fin 2) ℝ)).IsLorentzian := by
  convert isLorentzian_quadratic_fin_two' (a := 1) (b := 2) (c := 0) zero_le_one zero_le_two
    le_rfl (by norm_num) using 1
  simp only [Fin.sum_univ_two, one_smul, Derivation.leibniz, Derivation.leibniz_pow,
    pderiv_X_self, pderiv_X_of_ne (show (0 : Fin 2) ≠ 1 by decide),
    pderiv_X_of_ne (show (1 : Fin 2) ≠ 0 by decide), smul_eq_mul, map_one, map_ofNat, map_zero]
  ring

/-! ### [BH, Corollary 2.32]: products -/

/-- An instance of `MvPolynomial.LorentzianMul (Fin 2)`: `z₀` and `z₀ + z₁` are Lorentzian, and so
is their product `z₀² + z₀z₁`. -/
public theorem lorentzianMul_fin_two_example :
    (X 0 : MvPolynomial (Fin 2) ℝ).IsLorentzian ∧
      (X 0 + X 1 : MvPolynomial (Fin 2) ℝ).IsLorentzian ∧
      (X 0 * (X 0 + X 1) : MvPolynomial (Fin 2) ℝ).IsLorentzian := by
  refine ⟨IsLorentzian.of_isHomogeneous_of_le_one (fun α => ?_) (isHomogeneous_X ℝ 0) le_rfl,
    IsLorentzian.of_isHomogeneous_of_le_one (fun α => ?_)
      ((isHomogeneous_X ℝ 0).add (isHomogeneous_X ℝ 1)) le_rfl, ?_⟩
  · rw [coeff_X]; split_ifs <;> norm_num
  · rw [coeff_add, coeff_X, coeff_X]; split_ifs <;> norm_num
  · convert isLorentzian_quadratic_fin_two' (a := 1) (b := 1) (c := 0) zero_le_one zero_le_one
      le_rfl (by norm_num) using 1
    simp only [map_one, map_zero]
    ring

/-! ### [BH, Theorem 2.30]: log-concavity -/

/-- An instance of `MvPolynomial.LorentzianLogConcave (Fin 2)` at `α = 0`: `z₀z₁` is Lorentzian
and `x ↦ log (x₀x₁)` is concave on the open positive orthant. -/
public theorem lorentzianLogConcave_fin_two_example :
    (X 0 * X 1 : MvPolynomial (Fin 2) ℝ).IsLorentzian ∧
      ConcaveOn ℝ (Set.univ.pi fun _ ↦ Set.Ioi 0) (fun x : Fin 2 → ℝ ↦
        Real.log (eval x (iteratedPDeriv 0 (X 0 * X 1 : MvPolynomial (Fin 2) ℝ)))) := by
  refine ⟨lorentzianNonnegLinearSubstitution_fin_two_example.1, ?_⟩
  have hconv : Convex ℝ (Set.univ.pi fun _ : Fin 2 ↦ Set.Ioi (0 : ℝ)) :=
    convex_pi fun _ _ => convex_Ioi 0
  have hlog (i : Fin 2) : ConcaveOn ℝ (Set.univ.pi fun _ : Fin 2 ↦ Set.Ioi (0 : ℝ))
      (fun x ↦ Real.log (x i)) :=
    (strictConcaveOn_log_Ioi.concaveOn.comp_linearMap
      (LinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 ↦ ℝ) i)).subset
      (fun x (hx : x ∈ Set.univ.pi fun _ : Fin 2 ↦ Set.Ioi (0 : ℝ)) => hx i (Set.mem_univ i))
      hconv
  refine ((hlog 0).add (hlog 1)).congr fun x hx => ?_
  have h0 : 0 < x 0 := hx 0 (Set.mem_univ 0)
  have h1 : 0 < x 1 := hx 1 (Set.mem_univ 1)
  simp [iteratedPDeriv_zero_apply, Real.log_mul h0.ne' h1.ne']

/-! ### [BH, Theorem 3.2]: the symbol theorem -/

/-- An instance of `MvPolynomial.BrandenHuhSymbolTheorem (Fin 1) (Fin 2)` with `κ = e₀` and the
operator `T(f) = [z₀] f · x₀x₁` into polynomials in other variables: for every `ℓ`, every
Lorentzian `f ∈ ℝ_κ[z₀]` has Lorentzian image. -/
public theorem brandenHuhSymbolTheorem_fin_one_fin_two_example :
    ∀ ℓ : ℤ,
      IsHomogeneousOperator (Finsupp.single (0 : Fin 1) 1) ℓ
        (LinearMap.smulRight ((lcoeff ℝ (Finsupp.single (0 : Fin 1) 1)).comp
          (restrictSupport ℝ (Set.Iic (Finsupp.single (0 : Fin 1) 1))).subtype)
          (X 0 * X 1 : MvPolynomial (Fin 2) ℝ)) →
      (algebraicSymbol (Finsupp.single (0 : Fin 1) 1)
        (LinearMap.smulRight ((lcoeff ℝ (Finsupp.single (0 : Fin 1) 1)).comp
          (restrictSupport ℝ (Set.Iic (Finsupp.single (0 : Fin 1) 1))).subtype)
          (X 0 * X 1 : MvPolynomial (Fin 2) ℝ))).IsLorentzian →
      ∀ f : restrictSupport ℝ (Set.Iic (Finsupp.single (0 : Fin 1) 1)),
        (f : MvPolynomial (Fin 1) ℝ).IsLorentzian →
          (LinearMap.smulRight ((lcoeff ℝ (Finsupp.single (0 : Fin 1) 1)).comp
            (restrictSupport ℝ (Set.Iic (Finsupp.single (0 : Fin 1) 1))).subtype)
            (X 0 * X 1 : MvPolynomial (Fin 2) ℝ) f).IsLorentzian := by
  intro ℓ _ _ f hf
  have hc : 0 ≤ (f : MvPolynomial (Fin 1) ℝ).coeff (Finsupp.single 0 1) := by
    rcases hf with h0 | ⟨d, -, hnn, -⟩
    · simp [h0]
    · exact hnn _
  simpa using lorentzianNonnegLinearSubstitution_fin_two_example.1.smul hc

/-! ### [BH, Corollary 3.8]: normalized products -/

/-- An instance of `MvPolynomial.FullFactorialNormalizationMulLorentzian (Fin 2)` with
`f = g = z₀ + z₁`: `𝓔(f) = z₀ + z₁` is Lorentzian, and so is
`𝓔(f²) = z₀²/2 + 2z₀z₁ + z₁²/2`. -/
public theorem fullFactorialNormalizationMulLorentzian_fin_two_example :
    (fullFactorialNormalization (Fin 2) ℝ (X 0 + X 1)).IsLorentzian ∧
      (fullFactorialNormalization (Fin 2) ℝ ((X 0 + X 1) * (X 0 + X 1))).IsLorentzian := by
  refine ⟨?_, ?_⟩
  · rw [map_add, X, X, fullFactorialNormalization_monomial, fullFactorialNormalization_monomial]
    refine IsLorentzian.of_isHomogeneous_of_le_one (fun α => ?_)
      ((isHomogeneous_monomial _ (by simp)).add (isHomogeneous_monomial _ (by simp))) le_rfl
    simp only [coeff_add, coeff_monomial]
    split_ifs <;> simp [Finsupp.factorial, Finsupp.prod_single_index]
  · have h : ((X 0 + X 1) * (X 0 + X 1) : MvPolynomial (Fin 2) ℝ) =
        C 1 * X 0 ^ 2 + C 2 * (X 0 * X 1) + C 1 * X 1 ^ 2 := by
      simp only [map_one, map_ofNat]; ring
    rw [h, quadratic_fin_two_eq, map_add, map_add, fullFactorialNormalization_monomial,
      fullFactorialNormalization_monomial, fullFactorialNormalization_monomial,
      factorial_single_two, factorial_single_two, factorial_single_add_single]
    exact isLorentzian_quadratic_fin_two (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-! ### [BH, Theorem 3.10]: normalized support polynomials of M-convex sets -/

/-- An instance of `MvPolynomial.NormalizedSupportPolyLorentzianOfMConvex (Fin 2)`: the discrete
simplex `J = {2e₀, e₀ + e₁, 2e₁}` is M-convex and `E_J = z₀²/2 + z₀z₁ + z₁²/2` is Lorentzian. -/
public theorem normalizedSupportPolyLorentzianOfMConvex_fin_two_example :
    (({Finsupp.single 0 2, Finsupp.single 0 1 + Finsupp.single 1 1, Finsupp.single 1 2} :
        Finset (Fin 2 →₀ ℕ)) : Set (Fin 2 →₀ ℕ)).IsMConvex ∧
      (normalizedSupportPoly ℝ ({Finsupp.single 0 2, Finsupp.single 0 1 + Finsupp.single 1 1,
        Finsupp.single 1 2} : Finset (Fin 2 →₀ ℕ))).IsLorentzian := by
  refine ⟨⟨Finset.finite_toSet _, ⟨_, Finset.mem_coe.2 (Finset.mem_insert_self _ _)⟩,
    ⟨2, fun α hα => ?_⟩, fun α hα β hβ i hi => ?_⟩, ?_⟩
  · simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hα
    rcases hα with rfl | rfl | rfl <;> simp
  · simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hα hβ ⊢
    rcases hα with rfl | rfl | rfl <;> rcases hβ with rfl | rfl | rfl <;> fin_cases i <;>
      simp [Finsupp.ext_iff, Fin.forall_fin_two, Fin.exists_fin_two] at hi ⊢
  · rw [normalizedSupportPoly, Finset.sum_insert (by simp [Finsupp.ext_iff, Fin.forall_fin_two]),
      Finset.sum_insert (by simp [Finsupp.ext_iff, Fin.forall_fin_two]), Finset.sum_singleton,
      ← add_assoc, factorial_single_two, factorial_single_two, factorial_single_add_single]
    exact isLorentzian_quadratic_fin_two (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-! ### [RSW, Corollary 5.9]: antiderivatives -/

/-- `MvPolynomial.AntiderivativeLorentzian σ` holds for every finite variable type `σ`: it is
`MvPolynomial.IsLorentzian.antiderivative`. -/
public theorem antiderivativeLorentzian_holds (σ : Type*) [Fintype σ] :
    AntiderivativeLorentzian σ :=
  fun t _ hf => hf.antiderivative t

/-! ### [HMMS, Theorem 3]: normalized Schur polynomials -/

/-- An instance of `PartitionAtMostParts.NormalizedSchurIsLorentzian` at `r = 2`, `μ = (1, 1)`:
the normalized Schur polynomial `𝓔(s_{(1,1)}(z₀, z₁)) = z₀z₁` is Lorentzian. -/
public theorem normalizedSchurIsLorentzian_fin_two_example :
    (fullFactorialNormalization (Fin 2) ℝ
      ((PartitionAtMostParts.hook 2 1 0).schurPolynomial ℝ)).IsLorentzian := by
  rw [PartitionAtMostParts.schurPolynomial_hook ℝ (by norm_num) 1 0, hsymm_zero, pow_one,
    mul_one, Fin.prod_univ_two, X, X, monomial_mul, one_mul, fullFactorialNormalization_monomial,
    factorial_single_add_single]
  convert isLorentzian_quadratic_fin_two (a := 0) (b := 1) (c := 0) le_rfl zero_le_one le_rfl
    (by norm_num) using 1
  simp

end CitedResultsDischarged.Lorentzian

/-!
# Instances of the cited results on real stability

Small concrete instances of the cited propositions `RealStablePreserverOfSymbol`,
`IsRealStableHomogenizeOfNonneg`, `IsLorentzianOfRealStable`, `IsRealStablePDerivClosed`,
`IsRealStableLimitClosed` and `IsRealStableSpecializeClosed`, and the degree-at-most-one case of
`IsLorentzianOfRealStable`.
-/

namespace CitedResultsDischarged.RealStable

open MvPolynomial Filter

/-- `z_i + c` is real-stable for every real `c`. -/
private lemma isRealStable_X_add_C {σ : Type*} (i : σ) (c : ℝ) :
    (X i + C c : MvPolynomial σ ℝ).IsRealStable := fun ζ hζ h => by
  have := congrArg Complex.im h
  simp at this
  linarith [hζ i]

/-- A nonzero constant multiple of a real-stable polynomial is real-stable. -/
private lemma isRealStable_C_mul {σ : Type*} {c : ℝ} (hc : c ≠ 0) {f : MvPolynomial σ ℝ}
    (hf : f.IsRealStable) : (C c * f).IsRealStable := fun ζ hζ => by
  rw [map_mul, aeval_C]
  exact mul_ne_zero (by simpa using hc) (hf ζ hζ)

/-- `z_i` is real-stable. -/
private lemma isRealStable_X {σ : Type*} (i : σ) : (X i : MvPolynomial σ ℝ).IsRealStable := by
  simpa using isRealStable_X_add_C i 0

/-- `z_i + z_j` is real-stable. -/
private lemma isRealStable_X_add_X {σ : Type*} (i j : σ) :
    (X i + X j : MvPolynomial σ ℝ).IsRealStable := fun ζ hζ h => by
  have := congrArg Complex.im h
  simp at this
  linarith [hζ i, hζ j]

/-! ### Specialization (`IsRealStableSpecializeClosed`) -/

/-- The instance `f = z₀ (z₁ + 1)`, `i = 1` of `IsRealStableSpecializeClosed (Fin 2)`: the
specialization `z₁ = a` is `(a + 1) z₀`, which is zero for `a = -1` and real-stable otherwise. -/
public theorem specialize_X_mul_X_add_one :
    (X 0 * (X 1 + C 1) : MvPolynomial (Fin 2) ℝ).IsRealStable ∧
      ∀ a : ℝ, aeval (Function.update X 1 (C a)) (X 0 * (X 1 + C 1) : MvPolynomial (Fin 2) ℝ) = 0 ∨
        (aeval (Function.update X 1 (C a))
          (X 0 * (X 1 + C 1) : MvPolynomial (Fin 2) ℝ)).IsRealStable := by
  refine ⟨(isRealStable_X 0).mul (isRealStable_X_add_C 1 1), fun a => ?_⟩
  have h : aeval (Function.update X 1 (C a)) (X 0 * (X 1 + C 1) : MvPolynomial (Fin 2) ℝ) =
      C (a + 1) * X 0 := by
    simp [map_add, mul_comm]
  rw [h]
  by_cases ha : a + 1 = 0
  · left; simp [ha]
  · right; exact isRealStable_C_mul ha (isRealStable_X 0)

/-! ### Differentiation (`IsRealStablePDerivClosed`) -/

/-- The instance `f = (z₀ + 1)(z₀ - 1)(z₁ + 2)` of `IsRealStablePDerivClosed (Fin 2)`, for both
variables: `∂₀ f = 2 z₀ (z₁ + 2)` and `∂₁ f = (z₀ + 1)(z₀ - 1)` are real-stable. -/
public theorem pderiv_of_quadratic_mul_linear :
    let f : MvPolynomial (Fin 2) ℝ := (X 0 + C 1) * (X 0 + C (-1)) * (X 1 + C 2)
    f.IsRealStable ∧ ∀ i : Fin 2, pderiv i f = 0 ∨ (pderiv i f).IsRealStable := by
  intro f
  refine ⟨((isRealStable_X_add_C 0 1).mul (isRealStable_X_add_C 0 (-1))).mul
    (isRealStable_X_add_C 1 2), fun i => Or.inr ?_⟩
  fin_cases i
  · have h : pderiv (0 : Fin 2) f = C 2 * (X 0 * (X 1 + C 2)) := by
      simp only [f, Derivation.leibniz, pderiv_X, map_add, pderiv_C, smul_eq_mul]
      simp only [Fin.isValue, C_1, C_neg, ne_eq, one_ne_zero, not_false_eq_true,
        Pi.single_eq_of_ne, add_zero, mul_zero, Pi.single_eq_same, mul_one, zero_add]
      rw [show (C 2 : MvPolynomial (Fin 2) ℝ) = 2 from map_ofNat C 2]
      ring
    rw [show ((⟨0, by decide⟩ : Fin 2)) = 0 from rfl, h]
    exact isRealStable_C_mul two_ne_zero ((isRealStable_X 0).mul (isRealStable_X_add_C 1 2))
  · have h : pderiv (1 : Fin 2) f = (X 0 + C 1) * (X 0 + C (-1)) := by
      simp only [f, Derivation.leibniz, pderiv_X, map_add, pderiv_C, smul_eq_mul]
      simp
    rw [show ((⟨1, by decide⟩ : Fin 2)) = 1 from rfl, h]
    exact (isRealStable_X_add_C 0 1).mul (isRealStable_X_add_C 0 (-1))

/-! ### Hurwitz's theorem (`IsRealStableLimitClosed`) -/

/-- An instance of Hurwitz's theorem `IsRealStableLimitClosed (Fin 1)` on the upper half-plane
`Ω = {z | 0 < Im z₀}`, in the non-vanishing branch: `F k z = z₀ + i/(k+1)` is analytic and
non-vanishing on `Ω`, converges to `f z = z₀` uniformly on `Ω` (the difference is the constant
`i/(k+1)`), and `f` does not vanish on `Ω`. -/
public theorem hurwitz_X_add_I_div_succ :
    let Ω : Set (Fin 1 → ℂ) := {z | ∀ i, 0 < (z i).im}
    let F : ℕ → (Fin 1 → ℂ) → ℂ := fun k z => z 0 + ((1 / ((k : ℝ) + 1) : ℝ) : ℂ) * Complex.I
    IsOpen Ω ∧ IsConnected Ω ∧ (∀ k, AnalyticOnNhd ℂ (F k) Ω) ∧ (∀ k, ∀ z ∈ Ω, F k z ≠ 0) ∧
      (∀ K ⊆ Ω, IsCompact K → TendstoUniformlyOn F (fun z => z 0) atTop K) ∧
      ∀ z ∈ Ω, z 0 ≠ 0 := by
  intro Ω F
  refine ⟨isOpen_upperHalfPlane_pi, isConnected_upperHalfPlane_pi, fun k => ?_,
    fun k z hz h => ?_, fun K _ _ => ?_, fun z hz h => ?_⟩
  · exact ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0).analyticOnNhd _).add
      analyticOnNhd_const
  · have := congrArg Complex.im h
    simp only [F, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, Complex.zero_im] at this
    have h1 : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    linarith [hz 0]
  · rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [(tendsto_order.1 tendsto_one_div_add_atTop_nhds_zero_nat).2 ε hε]
      with k hk z _
    rw [dist_eq_norm]
    simp only [F, sub_add_cancel_left, norm_neg, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs]
    rwa [abs_of_pos (by positivity)]
  · have := hz 0
    rw [h, Complex.zero_im] at this
    exact lt_irrefl _ this

/-- An instance of Hurwitz's theorem `IsRealStableLimitClosed (Fin 1)` on the upper half-plane,
in the identically-zero branch: the non-vanishing constants `F k = 1/(k+1)` converge uniformly
to `0`, which vanishes identically on `Ω`. -/
public theorem hurwitz_const_inv_succ :
    let Ω : Set (Fin 1 → ℂ) := {z | ∀ i, 0 < (z i).im}
    let F : ℕ → (Fin 1 → ℂ) → ℂ := fun k _ => ((1 / ((k : ℝ) + 1) : ℝ) : ℂ)
    IsOpen Ω ∧ IsConnected Ω ∧ (∀ k, AnalyticOnNhd ℂ (F k) Ω) ∧ (∀ k, ∀ z ∈ Ω, F k z ≠ 0) ∧
      (∀ K ⊆ Ω, IsCompact K → TendstoUniformlyOn F (fun _ => 0) atTop K) ∧
      ∀ z ∈ Ω, (fun _ => (0 : ℂ)) z = 0 := by
  intro Ω F
  refine ⟨isOpen_upperHalfPlane_pi, isConnected_upperHalfPlane_pi, fun k => analyticOnNhd_const,
    fun k z _ => ?_, fun K _ _ => ?_, fun _ _ => rfl⟩
  · simp only [F, ne_eq, Complex.ofReal_eq_zero]
    positivity
  · rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [(tendsto_order.1 tendsto_one_div_add_atTop_nhds_zero_nat).2 ε hε]
      with k hk z _
    rw [dist_comm, dist_zero_right]
    simp only [F, Complex.norm_real, Real.norm_eq_abs]
    rwa [abs_of_pos (by positivity)]

/-- An instance of the polynomial form of Hurwitz's theorem,
`MvPolynomial.IsRealStableLimitClosed.eq_zero_or_isRealStable`, with `D = 1`: `F k = z₀ + 1/(k+1)`
is real-stable of degree `1`, its coefficients tend to those of `z₀`, and every coefficientwise
limit `f` is `z₀`, which is real-stable. -/
public theorem limit_X_add_inv_succ :
    let F : ℕ → MvPolynomial (Fin 1) ℝ := fun k => X 0 + C (1 / ((k : ℝ) + 1))
    (∀ k, (F k).IsRealStable) ∧ (∀ k, (F k).totalDegree ≤ 1) ∧
      (∀ α, Tendsto (fun k => (F k).coeff α) atTop
        (nhds ((X 0 : MvPolynomial (Fin 1) ℝ).coeff α))) ∧
      ∀ f : MvPolynomial (Fin 1) ℝ,
        (∀ α, Tendsto (fun k => (F k).coeff α) atTop (nhds (f.coeff α))) →
          f = 0 ∨ f.IsRealStable := by
  intro F
  have hlim : ∀ α, Tendsto (fun k => (F k).coeff α) atTop
      (nhds ((X 0 : MvPolynomial (Fin 1) ℝ).coeff α)) := by
    intro α
    simp only [F, coeff_add, coeff_C]
    by_cases hα : α = 0
    · subst hα
      simp only [if_true]
      have : Tendsto (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1)) atTop (nhds 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      simpa using (tendsto_const_nhds (x := (X 0 : MvPolynomial (Fin 1) ℝ).coeff 0)).add this
    · simp only [Ne.symm hα, if_false, add_zero]
      exact tendsto_const_nhds
  refine ⟨fun k => isRealStable_X_add_C 0 _, fun k => ?_, hlim, fun f hf => Or.inr ?_⟩
  · refine (totalDegree_add _ _).trans (max_le ?_ ?_)
    · simp
    · simp
  · have : f = X 0 := by
      ext α
      exact tendsto_nhds_unique (hf α) (hlim α)
    rw [this]
    exact isRealStable_X 0

/-! ### Stable homogeneous polynomials are Lorentzian (`IsLorentzianOfRealStable`) -/

/-- The case of degree at most one of `IsLorentzianOfRealStable`: a homogeneous polynomial of
degree `d ≤ 1` with nonnegative coefficients is Lorentzian (real stability is not needed). -/
public theorem isLorentzianOfRealStable_of_le_one {σ : Type*} [Fintype σ]
    (f : MvPolynomial σ ℝ) {d : ℕ} (hd : f.IsHomogeneous d) (hd1 : d ≤ 1)
    (hnn : f.HasNonnegCoeffs) : f.IsLorentzian :=
  IsLorentzian.of_isHomogeneous_of_le_one hnn hd hd1

/-- The instance `f = z₀ z₁` of `IsLorentzianOfRealStable (Fin 2)`: `f` is homogeneous of degree
`2`, real-stable, has nonnegative coefficients, and is Lorentzian (its Hessian `!![0, 1; 1, 0]`
has one positive eigenvalue). -/
public theorem isLorentzian_X_mul_X :
    let f : MvPolynomial (Fin 2) ℝ := X 0 * X 1
    f.IsHomogeneous 2 ∧ f.IsRealStable ∧ f.HasNonnegCoeffs ∧ f.IsLorentzian := by
  intro f
  have hhom : f.IsHomogeneous 2 := (isHomogeneous_X ℝ 0).mul (isHomogeneous_X ℝ 1)
  have hnn : f.HasNonnegCoeffs := by
    intro α
    simp only [f, X, monomial_mul, one_mul, coeff_monomial]
    split_ifs <;> norm_num
  refine ⟨hhom, (isRealStable_X 0).mul (isRealStable_X 1), hnn, ?_⟩
  rw [isLorentzian_iff_hasAtMostOnePosEigenvalue_of_isHomogeneous_two hhom hnn]
  have hH : hessianAtZero f = !![0, 1; 1, 0] := by
    ext i j
    rw [hessianAtZero_apply_eq_constantCoeff_pderiv_pderiv]
    fin_cases i <;> fin_cases j <;> simp [f]
  rw [hH, Matrix.hasAtMostOnePosEigenvalue_fin_two_iff le_rfl]
  norm_num

/-! ### Homogenization (`IsRealStableHomogenizeOfNonneg`) -/

/-- The homogenization may be computed as a sum over any finite set of exponents containing the
support. -/
private lemma homogenize_eq_sum_of_support_subset {σ : Type*} (f : MvPolynomial σ ℝ) (D : ℕ)
    {s : Finset (σ →₀ ℕ)} (hs : f.support ⊆ s) :
    f.homogenize D = ∑ α ∈ s with α.degree ≤ D,
      monomial (α.mapDomain Option.some + Finsupp.single none (D - α.degree)) (coeff α f) := by
  rw [homogenize]
  refine Finset.sum_subset (Finset.filter_subset_filter _ hs) fun α hα hα' => ?_
  have : α ∉ f.support := fun h => hα' (Finset.mem_filter.2 ⟨h, (Finset.mem_filter.1 hα).2⟩)
  rw [notMem_support_iff.1 this, monomial_zero]

/-- The instance `f = z₀ + 1` of `IsRealStableHomogenizeOfNonneg (Fin 1)`: `f` has nonnegative
coefficients and is real-stable, and its homogenization `f_H = z₀ + y` of degree
`totalDegree f = 1` is real-stable. -/
public theorem homogenize_X_add_one :
    let f : MvPolynomial (Fin 1) ℝ := X 0 + C 1
    f.HasNonnegCoeffs ∧ f.IsRealStable ∧ (f.homogenize f.totalDegree).IsRealStable := by
  intro f
  suffices h : f.IsRealStable ∧ f.HasNonnegCoeffs ∧
      ∀ D : ℕ, f.totalDegree ≤ D → (f.homogenize D).IsRealStable from
    ⟨h.2.1, h.1, h.2.2 _ le_rfl⟩
  have hcoeff : ∀ α, f.coeff α = (if Finsupp.single 0 1 = α then 1 else 0) +
      (if (0 : Fin 1 →₀ ℕ) = α then 1 else 0) := by
    intro α
    simp only [f, coeff_add, coeff_X, coeff_C]
  refine ⟨isRealStable_X_add_C 0 1, fun α => ?_, fun D hD => ?_⟩
  · rw [hcoeff]; split_ifs <;> norm_num
  have hne : (Finsupp.single (0 : Fin 1) 1) ≠ 0 := by simp
  have hc1 : f.coeff (Finsupp.single 0 1) = 1 := by
    rw [hcoeff, if_pos rfl, if_neg hne.symm, add_zero]
  have hc0 : f.coeff 0 = 1 := by
    rw [hcoeff, if_neg hne, if_pos rfl, zero_add]
  have hsupp : f.support ⊆ {Finsupp.single 0 1, 0} := by
    intro α hα
    rw [mem_support_iff, hcoeff] at hα
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_contra h
    push Not at h
    exact hα (by rw [if_neg (Ne.symm h.1), if_neg (Ne.symm h.2), add_zero])
  have hD1 : 1 ≤ D := by
    refine le_trans ?_ hD
    have hmem : Finsupp.single (0 : Fin 1) 1 ∈ f.support := by
      rw [mem_support_iff, hc1]; exact one_ne_zero
    simpa using le_totalDegree hmem
  have h : f.homogenize D = X none ^ (D - 1) * (X (some 0) + X none) := by
    rw [homogenize_eq_sum_of_support_subset f D hsupp, Finset.filter_true_of_mem (by
      intro α hα
      simp only [Finset.mem_insert, Finset.mem_singleton] at hα
      rcases hα with rfl | rfl <;> simp [hD1]), Finset.sum_pair hne, hc1, hc0]
    obtain ⟨E, rfl⟩ := Nat.exists_eq_add_of_le' hD1
    simp only [Finsupp.mapDomain_single, Finsupp.mapDomain_zero, Finsupp.degree_single,
      map_zero, zero_add, Nat.add_sub_cancel, Nat.sub_zero]
    rw [X_pow_eq_monomial, X, X, mul_add, monomial_mul, monomial_mul, one_mul,
      ← Finsupp.single_add]
    simp [add_comm]
  rw [h]
  exact (isRealStable_X_pow _ _).mul (isRealStable_X_add_X _ _)

/-! ### Symbols (`RealStablePreserverOfSymbol`) -/

/-- The multi-indices below `e₀` in one variable are `0` and `e₀`. -/
private lemma Iic_single_zero_one :
    Finset.Iic (Finsupp.single (0 : Fin 1) 1) = {Finsupp.single 0 1, 0} := by
  ext α
  have hα : α = Finsupp.single 0 (α 0) :=
    Finsupp.ext fun i => by fin_cases i; simp
  simp only [Finset.mem_Iic, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro h
    have h0 : α 0 ≤ 1 := by simpa using h 0
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 h0 with h1 | h1
    · exact Or.inr (by rw [hα, h1, Finsupp.single_zero])
    · exact Or.inl (by rw [hα, h1])
  · rintro (rfl | rfl)
    · exact le_rfl
    · exact zero_le

/-- The instance `κ = e₀`, `T` the inclusion `ℝ_κ[z₀] → ℝ[z₀]` of `RealStablePreserverOfSymbol
(Fin 1)`: the algebraic symbol of `T` is `z₀ + w₀`, which is real-stable, and `T` maps every
real-stable `f` to the real-stable `f`. -/
public theorem realStablePreserver_inclusion :
    let κ : Fin 1 →₀ ℕ := Finsupp.single 0 1
    let T := (restrictSupport ℝ (Set.Iic κ)).subtype
    algebraicSymbol κ T = X (Sum.inl 0) + X (Sum.inr 0) ∧
      (algebraicSymbol κ T).IsRealStable ∧
      ∀ f : restrictSupport ℝ (Set.Iic κ), (f : MvPolynomial (Fin 1) ℝ).IsRealStable →
        T f = 0 ∨ (T f).IsRealStable := by
  intro κ T
  have hsym : algebraicSymbol κ T = X (Sum.inl 0) + X (Sum.inr 0) := by
    simp only [algebraicSymbol, T, Submodule.subtype_apply]
    refine (Finset.sum_attach _ (fun α : Fin 1 →₀ ℕ =>
      C (κ.choose α : ℝ) * rename Sum.inl (monomial α 1) *
        rename Sum.inr (monomial (κ - α) 1))).trans ?_
    refine (Finset.sum_congr (s₂ := {κ, 0}) ?_ fun _ _ => rfl).trans ?_
    · convert Iic_single_zero_one
    rw [Finset.sum_pair (by simp [κ])]
    simp [κ, Finsupp.choose, X, rename_monomial, Finsupp.mapDomain_single]
  refine ⟨hsym, hsym ▸ isRealStable_X_add_X _ _, fun f hf => Or.inr hf⟩

end CitedResultsDischarged.RealStable

/-!
# Cited results on polynomials: small instances

Each of the eight cited polynomial results stated as `Prop`s (`ShiftedNarayanaNegRealRoots`,
`ShiftedNarayanaInterlacing`, `ShiftedNarayanaCoeffLogConvex`, `NarayanaTransformLogConvex`,
`Polynomial.NewtonInequalities`, `Polynomial.GammaRealRootedIff`,
`Polynomial.JacobiRootsSimpleInIoo`, `PowerSeries.LagrangeInversion`) is proved on a small,
non-degenerate instance. Newton's inequality is proved for every polynomial of degree at most
two, and Lagrange inversion for `φ = 1 + u`, `n ≤ 2`, over every commutative ring. Lagrange
inversion `PowerSeries.LagrangeInversion` and the γ-expansion `ShiftedNarayanaGammaExpansion` are
proved in full in the library itself (`PowerSeries.lagrangeInversion`,
`shiftedNarayanaGammaExpansion_holds`).
-/

namespace CitedResultsDischarged.Polynomials

open Polynomial

/-! ### Negative real zeros and interlacing -/

/-- `Ñ_2 = 1 + 3x + x²` has exactly two negative real zeros, `(-3 ± √5) / 2`. -/
public theorem encard_negRoots_shiftedNarayanaPolynomial_two :
    {ρ : ℝ | ρ < 0 ∧ (shiftedNarayanaPolynomial 2).IsRoot ρ}.encard = 2 := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hs : 0 < Real.sqrt 5 := by positivity
  have hs3 : Real.sqrt 5 < 3 := by nlinarith
  have hset : {ρ : ℝ | ρ < 0 ∧ (shiftedNarayanaPolynomial 2).IsRoot ρ} =
      {(-3 - Real.sqrt 5) / 2, (-3 + Real.sqrt 5) / 2} := by
    ext ρ
    simp only [shiftedNarayanaPolynomial_two, Set.mem_ofPred_eq, IsRoot.def, eval_add, eval_one,
      eval_mul, eval_X, eval_pow, eval_ofNat, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨-, h⟩
      have : (ρ - (-3 - Real.sqrt 5) / 2) * (ρ - (-3 + Real.sqrt 5) / 2) = 0 := by nlinarith
      rcases mul_eq_zero.1 this with h | h
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    · rintro (rfl | rfl) <;> constructor <;> nlinarith
  rw [hset, Set.encard_pair]
  intro h
  linarith

/-- Interlacing of the zeros of `Ñ_1 = 1 + x` and `Ñ_2 = 1 + 3x + x²`: the zero `-1` of `Ñ_1`
lies strictly between the two zeros of `Ñ_2`. This is `ShiftedNarayanaInterlacing` at `m = 1`. -/
public theorem shiftedNarayana_interlacing_one :
    ∀ (ρ : Fin 1 → ℝ) (θ : Fin (1 + 1) → ℝ), StrictMono ρ → StrictMono θ →
      (∀ i, (shiftedNarayanaPolynomial 1).IsRoot (ρ i)) →
      (∀ i, (shiftedNarayanaPolynomial (1 + 1)).IsRoot (θ i)) →
      ∀ i : Fin 1, θ i.castSucc < ρ i ∧ ρ i < θ i.succ := by
  intro ρ θ _ hθ hρr hθr i
  obtain rfl : i = 0 := Subsingleton.elim _ _
  have h0 := hρr 0
  have ha := hθr 0
  have hb := hθr 1
  have hlt : θ 0 < θ 1 := hθ (by decide)
  simp only [shiftedNarayanaPolynomial_one, IsRoot.def, eval_add, eval_one, eval_X] at h0
  simp only [show 1 + 1 = 2 from rfl, shiftedNarayanaPolynomial_two, IsRoot.def, eval_add,
    eval_one, eval_mul, eval_X, eval_pow, eval_ofNat] at ha hb
  have hsum : θ 0 + θ 1 = -3 := by
    have : (θ 0 - θ 1) * (θ 0 + θ 1 + 3) = 0 := by nlinarith
    rcases mul_eq_zero.1 this with h | h
    · exact absurd (by linarith : θ 0 = θ 1) hlt.ne
    · linarith
  have hprod : (θ 0 + 1) * (θ 1 + 1) = -1 := by nlinarith
  have hρ : ρ 0 = -1 := by linarith
  simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one, hρ]
  constructor <;> nlinarith

/-! ### Coefficientwise log-convexity and the Narayana transformation -/

/-- `Ñ_1 Ñ_3 - Ñ_2² = x + x² + x³` has nonnegative coefficients: `ShiftedNarayanaCoeffLogConvex`
at `m = 1`. -/
public theorem coeff_shiftedNarayana_one_logConvex (k : ℕ) :
    0 ≤ (shiftedNarayanaPolynomial 1 * shiftedNarayanaPolynomial (1 + 2) -
      shiftedNarayanaPolynomial (1 + 1) ^ 2).coeff k := by
  have h : shiftedNarayanaPolynomial 1 * shiftedNarayanaPolynomial (1 + 2) -
      shiftedNarayanaPolynomial (1 + 1) ^ 2 = X + X ^ 2 + X ^ 3 := by
    rw [show 1 + 2 = 3 from rfl, show 1 + 1 = 2 from rfl, shiftedNarayanaPolynomial_one,
      shiftedNarayanaPolynomial_two, shiftedNarayanaPolynomial_three]
    ring
  rw [h]
  simp only [coeff_add, coeff_X, coeff_X_pow]
  split_ifs <;> norm_num

/-- The Narayana transformation `b₀ = a₀`, `b_{n+1} = ∑_{k ≤ n} [x^k] Ñ_n · a_k` of a positive
log-convex sequence satisfies `b_{n+1}² ≤ b_n b_{n+2}` for `n ≤ 2`: `NarayanaTransformLogConvex`
restricted to its first three inequalities (`b₁ = a₀`, `b₂ = a₀ + a₁`, `b₃ = a₀ + 3a₁ + a₂`,
`b₄ = a₀ + 6a₁ + 6a₂ + a₃`). -/
public theorem narayanaTransform_logConvex_of_le_two :
    ∀ a b : ℕ → ℝ, (∀ k, 0 < a k) → (∀ k, a (k + 1) ^ 2 ≤ a k * a (k + 2)) →
      b 0 = a 0 →
      (∀ n, b (n + 1) = ∑ k ∈ Finset.range (n + 1), (shiftedNarayanaPolynomial n).coeff k * a k) →
      ∀ n, n ≤ 2 → b (n + 1) ^ 2 ≤ b n * b (n + 2) := by
  intro a b ha hlc hb0 hb n hn
  have hb1 : b 1 = a 0 := by
    simp [hb 0, shiftedNarayanaPolynomial_zero]
  have hb2 : b 2 = a 0 + a 1 := by
    rw [hb 1, shiftedNarayanaPolynomial_one]
    simp [Finset.sum_range_succ, coeff_one, coeff_X]
  have hb3 : b 3 = a 0 + 3 * a 1 + a 2 := by
    rw [hb 2, shiftedNarayanaPolynomial_two]
    simp [Finset.sum_range_succ, coeff_one, coeff_X, coeff_X_pow]
  have hb4 : b 4 = a 0 + 6 * a 1 + 6 * a 2 + a 3 := by
    rw [hb 3, shiftedNarayanaPolynomial_three]
    simp [Finset.sum_range_succ, coeff_one, coeff_X, coeff_X_pow]
  have h0 := ha 0
  have h1 := ha 1
  have h2 := ha 2
  have h3 := ha 3
  have l0 := hlc 0
  have l1 := hlc 1
  interval_cases n
  · rw [hb0, hb1, hb2]
    nlinarith
  · rw [hb1, hb2, hb3]
    nlinarith
  · rw [hb2, hb3, hb4]
    nlinarith [mul_pos h0 h1, mul_pos h0 h2, mul_pos h0 h3]

/-! ### Newton's inequalities -/

/-- `Polynomial.NewtonInequalities` for polynomials of degree at most two: a real quadratic
`c₀ + c₁x + c₂x²` with nonnegative coefficients and a real zero has `c₀c₂ ≤ c₁²`. -/
public theorem isLogConcave_of_splits_of_natDegree_le_two (f : ℝ[X]) (hdeg : f.natDegree ≤ 2)
    (hnn : ∀ j, 0 ≤ f.coeff j) (hf : f.Splits) : f.IsLogConcave := by
  refine ⟨hnn, fun j => ?_⟩
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · by_cases h2 : f.coeff 2 = 0
    · rw [h2, mul_zero]
      positivity
    · have hnd : f.natDegree = 2 := le_antisymm hdeg (le_natDegree_of_ne_zero h2)
      have hd0 : f.degree ≠ 0 := by
        rw [degree_eq_natDegree (by rintro rfl; simp at h2), hnd]; decide
      obtain ⟨x, hx⟩ := hf.exists_eval_eq_zero hd0
      rw [eval_eq_sum_range' (by omega : f.natDegree < 3)] at hx
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one,
        zero_add] at hx
      have e0 := hnn 0
      have e2 := hnn 2
      nlinarith [sq_nonneg (2 * f.coeff 2 * x + f.coeff 1), mul_nonneg e0 e2]
  · rw [coeff_eq_zero_of_natDegree_lt (by omega : f.natDegree < j + 2), mul_zero]
    positivity

/-! ### γ-polynomials and real roots -/

/-- `Polynomial.GammaRealRootedIff` at `n = 2`, `γ₀ = γ₁ = 1`: the symmetric polynomial
`h(x) = (1 + x)² + x = 1 + 3x + x²` and its γ-polynomial `γ_h(z) = 1 + z` both split with
nonpositive zeros. -/
public theorem gammaRealRootedIff_two_one_one :
    ∀ h : ℝ[X], h.natDegree ≤ 2 → (∀ i ≤ 2, h.coeff i = h.coeff (2 - i)) →
      ∀ γ : ℕ → ℝ, (∀ j, γ j = 1) →
        h = ∑ i ∈ Finset.range (2 / 2 + 1), C (γ i) * X ^ i * (1 + X) ^ (2 - 2 * i) →
        let γh : ℝ[X] := ∑ i ∈ Finset.range (2 / 2 + 1), C (γ i) * X ^ i
        (γh.Splits ∧ ∀ r ∈ γh.roots, r ≤ 0) ↔ (h.Splits ∧ ∀ r ∈ h.roots, r ≤ 0) := by
  intro h _ _ γ hγ hh₀
  subst hh₀
  dsimp only
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hs : 0 < Real.sqrt 5 := by positivity
  have hs3 : Real.sqrt 5 < 3 := by nlinarith
  set r₁ : ℝ := (-3 - Real.sqrt 5) / 2
  set r₂ : ℝ := (-3 + Real.sqrt 5) / 2
  have hg : (∑ j ∈ Finset.range (2 / 2 + 1), C (γ j) * X ^ j : ℝ[X]) = X - C (-1) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, hγ, map_one, map_neg]
    ring
  have key₁ : C r₁ + C r₂ = (-3 : ℝ[X]) := by
    rw [← C_add, show r₁ + r₂ = -3 by simp only [r₁, r₂]; ring, map_neg, map_ofNat]
  have key₂ : C r₁ * C r₂ = (1 : ℝ[X]) := by
    rw [← C_mul, show r₁ * r₂ = 1 by simp only [r₁, r₂]; nlinarith, C_1]
  have hh : (∑ j ∈ Finset.range (2 / 2 + 1), C (γ j) * X ^ j * (1 + X) ^ (2 - 2 * j) : ℝ[X]) =
      (X - C r₁) * (X - C r₂) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, hγ, map_one]
    norm_num
    linear_combination X * key₁ - key₂
  rw [hg, hh]
  refine iff_of_true ⟨Splits.X_sub_C _, ?_⟩ ⟨(Splits.X_sub_C _).mul (Splits.X_sub_C _), ?_⟩
  · intro r hr
    rw [roots_X_sub_C, Multiset.mem_singleton] at hr
    rw [hr]; norm_num
  · intro r hr
    rw [roots_mul (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)), roots_X_sub_C,
      roots_X_sub_C, Multiset.mem_add, Multiset.mem_singleton, Multiset.mem_singleton] at hr
    rcases hr with rfl | rfl
    · simp only [r₁]; linarith
    · simp only [r₂]; linarith

/-! ### Zeros of Jacobi polynomials -/

/-- `P^{(1,0)}_1(t) = (3t + 1)/2` has its single zero `-1/3`, simple and in `(-1, 1)`:
`Polynomial.JacobiRootsSimpleInIoo` at `α = 1`, `β = 0`, `n = 1`. -/
public theorem jacobi_one_zero_one_roots :
    (jacobi 1 0 1).roots.card = 1 ∧ (jacobi 1 0 1).roots.Nodup ∧
      ∀ x ∈ (jacobi 1 0 1).roots, x ∈ Set.Ioo (-1 : ℝ) 1 := by
  have hP : jacobi 1 0 1 = C (3 / 2 : ℝ) * (X - C (-1 / 3)) := by
    apply Polynomial.funext
    intro x
    simp [jacobi, Finset.sum_range_succ, Nat.choose]
    ring
  rw [hP, roots_C_mul _ (by norm_num), roots_X_sub_C]
  refine ⟨rfl, Multiset.nodup_singleton _, fun x hx => ?_⟩
  rw [Multiset.mem_singleton] at hx
  subst hx
  constructor <;> norm_num

/-- `P^{(0,0)}_2(t) = (3t² - 1)/2`, the Legendre polynomial, has the two simple zeros `∓1/√3` in
`(-1, 1)`: `Polynomial.JacobiRootsSimpleInIoo` at `α = β = 0`, `n = 2`. -/
public theorem jacobi_zero_zero_two_roots :
    (jacobi 0 0 2).roots.card = 2 ∧ (jacobi 0 0 2).roots.Nodup ∧
      ∀ x ∈ (jacobi 0 0 2).roots, x ∈ Set.Ioo (-1 : ℝ) 1 := by
  set s : ℝ := Real.sqrt (1 / 3)
  have hs2 : s ^ 2 = 1 / 3 := Real.sq_sqrt (by norm_num)
  have hs : 0 < s := Real.sqrt_pos.2 (by norm_num)
  have hs1 : s < 1 := by nlinarith
  have hP : jacobi 0 0 2 = C (3 / 2 : ℝ) * ((X - C (-s)) * (X - C s)) := by
    apply Polynomial.funext
    intro x
    simp [jacobi, Finset.sum_range_succ, Nat.choose]
    linear_combination (3 / 2 : ℝ) * hs2
  rw [hP, roots_C_mul _ (by norm_num),
    roots_mul (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)), roots_X_sub_C,
    roots_X_sub_C]
  refine ⟨rfl, ?_, fun x hx => ?_⟩
  · rw [Multiset.singleton_add, Multiset.nodup_cons, Multiset.mem_singleton]
    exact ⟨by linarith, Multiset.nodup_singleton _⟩
  · rw [Multiset.mem_add, Multiset.mem_singleton, Multiset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> constructor <;> linarith

/-! ### Lagrange inversion -/

/-- `PowerSeries.LagrangeInversion R` for `φ = 1 + u` and `n ≤ 2`, over EVERY commutative ring
`R` (characteristic `p` and torsion included): from `G = X (1 + G)` alone,
`n [x^n] G^k = k [u^{n-k}] (1 + u)^n` for `1 ≤ k ≤ n ≤ 2`. -/
public theorem lagrangeInversion_one_add_X_of_le_two (R : Type*) [CommRing R] :
    ∀ G : PowerSeries R, PowerSeries.constantCoeff G = 0 →
      G = PowerSeries.X * Polynomial.aeval G (1 + X : R[X]) →
      ∀ k n : ℕ, 1 ≤ k → k ≤ n → n ≤ 2 →
        (n : R) * PowerSeries.coeff n (G ^ k) = (k : R) * ((1 + X : R[X]) ^ n).coeff (n - k) := by
  intro G hG0 hG k n hk hkn hn
  have hfix : G = PowerSeries.X * (1 + G) := by
    conv_lhs => rw [hG]
    simp
  have c0 : PowerSeries.coeff 0 G = 0 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]; exact hG0
  have c1 : PowerSeries.coeff 1 G = 1 := by
    rw [hfix, PowerSeries.coeff_succ_X_mul]
    simp [hG0]
  have c2 : PowerSeries.coeff 2 G = 1 := by
    rw [hfix, PowerSeries.coeff_succ_X_mul]
    simp only [map_add, PowerSeries.coeff_one, c1]
    simp
  have sq2 : ((1 + X : R[X]) ^ 2) = 1 + 2 * X + X ^ 2 := by ring
  interval_cases n <;> interval_cases k
  · simp [c1]
  · simp only [pow_one, Nat.cast_ofNat, Nat.cast_one, one_mul, c2, sq2]
    simp [coeff_X, coeff_one]
  · rw [sq G, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, sq2]
    simp [Finset.sum_range_succ, c0, c1, c2, coeff_X, coeff_one]

end CitedResultsDischarged.Polynomials

/-!
# Instances of Defant's fertilitope results

Instances, at the permutation `π = 2135467`, of five results of C. Defant (*Fertilitopes*,
Discrete Comput. Geom. 2023) that the library takes as hypotheses: the refined fertility
formula, injectivity of `𝓗 ↦ 𝐪_𝓗` on valid hook configurations, the lattice points of the
fertilitope, and the identification of fertilitopes with integral binary nestohedra. The
fertilitope of `2135467` is the nestohedron `Δ_{1} + Δ_{2} + Δ_{3} + Δ_{12} + Δ_{123}`.
-/

namespace CitedResultsDischarged.Fertility

open Polynomial List
open scoped Pointwise

private lemma narayanaPolynomial_one : narayanaPolynomial 1 = X := by
  simp [narayanaPolynomial]

private lemma narayanaPolynomial_two : narayanaPolynomial 2 = X + X ^ 2 := by
  have h : (C (2⁻¹ : ℝ) : ℝ[X]) * 2 = 1 := by
    rw [← map_ofNat C 2, ← C_mul]; norm_num
  simp only [narayanaPolynomial, OfNat.ofNat_ne_zero, ↓reduceIte, Nat.cast_ofNat, map_mul,
    map_natCast, Nat.reduceAdd, Nat.one_le_ofNat, Finset.sum_Icc_succ_top, Finset.Icc_self,
    Finset.sum_singleton, Nat.choose_succ_self_right, tsub_self, Nat.choose_zero_right,
    Nat.cast_one, mul_one, pow_one, Nat.choose_self, Nat.add_one_sub_one]
  rw [h]; ring

private lemma narayanaPolynomial_three : narayanaPolynomial 3 = X + 3 * X ^ 2 + X ^ 3 := by
  have h : (C (3⁻¹ : ℝ) : ℝ[X]) * 3 = 1 := by
    rw [← map_ofNat C 3, ← C_mul]; norm_num
  simp only [narayanaPolynomial, OfNat.ofNat_ne_zero, ↓reduceIte, Nat.cast_ofNat, map_mul,
    map_natCast, Nat.reduceAdd, Nat.one_le_ofNat, Finset.sum_Icc_succ_top, Finset.Icc_self,
    Finset.sum_singleton, Nat.choose, add_zero, tsub_self, Nat.choose_zero_right, Nat.cast_one,
    mul_one, pow_one, Nat.add_one_sub_one, Nat.choose_one_right, Nat.choose_succ_self_right]
  rw [h]; ring

/-- The Narayana sum over the five triples, stated for any `S` equal to them so that the
dependent index type `Fin (numDescents + 1)` can be fixed to `Fin 3`. -/
private lemma sum_narayanaTupleProd_five (S : Finset (Fin 3 → ℕ))
    (hS : S = {![3, 1, 1], ![2, 1, 2], ![2, 2, 1], ![1, 2, 2], ![1, 3, 1]}) :
    ∑ q ∈ S, narayanaTupleProd q = 5 * X ^ 3 + 12 * X ^ 4 + 5 * X ^ 5 := by
  subst hS
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [narayanaTupleProd, Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, narayanaPolynomial_one,
    narayanaPolynomial_two, narayanaPolynomial_three]
  ring

/-- **Refined fertility formula at `π = 2135467`**: `x D_π(x) = ∑_{𝐪 ∈ 𝒱(π)} N_𝐪(x)`, both
sides being `5x³ + 12x⁴ + 5x⁵`. -/
public theorem X_mul_fiberDescentPolynomial_eq_sum_validCompositions_2135467 :
    (X : ℝ[X]) * [2, 1, 3, 5, 4, 6, 7].fiberDescentPolynomial ℝ =
      ∑ q ∈ [2, 1, 3, 5, 4, 6, 7].validCompositions, narayanaTupleProd q := by
  rw [X_mul_fiberDescentPolynomial_2135467]
  exact (sum_narayanaTupleProd_five _ validCompositions_2135467).symm

/-- **Injectivity of `𝓗 ↦ 𝐪_𝓗` at `π = 2135467`**: the five valid hook configurations of
`2135467` induce five distinct valid compositions. -/
public theorem injOn_hookComposition_2135467 :
    Set.InjOn [2, 1, 3, 5, 4, 6, 7].hookComposition
      ([2, 1, 3, 5, 4, 6, 7].validHookConfigurations : Set (Finset (ℕ × ℕ))) := by
  apply Finset.card_image_iff.mp
  change [2, 1, 3, 5, 4, 6, 7].validCompositions.card = _
  rw [validCompositions_2135467, validHookConfigurations_2135467]
  decide

/-- The five valid compositions of `2135467`, as points of `ℝ³`. -/
private def fiveReal : Set (Fin 3 → ℝ) :=
  {![3, 1, 1], ![2, 1, 2], ![2, 2, 1], ![1, 2, 2], ![1, 3, 1]}

/-- The binary building set `{{1}, {2}, {3}, {1, 2}, {1, 2, 3}}` on `[3]` (indexed from `0`). -/
private def building3 : Finset (Finset (Fin 3)) :=
  {{0}, {1}, {2}, {0, 1}, Finset.univ}

private lemma isBinaryBuildingSet_building3 : IsBinaryBuildingSet building3 where
  exists_eq_Icc := by decide
  singleton_mem := by decide
  disjoint_or_subset_or_subset := by decide

private lemma nestohedron_building3 :
    nestohedron ℝ building3 (fun _ => 1) = convexHull ℝ fiveReal := by
  simp only [nestohedron, one_smul, coordSimplex]
  rw [← convexHull_sum]
  congr 1
  simp only [building3]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [show (Finset.univ : Finset (Fin 3)) = {0, 1, 2} by decide]
  have e0 : (Pi.single 0 1 : Fin 3 → ℝ) = ![1, 0, 0] := by ext i; fin_cases i <;> rfl
  have e1 : (Pi.single 1 1 : Fin 3 → ℝ) = ![0, 1, 0] := by ext i; fin_cases i <;> rfl
  have e2 : (Pi.single 2 1 : Fin 3 → ℝ) = ![0, 0, 1] := by ext i; fin_cases i <;> rfl
  simp only [Finset.coe_insert, Finset.coe_singleton]
  simp only [Set.image_insert_eq, Set.image_singleton]
  simp only [e0, e1, e2]
  simp only [Set.insert_eq, Set.union_add, Set.add_union, Set.singleton_add_singleton,
    Matrix.cons_add_cons, Matrix.empty_add_empty]
  norm_num
  ext v
  simp only [fiveReal, Set.mem_singleton_iff, Set.mem_insert_iff]
  tauto

/-- The coordinatewise cast of the five triples, stated for any `S` equal to them so that the
dependent index type `Fin (numDescents + 1)` can be fixed to `Fin 3`. -/
private lemma image_cast_five (S : Finset (Fin 3 → ℕ))
    (hS : S = {![3, 1, 1], ![2, 1, 2], ![2, 2, 1], ![1, 2, 2], ![1, 3, 1]}) :
    (fun q i => (q i : ℝ)) '' (S : Set (Fin 3 → ℕ)) = fiveReal := by
  have cast_vec3 (a b c : ℕ) : (fun q i => (q i : ℝ)) ![a, b, c] = ![(a : ℝ), b, c] := by
    ext i; fin_cases i <;> rfl
  subst hS
  simp only [fiveReal, Finset.coe_insert, Finset.coe_singleton, Set.image_insert_eq,
    Set.image_singleton, cast_vec3, Nat.cast_ofNat, Nat.cast_one]

private lemma fertilitope_2135467 :
    fertilitope ℝ [2, 1, 3, 5, 4, 6, 7] = convexHull ℝ fiveReal :=
  congrArg (convexHull ℝ) (image_cast_five _ validCompositions_2135467)

private lemma mem_permWords_2135467 : [2, 1, 3, 5, 4, 6, 7] ∈ permWords 7 := by
  simp only [permWords, words, IsWord, Set.mem_ofPred_eq]
  decide

private lemma isIntegralBinaryNestohedron_convexHull_fiveReal :
    IsIntegralBinaryNestohedron ℝ (convexHull ℝ fiveReal) := by
  refine ⟨⟨building3, isBinaryBuildingSet_building3, fun _ => 1, fun _ _ => one_pos,
    nestohedron_building3.symm⟩, fun v hv => ⟨extremePoints_subset hv, ?_⟩⟩
  have hv' := extremePoints_convexHull_subset hv
  simp only [fiveReal, Set.mem_insert_iff, Set.mem_singleton_iff] at hv'
  intro i
  rcases hv' with rfl | rfl | rfl | rfl | rfl <;> fin_cases i <;>
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.zero_eta, Fin.isValue, Fin.mk_one,
      Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Set.mem_range,
      Int.cast_eq_one, exists_eq]
  all_goals exact ⟨_, Int.cast_ofNat _⟩

/-- **Lattice points of the fertilitope at `π = 2135467`**: `Fer_π ∩ ℤ³ = 𝒱(π)`. -/
public theorem latticePoints_fertilitope_eq_image_validCompositions_2135467 :
    (fertilitope ℝ [2, 1, 3, 5, 4, 6, 7]).latticePoints =
      (fun q i => (q i : ℝ)) '' ([2, 1, 3, 5, 4, 6, 7].validCompositions :
        Set (Fin ([2, 1, 3, 5, 4, 6, 7].numDescents + 1) → ℕ)) :=
  latticePoints_fertilitope_2135467.trans (image_cast_five _ validCompositions_2135467).symm

/-- **The fertilitope of `2135467` is an integral binary nestohedron**: it is
`Δ_{1} + Δ_{2} + Δ_{3} + Δ_{12} + Δ_{123}`. -/
public theorem isIntegralBinaryNestohedron_fertilitope_2135467 :
    IsIntegralBinaryNestohedron ℝ (fertilitope ℝ [2, 1, 3, 5, 4, 6, 7]) := by
  rw [fertilitope_2135467]
  exact isIntegralBinaryNestohedron_convexHull_fiveReal

/-- **Realization of an integral binary nestohedron at `r = 3`**: the nestohedron
`P = Δ_{1} + Δ_{2} + Δ_{3} + Δ_{12} + Δ_{123} ⊆ ℝ³` is an integral binary nestohedron, and
`π = 2135467 ∈ S_7`, with `des(π) = 2`, has `𝒱(π) = P ∩ ℤ³`. -/
public theorem exists_validCompositions_eq_latticePoints_nestohedron_three :
    IsIntegralBinaryNestohedron ℝ
        (nestohedron ℝ ({{0}, {1}, {2}, {0, 1}, Finset.univ} : Finset (Finset (Fin 3)))
          (fun _ => 1)) ∧
      ∃ n : ℕ, 1 ≤ n ∧ ∃ π ∈ permWords n, ∃ h : π.numDescents + 1 = 3,
        (nestohedron ℝ ({{0}, {1}, {2}, {0, 1}, Finset.univ} : Finset (Finset (Fin 3)))
          (fun _ => 1)).latticePoints =
          (fun q i => (q (Fin.cast h.symm i) : ℝ)) ''
            (π.validCompositions : Set (Fin (π.numDescents + 1) → ℕ)) := by
  have hP : nestohedron ℝ ({{0}, {1}, {2}, {0, 1}, Finset.univ} : Finset (Finset (Fin 3)))
      (fun _ => 1) = convexHull ℝ fiveReal := nestohedron_building3
  rw [hP]
  refine ⟨isIntegralBinaryNestohedron_convexHull_fiveReal, 7, by norm_num,
    [2, 1, 3, 5, 4, 6, 7], mem_permWords_2135467, by decide, ?_⟩
  rw [← fertilitope_2135467]
  exact latticePoints_fertilitope_eq_image_validCompositions_2135467

end CitedResultsDischarged.Fertility

/-!
# Cited combinatorial results: instances and reductions

Instances of seven cited results of the library, each a `def … : Prop` taken as a hypothesis.

* `BonaFiberDescentSymmetric`, `BonaFiberDescentUnimodal` (stated over `ℕ`, as their sources):
  the same over every semiring, resp. strictly ordered semiring, follows by the cast `ℕ → R`
  (`BonaFiberDescentSymmetric.isSymmetricWRT`, `BonaFiberDescentUnimodal.isUnimodalPolynomial`),
  and each instance is proved at `π = 123` and `π = 2134` over every admissible coefficient ring.
* `BrandenFiberDescentGammaNonneg` (the γ-expansion with peak-count coefficients): its
  γ-nonnegativity clause is `BrandenFiberDescentGammaNonneg.isGammaNonnegWRT`; the expansion is
  proved at `π = 123` and `π = 2134` (`fiberDescentPolynomial_123_eq_sum_peakCount`,
  `fiberDescentPolynomial_2134_eq_sum_peakCount`), and γ-nonnegativity of both over every ordered
  commutative semiring.
* `SchroederTreesBlackGenFunEq` at `q = 2`, for every color type and every semiring
  (`finsum_schroederTrees_numNodes_two`).
* `SchroederRefinedFertilityFormula` at `π = 213`, for every color type and every commutative
  semiring (`schroederRefinedFertility_213`).
* `Finpartition.KrewerasBlockSizeCount` and `Finpartition.EdelmanChainCount` at `n = 3`, for all
  remaining parameters (`krewerasBlockSizeCount_three`, `edelmanChainCount_three`).
-/

universe u

namespace CitedResultsDischarged.Combinatorics

open Polynomial Finset BinaryTree

/-! ### Fiber descent polynomials -/

section FiberDescent

open List


/-- The `j`-th coefficient of `fiberDescentPolynomial R π` is the number of permutations in
`stackFiber π` with exactly `j` descents. -/
theorem coeff_fiberDescentPolynomial (R : Type*) [Semiring R] (π : List ℕ) (j : ℕ) :
    (fiberDescentPolynomial R π).coeff j =
      (((stackFiber π).filter (·.numDescents = j)).card : R) := by
  simp only [fiberDescentPolynomial, finsetSum_coeff, coeff_X_pow]
  rw [Finset.sum_boole]
  congr 2
  ext σ; simp [eq_comm]

/-- `fiberDescentPolynomial R π` is the image of `fiberDescentPolynomial ℕ π` under the cast
`ℕ → R`. -/
theorem fiberDescentPolynomial_eq_map (R : Type*) [Semiring R] (π : List ℕ) :
    fiberDescentPolynomial R π = (fiberDescentPolynomial ℕ π).map (Nat.castRingHom R) := by
  ext j
  rw [coeff_map, coeff_fiberDescentPolynomial, coeff_fiberDescentPolynomial]
  simp

private theorem perms3 : (idPermWord 3).permutations.toFinset =
    ({[1,2,3],[2,1,3],[3,2,1],[2,3,1],[3,1,2],[1,3,2]} : Finset (List ℕ)) := by
  rw [List.toFinset_eq_of_perm _ _ (List.permutations_perm_permutations' _)]
  simp only [idPermWord, range'_succ, Nat.reduceAdd, range'_zero, permutations', flatMap_cons,
    permutations'Aux, flatMap_nil, append_nil, List.map_cons, map_nil, cons_append, nil_append,
    toFinset_cons, toFinset_nil, insert_empty_eq]
  decide

private theorem perms4 : (idPermWord 4).permutations.toFinset =
    ({[1,2,3,4],[2,1,3,4],[2,3,1,4],[2,3,4,1],[1,3,2,4],[3,1,2,4],[3,2,1,4],[3,2,4,1],
      [1,3,4,2],[3,1,4,2],[3,4,1,2],[3,4,2,1],[1,2,4,3],[2,1,4,3],[2,4,1,3],[2,4,3,1],
      [1,4,2,3],[4,1,2,3],[4,2,1,3],[4,2,3,1],[1,4,3,2],[4,1,3,2],[4,3,1,2],[4,3,2,1]} :
      Finset (List ℕ)) := by
  rw [List.toFinset_eq_of_perm _ _ (List.permutations_perm_permutations' _)]
  simp [idPermWord, List.permutations', List.permutations'Aux, List.range'_succ]

private theorem stackFiber_123 :
    stackFiber [1,2,3] = {[1,2,3],[1,3,2],[2,1,3],[3,1,2],[3,2,1]} := by
  rw [stackFiber, show [1,2,3].length = 3 from rfl, perms3]
  simp only [filter_insert, stackSort.eq_2, foldr_cons, foldr_nil, Nat.one_le_ofNat,
    sup_of_le_left, Nat.reduceLeDiff, sup_of_le_right, ne_eq, OfNat.one_ne_ofNat,
    not_false_eq_true, idxOf_cons_ne, Nat.reduceEqDiff, idxOf_cons_self, Nat.succ_eq_add_one,
    zero_add, Nat.reduceAdd, take_succ_cons, take_zero, stackSort.eq_1, drop_succ_cons, drop_nil,
    append_nil, nil_append, cons_append, ↓reduceIte, drop_zero, cons.injEq, OfNat.ofNat_ne_one,
    and_true, and_self, Finset.filter_singleton]
  decide

private theorem stackFiber_2134 :
    stackFiber [2,1,3,4] = {[2,3,1,4],[2,4,1,3],[2,4,3,1],[4,2,3,1]} := by
  rw [stackFiber, show [2,1,3,4].length = 4 from rfl, perms4]
  simp [Finset.filter_insert, Finset.filter_singleton, stackSort.eq_1, stackSort.eq_2]

private theorem card_filter_numDescents (R : Type*) [Semiring R] {π : List ℕ} {S : Finset (List ℕ)}
    (hS : stackFiber π = S) (j k : ℕ) (h : (S.filter (·.numDescents = j)).card = k) :
    (fiberDescentPolynomial R π).coeff j = (k : R) := by
  rw [coeff_fiberDescentPolynomial, hS, h]

private theorem coeff_eq_zero_of_lt {R : Type*} [Semiring R] {π : List ℕ} {d : ℕ}
    (h : ∀ σ ∈ stackFiber π, σ.numDescents ≤ d) (j : ℕ) (hj : d < j) :
    (fiberDescentPolynomial R π).coeff j = 0 := by
  rw [coeff_fiberDescentPolynomial, Finset.card_eq_zero.mpr, Nat.cast_zero]
  exact Finset.filter_eq_empty_iff.mpr fun σ hσ hσj => by have := h σ hσ; omega

section Coeffs

variable (R : Type*) [Semiring R]

private theorem coeff_123_zero : (fiberDescentPolynomial R [1,2,3]).coeff 0 = 1 := by
  rw [card_filter_numDescents R stackFiber_123 0 1 (by decide), Nat.cast_one]
private theorem coeff_123_one : (fiberDescentPolynomial R [1,2,3]).coeff 1 = 3 := by
  rw [card_filter_numDescents R stackFiber_123 1 3 (by decide), Nat.cast_ofNat]
private theorem coeff_123_two : (fiberDescentPolynomial R [1,2,3]).coeff 2 = 1 := by
  rw [card_filter_numDescents R stackFiber_123 2 1 (by decide), Nat.cast_one]
private theorem numDescents_le_123 : ∀ σ ∈ stackFiber [1,2,3], σ.numDescents ≤ 2 := by
  rw [stackFiber_123]; decide

private theorem coeff_2134_zero : (fiberDescentPolynomial R [2,1,3,4]).coeff 0 = 0 := by
  rw [card_filter_numDescents R stackFiber_2134 0 0 (by decide), Nat.cast_zero]
private theorem coeff_2134_one : (fiberDescentPolynomial R [2,1,3,4]).coeff 1 = 2 := by
  rw [card_filter_numDescents R stackFiber_2134 1 2 (by decide), Nat.cast_ofNat]
private theorem coeff_2134_two : (fiberDescentPolynomial R [2,1,3,4]).coeff 2 = 2 := by
  rw [card_filter_numDescents R stackFiber_2134 2 2 (by decide), Nat.cast_ofNat]
private theorem coeff_2134_three : (fiberDescentPolynomial R [2,1,3,4]).coeff 3 = 0 := by
  rw [card_filter_numDescents R stackFiber_2134 3 0 (by decide), Nat.cast_zero]
private theorem numDescents_le_2134 : ∀ σ ∈ stackFiber [2,1,3,4], σ.numDescents ≤ 2 := by
  rw [stackFiber_2134]; decide

end Coeffs

/-- The fiber descent polynomial of `123` is symmetric with respect to degree `2`. -/
theorem isSymmetricWRT_fiberDescentPolynomial_123 (R : Type*) [Semiring R] :
    IsSymmetricWRT (3 - 1) (fiberDescentPolynomial R [1,2,3]) := by
  refine ⟨coeff_eq_zero_of_lt numDescents_le_123, fun j hj => ?_⟩
  interval_cases j <;> simp [coeff_123_zero, coeff_123_one, coeff_123_two]

/-- The fiber descent polynomial of `2134` is symmetric with respect to degree `3`. -/
theorem isSymmetricWRT_fiberDescentPolynomial_2134 (R : Type*) [Semiring R] :
    IsSymmetricWRT (4 - 1) (fiberDescentPolynomial R [2,1,3,4]) := by
  refine ⟨fun j hj => coeff_eq_zero_of_lt numDescents_le_2134 j (by omega), fun j hj => ?_⟩
  interval_cases j <;> simp [coeff_2134_zero, coeff_2134_one, coeff_2134_two, coeff_2134_three]

section Ordered

variable (R : Type*) [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]

private theorem natDegree_123 : (fiberDescentPolynomial R [1,2,3]).natDegree = 2 :=
  natDegree_eq_of_le_of_coeff_ne_zero
    (natDegree_le_iff_coeff_eq_zero.mpr fun N hN => coeff_eq_zero_of_lt numDescents_le_123 N
      (by exact_mod_cast hN))
    (by rw [coeff_123_two]; exact one_ne_zero)

private theorem natDegree_2134 : (fiberDescentPolynomial R [2,1,3,4]).natDegree = 2 :=
  natDegree_eq_of_le_of_coeff_ne_zero
    (natDegree_le_iff_coeff_eq_zero.mpr fun N hN => coeff_eq_zero_of_lt numDescents_le_2134 N
      (by exact_mod_cast hN))
    (by rw [coeff_2134_two]; exact two_ne_zero)

/-- The fiber descent polynomial of `123` is unimodal. -/
theorem isUnimodalPolynomial_fiberDescentPolynomial_123 :
    IsUnimodalPolynomial (fiberDescentPolynomial R [1,2,3]) := by
  refine ⟨1, by rw [natDegree_123]; norm_num, fun j hj => ?_, fun j hj1 hj2 => ?_⟩
  · interval_cases j
    rw [coeff_123_zero, coeff_123_one]; exact_mod_cast (show (1 : ℕ) ≤ 3 by norm_num)
  · rw [natDegree_123] at hj2
    interval_cases j
    rw [coeff_123_one, coeff_123_two]; exact_mod_cast (show (1 : ℕ) ≤ 3 by norm_num)

/-- The fiber descent polynomial of `2134` is unimodal. -/
theorem isUnimodalPolynomial_fiberDescentPolynomial_2134 :
    IsUnimodalPolynomial (fiberDescentPolynomial R [2,1,3,4]) := by
  refine ⟨1, by rw [natDegree_2134]; norm_num, fun j hj => ?_, fun j hj1 hj2 => ?_⟩
  · interval_cases j
    rw [coeff_2134_zero, coeff_2134_one]; exact zero_le_two
  · rw [natDegree_2134] at hj2
    interval_cases j
    rw [coeff_2134_one, coeff_2134_two]

end Ordered

private theorem numDescents_values_123 :
    [1,2,3].numDescents = 0 ∧ [1,3,2].numDescents = 1 ∧ [2,1,3].numDescents = 1 ∧
      [3,1,2].numDescents = 1 ∧ [3,2,1].numDescents = 2 := by decide

private theorem numDescents_values_2134 :
    [2,3,1,4].numDescents = 1 ∧ [2,4,1,3].numDescents = 1 ∧ [2,4,3,1].numDescents = 2 ∧
      [4,2,3,1].numDescents = 2 := by decide

/-- The fiber descent polynomial of `123` is `γ`-nonnegative with respect to degree `2`. -/
theorem isGammaNonnegWRT_fiberDescentPolynomial_123 (R : Type*) [CommSemiring R] [PartialOrder R]
    [IsOrderedRing R] : IsGammaNonnegWRT (3 - 1) (fiberDescentPolynomial R [1,2,3]) := by
  refine ⟨fun _ => 1, fun _ _ => zero_le_one, ?_⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := numDescents_values_123
  rw [fiberDescentPolynomial, stackFiber_123, Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, h1, h2, h3, h4, h5]
  simp [Finset.sum_range_succ]
  ring

/-- The fiber descent polynomial of `2134` is `γ`-nonnegative with respect to degree `3`. -/
theorem isGammaNonnegWRT_fiberDescentPolynomial_2134 (R : Type*) [CommSemiring R]
    [PartialOrder R] [IsOrderedRing R] :
    IsGammaNonnegWRT (4 - 1) (fiberDescentPolynomial R [2,1,3,4]) := by
  refine ⟨fun j => ((2 * j : ℕ) : R), fun j _ => Nat.cast_nonneg _, ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := numDescents_values_2134
  rw [fiberDescentPolynomial, stackFiber_2134, Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, h1, h2, h3, h4]
  simp [Finset.sum_range_succ, map_ofNat]
  ring


/-- The instance `π = 123` of `BrandenFiberDescentGammaNonneg`: the fiber
`{123, 132, 213, 312, 321}` has four permutations without a peak and one (`132`) with one peak,
and `D_123 = 1 + 3x + x² = (4/4)(1 + x)² + (1/1) x`. -/
theorem fiberDescentPolynomial_123_eq_sum_peakCount :
    fiberDescentPolynomial ℝ [1,2,3] =
      ∑ m ∈ Finset.range ((3 - 1) / 2 + 1),
        C ((((stackFiber [1,2,3]).filter fun σ => σ.peakCount = m).card : ℝ) /
          2 ^ (3 - 1 - 2 * m)) * X ^ m * (1 + X) ^ (3 - 1 - 2 * m) := by
  have hp0 : ((stackFiber [1,2,3]).filter fun σ => σ.peakCount = 0).card = 4 := by
    rw [stackFiber_123]; decide
  have hp1 : ((stackFiber [1,2,3]).filter fun σ => σ.peakCount = 1).card = 1 := by
    rw [stackFiber_123]; decide
  obtain ⟨h1, h2, h3, h4, h5⟩ := numDescents_values_123
  simp only [show (3 - 1) / 2 + 1 = 2 from rfl, Finset.sum_range_succ, Finset.sum_range_zero,
    hp0, hp1]
  rw [fiberDescentPolynomial, stackFiber_123, Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, h1, h2, h3, h4, h5]
  norm_num
  ring

/-- The instance `π = 2134` of `BrandenFiberDescentGammaNonneg`: each of the four permutations
`2314, 2413, 2431, 4231` of the fiber has exactly one peak, and
`D_2134 = 2x + 2x² = (4/2) x (1 + x)`. -/
theorem fiberDescentPolynomial_2134_eq_sum_peakCount :
    fiberDescentPolynomial ℝ [2,1,3,4] =
      ∑ m ∈ Finset.range ((4 - 1) / 2 + 1),
        C ((((stackFiber [2,1,3,4]).filter fun σ => σ.peakCount = m).card : ℝ) /
          2 ^ (4 - 1 - 2 * m)) * X ^ m * (1 + X) ^ (4 - 1 - 2 * m) := by
  have hp0 : ((stackFiber [2,1,3,4]).filter fun σ => σ.peakCount = 0).card = 0 := by
    rw [stackFiber_2134]; decide
  have hp1 : ((stackFiber [2,1,3,4]).filter fun σ => σ.peakCount = 1).card = 4 := by
    rw [stackFiber_2134]; decide
  obtain ⟨h1, h2, h3, h4⟩ := numDescents_values_2134
  simp only [show (4 - 1) / 2 + 1 = 2 from rfl, Finset.sum_range_succ, Finset.sum_range_zero,
    hp0, hp1]
  rw [fiberDescentPolynomial, stackFiber_2134, Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, h1, h2, h3, h4]
  norm_num
  rw [show (C 2 : ℝ[X]) = 2 from map_ofNat C 2]
  ring

/-! ### The forms of the Bóna and Brändén statements over other coefficient rings -/

/-- From `BonaFiberDescentSymmetric` (over `ℕ`, as its source states it): the fiber descent
polynomial with coefficients in any semiring `R` is symmetric with respect to `n - 1`, its
coefficients being the casts of those over `ℕ`. -/
theorem BonaFiberDescentSymmetric.isSymmetricWRT (h : BonaFiberDescentSymmetric)
    (R : Type*) [Semiring R] {n : ℕ} {π : List ℕ} (hπ : π ∈ permWords n) :
    IsSymmetricWRT (n - 1) (fiberDescentPolynomial R π) := by
  obtain ⟨h₁, h₂⟩ := h n π hπ
  refine ⟨fun j hj => ?_, fun j hj => ?_⟩
  · rw [fiberDescentPolynomial_eq_map, coeff_map, h₁ j hj, map_zero]
  · rw [fiberDescentPolynomial_eq_map, coeff_map, coeff_map, h₂ j hj]

/-- From `BonaFiberDescentUnimodal` (over `ℕ`, as its source states it): the fiber descent
polynomial with coefficients in a strictly ordered semiring `R` is unimodal, since the cast
`ℕ → R` is injective and monotone. -/
theorem BonaFiberDescentUnimodal.isUnimodalPolynomial (h : BonaFiberDescentUnimodal)
    (R : Type*) [Semiring R] [PartialOrder R] [IsStrictOrderedRing R] {n : ℕ} {π : List ℕ}
    (hπ : π ∈ permWords n) : IsUnimodalPolynomial (fiberDescentPolynomial R π) := by
  obtain ⟨t, ht, h₁, h₂⟩ := h n π hπ
  have hdeg : (fiberDescentPolynomial R π).natDegree = (fiberDescentPolynomial ℕ π).natDegree := by
    rw [fiberDescentPolynomial_eq_map]
    exact natDegree_map_eq_of_injective Nat.cast_injective _
  refine ⟨t, hdeg ▸ ht, fun j hj => ?_, fun j hj₁ hj₂ => ?_⟩
  · rw [fiberDescentPolynomial_eq_map, coeff_map, coeff_map]
    exact Nat.cast_le.mpr (h₁ j hj)
  · rw [fiberDescentPolynomial_eq_map, coeff_map, coeff_map]
    exact Nat.cast_le.mpr (h₂ j hj₁ (hdeg ▸ hj₂))

/-- The γ-nonnegativity clause of `BrandenFiberDescentGammaNonneg` ([Counting, Theorem 1.3],
"in particular"): the fiber descent polynomial over `ℝ` is γ-nonnegative with respect to
`n - 1`, with `γ_m = |{σ ∈ s⁻¹(π) : peak σ = m}| / 2^(n-1-2m) ≥ 0`. -/
theorem BrandenFiberDescentGammaNonneg.isGammaNonnegWRT (h : BrandenFiberDescentGammaNonneg)
    {n : ℕ} {π : List ℕ} (hπ : π ∈ permWords n) :
    IsGammaNonnegWRT (n - 1) (fiberDescentPolynomial ℝ π) :=
  ⟨fun m => (((stackFiber π).filter fun σ => σ.peakCount = m).card : ℝ) / 2 ^ (n - 1 - 2 * m),
    fun _ _ => by positivity, h n π hπ⟩

end FiberDescent

/-! ### Schröder trees counted by black vertices -/


variable {α : Type*}

private lemma eq_nil_of_numNodes_eq_zero {t : BinaryTree α} (h : t.numNodes = 0) : t = nil := by
  cases t with
  | nil => rfl
  | node a l r => simp [numNodes] at h

private lemma numNodes_eq_one {t : BinaryTree α} (h : t.numNodes = 1) :
    ∃ a, t = node a nil nil := by
  cases t with
  | nil => simp [numNodes] at h
  | node a l r =>
    simp only [numNodes, add_eq_right, Nat.add_eq_zero_iff] at h
    exact ⟨a, by rw [eq_nil_of_numNodes_eq_zero h.1, eq_nil_of_numNodes_eq_zero h.2]⟩

private lemma numNodes_eq_two {t : BinaryTree α} (h : t.numNodes = 2) :
    (∃ a b, t = node a (node b nil nil) nil) ∨ ∃ a b, t = node a nil (node b nil nil) := by
  cases t with
  | nil => simp [numNodes] at h
  | node a l r =>
    simp only [numNodes] at h
    have : (l.numNodes = 1 ∧ r.numNodes = 0) ∨ (l.numNodes = 0 ∧ r.numNodes = 1) := by omega
    rcases this with ⟨hl, hr⟩ | ⟨hl, hr⟩
    · obtain ⟨b, rfl⟩ := numNodes_eq_one hl
      exact Or.inl ⟨a, b, by rw [eq_nil_of_numNodes_eq_zero hr]⟩
    · obtain ⟨b, rfl⟩ := numNodes_eq_one hr
      exact Or.inr ⟨a, b, by rw [eq_nil_of_numNodes_eq_zero hl]⟩

private lemma numNodes_eq_three {t : BinaryTree α} (h : t.numNodes = 3) :
    (∃ a b c, t = node a (node b (node c nil nil) nil) nil) ∨
    (∃ a b c, t = node a (node b nil (node c nil nil)) nil) ∨
    (∃ a b c, t = node a (node b nil nil) (node c nil nil)) ∨
    (∃ a b c, t = node a nil (node b (node c nil nil) nil)) ∨
    (∃ a b c, t = node a nil (node b nil (node c nil nil))) := by
  cases t with
  | nil => simp [numNodes] at h
  | node a l r =>
    simp only [numNodes] at h
    have : (l.numNodes = 2 ∧ r.numNodes = 0) ∨ (l.numNodes = 1 ∧ r.numNodes = 1) ∨
        (l.numNodes = 0 ∧ r.numNodes = 2) := by omega
    rcases this with ⟨hl, hr⟩ | ⟨hl, hr⟩ | ⟨hl, hr⟩
    · rw [eq_nil_of_numNodes_eq_zero hr]
      rcases numNodes_eq_two hl with ⟨b, c, rfl⟩ | ⟨b, c, rfl⟩
      · exact Or.inl ⟨a, b, c, rfl⟩
      · exact Or.inr (Or.inl ⟨a, b, c, rfl⟩)
    · obtain ⟨b, rfl⟩ := numNodes_eq_one hl
      obtain ⟨c, rfl⟩ := numNodes_eq_one hr
      exact Or.inr (Or.inr (Or.inl ⟨a, b, c, rfl⟩))
    · rw [eq_nil_of_numNodes_eq_zero hl]
      rcases numNodes_eq_two hr with ⟨b, c, rfl⟩ | ⟨b, c, rfl⟩
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨a, b, c, rfl⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨a, b, c, rfl⟩)))

private lemma length_postorder (t : BinaryTree α) : t.postorder.length = t.numNodes := by
  induction t with
  | nil => rfl
  | node a l r ihl ihr => simp [postorder, numNodes, ihl, ihr]; omega

private lemma numNodes_map {β : Type*} (f : α → β) (t : BinaryTree α) :
    (t.map f).numNodes = t.numNodes := by
  induction t with
  | nil => rfl
  | node a l r ihl ihr => simp [BinaryTree.map, numNodes, ihl, ihr]

variable {C : Type*} [TreeColors C] [DecidableEq C]

omit [TreeColors C] [DecidableEq C] in
private lemma mem_lrf_nil {P : Set (VertexType × C)} : (nil : BinaryTree C) ∈ localRuleFamily P :=
  trivial

omit [TreeColors C] [DecidableEq C] in
private lemma mem_lrf_node {P : Set (VertexType × C)} {a : C} {l r : BinaryTree C} :
    node a l r ∈ localRuleFamily P ↔
      (vertexType l r, a) ∈ P ∧ l ∈ localRuleFamily P ∧ r ∈ localRuleFamily P :=
  Iff.rfl

omit [DecidableEq C] in
private lemma mem_rule (τ : VertexType) (c : C) :
    (τ, c) ∈ ((Set.univ ×ˢ {TreeColors.black}) ∪
      {(.leaf, TreeColors.white), (.rightUnary, TreeColors.white)} : Set (VertexType × C)) ↔
      c = TreeColors.black ∨ ((τ = .leaf ∨ τ = .rightUnary) ∧ c = TreeColors.white) := by
  simp only [Set.mem_union, Set.mem_prod, Set.mem_univ, Set.mem_singleton_iff, true_and,
    Set.mem_insert_iff, Prod.mk.injEq]
  tauto

omit [DecidableEq C] in
private lemma schroeder_two_iff (T : BinaryTree C) :
    T ∈ {T ∈ schroederTrees C | T.numNodes = 2} ↔
      T = node TreeColors.black (node TreeColors.black nil nil) nil ∨
      T = node TreeColors.black (node TreeColors.white nil nil) nil ∨
      T = node TreeColors.black nil (node TreeColors.black nil nil) ∨
      T = node TreeColors.black nil (node TreeColors.white nil nil) ∨
      T = node TreeColors.white nil (node TreeColors.black nil nil) ∨
      T = node TreeColors.white nil (node TreeColors.white nil nil) := by
  have hbw : (TreeColors.black : C) ≠ TreeColors.white := TreeColors.black_ne_white
  rcases T with _ | ⟨a, _ | ⟨b, _ | ⟨_, _, _⟩, _ | ⟨_, _, _⟩⟩,
      _ | ⟨c, _ | ⟨_, _, _⟩, _ | ⟨_, _, _⟩⟩⟩ <;>
    simp only [schroederTrees, Set.union_insert, Set.union_singleton, Set.mem_ofPred_eq,
      mem_lrf_nil, mem_lrf_node, vertexType, numNodes, OfNat.zero_ne_ofNat, OfNat.one_ne_ofNat,
      and_false, reduceCtorEq, or_self, Set.mem_insert_iff, Prod.mk.injEq, true_and, false_and,
      Set.mem_prod, Set.mem_univ, Set.mem_singleton_iff, false_or, and_self, and_true, add_zero,
      zero_add, node.injEq, Nat.reduceAdd, Nat.reduceEqDiff, Nat.add_eq_zero_iff, one_ne_zero,
      or_false, Nat.succ_ne_self, Nat.add_eq_left, iff_false, not_and, and_imp] <;>
    try omega
  all_goals tauto

/-- The Schröder trees with two nodes, counted by black nodes, have generating polynomial
`schroederFactor R 2`. -/
theorem finsum_schroederTrees_numNodes_two (R : Type*) [Semiring R] :
    ∑ᶠ T ∈ {T ∈ BinaryTree.schroederTrees C | T.numNodes = 2},
      (Polynomial.X : Polynomial R) ^ T.numBlackNodes = Polynomial.schroederFactor R 2 := by
  have hbw : (TreeColors.black : C) ≠ TreeColors.white := TreeColors.black_ne_white
  have hS : {T ∈ BinaryTree.schroederTrees C | T.numNodes = 2} =
      ↑({node TreeColors.black (node TreeColors.black nil nil) nil,
        node TreeColors.black (node TreeColors.white nil nil) nil,
        node TreeColors.black nil (node TreeColors.black nil nil),
        node TreeColors.black nil (node TreeColors.white nil nil),
        node TreeColors.white nil (node TreeColors.black nil nil),
        node TreeColors.white nil (node TreeColors.white nil nil)} : Finset (BinaryTree C)) := by
    ext T
    rw [schroeder_two_iff]
    simp
  rw [hS, finsum_mem_coe_finset, Finset.sum_insert (by simp [hbw]),
    Finset.sum_insert (by simp [hbw]), Finset.sum_insert (by simp [hbw]),
    Finset.sum_insert (by simp [hbw, hbw.symm]),
    Finset.sum_insert (by simp [hbw]), Finset.sum_singleton]
  simp only [numBlackNodes, add_zero, ↓reduceIte, zero_add, Nat.reduceAdd, hbw.symm, pow_one,
    pow_zero, schroederFactor, Nat.cast_mul, map_mul, map_natCast, sum_range_succ, range_one,
    sum_singleton, tsub_zero, Nat.choose_self, Nat.cast_one, catalan_zero, mul_one,
    Nat.add_one_sub_one, Nat.choose_one_right, Nat.cast_ofNat, catalan_one, tsub_self,
    Nat.choose_zero_right, one_mul]
  rw [catalan_two]
  have h3 : (3 : R[X]) * X = X + X + X := by
    rw [show (3 : R[X]) = 1 + 1 + 1 by norm_num]
    simp only [add_mul, one_mul]
  have h2 : ((2 : ℕ) : R[X]) * X ^ 2 = X ^ 2 + X ^ 2 := by
    rw [Nat.cast_ofNat, two_mul]
  rw [h3, h2]
  abel


/-! ### The refined fertility formula for Schröder trees at `π = 213` -/

omit [DecidableEq C] in
private lemma fiber_213_iff (𝒯 : BinaryTree (ℕ × C)) :
    (𝒯 ∈ familyDecreasingLabelings (schroederTrees C) ∧ (𝒯.map Prod.fst).postorder = [2, 1, 3]) ↔
      ∃ c₁ c₂ : C, (c₁ = TreeColors.black ∨ c₁ = TreeColors.white) ∧
        (c₂ = TreeColors.black ∨ c₂ = TreeColors.white) ∧
        𝒯 = node (3, TreeColors.black) (node (2, c₁) nil nil) (node (1, c₂) nil nil) := by
  constructor
  · rintro ⟨hmem, hpost⟩
    have h3 : 𝒯.numNodes = 3 := by
      rw [← numNodes_map Prod.fst, ← length_postorder, hpost]; rfl
    rcases numNodes_eq_three h3 with ⟨⟨a, ca⟩, ⟨b, cb⟩, ⟨c, cc⟩, rfl⟩ |
      ⟨⟨a, ca⟩, ⟨b, cb⟩, ⟨c, cc⟩, rfl⟩ | ⟨⟨a, ca⟩, ⟨b, cb⟩, ⟨c, cc⟩, rfl⟩ |
      ⟨⟨a, ca⟩, ⟨b, cb⟩, ⟨c, cc⟩, rfl⟩ | ⟨⟨a, ca⟩, ⟨b, cb⟩, ⟨c, cc⟩, rfl⟩ <;>
    simp only [BinaryTree.map, postorder, List.append_nil, List.nil_append, List.cons_append,
      List.cons.injEq, and_true, familyDecreasingLabelings, schroederTrees, Set.union_insert,
      Set.union_singleton, decreasingLabelings, decreasingColoredTrees, decreasingTrees,
      Set.mem_ofPred_eq, Set.mem_iUnion, IsDecreasing.eq_2, IsDecreasing, labels,
      disjoint_self, bot_eq_empty, union_idempotent, notMem_empty, IsEmpty.forall_iff,
      implies_true, and_self, union_empty, not_false_eq_true,
      mem_singleton, forall_eq, true_and, singleton_union, disjoint_empty_right, mem_insert,
      forall_eq_or_imp, labels.eq_2, union_insert, exists_and_left, exists_prop,
      exists_eq_right_right', numNodes, add_zero, zero_add, Nat.reduceAdd, mem_lrf_node,
      vertexType, Set.mem_insert_iff, Prod.mk.injEq, reduceCtorEq, false_and, Set.mem_prod,
      Set.mem_univ, Set.mem_singleton_iff, false_or, mem_lrf_nil, node.injEq, and_false,
      exists_false, disjoint_singleton_right, empty_union, insert_union, ↓existsAndEq,
      exists_eq_or_imp, disjoint_insert_right] at hpost hmem ⊢ <;>
    obtain ⟨rfl, rfl, rfl⟩ := hpost <;>
    (simp only [Nat.not_ofNat_lt_one, Nat.one_lt_ofNat, Nat.lt_add_one, and_self, and_true,
      false_and] at hmem; try tauto)
  · rintro ⟨c₁, c₂, h₁, h₂, rfl⟩
    simp only [familyDecreasingLabelings, schroederTrees, Set.union_insert, Set.union_singleton,
      decreasingLabelings, decreasingColoredTrees, decreasingTrees, Set.mem_ofPred_eq,
      Set.mem_iUnion, BinaryTree.map, IsDecreasing.eq_2, IsDecreasing, labels, disjoint_self,
      bot_eq_empty, union_idempotent, notMem_empty, Order.lt_two_iff, IsEmpty.forall_iff,
      implies_true, and_self, Order.lt_one_iff, union_empty, disjoint_singleton_left,
      mem_singleton, OfNat.ofNat_ne_one, not_false_eq_true, singleton_union, mem_insert,
      forall_eq_or_imp, Nat.lt_add_one, forall_eq, Nat.one_lt_ofNat, labels.eq_2, insert_union,
      true_and, exists_and_left, exists_prop, exists_eq_right_right', numNodes, add_zero,
      zero_add, Nat.reduceAdd, mem_lrf_node, vertexType, Set.mem_insert_iff, Prod.mk.injEq,
      reduceCtorEq, false_and, Set.mem_prod, Set.mem_univ, Set.mem_singleton_iff, or_true,
      false_or, mem_lrf_nil, and_true, postorder, List.append_nil, List.nil_append,
      List.cons_append]
    refine ⟨by decide, by tauto, by tauto⟩


private theorem hooks_213 : List.hooks [2, 1, 3] = {(1, 3), (2, 3)} := by decide

private theorem descentSet_213 : List.descentSet [2, 1, 3] = {1} := by decide

private theorem vhc_213 : List.validHookConfigurations [2, 1, 3] = {{(1, 3)}} := by
  ext 𝓗
  simp only [List.validHookConfigurations, hooks_213, descentSet_213, mem_filter, mem_powerset,
    mem_singleton]
  constructor
  · rintro ⟨hsub, ⟨hcard, himg⟩, -, -⟩
    rw [List.numDescents, descentSet_213, card_singleton, card_eq_one] at hcard
    obtain ⟨a, rfl⟩ := hcard
    rw [image_singleton, singleton_inj] at himg
    have ha : a ∈ ({(1, 3), (2, 3)} : Finset (ℕ × ℕ)) := hsub (mem_singleton_self a)
    simp only [mem_insert, mem_singleton] at ha
    rcases ha with rfl | rfl
    · rfl
    · simp at himg
  · rintro rfl
    refine ⟨by decide, ⟨by simp [List.numDescents, descentSet_213], by decide⟩, ?_, ?_⟩
    · simp only [mem_singleton, forall_eq]
      decide
    · simp only [mem_singleton, forall_eq, ne_eq, not_true_eq_false, IsEmpty.forall_iff]

private theorem hookComposition_213 : List.hookComposition [2, 1, 3] {(1, 3)} = fun _ => 1 := by
  funext i
  refine Fin.cases ?_ (fun t => ?_) i
  · simp only [List.hookComposition, Fin.cases_zero]
    decide
  · have h := Finset.orderEmbOfFin_mem (List.descentSet [2, 1, 3]) rfl t
    have h1 : ∀ x ∈ List.descentSet [2, 1, 3], x = 1 := by
      rw [descentSet_213]; simp
    replace h := h1 _ h
    simp only [List.hookComposition, Fin.cases_succ]
    rw [h]
    decide

private theorem validCompositions_213 : List.validCompositions [2, 1, 3] = {fun _ => 1} := by
  rw [List.validCompositions, vhc_213, image_singleton, hookComposition_213]


private lemma schroeder_one_eq :
    {T ∈ schroederTrees C | T.numNodes = 1} =
      ↑({node TreeColors.black nil nil, node TreeColors.white nil nil} :
        Finset (BinaryTree C)) := by
  ext T
  simp only [Set.mem_ofPred_eq, coe_insert, coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨hT, h1⟩
    obtain ⟨a, rfl⟩ := numNodes_eq_one h1
    simp [schroederTrees, mem_lrf_nil, mem_lrf_node] at hT
    tauto
  · rintro (rfl | rfl) <;> simp [schroederTrees, mem_lrf_nil, mem_lrf_node, numNodes]

/-- The refined fertility formula for Schröder trees at `π = 213`: the sum of
`X ^ (numBlackNodes + 1)` over decreasingly labelled Schröder trees with postorder `213` equals the
sum over valid compositions `q` of `213` of the products of the generating polynomials of Schröder
trees with `q i` nodes. -/
theorem schroederRefinedFertility_213 (R : Type*) [CommSemiring R] :
    ∑ᶠ (𝒯 : BinaryTree (ℕ × C))
        (_ : 𝒯 ∈ BinaryTree.familyDecreasingLabelings (BinaryTree.schroederTrees C) ∧
          (𝒯.map Prod.fst).postorder = [2, 1, 3]),
        (X : R[X]) ^ (𝒯.skeleton.numBlackNodes + 1) =
      ∑ q ∈ [2, 1, 3].validCompositions, ∏ i,
        ∑ᶠ T ∈ {T ∈ BinaryTree.schroederTrees C | T.numNodes = q i},
          (X : R[X]) ^ (T.numBlackNodes + 1) := by
  have hbw : (TreeColors.black : C) ≠ TreeColors.white := TreeColors.black_ne_white
  set S : Finset (BinaryTree (ℕ × C)) :=
    {node (3, TreeColors.black) (node (2, TreeColors.black) nil nil)
       (node (1, TreeColors.black) nil nil),
     node (3, TreeColors.black) (node (2, TreeColors.black) nil nil)
       (node (1, TreeColors.white) nil nil),
     node (3, TreeColors.black) (node (2, TreeColors.white) nil nil)
       (node (1, TreeColors.black) nil nil),
     node (3, TreeColors.black) (node (2, TreeColors.white) nil nil)
       (node (1, TreeColors.white) nil nil)}
    with hS
  have hP : ∀ 𝒯 : BinaryTree (ℕ × C),
      (𝒯 ∈ BinaryTree.familyDecreasingLabelings (BinaryTree.schroederTrees C) ∧
        (𝒯.map Prod.fst).postorder = [2, 1, 3]) = (𝒯 ∈ (S : Set (BinaryTree (ℕ × C)))) := by
    intro 𝒯
    apply propext
    rw [fiber_213_iff, hS]
    simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨c₁, c₂, h₁ | h₁, h₂ | h₂, rfl⟩ <;> subst h₁ h₂ <;> simp
    · rintro (rfl | rfl | rfl | rfl) <;> simp
  simp_rw [hP]
  rw [finsum_mem_coe_finset, hS, Finset.sum_insert (by simp [hbw]),
    Finset.sum_insert (by simp [hbw]), Finset.sum_insert (by simp [hbw]), Finset.sum_singleton,
    validCompositions_213, Finset.sum_singleton]
  beta_reduce
  rw [schroeder_one_eq, finsum_mem_coe_finset,
    Finset.sum_pair (by simp [hbw]), Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    List.numDescents, descentSet_213, card_singleton]
  simp [BinaryTree.map, numBlackNodes, hbw.symm]
  ring


/-! ### Kreweras' and Edelman's counts on `NC(3)` -/


@[instance_reducible] private def decNC {s : Finset ℕ} :
    DecidablePred (Finpartition.IsNoncrossing (s := s)) :=
  fun P => by unfold Finpartition.IsNoncrossing; infer_instance

@[instance_reducible] private def decLE {s : Finset ℕ} :
    DecidableRel (α := Finpartition s) (· ≤ ·) :=
  fun P Q => decidable_of_iff (∀ b ∈ P.parts, ∃ c ∈ Q.parts, b ≤ c) Iff.rfl

private lemma forall_Icc_three (P : ℕ → Prop) :
    (∀ j ∈ Icc 1 3, P j) ↔ P 1 ∧ P 2 ∧ P 3 := by
  constructor
  · intro h; exact ⟨h 1 (by decide), h 2 (by decide), h 3 (by decide)⟩
  · rintro ⟨h1, h2, h3⟩ j hj
    rw [mem_Icc] at hj
    obtain ⟨hj1, hj3⟩ := hj
    interval_cases j <;> assumption

private lemma sum_Icc_three (f : ℕ → ℕ) : ∑ j ∈ Icc 1 3, f j = f 1 + f 2 + f 3 := by
  rw [show Icc 1 3 = ({1, 2, 3} : Finset ℕ) by decide]; simp; ring

private lemma prod_Icc_three (f : ℕ → ℕ) : ∏ j ∈ Icc 1 3, f j = f 1 * f 2 * f 3 := by
  rw [show Icc 1 3 = ({1, 2, 3} : Finset ℕ) by decide]; simp; ring

section Computable

attribute [local instance] decNC decLE

set_option maxRecDepth 100000 in
private lemma edelman3_dec (k ℓ : ℕ) (h1 : 1 ≤ k) (h2 : k ≤ ℓ) (h3 : ℓ ≤ 3) :
    (univ.filter (fun p : Finpartition (Icc 1 3) × Finpartition (Icc 1 3) =>
        p.1.IsNoncrossing ∧ p.2.IsNoncrossing ∧ p.1 ≤ p.2 ∧
          p.2.blockCount = k ∧ p.1.blockCount = ℓ)).card * 3 =
      (3 : ℕ).choose (k - 1) * (3 : ℕ).choose (ℓ - k) * (3 : ℕ).choose (3 - ℓ) := by
  interval_cases ℓ <;> interval_cases k <;> decide +kernel

set_option maxRecDepth 100000 in
private lemma kreweras3_dec (a b c : ℕ) (h : a + 2 * b + 3 * c = 3) :
    (univ.filter (fun ρ : Finpartition (Icc 1 3) => ρ.IsNoncrossing ∧
        ((ρ.parts.filter (fun B => B.card = 1)).card = a ∧
        (ρ.parts.filter (fun B => B.card = 2)).card = b ∧
        (ρ.parts.filter (fun B => B.card = 3)).card = c))).card *
      ((3 - (a + b + c) + 1).factorial * (a.factorial * b.factorial * c.factorial)) =
      (3 : ℕ).factorial := by
  have : (a = 3 ∧ b = 0 ∧ c = 0) ∨ (a = 1 ∧ b = 1 ∧ c = 0) ∨ (a = 0 ∧ b = 0 ∧ c = 1) := by
    omega
  rcases this with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> decide +kernel

end Computable

/-- Edelman's count at `n = 3`: three times the number of pairs `p₁ ≤ p₂` of noncrossing
partitions of `{1, 2, 3}` with `k` and `ℓ` blocks is `C(3, k - 1) C(3, ℓ - k) C(3, 3 - ℓ)`. -/
theorem edelmanChainCount_three : ∀ (k ℓ : ℕ), 1 ≤ k → k ≤ ℓ → ℓ ≤ 3 →
    open scoped Classical in
    (univ.filter (fun p : Finpartition (Icc 1 3) × Finpartition (Icc 1 3) =>
        p.1.IsNoncrossing ∧ p.2.IsNoncrossing ∧ p.1 ≤ p.2 ∧
          p.2.blockCount = k ∧ p.1.blockCount = ℓ)).card * 3 =
      (3 : ℕ).choose (k - 1) * (3 : ℕ).choose (ℓ - k) * (3 : ℕ).choose (3 - ℓ) := by
  intro k ℓ h1 h2 h3
  convert edelman3_dec k ℓ h1 h2 h3 using 3
  ext p; simp only [Finset.mem_filter]

/-- Kreweras's count at `n = 3`: the number of noncrossing partitions of `{1, 2, 3}` with `m j`
blocks of size `j` times `(3 - ∑ m j + 1)! ∏ (m j)!` is `3!`. -/
theorem krewerasBlockSizeCount_three : ∀ (m : ℕ → ℕ), ∑ j ∈ Icc 1 3, j * m j = 3 →
    open scoped Classical in
    (univ.filter (fun ρ : Finpartition (Icc 1 3) => ρ.IsNoncrossing ∧
        ∀ j ∈ Icc 1 3, (ρ.parts.filter (fun B => B.card = j)).card = m j)).card *
      ((3 - ∑ j ∈ Icc 1 3, m j + 1).factorial * ∏ j ∈ Icc 1 3, (m j).factorial) =
      (3 : ℕ).factorial := by
  intro m hm
  rw [sum_Icc_three] at hm
  rw [sum_Icc_three, prod_Icc_three]
  convert kreweras3_dec (m 1) (m 2) (m 3) (by omega) using 4
  simp only [forall_Icc_three]


/-! The statements above restate the cited propositions verbatim at the chosen parameters. -/

example : Finpartition.EdelmanChainCount ↔
    ∀ (n k ℓ : ℕ), 1 ≤ k → k ≤ ℓ → ℓ ≤ n →
    open scoped Classical in
    (univ.filter (fun p : Finpartition (Icc 1 n) × Finpartition (Icc 1 n) =>
        p.1.IsNoncrossing ∧ p.2.IsNoncrossing ∧ p.1 ≤ p.2 ∧
          p.2.blockCount = k ∧ p.1.blockCount = ℓ)).card * n =
      n.choose (k - 1) * n.choose (ℓ - k) * n.choose (n - ℓ) := Iff.rfl

example : Finpartition.KrewerasBlockSizeCount ↔
    ∀ (n : ℕ) (m : ℕ → ℕ), ∑ j ∈ Icc 1 n, j * m j = n →
    open scoped Classical in
    (univ.filter (fun ρ : Finpartition (Icc 1 n) => ρ.IsNoncrossing ∧
        ∀ j ∈ Icc 1 n, (ρ.parts.filter (fun B => B.card = j)).card = m j)).card *
      ((n - ∑ j ∈ Icc 1 n, m j + 1).factorial * ∏ j ∈ Icc 1 n, (m j).factorial) =
      n.factorial := Iff.rfl


private lemma mem_permWords_123 : [1, 2, 3] ∈ permWords 3 :=
  ⟨⟨by decide, by decide⟩, rfl, by decide⟩

private lemma mem_permWords_213 : [2, 1, 3] ∈ permWords 3 :=
  ⟨⟨by decide, by decide⟩, rfl, by decide⟩

private lemma mem_permWords_2134 : [2, 1, 3, 4] ∈ permWords 4 :=
  ⟨⟨by decide, by decide⟩, rfl, by decide⟩

example (h : BonaFiberDescentSymmetric) :
    IsSymmetricWRT (3 - 1) (List.fiberDescentPolynomial ℕ [1,2,3]) := h 3 _ mem_permWords_123

example (h : BonaFiberDescentUnimodal) :
    IsUnimodalPolynomial (List.fiberDescentPolynomial ℕ [2,1,3,4]) :=
  h 4 _ mem_permWords_2134

example (h : BrandenFiberDescentGammaNonneg) :
    List.fiberDescentPolynomial ℝ [2,1,3,4] =
      ∑ m ∈ Finset.range ((4 - 1) / 2 + 1),
        Polynomial.C ((((List.stackFiber [2,1,3,4]).filter fun σ => σ.peakCount = m).card : ℝ) /
          2 ^ (4 - 1 - 2 * m)) * Polynomial.X ^ m * (1 + Polynomial.X) ^ (4 - 1 - 2 * m) :=
  h 4 _ mem_permWords_2134

example (h : SchroederTreesBlackGenFunEq.{u, u}) (C : Type u) [TreeColors C] [DecidableEq C]
    (R : Type u) [Semiring R] :
    ∑ᶠ T ∈ {T ∈ BinaryTree.schroederTrees C | T.numNodes = 2},
      (Polynomial.X : Polynomial R) ^ T.numBlackNodes = Polynomial.schroederFactor R 2 :=
  h C R 2

example (h : SchroederRefinedFertilityFormula.{u, u}) (C : Type u) [TreeColors C] [DecidableEq C]
    (R : Type u) [CommSemiring R] :
    ∑ᶠ (𝒯 : BinaryTree (ℕ × C))
        (_ : 𝒯 ∈ BinaryTree.familyDecreasingLabelings (BinaryTree.schroederTrees C) ∧
          (𝒯.map Prod.fst).postorder = [2, 1, 3]),
        (X : R[X]) ^ (𝒯.skeleton.numBlackNodes + 1) =
      ∑ q ∈ [2, 1, 3].validCompositions, ∏ i,
        ∑ᶠ T ∈ {T ∈ BinaryTree.schroederTrees C | T.numNodes = q i},
          (X : R[X]) ^ (T.numBlackNodes + 1) :=
  h C R 3 (by norm_num) _ mem_permWords_213

end CitedResultsDischarged.Combinatorics
