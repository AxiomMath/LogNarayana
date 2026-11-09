/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module
public import LogNarayana.Lorentzian.SimplexIntegration.Defs
public import LogNarayana.Lorentzian.Hessian.Basic
public import LogNarayana.Lorentzian.Symbol.Basic
public import LogNarayana.Lorentzian.BrandenHuh.Basic

/-!
# Integration over a simplex

For `m ≥ 2` and `θ ≥ 0`, the Dirichlet integral of a monomial over the corner simplex
`Δ_{m-1}(θ) = {s ∈ ℝ^{m-1} | s_i ≥ 0, ∑ s_i ≤ θ}` is
`∫ (∏_{i<m} s_i^{γ_i}) (θ - ∑ s_i)^{γ_m} ds = γ! / (|γ| + m - 1)! · θ^(|γ| + m - 1)`;
the case `m = 2` is the Beta integral `∫₀^θ s^a (θ - s)^b ds = a! b! / (a + b + 1)! θ^(a+b+1)`,
and the case `γ = 0` is the volume `θ^(m-1) / (m-1)!` of the simplex. Consequently the simplex
integration operator `𝔍_m : ℝ[x, u_1, …, u_m] → ℝ[x, t]`, defined on monomials by these
coefficients, evaluates at `(ξ, θ)` to the integral of `G(ξ, s, θ - ∑ s_i)` over `Δ_{m-1}(θ)`.

The operator `𝔍_m` raises the degree of homogeneous polynomials by `m - 1`. Its algebraic symbol
for the degree bound `(ν, κ)` factors as `∏_j (x_j + y_j)^{ν_j} · Ψ_{m,κ}(t, v)`, and
`Ψ_{m,κ} = κ! · E_{J_{m,κ}}` is a multiple of the normalized support polynomial of the M-convex
set `J_{m,κ}`. By the theorems of Brändén–Huh the symbol is Lorentzian, so `𝔍_m` preserves
Lorentzian polynomials, also after multiplication by a weight `u^δ`.

## Main results

* `integral_pow_mul_sub_pow`: the Beta integral with natural exponents.
* `integral_cornerSimplex_prod_pow_mul_sub_sum_pow`: the Dirichlet integral of a monomial.
* `volume_cornerSimplex`: the volume of the corner simplex.
* `Finsupp.isMConvex_jKappa`: `J_{m,κ}` is M-convex.
* `MvPolynomial.psiKappa_eq_factorial_smul_normalizedSupportPoly`: `Ψ_{m,κ} = κ! • E_{J_{m,κ}}`.
* `MvPolynomial.eval_simplexIntegral`: `(𝔍_m G)(ξ, θ)` is the integral over `Δ_{m-1}(θ)`.
* `MvPolynomial.IsHomogeneous.simplexIntegral`,
  `MvPolynomial.isHomogeneousOperator_simplexIntegral`: `𝔍_m` raises degree by `m - 1`.
* `MvPolynomial.algebraicSymbol_simplexIntegral`: the factorization of the symbol of `𝔍_m`.
* `MvPolynomial.isLorentzian_prod_add_pow_mul_rename_psiKappa`: the symbol is Lorentzian.
* `MvPolynomial.IsLorentzian.simplexIntegral`,
  `MvPolynomial.IsLorentzian.simplexIntegral_prod_X_pow_mul`: `𝔍_m` preserves the Lorentzian
  property, also after multiplication by `u^δ`.

## Implementation notes

The coordinates `s_1, …, s_{m-1}` of `Δ_{m-1}(θ)` are indexed by `Fin (m - 1)`, and integrals
over it are Bochner integrals against `MeasureTheory.volume` on `Fin (m - 1) → ℝ`, the product
Lebesgue measure; its measure lies in `ℝ≥0∞`, so the volume is stated through `ENNReal.ofReal`.
The Dirichlet integral is proved by induction on the dimension, splitting off the first
coordinate by Fubini and evaluating the outer integral by the Beta integral.

The variables follow `MvPolynomial.simplexIntegral`: `x_j = X (inl j)`, `u_i = X (inr i)` in the
domain and `t = X none`, `x_j = X (some j)` in the codomain. The symbol lives in
`MvPolynomial (Option σ ⊕ (σ ⊕ Fin m)) R` with `x_j = X (inl (some j))`, `t = X (inl none)`,
`y_j = X (inr (inl j))`, `v_i = X (inr (inr i))`, and `Ψ_{m,κ}` is moved into it by `rename`.
The algebraic statements hold over any commutative semiring that is a `ℚ`-algebra, and the
paper's hypothesis `m ≥ 1` is dropped wherever the statement holds at `m = 0` as well.

The results of Brändén–Huh are cited, not proved, so each is taken as a hypothesis at the
variable types where the proof applies it: products [BH, Corollary 2.32]
(`MvPolynomial.LorentzianMul`), nonnegative linear substitution [BH, Theorem 2.10]
(`MvPolynomial.LorentzianNonnegLinearSubstitution`), normalized support polynomials of M-convex
sets [BH, Theorem 3.10] (`MvPolynomial.NormalizedSupportPolyLorentzianOfMConvex`) and the symbol
theorem [BH, Theorem 3.2] (`MvPolynomial.BrandenHuhSymbolTheorem`). A Lorentzian polynomial is
homogeneous by definition (`MvPolynomial.IsLorentzian`), so the paper's word "homogeneous"
carries no further hypothesis.

## References

* [LogNarayana]
* [BH] P. Brändén, J. Huh, *Lorentzian polynomials*, Ann. of Math. 192 (2020).
* [DLMF], §5.12 and §5.14.
-/

open MeasureTheory Set

/-! ### Dirichlet integrals over the corner simplex -/

section Dirichlet

/-- The recursion behind the Beta integral: integrating by parts against `s ^ a`
moves one power from `θ - s` to `s`. The boundary terms vanish at both ends. -/
private lemma integral_pow_mul_sub_pow_succ (a b : ℕ) (θ : ℝ) :
    ∫ s in (0 : ℝ)..θ, s ^ a * (θ - s) ^ (b + 1) =
      (b + 1) / (a + 1) * ∫ s in (0 : ℝ)..θ, s ^ (a + 1) * (θ - s) ^ b := by
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := θ)
    (u := fun s ↦ (θ - s) ^ (b + 1)) (u' := fun s ↦ -((b + 1) * (θ - s) ^ b))
    (v := fun s ↦ s ^ (a + 1) / (a + 1)) (v' := fun s ↦ s ^ a)
    (fun x _ ↦ by
      convert (hasDerivAt_pow (b + 1) (θ - x)).comp x ((hasDerivAt_id x).const_sub θ) using 1
      · rfl
      · simp)
    (fun x _ ↦ by
      convert (hasDerivAt_pow (a + 1) x).div_const ((a : ℝ) + 1) using 1
      field_simp; push_cast; ring)
    (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop)
  simp only [sub_self, zero_pow (Nat.succ_ne_zero _), zero_mul, zero_div, mul_zero, sub_zero,
    zero_sub] at hibp
  rw [← intervalIntegral.integral_const_mul]
  simp_rw [mul_comm (_ ^ a)] at hibp ⊢
  rw [hibp, ← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr fun s _ ↦ ?_
  field_simp

/-- **Beta integral with natural exponents.** For `a b : ℕ` and every real `θ`,
`∫₀^θ s^a (θ - s)^b ds = a! b! / (a + b + 1)! · θ^(a + b + 1)`. -/
@[lognarayana "lem_beta_integral"]
public theorem integral_pow_mul_sub_pow (a b : ℕ) {θ : ℝ} :
    ∫ s in (0 : ℝ)..θ, s ^ a * (θ - s) ^ b =
      (a.factorial * b.factorial : ℝ) / (a + b + 1).factorial * θ ^ (a + b + 1) := by
  induction b generalizing a with
  | zero =>
    simp [integral_pow, Nat.factorial_succ]
    field_simp
  | succ b ih =>
    rw [integral_pow_mul_sub_pow_succ, ih, show a + 1 + b + 1 = a + (b + 1) + 1 by ring,
      Nat.factorial_succ a, Nat.factorial_succ b]
    push_cast
    field_simp

private lemma isCompact_cornerSimplex (n : ℕ) (θ : ℝ) :
    IsCompact (cornerSimplex (Fin n) θ) := by
  refine (isCompact_univ_pi fun _ => isCompact_Icc (a := (0 : ℝ)) (b := θ)).of_isClosed_subset
    ?_ fun s ⟨h0, hs⟩ i _ => ⟨h0 i, (Finset.single_le_sum (fun j _ => h0 j)
      (Finset.mem_univ i)).trans hs⟩
  simp only [cornerSimplex, ofPred_and, ofPred_forall]
  exact (isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)).inter
    (isClosed_le (by fun_prop) continuous_const)

private lemma cornerSimplex_eq_empty {n : ℕ} {θ : ℝ} (hθ : θ < 0) :
    cornerSimplex (Fin n) θ = ∅ :=
  eq_empty_of_forall_notMem fun _ ⟨h0, hs⟩ =>
    (hs.trans_lt hθ).not_ge (Finset.sum_nonneg fun i _ => h0 i)

private lemma cons_mem_cornerSimplex {n : ℕ} {θ x : ℝ} {s : Fin n → ℝ} :
    (Fin.cons x s : Fin (n + 1) → ℝ) ∈ cornerSimplex (Fin (n + 1)) θ ↔
      0 ≤ x ∧ s ∈ cornerSimplex (Fin n) (θ - x) := by
  simp only [cornerSimplex, mem_ofPred_eq, Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ,
    Fin.sum_univ_succ, le_sub_iff_add_le']
  tauto

/-- **Fubini over the corner simplex.** Splitting off the first coordinate `x`, an integral
over `cornerSimplex (Fin (n + 1)) θ` is the integral over `x ∈ [0, θ]` of the integral over
the slice `cornerSimplex (Fin n) (θ - x)`. -/
private lemma integral_cornerSimplex_succ {n : ℕ} {θ : ℝ} (hθ : 0 ≤ θ)
    {f : (Fin (n + 1) → ℝ) → ℝ} (hf : Continuous f) :
    ∫ s in cornerSimplex (Fin (n + 1)) θ, f s =
      ∫ x in 0..θ, ∫ s in cornerSimplex (Fin n) (θ - x), f (Fin.cons x s) := by
  set K := cornerSimplex (Fin (n + 1)) θ
  have hKm : MeasurableSet K := (isCompact_cornerSimplex _ _).isClosed.measurableSet
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
  have hmp : MeasurePreserving e volume (volume.prod volume) :=
    measurePreserving_piFinSuccAbove (fun _ => volume) 0
  have he : ∀ p : ℝ × (Fin n → ℝ), e.symm p = Fin.cons p.1 p.2 := fun p => by
    simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
  have hint : Integrable (fun p => K.indicator f (e.symm p)) (volume.prod volume) :=
    (hmp.symm.integrable_comp_emb e.symm.measurableEmbedding).2 <|
      (integrable_indicator_iff hKm).2
        (hf.continuousOn.integrableOn_compact (isCompact_cornerSimplex _ _))
  have hslice : ∀ x, ∫ s, K.indicator f (Fin.cons x s) = (Icc 0 θ).indicator
      (fun x => ∫ s in cornerSimplex (Fin n) (θ - x), f (Fin.cons x s)) x := fun x => by
    by_cases hx0 : 0 ≤ x
    · by_cases hxθ : x ≤ θ
      · rw [indicator_of_mem (show x ∈ Icc 0 θ from ⟨hx0, hxθ⟩),
          ← integral_indicator (isCompact_cornerSimplex _ _).isClosed.measurableSet]
        congr 1 with s
        classical
        simp only [indicator_apply, K, cons_mem_cornerSimplex, hx0, true_and]
      · rw [indicator_of_notMem fun h => hxθ h.2]
        simp [indicator, K, cons_mem_cornerSimplex,
          cornerSimplex_eq_empty (by linarith : θ - x < 0)]
    · rw [indicator_of_notMem fun h => hx0 h.1]
      simp [indicator, K, cons_mem_cornerSimplex, hx0]
  rw [← integral_indicator hKm, ← hmp.symm.integral_comp' (K.indicator f), integral_prod _ hint]
  simp only [he, hslice]
  rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hθ]

/-- The Dirichlet integral over `cornerSimplex (Fin n) θ`, for every dimension `n`, by
induction on `n`: Fubini, the inductive hypothesis on each slice, and the Beta integral. -/
private lemma integral_cornerSimplex_fin_prod_pow_mul_sub_sum_pow (n : ℕ)
    (γ : Fin (n + 1) → ℕ) {θ : ℝ} (hθ : 0 ≤ θ) :
    ∫ s in cornerSimplex (Fin n) θ,
        (∏ i : Fin n, s i ^ γ (Fin.castSucc i)) * (θ - ∑ i, s i) ^ γ (Fin.last n) =
      ((∏ i, (γ i).factorial : ℕ) : ℝ) / ((∑ i, γ i) + n).factorial *
        θ ^ ((∑ i, γ i) + n) := by
  induction n generalizing θ with
  | zero =>
    have hK : cornerSimplex (Fin 0) θ = univ := by
      ext s; simp [cornerSimplex, hθ]
    simp [hK, Measure.real, volume_pi, Nat.factorial_ne_zero]
  | succ n ih =>
    rw [integral_cornerSimplex_succ hθ (by fun_prop)]
    set b := (∑ i, Fin.tail γ i) + n
    have hslice : ∀ x ∈ uIcc 0 θ,
        ∫ s in cornerSimplex (Fin n) (θ - x), (∏ i, (Fin.cons x s : Fin (n + 1) → ℝ) i ^
            γ (Fin.castSucc i)) * (θ - ∑ i, (Fin.cons x s : Fin (n + 1) → ℝ) i) ^
              γ (Fin.last (n + 1)) =
          ((∏ i, (Fin.tail γ i).factorial : ℕ) : ℝ) / b.factorial *
            (x ^ γ 0 * (θ - x) ^ b) := fun x hx => by
      have hcons : ∀ s : Fin n → ℝ, (∏ i, (Fin.cons x s : Fin (n + 1) → ℝ) i ^
            γ (Fin.castSucc i)) * (θ - ∑ i, (Fin.cons x s : Fin (n + 1) → ℝ) i) ^
              γ (Fin.last (n + 1)) = x ^ γ 0 * ((∏ i, s i ^ Fin.tail γ (Fin.castSucc i)) *
                ((θ - x) - ∑ i, s i) ^ Fin.tail γ (Fin.last n)) := fun s => by
        simp only [Fin.prod_univ_succ, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
          Fin.castSucc_zero, Fin.tail, Fin.succ_castSucc, Fin.succ_last, sub_sub]
        ring
      rw [uIcc_of_le hθ] at hx
      simp only [hcons]
      rw [integral_const_mul, ih (Fin.tail γ) (sub_nonneg.2 hx.2)]
      ring
    rw [intervalIntegral.integral_congr hslice, intervalIntegral.integral_const_mul,
      integral_pow_mul_sub_pow _ _, Fin.prod_univ_succ (fun i => (γ i).factorial),
      show (∑ i, γ i) + (n + 1) = γ 0 + b + 1 by
        rw [Fin.sum_univ_succ]; simp only [b, Fin.tail]; ring]
    simp only [Fin.tail]
    push_cast
    have := Nat.factorial_ne_zero b
    have := Nat.factorial_ne_zero (γ 0 + b + 1)
    field_simp

/-- **Dirichlet integral of a monomial over the corner simplex.** For `2 ≤ m`, `γ : Fin m → ℕ`
and `0 ≤ θ`, `∫_{Δ_{m-1}(θ)} (∏_{i<m-1} s_i^{γ_i}) (θ - ∑ s_i)^{γ_{m-1}} ds` equals
`γ! / (|γ| + m - 1)! · θ^(|γ|+m-1)`. -/
@[lognarayana "lem_dirichlet_monomial_integral"]
public theorem integral_cornerSimplex_prod_pow_mul_sub_sum_pow {m : ℕ} (hm : 2 ≤ m)
    (γ : Fin m → ℕ) {θ : ℝ} (hθ : 0 ≤ θ) :
    ∫ s in cornerSimplex (Fin (m - 1)) θ,
        (∏ i : Fin (m - 1), s i ^ γ (Fin.castLE (Nat.sub_le m 1) i)) *
          (θ - ∑ i, s i) ^ γ ⟨m - 1, by omega⟩ =
      ((∏ i, (γ i).factorial : ℕ) : ℝ) / ((∑ i, γ i) + m - 1).factorial *
        θ ^ ((∑ i, γ i) + m - 1) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  exact integral_cornerSimplex_fin_prod_pow_mul_sub_sum_pow n γ hθ

/-- **Volume of the corner simplex.** For `2 ≤ m` and `0 ≤ θ`, the Lebesgue measure of
`Δ_{m-1}(θ) = {s : Fin (m - 1) → ℝ | (∀ i, 0 ≤ s i) ∧ ∑ i, s i ≤ θ}` is `θ^(m-1) / (m-1)!`:
it is the case `γ = 0` of `integral_cornerSimplex_prod_pow_mul_sub_sum_pow`. -/
@[lognarayana "lem_simplex_volume"]
public theorem volume_cornerSimplex {m : ℕ} (hm : 2 ≤ m) {θ : ℝ} (hθ : 0 ≤ θ) :
    MeasureTheory.volume (cornerSimplex (Fin (m - 1)) θ) =
      ENNReal.ofReal (θ ^ (m - 1) / (m - 1).factorial) := by
  have h := integral_cornerSimplex_prod_pow_mul_sub_sum_pow hm (fun _ => 0) hθ
  simp only [pow_zero, Finset.prod_const_one, mul_one, Nat.factorial_zero,
    Finset.sum_const_zero, zero_add, Nat.cast_one, setIntegral_const, smul_eq_mul] at h
  rw [← ENNReal.ofReal_toReal (isCompact_cornerSimplex _ θ).measure_lt_top.ne,
    ← measureReal_def, h, one_div_mul_eq_div]

end Dirichlet

/-! ### The exponent set `J_{m,κ}` -/

namespace Finsupp

private lemma degree_le_degree_add_sub_one (m : ℕ) (κ : Fin m →₀ ℕ) :
    κ.degree ≤ κ.degree + m - 1 := by
  cases m with
  | zero => simp [Subsingleton.elim κ 0]
  | succ n => omega

/-- Membership in `J_{m,κ}`: bounded `v`-coordinates and coordinate sum `|κ| + m - 1`. -/
private lemma mem_jKappa_iff (m : ℕ) (κ : Fin m →₀ ℕ) (p : Option (Fin m) →₀ ℕ) :
    p ∈ jKappa m κ ↔ (∀ k, p (Option.some k) ≤ κ k) ∧ p.degree = κ.degree + m - 1 := by
  have hD := degree_le_degree_add_sub_one m κ
  constructor
  · intro hp
    obtain ⟨β, hβ, rfl⟩ := Finset.mem_image.mp hp
    have hβκ : β ≤ κ := Finset.mem_Iic.mp hβ
    have hdeg : β.degree ≤ κ.degree := degree_mono hβκ
    refine ⟨fun k => ?_, ?_⟩
    · simp [mapDomain_apply (Option.some_injective _), hβκ k]
    · rw [map_add, degree_single, degree_mapDomain]
      omega
  · rintro ⟨h1, h2⟩
    set β : Fin m →₀ ℕ := equivFunOnFinite.symm fun k => p (Option.some k)
    have hβdeg : β.degree = ∑ k, p (Option.some k) := by
      rw [degree_eq_sum]
      rfl
    refine Finset.mem_image.mpr ⟨β, Finset.mem_Iic.mpr h1, ?_⟩
    ext (_ | k)
    · rw [degree_eq_sum, Fintype.sum_option] at h2
      simp [mapDomain_of_notMem_range, hβdeg]
      omega
    · simp [mapDomain_apply (Option.some_injective _), β]

/-- One exchange step stays in `J_{m,κ}`. -/
private lemma exchange_mem_jKappa (m : ℕ) (κ : Fin m →₀ ℕ) {p : Option (Fin m) →₀ ℕ}
    (hp : p ∈ jKappa m κ) {i j : Option (Fin m)} (hij : i ≠ j) (hi : 1 ≤ p i)
    (hj : ∀ k, j = Option.some k → p j + 1 ≤ κ k) :
    p - single i 1 + single j 1 ∈ jKappa m κ := by
  rw [mem_jKappa_iff] at hp ⊢
  obtain ⟨h1, h2⟩ := hp
  refine ⟨fun k => ?_, ?_⟩
  · have := h1 k
    by_cases hjk : j = Option.some k
    · subst hjk
      have := hj k rfl
      simp [hij]
      omega
    · simp only [coe_add, coe_tsub, Pi.add_apply, Pi.sub_apply, single_apply]
      rw [if_neg hjk]
      omega
  · have := congrArg degree (tsub_add_cancel_of_le (single_le_iff.mpr hi))
    rw [map_add, degree_single] at this
    rw [map_add, degree_single]
    omega

/-- Two multi-indices of equal total degree: if one exceeds the other in some coordinate, it
falls short of it in another. -/
private lemma exists_lt_of_degree_eq {ι : Type*} [Finite ι] {α β : ι →₀ ℕ}
    (h : α.degree = β.degree) {i : ι} (hi : β i < α i) : ∃ j, α j < β j := by
  have := Fintype.ofFinite ι
  by_contra! hle
  have := Finset.sum_lt_sum (fun j _ => hle j) ⟨i, Finset.mem_univ _, hi⟩
  simp only [← degree_eq_sum] at this
  omega

/-- For every `m` and `κ ∈ ℕ^m`, the exponent set `J_{m,κ}` is M-convex: its points have
coordinate sum `|κ| + m - 1` and bounded `v`-coordinates, and an exchange step keeps both. -/
@[lognarayana "lem_j_kappa_mconvex"]
public theorem isMConvex_jKappa (m : ℕ) (κ : Fin m →₀ ℕ) :
    Set.IsMConvex (↑(jKappa m κ) : Set (Option (Fin m) →₀ ℕ)) := by
  refine ⟨Finset.finite_toSet _, ⟨_, Finset.mem_image_of_mem _ (Finset.mem_Iic.mpr zero_le)⟩,
    ⟨κ.degree + m - 1, fun α hα => ((mem_jKappa_iff m κ α).mp hα).2⟩, ?_⟩
  intro α hα β hβ i hi
  have hα' := (mem_jKappa_iff m κ α).mp hα
  have hβ' := (mem_jKappa_iff m κ β).mp hβ
  obtain ⟨j, hj⟩ := exists_lt_of_degree_eq (hα'.2.trans hβ'.2.symm) hi
  have hij : i ≠ j := by
    rintro rfl
    omega
  refine ⟨j, hj, exchange_mem_jKappa m κ hα hij (by omega) ?_,
    exchange_mem_jKappa m κ hβ hij.symm (by omega) ?_⟩
  · rintro k rfl
    have := hβ'.1 k
    omega
  · rintro k rfl
    have := hα'.1 k
    omega

end Finsupp

namespace MvPolynomial

/-! ### The symbol factor `Ψ_{m,κ}` -/

section PsiKappa

open Finsupp

/-- Over a finite index type, the multi-index factorial is the product over all indices. -/
private lemma factorial_eq_prod {ι : Type*} [Fintype ι] (α : ι →₀ ℕ) :
    α.factorial = ∏ i, (α i).factorial :=
  Finsupp.prod_fintype _ _ fun _ => rfl

/-- `(κ choose γ) · γ! · (κ - γ)! = κ!` for `γ ≤ κ`. -/
private lemma choose_mul_factorial_mul_factorial {ι : Type*} [Finite ι] {κ γ : ι →₀ ℕ}
    (h : γ ≤ κ) : κ.choose γ * γ.factorial * (κ - γ).factorial = κ.factorial := by
  have := Fintype.ofFinite ι
  simp only [factorial_eq_prod, Finsupp.choose,
    Finsupp.prod_fintype _ _ fun _ => Nat.choose_zero_right _, ← Finset.prod_mul_distrib,
    Finsupp.coe_tsub, Pi.sub_apply]
  exact Finset.prod_congr rfl fun i _ => Nat.choose_mul_factorial_mul_factorial (h i)

/-- The factorial of the point `(n, β)` of `ℕ^{1+m}` is `n! · β!`. -/
private lemma factorial_single_none_add_mapDomain {m : ℕ} (n : ℕ) (β : Fin m →₀ ℕ) :
    (single none n + β.mapDomain Option.some).factorial = n.factorial * β.factorial := by
  simp [factorial_eq_prod β, factorial_eq_prod (single none n + _), Fintype.prod_option,
    mapDomain_apply (Option.some_injective _), mapDomain_of_notMem_range]

/-- The coefficient of `Ψ_κ` at `γ` is `κ!` times the normalized coefficient at the point
`(N, κ - γ)`. -/
private lemma choose_mul_factorial_div {ι : Type*} [Finite ι] {κ γ : ι →₀ ℕ} (h : γ ≤ κ)
    (N : ℕ) : (κ.choose γ * γ.factorial / N.factorial : ℚ) =
      κ.factorial * (1 / (N.factorial * (κ - γ).factorial)) := by
  have := (κ - γ).factorial_pos
  rw [← choose_mul_factorial_mul_factorial h]
  push_cast
  field_simp

/-- The symbol factor is `κ!` times the normalized support polynomial of its exponent set:
`Ψ_{m,κ}(t, v) = κ! · E_{J_{m,κ}}(t, v)`. The bijection of the two sums is `γ ↦ κ - γ`. -/
@[lognarayana "lem_psi_normalized_support"]
public theorem psiKappa_eq_factorial_smul_normalizedSupportPoly (R : Type*) [CommSemiring R]
    [Algebra ℚ R] (m : ℕ) (κ : Fin m →₀ ℕ) :
    psiKappa R m κ = κ.factorial • normalizedSupportPoly R (Finsupp.jKappa m κ) := by
  unfold psiKappa normalizedSupportPoly Finsupp.jKappa
  rw [Finset.sum_image fun β _ β' _ h => Finsupp.ext fun i => by
      simpa [mapDomain_apply (Option.some_injective _)] using DFunLike.congr_fun h (some i),
    Finset.smul_sum]
  refine Finset.sum_nbij' (κ - ·) (κ - ·) (by simp) (by simp)
    (fun γ hγ => tsub_tsub_cancel_of_le (Finset.mem_Iic.1 hγ))
    (fun β hβ => tsub_tsub_cancel_of_le (Finset.mem_Iic.1 hβ)) fun γ hγ => ?_
  rw [Finset.mem_Iic] at hγ
  have : κ.degree + m - 1 - (κ - γ).degree = γ.degree + m - 1 := by
    have := degree_mono hγ
    rw [← map_tsub_of_le degree κ γ hγ]
    omega
  rw [this, smul_monomial, factorial_single_none_add_mapDomain, ← map_nsmul, nsmul_eq_mul,
    choose_mul_factorial_div hγ]
  push_cast
  rfl

end PsiKappa

/-! ### The simplex integration operator on monomials -/

section Monomial

variable {σ R : Type*} [CommSemiring R] [Algebra ℚ R] {m : ℕ}

/-- `𝔍_m` on the monomial `c x^α u^γ`, with `(α, γ)` the two parts of `β`. -/
private lemma simplexIntegral_monomial (β : σ ⊕ Fin m →₀ ℕ) (c : R) :
    simplexIntegral σ R m (monomial β c) =
      c • monomial (Finsupp.single none ((Finsupp.sumFinsuppEquivProdFinsupp β).2.degree + m - 1)
          + (Finsupp.sumFinsuppEquivProdFinsupp β).1.mapDomain some)
        (algebraMap ℚ R (((Finsupp.sumFinsuppEquivProdFinsupp β).2.factorial : ℚ) /
          (((Finsupp.sumFinsuppEquivProdFinsupp β).2.degree + m - 1).factorial : ℚ))) := by
  rw [show monomial β c = c • basisMonomials _ R β by simp [coe_basisMonomials, smul_monomial],
    map_smul, simplexIntegral, Module.Basis.constr_basis]

/-- `𝔍_m` on the monomial `c x^α u^γ`, written through `Finsupp.sumElim α γ`. -/
private lemma simplexIntegral_monomial_sumElim (α : σ →₀ ℕ) (γ : Fin m →₀ ℕ) (c : R) :
    simplexIntegral σ R m (monomial (Finsupp.sumElim α γ) c) =
      c • monomial (Finsupp.single none (γ.degree + m - 1) + α.mapDomain some)
        (algebraMap ℚ R ((γ.factorial : ℚ) / ((γ.degree + m - 1).factorial : ℚ))) := by
  rw [simplexIntegral_monomial]
  simp

end Monomial

/-! ### Evaluation as an integral over the simplex -/

section Eval

/-- The point `(s_1, …, s_{m-1}, θ - ∑ s_i)` of `ℝ^m` lying over `s ∈ ℝ^{m-1}`. -/
private noncomputable def simplexPoint {m : ℕ} (θ : ℝ) (s : Fin (m - 1) → ℝ) : Fin m → ℝ :=
  fun i => if h : (i : ℕ) < m - 1 then s ⟨i, h⟩ else θ - ∑ j, s j

private lemma simplexPoint_castLE {m : ℕ} (θ : ℝ) (s : Fin (m - 1) → ℝ) (i : Fin (m - 1)) :
    simplexPoint θ s (Fin.castLE (Nat.sub_le m 1) i) = s i := by
  simp [simplexPoint]

private lemma simplexPoint_last {m : ℕ} (hm : 1 ≤ m) (θ : ℝ) (s : Fin (m - 1) → ℝ) :
    simplexPoint θ s ⟨m - 1, by omega⟩ = θ - ∑ j, s j := by
  simp [simplexPoint]

private lemma continuous_simplexPoint {m : ℕ} (θ : ℝ) :
    Continuous (simplexPoint (m := m) θ) :=
  continuous_pi fun i => by
    unfold simplexPoint
    split_ifs
    exacts [continuous_apply _, by fun_prop]

/-- Every polynomial integrand is integrable over the simplex. -/
private lemma integrableOn_eval_simplexPoint {σ : Type*} {m : ℕ}
    (P : MvPolynomial (σ ⊕ Fin m) ℝ) (ξ : σ → ℝ) (θ : ℝ) :
    IntegrableOn (fun s => eval (Sum.elim ξ (simplexPoint θ s)) P)
      (cornerSimplex (Fin (m - 1)) θ) :=
  ((continuous_eval P).comp (continuous_pi fun o => by
    rcases o with j | i
    exacts [continuous_const, (continuous_apply i).comp (continuous_simplexPoint θ)]
    )).continuousOn.integrableOn_compact (isCompact_cornerSimplex _ _)

private lemma prod_fin_eq_prod_castLE_mul {m : ℕ} (hm : 1 ≤ m) (f : Fin m → ℝ) :
    ∏ i, f i = (∏ i : Fin (m - 1), f (Fin.castLE (Nat.sub_le m 1) i)) * f ⟨m - 1, by omega⟩ := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  rw [Fin.prod_univ_castSucc]
  rfl

private lemma sumElim_eq_add {σ τ : Type*} (α : σ →₀ ℕ) (γ : τ →₀ ℕ) :
    Finsupp.sumElim α γ = α.mapDomain Sum.inl + γ.mapDomain Sum.inr := by
  ext (j | i)
  · simp [Finsupp.mapDomain_apply Sum.inl_injective,
      Finsupp.mapDomain_of_notMem_range _ _ (by simp : Sum.inl j ∉ Set.range (Sum.inr : τ → σ ⊕ τ))]
  · simp [Finsupp.mapDomain_apply Sum.inr_injective,
      Finsupp.mapDomain_of_notMem_range _ _ (by simp : Sum.inr i ∉ Set.range (Sum.inl : σ → σ ⊕ τ))]

/-- Evaluating `a x^α u^γ` at `(ξ, w)`. -/
private lemma eval_monomial_sumElim {σ : Type*} {m : ℕ} (α : σ →₀ ℕ) (γ : Fin m →₀ ℕ) (a : ℝ)
    (ξ : σ → ℝ) (w : Fin m → ℝ) :
    eval (Sum.elim ξ w) (monomial (Finsupp.sumElim α γ) a) =
      a * (α.prod fun j k => ξ j ^ k) * ∏ i, w i ^ γ i := by
  rw [sumElim_eq_add, eval_monomial,
    Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _),
    Finsupp.prod_mapDomain_index_inj Sum.inl_injective,
    Finsupp.prod_mapDomain_index_inj Sum.inr_injective]
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [Finsupp.prod_fintype _ _ (fun i => pow_zero (w i)), mul_assoc]

/-- The evaluation formula on a monomial: both sides are
`a · γ! / (|γ| + m - 1)! · ξ^α θ^(|γ| + m - 1)`, the right side by
`integral_cornerSimplex_prod_pow_mul_sub_sum_pow`. -/
private lemma eval_simplexIntegral_monomial {σ : Type*} {m : ℕ} (hm : 2 ≤ m) (α : σ →₀ ℕ)
    (γ : Fin m →₀ ℕ) (a : ℝ) (ξ : σ → ℝ) {θ : ℝ} (hθ : 0 ≤ θ) :
    eval (fun o : Option σ => o.elim θ ξ)
        (simplexIntegral σ ℝ m (monomial (Finsupp.sumElim α γ) a)) =
      ∫ s in cornerSimplex (Fin (m - 1)) θ, eval (Sum.elim ξ (simplexPoint θ s))
        (monomial (Finsupp.sumElim α γ) a) := by
  simp_rw [eval_monomial_sumElim, prod_fin_eq_prod_castLE_mul (by omega : 1 ≤ m),
    simplexPoint_castLE, simplexPoint_last (by omega : 1 ≤ m)]
  rw [integral_const_mul, integral_cornerSimplex_prod_pow_mul_sub_sum_pow hm _ hθ,
    simplexIntegral_monomial_sumElim, smul_monomial, eval_monomial,
    Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _),
    Finsupp.prod_single_index (by simp),
    Finsupp.prod_mapDomain_index_inj (Option.some_injective _),
    Finsupp.factorial, Finsupp.prod_fintype _ _ (fun _ => rfl), Finsupp.degree_eq_sum]
  simp only [Option.elim_none, Option.elim_some, smul_eq_mul, map_div₀, map_natCast,
    Nat.cast_prod, map_prod]
  ring

/-- **The simplex integration operator is the simplex integral.** For `2 ≤ m`,
`G ∈ ℝ[x, u_1, …, u_m]`, `ξ : σ → ℝ` and `0 ≤ θ`,
`(𝔍_m G)(ξ, θ) = ∫_{Δ_{m-1}(θ)} G(ξ, s_1, …, s_{m-1}, θ - ∑ s_i) ds`. Both sides are linear
in `G` (the integrands are continuous on the compact simplex), and agree on monomials. -/
@[lognarayana "lem_simplex_integral_eval"]
public theorem eval_simplexIntegral {σ : Type*} {m : ℕ} (hm : 2 ≤ m)
    (G : MvPolynomial (σ ⊕ Fin m) ℝ) (ξ : σ → ℝ) {θ : ℝ} (hθ : 0 ≤ θ) :
    eval (fun o : Option σ => o.elim θ ξ) (simplexIntegral σ ℝ m G) =
      ∫ s in cornerSimplex (Fin (m - 1)) θ,
        eval (Sum.elim ξ fun i : Fin m =>
          if h : (i : ℕ) < m - 1 then s ⟨i, h⟩ else θ - ∑ j, s j) G := by
  change _ = ∫ s in cornerSimplex (Fin (m - 1)) θ, eval (Sum.elim ξ (simplexPoint θ s)) G
  induction G using MvPolynomial.induction_on' with
  | monomial β a =>
    rw [← Equiv.symm_apply_apply Finsupp.sumFinsuppEquivProdFinsupp β,
      Finsupp.sumFinsuppEquivProdFinsupp_symm_apply]
    exact eval_simplexIntegral_monomial hm _ _ a ξ hθ
  | add p q hp hq =>
    simp only [map_add, hp, hq]
    exact (integral_add (integrableOn_eval_simplexPoint p ξ θ)
      (integrableOn_eval_simplexPoint q ξ θ)).symm

end Eval

/-! ### Homogeneity -/

section Homogeneous

variable {σ R : Type*} [CommSemiring R] [Algebra ℚ R] {m : ℕ}

/-- The degree of a monomial exponent on `σ ⊕ τ` is the sum of the degrees of its two parts. -/
private lemma degree_eq_add_sumFinsuppEquivProdFinsupp {τ : Type*} (β : σ ⊕ τ →₀ ℕ) :
    β.degree = (Finsupp.sumFinsuppEquivProdFinsupp β).1.degree +
      (Finsupp.sumFinsuppEquivProdFinsupp β).2.degree := by
  have hβ : β = (Finsupp.sumFinsuppEquivProdFinsupp β).1.mapDomain Sum.inl +
      (Finsupp.sumFinsuppEquivProdFinsupp β).2.mapDomain Sum.inr := by
    ext (i | i) <;>
      simp [Finsupp.mapDomain_apply Sum.inl_injective, Finsupp.mapDomain_apply Sum.inr_injective,
        Finsupp.mapDomain_of_notMem_range]
  conv_lhs => rw [hβ]
  rw [map_add, Finsupp.degree_mapDomain, Finsupp.degree_mapDomain]

/-- Simplex integration sends the monomial `c x^α u^γ` (with `β = (α, γ)`) to a polynomial
homogeneous of degree `|β| + m - 1`. -/
private lemma isHomogeneous_simplexIntegral_monomial (hm : 1 ≤ m) (β : σ ⊕ Fin m →₀ ℕ) (c : R) :
    (simplexIntegral σ R m (monomial β c)).IsHomogeneous (β.degree + m - 1) := by
  rw [simplexIntegral_monomial]
  refine (mem_homogeneousSubmodule _ _).1 (Submodule.smul_mem _ _ (isHomogeneous_monomial _ ?_))
  rw [map_add, Finsupp.degree_single, Finsupp.degree_mapDomain,
    degree_eq_add_sumFinsuppEquivProdFinsupp β]
  omega

/-- For `m ≥ 1`, the simplex integration operator `𝔍_m` sends a polynomial homogeneous of
degree `d` to one homogeneous of degree `d + m - 1`: it sends `x^α u^γ` to a multiple of
`x^α t^(|γ| + m - 1)`. -/
@[lognarayana "thm_simplex_integration_degree"]
public theorem IsHomogeneous.simplexIntegral (hm : 1 ≤ m) {d : ℕ}
    {G : MvPolynomial (σ ⊕ Fin m) R} (hG : G.IsHomogeneous d) :
    (MvPolynomial.simplexIntegral σ R m G).IsHomogeneous (d + m - 1) := by
  rw [G.as_sum, map_sum]
  refine IsHomogeneous.sum _ _ _ fun β hβ => ?_
  have hd : β.degree = d := by
    rw [Finsupp.degree_eq_weight_one]
    exact hG (mem_support_iff.1 hβ)
  exact hd ▸ isHomogeneous_simplexIntegral_monomial hm β _

/-- For `m ≥ 1`, the simplex integration operator `𝔍_m`, restricted to the polynomials in
`(x, u)` of degree at most `κ` in each variable, is homogeneous of degree `m - 1`. -/
@[lognarayana "lem_simplex_integral_homogeneous_operator"]
public theorem isHomogeneousOperator_simplexIntegral (hm : 1 ≤ m) (κ : σ ⊕ Fin m →₀ ℕ) :
    IsHomogeneousOperator κ ((m : ℤ) - 1)
      ((simplexIntegral σ R m).domRestrict (restrictSupport R (Set.Iic κ))) := by
  intro β _ f hf _
  refine ⟨β.degree + m - 1, by omega, ?_⟩
  rw [LinearMap.domRestrict_apply, hf]
  exact isHomogeneous_simplexIntegral_monomial hm β 1

end Homogeneous

/-! ### The algebraic symbol -/

section Symbol

open Finsupp

/-- The lower interval `Iic ν` of a multi-index is the box `∏_{j ∈ supp ν} [0, ν j]`. -/
private lemma Iic_eq_finsupp {ι : Type*} [DecidableEq ι] (ν : ι →₀ ℕ) :
    Finset.Iic ν = ν.support.finsupp (fun i => Finset.Iic (ν i)) := by
  ext α
  rw [Finset.mem_Iic, Finset.mem_finsupp_iff]
  constructor
  · intro h
    refine ⟨fun i hi => ?_, fun i _ => Finset.mem_Iic.2 (h i)⟩
    rw [Finsupp.mem_support_iff] at hi ⊢
    have := h i
    omega
  · rintro ⟨hs, hle⟩ i
    by_cases hi : i ∈ ν.support
    · exact Finset.mem_Iic.1 (hle i hi)
    · have : i ∉ α.support := fun h => hi (hs h)
      rw [Finsupp.notMem_support_iff] at this
      omega

/-- The multi-index binomial theorem:
`∏_j (A_j + B_j)^{ν_j} = ∑_{α ≤ ν} (ν choose α) A^α B^{ν - α}`. -/
private lemma prod_add_pow {ι S : Type*} [DecidableEq ι] [CommSemiring S] (A B : ι → S)
    (ν : ι →₀ ℕ) :
    (ν.prod fun j n => (A j + B j) ^ n) =
      ∑ α ∈ Finset.Iic ν, (ν.choose α : S) * (α.prod fun j n => A j ^ n) *
        ((ν - α).prod fun j n => B j ^ n) := by
  conv_lhs => rw [Finsupp.prod]; simp only [add_pow, Nat.range_succ_eq_Iic]
  rw [Finset.prod_sum, Iic_eq_finsupp, Finset.finsupp, Finset.sum_map]
  refine Finset.sum_congr (by congr!) fun p hp => ?_
  simp only [Function.Embedding.coeFn_mk]
  set α := Finsupp.indicator ν.support p
  have hα : α.support ⊆ ν.support := Finsupp.support_indicator_subset _ _
  have hνα : (ν - α).support ⊆ ν.support := Finsupp.support_tsub
  rw [Finsupp.choose, Nat.cast_finsuppProd,
    Finsupp.prod_of_support_subset _ hα _ (fun _ _ => by simp),
    Finsupp.prod_of_support_subset _ hα _ (fun _ _ => by simp),
    Finsupp.prod_of_support_subset _ hνα _ (fun _ _ => by simp),
    ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_attach ν.support]
  refine Finset.prod_congr rfl fun j _ => ?_
  have : α j = p j j.2 := Finsupp.indicator_of_mem j.2 p
  simp only [Finsupp.coe_tsub, Pi.sub_apply, this]
  ring

/-- `sumElim α γ ≤ sumElim ν κ` if and only if `α ≤ ν` and `γ ≤ κ`. -/
private lemma sumElim_le_sumElim {ι κι : Type*} {α ν : ι →₀ ℕ} {γ κ : κι →₀ ℕ} :
    sumElim α γ ≤ sumElim ν κ ↔ α ≤ ν ∧ γ ≤ κ := by
  simp only [Finsupp.le_def, Sum.forall, sumElim_inl, sumElim_inr]

/-- A sum over the box below `sumElim ν κ` is the double sum over the boxes below `ν` and `κ`. -/
private lemma sum_Iic_sumElim {ι κι M : Type*} [DecidableEq ι] [DecidableEq κι]
    {_ : DecidableEq (ι ⊕ κι)} [AddCommMonoid M] (ν : ι →₀ ℕ) (κ : κι →₀ ℕ)
    (f : (ι ⊕ κι →₀ ℕ) → M) :
    ∑ β ∈ Finset.Iic (sumElim ν κ), f β =
      ∑ α ∈ Finset.Iic ν, ∑ γ ∈ Finset.Iic κ, f (sumElim α γ) := by
  rw [← Finset.sum_product']
  refine Finset.sum_nbij' (fun β => (β.comapDomain Sum.inl Sum.inl_injective.injOn,
      β.comapDomain Sum.inr Sum.inr_injective.injOn)) (fun p => sumElim p.1 p.2)
    ?_ ?_ ?_ ?_ ?_
  · intro β hβ
    simp only [Finset.mem_Iic, Finset.mem_product] at hβ ⊢
    rw [← comapDomain_sumElim_comapDomain β, sumElim_le_sumElim] at hβ
    exact hβ
  · intro p hp
    simp only [Finset.mem_Iic, Finset.mem_product] at hp ⊢
    exact sumElim_le_sumElim.2 hp
  · intro β _; simp
  · intro p _; simp
  · intro β _; simp

/-- Renaming a monomial gives the product of the renamed variables. -/
private lemma rename_monomial_eq_prod {ι τ S : Type*} [CommSemiring S] (f : ι → τ)
    (e : ι →₀ ℕ) (c : S) :
    rename f (monomial e c) = C c * e.prod fun i n => X (f i) ^ n := by
  rw [monomial_eq, map_mul, rename_C, map_finsuppProd]
  simp [rename_X]

/-- The multi-index binomial coefficient splits along `Finsupp.sumElim`. -/
private lemma choose_sumElim {ι κι : Type*} (ν α : ι →₀ ℕ) (κ γ : κι →₀ ℕ) :
    (sumElim ν κ).choose (sumElim α γ) = ν.choose α * κ.choose γ := by
  simp only [Finsupp.choose, prod_sumElim]
  rfl

/-- The monomial at the point `(n, β)` of `ℕ^{1 + m}`, as a product of powers. -/
private lemma prod_single_none_add_mapDomain_pow {ι M : Type*} [CommMonoid M] (n : ℕ)
    (β : ι →₀ ℕ) (f : Option ι → M) :
    (single none n + β.mapDomain some).prod (fun i k => f i ^ k) =
      f none ^ n * β.prod fun i k => f (some i) ^ k := by
  rw [prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _),
    prod_single_index (h := fun i k => f i ^ k) (pow_zero _),
    prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]

/-- Truncated subtraction of multi-indices splits along `Finsupp.sumElim`. -/
private lemma sumElim_tsub_sumElim {ι κι : Type*} (ν α : ι →₀ ℕ) (κ γ : κι →₀ ℕ) :
    sumElim ν κ - sumElim α γ = sumElim (ν - α) (κ - γ) := by
  ext (_ | _) <;> rfl

/-- The algebraic symbol of the simplex integration operator `𝔍_m`, restricted to polynomials
of degree at most `ν j` in `x_j` and at most `κ i` in `u_i`, factors as
`∏_j (x_j + y_j) ^ ν_j · Ψ_{m,κ}(t, v)`, where `x_j = X (inl (some j))`, `t = X (inl none)`,
`y_j = X (inr (inl j))` and `v_i = X (inr (inr i))`. The sum over the box below `(ν, κ)` splits
into the binomial expansion of the first factor times the sum defining `Ψ_{m,κ}`. -/
@[lognarayana "lem_simplex_symbol_factorization"]
public theorem algebraicSymbol_simplexIntegral {σ : Type*} (R : Type*) [CommSemiring R]
    [Algebra ℚ R] (m : ℕ) (ν : σ →₀ ℕ) (κ : Fin m →₀ ℕ) :
    algebraicSymbol (Finsupp.sumElim ν κ)
        ((simplexIntegral σ R m).comp
          (restrictSupport R (Set.Iic (Finsupp.sumElim ν κ))).subtype) =
      (ν.prod fun j n =>
          (X (Sum.inl (some j)) + X (Sum.inr (Sum.inl j)) :
            MvPolynomial (Option σ ⊕ (σ ⊕ Fin m)) R) ^ n) *
        rename (fun i : Option (Fin m) =>
            (i.elim (Sum.inl none) fun k => Sum.inr (Sum.inr k) : Option σ ⊕ (σ ⊕ Fin m)))
          (psiKappa R m κ) := by
  classical
  unfold algebraicSymbol
  simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype]
  rw [Finset.sum_attach _ (fun β => C ((sumElim ν κ).choose β : R) *
    rename Sum.inl (simplexIntegral σ R m (monomial β 1)) *
    rename Sum.inr (monomial (sumElim ν κ - β) 1)), sum_Iic_sumElim, prod_add_pow, psiKappa,
    map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun γ _ => ?_
  rw [choose_sumElim, sumElim_tsub_sumElim, simplexIntegral_monomial_sumElim, one_smul,
    rename_monomial_eq_prod, rename_monomial_eq_prod, rename_monomial_eq_prod, prod_sumElim,
    prod_single_none_add_mapDomain_pow, prod_single_none_add_mapDomain_pow]
  simp only [Function.comp_def, Option.elim_none, Option.elim_some, mul_div_assoc, map_mul,
    map_natCast, Nat.cast_mul, C_1]
  ring

end Symbol

/-! ### Lorentzian polynomials -/

section Lorentzian

/-- Renaming variables along a map is a `{0,1}` linear substitution, so it preserves the
Lorentzian property given `LorentzianNonnegLinearSubstitution`. -/
private lemma isLorentzian_rename {σ τ : Type*} [Fintype σ] [Fintype τ]
    (hsub : LorentzianNonnegLinearSubstitution σ τ) (e : σ → τ) {f : MvPolynomial σ ℝ}
    (hf : f.IsLorentzian) : (rename e f).IsLorentzian := by
  classical
  have h := hsub (fun i j => if j = e i then 1 else 0) (fun i j => by split_ifs <;> norm_num)
    f hf
  have he : (fun i => ∑ j, (if j = e i then (1 : ℝ) else 0) • (X j : MvPolynomial τ ℝ)) =
      X ∘ e := by
    funext i; simp [ite_smul]
  rwa [he, ← rename_eq_aeval] at h

/-- The linear form `X a + X b` is Lorentzian. -/
private lemma isLorentzian_X_add_X {τ : Type*} [Fintype τ] (a b : τ) :
    (X a + X b : MvPolynomial τ ℝ).IsLorentzian := by
  classical
  refine IsLorentzian.of_isHomogeneous_of_le_one (d := 1) (fun α => ?_)
    ((isHomogeneous_X ℝ a).add (isHomogeneous_X ℝ b)) le_rfl
  rw [coeff_add, coeff_X, coeff_X]
  split_ifs <;> norm_num

/-- A variable is a Lorentzian polynomial. -/
private lemma isLorentzian_X {τ : Type*} [Fintype τ] (i : τ) :
    (X i : MvPolynomial τ ℝ).IsLorentzian := by
  classical
  refine IsLorentzian.of_isHomogeneous_of_le_one (d := 1) (fun α => ?_) (isHomogeneous_X ℝ i)
    le_rfl
  rw [coeff_X]; split_ifs <;> simp

/-- Multiplying a Lorentzian polynomial by `∏_{i ∈ s} L_i ^ δ_i`, with each `L_i` Lorentzian,
keeps it Lorentzian, given the product theorem. -/
private lemma isLorentzian_prod_pow_mul {ι τ : Type*} [Fintype τ] (hmul : LorentzianMul τ)
    {L : ι → MvPolynomial τ ℝ} (hL : ∀ i, (L i).IsLorentzian) (s : Finset ι) (δ : ι → ℕ)
    {f : MvPolynomial τ ℝ} (hf : f.IsLorentzian) :
    ((∏ i ∈ s, L i ^ δ i) * f).IsLorentzian := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hf
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, mul_assoc]
    induction δ a with
    | zero => simpa using ih
    | succ n ihn => rw [pow_succ', mul_assoc]; exact hmul _ _ (hL a) ihn

/-- `Ψ_{m,κ} = κ! • E_{J_{m,κ}}` is Lorentzian, since `J_{m,κ}` is M-convex. -/
private lemma isLorentzian_psiKappa (m : ℕ) (κ : Fin m →₀ ℕ)
    (hBH : NormalizedSupportPolyLorentzianOfMConvex (Option (Fin m))) :
    (psiKappa ℝ m κ).IsLorentzian := by
  rw [psiKappa_eq_factorial_smul_normalizedSupportPoly, ← Nat.cast_smul_eq_nsmul ℝ]
  exact (hBH _ (Finsupp.isMConvex_jKappa m κ)).smul (Nat.cast_nonneg _)

/-- For `ν ∈ ℕ^σ` and `κ ∈ ℕ^m`, the polynomial `∏_j (x_j + y_j) ^ ν_j · Ψ_{m,κ}(t, v)` is
Lorentzian in the variables `x_j = X (inl (some j))`, `t = X (inl none)`, `y_j = X (inr (inl j))`
and `v_i = X (inr (inr i))`: `Ψ_{m,κ}` is Lorentzian, renaming is a nonnegative linear
substitution, and each factor `x_j + y_j` is a Lorentzian linear form. -/
@[lognarayana "lem_simplex_symbol_lorentzian"]
public theorem isLorentzian_prod_add_pow_mul_rename_psiKappa {σ : Type*} [Fintype σ] (m : ℕ)
    (ν : σ →₀ ℕ) (κ : Fin m →₀ ℕ)
    (hsub : LorentzianNonnegLinearSubstitution (Option (Fin m)) (Option σ ⊕ (σ ⊕ Fin m)))
    (hmul : LorentzianMul (Option σ ⊕ (σ ⊕ Fin m)))
    (hBH : NormalizedSupportPolyLorentzianOfMConvex (Option (Fin m))) :
    IsLorentzian
      ((ν.prod fun j n =>
          (X (Sum.inl (some j)) + X (Sum.inr (Sum.inl j)) :
            MvPolynomial (Option σ ⊕ (σ ⊕ Fin m)) ℝ) ^ n) *
        rename (fun i : Option (Fin m) =>
            (i.elim (Sum.inl none) fun k => Sum.inr (Sum.inr k) : Option σ ⊕ (σ ⊕ Fin m)))
          (psiKappa ℝ m κ)) :=
  isLorentzian_prod_pow_mul hmul (fun _ => isLorentzian_X_add_X _ _) ν.support ν
    (isLorentzian_rename hsub _ (isLorentzian_psiKappa m κ hBH))

/-- A polynomial in the variables `σ ⊕ τ` is supported below its own degree bounds
`(degreeOf (inl j), degreeOf (inr i))`. -/
private lemma mem_restrictSupport_Iic_sumElim_degreeOf {σ τ R : Type*} [Finite σ] [Finite τ]
    [CommSemiring R] (G : MvPolynomial (σ ⊕ τ) R) :
    G ∈ restrictSupport R (Set.Iic (Finsupp.sumElim
      (Finsupp.equivFunOnFinite.symm fun j => G.degreeOf (Sum.inl j))
      (Finsupp.equivFunOnFinite.symm fun i => G.degreeOf (Sum.inr i)))) := by
  rw [mem_restrictSupport_iff]
  rintro s hs (j | i)
  · simpa using monomial_le_degreeOf (Sum.inl j) hs
  · simpa using monomial_le_degreeOf (Sum.inr i) hs

/-- **Simplex integration preserves the Lorentzian property** (after [BH, Theorems 3.2 and 3.10]):
for `m ≥ 2` and a Lorentzian polynomial `G(x, u_1, …, u_m)`, the polynomial `𝔍_m G (x, t)` is
Lorentzian, given the cited results of Brändén–Huh on linear substitutions, products,
M-convex supports, and the symbol theorem for operators `ℝ[x, u] → ℝ[x, t]`. The degrees of `G`
are bounded by `(ν, κ)`, and on `ℝ_{(ν,κ)}[x, u]` the operator `𝔍_m` is homogeneous with the
Lorentzian symbol `∏_j (x_j + y_j)^{ν_j} · Ψ_{m,κ}(t, v)`. -/
@[lognarayana "thm_simplex_integration"]
public theorem IsLorentzian.simplexIntegral {σ : Type*} [Fintype σ] {m : ℕ} (hm : 2 ≤ m)
    (hsub : LorentzianNonnegLinearSubstitution (Option (Fin m)) (Option σ ⊕ (σ ⊕ Fin m)))
    (hmul : LorentzianMul (Option σ ⊕ (σ ⊕ Fin m)))
    (hBH : NormalizedSupportPolyLorentzianOfMConvex (Option (Fin m)))
    (hsym : BrandenHuhSymbolTheorem (σ ⊕ Fin m) (Option σ))
    {G : MvPolynomial (σ ⊕ Fin m) ℝ} (hG : G.IsLorentzian) :
    (MvPolynomial.simplexIntegral σ ℝ m G).IsLorentzian := by
  refine hsym _ _ _ (isHomogeneousOperator_simplexIntegral (by omega) _) ?_
    ⟨G, mem_restrictSupport_Iic_sumElim_degreeOf G⟩ hG
  rw [LinearMap.domRestrict, algebraicSymbol_simplexIntegral]
  exact isLorentzian_prod_add_pow_mul_rename_psiKappa m _ _ hsub hmul hBH

/-- **Weighted simplex integrals**: for `m ≥ 2`, a Lorentzian polynomial `G(x, u_1, …, u_m)` and
`δ ∈ ℕ^m`, the polynomial `𝔍_m(u^δ G)(x, t)` is Lorentzian, given the cited results of
Brändén–Huh on products, linear substitutions, M-convex supports, and the symbol theorem for
operators `ℝ[x, u] → ℝ[x, t]`. Each `u_i` is Lorentzian, so `u^δ G` is Lorentzian by the
product theorem, and `MvPolynomial.IsLorentzian.simplexIntegral` applies. -/
@[lognarayana "lem_simplex_integration_weighted"]
public theorem IsLorentzian.simplexIntegral_prod_X_pow_mul {σ : Type*} [Fintype σ] {m : ℕ}
    (hm : 2 ≤ m)
    (hmulG : LorentzianMul (σ ⊕ Fin m))
    (hsub : LorentzianNonnegLinearSubstitution (Option (Fin m)) (Option σ ⊕ (σ ⊕ Fin m)))
    (hmul : LorentzianMul (Option σ ⊕ (σ ⊕ Fin m)))
    (hBH : NormalizedSupportPolyLorentzianOfMConvex (Option (Fin m)))
    (hsym : BrandenHuhSymbolTheorem (σ ⊕ Fin m) (Option σ))
    {G : MvPolynomial (σ ⊕ Fin m) ℝ} (hG : G.IsLorentzian) (δ : Fin m → ℕ) :
    (MvPolynomial.simplexIntegral σ ℝ m ((∏ i, X (Sum.inr i) ^ δ i) * G)).IsLorentzian :=
  (isLorentzian_prod_pow_mul hmulG (fun i => isLorentzian_X (Sum.inr i)) _ δ hG).simplexIntegral
    hm hsub hmul hBH hsym

end Lorentzian

end MvPolynomial
























