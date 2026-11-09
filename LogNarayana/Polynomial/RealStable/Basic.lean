/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module
public import LogNarayana.Polynomial.RealStable.Defs
public import LogNarayana.Lorentzian.Symbol.Defs
public import LogNarayana.Lorentzian.Hessian.Defs
public import LogNarayana.AuxiliaryDefinitions

/-!
# Real stability

A polynomial `f ∈ ℝ[z_i : i ∈ σ]` is real-stable if it does not vanish when every `zᵢ` lies in
the open upper half-plane. This file proves the elementary closure properties of real stability
used in [LogNarayana] and records, as propositions to be taken as hypotheses, the deeper results
on real stability that the paper cites.

Real stability is closed under products, because evaluation is multiplicative and `ℂ` has no
zero divisors, and under renaming of variables along any map `φ : σ → τ`, because evaluating the
renamed polynomial at `ζ` is evaluating `f` at `ζ ∘ φ`. A nonzero real polynomial in one
variable `zᵢ` is real-stable if and only if it is real-rooted: a real-rooted polynomial has only
real zeros, and conversely the zeros of a real polynomial are closed under conjugation, so if none
lies in the open upper half-plane then none lies in the open lower half-plane either. Finally, if
`p ∈ ℝ[t]` is nonzero and real-rooted and `S` is nonempty, then `p(∑_{i ∈ S} zᵢ)` is real-stable,
since `∑_{i ∈ S} ζᵢ` lies in the upper half-plane whenever every `ζᵢ` does.

## Main definitions

The following are cited theorems, each stated as a `Prop` parametrized by the variable type and
taken as a hypothesis by the results that use it.

* `RealStablePreserverOfSymbol`: for `n ≥ 1` variables, a linear operator on `ℝ_κ[z]` with
  real-stable algebraic symbol maps real-stable polynomials to real-stable polynomials or to
  zero [BB].
* `IsRealStableHomogenizeOfNonneg`: the homogenization `f_H` of a real-stable polynomial `f`
  with nonnegative coefficients, of degree `deg f`, is real-stable [BBL], [BH].
* `IsLorentzianOfRealStable`: a homogeneous real-stable polynomial with nonnegative
  coefficients is Lorentzian [BH].
* `IsRealStablePDerivClosed`: a partial derivative of a real-stable polynomial is
  real-stable or zero [Wagner].
* `IsRealStableLimitClosed`: Hurwitz's theorem, a limit, uniformly on compact sets, of
  non-vanishing analytic functions on a domain of `ℂ^n` is non-vanishing or identically zero
  [BB], [Wagner].
* `IsRealStableSpecializeClosed`: substituting a real number for one variable of a
  real-stable polynomial gives a real-stable polynomial or zero [Wagner].

## Main results

* `MvPolynomial.IsRealStable.mul`: if `f` and `g` are real-stable, so is `f * g`.
* `MvPolynomial.IsRealStable.rename`: `f.IsRealStable → (rename φ f).IsRealStable`.
* `Polynomial.isRealStable_toMvPolynomial_iff_splits`: for `f ≠ 0`,
  `(toMvPolynomial i f).IsRealStable ↔ f.Splits`.
* `Polynomial.isRealStable_aeval_sum_X`: for `p ≠ 0` splitting over `ℝ` and `S` nonempty,
  `(Polynomial.aeval (∑ i ∈ S, X i) p).IsRealStable`.
* `MvPolynomial.RealStablePreserverOfSymbol.apply`: the symbol theorem for every finite
  variable type, the empty one included.
* `MvPolynomial.IsRealStableHomogenizeOfNonneg.isRealStable_homogenize_of_totalDegree_le`: the
  homogenization at any degree `D ≥ deg f` is real-stable.
* `MvPolynomial.IsRealStableLimitClosed.eq_zero_or_isRealStable`: a coefficientwise limit of
  real-stable polynomials of bounded total degree in finitely many variables is zero or
  real-stable.

## Implementation notes

Real-rootedness is Mathlib's `Polynomial.Splits`. A univariate polynomial is placed in an
arbitrary variable `i` of an arbitrary index type `σ` through `Polynomial.toMvPolynomial`; the
ring `ℝ[z₁]` is the case `σ = Fin 1`. The substitution `t ↦ ∑_{i ∈ S} zᵢ` is the `ℝ`-algebra map
`Polynomial.aeval (∑ i ∈ S, MvPolynomial.X i)`.

Since `MvPolynomial.IsRealStable` excludes the zero polynomial, the cited closure properties
conclude with a disjunction `g = 0 ∨ g.IsRealStable`. The symbol theorem, the homogenization
theorem and Hurwitz's theorem are stated, as in their sources, for finitely many variables (for
an infinite `σ` the proposition says nothing); the closure properties of [Wagner, Lemma 2.4]
are stated for any variable type, since only finitely many variables occur in the data.

In `RealStablePreserverOfSymbol`, the domain `ℝ_κ[z]` is
`MvPolynomial.restrictSupport ℝ (Set.Iic κ)` and the symbol is
`MvPolynomial.algebraicSymbol κ T ∈ MvPolynomial (σ ⊕ σ) ℝ`, whose variables `Sum.inl i` are the
`z_i` and `Sum.inr i` the `w_i`; only the sufficiency of condition (b) of [BB, Theorem 1.2] is
stated, for a finite nonempty `σ` ([BB]'s `n ≥ 1`). The empty case is proved in
`MvPolynomial.RealStablePreserverOfSymbol.apply`.

In `IsRealStableHomogenizeOfNonneg`, [BBL] homogenizes at `D = f.totalDegree`; at a larger
`D`, `homogenize f D = y ^ (D - f.totalDegree) * homogenize f f.totalDegree`
(`MvPolynomial.homogenize_eq_X_none_pow_mul`) and `y = X none` is real-stable.

In `IsLorentzianOfRealStable`, homogeneity is `∃ d, f.IsHomogeneous d`, and `σ` is
finite, as `MvPolynomial.IsLorentzian` requires.

In `IsRealStablePDerivClosed`, `∂_i` is `MvPolynomial.pderiv i`, which agrees with
`MvPolynomial.iteratedPDeriv (Finsupp.single i 1)`.

In `IsRealStableLimitClosed`, `ℂ^n` is `σ → ℂ` for a finite type `σ`, analyticity is
`AnalyticOnNhd ℂ`, a domain is an open set with `IsConnected`, and convergence uniformly on
compact subsets is `TendstoUniformlyOn` on every compact `K ⊆ Ω`. Its consequence for
polynomials, on the domain `{z | ∀ i, 0 < Im z_i}`, is
`MvPolynomial.IsRealStableLimitClosed.eq_zero_or_isRealStable`.

In `IsRealStableSpecializeClosed`, the substitution `z_i ↦ a` is the `ℝ`-algebra
endomorphism `MvPolynomial.aeval (Function.update MvPolynomial.X i (MvPolynomial.C a))` of
`ℝ[z_j : j ∈ σ]`, so the specialized polynomial stays in the same ring, where it no longer
involves `z_i`. Real stability there is the same as in `ℝ[z_j : j ∈ σ ∖ {i}]`, because its value
does not depend on the `i`-th coordinate of the evaluation point.

## References

* [LogNarayana], lemmas on real stability.
* [BB] J. Borcea and P. Brändén, *The Lee–Yang and Pólya–Schur programs. I. Linear operators
  preserving stability*, Invent. Math. 177 (2009), 541–569, Theorems 1.2 and 1.6.
* [BBL] J. Borcea, P. Brändén, T. M. Liggett, *Negative dependence and the geometry of
  polynomials*, J. Amer. Math. Soc. 22 (2009), Theorem 4.5.
* [BH] P. Brändén, J. Huh, *Lorentzian polynomials*, Ann. of Math. 192 (2020), Proposition 2.2
  and proof of Corollary 3.9.
* [Wagner] D. G. Wagner, *Multivariate stable polynomials: theory and applications*,
  Bull. Amer. Math. Soc. 48 (2011), Section 2 and Lemma 2.4(a),(d),(f).
-/

section RealRooted

open Polynomial

/-! ### Closure properties -/

/-- The product of two real-stable polynomials is real-stable. -/
@[lognarayana "lem_real_stable_mul"]
public theorem MvPolynomial.IsRealStable.mul {σ : Type*} {f g : MvPolynomial σ ℝ}
    (hf : f.IsRealStable) (hg : g.IsRealStable) : (f * g).IsRealStable := fun ζ hζ => by
  rw [map_mul]
  exact mul_ne_zero (hf ζ hζ) (hg ζ hζ)

/-- A real-stable polynomial is nonzero: the zero polynomial vanishes at `ζ ≡ i`. -/
public theorem MvPolynomial.IsRealStable.ne_zero {σ : Type*} {f : MvPolynomial σ ℝ}
    (hf : f.IsRealStable) : f ≠ 0 := by
  rintro rfl
  exact hf (fun _ => Complex.I) (fun _ => by simp) (map_zero _)

/-- Renaming the variables of a real-stable polynomial along any map gives a real-stable
polynomial. -/
@[lognarayana "lem_real_stable_rename"]
public theorem MvPolynomial.IsRealStable.rename {σ τ : Type*} (φ : σ → τ)
    {f : MvPolynomial σ ℝ} (hf : f.IsRealStable) :
    (MvPolynomial.rename φ f).IsRealStable := fun ζ hζ => by
  rw [MvPolynomial.aeval_rename]
  exact hf (ζ ∘ φ) fun i => hζ (φ i)

/-! ### Real-rooted polynomials -/

/-- A nonzero real-rooted real polynomial does not vanish on the open upper half-plane. -/
private lemma aeval_ne_zero_of_splits_of_im_pos {p : ℝ[X]} (hp : p ≠ 0) (hsplit : p.Splits)
    {z : ℂ} (hz : 0 < z.im) : aeval z p ≠ 0 := fun h => by
  obtain ⟨r, rfl⟩ := hsplit.mem_range_of_isRoot hp (x := z)
    (by rwa [IsRoot.def, eval_map_algebraMap])
  simp at hz

/-- Real stability of `f` in the variable `zᵢ` is the absence of zeros of `f` in the open upper
half-plane. -/
private lemma isRealStable_toMvPolynomial_iff {σ : Type*} (i : σ) (f : ℝ[X]) :
    (toMvPolynomial i f).IsRealStable ↔ ∀ z : ℂ, 0 < z.im → aeval z f ≠ 0 := by
  simp only [MvPolynomial.IsRealStable, MvPolynomial.aeval_toMvPolynomial]
  exact ⟨fun h z hz => h (fun _ => z) (fun _ => hz), fun h ζ hζ => h (ζ i) (hζ i)⟩

/-- A nonzero real polynomial whose complex zeros all lie in the closed lower half-plane splits
over `ℝ`: the conjugate of a zero is a zero, so every zero is real. -/
private lemma splits_of_forall_aeval_eq_zero_im_nonpos {f : ℝ[X]} (hf : f ≠ 0)
    (h : ∀ z : ℂ, aeval z f = 0 → z.im ≤ 0) : f.Splits := by
  refine Splits.of_splits_map (algebraMap ℝ ℂ) (IsAlgClosed.splits _) fun a ha => ?_
  rw [mem_roots (map_ne_zero hf), IsRoot, eval_map_algebraMap] at ha
  have hconj : aeval (starRingEnd ℂ a) f = 0 := by
    simpa [ha] using aeval_algHom_apply Complex.conjAe a f
  have h0 : a.im = 0 := le_antisymm (h a ha) (by simpa using h _ hconj)
  exact ⟨a.re, Complex.ext (by simp) (by simp [h0])⟩

/-- A nonzero real polynomial, viewed as a polynomial in the single variable `zᵢ`, is real-stable
if and only if it is real-rooted. -/
@[lognarayana "lem_real_stable_univariate_iff"]
public theorem Polynomial.isRealStable_toMvPolynomial_iff_splits {σ : Type*} (i : σ)
    {f : Polynomial ℝ} (hf : f ≠ 0) :
    (Polynomial.toMvPolynomial i f).IsRealStable ↔ f.Splits := by
  rw [isRealStable_toMvPolynomial_iff]
  exact ⟨fun hs => splits_of_forall_aeval_eq_zero_im_nonpos hf fun z hz =>
    not_lt.1 fun h => hs z h hz, fun hs _ => aeval_ne_zero_of_splits_of_im_pos hf hs⟩

/-- If `p ∈ ℝ[t]` is nonzero and real-rooted and `S` is nonempty, then `p(∑_{i ∈ S} zᵢ)` is
real-stable. -/
@[lognarayana "lem_real_stable_affine_shift"]
public theorem Polynomial.isRealStable_aeval_sum_X {σ : Type*} {p : Polynomial ℝ} (hp : p ≠ 0)
    (hsplit : p.Splits) {S : Finset σ} (hS : S.Nonempty) :
    (Polynomial.aeval (∑ i ∈ S, MvPolynomial.X i : MvPolynomial σ ℝ) p).IsRealStable :=
  fun ζ hζ => by
  rw [← aeval_algHom_apply, map_sum]
  simp only [MvPolynomial.aeval_X]
  exact aeval_ne_zero_of_splits_of_im_pos hp hsplit
    (by simpa [Complex.im_sum] using Finset.sum_pos (fun i _ => hζ i) hS)

end RealRooted

/-! ### Cited results -/

section Cited

namespace MvPolynomial

open Filter Topology

/-- `X i ^ n` is real-stable. -/
public theorem isRealStable_X_pow {σ : Type*} (i : σ) (n : ℕ) :
    (X i ^ n : MvPolynomial σ ℝ).IsRealStable := fun ζ hζ => by
  rw [map_pow, aeval_X]
  exact pow_ne_zero _ fun h => by simpa [h] using hζ i

/-- Over an empty variable type, a real polynomial is real-stable if and only if it is
nonzero. -/
public theorem isRealStable_iff_ne_zero_of_isEmpty {σ : Type*} [IsEmpty σ]
    {f : MvPolynomial σ ℝ} : f.IsRealStable ↔ f ≠ 0 := by
  refine ⟨IsRealStable.ne_zero, fun hf ζ _ h => hf ?_⟩
  rw [eq_C_of_isEmpty f, aeval_C] at h
  rw [eq_C_of_isEmpty f, show f.coeff 0 = 0 by simpa using h, C_0]

/-! ### The symbol theorem for every finite variable type -/

/-- **Borcea–Brändén** for every finite variable type, the empty one included: if the
algebraic symbol of `T : ℝ_κ[z] → ℝ[z]` is real-stable then `T` maps real-stable polynomials to
zero or to real-stable polynomials. For a nonempty `σ` this is `RealStablePreserverOfSymbol σ`;
for an empty `σ` the domain is the constants `ℝ · 1`, the symbol is `T 1` up to renaming, and
`T (c · 1) = c · T 1` is nonzero. -/
public theorem RealStablePreserverOfSymbol.apply {σ : Type*} [Finite σ]
    (h : RealStablePreserverOfSymbol σ) (κ : σ →₀ ℕ)
    (T : restrictSupport ℝ (Set.Iic κ) →ₗ[ℝ] MvPolynomial σ ℝ)
    (hT : (algebraicSymbol κ T).IsRealStable) (f : restrictSupport ℝ (Set.Iic κ))
    (hf : (f : MvPolynomial σ ℝ).IsRealStable) : T f = 0 ∨ (T f).IsRealStable := by
  rcases isEmpty_or_nonempty σ with hσ | hσ
  · right
    rw [isRealStable_iff_ne_zero_of_isEmpty]
    have h1 : (monomial (0 : σ →₀ ℕ) (1 : ℝ)) ∈ restrictSupport ℝ (Set.Iic κ) :=
      (monomial_mem_restrictSupport ℝ).2
        (Or.inl (Set.mem_Iic.2 (Subsingleton.elim (0 : σ →₀ ℕ) κ ▸ le_rfl)))
    have hsmul : ∀ g : restrictSupport ℝ (Set.Iic κ),
        g = (g : MvPolynomial σ ℝ).coeff 0 • ⟨monomial 0 1, h1⟩ := fun g => by
      ext1
      rw [Submodule.coe_smul, smul_monomial, smul_eq_mul, mul_one, ← C_apply]
      exact eq_C_of_isEmpty _
    have hc : (f : MvPolynomial σ ℝ).coeff 0 ≠ 0 := fun h0 =>
      hf.ne_zero (by rw [eq_C_of_isEmpty (f : MvPolynomial σ ℝ), h0, C_0])
    intro hTf
    rw [hsmul f, map_smul] at hTf
    have hT1 : T ⟨monomial 0 1, h1⟩ = 0 := (smul_eq_zero.1 hTf).resolve_left hc
    have hzero : ∀ g, T g = 0 := fun g => by rw [hsmul g, map_smul, hT1, smul_zero]
    exact hT.ne_zero (by simp [algebraicSymbol, hzero])
  · exact h κ T hT f hf

/-! ### Homogenization at a larger degree -/

/-- Homogenizing at a degree `D ≥ deg f` multiplies the homogenization at `deg f` by
`y ^ (D - deg f)`, where `y = X none`. -/
public theorem homogenize_eq_X_none_pow_mul {σ : Type*} (f : MvPolynomial σ ℝ) {D : ℕ}
    (hD : f.totalDegree ≤ D) :
    f.homogenize D = X none ^ (D - f.totalDegree) * f.homogenize f.totalDegree := by
  have hdeg : ∀ α ∈ f.support, α.degree ≤ f.totalDegree := fun α hα => le_totalDegree hα
  rw [homogenize, homogenize, Finset.mul_sum,
    Finset.filter_true_of_mem fun α hα => (hdeg α hα).trans hD,
    Finset.filter_true_of_mem hdeg]
  refine Finset.sum_congr rfl fun α hα => ?_
  rw [X_pow_eq_monomial, monomial_mul, one_mul]
  congr 1
  rw [add_left_comm, ← Finsupp.single_add]
  congr 2
  have := hdeg α hα
  rw [show D - α.degree = D - f.totalDegree + (f.totalDegree - α.degree) by omega]

/-- The form of `IsRealStableHomogenizeOfNonneg` used by the proofs: homogenizing a real-stable
polynomial with nonnegative coefficients at any degree `D ≥ deg f` gives a real-stable
polynomial, since it is `y ^ (D - deg f) · f_H` and `y ^ k` is real-stable. -/
public theorem IsRealStableHomogenizeOfNonneg.isRealStable_homogenize_of_totalDegree_le
    {σ : Type*} [Finite σ] (h : IsRealStableHomogenizeOfNonneg σ) {f : MvPolynomial σ ℝ}
    (hnn : f.HasNonnegCoeffs) (hf : f.IsRealStable) {D : ℕ} (hD : f.totalDegree ≤ D) :
    (f.homogenize D).IsRealStable := by
  rw [homogenize_eq_X_none_pow_mul f hD]
  exact (isRealStable_X_pow _ _).mul (h f hnn hf)

/-! ### Limits of real-stable polynomials, from Hurwitz's theorem -/

/-- The open upper half-plane product `{z : σ → ℂ | ∀ i, 0 < (z i).im}` is open in `ℂ^σ`. -/
public theorem isOpen_upperHalfPlane_pi {σ : Type*} [Finite σ] :
    IsOpen {z : σ → ℂ | ∀ i, 0 < (z i).im} := by
  rw [Set.ofPred_forall]
  exact isOpen_iInter_of_finite fun i =>
    isOpen_lt continuous_const (Complex.continuous_im.comp (continuous_apply i))

/-- The open upper half-plane product `{z : σ → ℂ | ∀ i, 0 < (z i).im}` is connected. -/
public theorem isConnected_upperHalfPlane_pi {σ : Type*} :
    IsConnected {z : σ → ℂ | ∀ i, 0 < (z i).im} := by
  refine Convex.isConnected (fun x hx y hy a b ha hb hab i => ?_)
    ⟨fun _ => Complex.I, fun _ => by simp⟩
  have hx' := hx i
  have hy' := hy i
  simp only [Pi.add_apply, Pi.smul_apply, Complex.add_im, Complex.smul_im, smul_eq_mul] at hx' hy' ⊢
  rcases ha.lt_or_eq with ha' | rfl
  · nlinarith [mul_pos ha' hx', mul_nonneg hb hy'.le]
  · simp only [zero_add] at hab
    subst hab
    simpa using hy'

/-- Evaluation of a polynomial supported in a finite set `S` of exponents, as a finite sum. -/
private lemma aeval_eq_sum_of_support_subset {σ : Type*} [Fintype σ] {S : Finset (σ →₀ ℕ)}
    {p : MvPolynomial σ ℝ} (hp : p.support ⊆ S) (z : σ → ℂ) :
    aeval z p = ∑ α ∈ S, Complex.ofReal (p.coeff α) * ∏ i, z i ^ α i := by
  rw [aeval_def, eval₂_eq', Finset.sum_subset hp fun α _ hα => by
    rw [notMem_support_iff.1 hα, map_zero, zero_mul]]
  rfl

/-- **A coefficientwise limit of real-stable polynomials of bounded degree is zero or
real-stable**, from Hurwitz's theorem `IsRealStableLimitClosed σ` on the domain
`ℍ^σ = {z | ∀ i, 0 < Im z_i}`: the evaluations of the `F k` are analytic and non-vanishing on
`ℍ^σ`, all `F k` and `f` are supported in the finite set of exponents `α ≤ (D, …, D)`, so the
evaluations converge to that of `f` uniformly on compact sets; and a polynomial vanishing on
`ℍ^σ` vanishes on a large product of finite sets, hence is zero. -/
public theorem IsRealStableLimitClosed.eq_zero_or_isRealStable {σ : Type*} [Finite σ]
    (h : IsRealStableLimitClosed σ) (D : ℕ) (F : ℕ → MvPolynomial σ ℝ) (f : MvPolynomial σ ℝ)
    (hF : ∀ k, (F k).IsRealStable) (hdeg : ∀ k, (F k).totalDegree ≤ D)
    (hlim : ∀ α : σ →₀ ℕ, Tendsto (fun k => (F k).coeff α) atTop (𝓝 (f.coeff α))) :
    f = 0 ∨ f.IsRealStable := by
  classical
  have := Fintype.ofFinite σ
  set Ω : Set (σ → ℂ) := {z | ∀ i, 0 < (z i).im} with hΩ
  set S : Finset (σ →₀ ℕ) := Finset.Iic (Finsupp.equivFunOnFinite.symm fun _ => D) with hSdef
  have hS : ∀ α : σ →₀ ℕ, α.degree ≤ D → α ∈ S := fun α hα => by
    rw [hSdef, Finset.mem_Iic]
    intro i
    change α i ≤ D
    refine le_trans ?_ hα
    rw [Finsupp.degree_eq_sum]
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have hFS : ∀ k, (F k).support ⊆ S := fun k α hα =>
    hS α ((le_totalDegree hα).trans (hdeg k))
  have hfS : f.support ⊆ S := by
    intro α hα
    by_contra hαS
    have h0 : ∀ k, (F k).coeff α = 0 := fun k =>
      notMem_support_iff.1 fun h => hαS (hFS k h)
    refine (mem_support_iff.1 hα) (tendsto_nhds_unique (hlim α) ?_)
    simp [h0]
  have hanalytic : ∀ p : MvPolynomial σ ℝ, AnalyticOnNhd ℂ (fun z : σ → ℂ => aeval z p) Ω :=
    fun p => AnalyticOnNhd.aeval_mvPolynomial
      (fun i => (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) i).analyticOnNhd _) p
  have hunif : ∀ K ⊆ Ω, IsCompact K → TendstoUniformlyOn (fun k z => aeval z (F k))
      (fun z => aeval z f) atTop K := by
    intro K _ hK
    set m : (σ →₀ ℕ) → (σ → ℂ) → ℂ := fun α z => ∏ i, z i ^ α i
    have hm : ContinuousOn (fun z => ∑ α ∈ S, ‖m α z‖) K :=
      (continuous_finsetSum _ fun α _ => (continuous_finsetProd _ fun i _ =>
        (continuous_apply i).pow _).norm).continuousOn
    obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hm
    have hmM : ∀ α ∈ S, ∀ z ∈ K, ‖m α z‖ ≤ |M| := fun α hα z hz => by
      refine le_trans ?_ ((le_abs_self _).trans' ((Real.le_norm_self _).trans (hM z hz)))
      exact Finset.single_le_sum (f := fun α => ‖m α z‖) (fun _ _ => norm_nonneg _) hα
    have hsum : Tendsto (fun k => ∑ α ∈ S, |f.coeff α - (F k).coeff α|) atTop (𝓝 0) := by
      have := tendsto_finsetSum S fun α _ => ((hlim α).const_sub (f.coeff α)).abs
      simpa using this
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [(tendsto_order.1 hsum).2 (ε / (|M| + 1)) (by positivity)] with k hk z hz
    rw [aeval_eq_sum_of_support_subset hfS, aeval_eq_sum_of_support_subset (hFS k),
      dist_eq_norm, ← Finset.sum_sub_distrib]
    calc ‖∑ α ∈ S, (Complex.ofReal (f.coeff α) * m α z - Complex.ofReal ((F k).coeff α) * m α z)‖
        ≤ ∑ α ∈ S, |f.coeff α - (F k).coeff α| * |M| := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun α hα => ?_)
          rw [← sub_mul, norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left (hmM α hα z hz) (abs_nonneg _)
      _ = (∑ α ∈ S, |f.coeff α - (F k).coeff α|) * |M| := (Finset.sum_mul _ _ _).symm
      _ ≤ (∑ α ∈ S, |f.coeff α - (F k).coeff α|) * (|M| + 1) :=
          mul_le_mul_of_nonneg_left (by linarith) (Finset.sum_nonneg fun _ _ => abs_nonneg _)
      _ < ε / (|M| + 1) * (|M| + 1) := mul_lt_mul_of_pos_right hk (by positivity)
      _ = ε := div_mul_cancel₀ _ (by positivity)
  rcases h Ω isOpen_upperHalfPlane_pi isConnected_upperHalfPlane_pi
    (fun k z => aeval z (F k)) (fun z => aeval z f) (fun k => hanalytic (F k))
    (fun k z hz => hF k z hz) hunif with hne | hzero
  · exact Or.inr fun ζ hζ => hne ζ hζ
  · left
    refine map_injective (algebraMap ℝ ℂ) (FaithfulSMul.algebraMap_injective ℝ ℂ) ?_
    rw [map_zero]
    refine eq_zero_of_eval_zero_at_prod_finset _
      (fun i => (Finset.range (degreeOf i (map (algebraMap ℝ ℂ) f) + 1)).image
        fun j : ℕ => ((j : ℂ) + 1) * Complex.I) (fun i => ?_) (fun x hx => ?_)
    · rw [Finset.card_image_of_injective _ fun a b hab => by
          simpa [Complex.ext_iff] using hab, Finset.card_range]
      exact Nat.lt_succ_self _
    · rw [eval_map, ← aeval_def]
      refine hzero x fun i => ?_
      obtain ⟨j, -, hj⟩ := Finset.mem_image.1 (hx i)
      rw [← hj]
      simp only [Complex.mul_im, Complex.I_re, Complex.I_im, mul_one, mul_zero,
        Complex.add_re, Complex.natCast_re, Complex.one_re]
      positivity

end MvPolynomial

end Cited
