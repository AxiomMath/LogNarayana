/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib
public import LogNarayana.Attr
public import LogNarayana.Narayana.AppellOperator.Defs
public import LogNarayana.Narayana.SignedAppell.Defs
public import LogNarayana.Lorentzian.Symbol.Defs
public import LogNarayana.Polynomial.RealStable.Defs
public import LogNarayana.Narayana.SignedAppell.Basic
public import LogNarayana.Polynomial.RealStable.Basic
public import LogNarayana.Narayana.Polynomials.Basic

/-!
# The Appell operator and real stability

This file proves the basic properties of the Appell operator `𝔄`, the linear map on polynomials
in the variables `z_i`, `i ∈ σ`, sending `z^α` to `∏_i η_{α_i}(z_i)`, and shows that it preserves
real stability.

Since `η_m = t^m + (lower terms)`, `𝔄` fixes the top-degree part of a polynomial up to terms of
strictly lower degree; in particular `𝔄(F) ≠ 0` for `F ≠ 0`. For `κ : σ →₀ ℕ`, the algebraic
symbol of the restriction `𝔄_κ` of `𝔄` to the polynomials of degree at most `κ i` in each `z_i`
factors as `∏_i η_{κ_i}(z_i + w_i)`. Each factor is real-stable because `η_m` is real-rooted, so
the symbol is real-stable, and the Borcea–Brändén symbol theorem (cited, taken as a hypothesis)
shows that `𝔄` preserves real stability.

## Main results

* `MvPolynomial.degree_lt_of_mem_support_appellOperator_sub`: if every `α ∈ supp F` has
  `|α| ≤ D`, then every `γ ∈ supp (𝔄(F) - F)` has `|γ| < D`.
* `MvPolynomial.appellOperator_ne_zero`: `F ≠ 0 → 𝔄(F) ≠ 0`.
* `MvPolynomial.algebraicSymbol_appellOperator`:
  `Sym_κ(𝔄_κ)(z, w) = ∏_{i ∈ σ} η_{κ_i}(z_i + w_i)`.
* `MvPolynomial.isRealStable_aeval_signedAppell`: `η_m(z_i + w_i)` is real-stable.
* `MvPolynomial.isRealStable_algebraicSymbol_appellOperator`: `Sym_κ(𝔄_κ)` is real-stable.
* `MvPolynomial.isRealStable_appellOperator`: `𝔄(F)` is real-stable whenever `F` is.

## Implementation notes

The paper works over `ℝ` with `σ` finite. The degree statements and the symbol factorization
hold over any commutative ring `R` (the coefficients of `η_m` are integers) and, except for the
symbol, for any index type `σ`. The total degree `|α|` of a multi-index is `Finsupp.degree α`.
The variables `z_i` are `X (Sum.inl i)` and the `w_i` are `X (Sum.inr i)` in
`MvPolynomial (σ ⊕ σ) R`, as in `MvPolynomial.algebraicSymbol`; `η_m(z_i + w_i)` is
`Polynomial.aeval (X (Sum.inl i) + X (Sum.inr i)) (Polynomial.signedAppell R m)`.

The Borcea–Brändén theorem [BB, Theorem 1.2] is cited, not proved: it enters as the hypothesis
`MvPolynomial.RealStablePreserverOfSymbol σ`. Likewise the Liu–Wang real-rootedness of the
shifted Narayana polynomials enters as the hypothesis `ShiftedNarayanaNegRealRoots`; their
γ-expansion is not needed.

## References

* [LogNarayana], Section 6 (the Appell operator).
* [BB] J. Borcea, P. Brändén, *The Lee–Yang and Pólya–Schur programs. I*, Theorem 1.2.
-/

namespace MvPolynomial

/-! ### The Appell operator lowers the top degree -/

section Degree

variable {R : Type*} [CommRing R] {σ : Type*}

/-- The polynomials all of whose monomials have total degree `< n`. -/
private noncomputable abbrev LowDeg (R : Type*) [CommRing R] (σ : Type*) (n : ℕ) :
    Submodule R (MvPolynomial σ R) :=
  restrictSupport R {γ : σ →₀ ℕ | γ.degree < n}

/-- The polynomials all of whose monomials have total degree `≤ n`. -/
private noncomputable abbrev LeDeg (R : Type*) [CommRing R] (σ : Type*) (n : ℕ) :
    Submodule R (MvPolynomial σ R) :=
  restrictSupport R {γ : σ →₀ ℕ | γ.degree ≤ n}

private lemma mem_lowDeg {n : ℕ} {P : MvPolynomial σ R} :
    P ∈ LowDeg R σ n ↔ ∀ γ ∈ P.support, γ.degree < n := by
  simp [mem_restrictSupport_iff, Set.subset_def]

private lemma mem_leDeg {n : ℕ} {P : MvPolynomial σ R} :
    P ∈ LeDeg R σ n ↔ ∀ γ ∈ P.support, γ.degree ≤ n := by
  simp [mem_restrictSupport_iff, Set.subset_def]

private lemma lowDeg_le_leDeg (n : ℕ) : LowDeg R σ n ≤ LeDeg R σ n :=
  restrictSupport_mono R fun _ h => le_of_lt (Set.mem_ofPred_eq ▸ h)

/-- The degree of a monomial of `P * Q` is the sum of the degrees of monomials of `P` and `Q`. -/
private lemma exists_degree_eq_of_mem_support_mul {P Q : MvPolynomial σ R} {γ : σ →₀ ℕ}
    (hγ : γ ∈ (P * Q).support) :
    ∃ a ∈ P.support, ∃ b ∈ Q.support, γ.degree = a.degree + b.degree := by
  classical
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.1 (support_mul P Q hγ)
  exact ⟨a, ha, b, hb, map_add _ _ _⟩

private lemma mul_mem_lowDeg {n m : ℕ} {P Q : MvPolynomial σ R} (hP : P ∈ LeDeg R σ n)
    (hQ : Q ∈ LowDeg R σ m) : P * Q ∈ LowDeg R σ (n + m) := by
  rw [mem_leDeg] at hP
  rw [mem_lowDeg] at hQ ⊢
  intro γ hγ
  obtain ⟨a, ha, b, hb, h⟩ := exists_degree_eq_of_mem_support_mul hγ
  exact h ▸ add_lt_add_of_le_of_lt (hP a ha) (hQ b hb)

private lemma mul_mem_lowDeg' {n m : ℕ} {P Q : MvPolynomial σ R} (hP : P ∈ LowDeg R σ n)
    (hQ : Q ∈ LeDeg R σ m) : P * Q ∈ LowDeg R σ (n + m) := by
  rw [mul_comm, add_comm]; exact mul_mem_lowDeg hQ hP

private lemma mul_mem_leDeg {n m : ℕ} {P Q : MvPolynomial σ R} (hP : P ∈ LeDeg R σ n)
    (hQ : Q ∈ LeDeg R σ m) : P * Q ∈ LeDeg R σ (n + m) := by
  rw [mem_leDeg] at hP hQ ⊢
  intro γ hγ
  obtain ⟨a, ha, b, hb, h⟩ := exists_degree_eq_of_mem_support_mul hγ
  exact h ▸ add_le_add (hP a ha) (hQ b hb)

private lemma monomial_mem_leDeg (γ : σ →₀ ℕ) (c : R) : monomial γ c ∈ LeDeg R σ γ.degree := by
  classical
  rw [mem_leDeg]
  intro δ hδ
  rw [Finset.mem_singleton.1 (support_monomial_subset hδ)]

private lemma X_pow_mem_leDeg (i : σ) (k : ℕ) : (X i ^ k : MvPolynomial σ R) ∈ LeDeg R σ k := by
  simp [X_pow_eq_monomial]

private lemma prod_mem_leDeg {ι : Type*} {f : ι → MvPolynomial σ R} {k : ι → ℕ} {s : Finset ι}
    (h : ∀ i ∈ s, f i ∈ LeDeg R σ (k i)) : ∏ i ∈ s, f i ∈ LeDeg R σ (∑ i ∈ s, k i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using monomial_mem_leDeg (R := R) (0 : σ →₀ ℕ) 1
  | insert a s ha ih =>
    rw [Finset.forall_mem_insert] at h
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact mul_mem_leDeg h.1 (ih h.2)

/-- The telescoping estimate: if each `f i` agrees with `g i` up to terms of degree `< k i`, and
`g i` has degree `≤ k i`, then `∏ f i` agrees with `∏ g i` up to terms of degree `< ∑ k i`. -/
private lemma prod_sub_prod_mem_lowDeg {ι : Type*} {f g : ι → MvPolynomial σ R} {k : ι → ℕ}
    {s : Finset ι} (hg : ∀ i ∈ s, g i ∈ LeDeg R σ (k i))
    (hfg : ∀ i ∈ s, f i - g i ∈ LowDeg R σ (k i)) :
    ∏ i ∈ s, f i - ∏ i ∈ s, g i ∈ LowDeg R σ (∑ i ∈ s, k i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.forall_mem_insert] at hg hfg
    have hf : f a ∈ LeDeg R σ (k a) := sub_add_cancel (f a) (g a) ▸
      add_mem (lowDeg_le_leDeg _ hfg.1) hg.1
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha,
      show f a * ∏ i ∈ s, f i - g a * ∏ i ∈ s, g i =
        f a * (∏ i ∈ s, f i - ∏ i ∈ s, g i) + (f a - g a) * ∏ i ∈ s, g i by ring]
    exact add_mem (mul_mem_lowDeg hf (ih hg.2 hfg.2)) (mul_mem_lowDeg' hfg.1 (prod_mem_leDeg hg.2))

/-- A univariate polynomial of degree `< k`, evaluated at `X i`, has all monomials of degree
`< k`. -/
private lemma aeval_X_mem_lowDeg (i : σ) {k : ℕ} {g : Polynomial R}
    (hg : g.degree < k) : Polynomial.aeval (X i : MvPolynomial σ R) g ∈ LowDeg R σ k := by
  classical
  rw [g.as_sum_support_C_mul_X_pow, map_sum]
  refine Submodule.sum_mem _ fun e he => ?_
  rw [map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X, algebraMap_eq,
    C_mul_X_pow_eq_monomial, mem_lowDeg]
  intro γ hγ
  rw [Finset.mem_singleton.1 (support_monomial_subset hγ), Finsupp.degree_single]
  exact_mod_cast (Polynomial.le_degree_of_ne_zero (Polynomial.mem_support_iff.1 he)).trans_lt hg

/-- `η_k(z_i) = z_i^k + (terms of degree < k)`. -/
private lemma signedAppell_sub_X_pow_mem_lowDeg (i : σ) (k : ℕ) :
    Polynomial.aeval (X i : MvPolynomial σ R) (Polynomial.signedAppell R k) - X i ^ k ∈
      LowDeg R σ k := by
  simpa using aeval_X_mem_lowDeg (σ := σ) i (Polynomial.degree_signedAppell_sub_X_pow_lt R k)

private lemma appellOperator_monomial_one (α : σ →₀ ℕ) :
    appellOperator R σ (monomial α 1) =
      ∏ i ∈ α.support, Polynomial.aeval (X i) (Polynomial.signedAppell R (α i)) := by
  rw [← congrFun (coe_basisMonomials σ R) α, appellOperator, Module.Basis.constr_basis]
  rfl

/-- The monomial case: `𝔄(z^α) - z^α` has all monomials of degree `< |α|`. -/
private lemma appellOperator_monomial_sub_mem_lowDeg (α : σ →₀ ℕ) :
    appellOperator R σ (monomial α 1) - monomial α 1 ∈ LowDeg R σ α.degree := by
  rw [appellOperator_monomial_one, monomial_eq, C_1, one_mul, Finsupp.prod, Finsupp.degree_apply]
  exact prod_sub_prod_mem_lowDeg (fun i _ => X_pow_mem_leDeg i (α i))
    fun i _ => signedAppell_sub_X_pow_mem_lowDeg i (α i)

end Degree

/-- If every `α ∈ supp F` has `|α| ≤ D`, then every `γ ∈ supp (𝔄(F) - F)` has `|γ| < D`. -/
@[lognarayana "lem_appell_operator_sub_degree"]
public theorem degree_lt_of_mem_support_appellOperator_sub {R : Type*} [CommRing R] {σ : Type*}
    {D : ℕ} {F : MvPolynomial σ R} (hF : ∀ α ∈ F.support, α.degree ≤ D) :
    ∀ γ ∈ (appellOperator R σ F - F).support, γ.degree < D := by
  rw [← mem_lowDeg, F.as_sum, map_sum, ← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun α hα => ?_
  have := Submodule.smul_mem _ (coeff α F)
    (restrictSupport_mono R (fun γ (h : γ.degree < α.degree) => (h.trans_le (hF α hα) : _))
      (appellOperator_monomial_sub_mem_lowDeg α))
  rwa [smul_sub, ← map_smul, smul_monomial, smul_eq_mul, mul_one] at this

/-- The Appell operator sends a nonzero polynomial to a nonzero polynomial. -/
@[lognarayana "lem_appell_operator_ne_zero"]
public theorem appellOperator_ne_zero {R : Type*} [CommRing R] {σ : Type*}
    {F : MvPolynomial σ R} (hF : F ≠ 0) : appellOperator R σ F ≠ 0 := by
  intro h0
  obtain ⟨α, hα, hmax⟩ :=
    F.support.exists_max_image Finsupp.degree (support_nonempty.mpr hF)
  have := (degree_lt_of_mem_support_appellOperator_sub hmax α).mt (lt_irrefl _)
  simp_all

/-! ### The symbol of the Appell operator -/

/-- The Appell operator on a monomial, as a product over all variables. -/
private lemma appellOperator_monomial_one_fintype {R σ : Type*} [CommRing R] [Fintype σ]
    (α : σ →₀ ℕ) :
    appellOperator R σ (monomial α 1) =
      ∏ i, Polynomial.aeval (X i) (Polynomial.signedAppell R (α i)) := by
  rw [← congrFun (coe_basisMonomials σ R) α, appellOperator, Module.Basis.constr_basis,
    Finsupp.prod_fintype _ _ (fun i => by simp [Polynomial.signedAppell])]

/-- The `α`-th term of the algebraic symbol of the Appell operator factors over the variables:
`(κ choose α) η^α(x) w^(κ - α) = ∏ᵢ (κᵢ choose αᵢ) η_{αᵢ}(xᵢ) wᵢ^(κᵢ - αᵢ)`. -/
private lemma symbol_term_appellOperator {R σ : Type*} [CommRing R] [Fintype σ]
    (κ α : σ →₀ ℕ) :
    C (κ.choose α : R) * rename Sum.inl (appellOperator R σ (monomial α 1)) *
        rename Sum.inr (monomial (κ - α) 1) =
      ∏ i, ((κ i).choose (α i) : MvPolynomial (σ ⊕ σ) R) *
        Polynomial.aeval (X (Sum.inl i)) (Polynomial.signedAppell R (α i)) *
          X (Sum.inr i) ^ (κ i - α i) := by
  rw [appellOperator_monomial_one_fintype, monomial_eq, C_1, one_mul,
    Finsupp.prod_fintype _ _ (fun i => pow_zero _), Finsupp.choose,
    Finsupp.prod_fintype _ _ (fun i => Nat.choose_zero_right _)]
  simp only [map_prod, map_pow, rename_X, Nat.cast_prod, Finset.prod_mul_distrib,
    ← Polynomial.aeval_algHom_apply, Finsupp.coe_tsub, Pi.sub_apply, map_natCast]

/-- The algebraic symbol of the Appell operator `𝔄_κ` factors:
`Sym_κ(𝔄_κ)(z, w) = ∏_{i ∈ σ} η_{κ_i}(z_i + w_i)`. -/
@[lognarayana "lem_appell_operator_symbol"]
public theorem algebraicSymbol_appellOperator {R σ : Type*} [CommRing R] [Fintype σ]
    (κ : σ →₀ ℕ) :
    algebraicSymbol κ ((appellOperator R σ).domRestrict (restrictSupport R (Set.Iic κ))) =
      ∏ i : σ, Polynomial.aeval (X (Sum.inl i) + X (Sum.inr i) : MvPolynomial (σ ⊕ σ) R)
        (Polynomial.signedAppell R (κ i)) := by
  classical
  simp only [Polynomial.aeval_add_signedAppell, Finset.prod_univ_sum, algebraicSymbol,
    LinearMap.domRestrict_apply]
  rw [Finset.sum_attach (Finset.Iic κ) (fun α => C (κ.choose α : R) *
    rename Sum.inl (appellOperator R σ (monomial α 1)) * rename Sum.inr (monomial (κ - α) 1))]
  refine Finset.sum_nbij' (⇑) Finsupp.equivFunOnFinite.symm ?_ ?_ (by simp) (by simp)
    (fun α _ => symbol_term_appellOperator κ α)
  · intro α hα
    simp only [Finset.mem_Iic, Fintype.mem_piFinset, Finset.mem_range] at hα ⊢
    exact fun i => Nat.lt_succ_of_le (hα i)
  · intro x hx
    simp only [Finset.mem_Iic, Fintype.mem_piFinset, Finset.mem_range] at hx ⊢
    exact fun i => by simpa using Nat.le_of_lt_succ (hx i)

/-! ### Real stability -/

/-- A nonzero real-rooted real polynomial has only real complex roots. -/
private lemma im_eq_zero_of_aeval_eq_zero {p : Polynomial ℝ} (hp : p.Splits) (hp0 : p ≠ 0)
    {z : ℂ} (hz : Polynomial.aeval z p = 0) : z.im = 0 := by
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map] at hz
  obtain ⟨x, rfl⟩ := hp.mem_range_of_isRoot hp0 (i := algebraMap ℝ ℂ) hz
  simp

/-- `η_m` is nonzero, since `η_m - X ^ m` has degree below `m`. -/
private lemma signedAppell_ne_zero (m : ℕ) : Polynomial.signedAppell ℝ m ≠ 0 := by
  intro h0
  have h := Polynomial.degree_signedAppell_sub_X_pow_lt ℝ m
  rw [h0, zero_sub, Polynomial.degree_neg, Polynomial.degree_X_pow] at h
  exact lt_irrefl _ h

/-- For every `i ∈ σ` and `m ≥ 0`, the polynomial `η_m(z_i + w_i)` in the variables
`z_j = X (Sum.inl j)`, `w_j = X (Sum.inr j)` is real-stable. -/
@[lognarayana "lem_signed_appell_shift_real_stable"]
public theorem isRealStable_aeval_signedAppell
    (hLW : ShiftedNarayanaNegRealRoots) {σ : Type*} (i : σ) (m : ℕ) :
    IsRealStable (Polynomial.aeval (X (Sum.inl i) + X (Sum.inr i) : MvPolynomial (σ ⊕ σ) ℝ)
      (Polynomial.signedAppell ℝ m)) := by
  intro ζ hζ hzero
  have him := im_eq_zero_of_aeval_eq_zero (Polynomial.splits_signedAppell hLW m)
    (signedAppell_ne_zero m) (z := ζ (Sum.inl i) + ζ (Sum.inr i))
    (by simpa [← Polynomial.aeval_algHom_apply] using hzero)
  rw [Complex.add_im] at him
  linarith [hζ (Sum.inl i), hζ (Sum.inr i)]

/-- For a finite set `σ` and `κ : σ →₀ ℕ`, the algebraic symbol `Sym_κ(𝔄_κ)(z, w)` of the
Appell operator `𝔄_κ` is real-stable. -/
@[lognarayana "lem_appell_symbol_real_stable"]
public theorem isRealStable_algebraicSymbol_appellOperator
    (hLW : ShiftedNarayanaNegRealRoots) {σ : Type*} [Finite σ]
    (κ : σ →₀ ℕ) :
    IsRealStable
      (algebraicSymbol κ ((appellOperator ℝ σ).domRestrict (restrictSupport ℝ (Set.Iic κ)))) := by
  have := Fintype.ofFinite σ
  intro ζ hζ
  rw [algebraicSymbol_appellOperator, map_prod]
  exact Finset.prod_ne_zero_iff.mpr fun i _ =>
    isRealStable_aeval_signedAppell hLW i (κ i) ζ hζ

/-- A real stable polynomial is nonzero: the zero polynomial vanishes at `(i, …, i)`. -/
private lemma ne_zero_of_isRealStable {σ : Type*} {F : MvPolynomial σ ℝ} (hF : F.IsRealStable) :
    F ≠ 0 := by
  rintro rfl
  exact hF (fun _ => Complex.I) (fun _ => by simp) (by simp)

/-- Every polynomial lies in `restrictSupport (Iic κ)` for `κ i = degreeOf i F`. -/
private lemma mem_restrictSupport_degreeOf {σ : Type*} [Finite σ] (F : MvPolynomial σ ℝ) :
    F ∈ restrictSupport ℝ (Set.Iic (Finsupp.equivFunOnFinite.symm fun i => degreeOf i F)) :=
  (mem_restrictSupport_iff ..).2 fun _ hm i => by simpa using monomial_le_degreeOf i hm

/-- For a finite set `σ`, the Appell operator `𝔄` preserves real stability: if
`F ∈ ℝ[z_i : i ∈ σ]` is real-stable, so is `𝔄(F)`. -/
@[lognarayana "prop_appell_operator_real_stable"]
public theorem isRealStable_appellOperator
    (hLW : ShiftedNarayanaNegRealRoots) {σ : Type*} [Finite σ]
    (hBB : RealStablePreserverOfSymbol σ) {F : MvPolynomial σ ℝ} (hF : F.IsRealStable) :
    (appellOperator ℝ σ F).IsRealStable :=
  (MvPolynomial.RealStablePreserverOfSymbol.apply hBB _ _
    (isRealStable_algebraicSymbol_appellOperator hLW _)
    ⟨F, mem_restrictSupport_degreeOf F⟩ hF).resolve_left
    (appellOperator_ne_zero (ne_zero_of_isRealStable hF))

end MvPolynomial
