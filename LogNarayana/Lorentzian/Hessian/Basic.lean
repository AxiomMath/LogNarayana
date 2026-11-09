/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module
public import LogNarayana.Lorentzian.Hessian.Defs
public import LogNarayana.Lorentzian.PositiveIndex.Basic

/-!
# Hessians and Lorentzian polynomials

Elementary facts about the Hessian at the origin `Hess(h) = (∂_p ∂_q h (0))_{p,q}` of a
polynomial and about Lorentzian polynomials in low degree.

The Hessian at the origin of a derivative `∂^α h` has entries
`Hess(∂^α h)_{pq} = (α + e_p + e_q)! · [z^(α + e_p + e_q)] h`. Polynomials with nonnegative
coefficients that are homogeneous of degree `0` or `1` are Lorentzian, and so are nonnegative
multiples of Lorentzian polynomials.

In degree two the Hessian condition carries everything. If `A` is a real symmetric matrix with
nonnegative diagonal and at most one positive eigenvalue, `uᵀ A u > 0` and `(A u)_j = 0`, then
row `j` of `A` vanishes. Applied to the Hessian of a nonzero quadratic form `g` with
nonnegative coefficients, this shows that the support of `g` is M-convex as soon as `Hess(g)`
has at most one positive eigenvalue; hence such a `g` is Lorentzian iff `Hess(g)` has at most
one positive eigenvalue.

## Main results

* `MvPolynomial.hessianAtZero_iteratedPDeriv_apply`: the entries of `Hess(∂^α h)`.
* `MvPolynomial.hessianAtZero_apply_eq_constantCoeff_pderiv_pderiv`:
  `Hess(g)_{ij} = ∂_j ∂_i g (0)`.
* `MvPolynomial.IsLorentzian.of_isHomogeneous_of_le_one`: a homogeneous polynomial of degree
  `d ≤ 1` with nonnegative coefficients is Lorentzian.
* `Matrix.apply_eq_zero_of_mulVec_apply_eq_zero`: rows annihilated by a positive vector vanish.
* `MvPolynomial.isMConvex_support_of_isHomogeneous_two`: a nonzero quadratic form with
  nonnegative coefficients whose Hessian has at most one positive eigenvalue has M-convex
  support.
* `MvPolynomial.isLorentzian_iff_hasAtMostOnePosEigenvalue_of_isHomogeneous_two`: a quadratic
  form with nonnegative coefficients is Lorentzian iff its Hessian has at most one positive
  eigenvalue.
* `MvPolynomial.IsLorentzian.smul`: a nonnegative multiple of a Lorentzian polynomial is
  Lorentzian.

## Implementation notes

The paper works over `ℝ`. The Hessian formula is stated over any commutative semiring, the
degree-at-most-one lemma over any partially ordered commutative ring, and the scaling lemma over
any linearly ordered field. The paper compares the positive indices of `c A` and `A` through
the congruence by `√c · I`; since `√c` need not exist over a general ordered field, the equality
`(c • A).posIndex = A.posIndex` for `c > 0` is proved directly: `c • A` and `A` have the same
positive subspaces.

For the Hessian formula, the paper composes `∂^(e_p + e_q) ∂^α = ∂^(α + e_p + e_q)`; here the
coefficient formula `[z^β] ∂^α h = ((β + α)! / β!) · [z^(β + α)] h` is applied twice instead.

## References

* [BH] P. Brändén, J. Huh, *Lorentzian polynomials*, Ann. of Math. 192 (2020).
* [LogNarayana]
-/

open Finsupp (single)
open scoped Matrix

/-! ### Real matrices with at most one positive eigenvalue -/

namespace Matrix

/-- If `a > 0`, `x, y ≥ 0` and `a (x + 2 t h + t² y) ≤ (t q)²` for every real `t`, then
`h = 0`: at `t = c h` with `c = a / (q² + 1)` the inequality would give `2 a ≤ c q² < a`. -/
private lemma eq_zero_of_forall_mul_quadratic_le_sq {a x y h q : ℝ} (ha : 0 < a) (hx : 0 ≤ x)
    (hy : 0 ≤ y) (H : ∀ t : ℝ, a * (x + 2 * t * h + t ^ 2 * y) ≤ (t * q) ^ 2) : h = 0 := by
  by_contra hh
  have hq : 0 < q ^ 2 + 1 := by positivity
  set c := a / (q ^ 2 + 1)
  have hc : 0 < c := div_pos ha hq
  have hcq : c * q ^ 2 < a := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ hq]; nlinarith
  have h1 := H (c * h)
  have h2 : (2 * a) * (c * h ^ 2) ≤ (c * q ^ 2) * (c * h ^ 2) := by
    nlinarith [mul_nonneg ha.le hx, mul_nonneg ha.le (mul_nonneg (sq_nonneg (c * h)) hy)]
  linarith [le_of_mul_le_mul_right h2 (by positivity)]

variable {σ : Type*} [Fintype σ]

/-- For symmetric `A`, `uᵀ A w = (A u) ⬝ᵥ w`. -/
private lemma dotProduct_mulVec_of_isSymm {A : Matrix σ σ ℝ} (hA : A.IsSymm) (u w : σ → ℝ) :
    u ⬝ᵥ A *ᵥ w = (A *ᵥ u) ⬝ᵥ w := by
  rw [dotProduct_mulVec, ← hA.eq, vecMul_transpose, hA.eq]

/-- If `A` is a real symmetric matrix with nonnegative diagonal and at most one positive
eigenvalue, `u ⬝ᵥ A *ᵥ u > 0`, and `(A *ᵥ u) j = 0`, then the row `j` of `A` is zero.

The reverse Cauchy–Schwarz inequality tested on `v = e_j + t e_m` gives
`a (A_jj + 2 t A_jm + t² A_mm) ≤ (t q)²` for every real `t`, with `a = uᵀ A u` and
`q = (A u)_m`, which forces `A_jm = 0`. -/
@[lognarayana "lem_quadratic_zero_row"]
public theorem apply_eq_zero_of_mulVec_apply_eq_zero {A : Matrix σ σ ℝ} (hA : A.IsSymm)
    (hdiag : ∀ i, 0 ≤ A i i) (hpos : A.HasAtMostOnePosEigenvalue) {u : σ → ℝ}
    (hu : 0 < u ⬝ᵥ A *ᵥ u) {j : σ} (hj : (A *ᵥ u) j = 0) (m : σ) : A j m = 0 := by
  classical
  refine eq_zero_of_forall_mul_quadratic_le_sq hu (hdiag j) (hdiag m)
    (q := (A *ᵥ u) m) fun t => ?_
  have key := hpos.mul_le_sq_dotProduct_mulVec hA hu (Pi.single j 1 + t • Pi.single m 1)
  have hsym : A m j = A j m := by simpa using congrFun (congrFun hA j) m
  rw [dotProduct_mulVec_of_isSymm hA u (_ + _)] at key
  convert key using 2
  · simp [mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, hsym]; ring
  · simp [dotProduct_add, hj]

/-- The zero matrix has positive index `0`. -/
private lemma posIndex_zero {R : Type*} [CommRing R] [Nontrivial R] [PartialOrder R] :
    (0 : Matrix σ σ R).posIndex = 0 := by
  refine Nat.eq_zero_of_le_zero (csSup_le' ?_)
  rintro n ⟨W, hW, rfl⟩
  obtain rfl : W = ⊥ :=
    (Submodule.eq_bot_iff W).2 fun v hv => by_contra fun hv0 => by simpa using hW v hv hv0
  exact (finrank_bot R (σ → R)).le

/-- A positive multiple of a matrix has the same positive index: `c • A` and `A` have the same
positive subspaces. -/
private lemma posIndex_smul {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (A : Matrix σ σ R) {c : R} (hc : 0 < c) : (c • A).posIndex = A.posIndex := by
  simp only [Matrix.posIndex, Matrix.IsPositiveSubspace, smul_mulVec, dotProduct_smul,
    smul_eq_mul, mul_pos_iff_of_pos_left hc]

end Matrix

namespace MvPolynomial

/-! ### The Hessian at the origin of a derivative -/

section CommSemiring

variable {σ R : Type*} [CommSemiring R]

private lemma factorial_pos (β : σ →₀ ℕ) : 0 < β.factorial :=
  Finset.prod_pos fun _ _ => Nat.factorial_pos _

private lemma factorial_dvd_factorial {α β : σ →₀ ℕ} (h : α ≤ β) :
    α.factorial ∣ β.factorial := by
  classical
  unfold Finsupp.factorial
  rw [Finsupp.prod_of_support_subset α (Finsupp.support_mono h) _ (fun _ _ => rfl)]
  exact Finset.prod_dvd_prod_of_dvd _ _ fun i _ => Nat.factorial_dvd_factorial (h i)

private lemma iteratedPDeriv_monomial' (α δ : σ →₀ ℕ) (c : R) :
    iteratedPDeriv α (monomial δ c) =
      monomial (δ - α)
        (c * if α ≤ δ then ((δ.factorial / (δ - α).factorial : ℕ) : R) else 0) := by
  have : monomial δ c = c • (basisMonomials σ R) δ := by
    simp [basisMonomials]; rfl
  rw [this, map_smul, iteratedPDeriv, Module.Basis.constr_basis, smul_monomial, smul_eq_mul]

/-- `[z^β] ∂^α h = ((β + α)! / β!) · [z^(β + α)] h`. -/
private lemma coeff_iteratedPDeriv (α β : σ →₀ ℕ) (h : MvPolynomial σ R) :
    coeff β (iteratedPDeriv α h) =
      (((β + α).factorial / β.factorial : ℕ) : R) * coeff (β + α) h := by
  classical
  induction h using MvPolynomial.induction_on' with
  | monomial δ c =>
    rw [iteratedPDeriv_monomial', coeff_monomial, coeff_monomial]
    by_cases hd : δ = β + α
    · subst hd
      simp [mul_comm]
    · rw [if_neg hd, mul_zero]
      by_cases hle : α ≤ δ
      · rw [if_neg]
        rintro rfl
        exact hd (tsub_add_cancel_of_le hle).symm
      · simp [hle]
  | add p q hp hq => simp [hp, hq, mul_add]

/-- `∂^0` is the identity. -/
@[simp]
public lemma iteratedPDeriv_zero_apply (g : MvPolynomial σ R) : iteratedPDeriv 0 g = g := by
  suffices H : (iteratedPDeriv 0 : MvPolynomial σ R →ₗ[R] _) = LinearMap.id by
    rw [H]; rfl
  refine (basisMonomials σ R).ext fun β => ?_
  rw [iteratedPDeriv, Module.Basis.constr_basis]
  simp [coe_basisMonomials, Nat.div_self (factorial_pos β)]

/-- The `(i, j)` entry of the Hessian at the origin is the constant term of `∂_j ∂_i g`. -/
public lemma hessianAtZero_apply_eq_constantCoeff_pderiv_pderiv (g : MvPolynomial σ R)
    (i j : σ) : hessianAtZero g i j = constantCoeff (pderiv j (pderiv i g)) := by
  rw [hessianAtZero, Matrix.of_apply, ← zero_add (single i 1), iteratedPDeriv_add_single,
    iteratedPDeriv_add_single, iteratedPDeriv_zero_apply]

/-- The `(p, q)` entry of the Hessian at the origin of `∂^α h` is
`(α + e_p + e_q)! · [z^(α + e_p + e_q)] h`. -/
@[lognarayana "lem_hessian_derivative_entries"]
public theorem hessianAtZero_iteratedPDeriv_apply (h : MvPolynomial σ R) (α : σ →₀ ℕ)
    (p q : σ) :
    hessianAtZero (iteratedPDeriv α h) p q =
      ((α + Finsupp.single p 1 + Finsupp.single q 1).factorial : R) *
        coeff (α + Finsupp.single p 1 + Finsupp.single q 1) h := by
  have hγ : α + single p 1 + single q 1 = (single p 1 + single q 1) + α := by abel
  have h0 : Finsupp.factorial (0 : σ →₀ ℕ) = 1 := by simp [Finsupp.factorial]
  rw [hγ, hessianAtZero, Matrix.of_apply, constantCoeff_eq, coeff_iteratedPDeriv,
    coeff_iteratedPDeriv, zero_add, h0, Nat.div_one, ← mul_assoc, ← Nat.cast_mul,
    Nat.mul_div_cancel' (factorial_dvd_factorial le_self_add)]

/-- The Hessian entries of `g` are `H p q = (e_p + e_q)! · [z^(e_p + e_q)] g`. -/
private lemma hessianAtZero_apply_eq (g : MvPolynomial σ R) (p q : σ) :
    hessianAtZero g p q =
      ((single p 1 + single q 1 : σ →₀ ℕ).factorial : R) * coeff (single p 1 + single q 1) g := by
  simpa [iteratedPDeriv_zero_apply] using hessianAtZero_iteratedPDeriv_apply g 0 p q

/-- The Hessian at the origin of the zero polynomial is the zero matrix. -/
private lemma hessianAtZero_zero : hessianAtZero (0 : MvPolynomial σ R) = 0 := by
  ext i j; simp [hessianAtZero]

/-- The Hessian at the origin commutes with scalar multiplication. -/
private lemma hessianAtZero_smul (c : R) (g : MvPolynomial σ R) :
    hessianAtZero (c • g) = c • hessianAtZero g := by
  ext i j; simp [hessianAtZero]

end CommSemiring

/-! ### Lorentzian polynomials of degree at most one -/

/-- A polynomial with nonnegative coefficients that is homogeneous of degree `d ≤ 1` (so the
zero polynomial, a nonnegative constant, or a linear form with nonnegative coefficients) is
Lorentzian: these are the clauses of the `d ≤ 1` branch of the definition. -/
@[lognarayana "lem_lorentzian_linear"]
public theorem IsLorentzian.of_isHomogeneous_of_le_one {σ R : Type*} [Fintype σ] [CommRing R]
    [PartialOrder R] {f : MvPolynomial σ R} {d : ℕ}
    (hf : f.HasNonnegCoeffs) (hd : f.IsHomogeneous d) (hd1 : d ≤ 1) : f.IsLorentzian :=
  Or.inr ⟨_, hd, hf, Or.inl hd1⟩

/-! ### Quadratic forms -/

section Quadratic

variable {σ : Type*} [Fintype σ]

omit [Fintype σ] in
/-- A multi-index of degree `2` with `α i ≥ 1` is `e_i + e_a` for some `a`. -/
private lemma exists_eq_single_add_single {α : σ →₀ ℕ} (hα : α.degree = 2)
    {i : σ} (hi : 1 ≤ α i) : ∃ a, α = single i 1 + single a 1 := by
  have hle : single i 1 ≤ α := Finsupp.single_le_iff.mpr hi
  have hα' : α = single i 1 + (α - single i 1) := (add_tsub_cancel_of_le hle).symm
  have hdeg : (α - single i 1).degree = 1 := by
    have := congrArg Finsupp.degree hα'
    rw [map_add, Finsupp.degree_single] at this
    omega
  obtain ⟨a, ha⟩ : (α - single i 1) ∈ Set.range (fun a : σ ↦ single a 1) := by
    rw [Finsupp.range_single_one]
    exact hdeg
  exact ⟨a, hα'.trans (by rw [← ha])⟩

omit [Fintype σ] in
/-- A multi-index `β` of degree `2` is `e_k + e_l` for some `k, l`. -/
private lemma exists_eq_single_add_single' {β : σ →₀ ℕ} (hβ : β.degree = 2) :
    ∃ k l, β = single k 1 + single l 1 := by
  obtain ⟨k, hk⟩ := Finsupp.ne_iff.mp (show β ≠ 0 by rintro rfl; simp at hβ)
  exact ⟨k, exists_eq_single_add_single hβ (Nat.one_le_iff_ne_zero.mpr hk)⟩

omit [Fintype σ] in
/-- The symmetric exchange step: if membership of `e_p + e_q` in `J` is a symmetric relation
`P p q` such that `P i a` and `P j m` force `P i j ∨ P a j`, then any two elements
`e_i + e_a`, `e_k + e_l` of `J` with `(e_k + e_l) i < (e_i + e_a) i` admit an exchange. -/
private lemma exchange_of_rel (J : Set (σ →₀ ℕ)) (P : σ → σ → Prop)
    (hP : ∀ p q, single p 1 + single q 1 ∈ J ↔ P p q)
    (hsymm : ∀ p q, P p q → P q p)
    (step1 : ∀ i a j m, P i a → P j m → P i j ∨ P a j) {i a k l : σ}
    (hα : P i a) (hβ : P k l)
    (hi : (single k 1 + single l 1 : σ →₀ ℕ) i <
      (single i 1 + single a 1 : σ →₀ ℕ) i) :
    ∃ j, (single i 1 + single a 1 : σ →₀ ℕ) j <
        (single k 1 + single l 1 : σ →₀ ℕ) j ∧
      single i 1 + single a 1 - single i 1 + single j 1 ∈ J ∧
      single k 1 + single l 1 - single j 1 + single i 1 ∈ J := by
  classical
  have hjl : (single i 1 + single a 1 : σ →₀ ℕ) l <
      (single k 1 + single l 1 : σ →₀ ℕ) l → P a l → P k i →
        ∃ j, (single i 1 + single a 1 : σ →₀ ℕ) j <
            (single k 1 + single l 1 : σ →₀ ℕ) j ∧
          single i 1 + single a 1 - single i 1 + single j 1 ∈ J ∧
          single k 1 + single l 1 - single j 1 + single i 1 ∈ J := by
    intro h1 h2 h3
    refine ⟨l, h1, ?_, ?_⟩
    · rwa [add_tsub_cancel_left, hP]
    · rwa [add_tsub_cancel_right, hP]
  have hjk : (single i 1 + single a 1 : σ →₀ ℕ) k <
      (single k 1 + single l 1 : σ →₀ ℕ) k → P a k → P l i →
        ∃ j, (single i 1 + single a 1 : σ →₀ ℕ) j <
            (single k 1 + single l 1 : σ →₀ ℕ) j ∧
          single i 1 + single a 1 - single i 1 + single j 1 ∈ J ∧
          single k 1 + single l 1 - single j 1 + single i 1 ∈ J := by
    intro h1 h2 h3
    refine ⟨k, h1, ?_, ?_⟩
    · rwa [add_tsub_cancel_left, hP]
    · rwa [add_tsub_cancel_left, hP]
  have ev : ∀ p q x : σ, (single p 1 + single q 1 : σ →₀ ℕ) x =
      (if p = x then 1 else 0) + (if q = x then 1 else 0) := fun p q x => by
    simp [Finsupp.single_apply]
  by_cases hak : a = k
  · subst hak
    have hli : l ≠ i := by
      rintro rfl
      simp [ev] at hi; omega
    exact hjl (by simp [ev, Ne.symm hli]) hβ (hsymm _ _ hα)
  by_cases hal : a = l
  · subst hal
    have hki : k ≠ i := by
      rintro rfl
      simp [ev] at hi
    exact hjk (by simp [ev, Ne.symm hki]) (hsymm _ _ hβ) (hsymm _ _ hα)
  have hki : k ≠ i := by
    rintro rfl
    by_cases hlk : l = k <;> simp [ev, hak, hlk] at hi
  have hli : l ≠ i := by
    rintro rfl
    by_cases hkl : k = l <;> simp [ev, hal, hkl] at hi
  have ek : (single i 1 + single a 1 : σ →₀ ℕ) k <
      (single k 1 + single l 1 : σ →₀ ℕ) k := by
    simp [ev, Ne.symm hki, hak]
  have el : (single i 1 + single a 1 : σ →₀ ℕ) l <
      (single k 1 + single l 1 : σ →₀ ℕ) l := by
    simp [ev, Ne.symm hli, hal]
  by_cases hAK : P a k
  · by_cases hIL : P i l
    · exact hjk ek hAK (hsymm _ _ hIL)
    · exact hjl el ((step1 i a l k hα (hsymm _ _ hβ)).resolve_left hIL)
        ((step1 k l i a hβ hα).resolve_right fun h => hIL (hsymm _ _ h))
  · exact hjl el
      (hsymm _ _ ((step1 k l a i hβ (hsymm _ _ hα)).resolve_left fun h => hAK (hsymm _ _ h)))
      (hsymm _ _ ((step1 i a k l hα hβ).resolve_right hAK))

/-- Let `H` be a real symmetric matrix with nonnegative entries and at most one positive
eigenvalue. If `H i a > 0` and row `j` of `H` is nonzero, then `H i j > 0` or `H a j > 0`:
otherwise `u = e_i + e_a` has `uᵀ H u > 0` and `(H u)_j = 0`, which kills row `j`. -/
private lemma pos_or_pos_of_pos {H : Matrix σ σ ℝ}
    (hS : H.IsSymm) (hnnH : ∀ p q, 0 ≤ H p q) (hH : H.HasAtMostOnePosEigenvalue)
    {i a j m : σ} (hia : 0 < H i a) (hjm : 0 < H j m) : 0 < H i j ∨ 0 < H a j := by
  classical
  by_contra hcon
  push Not at hcon
  have hij : H i j = 0 := le_antisymm hcon.1 (hnnH _ _)
  have haj : H a j = 0 := le_antisymm hcon.2 (hnnH _ _)
  set u : σ → ℝ := Pi.single i 1 + Pi.single a 1
  have hu : 0 < u ⬝ᵥ H *ᵥ u := by
    have : u ⬝ᵥ H *ᵥ u = H i i + H i a + (H a i + H a a) := by
      simp [u, Matrix.mulVec_add, dotProduct_add, add_dotProduct]
      ring
    rw [this]
    linarith [hnnH i i, hnnH a a, hnnH a i]
  have hj : (H *ᵥ u) j = 0 := by
    have : (H *ᵥ u) j = H j i + H j a := by simp [u, Matrix.mulVec_add]
    rw [this, hS.apply i j, hS.apply a j, hij, haj, add_zero]
  have := Matrix.apply_eq_zero_of_mulVec_apply_eq_zero hS (fun p => hnnH p p) hH hu hj m
  linarith

/-- A nonzero quadratic form with nonnegative coefficients whose Hessian has at most one
positive eigenvalue has M-convex support.

The Hessian entries `H p q = (e_p + e_q)! · [z^(e_p + e_q)] g` are nonnegative, and positive
exactly when `e_p + e_q` lies in the support; every element of the support has this form. The
exchange property then follows from `Matrix.apply_eq_zero_of_mulVec_apply_eq_zero` by a case
analysis on the indices. -/
@[lognarayana "lem_quadratic_support_mconvex"]
public theorem isMConvex_support_of_isHomogeneous_two {g : MvPolynomial σ ℝ} (hg0 : g ≠ 0)
    (hg : g.IsHomogeneous 2) (hnn : g.HasNonnegCoeffs)
    (hH : (hessianAtZero g).HasAtMostOnePosEigenvalue) :
    (↑g.support : Set (σ →₀ ℕ)).IsMConvex := by
  classical
  have hfac : ∀ p q, (0 : ℝ) < ((single p 1 + single q 1 : σ →₀ ℕ).factorial : ℝ) :=
    fun p q => Nat.cast_pos.mpr (factorial_pos _)
  have hmem : ∀ p q, single p 1 + single q 1 ∈ (↑g.support : Set (σ →₀ ℕ)) ↔
      0 < hessianAtZero g p q := by
    intro p q
    rw [Finset.mem_coe, mem_support_iff, hessianAtZero_apply_eq,
      mul_pos_iff_of_pos_left (hfac p q)]
    exact ⟨fun h => lt_of_le_of_ne (hnn _) (Ne.symm h), fun h => h.ne'⟩
  have hnnH : ∀ p q, 0 ≤ hessianAtZero g p q := fun p q => by
    rw [hessianAtZero_apply_eq]
    exact mul_nonneg (hfac p q).le (hnn _)
  have hsymm : ∀ p q, 0 < hessianAtZero g p q → 0 < hessianAtZero g q p := fun p q h => by
    rwa [hessianAtZero_apply_eq, add_comm, ← hessianAtZero_apply_eq]
  have hS : (hessianAtZero g).IsSymm := Matrix.IsSymm.ext fun p q => by
    rw [hessianAtZero_apply_eq, hessianAtZero_apply_eq, add_comm]
  have hdeg : ∀ α ∈ g.support, α.degree = 2 := fun α h => by
    rw [Finsupp.degree_eq_weight_one]
    exact hg (mem_support_iff.mp h)
  refine ⟨g.support.finite_toSet, ?_, ⟨2, hdeg⟩, ?_⟩
  · simpa [Finset.coe_nonempty, Finset.nonempty_iff_ne_empty] using hg0
  intro α hα β hβ i hi
  obtain ⟨a, rfl⟩ := exists_eq_single_add_single (hdeg α hα) (i := i) (by omega)
  obtain ⟨k, l, rfl⟩ := exists_eq_single_add_single' (hdeg β hβ)
  rw [hmem] at hα hβ
  exact exchange_of_rel _ _ hmem hsymm (fun _ _ _ _ => pos_or_pos_of_pos hS hnnH hH) hα hβ hi

/-- A homogeneous quadratic polynomial with nonnegative coefficients is Lorentzian if and only if
its Hessian has at most one positive eigenvalue. The M-convexity of the support required by the
definition is `isMConvex_support_of_isHomogeneous_two`. -/
@[lognarayana "lem_lorentzian_quadratic_iff"]
public theorem isLorentzian_iff_hasAtMostOnePosEigenvalue_of_isHomogeneous_two
    {g : MvPolynomial σ ℝ} (hg : g.IsHomogeneous 2) (hnn : g.HasNonnegCoeffs) :
    g.IsLorentzian ↔ (hessianAtZero g).HasAtMostOnePosEigenvalue := by
  by_cases hg0 : g = 0
  · subst hg0
    simp [IsLorentzian, Matrix.HasAtMostOnePosEigenvalue, hessianAtZero_zero,
      Matrix.posIndex_zero]
  constructor
  · rintro (h | ⟨d, hd, -, hd1 | ⟨-, -, hH⟩⟩)
    · exact absurd h hg0
    · have := hg.inj_right hd hg0
      omega
    · have h2 : d = 2 := (hg.inj_right hd hg0).symm
      simpa [iteratedPDeriv_zero_apply] using hH 0 (by simp [h2])
  · intro hH
    refine Or.inr ⟨2, hg, hnn, Or.inr ⟨le_rfl,
      isMConvex_support_of_isHomogeneous_two hg0 hg hnn hH, fun α hα => ?_⟩⟩
    obtain rfl := (Finsupp.degree_eq_zero_iff α).1 hα
    simpa [iteratedPDeriv_zero_apply] using hH

end Quadratic

/-! ### Nonnegative multiples -/

/-- A nonnegative scalar multiple of a Lorentzian polynomial is Lorentzian. For `c > 0`, `c • f`
has the same degree, sign pattern and support as `f`, and
`Hess(∂^α (c • f)) = c • Hess(∂^α f)` has the same positive index. -/
@[lognarayana "lem_lorentzian_smul"]
public theorem IsLorentzian.smul {σ R : Type*} [Fintype σ] [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] {f : MvPolynomial σ R} (hf : f.IsLorentzian) {c : R}
    (hc : 0 ≤ c) : (c • f).IsLorentzian := by
  rcases hc.eq_or_lt with rfl | hc
  · exact Or.inl (zero_smul _ _)
  rcases hf with rfl | ⟨d, hd, hnn, hcase⟩
  · exact Or.inl (smul_zero _)
  refine Or.inr ⟨d, ?_, fun α => ?_, hcase.imp_right fun ⟨h2, hM, hH⟩ => ⟨h2, ?_, fun α hα => ?_⟩⟩
  · simpa [smul_eq_C_mul] using (isHomogeneous_C σ c).mul hd
  · simpa [coeff_smul] using mul_nonneg hc.le (hnn α)
  · rwa [support_smul_eq hc.ne']
  · simpa [map_smul, hessianAtZero_smul, Matrix.posIndex_smul _ hc] using hH α hα

end MvPolynomial
