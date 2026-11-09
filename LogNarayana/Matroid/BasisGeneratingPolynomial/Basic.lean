/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module
public import LogNarayana.Matroid.BasisGeneratingPolynomial.Defs
public import LogNarayana.Lorentzian.Symbol.Basic

/-!
# Matroid basis generating polynomials

For a matroid `M` on a finite set `E`, the basis generating polynomial
`B_M = ∑_{B base of M} ∏_{e ∈ B} z_e` is Lorentzian. The argument runs in three steps.

* Symmetric basis exchange: for bases `B₁, B₂` and `e ∈ B₁ \ B₂` there is `f ∈ B₂ \ B₁` such that
  both `insert f (B₁ \ {e})` and `insert e (B₂ \ {f})` are bases. This strengthens Mathlib's
  `Matroid.IsBase.exchange`, which provides only the first of the two bases. The proof intersects
  the fundamental circuit of `e` with respect to `B₂` with the fundamental cocircuit of `e` with
  respect to `B₁`; a circuit and a cocircuit never meet in exactly one element.
* The indicator vectors `𝟏_B = ∑_{e ∈ B} e_e` of the bases form an M-convex set: finitely many,
  at least one, all of degree the rank of `M`, and the exchange axiom is symmetric basis exchange.
* `B_M` is the normalized support polynomial `E_J` of that set `J` (each `𝟏_B` is a `0/1` vector,
  so its factorial is `1`), and the Brändén–Huh theorem on normalized support polynomials of
  M-convex sets shows that it is Lorentzian.

## Main results

* `Matroid.IsBase.symmetric_exchange`: the symmetric basis exchange property.
* `Matroid.isMConvex_setOf_indicator_isBase`: the indicator vectors of the bases of a finite
  matroid form an M-convex set.
* `Matroid.isLorentzian_basisGeneratingPolynomial`: `B_M` is Lorentzian.

## Implementation notes

The paper states symmetric exchange for a matroid on a finite ground set; it is proved here for
an arbitrary `M : Matroid α`, which is a generalization.

Multi-indices are indexed by the ambient type `α` of the matroid rather than by its ground set
`E`; every indicator vector `𝟏_B` is supported in `E`, so this is the paper's set
`{𝟏_B} ⊆ ℤ_{≥0}^E` extended by zero, and M-convexity does not see the extension. The finiteness
of `E` is the instance `M.Finite`; bases are then finite and are written as `Finset`s, and the
indicator vector of `B` is `∑ e ∈ B, Finsupp.single e 1`.

The Brändén–Huh theorem [BH, Theorem 3.10] is cited, not proved here; it enters as the
hypothesis `MvPolynomial.NormalizedSupportPolyLorentzianOfMConvex α` for the variable type `α`
of the matroid. The polynomial is taken over `ℝ`, the paper's scalars.

## References

* [LogNarayana], Section 2.
* [BH] P. Brändén, J. Huh, *Lorentzian polynomials*, Ann. of Math. 192 (2020), Theorem 3.10.
-/

open Finsupp MvPolynomial

namespace Matroid

section SymmetricExchange

variable {α : Type*} {M : Matroid α} {B₁ B₂ : Set α} {e : α}

/-- Exchanging a base `B` along the fundamental circuit of `y ∉ B`: removing any other element
`x` of `M.fundCircuit y B` from `insert y B` gives a base. -/
private lemma IsBase.isBase_insert_diff_of_mem_fundCircuit {B : Set α} {x y : α}
    (hB : M.IsBase B) (hyE : y ∈ M.E) (hyB : y ∉ B) (hx : x ∈ M.fundCircuit y B)
    (hxy : x ≠ y) : M.IsBase (insert y (B \ {x})) := by
  rw [Set.insert_sdiff_singleton_comm hxy.symm]
  exact hB.exchange_isBase_of_indep' (by simpa [hxy] using M.fundCircuit_subset_insert y B hx)
    hyB ((hB.indep.mem_fundCircuit_iff (by rwa [hB.closure_eq]) hyB).1 hx)

/-- **Symmetric basis exchange.** If `B₁` and `B₂` are bases of `M` and `e ∈ B₁ \ B₂`, then
there is `f ∈ B₂ \ B₁` such that both `(B₁ \ {e}) ∪ {f}` and `(B₂ \ {f}) ∪ {e}` are bases. -/
@[lognarayana "lem_matroid_symmetric_exchange"]
public theorem IsBase.symmetric_exchange (hB₁ : M.IsBase B₁) (hB₂ : M.IsBase B₂)
    (he : e ∈ B₁ \ B₂) :
    ∃ f ∈ B₂ \ B₁, M.IsBase (insert f (B₁ \ {e})) ∧ M.IsBase (insert e (B₂ \ {f})) := by
  obtain ⟨heB₁, heB₂⟩ := he
  have heE : e ∈ M.E := hB₁.subset_ground heB₁
  -- The fundamental circuit of `e` w.r.t. `B₂` and the fundamental cocircuit of `e` w.r.t. `B₁`
  -- meet in `e`, hence (a circuit and a cocircuit never meet in one element) in some `f ≠ e`.
  obtain ⟨f, ⟨hfC, hfK⟩, hfe⟩ : ∃ f ∈ M.fundCircuit e B₂ ∩ M.fundCocircuit e B₁, f ≠ e := by
    by_contra! h
    exact (hB₂.fundCircuit_isCircuit heE heB₂).inter_isCocircuit_ne_singleton
      (fundCocircuit_isCocircuit heB₁ hB₁) (Set.eq_singleton_iff_unique_mem.2
        ⟨⟨M.mem_fundCircuit e B₂, M.mem_fundCocircuit e B₁⟩, h⟩)
  have hfB₂ : f ∈ B₂ := by simpa [hfe] using M.fundCircuit_subset_insert e B₂ hfC
  have hfB₁ : f ∈ M.E \ B₁ := by simpa [hfe] using M.fundCocircuit_subset_insert_compl e B₁ hfK
  exact ⟨f, ⟨hfB₂, hfB₁.2⟩,
    hB₁.isBase_insert_diff_of_mem_fundCircuit hfB₁.1 hfB₁.2
      ((hB₁.mem_fundCocircuit_iff_mem_fundCircuit (e := f) (f := e)).1 hfK) hfe.symm,
    hB₂.isBase_insert_diff_of_mem_fundCircuit heE heB₂ hfC hfe⟩

end SymmetricExchange

section Indicator

/-! ### Indicator vectors `∑ e ∈ B, single e 1` of finite sets -/

variable {α : Type*}

private lemma sum_single_one_apply [DecidableEq α] (B : Finset α) (a : α) :
    (∑ e ∈ B, single e 1 : α →₀ ℕ) a = if a ∈ B then 1 else 0 := by
  simp [finsetSum_apply, single_apply]

private lemma support_sum_single_one (B : Finset α) :
    (∑ e ∈ B, single e 1 : α →₀ ℕ).support = B := by
  classical
  ext a; simp [sum_single_one_apply]

private lemma sum_single_one_injective :
    Function.Injective (fun B : Finset α => (∑ e ∈ B, single e 1 : α →₀ ℕ)) := by
  classical
  intro B C h
  simpa [support_sum_single_one] using congrArg Finsupp.support h

private lemma degree_sum_single_one (B : Finset α) :
    (∑ e ∈ B, single e 1 : α →₀ ℕ).degree = B.card := by
  simp [map_sum]

private lemma factorial_sum_single_one (B : Finset α) :
    (∑ e ∈ B, single e 1 : α →₀ ℕ).factorial = 1 := by
  classical
  exact Finset.prod_eq_one fun x _ => by rw [sum_single_one_apply]; split_ifs <;> rfl

/-- Exchanging `i ∈ B` for `f ∉ B` changes the indicator vector of `B` by `-eᵢ + e_f`. -/
private lemma sum_single_one_sub_add [DecidableEq α] {B : Finset α} {i f : α}
    (hi : i ∈ B) (hf : f ∉ B) :
    (∑ e ∈ B, single e 1 : α →₀ ℕ) - single i 1 + single f 1 =
      ∑ e ∈ insert f (B.erase i), single e 1 := by
  rw [Finset.sum_insert (fun h => hf (Finset.mem_of_mem_erase h)), ← Finset.sum_erase_add _ _ hi,
    add_tsub_cancel_right, add_comm]

private lemma prod_X_eq_monomial_sum_single_one {R : Type*} [CommSemiring R] (B : Finset α) :
    (∏ e ∈ B, X e : MvPolynomial α R) = monomial (∑ e ∈ B, single e 1) 1 := by
  classical
  induction B using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, X, monomial_mul, one_mul]

/-- The indicator vectors `𝟏_B = ∑ e ∈ B, e_e` of the bases `B` of a matroid on a finite ground
set form an M-convex set. -/
@[lognarayana "lem_basis_indicators_mconvex"]
public theorem isMConvex_setOf_indicator_isBase (M : Matroid α) [M.Finite] :
    {x : α →₀ ℕ | ∃ B : Finset α, M.IsBase ↑B ∧ x = ∑ e ∈ B, Finsupp.single e 1}.IsMConvex := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine Set.Finite.of_finite_image (f := fun x : α →₀ ℕ => (x.support : Set α))
      (M.ground_finite.finite_subsets.subset ?_) ?_
    · rintro _ ⟨x, ⟨B, hB, rfl⟩, rfl⟩
      simpa [support_sum_single_one] using hB.subset_ground
    · rintro _ ⟨B₁, -, rfl⟩ _ ⟨B₂, -, rfl⟩ h
      simp_all [support_sum_single_one]
  · obtain ⟨B, hB⟩ := M.exists_isBase
    exact ⟨_, hB.finite.toFinset, by simpa using hB, rfl⟩
  · obtain ⟨B₀, hB₀⟩ := M.exists_isBase
    refine ⟨B₀.ncard, ?_⟩
    rintro _ ⟨B, hB, rfl⟩
    rw [degree_sum_single_one, ← Set.ncard_coe_finset]
    exact hB.ncard_eq_ncard_of_isBase hB₀
  · rintro _ ⟨B₁, hB₁, rfl⟩ _ ⟨B₂, hB₂, rfl⟩ i hi
    have hi' : i ∈ B₁ ∧ i ∉ B₂ := by
      simp only [sum_single_one_apply] at hi
      split_ifs at hi <;> simp_all
    obtain ⟨f, ⟨hf₂, hf₁ : f ∉ B₁⟩, h₁, h₂⟩ := hB₁.symmetric_exchange hB₂ (by simpa using hi')
    refine ⟨f, by simp_all [sum_single_one_apply],
      ⟨insert f (B₁.erase i), by simpa using h₁, sum_single_one_sub_add hi'.1 hf₁⟩,
      ⟨insert i (B₂.erase f), by simpa using h₂, sum_single_one_sub_add hf₂ hi'.2⟩⟩

end Indicator

section Lorentzian

variable {α : Type*} [Fintype α]

open scoped Classical in
/-- `B_M` is the normalized support polynomial of the indicator vectors of the bases of `M`. -/
private lemma basisGeneratingPolynomial_eq_normalizedSupportPoly (M : Matroid α) :
    M.basisGeneratingPolynomial ℝ = normalizedSupportPoly ℝ
      (({B : Finset α | M.IsBase ↑B} : Finset (Finset α)).image
        fun B => ∑ e ∈ B, single e 1) := by
  unfold Matroid.basisGeneratingPolynomial normalizedSupportPoly
  rw [Finset.sum_image fun B _ C _ h => sum_single_one_injective h]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [prod_X_eq_monomial_sum_single_one, factorial_sum_single_one]
  simp

/-- **Basis generating polynomials are Lorentzian**: for every matroid `M` on a finite type `α`,
the basis generating polynomial `B_M ∈ ℝ[z_e : e ∈ α]` is Lorentzian, given the Brändén–Huh
theorem that normalized support polynomials of M-convex sets are Lorentzian. -/
@[lognarayana "lem_basis_gen_poly_lorentzian"]
public theorem isLorentzian_basisGeneratingPolynomial
    (hBH : MvPolynomial.NormalizedSupportPolyLorentzianOfMConvex α) (M : Matroid α) :
    (M.basisGeneratingPolynomial ℝ).IsLorentzian := by
  classical
  rw [basisGeneratingPolynomial_eq_normalizedSupportPoly]
  refine hBH _ ?_
  convert isMConvex_setOf_indicator_isBase M using 1
  ext x
  simp [eq_comm]

end Lorentzian

end Matroid
