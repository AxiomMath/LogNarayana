/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module
public import Mathlib
public import LogNarayana.Attr
public import LogNarayana.AuxiliaryDefinitions

/-!
# Multi-index factorials, binomial coefficients and iterated partial derivatives

A multi-index is a finitely supported function `α : σ →₀ ℕ`, the exponent type of
`MvPolynomial σ R`. Its factorial is `α! = ∏ i, (α i)!`, and the binomial coefficient of two
multi-indices is `(κ choose α) = ∏ i, (κ i choose α i)`; in both products only finitely many
factors differ from `1`, so `σ` need not be finite.

For a multi-index `α`, the operator `∂^α` on `R[z_i : i ∈ σ]` is the linear map acting on
monomials by `∂^α z^β = β! / (β - α)! • z^(β - α)` when `α ≤ β`, and `∂^α z^β = 0` otherwise.
It is the composite `∏ i, (∂/∂z_i)^(α i)` of the ordinary partial derivatives: raising one index
of `α` by one is the same as applying one more partial derivative,
`∂^(α + e_i) h = ∂/∂z_i (∂^α h)`.

## Main definitions

* `Finsupp.factorial`: the factorial `∏ i ∈ α.support, (α i)!` of a multi-index `α : σ →₀ ℕ`.
* `Finsupp.choose`: the binomial coefficient `∏ i ∈ α.support, (κ i).choose (α i)` of
  multi-indices `κ α : σ →₀ ℕ`.
* `MvPolynomial.iteratedPDeriv`: the operator `∂^α` as an `R`-linear endomorphism of
  `MvPolynomial σ R`.

## Main results

* `Finsupp.factorial_pos`, `Finsupp.factorial_dvd_factorial`: `0 < α!`, and `γ! ∣ β!` when
  `γ ≤ β`.
* `MvPolynomial.iteratedPDeriv_add_single`: `∂^(α + single i 1) h = pderiv i (∂^α h)`.

## Implementation notes

`Finsupp.factorial` is `Finsupp.prod` of `fun _ n ↦ n !`, the same expression as the denominator
of `Finsupp.multinomial`, so `Finsupp.multinomial_spec` reads
`α.factorial * multinomial α = (α.sum fun _ ↦ id)!` by definition.

`Finsupp.choose` is total: it needs no hypothesis `α ≤ κ`, and when `α ≰ κ` some factor
`(κ i).choose (α i)` with `κ i < α i` vanishes, so `κ.choose α = 0`, extending
`Nat.choose_eq_zero_of_lt` coordinatewise.

`MvPolynomial.iteratedPDeriv` is defined by its values on the monomial basis
`MvPolynomial.basisMonomials`, extended linearly (`Basis.constr`), over an arbitrary commutative
semiring `R`. The coefficient `β! / (β - α)!` is the natural number
`Finsupp.factorial β / Finsupp.factorial (β - α)`, an exact quotient when `α ≤ β`, cast into
`R`. The single partial derivative `∂_i` is Mathlib's `MvPolynomial.pderiv i`.
-/

namespace Finsupp

variable {σ : Type*}

/-- Splitting off one factor: `f! = (f i)! · (f.erase i)!`. -/
private lemma factorial_eq_mul_erase (f : σ →₀ ℕ) (i : σ) :
    f.factorial = (f i).factorial * (f.erase i).factorial :=
  (mul_prod_erase' f i _ fun _ => rfl).symm

/-- `0! = 1` for the zero multi-index. -/
@[simp]
public lemma factorial_zero : (0 : σ →₀ ℕ).factorial = 1 :=
  prod_zero_index

/-- A multi-index factorial is positive. -/
public lemma factorial_pos (f : σ →₀ ℕ) : 0 < f.factorial :=
  Finset.prod_pos fun _ _ => Nat.factorial_pos _

/-- `γ! ∣ β!` whenever `γ ≤ β` coordinatewise. -/
public lemma factorial_dvd_factorial {γ β : σ →₀ ℕ} (h : γ ≤ β) :
    γ.factorial ∣ β.factorial :=
  prod_dvd_prod_of_subset_of_dvd (support_mono h) fun j _ => Nat.factorial_dvd_factorial (h j)

/-- Lowering one entry of `γ ≤ β` by one: `β! / (γ - e_i)! = (β! / γ!) · γ_i` when `0 < γ_i`.
This is the coefficient identity behind `∂_i ∘ ∂^α = ∂^(α + e_i)`. -/
private lemma factorial_div_tsub_single {γ β : σ →₀ ℕ} (h : γ ≤ β) {i : σ} (hi : 0 < γ i) :
    β.factorial / (γ - single i 1).factorial = β.factorial / γ.factorial * γ i := by
  classical
  have he : (γ - single i 1).erase i = γ.erase i := by
    ext j; by_cases hj : j = i <;> simp [hj]
  have hγ : γ.factorial = γ i * (γ - single i 1).factorial := by
    rw [factorial_eq_mul_erase γ i, factorial_eq_mul_erase (γ - single i 1) i, he,
      tsub_apply, single_eq_same, ← mul_assoc, ← Nat.mul_factorial_pred hi.ne']
  obtain ⟨k, hk⟩ := factorial_dvd_factorial h
  rw [hk, Nat.mul_div_cancel_left _ (factorial_pos γ), hγ, mul_right_comm,
    Nat.mul_div_cancel _ (factorial_pos _), mul_comm]

end Finsupp

namespace MvPolynomial

variable {σ R : Type*} [CommSemiring R]

private lemma iteratedPDeriv_monomial (α β : σ →₀ ℕ) :
    iteratedPDeriv α (monomial β (1 : R)) =
      monomial (β - α) (if α ≤ β then ((β.factorial / (β - α).factorial : ℕ) : R) else 0) := by
  rw [iteratedPDeriv, show monomial β (1 : R) = basisMonomials σ R β by rw [coe_basisMonomials],
    Module.Basis.constr_basis]

/-- `∂^(α + e_i) h = ∂/∂z_i (∂^α h)`: one more step in the variable `z_i` of an iterated
partial derivative is the ordinary partial derivative `MvPolynomial.pderiv i`.

Both sides are linear in `h`, so it suffices to compare them on the monomials `z^β`, where the
identity reduces to `Finsupp.factorial` arithmetic. -/
@[lognarayana "lem_partial_multi_pderiv"]
public theorem iteratedPDeriv_add_single (h : MvPolynomial σ R) (α : σ →₀ ℕ) (i : σ) :
    iteratedPDeriv (α + Finsupp.single i 1) h = pderiv i (iteratedPDeriv α h) := by
  classical
  suffices H : iteratedPDeriv (α + Finsupp.single i 1) =
      (pderiv i).toLinearMap ∘ₗ (iteratedPDeriv α : MvPolynomial σ R →ₗ[R] _) by
    rw [H]; rfl
  refine (basisMonomials σ R).ext fun β => ?_
  rw [coe_basisMonomials, LinearMap.comp_apply, iteratedPDeriv_monomial, iteratedPDeriv_monomial,
    Derivation.coeFn_coe, pderiv_monomial, ← tsub_tsub]
  by_cases hab : α ≤ β
  · simp only [← le_tsub_iff_left hab, Finsupp.single_le_iff, if_pos hab]
    by_cases hi : 1 ≤ (β - α) i
    · rw [if_pos hi, Finsupp.factorial_div_tsub_single tsub_le_self hi]
      push_cast; rfl
    · simp [Nat.lt_one_iff.mp (not_le.mp hi)]
  · rw [if_neg fun hb => hab (le_self_add.trans hb)]
    simp [hab]

end MvPolynomial
