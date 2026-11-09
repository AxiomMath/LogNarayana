/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module
public import LogNarayana.StackSorting.FiberPolynomials.Defs
public import LogNarayana.StackSorting.Descents.Basic

/-!
# The fiber polynomials

For a word `π` of length `ℓ`, write `s⁻¹(π)` for its stack-sorting fiber. This file relates the
fiber polynomials of `π`:

* the fiber descent polynomial `D_π(x) = ∑_{σ ∈ s⁻¹(π)} x^{des(σ)}`;
* the homogeneous fiber polynomial `H_π(x, y) = ∑_{σ ∈ s⁻¹(π)} x^{des(σ)} y^{ℓ - 1 - des(σ)}`;
* the fiber top polynomial `𝒟_π(x, y) = ∑_{σ ∈ s⁻¹(π)} ∏_{a ∈ DT(σ)} x_a ∏_{a ∈ AT(σ)} y_a`.

Every element of the fiber is a permutation of `1 ⋯ ℓ`, so it has no repeated entries and
`|DT(σ)| = des(σ)`, `|AT(σ)| = ℓ - 1 - des(σ)`. Hence specializing `x_a ↦ x`, `y_a ↦ y` in `𝒟_π`
gives `H_π`; `H_π` is the degree `ℓ - 1` homogenization `y^{ℓ-1} D_π(x / y)` of `D_π`; and
`H_π(x, 1) = D_π(x)`.

## Main results

* `List.rename_fiberTopPolynomial`: the image of `List.fiberTopPolynomial R π` under the
  renaming `x_a ↦ x`, `y_a ↦ y` is `List.fiberHomogPolynomial R π`.
* `List.fiberHomogPolynomial_eq_homogenize`: for `π ∈ S_n` with `n ≥ 1`,
  `H_π = hom_{n-1}(D_π)`.
* `List.aeval_fiberHomogPolynomial_one`: `H_π(x, 1) = D_π(x)`.

## Implementation notes

The two-variable polynomials live in `MvPolynomial (Fin 2) R` with `x = X 0` and `y = X 1`; the
fiber top polynomial lives in `MvPolynomial (Bool × ℕ) R` with `x_a = X (true, a)` and
`y_a = X (false, a)`. The specialization is `MvPolynomial.rename` along `(true, a) ↦ 0`,
`(false, a) ↦ 1`; the homogenization is `Polynomial.homogenize`; the substitution `y = 1` is
`MvPolynomial.aeval ![Polynomial.X, 1]`. The paper works over `ℝ`; every statement is made over
an arbitrary commutative semiring `R`. The paper states the specialization and the substitution
for `π ∈ S_n` with `n ≥ 1`; both hold for every list `π`, so no hypothesis on `π` is imposed.

## References

* [LogNarayana], Section 2.
-/


open MvPolynomial

namespace List

/-- Every member of the stack-sorting fiber of `π` is a word without repeated letters, of the
same length as `π`: it is a permutation of `1 ⋯ π.length`. -/
private lemma nodup_and_length_of_mem_stackFiber {π σ : List ℕ} (hσ : σ ∈ stackFiber π) :
    σ.Nodup ∧ σ.length = π.length := by
  have hp : σ.Perm (idPermWord π.length) := by
    simpa [stackFiber] using (Finset.mem_filter.1 hσ).1
  exact ⟨hp.nodup_iff.2 (by simpa [idPermWord] using List.nodup_range' ..),
    by simp [hp.length_eq, idPermWord]⟩

/-- For every word `π`, substituting `x` for every `x_a` and `y` for every `y_a` in the
fiber top polynomial `𝒟_π(x, y)` gives the homogeneous fiber polynomial `H_π(x, y)`. -/
@[lognarayana "lem_fiber_top_specialize"]
public theorem rename_fiberTopPolynomial (R : Type*) [CommSemiring R] (π : List ℕ) :
    rename (fun p : Bool × ℕ ↦ if p.1 then (0 : Fin 2) else 1) (fiberTopPolynomial R π) =
      fiberHomogPolynomial R π := by
  unfold fiberTopPolynomial fiberHomogPolynomial
  rw [map_sum]
  refine Finset.sum_congr rfl fun σ hσ => ?_
  obtain ⟨hnd, hlen⟩ := nodup_and_length_of_mem_stackFiber hσ
  simp only [map_mul, map_prod, rename_X, ite_true, Bool.false_eq_true, ite_false,
    Finset.prod_const, card_descentTops hnd, card_ascentTops hnd, hlen]

/-- A list has at most `length - 1` descents. -/
private lemma numDescents_le_length_sub_one (σ : List ℕ) : σ.numDescents ≤ σ.length - 1 := by
  unfold numDescents descentSet
  exact (Finset.card_filter_le _ _).trans (by simp)

/-- Let `n ≥ 1` and `π ∈ S_n`. The homogeneous fiber polynomial `H_π(x, y)` is the degree
`n - 1` homogenization `y^{n-1} D_π(x / y)` of the fiber descent polynomial `D_π`. -/
@[lognarayana "lem_fiber_homog_eq"]
public theorem fiberHomogPolynomial_eq_homogenize (R : Type*) [CommSemiring R] {n : ℕ}
    (hn : 1 ≤ n) {π : List ℕ} (hπ : π ∈ permWords n) :
    fiberHomogPolynomial R π = (fiberDescentPolynomial R π).homogenize (n - 1) := by
  obtain rfl : π.length = n := hπ.2.1
  unfold fiberHomogPolynomial fiberDescentPolynomial
  rw [Polynomial.homogenize_finsetSum]
  refine Finset.sum_congr rfl fun σ hσ => ?_
  rw [Polynomial.homogenize_X_pow
    ((nodup_and_length_of_mem_stackFiber hσ).2 ▸ numDescents_le_length_sub_one σ)]

/-- Substituting `y = 1` in the homogeneous fiber polynomial `H_π(x, y)` gives the fiber
descent polynomial `D_π(x)`. -/
@[lognarayana "lem_fiber_homog_at_one"]
public theorem aeval_fiberHomogPolynomial_one (R : Type*) [CommSemiring R] (π : List ℕ) :
    aeval ![Polynomial.X, 1] (fiberHomogPolynomial R π) = fiberDescentPolynomial R π := by
  simp [fiberHomogPolynomial, fiberDescentPolynomial]

end List
