/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib
public import LogNarayana.AuxiliaryDefinitions

/-!
# The Lagrange inversion formula

Let `R` be a commutative ring, `φ ∈ R[u]` and `G ∈ R⟦z⟧` with `constantCoeff G = 0` and
`G = z φ(G)`. Then for all `1 ≤ k ≤ n`, `n [z^n] G^k = k [u^(n-k)] φ(u)^n`
(`PowerSeries.lagrangeInversion`). This proves the proposition `PowerSeries.LagrangeInversion R`
for every commutative ring `R`.

## Proof

For a polynomial `ψ`, let `L ψ = ∑ₙ [u^n](ψ φ^n) zⁿ`. The series `L` is additive, `R`-linear and
satisfies `L (u χ) = z L (φ χ)`; by induction on the coefficients these identities give
`L ψ = L 1 · ψ(G)`. The coefficient identity `[u^(n+1)] φ^(n+1) = [u^n] (φ' φ^n)`, proved over a
torsion-free domain by differentiating and transported to every commutative ring through the
universal polynomial over `ℤ[a₀, a₁, …]`, shows `L 1 · (1 - z φ'(G)) = 1`. Differentiating
`G = z φ(G)` then gives `z (G^k)' = k L(u^k)`, whose `n`-th coefficient is the formula.

## References

* [R. P. Stanley, *Enumerative Combinatorics, Vol. 2*][stanley1999], Theorem 5.4.2.
-/

public section

open Polynomial

namespace Polynomial

/-- Over a torsion-free domain, `[u^(n+1)] Φ^(n+1) = [u^n] (Φ' Φ^n)`. -/
private theorem coeff_pow_succ_self_eq_of_charZero {A : Type*} [CommRing A] [IsDomain A]
    [CharZero A] (Φ : A[X]) (n : ℕ) :
    (Φ ^ (n + 1)).coeff (n + 1) = (derivative Φ * Φ ^ n).coeff n := by
  have h := coeff_derivative (Φ ^ (n + 1)) n
  rw [derivative_pow, Nat.add_sub_cancel, mul_assoc, coeff_C_mul, mul_comm (Φ ^ n)] at h
  apply mul_left_cancel₀ (Nat.cast_ne_zero.mpr n.succ_ne_zero : ((n + 1 : ℕ) : A) ≠ 0)
  rw [h]
  push_cast
  ring

/-- Over every commutative ring, `[u^(n+1)] φ^(n+1) = [u^n] (φ' φ^n)`: the identity is one
between integer polynomials in the coefficients of `φ`, so it is specialised from the universal
polynomial over `ℤ[a₀, a₁, …]`. -/
theorem coeff_pow_succ_self_eq_coeff_derivative_mul_pow {R : Type*} [CommRing R] (φ : R[X])
    (n : ℕ) : (φ ^ (n + 1)).coeff (n + 1) = (derivative φ * φ ^ n).coeff n := by
  let Φ : (MvPolynomial ℕ ℤ)[X] :=
    ∑ i ∈ Finset.range (φ.natDegree + 1), C (MvPolynomial.X i) * X ^ i
  let f : MvPolynomial ℕ ℤ →+* R := MvPolynomial.eval₂Hom (Int.castRingHom R) (fun i => φ.coeff i)
  have hΦ : Φ.map f = φ := by
    simp only [Φ, Polynomial.map_sum, Polynomial.map_mul, map_C, Polynomial.map_pow, map_X]
    conv_rhs => rw [φ.as_sum_range_C_mul_X_pow]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show f (MvPolynomial.X i) = φ.coeff i from MvPolynomial.eval₂_X _ _ _]
  have h := congrArg f (coeff_pow_succ_self_eq_of_charZero Φ n)
  rwa [← coeff_map, ← coeff_map, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_pow,
    ← derivative_map, hΦ] at h

variable {R : Type*} [CommRing R] (φ : R[X])

/-- The series `∑ₙ [u^n](ψ φ^n) zⁿ` attached to polynomials `φ` and `ψ`. -/
private noncomputable def lagrangeSeries (ψ : R[X]) : PowerSeries R :=
  PowerSeries.mk fun n => (ψ * φ ^ n).coeff n

private theorem lagrangeSeries_add (ψ₁ ψ₂ : R[X]) :
    lagrangeSeries φ (ψ₁ + ψ₂) = lagrangeSeries φ ψ₁ + lagrangeSeries φ ψ₂ := by
  ext n
  simp [lagrangeSeries, add_mul]

private theorem lagrangeSeries_C (a : R) :
    lagrangeSeries φ (C a) = PowerSeries.C a * lagrangeSeries φ 1 := by
  ext n
  simp [lagrangeSeries, coeff_C_mul]

private theorem lagrangeSeries_X_mul (χ : R[X]) :
    lagrangeSeries φ (X * χ) = PowerSeries.X * lagrangeSeries φ (φ * χ) := by
  ext n
  rcases n with _ | m
  · simp [lagrangeSeries]
  · rw [PowerSeries.coeff_succ_X_mul]
    simp only [lagrangeSeries, PowerSeries.coeff_mk]
    rw [mul_assoc, coeff_X_mul, pow_succ]
    congr 1
    ring

/-- If `G = z φ(G)`, then `∑ₙ [u^n](ψ φ^n) zⁿ = (∑ₙ [u^n] φ^n zⁿ) · ψ(G)` for every `ψ`. -/
private theorem lagrangeSeries_eq (G : PowerSeries R) (hG : G = PowerSeries.X * aeval G φ)
    (ψ : R[X]) : lagrangeSeries φ ψ = lagrangeSeries φ 1 * aeval G ψ := by
  let M : R[X] → PowerSeries R := fun ψ => lagrangeSeries φ ψ - lagrangeSeries φ 1 * aeval G ψ
  have hsplit : ∀ ψ, M ψ = PowerSeries.C (ψ.coeff 0) * M 1 + PowerSeries.X * M (φ * ψ.divX) := by
    intro ψ
    conv_lhs => rw [← X_mul_divX_add ψ]
    simp only [M, lagrangeSeries_add, lagrangeSeries_C, lagrangeSeries_X_mul, map_add, map_mul,
      aeval_C, aeval_X, map_one]
    rw [show algebraMap R (PowerSeries R) (ψ.coeff 0) = PowerSeries.C (ψ.coeff 0) from rfl]
    linear_combination (-(lagrangeSeries φ 1 * aeval G ψ.divX)) * hG
  have hM : ∀ m, ∀ ψ, PowerSeries.coeff m (M ψ) = 0 := by
    intro m
    induction m with
    | zero =>
      intro ψ
      rw [hsplit]
      simp [M]
    | succ m ih =>
      intro ψ
      rw [hsplit, map_add, PowerSeries.coeff_succ_X_mul, ih]
      simp [M]
  have : M ψ = 0 := by
    ext m
    simpa using hM m ψ
  exact sub_eq_zero.mp this

private theorem lagrangeSeries_one_mul (G : PowerSeries R) (hG : G = PowerSeries.X * aeval G φ) :
    lagrangeSeries φ 1 * (1 - PowerSeries.X * aeval G (derivative φ)) = 1 := by
  have h1 : lagrangeSeries φ 1 - PowerSeries.X * lagrangeSeries φ (derivative φ) = 1 := by
    ext n
    rcases n with _ | m
    · simp [lagrangeSeries]
    · rw [map_sub, PowerSeries.coeff_succ_X_mul]
      simp only [lagrangeSeries, PowerSeries.coeff_mk, one_mul, PowerSeries.coeff_one]
      rw [coeff_pow_succ_self_eq_coeff_derivative_mul_pow]
      simp
  rw [lagrangeSeries_eq φ G hG (derivative φ)] at h1
  linear_combination h1

/-- **The Lagrange inversion formula** over every commutative ring `R`: if `φ : R[X]` and
`G : R⟦X⟧` satisfy `constantCoeff G = 0` and `G = X * φ(G)`, then for all `1 ≤ k ≤ n`,
`n * coeff n (G ^ k) = k * (φ ^ n).coeff (n - k)`. -/
theorem _root_.PowerSeries.lagrangeInversion (R : Type*) [CommRing R] :
    PowerSeries.LagrangeInversion R := by
  intro φ G _ hG k n hk hkn
  set D := PowerSeries.derivative R
  set U := 1 - PowerSeries.X * aeval G (derivative φ)
  have hU : lagrangeSeries φ 1 * U = 1 := lagrangeSeries_one_mul φ G hG
  have hDG : PowerSeries.X * D G * U = G := by
    have h := congrArg D hG
    rw [Derivation.leibniz, Derivation.map_aeval, PowerSeries.derivative_X] at h
    simp only [smul_eq_mul] at h
    rw [show PowerSeries.X * D G * U
        = PowerSeries.X * (D G - PowerSeries.X * (aeval G (derivative φ) * D G)) by ring]
    conv_rhs => rw [hG]
    congr 1
    linear_combination h
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hkey : PowerSeries.X * D (G ^ (j + 1))
      = PowerSeries.C ((j + 1 : ℕ) : R) * lagrangeSeries φ (X ^ (j + 1)) := by
    rw [PowerSeries.derivative_pow, lagrangeSeries_eq φ G hG, map_pow, aeval_X,
      Nat.add_sub_cancel, map_natCast]
    linear_combination
      (((j + 1 : ℕ) : PowerSeries R) * G ^ j * PowerSeries.X * D G) * (-hU)
        + (((j + 1 : ℕ) : PowerSeries R) * lagrangeSeries φ 1 * G ^ j) * hDG
  have hc := congrArg (PowerSeries.coeff n) hkey
  rw [PowerSeries.coeff_C_mul] at hc
  simp only [lagrangeSeries, PowerSeries.coeff_mk] at hc
  rw [coeff_X_pow_mul', if_pos hkn] at hc
  rw [← hc]
  rcases n with _ | m
  · omega
  · rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative]
    push_cast
    ring

end Polynomial

end
