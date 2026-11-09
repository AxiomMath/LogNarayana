/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib
public import LogNarayana.Attr
public import LogNarayana.Noncrossing.CaseTwo.Defs
public import LogNarayana.PowerSeries.LagrangeInversion
public import LogNarayana.Narayana.Polynomials.Defs
public import LogNarayana.Polynomial.RealStable.Defs
public import LogNarayana.Noncrossing.RestrictedRefinement.Defs
public import LogNarayana.Narayana.Polynomials.Basic
public import LogNarayana.Nestohedron.QuadraticReplacement.Basic
public import LogNarayana.Polynomial.RealStable.Basic
public import LogNarayana.Noncrossing.RestrictedRefinement.Basic

/-!
# The case `a = 2`: real-rootedness via Lagrange inversion

For a polynomial `φ` over a commutative ring, the equation `G = z φ(G)` has a power-series
solution with vanishing constant term, and the Lagrange inversion formula
(`PowerSeries.lagrangeInversion`) extends by linearity to
`n [z^n] H(G) = [u^(n-1)] (H'(u) φ(u)^n)` for every polynomial `H`. Applied to
`φ(u) = (u + 1)(u + x)`, it shows that the Narayana generating series
`U(z) = ∑_{q ≥ 1} N_q(x) z^q` satisfies `U = z (U + 1) (U + x)`, and it computes the sum of
`∏ᵢ N_{qᵢ}(x)` over the compositions of `n` into `k` parts at least `2` as
`k / (n - k) · [u^(n-2k)] (u+1+x)^(k-1) (2u+1+x) (u+1)^(n-k) (u+x)^(n-k)`.

The polynomial on the right is a product of linear forms with nonnegative coefficients, hence
real-stable, and its coefficients in `u` are, up to positive factors, its iterated
`u`-derivatives specialised at `u = 0`. By Wagner's closure properties they are real-rooted, and
so is the restricted noncrossing refinement polynomial `R^{(2)}_{n,k}(x)`.

## Main results

* `PowerSeries.exists_constantCoeff_eq_zero_eq_X_mul_aeval`: there is `G : R⟦X⟧` with
  `constantCoeff G = 0` and `G = X * aeval G φ`.
* `PowerSeries.natCast_mul_coeff_aeval_eq_coeff_derivative_mul_pow`: Lagrange inversion for
  polynomials of the inverse series.
* `narayanaGenSeries_eq_X_mul_add_one_mul_add_C_X` : `U = z (U + 1) (U + x)` in `ℝ[x]⟦z⟧`.
* `sum_narayanaTupleProd_eq_div_mul_coeff`: the Lagrange-inversion identity for Narayana
  products with parts at least `2`.
* `Polynomial.splits_restrictedNoncrossingRefinementPoly_two`: `R^{(2)}_{n,k}(x)` is
  real-rooted.

## Implementation notes

The composites `φ(G)` and `H(G)` are `Polynomial.aeval G φ` and `Polynomial.aeval G H`, using
the algebra structure of `R⟦X⟧`. A polynomial in `u` with coefficients in `ℝ[x]` lives in
`ℝ[X][X]`, with `u = X` and `x = C X`. The Lagrange inversion formula is applied over the field
`RatFunc ℝ` of rational functions in `x`, as in the paper, and pulled back to `ℝ[X]` by
injectivity. For real stability, a bivariate polynomial `F ∈ ℝ[x][u]` is moved to
`MvPolynomial (Fin 2) ℝ`, with `u ↦ X 0` and `x ↦ X 1`; real-rootedness is `Polynomial.Splits`.

The real-rootedness of `R^{(2)}_{n,k}` is stated for all `n` and `k`: outside the paper's range
`1 ≤ k`, `2k ≤ n` the polynomial is `0`, or `1` when `n = k = 0`, and both split. The cited
results the proof rests on — Kreweras' count of noncrossing partitions by block sizes and the
closure of real stability under partial derivatives and under real specialization — are taken as
hypotheses; the Lagrange inversion formula and the γ-expansion of the shifted Narayana
polynomials are proved (`PowerSeries.lagrangeInversion`, `shiftedNarayanaGammaExpansion_holds`).

## References

* [LogNarayana], Section 7.
* [R. P. Stanley, *Enumerative Combinatorics, Vol. 2*][stanley1999], Theorem 5.4.2.
-/

/-! ### A power-series fixed point of `G = z φ(G)` -/

namespace PowerSeries

section FixedPoint

variable {R : Type*} [CommRing R]

private lemma X_pow_dvd_sub_iff {n : ℕ} {f g : PowerSeries R} :
    (X : PowerSeries R) ^ n ∣ f - g ↔ ∀ m < n, coeff m f = coeff m g := by
  simp [X_pow_dvd_iff, sub_eq_zero]

/-- `H ↦ X * φ(H)` raises the `X`-adic order of differences by one. -/
private lemma X_pow_succ_dvd_X_mul_aeval_sub (φ : Polynomial R) {n : ℕ} {G G' : PowerSeries R}
    (h : (X : PowerSeries R) ^ n ∣ G - G') :
    (X : PowerSeries R) ^ (n + 1) ∣ X * Polynomial.aeval G φ - X * Polynomial.aeval G' φ := by
  rw [← mul_sub, pow_succ']
  refine mul_dvd_mul_left _ (h.trans ?_)
  simp only [Polynomial.aeval_def, ← Polynomial.eval_map]
  exact Polynomial.sub_dvd_eval_sub _ _ _

/-- The `n`-th iterate of `H ↦ X * φ(H)` agrees on any two inputs up to order `n`. -/
private lemma X_pow_dvd_iterate_sub (φ : Polynomial R) (n : ℕ) (H H' : PowerSeries R) :
    (X : PowerSeries R) ^ n ∣
      (fun H => X * Polynomial.aeval H φ)^[n] H - (fun H => X * Polynomial.aeval H φ)^[n] H' := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Function.iterate_succ_apply']
    exact X_pow_succ_dvd_X_mul_aeval_sub φ ih

end FixedPoint

/-- For a polynomial `φ` over a commutative ring `R`, there is a power series `G` with zero
constant term satisfying `G = X * φ(G)`. -/
@[lognarayana "lem_power_series_fixed_point_exists"]
public theorem exists_constantCoeff_eq_zero_eq_X_mul_aeval {R : Type*} [CommRing R]
    (φ : Polynomial R) :
    ∃ G : PowerSeries R, constantCoeff G = 0 ∧ G = X * Polynomial.aeval G φ := by
  set F : PowerSeries R → PowerSeries R := fun H => X * Polynomial.aeval H φ
  set G : PowerSeries R := PowerSeries.mk fun n => coeff n (F^[n + 1] 0) with hG
  have hGF : ∀ m, (X : PowerSeries R) ^ m ∣ G - F^[m] 0 := fun m =>
    X_pow_dvd_sub_iff.mpr fun j hj => by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
      rw [hG, coeff_mk, Function.iterate_add_apply F (j + 1) k]
      exact (X_pow_dvd_sub_iff.mp (X_pow_dvd_iterate_sub φ _ _ _) j (by omega)).symm
  have hfix : G = F G := by
    ext m
    rw [hG, coeff_mk, Function.iterate_succ_apply', ← hG]
    exact (X_pow_dvd_sub_iff.mp (X_pow_succ_dvd_X_mul_aeval_sub φ (hGF m)) m (by omega)).symm
  refine ⟨G, ?_, hfix⟩
  rw [hfix]
  simp [F]

end PowerSeries

/-! ### Lagrange inversion for polynomials of the inverse series -/

namespace PowerSeries

/-- A power series without constant term has `X ^ k ∣ G ^ k`, so its `k`-th power has no
coefficient below degree `k`. -/
private lemma coeff_pow_eq_zero_of_lt {R : Type*} [CommRing R] {G : R⟦X⟧}
    (hG0 : constantCoeff G = 0) {n k : ℕ} (hnk : n < k) : coeff n (G ^ k) = 0 := by
  obtain ⟨g, rfl⟩ : X ∣ G := X_dvd_iff.mpr hG0
  rw [mul_pow, coeff_X_pow_mul', if_neg (by omega)]

/-- Lagrange inversion for a monomial `H = X ^ j`, for every `j`, including the cases `j = 0`
and `j > n` that `PowerSeries.LagrangeInversion` excludes. -/
private lemma natCast_mul_coeff_pow_eq_coeff_derivative_X_pow_mul {K : Type*} [Field K]
    {φ : Polynomial K} {G : K⟦X⟧} (hG0 : constantCoeff G = 0)
    (hG : G = X * Polynomial.aeval G φ) (j : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    (n : K) * coeff n (G ^ j) =
      (Polynomial.derivative (Polynomial.X ^ j) * φ ^ n).coeff (n - 1) := by
  rw [Polynomial.derivative_X_pow, mul_assoc, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow_mul']
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp [coeff_one, show n ≠ 0 by omega]
  rcases le_or_gt j n with hjn | hjn
  · rw [if_pos (by omega), show n - 1 - (j - 1) = n - j by omega,
      lagrangeInversion K φ G hG0 hG j n hj hjn]
  · rw [if_neg (by omega), coeff_pow_eq_zero_of_lt hG0 hjn, mul_zero, mul_zero]


/-- **Lagrange inversion for polynomials of the inverse series**: over a field `K` of characteristic
zero, if `φ : K[X]` and `G : K⟦X⟧` satisfy `constantCoeff G = 0` and `G = X * φ(G)`, then for every
polynomial `H` and every `n ≥ 1`, `n * coeff n (H(G)) = (H' * φ ^ n).coeff (n - 1)`. -/
@[lognarayana "lem_lagrange_inversion_poly"]
public theorem natCast_mul_coeff_aeval_eq_coeff_derivative_mul_pow
    {K : Type*} [Field K] [CharZero K]
    (φ : Polynomial K) (G : K⟦X⟧) (hG0 : constantCoeff G = 0)
    (hG : G = X * Polynomial.aeval G φ) (H : Polynomial K) (n : ℕ) (hn : 1 ≤ n) :
    (n : K) * coeff n (Polynomial.aeval G H) =
      (Polynomial.derivative H * φ ^ n).coeff (n - 1) := by
  induction H using Polynomial.induction_on' with
  | add p q hp hq => simp [mul_add, add_mul, hp, hq]
  | monomial j a =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, Polynomial.aeval_C, Polynomial.aeval_X_pow,
      PowerSeries.algebraMap_eq, coeff_C_mul, mul_left_comm,
      natCast_mul_coeff_pow_eq_coeff_derivative_X_pow_mul hG0 hG j hn,
      Polynomial.derivative_C_mul, mul_assoc, Polynomial.coeff_C_mul]

end PowerSeries

/-! ### The functional equation of the Narayana series -/

section GFEquation

open Polynomial

/-- Reindex a sum over `[1, n]` as a sum over `range n`. -/
private lemma sum_Icc_one_eq_sum_range {M : Type*} [AddCommMonoid M] (n : ℕ) (f : ℕ → M) :
    ∑ i ∈ Finset.Icc 1 n, f i = ∑ a ∈ Finset.range n, f (a + 1) := by
  rw [Finset.range_eq_Ico, Finset.sum_Ico_add']; rfl

/-- `[u^m] ((u + 1)(u + x))^(m+1) = (m+1) N_{m+1}(x)` in `ℝ[x][u]`. -/
private lemma coeff_pow_eq (m : ℕ) :
    (((X + 1) * (X + C (X : ℝ[X]))) ^ (m + 1)).coeff m =
      ((m + 1 : ℕ) : ℝ[X]) * narayanaPolynomial (m + 1) := by
  rw [mul_pow, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    narayanaPolynomial, if_neg m.succ_ne_zero, Finset.mul_sum,
    sum_Icc_one_eq_sum_range]
  refine Finset.sum_congr rfl fun a ha => ?_
  have ha : a ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
  have hc : ((m + 1 : ℕ) : ℝ[X]) * C ((m + 1 : ℕ) : ℝ)⁻¹ = 1 := by
    rw [← C_eq_natCast, ← C_mul, mul_inv_cancel₀ (by positivity), C_1]
  rw [coeff_X_add_one_pow, coeff_X_add_C_pow,
    Nat.choose_symm_of_eq_add (show m + 1 = (m - a) + (a + 1) by omega),
    show m + 1 - (m - a) = a + 1 by omega, Nat.add_sub_cancel]
  simp only [map_mul, map_natCast]
  linear_combination -(((m + 1).choose (a + 1) : ℝ[X]) * ((m + 1).choose a : ℝ[X]) *
    X ^ (a + 1)) * hc

/-- The fixed point of `G ↦ z (G + 1) (G + x)` with zero constant term is the Narayana series:
Lagrange inversion with `k = 1` reads off its coefficients from `coeff_pow_eq`. -/
private lemma eq_narayanaGenSeries {G : PowerSeries ℝ[X]}
    (hG0 : PowerSeries.constantCoeff G = 0)
    (hG : G = PowerSeries.X * ((G + 1) * (G + PowerSeries.C X))) :
    G = narayanaGenSeries := by
  refine PowerSeries.ext fun n => ?_
  rcases n with _ | m
  · simp [narayanaGenSeries, hG0]
  · have h := PowerSeries.lagrangeInversion ℝ[X] ((X + 1) * (X + C X)) G hG0
      (by simpa [PowerSeries.algebraMap_eq] using hG) 1 (m + 1) le_rfl (by omega)
    rw [pow_one, Nat.cast_one, one_mul, Nat.add_sub_cancel, coeff_pow_eq] at h
    rw [narayanaGenSeries, PowerSeries.coeff_mk, if_neg m.succ_ne_zero]
    exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr m.succ_ne_zero) h

/-- The Narayana generating series `U = narayanaGenSeries` satisfies the functional equation
`U = z (U + 1) (U + x)` in `ℝ[x]⟦z⟧`. -/
@[lognarayana "lem_narayana_gf_equation"]
public theorem narayanaGenSeries_eq_X_mul_add_one_mul_add_C_X :
    narayanaGenSeries =
      PowerSeries.X * (narayanaGenSeries + 1) * (narayanaGenSeries + PowerSeries.C X) := by
  obtain ⟨G, hG0, hG⟩ :=
    PowerSeries.exists_constantCoeff_eq_zero_eq_X_mul_aeval ((X + 1) * (X + C (X : ℝ[X])))
  have hG' : G = PowerSeries.X * ((G + 1) * (G + PowerSeries.C X)) := by
    simpa [PowerSeries.algebraMap_eq] using hG
  rw [← eq_narayanaGenSeries hG0 hG', mul_assoc]
  exact hG'

end GFEquation

/-! ### A Lagrange-inversion identity for Narayana products with parts at least two -/

section NCTwoIdentity

open Polynomial Finset

/-- The `n`-th coefficient of `f ^ k` is the sum over `k`-tuples summing to `n` of the products
of the coefficients of `f`. -/
private theorem coeff_pow_eq_sum_antidiagonalTuple {R : Type*} [CommRing R] (k n : ℕ)
    (f : PowerSeries R) :
    PowerSeries.coeff n (f ^ k) =
      ∑ q ∈ Finset.Nat.antidiagonalTuple k n, ∏ i, PowerSeries.coeff (q i) f := by
  classical
  have : f ^ k = ∏ _i : Fin k, f := by simp
  rw [this, PowerSeries.coeff_prod]
  refine Finset.sum_nbij' (fun l => ⇑l) (fun q => Finsupp.equivFunOnFinite.symm q) ?_ ?_ ?_ ?_ ?_
  · intro l hl
    simp only [mem_finsuppAntidiag] at hl
    simp [Finset.Nat.mem_antidiagonalTuple, ← hl.1]
  · intro q hq
    simp only [Finset.Nat.mem_antidiagonalTuple] at hq
    simp [mem_finsuppAntidiag, hq]
  · intro l _; simp
  · intro q _; simp
  · intro l _; rfl

/-- Lagrange inversion for `G = z (G + 1) (G + x)` over `ℝ[X]` and `H(u) = (u (u + 1 + x))^k`,
obtained from `PowerSeries.natCast_mul_coeff_aeval_eq_coeff_derivative_mul_pow` over the field
`RatFunc ℝ` and the injectivity of `ℝ[X] → RatFunc ℝ`. -/
private theorem natCast_mul_coeff_pow_X_mul_X_add_one_add_C_X_eq
    (G : PowerSeries ℝ[X]) (hG0 : PowerSeries.constantCoeff G = 0)
    (hG : G = PowerSeries.X * (G + 1) * (G + PowerSeries.C X)) (k N : ℕ) (hN : 1 ≤ N) :
    (N : ℝ[X]) * PowerSeries.coeff N ((G * (G + 1 + PowerSeries.C X)) ^ k) =
      (derivative ((X * (X + 1 + C X)) ^ k) * ((X + 1) * (X + C X)) ^ N).coeff (N - 1) := by
  set ι := algebraMap ℝ[X] (RatFunc ℝ) with hιdef
  have hι : Function.Injective ι := IsFractionRing.injective ℝ[X] (RatFunc ℝ)
  set a : RatFunc ℝ := ι X with ha
  have ha0 : a ≠ 0 := by
    rw [ha, ← map_zero ι]; exact hι.ne X_ne_zero
  set V := PowerSeries.map ι G with hVdef
  have hV0 : PowerSeries.constantCoeff V = 0 := by
    rw [hVdef, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, hG0, map_zero]
  have hV : V = PowerSeries.X * (V + 1) * (V + PowerSeries.C a) := by
    conv_lhs => rw [hVdef, hG]
    simp [hVdef, ha]
  have h := PowerSeries.natCast_mul_coeff_aeval_eq_coeff_derivative_mul_pow
    ((X + 1) * (X + C a)) V hV0 (by
      simp only [map_mul, map_add, aeval_X, aeval_C, map_one, PowerSeries.algebraMap_eq]
      rw [← mul_assoc]; exact hV) ((X * (X + 1 + C a)) ^ k) N hN
  simp only [map_mul, map_add, map_pow, aeval_X, aeval_C, map_one,
    PowerSeries.algebraMap_eq] at h
  apply hι
  have hmap : (PowerSeries.map ι) ((G * (G + 1 + PowerSeries.C X)) ^ k) =
      (V * (V + 1 + PowerSeries.C a)) ^ k := by simp [hVdef, ha]
  have hpoly : ((derivative ((X * (X + 1 + C X)) ^ k) * ((X + 1) * (X + C X)) ^ N :
      ℝ[X][X]).map ι) = derivative ((X * (X + 1 + C a)) ^ k) * ((X + 1) * (X + C a)) ^ N := by
    simp [Polynomial.map_mul, Polynomial.map_pow, ha, ← Polynomial.derivative_map]
  rw [map_mul, map_natCast, ← PowerSeries.coeff_map, hmap, h, ← coeff_map, hpoly]

/-- The coefficients of `U - x z`: zero below degree `2`, and `N_q(x)` from degree `2` on. -/
private theorem coeff_narayanaGenSeries_sub (q : ℕ) :
    PowerSeries.coeff q (narayanaGenSeries - PowerSeries.C (X : ℝ[X]) * PowerSeries.X) =
      if q < 2 then 0 else narayanaPolynomial q := by
  rw [map_sub, narayanaGenSeries, PowerSeries.coeff_mk, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_X]
  rcases q with _ | _ | q
  · simp
  · simp [narayanaPolynomial]
  · simp

/-- The sum of `∏ᵢ N_{qᵢ}(x)` over compositions of `n` into `k` parts at least `2` is
`[z^n] (U - x z)^k`. -/
private theorem sum_narayanaTupleProd_eq_coeff_pow (k n : ℕ) :
    ∑ q ∈ (Finset.Nat.antidiagonalTuple k n).filter (fun q => ∀ i, 2 ≤ q i),
        narayanaTupleProd q =
      PowerSeries.coeff n
        ((narayanaGenSeries - PowerSeries.C (X : ℝ[X]) * PowerSeries.X) ^ k) := by
  rw [coeff_pow_eq_sum_antidiagonalTuple, Finset.sum_filter]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp_rw [coeff_narayanaGenSeries_sub]
  split_ifs with h
  · exact Finset.prod_congr rfl fun i _ => (if_neg (by have := h i; omega)).symm
  · push Not at h
    obtain ⟨i, hi⟩ := h
    exact (Finset.prod_eq_zero (Finset.mem_univ i) (by rw [if_pos hi])).symm

/-- The Lagrange-inversion integrand `H'(u) φ(u)^N` for `H(u) = (u (u + 1 + x))^k` and
`φ(u) = (u + 1)(u + x)`, with its factor `u^(k-1)` split off. -/
private theorem derivative_pow_mul_pow {k : ℕ} (hk : 1 ≤ k) (N : ℕ) :
    derivative ((X * (X + 1 + C X)) ^ k : ℝ[X][X]) * ((X + 1) * (X + C X)) ^ N =
      X ^ (k - 1) * (C (k : ℝ[X]) *
        ((X + 1 + C X) ^ (k - 1) * (2 * X + 1 + C X) * (X + 1) ^ N * (X + C X) ^ N)) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp only [derivative_pow, derivative_mul, derivative_X, derivative_add, derivative_one,
    derivative_C, Nat.add_sub_cancel, mul_pow, ← map_natCast C]
  ring

/-- For `k ≥ 1` and `n ≥ 2k`, the sum over compositions `q` of `n` into `k` parts `qᵢ ≥ 2` of
`∏ᵢ N_{qᵢ}(x)` is `k/(n-k)` times the coefficient of `u^(n-2k)` in
`(u+1+x)^(k-1) (2u+1+x) (u+1)^(n-k) (u+x)^(n-k)`. -/
@[lognarayana "lem_nc_two_lagrange_identity"]
public theorem sum_narayanaTupleProd_eq_div_mul_coeff
    (k n : ℕ) (hk : 1 ≤ k) (hn : 2 * k ≤ n) :
    ∑ q ∈ (Finset.Nat.antidiagonalTuple k n).filter (fun q => ∀ i, 2 ≤ q i),
        narayanaTupleProd q =
      C ((k : ℝ) / ((n : ℝ) - k)) *
        ((X + 1 + C X) ^ (k - 1) * (2 * X + 1 + C X) * (X + 1) ^ (n - k) *
          (X + C X) ^ (n - k) : ℝ[X][X]).coeff (n - 2 * k) := by
  have hU := narayanaGenSeries_eq_X_mul_add_one_mul_add_C_X
  have hU0 : PowerSeries.constantCoeff narayanaGenSeries = 0 := by
    rw [narayanaGenSeries, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.coeff_mk]; simp
  -- `U - x z = z U (U + 1 + x)`
  have hW : narayanaGenSeries - PowerSeries.C (X : ℝ[X]) * PowerSeries.X =
      PowerSeries.X * (narayanaGenSeries * (narayanaGenSeries + 1 + PowerSeries.C X)) := by
    linear_combination hU
  have key := natCast_mul_coeff_pow_X_mul_X_add_one_add_C_X_eq _ hU0 hU k (n - k)
    (by omega)
  rw [derivative_pow_mul_pow hk, show n - k - 1 = (n - 2 * k) + (k - 1) by omega,
    coeff_X_pow_mul, coeff_C_mul] at key
  rw [sum_narayanaTupleProd_eq_coeff_pow, hW, mul_pow, PowerSeries.coeff_X_pow_mul',
    if_pos (by omega)]
  have hnk : (n : ℝ) - k ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast (by omega : n ≠ k))
  apply mul_left_cancel₀ (show ((n - k : ℕ) : ℝ[X]) ≠ 0 by exact_mod_cast (by omega : n - k ≠ 0))
  rw [key, ← mul_assoc, ← map_natCast C (n - k),
    ← map_natCast C k, ← C_mul, Nat.cast_sub (by omega : k ≤ n)]
  congr 2
  field_simp

end NCTwoIdentity

/-! ### Real-rootedness of `R^{(2)}_{n,k}` -/

section NCTwoRealRooted

open Polynomial Finset

/-- A polynomial in `u` with coefficients in `ℝ[x]`, as a polynomial in `X 0 = u`, `X 1 = x`. -/
private noncomputable def toBivariate : ℝ[X][X] →+* MvPolynomial (Fin 2) ℝ :=
  Polynomial.eval₂RingHom ((Polynomial.toMvPolynomial (1 : Fin 2)).toRingHom) (MvPolynomial.X 0)

private lemma toBivariate_X : toBivariate X = MvPolynomial.X 0 := by simp [toBivariate]

private lemma toBivariate_C (a : ℝ[X]) : toBivariate (C a) = toMvPolynomial 1 a := by
  simp [toBivariate]

private lemma pderiv_zero_toMvPolynomial_one (a : ℝ[X]) :
    MvPolynomial.pderiv (0 : Fin 2) (toMvPolynomial (1 : Fin 2) a) = 0 := by
  induction a using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n c => simp [toMvPolynomial, MvPolynomial.pderiv_X]

private lemma pderiv_toBivariate (p : ℝ[X][X]) :
    MvPolynomial.pderiv 0 (toBivariate p) = toBivariate (derivative p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n c =>
    simp [toBivariate, derivative_monomial, pderiv_zero_toMvPolynomial_one, Derivation.leibniz,
      Derivation.leibniz_pow, MvPolynomial.pderiv_X]
    ring

private lemma aeval_update_zero_toBivariate (p : ℝ[X][X]) :
    MvPolynomial.aeval (Function.update MvPolynomial.X (0 : Fin 2) (MvPolynomial.C 0))
        (toBivariate p) = toMvPolynomial 1 (p.eval 0) := by
  have : (MvPolynomial.aeval (Function.update MvPolynomial.X (0 : Fin 2)
      (MvPolynomial.C (0 : ℝ)))).toRingHom.comp toBivariate =
      (toMvPolynomial (1 : Fin 2)).toRingHom.comp (Polynomial.evalRingHom 0) := by
    refine Polynomial.ringHom_ext' (Polynomial.ringHom_ext' ?_ ?_) ?_
    · ext; simp [toBivariate]
    · simp [toBivariate, toMvPolynomial]
    · simp [toBivariate]
  exact congrArg (fun f => f p) this

/-- Iterated `u`-derivatives of a real-stable `F(u, x)` are zero or real-stable. -/
private lemma toBivariate_iterate_derivative (hder : ∀ σ : Type, IsRealStablePDerivClosed σ)
    {G : ℝ[X][X]} (hG : (toBivariate G).IsRealStable) (j : ℕ) :
    toBivariate (derivative^[j] G) = 0 ∨ (toBivariate (derivative^[j] G)).IsRealStable := by
  induction j with
  | zero => exact Or.inr hG
  | succ j ih =>
    rw [Function.iterate_succ_apply', ← pderiv_toBivariate]
    rcases ih with h | h
    · simp [h]
    · exact hder _ _ h 0

/-- If `F(u, x)` is zero or real-stable, then `F(0, x)` is real-rooted. -/
private lemma splits_eval_zero
    (hspec : ∀ (σ : Type) [DecidableEq σ], IsRealStableSpecializeClosed σ)
    {G : ℝ[X][X]} (hG : toBivariate G = 0 ∨ (toBivariate G).IsRealStable) :
    (G.eval 0).Splits := by
  by_cases h0 : G.eval 0 = 0
  · simp [h0]
  have hne : toMvPolynomial (1 : Fin 2) (G.eval 0) ≠ 0 :=
    (map_ne_zero_iff _ (toMvPolynomial_injective _)).2 h0
  refine (isRealStable_toMvPolynomial_iff_splits (1 : Fin 2) h0).1 ?_
  rw [← aeval_update_zero_toBivariate] at hne ⊢
  rcases hG with h | h
  · simp [h] at hne
  · exact (hspec _ _ h 0 0).resolve_left hne

/-- If `F(u, x)` is real-stable, every coefficient `[u^m] F = (∂_u^m F)(0, x) / m!` is
real-rooted. -/
private lemma splits_coeff_of_isRealStable_toBivariate
    (hder : ∀ σ : Type, IsRealStablePDerivClosed σ)
    (hspec : ∀ (σ : Type) [DecidableEq σ], IsRealStableSpecializeClosed σ)
    {G : ℝ[X][X]} (hG : (toBivariate G).IsRealStable) (m : ℕ) : (G.coeff m).Splits := by
  have : G.coeff m = C (m.factorial : ℝ)⁻¹ * (derivative^[m] G).eval 0 := by
    rw [← coeff_zero_eq_eval_zero, coeff_iterate_derivative, zero_add, Nat.descFactorial_self,
      nsmul_eq_mul, ← mul_assoc, ← C_eq_natCast, ← C_mul, inv_mul_cancel₀ (by positivity), C_1,
      one_mul]
  rw [this]
  exact (Splits.C _).mul (splits_eval_zero hspec (toBivariate_iterate_derivative hder hG m))

private lemma ne_zero_of_im_pos {z : ℂ} (h : 0 < z.im) : z ≠ 0 := fun hz => by simp [hz] at h

private lemma isRealStable_toBivariate (k n : ℕ) :
    (toBivariate ((X + 1 + C X) ^ (k - 1) * (2 * X + 1 + C X) * (X + 1) ^ (n - k) *
      (X + C X) ^ (n - k))).IsRealStable := by
  intro ζ hζ
  have h0 := hζ 0
  have h1 := hζ 1
  simp only [map_mul, map_pow, map_add, map_one, map_ofNat, toBivariate_X, toBivariate_C,
    toMvPolynomial_X, MvPolynomial.aeval_X]
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ ?_) ?_) (pow_ne_zero _ ?_))
    (pow_ne_zero _ ?_) <;> exact ne_zero_of_im_pos (by
      simp only [Fin.isValue, Complex.add_im, Complex.mul_im, Complex.re_ofNat, Complex.im_ofNat,
        zero_mul, add_zero, Complex.one_im]
      positivity)

namespace Polynomial

/-- For all `n k : ℕ`, the restricted noncrossing refinement polynomial `R^{(2)}_{n,k}(x)` is
real-rooted. -/
@[lognarayana "prop_nc_two_real_rooted"]
public theorem splits_restrictedNoncrossingRefinementPoly_two
    (hKr : Finpartition.KrewerasBlockSizeCount)
    (hder : ∀ σ : Type, IsRealStablePDerivClosed σ)
    (hspec : ∀ (σ : Type) [DecidableEq σ], IsRealStableSpecializeClosed σ)
    (n k : ℕ) :
    (restrictedNoncrossingRefinementPoly ℝ (Finset.Icc 1 n) 2 k).Splits := by
  rw [← restrictedNoncrossingDeformedNarayanaPoly_one hKr,
    restrictedNoncrossingDeformedNarayanaPoly_eq_sum_antidiagonalTuple hKr n k 2 (by norm_num) 1]
  have hS : ∑ q ∈ (Finset.Nat.antidiagonalTuple k n).filter (fun q => ∀ i, 2 ≤ q i),
        ∏ i, deformedNarayanaPolynomial ℝ 1 (q i) =
      ∑ q ∈ (Finset.Nat.antidiagonalTuple k n).filter (fun q => ∀ i, 2 ≤ q i),
        narayanaTupleProd q :=
    sum_congr rfl fun q hq => prod_congr rfl fun i _ =>
      deformedNarayanaPolynomial_one (by have := (mem_filter.1 hq).2 i; omega)
  rw [hS]
  refine (Splits.C _).mul ?_
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp only [narayanaTupleProd, Finset.univ_eq_empty, prod_empty, sum_const, nsmul_eq_mul,
      mul_one]
    rw [← C_eq_natCast]
    exact Splits.C _
  by_cases hn : 2 * k ≤ n
  · rw [sum_narayanaTupleProd_eq_div_mul_coeff k n hk hn]
    exact (Splits.C _).mul
      (splits_coeff_of_isRealStable_toBivariate hder hspec (isRealStable_toBivariate k n) _)
  · rw [sum_eq_zero fun q hq => ?_]
    · exact Splits.zero
    exfalso
    obtain ⟨hq, h2⟩ := mem_filter.1 hq
    rw [Finset.Nat.mem_antidiagonalTuple] at hq
    have : ∑ _i : Fin k, 2 ≤ ∑ i, q i := sum_le_sum fun i _ => h2 i
    simp at this
    omega

end Polynomial

end NCTwoRealRooted
