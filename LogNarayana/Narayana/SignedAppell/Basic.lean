/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib
public import LogNarayana.Attr
public import LogNarayana.Narayana.SignedAppell.Defs
public import LogNarayana.Narayana.Polynomials.Defs
public import LogNarayana.Narayana.Polynomials.Basic

/-!
# The signed Appell sequence

This file proves the basic properties of the signed Appell polynomials
`η_m(t) = ∑_{j=0}^{⌊m/2⌋} (-1)^j C_j (m choose 2j) t^(m-2j)`.

The polynomial `η_m` is `t^m` plus lower-order terms, and `η_m' = m η_{m-1}`, so `(η_m)` is an
Appell sequence; it satisfies the binomial identity `η_d(z + w) = ∑_m (d choose m) η_m(z) w^(d-m)`.
Its first values are `1, t, t² - 1, t³ - 3t, t⁴ - 6t² + 2`, and `η_m(-t) = (-1)^m η_m(t)`.
Under the change of variables `t = r⁻¹ - r` it becomes the shifted Narayana polynomial:
`η_m(r⁻¹ - r) = r^(-m) Ñ_m(-r²)` for `r > 0`, which follows from the Catalan γ-expansion of
`Ñ_m`, proved here. Since the change of variables is strictly monotone on `r > 0`, the `m`
distinct negative zeros of `Ñ_m` (a theorem of Liu and Wang, taken as a hypothesis) give `m`
distinct real zeros of `η_m`; hence `η_m` is real-rooted.

## Main results

* `Polynomial.degree_signedAppell_sub_X_pow_lt`: `deg (η_m - t^m) < m`.
* `Polynomial.derivative_signedAppell`:
  `derivative (signedAppell R m) = m * signedAppell R (m - 1)`.
* `Polynomial.signedAppell_first_values`: the values of `η_0, …, η_4`.
* `Polynomial.signedAppell_comp_neg_X`: `η_m(-t) = (-1)^m η_m(t)`.
* `Polynomial.isAppell_signedAppell`: `fun m => signedAppell R m` is an Appell sequence.
* `Polynomial.aeval_add_signedAppell`: for `z w` in a commutative `R`-algebra `S`,
  `η_d(z + w) = ∑ m ∈ range (d + 1), d.choose m * η_m(z) * w ^ (d - m)`.
* `Polynomial.eval_signedAppell_inv_sub`: `η_m(r⁻¹ - r) = r^(-m) Ñ_m(-r²)` for `r > 0`.
* `Polynomial.splits_signedAppell`: `η_m` splits over `ℝ`.
* `Polynomial.encard_setOf_eval_signedAppell_eq_zero`: `{t : ℝ | η_m(t) = 0}` has exactly `m`
  elements.

## Implementation notes

The paper works in `ℝ[t]`. The identities with integer coefficients are stated over an
arbitrary ring `R` (`R = ℝ` being the paper); `isAppell_signedAppell` needs `R` nontrivial,
since over the zero ring every polynomial has degree `⊥`. The binomial identity, stated in the
paper in `ℝ[z, w]`, is stated for arbitrary elements `z w` of a commutative `R`-algebra; the
paper's identity is the case `S = MvPolynomial (Fin 2) ℝ`, `z = X 0`, `w = X 1`. The derivative
identity also holds for `m = 0`, where both sides vanish. The substitution `t ↦ -t` is
`Polynomial.comp _ (-X)`. Real-rootedness is `Polynomial.Splits` over `ℝ`, and the number of
zeros is `Set.encard`, valued in `ℕ∞`, so that statement also asserts that the zero set is
finite.

## References

* [LogNarayana], Section 6 (the signed Appell sequence).
-/

open Finset

namespace Polynomial

/-! ### Monicity and the derivative -/

/-- The signed Appell polynomial `η_m` is `t^m` plus terms of degree less than `m`:
`deg (η_m - t^m) < m`. -/
@[lognarayana "lem_signed_appell_monic"]
public theorem degree_signedAppell_sub_X_pow_lt (R : Type*) [Ring R] (m : ℕ) :
    (signedAppell R m - X ^ m).degree < (m : WithBot ℕ) := by
  rw [signedAppell, Finset.sum_range_succ']
  simp only [pow_zero, catalan_zero, Nat.cast_one, mul_one, Nat.choose_zero_right, mul_zero,
    Nat.sub_zero, map_one, one_mul, add_sub_cancel_right]
  refine lt_of_le_of_lt (degree_sum_le _ _) ?_
  refine (Finset.sup_lt_iff (WithBot.bot_lt_coe m)).2 fun j hj => ?_
  refine lt_of_le_of_lt (degree_C_mul_X_pow_le _ _) ?_
  have := Finset.mem_range.1 hj
  exact WithBot.coe_lt_coe.2 (Nat.sub_lt (by omega) (by omega))

/-- The sum defining `signedAppell R m` may be extended to any range past `m / 2`. -/
private lemma signedAppell_eq_sum_range {R : Type*} [Ring R] {m N : ℕ} (h : m / 2 < N) :
    signedAppell R m = ∑ j ∈ Finset.range N,
      C ((-1) ^ j * (catalan j : R) * (m.choose (2 * j) : R)) * X ^ (m - 2 * j) := by
  refine Finset.sum_subset (Finset.range_subset_range.2 (by omega)) fun j _ hj => ?_
  simp [Nat.choose_eq_zero_of_lt (show m < 2 * j by simp at hj; omega)]

/-- Term by term, `η_{n+1}' = (n+1) η_n`; this holds for every index `j`. -/
private lemma derivative_signedAppell_term {R : Type*} [Ring R] (n j : ℕ) :
    derivative (C ((-1) ^ j * (catalan j : R) * ((n + 1).choose (2 * j) : R)) *
      X ^ (n + 1 - 2 * j)) =
    ((n + 1 : ℕ) : R[X]) * (C ((-1) ^ j * (catalan j : R) * (n.choose (2 * j) : R)) *
      X ^ (n - 2 * j)) := by
  rw [derivative_C_mul_X_pow, ← C_eq_natCast, ← mul_assoc, ← C_mul,
    show n + 1 - 2 * j - 1 = n - 2 * j by omega, mul_assoc, mul_assoc, mul_assoc,
    ← Nat.cast_mul, ← Nat.choose_mul_succ_eq, Nat.cast_mul, (Nat.cast_commute (n + 1) _).eq]
  simp only [mul_assoc]

/-- The signed Appell polynomials form an Appell sequence: `η_m' = m η_{m-1}`. -/
@[lognarayana "lem_signed_appell_derivative"]
public theorem derivative_signedAppell (R : Type*) [Ring R] (m : ℕ) :
    derivative (signedAppell R m) = (m : R[X]) * signedAppell R (m - 1) := by
  rcases m with _ | n
  · simp [signedAppell]
  rw [signedAppell_eq_sum_range (N := n + 2) (by omega), Nat.add_sub_cancel,
    signedAppell_eq_sum_range (N := n + 2) (by omega), derivative_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => derivative_signedAppell_term n j

/-! ### First values, parity and the Appell property -/

/-- The first five signed Appell polynomials:
`(η_0, η_1, η_2, η_3, η_4) = (1, t, t² - 1, t³ - 3t, t⁴ - 6t² + 2)`. -/
@[lognarayana "lem_signed_appell_first_values"]
public theorem signedAppell_first_values (R : Type*) [Ring R] :
    signedAppell R 0 = 1 ∧
    signedAppell R 1 = X ∧
    signedAppell R 2 = X ^ 2 - 1 ∧
    signedAppell R 3 = X ^ 3 - 3 * X ∧
    signedAppell R 4 = X ^ 4 - 6 * X ^ 2 + 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [signedAppell, Finset.sum_range_succ, catalan_two, Nat.choose_succ_succ, sub_eq_add_neg]

/-- For `2j ≤ m`, `(-1)^(m-2j) = (-1)^m` in any monoid with a distributive negation. -/
private lemma neg_one_pow_sub_two_mul {R : Type*} [Monoid R] [HasDistribNeg R] {m j : ℕ}
    (h : 2 * j ≤ m) : (-1 : R) ^ (m - 2 * j) = (-1) ^ m := by
  conv_rhs => rw [← Nat.sub_add_cancel h, pow_add, pow_mul]
  simp

/-- The signed Appell polynomial `η_m` has the parity of `m`: `η_m(-t) = (-1)^m η_m(t)`. -/
@[lognarayana "lem_signed_appell_parity"]
public theorem signedAppell_comp_neg_X (R : Type*) [Ring R] (m : ℕ) :
    (signedAppell R m).comp (-X) = (-1) ^ m * signedAppell R m := by
  simp only [signedAppell, sum_comp, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [C_mul_comp, X_pow_comp, neg_pow (X : R[X]),
    neg_one_pow_sub_two_mul (by have := Finset.mem_range.mp hj; omega), ← mul_assoc, ← mul_assoc,
    ((Commute.neg_one_left _).pow_left m).eq]

/-- The signed Appell polynomials `(η_m)_{m ≥ 0}` form an Appell sequence. -/
@[lognarayana "lem_signed_appell_is_appell"]
public theorem isAppell_signedAppell (R : Type*) [Ring R] [Nontrivial R] :
    IsAppell (signedAppell R) := by
  refine ⟨fun m => ?_, fun m => by simp [derivative_signedAppell, nsmul_eq_mul]⟩
  rw [← sub_add_cancel (signedAppell R m) (X ^ m), degree_add_eq_right_of_degree_lt, degree_X_pow]
  simpa using degree_signedAppell_sub_X_pow_lt R m

/-! ### The binomial identity -/

private lemma map_signedAppell {R S : Type*} [Ring R] [Ring S] (f : R →+* S) (m : ℕ) :
    (signedAppell R m).map f = signedAppell S m := by
  simp [signedAppell, Polynomial.map_sum]

private lemma map_hasseDeriv_eq {R S : Type*} [Semiring R] [Semiring S] (f : R →+* S) (k : ℕ)
    (p : R[X]) : (hasseDeriv k p).map f = hasseDeriv k (p.map f) := by
  ext n
  simp [hasseDeriv_coeff]

private lemma iterate_derivative_signedAppell (R : Type*) [Ring R] (d k : ℕ) :
    derivative^[k] (signedAppell R d) = (d.descFactorial k : R[X]) * signedAppell R (d - k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, derivative_mul, derivative_natCast, zero_mul, zero_add,
      derivative_signedAppell, Nat.descFactorial_succ, ← mul_assoc, Nat.sub_sub]
    push_cast
    rw [← Nat.cast_mul, ← Nat.cast_mul, Nat.mul_comm, Nat.add_comm]

private lemma hasseDeriv_signedAppell_int (d k : ℕ) :
    hasseDeriv k (signedAppell ℤ d) = (d.choose k : ℤ[X]) * signedAppell ℤ (d - k) := by
  have h := congrFun (factorial_smul_hasseDeriv (R := ℤ) (k := k)) (signedAppell ℤ d)
  rw [iterate_derivative_signedAppell, Nat.descFactorial_eq_factorial_mul_choose,
    LinearMap.smul_apply] at h
  apply smul_right_injective ℤ[X] (Nat.factorial_ne_zero k)
  simp only [h, nsmul_eq_mul]
  push_cast
  ring

/-- The `k`-th Hasse derivative of `η_d` is `(d choose k) η_{d-k}`; proved over `ℤ`, where `k!` can
be cancelled, and transported along `ℤ → S`. -/
private lemma hasseDeriv_signedAppell (S : Type*) [CommRing S] (d k : ℕ) :
    hasseDeriv k (signedAppell S d) = (d.choose k : S[X]) * signedAppell S (d - k) := by
  rw [← map_signedAppell (Int.castRingHom S), ← map_hasseDeriv_eq, hasseDeriv_signedAppell_int,
    Polynomial.map_mul, map_signedAppell]
  simp

private lemma natDegree_signedAppell_le (R : Type*) [Ring R] (d : ℕ) :
    (signedAppell R d).natDegree ≤ d := by
  have h := degree_signedAppell_sub_X_pow_lt R d
  rw [← sub_add_cancel (signedAppell R d) (X ^ d)]
  refine (natDegree_add_le _ _).trans (max_le ?_ (natDegree_X_pow_le d))
  exact natDegree_le_iff_degree_le.2 h.le

/-- The binomial identity over the base ring itself, read off from the Taylor expansion of `η_d`
at `w`, whose `k`-th coefficient is `(d choose k) η_{d-k}(w)`. -/
private lemma eval_add_signedAppell (S : Type*) [CommRing S] (d : ℕ) (z w : S) :
    (signedAppell S d).eval (z + w) =
      ∑ m ∈ range (d + 1), (d.choose m : S) * (signedAppell S m).eval z * w ^ (d - m) := by
  rw [add_comm, ← taylor_eval, eval_eq_sum_range' (n := d + 1)
    (by rw [natDegree_taylor]; exact Nat.lt_succ_of_le (natDegree_signedAppell_le S d))]
  simp only [taylor_coeff, hasseDeriv_signedAppell, eval_mul, eval_natCast]
  rw [← sum_range_reflect]
  refine sum_congr rfl fun m hm => ?_
  have hm := mem_range.1 hm
  rw [show d + 1 - 1 - m = d - m by omega, show d - (d - m) = m by omega,
    Nat.choose_symm (by omega)]

/-- The signed Appell polynomials satisfy the binomial identity
`η_d(z + w) = ∑_{m=0}^{d} (d choose m) η_m(z) w^(d-m)`. -/
@[lognarayana "lem_signed_appell_binomial"]
public theorem aeval_add_signedAppell {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (d : ℕ) (z w : S) :
    aeval (z + w) (signedAppell R d) =
      ∑ m ∈ range (d + 1), (d.choose m : S) * aeval z (signedAppell R m) * w ^ (d - m) := by
  simp only [← eval_map_algebraMap, map_signedAppell, eval_add_signedAppell]

/-! ### The change of variables `t = r⁻¹ - r` -/

private lemma choose_identity {j k m : ℕ} (hjk : j ≤ k) (hkm : k ≤ m) :
    (2 * j).choose j * m.choose (2 * j) * (m - 2 * j).choose (k - j) =
      m.choose k * k.choose j * (m - k).choose j := by
  by_cases h : j + k ≤ m
  · have h1 := Nat.choose_mul (n := m) (k := 2 * j) (s := j) (by omega)
    have h2 := Nat.choose_mul (n := m) (k := k) (s := j) hjk
    have h3 := Nat.choose_mul (n := m - j) (k := k) (s := j) hjk
    have h4 := Nat.choose_mul (n := m - j) (k := k) (s := k - j) (by omega)
    rw [Nat.choose_symm hjk] at h4
    have e1 : 2 * j - j = j := by omega
    have e2 : m - j - j = m - 2 * j := by omega
    have e3 : m - j - (k - j) = m - k := by omega
    have e4 : k - (k - j) = j := by omega
    rw [e1] at h1
    rw [e2] at h3
    rw [e3, e4] at h4
    calc (2 * j).choose j * m.choose (2 * j) * (m - 2 * j).choose (k - j)
        = m.choose j * ((m - j).choose j * (m - 2 * j).choose (k - j)) := by
          rw [mul_comm ((2 * j).choose j), h1, mul_assoc]
      _ = m.choose j * ((m - j).choose (k - j) * (m - k).choose j) := by rw [← h3, h4]
      _ = _ := by rw [← mul_assoc, ← h2, mul_assoc]
  · have hr : (m - k).choose j = 0 := Nat.choose_eq_zero_of_lt (by omega)
    rw [hr, mul_zero]
    by_cases h' : 2 * j ≤ m
    · rw [Nat.choose_eq_zero_of_lt (n := m - 2 * j) (by omega), mul_zero]
    · rw [Nat.choose_eq_zero_of_lt (n := m) (by omega), mul_zero, zero_mul]

private lemma catalan_choose_mul {j k m : ℕ} (hjk : j ≤ k) (hkm : k ≤ m) :
    catalan j * m.choose (2 * j) * (m - 2 * j).choose (k - j) * (m + 1 - k) =
      m.choose k * k.choose j * (m + 1 - k).choose (j + 1) := by
  rw [show m + 1 - k = m - k + 1 by omega]
  refine Nat.eq_of_mul_eq_mul_left (Nat.succ_pos j) ?_
  calc (j + 1) * (catalan j * m.choose (2 * j) * (m - 2 * j).choose (k - j) * (m - k + 1))
      = (2 * j).choose j * m.choose (2 * j) * (m - 2 * j).choose (k - j) * (m - k + 1) := by
        rw [← Nat.centralBinom_eq_two_mul_choose, ← succ_mul_catalan_eq_centralBinom]; ring
    _ = m.choose k * k.choose j * ((m - k + 1) * (m - k).choose j) := by
        rw [choose_identity hjk hkm]; ring
    _ = _ := by rw [Nat.add_one_mul_choose_eq]; simp only [Nat.succ_eq_add_one]; ring

private lemma sum_choose_mul_choose_succ (k n : ℕ) :
    ∑ j ∈ range (k + 1), k.choose j * n.choose (j + 1) = (n + k).choose (k + 1) := by
  rw [Nat.add_choose_eq n k (k + 1), Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun a b : ℕ => n.choose a * k.choose b), Finset.sum_range_succ' _ (k + 1)]
  simp only [Nat.sub_zero, Nat.choose_succ_self, mul_zero, add_zero]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj : j ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  rw [show k + 1 - (j + 1) = k - j by omega, Nat.choose_symm hj, mul_comm]

private lemma sum_catalan_choose {k m : ℕ} (hkm : k ≤ m) :
    ∑ j ∈ range (k + 1), (catalan j * m.choose (2 * j) : ℝ) * (m - 2 * j).choose (k - j) =
      ((m + 1 : ℕ) : ℝ)⁻¹ * ((m + 1).choose (k + 1) : ℝ) * ((m + 1).choose k : ℝ) := by
  have hnat : (m + 1) * ∑ j ∈ range (k + 1),
      catalan j * m.choose (2 * j) * (m - 2 * j).choose (k - j) =
        (m + 1).choose (k + 1) * (m + 1).choose k := by
    refine Nat.eq_of_mul_eq_mul_right (show 0 < m + 1 - k by omega) ?_
    rw [mul_assoc, Finset.sum_mul, Finset.sum_congr rfl fun j hj =>
      catalan_choose_mul (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)) hkm]
    simp_rw [mul_assoc, ← Finset.mul_sum]
    rw [sum_choose_mul_choose_succ, show m + 1 - k + k = m + 1 by omega,
      ← Nat.choose_mul_succ_eq]
    ring
  rw [mul_assoc, eq_inv_mul_iff_mul_eq₀ (by positivity)]
  exact_mod_cast hnat

/-- The γ-expansion of the shifted Narayana polynomial:
`Ñ_m(x) = ∑_{j ≤ m/2} C_j (m choose 2j) x^j (1+x)^(m-2j)`. -/
private lemma shiftedNarayanaPolynomial_eq_sum_gamma (m : ℕ) :
    shiftedNarayanaPolynomial m =
      ∑ j ∈ range (m / 2 + 1),
        C ((catalan j : ℝ) * (m.choose (2 * j) : ℝ)) * X ^ j * (1 + X) ^ (m - 2 * j) := by
  ext k
  simp only [shiftedNarayanaPolynomial, finsetSum_coeff, coeff_C_mul_X_pow]
  simp_rw [mul_assoc, ← mul_comm ((1 + X : ℝ[X]) ^ _), coeff_C_mul, coeff_mul_X_pow',
    coeff_one_add_X_pow]
  rw [Finset.sum_ite_eq]
  set f : ℕ → ℝ := fun j => (catalan j : ℝ) * (m.choose (2 * j) : ℝ) *
    if j ≤ k then ((m - 2 * j).choose (k - j) : ℝ) else 0 with hf
  split_ifs with hk
  · have hkm : k ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
    have hR : ∑ j ∈ range (m / 2 + 1), f j = ∑ j ∈ range (m + 1), f j := by
      refine Finset.sum_subset (Finset.range_subset_range.2 (by omega)) fun j _ hj => ?_
      have : m < 2 * j := by simp only [Finset.mem_range] at hj; omega
      simp [hf, Nat.choose_eq_zero_of_lt this]
    have hL : ∑ j ∈ range (k + 1), (catalan j * m.choose (2 * j) : ℝ) *
        (m - 2 * j).choose (k - j) = ∑ j ∈ range (m + 1), f j := by
      calc _ = ∑ j ∈ range (k + 1), f j := Finset.sum_congr rfl fun j hj => by
              simp [hf, Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)]
        _ = _ := Finset.sum_subset (Finset.range_subset_range.2 (by omega)) fun j _ hj => by
              have : ¬ j ≤ k := by simp only [Finset.mem_range] at hj; omega
              simp [hf, this]
    rw [hR, ← hL, sum_catalan_choose hkm, mul_assoc]
  · have hkm : m < k := by simpa using hk
    refine (Finset.sum_eq_zero fun j hj => ?_).symm
    have : 2 * j ≤ m := by simp only [Finset.mem_range] at hj; omega
    simp [Nat.choose_eq_zero_of_lt (show m - 2 * j < k - j by omega)]

/-- For `r > 0`, `η_m(r⁻¹ - r) = r^(-m) Ñ_m(-r²)`. -/
@[lognarayana "lem_signed_appell_root_change"]
public theorem eval_signedAppell_inv_sub (m : ℕ) {r : ℝ} (hr : 0 < r) :
    (signedAppell ℝ m).eval (r⁻¹ - r) = r⁻¹ ^ m * (shiftedNarayanaPolynomial m).eval (-r ^ 2) := by
  rw [shiftedNarayanaPolynomial_eq_sum_gamma, signedAppell]
  simp only [eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, eval_add, eval_one,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  obtain ⟨n, rfl⟩ : ∃ n, m = 2 * j + n := ⟨m - 2 * j, by have := Finset.mem_range.1 hj; omega⟩
  have hr0 := hr.ne'
  rw [Nat.add_sub_cancel_left, show r⁻¹ - r = r⁻¹ * (1 + -r ^ 2) by field_simp; ring, mul_pow,
    show (-1 : ℝ) = r⁻¹ ^ 2 * -r ^ 2 by field_simp]
  ring

/-! ### Real zeros -/

/-- `η_m` is `X ^ m` plus lower-order terms. -/
private theorem X_pow_add_signedAppell_sub (m : ℕ) :
    X ^ m + (signedAppell ℝ m - X ^ m) = signedAppell ℝ m :=
  add_sub_cancel _ _

/-- `η_m` is monic. -/
private theorem monic_signedAppell (m : ℕ) : (signedAppell ℝ m).Monic :=
  X_pow_add_signedAppell_sub m ▸ monic_X_pow_add (degree_signedAppell_sub_X_pow_lt ℝ m)

/-- `η_m` has degree `m`. -/
private theorem natDegree_signedAppell (m : ℕ) : (signedAppell ℝ m).natDegree = m := by
  rw [← X_pow_add_signedAppell_sub, natDegree_add_eq_left_of_degree_lt
    (by simpa using degree_signedAppell_sub_X_pow_lt ℝ m), natDegree_X_pow]

/-- The change of variables `ρ ↦ (√-ρ)⁻¹ - √-ρ` is strictly increasing on `(-∞, 0)`. -/
private theorem strictMonoOn_inv_sqrt_neg_sub_sqrt_neg :
    StrictMonoOn (fun ρ : ℝ => (√(-ρ))⁻¹ - √(-ρ)) (Set.Iio 0) := by
  intro a _ b hb hab
  have hb' : 0 < √(-b) := Real.sqrt_pos.2 (neg_pos.2 hb)
  have h : √(-b) < √(-a) := Real.sqrt_lt_sqrt (neg_nonneg.2 (le_of_lt hb)) (neg_lt_neg hab)
  have : (√(-a))⁻¹ < (√(-b))⁻¹ := inv_strictAntiOn hb' (hb'.trans h) h
  dsimp only
  linarith

/-- The change of variables carries a negative zero `ρ` of `Ñ_m` to the zero
`(√-ρ)⁻¹ - √-ρ` of `η_m`. -/
private theorem eval_signedAppell_inv_sqrt_neg_sub_eq_zero (m : ℕ) {ρ : ℝ} (hρ : ρ < 0)
    (h : (shiftedNarayanaPolynomial m).IsRoot ρ) :
    (signedAppell ℝ m).eval ((√(-ρ))⁻¹ - √(-ρ)) = 0 := by
  rw [eval_signedAppell_inv_sub m (Real.sqrt_pos.2 (neg_pos.2 hρ)),
    Real.sq_sqrt (neg_nonneg.2 hρ.le), neg_neg, h.eq_zero, mul_zero]

/-- The lower bound: `η_m` has at least `m` roots, the images of the `m` negative zeros of
`Ñ_m` under the injective change of variables `ρ ↦ (√-ρ)⁻¹ - √-ρ`. -/
private theorem le_card_roots_signedAppell (hLW : ShiftedNarayanaNegRealRoots) (m : ℕ) :
    m ≤ (signedAppell ℝ m).roots.card := by
  have hp := (monic_signedAppell m).ne_zero
  have h : (m : ℕ∞) ≤ (signedAppell ℝ m).roots.toFinset.card := by
    rw [← Set.encard_coe_eq_coe_finsetCard, ← hLW m]
    refine Set.encard_le_encard_of_injOn (fun ρ hρ => ?_)
      (strictMonoOn_inv_sqrt_neg_sub_sqrt_neg.injOn.mono fun _ hρ => hρ.1)
    simpa [hp] using eval_signedAppell_inv_sqrt_neg_sub_eq_zero m hρ.1 hρ.2
  exact (by exact_mod_cast h : m ≤ _).trans (Multiset.toFinset_card_le _)

/-- For every `m ≥ 0`, the signed Appell polynomial `η_m` is real-rooted. -/
@[lognarayana "lem_signed_appell_real_rooted"]
public theorem splits_signedAppell (hLW : ShiftedNarayanaNegRealRoots) (m : ℕ) :
    (signedAppell ℝ m).Splits :=
  splits_iff_card_roots.2 <| (card_roots' _).antisymm <|
    (natDegree_signedAppell m).trans_le (le_card_roots_signedAppell hLW m)

/-- A nonzero polynomial over a field has at most `natDegree p` zeros. -/
private theorem encard_setOf_eval_eq_zero_le {K : Type*} [Field K] {p : K[X]} (hp : p ≠ 0) :
    {t : K | p.eval t = 0}.encard ≤ p.natDegree := by
  classical
  have : {t : K | p.eval t = 0} = (p.roots.toFinset : Set K) := by
    ext t; simp [hp]
  rw [this, Set.encard_coe_eq_coe_finsetCard]
  exact_mod_cast (Multiset.toFinset_card_le _).trans (card_roots' p)

/-- For every `m ≥ 0`, the set `{t ∈ ℝ : η_m(t) = 0}` of real zeros of the signed Appell
polynomial has exactly `m` elements. -/
@[lognarayana "lem_signed_appell_distinct_real_zeros"]
public theorem encard_setOf_eval_signedAppell_eq_zero (hN : ShiftedNarayanaNegRealRoots)
    (m : ℕ) :
    {t : ℝ | (signedAppell ℝ m).eval t = 0}.encard = m := by
  refine le_antisymm ?_ ?_
  · simpa [natDegree_signedAppell] using
      encard_setOf_eval_eq_zero_le (monic_signedAppell m).ne_zero
  · rw [← hN m]
    exact Set.encard_le_encard_of_injOn
      (fun ρ hρ => eval_signedAppell_inv_sqrt_neg_sub_eq_zero m hρ.1 hρ.2)
      (strictMonoOn_inv_sqrt_neg_sub_sqrt_neg.injOn.mono fun _ hρ => hρ.1)

end Polynomial
