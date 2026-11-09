/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib
public import LogNarayana.Attr
public import LogNarayana.Nestohedron.QuadraticReplacement.Defs
public import LogNarayana.StackSorting.AdoptableForest.Defs
public import LogNarayana.StackSorting.FiberPolynomials.Defs
public import LogNarayana.Lorentzian.QuadraticKernel.Defs
public import LogNarayana.Nestohedron.Fertilitope.Defs
public import LogNarayana.StackSorting.Descents.Defs
public import LogNarayana.Lorentzian.Hessian.Defs
public import LogNarayana.StackSorting.ValidHookConfigurations.Defs
public import LogNarayana.Polynomial.LogConcave.Defs
public import LogNarayana.StackSorting.Matchings.Defs
public import LogNarayana.Narayana.Polynomials.Defs
public import LogNarayana.StackSorting.StackSort.Defs
public import LogNarayana.Nestohedron.Fertilitope.Basic
public import LogNarayana.StackSorting.ValidHookConfigurations.Basic
public import LogNarayana.Lorentzian.Symbol.Basic
public import LogNarayana.Polynomial.LogConcave.Basic
public import LogNarayana.StackSorting.Matchings.Basic
public import LogNarayana.Narayana.Polynomials.Basic
public import LogNarayana.StackSorting.Peaks
public import LogNarayana.Lorentzian.BrandenHuh.Basic
public import LogNarayana.StackSorting.AdoptableForest.Basic
public import LogNarayana.Lorentzian.Bivariate
public import LogNarayana.Lorentzian.QuadraticKernel.Basic
public import LogNarayana.Forest.Weighted.Basic

/-!
# Quadratic replacements on fertilitopes

Let `P ⊆ ℝ^r` (`r ≥ 1`) be an integral binary nestohedron, let `a ∈ ℝ_{≥0}^p`, `A = aᵀ x`, and
let `B` be homogeneous of degree `2` with nonnegative coefficients and `Hess B - a aᵀ ⪯ 0`.
Replacing the variables of the bivariate Narayana polynomials `Q_m` by `A` and `B`, the
polynomial `B^{r-1} ∑_{q ∈ P ∩ ℤ^r} ∏_i Q_{q_i - 1}(A, B)` is Lorentzian and homogeneous of
degree `S + r - 2`, `S` being the common coordinate sum of the points of `P`.

The proof realizes `P ∩ ℤ^r` as the valid compositions of a permutation `π` (Defant), and
rewrites the polynomial as a weighted sum over the fiber matchings of `π`, through the identity
`Γ_π(z) = z^{des(π)} ∑_{𝐪 ∈ 𝒱(π)} ∏_i M_{q_i - 1}(z)` for the matching polynomial, which rests on
the uniqueness of `γ`-expansions. The specializations `A = e₁`, `B = e₂` and `A = x + y`,
`B = λ x y` give Lorentzian polynomials in the elementary symmetric polynomials and, by
dehomogenization, the ultra-log-concavity, log-concavity and absence of internal zeros of the
deformed Narayana sums `∑_{q ∈ P ∩ ℤ^r} ∏_i N_{q_i}^{(λ)}(x)` for `0 ≤ λ ≤ 2`.

## Main results

* `deformedNarayanaPolynomial_one`: `N_q^{(1)} = N_q` for `q ≥ 1`.
* `Polynomial.eq_of_sum_X_pow_mul_one_add_X_pow_eq`: uniqueness of `γ`-expansions.
* `List.fiberMatchingPolynomial_eq_sum_validCompositions`: the matching polynomial `Γ_π` through
  valid compositions.
* `List.finsum_fiberMatchings_eq_sum_validCompositions`: weighted matching sums over valid
  compositions.
* `MvPolynomial.hessianAtZero_esymm_two_sub_vecMulVec_one`: `Hess(e₂) - 𝟙 𝟙ᵀ = -1`.
* `MvPolynomial.isHomogeneous_pow_mul_finsum_latticePoints_prod_narayanaQ`: the quadratic
  replacement is homogeneous of degree `S + r - 2`.
* `MvPolynomial.isLorentzian_pow_mul_finsum_latticePoints_prod_narayanaQ`: the quadratic
  replacement is Lorentzian.
* `MvPolynomial.isLorentzian_esymm_two_pow_mul_finsum_latticePoints_prod_narayanaQ`: the
  replacement by `e₁` and `e₂` is Lorentzian.
* `MvPolynomial.isLorentzian_finsum_latticePoints_prod_mul_narayanaQ`: the product form
  `∑_q ∏_i (B · Q_{q_i - 1}(A, B))` is Lorentzian.
* `Polynomial.finsum_latticePoints_prod_deformedNarayanaPolynomial_zero`: the deformed Narayana
  sum at `λ = 0` is `|P ∩ ℤ^r| x^r (1 + x)^{S-r}`.
* `Polynomial.isUltraLogConcave_finsum_latticePoints_prod_deformedNarayanaPolynomial_zero` and
  `Polynomial.isUltraLogConcave_finsum_latticePoints_prod_deformedNarayanaPolynomial`: the
  deformed Narayana sums are ultra-log-concave for `λ = 0` and for `0 < λ ≤ 2`.
* `Polynomial.isLogConcave_finsum_latticePoints_prod_deformedNarayanaPolynomial` and
  `Polynomial.hasNoInternalZeros_coeff_finsum_latticePoints_prod_deformedNarayanaPolynomial`:
  for `0 ≤ λ ≤ 2` the deformed Narayana sums are log-concave with no internal zeros.

## Implementation notes

The coordinates of a lattice point `q` are real numbers; the index `q_i` is written `⌊q i⌋₊`,
which equals `q i` since the coordinates are positive integers (`pos_of_mem_nestohedron`). The
lattice points `P ∩ ℤ^r` form a finite set, and sums over them are `finsum`s over
`Set.latticePoints P`. `Q_m(A, B)` is `aeval ![A, B] (narayanaQ ℝ m)`, `a aᵀ` is
`Matrix.vecMulVec a a`, and `M ⪯ 0` is `(-M).PosSemidef`. The cited results the arguments rest
on — Defant's realization of integral binary nestohedra and refined fertility formula, the
`γ`-expansion of the shifted Narayana polynomials, and the properties of Lorentzian polynomials
of Brändén–Huh — are taken as hypotheses.

## References

* [LogNarayana]
* [BrandenHuh2020]
-/

open Polynomial

/-- For every integer `q ≥ 1`, the deformed Narayana polynomial at `λ = 1` is the Narayana
polynomial: `N_q^{(1)} = N_q`. -/
@[lognarayana "lem_deformed_narayana_one"]
public theorem deformedNarayanaPolynomial_one {q : ℕ} (hq : 1 ≤ q) :
    deformedNarayanaPolynomial ℝ 1 q = narayanaPolynomial q := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hq
  rw [narayanaPolynomial_succ_eq_X_mul,
    shiftedNarayanaPolynomial_eq_aeval_narayanaQ,
    deformedNarayanaPolynomial, Nat.add_sub_cancel, map_one, one_mul]

namespace Polynomial

open Finset

/-- A vanishing combination `∑ i < n, f i • X ^ i * (1 + X) ^ e i` has all coefficients `f i`
zero: the coefficient of `X ^ j` is `f j` plus terms with `i < j`. -/
private lemma eq_zero_of_sum_C_mul_X_pow_mul_one_add_X_pow {R : Type*} [CommSemiring R]
    {n : ℕ} {e : ℕ → ℕ} {f : ℕ → R}
    (hf : ∑ i ∈ range n, C (f i) * X ^ i * (1 + X) ^ e i = 0) : ∀ j < n, f j = 0 := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  intro hj
  have hc := congrArg (coeff · j) hf
  simp only [finsetSum_coeff, mul_assoc, coeff_C_mul, coeff_X_pow_mul', coeff_zero] at hc
  rw [Finset.sum_eq_single_of_mem j (mem_range.2 hj)] at hc
  · simpa [coeff_zero_eq_eval_zero] using hc
  · intro i hi hij
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · simp [ih i hlt (mem_range.1 hi)]
    · simp [show ¬ i ≤ j by omega]

/-- The coefficients of a gamma expansion are unique: if
`∑_{j=0}^{⌊d/2⌋} gⱼ xʲ (1+x)^(d-2j) = ∑_{j=0}^{⌊d/2⌋} hⱼ xʲ (1+x)^(d-2j)` in `ℝ[x]`, then
`gⱼ = hⱼ` for all `0 ≤ j ≤ ⌊d/2⌋`. -/
@[lognarayana "lem_gamma_expansion_unique"]
public theorem eq_of_sum_X_pow_mul_one_add_X_pow_eq (d : ℕ) (g h : ℕ → ℝ)
    (hgh : ∑ j ∈ range (d / 2 + 1), C (g j) * X ^ j * (1 + X) ^ (d - 2 * j) =
      ∑ j ∈ range (d / 2 + 1), C (h j) * X ^ j * (1 + X) ^ (d - 2 * j)) :
    ∀ j ≤ d / 2, g j = h j := by
  intro j hj
  refine sub_eq_zero.1 (eq_zero_of_sum_C_mul_X_pow_mul_one_add_X_pow (n := d / 2 + 1)
    (e := fun i => d - 2 * i) (f := g - h) ?_ j (by omega))
  simp [C_sub, sub_mul, sum_sub_distrib, hgh]

end Polynomial

namespace List

section GammaFertility

open Polynomial Finset

/-- The embedding `ℝ[x] → ℝ(x)`. -/
local notation "φ" => algebraMap ℝ[X] (RatFunc ℝ)

/-- The substitution point `t = x / (1 + x)^2` in `ℝ(x)`. -/
local notation "𝐭" => φ X / φ (1 + X) ^ 2

/-- In a field, `x^g y^(d - 2g) = y^d (x / y^2)^g` when `2g ≤ d` and `y ≠ 0`. -/
private lemma pow_mul_pow_sub_eq {K : Type*} [Field K] {x y : K} (hy : y ≠ 0) {g d : ℕ}
    (h : 2 * g ≤ d) : x ^ g * y ^ (d - 2 * g) = y ^ d * (x / y ^ 2) ^ g := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_sub_cancel_left, div_pow, pow_add, ← pow_mul]
  field_simp

private lemma algebraMap_ne_zero {p : ℝ[X]} (hp : p ≠ 0) : φ p ≠ 0 :=
  (map_ne_zero_iff _ (RatFunc.algebraMap_injective ℝ)).2 hp

private lemma algebraMap_one_add_X_ne_zero : φ (1 + X) ≠ 0 :=
  algebraMap_ne_zero fun h => by simpa [coeff_one] using congrArg (coeff · 1) h

/-- The image in `ℝ(x)` of a `γ`-sum of degree `d`: with `y = 1 + x` and `t = x / y^2`,
`∑_{g ≤ d/2} c_g x^g y^{d - 2g} = y^d ∑_{g ≤ d/2} c_g t^g`. -/
private lemma algebraMap_gammaSum (d : ℕ) (c : ℕ → ℝ) :
    φ (∑ g ∈ Finset.range (d / 2 + 1), C (c g) * X ^ g * (1 + X) ^ (d - 2 * g)) =
      φ (1 + X) ^ d * aeval 𝐭 (∑ g ∈ Finset.range (d / 2 + 1), C (c g) * X ^ g) := by
  simp only [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun g hg => ?_
  rw [mul_assoc, map_mul, map_mul, map_pow, map_pow,
    pow_mul_pow_sub_eq algebraMap_one_add_X_ne_zero (by have := Finset.mem_range.1 hg; omega),
    map_mul, aeval_C, map_pow, aeval_X,
    show (C (c g) : ℝ[X]) = algebraMap ℝ ℝ[X] (c g) from rfl, ← IsScalarTower.algebraMap_apply]
  ring

/-- Substituting `t = x / (1 + x)^2` is injective on polynomials of degree at most `d / 2`:
this is uniqueness of `γ`-vectors, read in `ℝ(x)`. -/
private lemma eq_of_aeval_eq {d : ℕ} {P Q : ℝ[X]} (hP : P.natDegree ≤ d / 2)
    (hQ : Q.natDegree ≤ d / 2) (h : aeval 𝐭 P = aeval 𝐭 Q) : P = Q := by
  have hrepr : ∀ P : ℝ[X], P.natDegree ≤ d / 2 →
      φ (∑ g ∈ Finset.range (d / 2 + 1), C (P.coeff g) * X ^ g * (1 + X) ^ (d - 2 * g)) =
        φ (1 + X) ^ d * aeval 𝐭 P := fun P hP => by
    rw [algebraMap_gammaSum, ← as_sum_range_C_mul_X_pow' P (by omega)]
  have hcoeff := eq_of_sum_X_pow_mul_one_add_X_pow_eq d (P.coeff ·) (Q.coeff ·)
    (RatFunc.algebraMap_injective ℝ (by rw [hrepr P hP, hrepr Q hQ, h]))
  ext g
  by_cases hg : g ≤ d / 2
  · exact hcoeff g hg
  · rw [coeff_eq_zero_of_natDegree_lt (by omega), coeff_eq_zero_of_natDegree_lt (by omega)]

private lemma fiberMatchingPolynomial_eq_sum (π : List ℕ) :
    π.fiberMatchingPolynomial ℝ = ∑ M ∈ (List.fiberMatchings_finite π).toFinset, X ^ M.card :=
  finsum_mem_eq_finite_toFinset_sum _ (List.fiberMatchings_finite π)

private lemma two_mul_card_le {n : ℕ} {π : List ℕ} (hπ : π ∈ permWords n) {M}
    (hM : M ∈ (List.fiberMatchings_finite π).toFinset) : 2 * M.card ≤ n - 1 := by
  have :=
    ((List.fiberMatchings_finite π).mem_toFinset.1 hM).1.card_unmatchedVertices_add_two_mul_card
  have := hπ.2.1
  omega

/-- The matching expansion of `D_π`, read in `ℝ(x)`: `D_π = (1 + x)^(n-1) Γ_π(t)`. -/
private lemma algebraMap_fiberDescentPolynomial_eq_aeval_fiberMatchingPolynomial {n : ℕ}
    (hn : 1 ≤ n) {π : List ℕ} (hπ : π ∈ permWords n) :
    φ (π.fiberDescentPolynomial ℝ) =
      φ (1 + X) ^ (n - 1) * aeval 𝐭 (π.fiberMatchingPolynomial ℝ) := by
  rw [List.fiberDescentPolynomial_eq_finsum_fiberMatchings ℝ hn hπ,
    finsum_mem_eq_finite_toFinset_sum _ (List.fiberMatchings_finite π),
    fiberMatchingPolynomial_eq_sum]
  simp only [map_sum, Finset.mul_sum, map_mul, map_pow, aeval_X]
  exact Finset.sum_congr rfl fun M hM => pow_mul_pow_sub_eq algebraMap_one_add_X_ne_zero
    (two_mul_card_le hπ hM)

/-- The parts of a valid composition of `π ∈ 𝔖_n` are positive and
`∑_i (q_i - 1) + 2 des(π) = n - 1`. -/
private lemma validComposition_parts {n : ℕ} (hn : 1 ≤ n) {π : List ℕ} (hπ : π ∈ permWords n)
    {q : Fin (π.numDescents + 1) → ℕ} (hq : q ∈ π.validCompositions) :
    (∀ i, 1 ≤ q i) ∧ ∑ i, (q i - 1) + 2 * π.numDescents = n - 1 := by
  have hqc := List.mem_compositionTuple_of_mem_validCompositions hn hπ hq
  simp only [Finset.Nat.compositionTuple, Finset.mem_filter,
    Finset.Nat.mem_antidiagonalTuple] at hqc
  obtain ⟨hsum, hpos⟩ := hqc
  have : ∑ i, (q i - 1) + ∑ _i : Fin (π.numDescents + 1), 1 = ∑ i, q i := by
    rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun i _ => Nat.sub_add_cancel (hpos i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at this
  exact ⟨hpos, by omega⟩

/-- The refined fertility formula, read in `ℝ(x)`:
`D_π = (1 + x)^(n-1) R(t)` with `R = z^k ∑_{𝐪 ∈ 𝒱(π)} ∏_i M_{q_i - 1}`. -/
private lemma algebraMap_fiberDescentPolynomial_eq_aeval_validCompositions
    (hfert : RefinedFertilityFormula)
    {n : ℕ} (hn : 1 ≤ n) {π : List ℕ} (hπ : π ∈ permWords n) :
    φ (π.fiberDescentPolynomial ℝ) = φ (1 + X) ^ (n - 1) * aeval 𝐭 (X ^ π.numDescents *
      ∑ q ∈ π.validCompositions, ∏ i : Fin (π.numDescents + 1), narayanaM ℝ (q i - 1)) := by
  have hy := algebraMap_one_add_X_ne_zero
  have hN {q : ℕ} (hq : 1 ≤ q) : φ (narayanaPolynomial q) =
      φ X * (φ (1 + X) ^ (q - 1) * aeval 𝐭 (narayanaM ℝ (q - 1))) := by
    rw [← Nat.sub_add_cancel hq, narayanaPolynomial_succ_eq_X_mul, map_mul, Nat.add_sub_cancel,
      shiftedNarayanaGammaExpansion_holds, algebraMap_gammaSum]
    rfl
  refine mul_left_cancel₀ (algebraMap_ne_zero X_ne_zero) ?_
  rw [← map_mul, hfert n hn π hπ]
  simp only [map_mul, map_pow, map_sum, map_prod, aeval_X, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q hq => ?_
  obtain ⟨hpos, hrest⟩ := validComposition_parts hn hπ hq
  rw [Finset.prod_congr rfl fun i _ => hN (hpos i),
    Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin,
    Finset.prod_pow_eq_pow_sum, show ∑ i, (q i - 1) = n - 1 - 2 * π.numDescents by omega]
  generalize ∏ i, aeval 𝐭 (narayanaM ℝ (q i - 1)) = Pr
  linear_combination (φ X * Pr) *
    pow_mul_pow_sub_eq (x := φ X) (g := π.numDescents) (d := n - 1) hy (by omega)

private lemma natDegree_narayanaM_le (m : ℕ) : (narayanaM ℝ m).natDegree ≤ m / 2 :=
  natDegree_sum_le_of_forall_le _ _ fun j hj =>
    (natDegree_C_mul_X_pow_le _ _).trans (by have := Finset.mem_range.1 hj; omega)

private lemma natDegree_fiberMatchingPolynomial_le {n : ℕ} {π : List ℕ} (hπ : π ∈ permWords n) :
    (π.fiberMatchingPolynomial ℝ).natDegree ≤ (n - 1) / 2 := by
  rw [fiberMatchingPolynomial_eq_sum]
  exact natDegree_sum_le_of_forall_le _ _ fun M hM =>
    (natDegree_X_pow_le _).trans (by have := two_mul_card_le hπ hM; omega)

private lemma natDegree_validCompositions_le {n : ℕ} (hn : 1 ≤ n) {π : List ℕ}
    (hπ : π ∈ permWords n) :
    (X ^ π.numDescents * ∑ q ∈ π.validCompositions,
      ∏ i : Fin (π.numDescents + 1), narayanaM ℝ (q i - 1)).natDegree ≤ (n - 1) / 2 := by
  rcases π.validCompositions.eq_empty_or_nonempty with hV | ⟨q₀, hq₀⟩
  · simp [hV]
  have h2k := (validComposition_parts hn hπ hq₀).2
  refine natDegree_mul_le.trans <| (add_le_add (natDegree_X_pow_le _) <|
    natDegree_sum_le_of_forall_le _ _ (n := (n - 1 - 2 * π.numDescents) / 2) fun q hq => ?_).trans
      (by omega)
  obtain ⟨-, hrest⟩ := validComposition_parts hn hπ hq
  refine (natDegree_prod_le _ _).trans <|
    (Finset.sum_le_sum fun i _ => natDegree_narayanaM_le (q i - 1)).trans ?_
  rw [show n - 1 - 2 * π.numDescents = ∑ i, (q i - 1) by omega, Nat.le_div_iff_mul_le two_pos,
    Finset.sum_mul]
  exact Finset.sum_le_sum fun i _ => Nat.div_mul_le_self _ _

/-- For `n ≥ 1` and `π ∈ S_n`,
`Γ_π(z) = z^{des(π)} ∑_{𝐪 ∈ 𝒱(π)} ∏_{i=0}^{des(π)} M_{q_i - 1}(z)`. -/
@[lognarayana "lem_gamma_fertility"]
public theorem fiberMatchingPolynomial_eq_sum_validCompositions
    (hfert : RefinedFertilityFormula)
    {n : ℕ} (hn : 1 ≤ n) {π : List ℕ} (hπ : π ∈ permWords n) :
    π.fiberMatchingPolynomial ℝ =
      X ^ π.numDescents *
        ∑ q ∈ π.validCompositions, ∏ i : Fin (π.numDescents + 1), narayanaM ℝ (q i - 1) :=
  eq_of_aeval_eq (natDegree_fiberMatchingPolynomial_le hπ) (natDegree_validCompositions_le hn hπ) <|
    mul_left_cancel₀ (pow_ne_zero (n - 1) algebraMap_one_add_X_ne_zero) <|
      (algebraMap_fiberDescentPolynomial_eq_aeval_fiberMatchingPolynomial hn hπ).symm.trans
        (algebraMap_fiberDescentPolynomial_eq_aeval_validCompositions hfert hn hπ)

end GammaFertility

section MatchingIdentity

open Polynomial Finset

variable {S : Type*} [CommRing S] [Algebra ℝ S]

/-- The weight-`d` homogenisation `∑_g c_g z^g ↦ ∑_g c_g B^g A^{d - 2g}`. -/
private noncomputable def homog (A B : S) (d : ℕ) : ℝ[X] →ₗ[ℝ] S :=
  Polynomial.lsum fun g => LinearMap.toSpanSingleton ℝ S (B ^ g * A ^ (d - 2 * g))

private lemma homog_monomial (A B : S) (d g : ℕ) (c : ℝ) :
    homog A B d (monomial g c) = c • (B ^ g * A ^ (d - 2 * g)) := by
  simp [homog, Polynomial.lsum_apply]

private lemma homog_X_pow (A B : S) (d g : ℕ) :
    homog A B d (X ^ g) = B ^ g * A ^ (d - 2 * g) := by
  rw [← monomial_one_right_eq_X_pow, homog_monomial, one_smul]

private lemma homog_eq_sum (A B : S) {d : ℕ} {P : ℝ[X]} (hP : 2 * P.natDegree ≤ d) :
    homog A B d P = ∑ a ∈ Finset.range (d / 2 + 1), P.coeff a • (B ^ a * A ^ (d - 2 * a)) := by
  conv_lhs => rw [P.as_sum_range' (d / 2 + 1) (by omega)]
  simp [map_sum, homog_monomial]

private lemma homog_mul (A B : S) {d e : ℕ} {P Q : ℝ[X]} (hP : 2 * P.natDegree ≤ d)
    (hQ : 2 * Q.natDegree ≤ e) :
    homog A B (d + e) (P * Q) = homog A B d P * homog A B e Q := by
  rw [homog_eq_sum A B hP, homog_eq_sum A B hQ, Finset.sum_mul_sum]
  conv_lhs => rw [P.as_sum_range' (d / 2 + 1) (by omega), Q.as_sum_range' (e / 2 + 1) (by omega),
    Finset.sum_mul_sum]
  simp only [map_sum, monomial_mul_monomial, homog_monomial]
  refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => ?_
  have ha := Finset.mem_range.1 ha
  have hb := Finset.mem_range.1 hb
  rw [show d + e - 2 * (a + b) = (d - 2 * a) + (e - 2 * b) by omega, pow_add, pow_add,
    smul_mul_smul_comm]
  congr 1
  ring

private lemma two_mul_natDegree_prod_le {ι : Type*} (s : Finset ι) (f : ι → ℝ[X]) (d : ι → ℕ)
    (hf : ∀ i ∈ s, 2 * (f i).natDegree ≤ d i) : 2 * (∏ i ∈ s, f i).natDegree ≤ ∑ i ∈ s, d i :=
  (Nat.mul_le_mul_left 2 (natDegree_prod_le s f)).trans <|
    Finset.mul_sum s _ 2 ▸ Finset.sum_le_sum hf

private lemma homog_prod (A B : S) {ι : Type*} (s : Finset ι) (f : ι → ℝ[X]) (d : ι → ℕ)
    (hf : ∀ i ∈ s, 2 * (f i).natDegree ≤ d i) :
    homog A B (∑ i ∈ s, d i) (∏ i ∈ s, f i) = ∏ i ∈ s, homog A B (d i) (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using homog_X_pow A B 0 0
  | insert j s hj ih =>
    have hs : ∀ i ∈ s, 2 * (f i).natDegree ≤ d i := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    rw [Finset.sum_insert hj, Finset.prod_insert hj, Finset.prod_insert hj,
      homog_mul A B (hf j (Finset.mem_insert_self j s)) (two_mul_natDegree_prod_le s f d hs), ih hs]

private lemma two_mul_natDegree_narayanaM_le (m : ℕ) : 2 * (narayanaM ℝ m).natDegree ≤ m := by
  have := natDegree_narayanaM_le m
  omega

private lemma homog_narayanaM (A B : S) (m : ℕ) :
    homog A B m (narayanaM ℝ m) = MvPolynomial.aeval ![A, B] (narayanaQ ℝ m) := by
  simp only [narayanaM, narayanaQ, map_sum, map_mul, map_pow, MvPolynomial.aeval_C,
    MvPolynomial.aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← C_mul, C_mul_X_pow_eq_monomial, homog_monomial, Algebra.smul_def, map_mul]
  simp only [map_natCast]
  ring

/-- The homogenisation sends the fiber-matching polynomial `Γ_π` to the weighted matching sum. -/
private lemma homog_fiberMatchingPolynomial (A B : S) (d : ℕ) (π : List ℕ) :
    homog A B d (π.fiberMatchingPolynomial ℝ) =
      ∑ᶠ M ∈ π.fiberMatchings, B ^ M.card * A ^ (d - 2 * M.card) := by
  rw [List.fiberMatchingPolynomial,
    finsum_mem_eq_finite_toFinset_sum _ (List.fiberMatchings_finite π),
    finsum_mem_eq_finite_toFinset_sum _ (List.fiberMatchings_finite π), map_sum]
  simp only [homog_X_pow]

end MatchingIdentity

open MvPolynomial

/-- For `π ∈ S_n` with `n ≥ 1` and `A, B ∈ ℝ[𝐱]`,
`∑_{M ∈ 𝒜(π)} B^{|M|} A^{n-1-2|M|} = B^{des(π)} ∑_{𝐪 ∈ 𝒱(π)} ∏_{i=0}^{des(π)} Q_{q_i-1}(A, B)`. -/
@[lognarayana "lem_kernel_polytope_matching_identity"]
public theorem finsum_fiberMatchings_eq_sum_validCompositions
    (hfert : RefinedFertilityFormula) {σ : Type*}
    {n : ℕ} (hn : 1 ≤ n) {π : List ℕ} (hπ : π ∈ permWords n) (A B : MvPolynomial σ ℝ) :
    ∑ᶠ M ∈ π.fiberMatchings, B ^ M.card * A ^ (n - 1 - 2 * M.card) =
      B ^ π.numDescents * ∑ q ∈ π.validCompositions,
        ∏ i : Fin (π.numDescents + 1), aeval ![A, B] (narayanaQ ℝ (q i - 1)) := by
  rw [← homog_fiberMatchingPolynomial,
    List.fiberMatchingPolynomial_eq_sum_validCompositions hfert hn hπ, Finset.mul_sum,
    map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q hq => ?_
  have hM : ∀ i ∈ (Finset.univ : Finset (Fin (π.numDescents + 1))),
      2 * (narayanaM ℝ (q i - 1)).natDegree ≤ q i - 1 := fun i _ => two_mul_natDegree_narayanaM_le _
  have hparts : 2 * π.numDescents + ∑ i, (q i - 1) = n - 1 := by
    have := (validComposition_parts hn hπ hq).2
    omega
  rw [← hparts,
    homog_mul A B (by rw [Polynomial.natDegree_X_pow]) (two_mul_natDegree_prod_le _ _ _ hM),
    homog_X_pow,
    Nat.sub_self, pow_zero, mul_one, homog_prod A B _ _ _ hM]
  simp only [homog_narayanaM]

end List

namespace MvPolynomial

section E2KernelMatrix

open Finsupp

/-- `∂^0` is the identity. -/
private lemma iteratedPDeriv_zero' {σ R : Type*} [CommSemiring R] (g : MvPolynomial σ R) :
    iteratedPDeriv 0 g = g := by
  suffices H : (iteratedPDeriv 0 : MvPolynomial σ R →ₗ[R] _) = LinearMap.id by
    rw [H]; rfl
  refine (basisMonomials σ R).ext fun β => ?_
  rw [iteratedPDeriv, Module.Basis.constr_basis]
  simp [coe_basisMonomials, Nat.div_self (factorial_pos β)]

/-- The `(i, j)` entry of the Hessian at the origin is the coefficient of `z_i z_j`, doubled
on the diagonal. -/
private lemma hessianAtZero_apply_eq_coeff {σ R : Type*} [CommSemiring R]
    (g : MvPolynomial σ R) (i j : σ) :
    hessianAtZero g i j = coeff (single j 1 + single i 1) g * ((single j 1 i : ℕ) + 1 : R) := by
  rw [hessianAtZero, Matrix.of_apply, ← zero_add (single i 1), iteratedPDeriv_add_single,
    iteratedPDeriv_add_single, iteratedPDeriv_zero', constantCoeff_eq,
    coeff_pderiv, coeff_pderiv, zero_add]
  simp

/-- The value at `k` of the indicator multi-index of a finset. -/
private lemma sum_single_apply {σ : Type*} [DecidableEq σ] (t : Finset σ) (k : σ) :
    (∑ l ∈ t, single l 1 : σ →₀ ℕ) k = if k ∈ t then 1 else 0 := by
  simp [Finsupp.finsetSum_apply, single_apply]

/-- The coefficient of `z_i z_j` in `e₂` is `0` on the diagonal and `1` off it. -/
private lemma coeff_esymm_two {σ R : Type*} [Fintype σ] [DecidableEq σ] [CommSemiring R]
    (i j : σ) :
    coeff (single j 1 + single i 1) (esymm σ R 2) = if i = j then 0 else 1 := by
  rw [esymm_eq_sum_monomial, coeff_sum]
  simp only [coeff_monomial]
  split_ifs with hij
  · subst hij
    refine Finset.sum_eq_zero fun t _ => if_neg fun h => ?_
    have := congrArg (· i) h
    simp only [sum_single_apply, Finsupp.coe_add, Pi.add_apply, single_eq_same] at this
    split_ifs at this
    omega
  · rw [Finset.sum_eq_single {i, j}, if_pos (by rw [Finset.sum_pair hij, add_comm])]
    · intro t _ ht
      refine if_neg fun h => ht ?_
      ext k
      have := congrArg (· k) h
      simp only [sum_single_apply, Finsupp.coe_add, Pi.add_apply, single_apply] at this
      simp only [Finset.mem_insert, Finset.mem_singleton]
      split_ifs at this <;> grind
    · simp [Finset.card_pair hij]

/-- The Hessian of `e₂` minus the all-ones matrix `a aᵀ` (with `a = (1, …, 1)`) is `-I`. -/
@[lognarayana "lem_e2_kernel_matrix"]
public theorem hessianAtZero_esymm_two_sub_vecMulVec_one {σ R : Type*} [Fintype σ]
    [DecidableEq σ] [CommRing R] :
    hessianAtZero (esymm σ R 2) - Matrix.vecMulVec (1 : σ → R) 1 = -1 := by
  ext i j
  rw [Matrix.sub_apply, hessianAtZero_apply_eq_coeff, coeff_esymm_two]
  by_cases hij : i = j
  · simp [hij]
  · simp [hij]

end E2KernelMatrix

/-- A positive real number that is an integer is the cast of its natural floor, which is
at least `1`. -/
private lemma natFloor_cast_eq {x : ℝ} (hx : 0 < x) (hz : x ∈ Set.range (Int.cast : ℤ → ℝ)) :
    ((⌊x⌋₊ : ℕ) : ℝ) = x ∧ 1 ≤ ⌊x⌋₊ := by
  obtain ⟨n, rfl⟩ := hz
  lift n to ℕ using (by exact_mod_cast hx.le : (0 : ℤ) ≤ n)
  simp only [Int.cast_natCast, Nat.floor_natCast, true_and]
  exact_mod_cast hx

/-- The degree count: if `q` has positive integer coordinates summing to `S`, then
`2 (r - 1) + ∑ i, (⌊q i⌋₊ - 1) = S + r - 2`. -/
private lemma two_mul_add_sum_natFloor_sub_one {r S : ℕ} (hr : 1 ≤ r) {q : Fin r → ℝ}
    (hpos : ∀ i, 0 < q i) (hint : ∀ i, q i ∈ Set.range (Int.cast : ℤ → ℝ))
    (hS : ∑ i, q i = S) :
    2 * (r - 1) + ∑ i, (⌊q i⌋₊ - 1) = S + r - 2 := by
  have h i := natFloor_cast_eq (hpos i) (hint i)
  have hsum : ∑ i, ⌊q i⌋₊ = S := by
    exact_mod_cast (by push_cast; simp_rw [fun i => (h i).1]; exact hS :
      ((∑ i, ⌊q i⌋₊ : ℕ) : ℝ) = S)
  have hrS : r ≤ S := by
    simpa [hsum] using Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => (h i).2
  rw [Finset.sum_tsub_distrib _ fun i _ => (h i).2, hsum]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
  omega

/-- Let `P ⊆ ℝ^r`, `r ≥ 1`, be an integral binary nestohedron whose points all have coordinate
sum `S`, and let `A`, `B` be homogeneous of degrees `1` and `2`. Then
`B^{r-1} ∑_{q ∈ P ∩ ℤ^r} ∏_i Q_{q_i - 1}(A, B)` is homogeneous of degree `S + r - 2`. -/
@[lognarayana "thm_kernel_polytope_degree"]
public theorem isHomogeneous_pow_mul_finsum_latticePoints_prod_narayanaQ
    {r : ℕ} (hr : 1 ≤ r) {P : Set (Fin r → ℝ)} (hP : IsIntegralBinaryNestohedron ℝ P)
    {S : ℕ} (hS : ∀ v ∈ P, ∑ i, v i = S)
    {σ : Type*} {A B : MvPolynomial σ ℝ} (hA : A.IsHomogeneous 1) (hB : B.IsHomogeneous 2) :
    (B ^ (r - 1) * ∑ᶠ q ∈ P.latticePoints,
      ∏ i, aeval ![A, B] (narayanaQ ℝ (⌊q i⌋₊ - 1))).IsHomogeneous (S + r - 2) := by
  obtain ⟨⟨𝓑, h𝓑, c, hc, rfl⟩, -⟩ := hP
  refine finsum_mem_induction (fun p => (B ^ (r - 1) * p).IsHomogeneous (S + r - 2))
    (by simpa using isHomogeneous_zero _ _ _) (fun _ _ h₁ h₂ => mul_add (B ^ (r - 1)) _ _ ▸
      h₁.add h₂) fun q hq => ?_
  rw [← two_mul_add_sum_natFloor_sub_one hr (pos_of_mem_nestohedron h𝓑 hc hq.1) hq.2
    (hS q hq.1)]
  exact (hB.pow _).mul (IsHomogeneous.prod _ _ _ fun i _ => hA.aeval_narayanaQ hB _)

section KernelPolytopeLorentzian

open Matrix

open scoped Classical in
/-- The admissible matchings on `[N]` are the admissible subsets of `[N] × [N]`. -/
private lemma setOf_isAdmissibleMatching_eq_filter (N : ℕ) (par : ℕ → Option ℕ) (L : Finset ℕ) :
    {M | IsAdmissibleMatching N par L M} =
      ↑((Finset.Icc 1 N ×ˢ Finset.Icc 1 N).powerset.filter
        (fun M : Finset (ℕ × ℕ) => IsAdmissibleMatching N par L M)) := by
  ext M
  simp only [Set.mem_ofPred_eq, Finset.coe_filter, Finset.mem_powerset, iff_and_self]
  intro hM x hx
  have h := hM.isNoncrossingPartialMatching
  have := h.one_le_fst x hx
  have := h.fst_lt_snd x hx
  have := h.snd_le x hx
  simp only [Finset.mem_product, Finset.mem_Icc]
  omega

/-- The descents of a list of length `ℓ` lie in `[ℓ - 1]`. -/
private lemma descentSet_subset_Icc {α : Type*} [LT α] [DecidableLT α] (π : List α) :
    π.descentSet ⊆ Finset.Icc 1 (π.length - 1) := fun v hv => by
  have := (Finset.mem_filter.1 hv).1
  simp only [Finset.mem_Ico, Finset.mem_Icc] at this ⊢
  omega

/-- `-C ⪰ 0` written as a quadratic form: `wᵀ C w ≤ 0`. -/
private lemma dotProduct_mulVec_nonpos_of_posSemidef_neg {σ : Type*} [Fintype σ]
    {C : Matrix σ σ ℝ} (hC : (-C).PosSemidef) (w : σ → ℝ) : w ⬝ᵥ (C *ᵥ w) ≤ 0 := by
  have := hC.dotProduct_mulVec_nonneg w
  simp only [star_trivial, Matrix.neg_mulVec, dotProduct_neg] at this
  linarith

/-- Let `P ⊆ ℝ^r`, `r ≥ 1`, be an integral binary nestohedron, `a ∈ ℝ_{≥0}^p`, `A = aᵀ x`, and
`B` homogeneous of degree `2` with nonnegative coefficients and `Hess B - a aᵀ ⪯ 0`. Then
`B^{r-1} ∑_{q ∈ P ∩ ℤ^r} ∏_i Q_{q_i - 1}(A, B)` is Lorentzian. -/
@[lognarayana "thm_kernel_polytope_lorentzian"]
public theorem isLorentzian_pow_mul_finsum_latticePoints_prod_narayanaQ
    (hreal : IntegralBinaryNestohedronRealization)
    (hfert : RefinedFertilityFormula)
    (hsub : ∀ (σ τ : Type) [Fintype σ] [Fintype τ], LorentzianNonnegLinearSubstitution σ τ)
    (hder : ∀ (σ : Type) [Fintype σ], LorentzianNonnegDerivative σ)
    (hmul : ∀ (σ : Type) [Fintype σ], LorentzianMul σ)
    (hBH : ∀ (σ : Type) [Fintype σ], NormalizedSupportPolyLorentzianOfMConvex σ)
    (hsym : ∀ (σ τ : Type) [Fintype σ] [Fintype τ], BrandenHuhSymbolTheorem σ τ)
    {r : ℕ} (hr : 1 ≤ r) {P : Set (Fin r → ℝ)} (hP : IsIntegralBinaryNestohedron ℝ P)
    {p : ℕ} {a : Fin p → ℝ} (ha : ∀ j, 0 ≤ a j)
    {B : MvPolynomial (Fin p) ℝ} (hB : B.IsHomogeneous 2) (hBnn : B.HasNonnegCoeffs)
    (hHess : (-(hessianAtZero B - Matrix.vecMulVec a a)).PosSemidef) :
    (B ^ (r - 1) * ∑ᶠ q ∈ P.latticePoints,
      ∏ i, aeval ![∑ j, C (a j) * X j, B] (narayanaQ ℝ (⌊q i⌋₊ - 1))).IsLorentzian := by
  classical
  obtain ⟨n, hn, π, hπ, rfl, hlat⟩ := hreal r hr P hP
  have hlen : π.length = n := hπ.2.1
  have hinj : Set.InjOn (fun (q : Fin (π.numDescents + 1) → ℕ) i => (q i : ℝ))
      π.validCompositions := fun q _ q' _ h => _root_.funext fun i => by simpa using congrFun h i
  rw [hlat, finsum_mem_image (by simpa using hinj), finsum_mem_coe_finset]
  simp only [Fin.cast_eq_self, Nat.floor_natCast, Nat.add_sub_cancel]
  rw [← List.finsum_fiberMatchings_eq_sum_validCompositions hfert hn hπ,
    List.fiberMatchings_eq_setOf_isAdmissibleMatching hπ, setOf_isAdmissibleMatching_eq_filter,
    finsum_mem_coe_finset, show ∑ j, C (a j) * X j = ∑ j, a j • (X j : MvPolynomial (Fin p) ℝ) by
      simp [smul_eq_C_mul]]
  exact isLorentzian_sum_admissibleMatching_pow_mul_pow hsub hmul hsym hBH hder
    (hlen ▸ List.isPostorderForest_adoptableForest π) (hlen ▸ descentSet_subset_Icc π)
    (fun v hv => List.isLeaf_adoptableForest_of_mem_descentSet π hv) a B ha hB hBnn
    (dotProduct_mulVec_nonpos_of_posSemidef_neg hHess)

end KernelPolytopeLorentzian

/-- The elementary symmetric polynomials have nonnegative coefficients. -/
private lemma hasNonnegCoeffs_esymm {σ R : Type*} [Fintype σ] [CommSemiring R] [PartialOrder R]
    [IsOrderedRing R] (k : ℕ) : (esymm σ R k).HasNonnegCoeffs := by
  classical
  intro α
  rw [esymm_eq_sum_monomial, coeff_sum]
  exact Finset.sum_nonneg fun t _ => by
    rw [coeff_monomial]; split_ifs <;> simp

/-- `e_k` is homogeneous of degree `k`. -/
private lemma isHomogeneous_esymm (σ R : Type*) [Fintype σ] [CommSemiring R] (k : ℕ) :
    (esymm σ R k).IsHomogeneous k := by
  classical
  rw [esymm_eq_sum_monomial]
  refine IsHomogeneous.sum _ _ _ fun t ht => isHomogeneous_monomial _ ?_
  rw [Finset.mem_powersetCard] at ht
  rw [← ht.2, map_sum, Finset.card_eq_sum_ones]
  simp

/-- The sum of the variables is `e₁`. -/
private lemma sum_C_one_mul_X_eq_esymm_one (m : ℕ) :
    ∑ j, C (1 : ℝ) * X j = esymm (Fin m) ℝ 1 := by
  simp [esymm_one]

/-- Let `P ⊆ ℝ^r`, `r ≥ 1`, be an integral binary nestohedron and `x = (x₁, …, x_m)`. Then
`e₂(x)^{r-1} ∑_{q ∈ P ∩ ℤ^r} ∏_i Q_{q_i - 1}(e₁(x), e₂(x))` is Lorentzian. -/
@[lognarayana "thm_e2_kernel_polytope_lorentzian"]
public theorem isLorentzian_esymm_two_pow_mul_finsum_latticePoints_prod_narayanaQ
    (hreal : IntegralBinaryNestohedronRealization) (hfert : RefinedFertilityFormula)
    (hsub : ∀ (σ τ : Type) [Fintype σ] [Fintype τ], LorentzianNonnegLinearSubstitution σ τ)
    (hder : ∀ (σ : Type) [Fintype σ], LorentzianNonnegDerivative σ)
    (hmul : ∀ (σ : Type) [Fintype σ], LorentzianMul σ)
    (hBH : ∀ (σ : Type) [Fintype σ], NormalizedSupportPolyLorentzianOfMConvex σ)
    (hsym : ∀ (σ τ : Type) [Fintype σ] [Fintype τ], BrandenHuhSymbolTheorem σ τ)
    (m : ℕ) {r : ℕ} (hr : 1 ≤ r) {P : Set (Fin r → ℝ)} (hP : IsIntegralBinaryNestohedron ℝ P) :
    (esymm (Fin m) ℝ 2 ^ (r - 1) * ∑ᶠ q ∈ P.latticePoints,
      ∏ i, aeval ![esymm (Fin m) ℝ 1, esymm (Fin m) ℝ 2]
        (narayanaQ ℝ (⌊q i⌋₊ - 1))).IsLorentzian := by
  rw [← sum_C_one_mul_X_eq_esymm_one]
  refine isLorentzian_pow_mul_finsum_latticePoints_prod_narayanaQ hreal hfert
    hsub hder hmul hBH hsym hr hP (a := 1)
    (fun _ => zero_le_one) (isHomogeneous_esymm _ _ _) (hasNonnegCoeffs_esymm 2) ?_
  rw [hessianAtZero_esymm_two_sub_vecMulVec_one, neg_neg]
  exact Matrix.PosSemidef.one

/-- Setting `t = 0` in the quadratic kernel `K_{A,B}`, i.e. substituting `t ↦ 0` and `z_j ↦ z_j`,
recovers `B`. -/
private lemma aeval_elim_quadraticKernel {p : ℕ} (A B : MvPolynomial (Fin p) ℝ) :
    aeval (Option.elim' 0 X) (quadraticKernel A B) = B := by
  simp [quadraticKernel, Function.comp_def, bind₁_rename, bind₁_X_left]

/-- If the quadratic kernel `K_{A,B}` is Lorentzian then so is `B`: the specialisation `t = 0` is
a nonnegative linear substitution of variables. -/
private lemma isLorentzian_of_isLorentzian_quadraticKernel {p : ℕ}
    (hsub : LorentzianNonnegLinearSubstitution (Option (Fin p)) (Fin p))
    {A B : MvPolynomial (Fin p) ℝ} (hK : (quadraticKernel A B).IsLorentzian) :
    B.IsLorentzian := by
  have h := hsub (fun i j ↦ if i = some j then 1 else 0) (fun i j ↦ by positivity) _ hK
  have hsubst : (fun i : Option (Fin p) ↦ ∑ j, (if i = some j then (1 : ℝ) else 0) •
      (X j : MvPolynomial (Fin p) ℝ)) = Option.elim' 0 X := by
    funext i
    cases i <;> simp [ite_smul, Finset.sum_ite_eq]
  rwa [hsubst, aeval_elim_quadraticKernel] at h

/-- Let `P ⊆ ℝ^r`, `r ≥ 1`, be an integral binary nestohedron, `a ∈ ℝ_{≥0}^p`, `A = aᵀ x`, and
`B` homogeneous of degree `2` with nonnegative coefficients and `Hess B - a aᵀ ⪯ 0`. Then
`∑_{q ∈ P ∩ ℤ^r} ∏_i (B · Q_{q_i - 1}(A, B))` is Lorentzian. -/
@[lognarayana "thm_kernel_polytope_product"]
public theorem isLorentzian_finsum_latticePoints_prod_mul_narayanaQ
    (hreal : IntegralBinaryNestohedronRealization)
    (hfert : RefinedFertilityFormula)
    (hsub : ∀ (σ τ : Type) [Fintype σ] [Fintype τ], LorentzianNonnegLinearSubstitution σ τ)
    (hder : ∀ (σ : Type) [Fintype σ], LorentzianNonnegDerivative σ)
    (hmul : ∀ (σ : Type) [Fintype σ], LorentzianMul σ)
    (hBH : ∀ (σ : Type) [Fintype σ], NormalizedSupportPolyLorentzianOfMConvex σ)
    (hsym : ∀ (σ τ : Type) [Fintype σ] [Fintype τ], BrandenHuhSymbolTheorem σ τ)
    {r : ℕ} (hr : 1 ≤ r) {P : Set (Fin r → ℝ)} (hP : IsIntegralBinaryNestohedron ℝ P)
    {p : ℕ} {a : Fin p → ℝ} (ha : ∀ j, 0 ≤ a j)
    {B : MvPolynomial (Fin p) ℝ} (hB : B.IsHomogeneous 2) (hBnn : B.HasNonnegCoeffs)
    (hHess : (-(hessianAtZero B - Matrix.vecMulVec a a)).PosSemidef) :
    (∑ᶠ q ∈ P.latticePoints,
      ∏ i, (B * aeval ![∑ j, C (a j) * X j, B] (narayanaQ ℝ (⌊q i⌋₊ - 1)))).IsLorentzian := by
  convert hmul (Fin p) B _
    (isLorentzian_of_isLorentzian_quadraticKernel (hsub _ _)
      ((isLorentzian_quadraticKernel_iff ha hB hBnn).2 hHess))
    (isLorentzian_pow_mul_finsum_latticePoints_prod_narayanaQ hreal hfert hsub hder hmul
      hBH hsym hr hP ha hB hBnn hHess) using 1
  rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel hr, mul_finsum_mem]
  refine finsum_mem_congr rfl fun q _ ↦ ?_
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end MvPolynomial

namespace Polynomial

/-- `N^{(0)}_q(x) = x (1 + x)^{q-1}`. -/
private theorem deformedNarayanaPolynomial_zero (R : Type*) [CommSemiring R] (q : ℕ) :
    deformedNarayanaPolynomial R 0 q = X * (1 + X) ^ (q - 1) := by
  rw [deformedNarayanaPolynomial, narayanaQ, map_sum, Finset.sum_eq_single 0]
  · simp
  · intro j _ hj
    simp [zero_pow hj]
  · simp

/-- A `finsum` over a set of a function constant on it is the cardinality times the value. -/
private theorem finsum_mem_eq_ncard_mul {α M : Type*} [Semiring M] {s : Set α} {f : α → M}
    {c : M} (h : ∀ a ∈ s, f a = c) : ∑ᶠ a ∈ s, f a = (s.ncard : M) * c := by
  rw [finsum_mem_congr rfl h]
  rcases s.finite_or_infinite with hs | hs
  · rw [finsum_mem_eq_finite_toFinset_sum _ hs, Finset.sum_const, Set.ncard_eq_toFinset_card s hs,
      nsmul_eq_mul]
  · rw [hs.ncard, Nat.cast_zero, zero_mul]
    by_cases hc : c = 0
    · simp [hc]
    · apply finsum_mem_eq_zero_of_infinite
      simpa [Function.support_const hc] using hs

/-- If every `k i ≥ 1`, then `∏_i X (1 + X)^{k_i - 1} = X^{|ι|} (1 + X)^{∑_i k_i - |ι|}`. -/
private theorem prod_X_mul_one_add_X_pow {R ι : Type*} [CommSemiring R] [Fintype ι]
    {k : ι → ℕ} (hk : ∀ i, 1 ≤ k i) :
    ∏ i, X * (1 + X : R[X]) ^ (k i - 1) =
      X ^ Fintype.card ι * (1 + X) ^ (∑ i, k i - Fintype.card ι) := by
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_pow_eq_pow_sum,
    Finset.sum_tsub_distrib _ fun i _ => hk i]
  simp

/-- A positive real number with integer value is the cast of its natural floor. -/
private theorem natCast_floor_eq_of_mem_range_intCast {x : ℝ} (hx : 0 < x)
    (hxZ : x ∈ Set.range (Int.cast : ℤ → ℝ)) : (⌊x⌋₊ : ℝ) = x := by
  obtain ⟨z, rfl⟩ := hxZ
  lift z to ℕ using by exact_mod_cast hx.le
  simp

/-- For an integral binary nestohedron `P ⊆ ℝ^r` whose points all have coordinate sum
`S ∈ ℤ_{≥0}`,
`∑_{q ∈ P ∩ ℤ^r} ∏_i N^{(0)}_{q_i}(x) = |P ∩ ℤ^r| x^r (1 + x)^{S-r}`. -/
@[lognarayana "lem_deformed_narayana_zero_sum"]
public theorem finsum_latticePoints_prod_deformedNarayanaPolynomial_zero
    {r : ℕ} {P : Set (Fin r → ℝ)} (hP : IsIntegralBinaryNestohedron ℝ P)
    {S : ℕ} (hS : ∀ v ∈ P, ∑ i, v i = S) :
    ∑ᶠ q ∈ P.latticePoints, ∏ i, deformedNarayanaPolynomial ℝ 0 ⌊q i⌋₊ =
      (P.latticePoints.ncard : ℝ[X]) * X ^ r * (1 + X) ^ (S - r) := by
  obtain ⟨⟨𝓑, h𝓑, c, hc, rfl⟩, -⟩ := hP
  rw [mul_assoc]
  refine finsum_mem_eq_ncard_mul fun q ⟨hqP, hqZ⟩ => ?_
  have hpos := pos_of_mem_nestohedron h𝓑 hc hqP
  have hfloor i := natCast_floor_eq_of_mem_range_intCast (hpos i) (hqZ i)
  have hsum : ∑ i, ⌊q i⌋₊ = S := by
    exact_mod_cast (by simpa only [hfloor] using hS q hqP : ∑ i, (⌊q i⌋₊ : ℝ) = S)
  simp_rw [deformedNarayanaPolynomial_zero, ← hsum]
  simpa using prod_X_mul_one_add_X_pow fun i => (by exact_mod_cast (hfloor i).symm ▸ hpos i :
    0 < ⌊q i⌋₊)

/-- `(1 + x)^e` is ultra-log-concave of order `e`: its normalized coefficients are all `1`. -/
private lemma isUltraLogConcave_one_add_X_pow (e : ℕ) :
    ((1 + X : ℝ[X]) ^ e).IsUltraLogConcave e := by
  have hcoeff : ∀ j, j ≤ e → ((1 + X : ℝ[X]) ^ e).coeff j / (e.choose j : ℝ) = 1 := fun j hj => by
    rw [coeff_one_add_X_pow]
    exact div_self (by exact_mod_cast (Nat.choose_pos hj).ne')
  refine ⟨?_, ⟨fun j hj => by dsimp only; rw [hcoeff j hj]; norm_num, fun j hj => ?_⟩,
    fun i j k _ hjk hk _ _ => ?_⟩
  · exact natDegree_pow_le.trans (by rw [add_comm, ← C_1, natDegree_X_add_C]; simp)
  · dsimp only
    rw [hcoeff j (by omega), hcoeff (j + 1) (by omega), hcoeff (j + 2) hj]; norm_num
  · dsimp only
    rw [hcoeff j (by omega)]; norm_num

/-- `(1 + x)^e x^n` is ultra-log-concave of order `e + n`. -/
private lemma isUltraLogConcave_one_add_X_pow_mul_X_pow (e n : ℕ) :
    ((1 + X : ℝ[X]) ^ e * X ^ n).IsUltraLogConcave (e + n) := by
  induction n with
  | zero => simpa using isUltraLogConcave_one_add_X_pow e
  | succ n ih => rw [pow_succ, ← mul_assoc]; exact ih.mul_X

/-- Scaling by a nonnegative constant preserves ultra-log-concavity. -/
private lemma isUltraLogConcave_C_mul {d : ℕ} {f : ℝ[X]} (hf : f.IsUltraLogConcave d)
    {c : ℝ} (hc : 0 ≤ c) : (C c * f).IsUltraLogConcave d := by
  obtain ⟨hdeg, ⟨hnn, hlc⟩, hnz⟩ := hf
  unfold IsUltraLogConcave IsLogConcaveSeq HasNoInternalZeros at *
  simp only [coeff_C_mul, mul_div_assoc]
  refine ⟨natDegree_C_mul_le c f |>.trans hdeg, ⟨fun j hj => mul_nonneg hc (hnn j hj),
    fun j hj => ?_⟩, fun i j k hij hjk hk hi hk' => ?_⟩
  · nlinarith [mul_le_mul_of_nonneg_left (hlc j hj) (mul_nonneg hc hc)]
  · rcases hc.lt_or_eq with hc | rfl
    · exact mul_pos hc (hnz i j k hij hjk hk (pos_of_mul_pos_right hi hc.le)
        (pos_of_mul_pos_right hk' hc.le))
    · simp at hi

/-- A lattice point of an integral binary nestohedron has every coordinate at least `1`. -/
private lemma one_le_of_mem_latticePoints {α : Type*} [LinearOrder α] [LocallyFiniteOrder α]
    {P : Set (α → ℝ)} (hP : IsIntegralBinaryNestohedron ℝ P) {q : α → ℝ}
    (hq : q ∈ P.latticePoints) (i : α) : 1 ≤ q i := by
  obtain ⟨⟨𝓑, h𝓑, c, hc, rfl⟩, -⟩ := hP
  obtain ⟨z, hz⟩ := hq.2 i
  have hpos := pos_of_mem_nestohedron h𝓑 hc hq.1 i
  rw [← hz] at hpos ⊢
  exact_mod_cast (Int.cast_pos.mp hpos : (0 : ℤ) < z)

/-- For an integral binary nestohedron `P ⊆ ℝ^r` with a lattice point whose points all have
coordinate sum `S ∈ ℤ_{≥0}`, the sum `∑_{q ∈ P ∩ ℤ^r} ∏_i N^{(0)}_{q_i}(x)` is ultra-log-concave of
order `S`. -/
@[lognarayana "lem_deformed_narayana_zero_ulc"]
public theorem isUltraLogConcave_finsum_latticePoints_prod_deformedNarayanaPolynomial_zero
    {r : ℕ} {P : Set (Fin r → ℝ)} (hP : IsIntegralBinaryNestohedron ℝ P)
    (hne : P.latticePoints.Nonempty) {S : ℕ} (hS : ∀ v ∈ P, ∑ i, v i = S) :
    (∑ᶠ q ∈ P.latticePoints, ∏ i, deformedNarayanaPolynomial ℝ 0 ⌊q i⌋₊).IsUltraLogConcave S := by
  obtain ⟨q, hq⟩ := hne
  have hrS : r ≤ S := by
    have : (r : ℝ) ≤ S := by
      simpa [← hS q hq.1] using Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) =>
        one_le_of_mem_latticePoints hP hq i
    exact_mod_cast this
  rw [finsum_latticePoints_prod_deformedNarayanaPolynomial_zero hP hS, mul_assoc,
    ← map_natCast C, mul_comm (X ^ r)]
  simpa [Nat.sub_add_cancel hrS] using
    isUltraLogConcave_C_mul (isUltraLogConcave_one_add_X_pow_mul_X_pow (S - r) r)
      (Nat.cast_nonneg _)

/-- The dehomogenization `F(x, 1)` of a Lorentzian bivariate form `F` of degree `d` is
ultra-log-concave of order `d`. -/
private lemma isUltraLogConcave_aeval_X_one {d : ℕ} {F : MvPolynomial (Fin 2) ℝ}
    (hL : F.IsLorentzian) (hF : F.IsHomogeneous d) :
    (MvPolynomial.aeval (![X, 1] : Fin 2 → ℝ[X]) F).IsUltraLogConcave d := by
  set f : ℝ[X] := MvPolynomial.aeval ![X, 1] F
  have hhom : f.homogenize d = F := homogenize_eq_of_isHomogeneous hF rfl
  have hdeg : f.natDegree ≤ d := by
    have := MvPolynomial.aeval_natDegree_le F hF.totalDegree_le ![X, 1] (n := 1)
      (fun i => by fin_cases i <;> simp)
    simpa using this
  have hnn : F.HasNonnegCoeffs := by
    rcases hL with h | ⟨e, he, hnn, -⟩
    · intro α; simp [h]
    · exact hnn
  have hf : ∀ i, 0 ≤ f.coeff i := by
    intro i
    by_cases hi : i ≤ d
    · have := hnn (Finsupp.single 0 i + Finsupp.single 1 (d - i))
      rw [← hhom, coeff_homogenize] at this
      simpa [hi] using this
    · rw [coeff_eq_zero_of_natDegree_lt (by omega)]
  exact (isLorentzian_homogenize_iff_isUltraLogConcave hf hdeg).1 (hhom ▸ hL)

/-- The form `B = λ x y` is homogeneous of degree `2`. -/
private lemma isHomogeneous_C_mul_X_zero_mul_X_one (lam : ℝ) :
    (MvPolynomial.C lam * MvPolynomial.X 0 * MvPolynomial.X 1 :
      MvPolynomial (Fin 2) ℝ).IsHomogeneous 2 :=
  (MvPolynomial.isHomogeneous_C_mul_X lam (0 : Fin 2)).mul (MvPolynomial.isHomogeneous_X ℝ 1)

/-- For `0 ≤ λ`, the form `B = λ x y` has nonnegative coefficients. -/
private lemma hasNonnegCoeffs_C_mul_X_zero_mul_X_one {lam : ℝ} (hlam : 0 ≤ lam) :
    (MvPolynomial.C lam * MvPolynomial.X 0 * MvPolynomial.X 1 :
      MvPolynomial (Fin 2) ℝ).HasNonnegCoeffs := by
  intro α
  simp only [MvPolynomial.X, MvPolynomial.C_mul_monomial, MvPolynomial.monomial_mul,
    MvPolynomial.coeff_monomial]
  split_ifs <;> simp [hlam]

/-- The deformed Narayana sum over a finite set `T ⊆ ℝ^r` is `λ^{1-r} x F(x, 1)`, where
`F = B^{r-1} ∑_{q ∈ T} ∏_i Q_{q_i-1}(A, B)` with `A = x + y` and `B = λ x y`. -/
private lemma finsum_prod_deformedNarayanaPolynomial_eq {lam : ℝ} (hlam : lam ≠ 0) {r : ℕ}
    (hr : 1 ≤ r) {T : Set (Fin r → ℝ)} (hT : T.Finite) :
    ∑ᶠ q ∈ T, ∏ i, deformedNarayanaPolynomial ℝ lam ⌊q i⌋₊ =
      C (lam ^ (r - 1))⁻¹ * (MvPolynomial.aeval (![X, 1] : Fin 2 → ℝ[X])
        ((MvPolynomial.C lam * MvPolynomial.X 0 * MvPolynomial.X 1) ^ (r - 1) *
          ∑ᶠ q ∈ T, ∏ i, MvPolynomial.aeval
            ![∑ j, MvPolynomial.C ((![1, 1] : Fin 2 → ℝ) j) * MvPolynomial.X j,
              MvPolynomial.C lam * MvPolynomial.X 0 * MvPolynomial.X 1]
            (narayanaQ ℝ (⌊q i⌋₊ - 1))) * X) := by
  have hcomp : ∀ Q : MvPolynomial (Fin 2) ℝ,
      MvPolynomial.aeval (![X, 1] : Fin 2 → ℝ[X]) (MvPolynomial.aeval
        ![∑ j, MvPolynomial.C ((![1, 1] : Fin 2 → ℝ) j) * MvPolynomial.X j,
          MvPolynomial.C lam * MvPolynomial.X 0 * MvPolynomial.X 1] Q) =
        MvPolynomial.aeval ![1 + X, C lam * X] Q := fun Q => by
    rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
    congr 2
    funext i
    fin_cases i <;> simp [add_comm]
  rw [finsum_mem_eq_finite_toFinset_sum _ hT, finsum_mem_eq_finite_toFinset_sum _ hT]
  simp only [map_mul, map_pow, map_sum, map_prod, hcomp, deformedNarayanaPolynomial,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    MvPolynomial.aeval_X, MvPolynomial.aeval_C, Matrix.cons_val_zero, Matrix.cons_val_one,
    mul_one, Polynomial.algebraMap_eq, ← Finset.mul_sum]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hr
  rw [Nat.add_sub_cancel, mul_pow, ← C_pow, pow_succ]
  have : C (lam ^ k)⁻¹ * C (lam ^ k) = 1 := by
    rw [← C_mul, inv_mul_cancel₀ (by positivity), C_1]
  linear_combination (-(X ^ k * X * ∑ q ∈ hT.toFinset, ∏ i, MvPolynomial.aeval
    ![1 + X, C lam * X] (narayanaQ ℝ (⌊q i⌋₊ - 1)))) * this

/-- For `0 < λ ≤ 2`, `r ≥ 1`, an integral binary nestohedron `P ⊆ ℝ^r` with a lattice point
whose points all have coordinate sum `S ∈ ℤ_{≥0}`, the deformed Narayana sum
`∑_{q ∈ P ∩ ℤ^r} ∏_i N^{(λ)}_{q_i}(x)` is ultra-log-concave of order `S + r - 1`. -/
@[lognarayana "lem_deformed_narayana_sum_ulc_pos"]
public theorem isUltraLogConcave_finsum_latticePoints_prod_deformedNarayanaPolynomial
    (hreal : IntegralBinaryNestohedronRealization)
    (hfert : RefinedFertilityFormula)
    (hsub : ∀ (σ τ : Type) [Fintype σ] [Fintype τ],
      MvPolynomial.LorentzianNonnegLinearSubstitution σ τ)
    (hder : ∀ (σ : Type) [Fintype σ], MvPolynomial.LorentzianNonnegDerivative σ)
    (hmul : ∀ (σ : Type) [Fintype σ], MvPolynomial.LorentzianMul σ)
    (hBH : ∀ (σ : Type) [Fintype σ],
      MvPolynomial.NormalizedSupportPolyLorentzianOfMConvex σ)
    (hsym : ∀ (σ τ : Type) [Fintype σ] [Fintype τ],
      MvPolynomial.BrandenHuhSymbolTheorem σ τ)
    {lam : ℝ} (hlam₀ : 0 < lam) (hlam₂ : lam ≤ 2)
    {r : ℕ} (hr : 1 ≤ r) {P : Set (Fin r → ℝ)} (hP : IsIntegralBinaryNestohedron ℝ P)
    (hne : P.latticePoints.Nonempty) {S : ℕ} (hS : ∀ v ∈ P, ∑ i, v i = S) :
    (∑ᶠ q ∈ P.latticePoints, ∏ i, deformedNarayanaPolynomial ℝ lam ⌊q i⌋₊).IsUltraLogConcave
      (S + r - 1) := by
  obtain ⟨q₀, hq₀, -⟩ := hne
  obtain ⟨𝓑, h𝓑, c, hc, hPeq⟩ := hP.1
  have hS0 : 0 < S := by
    exact_mod_cast (hS q₀ hq₀ ▸ Finset.sum_pos (fun i _ => pos_of_mem_nestohedron h𝓑 hc
      (hPeq ▸ hq₀) i) ⟨⟨0, hr⟩, Finset.mem_univ _⟩ : (0 : ℝ) < S)
  have hL := MvPolynomial.isLorentzian_pow_mul_finsum_latticePoints_prod_narayanaQ hreal hfert
    hsub hder hmul hBH hsym hr hP (a := ![1, 1]) (fun j => by fin_cases j <;> simp)
    (isHomogeneous_C_mul_X_zero_mul_X_one lam) (hasNonnegCoeffs_C_mul_X_zero_mul_X_one hlam₀.le)
    (MvPolynomial.posSemidef_neg_hessianAtZero_sub_vecMulVec hlam₀.le hlam₂)
  have hD := MvPolynomial.isHomogeneous_pow_mul_finsum_latticePoints_prod_narayanaQ hr hP hS
    (MvPolynomial.IsHomogeneous.sum Finset.univ
      (fun j => MvPolynomial.C ((![1, 1] : Fin 2 → ℝ) j) * MvPolynomial.X j) 1
      fun j _ => MvPolynomial.isHomogeneous_C_mul_X _ _)
    (isHomogeneous_C_mul_X_zero_mul_X_one lam)
  rw [finsum_prod_deformedNarayanaPolynomial_eq hlam₀.ne' hr
    (hPeq ▸ nestohedron_latticePoints_finite h𝓑 hc),
    show S + r - 1 = S + r - 2 + 1 by omega]
  exact isUltraLogConcave_C_mul (isUltraLogConcave_aeval_X_one hL hD).mul_X (by positivity)

/-- A binary nestohedron containing a lattice point has a constant coordinate sum, and that sum is
a natural number: the lattice point has positive integer coordinates. -/
private lemma exists_nat_sum_eq_of_latticePoints_nonempty {α : Type*} [Fintype α] [LinearOrder α]
    [LocallyFiniteOrder α] {P : Set (α → ℝ)} (hP : IsBinaryNestohedron ℝ P)
    (hne : P.latticePoints.Nonempty) : ∃ S : ℕ, ∀ v ∈ P, ∑ i, v i = S := by
  obtain ⟨𝓑, h𝓑, c, hc, rfl⟩ := hP
  obtain ⟨q₀, hq₀P, hq₀Z⟩ := hne
  have hfloor (i : α) : (⌊q₀ i⌋₊ : ℝ) = q₀ i := by
    obtain ⟨z, hz⟩ := hq₀Z i
    have hpos := pos_of_mem_nestohedron h𝓑 hc hq₀P i
    rw [← hz] at hpos ⊢
    lift z to ℕ using by exact_mod_cast hpos.le
    simp
  refine ⟨∑ i, ⌊q₀ i⌋₊, fun v hv => ?_⟩
  rw [sum_eq_sum_of_mem_nestohedron hv, ← sum_eq_sum_of_mem_nestohedron hq₀P]
  push_cast
  simp [hfloor]

/-- For `0 ≤ λ ≤ 2`, `r ≥ 1` and an integral binary nestohedron `P ⊆ ℝ^r`, the deformed
Narayana sum `∑_{q ∈ P ∩ ℤ^r} ∏_i N^{(λ)}_{q_i}(x)` is log-concave. -/
@[lognarayana "thm_deformed_narayana_lc"]
public theorem isLogConcave_finsum_latticePoints_prod_deformedNarayanaPolynomial
    (hreal : IntegralBinaryNestohedronRealization)
    (hfert : RefinedFertilityFormula)
    (hsub : ∀ (σ τ : Type) [Fintype σ] [Fintype τ],
      MvPolynomial.LorentzianNonnegLinearSubstitution σ τ)
    (hder : ∀ (σ : Type) [Fintype σ], MvPolynomial.LorentzianNonnegDerivative σ)
    (hmul : ∀ (σ : Type) [Fintype σ], MvPolynomial.LorentzianMul σ)
    (hBH : ∀ (σ : Type) [Fintype σ],
      MvPolynomial.NormalizedSupportPolyLorentzianOfMConvex σ)
    (hsym : ∀ (σ τ : Type) [Fintype σ] [Fintype τ],
      MvPolynomial.BrandenHuhSymbolTheorem σ τ)
    {lam : ℝ} (hlam₀ : 0 ≤ lam) (hlam₂ : lam ≤ 2)
    {r : ℕ} (hr : 1 ≤ r) {P : Set (Fin r → ℝ)} (hP : IsIntegralBinaryNestohedron ℝ P) :
    (∑ᶠ q ∈ P.latticePoints, ∏ i, deformedNarayanaPolynomial ℝ lam ⌊q i⌋₊).IsLogConcave := by
  rcases P.latticePoints.eq_empty_or_nonempty with hemp | hne
  · rw [hemp, finsum_mem_empty]
    exact ⟨fun j => by simp, fun j => by simp⟩
  obtain ⟨S, hS⟩ := exists_nat_sum_eq_of_latticePoints_nonempty hP.1 hne
  rcases hlam₀.eq_or_lt with rfl | hlam
  · exact (isUltraLogConcave_finsum_latticePoints_prod_deformedNarayanaPolynomial_zero hP
      hne hS).isLogConcave
  · exact (isUltraLogConcave_finsum_latticePoints_prod_deformedNarayanaPolynomial hreal hfert
      hsub hder hmul hBH hsym hlam hlam₂ hr hP hne hS).isLogConcave

/-- An ultra-log-concave polynomial of any order has a coefficient sequence with no internal
zeros: the normalizing binomial coefficients are positive on `0, …, d`. -/
private lemma hasNoInternalZeros_coeff_of_isUltraLogConcave {d : ℕ} {f : ℝ[X]}
    (hf : f.IsUltraLogConcave d) : HasNoInternalZeros f.natDegree f.coeff := by
  obtain ⟨hdeg, -, hnz⟩ := hf
  intro i j k hij hjk hkd hi hk
  have hc : ∀ m, m ≤ d → (0 : ℝ) < d.choose m := fun m hm => by
    exact_mod_cast Nat.choose_pos hm
  have hj := hnz i j k hij hjk (hkd.trans hdeg) (div_pos hi (hc i (by omega)))
    (div_pos hk (hc k (by omega)))
  exact (div_pos_iff_of_pos_right (hc j (by omega))).1 hj

/-- For `0 ≤ λ ≤ 2` and an integral binary nestohedron `P ⊆ ℝ^r` with `r ≥ 1`, the coefficient
sequence of `∑_{q ∈ P ∩ ℤ^r} ∏_i N^{(λ)}_{q_i}(x)` has no internal zeros. -/
@[lognarayana "thm_deformed_narayana_nz"]
public theorem hasNoInternalZeros_coeff_finsum_latticePoints_prod_deformedNarayanaPolynomial
    (hreal : IntegralBinaryNestohedronRealization)
    (hfert : RefinedFertilityFormula)
    (hsub : ∀ (σ τ : Type) [Fintype σ] [Fintype τ],
      MvPolynomial.LorentzianNonnegLinearSubstitution σ τ)
    (hder : ∀ (σ : Type) [Fintype σ], MvPolynomial.LorentzianNonnegDerivative σ)
    (hmul : ∀ (σ : Type) [Fintype σ], MvPolynomial.LorentzianMul σ)
    (hBH : ∀ (σ : Type) [Fintype σ],
      MvPolynomial.NormalizedSupportPolyLorentzianOfMConvex σ)
    (hsym : ∀ (σ τ : Type) [Fintype σ] [Fintype τ],
      MvPolynomial.BrandenHuhSymbolTheorem σ τ)
    {lam : ℝ} (hlam₀ : 0 ≤ lam) (hlam₂ : lam ≤ 2)
    {r : ℕ} (hr : 1 ≤ r) {P : Set (Fin r → ℝ)} (hP : IsIntegralBinaryNestohedron ℝ P) :
    HasNoInternalZeros
      (∑ᶠ q ∈ P.latticePoints, ∏ i, deformedNarayanaPolynomial ℝ lam ⌊q i⌋₊).natDegree
      (∑ᶠ q ∈ P.latticePoints, ∏ i, deformedNarayanaPolynomial ℝ lam ⌊q i⌋₊).coeff := by
  rcases P.latticePoints.eq_empty_or_nonempty with hemp | hne
  · rw [hemp, finsum_mem_empty]
    intro i j k _ _ _ hi _
    simp at hi
  obtain ⟨S, hS⟩ := exists_nat_sum_eq_of_latticePoints_nonempty hP.1 hne
  rcases hlam₀.eq_or_lt with rfl | hlam
  · exact hasNoInternalZeros_coeff_of_isUltraLogConcave
      (isUltraLogConcave_finsum_latticePoints_prod_deformedNarayanaPolynomial_zero hP hne hS)
  · exact hasNoInternalZeros_coeff_of_isUltraLogConcave
      (isUltraLogConcave_finsum_latticePoints_prod_deformedNarayanaPolynomial hreal hfert
        hsub hder hmul hBH hsym hlam hlam₂ hr hP hne hS)

end Polynomial
