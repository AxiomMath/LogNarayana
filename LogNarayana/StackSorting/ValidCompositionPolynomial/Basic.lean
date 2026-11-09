/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib
public import LogNarayana.Attr
public import LogNarayana.StackSorting.ValidCompositionPolynomial.Defs
public import LogNarayana.StackSorting.FiberPolynomials.Defs
public import LogNarayana.Narayana.Transform.Defs
public import LogNarayana.Polynomial.RealStable.Defs
public import LogNarayana.StackSorting.ValidHookConfigurations.Basic
public import LogNarayana.Narayana.Polynomials.Basic
public import LogNarayana.Polynomial.RealStable.Basic
public import LogNarayana.Narayana.RealRootedTransform.Basic
public import LogNarayana.StackSorting.StackSort.Basic

/-!
# Real-stable valid-composition polynomials

Let `n ≥ 1`, `π ∈ S_n` with `k = des(π)` descents, and let `F_π` be its valid-composition
polynomial. Every valid composition is a composition of `n - k` into `k + 1` parts, so `F_π` is
homogeneous of degree `n - 2k - 1`; by the refined fertility formula the fiber descent polynomial
is `D_π(x) = x^k 𝒩(F_π)(x)`. Since `F_π` has nonnegative coefficients, the real-stability of
`F_π` implies that `D_π` is real-rooted (Corollary 6.7).

The section closes with two examples. For `π = 1253467`, `𝒱(π) = {(4, 2), (3, 3)}` and
`F_π = z₀² z₁ (z₀ + z₁)` is real-stable, so `D_π` is real-rooted. For `π = 2135467`,
`F_π = z₀² + z₀ z₁ + z₁² + z₂ (z₀ + z₁)` is not real-stable, yet
`D_π(x) = x² (5 + 12x + 5x²)` is real-rooted: the converse of Corollary 6.7 fails.

## Main results

* `List.isHomogeneous_validCompositionPoly`: `F_π` is homogeneous of degree `n - 2 des(π) - 1`.
* `List.validCompositions_1253467`: `𝒱(1253467) = {(4, 2), (3, 3)}`.
* `List.validCompositionPoly_1253467`: `F_{1253467} = z₀² z₁ (z₀ + z₁)`.
* `List.validCompositionPoly_2135467`: `F_{2135467} = z₀² + z₀ z₁ + z₁² + z₂ (z₀ + z₁)`.
* `List.not_isRealStable_validCompositionPoly_2135467`: `F_{2135467}` is not real-stable.
* `List.fiberDescentPolynomial_eq_X_pow_mul_narayanaTransform`: `D_π = x^k 𝒩(F_π)`.
* `List.fiberDescentPolynomial_2135467_eq_X_sq_mul`: `D_{2135467}(x) = x² (5 + 12x + 5x²)`.
* `List.splits_fiberDescentPolynomial_2135467`: `D_{2135467}` is real-rooted.
* `List.splits_fiberDescentPolynomial_of_isRealStable_validCompositionPoly`: Corollary 6.7.
* `List.splits_fiberDescentPolynomial_1253467`: `D_{1253467}` is real-rooted.

## Implementation notes

Real-rootedness is `Polynomial.Splits` over `ℝ`. The published results the proofs rest on are
stated as `Prop`s and taken as hypotheses: Defant's refined fertility formula
`List.RefinedFertilityFormula`, Wagner's specialization closure `IsRealStableSpecializeClosed`,
the Borcea–Brändén symbol theorem `RealStablePreserverOfSymbol` (used at several variable types,
so quantified over all types in universe `0`), and the negative real zeros
`ShiftedNarayanaNegRealRoots` of the shifted Narayana polynomials. Their γ-expansion
`ShiftedNarayanaGammaExpansion` is proved (`shiftedNarayanaGammaExpansion_holds`).

## References

* [LogNarayana], Section 6 and Corollary 6.7.
* [Wagner], Lemma 2.4.
-/

namespace List

section Homogeneous

open MvPolynomial

/-- Lowering every part of a composition of `m` into `k` parts by one gives total `m - k`. -/
private lemma sum_sub_one_of_mem_compositionTuple {k m : ℕ} {q : Fin k → ℕ}
    (hq : q ∈ Finset.Nat.compositionTuple k m) : ∑ i, (q i - 1) = m - k := by
  simp only [Finset.Nat.compositionTuple, Finset.mem_filter,
    Finset.Nat.mem_antidiagonalTuple] at hq
  rw [Finset.sum_tsub_distrib _ fun i _ => hq.2 i, hq.1]
  simp

/-- For `π ∈ S_n` with `n ≥ 1` and `k = des(π)`, the valid-composition polynomial `F_π` is
homogeneous of degree `n - 2k - 1` (truncated difference in `ℕ`). -/
@[lognarayana "lem_valid_composition_poly_homogeneous"]
public theorem isHomogeneous_validCompositionPoly (R : Type*) [CommSemiring R] {n : ℕ}
    (hn : 1 ≤ n) {π : List ℕ} (hπ : π ∈ permWords n) :
    (π.validCompositionPoly R).IsHomogeneous (n - 2 * π.numDescents - 1) := by
  refine IsHomogeneous.sum _ _ _ fun q hq => ?_
  convert IsHomogeneous.prod _ _ _ fun i _ => isHomogeneous_X_pow (R := R) i (q i - 1)
  rw [sum_sub_one_of_mem_compositionTuple
    (List.mem_compositionTuple_of_mem_validCompositions hn hπ hq)]
  omega

end Homogeneous

section Example1253467

private lemma descentSet_1253467 : descentSet [1, 2, 5, 3, 4, 6, 7] = {3} := by decide

private lemma numDescents_1253467 : numDescents [1, 2, 5, 3, 4, 6, 7] = 1 := by
  simp [numDescents, descentSet_1253467]

/-- The single descent of `[1, 2, 5, 3, 4, 6, 7]` is at position `3`. -/
private lemma orderEmbOfFin_descentSet_1253467 (t) :
    (descentSet [1, 2, 5, 3, 4, 6, 7]).orderEmbOfFin rfl t = 3 := by
  have h := Finset.orderEmbOfFin_mem _ rfl t
  generalize (descentSet [1, 2, 5, 3, 4, 6, 7]).orderEmbOfFin rfl t = x at h ⊢
  simpa [descentSet_1253467] using h

/-- The composition of a single hook `(3, b)` on `[1, 2, 5, 3, 4, 6, 7]`: the letters outside
the hook, and the letters strictly inside it, other than `b`. -/
private lemma hookComposition_1253467_singleton (b : ℕ) :
    hookComposition [1, 2, 5, 3, 4, 6, 7] {(3, b)} =
      ![({u ∈ Finset.Icc 1 7 | u ≠ b ∧ ¬(3 < u ∧ u < b)} : Finset ℕ).card,
        ({u ∈ Finset.Icc 1 7 | u ≠ b ∧ 3 < u ∧ u < b} : Finset ℕ).card] := by
  funext i
  refine Fin.cases ?_ (fun t => ?_) i
  · simp [hookComposition]
  · obtain rfl : t = ⟨0, by decide⟩ := Fin.ext <| by
      have := t.2
      simp only [numDescents_1253467] at this
      simp
      omega
    simp [hookComposition, orderEmbOfFin_descentSet_1253467]
    rfl

private lemma validHookConfigurations_1253467 :
    validHookConfigurations [1, 2, 5, 3, 4, 6, 7] = {{(3, 6)}, {(3, 7)}} := by
  ext 𝓗
  simp only [validHookConfigurations, Finset.mem_filter, Finset.mem_powerset, numDescents_1253467,
    descentSet_1253467, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hsub, ⟨hcard, himg⟩, -, -⟩
    obtain ⟨⟨a, b⟩, rfl⟩ := Finset.card_eq_one.1 hcard
    obtain rfl : a = 3 := by simpa using himg
    have hb := hsub (Finset.mem_singleton_self _)
    have hb7 : b ≤ 7 := by simp_all [hooks]
    interval_cases b <;> first | exact absurd hb (by decide) | simp
  · rintro (rfl | rfl) <;> refine ⟨by decide, by decide, ?_, by simp⟩ <;>
      simp only [Finset.mem_singleton, Finset.mem_Icc] <;>
      rintro p rfl k ⟨hk1, hk2⟩ <;> interval_cases k <;> decide

/-- The valid compositions of the permutation `1253467` are `(4, 2)` and `(3, 3)`. -/
@[lognarayana "lem_valid_compositions_1253467"]
public theorem validCompositions_1253467 :
    validCompositions [1, 2, 5, 3, 4, 6, 7] = {![4, 2], ![3, 3]} := by
  simp only [validCompositions, validHookConfigurations_1253467, Finset.image_insert,
    Finset.image_singleton, hookComposition_1253467_singleton]
  decide

open MvPolynomial

private lemma sum_pair_eq (R : Type*) [CommSemiring R] :
    ∑ q ∈ ({![4, 2], ![3, 3]} : Finset (Fin 2 → ℕ)),
      ∏ i, (X i : MvPolynomial (Fin 2) R) ^ (q i - 1) = X 0 ^ 2 * X 1 * (X 0 + X 1) := by
  rw [Finset.sum_pair (by decide)]
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- The valid-composition polynomial of the permutation `1253467` is
`F_{1253467}(z₀, z₁) = z₀² z₁ (z₀ + z₁)`. -/
@[lognarayana "lem_valid_composition_poly_1253467"]
public theorem validCompositionPoly_1253467 (R : Type*) [CommSemiring R] :
    validCompositionPoly R [1, 2, 5, 3, 4, 6, 7] = X 0 ^ 2 * X 1 * (X 0 + X 1) := by
  rw [validCompositionPoly, validCompositions_1253467]
  exact sum_pair_eq R

end Example1253467

section Example2135467

open MvPolynomial

private lemma sum_five_eq (R : Type*) [CommSemiring R] :
    ∑ q ∈ ({![3, 1, 1], ![2, 1, 2], ![2, 2, 1], ![1, 2, 2], ![1, 3, 1]} :
        Finset (Fin 3 → ℕ)),
      ∏ i, (X i : MvPolynomial (Fin 3) R) ^ (q i - 1) =
        X 0 ^ 2 + X 0 * X 1 + X 1 ^ 2 + X 2 * (X 0 + X 1) := by
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_pair (by decide)]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.prod_univ_three, Fin.isValue,
    Matrix.cons_val_zero, Nat.add_one_sub_one, Matrix.cons_val_one, tsub_self, pow_zero, mul_one,
    Matrix.cons_val, pow_one, one_mul]
  ring

/-- The valid-composition polynomial of the permutation `2135467` is
`F_{2135467}(z₀, z₁, z₂) = z₀² + z₀ z₁ + z₁² + z₂ (z₀ + z₁)`. -/
@[lognarayana "lem_valid_composition_poly_2135467"]
public theorem validCompositionPoly_2135467 (R : Type*) [CommSemiring R] :
    validCompositionPoly R [2, 1, 3, 5, 4, 6, 7] =
      X 0 ^ 2 + X 0 * X 1 + X 1 ^ 2 + X 2 * (X 0 + X 1) := by
  rw [validCompositionPoly, validCompositions_2135467]
  exact sum_five_eq R

private lemma X_sq_add_X_add_one_ne_zero :
    (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial ℝ) ≠ 0 := fun h => by
  simpa using congrArg (Polynomial.coeff · 0) h

/-- `t² + t + 1` is not real-rooted: it has degree `2` but no real root. -/
private lemma not_splits_X_sq_add_X_add_one :
    ¬ (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial ℝ).Splits := by
  intro hs
  have hdeg : (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial ℝ).natDegree = 2 := by
    compute_degree!
  have hroots : (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial ℝ).roots = 0 := by
    refine Multiset.eq_zero_of_forall_notMem fun x hx => ?_
    rw [Polynomial.mem_roots X_sq_add_X_add_one_ne_zero] at hx
    simp only [Polynomial.IsRoot.def, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_one] at hx
    nlinarith [sq_nonneg (x + 1 / 2)]
  simpa [hdeg, hroots] using hs.natDegree_eq_card_roots

/-- `z₀² + z₀ z₁ + z₁² + z₂ (z₀ + z₁)` is not real-stable: specializing `z₂ = 0`, then `z₁ = 1`,
leaves `z₀² + z₀ + 1`, which is not real-rooted. -/
private lemma not_isRealStable_aux (hspec : IsRealStableSpecializeClosed (Fin 3)) :
    ¬ (X 0 ^ 2 + X 0 * X 1 + X 1 ^ 2 + X 2 * (X 0 + X 1) :
      MvPolynomial (Fin 3) ℝ).IsRealStable := by
  intro hF
  have e1 : aeval (Function.update X 2 (C 0 : MvPolynomial (Fin 3) ℝ))
      (X 0 ^ 2 + X 0 * X 1 + X 1 ^ 2 + X 2 * (X 0 + X 1) : MvPolynomial (Fin 3) ℝ) =
      X 0 ^ 2 + X 0 * X 1 + X 1 ^ 2 := by
    simp
  have e2 : aeval (Function.update X 1 (C 1 : MvPolynomial (Fin 3) ℝ))
      (X 0 ^ 2 + X 0 * X 1 + X 1 ^ 2 : MvPolynomial (Fin 3) ℝ) =
      Polynomial.toMvPolynomial 0 (Polynomial.X ^ 2 + Polynomial.X + 1) := by
    simp
  rcases hspec _ hF 2 0 with h1 | h1 <;> rw [e1] at h1
  · have := congrArg (MvPolynomial.coeff (Finsupp.single 1 2)) h1
    simp [MvPolynomial.coeff_X_pow, MvPolynomial.coeff_X_mul', Finsupp.single_eq_single_iff]
      at this
  rcases hspec _ h1 1 1 with h2 | h2
  · rw [e2] at h2
    exact X_sq_add_X_add_one_ne_zero
      ((Polynomial.toMvPolynomial_injective 0) (h2.trans (map_zero _).symm))
  rw [e2, Polynomial.isRealStable_toMvPolynomial_iff_splits] at h2
  · exact not_splits_X_sq_add_X_add_one h2
  · exact X_sq_add_X_add_one_ne_zero

/-- The valid-composition polynomial `F_{2135467}` is not real-stable. -/
@[lognarayana "lem_valid_composition_poly_2135467_not_real_stable"]
public theorem not_isRealStable_validCompositionPoly_2135467
    (hspec : _root_.IsRealStableSpecializeClosed
      (Fin ([2, 1, 3, 5, 4, 6, 7] : List ℕ).numDescents.succ)) :
    ¬ (validCompositionPoly ℝ [2, 1, 3, 5, 4, 6, 7]).IsRealStable := by
  rw [validCompositionPoly_2135467]
  exact not_isRealStable_aux hspec

end Example2135467

section NarayanaTransform

open Polynomial

private lemma narayanaTransform_monomial_one {σ : Type*} (α : σ →₀ ℕ) :
    MvPolynomial.narayanaTransform σ (MvPolynomial.monomial α (1 : ℝ)) =
      α.prod fun _ k => shiftedNarayanaPolynomial k := by
  rw [← congrFun (MvPolynomial.coe_basisMonomials σ ℝ) α, MvPolynomial.narayanaTransform,
    Module.Basis.constr_basis]

private lemma narayanaTransform_prod_X_pow {σ : Type*} [Fintype σ] (e : σ → ℕ) :
    MvPolynomial.narayanaTransform σ (∏ i, MvPolynomial.X i ^ e i) =
      ∏ i, shiftedNarayanaPolynomial (e i) := by
  have h : (∏ i, MvPolynomial.X i ^ e i : MvPolynomial σ ℝ) =
      MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm e) 1 := by
    simp [MvPolynomial.monomial_eq, Finsupp.prod_fintype]
  rw [h, narayanaTransform_monomial_one,
    Finsupp.prod_fintype _ _ (fun _ => shiftedNarayanaPolynomial_zero)]
  rfl

/-- A tuple of positive integers `q : I → ℕ` has `∏ i, N_{q i} = x ^ #I * 𝒩(∏ i, X_i ^ (q i - 1))`,
since `N_{m+1} = x Ñ_m`. -/
private lemma narayanaTupleProd_eq_X_pow_mul_narayanaTransform {I : Type*} [Fintype I]
    {q : I → ℕ} (hq : ∀ i, 1 ≤ q i) :
    narayanaTupleProd q =
      X ^ Fintype.card I *
        MvPolynomial.narayanaTransform I (∏ i, MvPolynomial.X i ^ (q i - 1)) := by
  rw [narayanaTransform_prod_X_pow, ← Finset.card_univ, ← Finset.prod_const,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← narayanaPolynomial_succ_eq_X_mul, Nat.sub_add_cancel (hq i)]

/-- For `n ≥ 1` and `π ∈ S_n` with `k = des(π)`, `D_π(x) = x^k 𝒩(F_π)(x)`. -/
@[lognarayana "lem_fiber_descent_eq_transform"]
public theorem fiberDescentPolynomial_eq_X_pow_mul_narayanaTransform
    (hfert : RefinedFertilityFormula) {n : ℕ} (hn : 1 ≤ n)
    {π : List ℕ} (hπ : π ∈ permWords n) :
    fiberDescentPolynomial ℝ π =
      X ^ π.numDescents *
        MvPolynomial.narayanaTransform (Fin (π.numDescents + 1)) (validCompositionPoly ℝ π) := by
  refine mul_left_cancel₀ (X_ne_zero (R := ℝ)) ?_
  rw [hfert n hn π hπ, List.validCompositionPoly, map_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [narayanaTupleProd_eq_X_pow_mul_narayanaTransform
      (Finset.mem_filter.1 (List.mem_compositionTuple_of_mem_validCompositions hn hπ hq)).2,
    Fintype.card_fin, pow_succ', mul_assoc]

/-- The Narayana transform of a monomial with coefficient `1` over finitely many variables is
`∏ i, Ñ_{α i}`. -/
private lemma narayanaTransform_monomial_one_fintype {σ : Type*} [Fintype σ] (α : σ →₀ ℕ) :
    MvPolynomial.narayanaTransform σ (MvPolynomial.monomial α 1) =
      ∏ i, shiftedNarayanaPolynomial (α i) := by
  rw [narayanaTransform_monomial_one,
    Finsupp.prod_fintype _ _ fun _ => shiftedNarayanaPolynomial_zero]

/-- `x² 𝒩(z₀² + z₀ z₁ + z₁² + z₂ (z₀ + z₁)) = x² (2 Ñ_2 + 3 Ñ_1²) = x² (5 + 12x + 5x²)`. -/
private lemma narayanaTransform_validCompositionPoly_2135467 :
    X ^ 2 * MvPolynomial.narayanaTransform (Fin 3)
      (MvPolynomial.X 0 ^ 2 + MvPolynomial.X 0 * MvPolynomial.X 1 + MvPolynomial.X 1 ^ 2 +
        MvPolynomial.X 2 * (MvPolynomial.X 0 + MvPolynomial.X 1)) =
      X ^ 2 * (5 + 12 * X + 5 * X ^ 2) := by
  simp only [mul_add, MvPolynomial.X_pow_eq_monomial]
  simp only [MvPolynomial.X, MvPolynomial.monomial_mul,
    one_mul, map_add, narayanaTransform_monomial_one_fintype, Fin.prod_univ_three]
  simp [shiftedNarayanaPolynomial_zero, shiftedNarayanaPolynomial_one,
    shiftedNarayanaPolynomial_two]
  ring

/-- The fiber descent polynomial of `2135467` is `D_{2135467}(x) = x² (5 + 12x + 5x²)`. -/
@[lognarayana "lem_fiber_descent_2135467"]
public theorem fiberDescentPolynomial_2135467_eq_X_sq_mul (hfert : RefinedFertilityFormula) :
    fiberDescentPolynomial ℝ [2, 1, 3, 5, 4, 6, 7] = X ^ 2 * (5 + 12 * X + 5 * X ^ 2) := by
  rw [fiberDescentPolynomial_eq_X_pow_mul_narayanaTransform hfert (n := 7) (by norm_num)
    (mem_permWords_iff_perm.2 (by decide)), validCompositionPoly_2135467]
  exact narayanaTransform_validCompositionPoly_2135467

/-- Vieta's formulas for a scaled monic quadratic with roots `a` and `b`. -/
private lemma C_mul_X_sub_C_mul_X_sub_C {R : Type*} [CommRing R] (c a b : R) :
    C c * ((X - C a) * (X - C b)) = C c * X ^ 2 - C (c * (a + b)) * X + C (c * (a * b)) := by
  simp only [C_mul, C_add]
  ring

/-- `5x² + 12x + 5 = 5 (x - r₊)(x - r₋)` with `r_± = (-6 ± √11)/5`. -/
private lemma quadratic_eq :
    (5 + 12 * X + 5 * X ^ 2 : ℝ[X]) =
      C 5 * ((X - C ((-6 + √11) / 5)) * (X - C ((-6 - √11) / 5))) := by
  rw [C_mul_X_sub_C_mul_X_sub_C, show 5 * ((-6 + √11) / 5 + (-6 - √11) / 5) = -12 by ring,
    show (5 : ℝ) * ((-6 + √11) / 5 * ((-6 - √11) / 5)) = 5 by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 11 by norm_num)]]
  simp only [map_neg, C_ofNat]
  ring

/-- The fiber descent polynomial `D_{2135467}` of the permutation `2135467` is real-rooted. -/
@[lognarayana "lem_fiber_descent_2135467_real_rooted"]
public theorem splits_fiberDescentPolynomial_2135467 (hfert : RefinedFertilityFormula) :
    (fiberDescentPolynomial ℝ [2, 1, 3, 5, 4, 6, 7]).Splits := by
  rw [fiberDescentPolynomial_2135467_eq_X_sq_mul hfert, quadratic_eq]
  exact ((Splits.X).pow 2).mul ((Splits.C 5).mul
    ((Splits.X_sub_C _).mul (Splits.X_sub_C _)))

end NarayanaTransform

section StableFiber

open Polynomial MvPolynomial

/-- The valid-composition polynomial has nonnegative coefficients. -/
private lemma hasNonnegCoeffs_validCompositionPoly (π : List ℕ) :
    (validCompositionPoly ℝ π).HasNonnegCoeffs := by
  intro α
  rw [validCompositionPoly, MvPolynomial.coeff_sum]
  refine Finset.sum_nonneg fun q _ => ?_
  simp only [MvPolynomial.X_pow_eq_monomial, ← monomial_sum_one, MvPolynomial.coeff_monomial]
  split_ifs <;> norm_num

/-- **Corollary 6.7** [LogNarayana]: for `n ≥ 1` and `π ∈ S_n`, if `F_π` is real-stable then
`D_π` is real-rooted. -/
@[lognarayana "thm_stable_fiber_real_rooted"]
public theorem splits_fiberDescentPolynomial_of_isRealStable_validCompositionPoly
    (hBB : ∀ σ : Type, RealStablePreserverOfSymbol σ)
    (hroots : ShiftedNarayanaNegRealRoots)
    (hfert : RefinedFertilityFormula)
    {n : ℕ} (hn : 1 ≤ n) {π : List ℕ} (hπ : π ∈ permWords n)
    (hF : (validCompositionPoly ℝ π).IsRealStable) :
    (fiberDescentPolynomial ℝ π).Splits := by
  rw [fiberDescentPolynomial_eq_X_pow_mul_narayanaTransform hfert hn hπ]
  exact (Splits.X.pow _).mul
    (splits_narayanaTransform_of_isRealStable hBB hroots
      (isHomogeneous_validCompositionPoly ℝ hn hπ) hF (hasNonnegCoeffs_validCompositionPoly π))

/-- `z₀² z₁ (z₀ + z₁)` is real-stable. -/
private lemma isRealStable_X_sq_mul_X_mul_add :
    (MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1 * (MvPolynomial.X 0 + MvPolynomial.X 1) :
      MvPolynomial (Fin 2) ℝ).IsRealStable := by
  intro ζ hζ
  have hne {w : ℂ} (hw : 0 < w.im) : w ≠ 0 := fun h => by simp [h] at hw
  simp only [map_mul, map_pow, map_add, MvPolynomial.aeval_X]
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (hne (hζ 0))) (hne (hζ 1)))
    (hne (by simpa using add_pos (hζ 0) (hζ 1)))

/-- The fiber descent polynomial `D_{1253467}` of the permutation `1253467` is real-rooted. -/
@[lognarayana "lem_fiber_descent_1253467_real_rooted"]
public theorem splits_fiberDescentPolynomial_1253467
    (hBB : ∀ σ : Type, RealStablePreserverOfSymbol σ)
    (hroots : ShiftedNarayanaNegRealRoots)
    (hfert : RefinedFertilityFormula) :
    (fiberDescentPolynomial ℝ [1, 2, 5, 3, 4, 6, 7]).Splits := by
  refine splits_fiberDescentPolynomial_of_isRealStable_validCompositionPoly hBB hroots hfert
    (n := 7) (by norm_num) (mem_permWords_iff_perm.2 (by decide)) ?_
  rw [validCompositionPoly_1253467]
  exact isRealStable_X_sq_mul_X_mul_add

end StableFiber

end List
