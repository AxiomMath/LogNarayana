/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module
public import Mathlib
public import LogNarayana.Attr
public import LogNarayana.Troupe.SchroederNestohedron.Defs
public import LogNarayana.Nestohedron.Fertilitope.Defs
public import LogNarayana.StackSorting.Descents.Defs
public import LogNarayana.StackSorting.ValidHookConfigurations.Defs
public import LogNarayana.Polynomial.LogConcave.Defs
public import LogNarayana.Troupe.Schroeder.Defs
public import LogNarayana.Nestohedron.Fertilitope.Basic
public import LogNarayana.Lorentzian.Symbol.Basic
public import LogNarayana.Polynomial.LogConcave.Basic
public import LogNarayana.Lorentzian.BrandenHuh.Basic
public import LogNarayana.Troupe.Schroeder.Basic

/-!
# Schröder factors and integral binary nestohedra

For `n ≥ 1` and a permutation `π ∈ S_n` with `k = des(π)` descents, specialising the Schröder
postorder polynomial `𝒞_π(z, w)` at `w = 1` gives
`𝒞_π(z, 1) = z^k ∑_{(q₀, …, q_k) ∈ 𝒱(π)} ∏_{i=0}^k R_{q_i}(z)`,
where `𝒱(π)` is the set of valid compositions of `π` and `R_q` the Schröder factors. It follows
from the refined tree fertility formula and the generating function of Schröder trees by black
vertices, after cancelling one factor of `z`.

Let `P ⊆ ℝ^r` be an integral binary nestohedron. Realizing `P ∩ ℤ^r` as the set of valid
compositions of a permutation `π` with `r - 1` descents, the formula above identifies
`z^{r-1} ∑_{q ∈ P ∩ ℤ^r} ∏_{i=1}^{r} R_{q_i}(z)` with `𝒞_π(z, 1)`, which is ultra-log-concave;
removing the monomial factor, the sum itself is log-concave.

## Main results

* `Polynomial.IsLogConcave.of_X_pow_mul`: if `X ^ k * f` is log-concave, so is `f`.
* `List.aeval_schroederFiberPolynomial_eq_X_pow_mul_sum_prod_schroederFactor`: the Schröder
  product formula `𝒞_π(z, 1) = z^{des(π)} ∑_{q ∈ 𝒱(π)} ∏_i R_{q_i}(z)`.
* `Polynomial.isLogConcave_finsum_latticePoints_prod_schroederFactor`:
  `∑_{q ∈ P ∩ ℤ^r} ∏_{i=1}^{r} R_{q_i}(z)` is log-concave.

## Implementation notes

The specialisation `w = 1` is `MvPolynomial.aeval ![X, 1]`, sending `z = X 0` to the variable
`X` of `R[X]` and `w = X 1` to `1`. The lattice points of `P` lie in the positive orthant, so
each coordinate `q i` is a positive integer and is turned into the natural number `⌊q i⌋₊`
indexing `R_{q_i}`; the set `P ∩ ℤ^r` is finite, so the sum is a `finsum`.

The cited results the proofs rest on are hypotheses: Defant's refined fertility formula
(`SchroederRefinedFertilityFormula`), Defant's enumeration of Schröder trees by black vertices
(`SchroederTreesBlackGenFunEq`), Defant's realization of integral binary nestohedra as
fertilitopes (`IntegralBinaryNestohedronRealization`), and the Brändén–Huh closure properties of
Lorentzian polynomials.

## References

* [LogNarayana], Section 8 (Schröder factors and integral binary nestohedra).
* [Troupes] C. Defant, *Troupes, cumulants, and stack-sorting*, Theorem 4.5 and Example 4.12.
-/

open Polynomial

namespace Polynomial

/-- If `X ^ k * f` is log-concave, then `f` is log-concave. -/
@[lognarayana "lem_log_concave_monomial_shift"]
public theorem IsLogConcave.of_X_pow_mul {R : Type*} [Semiring R] [PartialOrder R]
    {f : R[X]} {k : ℕ} (h : IsLogConcave (X ^ k * f)) : IsLogConcave f := by
  obtain ⟨h0, h1⟩ := h
  refine ⟨fun j => ?_, fun j => ?_⟩
  · simpa only [X_pow_mul, coeff_mul_X_pow] using h0 (j + k)
  · simpa only [X_pow_mul, coeff_mul_X_pow, Nat.add_right_comm _ k] using h1 (j + k)

end Polynomial

namespace List

/-- An additive map commutes with a `finsum` over a set as soon as it sends no nonzero term of
the summand to zero: if the support is infinite, both sides vanish. -/
private lemma map_finsum_mem_of_ne_zero {α M N : Type*} [AddCommMonoid M] [AddCommMonoid N]
    (g : M →+ N) (s : Set α) (f : α → M) (hg : ∀ a ∈ s, f a ≠ 0 → g (f a) ≠ 0) :
    g (∑ᶠ a ∈ s, f a) = ∑ᶠ a ∈ s, g (f a) := by
  by_cases hf : (s ∩ Function.support f).Finite
  · exact g.map_finsum_mem' hf
  · have hs : s ∩ Function.support (fun a => g (f a)) = s ∩ Function.support f := by
      ext a
      simp only [Set.mem_inter_iff, Function.mem_support]
      exact ⟨fun ⟨ha, h⟩ => ⟨ha, fun h0 => h (by rw [h0, map_zero])⟩,
        fun ⟨ha, h⟩ => ⟨ha, hg a ha h⟩⟩
    rw [finsum_mem_eq_zero_of_infinite hf, finsum_mem_eq_zero_of_infinite (by rwa [hs]), map_zero]

/-- Multiplication by `X` is injective on `R[X]`. -/
private lemma X_mul_injective {R : Type*} [Semiring R] {p q : R[X]} (h : X * p = X * q) :
    p = q := by
  ext n
  simpa [coeff_X_mul] using congrArg (coeff · (n + 1)) h

/-- The Schröder factor `R_q`, shifted by `X`, counts Schröder trees with `q` nodes by
`1 + ` their number of black nodes. -/
private lemma finsum_X_pow_succ_eq_X_mul_schroederFactor.{u, v}
    (htroupes : SchroederTreesBlackGenFunEq.{u, v})
    (C : Type u) [BinaryTree.TreeColors C] [DecidableEq C] (R : Type v) [CommSemiring R]
    [Nontrivial R] (q : ℕ) :
    ∑ᶠ T ∈ {T ∈ BinaryTree.schroederTrees C | T.numNodes = q},
      (X : R[X]) ^ (T.numBlackNodes + 1) = X * schroederFactor R q := by
  rw [← htroupes C R q]
  refine .trans ?_ (map_finsum_mem_of_ne_zero (.mulLeft X) _ _ fun T _ _ => ?_).symm
  · simp [pow_succ']
  · simpa [← pow_succ'] using (monic_X_pow (R := R) _).ne_zero

/-- **Schröder product formula**: for `n ≥ 1` and `π ∈ S_n`,
`𝒞_π(z, 1) = z^{des(π)} ∑_{q ∈ 𝒱(π)} ∏_{i=0}^{des(π)} R_{q_i}(z)`. -/
@[lognarayana "lem_schroeder_fertility_identity"]
public theorem aeval_schroederFiberPolynomial_eq_X_pow_mul_sum_prod_schroederFactor.{u, v}
    (hrefined : SchroederRefinedFertilityFormula.{u, v})
    (htroupes : SchroederTreesBlackGenFunEq.{u, v})
    (C : Type u) [BinaryTree.TreeColors C] [DecidableEq C] (R : Type v) [CommSemiring R]
    {n : ℕ} (hn : 1 ≤ n) {π : List ℕ} (hπ : π ∈ permWords n) :
    MvPolynomial.aeval ![(X : R[X]), 1] (schroederFiberPolynomial R C π) =
      X ^ π.numDescents * ∑ q ∈ π.validCompositions, ∏ i, schroederFactor R (q i) := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact Subsingleton.elim _ _
  apply X_mul_injective
  let g : MvPolynomial (Fin 2) R →+ R[X] :=
    (AddMonoidHom.mulLeft X).comp (MvPolynomial.aeval ![(X : R[X]), 1]).toAddMonoidHom
  have hg (b w : ℕ) : g (MvPolynomial.X 0 ^ b * MvPolynomial.X 1 ^ w) = X ^ (b + 1) := by
    simp [g, pow_succ']
  change g _ = _
  rw [List.schroederFiberPolynomial]
  refine (map_finsum_mem_of_ne_zero g {𝒯 | _ ∧ _} _
    fun _ _ _ => by rw [hg]; exact (monic_X_pow _).ne_zero).trans ?_
  simp_rw [hg]
  refine (hrefined C R n hn π hπ).trans ?_
  simp_rw [finsum_X_pow_succ_eq_X_mul_schroederFactor htroupes, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Finset.mul_sum]
  ring

end List

namespace Polynomial

/-- For an integral binary nestohedron `P ⊆ ℝ^r`, `r ≥ 1`, the polynomial
`∑_{q ∈ P ∩ ℤ^r} ∏_{i=1}^{r} R_{q_i}(z)` is log-concave. -/
@[lognarayana "thm_schroeder_nestohedron_lc"]
public theorem isLogConcave_finsum_latticePoints_prod_schroederFactor
    (hreal : IntegralBinaryNestohedronRealization)
    (htroupes : SchroederTreesBlackGenFunEq.{0, 0})
    (hrefined : SchroederRefinedFertilityFormula.{0, 0})
    (hsub : ∀ (σ τ : Type) [Fintype σ] [Fintype τ],
      MvPolynomial.LorentzianNonnegLinearSubstitution σ τ)
    (hmul : ∀ (σ : Type) [Fintype σ], MvPolynomial.LorentzianMul σ)
    (hBH : ∀ (σ : Type) [Fintype σ], MvPolynomial.NormalizedSupportPolyLorentzianOfMConvex σ)
    {r : ℕ} (hr : 1 ≤ r) {P : Set (Fin r → ℝ)} (hP : IsIntegralBinaryNestohedron ℝ P) :
    (∑ᶠ q ∈ P.latticePoints, ∏ i, schroederFactor ℝ ⌊q i⌋₊).IsLogConcave := by
  obtain ⟨n, hn, π, hπ, rfl, hlat⟩ := hreal r hr P hP
  let : BinaryTree.TreeColors Bool := ⟨true, false, by decide⟩
  have hinj : Function.Injective
      (fun (q : Fin (π.numDescents + 1) → ℕ) (i : Fin (π.numDescents + 1)) =>
        (q (Fin.cast rfl i) : ℝ)) := by
    intro a b hab
    funext i
    simpa using congrFun hab i
  have hF : (∑ᶠ q ∈ P.latticePoints, ∏ i, schroederFactor ℝ ⌊q i⌋₊) =
      ∑ q ∈ π.validCompositions, ∏ i, schroederFactor ℝ (q i) := by
    rw [hlat, finsum_mem_image hinj.injOn, finsum_mem_coe_finset]
    simp
  rw [hF]
  apply IsLogConcave.of_X_pow_mul (k := π.numDescents)
  rw [← List.aeval_schroederFiberPolynomial_eq_X_pow_mul_sum_prod_schroederFactor hrefined
    htroupes Bool ℝ hn hπ]
  exact (List.isUltraLogConcave_schroederFiberPolynomial_eval_one Bool hn hπ (hBH _) (hsub _ _)
    (hsub _ _) (hmul _)).isLogConcave

end Polynomial
