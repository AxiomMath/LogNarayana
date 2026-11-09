/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib
public import LogNarayana.Attr
public import LogNarayana.Noncrossing.RestrictedRefinement.Defs
public import LogNarayana.Narayana.Polynomials.Defs
public import LogNarayana.Polynomial.LogConcave.Defs
public import LogNarayana.Nestohedron.Fertilitope.Defs
public import LogNarayana.Nestohedron.QuadraticReplacement.Basic
public import LogNarayana.Nestohedron.Fertilitope.Basic
public import LogNarayana.Lorentzian.BrandenHuh.Basic
public import LogNarayana.Lorentzian.Symbol.Basic
public import LogNarayana.Narayana.Polynomials.Basic
public import LogNarayana.StackSorting.ValidHookConfigurations.Basic

/-!
# Noncrossing partitions and restricted refinements

Kreweras' count of noncrossing partitions with prescribed block sizes, together with the
multinomial count of words of a given content, shows that summing a block-multiplicative weight
`∏_{B ∈ τ} f(|B|)` over the noncrossing partitions `τ` of `[n]` with `k` blocks gives
`n! / (k! (n - k + 1)!)` times the sum of `∏ᵢ f(qᵢ)` over the compositions `q` of `n` into `k`
positive parts. With `f = x` this gives `∑_{ρ ∈ NC(q)} x^{|ρ|} = N_q(x)`.

A lower interval `{σ ∈ NC(n) : σ ≤ τ}` is isomorphic to the product `∏_{B ∈ τ} NC(B)`, and
`NC(B)` has the block distribution of `NC(|B|)`, so the inner sums of `R^{(a)}_{n,k}` are
`∏_{B ∈ τ} N_{|B|}(x)`; since `N^{(1)}_q = N_q`, this is `R^{(a)}_{n,k} = R^{(a),1}_{n,k}`.
The composition-sum form of `R^{(a),λ}_{n,k}` runs over the lattice points of the integral binary
nestohedron `a𝟙 + (n - ak)Δ_{[k]}`, so `R^{(a),λ}_{n,k}`, and hence `R^{(a)}_{n,k}`, is
log-concave with no internal zeros for `0 ≤ λ ≤ 2`. The section closes with the example
`R^{(3)}_{12,3}`.

## Main results

* `Fintype.card_fun_filter_card_fiber_eq_multinomial`: words of a given content are counted by
  a multinomial coefficient.
* `Finpartition.sum_noncrossing_prod_card_parts_eq`: the block-product sum over `NC(n)`.
* `Finpartition.sum_noncrossing_X_pow_blockCount_eq_narayanaPolynomial`:
  `∑_{ρ ∈ NC(q)} x^{|ρ|} = N_q(x)`.
* `Finpartition.sum_noncrossing_X_pow_blockCount_eq_of_card_eq`: the block distribution of
  `NC(A)` depends only on `#A`.
* `Finpartition.exists_orderIso_noncrossing_le_pi`: lower intervals of `NC(A)` are products.
* `Finpartition.sum_noncrossing_le_X_pow_blockCount_eq_prod_narayanaPolynomial`:
  `∑_{σ ≤ τ} x^{|σ|} = ∏_{B ∈ τ} N_{|B|}(x)`.
* `restrictedNoncrossingDeformedNarayanaPoly_eq_sum_antidiagonalTuple`: the composition-sum
  form of `R^{(a),λ}_{n,k}`.
* `restrictedNoncrossingDeformedNarayanaPoly_one`: `R^{(a),1}_{n,k} = R^{(a)}_{n,k}`.
* `restrictedNoncrossingRefinementPoly_icc_twelve_three_three`: the polynomial `R^{(3)}_{12,3}`.
* `latticePoints_image_smul_coordSimplex_univ`,
  `encard_latticePoints_image_smul_coordSimplex_fin_three`: lattice points of `a𝟙 + cΔ_{[k]}`.
* `isIntegralBinaryNestohedron_image_smul_coordSimplex_univ`: `a𝟙 + cΔ_{[k]}` is an integral
  binary nestohedron.
* `Polynomial.isLogConcave_restrictedNoncrossingDeformedNarayanaPoly`,
  `Polynomial.hasNoInternalZeros_coeff_restrictedNoncrossingDeformedNarayanaPoly`,
  `Polynomial.isLogConcave_restrictedNoncrossingRefinementPoly`,
  `Polynomial.hasNoInternalZeros_coeff_restrictedNoncrossingRefinementPoly`: log-concavity and
  no internal zeros of `R^{(a),λ}_{n,k}` and `R^{(a)}_{n,k}`.

## Implementation notes

`[n]` is `Finset.Icc 1 n` in `ℕ`, and the compositions of `n` into `k` parts are tuples of
`Finset.Nat.antidiagonalTuple k n`. Kreweras' formula and the other cited results are taken as
hypotheses. The paper's hypotheses `n ≥ 1` (and similar) are dropped wherever the identity
also holds without them.

## References

* [LogNarayana], Section 7.
* [Kreweras1972] G. Kreweras, *Sur les partitions non croisées d'un cycle*, Discrete Math. 1
  (1972).
-/

/-! ### Words of a given content -/

section

open Finset MvPolynomial

/-- A product of `g ∘ f` over a finite type collects into powers indexed by the fibres of `f`. -/
private lemma prod_comp_eq_prod_pow_card_fiber {ι σ M : Type*} [Fintype ι] [Fintype σ]
    [DecidableEq σ] [CommMonoid M] (g : σ → M) (f : ι → σ) :
    ∏ i, g (f i) = ∏ j, g j ^ #{i | f i = j} := by
  rw [← prod_fiberwise univ f]
  refine prod_congr rfl fun j _ => ?_
  rw [prod_congr rfl fun i hi => by rw [(mem_filter.1 hi).2], prod_const]

/-- Expanding `(∑ⱼ X j) ^ k` as a sum over words: the coefficient of `X ^ s` is the number of
words `q : Fin k → σ` in which each letter `j` occurs `s j` times. -/
private lemma coeff_sum_X_pow_eq_card {σ : Type*} [Fintype σ] [DecidableEq σ] (k : ℕ)
    (s : σ →₀ ℕ) :
    coeff s ((∑ j, X j : MvPolynomial σ ℕ) ^ k) =
      #{q : Fin k → σ | ∀ j, #{i | q i = j} = s j} := by
  rw [← Fin.prod_const, Fintype.prod_sum, coeff_sum]
  simp_rw [prod_comp_eq_prod_pow_card_fiber X, coeff_prod_X_pow, card_eq_sum_ones, sum_filter]
  refine sum_congr rfl fun q _ => ?_
  simp [Finsupp.ext_iff, eq_comm]

/-- The multinomial theorem: the coefficient of `X ^ s` in `(∑ⱼ X j) ^ k` is the multinomial
coefficient of `s`, when `∑ⱼ s j = k`. -/
private lemma coeff_sum_X_pow_eq_multinomial {σ : Type*} [Fintype σ] {k : ℕ}
    (s : σ →₀ ℕ) (hk : ∑ j, s j = k) :
    coeff s ((∑ j, X j : MvPolynomial σ ℕ) ^ k) = Nat.multinomial univ s := by
  have := coeff_linearCombination_X_pow_of_fintype (R := ℕ) (fun _ => 1) s k
  rw [if_pos (by rwa [Finsupp.sum_fintype _ _ (by simp)]),
    ← Finsupp.multinomial_of_support_subset (subset_univ _)] at this
  simpa [Finsupp.prod] using this

open Finset

/-- The number of words `q ∈ [n]^k` in which each letter `j` occurs exactly `m j` times is the
multinomial coefficient `k! / ∏ⱼ (m j)!`, when `∑ⱼ m j = k`. -/
@[lognarayana "lem_composition_type_count"]
public theorem Fintype.card_fun_filter_card_fiber_eq_multinomial {n k : ℕ} (m : Fin n → ℕ)
    (hk : ∑ j, m j = k) :
    #{q : Fin k → Fin n | ∀ j, #{i | q i = j} = m j} = Nat.multinomial univ m := by
  simpa using (coeff_sum_X_pow_eq_card k (Finsupp.equivFunOnFinite.symm m)).symm.trans
    (coeff_sum_X_pow_eq_multinomial _ (by simpa using hk))

end

/-! ### Block-product sums over noncrossing partitions -/

section

open Finset Polynomial

open scoped Classical in
/-- The multiplicity function of `g` on `s`: `j ↦ #{i ∈ s | g i = j}`. -/
private noncomputable def mult {ι : Type*} (s : Finset ι) (g : ι → ℕ) (j : ℕ) : ℕ :=
  #{i ∈ s | g i = j}

open scoped Classical in
private lemma mult_eq_zero {ι : Type*} {s : Finset ι} {g : ι → ℕ} {t : Finset ℕ}
    (h : ∀ i ∈ s, g i ∈ t) {j : ℕ} (hj : j ∉ t) : mult s g j = 0 := by
  rw [mult, card_eq_zero, filter_eq_empty_iff]
  rintro i hi rfl
  exact hj (h i hi)

open scoped Classical in
/-- A multiplicity function is determined by its values on a set containing the image. -/
private lemma mult_eq_of_eqOn {ι : Type*} {s : Finset ι} {g : ι → ℕ} {t : Finset ℕ}
    (h : ∀ i ∈ s, g i ∈ t) {m : ℕ → ℕ} (hm0 : ∀ j ∉ t, m j = 0)
    (hm : ∀ j ∈ t, mult s g j = m j) : mult s g = m := by
  funext j
  by_cases hj : j ∈ t
  · exact hm j hj
  · rw [mult_eq_zero h hj, hm0 j hj]

open scoped Classical in
private lemma sum_mult {ι : Type*} {s : Finset ι} {g : ι → ℕ} {t : Finset ℕ}
    (h : ∀ i ∈ s, g i ∈ t) : ∑ j ∈ t, mult s g j = #s :=
  (card_eq_sum_card_fiberwise h).symm

open scoped Classical in
private lemma sum_mul_mult {ι : Type*} {s : Finset ι} {g : ι → ℕ} {t : Finset ℕ}
    (h : ∀ i ∈ s, g i ∈ t) : ∑ j ∈ t, j * mult s g j = ∑ i ∈ s, g i := by
  rw [← sum_fiberwise_of_maps_to h]
  refine sum_congr rfl fun j _ => ?_
  rw [mult, sum_congr rfl (fun i hi => (mem_filter.1 hi).2), sum_const, smul_eq_mul, mul_comm]

open scoped Classical in
private lemma prod_pow_mult {ι M : Type*} [CommMonoid M] {s : Finset ι} {g : ι → ℕ}
    {t : Finset ℕ} (h : ∀ i ∈ s, g i ∈ t) (F : ℕ → M) :
    ∏ j ∈ t, F j ^ mult s g j = ∏ i ∈ s, F (g i) := by
  rw [← prod_fiberwise_of_maps_to h]
  refine prod_congr rfl fun j _ => ?_
  rw [mult, prod_congr rfl (fun i hi => congrArg F (mem_filter.1 hi).2), prod_const]

open scoped Classical in
@[to_additive]
private lemma prod_fin_eq_prod_Icc {M : Type*} [CommMonoid M] (n : ℕ) (F : ℕ → M) :
    ∏ j : Fin n, F (j + 1) = ∏ j ∈ Icc 1 n, F j := by
  rw [Fin.prod_univ_eq_prod_range (fun j => F (j + 1)), range_eq_Ico, prod_Ico_add' F 0 n 1]
  rfl

open scoped Classical in
private lemma card_mem_Icc {n : ℕ} (τ : Finpartition (Icc 1 n)) {B : Finset ℕ}
    (hB : B ∈ τ.parts) : B.card ∈ Icc 1 n :=
  mem_Icc.2 ⟨card_pos.2 (τ.nonempty_of_mem_parts hB), by simpa using card_le_card (τ.le hB)⟩

open scoped Classical in
/-- The positive compositions of `n` into `k` parts. -/
private noncomputable abbrev compositions (k n : ℕ) : Finset (Fin k → ℕ) :=
  (Finset.Nat.antidiagonalTuple k n).filter (fun q => ∀ i, 0 < q i)

open scoped Classical in
private lemma mem_Icc_of_mem_compositions {k n : ℕ} {q : Fin k → ℕ}
    (hq : q ∈ compositions k n) (i : Fin k) : q i ∈ Icc 1 n := by
  obtain ⟨hq, hpos⟩ := mem_filter.1 hq
  rw [Finset.Nat.mem_antidiagonalTuple] at hq
  exact mem_Icc.2 ⟨hpos i, hq ▸ single_le_sum (fun j _ => Nat.zero_le (q j)) (mem_univ i)⟩

open scoped Classical in
/-- `m` is a block-size type of a partition of `[n]` into `k` blocks. -/
private def IsType (n k : ℕ) (m : ℕ → ℕ) : Prop :=
  (∀ j ∉ Icc 1 n, m j = 0) ∧ ∑ j ∈ Icc 1 n, m j = k ∧ ∑ j ∈ Icc 1 n, j * m j = n

open scoped Classical in
private lemma isType_parts {n k : ℕ} {τ : Finpartition (Icc 1 n)} (hτ : τ.blockCount = k) :
    IsType n k (mult τ.parts card) := by
  have h := fun B (hB : B ∈ τ.parts) => card_mem_Icc τ hB
  refine ⟨fun j hj => mult_eq_zero h hj, by rw [sum_mult h]; exact hτ, ?_⟩
  rw [sum_mul_mult h, τ.sum_card_parts]
  simp

open scoped Classical in
private lemma isType_compositions {n k : ℕ} {q : Fin k → ℕ} (hq : q ∈ compositions k n) :
    IsType n k (mult univ q) := by
  have h := fun i (_ : i ∈ univ) => mem_Icc_of_mem_compositions hq i
  refine ⟨fun j hj => mult_eq_zero h hj, by rw [sum_mult h]; simp, ?_⟩
  rw [sum_mul_mult h]
  exact Finset.Nat.mem_antidiagonalTuple.1 (mem_filter.1 hq).1

open scoped Classical in
/-- Kreweras' formula, in terms of the block-size type `mult τ.parts card`. -/
private lemma card_nc_fiber (hKr : Finpartition.KrewerasBlockSizeCount) {n k : ℕ} {m : ℕ → ℕ}
    (hm : IsType n k m) :
    #{τ ∈ univ.filter (fun τ : Finpartition (Icc 1 n) => τ.IsNoncrossing ∧ τ.blockCount = k) |
        mult τ.parts card = m} * ((n - k + 1).factorial * ∏ j ∈ Icc 1 n, (m j).factorial) =
      n.factorial := by
  obtain ⟨hm0, hmk, hmn⟩ := hm
  have := hKr n m hmn
  rw [hmk] at this
  convert this using 3
  ext τ
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨⟨hnc, -⟩, h⟩
    exact ⟨hnc, fun j _ => congrFun h j⟩
  · rintro ⟨hnc, h⟩
    have h' := mult_eq_of_eqOn (fun B hB => card_mem_Icc τ hB) hm0 h
    refine ⟨⟨hnc, ?_⟩, h'⟩
    rw [Finpartition.blockCount, ← sum_mult (fun B hB => card_mem_Icc τ hB), h', hmk]

open scoped Classical in
/-- The positive compositions of `n` of type `m` are counted by a multinomial coefficient. -/
private lemma card_compositions_fiber {n k : ℕ} {m : ℕ → ℕ} (hm : IsType n k m) :
    (∏ j ∈ Icc 1 n, (m j).factorial) * #{q ∈ compositions k n | mult univ q = m} =
      k.factorial := by
  obtain ⟨hm0, hmk, hmn⟩ := hm
  have hk' : ∑ j : Fin n, m (j + 1) = k := by rw [sum_fin_eq_sum_Icc, hmk]
  rw [← prod_fin_eq_prod_Icc n (fun j => (m j).factorial), ← hk',
    ← Nat.multinomial_spec univ (fun j : Fin n => m (j + 1)), hk',
    ← Fintype.card_fun_filter_card_fiber_eq_multinomial _ hk']
  congr 1
  symm
  refine card_bij (fun q' _ i => (q' i : ℕ) + 1) ?_ ?_ ?_
  · intro q' hq'
    simp only [mem_filter, mem_univ, true_and] at hq'
    have hmaps : ∀ i ∈ (univ : Finset (Fin k)), (q' i : ℕ) + 1 ∈ Icc 1 n := fun i _ =>
      mem_Icc.2 ⟨by omega, (q' i).2⟩
    have hm' : mult univ (fun i => (q' i : ℕ) + 1) = m := by
      refine mult_eq_of_eqOn hmaps hm0 fun j hj => ?_
      rw [mem_Icc] at hj
      have := hq' ⟨j - 1, by omega⟩
      simp only [show j - 1 + 1 = j by omega] at this
      rw [← this, mult]
      congr 1
      ext i
      simp only [mem_filter, mem_univ, true_and, Fin.ext_iff]
      omega
    refine mem_filter.2 ⟨mem_filter.2 ⟨?_, fun i => Nat.succ_pos _⟩, hm'⟩
    rw [Finset.Nat.mem_antidiagonalTuple, ← sum_mul_mult hmaps, hm', hmn]
  · intro q₁ _ q₂ _ h
    funext i
    exact Fin.ext (by simpa using congrFun h i)
  · intro q hq
    obtain ⟨hqQ, hqm⟩ := mem_filter.1 hq
    have hi : ∀ i, 1 ≤ q i ∧ q i ≤ n := fun i => mem_Icc.1 (mem_Icc_of_mem_compositions hqQ i)
    refine ⟨fun i => ⟨q i - 1, by have := hi i; omega⟩, ?_, ?_⟩
    · simp only [mem_filter, mem_univ, true_and]
      intro j
      rw [← hqm, mult]
      congr 1
      ext i
      have := hi i
      simp only [mem_filter, mem_univ, true_and, Fin.ext_iff]
      omega
    · funext i
      have := hi i
      simp only
      omega

open scoped Classical in
/-- On each block-size type `m`, the noncrossing partitions of `[n]` into `k` blocks and the
positive compositions of `n` into `k` parts occur in the ratio `n! / (k! (n - k + 1)!)`. -/
private lemma card_nc_fiber_eq (hKr : Finpartition.KrewerasBlockSizeCount) {n k : ℕ}
    {m : ℕ → ℕ} (hm : IsType n k m) :
    (#{τ ∈ univ.filter (fun τ : Finpartition (Icc 1 n) => τ.IsNoncrossing ∧ τ.blockCount = k) |
        mult τ.parts card = m} : ℝ) =
      n.factorial / (k.factorial * (n - k + 1).factorial) *
        #{q ∈ compositions k n | mult univ q = m} := by
  rw [div_mul_eq_mul_div, eq_div_iff (by positivity)]
  rw [← card_nc_fiber hKr hm, ← card_compositions_fiber hm]
  push_cast
  ring

namespace Finpartition

open Finset Polynomial

open scoped Classical in
/-- For any `f : ℕ → ℝ[X]`, the sum over noncrossing partitions `τ` of `[n]` with `k` blocks of
`∏_{B ∈ τ} f |B|` is `n! / (k! (n - k + 1)!)` times the sum over compositions `q` of `n` into `k`
positive parts of `∏ᵢ f (qᵢ)`, given Kreweras' block-size count. -/
@[lognarayana "lem_nc_block_product_sum"]
public theorem sum_noncrossing_prod_card_parts_eq (hKr : KrewerasBlockSizeCount)
    (n k : ℕ) (f : ℕ → ℝ[X]) :
    open scoped Classical in
    ∑ τ ∈ univ.filter (fun τ : Finpartition (Icc 1 n) => τ.IsNoncrossing ∧ τ.blockCount = k),
        ∏ B ∈ τ.parts, f B.card =
      C ((n.factorial : ℝ) / (k.factorial * (n - k + 1).factorial)) *
        ∑ q ∈ (Finset.Nat.antidiagonalTuple k n).filter (fun q => ∀ i, 0 < q i),
          ∏ i, f (q i) := by
  set S := univ.filter (fun τ : Finpartition (Icc 1 n) => τ.IsNoncrossing ∧ τ.blockCount = k)
  set M := S.image (fun τ => mult τ.parts card) ∪ (compositions k n).image (mult univ)
  rw [← sum_fiberwise_of_maps_to (g := fun τ => mult τ.parts card) (t := M)
      (fun τ hτ => mem_union_left _ (mem_image_of_mem _ hτ)),
    ← sum_fiberwise_of_maps_to (g := mult univ) (t := M)
      (fun q hq => mem_union_right _ (mem_image_of_mem _ hq)), mul_sum]
  refine sum_congr rfl fun m hm => ?_
  have hmT : IsType n k m := by
    rcases mem_union.1 hm with hm | hm
    · obtain ⟨τ, hτ, rfl⟩ := mem_image.1 hm
      exact isType_parts (mem_filter.1 hτ).2.2
    · obtain ⟨q, hq, rfl⟩ := mem_image.1 hm
      exact isType_compositions hq
  rw [sum_congr rfl (g := fun _ => ∏ j ∈ Icc 1 n, f j ^ m j) ?_,
    sum_congr (s₁ := {q ∈ compositions k n | mult univ q = m}) rfl
      (g := fun _ => ∏ j ∈ Icc 1 n, f j ^ m j) ?_,
    sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul, ← mul_assoc, ← map_natCast C,
    ← map_natCast C, ← C_mul, card_nc_fiber_eq hKr hmT]
  · intro q hq
    rw [← (mem_filter.1 hq).2, prod_pow_mult (fun i _ => mem_Icc_of_mem_compositions
      (mem_filter.1 hq).1 i)]
  · intro τ hτ
    rw [← (mem_filter.1 hτ).2, prod_pow_mult (fun B hB => card_mem_Icc τ hB)]

end Finpartition

end

/-! ### Noncrossing partitions counted by blocks -/

section

open Finset Polynomial

/-- The number of tuples `Fin k → ℕ` with sum `m` is `(k + m - 1).choose m`. -/
private lemma card_antidiagonalTuple (k m : ℕ) :
    #(Finset.Nat.antidiagonalTuple k m) = (k + m - 1).choose m := by
  have h := Finset.card_finsuppAntidiag_nat_eq_choose (s := (univ : Finset (Fin k))) m
  rw [card_univ, Fintype.card_fin] at h
  rw [← h]
  refine card_bij (fun f _ => Finsupp.equivFunOnFinite.symm f) ?_
    (fun a _ b _ hab => Finsupp.equivFunOnFinite.symm.injective hab) ?_
  · intro f hf
    simp_all [Finset.Nat.mem_antidiagonalTuple, mem_finsuppAntidiag]
  · intro g hg
    refine ⟨Finsupp.equivFunOnFinite g, ?_, by simp⟩
    simpa [Finset.Nat.mem_antidiagonalTuple] using (mem_finsuppAntidiag.1 hg).1

/-- The number of compositions of `n` into `k ≤ n` positive parts is `(n - 1).choose (n - k)`. -/
private lemma card_positive_compositions {k n : ℕ} (hkn : k ≤ n) :
    #((Finset.Nat.antidiagonalTuple k n).filter (fun q => ∀ i, 0 < q i)) =
      (n - 1).choose (n - k) := by
  rw [← show k + (n - k) - 1 = n - 1 by omega, ← card_antidiagonalTuple]
  refine card_bij' (fun q _ i => q i - 1) (fun p _ i => p i + 1) ?_ ?_ ?_ ?_
  · intro q hq
    simp only [mem_filter, Finset.Nat.mem_antidiagonalTuple] at hq ⊢
    have : ∑ i, (q i - 1 + 1) = n := by
      rw [← hq.1]; exact sum_congr rfl fun i _ => Nat.sub_add_cancel (hq.2 i)
    simp [sum_add_distrib] at this
    omega
  · intro p hp
    simp only [mem_filter, Finset.Nat.mem_antidiagonalTuple] at hp ⊢
    refine ⟨?_, fun i => Nat.succ_pos _⟩
    simp [sum_add_distrib, hp]; omega
  · intro q hq
    funext i; exact Nat.sub_add_cancel ((mem_filter.1 hq).2 i)
  · intro p _
    funext i; simp

/-- The coefficient identity
`q! / (k! (q - k + 1)!) · (q - 1).choose (q - k) = q⁻¹ · q.choose k · q.choose (k - 1)`
for `1 ≤ k ≤ q`. -/
private lemma coeff_eq {k q : ℕ} (hk : 1 ≤ k) (hkq : k ≤ q) :
    (q.factorial : ℝ) / (k.factorial * (q - k + 1).factorial) * ((q - 1).choose (q - k) : ℕ) =
      (q : ℝ)⁻¹ * (q.choose k : ℝ) * (q.choose (k - 1) : ℝ) := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le' hk
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hkq
  rw [show i + 1 + j - 1 = i + j by omega, show i + 1 + j - (i + 1) = j by omega,
    show i + 1 - 1 = i by omega, Nat.cast_choose ℝ (show j ≤ i + j by omega),
    Nat.cast_choose ℝ (show i + 1 ≤ i + 1 + j by omega),
    Nat.cast_choose ℝ (show i ≤ i + 1 + j by omega),
    show i + j - j = i by omega, show i + 1 + j - (i + 1) = j by omega,
    show i + 1 + j - i = j + 1 by omega, show i + 1 + j = (i + j) + 1 by omega,
    Nat.factorial_succ (i + j), Nat.factorial_succ i, Nat.factorial_succ j]
  have := Nat.factorial_pos i
  have := Nat.factorial_pos j
  have := Nat.factorial_pos (i + j)
  push_cast
  field_simp

/-- For `1 ≤ k ≤ q`, the noncrossing partitions of `[q]` with `k` blocks contribute the
Narayana monomial `q⁻¹ · q.choose k · q.choose (k - 1) · x^k`. -/
private lemma sum_noncrossing_blockCount_eq (hKr : Finpartition.KrewerasBlockSizeCount)
    {q k : ℕ} (hk : 1 ≤ k) (hkq : k ≤ q) :
    open scoped Classical in
    ∑ ρ ∈ univ.filter (fun ρ : Finpartition (Icc 1 q) =>
        ρ.IsNoncrossing ∧ ρ.blockCount = k), (X : ℝ[X]) ^ ρ.blockCount =
      C ((q : ℝ)⁻¹ * (q.choose k : ℝ) * (q.choose (k - 1) : ℝ)) * X ^ k := by
  classical
  have := Finpartition.sum_noncrossing_prod_card_parts_eq hKr q k (fun _ => X)
  simp only [prod_const, card_univ, Fintype.card_fin, sum_const,
    card_positive_compositions hkq, nsmul_eq_mul] at this
  rw [← coeff_eq hk hkq, C_mul, mul_assoc, C_eq_natCast, ← this]

namespace Finpartition

open Finset Polynomial

/-- The sum of `x ^ |ρ|` over the noncrossing partitions `ρ` of `[q] = Finset.Icc 1 q` is the
Narayana polynomial `N_q(x)`. -/
@[lognarayana "lem_nc_narayana_blocks"]
public theorem sum_noncrossing_X_pow_blockCount_eq_narayanaPolynomial
    (hKr : KrewerasBlockSizeCount) (q : ℕ) :
    open scoped Classical in
    ∑ ρ ∈ univ.filter (fun ρ : Finpartition (Icc 1 q) => ρ.IsNoncrossing),
        (X : ℝ[X]) ^ ρ.blockCount = narayanaPolynomial q := by
  classical
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · have h (ρ : Finpartition (Icc 1 0)) : ρ.blockCount = 0 := by
      simp [Finpartition.blockCount, Finpartition.parts_eq_empty_iff]
    simpa [narayanaPolynomial, h] using
      Finpartition.sum_noncrossing_prod_card_parts_eq hKr 0 0 (fun _ => X)
  rw [narayanaPolynomial, if_neg hq.ne', ← sum_fiberwise_of_maps_to (t := Icc 1 q)
    (g := Finpartition.blockCount) fun ρ _ => ?_]
  · simp_rw [filter_filter]
    exact sum_congr rfl fun k hk =>
      sum_noncrossing_blockCount_eq hKr (mem_Icc.1 hk).1 (mem_Icc.1 hk).2
  · have h1 := ρ.card_parts_le_card
    have h2 := (ρ.parts_nonempty (nonempty_Icc.2 hq).ne_empty).card_pos
    simp only [Nat.card_Icc] at h1
    simp only [mem_Icc, Finpartition.blockCount]; omega

end Finpartition

end

/-! ### Relabelling the ground set -/

section

open Finset Polynomial

variable {α β : Type*}

/-- The image of a finite partition of `s` under a map injective on `s`. -/
private def imagePart [DecidableEq α] [DecidableEq β] (f : α → β) {s : Finset α} {t : Finset β}
    (hf : Set.InjOn f s) (ht : s.image f = t) (P : Finpartition s) : Finpartition t where
  parts := P.parts.image (Finset.image f)
  supIndep := by
    rw [Finset.supIndep_iff_pairwiseDisjoint]
    rintro _ hB' _ hC' hne
    obtain ⟨B, hB, rfl⟩ := mem_image.1 (Finset.mem_coe.1 hB')
    obtain ⟨C, hC, rfl⟩ := mem_image.1 (Finset.mem_coe.1 hC')
    have hBC : B ≠ C := by rintro rfl; exact hne rfl
    have hd := P.disjoint hB hC hBC
    simp only [Function.onFun, id]
    rw [Finset.disjoint_left]
    rintro _ hx' hy'
    obtain ⟨x, hx, rfl⟩ := mem_image.1 hx'
    obtain ⟨y, hy, hxy⟩ := mem_image.1 hy'
    have := hf (Finset.mem_coe.2 (P.le hC hy)) (Finset.mem_coe.2 (P.le hB hx)) hxy
    subst this
    exact Finset.disjoint_left.1 hd hx hy
  sup_parts := by
    rw [← ht]
    conv_rhs => rw [← P.sup_parts]
    ext y
    simp only [Finset.sup_image, Finset.mem_sup, Function.comp, id, mem_image]
    constructor
    · rintro ⟨B, hB, x, hx, rfl⟩
      exact ⟨x, ⟨B, hB, hx⟩, rfl⟩
    · rintro ⟨x, ⟨B, hB, hx⟩, rfl⟩
      exact ⟨B, hB, x, hx, rfl⟩
  bot_notMem := by
    simp only [mem_image, not_exists, not_and]
    intro B hB h
    exact P.ne_bot hB (by simpa using h)


private theorem parts_imagePart [DecidableEq α] [DecidableEq β] (f : α → β) {s : Finset α}
    {t : Finset β} (hf : Set.InjOn f s) (ht : s.image f = t) (P : Finpartition s) :
    (imagePart f hf ht P).parts = P.parts.image (Finset.image f) := rfl

private theorem image_image_of_leftInvOn [DecidableEq α] [DecidableEq β] {f : α → β}
    {g : β → α} {s B : Finset α} (hgf : ∀ x ∈ s, g (f x) = x) (hB : B ⊆ s) :
    (B.image f).image g = B := by
  rw [Finset.image_image]
  conv_rhs => rw [← Finset.image_id (s := B)]
  exact Finset.image_congr fun x hx => hgf x (hB hx)

private theorem imagePart_imagePart [DecidableEq α] [DecidableEq β] {f : α → β} {g : β → α}
    {s : Finset α} {t : Finset β} (hf : Set.InjOn f s) (hg : Set.InjOn g t)
    (hst : s.image f = t) (hts : t.image g = s) (hgf : ∀ x ∈ s, g (f x) = x)
    (P : Finpartition s) :
    imagePart g hg hts (imagePart f hf hst P) = P := by
  ext B
  rw [parts_imagePart, parts_imagePart, Finset.image_image]
  have : (P.parts.image (Finset.image g ∘ Finset.image f)) = P.parts.image id :=
    Finset.image_congr fun C hC => image_image_of_leftInvOn hgf (P.le hC)
  rw [this, Finset.image_id]

private theorem card_parts_imagePart [DecidableEq α] [DecidableEq β] {f : α → β} {g : β → α}
    {s : Finset α} {t : Finset β} (hf : Set.InjOn f s) (hst : s.image f = t)
    (hgf : ∀ x ∈ s, g (f x) = x) (P : Finpartition s) :
    (imagePart f hf hst P).blockCount = P.blockCount := by
  rw [Finpartition.blockCount, parts_imagePart, Finset.card_image_of_injOn]
  intro B hB C hC h
  rw [← image_image_of_leftInvOn hgf (P.le hB), ← image_image_of_leftInvOn hgf (P.le hC)]
  exact congrArg (Finset.image g) h

private theorem isNoncrossing_of_imagePart [LinearOrder α] [LinearOrder β] {f : α → β}
    {g : β → α} {s : Finset α} {t : Finset β} (hf : Set.InjOn f s) (hst : s.image f = t)
    (hgf : ∀ x ∈ s, g (f x) = x) (hmono : StrictMonoOn f s) (P : Finpartition s)
    (h : (imagePart f hf hst P).IsNoncrossing) : P.IsNoncrossing := by
  intro B hB B' hB' hne a ha c hc b hb d hd ⟨h1, h2, h3⟩
  have hs : ∀ x ∈ B, x ∈ s := fun x hx => P.le hB hx
  have hs' : ∀ x ∈ B', x ∈ s := fun x hx => P.le hB' hx
  refine h (B.image f) (mem_image_of_mem _ hB) (B'.image f) (mem_image_of_mem _ hB') ?_
    (f a) (mem_image_of_mem f ha) (f c) (mem_image_of_mem f hc)
    (f b) (mem_image_of_mem f hb) (f d) (mem_image_of_mem f hd)
    ⟨hmono (hs a ha) (hs' b hb) h1, hmono (hs' b hb) (hs c hc) h2,
      hmono (hs c hc) (hs' d hd) h3⟩
  intro heq
  apply hne
  rw [← image_image_of_leftInvOn hgf (P.le hB), ← image_image_of_leftInvOn hgf (P.le hB'), heq]

open scoped Classical in
private theorem sum_noncrossing_eq_of_strictMonoOn [LinearOrder α] [LinearOrder β]
    {M : Type*} [AddCommMonoid M] (F : ℕ → M) {f : α → β} {g : β → α}
    {s : Finset α} {t : Finset β} (hst : s.image f = t) (hts : t.image g = s)
    (hgf : ∀ x ∈ s, g (f x) = x) (hfg : ∀ y ∈ t, f (g y) = y)
    (hf : StrictMonoOn f s) (hg : StrictMonoOn g t) :
    ∑ ρ ∈ univ.filter (fun ρ : Finpartition s => ρ.IsNoncrossing), F ρ.blockCount =
      ∑ ρ ∈ univ.filter (fun ρ : Finpartition t => ρ.IsNoncrossing), F ρ.blockCount := by
  have hfi : Set.InjOn f s := fun x hx y hy h => by rw [← hgf x hx, ← hgf y hy, h]
  have hgi : Set.InjOn g t := fun x hx y hy h => by rw [← hfg x hx, ← hfg y hy, h]
  refine Finset.sum_nbij' (imagePart f hfi hst) (imagePart g hgi hts) ?_ ?_ ?_ ?_ ?_
  · intro ρ hρ
    simp only [mem_filter, mem_univ, true_and] at hρ ⊢
    refine isNoncrossing_of_imagePart hgi hts hfg hg _ ?_
    rwa [imagePart_imagePart hfi hgi hst hts hgf]
  · intro ρ hρ
    simp only [mem_filter, mem_univ, true_and] at hρ ⊢
    refine isNoncrossing_of_imagePart hfi hst hgf hf _ ?_
    rwa [imagePart_imagePart hgi hfi hts hst hfg]
  · intro ρ _
    exact imagePart_imagePart hfi hgi hst hts hgf ρ
  · intro ρ _
    exact imagePart_imagePart hgi hfi hts hst hfg ρ
  · intro ρ _
    rw [card_parts_imagePart hfi hst hgf]

open scoped Classical in
private theorem sum_noncrossing_empty [LinearOrder α] {M : Type*} [AddCommMonoid M]
    (F : ℕ → M) :
    ∑ ρ ∈ univ.filter (fun ρ : Finpartition (∅ : Finset α) => ρ.IsNoncrossing),
      F ρ.blockCount = F 0 := by
  have h0 : ∀ ρ : Finpartition (∅ : Finset α), ρ.parts = ∅ :=
    fun ρ => Finpartition.parts_eq_empty_iff.2 rfl
  have hnc : ∀ ρ : Finpartition (∅ : Finset α), ρ.IsNoncrossing := by
    intro ρ B hB
    simp [h0 ρ] at hB
  have : Unique (Finpartition (∅ : Finset α)) :=
    inferInstanceAs (Unique (Finpartition (⊥ : Finset α)))
  rw [Finset.filter_true_of_mem (fun ρ _ => hnc ρ), Finset.univ_unique, Finset.sum_singleton,
    Finpartition.blockCount, h0, Finset.card_empty]

/-- A map `s → t` between finsets, extended to all of `α` by the value `b₀` off `s`. -/
private def extend [DecidableEq α] {s : Finset α} {t : Finset β} (e : s → t) (b₀ : β) (a : α) :
    β :=
  if h : a ∈ s then e ⟨a, h⟩ else b₀

private theorem extend_coe [DecidableEq α] {s : Finset α} {t : Finset β} (e : s → t) (b₀ : β)
    (x : s) :
    extend e b₀ x = e x := by
  simp [extend]

private theorem extend_symm_extend [DecidableEq α] [DecidableEq β] {s : Finset α} {t : Finset β}
    (e : s ≃ t) (a₀ : α) (b₀ : β)
    {x : α} (hx : x ∈ s) : extend e.symm a₀ (extend e b₀ x) = x := by
  rw [show x = ((⟨x, hx⟩ : s) : α) from rfl, extend_coe, extend_coe, Equiv.symm_apply_apply]

private theorem image_extend [DecidableEq α] [DecidableEq β] {s : Finset α} {t : Finset β}
    (e : s ≃ t)
    (b₀ : β) : s.image (extend e b₀) = t := by
  ext b
  simp only [mem_image]
  refine ⟨?_, fun hb => ⟨_, (e.symm ⟨b, hb⟩).2, by rw [extend_coe]; simp⟩⟩
  rintro ⟨a, ha, rfl⟩
  exact (extend_coe e b₀ ⟨a, ha⟩).symm ▸ (e _).2

private theorem strictMonoOn_extend [DecidableEq α] [Preorder α] [Preorder β] {s : Finset α}
    {t : Finset β}
    (e : s ≃o t) (b₀ : β) : StrictMonoOn (extend e b₀) s := by
  intro a ha b hb hab
  rw [show a = ((⟨a, ha⟩ : s) : α) from rfl, show b = ((⟨b, hb⟩ : s) : α) from rfl,
    extend_coe, extend_coe]
  exact e.strictMono (Subtype.mk_lt_mk.2 hab)

open scoped Classical in
/-- Relabelling along an order isomorphism `s ≃o t` preserves block-count statistics of
noncrossing partitions. -/
private theorem sum_noncrossing_eq_of_orderIso [LinearOrder α] [LinearOrder β]
    {M : Type*} [AddCommMonoid M] (F : ℕ → M) {s : Finset α} {t : Finset β} (e : s ≃o t) :
    ∑ ρ ∈ univ.filter (fun ρ : Finpartition s => ρ.IsNoncrossing), F ρ.blockCount =
      ∑ ρ ∈ univ.filter (fun ρ : Finpartition t => ρ.IsNoncrossing), F ρ.blockCount := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨a₀, ha₀⟩
  · obtain rfl : t = ∅ := by
      rw [← card_eq_zero, ← Fintype.card_coe, ← Fintype.card_congr e.toEquiv]; simp
    rw [sum_noncrossing_empty, sum_noncrossing_empty]
  have b₀ : β := e ⟨a₀, ha₀⟩
  exact sum_noncrossing_eq_of_strictMonoOn F (image_extend e.toEquiv b₀)
    (image_extend e.symm.toEquiv a₀) (fun _ => extend_symm_extend e.toEquiv a₀ b₀)
    (fun _ => extend_symm_extend e.symm.toEquiv b₀ a₀) (strictMonoOn_extend e b₀)
    (strictMonoOn_extend e.symm a₀)

namespace Finpartition

open Finset Polynomial

/-- For a finite set `A` of a linear order with `q` elements, the sum of `x ^ |ρ|` over the
noncrossing partitions `ρ` of `A` equals the same sum over the noncrossing partitions of
`[q] = Finset.Icc 1 q`. -/
@[lognarayana "lem_nc_relabel_gen_poly"]
public theorem sum_noncrossing_X_pow_blockCount_eq_of_card_eq {α : Type*} [LinearOrder α]
    (R : Type*) [CommSemiring R] (A : Finset α) {q : ℕ} (hA : #A = q) :
    open scoped Classical in
    ∑ ρ ∈ univ.filter (fun ρ : Finpartition A => ρ.IsNoncrossing), (X : R[X]) ^ ρ.blockCount =
      ∑ ρ ∈ univ.filter (fun ρ : Finpartition (Icc 1 q) => ρ.IsNoncrossing),
        (X : R[X]) ^ ρ.blockCount :=
  sum_noncrossing_eq_of_orderIso _
    ((A.orderIsoOfFin hA).symm.trans ((Icc 1 q).orderIsoOfFin (by simp)))

end Finpartition

end

/-! ### Lower intervals of the noncrossing partition lattice -/

section

open Finset

variable {α : Type*} [LinearOrder α] {A : Finset α}

/-- A block of a refinement `σ` of `τ` that meets a block `B` of `τ` lies in `B`. -/
private lemma subset_of_le {σ τ : Finpartition A} (h : σ ≤ τ) {β B : Finset α}
    (hβ : β ∈ σ.parts) (hB : B ∈ τ.parts) {x : α} (hxβ : x ∈ β) (hxB : x ∈ B) : β ⊆ B := by
  obtain ⟨C, hC, hβC⟩ := h hβ
  obtain rfl : C = B := by
    by_contra hne
    exact disjoint_left.1 (τ.disjoint hC hB hne) (hβC hxβ) hxB
  exact hβC

/-- The restriction of a refinement `σ` of `τ` to a block `B` of `τ`. -/
private def restrictTo {σ τ : Finpartition A} (h : σ ≤ τ) {B : Finset α} (hB : B ∈ τ.parts) :
    Finpartition B :=
  σ.ofSubset (parts := σ.parts.filter (· ⊆ B)) (filter_subset _ _) <| by
    refine le_antisymm (Finset.sup_le fun β hβ => (mem_filter.1 hβ).2) fun x hx => ?_
    obtain ⟨β, hβ, hxβ⟩ := σ.exists_mem (τ.le hB hx)
    exact mem_sup.2 ⟨β, mem_filter.2 ⟨hβ, subset_of_le h hβ hB hxβ hx⟩, hxβ⟩

private lemma restrictTo_parts {σ τ : Finpartition A} (h : σ ≤ τ) {B : Finset α}
    (hB : B ∈ τ.parts) : (restrictTo h hB).parts = σ.parts.filter (· ⊆ B) := rfl

private lemma isNoncrossing_restrictTo {σ τ : Finpartition A} (hσ : σ.IsNoncrossing)
    (h : σ ≤ τ) {B : Finset α} (hB : B ∈ τ.parts) : (restrictTo h hB).IsNoncrossing :=
  fun β hβ β' hβ' => hσ β (mem_filter.1 hβ).1 β' (mem_filter.1 hβ').1

/-- Gluing partitions of the blocks of `τ` refines `τ`. -/
private lemma bind_le (τ : Finpartition A) (Q : ∀ B ∈ τ.parts, Finpartition B) :
    τ.bind Q ≤ τ := fun β hβ => by
  obtain ⟨B, hB, hβB⟩ := Finpartition.mem_bind.1 hβ
  exact ⟨B, hB, (Q B hB).le hβB⟩

/-- Gluing noncrossing partitions of the blocks of a noncrossing `τ` gives a noncrossing
partition. -/
private lemma isNoncrossing_bind {τ : Finpartition A} (hτ : τ.IsNoncrossing)
    {Q : ∀ B ∈ τ.parts, Finpartition B} (hQ : ∀ B hB, (Q B hB).IsNoncrossing) :
    (τ.bind Q).IsNoncrossing := by
  intro β hβ β' hβ' hne a ha c hc b hb d hd
  obtain ⟨B, hB, hβB⟩ := Finpartition.mem_bind.1 hβ
  obtain ⟨B', hB', hβB'⟩ := Finpartition.mem_bind.1 hβ'
  by_cases hBB : B = B'
  · subst hBB
    exact hQ B hB β hβB β' hβB' hne a ha c hc b hb d hd
  · have h1 := (Q B hB).le hβB
    have h2 := (Q B' hB').le hβB'
    exact hτ B hB B' hB' hBB a (h1 ha) c (h1 hc) b (h2 hb) d (h2 hd)

private lemma bind_restrictTo {σ τ : Finpartition A} (h : σ ≤ τ) :
    τ.bind (fun _ hB => restrictTo h hB) = σ := by
  ext β
  simp only [Finpartition.mem_bind, restrictTo_parts, mem_filter]
  refine ⟨fun ⟨_, _, hβ, _⟩ => hβ, fun hβ => ?_⟩
  obtain ⟨B, hB, hβB⟩ := h hβ
  exact ⟨B, hB, hβ, hβB⟩

private lemma restrictTo_bind (τ : Finpartition A) (Q : ∀ B ∈ τ.parts, Finpartition B)
    {B : Finset α} (hB : B ∈ τ.parts) : restrictTo (bind_le τ Q) hB = Q B hB := by
  ext β
  simp only [Finpartition.mem_bind, restrictTo_parts, mem_filter]
  refine ⟨fun ⟨⟨B', hB', hβ⟩, hβB⟩ => ?_, fun hβ => ⟨⟨B, hB, hβ⟩, (Q B hB).le hβ⟩⟩
  obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.2 ((Q B' hB').ne_bot hβ)
  obtain rfl : B' = B := by
    by_contra hne
    exact disjoint_left.1 (τ.disjoint hB' hB hne) ((Q B' hB').le hβ hx) (hβB hx)
  exact hβ

/-- Two refinements of `τ` compare as their restrictions to every block of `τ` do. -/
private lemma le_iff_forall_restrictTo_le {σ σ' τ : Finpartition A} (h : σ ≤ τ) (h' : σ' ≤ τ) :
    σ ≤ σ' ↔ ∀ B (hB : B ∈ τ.parts), restrictTo h hB ≤ restrictTo h' hB := by
  refine ⟨fun hle B hB β hβ => ?_, fun hle β hβ => ?_⟩
  · rw [restrictTo_parts, mem_filter] at hβ
    obtain ⟨γ, hγ, hβγ⟩ := hle hβ.1
    obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.2 (σ.ne_bot hβ.1)
    exact ⟨γ, mem_filter.2 ⟨hγ, subset_of_le h' hγ hB (hβγ hx) (hβ.2 hx)⟩, hβγ⟩
  · obtain ⟨B, hB, hβB⟩ := h hβ
    obtain ⟨γ, hγ, hβγ⟩ := hle B hB (mem_filter.2 ⟨hβ, hβB⟩)
    exact ⟨γ, (mem_filter.1 hγ).1, hβγ⟩

namespace Finpartition

open Finset

/-- For a noncrossing partition `τ` of a finite subset `A` of a linear order, the map
`σ ↦ ({β ∈ σ : β ⊆ B})_{B ∈ τ}` is an order isomorphism from the noncrossing partitions of `A`
refining `τ` onto the product over the blocks `B` of `τ` of the noncrossing partitions of `B`. -/
@[lognarayana "lem_nc_interval_product"]
public theorem exists_orderIso_noncrossing_le_pi {α : Type*} [LinearOrder α] {A : Finset α}
    (τ : Finpartition A) (hτ : τ.IsNoncrossing) :
    ∃ e : {σ : Finpartition A // σ.IsNoncrossing ∧ σ ≤ τ} ≃o
        ((B : τ.parts) → {ρ : Finpartition (B : Finset α) // ρ.IsNoncrossing}),
      ∀ (σ : {σ : Finpartition A // σ.IsNoncrossing ∧ σ ≤ τ}) (B : τ.parts),
        (e σ B : Finpartition (B : Finset α)).parts = σ.1.parts.filter (· ⊆ (B : Finset α)) :=
  ⟨{ toFun σ B := ⟨restrictTo σ.2.2 B.2, isNoncrossing_restrictTo σ.2.1 σ.2.2 B.2⟩
     invFun ρ := ⟨τ.bind fun B hB => (ρ ⟨B, hB⟩).1, isNoncrossing_bind hτ fun B hB => (ρ ⟨B, hB⟩).2,
       bind_le _ _⟩
     left_inv σ := Subtype.ext (bind_restrictTo σ.2.2)
     right_inv ρ := funext fun B => Subtype.ext (restrictTo_bind τ _ B.2)
     map_rel_iff' {σ σ'} := by
       simp only [Equiv.coe_fn_mk, Pi.le_def, Subtype.mk_le_mk, Subtype.forall]
       exact (le_iff_forall_restrictTo_le σ.2.2 σ'.2.2).symm },
   fun _ _ => rfl⟩

end Finpartition

end

/-! ### The block generating polynomial of a lower interval -/

section

open Finset Polynomial

/-- If `σ ≤ τ`, the number of blocks of `σ` is the sum over the blocks `B` of `τ` of the number
of blocks of `σ` contained in `B`. -/
private lemma card_parts_eq_sum_card_filter_subset {α : Type*} [DecidableEq α] {A : Finset α}
    {σ τ : Finpartition A} (h : σ ≤ τ) :
    #σ.parts = ∑ B ∈ τ.parts, #(σ.parts.filter (· ⊆ B)) := by
  have hU : σ.parts = τ.parts.biUnion (fun B => σ.parts.filter (· ⊆ B)) := by
    ext p
    simp only [mem_biUnion, mem_filter]
    exact ⟨fun hp => (h hp).imp fun B ⟨hB, hpB⟩ => ⟨hB, hp, hpB⟩, fun ⟨_, _, hp, _⟩ => hp⟩
  conv_lhs => rw [hU]
  refine card_biUnion fun B hB C hC hBC => disjoint_left.2 fun p hp hp' => ?_
  simp only [mem_filter] at hp hp'
  obtain ⟨x, hx⟩ := σ.nonempty_of_mem_parts hp.1
  exact hBC (τ.eq_of_mem_parts hB hC (hp.2 hx) (hp'.2 hx))

/-- Under an identification of the noncrossing partitions below `τ` with families of
noncrossing partitions of the blocks of `τ` that restricts each `σ` to the blocks, `X ^ |σ|`
is the product over the blocks of `X ^ |σ_B|`. -/
private lemma X_pow_blockCount_eq_prod {R : Type*} [CommSemiring R] {α : Type*} [LinearOrder α]
    {A : Finset α} {τ : Finpartition A}
    (e : {σ : Finpartition A // σ.IsNoncrossing ∧ σ ≤ τ} ≃o
        ((B : τ.parts) → {ρ : Finpartition (B : Finset α) // ρ.IsNoncrossing}))
    (he : ∀ σ (B : τ.parts),
      (e σ B : Finpartition (B : Finset α)).parts = σ.1.parts.filter (· ⊆ (B : Finset α)))
    (σ : {σ : Finpartition A // σ.IsNoncrossing ∧ σ ≤ τ}) :
    (X : R[X]) ^ σ.1.blockCount = ∏ B : τ.parts, (X : R[X]) ^ (e σ B).1.blockCount := by
  rw [Finpartition.blockCount, card_parts_eq_sum_card_filter_subset σ.2.2,
    ← sum_coe_sort τ.parts, ← prod_pow_eq_pow_sum]
  simp only [Finpartition.blockCount, he]

/-- The block generating polynomial of `NC(A)` for any finite `A ⊆ ℕ` is `N_{|A|}`. -/
private lemma sum_noncrossing_X_pow_blockCount (hKr : Finpartition.KrewerasBlockSizeCount)
    (A : Finset ℕ) :
    open scoped Classical in
    ∑ ρ : {ρ : Finpartition A // ρ.IsNoncrossing}, (X : ℝ[X]) ^ ρ.1.blockCount =
      narayanaPolynomial #A := by
  classical
  rw [← Finpartition.sum_noncrossing_X_pow_blockCount_eq_narayanaPolynomial hKr,
    ← Finpartition.sum_noncrossing_X_pow_blockCount_eq_of_card_eq ℝ A rfl,
    ← sum_subtype_eq_sum_filter, subtype_univ]

namespace Finpartition

open Finset Polynomial

/-- For a noncrossing partition `τ` of `[n] = Finset.Icc 1 n`, the sum of `x ^ |σ|` over the
noncrossing partitions `σ ≤ τ` equals `∏_{B ∈ τ} N_{|B|}(x)`. -/
@[lognarayana "lem_nc_interval_gen_poly"]
public theorem sum_noncrossing_le_X_pow_blockCount_eq_prod_narayanaPolynomial
    (hKr : KrewerasBlockSizeCount) {n : ℕ} (τ : Finpartition (Icc 1 n))
    (hτ : τ.IsNoncrossing) :
    open scoped Classical in
    ∑ σ ∈ univ.filter (fun σ : Finpartition (Icc 1 n) => σ.IsNoncrossing ∧ σ ≤ τ),
        (X : ℝ[X]) ^ σ.blockCount = ∏ B ∈ τ.parts, narayanaPolynomial B.card := by
  classical
  obtain ⟨e, he⟩ := Finpartition.exists_orderIso_noncrossing_le_pi τ hτ
  rw [← sum_subtype_eq_sum_filter, subtype_univ, ← prod_coe_sort τ.parts]
  simp only [X_pow_blockCount_eq_prod e he, ← sum_noncrossing_X_pow_blockCount hKr]
  rw [Fintype.prod_sum]
  exact e.toEquiv.sum_comp (fun g => ∏ B, (X : ℝ[X]) ^ (g B).1.blockCount)

end Finpartition

end

/-! ### The composition-sum form of the restricted sums -/

section

open Finset Polynomial

open Finset Polynomial

/-- **Composition-sum form**: for `a ≥ 1` and `λ ∈ ℝ`, the restricted noncrossing sum
`R^{(a),λ}_{n,k}` on `[n]` equals `n! / (k! (n - k + 1)!)` times the sum, over compositions
`q` of `n` into `k` parts each at least `a`, of `∏ᵢ N^{(λ)}_{qᵢ}`, given Kreweras' count. -/
@[lognarayana "lem_restricted_nc_composition_sum"]
public theorem restrictedNoncrossingDeformedNarayanaPoly_eq_sum_antidiagonalTuple
    (hKr : Finpartition.KrewerasBlockSizeCount) (n k a : ℕ) (ha : 1 ≤ a) (lam : ℝ) :
    restrictedNoncrossingDeformedNarayanaPoly ℝ lam (Icc 1 n) a k =
      C ((n.factorial : ℝ) / (k.factorial * (n - k + 1).factorial)) *
        ∑ q ∈ (Finset.Nat.antidiagonalTuple k n).filter (fun q => ∀ i, a ≤ q i),
          ∏ i, deformedNarayanaPolynomial ℝ lam (q i) := by
  classical
  have h := Finpartition.sum_noncrossing_prod_card_parts_eq hKr n k
    (fun q => if a ≤ q then deformedNarayanaPolynomial ℝ lam q else 0)
  simp only [prod_ite_zero, mem_univ, true_implies, ← sum_filter, filter_filter, and_assoc] at h
  rw [restrictedNoncrossingDeformedNarayanaPoly, h]
  congr 2
  exact filter_congr fun q _ => ⟨And.right, fun h => ⟨fun i => ha.trans (h i), h⟩⟩

end

/-! ### The restricted sum at `λ = 1` -/

section

open Polynomial Finset

/-- For all natural numbers `n, k, a`, the restricted noncrossing sum of deformed
Narayana polynomials at `λ = 1` is the restricted noncrossing refinement polynomial:
`R^{(a),1}_{n,k}(x) = R^{(a)}_{n,k}(x)`. -/
@[lognarayana "lem_restricted_nc_lambda_one"]
public theorem restrictedNoncrossingDeformedNarayanaPoly_one
    (hKr : Finpartition.KrewerasBlockSizeCount) {n k a : ℕ} :
    restrictedNoncrossingDeformedNarayanaPoly ℝ 1 (Icc 1 n) a k =
      restrictedNoncrossingRefinementPoly ℝ (Icc 1 n) a k := by
  classical
  rw [restrictedNoncrossingDeformedNarayanaPoly, restrictedNoncrossingRefinementPoly]
  refine Finset.sum_congr (by congr) fun τ hτ => ?_
  rw [Finpartition.sum_noncrossing_le_X_pow_blockCount_eq_prod_narayanaPolynomial hKr τ
    (Finset.mem_filter.1 hτ).2.1]
  exact Finset.prod_congr rfl fun B hB => deformedNarayanaPolynomial_one
    (Finset.card_pos.2 (τ.nonempty_of_mem_parts hB))

end

/-! ### The example `R^{(3)}_{12,3}` -/

section

open Polynomial Finset

/-- The composition formula at `λ = 1`: the restricted noncrossing refinement polynomial is the
Kreweras multiplicity times a sum, over compositions of `n` into `k` parts each at least `a`, of
products of Narayana polynomials. -/
private lemma restrictedNoncrossingRefinementPoly_eq_sum_prod_narayanaPolynomial
    (hKr : Finpartition.KrewerasBlockSizeCount)
    (n k a : ℕ) (ha : 1 ≤ a) :
    restrictedNoncrossingRefinementPoly ℝ (Icc 1 n) a k =
      C ((n.factorial : ℝ) / (k.factorial * (n - k + 1).factorial)) *
        ∑ q ∈ (Finset.Nat.antidiagonalTuple k n).filter (fun q => ∀ i, a ≤ q i),
          ∏ i, narayanaPolynomial (q i) := by
  rw [← restrictedNoncrossingDeformedNarayanaPoly_one hKr,
    restrictedNoncrossingDeformedNarayanaPoly_eq_sum_antidiagonalTuple hKr n k a ha]
  congr 1
  refine sum_congr rfl fun q hq => prod_congr rfl fun i _ => ?_
  exact deformedNarayanaPolynomial_one (ha.trans ((mem_filter.1 hq).2 i))

private lemma narayana_three : narayanaPolynomial 3 = X + 3 * X ^ 2 + X ^ 3 := by
  simp [narayanaPolynomial, Finset.sum_Icc_succ_top, Nat.choose]
  simp only [← map_ofNat C, ← C_mul]; norm_num

private lemma narayana_four : narayanaPolynomial 4 = X + 6 * X ^ 2 + 6 * X ^ 3 + X ^ 4 := by
  simp [narayanaPolynomial, Finset.sum_Icc_succ_top, Nat.choose]
  simp only [← map_ofNat C, ← C_mul]; norm_num

private lemma narayana_five :
    narayanaPolynomial 5 = X + 10 * X ^ 2 + 20 * X ^ 3 + 10 * X ^ 4 + X ^ 5 := by
  simp [narayanaPolynomial, Finset.sum_Icc_succ_top, Nat.choose]
  simp only [← map_ofNat C, ← C_mul]; norm_num

private lemma narayana_six : narayanaPolynomial 6 =
    X + 15 * X ^ 2 + 50 * X ^ 3 + 50 * X ^ 4 + 15 * X ^ 5 + X ^ 6 := by
  simp [narayanaPolynomial, Finset.sum_Icc_succ_top, Nat.choose]
  simp only [← map_ofNat C, ← C_mul]; norm_num

private lemma compositions_eq :
    (Finset.Nat.antidiagonalTuple 3 12).filter (fun q => ∀ i, 3 ≤ q i) =
      {![3, 3, 6], ![3, 6, 3], ![6, 3, 3], ![3, 4, 5], ![3, 5, 4], ![4, 3, 5],
        ![4, 5, 3], ![5, 3, 4], ![5, 4, 3], ![4, 4, 4]} := by
  decide

open Polynomial

/-- The restricted noncrossing refinement polynomial `R^{(3)}_{12,3}` equals
`x^3 (220 + 4290 x + 30558 x^2 + 105336 x^3 + 192720 x^4 + 192720 x^5 + 105336 x^6
+ 30558 x^7 + 4290 x^8 + 220 x^9)`. -/
@[lognarayana "lem_restricted_nc_example"]
public theorem restrictedNoncrossingRefinementPoly_icc_twelve_three_three
    (hKr : Finpartition.KrewerasBlockSizeCount) :
    restrictedNoncrossingRefinementPoly ℝ (Finset.Icc (1 : ℕ) 12) 3 3 =
      X ^ 3 * (220 + 4290 * X + 30558 * X ^ 2 + 105336 * X ^ 3 + 192720 * X ^ 4 +
        192720 * X ^ 5 + 105336 * X ^ 6 + 30558 * X ^ 7 + 4290 * X ^ 8 + 220 * X ^ 9) := by
  rw [restrictedNoncrossingRefinementPoly_eq_sum_prod_narayanaPolynomial hKr 12 3 3
    (by norm_num), compositions_eq,
    show (Nat.factorial 12 : ℝ) / (Nat.factorial 3 * Nat.factorial (12 - 3 + 1)) = 22 by
      norm_num [Nat.factorial], map_ofNat C]
  repeat rw [sum_insert (by decide)]
  simp only [sum_singleton, Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, narayana_three, narayana_four,
    narayana_five, narayana_six]
  ring

end

/-! ### Lattice points of a dilated simplex -/

section

open Finset

/-- The coordinate simplex on all coordinates is the standard simplex. -/
private theorem coordSimplex_univ_eq_stdSimplex (ι : Type*) [Fintype ι] [DecidableEq ι] :
    coordSimplex ℝ (Set.univ : Set ι) = stdSimplex ℝ ι := by
  rw [coordSimplex, Set.image_univ, ← convexHull_basis_eq_stdSimplex]
  congr 2
  funext i j
  simp [Pi.single_apply, eq_comm]

/-- The standard simplex dilated by `c ≥ 0` and translated by `a • 1` is the set of vectors
with all coordinates at least `a` and coordinate sum `a * card ι + c`. -/
private theorem mem_image_stdSimplex_iff {ι : Type*} [Fintype ι] [Nonempty ι] (a : ℝ)
    {c : ℝ} (hc : 0 ≤ c) (v : ι → ℝ) :
    v ∈ (fun y : ι → ℝ => a • (1 : ι → ℝ) + c • y) '' stdSimplex ℝ ι ↔
      (∀ i, a ≤ v i) ∧ ∑ i, v i = a * Fintype.card ι + c := by
  constructor
  · rintro ⟨y, ⟨hy0, hy1⟩, rfl⟩
    refine ⟨fun i => ?_, ?_⟩
    · simpa using mul_nonneg hc (hy0 i)
    · simp [Finset.sum_add_distrib, ← Finset.mul_sum, hy1, mul_comm]
  · rintro ⟨hva, hvs⟩
    rcases hc.eq_or_lt with rfl | hc
    · have hv : ∀ i, v i = a := by
        have hs : ∑ i, (v i - a) = 0 := by simp [Finset.sum_sub_distrib, hvs, mul_comm]
        intro i
        linarith [(Finset.sum_eq_zero_iff_of_nonneg fun i _ => sub_nonneg.mpr (hva i)).mp hs i
          (Finset.mem_univ i)]
      classical
      refine ⟨Pi.single (Classical.arbitrary ι) 1, single_mem_stdSimplex ℝ _, ?_⟩
      funext i
      simp [hv i]
    · refine ⟨fun i => (v i - a) / c, ⟨fun i => div_nonneg (sub_nonneg.mpr (hva i)) hc.le, ?_⟩,
        funext fun i => ?_⟩
      · rw [← Finset.sum_div, Finset.sum_sub_distrib, div_eq_one_iff_eq hc.ne', hvs]
        simp [mul_comm]
      · simp only [Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
        field_simp
        ring

open Finset

/-- For `k ≥ 1`, `a ∈ ℤ` and `c ∈ ℕ`, the lattice points of `a𝟙 + cΔ_{[k]}` are the integer
vectors `q` with `a ≤ q i` for all `i` and `∑ i, q i = a k + c`. -/
@[lognarayana "lem_simplex_dilate_lattice_points"]
public theorem latticePoints_image_smul_coordSimplex_univ {k : ℕ} (hk : 1 ≤ k) (a : ℤ)
    (c : ℕ) :
    Set.latticePoints ((fun y : Fin k → ℝ => (a : ℝ) • (1 : Fin k → ℝ) + (c : ℝ) • y) ''
        coordSimplex ℝ (Set.univ : Set (Fin k))) =
      (fun q : Fin k → ℤ => fun i => (q i : ℝ)) ''
        {q : Fin k → ℤ | (∀ i, a ≤ q i) ∧ ∑ i, q i = a * k + c} := by
  have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  ext v
  simp only [Set.latticePoints, coordSimplex_univ_eq_stdSimplex, Set.mem_ofPred_eq,
    mem_image_stdSimplex_iff _ c.cast_nonneg, Fintype.card_fin]
  constructor
  · rintro ⟨⟨hva, hvs⟩, hz⟩
    choose z hz using hz
    obtain rfl : v = fun i => (z i : ℝ) := funext fun i => (hz i).symm
    beta_reduce at hva hvs
    exact ⟨z, ⟨fun i => by exact_mod_cast hva i, by exact_mod_cast hvs⟩, rfl⟩
  · rintro ⟨q, ⟨hqa, hqs⟩, rfl⟩
    beta_reduce
    exact ⟨⟨fun i => by exact_mod_cast hqa i, by exact_mod_cast hqs⟩, fun i => ⟨q i, rfl⟩⟩

end

/-! ### The lattice points of `3𝟙 + 3Δ_{[3]}` -/

section

open Finset

/-- There are `10` integer vectors `q : Fin 3 → ℤ` with every `q i ≥ 3` and `∑ i, q i = 12`. -/
private lemma encard_shifted_compositions :
    {q : Fin 3 → ℤ | (∀ i, 3 ≤ q i) ∧ ∑ i, q i = 12}.encard = 10 := by
  have : {q : Fin 3 → ℤ | (∀ i, 3 ≤ q i) ∧ ∑ i, q i = 12} =
      ↑((Fintype.piFinset fun _ : Fin 3 => Icc (3 : ℤ) 9).filter fun q => ∑ i, q i = 12) := by
    ext q
    simp [Fin.forall_fin_succ, Fin.sum_univ_three]
    omega
  rw [this, Set.encard_coe_eq_coe_finsetCard]
  rfl

/-- The set `((3,3,3) + 3Δ_{[3]}) ∩ ℤ³` has exactly `10` elements. -/
@[lognarayana "lem_restricted_nc_example_lattice_count"]
public theorem encard_latticePoints_image_smul_coordSimplex_fin_three :
    (Set.latticePoints ((fun y : Fin 3 → ℝ => (3 : ℝ) • (1 : Fin 3 → ℝ) + (3 : ℝ) • y) ''
        coordSimplex ℝ (Set.univ : Set (Fin 3)))).encard = 10 := by
  have h := latticePoints_image_smul_coordSimplex_univ (k := 3) (by norm_num) 3 3
  push_cast at h
  rw [h, Set.InjOn.encard_image (f := fun q : Fin 3 → ℤ => fun i => (q i : ℝ))
    (Int.cast_injective.comp_left).injOn, encard_shifted_compositions]

end

/-! ### Dilated simplices are integral binary nestohedra -/

section

open Finset
open scoped Pointwise

/-- The coordinate simplex on a single coordinate is the corresponding basis vector. -/
private theorem coordSimplex_singleton {k : ℕ} (i : Fin k) :
    coordSimplex ℝ ({i} : Set (Fin k)) = {Pi.single i 1} := by
  simp [coordSimplex]

/-- The coordinate simplex on a nonempty set of coordinates is nonempty. -/
private theorem coordSimplex_nonempty {k : ℕ} {J : Set (Fin k)} (hJ : J.Nonempty) :
    (coordSimplex ℝ J).Nonempty :=
  (hJ.image _).mono (subset_convexHull ℝ _)

/-- A coordinate simplex is convex. -/
private theorem convex_coordSimplex {k : ℕ} (J : Set (Fin k)) : Convex ℝ (coordSimplex ℝ J) :=
  convex_convexHull ℝ _

/-- The Minkowski sum `∑ᵢ a Δ_{{i}}` is the point `a 𝟙`. -/
private theorem sum_smul_coordSimplex_singletons {k : ℕ} (a : ℝ) :
    ∑ J ∈ (univ : Finset (Fin k)).image (fun i => ({i} : Finset (Fin k))),
      a • coordSimplex ℝ (J : Set (Fin k)) = {a • (1 : Fin k → ℝ)} := by
  rw [sum_image (fun i _ j _ h => Finset.singleton_injective h)]
  simp only [coe_singleton, coordSimplex_singleton, Set.smul_set_singleton,
    Set.finsetSum_singleton]
  congr 1
  ext j
  simp [Finset.sum_apply, Pi.single_apply]

/-- The singletons of `Fin k` form a binary building set. -/
private theorem isBinaryBuildingSet_singletons (k : ℕ) :
    IsBinaryBuildingSet ((univ : Finset (Fin k)).image (fun i => ({i} : Finset (Fin k)))) where
  exists_eq_Icc J hJ := by
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hJ
    exact ⟨i, i, le_rfl, (Finset.Icc_self i).symm⟩
  singleton_mem i := Finset.mem_image.2 ⟨i, mem_univ _, rfl⟩
  disjoint_or_subset_or_subset J hJ K hK := by
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hJ
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hK
    by_cases h : i = j
    · subst h
      simp
    · left
      simpa using h

/-- The singletons of `Fin k` together with `univ` form a binary building set, for `k ≥ 1`. -/
private theorem isBinaryBuildingSet_insert_univ_singletons {k : ℕ} (hk : 1 ≤ k) :
    IsBinaryBuildingSet (insert univ
      ((univ : Finset (Fin k)).image (fun i => ({i} : Finset (Fin k))))) where
  exists_eq_Icc J hJ := by
    rcases Finset.mem_insert.1 hJ with rfl | hJ
    · obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
      exact ⟨0, Fin.last n, Fin.zero_le _, by ext x; simp [Fin.le_last]⟩
    · exact (isBinaryBuildingSet_singletons k).exists_eq_Icc J hJ
  singleton_mem i := Finset.mem_insert_of_mem ((isBinaryBuildingSet_singletons k).singleton_mem i)
  disjoint_or_subset_or_subset J hJ K hK := by
    rcases Finset.mem_insert.1 hJ with rfl | hJ
    · exact Or.inr (Or.inr (subset_univ _))
    rcases Finset.mem_insert.1 hK with rfl | hK
    · exact Or.inr (Or.inl (subset_univ _))
    exact (isBinaryBuildingSet_singletons k).disjoint_or_subset_or_subset J hJ K hK

/-- The nestohedron of the singletons and `univ`, with coefficient `a` on each singleton and `c`
added on `univ`, is the translate `a 𝟙 + c Δ` of the dilated standard simplex. The coefficient
on `univ` is `a + c` when `k = 1`, where `univ` is itself a singleton. -/
private theorem nestohedron_insert_univ_singletons {k : ℕ} (hk : 1 ≤ k) {a c : ℝ}
    (ha : 0 ≤ a) (hc : 0 ≤ c) :
    nestohedron ℝ (insert univ ((univ : Finset (Fin k)).image (fun i => ({i} : Finset (Fin k)))))
      (fun J => (if J ∈ (univ : Finset (Fin k)).image (fun i => ({i} : Finset (Fin k)))
        then a else 0) + if J = univ then c else 0) =
      {a • (1 : Fin k → ℝ)} + c • coordSimplex ℝ (Set.univ : Set (Fin k)) := by
  set S := (univ : Finset (Fin k)).image (fun i => ({i} : Finset (Fin k)))
  have hne : ∀ J ∈ insert univ S, (coordSimplex ℝ (J : Set (Fin k))).Nonempty := by
    intro J hJ
    refine coordSimplex_nonempty (coe_nonempty.2 ?_)
    rcases Finset.mem_insert.1 hJ with rfl | hJ
    · exact univ_nonempty_iff.2 ⟨⟨0, hk⟩⟩
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hJ
      exact singleton_nonempty i
  calc nestohedron ℝ (insert univ S) _
      = ∑ J ∈ insert univ S, ((if J ∈ S then a • coordSimplex ℝ (J : Set (Fin k)) else 0) +
          if J = univ then c • coordSimplex ℝ (J : Set (Fin k)) else 0) := by
        refine sum_congr rfl fun J hJ => ?_
        rw [(convex_coordSimplex _).add_smul (by split_ifs <;> simp [ha])
          (by split_ifs <;> simp [hc]), ite_smul, ite_smul, Set.zero_smul_set (hne J hJ)]
    _ = _ := by
        rw [sum_add_distrib, sum_ite_mem, inter_eq_right.2 (subset_insert _ _),
          sum_smul_coordSimplex_singletons, sum_ite_eq', if_pos (mem_insert_self _ _), coe_univ]

/-- For `a > 0` and `c ≥ 0`, the translate `a 𝟙 + c Δ` of the dilated standard simplex is a
binary nestohedron: for `c = 0` it is `∑ᵢ a Δ_{{i}}`, and for `c > 0` it is
`∑ᵢ a Δ_{{i}} + c Δ_{[k]}`. -/
private theorem isBinaryNestohedron_singleton_add_smul_coordSimplex_univ {k : ℕ} (hk : 1 ≤ k)
    {a c : ℝ} (ha : 0 < a) (hc : 0 ≤ c) :
    IsBinaryNestohedron ℝ
      ({a • (1 : Fin k → ℝ)} + c • coordSimplex ℝ (Set.univ : Set (Fin k))) := by
  rcases hc.eq_or_lt with rfl | hc
  · refine ⟨_, isBinaryBuildingSet_singletons k, fun _ => a, fun _ _ => ha, ?_⟩
    rw [nestohedron, sum_smul_coordSimplex_singletons,
      Set.zero_smul_set (coordSimplex_nonempty ⟨⟨0, hk⟩, Set.mem_univ _⟩), add_zero]
  · refine ⟨_, isBinaryBuildingSet_insert_univ_singletons hk, _, fun J hJ => ?_,
      (nestohedron_insert_univ_singletons hk ha.le hc.le).symm⟩
    rcases Finset.mem_insert.1 hJ with rfl | hJ
    · rw [if_pos rfl]
      split_ifs <;> positivity
    · rw [if_pos hJ]
      split_ifs <;> positivity

/-- The extreme points of `a 𝟙 + c Δ` are among the points `a 𝟙 + c eⱼ`. -/
private theorem extremePoints_image_coordSimplex_univ_subset {k : ℕ} (a c : ℝ) :
    ((fun y : Fin k → ℝ => a • (1 : Fin k → ℝ) + c • y) ''
        coordSimplex ℝ (Set.univ : Set (Fin k))).extremePoints ℝ ⊆
      Set.range fun j => a • (1 : Fin k → ℝ) + c • Pi.single j 1 := by
  let F : (Fin k → ℝ) →ᵃ[ℝ] (Fin k → ℝ) :=
    c • AffineMap.id ℝ (Fin k → ℝ) + AffineMap.const ℝ (Fin k → ℝ) (a • 1)
  have hF : (fun y : Fin k → ℝ => a • (1 : Fin k → ℝ) + c • y) = F := by
    funext y
    simp [F, add_comm]
  rw [hF, coordSimplex, AffineMap.image_convexHull]
  intro v hv
  obtain ⟨_, ⟨j, -, rfl⟩, rfl⟩ := extremePoints_convexHull_subset hv
  exact ⟨j, by simp [F, add_comm]⟩

/-- For `k ≥ 1`, an integer `a ≥ 1` and `c ∈ ℕ`, the translated dilate `a𝟙 + cΔ_{[k]}` of the
standard simplex in `ℝ^k` is an integral binary nestohedron. -/
@[lognarayana "lem_simplex_dilate_nestohedron"]
public theorem isIntegralBinaryNestohedron_image_smul_coordSimplex_univ {k : ℕ} (hk : 1 ≤ k)
    {a : ℤ} (ha : 1 ≤ a) (c : ℕ) :
    IsIntegralBinaryNestohedron ℝ
      ((fun y : Fin k → ℝ => (a : ℝ) • (1 : Fin k → ℝ) + (c : ℝ) • y) ''
        coordSimplex ℝ (Set.univ : Set (Fin k))) := by
  refine ⟨?_, fun v hv => ⟨extremePoints_subset hv, ?_⟩⟩
  · simpa only [Set.singleton_add, ← Set.image_smul, Set.image_image] using
      isBinaryNestohedron_singleton_add_smul_coordSimplex_univ hk (a := a) (c := c)
        (by exact_mod_cast ha) c.cast_nonneg
  · obtain ⟨j, rfl⟩ := extremePoints_image_coordSimplex_univ_subset _ _ hv
    intro i
    refine ⟨a + c * if i = j then 1 else 0, ?_⟩
    rcases eq_or_ne i j with rfl | h <;> simp [*]

end

/-! ### Log-concavity of the deformed restricted sums -/

section

open Finset Polynomial

/-- Multiplying by a nonnegative constant preserves log-concavity. -/
private lemma isLogConcave_C_mul {f : ℝ[X]} {c : ℝ} (hc : 0 ≤ c) (hf : f.IsLogConcave) :
    (C c * f).IsLogConcave := by
  refine ⟨fun j => ?_, fun j => ?_⟩ <;> simp only [coeff_C_mul]
  · exact mul_nonneg hc (hf.1 j)
  · nlinarith [mul_le_mul_of_nonneg_left (hf.2 j) (mul_nonneg hc hc)]

/-- The lattice points of `a𝟙 + (n - ak)Δ_{[k]}`, as the image of the compositions of `n`
into `k` parts each at least `a`. -/
private lemma latticePoints_eq_image {n k a : ℕ} (hk : 1 ≤ k)
    (hnak : a * k ≤ n) :
    Set.latticePoints ((fun y : Fin k → ℝ =>
        ((a : ℤ) : ℝ) • (1 : Fin k → ℝ) + ((n - a * k : ℕ) : ℝ) • y) ''
        coordSimplex ℝ (Set.univ : Set (Fin k))) =
      (fun q : Fin k → ℕ => fun i => (q i : ℝ)) ''
        ↑((Finset.Nat.antidiagonalTuple k n).filter (fun q => ∀ i, a ≤ q i)) := by
  rw [latticePoints_image_smul_coordSimplex_univ hk]
  ext x
  simp only [Set.mem_image, Set.mem_ofPred_eq, coe_filter, Finset.Nat.mem_antidiagonalTuple]
  constructor
  · rintro ⟨q, ⟨hqa, hqs⟩, rfl⟩
    have hq0 : ∀ i, 0 ≤ q i := fun i => (Int.natCast_nonneg a).trans (hqa i)
    refine ⟨fun i => (q i).toNat, ⟨?_, fun i => (Int.le_toNat (hq0 i)).2 (hqa i)⟩,
      funext fun i => by exact_mod_cast Int.toNat_of_nonneg (hq0 i)⟩
    zify [hnak] at hqs ⊢
    simp only [Int.toNat_of_nonneg (hq0 _)]
    omega
  · rintro ⟨q, ⟨hqs, hqa⟩, rfl⟩
    refine ⟨fun i => (q i : ℤ), ⟨fun i => Int.ofNat_le.2 (hqa i), ?_⟩, by simp⟩
    push_cast [hnak]
    rw [← Nat.cast_sum, hqs]
    ring

open Polynomial

namespace Polynomial

/-- For integers `k, a ≥ 1` and `n` with `a k ≤ n` and `0 ≤ λ ≤ 2`, the restricted noncrossing sum
`R^{(a),λ}_{n,k}(x)` of deformed Narayana polynomials is log-concave. -/
@[lognarayana "thm_restricted_nc_deformed_lc"]
public theorem isLogConcave_restrictedNoncrossingDeformedNarayanaPoly
    (hKr : Finpartition.KrewerasBlockSizeCount)
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
    {n k a : ℕ} (hk : 1 ≤ k) (ha : 1 ≤ a) (hnak : a * k ≤ n)
    {lam : ℝ} (hlam₀ : 0 ≤ lam) (hlam₂ : lam ≤ 2) :
    (restrictedNoncrossingDeformedNarayanaPoly ℝ lam (Finset.Icc 1 n) a k).IsLogConcave := by
  rw [restrictedNoncrossingDeformedNarayanaPoly_eq_sum_antidiagonalTuple hKr n k a ha lam]
  refine isLogConcave_C_mul (by positivity) ?_
  have hS := Polynomial.isLogConcave_finsum_latticePoints_prod_deformedNarayanaPolynomial
    hreal hfert hsub hder hmul hBH hsym hlam₀ hlam₂ hk
    (isIntegralBinaryNestohedron_image_smul_coordSimplex_univ hk (a := (a : ℤ))
      (by exact_mod_cast ha) (n - a * k))
  rw [latticePoints_eq_image hk hnak, finsum_mem_image, finsum_mem_coe_finset] at hS
  · simpa using hS
  · exact fun p _ q _ h => _root_.funext fun i => by exact_mod_cast congrFun h i

end Polynomial

end

/-! ### No internal zeros for the deformed restricted sums -/

section

open Finset Polynomial

/-- Multiplying by a positive constant preserves having no internal zeros. -/
private lemma hasNoInternalZeros_C_mul {f : ℝ[X]} {c : ℝ} (hc : 0 < c)
    (hf : HasNoInternalZeros f.natDegree f.coeff) :
    HasNoInternalZeros (C c * f).natDegree (C c * f).coeff := by
  rw [natDegree_C_mul hc.ne']
  intro i j k hij hjk hkd hi hk
  simp only [coeff_C_mul, mul_pos_iff_of_pos_left hc] at hi hk ⊢
  exact hf i j k hij hjk hkd hi hk


open Polynomial

namespace Polynomial

/-- For integers `k, a ≥ 1` and `n` with `a k ≤ n` and `0 ≤ λ ≤ 2`, the coefficient sequence of the
restricted noncrossing sum `R^{(a),λ}_{n,k}(x)` of deformed Narayana polynomials has no internal
zeros. -/
@[lognarayana "thm_restricted_nc_deformed_nz"]
public theorem hasNoInternalZeros_coeff_restrictedNoncrossingDeformedNarayanaPoly
    (hKr : Finpartition.KrewerasBlockSizeCount)
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
    {n k a : ℕ} (hk : 1 ≤ k) (ha : 1 ≤ a) (hnak : a * k ≤ n)
    {lam : ℝ} (hlam₀ : 0 ≤ lam) (hlam₂ : lam ≤ 2) :
    HasNoInternalZeros
      (restrictedNoncrossingDeformedNarayanaPoly ℝ lam (Finset.Icc 1 n) a k).natDegree
      (restrictedNoncrossingDeformedNarayanaPoly ℝ lam (Finset.Icc 1 n) a k).coeff := by
  rw [restrictedNoncrossingDeformedNarayanaPoly_eq_sum_antidiagonalTuple hKr n k a ha lam]
  refine hasNoInternalZeros_C_mul (by positivity) ?_
  have hP := isIntegralBinaryNestohedron_image_smul_coordSimplex_univ hk
    (a := (a : ℤ)) (by exact_mod_cast ha) (n - a * k)
  have hS :=
    Polynomial.hasNoInternalZeros_coeff_finsum_latticePoints_prod_deformedNarayanaPolynomial
    hreal hfert hsub hder hmul hBH hsym hlam₀ hlam₂ hk hP
  rw [latticePoints_eq_image hk hnak, finsum_mem_image, finsum_mem_coe_finset] at hS
  · simpa using hS
  · exact fun p _ q _ h => _root_.funext fun i => by exact_mod_cast congrFun h i

end Polynomial

end

/-! ### Log-concavity of the restricted refinement polynomials -/

section

open Polynomial



open Polynomial

namespace Polynomial

/-- For integers `k, a ≥ 1` and `n` with `a k ≤ n`, the restricted noncrossing refinement polynomial
`R^{(a)}_{n,k}(x)` is log-concave. -/
@[lognarayana "thm_restricted_nc_lc"]
public theorem isLogConcave_restrictedNoncrossingRefinementPoly
    (hKr : Finpartition.KrewerasBlockSizeCount)
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
    {n k a : ℕ} (hk : 1 ≤ k) (ha : 1 ≤ a) (hnak : a * k ≤ n) :
    (restrictedNoncrossingRefinementPoly ℝ (Finset.Icc 1 n) a k).IsLogConcave := by
  rw [← restrictedNoncrossingDeformedNarayanaPoly_one hKr]
  exact isLogConcave_restrictedNoncrossingDeformedNarayanaPoly hKr hreal hfert hsub hder
    hmul hBH hsym hk ha hnak zero_le_one one_le_two

end Polynomial

end

/-! ### No internal zeros for the restricted refinement polynomials -/

section

open Polynomial



open Polynomial

namespace Polynomial

/-- For integers `k, a ≥ 1` and `n` with `a k ≤ n`, the coefficient sequence of the restricted
noncrossing refinement polynomial `R^{(a)}_{n,k}(x)` has no internal zeros. -/
@[lognarayana "thm_restricted_nc_nz"]
public theorem hasNoInternalZeros_coeff_restrictedNoncrossingRefinementPoly
    (hKr : Finpartition.KrewerasBlockSizeCount)
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
    {n k a : ℕ} (hk : 1 ≤ k) (ha : 1 ≤ a) (hnak : a * k ≤ n) :
    HasNoInternalZeros
      (restrictedNoncrossingRefinementPoly ℝ (Finset.Icc 1 n) a k).natDegree
      (restrictedNoncrossingRefinementPoly ℝ (Finset.Icc 1 n) a k).coeff := by
  rw [← restrictedNoncrossingDeformedNarayanaPoly_one hKr]
  exact hasNoInternalZeros_coeff_restrictedNoncrossingDeformedNarayanaPoly hKr hreal hfert
    hsub hder hmul hBH hsym hk ha hnak zero_le_one one_le_two

end Polynomial

end
