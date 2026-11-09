/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib
public import LogNarayana.Attr
public import LogNarayana.StackSorting.FurtherDirections.Defs
public import LogNarayana.Nestohedron.Fertilitope.Defs
public import LogNarayana.StackSorting.Descents.Defs
public import LogNarayana.Polynomial.LogConcave.Defs
public import LogNarayana.StackSorting.Matchings.Defs
public import LogNarayana.Narayana.Polynomials.Defs
public import LogNarayana.Polynomial.RealStable.Defs
public import LogNarayana.StackSorting.FiberPolynomials.Defs
public import LogNarayana.StackSorting.StackSort.Defs
public import LogNarayana.StackSorting.Descents.Basic
public import LogNarayana.StackSorting.Matchings.Basic
public import LogNarayana.Narayana.Polynomials.Basic
public import LogNarayana.Polynomial.RealStable.Basic

/-!
# Further directions: stack-sorting fibers and a non-log-concave polytope

Fix `n ≥ 1` and `π ∈ S_n`. The peak polynomial of the stack-sorting fiber `s⁻¹(π)` is a
rescaling of the matching polynomial: `∑_{σ ∈ s⁻¹(π)} z^{peak(σ)} = 2^{n-1} Γ_π(z/4)`. If the
fiber top polynomial `𝒟_π(x, y)` is real-stable, then the fiber descent polynomial `D_π(x)` is
real-rooted; if `D_π` is real-rooted, then so is `Γ_π` (by the theorem of Brändén and Gal), and
`Γ_π` is then log-concave (by Newton's inequalities).

The polytope `P^nlc ⊆ ℝ^27`, the convex hull of the ten points `v_S` with `S ⊆ [5]`, `|S| = 2`,
has these points as its extreme points and as its only lattice points. The segment
`[v_{1,2}, v_{1,3}]` is an edge of `P^nlc` whose direction is not of the form `c (eᵢ - eⱼ)`, so
`P^nlc` is not a generalized permutohedron. Its Narayana sum is
`x^27 (1 + x)^2 (Ñ_22(x) + 9 (1 + x)^22)`, whose coefficients `10, 471, 22472` at `x^27, x^28,
x^29` violate log-concavity: `P^nlc` is an integral polytope in the positive orthant, in the
hyperplane `∑ q_i = 51`, whose Narayana sum is not log-concave.

## Main results

* `List.sum_stackFiber_X_pow_peakCount`: `∑_{σ ∈ s⁻¹(π)} z^{peak(σ)} = 2^{n-1} Γ_π(z/4)`.
* `List.splits_fiberMatchingPolynomial_of_splits_fiberDescentPolynomial`: if `D_π` is
  real-rooted, then `Γ_π` is real-rooted.
* `List.isLogConcave_fiberMatchingPolynomial_of_splits_fiberDescentPolynomial`: if `D_π` is
  real-rooted, then `Γ_π` is log-concave.
* `List.splits_fiberDescentPolynomial_of_isRealStable_fiberTopPolynomial`: if `𝒟_π` is
  real-stable, then `D_π` is real-rooted.
* `nlcVertex_sub_ne_smul_single_sub_single`: `v_{1,3} - v_{1,2}` is not a multiple of any
  `eᵢ - eⱼ`.
* `isPolytopeEdge_nlcPolytope_nlcVertex`: `[v_{1,2}, v_{1,3}]` is an edge of `P^nlc`.
* `not_isGeneralizedPermutohedron_nlcPolytope`: `P^nlc` is not a generalized permutohedron.
* `nlcVertex_mem_extremePoints_nlcPolytope`: every `v_S` is an extreme point of `P^nlc`.
* `latticePoints_nlcPolytope`: the lattice points of `P^nlc` are the ten points `v_S`.
* `finsum_latticePoints_nlcPolytope_prod_narayanaPolynomial`: the Narayana sum of `P^nlc`.
* `coeff_one_add_X_sq_mul_shiftedNarayanaPolynomial_add_low`: the low coefficients
  `10, 471, 22472`.
* `exists_isIntegralPolytope_not_isLogConcave_finsum_latticePoints_prod_narayanaPolynomial`:
  an integral polytope whose Narayana sum is not log-concave.

## Implementation notes

Real-rootedness is `Polynomial.Splits` over `ℝ`. The theorem of Brändén and Gal, Newton's
inequalities and Wagner's specialization theorem are cited results
(`Polynomial.GammaRealRootedIff`, `Polynomial.NewtonInequalities`,
`IsRealStableSpecializeClosed`), taken as hypotheses. The variables of `𝒟_π` are indexed by
`Bool × ℕ` (`x_a = X (true, a)`, `y_b = X (false, b)`), and `Γ_π(z/4)` is the composition
`Γ_π.comp (C (1/4) * X)`.

Subsets of `[5]` are `Finset (Fin 5)`, indexed from `0`, so the paper's `{1, 2}` and `{1, 3}`
are `{0, 1}` and `{0, 2}`. The lattice points of a bounded set are finitely many, so a Narayana
sum is a `finsum` over `Set.latticePoints`, and the index `q_i` of a Narayana polynomial is
recovered as `⌊q i⌋₊`.

## References

* [LogNarayana] *Log-Concavity in Narayana Transforms and Stack-Sorting Fibers*, Sections 2, 5
  and 9.
* [FPV] L. Ferroni, G. Panova, L. Venturello, Theorem 1.1.
* [StanleyLC] R. P. Stanley, Theorem 2.
* [Wagner] D. G. Wagner, Lemma 2.4.
-/

/-! ### Stack-sorting fibers -/

namespace List

section Fibers

open Polynomial

/-- Every polynomial `h(x) = ∑_{i ≤ ⌊n/2⌋} γ_i x^i (1 + x)^{n - 2i}` has degree at most `n`. -/
public theorem _root_.Polynomial.natDegree_sum_gammaBasis_le (n : ℕ) (γ : ℕ → ℝ) :
    (∑ i ∈ Finset.range (n / 2 + 1), C (γ i) * X ^ i * (1 + X) ^ (n - 2 * i)).natDegree ≤ n := by
  refine natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
  have hi : 2 * i ≤ n := by have := Finset.mem_range.1 hi; omega
  refine (natDegree_mul_le.trans (add_le_add natDegree_mul_le natDegree_pow_le)).trans ?_
  have h1 : (1 + X : ℝ[X]).natDegree ≤ 1 := by
    rw [add_comm]; exact (natDegree_X_add_C (1 : ℝ)).le
  have := Nat.mul_le_mul_left (n - 2 * i) h1
  rw [natDegree_C, natDegree_X_pow]
  omega

/-- Every polynomial `h(x) = ∑_{i ≤ ⌊n/2⌋} γ_i x^i (1 + x)^{n - 2i}` is symmetric with center of
symmetry `n/2`: `h_k = h_{n-k}` for `k ≤ n`. -/
public theorem _root_.Polynomial.coeff_sum_gammaBasis_symm (n : ℕ) (γ : ℕ → ℝ) {k : ℕ}
    (hk : k ≤ n) :
    (∑ i ∈ Finset.range (n / 2 + 1), C (γ i) * X ^ i * (1 + X) ^ (n - 2 * i)).coeff k =
      (∑ i ∈ Finset.range (n / 2 + 1), C (γ i) * X ^ i * (1 + X) ^ (n - 2 * i)).coeff
        (n - k) := by
  simp only [finsetSum_coeff, mul_assoc, coeff_C_mul, coeff_X_pow_mul', coeff_one_add_X_pow]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi : 2 * i ≤ n := by have := Finset.mem_range.1 hi; omega
  congr 1
  by_cases h1 : i ≤ k <;> by_cases h2 : i ≤ n - k <;> simp only [h1, h2, if_true, if_false]
  · exact_mod_cast Nat.choose_symm_of_eq_add (by omega)
  · exact_mod_cast Nat.choose_eq_zero_of_lt (by omega)
  · exact_mod_cast (Nat.choose_eq_zero_of_lt (by omega)).symm

/-- The cited theorem of Brändén and Gal ([FPV, Theorem 1.1]), applied to
`h(x) = ∑_{i ≤ ⌊n/2⌋} γ_i x^i (1 + x)^{n - 2i}`: this `h` is symmetric with center of symmetry
`n/2` (`Polynomial.natDegree_sum_gammaBasis_le`, `Polynomial.coeff_sum_gammaBasis_symm`), so
`γ_h(x) = ∑ γ_i x^i` has only nonpositive real zeros if and only if `h(x)` does. -/
public theorem _root_.Polynomial.GammaRealRootedIff.iff_of_gammaBasis
    (hBG : Polynomial.GammaRealRootedIff) (n : ℕ) (γ : ℕ → ℝ) :
    let g : ℝ[X] := ∑ i ∈ Finset.range (n / 2 + 1), C (γ i) * X ^ i
    let h : ℝ[X] := ∑ i ∈ Finset.range (n / 2 + 1), C (γ i) * X ^ i * (1 + X) ^ (n - 2 * i)
    (g.Splits ∧ ∀ r ∈ g.roots, r ≤ 0) ↔ (h.Splits ∧ ∀ r ∈ h.roots, r ≤ 0) :=
  hBG n _ (natDegree_sum_gammaBasis_le n γ) (fun _ hk => coeff_sum_gammaBasis_symm n γ hk) γ rfl

/-- A matching of `π` has at most `(π.length - 1) / 2` arcs. -/
private lemma two_mul_card_le_of_mem_fiberMatchings {π : List ℕ} {M : Finset (ℕ × ℕ)}
    (hM : M ∈ π.fiberMatchings) : 2 * M.card ≤ π.length - 1 := by
  have := hM.1.card_unmatchedVertices_add_two_mul_card
  omega

/-- The termwise identity `z^k 2^(N-2k) = 2^N (z/4)^k` for `2k ≤ N`. -/
private lemma X_pow_mul_two_pow_sub {K : Type*} [Field K] [NeZero (2 : K)] {k N : ℕ}
    (h : 2 * k ≤ N) :
    (X : K[X]) ^ k * 2 ^ (N - 2 * k) = 2 ^ N * (C (1 / 4 : K) * X) ^ k := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
  have h4 : (2 : K[X]) ^ 2 * C (1 / 4 : K) = 1 := by
    rw [← C_ofNat, ← C_pow, ← C_mul, ← C_1, show (1 / 4 : K) = (2 ^ 2)⁻¹ by norm_num,
      mul_inv_cancel₀ (pow_ne_zero _ two_ne_zero)]
  calc (X : K[X]) ^ k * 2 ^ (2 * k + m - 2 * k)
        = (2 ^ 2 * C (1 / 4 : K)) ^ k * X ^ k * 2 ^ m := by
        rw [h4, one_pow, one_mul, Nat.add_sub_cancel_left, mul_comm]
    _ = _ := by rw [pow_add, pow_mul]; ring

/-- For `n ≥ 1` and `π ∈ S_n`, `∑_{σ ∈ s⁻¹(π)} z^{peak(σ)} = 2^{n-1} Γ_π(z/4)` in `ℝ[z]`. -/
@[lognarayana "lem_fiber_peak_gamma"]
public theorem sum_stackFiber_X_pow_peakCount {n : ℕ} (hn : 1 ≤ n) {π : List ℕ}
    (hπ : π ∈ permWords n) :
    ∑ σ ∈ stackFiber π, (X : ℝ[X]) ^ σ.peakCount =
      2 ^ (n - 1) * (π.fiberMatchingPolynomial ℝ).comp (C (1 / 4 : ℝ) * X) := by
  have hfin := List.fiberMatchings_finite π
  have h := congrArg (MvPolynomial.eval fun _ => (1 : ℝ[X]))
    (List.fiberPeakPolynomial_eq_finsum_fiberMatchings ℝ[X] hn hπ X)
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin] at h
  simp only [List.fiberPeakPolynomial, map_sum, map_mul, map_add, map_pow, MvPolynomial.eval_C,
    MvPolynomial.eval_X, one_pow, mul_one, one_add_one_eq_two] at h
  rw [h, List.fiberMatchingPolynomial, finsum_mem_eq_finite_toFinset_sum _ hfin,
    Polynomial.sum_comp, Finset.mul_sum]
  refine Finset.sum_congr rfl fun M hM => ?_
  rw [pow_comp, X_comp, X_pow_mul_two_pow_sub
    (hπ.2.1 ▸ two_mul_card_le_of_mem_fiberMatchings (hfin.mem_toFinset.mp hM))]

/-- A sum over a finite set of finsets, of a function of the cardinality only, regrouped by
cardinality: `∑_{M ∈ S} f |M| = ∑_{j < m+1} #{M ∈ S : |M| = j} • f j` when every `|M| ≤ m`. -/
private lemma sum_card_eq_sum_range {β M : Type*} [AddCommMonoid M] (S : Finset (Finset β))
    (m : ℕ) (hS : ∀ s ∈ S, s.card ≤ m) (f : ℕ → M) :
    ∑ s ∈ S, f s.card = ∑ j ∈ Finset.range (m + 1), (S.filter (·.card = j)).card • f j := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := Finset.card) (t := Finset.range (m + 1))
    (fun s hs => Finset.mem_range.mpr (Nat.lt_succ_of_le (hS s hs)))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_congr rfl (fun s hs => by rw [(Finset.mem_filter.mp hs).2]),
    Finset.sum_const]

/-- For `π ∈ 𝔖_n`, a sum over the matchings of `π` of a function of the number of arcs, regrouped
by the number of arcs `j ≤ ⌊(n - 1)/2⌋`, with `γ_j` the number of matchings with `j` arcs. -/
private lemma finsum_fiberMatchings_eq_sum_range {n : ℕ} {π : List ℕ} (hπ : π ∈ permWords n)
    (f : ℕ → ℝ[X]) :
    ∑ᶠ M ∈ π.fiberMatchings, f M.card =
      ∑ j ∈ Finset.range ((n - 1) / 2 + 1),
        C (((List.fiberMatchings_finite π).toFinset.filter (·.card = j)).card : ℝ) * f j := by
  rw [finsum_mem_eq_finite_toFinset_sum _ (List.fiberMatchings_finite π),
    sum_card_eq_sum_range _ ((n - 1) / 2) (fun M hM => ?_) f]
  · simp [nsmul_eq_mul]
  · have :=
      ((List.fiberMatchings_finite π).mem_toFinset.mp hM).1.card_unmatchedVertices_add_two_mul_card
    have := hπ.2.1
    omega

/-- Every real zero of `D_π` is nonpositive: `D_π(t) = ∑_{σ ∈ s⁻¹(π)} t^{des(σ)} > 0` for `t > 0`
when the fiber is nonempty, and `D_π = 0` has no roots otherwise. -/
private lemma roots_fiberDescentPolynomial_nonpos (π : List ℕ) :
    ∀ r ∈ (fiberDescentPolynomial ℝ π).roots, r ≤ 0 := by
  intro r hr
  by_contra! hpos
  obtain ⟨h0, hr⟩ := mem_roots'.mp hr
  obtain hemp | hne := (stackFiber π).eq_empty_or_nonempty
  · exact h0 (by rw [fiberDescentPolynomial, hemp, Finset.sum_empty])
  · rw [IsRoot, fiberDescentPolynomial, eval_finsetSum] at hr
    simp only [eval_pow, eval_X] at hr
    exact (Finset.sum_pos (fun σ _ => pow_pos hpos _) hne).ne' hr

/-- Let `n ≥ 1` and `π ∈ S_n`. If the fiber descent polynomial `D_π(x)` is real-rooted, then the
matching polynomial `Γ_π(z)` is real-rooted. -/
@[lognarayana "lem_fiber_real_rooted_gamma_real_rooted"]
public theorem splits_fiberMatchingPolynomial_of_splits_fiberDescentPolynomial
    (hBG : GammaRealRootedIff)
    {n : ℕ} (hn : 1 ≤ n) {π : List ℕ} (hπ : π ∈ permWords n)
    (hroot : (fiberDescentPolynomial ℝ π).Splits) :
    (fiberMatchingPolynomial ℝ π).Splits := by
  have hg := finsum_fiberMatchings_eq_sum_range hπ (X ^ ·)
  have hD := finsum_fiberMatchings_eq_sum_range hπ fun j => X ^ j * (1 + X) ^ (n - 1 - 2 * j)
  rw [← fiberMatchingPolynomial, ← fiberDescentPolynomial_eq_finsum_fiberMatchings ℝ hn hπ] at *
  have key := hBG.iff_of_gammaBasis (n - 1) fun j =>
    ((List.fiberMatchings_finite π).toFinset.filter (·.card = j)).card
  simp only [mul_assoc, ← hg, ← hD] at key
  exact (key.mpr ⟨hroot, roots_fiberDescentPolynomial_nonpos π⟩).1

/-- `Γ_π` has nonnegative coefficients, for any list `π`: it is a sum of monomials `z^{|M|}`. -/
private lemma coeff_fiberMatchingPolynomial_nonneg {R : Type*} [CommSemiring R] [PartialOrder R]
    [IsOrderedRing R] {α : Type*} [LT α] [DecidableRel (α := α) (· < ·)] (π : List α) (j : ℕ) :
    0 ≤ (List.fiberMatchingPolynomial R π).coeff j := by
  revert j
  refine finsum_mem_induction (fun g : R[X] => ∀ j, 0 ≤ g.coeff j) (fun j => by simp)
    (fun f g hf hg j => by rw [coeff_add]; exact add_nonneg (hf j) (hg j)) fun M _ j => ?_
  rw [coeff_X_pow]
  split_ifs <;> simp

/-- Let `n ≥ 1` and `π ∈ S_n`. If the fiber descent polynomial `D_π(x)` is real-rooted, then the
matching polynomial `Γ_π(z)` is log-concave. -/
@[lognarayana "lem_fiber_real_rooted_gamma_log_concave"]
public theorem isLogConcave_fiberMatchingPolynomial_of_splits_fiberDescentPolynomial
    (hBG : GammaRealRootedIff) (hNewton : NewtonInequalities)
    {n : ℕ} (hn : 1 ≤ n) {π : List ℕ} (hπ : π ∈ permWords n)
    (hroot : (fiberDescentPolynomial ℝ π).Splits) :
    (fiberMatchingPolynomial ℝ π).IsLogConcave :=
  hNewton _ (coeff_fiberMatchingPolynomial_nonneg π)
    (splits_fiberMatchingPolynomial_of_splits_fiberDescentPolynomial hBG hn hπ hroot)

end Fibers

section RealStable

open MvPolynomial

/-- Specializing finitely many variables of a real-stable polynomial to real values gives zero or
a real-stable polynomial, by iterating Wagner's one-variable specialization. -/
private lemma specialize_finset {σ : Type*} [DecidableEq σ]
    (hspec : IsRealStableSpecializeClosed σ) {f : MvPolynomial σ ℝ} (hf : f.IsRealStable)
    (a : σ → ℝ) (S : Finset σ) :
    aeval (fun j => if j ∈ S then C (a j) else X j) f = 0 ∨
      (aeval (fun j => if j ∈ S then C (a j) else X j) f).IsRealStable := by
  induction S using Finset.induction_on with
  | empty => right; simpa using hf
  | @insert i S hi ih =>
    have key : aeval (fun j => if j ∈ insert i S then C (a j) else X j) f =
        aeval (Function.update X i (C (a i)))
          (aeval (fun j => if j ∈ S then C (a j) else X j) f) := by
      simp only [aeval_eq_bind₁, bind₁_bind₁]
      congr 2
      funext j
      by_cases hj : j ∈ S
      · simp [hj, show j ≠ i by rintro rfl; exact hi hj]
      · by_cases hji : j = i
        · subst hji; simp [hj]
        · simp [hj, hji]
    rw [key]
    rcases ih with h0 | hs
    · left; rw [h0, map_zero]
    · exact hspec _ hs i (a i)

/-- Every element of the stack-sorting fiber has distinct entries. -/
private lemma nodup_of_mem_stackFiber {π σ : List ℕ} (h : σ ∈ stackFiber π) : σ.Nodup := by
  simp only [stackFiber, Finset.mem_filter, List.mem_toFinset, List.mem_permutations] at h
  exact h.1.nodup_iff.2 (List.nodup_range' ..)

/-- A nonempty fiber gives a nonzero fiber descent polynomial: its value at `1` is the size of
the fiber. -/
private lemma fiberDescentPolynomial_ne_zero {π : List ℕ} (hfib : (stackFiber π).Nonempty) :
    fiberDescentPolynomial ℝ π ≠ 0 := by
  intro h
  have := congrArg (Polynomial.eval 1) h
  simp only [fiberDescentPolynomial, Polynomial.eval_finsetSum, Polynomial.eval_pow,
    Polynomial.eval_X, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one, Polynomial.eval_zero,
    Nat.cast_eq_zero, Finset.card_eq_zero] at this
  exact hfib.ne_empty this

/-- Setting every `y`-variable to `1` and every `x`-variable to one variable turns the fiber top
polynomial into the fiber descent polynomial. -/
private lemma aeval_fiberTopPolynomial (π : List ℕ) :
    aeval (fun j : Bool × ℕ => if j.1 then (X () : MvPolynomial Unit ℝ) else 1)
      (fiberTopPolynomial ℝ π) =
      Polynomial.toMvPolynomial () (fiberDescentPolynomial ℝ π) := by
  simp only [fiberTopPolynomial, fiberDescentPolynomial, map_sum, map_mul, map_prod, aeval_X,
    map_pow, Polynomial.toMvPolynomial_X, if_true, Bool.false_eq_true, if_false,
    Finset.prod_const_one, mul_one, Finset.prod_const]
  refine Finset.sum_congr rfl fun σ hσ => ?_
  rw [card_descentTops (nodup_of_mem_stackFiber hσ)]

/-- The same substitution done in two steps: first `y_b = 1` for the `y`-variables `S` that
occur, then all `x`-variables identified. -/
private lemma rename_specialize_fiberTopPolynomial (π : List ℕ) :
    rename (fun _ => ())
      (aeval (fun j => if j ∈ (fiberTopPolynomial ℝ π).vars.filter (·.1 = false) then C 1
        else X j) (fiberTopPolynomial ℝ π)) =
      Polynomial.toMvPolynomial () (fiberDescentPolynomial ℝ π) := by
  rw [← aeval_fiberTopPolynomial, ← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  refine MvPolynomial.eval₂Hom_congr' rfl (fun j hj _ => ?_) rfl
  rcases j with ⟨_ | _, k⟩ <;> simp [hj]

/-- Let `π` be a list with `s⁻¹(π) ≠ ∅`. If the fiber top polynomial `𝒟_π(x, y)` is real-stable,
then the fiber descent polynomial `D_π(x)` is real-rooted. -/
@[lognarayana "lem_fiber_top_stable_descent_real_rooted"]
public theorem splits_fiberDescentPolynomial_of_isRealStable_fiberTopPolynomial
    (hspec : IsRealStableSpecializeClosed (Bool × ℕ))
    {π : List ℕ} (hfib : (stackFiber π).Nonempty)
    (hstable : (fiberTopPolynomial ℝ π).IsRealStable) :
    (fiberDescentPolynomial ℝ π).Splits := by
  have hD := fiberDescentPolynomial_ne_zero hfib
  have hg := rename_specialize_fiberTopPolynomial π
  rcases specialize_finset hspec hstable (fun _ => 1) _ with h0 | hs
  · exact (hD (Polynomial.toMvPolynomial_injective () (by rw [← hg, h0, map_zero, map_zero]))).elim
  · exact (Polynomial.isRealStable_toMvPolynomial_iff_splits () hD).1 (hg ▸ hs.rename _)

end RealStable

end List

/-! ### The edge `[v_{1,2}, v_{1,3}]` and generalized permutohedra -/

/-- A multiple of `e_i - e_j` vanishes outside `{i, j}`, so a vector with three nonzero
coordinates is not of that form. -/
private lemma ne_smul_single_sub_single {ι : Type*} [DecidableEq ι] {f : ι → ℝ} {a b d : ι}
    (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d) (ha : f a ≠ 0) (hb : f b ≠ 0) (hd : f d ≠ 0)
    (i j : ι) (c : ℝ) : f ≠ c • (Pi.single i 1 - Pi.single j 1) := by
  rintro rfl
  simp only [Pi.smul_apply, Pi.sub_apply, Pi.single_apply, smul_eq_mul] at ha hb hd
  split_ifs at ha hb hd <;> simp_all

/-- The direction `v_{1,3} - v_{1,2}` of the apex edge of the non-log-concave example polytope
is not a multiple of any `e_i - e_j` (indices `0`-based: `{0, 2}` and `{0, 1}`). -/
@[lognarayana "lem_nlc_polytope_apex_edge_direction"]
public theorem nlcVertex_sub_ne_smul_single_sub_single (i j : Fin 27) (c : ℝ) :
    (fun k => (nlcVertex {0, 2} k : ℝ)) - (fun k => (nlcVertex {0, 1} k : ℝ)) ≠
      c • (Pi.single i 1 - Pi.single j 1) :=
  ne_smul_single_sub_single (a := 0) (b := 1) (d := 2) (by decide) (by decide) (by decide)
    (by rw [Pi.sub_apply, sub_ne_zero, Ne, Int.cast_inj]; decide)
    (by rw [Pi.sub_apply, sub_ne_zero, Ne, Int.cast_inj]; decide)
    (by rw [Pi.sub_apply, sub_ne_zero, Ne, Int.cast_inj]; decide) i j c

section ApexEdge

open Set

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- If a linear functional equals `m` at `x` and `y`, then `{ℓ < m} ∪ [x, y]` is convex. -/
private lemma convex_lt_union_segment (ℓ : E →ₗ[ℝ] ℝ) {x y : E} {m : ℝ} (hx : ℓ x = m)
    (hy : ℓ y = m) : Convex ℝ ({q | ℓ q < m} ∪ segment ℝ x y) := by
  have hle : ∀ q ∈ {q | ℓ q < m} ∪ segment ℝ x y, ℓ q ≤ m := by
    rintro q (hq | ⟨a, b, -, -, hab, rfl⟩)
    · exact hq.le
    · simp [hx, hy, ← add_mul, hab]
  refine convex_iff_openSegment_subset.2 fun p hp q hq => ?_
  rintro _ ⟨a, b, ha, hb, hab, rfl⟩
  have hm : a * m + b * m = m := by rw [← add_mul, hab, one_mul]
  simp only [mem_union, mem_ofPred_eq, map_add, map_smul, smul_eq_mul]
  obtain (hp' | hp') := hp
  · exact Or.inl (by nlinarith [mul_lt_mul_of_pos_left (show ℓ p < m from hp') ha,
      mul_le_mul_of_nonneg_left (hle q hq) hb.le])
  obtain (hq' | hq') := hq
  · exact Or.inl (by nlinarith [mul_le_mul_of_nonneg_left (hle p (Or.inr hp')) ha.le,
      mul_lt_mul_of_pos_left (show ℓ q < m from hq') hb])
  · exact Or.inr ((convex_segment x y).openSegment_subset hp' hq' ⟨a, b, ha, hb, hab, rfl⟩)

/-- If a linear functional is `< m` on every point of `s` other than `x, y ∈ s`, where it equals
`m`, then `[x, y]` is the set of maximisers of `ℓ` on `convexHull ℝ s`. -/
private lemma segment_eq_maximizers_convexHull (ℓ : E →ₗ[ℝ] ℝ) {s : Set E} {x y : E} {m : ℝ}
    (hxs : x ∈ s) (hys : y ∈ s) (hx : ℓ x = m) (hy : ℓ y = m)
    (hs : ∀ v ∈ s, ℓ v < m ∨ v = x ∨ v = y) :
    segment ℝ x y = {q ∈ convexHull ℝ s | ∀ p ∈ convexHull ℝ s, ℓ p ≤ ℓ q} := by
  have hseg : ∀ q ∈ segment ℝ x y, ℓ q = m := by
    rintro _ ⟨a, b, -, -, hab, rfl⟩
    simp [hx, hy, ← add_mul, hab]
  have hsub : convexHull ℝ s ⊆ {q | ℓ q < m} ∪ segment ℝ x y := by
    refine convexHull_min (fun v hv => ?_) (convex_lt_union_segment ℓ hx hy)
    obtain (h | rfl | rfl) := hs v hv
    exacts [Or.inl h, Or.inr (left_mem_segment ℝ _ _), Or.inr (right_mem_segment ℝ _ _)]
  ext q
  refine ⟨fun hq => ⟨(convex_convexHull ℝ s).segment_subset (subset_convexHull ℝ s hxs)
    (subset_convexHull ℝ s hys) hq, fun p hp => ?_⟩, fun ⟨hq, hmax⟩ => ?_⟩
  · rw [hseg q hq]
    obtain (h | h) := hsub hp
    exacts [h.le, (hseg p h).le]
  · have := hx ▸ hmax x (subset_convexHull ℝ s hxs)
    exact (hsub hq).resolve_left this.not_gt

/-- The weight `ℓ(v_T) = 2 (1 + [0 ∈ T]) + (1 + [1 ∈ T]) + (1 + [2 ∈ T])`, as a natural number. -/
private def apexWeight (T : Finset (Fin 5)) : ℕ :=
  2 * (if (0 : Fin 5) ∈ T then 2 else 1) + (if (1 : Fin 5) ∈ T then 2 else 1) +
    (if (2 : Fin 5) ∈ T then 2 else 1)

private lemma apexWeight_cases : ∀ T : Finset (Fin 5), T.card = 2 →
    apexWeight T < 7 ∨ T = {0, 1} ∨ T = {0, 2} := by
  unfold apexWeight; decide

/-- The functional `ℓ q = 2 q₂₂ + q₂₃ + q₂₄`. -/
private noncomputable def apexFunctional : (Fin 27 → ℝ) →ₗ[ℝ] ℝ :=
  2 • LinearMap.proj (R := ℝ) (φ := fun _ : Fin 27 => ℝ) 22 +
    LinearMap.proj (R := ℝ) (φ := fun _ : Fin 27 => ℝ) 23 +
    LinearMap.proj (R := ℝ) (φ := fun _ : Fin 27 => ℝ) 24

private lemma apexFunctional_nlcVertex (T : Finset (Fin 5)) :
    apexFunctional (fun i => (nlcVertex T i : ℝ)) = (apexWeight T : ℝ) := by
  have h22 : (22 : Fin 27) = Fin.natAdd 22 (0 : Fin 5) := rfl
  have h23 : (23 : Fin 27) = Fin.natAdd 22 (1 : Fin 5) := rfl
  have h24 : (24 : Fin 27) = Fin.natAdd 22 (2 : Fin 5) := rfl
  simp only [apexFunctional, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.proj_apply,
    h22, h23, h24, nlcVertex, Fin.append_right, apexWeight]
  split_ifs <;> norm_num

/-- The segment `[v_{1,2}, v_{1,3}]` is an edge of `P^nlc` (indices `0`-based: `{0, 1}` and
`{0, 2}`). -/
@[lognarayana "lem_nlc_polytope_apex_edge"]
public theorem isPolytopeEdge_nlcPolytope_nlcVertex :
    IsPolytopeEdge nlcPolytope (fun i => (nlcVertex {0, 1} i : ℝ))
      (fun i => (nlcVertex {0, 2} i : ℝ)) := by
  refine ⟨fun h => (by decide : nlcVertex {0, 1} 0 ≠ nlcVertex {0, 2} 0)
    (by exact_mod_cast congrFun h 0), apexFunctional,
    segment_eq_maximizers_convexHull apexFunctional ⟨{0, 1}, by decide, rfl⟩
      ⟨{0, 2}, by decide, rfl⟩ (m := 7)
      (by rw [apexFunctional_nlcVertex, (by decide : apexWeight {0, 1} = 7)]; norm_num)
      (by rw [apexFunctional_nlcVertex, (by decide : apexWeight {0, 2} = 7)]; norm_num) ?_⟩
  rintro _ ⟨T, hT, rfl⟩
  obtain (h | rfl | rfl) := apexWeight_cases T hT
  exacts [Or.inl (by rw [apexFunctional_nlcVertex]; exact_mod_cast h), Or.inr (Or.inl rfl),
    Or.inr (Or.inr rfl)]

end ApexEdge

/-- The polytope `P^nlc ⊆ ℝ^27` is not a generalized permutohedron. -/
@[lognarayana "prop_nlc_polytope_not_gen_permutohedron"]
public theorem not_isGeneralizedPermutohedron_nlcPolytope :
    ¬ IsGeneralizedPermutohedron nlcPolytope := by
  intro h
  obtain ⟨i, j, -, c, hc⟩ := h.2 _ _ isPolytopeEdge_nlcPolytope_nlcVertex
  exact nlcVertex_sub_ne_smul_single_sub_single i j c hc

/-! ### Extreme points and lattice points of `P^nlc` -/

section LatticePoints

open Finset

private lemma nlcVertex_natAdd (S : Finset (Fin 5)) (i : Fin 5) :
    ((nlcVertex S (Fin.natAdd 22 i) : ℤ) : ℝ) = if i ∈ S then 2 else 1 := by
  simp only [nlcVertex, Fin.append_right]
  split_ifs <;> simp

/-- If a convex combination of values `≤ c` is `≥ c`, every value of positive weight is `c`. -/
private lemma eq_of_le_sum_mul {ι : Type*} {t : Finset ι} {w f : ι → ℝ} {c : ℝ}
    (hw0 : ∀ i ∈ t, 0 ≤ w i) (hw1 : ∑ i ∈ t, w i = 1) (hf : ∀ i ∈ t, f i ≤ c)
    (h : c ≤ ∑ i ∈ t, w i * f i) {i : ι} (hi : i ∈ t) (hwi : w i ≠ 0) : f i = c := by
  have hnn : ∀ i ∈ t, 0 ≤ w i * (c - f i) := fun i hi =>
    mul_nonneg (hw0 i hi) (sub_nonneg.2 (hf i hi))
  have h0 : ∑ i ∈ t, w i * (c - f i) = 0 := le_antisymm
    (by simpa [mul_sub, sum_sub_distrib, ← sum_mul, hw1] using h) (sum_nonneg hnn)
  have := (sum_eq_zero_iff_of_nonneg hnn).1 h0 i hi
  simpa [hwi, sub_eq_zero, eq_comm] using this

/-- A point of `s` at which a continuous linear functional is strictly maximised over `s` is an
exposed point of the convex hull of `s`. -/
private lemma mem_exposedPoints_convexHull {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] {s : Set E} {x : E} (hx : x ∈ s) (l : StrongDual ℝ E)
    (hl : ∀ y ∈ s, l y ≤ l x ∧ (l x ≤ l y → y = x)) :
    x ∈ (convexHull ℝ s).exposedPoints ℝ := by
  refine ⟨subset_convexHull ℝ s hx, l, fun y hy => ?_⟩
  obtain ⟨ι, t, w, z, hw0, hw1, hz, rfl⟩ := (_root_.convexHull_eq s).subset hy
  rw [centerMass_eq_of_sum_1 _ _ hw1]
  simp only [map_sum, map_smul, smul_eq_mul]
  refine ⟨?_, fun h => ?_⟩
  · calc ∑ i ∈ t, w i * l (z i) ≤ ∑ i ∈ t, w i * l x :=
          sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hl _ (hz i hi)).1 (hw0 i hi)
      _ = l x := by rw [← sum_mul, hw1, one_mul]
  · calc ∑ i ∈ t, w i • z i = ∑ i ∈ t, w i • x := sum_congr rfl fun i hi => by
          by_cases hwi : w i = 0
          · simp [hwi]
          · rw [(hl _ (hz i hi)).2
              (eq_of_le_sum_mul hw0 hw1 (fun i hi => (hl _ (hz i hi)).1) h hi hwi).ge]
      _ = x := by rw [← sum_smul, hw1, one_smul]

/-- Every vertex `v_S` (`S ⊆ [5]`, `|S| = 2`) of `P^nlc` is an extreme point of `P^nlc`. -/
@[lognarayana "lem_nlc_polytope_vertex_extreme"]
public theorem nlcVertex_mem_extremePoints_nlcPolytope (S : Finset (Fin 5)) (hS : S.card = 2) :
    (fun i => (nlcVertex S i : ℝ)) ∈ nlcPolytope.extremePoints ℝ := by
  refine exposedPoints_subset_extremePoints <| mem_exposedPoints_convexHull ⟨S, hS, rfl⟩
    (-∑ i ∈ univ.filter (· ∉ S), ContinuousLinearMap.proj (Fin.natAdd 22 i)) ?_
  rintro _ ⟨T, hT, rfl⟩
  simp only [neg_apply, _root_.sum_apply,
    ContinuousLinearMap.proj_apply, nlcVertex_natAdd, neg_le_neg_iff]
  have hle : ∑ i ∈ univ.filter (· ∉ S), (if i ∈ S then (2 : ℝ) else 1) ≤
      ∑ i ∈ univ.filter (· ∉ S), (if i ∈ T then (2 : ℝ) else 1) :=
    sum_le_sum fun i hi => by simp only [mem_filter] at hi; simp [hi.2]; split_ifs <;> norm_num
  refine ⟨hle, fun h => ?_⟩
  suffices T ⊆ S by rw [eq_of_subset_of_card_le this (by rw [hS, hT])]
  intro i hiT
  by_contra hiS
  refine (sum_lt_sum (fun j hj => ?_) ⟨i, by simpa using hiS, ?_⟩).not_ge h
  · simp only [mem_filter] at hj; simp [hj.2]; split_ifs <;> norm_num
  · simp [hiS, hiT]

private lemma sum_ite_two_one (S : Finset (Fin 5)) :
    ∑ j, (if j ∈ S then (2 : ℝ) else 1) = 5 + #S := by
  have : ∀ j, (if j ∈ S then (2 : ℝ) else 1) = 1 + if j ∈ S then 1 else 0 := by
    intro j; split_ifs <;> norm_num
  simp [this, sum_add_distrib]

/-- A convex combination of values `≥ c` is `≥ c`. -/
private lemma le_sum_mul {ι : Type*} {t : Finset ι} {w f : ι → ℝ} {c : ℝ}
    (hw0 : ∀ i ∈ t, 0 ≤ w i) (hw1 : ∑ i ∈ t, w i = 1) (hf : ∀ i ∈ t, c ≤ f i) :
    c ≤ ∑ i ∈ t, w i * f i := by
  calc c = ∑ i ∈ t, w i * c := by rw [← sum_mul, hw1, one_mul]
    _ ≤ _ := sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hf i hi) (hw0 i hi)

/-- A convex combination of values `≤ c` is `≤ c`. -/
private lemma sum_mul_le {ι : Type*} {t : Finset ι} {w f : ι → ℝ} {c : ℝ}
    (hw0 : ∀ i ∈ t, 0 ≤ w i) (hw1 : ∑ i ∈ t, w i = 1) (hf : ∀ i ∈ t, f i ≤ c) :
    ∑ i ∈ t, w i * f i ≤ c := by
  simpa using le_sum_mul (f := (- f ·)) (c := -c) hw0 hw1 (by simpa using hf)

/-- If a convex combination of values `≥ c` equals `c`, every value of positive weight is `c`. -/
private lemma eq_of_sum_mul_eq {ι : Type*} {t : Finset ι} {w f : ι → ℝ} {c : ℝ}
    (hw0 : ∀ i ∈ t, 0 ≤ w i) (hw1 : ∑ i ∈ t, w i = 1) (hf : ∀ i ∈ t, c ≤ f i)
    (h : ∑ i ∈ t, w i * f i = c) {i : ι} (hi : i ∈ t) (hwi : w i ≠ 0) : f i = c := by
  have h0 : ∑ i ∈ t, w i * (f i - c) = 0 := by
    simp [mul_sub, sum_sub_distrib, ← sum_mul, hw1, h]
  have := (sum_eq_zero_iff_of_nonneg fun i hi =>
    mul_nonneg (hw0 i hi) (sub_nonneg.2 (hf i hi))).1 h0 i hi
  simpa [hwi, sub_eq_zero] using this

/-- An integral convex combination of the patterns `1 + 1_{Sᵢ}` on `Fin 5`, `|Sᵢ| = 2`, puts all
its weight on a single `2`-element set. -/
private lemma exists_eq_of_sum_mul_ite_int {ι : Type*} {t : Finset ι} {w : ι → ℝ}
    {S : ι → Finset (Fin 5)} (hw0 : ∀ i ∈ t, 0 ≤ w i) (hw1 : ∑ i ∈ t, w i = 1)
    (hS : ∀ i ∈ t, #(S i) = 2)
    (hint : ∀ j, ∃ n : ℤ, (n : ℝ) = ∑ i ∈ t, w i * if j ∈ S i then 2 else 1) :
    ∃ T : Finset (Fin 5), #T = 2 ∧ ∀ i ∈ t, w i ≠ 0 → S i = T := by
  classical
  obtain ⟨a, ha⟩ : ∃ a : Fin 5 → ℝ, ∀ j, a j = ∑ i ∈ t, w i * if j ∈ S i then 2 else 1 :=
    ⟨_, fun _ => rfl⟩
  have h12 : ∀ j, ∀ i ∈ t,
      (1 : ℝ) ≤ (if j ∈ S i then 2 else 1) ∧ (if j ∈ S i then 2 else 1) ≤ (2 : ℝ) :=
    fun j i _ => by split_ifs <;> norm_num
  have ha12 : ∀ j, a j = 1 ∨ a j = 2 := by
    intro j
    obtain ⟨n, hn⟩ := hint j
    have h1 : (1 : ℝ) ≤ n := hn ▸ le_sum_mul hw0 hw1 fun i hi => (h12 j i hi).1
    have h2 : (n : ℝ) ≤ 2 := hn ▸ sum_mul_le hw0 hw1 fun i hi => (h12 j i hi).2
    have : n = 1 ∨ n = 2 := by
      have : (1 : ℤ) ≤ n := by exact_mod_cast h1
      have : n ≤ (2 : ℤ) := by exact_mod_cast h2
      omega
    rw [ha j, ← hn]
    rcases this with rfl | rfl <;> simp
  let T := univ.filter fun j => a j = 2
  have haT : ∀ j, a j = if j ∈ T then 2 else 1 := fun j => by
    rcases ha12 j with h | h <;> simp [T, h]
  have hcard : #T = 2 := by
    have hsum : ∑ j, a j = 7 := by
      simp only [ha]
      rw [sum_comm]
      calc _ = ∑ i ∈ t, w i * 7 := sum_congr rfl fun i hi => by
            rw [← mul_sum, sum_ite_two_one, hS i hi]; norm_num
        _ = 7 := by rw [← sum_mul, hw1, one_mul]
    simp only [haT, sum_ite_two_one] at hsum
    exact_mod_cast (by linarith : (#T : ℝ) = 2)
  refine ⟨T, hcard, fun i hi hwi =>
    eq_of_subset_of_card_le (fun j hj => ?_) (by rw [hS i hi, hcard])⟩
  by_contra hjT
  have := eq_of_sum_mul_eq hw0 hw1 (fun i hi => (h12 j i hi).1)
    (by rw [← ha j, haT j, if_neg hjT]) hi hwi
  norm_num [hj] at this

/-- The lattice points of `P^nlc` are exactly its ten vertices `v_S`, `S ⊆ [5]`, `|S| = 2`. -/
@[lognarayana "lem_nlc_polytope_lattice_points"]
public theorem latticePoints_nlcPolytope :
    nlcPolytope.latticePoints =
      (fun S : Finset (Fin 5) => fun i => (nlcVertex S i : ℝ)) '' {S | S.card = 2} := by
  ext q
  constructor
  · rintro ⟨hq, hint⟩
    obtain ⟨ι, t, w, z, hw0, hw1, hz, rfl⟩ := (_root_.convexHull_eq _).subset hq
    simp only [Set.mem_image, Set.mem_ofPred_eq] at hz
    choose! S hS hzS using hz
    rw [centerMass_eq_of_sum_1 _ _ hw1] at hint ⊢
    have hcoord : ∀ j, (∑ i ∈ t, w i • z i) (Fin.natAdd 22 j) =
        ∑ i ∈ t, w i * if j ∈ S i then 2 else 1 := fun j => by
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      exact sum_congr rfl fun i hi => by rw [← hzS i hi, ← nlcVertex_natAdd]
    obtain ⟨T, hT, hST⟩ := exists_eq_of_sum_mul_ite_int hw0 hw1 hS
      fun j => by simpa [hcoord] using hint (Fin.natAdd 22 j)
    refine ⟨T, hT, ?_⟩
    calc _ = ∑ i ∈ t, w i • (fun j => (nlcVertex T j : ℝ)) := by rw [← sum_smul, hw1, one_smul]
      _ = _ := sum_congr rfl fun i hi => by
        by_cases hwi : w i = 0
        · simp [hwi]
        · rw [← hzS i hi, hST i hi hwi]
  · rintro ⟨S, hS, rfl⟩
    exact ⟨subset_convexHull ℝ _ ⟨S, hS, rfl⟩, fun i => ⟨_, rfl⟩⟩

end LatticePoints

/-! ### The Narayana sum of `P^nlc` -/

section NarayanaSum

open Polynomial

private lemma narayanaPolynomial_one : narayanaPolynomial 1 = X := by
  rw [narayanaPolynomial_succ_eq_X_mul, shiftedNarayanaPolynomial_zero, mul_one]

private lemma narayanaPolynomial_two : narayanaPolynomial 2 = X * (1 + X) := by
  rw [narayanaPolynomial_succ_eq_X_mul, shiftedNarayanaPolynomial_one]

/-- `v_S` records `S` in its last five coordinates, so distinct sets give distinct vertices. -/
private lemma nlcVertex_injective : Function.Injective nlcVertex := by
  intro S T h
  ext i
  have := congrFun h (Fin.natAdd 22 i)
  simp only [nlcVertex, Fin.append_right] at this
  by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;> simp_all

private lemma nlcVertex_cast_injective :
    Function.Injective fun S : Finset (Fin 5) => fun i => (nlcVertex S i : ℝ) :=
  (Int.cast_injective (α := ℝ)).comp_left.comp nlcVertex_injective

/-- The Narayana product at the vertex `v_S`: the last five coordinates give `x^5 (1 + x)^2`,
and the first twenty-two give `x^22 Ñ_22` for `S = {0, 1}` and `(x (1 + x))^22` otherwise. -/
private lemma prod_narayanaPolynomial_nlcVertex (S : Finset (Fin 5)) (hS : S.card = 2) :
    ∏ i : Fin 27, narayanaPolynomial (nlcVertex S i).toNat =
      if S = {0, 1} then X ^ 27 * (1 + X) ^ 2 * shiftedNarayanaPolynomial 22
      else X ^ 27 * (1 + X) ^ 2 * (1 + X) ^ 22 := by
  refine (Fin.prod_univ_add (a := 22) (b := 5) _).trans ?_
  simp only [nlcVertex, Fin.append_left, Fin.append_right, apply_ite Int.toNat,
    apply_ite narayanaPolynomial, Finset.prod_ite, Finset.filter_not, Finset.prod_const,
    Finset.filter_mem_eq_inter, Finset.univ_inter, hS,
    Finset.card_sdiff_of_subset S.subset_univ]
  split_ifs
  · simp [Fin.prod_univ_succ, narayanaPolynomial_succ_eq_X_mul 22, narayanaPolynomial_one,
      narayanaPolynomial_two]
    ring
  · simp [narayanaPolynomial_one, narayanaPolynomial_two]
    ring

/-- `∑_{q ∈ P^nlc ∩ ℤ^27} ∏_{i=1}^{27} N_{q_i}(x) = x^27 (1 + x)^2 (Ñ_22(x) + 9 (1 + x)^22)`. -/
@[lognarayana "lem_nlc_polytope_narayana_sum"]
public theorem finsum_latticePoints_nlcPolytope_prod_narayanaPolynomial :
    ∑ᶠ q ∈ nlcPolytope.latticePoints, ∏ i : Fin 27, narayanaPolynomial ⌊q i⌋₊ =
      X ^ 27 * (1 + X) ^ 2 * (shiftedNarayanaPolynomial 22 + 9 * (1 + X) ^ 22) := by
  rw [latticePoints_nlcPolytope, finsum_mem_image nlcVertex_cast_injective.injOn,
    ← Finset.coe_filter_univ, finsum_mem_coe_finset]
  simp only [← Int.floor_toNat, Int.floor_intCast]
  rw [Finset.sum_congr rfl fun S hS =>
      prod_narayanaPolynomial_nlcVertex S (Finset.mem_filter.mp hS).2,
    Finset.sum_ite, Finset.sum_const, Finset.sum_const, Finset.filter_filter,
    Finset.filter_filter,
    show (Finset.univ.filter fun S : Finset (Fin 5) => S.card = 2 ∧ S = {0, 1}).card = 1 by
      decide,
    show (Finset.univ.filter fun S : Finset (Fin 5) => S.card = 2 ∧ ¬S = {0, 1}).card = 9 by
      decide]
  simp only [one_smul, nsmul_eq_mul]
  push_cast
  ring

/-- The coefficient of `X ^ k` in `Ñ_m`, for `k ≤ m`. -/
private lemma coeff_shiftedNarayanaPolynomial {m k : ℕ} (hk : k ≤ m) :
    (shiftedNarayanaPolynomial m).coeff k =
      ((m + 1 : ℕ) : ℝ)⁻¹ * ((m + 1).choose (k + 1) : ℝ) * ((m + 1).choose k : ℝ) := by
  simp_rw [shiftedNarayanaPolynomial, finsetSum_coeff, coeff_C_mul_X_pow, Finset.sum_ite_eq]
  simp [Nat.lt_succ_iff.mpr hk]

/-- The three lowest coefficients of `(1 + X) ^ 2 * p`, in terms of those of `p`. -/
private lemma coeff_one_add_X_sq_mul {R : Type*} [CommSemiring R] (p : R[X]) :
    (((1 + X) ^ 2 * p).coeff 0, ((1 + X) ^ 2 * p).coeff 1, ((1 + X) ^ 2 * p).coeff 2) =
      (p.coeff 0, 2 * p.coeff 0 + p.coeff 1, p.coeff 0 + 2 * p.coeff 1 + p.coeff 2) := by
  rw [show (1 + X : R[X]) ^ 2 = 1 + C 2 * X + X ^ 2 by rw [C_ofNat]; ring]
  simp [add_mul, mul_assoc, coeff_X_mul, coeff_X_pow_mul', coeff_C_mul]
  constructor <;> ring

/-- For `g(x) = (1 + x)^2 (Ñ_22(x) + 9 (1 + x)^22)`,
`([x^0] g, [x^1] g, [x^2] g) = (10, 471, 22472)`. -/
@[lognarayana "lem_nlc_polytope_low_coeffs"]
public theorem coeff_one_add_X_sq_mul_shiftedNarayanaPolynomial_add_low :
    let g : ℝ[X] := (1 + X) ^ 2 * (shiftedNarayanaPolynomial 22 + 9 * (1 + X) ^ 22)
    (g.coeff 0, g.coeff 1, g.coeff 2) = ((10 : ℝ), (471 : ℝ), (22472 : ℝ)) := by
  intro g
  rw [coeff_one_add_X_sq_mul]
  simp only [coeff_add, coeff_shiftedNarayanaPolynomial (show 0 ≤ 22 by norm_num),
    coeff_shiftedNarayanaPolynomial (show 1 ≤ 22 by norm_num),
    coeff_shiftedNarayanaPolynomial (show 2 ≤ 22 by norm_num),
    ← C_ofNat (R := ℝ) 9, coeff_C_mul, add_comm (1 : ℝ[X]) X, coeff_X_add_one_pow]
  norm_num [Nat.choose]

/-- Multiplying by `X ^ n` shifts coefficients, so a failure of log-concavity of `g` at its
lowest three coefficients is a failure for `X ^ n * g` at index `n + 1`. -/
private lemma not_isLogConcave_X_pow_mul {R : Type*} [Semiring R] [LinearOrder R] (n : ℕ)
    {g : R[X]} (h : g.coeff 1 ^ 2 < g.coeff 0 * g.coeff 2) : ¬ (X ^ n * g).IsLogConcave := by
  rintro ⟨-, hlc⟩
  simpa [coeff_X_pow_mul', h.not_ge] using hlc n

private lemma nlcVertex_pos : ∀ S i, 0 < nlcVertex S i := by
  unfold nlcVertex; decide

private lemma sum_nlcVertex : ∀ S : Finset (Fin 5), S.card = 2 → ∑ i, nlcVertex S i = 51 := by
  unfold nlcVertex; decide

/-- The polytope lies in the positive orthant and in the hyperplane `∑ q_i = 51`, since each
vertex `v_S` (with `|S| = 2`) does and both sets are convex. -/
private lemma nlcPolytope_subset :
    nlcPolytope ⊆ Set.univ.pi (fun _ => Set.Ioi 0) ∩ {q | ∑ i, q i = 51} := by
  refine convexHull_min ?_ ((convex_pi fun i _ => convex_Ioi (0 : ℝ)).inter
    (convex_hyperplane (f := fun q : Fin 27 → ℝ => ∑ i, q i)
      ⟨fun x y => by simp [Finset.sum_add_distrib], fun c x => by simp [Finset.mul_sum]⟩ 51))
  rintro _ ⟨S, hS, rfl⟩
  exact ⟨fun i _ => (Int.cast_pos (R := ℝ)).2 (nlcVertex_pos S i),
    show ∑ i, (nlcVertex S i : ℝ) = 51 by exact_mod_cast sum_nlcVertex S hS⟩

/-- There is an integral polytope `P ⊆ ℝ_{>0}^{27}` contained in `{q : ∑ i, q i = 51}` such that
`∑_{q ∈ P ∩ ℤ^{27}} ∏_{i} N_{q_i}(x)` is not log-concave. -/
@[lognarayana "prop_non_log_concave_polytope"]
public theorem
    exists_isIntegralPolytope_not_isLogConcave_finsum_latticePoints_prod_narayanaPolynomial :
    ∃ P : Set (Fin 27 → ℝ), IsIntegralPolytope P ∧ (∀ q ∈ P, ∀ i, 0 < q i) ∧
      (∀ q ∈ P, ∑ i, q i = 51) ∧
      ¬ (∑ᶠ q ∈ P.latticePoints, ∏ i : Fin 27, narayanaPolynomial ⌊q i⌋₊).IsLogConcave := by
  set v : Finset (Fin 5) → Fin 27 → ℝ := fun S i => (nlcVertex S i : ℝ)
  refine ⟨nlcPolytope, ⟨⟨(Finset.univ.filter (fun S : Finset (Fin 5) => S.card = 2)).image v,
    ⟨v {0, 1}, Finset.mem_image.2 ⟨{0, 1}, by simp, rfl⟩⟩,
    by simp only [nlcPolytope]; congr 1; ext; simp [v]⟩,
    fun x hx i => ?_⟩, fun q hq i => (nlcPolytope_subset hq).1 i trivial,
    fun q hq => (nlcPolytope_subset hq).2, ?_⟩
  · obtain ⟨S, -, rfl⟩ := extremePoints_convexHull_subset hx
    exact ⟨_, rfl⟩
  · have hg := coeff_one_add_X_sq_mul_shiftedNarayanaPolynomial_add_low
    simp only [Prod.mk.injEq] at hg
    obtain ⟨h0, h1, h2⟩ := hg
    rw [finsum_latticePoints_nlcPolytope_prod_narayanaPolynomial, mul_assoc]
    exact not_isLogConcave_X_pow_mul 27 (by rw [h0, h1, h2]; norm_num)

end NarayanaSum
