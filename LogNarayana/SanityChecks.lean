/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib
public import LogNarayana.AuxiliaryDefinitions
public import LogNarayana.StackSorting.ValidHookConfigurations.Basic
public import LogNarayana.Nestohedron.Fertilitope.Basic
public import LogNarayana.Zonotope.TreeZonotope.Basic

/-!
# Sanity checks of the definitions against values printed in the paper
-/

@[expose] public section

namespace LogNarayanaSanity

open Polynomial

/-- Fuel-bounded copy of `List.stackSort`, structurally recursive so the kernel can run it. -/
def stackSortFuel : ℕ → List ℕ → List ℕ
  | 0, _ => []
  | _ + 1, [] => []
  | k + 1, a :: l =>
    stackSortFuel k ((a :: l).take ((a :: l).idxOf (l.foldr max a))) ++
      stackSortFuel k ((a :: l).drop ((a :: l).idxOf (l.foldr max a) + 1)) ++ [l.foldr max a]

/-- The right fold of `max` over `l` with initial value `a` is an element of `a :: l`. -/
lemma foldr_max_mem (a : ℕ) (l : List ℕ) : l.foldr max a ∈ a :: l := by
  induction l with
  | nil => simp
  | cons b l ih =>
    simp only [List.foldr_cons, List.mem_cons] at ih ⊢
    rcases max_choice b (l.foldr max a) with h | h <;> rw [h]
    · simp
    · rcases ih with h' | h' <;> simp [h']

/-- With fuel at least the length of `σ`, `stackSortFuel` computes `List.stackSort σ`. -/
lemma stackSortFuel_eq : ∀ (k : ℕ) (σ : List ℕ), σ.length ≤ k → stackSortFuel k σ = σ.stackSort
  | 0, σ, h => by
    rw [List.length_eq_zero_iff.1 (Nat.le_zero.1 h)]; simp [stackSortFuel, List.stackSort]
  | k + 1, [], _ => by simp [stackSortFuel, List.stackSort]
  | k + 1, a :: l, h => by
    have hm := List.idxOf_lt_length_of_mem (foldr_max_mem a l)
    simp only [List.length_cons] at h hm
    rw [stackSortFuel, List.stackSort.eq_2,
      stackSortFuel_eq k _ (by simp only [List.length_take, List.length_cons]; omega),
      stackSortFuel_eq k _ (by simp only [List.length_drop, List.length_cons]; omega)]


/-- The stack-sorting fiber of `π` as an explicit list: the permutations (Mathlib's structurally
recursive `List.permutations'`) of `12⋯n` that `stackSortFuel` sends to `π`. -/
def fiberList (π : List ℕ) : List (List ℕ) :=
  (idPermWord π.length).permutations'.filter fun σ => stackSortFuel σ.length σ = π

/-- The underlying multiset of `List.stackFiber π` is the list `fiberList π`. -/
lemma stackFiber_val (π : List ℕ) :
    (List.stackFiber π).val = (fiberList π : Multiset (List ℕ)) := by
  have hnd : (idPermWord π.length).permutations.Nodup :=
    List.nodup_permutations _ (List.nodup_range' ..)
  rw [List.stackFiber, Finset.filter_val, List.toFinset_val, hnd.dedup, Multiset.filter_coe,
    fiberList, Multiset.coe_eq_coe]
  refine ((List.permutations_perm_permutations' _).filter _).trans (List.Perm.of_eq ?_)
  refine List.filter_congr fun σ hσ => ?_
  have hlen : σ.length = π.length := by
    rw [List.mem_permutations'] at hσ; simpa [idPermWord] using hσ.length_eq
  simp [stackSortFuel_eq σ.length σ le_rfl]

/-- Sums over a stack-sorting fiber are sums over `fiberList`. -/
lemma sum_stackFiber {M β : Type*} [AddCommMonoid M] (π : List ℕ) (h : List ℕ → β) (g : β → M)
    (l : List β) (hl : List.Perm ((fiberList π).map h) l) :
    ∑ σ ∈ List.stackFiber π, g (h σ) = (l.map g).sum := by
  rw [Finset.sum_eq_multiset_sum, stackFiber_val, Multiset.map_coe, Multiset.sum_coe]
  change (List.map (g ∘ h) _).sum = _
  rw [← List.map_map]
  exact (hl.map g).sum_eq

/-- `sum_stackFiber` for a summand `f` that is `g ∘ h` up to definitional unfolding. -/
lemma sum_stackFiber' {M β : Type*} [AddCommMonoid M] {π : List ℕ} {f : List ℕ → M}
    (h : List ℕ → β) (g : β → M) (l : List β) (hf : ∀ σ, f σ = g (h σ))
    (hl : List.Perm ((fiberList π).map h) l) :
    ∑ σ ∈ List.stackFiber π, f σ = (l.map g).sum := by
  simp_rw [hf]; exact sum_stackFiber π h g l hl

/-- The Narayana transform of the monomial `z^α` is `∏_i Ñ_{α i}`. -/
lemma narayanaTransform_monomial {σ : Type*} (α : σ →₀ ℕ) :
    MvPolynomial.narayanaTransform σ (MvPolynomial.monomial α 1) =
      α.prod fun _ k => shiftedNarayanaPolynomial k := by
  rw [show MvPolynomial.monomial α (1 : ℝ) = MvPolynomial.basisMonomials σ ℝ α by
    rw [MvPolynomial.coe_basisMonomials]]
  exact Module.Basis.constr_basis _ _ _ _

/-- For `q ≠ 0`, the `j`-th coefficient of `N_q` is `(1/q) C(q, j) C(q, j - 1)` for
`1 ≤ j ≤ q`, and `0` otherwise. -/
lemma coeff_narayanaPolynomial {q : ℕ} (hq : q ≠ 0) (j : ℕ) :
    (narayanaPolynomial q).coeff j =
      if j ∈ Finset.Icc 1 q then (q : ℝ)⁻¹ * (q.choose j : ℝ) * (q.choose (j - 1) : ℝ) else 0 := by
  rw [narayanaPolynomial, if_neg hq, finsetSum_coeff]
  simp only [coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]

/-- The `j`-th coefficient of `Ñ_m` is `(1/(m+1)) C(m+1, j+1) C(m+1, j)` for `j ≤ m`, and `0`
otherwise. -/
lemma coeff_shiftedNarayanaPolynomial (m j : ℕ) :
    (shiftedNarayanaPolynomial m).coeff j =
      if j ∈ Finset.range (m + 1) then
        ((m + 1 : ℕ) : ℝ)⁻¹ * ((m + 1).choose (j + 1) : ℝ) * ((m + 1).choose j : ℝ) else 0 := by
  rw [shiftedNarayanaPolynomial, finsetSum_coeff]
  simp only [coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]

/-! ### Narayana polynomials (paper, Sec. 1.1 and Sec. 2.2) -/

/-- `N_0 = 1`. -/
theorem sanity_narayana_zero : narayanaPolynomial 0 = 1 := by simp [narayanaPolynomial]

/-- `N_1 = x`. -/
theorem sanity_narayana_one : narayanaPolynomial 1 = X := by
  ext j; rw [coeff_narayanaPolynomial (by norm_num)]
  rcases j with _ | _ | j <;> simp [coeff_X]

/-- `N_2 = x + x²` (Narayana numbers `1, 1`). -/
theorem sanity_narayana_two : narayanaPolynomial 2 = X + X ^ 2 := by
  ext j; rw [coeff_narayanaPolynomial (by norm_num)]
  rcases j with _ | _ | _ | j <;> simp [coeff_X_pow, coeff_X, Nat.choose]

/-- `N_3 = x + 3x² + x³` (Narayana numbers `1, 3, 1`). -/
theorem sanity_narayana_three : narayanaPolynomial 3 = X + 3 * X ^ 2 + X ^ 3 := by
  ext j; rw [coeff_narayanaPolynomial (by norm_num)]
  rcases j with _ | _ | _ | _ | j <;> simp [coeff_X_pow, coeff_X, Nat.choose]

/-- `N_4 = x + 6x² + 6x³ + x⁴` (Narayana numbers `1, 6, 6, 1`). -/
theorem sanity_narayana_four : narayanaPolynomial 4 = X + 6 * X ^ 2 + 6 * X ^ 3 + X ^ 4 := by
  ext j; rw [coeff_narayanaPolynomial (by norm_num)]
  rcases j with _ | _ | _ | _ | _ | j <;> simp [coeff_X_pow, coeff_X, Nat.choose]
  all_goals norm_num

/-- `N_5 = x + 10x² + 20x³ + 10x⁴ + x⁵` (Narayana numbers `1, 10, 20, 10, 1`). -/
theorem sanity_narayana_five :
    narayanaPolynomial 5 = X + 10 * X ^ 2 + 20 * X ^ 3 + 10 * X ^ 4 + X ^ 5 := by
  ext j; rw [coeff_narayanaPolynomial (by norm_num)]
  rcases j with _ | _ | _ | _ | _ | _ | j <;> simp [coeff_X_pow, coeff_X, Nat.choose] <;>
    norm_num

/-- `N_6 = x + 15x² + 50x³ + 50x⁴ + 15x⁵ + x⁶`. -/
theorem sanity_narayana_six :
    narayanaPolynomial 6 = X + 15 * X ^ 2 + 50 * X ^ 3 + 50 * X ^ 4 + 15 * X ^ 5 + X ^ 6 := by
  ext j; rw [coeff_narayanaPolynomial (by norm_num)]
  rcases j with _ | _ | _ | _ | _ | _ | _ | j <;> simp [coeff_X_pow, coeff_X, Nat.choose] <;>
    norm_num

/-- `Ñ_0 = 1` (Sec. 2.2). -/
theorem sanity_shifted_zero : shiftedNarayanaPolynomial 0 = 1 := by
  ext j; rw [coeff_shiftedNarayanaPolynomial]
  rcases j with _ | j <;> simp [coeff_one]

/-- `Ñ_1 = 1 + x` (Sec. 2.2). -/
theorem sanity_shifted_one : shiftedNarayanaPolynomial 1 = 1 + X := by
  ext j; rw [coeff_shiftedNarayanaPolynomial]
  rcases j with _ | _ | j <;> simp [coeff_X, coeff_one]

/-- `Ñ_2 = 1 + 3x + x²` (Sec. 2.2). -/
theorem sanity_shifted_two : shiftedNarayanaPolynomial 2 = 1 + 3 * X + X ^ 2 := by
  ext j; rw [coeff_shiftedNarayanaPolynomial]
  rcases j with _ | _ | _ | j <;> simp [coeff_X_pow, coeff_X, coeff_one, Nat.choose]

/-- `Ñ_3 = 1 + 6x + 6x² + x³` (Sec. 2.2). -/
theorem sanity_shifted_three : shiftedNarayanaPolynomial 3 = 1 + 6 * X + 6 * X ^ 2 + X ^ 3 := by
  ext j; rw [coeff_shiftedNarayanaPolynomial]
  rcases j with _ | _ | _ | _ | j <;> simp [coeff_X_pow, coeff_X, coeff_one, Nat.choose]
  all_goals norm_num

/-- `Ñ_4 = 1 + 10x + 20x² + 10x³ + x⁴`. -/
theorem sanity_shifted_four :
    shiftedNarayanaPolynomial 4 = 1 + 10 * X + 20 * X ^ 2 + 10 * X ^ 3 + X ^ 4 := by
  ext j; rw [coeff_shiftedNarayanaPolynomial]
  rcases j with _ | _ | _ | _ | _ | j <;> simp [coeff_X_pow, coeff_X, coeff_one, Nat.choose] <;>
    norm_num

/-- `Ñ_m = N_{m+1} / x`, checked as `x Ñ_m = N_{m+1}` for `m ≤ 3` from the two definitions. -/
theorem sanity_X_mul_shifted :
    X * shiftedNarayanaPolynomial 0 = narayanaPolynomial 1 ∧
    X * shiftedNarayanaPolynomial 1 = narayanaPolynomial 2 ∧
    X * shiftedNarayanaPolynomial 2 = narayanaPolynomial 3 ∧
    X * shiftedNarayanaPolynomial 3 = narayanaPolynomial 4 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  simp only [sanity_shifted_zero, sanity_shifted_one, sanity_shifted_two, sanity_shifted_three,
    sanity_narayana_one, sanity_narayana_two, sanity_narayana_three, sanity_narayana_four] <;>
  ring

/-- The γ-expansion (2.1) `Ñ_m = ∑_j C_j (m choose 2j) x^j (1+x)^{m-2j}` (the cited
`ShiftedNarayanaGammaExpansion`) holds for `m ≤ 4`. -/
theorem sanity_gamma_expansion (m : ℕ) (hm : m ≤ 4) :
    shiftedNarayanaPolynomial m =
      ∑ j ∈ Finset.range (m / 2 + 1),
        C ((catalan j : ℝ) * (m.choose (2 * j) : ℝ)) * X ^ j * (1 + X) ^ (m - 2 * j) := by
  interval_cases m <;>
  simp [sanity_shifted_zero, sanity_shifted_one, sanity_shifted_two, sanity_shifted_three,
    sanity_shifted_four, Finset.sum_range_succ, catalan_two, Nat.choose] <;>
  ring

/-- `Q_m(1 + x, x) = Ñ_m` for `m ≤ 3` (Sec. 2.2, after (2.2)). -/
theorem sanity_narayanaQ (m : ℕ) (hm : m ≤ 3) :
    MvPolynomial.aeval ![1 + X, X] (narayanaQ ℝ m) = shiftedNarayanaPolynomial m := by
  interval_cases m <;>
  simp [narayanaQ, sanity_shifted_zero, sanity_shifted_one, sanity_shifted_two,
    sanity_shifted_three, Finset.sum_range_succ, Nat.choose] <;>
  ring

/-- `N^{(1)}_q = N_q` for `1 ≤ q ≤ 4` (Sec. 4.3 and Sec. 7.1). -/
theorem sanity_deformed_one (q : ℕ) (hq : 1 ≤ q) (hq4 : q ≤ 4) :
    deformedNarayanaPolynomial ℝ 1 q = narayanaPolynomial q := by
  interval_cases q <;>
  simp [deformedNarayanaPolynomial, narayanaQ, sanity_narayana_one, sanity_narayana_two,
    sanity_narayana_three, sanity_narayana_four, Finset.sum_range_succ, Nat.choose] <;>
  ring

/-- `N^{(λ)}_3 = x((1 + x)² + λx)` and `N^{(0)}_q = x (1 + x)^{q-1}` at `q = 4`
(Corollary 4.7 and its proof). -/
theorem sanity_deformed_three (lam : ℝ) :
    deformedNarayanaPolynomial ℝ lam 3 = X * ((1 + X) ^ 2 + C lam * X) ∧
    deformedNarayanaPolynomial ℝ 0 4 = X * (1 + X) ^ 3 := by
  constructor <;>
  simp [deformedNarayanaPolynomial, narayanaQ, Finset.sum_range_succ, Nat.choose]

/-- The first signed Appell polynomials `η_0, …, η_4` (Sec. 6.1). -/
theorem sanity_signedAppell :
    signedAppell ℝ 0 = 1 ∧ signedAppell ℝ 1 = X ∧ signedAppell ℝ 2 = X ^ 2 - 1 ∧
    signedAppell ℝ 3 = X ^ 3 - 3 * X ∧ signedAppell ℝ 4 = X ^ 4 - 6 * X ^ 2 + 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
  simp [signedAppell, Finset.sum_range_succ, catalan_two, Nat.choose] <;>
  ring

/-- The Narayana transform of `z²` is `Ñ_2 = (1 + x)² + x` (the paper's `𝒩(F)` for `F = z_1²`),
and that of `z₀ z₁²` is `Ñ_1 Ñ_2`. -/
theorem sanity_narayanaTransform :
    MvPolynomial.narayanaTransform (Fin 1) (MvPolynomial.X 0 ^ 2) = (1 + X) ^ 2 + X ∧
    MvPolynomial.narayanaTransform (Fin 2) (MvPolynomial.X 0 * MvPolynomial.X 1 ^ 2) =
      (1 + X) * (1 + 3 * X + X ^ 2) := by
  constructor
  · rw [MvPolynomial.X_pow_eq_monomial, narayanaTransform_monomial, Finsupp.prod_single_index]
    · rw [sanity_shifted_two]
      ring
    · exact sanity_shifted_zero
  · rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.X, MvPolynomial.monomial_mul, one_mul,
      narayanaTransform_monomial, Finsupp.prod_fintype _ _ (fun _ => sanity_shifted_zero),
      Fin.prod_univ_two]
    simp [sanity_shifted_one, sanity_shifted_two]

/-! ### Stack-sorting, descents, tops and peaks (Sec. 1.1, Sec. 2.1) -/

/-- `s(416352) = 143256` (Sec. 1.1). -/
theorem sanity_stackSort_416352 :
    (List.stackSort [4, 1, 6, 3, 5, 2] : List ℕ) = [1, 4, 3, 2, 5, 6] := by
  rw [← stackSortFuel_eq 6 _ (by decide)]
  decide

/-- Fig. 2: the tree with inorder `σ = 2751364` has postorder `π = 2135467 = s(σ)`. -/
theorem sanity_stackSort_2751364 :
    (List.stackSort [2, 7, 5, 1, 3, 6, 4] : List ℕ) = [2, 1, 3, 5, 4, 6, 7] := by
  rw [← stackSortFuel_eq 7 _ (by decide)]
  decide

/-- For `σ = 2751364`: `Des = {2, 3, 6}`, `DT = {5, 6, 7}`, `AT = {3, 6, 7}`, two peaks (the two
binary vertices of Fig. 2, labelled `7` and `6 = DT ∩ AT`). -/
theorem sanity_tops_2751364 :
    List.descentSet ([2, 7, 5, 1, 3, 6, 4] : List ℕ) = {2, 3, 6} ∧
    List.numDescents ([2, 7, 5, 1, 3, 6, 4] : List ℕ) = 3 ∧
    List.descentTops ([2, 7, 5, 1, 3, 6, 4] : List ℕ) = {5, 6, 7} ∧
    List.ascentTops ([2, 7, 5, 1, 3, 6, 4] : List ℕ) = {3, 6, 7} ∧
    List.peakCount ([2, 7, 5, 1, 3, 6, 4] : List ℕ) = 2 ∧
    (List.descentTops ([2, 7, 5, 1, 3, 6, 4] : List ℕ) ∩
      List.ascentTops [2, 7, 5, 1, 3, 6, 4]).card = 2 := by
  decide

/-- The fiber of `123` is `{123, 132, 213, 312, 321}`, and `s⁻¹(21) = ∅`. -/
theorem sanity_stackFiber_small :
    List.stackFiber [1, 2, 3] = {[1, 2, 3], [1, 3, 2], [2, 1, 3], [3, 1, 2], [3, 2, 1]} ∧
    List.stackFiber [2, 1] = ∅ := by
  constructor <;> rw [← Finset.val_inj, stackFiber_val] <;> decide +kernel

/-- The fertility `|s⁻¹(12⋯n)|` is the Catalan number `C_n` for `n ≤ 6`. -/
theorem sanity_fertility_identity :
    (List.stackFiber (idPermWord 1)).card = catalan 1 ∧
    (List.stackFiber (idPermWord 2)).card = catalan 2 ∧
    (List.stackFiber (idPermWord 3)).card = catalan 3 ∧
    (List.stackFiber (idPermWord 4)).card = catalan 4 ∧
    (List.stackFiber (idPermWord 5)).card = catalan 5 ∧
    (List.stackFiber (idPermWord 6)).card = catalan 6 := by
  simp only [Finset.card, stackFiber_val, Multiset.coe_card]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [show (catalan _ : ℕ) = _ from rfl] <;>
    decide +kernel

/-- `x D_{12⋯n}(x) = N_n(x)` for `n = 1, …, 4` (Sec. 1.1), by enumerating the fiber. -/
theorem sanity_fiberDescent_identity :
    X * List.fiberDescentPolynomial ℝ (idPermWord 1) = narayanaPolynomial 1 ∧
    X * List.fiberDescentPolynomial ℝ (idPermWord 2) = narayanaPolynomial 2 ∧
    X * List.fiberDescentPolynomial ℝ (idPermWord 3) = narayanaPolynomial 3 ∧
    X * List.fiberDescentPolynomial ℝ (idPermWord 4) = narayanaPolynomial 4 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [List.fiberDescentPolynomial, sum_stackFiber' List.numDescents (X ^ ·) [0]
      (fun _ => rfl) (by decide +kernel), sanity_narayana_one]
    simp
  · rw [List.fiberDescentPolynomial, sum_stackFiber' List.numDescents (X ^ ·) [0, 1]
      (fun _ => rfl) (by decide +kernel), sanity_narayana_two]
    simp
    ring
  · rw [List.fiberDescentPolynomial, sum_stackFiber' List.numDescents (X ^ ·) [0, 1, 1, 1, 2]
      (fun _ => rfl) (by decide +kernel), sanity_narayana_three]
    simp
    ring
  · rw [List.fiberDescentPolynomial, sum_stackFiber' List.numDescents (X ^ ·)
      ([0] ++ List.replicate 6 1 ++ List.replicate 6 2 ++ [3]) (fun _ => rfl) (by decide +kernel),
      sanity_narayana_four]
    simp
    ring

/-- `D_{2135467}(x) = 5x² + 12x³ + 5x⁴` (Sec. 1.2 and Example 3.3), by enumerating all `7!`
permutations. -/
theorem sanity_fiberDescent_2135467 :
    List.fiberDescentPolynomial ℝ [2, 1, 3, 5, 4, 6, 7] = 5 * X ^ 2 + 12 * X ^ 3 + 5 * X ^ 4 := by
  rw [List.fiberDescentPolynomial, sum_stackFiber' List.numDescents (X ^ ·)
    (List.replicate 5 2 ++ List.replicate 12 3 ++ List.replicate 5 4) (fun _ => rfl)
    (by decide +kernel)]
  simp only [List.map_append, List.map_replicate, List.sum_append, List.sum_replicate,
    nsmul_eq_mul]
  push_cast
  ring

/-- `H_{2135467}(x, y) = 5x²y²(x + y)² + 2x³y³` (Example 3.3). -/
theorem sanity_fiberHomog_2135467 :
    List.fiberHomogPolynomial ℝ [2, 1, 3, 5, 4, 6, 7] =
      5 * MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1 ^ 2 * (MvPolynomial.X 0 + MvPolynomial.X 1) ^ 2 +
        2 * MvPolynomial.X 0 ^ 3 * MvPolynomial.X 1 ^ 3 := by
  rw [List.fiberHomogPolynomial]
  refine (sum_stackFiber' List.numDescents
    (fun d => (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℝ) ^ d * MvPolynomial.X 1 ^ (7 - 1 - d))
    (List.replicate 5 2 ++ List.replicate 12 3 ++ List.replicate 5 4) (fun _ => rfl)
    (by decide +kernel)).trans ?_
  simp only [List.map_append, List.map_replicate, List.sum_append, List.sum_replicate,
    nsmul_eq_mul]
  push_cast
  ring

/-- `H^λ_{2135467}(x, y) = 5λ²x²y²(x + y)² + 2λ³x³y³`: the fiber's `(peak, des)` statistics. -/
theorem sanity_fiberPeak_2135467 (lam : ℝ) :
    List.fiberPeakPolynomial ℝ lam [2, 1, 3, 5, 4, 6, 7] =
      MvPolynomial.C (5 * lam ^ 2) * MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1 ^ 2 *
          (MvPolynomial.X 0 + MvPolynomial.X 1) ^ 2 +
        MvPolynomial.C (2 * lam ^ 3) * MvPolynomial.X 0 ^ 3 * MvPolynomial.X 1 ^ 3 := by
  rw [List.fiberPeakPolynomial]
  refine (sum_stackFiber' (fun σ => (σ.peakCount, σ.numDescents))
    (fun p => MvPolynomial.C (lam ^ p.1) * (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℝ) ^ p.2 *
      MvPolynomial.X 1 ^ (7 - 1 - p.2))
    (List.replicate 5 (2, 2) ++ List.replicate 10 (2, 3) ++ List.replicate 5 (2, 4) ++
      List.replicate 2 (3, 3)) (fun _ => rfl) (by decide +kernel)).trans ?_
  simp only [List.map_append, List.map_replicate, List.sum_append, List.sum_replicate,
    nsmul_eq_mul, MvPolynomial.C_mul, map_ofNat MvPolynomial.C, MvPolynomial.C_pow]
  push_cast
  ring

/-- Sec. 9.1: `∑_{σ ∈ s⁻¹(π)} z^{peak(σ)} = 2^{n-1} Γ_π(z / 4)` at `π = 2135467`, with
`Γ_π(z) = 5z² + 2z³` (Example 3.3): the peak distribution is `20z² + 2z³`. -/
theorem sanity_peak_distribution_2135467 (z : ℝ) :
    (∑ σ ∈ List.stackFiber [2, 1, 3, 5, 4, 6, 7], (X : ℝ[X]) ^ σ.peakCount).eval z =
      2 ^ 6 * (5 * (z / 4) ^ 2 + 2 * (z / 4) ^ 3) := by
  rw [sum_stackFiber' List.peakCount (X ^ ·) (List.replicate 20 2 ++ List.replicate 2 3)
    (fun _ => rfl) (by decide +kernel)]
  simp only [List.map_append, List.map_replicate, List.sum_append, List.sum_replicate,
    nsmul_eq_mul, eval_add, eval_mul, eval_pow, eval_X, eval_natCast]
  ring

/-- `𝒟_{123}(x, y) = (x₂ + y₂)(x₃ + y₃) + x₃y₃`, and `𝒟_{12} = x₂ + y₂`; every coefficient is `1`,
as for a basis generating polynomial (Thm. 1.2). -/
theorem sanity_fiberTop_small :
    List.fiberTopPolynomial ℝ [1, 2] = MvPolynomial.X (true, 2) + MvPolynomial.X (false, 2) ∧
    List.fiberTopPolynomial ℝ [1, 2, 3] =
      (MvPolynomial.X (true, 2) + MvPolynomial.X (false, 2)) *
          (MvPolynomial.X (true, 3) + MvPolynomial.X (false, 3)) +
        MvPolynomial.X (true, 3) * MvPolynomial.X (false, 3) := by
  constructor
  · rw [List.fiberTopPolynomial, sum_stackFiber' (fun σ => (σ.descentTops, σ.ascentTops))
      (fun p => (∏ a ∈ p.1, (MvPolynomial.X (true, a) : MvPolynomial (Bool × ℕ) ℝ)) *
        ∏ b ∈ p.2, MvPolynomial.X (false, b))
      [(∅, {2}), ({2}, ∅)] (fun _ => rfl) (by decide +kernel)]
    simp
    ring
  · rw [List.fiberTopPolynomial, sum_stackFiber' (fun σ => (σ.descentTops, σ.ascentTops))
      (fun p => (∏ a ∈ p.1, (MvPolynomial.X (true, a) : MvPolynomial (Bool × ℕ) ℝ)) *
        ∏ b ∈ p.2, MvPolynomial.X (false, b))
      [(∅, {2, 3}), ({3}, {3}), ({2}, {3}), ({3}, {2}), ({2, 3}, ∅)] (fun _ => rfl)
      (by decide +kernel)]
    simp
    ring

/-- Sec. 5 (Prop. 5.2 and the display after it): `𝒞_{21345}(z, 1) = (z + 1) H_{21345}(z + 1, z)
= 3z + 20z² + 45z³ + 42z⁴ + 14z⁵`, with `H_{21345}` computed by enumerating the fiber. -/
theorem sanity_schroeder_21345 :
    (X + 1 : ℝ[X]) * MvPolynomial.aeval ![(X + 1 : ℝ[X]), X]
      (List.fiberHomogPolynomial ℝ [2, 1, 3, 4, 5]) =
      3 * X + 20 * X ^ 2 + 45 * X ^ 3 + 42 * X ^ 4 + 14 * X ^ 5 := by
  have hH : List.fiberHomogPolynomial ℝ [2, 1, 3, 4, 5] =
      3 * MvPolynomial.X 0 * MvPolynomial.X 1 ^ 3 +
        8 * MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1 ^ 2 +
        3 * MvPolynomial.X 0 ^ 3 * MvPolynomial.X 1 := by
    rw [List.fiberHomogPolynomial]
    refine (sum_stackFiber' List.numDescents
      (fun d => (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℝ) ^ d * MvPolynomial.X 1 ^ (5 - 1 - d))
      (List.replicate 3 1 ++ List.replicate 8 2 ++ List.replicate 3 3) (fun _ => rfl)
      (by decide +kernel)).trans ?_
    simp only [List.map_append, List.map_replicate, List.sum_append, List.sum_replicate,
      nsmul_eq_mul]
    push_cast
    ring
  rw [hH]
  simp
  ring

/-! ### Matchings and `Γ_π` (Sec. 3.1, Example 3.3) -/

/-- A decidable restatement of `IsNoncrossingPartialMatching`. -/
def NCPMProp (N : ℕ) (M : Finset (ℕ × ℕ)) : Prop :=
  (∀ p ∈ M, 1 ≤ p.1) ∧ (∀ p ∈ M, p.1 < p.2) ∧ (∀ p ∈ M, p.2 ≤ N) ∧
    (∀ p ∈ M, ∀ q ∈ M, ∀ x ∈ ({p.1, p.2} : Finset ℕ), (x = q.1 ∨ x = q.2) → p = q) ∧
    ∀ p ∈ M, ∀ q ∈ M, ¬ (p.1 < q.1 ∧ q.1 < p.2 ∧ p.2 < q.2)

/-- `NCPMProp N` is decidable. -/
instance (N : ℕ) : DecidablePred (NCPMProp N) := fun M => by unfold NCPMProp; infer_instance

/-- `IsNoncrossingPartialMatching N M` is equivalent to `NCPMProp N M`. -/
lemma isNoncrossingPartialMatching_iff (N : ℕ) (M : Finset (ℕ × ℕ)) :
    IsNoncrossingPartialMatching N M ↔ NCPMProp N M :=
  ⟨fun h => ⟨h.one_le_fst, h.fst_lt_snd, h.snd_le,
      fun p hp q hq x hx hxq => h.eq_of_mem_of_mem p hp q hq x (by simpa using hx) hxq,
      h.noncrossing⟩,
    fun ⟨h1, h2, h3, h4, h5⟩ =>
      ⟨h1, h2, h3, fun p hp q hq x hx hxq => h4 p hp q hq x (by simpa using hx) hxq, h5⟩⟩

/-- A noncrossing partial matching on `[N]` has at most `N / 2` pairs (its endpoints are
distinct elements of `[N]`). -/
lemma card_le_of_NCPMProp {N : ℕ} {M : Finset (ℕ × ℕ)} (h : NCPMProp N M) : M.card ≤ N / 2 := by
  obtain ⟨h1, h2, h3, h4, -⟩ := h
  have hfst : Set.InjOn Prod.fst (M : Set (ℕ × ℕ)) := fun p hp q hq hpq =>
    h4 p hp q hq p.1 (by simp) (Or.inl hpq)
  have hsnd : Set.InjOn Prod.snd (M : Set (ℕ × ℕ)) := fun p hp q hq hpq =>
    h4 p hp q hq p.2 (by simp) (Or.inr hpq)
  have hdisj : Disjoint (M.image Prod.fst) (M.image Prod.snd) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨q, hq, hqp⟩ := Finset.mem_image.1 hx'
    have := h4 p hp q hq p.1 (by simp) (Or.inr hqp.symm)
    subst this
    exact absurd hqp (h2 p hp).ne'
  have hsub : M.image Prod.fst ∪ M.image Prod.snd ⊆ Finset.Icc 1 N := by
    intro x hx
    rcases Finset.mem_union.1 hx with hx | hx <;> obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hx <;>
      have := h1 p hp <;> have := h2 p hp <;> have := h3 p hp <;> simp <;> omega
  have := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injOn hfst,
    Finset.card_image_of_injOn hsnd, Nat.card_Icc] at this
  omega

/-- The finite set of candidate matchings that `fiberMatchings π` is cut out of. -/
def fiberMatchingsFinset (π : List ℕ) : Finset (Finset (ℕ × ℕ)) :=
  ((Finset.range ((π.length - 1) / 2 + 1)).biUnion fun k =>
      ((Finset.Icc 1 (π.length - 1) ×ˢ Finset.Icc 1 (π.length - 1)).filter
        (fun p => p.1 < p.2)).powersetCard k).filter
    fun M => π.descentSet ⊆ M.leftEndpoints ∧ NCPMProp (π.length - 1) M ∧
      ∀ p ∈ M, ∃ (ha : p.1 - 1 < π.length) (hb : p.2 < π.length), π[p.1 - 1] < π[p.2]

/-- `π.fiberMatchings` is the set underlying `fiberMatchingsFinset π`. -/
lemma fiberMatchings_eq (π : List ℕ) :
    π.fiberMatchings = (fiberMatchingsFinset π : Set (Finset (ℕ × ℕ))) := by
  ext M
  simp only [List.fiberMatchings, fiberMatchingsFinset, isNoncrossingPartialMatching_iff,
    Set.mem_ofPred_eq, Finset.coe_filter, Finset.mem_biUnion, Finset.mem_range,
    Finset.mem_powersetCard]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨M.card, by have := card_le_of_NCPMProp h1; omega, fun p hp => ?_, rfl⟩, h2, h1, h3⟩
    have := h1.1 p hp; have := h1.2.1 p hp; have := h1.2.2.1 p hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]; omega
  · rintro ⟨-, h2, h1, h3⟩; exact ⟨h1, h2, h3⟩

set_option maxHeartbeats 2000000 in
-- exhaustive enumeration of candidate matchings by `decide` is expensive
/-- `Γ_{2135467}(z) = 5z² + 2z³` (Example 3.3): the seven matchings of `𝒜(2135467)`, found by
enumerating all sets of at most three candidate pairs. -/
theorem sanity_gamma_2135467 :
    List.fiberMatchingPolynomial ℝ [2, 1, 3, 5, 4, 6, 7] = 5 * X ^ 2 + 2 * X ^ 3 := by
  have key : (fiberMatchingsFinset [2, 1, 3, 5, 4, 6, 7]).val.map Finset.card =
      ((List.replicate 5 2 ++ List.replicate 2 3 : List ℕ) : Multiset ℕ) := by
    decide +kernel
  rewrite [List.fiberMatchingPolynomial, fiberMatchings_eq, finsum_mem_coe_finset,
    Finset.sum_eq_multiset_sum,
    show (fun M : Finset (ℕ × ℕ) => (X : ℝ[X]) ^ M.card) = (fun d => (X : ℝ[X]) ^ d) ∘ Finset.card
      from rfl, ← Multiset.map_map, key, Multiset.map_coe, Multiset.sum_coe, List.map_append,
    List.map_replicate, List.map_replicate, List.sum_append, List.sum_replicate,
    List.sum_replicate, nsmul_eq_mul, nsmul_eq_mul]
  norm_num

/-- Prop. 3.1 at `π = 2135467`: `D_π = ∑_{M ∈ 𝒜(π)} x^{|M|} (1 + x)^{n-1-2|M|}`, i.e.
`5x²(1 + x)² + 2x³`, agrees with the enumerated `D_π`. -/
theorem sanity_matching_formula_2135467 :
    List.fiberDescentPolynomial ℝ [2, 1, 3, 5, 4, 6, 7] =
      5 * (X ^ 2 * (1 + X) ^ 2) + 2 * (X ^ 3 * (1 + X) ^ 0) := by
  rw [sanity_fiberDescent_2135467]
  ring

/-! ### Valid compositions and the refined fertility formula (Sec. 1.2, Sec. 2.3) -/

/-- The valid compositions of `2135467` are `(3,1,1), (2,1,2), (2,2,1), (1,2,2), (1,3,1)`
(`List.validCompositions_2135467`). -/
theorem sanity_validCompositions_2135467 :
    List.validCompositions [2, 1, 3, 5, 4, 6, 7] =
      {![3, 1, 1], ![2, 1, 2], ![2, 2, 1], ![1, 2, 2], ![1, 3, 1]} :=
  List.validCompositions_2135467

/-- The refined fertility formula `x D_π(x) = ∑_{q ∈ 𝒱(π)} ∏ N_{q_i}(x)` (the cited
`RefinedFertilityFormula`) at `π = 2135467`: the left side is enumerated from the definitions, the
right side is the paper's display `N_{(3,1,1)} + N_{(2,2,1)} + N_{(1,3,1)} + N_{(2,1,2)} +
N_{(1,2,2)} = 5x³ + 12x⁴ + 5x⁵` over the five compositions of
`sanity_validCompositions_2135467`. -/
theorem sanity_refined_fertility_2135467 :
    X * List.fiberDescentPolynomial ℝ [2, 1, 3, 5, 4, 6, 7] =
        ∑ q ∈ ({![3, 1, 1], ![2, 1, 2], ![2, 2, 1], ![1, 2, 2], ![1, 3, 1]} :
          Finset (Fin 3 → ℕ)), ∏ i, narayanaPolynomial (q i) ∧
      X * List.fiberDescentPolynomial ℝ [2, 1, 3, 5, 4, 6, 7] =
        5 * X ^ 3 + 12 * X ^ 4 + 5 * X ^ 5 := by
  have h : ∑ q ∈ ({![3, 1, 1], ![2, 1, 2], ![2, 2, 1], ![1, 2, 2], ![1, 3, 1]} :
      Finset (Fin 3 → ℕ)), ∏ i, narayanaPolynomial (q i) = 5 * X ^ 3 + 12 * X ^ 4 + 5 * X ^ 5 := by
    repeat rw [Finset.sum_insert (by decide)]
    simp only [Finset.sum_singleton, Fin.prod_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
      sanity_narayana_one, sanity_narayana_two, sanity_narayana_three]
    ring
  rw [h, sanity_fiberDescent_2135467]
  constructor <;> ring

/-- The fertilitope `Fer_{2135467}` has the five lattice points of Fig. 1
(`List.latticePoints_fertilitope_2135467`). -/
theorem sanity_fertilitope_2135467 :
    (List.fertilitope ℝ [2, 1, 3, 5, 4, 6, 7]).latticePoints =
      ({![3, 1, 1], ![2, 1, 2], ![2, 2, 1], ![1, 2, 2], ![1, 3, 1]} : Set (Fin 3 → ℝ)) :=
  List.latticePoints_fertilitope_2135467

/-! ### Restricted noncrossing sums (Sec. 7.1, the example after Thm. 7.1) -/

/-- Eq. (7.1) at `n = 12`, `k = a = 3`: `n! / (k! (n-k+1)!) = 22`, and `22` times the sum of
`∏ N_{q_i}` over the ten compositions of `12` into three parts `≥ 3` is the printed
`R^{(3)}_{12,3}(x)`. The composition sum is enumerated from `Finset.Nat.antidiagonalTuple`. -/
theorem sanity_restricted_nc_12_3_3 :
    Nat.factorial 12 / (Nat.factorial 3 * Nat.factorial 10) = 22 ∧
    ((Finset.Nat.antidiagonalTuple 3 12).filter fun q => ∀ i, 3 ≤ q i).card = 10 ∧
    22 * ∑ q ∈ (Finset.Nat.antidiagonalTuple 3 12).filter (fun q => ∀ i, 3 ≤ q i),
        ∏ i, narayanaPolynomial (q i) =
      X ^ 3 * (220 + 4290 * X + 30558 * X ^ 2 + 105336 * X ^ 3 + 192720 * X ^ 4 +
        192720 * X ^ 5 + 105336 * X ^ 6 + 30558 * X ^ 7 + 4290 * X ^ 8 + 220 * X ^ 9) := by
  refine ⟨by decide, by decide +kernel, ?_⟩
  rw [Finset.sum_eq_multiset_sum,
    show ((Finset.Nat.antidiagonalTuple 3 12).filter fun q => ∀ i, 3 ≤ q i).val.map
        (fun q => ∏ i, narayanaPolynomial (q i)) =
      (((Finset.Nat.antidiagonalTuple 3 12).filter fun q => ∀ i, 3 ≤ q i).val.map
        (fun q : Fin 3 → ℕ => [q 0, q 1, q 2].map narayanaPolynomial |>.prod)) by
      refine Multiset.map_congr rfl fun q _ => ?_
      simp [Fin.prod_univ_three, mul_assoc],
    show (fun q : Fin 3 → ℕ => ([q 0, q 1, q 2].map narayanaPolynomial).prod) =
      (fun l : List ℕ => (l.map narayanaPolynomial).prod) ∘ (fun q : Fin 3 → ℕ => [q 0, q 1, q 2])
      from rfl, ← Multiset.map_map,
    show ((Finset.Nat.antidiagonalTuple 3 12).filter fun q => ∀ i, 3 ≤ q i).val.map
        (fun q : Fin 3 → ℕ => [q 0, q 1, q 2]) =
      (([[3, 3, 6], [3, 4, 5], [3, 5, 4], [3, 6, 3], [4, 3, 5], [4, 4, 4], [4, 5, 3], [5, 3, 4],
        [5, 4, 3], [6, 3, 3]] : List (List ℕ)) : Multiset (List ℕ)) by decide +kernel]
  simp only [Multiset.map_coe, Multiset.sum_coe, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, List.sum_cons, List.sum_nil, sanity_narayana_three, sanity_narayana_four,
    sanity_narayana_five, sanity_narayana_six]
  ring

/-! ### The path zonotope (Example 6.6) -/

/-- The path `1 - 2 - 3 - 4` as a loopless multigraph on `Fin 4` with edges `Fin 3`. -/
def pathFour : LooplessMultigraph (Fin 4) (Fin 3) :=
  ⟨Fin.castSucc, Fin.succ, fun i => (Fin.castSucc_lt_succ (i := i)).ne⟩

/-- Example 6.6: the Narayana sum `∑ ∏_v Ñ_{q_v - 1}` over the eight lattice points of `P_{T,𝟏}`
listed in the paper is `8 + 28x + 28x² + 8x³ = 4(1 + x)(x + 2)(2x + 1)`, and multiplying by `x^4`
gives `∑ ∏_v N_{q_v}`. The eight points are those of
`LooplessMultigraph.latticePoints_zonotope_path_four`. -/
theorem sanity_path_zonotope_sum :
    (∑ q ∈ ({![2, 2, 2, 1], ![2, 2, 1, 2], ![2, 1, 3, 1], ![2, 1, 2, 2], ![1, 3, 2, 1],
        ![1, 3, 1, 2], ![1, 2, 3, 1], ![1, 2, 2, 2]} : Finset (Fin 4 → ℕ)),
        ∏ v, shiftedNarayanaPolynomial (q v - 1)) = 8 + 28 * X + 28 * X ^ 2 + 8 * X ^ 3 ∧
    (8 + 28 * X + 28 * X ^ 2 + 8 * X ^ 3 : ℝ[X]) = 4 * (1 + X) * (X + 2) * (2 * X + 1) ∧
    (∑ q ∈ ({![2, 2, 2, 1], ![2, 2, 1, 2], ![2, 1, 3, 1], ![2, 1, 2, 2], ![1, 3, 2, 1],
        ![1, 3, 1, 2], ![1, 2, 3, 1], ![1, 2, 2, 2]} : Finset (Fin 4 → ℕ)),
        ∏ v, narayanaPolynomial (q v)) = X ^ 4 * (8 + 28 * X + 28 * X ^ 2 + 8 * X ^ 3) := by
  refine ⟨?_, by ring, ?_⟩ <;>
  · repeat rw [Finset.sum_insert (by decide)]
    simp only [Finset.sum_singleton, Fin.prod_univ_four, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
      Matrix.tail_cons, sanity_shifted_zero, sanity_shifted_one, sanity_shifted_two,
      sanity_narayana_one, sanity_narayana_two, sanity_narayana_three, Nat.reduceSub]
    ring

/-- Each of the eight listed points is a lattice point of the zonotope `P_{T,𝟏}` (explicit
orientation witnesses, from the definition `LooplessMultigraph.zonotope`). -/
theorem sanity_path_zonotope_mem (q : Fin 4 → ℕ)
    (hq : q ∈ ({![2, 2, 2, 1], ![2, 2, 1, 2], ![2, 1, 3, 1], ![2, 1, 2, 2], ![1, 3, 2, 1],
        ![1, 3, 1, 2], ![1, 2, 3, 1], ![1, 2, 2, 2]} : Finset (Fin 4 → ℕ))) :
    (fun v => (q v : ℝ)) ∈ (pathFour.zonotope (fun _ => (1 : ℝ))).latticePoints := by
  have key : ∀ (q : Fin 4 → ℕ) (h : Fin 3 → Fin 4), (∀ e, h e = e.castSucc ∨ h e = e.succ) →
      (∀ v, (q v : ℝ) = 1 + ∑ e, (Pi.single (h e) (1 : ℝ) : Fin 4 → ℝ) v) →
      (fun v => (q v : ℝ)) ∈ (pathFour.zonotope (fun _ => (1 : ℝ))).latticePoints := by
    intro q h hh hq
    refine ⟨⟨fun e => Pi.single (h e) 1, fun e => subset_convexHull ℝ _ ⟨h e, ?_, rfl⟩, ?_⟩,
      fun v => ⟨q v, by simp⟩⟩
    · rcases hh e with h' | h' <;> simp [h', pathFour]
    · funext v; simp [hq, Finset.sum_apply]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact key _ ![0, 1, 2] (by decide)
      (by intro v; fin_cases v <;> simp [Fin.sum_univ_three] <;> norm_num)
  · exact key _ ![0, 1, 3] (by decide)
      (by intro v; fin_cases v <;> simp [Fin.sum_univ_three] <;> norm_num)
  · exact key _ ![0, 2, 2] (by decide)
      (by intro v; fin_cases v <;> simp [Fin.sum_univ_three] <;> norm_num)
  · exact key _ ![0, 2, 3] (by decide)
      (by intro v; fin_cases v <;> simp [Fin.sum_univ_three] <;> norm_num)
  · exact key _ ![1, 1, 2] (by decide)
      (by intro v; fin_cases v <;> simp [Fin.sum_univ_three] <;> norm_num)
  · exact key _ ![1, 1, 3] (by decide)
      (by intro v; fin_cases v <;> simp [Fin.sum_univ_three] <;> norm_num)
  · exact key _ ![1, 2, 2] (by decide)
      (by intro v; fin_cases v <;> simp [Fin.sum_univ_three] <;> norm_num)
  · exact key _ ![1, 2, 3] (by decide)
      (by intro v; fin_cases v <;> simp [Fin.sum_univ_three] <;> norm_num)

/-! ### Binary building sets (Sec. 2.3) -/

/-- `{{0}, {1}, {2}, {0,1}, {0,1,2}}` is a binary building set on `Fin 3`; `{{0},{1},{2},{0,1},
{1,2}}` is not (the two intervals cross), nor is a family missing a singleton. -/
theorem sanity_binary_building_set :
    IsBinaryBuildingSet ({{0}, {1}, {2}, {0, 1}, {0, 1, 2}} : Finset (Finset (Fin 3))) ∧
    ¬ IsBinaryBuildingSet ({{0}, {1}, {2}, {0, 1}, {1, 2}} : Finset (Finset (Fin 3))) ∧
    ¬ IsBinaryBuildingSet ({{0}, {1}, {0, 1, 2}} : Finset (Finset (Fin 3))) := by
  refine ⟨⟨by decide, by decide, by decide⟩, fun h => ?_, fun h => ?_⟩
  · have := h.disjoint_or_subset_or_subset {0, 1} (by decide) {1, 2} (by decide)
    revert this
    decide
  · have := h.singleton_mem 2
    revert this
    decide

/-! ### The non-log-concave polytope (Proposition 9.5) -/

/-- `N_{m+1} = x Ñ_m`. -/
lemma narayanaPolynomial_succ (m : ℕ) :
    narayanaPolynomial (m + 1) = X * shiftedNarayanaPolynomial m := by
  ext j
  rw [coeff_narayanaPolynomial (Nat.succ_ne_zero m)]
  rcases j with _ | j
  · simp
  · rw [coeff_X_mul, coeff_shiftedNarayanaPolynomial]
    simp only [Finset.mem_Icc, Finset.mem_range, Nat.add_sub_cancel]
    by_cases h : j < m + 1
    · rw [if_pos (by omega), if_pos h]
    · rw [if_neg (by omega), if_neg h]

/-- All ten vertices `v_S` (`|S| = 2`) have positive integer coordinates with sum `51`. -/
theorem sanity_nlcVertex :
    ∀ S : Finset (Fin 5), S.card = 2 → (∑ i, nlcVertex S i = 51) ∧ ∀ i, 0 < nlcVertex S i := by
  decide +kernel

/-- Proposition 9.5: `x^{-27} ∑ ∏ N_{q_i} = (1 + x)² (Ñ_22 + 9 (1 + x)^22)`, summing over the ten
vertices `v_S` (the paper shows these are all the lattice points), and the first three
coefficients `10, 471, 22472` violate log-concavity. -/
theorem sanity_nlc_sum :
    ∑ S ∈ (Finset.univ : Finset (Finset (Fin 5))).filter (·.card = 2),
        ∏ i, narayanaPolynomial (nlcVertex S i).toNat =
      X ^ 27 * ((1 + X) ^ 2 * (shiftedNarayanaPolynomial 22 + 9 * (1 + X) ^ 22)) := by
  have key : ((Finset.univ : Finset (Finset (Fin 5))).filter (·.card = 2)).val.map
      (fun S => (Finset.univ : Finset (Fin 27)).val.map fun i => (nlcVertex S i).toNat) =
      ((((23 :: List.replicate 21 1 ++ [2, 2, 1, 1, 1] : List ℕ) : Multiset ℕ) ::
        List.replicate 9 ((List.replicate 22 2 ++ [2, 2, 1, 1, 1] : List ℕ) : Multiset ℕ) :
          List (Multiset ℕ)) : Multiset (Multiset ℕ)) := by
    decide +kernel
  rw [Finset.sum_eq_multiset_sum,
    show (fun S : Finset (Fin 5) => ∏ i, narayanaPolynomial (nlcVertex S i).toNat) =
      (fun m : Multiset ℕ => (m.map narayanaPolynomial).prod) ∘
        (fun S => (Finset.univ : Finset (Fin 27)).val.map fun i => (nlcVertex S i).toNat) by
      funext S; simp [Finset.prod_eq_multiset_prod],
    ← Multiset.map_map, key]
  simp only [Multiset.map_coe, Multiset.sum_coe, Multiset.prod_coe, List.map_cons,
    List.map_append, List.map_replicate, List.prod_cons, List.prod_append, List.prod_replicate,
    List.map_nil, List.prod_nil, List.sum_cons, List.sum_replicate, nsmul_eq_mul,
    narayanaPolynomial_succ 22, sanity_narayana_one, sanity_narayana_two]
  push_cast
  ring

/-- The first three coefficients of `(1 + x)² (Ñ_22 + 9 (1 + x)^22)` are `10, 471, 22472`, and
`10 · 22472 > 471²`, so they violate log-concavity. -/
theorem sanity_nlc_coeffs :
    ((1 + X) ^ 2 * (shiftedNarayanaPolynomial 22 + 9 * (1 + X) ^ 22)).coeff 0 = 10 ∧
    ((1 + X) ^ 2 * (shiftedNarayanaPolynomial 22 + 9 * (1 + X) ^ 22)).coeff 1 = 471 ∧
    ((1 + X) ^ 2 * (shiftedNarayanaPolynomial 22 + 9 * (1 + X) ^ 22)).coeff 2 = 22472 ∧
    ¬ ((10 : ℝ) * 22472 ≤ 471 ^ 2) := by
  have e : (1 + X : ℝ[X]) ^ 2 * (shiftedNarayanaPolynomial 22 + 9 * (1 + X) ^ 22) =
      (shiftedNarayanaPolynomial 22 + 9 * (1 + X) ^ 22) +
        C 2 * (X * (shiftedNarayanaPolynomial 22 + 9 * (1 + X) ^ 22)) +
        X * (X * (shiftedNarayanaPolynomial 22 + 9 * (1 + X) ^ 22)) := by
    rw [show (C 2 : ℝ[X]) = 2 from rfl]
    ring
  have h9 : (9 : ℝ[X]) = C 9 := rfl
  have c0 : (shiftedNarayanaPolynomial 22).coeff 0 = 1 := by
    rw [coeff_shiftedNarayanaPolynomial]; norm_num [Nat.choose_one_right]
  have c1 : (shiftedNarayanaPolynomial 22).coeff 1 = 253 := by
    rw [coeff_shiftedNarayanaPolynomial, if_pos (by simp),
      show (23 : ℕ).choose 2 = 253 by decide]; norm_num
  have c2 : (shiftedNarayanaPolynomial 22).coeff 2 = 19481 := by
    rw [coeff_shiftedNarayanaPolynomial, if_pos (by simp),
      show (23 : ℕ).choose 3 = 1771 by decide, show (23 : ℕ).choose 2 = 253 by decide]; norm_num
  rw [e, h9]
  simp only [coeff_add, coeff_C_mul, coeff_X_mul, coeff_X_mul_zero, coeff_one_add_X_pow, c0, c1, c2]
  norm_num [Nat.choose]

end LogNarayanaSanity

/-! ## Log-concavity, ultra-log-concavity, Lorentzian and real-stable polynomials

Small positive and negative instances, proved from the definitions. -/

namespace LogNarayanaSanityLor

section Univariate

open Polynomial

/-! ### Ultra-log-concavity and log-concavity -/

/-- `1 + 2x + x²` is ultra-log-concave of order `2`. -/
theorem sanity_ulc_one_add_two_X_add_X_sq :
    (1 + 2 * X + X ^ 2 : ℝ[X]).IsUltraLogConcave 2 := by
  refine ⟨?_, ⟨?_, ?_⟩, ?_⟩
  · compute_degree!
  · intro j hj
    interval_cases j <;> simp [coeff_X, coeff_one, coeff_X_pow, Nat.choose]
  · intro j hj
    obtain rfl : j = 0 := by omega
    norm_num [coeff_X, coeff_one, coeff_X_pow, Nat.choose]
  · intro i j k hij hjk hk _ _
    obtain ⟨rfl, rfl, rfl⟩ : i = 0 ∧ j = 1 ∧ k = 2 := by omega
    norm_num [coeff_X, coeff_one, coeff_X_pow, Nat.choose]

/-- `1 + 3x + x²` is ultra-log-concave of order `2`. -/
theorem sanity_ulc_one_add_three_X_add_X_sq :
    (1 + 3 * X + X ^ 2 : ℝ[X]).IsUltraLogConcave 2 := by
  refine ⟨?_, ⟨?_, ?_⟩, ?_⟩
  · compute_degree!
  · intro j hj
    interval_cases j <;> norm_num [coeff_X, coeff_one, coeff_X_pow, Nat.choose]
  · intro j hj
    obtain rfl : j = 0 := by omega
    norm_num [coeff_X, coeff_one, coeff_X_pow, Nat.choose]
  · intro i j k hij hjk hk _ _
    obtain ⟨rfl, rfl, rfl⟩ : i = 0 ∧ j = 1 ∧ k = 2 := by omega
    norm_num [coeff_X, coeff_one, coeff_X_pow, Nat.choose]

/-- `1 + x + x²` is not ultra-log-concave of order `2`. -/
theorem sanity_not_ulc_one_add_X_add_X_sq :
    ¬ (1 + X + X ^ 2 : ℝ[X]).IsUltraLogConcave 2 := by
  rintro ⟨-, ⟨-, h⟩, -⟩
  have := h 0 le_rfl
  norm_num [coeff_X, coeff_one, coeff_X_pow, Nat.choose] at this

/-- `1 + x³` is not ultra-log-concave of order `3`: its coefficients have internal zeros. -/
theorem sanity_not_ulc_one_add_X_cube :
    ¬ (1 + X ^ 3 : ℝ[X]).IsUltraLogConcave 3 := by
  rintro ⟨-, -, h⟩
  have := h 0 1 3 (by norm_num) (by norm_num) le_rfl
    (by norm_num [coeff_one, coeff_X_pow]) (by norm_num [coeff_one, coeff_X_pow])
  norm_num [coeff_one, coeff_X_pow] at this

/-- `1 + x³` is log-concave. -/
theorem sanity_logConcave_one_add_X_cube :
    (1 + X ^ 3 : ℝ[X]).IsLogConcave := by
  refine ⟨fun j => ?_, fun j => ?_⟩
  · simp only [coeff_add, coeff_one, coeff_X_pow]
    split_ifs <;> norm_num
  · simp only [coeff_add, coeff_one, coeff_X_pow]
    rcases j with _ | _ | _ | j <;> simp

/-- `1 + 2x + x²` is not ultra-log-concave of order `1`, its degree being `2`. -/
theorem sanity_not_ulc_one_add_two_X_add_X_sq_order_one :
    ¬ (1 + 2 * X + X ^ 2 : ℝ[X]).IsUltraLogConcave 1 := by
  rintro ⟨h, -⟩
  have : (1 + 2 * X + X ^ 2 : ℝ[X]).natDegree = 2 := by compute_degree!
  omega

/-- The zero polynomial is ultra-log-concave of order `0`. -/
theorem sanity_ulc_zero : (0 : ℝ[X]).IsUltraLogConcave 0 := by
  refine ⟨by simp, ⟨fun j _ => by simp, fun j hj => by omega⟩, fun i j k _ _ _ hi _ => ?_⟩
  simp at hi

/-- `1 - x` is not log-concave, having a negative coefficient. -/
theorem sanity_not_logConcave_one_sub_X : ¬ (1 - X : ℝ[X]).IsLogConcave := by
  rintro ⟨h, -⟩
  have := h 1
  norm_num [coeff_one, coeff_X] at this

/-! ### Real stability and negative roots -/

/-- `z₀ + z₁` is real stable. -/
theorem sanity_realStable_X_add_X :
    (MvPolynomial.X 0 + MvPolynomial.X 1 : MvPolynomial (Fin 2) ℝ).IsRealStable := by
  intro ζ hζ h
  have h0 := hζ 0
  have h1 := hζ 1
  simp only [map_add, MvPolynomial.aeval_X] at h
  have := congrArg Complex.im h
  simp only [Complex.add_im, Complex.zero_im] at this
  linarith

/-- `z₀² + 1` is not real stable. -/
theorem sanity_not_realStable_X_sq_add_one :
    ¬ (MvPolynomial.X 0 ^ 2 + 1 : MvPolynomial (Fin 1) ℝ).IsRealStable := by
  intro h
  exact h (fun _ => Complex.I) (fun _ => by simp) (by simp)

/-- The zero polynomial is not real stable. -/
theorem sanity_not_realStable_zero : ¬ (0 : MvPolynomial (Fin 1) ℝ).IsRealStable := by
  intro h
  exact h (fun _ => Complex.I) (fun _ => by simp) (by simp)

/-- `x + 1` has only negative roots. -/
theorem sanity_hasOnlyNegativeRoots_X_add_one : (X + 1 : ℝ[X]).HasOnlyNegativeRoots := by
  have e : (X + 1 : ℝ[X]) = X + C 1 := by simp
  rw [e]
  refine ⟨Splits.X_add_C 1, ?_⟩
  rw [roots_X_add_C]
  intro r hr
  rw [Multiset.mem_singleton] at hr
  rw [hr]
  norm_num

/-- `x - 1` does not have only negative roots. -/
theorem sanity_not_hasOnlyNegativeRoots_X_sub_one : ¬ (X - 1 : ℝ[X]).HasOnlyNegativeRoots := by
  rintro ⟨-, h⟩
  have e : (X - 1 : ℝ[X]) = X - C 1 := by simp
  rw [e, roots_X_sub_C] at h
  have := h 1 (Multiset.mem_singleton_self _)
  norm_num at this

end Univariate

/-! ### Lorentzian polynomials: general lemmas -/

section LorentzianHelpers

open MvPolynomial Matrix

variable {σ : Type*}

/-- The factorial `α! = ∏_i (α i)!` of a finitely supported exponent is positive. -/
theorem factorial_pos (α : σ →₀ ℕ) : 0 < α.factorial :=
  Finset.prod_pos fun _ _ => Nat.factorial_pos _

/-- The factorial of the zero exponent is `1`. -/
theorem factorial_zero : (0 : σ →₀ ℕ).factorial = 1 := by
  simp [Finsupp.factorial]

/-- The iterated partial derivative `∂^α` of `c z^β` is `c β!/(β - α)! z^{β - α}` if `α ≤ β`,
and `0` otherwise. -/
theorem iteratedPDeriv_monomial (α β : σ →₀ ℕ) (c : ℝ) :
    iteratedPDeriv α (monomial β c : MvPolynomial σ ℝ) =
      monomial (β - α)
        (c * if α ≤ β then ((β.factorial / (β - α).factorial : ℕ) : ℝ) else 0) := by
  have h : (monomial β c : MvPolynomial σ ℝ) = c • basisMonomials σ ℝ β := by
      rw [MvPolynomial.coe_basisMonomials, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [h, map_smul]
  unfold iteratedPDeriv
  rw [Module.Basis.constr_basis, MvPolynomial.smul_monomial, smul_eq_mul]

/-- The constant coefficient of `∂^γ f` is `γ!` times the coefficient of `z^γ` in `f`. -/
theorem constantCoeff_iteratedPDeriv (γ : σ →₀ ℕ) (f : MvPolynomial σ ℝ) :
    constantCoeff (iteratedPDeriv γ f) = coeff γ f * γ.factorial := by
  classical
  refine MvPolynomial.induction_on' f (fun β c => ?_) (fun p q hp hq => ?_)
  · rw [iteratedPDeriv_monomial, constantCoeff_monomial, MvPolynomial.coeff_monomial]
    by_cases hβ : β = γ
    · subst hβ
      simp
    · rw [if_neg hβ, zero_mul]
      split_ifs with h1 h2
      · exact absurd (le_antisymm (tsub_eq_zero_iff_le.mp h1) h2) hβ
      · simp
      · rfl
  · simp [hp, hq, add_mul]

/-- `∂^0 f = f`. -/
theorem iteratedPDeriv_zero (f : MvPolynomial σ ℝ) : iteratedPDeriv 0 f = f := by
  refine MvPolynomial.induction_on' f (fun β c => ?_) (fun p q hp hq => ?_)
  · rw [iteratedPDeriv_monomial]
    simp [Nat.div_self (factorial_pos β)]
  · rw [map_add, hp, hq]

/-- The `(i, j)` entry of the Hessian of `f` at `0` is the coefficient of `z_i z_j` in `f`
times `(e_i + e_j)!`. -/
theorem hessianAtZero_apply (f : MvPolynomial σ ℝ) (i j : σ) :
    hessianAtZero f i j =
      coeff (Finsupp.single i 1 + Finsupp.single j 1) f *
        (Finsupp.single i 1 + Finsupp.single j 1).factorial := by
  simp [hessianAtZero, constantCoeff_iteratedPDeriv]

/-- In two variables, `α! = (α 0)! (α 1)!`. -/
theorem factorial_fin_two (α : Fin 2 →₀ ℕ) : α.factorial = (α 0).factorial * (α 1).factorial := by
  rw [Finsupp.factorial, Finsupp.prod_fintype _ _ (fun _ => Nat.factorial_zero),
    Fin.prod_univ_two]

/-- In two variables, the degree of `α` is `α 0 + α 1`. -/
theorem degree_fin_two (α : Fin 2 →₀ ℕ) : α.degree = α 0 + α 1 := by
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_two]

/-- Two exponents in two variables are equal iff their coordinates are. -/
theorem finsupp_fin_two_eq_iff (β α : Fin 2 →₀ ℕ) : β = α ↔ β 0 = α 0 ∧ β 1 = α 1 := by
  rw [Finsupp.ext_iff, Fin.forall_fin_two]

/-- A `2 × 2` real matrix whose quadratic form is nonpositive at some nonzero vector has
positive index at most `1`. -/
theorem posIndex_le_one_of_fin_two (A : Matrix (Fin 2) (Fin 2) ℝ) (v : Fin 2 → ℝ) (hv : v ≠ 0)
    (h : v ⬝ᵥ (A *ᵥ v) ≤ 0) : A.posIndex ≤ 1 := by
  unfold Matrix.posIndex
  refine csSup_le ⟨0, ⊥, fun w hw hw0 => absurd ((Submodule.mem_bot ℝ).mp hw) hw0,
    finrank_bot ℝ _⟩ ?_
  rintro n ⟨W, hW, rfl⟩
  by_contra hn
  push Not at hn
  have hle : Module.finrank ℝ W ≤ 2 := by simpa using Submodule.finrank_le W
  have htop : W = ⊤ := Submodule.eq_top_of_finrank_eq (by simp; omega)
  have := hW v (htop ▸ Submodule.mem_top) hv
  linarith

/-- A positive definite `2 × 2` real matrix has positive index at least `2`. -/
theorem two_le_posIndex_of_fin_two (A : Matrix (Fin 2) (Fin 2) ℝ)
    (h : ∀ v : Fin 2 → ℝ, v ≠ 0 → 0 < v ⬝ᵥ (A *ᵥ v)) : 2 ≤ A.posIndex := by
  unfold Matrix.posIndex
  refine le_csSup ⟨2, ?_⟩ ⟨⊤, fun v _ hv => h v hv, by simp⟩
  rintro n ⟨W, -, rfl⟩
  simpa using Submodule.finrank_le W

/-- A nonzero homogeneous quadratic whose Hessian has positive index at least `2` is not
Lorentzian. -/
theorem not_isLorentzian_of_two_le_posIndex (f : MvPolynomial (Fin 2) ℝ) (hf0 : f ≠ 0)
    (hf : f.IsHomogeneous 2) (hH : 2 ≤ (hessianAtZero f).posIndex) : ¬ f.IsLorentzian := by
  rintro (h0 | ⟨d, hd, -, hcase⟩)
  · exact hf0 h0
  obtain rfl : d = 2 := hd.inj_right hf hf0
  rcases hcase with h | ⟨-, -, h⟩
  · omega
  have := h 0 (by simp)
  rw [iteratedPDeriv_zero] at this
  exact absurd this (by unfold Matrix.HasAtMostOnePosEigenvalue; omega)

/-- A nonzero homogeneous quadratic whose support is not M-convex is not Lorentzian. -/
theorem not_isLorentzian_of_not_mconvex (f : MvPolynomial (Fin 2) ℝ) (hf0 : f ≠ 0)
    (hf : f.IsHomogeneous 2) (hS : ¬ (f.support : Set (Fin 2 →₀ ℕ)).IsMConvex) :
    ¬ f.IsLorentzian := by
  rintro (h0 | ⟨d, hd, -, hcase⟩)
  · exact hf0 h0
  obtain rfl : d = 2 := hd.inj_right hf hf0
  rcases hcase with h | ⟨-, h, -⟩
  · omega
  · exact hS h

/-- A finite set of exponents in two variables consisting of all exponents of degree `2` is
M-convex. -/
theorem isMConvex_of_degree_two (s : Finset (Fin 2 →₀ ℕ)) (hs : ∀ α, α ∈ s ↔ α 0 + α 1 = 2) :
    (s : Set (Fin 2 →₀ ℕ)).IsMConvex := by
  refine ⟨s.finite_toSet, ⟨Finsupp.single 0 2, (hs _).2 (by simp)⟩,
    ⟨2, fun α hα => by rw [degree_fin_two]; exact (hs α).1 hα⟩, ?_⟩
  intro α hα β hβ i hi
  have ha := (hs α).1 hα
  have hb := (hs β).1 hβ
  fin_cases i
  · refine ⟨1, ?_, (hs _).2 ?_, (hs _).2 ?_⟩
    · simp at hi; omega
    · simp at hi ⊢; omega
    · simp at hi ⊢; omega
  · refine ⟨0, ?_, (hs _).2 ?_, (hs _).2 ?_⟩
    · simp at hi; omega
    · simp at hi ⊢; omega
    · simp at hi ⊢; omega

end LorentzianHelpers

/-! ### Lorentzian polynomials: instances in two variables -/

section LorentzianInstances

open MvPolynomial Matrix

/-- The quadratic form `v ⬝ᵥ A v` of a `2 × 2` matrix, written out in coordinates. -/
theorem quadForm_fin_two (A : Matrix (Fin 2) (Fin 2) ℝ) (v : Fin 2 → ℝ) :
    v ⬝ᵥ (A *ᵥ v) = v 0 * (A 0 0 * v 0 + A 0 1 * v 1) + v 1 * (A 1 0 * v 0 + A 1 1 * v 1) := by
  simp [dotProduct, mulVec, Fin.sum_univ_two]

/-- `z₀ z₁` is the monomial with exponent `e₀ + e₁`. -/
theorem X_zero_mul_X_one :
    (X 0 * X 1 : MvPolynomial (Fin 2) ℝ) =
      monomial (Finsupp.single 0 1 + Finsupp.single 1 1) 1 := by
  change monomial _ 1 * monomial _ 1 = _
  rw [monomial_mul, one_mul]

/-- The coefficient of `z^α` in `z₀ z₁` is `1` if `α = (1, 1)`, and `0` otherwise. -/
theorem coeff_X_zero_mul_X_one (α : Fin 2 →₀ ℕ) :
    coeff α (X 0 * X 1 : MvPolynomial (Fin 2) ℝ) = if α 0 = 1 ∧ α 1 = 1 then 1 else 0 := by
  rw [X_zero_mul_X_one, MvPolynomial.coeff_monomial]
  simp only [finsupp_fin_two_eq_iff]
  simp [eq_comm]

/-- The coefficient of `z^α` in `z_i²` is `1` if `α i = 2` and the other coordinate is `0`, and
`0` otherwise. -/
theorem coeff_X_sq (i : Fin 2) (α : Fin 2 →₀ ℕ) :
    coeff α (X i ^ 2 : MvPolynomial (Fin 2) ℝ) =
      if α i = 2 ∧ α (1 - i) = 0 then 1 else 0 := by
  rw [X_pow_eq_monomial, MvPolynomial.coeff_monomial]
  simp only [finsupp_fin_two_eq_iff]
  fin_cases i <;> simp [eq_comm, and_comm]

/-- The coefficients of `(z₀ + z₁)²` are `1, 2, 1` at the exponents `(2, 0), (1, 1), (0, 2)`. -/
theorem coeff_add_sq (α : Fin 2 →₀ ℕ) :
    coeff α ((X 0 + X 1) ^ 2 : MvPolynomial (Fin 2) ℝ) =
      (if α 0 = 2 ∧ α 1 = 0 then 1 else 0) + 2 * (if α 0 = 1 ∧ α 1 = 1 then 1 else 0) +
        (if α 1 = 2 ∧ α 0 = 0 then 1 else 0) := by
  have e : ((X 0 + X 1) ^ 2 : MvPolynomial (Fin 2) ℝ) =
      X 0 ^ 2 + C 2 * (X 0 * X 1) + X 1 ^ 2 := by
    simp only [map_ofNat]
    ring
  rw [e, coeff_add, coeff_add, coeff_C_mul, coeff_X_sq, coeff_X_sq, coeff_X_zero_mul_X_one]
  simp

/-- The coefficients of `z₀² + z₀ z₁ + z₁²` are `1` at the exponents `(2, 0), (1, 1), (0, 2)`. -/
theorem coeff_sq_add_mul_add_sq (α : Fin 2 →₀ ℕ) :
    coeff α (X 0 ^ 2 + X 0 * X 1 + X 1 ^ 2 : MvPolynomial (Fin 2) ℝ) =
      (if α 0 = 2 ∧ α 1 = 0 then 1 else 0) + (if α 0 = 1 ∧ α 1 = 1 then 1 else 0) +
        (if α 1 = 2 ∧ α 0 = 0 then 1 else 0) := by
  rw [coeff_add, coeff_add, coeff_X_sq, coeff_X_sq, coeff_X_zero_mul_X_one]
  simp

/-- The coefficients of `z₀² + z₁²` are `1` at the exponents `(2, 0)` and `(0, 2)`. -/
theorem coeff_sq_add_sq (α : Fin 2 →₀ ℕ) :
    coeff α (X 0 ^ 2 + X 1 ^ 2 : MvPolynomial (Fin 2) ℝ) =
      (if α 0 = 2 ∧ α 1 = 0 then 1 else 0) + (if α 1 = 2 ∧ α 0 = 0 then 1 else 0) := by
  rw [coeff_add, coeff_X_sq, coeff_X_sq]
  simp

/-- `(z₀ + z₁)²` is Lorentzian. -/
theorem sanity_isLorentzian_add_sq :
    ((X 0 + X 1) ^ 2 : MvPolynomial (Fin 2) ℝ).IsLorentzian := by
  refine Or.inr ⟨2, ?_, ?_, Or.inr ⟨le_rfl, ?_, ?_⟩⟩
  · simpa using ((isHomogeneous_X ℝ (0 : Fin 2)).add (isHomogeneous_X ℝ 1)).pow 2
  · intro α
    rw [coeff_add_sq]
    split_ifs <;> norm_num
  · apply isMConvex_of_degree_two
    intro α
    rw [mem_support_iff, coeff_add_sq]
    split_ifs <;> simp_all
    all_goals omega
  · intro α hα
    rw [(Finsupp.degree_eq_zero_iff α).1 (by simpa using hα), iteratedPDeriv_zero]
    refine posIndex_le_one_of_fin_two _ ![1, -1] (fun h => by simpa using congrFun h 0) ?_
    rw [quadForm_fin_two]
    simp [hessianAtZero_apply, coeff_add_sq, factorial_fin_two]

/-- `z₀ z₁` is Lorentzian. -/
theorem sanity_isLorentzian_X_zero_mul_X_one :
    (X 0 * X 1 : MvPolynomial (Fin 2) ℝ).IsLorentzian := by
  refine Or.inr ⟨2, ?_, ?_, Or.inr ⟨le_rfl, ?_, ?_⟩⟩
  · exact (isHomogeneous_X ℝ (0 : Fin 2)).mul (isHomogeneous_X ℝ 1)
  · intro α
    rw [coeff_X_zero_mul_X_one]
    split_ifs <;> norm_num
  · have hS : ∀ α, α ∈ ((X 0 * X 1 : MvPolynomial (Fin 2) ℝ).support : Set (Fin 2 →₀ ℕ)) ↔
        α 0 = 1 ∧ α 1 = 1 := by
      intro α
      rw [Finset.mem_coe, mem_support_iff, coeff_X_zero_mul_X_one]
      split_ifs with h <;> simp [h]
    refine ⟨Finset.finite_toSet _, ⟨Finsupp.single 0 1 + Finsupp.single 1 1, (hS _).2 ?_⟩,
      ⟨2, fun α hα => ?_⟩, fun α hα β hβ i hi => ?_⟩
    · simp
    · rw [degree_fin_two]
      have := (hS α).1 hα
      omega
    · have ha := (hS α).1 hα
      have hb := (hS β).1 hβ
      fin_cases i <;> simp at hi <;> omega
  · intro α hα
    rw [(Finsupp.degree_eq_zero_iff α).1 (by simpa using hα), iteratedPDeriv_zero]
    refine posIndex_le_one_of_fin_two _ ![1, 0] (fun h => by simpa using congrFun h 0) ?_
    rw [quadForm_fin_two]
    simp [hessianAtZero_apply, coeff_X_zero_mul_X_one, factorial_fin_two]

/-- `z₀² + z₁²` is not Lorentzian: its support is not M-convex. -/
theorem sanity_not_isLorentzian_sq_add_sq :
    ¬ (X 0 ^ 2 + X 1 ^ 2 : MvPolynomial (Fin 2) ℝ).IsLorentzian := by
  apply not_isLorentzian_of_not_mconvex
  · intro h
    have := congrArg (coeff (Finsupp.single 0 2)) h
    rw [coeff_sq_add_sq, coeff_zero] at this
    simp at this
  · exact (isHomogeneous_X_pow _ _).add (isHomogeneous_X_pow _ _)
  · rintro ⟨-, -, -, h⟩
    obtain ⟨j, hj, h1, -⟩ := h (Finsupp.single 0 2)
      (by simp only [Finset.mem_coe, mem_support_iff, coeff_sq_add_sq]; simp)
      (Finsupp.single 1 2)
      (by simp only [Finset.mem_coe, mem_support_iff, coeff_sq_add_sq]; simp) 0 (by simp)
    fin_cases j
    · simp at hj
    · simp only [Finset.mem_coe, mem_support_iff, coeff_sq_add_sq] at h1
      simp at h1

/-- `z₀² + z₀ z₁ + z₁²` is not Lorentzian: its Hessian is positive definite. -/
theorem sanity_not_isLorentzian_sq_add_mul_add_sq :
    ¬ (X 0 ^ 2 + X 0 * X 1 + X 1 ^ 2 : MvPolynomial (Fin 2) ℝ).IsLorentzian := by
  apply not_isLorentzian_of_two_le_posIndex
  · intro h
    have := congrArg (coeff (Finsupp.single 0 2)) h
    rw [coeff_sq_add_mul_add_sq, coeff_zero] at this
    simp at this
  · exact ((isHomogeneous_X_pow _ _).add
      ((isHomogeneous_X ℝ (0 : Fin 2)).mul (isHomogeneous_X ℝ 1))).add (isHomogeneous_X_pow _ _)
  · apply two_le_posIndex_of_fin_two
    intro v hv
    rw [quadForm_fin_two]
    simp only [hessianAtZero_apply, coeff_sq_add_mul_add_sq, factorial_fin_two]
    simp
    have hpos : 0 < v 0 ^ 2 + v 1 ^ 2 := by
      by_contra hc
      apply hv
      ext i
      fin_cases i <;> simp <;> nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
    nlinarith [sq_nonneg (v 0 + v 1)]

/-- The zero polynomial is Lorentzian. -/
theorem sanity_isLorentzian_zero : (0 : MvPolynomial (Fin 2) ℝ).IsLorentzian := Or.inl rfl

/-- The constant polynomial `3` is Lorentzian. -/
theorem sanity_isLorentzian_C_three : (C 3 : MvPolynomial (Fin 2) ℝ).IsLorentzian := by
  refine Or.inr ⟨0, isHomogeneous_C _ _, fun α => ?_, Or.inl (by norm_num)⟩
  rw [coeff_C]
  split_ifs <;> norm_num

/-- `z₀ - z₁` is not Lorentzian, having a negative coefficient. -/
theorem sanity_not_isLorentzian_X_sub_X :
    ¬ (X 0 - X 1 : MvPolynomial (Fin 2) ℝ).IsLorentzian := by
  have hc : coeff (Finsupp.single 1 1) (X 0 - X 1 : MvPolynomial (Fin 2) ℝ) = -1 := by
    simp [coeff_X, Finsupp.single_eq_single_iff]
  rintro (h | ⟨d, -, hn, -⟩)
  · rw [h, coeff_zero] at hc
    norm_num at hc
  · have := hn (Finsupp.single 1 1)
    rw [hc] at this
    norm_num at this

end LorentzianInstances

end LogNarayanaSanityLor

/-!
## Sanity checks of the noncrossing and Schur definitions on small cases

Small values of `restrictedNoncrossingRefinementPoly`, `restrictedNoncrossingDeformedNarayanaPoly`,
the instance `n = 3` of the cited Kreweras count, and Kostka numbers, Schur polynomials and
their Narayana transforms for one-row shapes with `r = 2`, all computed from the definitions.
-/

namespace LogNarayanaSanityNC

open Finset Polynomial

section Compute

/-- Noncrossingness of a finpartition of a finset of naturals, decided by its definition. -/
abbrev decNC (s : Finset ℕ) : DecidablePred (fun P : Finpartition s => P.IsNoncrossing) :=
  fun P => inferInstanceAs (Decidable (∀ B ∈ P.parts, ∀ B' ∈ P.parts, B ≠ B' →
    ∀ a ∈ B, ∀ c ∈ B, ∀ b ∈ B', ∀ d ∈ B', ¬ (a < b ∧ b < c ∧ c < d)))

/-- Refinement of finpartitions, decided by its definition. -/
abbrev decLE (s : Finset ℕ) (P Q : Finpartition s) : Decidable (P ≤ Q) :=
  inferInstanceAs (Decidable (∀ b ∈ P.parts, ∃ c ∈ Q.parts, b ⊆ c))

/-- Equality of finpartitions, decided on their parts. -/
abbrev decEqFP (s : Finset ℕ) : DecidableEq (Finpartition s) := fun P Q =>
  decidable_of_iff (P.parts = Q.parts) Finpartition.ext_iff.symm

attribute [local instance] decNC decLE decEqFP

/-- The fibres of `f : s → ℕ`, as a family of subsets of `s`. -/
def fibres (s : Finset ℕ) (f : ∀ a ∈ s, ℕ) : Finset (Finset ℕ) :=
  s.attach.image fun x => (s.attach.filter fun y => f y.1 y.2 = f x.1 x.2).map
    (Function.Embedding.subtype _)

/-- The finpartition of `s` into the fibres of `f`, or `⊤` if they do not form one. -/
def ofFibres (s : Finset ℕ) (f : ∀ a ∈ s, ℕ) : Finpartition s :=
  if h : (fibres s f).sup id = s ∧ ⊥ ∉ fibres s f ∧ (fibres s f).SupIndep id then
    ⟨_, h.2.2, h.1, h.2.1⟩
  else ⊤

/-- Equal nonempty finsets have equal minima. -/
lemma sanity_min'_congr {A B : Finset ℕ} (hA : A.Nonempty) (hB : B.Nonempty) (h : A = B) :
    A.min' hA = B.min' hB := by
  subst h
  rfl

/-- An enumeration of the finpartitions of `s` by the least element of the part of each `a`:
a function `f` with `f a ≤ a`, so `∏_{a ∈ s} |{b ∈ s | b ≤ a}|` candidates. -/
theorem sanity_univ_eq_image (s : Finset ℕ) :
    (univ : Finset (Finpartition s)) =
      (s.pi fun a => s.filter (· ≤ a)).image (ofFibres s) := by
  refine (Finset.eq_univ_of_forall fun P => ?_).symm
  rw [Finset.mem_image]
  let f : ∀ a ∈ s, ℕ := fun a ha => (P.part a).min' ⟨a, P.mem_part ha⟩
  have hf : ∀ a (ha : a ∈ s) b (hb : b ∈ s), f b hb = f a ha ↔ b ∈ P.part a := by
    intro a ha b hb
    refine ⟨fun h => ?_, fun h => sanity_min'_congr _ _ (P.part_eq_of_mem (P.part_mem.2 ha) h)⟩
    have h1 : f b hb ∈ P.part b := Finset.min'_mem _ _
    have h2 : f a ha ∈ P.part a := Finset.min'_mem _ _
    rw [h] at h1
    exact P.eq_of_mem_parts (P.part_mem.2 hb) (P.part_mem.2 ha) h1 h2 ▸ P.mem_part hb
  refine ⟨f, Finset.mem_pi.2 fun a ha => Finset.mem_filter.2
    ⟨P.part_subset a (Finset.min'_mem _ _), Finset.min'_le _ _ (P.mem_part ha)⟩, ?_⟩
  have hps : fibres s f = P.parts := by
    have hx : ∀ x : s, ((s.attach.filter fun y => f y.1 y.2 = f x.1 x.2).map
        (Function.Embedding.subtype _)) = P.part x.1 := by
      intro x
      ext b
      simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_attach, true_and,
        Function.Embedding.coe_subtype, Subtype.exists, exists_and_right, exists_eq_right]
      exact ⟨fun ⟨hb, h⟩ => (hf x.1 x.2 b hb).1 h,
        fun h => ⟨P.part_subset x.1 h, (hf x.1 x.2 b (P.part_subset x.1 h)).2 h⟩⟩
    ext t
    simp only [fibres, hx, Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists]
    refine ⟨fun ⟨x, hx, h⟩ => h ▸ P.part_mem.2 hx, fun ht => ?_⟩
    obtain ⟨x, hx, hxt⟩ := P.part_surjOn ht
    exact ⟨x, hx, hxt⟩
  unfold ofFibres
  rw [dif_pos (by rw [hps]; exact ⟨P.sup_parts, P.bot_notMem, P.supIndep⟩)]
  ext t
  simp only [hps]

/-- The multiset of block counts `|σ|` over the pairs `(τ, σ)` of the double sum. -/
def refinementCounts (s : Finset ℕ) (a k : ℕ) : Multiset ℕ :=
  (univ.filter (fun τ : Finpartition s =>
      τ.IsNoncrossing ∧ τ.blockCount = k ∧ ∀ B ∈ τ.parts, a ≤ B.card)).val.bind fun τ =>
    (univ.filter (fun σ : Finpartition s => σ.IsNoncrossing ∧ σ ≤ τ)).val.map
      (fun σ => σ.blockCount)

/-- `restrictedNoncrossingRefinementPoly R s a k` is `∑ x^n` over the multiset
`refinementCounts s a k`. -/
theorem sanity_refinementPoly_eq (R : Type*) [CommSemiring R] (s : Finset ℕ) (a k : ℕ) :
    restrictedNoncrossingRefinementPoly R s a k =
      ((refinementCounts s a k).map fun n => (X : R[X]) ^ n).sum := by
  unfold restrictedNoncrossingRefinementPoly refinementCounts
  simp only [Finset.sum_eq_multiset_sum, Multiset.map_bind, Multiset.sum_bind, Multiset.map_map]
  congr!

/-- The multiset of block-size multisets of the partitions `τ` of the outer sum. -/
def blockSizes (s : Finset ℕ) (a k : ℕ) : Multiset (Multiset ℕ) :=
  (univ.filter (fun τ : Finpartition s =>
      τ.IsNoncrossing ∧ τ.blockCount = k ∧ ∀ B ∈ τ.parts, a ≤ B.card)).val.map fun τ =>
    τ.parts.val.map Finset.card

/-- `restrictedNoncrossingDeformedNarayanaPoly R lam s a k` is the sum, over the multiset
`blockSizes s a k`, of the products of `N^{(lam)}_b` over the block sizes `b`. -/
theorem sanity_deformedPoly_eq (R : Type*) [CommSemiring R] (lam : R) (s : Finset ℕ) (a k : ℕ) :
    restrictedNoncrossingDeformedNarayanaPoly R lam s a k =
      ((blockSizes s a k).map fun m => (m.map (deformedNarayanaPolynomial R lam)).prod).sum := by
  unfold restrictedNoncrossingDeformedNarayanaPoly blockSizes
  simp only [Finset.sum_eq_multiset_sum, Finset.prod_eq_multiset_prod, Multiset.map_map]
  congr!
  simp [Multiset.map_map]

/-- The number of noncrossing partitions of `[3]` with `m₁, m₂, m₃` blocks of sizes `1, 2, 3`. -/
def krewerasCount3 (m₁ m₂ m₃ : ℕ) : ℕ :=
  (univ.filter (fun ρ : Finpartition (Icc 1 3) => ρ.IsNoncrossing ∧
    (ρ.parts.filter (fun B => B.card = 1)).card = m₁ ∧
    (ρ.parts.filter (fun B => B.card = 2)).card = m₂ ∧
    (ρ.parts.filter (fun B => B.card = 3)).card = m₃)).card

/-- The block counts of the noncrossing partitions of `[3]`. -/
theorem sanity_refinementCounts_3_1_1 : refinementCounts (Icc 1 3) 1 1 = {1, 2, 2, 2, 3} := by
  rw [refinementCounts, sanity_univ_eq_image]; decide +kernel

/-- The block counts of the double sum for `s = [3]`, `a = 1`, `k = 2`. -/
theorem sanity_refinementCounts_3_1_2 : refinementCounts (Icc 1 3) 1 2 = {2, 3, 2, 3, 2, 3} := by
  rw [refinementCounts, sanity_univ_eq_image]; decide +kernel

/-- The block counts of the noncrossing partitions of `[4]`. -/
theorem sanity_refinementCounts_4_1_1 :
    refinementCounts (Icc 1 4) 1 1 = {1, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 4} := by
  rw [refinementCounts, sanity_univ_eq_image]; decide +kernel

/-- The block counts of the double sum for `s = [4]`, `a = 2`, `k = 2`. -/
theorem sanity_refinementCounts_4_2_2 : refinementCounts (Icc 1 4) 2 2 =
    {2, 3, 3, 4, 2, 3, 3, 4} := by
  rw [refinementCounts, sanity_univ_eq_image]; decide +kernel

/-- The block counts of the `42` noncrossing partitions of `[5]`, with multiplicities
`1, 10, 20, 10, 1`. -/
theorem sanity_refinementCounts_5_1_1 :
    refinementCounts (Icc 1 5) 1 1 = Multiset.replicate 1 1 + Multiset.replicate 10 2 +
      Multiset.replicate 20 3 + Multiset.replicate 10 4 + Multiset.replicate 1 5 := by
  rw [refinementCounts, sanity_univ_eq_image]; decide +kernel

/-- The noncrossing partitions of `[3]` into two blocks have block sizes `{1, 2}`, three times. -/
theorem sanity_blockSizes_3_1_2 : blockSizes (Icc 1 3) 1 2 = {{1, 2}, {1, 2}, {1, 2}} := by
  rw [blockSizes, sanity_univ_eq_image]; decide +kernel

/-- There is `1` noncrossing partition of `[3]` with three singletons, `3` with one singleton
and one pair, and `1` with a single block. -/
theorem sanity_krewerasCount3_values :
    krewerasCount3 3 0 0 = 1 ∧ krewerasCount3 1 1 0 = 3 ∧ krewerasCount3 0 0 1 = 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> (rw [krewerasCount3, sanity_univ_eq_image]; decide +kernel)

/-- The number of noncrossing partitions of `[4]` is the Catalan number `14`, of all
partitions of `[4]` the Bell number `15`. -/
theorem sanity_card_noncrossing_Icc4 :
    (univ.filter (fun P : Finpartition (Icc 1 4) => P.IsNoncrossing)).card = 14 ∧
      (univ : Finset (Finpartition (Icc 1 4))).card = 15 := by
  rw [sanity_univ_eq_image]; decide +kernel

end Compute

/-- The crossing partition `{1,3}{2,4}` of `[4]` is not noncrossing. -/
theorem sanity_not_isNoncrossing_13_24 (P : Finpartition (Icc 1 4))
    (hP : P.parts = {{1, 3}, {2, 4}}) : ¬ P.IsNoncrossing := by
  intro h
  exact h {1, 3} (by simp [hP]) {2, 4} (by simp [hP]) (by decide) 1 (by simp) 3 (by simp)
    2 (by simp) 4 (by simp) (by decide)

/-! ### Restricted noncrossing sums and Kreweras' count -/

/-- `R^{(1)}_{3,2} = 3x² + 3x³`, matching Edelman's `(1/n) C(n,k-1) C(n,ℓ-k) C(n,n-ℓ)`. -/
theorem sanity_refinementPoly_Icc3_a1_k2 :
    restrictedNoncrossingRefinementPoly ℝ (Icc 1 3) 1 2 = 3 * X ^ 2 + 3 * X ^ 3 := by
  rw [sanity_refinementPoly_eq, sanity_refinementCounts_3_1_2]
  simp
  ring

/-- `R^{(1)}_{3,1} = N_3 = x + 3x² + x³`. -/
theorem sanity_refinementPoly_Icc3_a1_k1 :
    restrictedNoncrossingRefinementPoly ℝ (Icc 1 3) 1 1 = X + 3 * X ^ 2 + X ^ 3 := by
  rw [sanity_refinementPoly_eq, sanity_refinementCounts_3_1_1]
  simp
  ring

/-- `R^{(1)}_{4,1} = N_4 = x + 6x² + 6x³ + x⁴` (14 noncrossing partitions of `[4]`). -/
theorem sanity_refinementPoly_Icc4_a1_k1 :
    restrictedNoncrossingRefinementPoly ℝ (Icc 1 4) 1 1 = X + 6 * X ^ 2 + 6 * X ^ 3 + X ^ 4 := by
  rw [sanity_refinementPoly_eq, sanity_refinementCounts_4_1_1]
  simp
  ring

/-- `R^{(2)}_{4,2} = 2 (x + x²)²`: `τ ∈ {12|34, 14|23}`, `13|24` crossing. -/
theorem sanity_refinementPoly_Icc4_a2_k2 :
    restrictedNoncrossingRefinementPoly ℝ (Icc 1 4) 2 2 = 2 * (X + X ^ 2) ^ 2 := by
  rw [sanity_refinementPoly_eq, sanity_refinementCounts_4_2_2]
  simp
  ring

/-- `R^{(1)}_{5,1} = N_5 = x + 10x² + 20x³ + 10x⁴ + x⁵` (42 noncrossing partitions of `[5]`). -/
theorem sanity_refinementPoly_Icc5_a1_k1 :
    restrictedNoncrossingRefinementPoly ℝ (Icc 1 5) 1 1 =
      X + 10 * X ^ 2 + 20 * X ^ 3 + 10 * X ^ 4 + X ^ 5 := by
  rw [sanity_refinementPoly_eq, sanity_refinementCounts_5_1_1]
  simp [Multiset.replicate_succ]
  ring

/-- `N^{(1)}_1 = x`. -/
theorem sanity_deformedNarayana_one :
    deformedNarayanaPolynomial ℝ 1 1 = X := by
  simp [deformedNarayanaPolynomial, narayanaQ]

/-- `N^{(1)}_2 = x (1 + x)`. -/
theorem sanity_deformedNarayana_two :
    deformedNarayanaPolynomial ℝ 1 2 = X * (1 + X) := by
  simp [deformedNarayanaPolynomial, narayanaQ]

/-- `R^{(1),1}_{3,2} = R^{(1)}_{3,2}`. -/
theorem sanity_deformedPoly_Icc3_a1_k2 :
    restrictedNoncrossingDeformedNarayanaPoly ℝ 1 (Icc 1 3) 1 2 =
      restrictedNoncrossingRefinementPoly ℝ (Icc 1 3) 1 2 := by
  rw [sanity_refinementPoly_Icc3_a1_k2, sanity_deformedPoly_eq, sanity_blockSizes_3_1_2]
  simp [sanity_deformedNarayana_one, sanity_deformedNarayana_two]
  ring

open Classical in
/-- The instance `n = 3` of `Finpartition.KrewerasBlockSizeCount`, for every `m`. -/
theorem sanity_kreweras_Icc3 : ∀ m : ℕ → ℕ, ∑ j ∈ Icc 1 3, j * m j = 3 →
    (univ.filter (fun ρ : Finpartition (Icc 1 3) => ρ.IsNoncrossing ∧
        ∀ j ∈ Icc 1 3, (ρ.parts.filter (fun B => B.card = j)).card = m j)).card *
      ((3 - ∑ j ∈ Icc 1 3, m j + 1).factorial * ∏ j ∈ Icc 1 3, (m j).factorial) =
      (3 : ℕ).factorial := by
  intro m hm
  have hI : Icc 1 3 = {1, 2, 3} := by decide
  have hm' : m 1 + 2 * m 2 + 3 * m 3 = 3 := by
    rw [hI] at hm; simp at hm; omega
  have hsum : ∑ j ∈ Icc 1 3, m j = m 1 + m 2 + m 3 := by
    rw [hI]
    simp
    ring
  have hprod : ∏ j ∈ Icc 1 3, (m j).factorial =
      (m 1).factorial * (m 2).factorial * (m 3).factorial := by
    rw [hI]
    simp
    ring
  have hj : ∀ j, j ∈ Icc 1 3 ↔ j = 1 ∨ j = 2 ∨ j = 3 := by intro j; simp; omega
  have hcard : (univ.filter (fun ρ : Finpartition (Icc 1 3) => ρ.IsNoncrossing ∧
        ∀ j ∈ Icc 1 3, (ρ.parts.filter (fun B => B.card = j)).card = m j)).card =
      krewerasCount3 (m 1) (m 2) (m 3) := by
    unfold krewerasCount3
    refine congrArg Finset.card (Finset.ext fun ρ => ?_)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hj, forall_eq_or_imp, forall_eq]
  rw [hcard, hsum, hprod]
  obtain ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ :
      (m 1 = 3 ∧ m 2 = 0 ∧ m 3 = 0) ∨ (m 1 = 1 ∧ m 2 = 1 ∧ m 3 = 0) ∨
        (m 1 = 0 ∧ m 2 = 0 ∧ m 3 = 1) := by omega
  all_goals rw [h1, h2, h3]
  · rw [sanity_krewerasCount3_values.1]
    decide
  · rw [sanity_krewerasCount3_values.2.1]
    decide
  · rw [sanity_krewerasCount3_values.2.2]
    decide

/-- `Finpartition.KrewerasBlockSizeCount` implies its instance `n = 3`. -/
theorem sanity_kreweras_Icc3_is_instance (h : Finpartition.KrewerasBlockSizeCount) :
    ∀ m : ℕ → ℕ, ∑ j ∈ Icc 1 3, j * m j = 3 →
    (open scoped Classical in (univ.filter (fun ρ : Finpartition (Icc 1 3) => ρ.IsNoncrossing ∧
        ∀ j ∈ Icc 1 3, (ρ.parts.filter (fun B => B.card = j)).card = m j)).card) *
      ((3 - ∑ j ∈ Icc 1 3, m j + 1).factorial * ∏ j ∈ Icc 1 3, (m j).factorial) =
      (3 : ℕ).factorial :=
  h 3

/-! ### Kostka numbers, Schur polynomials and their Narayana transforms, `r = 2` -/

section Schur

open PartitionAtMostParts

/-- The Young diagram of the one-row shape `(1)` has the single cell `(0, 0)`. -/
theorem sanity_cells_row_2_1 : (row 2 1).youngDiagram.cells = {(0, 0)} := by decide +kernel

/-- The Young diagram of the one-row shape `(2)` has the cells `(0, 0), (0, 1)`. -/
theorem sanity_cells_row_2_2 : (row 2 2).youngDiagram.cells = {(0, 0), (0, 1)} := by decide +kernel

/-- `(i, j)` is a cell of the shape `(1)` iff `i = j = 0`. -/
theorem sanity_mem_row_2_1 {i j : ℕ} : (i, j) ∈ (row 2 1).youngDiagram ↔ i = 0 ∧ j = 0 := by
  rw [← YoungDiagram.mem_cells, sanity_cells_row_2_1]; simp

/-- `(i, j)` is a cell of the shape `(2)` iff `i = 0` and `j ≤ 1`. -/
theorem sanity_mem_row_2_2 {i j : ℕ} : (i, j) ∈ (row 2 2).youngDiagram ↔ i = 0 ∧ j ≤ 1 := by
  rw [← YoungDiagram.mem_cells, sanity_cells_row_2_2]; simp; omega

/-- The tableau of shape `(1)` with entry `u`. -/
def tab1 (u : ℕ) : SemistandardYoungTableau (row 2 1).youngDiagram where
  entry i j := if i = 0 ∧ j = 0 then u else 0
  row_weak' {i j1 j2} hj h := by rw [sanity_mem_row_2_1] at h; omega
  col_strict' {i1 i2 j} hi h := by rw [sanity_mem_row_2_1] at h; omega
  zeros' {i j} h := by rw [sanity_mem_row_2_1] at h; simp [h]

/-- The tableau of shape `(2)` with row `u v`, `u ≤ v`. -/
def tab2 (u v : ℕ) (huv : u ≤ v) : SemistandardYoungTableau (row 2 2).youngDiagram where
  entry i j := if i = 0 ∧ j = 0 then u else if i = 0 ∧ j = 1 then v else 0
  row_weak' {i j1 j2} hj h := by
    rw [sanity_mem_row_2_2] at h
    obtain ⟨rfl, h⟩ := h
    have h1 : j1 = 0 := by omega
    have h2 : j2 = 1 := by omega
    subst h1 h2; simpa using huv
  col_strict' {i1 i2 j} hi h := by rw [sanity_mem_row_2_2] at h; omega
  zeros' {i j} h := by
    rw [sanity_mem_row_2_2] at h
    have : ¬ (i = 0 ∧ j = 0) := by omega
    have : ¬ (i = 0 ∧ j = 1) := by omega
    simp [*]

/-- The entries of `tab1 u`. -/
theorem sanity_tab1_apply (u i j : ℕ) : tab1 u i j = if i = 0 ∧ j = 0 then u else 0 := rfl

/-- The entries of `tab2 u v huv`. -/
theorem sanity_tab2_apply (u v : ℕ) (huv : u ≤ v) (i j : ℕ) :
    tab2 u v huv i j = if i = 0 ∧ j = 0 then u else if i = 0 ∧ j = 1 then v else 0 := rfl

/-- The content of a tableau of shape `(1)` counts whether its entry is `i`. -/
theorem sanity_content_row_2_1 (T : SemistandardYoungTableau (row 2 1).youngDiagram) (i : Fin 2) :
    T.content 2 i = if T 0 0 = i then 1 else 0 := by
  simp only [SemistandardYoungTableau.content]
  rw [sanity_cells_row_2_1, Finset.card_filter, Finset.sum_singleton]

/-- The content of a tableau of shape `(2)` counts the entries of its row equal to `i`. -/
theorem sanity_content_row_2_2 (T : SemistandardYoungTableau (row 2 2).youngDiagram) (i : Fin 2) :
    T.content 2 i = (if T 0 0 = i then 1 else 0) + (if T 0 1 = i then 1 else 0) := by
  simp only [SemistandardYoungTableau.content]
  rw [sanity_cells_row_2_2, Finset.card_filter, Finset.sum_pair (by decide)]

/-- A tableau of shape `(1)` with entry `u` is `tab1 u`. -/
theorem sanity_eq_tab1 (T : SemistandardYoungTableau (row 2 1).youngDiagram) (u : ℕ)
    (h : T 0 0 = u) :
    T = tab1 u := by
  ext i j
  by_cases hij : (i, j) ∈ (row 2 1).youngDiagram
  · rw [sanity_mem_row_2_1] at hij
    obtain ⟨rfl, rfl⟩ := hij
    simp [sanity_tab1_apply, h]
  · rw [T.zeros hij, (tab1 u).zeros hij]

/-- A tableau of shape `(2)` with row `u v` is `tab2 u v huv`. -/
theorem sanity_eq_tab2 (T : SemistandardYoungTableau (row 2 2).youngDiagram) (u v : ℕ) (huv : u ≤ v)
    (hu : T 0 0 = u) (hv : T 0 1 = v) : T = tab2 u v huv := by
  ext i j
  by_cases hij : (i, j) ∈ (row 2 2).youngDiagram
  · rw [sanity_mem_row_2_2] at hij
    obtain ⟨rfl, hj⟩ := hij
    obtain rfl | rfl : j = 0 ∨ j = 1 := by omega
    · simp [sanity_tab2_apply, hu]
    · simp [sanity_tab2_apply, hv]
  · rw [T.zeros hij, (tab2 u v huv).zeros hij]

/-- A tableau of shape `(1)` has entries in `{0, 1}` iff its entry is less than `2`. -/
theorem sanity_ssyt_row_2_1 (T : SemistandardYoungTableau (row 2 1).youngDiagram) :
    T ∈ (row 2 1).semistandardYoungTableaux ↔ T 0 0 < 2 := by
  simp only [semistandardYoungTableaux, Set.mem_ofPred_eq, sanity_mem_row_2_1]
  refine ⟨fun h => h 0 0 ⟨rfl, rfl⟩, ?_⟩
  rintro h i j ⟨rfl, rfl⟩
  exact h

/-- A tableau of shape `(2)` has entries in `{0, 1}` iff both entries of its row are less than
`2`. -/
theorem sanity_ssyt_row_2_2 (T : SemistandardYoungTableau (row 2 2).youngDiagram) :
    T ∈ (row 2 2).semistandardYoungTableaux ↔ T 0 0 < 2 ∧ T 0 1 < 2 := by
  simp only [semistandardYoungTableaux, Set.mem_ofPred_eq, sanity_mem_row_2_2]
  constructor
  · intro h; exact ⟨h 0 0 ⟨rfl, by omega⟩, h 0 1 ⟨rfl, le_rfl⟩⟩
  · rintro h i j ⟨rfl, hj⟩
    obtain rfl | rfl : j = 0 ∨ j = 1 := by omega
    exacts [h.1, h.2]

/-- Two functions `Fin 2 → ℕ` are equal iff their values at `0` and `1` are. -/
theorem sanity_content_eq_iff (c α : Fin 2 → ℕ) : c = α ↔ c 0 = α 0 ∧ c 1 = α 1 := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · rintro ⟨h0, h1⟩; funext i; fin_cases i <;> assumption

/-- `K_{(1),(1,0)} = 1`. -/
theorem sanity_kostka_row1_10 : (row 2 1).kostkaNumber ![1, 0] = 1 := by
  rw [kostkaNumber, Set.ncard_eq_one]
  refine ⟨tab1 0, Set.ext fun T => ?_⟩
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, sanity_ssyt_row_2_1, sanity_content_eq_iff,
    sanity_content_row_2_1]
  constructor
  · rintro ⟨h2, h0, h1⟩
    refine sanity_eq_tab1 T 0 ?_
    rcases (by omega : T 0 0 = 0 ∨ T 0 0 = 1) with h | h <;> simp [h] at h0 h1 ⊢
  · rintro rfl; simp [sanity_tab1_apply]

/-- `K_{(1),(0,1)} = 1`. -/
theorem sanity_kostka_row1_01 : (row 2 1).kostkaNumber ![0, 1] = 1 := by
  rw [kostkaNumber, Set.ncard_eq_one]
  refine ⟨tab1 1, Set.ext fun T => ?_⟩
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, sanity_ssyt_row_2_1, sanity_content_eq_iff,
    sanity_content_row_2_1]
  constructor
  · rintro ⟨h2, h0, h1⟩
    refine sanity_eq_tab1 T 1 ?_
    rcases (by omega : T 0 0 = 0 ∨ T 0 0 = 1) with h | h <;> simp [h] at h0 h1 ⊢
  · rintro rfl; simp [sanity_tab1_apply]

/-- `K_{(2),(2,0)} = 1`. -/
theorem sanity_kostka_row2_20 : (row 2 2).kostkaNumber ![2, 0] = 1 := by
  rw [kostkaNumber, Set.ncard_eq_one]
  refine ⟨tab2 0 0 le_rfl, Set.ext fun T => ?_⟩
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, sanity_ssyt_row_2_2, sanity_content_eq_iff,
    sanity_content_row_2_2]
  constructor
  · rintro ⟨h2, h0, h1⟩
    refine sanity_eq_tab2 T 0 0 le_rfl ?_ ?_ <;>
    · revert h0 h1; simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
        Fin.val_zero, Fin.val_one]; split_ifs <;> intros <;> omega
  · rintro rfl; simp [sanity_tab2_apply]

/-- `K_{(2),(1,1)} = 1`: the single tableau `0 1` (entries in `{0, 1}` stand for `[2]`). -/
theorem sanity_kostka_row2_11 : (row 2 2).kostkaNumber ![1, 1] = 1 := by
  rw [kostkaNumber, Set.ncard_eq_one]
  refine ⟨tab2 0 1 zero_le_one, Set.ext fun T => ?_⟩
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, sanity_ssyt_row_2_2, sanity_content_eq_iff,
    sanity_content_row_2_2]
  constructor
  · rintro ⟨h2, h0, h1⟩
    have hw : T 0 0 ≤ T 0 1 := T.row_weak (by omega : 0 < 1) (sanity_mem_row_2_2.2 ⟨rfl, le_rfl⟩)
    refine sanity_eq_tab2 T 0 1 zero_le_one ?_ ?_ <;>
    · revert h0 h1; simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
        Fin.val_zero, Fin.val_one]; split_ifs <;> intros <;> omega
  · rintro rfl; simp [sanity_tab2_apply]

/-- `K_{(2),(0,2)} = 1`. -/
theorem sanity_kostka_row2_02 : (row 2 2).kostkaNumber ![0, 2] = 1 := by
  rw [kostkaNumber, Set.ncard_eq_one]
  refine ⟨tab2 1 1 le_rfl, Set.ext fun T => ?_⟩
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, sanity_ssyt_row_2_2, sanity_content_eq_iff,
    sanity_content_row_2_2]
  constructor
  · rintro ⟨h2, h0, h1⟩
    refine sanity_eq_tab2 T 1 1 le_rfl ?_ ?_ <;>
    · revert h0 h1; simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
        Fin.val_zero, Fin.val_one]; split_ifs <;> intros <;> omega
  · rintro rfl; simp [sanity_tab2_apply]

/-- The pairs of naturals with sum `1`. -/
theorem sanity_antidiagonalTuple_2_1 :
    Finset.Nat.antidiagonalTuple 2 1 = {![1, 0], ![0, 1]} := by decide +kernel

/-- The pairs of naturals with sum `2`. -/
theorem sanity_antidiagonalTuple_2_2 :
    Finset.Nat.antidiagonalTuple 2 2 = {![2, 0], ![1, 1], ![0, 2]} := by decide +kernel

/-- The one-row shape `(1)` has size `1`. -/
theorem sanity_size_row_2_1 : ∑ i, (row 2 1).1 i = 1 := by decide +kernel

/-- The one-row shape `(2)` has size `2`. -/
theorem sanity_size_row_2_2 : ∑ i, (row 2 2).1 i = 2 := by decide +kernel

/-- The finitely supported function with values `α 0, α 1` is `α 0 e₀ + α 1 e₁`. -/
theorem sanity_equivFunOnFinite_symm_eq (α : Fin 2 → ℕ) :
    Finsupp.equivFunOnFinite.symm α = Finsupp.single 0 (α 0) + Finsupp.single 1 (α 1) := by
  ext i; fin_cases i <;> simp

/-- `s_{(1)}(z₁, z₂) = z₁ + z₂`. -/
theorem sanity_schurPolynomial_row1 :
    (row 2 1).schurPolynomial ℝ = MvPolynomial.X 0 + MvPolynomial.X 1 := by
  rw [schurPolynomial, sanity_size_row_2_1, sanity_antidiagonalTuple_2_1,
    Finset.sum_pair (by decide), sanity_kostka_row1_10, sanity_kostka_row1_01]
  simp [sanity_equivFunOnFinite_symm_eq, MvPolynomial.X]

/-- `s_{(2)}(z₁, z₂) = z₁² + z₁ z₂ + z₂²`. -/
theorem sanity_schurPolynomial_row2 :
    (row 2 2).schurPolynomial ℝ =
      MvPolynomial.X 0 ^ 2 + MvPolynomial.X 0 * MvPolynomial.X 1 + MvPolynomial.X 1 ^ 2 := by
  rw [schurPolynomial, sanity_size_row_2_2, sanity_antidiagonalTuple_2_2,
    Finset.sum_insert (by decide),
    Finset.sum_pair (by decide), sanity_kostka_row2_20, sanity_kostka_row2_11,
    sanity_kostka_row2_02]
  have e1 : (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℝ) ^ 2 =
      MvPolynomial.monomial (Finsupp.single 0 2) 1 := MvPolynomial.X_pow_eq_monomial
  have e2 : (MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) ℝ) =
      MvPolynomial.monomial (Finsupp.single 0 1 + Finsupp.single 1 1) 1 := by
    rw [MvPolynomial.X, MvPolynomial.X, MvPolynomial.monomial_mul, one_mul]
  have e3 : (MvPolynomial.X 1 : MvPolynomial (Fin 2) ℝ) ^ 2 =
      MvPolynomial.monomial (Finsupp.single 1 2) 1 := MvPolynomial.X_pow_eq_monomial
  rw [e1, e2, e3]
  simp [sanity_equivFunOnFinite_symm_eq, add_assoc]

/-- The Narayana transform of `c z₀^{α 0} z₁^{α 1}` is `c Ñ_{α 0} Ñ_{α 1}`. -/
theorem sanity_narayanaTransform_monomial (α : Fin 2 →₀ ℕ) (c : ℝ) :
    MvPolynomial.narayanaTransform (Fin 2) (MvPolynomial.monomial α c) =
      c • (shiftedNarayanaPolynomial (α 0) * shiftedNarayanaPolynomial (α 1)) := by
  have h0 : shiftedNarayanaPolynomial 0 = 1 := by simp [shiftedNarayanaPolynomial]
  rw [show MvPolynomial.monomial α c = c • MvPolynomial.monomial α 1 by
    rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one], map_smul]
  congr 1
  rw [show MvPolynomial.monomial α (1 : ℝ) = MvPolynomial.basisMonomials (Fin 2) ℝ α by
    simp [MvPolynomial.coe_basisMonomials], MvPolynomial.narayanaTransform,
    Module.Basis.constr_basis,
    Finsupp.prod_fintype _ _ (fun _ => h0), Fin.prod_univ_two]

/-- `Ñ_0 = 1`. -/
theorem sanity_shiftedNarayana_zero : shiftedNarayanaPolynomial 0 = 1 := by
  simp [shiftedNarayanaPolynomial]

/-- `Ñ_1 = 1 + x`. -/
theorem sanity_shiftedNarayana_one : shiftedNarayanaPolynomial 1 = 1 + X := by
  simp only [shiftedNarayanaPolynomial, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

/-- `Ñ_2 = 1 + 3x + x²`. -/
theorem sanity_shiftedNarayana_two : shiftedNarayanaPolynomial 2 = 1 + 3 * X + X ^ 2 := by
  simp only [shiftedNarayanaPolynomial, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.choose]
  rw [show (3 : ℝ[X]) = C 3 from (map_ofNat C 3).symm]

/-- `Φ_{(1),2} = 2 + 2x`, the paper's `r/(r+d) ∑_j C(r+d,j) C(r+d,d-j) x^j = (2/3)(3 + 3x)`. -/
theorem sanity_schurNarayanaTransform_row1 :
    (row 2 1).schurNarayanaTransform = 2 + 2 * X := by
  rw [schurNarayanaTransform, schurPolynomial, sanity_size_row_2_1, sanity_antidiagonalTuple_2_1,
    Finset.sum_pair (by decide), sanity_kostka_row1_10, sanity_kostka_row1_01, map_add,
    sanity_narayanaTransform_monomial, sanity_narayanaTransform_monomial]
  simp [sanity_shiftedNarayana_zero, sanity_shiftedNarayana_one]
  ring

/-- `Φ_{(2),2} = 3 + 8x + 3x²`, the paper's `(2/4)(6 + 16x + 6x²)`. -/
theorem sanity_schurNarayanaTransform_row2 :
    (row 2 2).schurNarayanaTransform = 3 + 8 * X + 3 * X ^ 2 := by
  rw [schurNarayanaTransform, schurPolynomial, sanity_size_row_2_2, sanity_antidiagonalTuple_2_2,
    Finset.sum_insert (by decide), Finset.sum_pair (by decide), sanity_kostka_row2_20,
    sanity_kostka_row2_11, sanity_kostka_row2_02, map_add, map_add,
    sanity_narayanaTransform_monomial,
    sanity_narayanaTransform_monomial, sanity_narayanaTransform_monomial]
  simp [sanity_shiftedNarayana_zero, sanity_shiftedNarayana_one, sanity_shiftedNarayana_two]
  ring

end Schur

end LogNarayanaSanityNC

end
