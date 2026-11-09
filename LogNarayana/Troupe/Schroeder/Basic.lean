/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module
public import Mathlib
public import LogNarayana.Attr
public import LogNarayana.Troupe.Schroeder.Defs
public import LogNarayana.BinaryTree.Colored.Defs
public import LogNarayana.StackSorting.Descents.Defs
public import LogNarayana.Lorentzian.Hessian.Defs
public import LogNarayana.Polynomial.LogConcave.Defs
public import LogNarayana.StackSorting.Matchings.Defs
public import LogNarayana.StackSorting.FiberPolynomials.Defs
public import LogNarayana.Troupe.LocalRules.Defs
public import LogNarayana.Troupe.PostorderPolynomial.Basic
public import LogNarayana.Lorentzian.Hessian.Basic
public import LogNarayana.Lorentzian.Symbol.Basic
public import LogNarayana.StackSorting.Matchings.Basic
public import LogNarayana.Lorentzian.BrandenHuh.Basic
public import LogNarayana.StackSorting.FiberMatroid.Basic
public import LogNarayana.Lorentzian.Bivariate

/-!
# Schröder two-colored trees

For `n ≥ 1` and `π ∈ S_n`, the Schröder postorder polynomial `𝒞_π(z, w)` counts the decreasing
Schröder two-colored binary trees with postorder reading `π` by their numbers of black and white
vertices. Summing out the colors vertex by vertex, a vertex of type `leaf` or `ru` contributes
`z + w` and one of type `lu` or `bin` contributes `z`; counting vertex types through the descents
of the inorder reading gives the Schröder identity `𝒞_π(z, w) = (z + w) H_π(z + w, z)`.

Since `H_π` is Lorentzian, the substitution `(x, y) ↦ (z + w, z)` has a nonnegative matrix and
`z + w` is Lorentzian, `𝒞_π` is Lorentzian. Every vertex is black or white, so `𝒞_π` is the
degree-`n` homogenization of `𝒞_π(z, 1)`, which is therefore ultra-log-concave of order `n`.

The section closes with the example `π = 21345`: its matchings are
`{(1,2)}, {(1,3)}, {(1,4)}, {(1,2),(3,4)}, {(1,4),(2,3)}`, so `Γ_π(z) = 3z + 2z²`, and
`𝒞_π(z, 1) = 3z + 20z² + 45z³ + 42z⁴ + 14z⁵`.

## Main results

* `List.fiberMatchingPolynomial_21345`: `Γ_{21345}(z) = 3z + 2z²`.
* `List.schroederFiberPolynomial_eq`: `𝒞_π(z, w) = (z + w) H_π(z + w, z)`.
* `List.schroederFiberPolynomial_21345_eval_one`:
  `𝒞_{21345}(z, 1) = 3z + 20z² + 45z³ + 42z⁴ + 14z⁵`.
* `List.isLorentzian_schroederFiberPolynomial`: `𝒞_π(z, w)` is Lorentzian.
* `List.isUltraLogConcave_schroederFiberPolynomial_eval_one`: `𝒞_π(z, 1)` is ultra-log-concave
  of order `n`.

## Implementation notes

Both polynomials live in `MvPolynomial (Fin 2) R` with `z = X 0` and `w = X 1`; the substitution
`x ↦ z + w`, `y ↦ z` into `H_π(x, y)` is `MvPolynomial.bind₁ ![X 0 + X 1, X 0]`, and the
specialization `w = 1` is `MvPolynomial.aeval ![Polynomial.X, 1]`. The paper works over `ℝ`; the
identities are stated over any commutative semiring `R`, and for any type of colors `C` with
distinguished distinct `black` and `white`. Permutations are one-line lists, so `21345` is
`[2, 1, 3, 4, 5]`.

The results of Brändén–Huh used for the Lorentzian property are taken as hypotheses: Theorem 3.10
and Theorem 2.10 (for `H_π`), Theorem 2.10 again (for the substitution `x = z + w`, `y = z`), and
Corollary 2.32 (for the product).

## References

* [LogNarayana] *Log-Concavity in Narayana Transforms and Stack-Sorting Fibers*, Section 5 and
  Proposition 5.2.
* [BH] P. Brändén, J. Huh, *Lorentzian polynomials*, Ann. of Math. 192 (2020).
-/

open MvPolynomial

/-! ### The matching polynomial of `21345` -/

namespace List

/-- The six pairs `(a, b)` with `1 ≤ a < b ≤ 4`. -/
private def pairs21345 : Finset (ℕ × ℕ) := {(1, 2), (1, 3), (1, 4), (2, 3), (2, 4), (3, 4)}

/-- The matchings of `21345`. -/
private def matchings21345 : Finset (Finset (ℕ × ℕ)) :=
  {{(1, 2)}, {(1, 3)}, {(1, 4)}, {(1, 2), (3, 4)}, {(1, 4), (2, 3)}}

/-- `IsNoncrossingPartialMatching` with the entry quantifier bounded, so that it is decidable. -/
private abbrev IsNPM (N : ℕ) (M : Finset (ℕ × ℕ)) : Prop :=
  (∀ p ∈ M, 1 ≤ p.1) ∧ (∀ p ∈ M, p.1 < p.2) ∧ (∀ p ∈ M, p.2 ≤ N) ∧
  (∀ p ∈ M, ∀ q ∈ M, ∀ x ∈ ({p.1, p.2} : Finset ℕ), x = q.1 ∨ x = q.2 → p = q) ∧
  (∀ p ∈ M, ∀ q ∈ M, ¬ (p.1 < q.1 ∧ q.1 < p.2 ∧ p.2 < q.2))

private lemma isNoncrossingPartialMatching_iff_isNPM {N : ℕ} {M : Finset (ℕ × ℕ)} :
    IsNoncrossingPartialMatching N M ↔ IsNPM N M :=
  ⟨fun ⟨h1, h2, h3, h4, h5⟩ =>
    ⟨h1, h2, h3, fun p hp q hq x hx => h4 p hp q hq x (by simpa using hx), h5⟩,
   fun ⟨h1, h2, h3, h4, h5⟩ =>
    ⟨h1, h2, h3, fun p hp q hq x hx => h4 p hp q hq x (by simpa using hx), h5⟩⟩

private lemma subset_pairs21345 {M : Finset (ℕ × ℕ)} (h : IsNoncrossingPartialMatching 4 M) :
    M ⊆ pairs21345 := by
  rintro ⟨a, b⟩ hp
  have := h.one_le_fst _ hp
  have := h.fst_lt_snd _ hp
  have := h.snd_le _ hp
  simp only at *
  have : a ≤ 4 := by omega
  interval_cases a <;> interval_cases b <;> simp [pairs21345]

/-- The exhaustive search: among the subsets of `pairs21345`, the matchings of `21345` are
exactly `matchings21345`. -/
private lemma mem_matchings21345_iff : ∀ M ∈ pairs21345.powerset,
    (IsNPM 4 M ∧ ([2, 1, 3, 4, 5] : List ℕ).descentSet ⊆ M.leftEndpoints ∧
      ∀ p ∈ M, ∃ (ha : p.1 - 1 < 5) (hb : p.2 < 5),
        ([2, 1, 3, 4, 5] : List ℕ)[p.1 - 1] < ([2, 1, 3, 4, 5] : List ℕ)[p.2]) ↔
      M ∈ matchings21345 := by
  decide

private lemma fiberMatchings_21345 :
    ([2, 1, 3, 4, 5] : List ℕ).fiberMatchings = ↑matchings21345 := by
  ext M
  simp only [List.fiberMatchings, Set.mem_ofPred_eq, Finset.mem_coe]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact (mem_matchings21345_iff M (Finset.mem_powerset.2 (subset_pairs21345 h1))).1
      ⟨isNoncrossingPartialMatching_iff_isNPM.1 h1, h2, h3⟩
  · intro hM
    obtain ⟨h1, h2, h3⟩ := (mem_matchings21345_iff M (by revert M; decide)).2 hM
    exact ⟨isNoncrossingPartialMatching_iff_isNPM.2 h1, h2, h3⟩

/-- `Γ_{21345}(z) = 3z + 2z²`. -/
@[lognarayana "lem_gamma_21345"]
public theorem fiberMatchingPolynomial_21345 (R : Type*) [CommSemiring R] :
    fiberMatchingPolynomial R [2, 1, 3, 4, 5] = 3 * Polynomial.X + 2 * Polynomial.X ^ 2 := by
  rw [List.fiberMatchingPolynomial, fiberMatchings_21345, finsum_mem_coe_finset]
  simp +decide [matchings21345, Finset.sum_insert]
  ring

end List

/-! ### The Schröder identity -/

namespace BinaryTree

variable {R : Type*} [CommSemiring R] {C : Type*} [TreeColors C] [DecidableEq C]

/-- The four vertex-type counts of a binary plane tree add up to its number of vertices. -/
private lemma sum_numNodesOfType {α : Type*} (T : BinaryTree α) :
    T.numNodesOfType .leaf + T.numNodesOfType .leftUnary + T.numNodesOfType .rightUnary +
      T.numNodesOfType .binary = T.postorder.length := by
  induction T with
  | nil => simp [postorder]
  | node a l r ihl ihr =>
    simp only [numNodesOfType, postorder, List.length_append, List.length_singleton]
    cases l <;> cases r <;> simp [vertexType] at ihl ihr ⊢ <;> omega

variable (R) in
/-- The color weight `black ↦ z`, `white ↦ w`, and `1` on every other color. -/
private noncomputable def schroederColorWeight (c : C) : MvPolynomial (Fin 2) R :=
  if c = TreeColors.black then X 0 else if c = TreeColors.white then X 1 else 1

/-- The Schröder local rule: black on every vertex type, white on `leaf` and `ru`. -/
private abbrev schroederRule (C : Type*) [TreeColors C] : Set (VertexType × C) :=
  (Set.univ ×ˢ {TreeColors.black}) ∪
    {(.leaf, TreeColors.white), (.rightUnary, TreeColors.white)}

/-- The color weight multiplied over a colored tree is `z^{black} w^{white}`. -/
private lemma rec_schroederColorWeight_eq (T : BinaryTree (ℕ × C)) :
    BinaryTree.rec (motive := fun _ => MvPolynomial (Fin 2) R) 1
      (fun a _ _ ihl ihr => schroederColorWeight R a.2 * ihl * ihr) T =
      X 0 ^ T.skeleton.numBlackNodes * X 1 ^ T.skeleton.numWhiteNodes := by
  have hbw : (TreeColors.black : C) ≠ TreeColors.white := TreeColors.black_ne_white
  induction T with
  | nil => simp [BinaryTree.map]
  | node a l r ihl ihr =>
    dsimp only
    rw [ihl, ihr]
    by_cases hb : a.2 = TreeColors.black
    · simp [schroederColorWeight, BinaryTree.map, hb, hbw, pow_add] at *
      ring
    · by_cases hw : a.2 = TreeColors.white
      · simp [schroederColorWeight, BinaryTree.map, hw, hbw.symm, pow_add] at *
        ring
      · simp [schroederColorWeight, BinaryTree.map, hb, hw, pow_add] at *
        ring

/-- Summing the color weight over the colors the Schröder rule allows at a vertex type gives
`z + w` on types `leaf`, `ru` and `z` on types `lu`, `bin`. -/
private lemma finsum_schroederColorWeight (τ : VertexType) :
    ∑ᶠ (c : C) (_ : (τ, c) ∈ schroederRule C), schroederColorWeight R c =
      if τ = .leaf ∨ τ = .rightUnary then X 0 + X 1 else X 0 := by
  have hbw : (TreeColors.black : C) ≠ TreeColors.white := TreeColors.black_ne_white
  change ∑ᶠ c ∈ {c : C | (τ, c) ∈ schroederRule C}, schroederColorWeight R c = _
  cases τ <;>
    simp only [Set.union_insert, Set.union_singleton, Set.insert_def, Set.mem_prod, Set.mem_univ,
      Set.mem_singleton_iff, true_and, or_comm, Set.mem_ofPred_eq, Prod.mk.injEq, reduceCtorEq,
      false_and, false_or, Set.ofPred_eq_eq_singleton, schroederColorWeight, Fin.isValue,
      finsum_cond_eq_left, ↓reduceIte, or_self, or_true] <;>
    exact (finsum_mem_pair (M := MvPolynomial (Fin 2) R) hbw).trans (by simp [hbw.symm])

/-- The product over the vertices of a tree of the Schröder color sums is
`z^{n_lu + n_bin} (z + w)^{n_leaf + n_ru}`. -/
private lemma rec_finsum_schroederColorWeight_eq {α : Type*} (T : BinaryTree α) :
    BinaryTree.rec (motive := fun _ => MvPolynomial (Fin 2) R) 1
      (fun _ l r ihl ihr =>
        (∑ᶠ (c : C) (_ : (vertexType l r, c) ∈ schroederRule C), schroederColorWeight R c) *
          ihl * ihr) T =
      X 0 ^ (T.numNodesOfType .leftUnary + T.numNodesOfType .binary) *
        (X 0 + X 1) ^ (T.numNodesOfType .leaf + T.numNodesOfType .rightUnary) := by
  induction T with
  | nil => simp
  | node a l r ihl ihr =>
    dsimp only
    rw [ihl, ihr, finsum_schroederColorWeight]
    cases l <;> cases r <;> simp [vertexType, numNodesOfType] <;> ring

/-- The weight of one decreasing tree `T` with `N ≥ 1` vertices: the product of its Schröder
color sums is `(z + w) (z + w)^{des(I(T))} z^{N - 1 - des(I(T))}`. -/
private lemma rec_finsum_schroederColorWeight_eq_of_isDecreasing (T : BinaryTree ℕ)
    (hT : T.IsDecreasing) (hne : T ≠ nil) :
    BinaryTree.rec (motive := fun _ => MvPolynomial (Fin 2) R) 1
      (fun _ l r ihl ihr =>
        (∑ᶠ (c : C) (_ : (vertexType l r, c) ∈ schroederRule C), schroederColorWeight R c) *
          ihl * ihr) T =
      (X 0 + X 1) * ((X 0 + X 1) ^ T.inorder.numDescents *
        X 0 ^ (T.postorder.length - 1 - T.inorder.numDescents)) := by
  have h1 := numNodesOfType_leaf_eq_numNodesOfType_binary_add_one T hne
  have h2 := sum_numNodesOfType T
  rw [rec_finsum_schroederColorWeight_eq, numDescents_inorder_of_isDecreasing hT,
    show T.numNodesOfType .leaf + T.numNodesOfType .rightUnary =
      T.numNodesOfType .rightUnary + T.numNodesOfType .binary + 1 by omega,
    show T.postorder.length - 1 - (T.numNodesOfType .rightUnary + T.numNodesOfType .binary) =
      T.numNodesOfType .leftUnary + T.numNodesOfType .binary by omega]
  ring

end BinaryTree

namespace List

/-- **Schröder identity**: for `n ≥ 1` and `π ∈ S_n`,
`𝒞_π(z, w) = (z + w) H_π(z + w, z)`, where `z = X 0` and `w = X 1`. -/
@[lognarayana "prop_schroeder_identity"]
public theorem schroederFiberPolynomial_eq (R : Type*) [CommSemiring R] (C : Type*)
    [BinaryTree.TreeColors C] [DecidableEq C] {n : ℕ} (hn : 1 ≤ n) {π : List ℕ}
    (hπ : π ∈ permWords n) :
    schroederFiberPolynomial R C π =
      (X 0 + X 1) * bind₁ ![X 0 + X 1, X 0] (fiberHomogPolynomial R π) := by
  have hP (τ : BinaryTree.VertexType) :
      {c : C | (τ, c) ∈ BinaryTree.schroederRule C}.Finite :=
    (({BinaryTree.TreeColors.black, BinaryTree.TreeColors.white} : Set C).toFinite).subset
      fun c => by cases τ <;> simp <;> tauto
  have key := BinaryTree.finsum_familyDecreasingLabelings_localRuleFamily
    (BinaryTree.schroederRule C) hP hπ (BinaryTree.schroederColorWeight R) (fun _ => 1)
  simp only [one_mul, BinaryTree.rec_schroederColorWeight_eq] at key
  rw [List.schroederFiberPolynomial, BinaryTree.schroederTrees, key, List.fiberHomogPolynomial,
    map_sum, Finset.mul_sum]
  simp only [map_mul, map_pow, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  rw [List.sum_stackFiber_eq_finsum_decreasingTrees π (fun σ => (X 0 + X 1) *
    ((X 0 + X 1) ^ σ.numDescents * X 0 ^ (π.length - 1 - σ.numDescents))), hπ.2.1]
  refine finsum_congr fun T => finsum_congr fun hT => ?_
  have hne : T ≠ BinaryTree.nil := by
    rintro rfl
    have := hπ.2.1
    rw [← hT.2] at this
    simp [BinaryTree.postorder] at this
    omega
  rw [BinaryTree.rec_finsum_schroederColorWeight_eq_of_isDecreasing T hT.1.1 hne, hT.2, hπ.2.1]

/-! ### The Schröder postorder polynomial of `21345` at `w = 1` -/

/-- A matching of `π` has at most `(π.length - 1) / 2` arcs. -/
private lemma card_le_of_mem_fiberMatchings {π : List ℕ} {M : Finset (ℕ × ℕ)}
    (hM : M ∈ π.fiberMatchings) : M.card ≤ (π.length - 1) / 2 := by
  have := hM.1.card_unmatchedVertices_add_two_mul_card
  omega

/-- `[z^j] Γ_π` counts the matchings of `π` with `j` arcs. -/
private lemma coeff_fiberMatchingPolynomial (R : Type*) [CommSemiring R] (π : List ℕ) (j : ℕ) :
    (π.fiberMatchingPolynomial R).coeff j =
      (((List.fiberMatchings_finite π).toFinset.filter (fun M => M.card = j)).card : R) := by
  rw [List.fiberMatchingPolynomial,
    finsum_mem_eq_finite_toFinset_sum _ (List.fiberMatchings_finite π),
    Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_X_pow]
  rw [Finset.sum_boole]
  congr 2
  ext M
  simp [eq_comm]

/-- Grouping a sum over the matchings of `π` by their number of arcs. -/
private lemma finsum_fiberMatchings_eq_sum_coeff (R : Type*) [CommSemiring R] {S : Type*}
    [Semiring S] [Algebra R S] (π : List ℕ) (f : ℕ → S) :
    ∑ᶠ M ∈ π.fiberMatchings, f M.card = ∑ j ∈ Finset.range ((π.length - 1) / 2 + 1),
      (π.fiberMatchingPolynomial R).coeff j • f j := by
  rw [finsum_mem_eq_finite_toFinset_sum _ (List.fiberMatchings_finite π),
    ← Finset.sum_fiberwise_of_maps_to (g := Finset.card)
      fun M hM => Finset.mem_range_succ_iff.mpr <|
        card_le_of_mem_fiberMatchings ((List.fiberMatchings_finite π).mem_toFinset.mp hM)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_congr rfl fun M hM => by rw [(Finset.mem_filter.mp hM).2], Finset.sum_const,
    coeff_fiberMatchingPolynomial, Nat.cast_smul_eq_nsmul]

private lemma mem_permWords_21345 : [2, 1, 3, 4, 5] ∈ permWords 5 :=
  ⟨by simp [words, IsWord], rfl, by decide⟩

/-- `H_{21345}(x, y) = 3 x y (x + y)² + 2 x² y²`. -/
private lemma fiberHomogPolynomial_21345 (R : Type*) [CommSemiring R] :
    List.fiberHomogPolynomial R [2, 1, 3, 4, 5] =
      3 * (X 0 * X 1) * (X 0 + X 1) ^ 2 + 2 * (X 0 * X 1) ^ 2 := by
  rw [List.fiberHomogPolynomial_eq_finsum_fiberMatchings R (n := 5) (by norm_num)
      mem_permWords_21345,
    finsum_fiberMatchings_eq_sum_coeff R _ (fun j => (X 0 * X 1 : MvPolynomial (Fin 2) R) ^ j *
      (X 0 + X 1) ^ (5 - 1 - 2 * j)),
    List.fiberMatchingPolynomial_21345]
  simp [Finset.sum_range_succ, Polynomial.coeff_X, Polynomial.coeff_X_pow, Algebra.smul_def,
    map_ofNat]
  ring

/-- `𝒞_{21345}(z, 1) = 3z + 20z² + 45z³ + 42z⁴ + 14z⁵`. -/
@[lognarayana "lem_schroeder_example_21345"]
public theorem schroederFiberPolynomial_21345_eval_one (R : Type*) [CommSemiring R] (C : Type*)
    [BinaryTree.TreeColors C] [DecidableEq C] :
    (aeval ![Polynomial.X, 1] (schroederFiberPolynomial R C [2, 1, 3, 4, 5]) : Polynomial R) =
      3 * Polynomial.X + 20 * Polynomial.X ^ 2 + 45 * Polynomial.X ^ 3 +
        42 * Polynomial.X ^ 4 + 14 * Polynomial.X ^ 5 := by
  rw [List.schroederFiberPolynomial_eq R C (n := 5) (by norm_num) mem_permWords_21345,
    fiberHomogPolynomial_21345]
  simp [map_ofNat]
  ring

/-! ### The Lorentzian property -/

/-- The linear form `z + w` is Lorentzian. -/
private lemma isLorentzian_X_zero_add_X_one :
    (X 0 + X 1 : MvPolynomial (Fin 2) ℝ).IsLorentzian :=
  IsLorentzian.of_isHomogeneous_of_le_one (d := 1)
    (fun α ↦ by simp only [coeff_add, coeff_X]; positivity)
    ((isHomogeneous_X ℝ 0).add (isHomogeneous_X ℝ 1)) le_rfl

/-- The substitution `(z, w) ↦ (z + w, z)` preserves Lorentzian polynomials, being the linear
substitution with the nonnegative matrix `!![1, 1; 1, 0]`. -/
private lemma isLorentzian_bind₁_X_zero_add_X_one_X_zero
    (hsub : LorentzianNonnegLinearSubstitution (Fin 2) (Fin 2)) {f : MvPolynomial (Fin 2) ℝ}
    (hf : f.IsLorentzian) :
    (bind₁ (![X 0 + X 1, X 0] : Fin 2 → MvPolynomial (Fin 2) ℝ) f).IsLorentzian := by
  have h := hsub ![![1, 1], ![1, 0]] (by intro i j; fin_cases i <;> fin_cases j <;> simp) f hf
  have hfun : (fun i : Fin 2 ↦ ∑ j, (![![1, 1], ![1, 0]] : Fin 2 → Fin 2 → ℝ) i j •
      (X j : MvPolynomial (Fin 2) ℝ)) = ![X 0 + X 1, X 0] := by
    funext i
    fin_cases i <;> simp
  rwa [hfun, aeval_eq_bind₁] at h

/-- **Proposition 5.2.** For `n ≥ 1` and `π ∈ S_n`, the Schröder postorder polynomial
`𝒞_π(z, w)` is Lorentzian, given the Brändén–Huh theorems that normalized support polynomials of
M-convex sets are Lorentzian, that nonnegative linear substitutions preserve Lorentzian
polynomials, and that products of Lorentzian polynomials are Lorentzian. -/
@[lognarayana "prop_schroeder_lorentzian"]
public theorem isLorentzian_schroederFiberPolynomial (C : Type*)
    [BinaryTree.TreeColors C] [DecidableEq C] {n : ℕ} (hn : 1 ≤ n) {π : List ℕ}
    (hπ : π ∈ permWords n)
    (hBH : NormalizedSupportPolyLorentzianOfMConvex
      ↥(Finset.univ ×ˢ Finset.Icc 1 n : Finset (Bool × ℕ)))
    (hsub : LorentzianNonnegLinearSubstitution
      ↥(Finset.univ ×ˢ Finset.Icc 1 n : Finset (Bool × ℕ)) (Fin 2))
    (hsub₂ : LorentzianNonnegLinearSubstitution (Fin 2) (Fin 2))
    (hmul : LorentzianMul (Fin 2)) :
    (schroederFiberPolynomial ℝ C π).IsLorentzian := by
  rw [List.schroederFiberPolynomial_eq ℝ C hn hπ]
  exact hmul _ _ isLorentzian_X_zero_add_X_one <|
    isLorentzian_bind₁_X_zero_add_X_one_X_zero hsub₂ <|
      List.isLorentzian_fiberHomogPolynomial hn hπ hBH hsub

/-! ### Black-vertex counts are ultra-log-concave -/

/-- In a Schröder two-colored tree of pairs, the black and white vertices together are all the
vertices, counted by the length of the postorder reading of the labels. -/
private theorem numBlack_add_numWhite {C : Type*} [BinaryTree.TreeColors C] [DecidableEq C] :
    ∀ 𝒯 : BinaryTree (ℕ × C), 𝒯.map Prod.snd ∈ BinaryTree.schroederTrees C →
      (𝒯.map Prod.snd).numBlackNodes + (𝒯.map Prod.snd).numWhiteNodes =
        ((𝒯.map Prod.fst).postorder).length
  | .nil, _ => rfl
  | .node a l r, ⟨hroot, hl, hr⟩ => by
    have ihl := numBlack_add_numWhite l hl
    have ihr := numBlack_add_numWhite r hr
    simp only [BinaryTree.map, BinaryTree.numBlackNodes, BinaryTree.numWhiteNodes,
      BinaryTree.postorder, List.length_append, List.length_singleton] at *
    have hbw : a.2 = BinaryTree.TreeColors.black ∨ a.2 = BinaryTree.TreeColors.white := by
      simp only [Set.mem_union, Set.mem_prod, Set.mem_univ, Set.mem_singleton_iff, true_and,
        Set.mem_insert_iff, Prod.mk.injEq] at hroot
      tauto
    have hne := BinaryTree.TreeColors.black_ne_white (C := C)
    rcases hbw with h | h <;> simp [h, hne, hne.symm] <;> omega

/-- Induction over `𝒞_π` as a sum of monomials `z^b w^w` with `b + w = |π|`: a property closed
under `0` and `+` that holds for every such monomial holds for `𝒞_π`. -/
private theorem schroederFiberPolynomial_induction {C : Type*} [BinaryTree.TreeColors C]
    [DecidableEq C] {π : List ℕ} (P : MvPolynomial (Fin 2) ℝ → Prop) (h0 : P 0)
    (hadd : ∀ a b, P a → P b → P (a + b))
    (hmono : ∀ b w : ℕ, b + w = π.length → P (X 0 ^ b * X 1 ^ w)) :
    P (List.schroederFiberPolynomial ℝ C π) := by
  refine finsum_induction P h0 hadd fun 𝒯 => finsum_induction P h0 hadd ?_
  rintro ⟨hmem, rfl⟩
  simp only [BinaryTree.familyDecreasingLabelings, Set.mem_iUnion] at hmem
  obtain ⟨T, hT, h𝒯⟩ := hmem
  exact hmono _ _ (numBlack_add_numWhite 𝒯 (by rwa [← h𝒯.2] at hT))

/-- **Proposition 5.2.** For `n ≥ 1` and `π ∈ S_n`, the polynomial `𝒞_π(z, 1) ∈ ℝ[z]` is
ultra-log-concave of order `n`, given the Brändén–Huh theorems that normalized support
polynomials of M-convex sets are Lorentzian, that nonnegative linear substitutions preserve
Lorentzian polynomials, and that products of Lorentzian polynomials are Lorentzian. -/
@[lognarayana "prop_schroeder_black_ulc"]
public theorem isUltraLogConcave_schroederFiberPolynomial_eval_one (C : Type*)
    [BinaryTree.TreeColors C] [DecidableEq C] {n : ℕ} (hn : 1 ≤ n) {π : List ℕ}
    (hπ : π ∈ permWords n)
    (hBH : NormalizedSupportPolyLorentzianOfMConvex
      ↥(Finset.univ ×ˢ Finset.Icc 1 n : Finset (Bool × ℕ)))
    (hsub : LorentzianNonnegLinearSubstitution
      ↥(Finset.univ ×ˢ Finset.Icc 1 n : Finset (Bool × ℕ)) (Fin 2))
    (hsub₂ : LorentzianNonnegLinearSubstitution (Fin 2) (Fin 2))
    (hmul : LorentzianMul (Fin 2)) :
    (aeval ![Polynomial.X, 1] (schroederFiberPolynomial ℝ C π) : Polynomial ℝ).IsUltraLogConcave
      n := by
  obtain rfl : π.length = n := hπ.2.1
  have hhom : (List.schroederFiberPolynomial ℝ C π).IsHomogeneous π.length :=
    schroederFiberPolynomial_induction (fun p => p.IsHomogeneous π.length)
      (isHomogeneous_zero _ _ _) (fun _ _ ha hb => ha.add hb)
      fun b w hbw => hbw ▸ (isHomogeneous_X_pow _ _).mul (isHomogeneous_X_pow _ _)
  have hcoeff := schroederFiberPolynomial_induction (C := C) (π := π)
    (fun p => ∀ i, 0 ≤ (aeval ![Polynomial.X, 1] p : Polynomial ℝ).coeff i) (by simp)
    (fun a b ha hb i => by simpa using add_nonneg (ha i) (hb i))
    fun b w _ i => by
      simp [Polynomial.coeff_X_pow]
      split_ifs <;> norm_num
  have hdeg := schroederFiberPolynomial_induction (C := C) (π := π)
    (fun p => (aeval ![Polynomial.X, 1] p : Polynomial ℝ).natDegree ≤ π.length) (by simp)
    (fun a b ha hb => by simpa using (Polynomial.natDegree_add_le _ _).trans (max_le ha hb))
    fun b w hbw => by simp; omega
  rw [← Polynomial.isLorentzian_homogenize_iff_isUltraLogConcave hcoeff hdeg,
    Polynomial.homogenize_eq_of_isHomogeneous hhom rfl]
  exact List.isLorentzian_schroederFiberPolynomial C hn hπ hBH hsub hsub₂ hmul

end List
