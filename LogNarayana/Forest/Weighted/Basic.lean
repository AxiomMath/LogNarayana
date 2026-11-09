/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib
public import LogNarayana.Attr
public import LogNarayana.Forest.Weighted.Defs
public import LogNarayana.Forest.PartialMatching.Defs
public import LogNarayana.Lorentzian.Hessian.Defs
public import LogNarayana.StackSorting.AdoptableForest.Defs
public import LogNarayana.Forest.LaminarMatroid.Defs
public import LogNarayana.Forest.OpenPairPolynomial.Defs
public import LogNarayana.Forest.Operations.Defs
public import LogNarayana.StackSorting.Matchings.Defs
public import LogNarayana.Forest.Operations.Basic
public import LogNarayana.Lorentzian.QuadraticKernel.Basic
public import LogNarayana.Lorentzian.Hessian.Basic
public import LogNarayana.Forest.OpenPairPolynomial.Basic
public import LogNarayana.Lorentzian.Convolution.Basic
public import LogNarayana.Lorentzian.BrandenHuh.Basic
public import LogNarayana.Lorentzian.Symbol.Basic
public import LogNarayana.StackSorting.Matchings.Basic
public import LogNarayana.Forest.LaminarMatroid.Basic

/-!
# Weighted forests

For a marked postorder forest `(par, L)` on `[N]` and polynomials `A, B ∈ ℝ[x]`, the weighted
open-pair polynomial `P^{A,B}_{par,L}(x, t)` is computed on two small examples: the marked tree
on `[3]` with root `3` and marked leaves `1, 2` gives `A t ^ 2 + t ^ 3 + B t`, and its factorial
normalization in `t` is `A t ^ 2 / 2! + t ^ 3 / 3! + B t`; two marked singletons side by side
give `t ^ 2`.

The main results are Lorentzian properties. If each vertex `v` carries a linear form
`A_v = a_vᵀ x` with `a_v ≥ 0` and a quadratic form `B_v` with nonnegative coefficients and
`Hess B_v - a_v a_vᵀ ⪯ 0`, then the factorial normalization `𝓝_t P^{A,B}_{par,L}` of the
vertex-weighted open-pair polynomial is Lorentzian. The proof is by strong induction on the
number of vertices: a marked postorder forest splits into a smaller marked forest followed by
either the marked singleton or a rooted marked tree; the normalized polynomial of a
concatenation is the `t`-derivative of the `t`-convolution of the two normalized polynomials,
and the normalized polynomial of a rooted tree is the root operator applied to the normalized
polynomial of the forest below the root. Taking constant families gives the weighted version,
and setting `t = 0`, a nonnegative linear substitution, shows that the sum
`∑_M B^{|M|} A^{N - 2|M|}` over the admissible matchings `M` of `(par, L)` is Lorentzian.

## Main results

* `weightedOpenPairPolynomial_rootRecurrenceExampleTree`:
  `P^{A,B}_{𝒯,{1,2}} = A t ^ 2 + t ^ 3 + B t`.
* `factorialNormalization_weightedOpenPairPolynomial_rootRecurrenceExampleTree`:
  `𝓝_t P^{A,B}_{𝒯,{1,2}} = A t ^ 2 / 2! + t ^ 3 / 3! + B t`.
* `weightedOpenPairPolynomial_markedSingleton_concat_markedSingleton`:
  `P^{A,B}_{𝒮 ⊔ 𝒮} = t ^ 2`.
* `isLorentzian_factorialNormalization_vertexWeightedOpenPairPolynomial`: the normalized
  vertex-weighted open-pair polynomial is Lorentzian.
* `isLorentzian_factorialNormalization_weightedOpenPairPolynomial`: the normalized weighted
  open-pair polynomial is Lorentzian.
* `isLorentzian_sum_admissibleMatching_pow_mul_pow`: `∑_M B^{|M|} A^{N - 2|M|}` is Lorentzian.

## Implementation notes

The variables `x` are indexed by a type `σ` (finite for the Lorentzian results, the paper's
`[p]`), and `t` is `X none` in `MvPolynomial (Option σ) ℝ`; polynomials in `x` are embedded by
`rename some`. The negative semidefiniteness `C ⪯ 0` is written as `w ⬝ᵥ C *ᵥ w ≤ 0` for all
`w : σ → ℝ`; the Hessian of a polynomial is symmetric, so this is the paper's condition. The
linear form `A` is `∑ i, a i • X i`. The results of Brändén–Huh the proofs use are taken as
hypotheses (`hsub`, `hmul`, `hsym`, `hBH`, `hder`), each quantified over all finite types in the
universe of `σ`, since the proofs use them at other types.

## References

* [LogNarayana] *Log-Concavity in Narayana Transforms and Stack-Sorting Fibers*, Sections 4
  and 7.
* [BH] P. Brändén, J. Huh, *Lorentzian polynomials*, Ann. of Math. 192 (2020).
-/

open MvPolynomial Matrix

universe u

/-! ### The root recurrence on the tree with two marked leaves -/

private lemma iterate_none (k : ℕ) :
    (fun o : Option ℕ => o.bind rootRecurrenceExampleTree.1)^[k] none = none := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply, Option.bind_none, ih]

private lemma isStrictAncestor_iff (b a : ℕ) :
    IsStrictAncestor rootRecurrenceExampleTree.1 b a ↔ b = 3 ∧ (a = 1 ∨ a = 2) := by
  constructor
  · rintro ⟨⟨k, hk⟩, hne⟩
    match k, hk with
    | 0, hk =>
      simp at hk
      exact absurd hk.symm hne
    | 1, hk =>
      simp only [Function.iterate_one, Option.bind_some, rootRecurrenceExampleTree] at hk
      split_ifs at hk with h
      · simp at hk
        exact ⟨hk.symm, h⟩
    | k + 2, hk =>
      rw [Function.iterate_add_apply, show (fun o : Option ℕ => o.bind
          rootRecurrenceExampleTree.1)^[2] (some a) = none by
        simp only [Function.iterate_succ_apply, Function.iterate_zero_apply, Option.bind_some,
          rootRecurrenceExampleTree]
        split_ifs <;> simp, iterate_none] at hk
      simp at hk
  · rintro ⟨rfl, ha⟩
    refine ⟨⟨1, ?_⟩, by omega⟩
    simp [rootRecurrenceExampleTree, ha]

private abbrev openPairPred (M : Finset (ℕ × ℕ)) (O : Finset ℕ) : Prop :=
  ((∀ p ∈ M, 1 ≤ p.1) ∧ (∀ p ∈ M, p.1 < p.2) ∧ (∀ p ∈ M, p.2 ≤ 3) ∧
    (∀ p ∈ M, ∀ q ∈ M, ∀ x ∈ ({p.1, p.2} : Finset ℕ), x ∈ ({q.1, q.2} : Finset ℕ) → p = q) ∧
    (∀ p ∈ M, ∀ q ∈ M, ¬ (p.1 < q.1 ∧ q.1 < p.2 ∧ p.2 < q.2))) ∧
  (∀ p ∈ M, p.2 = 3 ∧ (p.1 = 1 ∨ p.1 = 2)) ∧
  O ⊆ Finset.unmatchedVertices 3 M ∧
  (∀ u ∈ O, ∀ p ∈ M, ¬ (p.1 < u ∧ u < p.2)) ∧
  ({1, 2} : Finset ℕ) ⊆ M.leftEndpoints ∪ O

private lemma isOpenPair_iff (M : Finset (ℕ × ℕ)) (O : Finset ℕ) :
    IsOpenPair 3 rootRecurrenceExampleTree.1 rootRecurrenceExampleTree.2 M O ↔
      openPairPred M O := by
  simp only [openPairPred, ← isStrictAncestor_iff]
  constructor
  · rintro ⟨⟨h1, h2, h3, h4, h5⟩, h6, h7, h8, h9⟩
    exact ⟨⟨h1, h2, h3, fun p hp q hq x hx hx' => h4 p hp q hq x (by simpa using hx)
      (by simpa using hx'), h5⟩, h6, h7, h8, h9⟩
  · rintro ⟨⟨h1, h2, h3, h4, h5⟩, h6, h7, h8, h9⟩
    exact ⟨⟨h1, h2, h3, fun p hp q hq x hx hx' => h4 p hp q hq x (by simp [hx])
      (by simp [hx']), h5⟩, h6, h7, h8, h9⟩

open scoped Classical in
/-- The open pairs of `rootRecurrenceExampleTree` on `[3]` are `(∅, {1, 2})`, `(∅, {1, 2, 3})`
and `({(2, 3)}, {1})`. Every pair of a matching must be `(1, 3)` or `(2, 3)`, which cuts the
search down to `32` candidates, decided directly. -/
private lemma openPairs_eq :
    ((Finset.Icc 1 3 ×ˢ Finset.Icc 1 3).powerset ×ˢ (Finset.Icc 1 3).powerset).filter
        (fun MO : Finset (ℕ × ℕ) × Finset ℕ =>
          IsOpenPair 3 rootRecurrenceExampleTree.1 rootRecurrenceExampleTree.2 MO.1 MO.2) =
      {(∅, {1, 2}), (∅, {1, 2, 3}), ({(2, 3)}, {1})} := by
  rw [Finset.filter_congr (fun MO _ => isOpenPair_iff MO.1 MO.2)]
  refine .trans ?_ (show (({(1, 3), (2, 3)} : Finset (ℕ × ℕ)).powerset ×ˢ
      (Finset.Icc 1 3).powerset).filter (fun MO => openPairPred MO.1 MO.2) =
        {(∅, {1, 2}), (∅, {1, 2, 3}), ({(2, 3)}, {1})} by decide)
  ext ⟨M, O⟩
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_powerset]
  refine ⟨fun ⟨⟨_, hO⟩, h⟩ => ⟨⟨fun p hp => ?_, hO⟩, h⟩,
    fun ⟨⟨hM, hO⟩, h⟩ => ⟨⟨hM.trans (by decide), hO⟩, h⟩⟩
  obtain ⟨h1, h2⟩ := h.2.1 p hp
  obtain ⟨a, b⟩ := p
  rcases h2 with rfl | rfl <;> subst h1 <;> simp

/-- The weighted open-pair polynomial of the marked tree `(𝒯, {1, 2})` on `[3]` with root `3`
and marked leaves `1, 2` is `A t ^ 2 + t ^ 3 + B t`, for all `A, B ∈ ℝ[x]`. -/
@[lognarayana "lem_ex_root_recurrence"]
public theorem weightedOpenPairPolynomial_rootRecurrenceExampleTree {σ : Type*}
    (A B : MvPolynomial σ ℝ) :
    weightedOpenPairPolynomial 3 rootRecurrenceExampleTree.1 rootRecurrenceExampleTree.2 A B =
      rename some A * X none ^ 2 + X none ^ 3 + rename some B * X none := by
  rw [weightedOpenPairPolynomial, vertexWeightedOpenPairPolynomial, openPairs_eq,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
    show Finset.unmatchedVertices 3 ∅ \ {1, 2} = {3} by decide,
    show Finset.unmatchedVertices 3 ∅ \ {1, 2, 3} = ∅ by decide,
    show Finset.unmatchedVertices 3 {(2, 3)} \ {1} = ∅ by decide]
  simp
  ring

/-! ### The normalized root recurrence -/

section FactorialNormalization

variable {σ R : Type*} [CommSemiring R] [Algebra ℚ R]

omit [Algebra ℚ R] in
/-- A linear map built by `Basis.constr` on the monomial basis, evaluated on a monomial. -/
private lemma constr_basisMonomials_monomial (g : (σ →₀ ℕ) → MvPolynomial σ R) (α : σ →₀ ℕ)
    (c : R) : (basisMonomials σ R).constr R g (monomial α c) = c • g α := by
  rw [← mul_one c, ← smul_eq_mul, ← smul_monomial, map_smul, ← congrFun (coe_basisMonomials σ R) α,
    Module.Basis.constr_basis, smul_eq_mul, mul_one]

/-- The value of `factorialNormalization t` on a monomial. -/
private lemma factorialNormalization_monomial (t : σ) (α : σ →₀ ℕ) (c : R) :
    factorialNormalization t (monomial α c) =
      monomial α (c * algebraMap ℚ R (1 / ((α t).factorial : ℚ))) := by
  rw [factorialNormalization, constr_basisMonomials_monomial, smul_monomial, smul_eq_mul]

/-- `factorialNormalization t` commutes with multiplication by a polynomial free of `t`. -/
private lemma factorialNormalization_mul_left (t : σ) {A : MvPolynomial σ R} (hA : t ∉ A.vars)
    (P : MvPolynomial σ R) :
    factorialNormalization t (A * P) = A * factorialNormalization t P := by
  classical
  induction P using MvPolynomial.induction_on' with
  | add p q hp hq => rw [mul_add, map_add, hp, hq, map_add, mul_add]
  | monomial α c =>
    conv_lhs => rw [A.as_sum]
    conv_rhs => rw [A.as_sum]
    rw [Finset.sum_mul, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun v hv => ?_
    have hvt : v t = 0 := Finsupp.notMem_support_iff.1 fun h =>
      hA ((mem_vars_iff_mem_support t).2 ⟨v, hv, h⟩)
    rw [factorialNormalization_monomial, monomial_mul, monomial_mul,
      factorialNormalization_monomial, Finsupp.add_apply, hvt, zero_add, mul_assoc]

/-- `factorialNormalization t (t ^ k) = t ^ k / k!`. -/
private lemma factorialNormalization_X_pow (t : σ) (k : ℕ) :
    factorialNormalization t (X t ^ k : MvPolynomial σ R) =
      algebraMap ℚ R (1 / (k.factorial : ℚ)) • X t ^ k := by
  classical
  rw [X_pow_eq_monomial, factorialNormalization_monomial, smul_monomial, one_mul, smul_eq_mul,
    mul_one, Finsupp.single_eq_same]

end FactorialNormalization

/-- A polynomial renamed along `some` does not involve the new variable `none`. -/
private lemma none_notMem_vars_rename {τ : Type*} (A : MvPolynomial τ ℝ) :
    (none : Option τ) ∉ (rename some A).vars := by
  classical
  intro h
  obtain ⟨i, -, hi⟩ := Finset.mem_image.1 (vars_rename some A h)
  exact Option.some_ne_none i hi

/-- The factorial normalization in `t` of the weighted open-pair polynomial of the marked tree
`(𝒯, {1, 2})` on `[3]` with root `3` and marked leaves `1, 2` is
`A t ^ 2 / 2! + t ^ 3 / 3! + B t`, for all `A, B ∈ ℝ[x]`. -/
@[lognarayana "lem_ex_root_recurrence_normalized"]
public theorem factorialNormalization_weightedOpenPairPolynomial_rootRecurrenceExampleTree
    {σ : Type*} (A B : MvPolynomial σ ℝ) :
    factorialNormalization none
        (weightedOpenPairPolynomial 3 rootRecurrenceExampleTree.1 rootRecurrenceExampleTree.2
          A B) =
      rename some A * ((1 / (Nat.factorial 2 : ℝ)) • X none ^ 2) +
        (1 / (Nat.factorial 3 : ℝ)) • X none ^ 3 + rename some B * X none := by
  rw [weightedOpenPairPolynomial_rootRecurrenceExampleTree, map_add, map_add,
    factorialNormalization_mul_left _ (none_notMem_vars_rename A),
    factorialNormalization_mul_left _ (none_notMem_vars_rename B),
    factorialNormalization_X_pow, factorialNormalization_X_pow,
    ← pow_one (X none : MvPolynomial (Option σ) ℝ), factorialNormalization_X_pow]
  simp

/-! ### Two marked singletons -/

/-- The parent map of the marked singleton is a parent map on `[1]`: its only vertex is a root. -/
private lemma isParentMap_markedSingleton : IsParentMap 1 markedSingleton.1 :=
  fun _ _ h => by simp [markedSingleton] at h

/-- The weighted open-pair polynomial of the concatenation `𝒮 ⊔ 𝒮` of two marked singletons is
`t ^ 2`, for all `A, B ∈ ℝ[x]`. -/
@[lognarayana "lem_ex_two_marked_singletons"]
public theorem weightedOpenPairPolynomial_markedSingleton_concat_markedSingleton {σ : Type*}
    (A B : MvPolynomial σ ℝ) :
    weightedOpenPairPolynomial (1 + 1)
        (forestConcatParent 1 markedSingleton.1 markedSingleton.1)
        (forestConcatMarked 1 markedSingleton.2 markedSingleton.2) A B =
      X none ^ 2 := by
  rw [weightedOpenPairPolynomial,
    vertexWeightedOpenPairPolynomial_forestConcat isParentMap_markedSingleton
      (by simp [markedSingleton]) isParentMap_markedSingleton
      (by simp [markedSingleton]),
    vertexWeightedOpenPairPolynomial_markedSingleton, sq]

/-! ### Vertex-weighted open-pair polynomials are Lorentzian after normalization -/

/-- The Hessian at the origin of a real polynomial is symmetric. -/
private lemma isHermitian_hessianAtZero {σ : Type*} (g : MvPolynomial σ ℝ) :
    (hessianAtZero g).IsHermitian := by
  ext i j
  simp [hessianAtZero, add_comm]

/-- The paper's `Hess B - a aᵀ ⪯ 0`, written with quadratic forms, as positive semidefiniteness
of the negative. -/
private lemma posSemidef_neg_of_forall {σ : Type*} [Fintype σ] {a : σ → ℝ}
    {B : MvPolynomial σ ℝ}
    (h : ∀ w : σ → ℝ, w ⬝ᵥ ((hessianAtZero B - vecMulVec a a) *ᵥ w) ≤ 0) :
    (-(hessianAtZero B - vecMulVec a a)).PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun w => ?_
  · refine ((isHermitian_hessianAtZero B).sub ?_).neg
    ext i j
    simp [vecMulVec_apply, mul_comm]
  · rw [star_trivial, neg_mulVec, dotProduct_neg]
    exact neg_nonneg.mpr (h w)

/-- If `𝓝_t P` and `𝓝_t Q` are Lorentzian, so is `𝓝_t (P Q)`. -/
private lemma isLorentzian_factorialNormalization_mul {σ : Type u} [Fintype σ]
    (hsub : ∀ (σ τ : Type u) [Fintype σ] [Fintype τ], LorentzianNonnegLinearSubstitution σ τ)
    (hmul : ∀ (σ : Type u) [Fintype σ], LorentzianMul σ)
    (hsym : ∀ (σ τ : Type u) [Fintype σ] [Fintype τ], BrandenHuhSymbolTheorem σ τ)
    (hBH : ∀ (σ : Type u) [Fintype σ], NormalizedSupportPolyLorentzianOfMConvex σ)
    (hder : ∀ (σ : Type u) [Fintype σ], LorentzianNonnegDerivative σ)
    {P Q : MvPolynomial (Option σ) ℝ}
    (hP : (factorialNormalization none P).IsLorentzian)
    (hQ : (factorialNormalization none Q).IsLorentzian) :
    (factorialNormalization none (P * Q)).IsLorentzian := by
  classical
  rw [factorialNormalization_mul]
  simpa [Pi.single_apply] using hder (Option σ) (Pi.single none 1) (fun i => by
    by_cases hi : i = none <;> simp [hi]) _
    (IsLorentzian.tConvolution hsub hmul hsym hBH hP hQ)

/-- If `𝓝_t P` is Lorentzian, then so is `𝓝_t ((A + t) P + B δ_t P)` for a kernel pair
`A = aᵀ x`, `B`. -/
private lemma isLorentzian_factorialNormalization_adjoinRoot {σ : Type u} [Fintype σ]
    (hsub : ∀ (σ τ : Type u) [Fintype σ] [Fintype τ], LorentzianNonnegLinearSubstitution σ τ)
    (hmul : ∀ (σ : Type u) [Fintype σ], LorentzianMul σ)
    (hsym : ∀ (σ τ : Type u) [Fintype σ] [Fintype τ], BrandenHuhSymbolTheorem σ τ)
    (hBH : ∀ (σ : Type u) [Fintype σ], NormalizedSupportPolyLorentzianOfMConvex σ)
    (hder : ∀ (σ : Type u) [Fintype σ], LorentzianNonnegDerivative σ)
    {a : σ → ℝ} (ha : ∀ i, 0 ≤ a i) {B : MvPolynomial σ ℝ} (hB : B.IsHomogeneous 2)
    (hBnn : B.HasNonnegCoeffs)
    (hHess : ∀ w : σ → ℝ, w ⬝ᵥ ((hessianAtZero B - vecMulVec a a) *ᵥ w) ≤ 0)
    {P : MvPolynomial (Option σ) ℝ} (hP : (factorialNormalization none P).IsLorentzian) :
    (factorialNormalization none ((rename some (∑ i, a i • X i) + X none) * P +
      rename some B * divX none P)).IsLorentzian := by
  classical
  rw [factorialNormalization_add_X_mul_add_mul_divX none (none_notMem_vars_rename _)
    (none_notMem_vars_rename _)]
  simp only [smul_eq_C_mul]
  exact isLorentzian_rootOperator hsub hmul hBH hsym hder ha hB hBnn
    (posSemidef_neg_of_forall hHess) hP

/-- The factorial normalization `𝓝_t` fixes every monomial of degree at most one in `t`. -/
private lemma factorialNormalization_monomial_of_le_one {σ : Type*} (t : σ) {α : σ →₀ ℕ}
    (hα : α t ≤ 1) (c : ℝ) : factorialNormalization t (monomial α c) = monomial α c := by
  rw [factorialNormalization_monomial]
  interval_cases α t <;> simp

/-- A monomial of total degree at most one with coefficient in `[0, 1]` is Lorentzian. -/
private lemma isLorentzian_monomial {σ : Type*} [Fintype σ] {α : σ →₀ ℕ} (hα : α.degree ≤ 1)
    {c : ℝ} (hc₀ : 0 ≤ c) : (monomial α c).IsLorentzian := by
  classical
  exact IsLorentzian.of_isHomogeneous_of_le_one (d := α.degree)
    (fun m => by rw [coeff_monomial]; split_ifs <;> linarith)
    (isHomogeneous_monomial _ (by rw [Finsupp.degree_eq_weight_one])) hα

/-- On the empty forest the open-pair polynomial is `1` or `0`. -/
private lemma vertexWeightedOpenPairPolynomial_zero {σ : Type*} (par : ℕ → Option ℕ)
    (L : Finset ℕ) (A B : ℕ → MvPolynomial σ ℝ) :
    vertexWeightedOpenPairPolynomial 0 par L A B = 0 ∨
      vertexWeightedOpenPairPolynomial 0 par L A B = 1 := by
  classical
  unfold vertexWeightedOpenPairPolynomial
  simp only [zero_lt_one, Finset.Icc_eq_empty_of_lt, Finset.empty_product,
    Finset.powerset_empty, Finset.singleton_product_singleton]
  rw [Finset.filter_singleton]
  split_ifs
  · simp [Finset.unmatchedVertices]
  · simp

/-- The vertex conditions of the paper: `a_v ≥ 0`, `B_v` a quadratic form with nonnegative
coefficients, and `Hess B_v - a_v a_vᵀ ⪯ 0`. -/
private def VertexCondition {σ : Type*} [Fintype σ] (a : σ → ℝ) (B : MvPolynomial σ ℝ) : Prop :=
  (∀ i, 0 ≤ a i) ∧ B.IsHomogeneous 2 ∧ B.HasNonnegCoeffs ∧
    ∀ w : σ → ℝ, w ⬝ᵥ ((hessianAtZero B - vecMulVec a a) *ᵥ w) ≤ 0

/-- The induction on the number of vertices: if every vertex satisfies the kernel conditions,
then `𝓝_t P_{(par, L)}` is Lorentzian. The step splits off the last tree, which is either the
marked singleton (`𝓝_t t = t`) or a root over a smaller marked forest. -/
private theorem isLorentzian_of_vertexCondition {σ : Type u} [Fintype σ]
    (hsub : ∀ (σ τ : Type u) [Fintype σ] [Fintype τ], LorentzianNonnegLinearSubstitution σ τ)
    (hmul : ∀ (σ : Type u) [Fintype σ], LorentzianMul σ)
    (hsym : ∀ (σ τ : Type u) [Fintype σ] [Fintype τ], BrandenHuhSymbolTheorem σ τ)
    (hBH : ∀ (σ : Type u) [Fintype σ], NormalizedSupportPolyLorentzianOfMConvex σ)
    (hder : ∀ (σ : Type u) [Fintype σ], LorentzianNonnegDerivative σ)
    (n : ℕ) {par : ℕ → Option ℕ} {L : Finset ℕ}
    (hpar : IsPostorderForest n par) (hL : L ⊆ Finset.Icc 1 n) (hLleaf : ∀ v ∈ L, IsLeaf par v)
    (a : ℕ → σ → ℝ) (B : ℕ → MvPolynomial σ ℝ)
    (hw : ∀ v ∈ Finset.Icc 1 n, VertexCondition (a v) (B v)) :
    (factorialNormalization (none : Option σ)
      (vertexWeightedOpenPairPolynomial n par L (fun v => ∑ i, a v i • X i) B)).IsLorentzian := by
  classical
  induction n using Nat.strong_induction_on generalizing par L a B with
  | _ n ih =>
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rcases vertexWeightedOpenPairPolynomial_zero par L (fun v => ∑ i, a v i • X i) B with h | h
    · rw [h, map_zero]
      exact Or.inl rfl
    · rw [h, ← C_1, ← monomial_zero', factorialNormalization_monomial_of_le_one _ (by simp)]
      exact isLorentzian_monomial (by simp) zero_le_one
  obtain ⟨N₁, N₂, rfl, hN₂, par₁, L₁, ⟨hpar₁, hL₁, hLleaf₁⟩, parG, LG, ⟨hparG, hLG, hLleafG⟩,
    rfl, rfl, hG⟩ := exists_forestConcat_eq_of_isPostorderForest hpar hL hLleaf hn
  rw [vertexWeightedOpenPairPolynomial_forestConcat hpar₁.1 hL₁ hparG.1 hLG]
  refine isLorentzian_factorialNormalization_mul hsub hmul hsym hBH hder
    (ih N₁ (by omega) hpar₁ hL₁ hLleaf₁ a B fun v hv => hw v ?_) ?_
  · simp only [Finset.mem_Icc] at hv ⊢
    omega
  have hw' : ∀ v ∈ Finset.Icc 1 N₂, VertexCondition (a (N₁ + v)) (B (N₁ + v)) := fun v hv =>
    hw (N₁ + v) (by simp only [Finset.mem_Icc] at hv ⊢; omega)
  rcases hG with ⟨hS, rfl⟩ | ⟨par₂, L₂, ⟨hpar₂, hL₂, hLleaf₂⟩, rfl, rfl⟩
  · obtain ⟨rfl, rfl⟩ : parG = markedSingleton.1 ∧ LG = markedSingleton.2 := Prod.mk.inj hS
    rw [vertexWeightedOpenPairPolynomial_markedSingleton, X,
      factorialNormalization_monomial_of_le_one _ (by simp)]
    exact isLorentzian_monomial (by simp) zero_le_one
  · obtain ⟨M, rfl⟩ : ∃ M, N₂ = M + 1 := ⟨N₂ - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at hpar₂ hL₂ hparG ⊢
    rw [vertexWeightedOpenPairPolynomial_forestAdjoinRoot hpar₂.1 hL₂]
    obtain ⟨ha₀, hB₀, hBnn₀, hH₀⟩ := hw' (M + 1) (by simp)
    exact isLorentzian_factorialNormalization_adjoinRoot hsub hmul hsym hBH hder ha₀ hB₀ hBnn₀
      hH₀ (ih M (by omega) hpar₂ hL₂ hLleaf₂ (fun v => a (N₁ + v)) (fun v => B (N₁ + v))
        fun v hv => hw' v (by simp only [Finset.mem_Icc] at hv ⊢; omega))

/-- For a marked postorder forest `(par, L)` on `[N]`, linear forms `A_v = a_vᵀ x` with
`a_v ≥ 0`, and quadratic forms `B_v` with nonnegative coefficients and
`Hess B_v - a_v a_vᵀ ⪯ 0`, the factorial normalization `𝓝_t P^{A,B}_{par,L}(x, t)` of the
vertex-weighted open-pair polynomial is Lorentzian. -/
@[lognarayana "thm_weighted_forest_lorentzian_vertex"]
public theorem isLorentzian_factorialNormalization_vertexWeightedOpenPairPolynomial
    {σ : Type u} [Fintype σ] {N : ℕ} {par : ℕ → Option ℕ} {L : Finset ℕ}
    (hsub : ∀ (σ τ : Type u) [Fintype σ] [Fintype τ], LorentzianNonnegLinearSubstitution σ τ)
    (hmul : ∀ (σ : Type u) [Fintype σ], LorentzianMul σ)
    (hsym : ∀ (σ τ : Type u) [Fintype σ] [Fintype τ], BrandenHuhSymbolTheorem σ τ)
    (hBH : ∀ (σ : Type u) [Fintype σ], NormalizedSupportPolyLorentzianOfMConvex σ)
    (hder : ∀ (σ : Type u) [Fintype σ], LorentzianNonnegDerivative σ)
    (hpar : IsPostorderForest N par) (hL : L ⊆ Finset.Icc 1 N)
    (hLleaf : ∀ v ∈ L, IsLeaf par v)
    (a : ℕ → σ → ℝ) (B : ℕ → MvPolynomial σ ℝ)
    (ha : ∀ v ∈ Finset.Icc 1 N, ∀ i, 0 ≤ a v i)
    (hB : ∀ v ∈ Finset.Icc 1 N, (B v).IsHomogeneous 2)
    (hBnn : ∀ v ∈ Finset.Icc 1 N, (B v).HasNonnegCoeffs)
    (hHess : ∀ v ∈ Finset.Icc 1 N, ∀ w : σ → ℝ,
      w ⬝ᵥ ((hessianAtZero (B v) - Matrix.vecMulVec (a v) (a v)) *ᵥ w) ≤ 0) :
    (factorialNormalization (none : Option σ)
      (vertexWeightedOpenPairPolynomial N par L (fun v => ∑ i, a v i • X i) B)).IsLorentzian :=
  isLorentzian_of_vertexCondition hsub hmul hsym hBH hder N hpar hL hLleaf a B fun v hv =>
    ⟨ha v hv, hB v hv, hBnn v hv, hHess v hv⟩

/-! ### Weighted open-pair polynomials are Lorentzian after normalization -/

/-- For a marked postorder forest `(par, L)` on `[N]`, a linear form `A = aᵀ x` with `a ≥ 0`,
and a quadratic form `B` with nonnegative coefficients and `Hess B - a aᵀ ⪯ 0`, the factorial
normalization `𝓝_t P^{A,B}_{par,L}(x, t)` of the weighted open-pair polynomial is
Lorentzian. -/
@[lognarayana "thm_weighted_forest_lorentzian"]
public theorem isLorentzian_factorialNormalization_weightedOpenPairPolynomial
    {σ : Type u} [Fintype σ] {N : ℕ} {par : ℕ → Option ℕ} {L : Finset ℕ}
    (hsub : ∀ (σ τ : Type u) [Fintype σ] [Fintype τ], LorentzianNonnegLinearSubstitution σ τ)
    (hmul : ∀ (σ : Type u) [Fintype σ], LorentzianMul σ)
    (hsym : ∀ (σ τ : Type u) [Fintype σ] [Fintype τ], BrandenHuhSymbolTheorem σ τ)
    (hBH : ∀ (σ : Type u) [Fintype σ], NormalizedSupportPolyLorentzianOfMConvex σ)
    (hder : ∀ (σ : Type u) [Fintype σ], LorentzianNonnegDerivative σ)
    (hpar : IsPostorderForest N par) (hL : L ⊆ Finset.Icc 1 N)
    (hLleaf : ∀ v ∈ L, IsLeaf par v)
    (a : σ → ℝ) (B : MvPolynomial σ ℝ)
    (ha : ∀ i, 0 ≤ a i) (hB : B.IsHomogeneous 2) (hBnn : B.HasNonnegCoeffs)
    (hHess : ∀ w : σ → ℝ, w ⬝ᵥ ((hessianAtZero B - Matrix.vecMulVec a a) *ᵥ w) ≤ 0) :
    (factorialNormalization (none : Option σ)
      (weightedOpenPairPolynomial N par L (∑ i, a i • X i) B)).IsLorentzian :=
  isLorentzian_factorialNormalization_vertexWeightedOpenPairPolynomial hsub hmul hsym hBH hder
    hpar hL hLleaf (fun _ => a) (fun _ => B) (fun _ _ => ha) (fun _ _ => hB) (fun _ _ => hBnn)
    (fun _ _ => hHess)

/-! ### Weighted admissible-matching polynomials are Lorentzian -/

/-- Evaluating at `t = 0` (`X none ↦ 0`, `X (some i) ↦ X i`) kills the factorial
normalization in `t`. -/
private lemma aeval_evalNone_factorialNormalization {σ : Type*} (f : MvPolynomial (Option σ) ℝ) :
    aeval (fun i : Option σ => i.elim (0 : MvPolynomial σ ℝ) X)
        (factorialNormalization none f) =
      aeval (fun i : Option σ => i.elim (0 : MvPolynomial σ ℝ) X) f := by
  induction f using MvPolynomial.induction_on' with
  | monomial α c =>
    have h : monomial α c = c • (basisMonomials (Option σ) ℝ) α := by
      simp [coe_basisMonomials, smul_monomial]
    rw [h, map_smul, factorialNormalization, Module.Basis.constr_basis, smul_monomial,
      smul_eq_mul, ← h]
    simp only [aeval_monomial, algebraMap_eq, Finsupp.prod]
    by_cases hα : α none = 0
    · simp [hα]
    · have h0 : ∏ i ∈ α.support, (Option.elim i (0 : MvPolynomial σ ℝ) X) ^ α i = 0 :=
        Finset.prod_eq_zero (i := none) (Finsupp.mem_support_iff.2 hα) (by simp [hα])
      simp [h0]
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]

/-- `P^{A,B}_{par,L}(x, 0)` is the sum of `B^{|M|} A^{N - 2|M|}` over the admissible matchings. -/
private lemma aeval_evalNone_weightedOpenPairPolynomial {σ : Type*} (N : ℕ)
    (par : ℕ → Option ℕ) (L : Finset ℕ) (A B : MvPolynomial σ ℝ) :
    aeval (fun i : Option σ => i.elim (0 : MvPolynomial σ ℝ) X)
        (weightedOpenPairPolynomial N par L A B) =
      open scoped Classical in
      ∑ M ∈ (Finset.Icc 1 N ×ˢ Finset.Icc 1 N).powerset.filter
        (fun M : Finset (ℕ × ℕ) => IsAdmissibleMatching N par L M),
      B ^ M.card * A ^ (N - 2 * M.card) := by
  classical
  simp only [weightedOpenPairPolynomial, vertexWeightedOpenPairPolynomial, map_sum, map_mul,
    map_pow, aeval_rename, Function.comp_def, Option.elim_some, aeval_X_left_apply,
    aeval_X, Option.elim_none, Finset.prod_const]
  rw [Finset.sum_filter, Finset.sum_product, Finset.sum_filter]
  refine Finset.sum_congr rfl fun M _ => ?_
  rw [Finset.sum_eq_single (∅ : Finset ℕ)]
  · simp only [Finset.card_empty, pow_zero, one_mul, Finset.sdiff_empty,
      isOpenPair_empty_iff_isAdmissibleMatching]
    split_ifs with h
    · have hc := h.isNoncrossingPartialMatching.card_unmatchedVertices_add_two_mul_card
      congr 2
      omega
    · rfl
  · intro O _ hO
    split_ifs <;> simp [zero_pow (Finset.card_ne_zero.2 (Finset.nonempty_iff_ne_empty.2 hO))]
  · simp

/-- Setting `t = 0` (`X none ↦ 0`, `X (some i) ↦ X i`) preserves the Lorentzian property: it is
the nonnegative linear substitution by the 0/1 matrix `[i = some j]`. -/
private lemma isLorentzian_aeval_evalNone {σ : Type u} [Fintype σ]
    (hsub : LorentzianNonnegLinearSubstitution (Option σ) σ) {f : MvPolynomial (Option σ) ℝ}
    (hf : f.IsLorentzian) :
    (aeval (fun i : Option σ => i.elim (0 : MvPolynomial σ ℝ) X) f).IsLorentzian := by
  classical
  convert hsub (fun i j => if i = some j then 1 else 0) (fun i j => by split_ifs <;> norm_num) f hf
    using 3
  funext i
  cases i <;> simp [ite_smul]

open Classical in
/-- For a marked postorder forest `(par, L)` on `[N]`, a linear form `A = aᵀ x` with `a ≥ 0`, and a
quadratic form `B` with nonnegative coefficients and `Hess B - a aᵀ ⪯ 0`, the polynomial
`∑_M B^{|M|} A^{N - 2|M|}`, summed over the admissible matchings `M` of `(par, L)`, is
Lorentzian. -/
@[lognarayana "thm_weighted_matching_lorentzian"]
public theorem isLorentzian_sum_admissibleMatching_pow_mul_pow
    {σ : Type u} [Fintype σ]
    (hsub : ∀ (σ τ : Type u) [Fintype σ] [Fintype τ], LorentzianNonnegLinearSubstitution σ τ)
    (hmul : ∀ (σ : Type u) [Fintype σ], LorentzianMul σ)
    (hsym : ∀ (σ τ : Type u) [Fintype σ] [Fintype τ], BrandenHuhSymbolTheorem σ τ)
    (hBH : ∀ (σ : Type u) [Fintype σ], NormalizedSupportPolyLorentzianOfMConvex σ)
    (hder : ∀ (σ : Type u) [Fintype σ], LorentzianNonnegDerivative σ)
    {N : ℕ} {par : ℕ → Option ℕ} {L : Finset ℕ}
    (hpar : IsPostorderForest N par) (hL : L ⊆ Finset.Icc 1 N)
    (hLleaf : ∀ v ∈ L, IsLeaf par v)
    (a : σ → ℝ) (B : MvPolynomial σ ℝ)
    (ha : ∀ i, 0 ≤ a i) (hB : B.IsHomogeneous 2) (hBnn : B.HasNonnegCoeffs)
    (hHess : ∀ w : σ → ℝ, w ⬝ᵥ ((hessianAtZero B - Matrix.vecMulVec a a) *ᵥ w) ≤ 0) :
    (∑ M ∈ (Finset.Icc 1 N ×ˢ Finset.Icc 1 N).powerset.filter
        (fun M : Finset (ℕ × ℕ) => IsAdmissibleMatching N par L M),
      B ^ M.card * (∑ i, a i • X i) ^ (N - 2 * M.card)).IsLorentzian := by
  have h := isLorentzian_aeval_evalNone (hsub _ σ)
    (isLorentzian_factorialNormalization_weightedOpenPairPolynomial
      hsub hmul hsym hBH hder hpar hL hLleaf a B ha hB hBnn hHess)
  rw [aeval_evalNone_factorialNormalization, aeval_evalNone_weightedOpenPairPolynomial] at h
  convert h
