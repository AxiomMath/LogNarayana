/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib
public import LogNarayana.Attr
public import LogNarayana.StackSorting.Descents.Defs
public import LogNarayana.StackSorting.FiberPolynomials.Defs
public import LogNarayana.StackSorting.Matchings.Defs
public import LogNarayana.Troupe.LocalRules.Defs
public import LogNarayana.StackSorting.StackSort.Defs
public import LogNarayana.Troupe.PostorderPolynomial.Defs
public import LogNarayana.Polynomial.LogConcave.Defs
public import LogNarayana.BinaryTree.Colored.Defs
public import LogNarayana.Troupe.PostorderPolynomial.Basic
public import LogNarayana.StackSorting.Matchings.Basic
public import LogNarayana.Polynomial.LogConcave.Basic
public import LogNarayana.Lorentzian.Bivariate
public import LogNarayana.Lorentzian.Hessian.Basic
public import LogNarayana.Lorentzian.BrandenHuh.Basic
public import LogNarayana.Lorentzian.Symbol.Basic
public import LogNarayana.StackSorting.Peaks

/-!
# Local colors: ultra-log-concavity

Let `X_L, X_a, X_b` be finite sets of colors with `|X_L| = L`, `|X_a| = a`, `|X_b| = b`, and let
`𝐔 = 𝐔_{X_L,X_a,X_b}` be the troupe of decreasing colored trees whose leaves are colored from
`X_L`, left-unary vertices from `X_a` and right-unary vertices from `X_b`. For `n ≥ 1` and
`π ∈ S_n`, the fiber descent polynomial is a sum over the matchings of `π`,
`D_{π,𝐔}(x) = L ∑_{M ∈ 𝒜(π)} (L x)^{|M|} (a + b x)^{n - 1 - 2|M|}`. Its degree `n - 1`
homogenization is `L ∑_j γ_{π,j} (Lxy)^j (ay + bx)^{n-1-2j}`, which for `a, b ≥ 1` is the
rescaled peak polynomial `L a^{n-1} H^{L/(ab)}_π((b/a) x, y)`. When `L ≤ 2ab` the parameter
`L/(ab)` lies in `[0, 2]`, so this is Lorentzian, and `D_{π,𝐔}` is ultra-log-concave of order
`n - 1`, hence log-concave.

## Main results

* `List.familyFiberDescentPolynomial_localColorFamily`: `D_{π,𝐔}` as a sum over matchings.
* `List.homogenize_familyFiberDescentPolynomial_localColorFamily`: the homogenization in
  `γ`-form.
* `List.homogenize_familyFiberDescentPolynomial_localColorFamily_eq_fiberPeakPolynomial`: the
  homogenization in peak form.
* `List.isUltraLogConcave_familyFiberDescentPolynomial_localColorFamily`: `D_{π,𝐔}` is
  ultra-log-concave of order `n - 1` when `L ≤ 2ab`.
* `List.isLogConcave_familyFiberDescentPolynomial_localColorFamily`: `D_{π,𝐔}` is log-concave
  when `L ≤ 2ab`.

## Implementation notes

The homogenization is Mathlib's `Polynomial.homogenize`, with `x = X 0` and `y = X 1`. The
sets of colors are finite sets `X_L, X_a, X_b : Finset C`, so that `|X_j| = j` is
`Finset.card`. The paper's requirement that each `X_j` contain black is not used. The cited
results of Brändén–Huh enter the two main theorems as hypotheses.

## References

* [LogNarayana] *Log-Concavity in Narayana Transforms and Stack-Sorting Fibers*, Sections 5
  and 6.
-/

/-! ### The fiber descent polynomial as a sum over matchings -/

section MatchingSum

open Polynomial BinaryTree

namespace BinaryTree

/-- The product of the weight `1` over all vertices is `1`. -/
private lemma rec_mul_eq_one {α R : Type*} [CommSemiring R] (T : BinaryTree α) :
    BinaryTree.rec (motive := fun _ => R) 1 (fun _ _ _ ihl ihr => ihl * ihr) T = 1 := by
  induction T with
  | nil => rfl
  | node a l r ihl ihr => simp only [ihl, ihr, mul_one]

/-- A product over the vertices of a weight depending only on the vertex type, in terms of the
vertex-type counts. -/
private lemma rec_vertexType_eq {α R : Type*} [CommSemiring R] (g : VertexType → R)
    (T : BinaryTree α) :
    BinaryTree.rec (motive := fun _ => R) 1 (fun _ l r ihl ihr => g (vertexType l r) * ihl * ihr)
        T =
      g .leaf ^ T.numNodesOfType .leaf * g .leftUnary ^ T.numNodesOfType .leftUnary *
        g .rightUnary ^ T.numNodesOfType .rightUnary * g .binary ^ T.numNodesOfType .binary := by
  induction T with
  | nil => simp
  | node a l r ihl ihr =>
    change g (vertexType l r) * _ * _ = _
    rw [ihl, ihr]
    cases l <;> cases r <;> simp [vertexType, pow_add] <;> ring

/-- The four vertex-type counts add up to the number of vertices. -/
private lemma sum_numNodesOfType {α : Type*} (T : BinaryTree α) :
    T.numNodesOfType .leaf + T.numNodesOfType .leftUnary + T.numNodesOfType .rightUnary +
      T.numNodesOfType .binary = T.postorder.length := by
  induction T with
  | nil => simp
  | node a l r ihl ihr =>
    cases l <;> cases r <;> simp [vertexType] at ihl ihr ⊢ <;> omega

/-- In a decreasing tree, `RC(T)` consists of labels and has `n_ru + n_bin` elements. -/
private lemma card_rightChildLabels {α : Type*} [Preorder α] [DecidableEq α] {T : BinaryTree α}
    (hT : T.IsDecreasing) :
    T.rightChildLabels ⊆ T.labels ∧
      T.rightChildLabels.card = T.numNodesOfType .rightUnary + T.numNodesOfType .binary := by
  induction T with
  | nil => simp
  | node m l r ihl ihr =>
    obtain ⟨hl, hr, hdisj, hlt⟩ := hT
    obtain ⟨hl1, hl2⟩ := ihl hl
    obtain ⟨hr1, hr2⟩ := ihr hr
    have hm : m ∉ l.rightChildLabels ∪ r.rightChildLabels := fun h =>
      lt_irrefl m (hlt m (Finset.union_subset_union hl1 hr1 h))
    have hd : Disjoint l.rightChildLabels r.rightChildLabels :=
      Finset.disjoint_of_subset_left hl1 (Finset.disjoint_of_subset_right hr1 hdisj)
    refine ⟨?_, ?_⟩
    · intro x hx
      simp only [rightChildLabels, Finset.mem_union, labels] at hx ⊢
      rcases hx with (hx | hx) | hx
      · exact Or.inl (Or.inr (hl1 hx))
      · exact Or.inr (hr1 hx)
      · cases r <;> simp_all
    · have hc := Finset.card_union_of_disjoint hd
      cases l <;> cases r <;>
        simp_all [rightChildLabels, vertexType] <;> omega

/-- `n_bin(T)` counted by vertex type agrees with `BinaryTree.numBinaryNodes`. -/
private lemma numNodesOfType_binary_eq_numBinaryNodes {α : Type*} (T : BinaryTree α) :
    T.numNodesOfType .binary = T.numBinaryNodes := by
  induction T with
  | nil => rfl
  | node a l r ihl ihr => cases l <;> cases r <;> simp_all [vertexType]

/-- A finite sum over the pairs `(a, b)` with `a ∈ S`, `b ∈ t a` is an iterated sum. -/
private lemma finsum_mem_sigma_eq {α β M : Type*} [AddCommMonoid M] {S : Set α} (hS : S.Finite)
    (t : α → Finset β) (f : α × β → M) :
    ∑ᶠ p ∈ {p : α × β | p.1 ∈ S ∧ p.2 ∈ t p.1}, f p = ∑ᶠ a ∈ S, ∑ b ∈ t a, f (a, b) := by
  classical
  lift S to Finset α using hS
  have hmem : ∀ p : α × β, p ∈ (S ×ˢ S.biUnion t).filter (fun p => p.2 ∈ t p.1) ↔
      p.1 ∈ S ∧ p.2 ∈ t p.1 := fun p => by
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_biUnion]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, p.1, h.1, h.2⟩, h.2⟩⟩
  rw [show {p : α × β | p.1 ∈ (S : Set α) ∧ p.2 ∈ t p.1} = ↑((S ×ˢ S.biUnion t).filter
      (fun p => p.2 ∈ t p.1)) by ext p; rw [Finset.mem_coe, hmem]; rfl, finsum_mem_coe_finset,
    finsum_mem_coe_finset, Finset.sum_finset_product _ S t hmem]

/-- **The vertex-type counts of a tree in the fiber.** For a decreasing tree `T` on `[n]` with
postorder `π ∈ S_n`, writing `M = M(T)` and `C = C(T)`: `n_leaf = |M| + 1`,
`n_lu = n - 1 - 2|M| - |C|`, `n_ru = |C|`, `n_bin = |M|` and `des(I(T)) = |M| + |C|`. -/
private lemma numNodesOfType_of_mem_fiber {n : ℕ} (hn : 1 ≤ n) {π : List ℕ}
    (hπ : π ∈ permWords n) {T : BinaryTree ℕ} (hT : T ∈ decreasingTrees (Finset.Icc 1 n))
    (hTp : T.postorder = π) :
    T.numNodesOfType .leaf = T.treeMatching.card + 1 ∧
      T.numNodesOfType .leftUnary = n - 1 - 2 * T.treeMatching.card - T.treeRightChoices.card ∧
      T.numNodesOfType .rightUnary = T.treeRightChoices.card ∧
      T.numNodesOfType .binary = T.treeMatching.card ∧
      T.inorder.numDescents = T.treeMatching.card + T.treeRightChoices.card := by
  have hbin := numBinaryNodes_eq_card_treeMatching hn hπ hT hTp
  have hright := card_rightChildLabels_eq_card_treeMatching_add_card_treeRightChoices hn hπ hT hTp
  have hrc := (card_rightChildLabels hT.1).2
  have htot := sum_numNodesOfType T
  rw [hTp, hπ.2.1] at htot
  have hne : T ≠ nil := by
    rintro rfl
    have h1 : 1 ∈ Finset.Icc 1 n := Finset.mem_Icc.mpr ⟨le_rfl, hn⟩
    simp [← hT.2] at h1
  have hleaf := numNodesOfType_leaf_eq_numNodesOfType_binary_add_one T hne
  have hbin' := numNodesOfType_binary_eq_numBinaryNodes T
  rw [numDescents_inorder_of_isDecreasing hT.1]
  omega

end BinaryTree

namespace List

/-- For finite sets of colors `X_L, X_a, X_b` and a permutation `π ∈ S_n` with `n ≥ 1`, the
fiber descent polynomial of `𝐔_{X_L,X_a,X_b}` at `π` is
`L ∑_{M ∈ 𝒜(π)} (L x)^{|M|} (a + b x)^{n - 1 - 2|M|}`, where `L = |X_L|`, `a = |X_a|`,
`b = |X_b|`. -/
@[lognarayana "lem_local_colors_matching_sum"]
public theorem familyFiberDescentPolynomial_localColorFamily (R : Type*) [CommSemiring R]
    {C : Type*} [BinaryTree.TreeColors C] (X_L X_a X_b : Finset C) {n : ℕ} (hn : 1 ≤ n) {π : List ℕ}
    (hπ : π ∈ permWords n) :
    π.familyFiberDescentPolynomial R
        (BinaryTree.localColorFamily (X_L : Set C) (X_a : Set C) (X_b : Set C)) =
      (X_L.card : R[X]) * ∑ᶠ M ∈ π.fiberMatchings,
        ((X_L.card : R[X]) * X) ^ M.card *
          ((X_a.card : R[X]) + (X_b.card : R[X]) * X) ^ (n - 1 - 2 * M.card) := by
  classical
  set P : Set (VertexType × C) := ({VertexType.leaf} ×ˢ (X_L : Set C)) ∪
    ({VertexType.leftUnary} ×ˢ (X_a : Set C)) ∪ ({VertexType.rightUnary} ×ˢ (X_b : Set C)) ∪
    {(VertexType.binary, TreeColors.black)}
  let g : VertexType → R[X]
    | .leaf => (X_L.card : R[X])
    | .leftUnary => (X_a.card : R[X])
    | .rightUnary => (X_b.card : R[X])
    | .binary => 1
  have hfib : ∀ τ : VertexType, ∃ s : Finset C, {c : C | (τ, c) ∈ P} = ↑s ∧
      (s.card : R[X]) = g τ := by
    intro τ
    cases τ
    · exact ⟨X_L, by ext c; simp [P], rfl⟩
    · exact ⟨X_a, by ext c; simp [P], rfl⟩
    · exact ⟨X_b, by ext c; simp [P], rfl⟩
    · exact ⟨{TreeColors.black}, by ext c; simp [P], by simp [g]⟩
  have hP : ∀ τ : VertexType, {c : C | (τ, c) ∈ P}.Finite := fun τ => by
    obtain ⟨s, hs, -⟩ := hfib τ
    rw [hs]
    exact s.finite_toSet
  have hsum : ∀ τ : VertexType, ∑ᶠ (c : C) (_ : (τ, c) ∈ P), (1 : R[X]) = g τ := fun τ => by
    obtain ⟨s, hs, hg⟩ := hfib τ
    rw [← hg, show (∑ᶠ (c : C) (_ : (τ, c) ∈ P), (1 : R[X])) = ∑ᶠ c ∈ (↑s : Set C), 1 by
      rw [← hs]; rfl, finsum_mem_coe_finset]
    simp
  have key := finsum_familyDecreasingLabelings_localRuleFamily P hP hπ (fun _ => (1 : R[X]))
    (fun T => X ^ T.inorder.numDescents)
  simp only [hsum, one_mul, rec_mul_eq_one, mul_one, rec_vertexType_eq] at key
  have hF : ∀ T ∈ {T | T ∈ decreasingTrees (Finset.Icc 1 n) ∧ T.postorder = π},
      X ^ T.inorder.numDescents *
        (g .leaf ^ T.numNodesOfType .leaf * g .leftUnary ^ T.numNodesOfType .leftUnary *
          g .rightUnary ^ T.numNodesOfType .rightUnary * g .binary ^ T.numNodesOfType .binary) =
      X ^ (T.treeMatching.card + T.treeRightChoices.card) * ((X_L.card : R[X]) ^
        (T.treeMatching.card + 1) *
        (X_a.card : R[X]) ^ (n - 1 - 2 * T.treeMatching.card - T.treeRightChoices.card) *
        (X_b.card : R[X]) ^ T.treeRightChoices.card) := by
    rintro T ⟨hT, hTp⟩
    obtain ⟨h1, h2, h3, -, h5⟩ := numNodesOfType_of_mem_fiber hn hπ hT hTp
    simp only [g, h1, h2, h3, h5, one_pow, mul_one]
  rw [List.familyFiberDescentPolynomial]
  change _ = ∑ᶠ (T : BinaryTree ℕ) (_ : T ∈ {T | T ∈ decreasingTrees (Finset.Icc 1 n) ∧
    T.postorder = π}), _ at key
  rw [show BinaryTree.localColorFamily (X_L : Set C) (X_a : Set C) (X_b : Set C) =
      localRuleFamily P from rfl, key,
    finsum_mem_eq_of_bijOn _ (BinaryTree.bijOn_treeMatching_treeRightChoices hn hπ)
      (g := fun p : Finset (ℕ × ℕ) × Finset ℕ =>
        X ^ (p.1.card + p.2.card) * ((X_L.card : R[X]) ^ (p.1.card + 1) *
          (X_a.card : R[X]) ^ (n - 1 - 2 * p.1.card - p.2.card) *
          (X_b.card : R[X]) ^ p.2.card)) hF,
    show {p : Finset (ℕ × ℕ) × Finset ℕ |
        p.1 ∈ π.fiberMatchings ∧ p.2 ⊆ Finset.unmatchedVertices (n - 1) p.1} =
      {p | p.1 ∈ π.fiberMatchings ∧ p.2 ∈ (Finset.unmatchedVertices (n - 1) p.1).powerset} by
      simp,
    finsum_mem_sigma_eq (List.fiberMatchings_finite π)
      fun M => (Finset.unmatchedVertices (n - 1) M).powerset,
    ← smul_eq_mul, smul_finsum_mem (List.fiberMatchings_finite π)]
  refine finsum_mem_congr rfl fun M hM => ?_
  have hU := hM.1.card_unmatchedVertices_add_two_mul_card
  rw [hπ.2.1] at hU
  dsimp only
  rw [smul_eq_mul, show n - 1 - 2 * M.card = (Finset.unmatchedVertices (n - 1) M).card by omega,
    add_comm (X_a.card : R[X]), ← Finset.sum_pow_mul_eq_add_pow, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  ring

end List

end MatchingSum

namespace List

/-! ### Homogenization in `γ`-form and in peak form -/

section Homogenize

open Polynomial

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
    finsum_mem_eq_finite_toFinset_sum _ (List.fiberMatchings_finite π), finsetSum_coeff]
  simp only [coeff_X_pow]
  rw [Finset.sum_boole]
  congr 2
  ext M
  simp [eq_comm]

/-- Grouping a sum over the matchings of `π` by their number of arcs: the matchings with `j`
arcs are counted by `[z^j] Γ_π`, and `j ≤ (π.length - 1) / 2`. -/
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

/-- Let `X_L, X_a, X_b` be finite sets of colors with `|X_L| = L`, `|X_a| = a`, `|X_b| = b`, let
`n ≥ 1` and `π ∈ S_n`. Then the degree `n - 1` homogenization of `D_{π,𝐔_{X_L,X_a,X_b}}` is
`L ∑_{j=0}^{⌊(n-1)/2⌋} ([z^j] Γ_π(z)) (Lxy)^j (ay + bx)^{n-1-2j}`, with `x = X 0`, `y = X 1`. -/
@[lognarayana "lem_local_colors_homog_gamma"]
public theorem homogenize_familyFiberDescentPolynomial_localColorFamily (R : Type*)
    [CommSemiring R] {C : Type*} [BinaryTree.TreeColors C] {X_L X_a X_b : Finset C} {L a b : ℕ}
    (hL : X_L.card = L) (ha : X_a.card = a) (hb : X_b.card = b) {n : ℕ} (hn : 1 ≤ n)
    {π : List ℕ} (hπ : π ∈ permWords n) :
    (familyFiberDescentPolynomial R
        (BinaryTree.localColorFamily (X_L : Set C) X_a X_b) π).homogenize (n - 1) =
      (L : MvPolynomial (Fin 2) R) * ∑ j ∈ Finset.range ((n - 1) / 2 + 1),
        MvPolynomial.C ((fiberMatchingPolynomial R π).coeff j) *
          ((L : MvPolynomial (Fin 2) R) * MvPolynomial.X 0 * MvPolynomial.X 1) ^ j *
          ((a : MvPolynomial (Fin 2) R) * MvPolynomial.X 1 +
            (b : MvPolynomial (Fin 2) R) * MvPolynomial.X 0) ^ (n - 1 - 2 * j) := by
  apply homogenize_eq_of_isHomogeneous
  · have hC (k : ℕ) : (k : MvPolynomial (Fin 2) R).IsHomogeneous 0 := by
      rw [← map_natCast MvPolynomial.C]
      exact MvPolynomial.isHomogeneous_C _ _
    have hX := MvPolynomial.isHomogeneous_X R (σ := Fin 2)
    convert (hC L).mul (MvPolynomial.IsHomogeneous.sum _ _ (n - 1) fun j hj => ?_) using 1
    · simp
    convert ((MvPolynomial.isHomogeneous_C _ _).mul ((((hC L).mul (hX 0)).mul (hX 1)).pow j)).mul
      ((((hC a).mul (hX 1)).add ((hC b).mul (hX 0))).pow (n - 1 - 2 * j)) using 1
    have := Finset.mem_range_succ_iff.mp hj
    omega
  · rw [List.familyFiberDescentPolynomial_localColorFamily R X_L X_a X_b hn hπ, hL, ha, hb,
      finsum_fiberMatchings_eq_sum_coeff R π fun k : ℕ =>
        ((L : R[X]) * X) ^ k * ((a : R[X]) + (b : R[X]) * X) ^ (n - 1 - 2 * k), hπ.2.1]
    simp [Algebra.smul_def, mul_assoc]

end Homogenize

section HomogenizePeak

open MvPolynomial

/-- The substitution `x ↦ (b/a) x` term by term: for `2j ≤ d`,
`L a^d ((λ (b/a) x y)^j ((b/a) x + y)^{d-2j}) = L (Lxy)^j (ay + bx)^{d-2j}` at `λ = L/(ab)`. -/
private lemma C_mul_aeval_rescale_term {R : Type*} [Semifield R] {L a b : R} (ha : a ≠ 0)
    (hb : b ≠ 0) {d j : ℕ} (hj : 2 * j ≤ d) :
    C (L * a ^ d) * aeval ![(C (b / a) * X 0 : MvPolynomial (Fin 2) R), X 1]
        ((C (L / (a * b)) * X 0 * X 1) ^ j * (X 0 + X 1) ^ (d - 2 * j)) =
      C L * ((C L * X 0 * X 1) ^ j * (C a * X 1 + C b * X 0) ^ (d - 2 * j)) := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hj
  have h1 : (C a ^ 2 * (C (L / (a * b)) * (C (b / a) * X 0) * X 1) : MvPolynomial (Fin 2) R) =
      C L * X 0 * X 1 := by
    simp only [← map_pow, ← mul_assoc, ← map_mul]
    congr 3
    field_simp
  have h2 : (C a * (C (b / a) * X 0 + X 1) : MvPolynomial (Fin 2) R) = C a * X 1 + C b * X 0 := by
    rw [mul_add, ← mul_assoc, ← map_mul, mul_div_cancel₀ _ ha, add_comm]
  rw [← h1, ← h2, Nat.add_sub_cancel_left]
  simp only [map_mul, map_pow, map_add, aeval_X, aeval_C, algebraMap_eq, Matrix.cons_val_zero,
    Matrix.cons_val_one, mul_pow]
  ring

/-- Let `X_L, X_a, X_b` be finite sets of colors with `|X_L| = L`, `|X_a| = a ≥ 1` and
`|X_b| = b ≥ 1`, let `n ≥ 1` and `π ∈ S_n`. Then the degree `n - 1` homogenization of
`D_{π,𝐔_{X_L,X_a,X_b}}` is `L a^{n-1} H^{L/(ab)}_π((b/a) x, y)`, with `x = X 0`, `y = X 1`. -/
@[lognarayana "lem_local_colors_homog_peak"]
public theorem homogenize_familyFiberDescentPolynomial_localColorFamily_eq_fiberPeakPolynomial
    (R : Type*) [Semifield R] [CharZero R] {C : Type*} [BinaryTree.TreeColors C]
    {X_L X_a X_b : Finset C}
    {L a b : ℕ} (hL : X_L.card = L) (ha : X_a.card = a) (hb : X_b.card = b) (ha1 : 1 ≤ a)
    (hb1 : 1 ≤ b) {n : ℕ} (hn : 1 ≤ n) {π : List ℕ} (hπ : π ∈ permWords n) :
    (familyFiberDescentPolynomial R
        (BinaryTree.localColorFamily (X_L : Set C) X_a X_b) π).homogenize (n - 1) =
      MvPolynomial.C ((L : R) * (a : R) ^ (n - 1)) *
        MvPolynomial.aeval ![MvPolynomial.C ((b : R) / a) * MvPolynomial.X 0, MvPolynomial.X 1]
          (fiberPeakPolynomial R ((L : R) / ((a : R) * b)) π) := by
  rw [List.homogenize_familyFiberDescentPolynomial_localColorFamily R hL ha hb hn hπ,
    List.fiberPeakPolynomial_eq_finsum_fiberMatchings R hn hπ,
    finsum_fiberMatchings_eq_sum_coeff R π fun k : ℕ =>
      (MvPolynomial.C ((L : R) / ((a : R) * b)) * X 0 * X 1) ^ k * (X 0 + X 1) ^ (n - 1 - 2 * k),
    hπ.2.1, map_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [map_smul, smul_eq_C_mul, mul_left_comm (MvPolynomial.C (_ * _)), C_mul_aeval_rescale_term
    (Nat.cast_ne_zero.mpr (by omega)) (Nat.cast_ne_zero.mpr (by omega)) (by grind)]
  simp only [map_natCast]
  ring

end HomogenizePeak

/-! ### Ultra-log-concavity and log-concavity -/

section ULC

open MvPolynomial

private lemma length_inorder_eq_length_postorder {α : Type*} (T : BinaryTree α) :
    T.inorder.length = T.postorder.length := by
  induction T with
  | nil => rfl
  | node a l r ihl ihr => simp [BinaryTree.inorder, BinaryTree.postorder, ihl, ihr]

private lemma numDescents_le_length_sub_one {α : Type*} [LinearOrder α] (σ : List α) :
    σ.numDescents ≤ σ.length - 1 :=
  (Finset.card_filter_le _ _).trans (by simp)

/-- The fiber descent polynomial of any family at `π` has nonnegative coefficients and degree at
most `π.length - 1`. -/
private lemma coeff_nonneg_and_natDegree_le {C : Type*} (U : Set (BinaryTree C)) (π : List ℕ) :
    (∀ i, 0 ≤ (List.familyFiberDescentPolynomial ℝ U π).coeff i) ∧
      (List.familyFiberDescentPolynomial ℝ U π).natDegree ≤ π.length - 1 := by
  let P : Polynomial ℝ → Prop := fun p => (∀ i, 0 ≤ p.coeff i) ∧ p.natDegree ≤ π.length - 1
  have h0 : P 0 := by simp [P]
  have hadd : ∀ p q, P p → P q → P (p + q) := fun p q hp hq =>
    ⟨fun i => by simpa using add_nonneg (hp.1 i) (hq.1 i),
      Polynomial.natDegree_add_le_of_degree_le hp.2 hq.2⟩
  refine finsum_induction P h0 hadd fun 𝒯 => finsum_induction P h0 hadd fun h =>
    ⟨fun i => by rw [Polynomial.coeff_X_pow]; split_ifs <;> norm_num, ?_⟩
  refine Polynomial.natDegree_X_pow_le _ |>.trans ?_
  rw [← h.2, ← length_inorder_eq_length_postorder]
  exact numDescents_le_length_sub_one _

/-- Rescaling the first variable by a nonnegative constant preserves Lorentzian bivariate
polynomials: an instance of the cited nonnegative linear substitution theorem, with the diagonal
matrix `diag(c, 1)`. -/
private lemma isLorentzian_aeval_C_mul_X_zero
    (hsub : MvPolynomial.LorentzianNonnegLinearSubstitution (Fin 2) (Fin 2)) {c : ℝ} (hc : 0 ≤ c)
    {f : MvPolynomial (Fin 2) ℝ} (hf : f.IsLorentzian) :
    (aeval ![C c * X 0, (X 1 : MvPolynomial (Fin 2) ℝ)] f).IsLorentzian := by
  have hX : ![C c * X 0, (X 1 : MvPolynomial (Fin 2) ℝ)] = fun i : Fin 2 =>
      ∑ j, (if i = j then ![c, 1] i else 0) • (X j : MvPolynomial (Fin 2) ℝ) := by
    funext i
    fin_cases i <;> simp [smul_eq_C_mul]
  rw [hX]
  exact hsub _ (fun i j => by split_ifs <;> fin_cases i <;> simp [hc]) f hf

/-- Let `L, a, b` be positive integers with `L ≤ 2ab`, and let `X_L, X_a, X_b` be finite sets of
colors with `|X_L| = L`, `|X_a| = a`, `|X_b| = b`. For `n ≥ 1` and `π ∈ S_n`, the polynomial
`D_{π,𝐔_{X_L,X_a,X_b}}(x)` is ultra-log-concave of order `n - 1`. -/
@[lognarayana "thm_local_colors_ulc"]
public theorem isUltraLogConcave_familyFiberDescentPolynomial_localColorFamily {C : Type*}
    [BinaryTree.TreeColors C] {X_L X_a X_b : Finset C} {L a b : ℕ} (hL0 : 0 < L) (ha0 : 0 < a)
    (hb0 : 0 < b) (hLab : L ≤ 2 * a * b) (hL : X_L.card = L) (ha : X_a.card = a)
    (hb : X_b.card = b) {n : ℕ} (hn : 1 ≤ n) {π : List ℕ} (hπ : π ∈ permWords n)
    (hsub : ∀ (σ τ : Type) [Fintype σ] [Fintype τ],
      MvPolynomial.LorentzianNonnegLinearSubstitution σ τ)
    (hder : ∀ (σ : Type) [Fintype σ], MvPolynomial.LorentzianNonnegDerivative σ)
    (hmul : ∀ (σ : Type) [Fintype σ], MvPolynomial.LorentzianMul σ)
    (hBH : ∀ (σ : Type) [Fintype σ], MvPolynomial.NormalizedSupportPolyLorentzianOfMConvex σ)
    (hsym : ∀ (σ τ : Type) [Fintype σ] [Fintype τ], MvPolynomial.BrandenHuhSymbolTheorem σ τ) :
    (familyFiberDescentPolynomial ℝ
      (BinaryTree.localColorFamily (X_L : Set C) X_a X_b) π).IsUltraLogConcave (n - 1) := by
  obtain ⟨hnonneg, hdeg⟩ :=
    coeff_nonneg_and_natDegree_le (BinaryTree.localColorFamily (X_L : Set C) X_a X_b) π
  rw [hπ.2.1] at hdeg
  refine (Polynomial.isLorentzian_homogenize_iff_isUltraLogConcave hnonneg hdeg).mp ?_
  rw [List.homogenize_familyFiberDescentPolynomial_localColorFamily_eq_fiberPeakPolynomial ℝ hL ha
    hb ha0 hb0 hn hπ, C_mul']
  refine IsLorentzian.smul (isLorentzian_aeval_C_mul_X_zero (hsub _ _) (by positivity)
    (List.isLorentzian_fiberPeakPolynomial hn hπ ⟨by positivity, ?_⟩ hsub hder hmul hBH hsym))
    (by positivity)
  rw [div_le_iff₀ (by positivity)]
  exact_mod_cast (by nlinarith : L ≤ 2 * (a * b))

end ULC

/-- Let `L, a, b` be positive integers with `L ≤ 2ab`, and let `X_L, X_a, X_b` be finite sets of
colors with `|X_L| = L`, `|X_a| = a`, `|X_b| = b`. For `n ≥ 1` and `π ∈ S_n`, the polynomial
`D_{π,𝐔_{X_L,X_a,X_b}}(x)` is log-concave. -/
@[lognarayana "thm_local_colors_lc"]
public theorem isLogConcave_familyFiberDescentPolynomial_localColorFamily {C : Type*}
    [BinaryTree.TreeColors C] {X_L X_a X_b : Finset C} {L a b : ℕ} (hL0 : 0 < L) (ha0 : 0 < a)
    (hb0 : 0 < b) (hLab : L ≤ 2 * a * b) (hL : X_L.card = L) (ha : X_a.card = a)
    (hb : X_b.card = b) {n : ℕ} (hn : 1 ≤ n) {π : List ℕ} (hπ : π ∈ permWords n)
    (hsub : ∀ (σ τ : Type) [Fintype σ] [Fintype τ],
      MvPolynomial.LorentzianNonnegLinearSubstitution σ τ)
    (hder : ∀ (σ : Type) [Fintype σ], MvPolynomial.LorentzianNonnegDerivative σ)
    (hmul : ∀ (σ : Type) [Fintype σ], MvPolynomial.LorentzianMul σ)
    (hBH : ∀ (σ : Type) [Fintype σ], MvPolynomial.NormalizedSupportPolyLorentzianOfMConvex σ)
    (hsym : ∀ (σ τ : Type) [Fintype σ] [Fintype τ], MvPolynomial.BrandenHuhSymbolTheorem σ τ) :
    (familyFiberDescentPolynomial ℝ
      (BinaryTree.localColorFamily (X_L : Set C) X_a X_b) π).IsLogConcave :=
  (List.isUltraLogConcave_familyFiberDescentPolynomial_localColorFamily hL0 ha0 hb0 hLab hL ha
    hb hn hπ hsub hder hmul hBH hsym).isLogConcave

end List
