/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib
public import LogNarayana.Attr
public import LogNarayana.StackSorting.FiberMatroid.Defs
public import LogNarayana.StackSorting.Descents.Defs
public import LogNarayana.Lorentzian.Hessian.Defs
public import LogNarayana.Matroid.Laminar.Defs
public import LogNarayana.Polynomial.LogConcave.Defs
public import LogNarayana.StackSorting.Matchings.Defs
public import LogNarayana.Matroid.BasisGeneratingPolynomial.Defs
public import LogNarayana.StackSorting.AdoptableForest.Defs
public import LogNarayana.StackSorting.FiberPolynomials.Defs
public import LogNarayana.Forest.LaminarMatroid.Defs
public import LogNarayana.StackSorting.StackSort.Defs
public import LogNarayana.BinaryTree.Decreasing.Basic
public import LogNarayana.StackSorting.Descents.Basic
public import LogNarayana.Lorentzian.Hessian.Basic
public import LogNarayana.Lorentzian.Symbol.Basic
public import LogNarayana.Polynomial.LogConcave.Basic
public import LogNarayana.StackSorting.Matchings.Basic
public import LogNarayana.Matroid.BasisGeneratingPolynomial.Basic
public import LogNarayana.Lorentzian.BrandenHuh.Basic
public import LogNarayana.StackSorting.AdoptableForest.Basic
public import LogNarayana.Lorentzian.Bivariate
public import LogNarayana.StackSorting.FiberPolynomials.Basic
public import LogNarayana.Forest.LaminarMatroid.Basic
public import LogNarayana.StackSorting.StackSort.Basic

/-!
# Proofs of Theorems 1.1 and 1.2, and Corollary 3.6

Fix `n ≥ 1` and `π ∈ S_n`. An element of the stack-sorting fiber `s⁻¹(π)` is determined by its
descent tops and its ascent tops. The fiber top polynomial
`𝒟_π(x, y) = ∑_{σ ∈ s⁻¹(π)} ∏_{a ∈ DT(σ)} x_a ∏_{b ∈ AT(σ)} y_b` is the position relabelling
`ρ_π` of the forest matching polynomial of the adoptable forest `𝓕_π` with marked set `Des(π)`;
transporting the forest matroid along `ρ_π` exhibits `𝒟_π` as the basis generating polynomial of
a laminar matroid on `{x, y} × [n]` whose bases have `n - 1` elements (Theorem 1.2). Hence `𝒟_π`
is Lorentzian, and so is its specialisation `x_a ↦ x`, `y_a ↦ y`, the homogeneous fiber
polynomial `H_π`; consequently the fiber descent polynomial `D_π` is ultra-log-concave of order
`n - 1`, and in particular log-concave (Theorem 1.1).

Differentiating `𝒟_π` in the variables of `A_d` and `A_a` and setting those of `B_d` and `B_a` to
zero gives a Lorentzian polynomial, the conditioned top polynomial; a weighted two-variable
substitution turns it into the homogenization of the conditional top polynomial, which is
therefore ultra-log-concave of order `n - 1 - |A_d| - |A_a|` (Corollary 3.6).

## Main results

* `List.eq_of_mem_stackFiber_of_descentTops_eq_of_ascentTops_eq`: `σ ↦ (DT(σ), AT(σ))` is
  injective on `s⁻¹(π)`.
* `List.fiberTopPolynomial_eq_positionRelabel_forestMatchingPoly`:
  `𝒟_π = ρ_π (Z_{𝓕_π, Des(π)})`.
* `List.exists_isLaminar_basisGeneratingPolynomial_eq_fiberTopPolynomial`: Theorem 1.2, the
  laminar matroid.
* `List.isLorentzian_fiberTopPolynomial`: Theorem 1.2, `𝒟_π` is Lorentzian.
* `List.isLorentzian_fiberHomogPolynomial`: Theorem 1.1, `H_π` is Lorentzian.
* `List.isUltraLogConcave_fiberDescentPolynomial`: `D_π` is ultra-log-concave of order `n - 1`.
* `List.isLogConcave_fiberDescentPolynomial`: `D_π` is log-concave.
* `List.isLorentzian_conditionalTopPolynomial`: the conditioned top polynomial is Lorentzian.
* `List.isUltraLogConcave_conditionalTopPolynomial`: Corollary 3.6.

## Implementation notes

The fiber top polynomial lives in `ℝ[z_e : e ∈ Bool × ℕ]`, with `x_a = X (true, a)` and
`y_a = X (false, a)`, while `MvPolynomial.IsLorentzian` needs a finite variable type; the
Lorentzian statements therefore exhibit their polynomial as the image, under renaming along the
inclusion `{x, y} × [n] ↪ Bool × ℕ`, of a Lorentzian polynomial in the variables `{x, y} × [n]`.

The Brändén–Huh results used — normalized support polynomials of M-convex sets are Lorentzian
[BH, Theorem 3.10], nonnegative combinations of partial derivatives preserve the Lorentzian
property [BH, Corollary 2.11], and so do nonnegative linear substitutions [BH, Theorem 2.10] —
are cited, not proved, and enter as hypotheses.

## References

* [LogNarayana] *Log-Concavity in Narayana Transforms and Stack-Sorting Fibers*, Theorems 1.1
  and 1.2, Corollary 3.6, Sections 2, 5 and 8.
* [BH] P. Brändén, J. Huh, *Lorentzian polynomials*, Ann. of Math. 192 (2020).
-/

/-! ### A fiber element is determined by its tops -/

section

open BinaryTree

/-- The right endpoints of a noncrossing partial matching on `[N]` lie in `[N]`. -/
private lemma image_snd_subset_Icc {N : ℕ} {M : Finset (ℕ × ℕ)}
    (hM : IsNoncrossingPartialMatching N M) : M.image Prod.snd ⊆ Finset.Icc 1 N := by
  intro v hv
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hv
  have := hM.one_le_fst p hp
  have := hM.fst_lt_snd p hp
  have := hM.snd_le p hp
  simp only [Finset.mem_Icc]; omega

/-- For a tree with postorder `π` of length `n`, `C(T) ⊆ U(M(T))` with `U` taken in `[n - 1]`. -/
private lemma treeRightChoices_subset {n : ℕ} {π : List ℕ} (hlen : π.length = n)
    {T : BinaryTree ℕ} (hTπ : T.postorder = π) :
    T.treeRightChoices ⊆ Finset.unmatchedVertices (n - 1) T.treeMatching := by
  rw [← hlen, ← hTπ]
  exact Finset.filter_subset _ _

/-- The `x`-copies of the choice set of a tree in the fiber are read off its right-child labels:
for `v : ℕ`, `v ∈ R(M(T)) ∪ C(T)` iff `v ∈ [n - 1]` and `π_{v+1} ∈ RC(T)`. -/
private lemma mem_plus_iff {n : ℕ} (hn : 1 ≤ n) {π : List ℕ} (hπ : π ∈ permWords n)
    {T : BinaryTree ℕ} (hT : T ∈ decreasingTrees (Finset.Icc 1 n)) (hTπ : T.postorder = π)
    (v : ℕ) :
    v ∈ T.treeMatching.image Prod.snd ∪ T.treeRightChoices ↔
      v ∈ Finset.Icc 1 (n - 1) ∧ ∃ h : v < π.length, π[v] ∈ T.rightChildLabels := by
  by_cases hv : v ∈ Finset.Icc 1 (n - 1)
  · rw [mem_rightChildLabels_iff_mem_treeMatching_or_treeRightChoices hπ hT hTπ hv]
    simp [hv]
  · have hM := (treeMatching_mem_fiberMatchings hn hπ hT hTπ).1
    rw [hπ.2.1] at hM
    simp only [hv, false_and, iff_false]
    exact fun h => hv <| Finset.union_subset (image_snd_subset_Icc hM)
      ((treeRightChoices_subset hπ.2.1 hTπ).trans Finset.sdiff_subset) h

/-- The `y`-copies of the choice set of a tree in the fiber are read off its left-child labels:
for `v : ℕ`, `v ∈ R(M(T)) ∪ (U(M(T)) \ C(T))` iff `v ∈ [n - 1]` and `π_{v+1} ∈ LC(T)`. -/
private lemma mem_minus_iff {n : ℕ} (hn : 1 ≤ n) {π : List ℕ} (hπ : π ∈ permWords n)
    {T : BinaryTree ℕ} (hT : T ∈ decreasingTrees (Finset.Icc 1 n)) (hTπ : T.postorder = π)
    (v : ℕ) :
    v ∈ T.treeMatching.image Prod.snd ∪
        (Finset.unmatchedVertices (n - 1) T.treeMatching \ T.treeRightChoices) ↔
      v ∈ Finset.Icc 1 (n - 1) ∧ ∃ h : v < π.length, π[v] ∈ T.leftChildLabels := by
  by_cases hv : v ∈ Finset.Icc 1 (n - 1)
  · rw [← mem_leftChildLabels_iff_mem_treeMatching_or_unmatchedVertices_sdiff hn hπ hT hTπ hv]
    simp [hv]
  · have hM := (treeMatching_mem_fiberMatchings hn hπ hT hTπ).1
    rw [hπ.2.1] at hM
    simp only [hv, false_and, iff_false]
    exact fun h => hv <| Finset.union_subset (image_snd_subset_Icc hM)
      (Finset.sdiff_subset.trans Finset.sdiff_subset) h

/-- Membership in the choice set `I(M, ∅, C)`: `v⁺ ∈ I` iff `v ∈ R(M) ∪ C`, and `v⁻ ∈ I` iff
`v ∈ R(M) ∪ (U(M) \ C)`. -/
private lemma mem_openChoiceSet_empty_iff (N : ℕ) (M : Finset (ℕ × ℕ)) (C : Finset ℕ)
    (b : Bool) (v : ℕ) :
    (b, v) ∈ Finset.openChoiceSet N M ∅ C ↔
      if b then v ∈ M.image Prod.snd ∪ C
      else v ∈ M.image Prod.snd ∪ (Finset.unmatchedVertices N M \ C) := by
  cases b <;> simp [Finset.openChoiceSet]

/-- Two trees in the fiber of `π` whose right-child labels agree and whose left-child labels agree
have the same choice set `I(M(T), ∅, C(T))`. -/
private lemma openChoiceSet_eq {n : ℕ} (hn : 1 ≤ n) {π : List ℕ} (hπ : π ∈ permWords n)
    {T T' : BinaryTree ℕ} (hT : T ∈ decreasingTrees (Finset.Icc 1 n)) (hTπ : T.postorder = π)
    (hT' : T' ∈ decreasingTrees (Finset.Icc 1 n)) (hT'π : T'.postorder = π)
    (hRC : T.rightChildLabels = T'.rightChildLabels)
    (hLC : T.leftChildLabels = T'.leftChildLabels) :
    Finset.openChoiceSet (n - 1) T.treeMatching ∅ T.treeRightChoices =
      Finset.openChoiceSet (n - 1) T'.treeMatching ∅ T'.treeRightChoices := by
  ext ⟨b, v⟩
  rw [mem_openChoiceSet_empty_iff, mem_openChoiceSet_empty_iff]
  cases b
  · simp only [Bool.false_eq_true, if_false]
    rw [mem_minus_iff hn hπ hT hTπ, mem_minus_iff hn hπ hT' hT'π, hLC]
  · simp only [if_true]
    rw [mem_plus_iff hn hπ hT hTπ, mem_plus_iff hn hπ hT' hT'π, hRC]

/-- The stack reconstruction recovers `(M(T), ∅, C(T))` from the choice set of a tree in the
fiber of `π`. -/
private lemma stackReconstruction_tree {n : ℕ} (hn : 1 ≤ n) {π : List ℕ} (hπ : π ∈ permWords n)
    {T : BinaryTree ℕ} (hT : T ∈ decreasingTrees (Finset.Icc 1 n)) (hTπ : T.postorder = π) :
    stackReconstruction (n - 1) (Finset.openChoiceSet (n - 1) T.treeMatching ∅
      T.treeRightChoices) = (T.treeMatching, ∅, T.treeRightChoices) := by
  have hM := (treeMatching_mem_fiberMatchings hn hπ hT hTπ).1
  rw [hπ.2.1] at hM
  exact stackReconstruction_openChoiceSet hM (Finset.empty_subset _) (by simp)
    (by simpa using treeRightChoices_subset hπ.2.1 hTπ)


namespace List

/-- Let `n ≥ 1` and `π ∈ S_n`. If `σ, σ' ∈ s⁻¹(π)` have `DT(σ) = DT(σ')` and
`AT(σ) = AT(σ')`, then `σ = σ'`. -/
@[lognarayana "lem_fiber_determined_by_tops"]
public theorem eq_of_mem_stackFiber_of_descentTops_eq_of_ascentTops_eq {n : ℕ} (hn : 1 ≤ n)
    {π : List ℕ} (hπ : π ∈ permWords n) {σ σ' : List ℕ} (hσ : σ ∈ stackFiber π)
    (hσ' : σ' ∈ stackFiber π) (hDT : σ.descentTops = σ'.descentTops)
    (hAT : σ.ascentTops = σ'.ascentTops) : σ = σ' := by
  have B := bijOn_inorder_postorder_eq_stackFiber hπ
  obtain ⟨T, hT, rfl⟩ := B.surjOn (Finset.mem_coe.2 hσ)
  obtain ⟨T', hT', rfl⟩ := B.surjOn (Finset.mem_coe.2 hσ')
  rw [descentTops_inorder_of_mem_decreasingTrees hT.1,
    descentTops_inorder_of_mem_decreasingTrees hT'.1] at hDT
  rw [ascentTops_inorder_of_mem_decreasingTrees hT.1,
    ascentTops_inorder_of_mem_decreasingTrees hT'.1] at hAT
  have h := (stackReconstruction_tree hn hπ hT.1 hT.2).symm.trans
    (openChoiceSet_eq hn hπ hT.1 hT.2 hT'.1 hT'.2 hDT hAT ▸
      stackReconstruction_tree hn hπ hT'.1 hT'.2)
  simp only [Prod.mk.injEq] at h
  rw [(bijOn_treeMatching_treeRightChoices hn hπ).injOn hT hT' (Prod.ext h.1 h.2.2)]

end List

end

/-! ### The fiber top polynomial as a relabelled forest matching polynomial -/

section

open MvPolynomial

/-- The admissible matchings for `(par, L)` on `[N]` are exactly the subsets of `[N] ×ˢ [N]`
indexing `forestMatchingPoly`: a noncrossing partial matching only has pairs `1 ≤ a < b ≤ N`. -/
private lemma setOf_isAdmissibleMatching_eq_coe_filter (N : ℕ) (par : ℕ → Option ℕ)
    (L : Finset ℕ) [DecidablePred (IsAdmissibleMatching N par L)] :
    {M | IsAdmissibleMatching N par L M} =
      ↑((Finset.Icc 1 N ×ˢ Finset.Icc 1 N).powerset.filter (IsAdmissibleMatching N par L)) := by
  ext M
  simp only [Set.mem_ofPred_eq, Finset.coe_filter, Finset.mem_powerset, iff_and_self]
  intro h p hp
  have hM := h.isNoncrossingPartialMatching
  have := hM.one_le_fst p hp
  have := hM.fst_lt_snd p hp
  have := hM.snd_le p hp
  simp only [Finset.mem_product, Finset.mem_Icc]
  omega


namespace List

/-- For `n ≥ 1` and `π ∈ S_n`, the fiber top polynomial is the position relabelling of the forest
matching polynomial of the adoptable forest with the descent set:
`𝒟_π(x, y) = ρ_π (Z_{𝓕_π, Des(π)})`. -/
@[lognarayana "lem_top_poly_forest"]
public theorem fiberTopPolynomial_eq_positionRelabel_forestMatchingPoly (R : Type*)
    [CommSemiring R] {n : ℕ} (hn : 1 ≤ n) {π : List ℕ} (hπ : π ∈ permWords n) :
    fiberTopPolynomial R π =
      positionRelabel R π (forestMatchingPoly R (n - 1) π.adoptableForest π.descentSet) := by
  classical
  rw [List.fiberTopPolynomial_eq_finsum_fiberMatchings R hn hπ,
    List.fiberMatchings_eq_setOf_isAdmissibleMatching hπ,
    setOf_isAdmissibleMatching_eq_coe_filter, finsum_mem_coe_finset, forestMatchingPoly, map_sum]
  refine Finset.sum_congr rfl fun M _ => ?_
  simp [map_prod, List.positionRelabelMap, List.getElem!_eq_getElem?_getD]

end List

end

/-! ### The laminar matroid of the fiber -/

section

open MvPolynomial Set

/-- The matroid `M` read on the subtype of a finite superset `G` of its ground set: the
restriction `M ↾ G`, which adds the elements of `G \ M.E` as loops, pulled back along the
inclusion. -/
private abbrev onFinset {β : Type*} (M : Matroid β) (G : Finset β) : Matroid G :=
  (M.restrict (G : Set β)).comap Subtype.val

private lemma onFinset_ground {β : Type*} (M : Matroid β) (G : Finset β) :
    (onFinset M G).E = univ := by
  ext x
  simp [onFinset]

private lemma onFinset_indep_iff {β : Type*} {M : Matroid β} {G : Finset β} {I : Set G} :
    (onFinset M G).Indep I ↔ M.Indep (Subtype.val '' I) := by
  simp only [onFinset, Matroid.comap_indep_iff, Matroid.restrict_indep_iff,
    Subtype.val_injective.injOn, and_true, and_iff_left_iff_imp]
  rintro - _ ⟨x, -, rfl⟩
  exact x.2

/-- Restricting to a superset of the ground set does not change the bases. -/
private lemma onFinset_isBase_iff {β : Type*} {M : Matroid β} {G : Finset β}
    (hX : M.E ⊆ G) {B : Set G} :
    (onFinset M G).IsBase B ↔ M.IsBase (Subtype.val '' B) := by
  have himg : Subtype.val '' (Subtype.val ⁻¹' (G : Set β) : Set G) = (G : Set β) := by
    ext x
    simp
  have hgr : ∀ X, (M.restrict (G : Set β)).IsBasis X G ↔ (M.restrict (G : Set β)).IsBase X :=
    fun X => Matroid.isBasis_ground_iff
  rw [onFinset, Matroid.comap_isBase_iff, Matroid.restrict_ground_eq, himg, hgr,
    Matroid.isBase_restrict_iff', Matroid.isBasis'_iff_isBasis_inter_ground,
    inter_eq_right.2 hX, Matroid.isBasis_ground_iff]
  simp only [Subtype.val_injective.injOn, true_and, and_iff_left_iff_imp]
  exact fun _ x _ => x.2

open Classical in
/-- The basis polynomial of `M` read on a finite superset `G` of its ground set, in the ambient
variables. -/
private lemma rename_basisGeneratingPolynomial_onFinset {β : Type*}
    (M : Matroid β) (G : Finset β) (hG : M.E ⊆ G) :
    rename Subtype.val ((onFinset M G).basisGeneratingPolynomial ℝ) =
      ∑ C ∈ G.powerset.filter (fun C : Finset β => M.IsBase (C : Set β)), ∏ e ∈ C, X e := by
  unfold Matroid.basisGeneratingPolynomial
  simp only [map_sum, map_prod, rename_X]
  refine Finset.sum_nbij' (fun B => B.map (Function.Embedding.subtype _))
    (fun C => C.subtype (· ∈ G)) ?_ ?_ ?_ ?_ ?_
  · intro B hB
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hB
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.coe_map,
      Function.Embedding.coe_subtype]
    refine ⟨fun x hx => ?_, (onFinset_isBase_iff hG).1 hB⟩
    obtain ⟨y, -, rfl⟩ := Finset.mem_map.1 hx
    exact y.2
  · intro C hC
    simp only [Finset.mem_filter, Finset.mem_powerset] at hC
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [onFinset_isBase_iff hG]
    convert hC.2
    ext x
    simp only [mem_image, Finset.mem_coe, Finset.mem_subtype]
    exact ⟨fun ⟨y, hy, hyx⟩ => hyx ▸ hy, fun hx => ⟨⟨x, hC.1 hx⟩, hx, rfl⟩⟩
  · intro B _
    ext x
    simp
  · intro C hC
    simp only [Finset.mem_filter, Finset.mem_powerset] at hC
    exact Finset.subtype_map_of_mem fun x hx => hC.1 hx
  · intro B _
    simp

open Classical in
/-- The bases of the image of a matroid on a finite ground set under a map injective on it,
listed inside a finite superset `G` of the image. -/
private lemma sum_isBase_map_prod_X {α β : Type*}
    (M : Matroid α) (E : Finset α) (hE : M.E = E) (f : α → β) (hf : InjOn f M.E)
    (G : Finset β) (hG : f '' E ⊆ G) :
    ∑ C ∈ G.powerset.filter (fun C : Finset β => (M.map f hf).IsBase (C : Set β)),
        ∏ e ∈ C, X e =
      rename f (∑ B ∈ E.powerset.filter (fun B : Finset α => M.IsBase (B : Set α)),
        ∏ e ∈ B, (X e : MvPolynomial α ℝ)) := by
  rw [hE] at hf
  simp only [map_sum, map_prod, rename_X]
  symm
  refine Finset.sum_nbij' (fun B => B.image f) (fun C => E.filter (f · ∈ C)) ?_ ?_ ?_ ?_ ?_
  · intro B hB
    simp only [Finset.mem_filter, Finset.mem_powerset] at hB ⊢
    refine ⟨fun y hy => ?_, (Matroid.map_isBase_iff _ _ _).2 ⟨_, hB.2, by simp⟩⟩
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
    exact hG ⟨x, hB.1 hx, rfl⟩
  · intro C hC
    simp only [Finset.mem_filter, Finset.mem_powerset] at hC ⊢
    obtain ⟨B₀, hB₀, hCB₀⟩ := (Matroid.map_isBase_iff _ _ _).1 hC.2
    have hB₀E : B₀ ⊆ E := hE ▸ hB₀.subset_ground
    refine ⟨Finset.filter_subset _ _, ?_⟩
    convert hB₀
    ext x
    have hfx : f x ∈ C ↔ f x ∈ f '' B₀ := by rw [← hCB₀, Finset.mem_coe]
    simp only [Finset.coe_filter, mem_ofPred_eq, hfx]
    refine ⟨fun ⟨hx, y, hy, hyx⟩ => ?_, fun hx => ⟨hB₀E hx, x, hx, rfl⟩⟩
    rwa [← hf (hB₀E hy) hx hyx]
  · intro B hB
    simp only [Finset.mem_filter, Finset.mem_powerset] at hB
    ext x
    simp only [Finset.mem_filter, Finset.mem_image]
    refine ⟨fun ⟨hx, y, hy, hyx⟩ => ?_, fun hx => ⟨hB.1 hx, x, hx, rfl⟩⟩
    rwa [← hf (hB.1 hy) hx hyx]
  · intro C hC
    simp only [Finset.mem_filter, Finset.mem_powerset] at hC
    obtain ⟨B₀, hB₀, hCB₀⟩ := (Matroid.map_isBase_iff _ _ _).1 hC.2
    have hB₀E : B₀ ⊆ E := hE ▸ hB₀.subset_ground
    ext y
    simp only [Finset.mem_image, Finset.mem_filter]
    refine ⟨fun ⟨x, ⟨_, hx⟩, hxy⟩ => hxy ▸ hx, fun hy => ?_⟩
    have : y ∈ f '' B₀ := hCB₀ ▸ hy
    obtain ⟨x, hx, rfl⟩ := this
    exact ⟨x, ⟨hB₀E hx, hy⟩, rfl⟩
  · intro B hB
    simp only [Finset.mem_filter, Finset.mem_powerset] at hB
    rw [Finset.prod_image fun x hx y hy hxy => hf (hB.1 hx) (hB.1 hy) hxy]

/-- The position relabelling of a permutation word is injective on positions in range, and
sends them into `{x, y} × [n]`. -/
private lemma positionRelabelMap_injOn_mapsTo {n : ℕ} {π : List ℕ} (hπ : π ∈ permWords n) :
    InjOn (List.positionRelabelMap π) {e | e.2 < n} ∧
      ∀ e : Bool × ℕ, e.2 < n →
        List.positionRelabelMap π e ∈ (Finset.univ ×ˢ Finset.Icc 1 n : Finset (Bool × ℕ)) := by
  obtain ⟨⟨hnd, -⟩, hlen, hlet⟩ := hπ
  subst hlen
  refine ⟨fun e he e' he' h => ?_, fun e he => ?_⟩
  · simp only [mem_ofPred_eq] at he he'
    simp only [List.positionRelabelMap, Prod.mk.injEq, List.getD_eq_getElem _ _ he,
      List.getD_eq_getElem _ _ he'] at h
    exact Prod.ext h.1 ((hnd.getElem_inj_iff).1 h.2)
  · simp only [List.positionRelabelMap, List.getD_eq_getElem _ _ he, Finset.mem_product,
      Finset.mem_univ, true_and]
    rw [← hlet]
    exact List.mem_toFinset.2 (List.getElem_mem he)

/-- A matroid whose independent sets are the forest independent family is laminar, with the
forest blocks as laminar family and the subtree sizes as capacities. -/
private lemma isLaminar_of_indep_iff_mem_forestIndepFamily {N : ℕ} {par : ℕ → Option ℕ}
    {L : Finset ℕ} {M : Matroid (Bool × ℕ)} (hE : M.E = ↑(forestGroundSet N L))
    (hI : ∀ I, M.Indep I ↔ ∃ J ∈ forestIndepFamily N par L, (J : Set (Bool × ℕ)) = I) :
    M.IsLaminar := by
  refine ⟨Finset.Icc 1 N, inferInstance, fun v => forestBlock N par L v,
    fun v => (subtreeVertices N par v).card, (isLaminar_forestBlock N par L).2, fun I => ?_⟩
  simp only [hI, capacityBoundedSets, mem_ofPred_eq, hE, forestIndepFamily, Finset.mem_filter,
    Finset.mem_powerset]
  constructor
  · rintro ⟨J, ⟨hJE, hJc⟩, rfl⟩
    refine ⟨Finset.coe_subset.2 hJE, fun v => ?_⟩
    rw [← Finset.coe_inter, encard_coe_eq_coe_finsetCard]
    exact_mod_cast hJc v v.2
  · rintro ⟨hIE, hIc⟩
    obtain ⟨J, rfl⟩ := ((forestGroundSet N L).finite_toSet.subset hIE).exists_finset_coe
    refine ⟨J, ⟨Finset.coe_subset.1 hIE, fun v hv => ?_⟩, rfl⟩
    have h := hIc ⟨v, hv⟩
    rw [← Finset.coe_inter, encard_coe_eq_coe_finsetCard] at h
    exact_mod_cast h

/-- Laminarity is preserved by mapping along an injective map and then reading the image on a
finite superset `G` of its ground set: a block `A k` becomes `f '' (A k ∩ M.E)` with the same
capacity, and the new loops `G \ f '' M.E` form one more block, of capacity `0`. -/
private lemma isLaminar_onFinset_map {α β : Type*} {M : Matroid α} (hM : M.IsLaminar)
    {f : α → β} (hf : InjOn f M.E) {G : Finset β} :
    (onFinset (M.map f hf) G).IsLaminar := by
  obtain ⟨ι, _, A, c, hlam, hind⟩ := hM
  let A' : Option ι → Set G
    | some k => Subtype.val ⁻¹' (f '' (A k ∩ M.E))
    | none => (Subtype.val ⁻¹' (f '' M.E))ᶜ
  let c' : Option ι → ℕ
    | some k => c k
    | none => 0
  have henc : ∀ (I : Set G) (J : Set α) (k : ι), J ⊆ M.E → Subtype.val '' I = f '' J →
      (I ∩ A' (some k)).encard = (J ∩ A k).encard := by
    intro I J k hJ hIJ
    rw [← Subtype.val_injective.injOn.encard_image, image_inter_preimage, hIJ,
      ← hf.image_inter hJ inter_subset_right, (hf.mono (inter_subset_left.trans hJ)).encard_image,
      inter_comm (A k), ← inter_assoc, inter_eq_left.2 hJ]
  refine ⟨Option ι, inferInstance, A', c', ?_, fun I => ?_⟩
  · rintro (_ | i) (_ | j) ⟨x, hxi, hxj⟩
    · exact Or.inl subset_rfl
    · exact absurd (image_mono inter_subset_right hxj) hxi
    · exact absurd (image_mono inter_subset_right hxi) hxj
    · obtain ⟨a, ha, hax⟩ := hxi
      obtain ⟨b, hb, hbx⟩ := hxj
      obtain rfl : a = b := hf ha.2 hb.2 (hax.trans hbx.symm)
      rcases hlam i j ⟨a, ha.1, hb.1⟩ with h | h
      · exact Or.inl (preimage_mono (image_mono (inter_subset_inter_left _ h)))
      · exact Or.inr (preimage_mono (image_mono (inter_subset_inter_left _ h)))
  rw [onFinset_indep_iff, Matroid.map_indep_iff, onFinset_ground]
  simp only [hind, capacityBoundedSets, mem_ofPred_eq, subset_univ, true_and]
  constructor
  · rintro ⟨J, ⟨hJE, hJc⟩, hIJ⟩ (_ | k)
    · have : I ∩ A' none = ∅ := eq_empty_iff_forall_notMem.2 fun x ⟨hx, hxn⟩ =>
        hxn (image_mono hJE (hIJ ▸ ⟨x, hx, rfl⟩))
      simp [this, c']
    · exact (henc I J k hJE hIJ).trans_le (hJc k)
  · intro hcap
    have h0 : (I ∩ A' none).encard ≤ 0 := hcap none
    have hIE : Subtype.val '' I ⊆ f '' M.E := by
      rintro _ ⟨x, hx, rfl⟩
      by_contra hne
      exact (encard_eq_zero.1 (nonpos_iff_eq_zero.1 h0)).subset ⟨hx, hne⟩
    have hIJ : Subtype.val '' I = f '' (M.E ∩ f ⁻¹' (Subtype.val '' I)) := by
      rw [image_inter_preimage, inter_eq_right.2 hIE]
    exact ⟨_, ⟨inter_subset_left, fun k =>
      (henc I _ k inter_subset_left hIJ).symm.trans_le (hcap (some k))⟩, hIJ⟩

/-- A base of the image of `M`, read on a finite superset of the image ground set, has the
cardinality of a base of `M`. -/
private lemma exists_isBase_encard_eq_of_isBase_onFinset_map {α β : Type*} {M : Matroid α}
    {f : α → β} (hf : InjOn f M.E) {G : Finset β} (hG : f '' M.E ⊆ G) {B : Set G}
    (hB : (onFinset (M.map f hf) G).IsBase B) : ∃ B₀, M.IsBase B₀ ∧ B.encard = B₀.encard := by
  obtain ⟨B₀, hB₀, hBB₀⟩ := (Matroid.map_isBase_iff _ _ _).1 ((onFinset_isBase_iff hG).1 hB)
  refine ⟨B₀, hB₀, ?_⟩
  rw [← Subtype.val_injective.injOn.encard_image, hBB₀, (hf.mono hB₀.subset_ground).encard_image]


namespace List

/-- **Theorem 1.2.** For `n ≥ 1` and `π ∈ S_n` with nonempty stack-sorting fiber, there is a
laminar matroid on `{x, y} × [n]` all of whose bases have `n - 1` elements and whose basis
generating polynomial is the fiber top polynomial `𝒟_π`. -/
@[lognarayana "thm_top_laminar_matroid"]
public theorem exists_isLaminar_basisGeneratingPolynomial_eq_fiberTopPolynomial
    {n : ℕ} (hn : 1 ≤ n) {π : List ℕ} (hπ : π ∈ permWords n) (hfib : (stackFiber π).Nonempty) :
    ∃ M : Matroid ↥(Finset.univ ×ˢ Finset.Icc 1 n : Finset (Bool × ℕ)),
      M.E = Set.univ ∧ M.IsLaminar ∧ (∀ B, M.IsBase B → B.encard = ((n - 1 : ℕ) : ℕ∞)) ∧
      rename Subtype.val (M.basisGeneratingPolynomial ℝ) = fiberTopPolynomial ℝ π := by
  classical
  set N := n - 1 with hN
  set par := π.adoptableForest
  set L := π.descentSet
  set E₀ := forestGroundSet N L
  set G : Finset (Bool × ℕ) := Finset.univ ×ˢ Finset.Icc 1 n
  set ρ := List.positionRelabelMap π
  have hlen : π.length = n := hπ.2.1
  have hpar : IsPostorderForest N par := by
    simpa [hlen] using List.isPostorderForest_adoptableForest π
  have hL : L ⊆ Finset.Icc 1 N := by
    intro i hi
    simp only [L, List.descentSet, Finset.mem_filter, Finset.mem_Ico] at hi
    simp only [Finset.mem_Icc]
    omega
  have hD := List.fiberTopPolynomial_eq_positionRelabel_forestMatchingPoly ℝ hn hπ
  have hZ : forestMatchingPoly ℝ N par L ≠ 0 := by
    intro h
    rw [h, map_zero] at hD
    have := congrArg (MvPolynomial.eval fun _ => (1 : ℝ)) hD
    simp only [List.fiberTopPolynomial, map_sum, map_mul, map_prod, eval_X,
      Finset.prod_const_one, mul_one, Finset.sum_const, nsmul_eq_mul, map_zero, Nat.cast_eq_zero,
      Finset.card_eq_zero] at this
    exact hfib.ne_empty this
  obtain ⟨M₀, hE₀, hI₀⟩ := exists_matroid_indep_iff_mem_forestIndepFamily N par L
  have hE₀n : ∀ e ∈ (E₀ : Set (Bool × ℕ)), e.2 < n := by
    intro e he
    simp only [E₀, forestGroundSet, Finset.coe_product, Finset.coe_univ, mem_prod, mem_univ,
      true_and, Finset.coe_sdiff, mem_sdiff, Finset.coe_Icc, mem_Icc] at he
    omega
  obtain ⟨hinj', hmaps⟩ := positionRelabelMap_injOn_mapsTo hπ
  have hinj : InjOn ρ (E₀ : Set (Bool × ℕ)) := hinj'.mono hE₀n
  have hρG : ρ '' E₀ ⊆ G := by
    rintro _ ⟨e, he, rfl⟩
    exact hmaps e (hE₀n e he)
  set M₁ := M₀.map ρ (hE₀ ▸ hinj)
  have hM₁E : ρ '' M₀.E ⊆ G := hE₀ ▸ hρG
  refine ⟨onFinset M₁ G, onFinset_ground M₁ G, ?_, ?_, ?_⟩
  · exact isLaminar_onFinset_map
      (isLaminar_of_indep_iff_mem_forestIndepFamily hE₀ hI₀) _
  · intro B hB
    obtain ⟨B₀, hB₀, h⟩ := exists_isBase_encard_eq_of_isBase_onFinset_map _ hM₁E hB
    rw [h, Matroid.encard_eq_of_isBase_of_indep_iff_mem_forestIndepFamily hpar hL hZ M₀ hI₀
      hB₀]
  · rw [rename_basisGeneratingPolynomial_onFinset M₁ G hM₁E,
      sum_isBase_map_prod_X M₀ E₀ hE₀ ρ _ G hρG, hD,
      forestMatchingPoly_eq_sum_isBase_prod_X hpar hL hZ M₀ hE₀ hI₀]

end List

end

/-! ### The fiber top polynomial is Lorentzian -/

section

open MvPolynomial


namespace List

/-- **Theorem 1.2.** For `n ≥ 1` and `π ∈ S_n`, the fiber top polynomial `𝒟_π(x, y)` is
Lorentzian: it is the image, under renaming along the inclusion `{x, y} × [n] ↪ Bool × ℕ`, of a
Lorentzian polynomial in the variables `{x, y} × [n]`. This is stated given the Brändén–Huh
theorem that normalized support polynomials of M-convex sets are Lorentzian. -/
@[lognarayana "thm_top_lorentzian"]
public theorem isLorentzian_fiberTopPolynomial {n : ℕ} (hn : 1 ≤ n) {π : List ℕ}
    (hπ : π ∈ permWords n)
    (hBH : NormalizedSupportPolyLorentzianOfMConvex
      ↥(Finset.univ ×ˢ Finset.Icc 1 n : Finset (Bool × ℕ))) :
    ∃ p : MvPolynomial ↥(Finset.univ ×ˢ Finset.Icc 1 n : Finset (Bool × ℕ)) ℝ,
      rename Subtype.val p = fiberTopPolynomial ℝ π ∧ p.IsLorentzian := by
  rcases (List.stackFiber π).eq_empty_or_nonempty with h | h
  · refine ⟨0, ?_, Or.inl rfl⟩
    rw [List.fiberTopPolynomial, h, Finset.sum_empty]
    exact map_zero _
  · obtain ⟨M, -, -, -, hM⟩ :=
      List.exists_isLaminar_basisGeneratingPolynomial_eq_fiberTopPolynomial hn hπ h
    exact ⟨_, hM, M.isLorentzian_basisGeneratingPolynomial hBH⟩

end List

end

/-! ### The homogeneous fiber polynomial is Lorentzian -/

section

open MvPolynomial

/-- Renaming variables along any map `f : σ → τ` is the nonnegative linear substitution with
the `0/1` matrix `a i j = [f i = j]`, so it preserves the Lorentzian property. -/
private lemma isLorentzian_rename {σ τ : Type*} [Fintype σ] [Fintype τ]
    (hsub : LorentzianNonnegLinearSubstitution σ τ) (f : σ → τ) {p : MvPolynomial σ ℝ}
    (hp : p.IsLorentzian) : (rename f p).IsLorentzian := by
  classical
  convert hsub (fun i j ↦ if f i = j then 1 else 0) (fun i j ↦ by positivity) p hp using 2
  exact algHom_ext fun i ↦ by simp


namespace List

/-- **Theorem 1.1.** For `n ≥ 1` and `π ∈ S_n`, the homogeneous fiber polynomial
`H_π(x, y)` is Lorentzian, given the Brändén–Huh theorems that normalized support polynomials of
M-convex sets are Lorentzian and that nonnegative linear substitutions preserve Lorentzian
polynomials. -/
@[lognarayana "thm_fiber_homog_lorentzian"]
public theorem isLorentzian_fiberHomogPolynomial {n : ℕ} (hn : 1 ≤ n) {π : List ℕ}
    (hπ : π ∈ permWords n)
    (hBH : NormalizedSupportPolyLorentzianOfMConvex
      ↥(Finset.univ ×ˢ Finset.Icc 1 n : Finset (Bool × ℕ)))
    (hsub : LorentzianNonnegLinearSubstitution
      ↥(Finset.univ ×ˢ Finset.Icc 1 n : Finset (Bool × ℕ)) (Fin 2)) :
    (fiberHomogPolynomial ℝ π).IsLorentzian := by
  obtain ⟨p, hp, hpL⟩ := List.isLorentzian_fiberTopPolynomial hn hπ hBH
  have := isLorentzian_rename hsub ((fun q : Bool × ℕ ↦ if q.1 then (0 : Fin 2) else 1) ∘
    Subtype.val) hpL
  rwa [← rename_rename, hp, List.rename_fiberTopPolynomial ℝ π] at this

end List

end

/-! ### Ultra-log-concavity of the fiber descent polynomial -/

section

open List Polynomial

/-- The fiber descent polynomial has nonnegative coefficients. -/
private lemma coeff_fiberDescentPolynomial_nonneg (π : List ℕ) (i : ℕ) :
    0 ≤ (fiberDescentPolynomial ℝ π).coeff i := by
  simp only [fiberDescentPolynomial, finsetSum_coeff, coeff_X_pow]
  exact Finset.sum_nonneg fun _ _ ↦ by split_ifs <;> norm_num

/-- A word has at most `length - 1` descents, so every member of the stack-sorting fiber of
`π` contributes a monomial of degree at most `π.length - 1`. -/
private lemma natDegree_fiberDescentPolynomial_le (π : List ℕ) :
    (fiberDescentPolynomial ℝ π).natDegree ≤ π.length - 1 := by
  refine natDegree_sum_le_of_forall_le _ _ fun σ hσ ↦ (natDegree_X_pow_le _).trans ?_
  simp only [stackFiber, Finset.mem_filter, List.mem_toFinset, List.mem_permutations] at hσ
  rw [← List.length_range' (s := 1) (n := π.length), ← idPermWord, ← hσ.1.length_eq]
  exact (Finset.card_filter_le _ _).trans (by simp)


namespace List

/-- For `n ≥ 1` and `π ∈ S_n`, the fiber descent polynomial `D_π(x)` is ultra-log-concave of
order `n - 1`. -/
@[lognarayana "thm_fiber_ulc"]
public theorem isUltraLogConcave_fiberDescentPolynomial {n : ℕ} (hn : 1 ≤ n) {π : List ℕ}
    (hπ : π ∈ permWords n)
    (hBH : MvPolynomial.NormalizedSupportPolyLorentzianOfMConvex
      ↥(Finset.univ ×ˢ Finset.Icc 1 n : Finset (Bool × ℕ)))
    (hsub : MvPolynomial.LorentzianNonnegLinearSubstitution
      ↥(Finset.univ ×ˢ Finset.Icc 1 n : Finset (Bool × ℕ)) (Fin 2)) :
    (fiberDescentPolynomial ℝ π).IsUltraLogConcave (n - 1) := by
  rw [← isLorentzian_homogenize_iff_isUltraLogConcave (coeff_fiberDescentPolynomial_nonneg π)
      (hπ.2.1 ▸ natDegree_fiberDescentPolynomial_le π),
    ← fiberHomogPolynomial_eq_homogenize ℝ hn hπ]
  exact isLorentzian_fiberHomogPolynomial hn hπ hBH hsub

end List

end

/-! ### Log-concavity of the fiber descent polynomial -/

section


namespace List

/-- For `n ≥ 1` and `π ∈ S_n`, the fiber descent polynomial `D_π(x)` is log-concave. -/
@[lognarayana "thm_fiber_log_concave"]
public theorem isLogConcave_fiberDescentPolynomial {n : ℕ} (hn : 1 ≤ n) {π : List ℕ}
    (hπ : π ∈ permWords n)
    (hBH : MvPolynomial.NormalizedSupportPolyLorentzianOfMConvex
      ↥(Finset.univ ×ˢ Finset.Icc 1 n : Finset (Bool × ℕ)))
    (hsub : MvPolynomial.LorentzianNonnegLinearSubstitution
      ↥(Finset.univ ×ˢ Finset.Icc 1 n : Finset (Bool × ℕ)) (Fin 2)) :
    (fiberDescentPolynomial ℝ π).IsLogConcave :=
  (List.isUltraLogConcave_fiberDescentPolynomial hn hπ hBH hsub).isLogConcave

end List

end

/-! ### The conditioned fiber top polynomial is Lorentzian -/

section

open MvPolynomial

/-- The variables `{x} × P ∪ {y} × Q`. -/
private def tops (P Q : Finset ℕ) : Finset (Bool × ℕ) :=
  P.image (Prod.mk true) ∪ Q.image (Prod.mk false)

private lemma mem_tops {P Q : Finset ℕ} {b : Bool} {a : ℕ} :
    (b, a) ∈ tops P Q ↔ cond b (a ∈ P) (a ∈ Q) := by
  cases b <;> simp [tops]

private lemma prod_tops (P Q : Finset ℕ) :
    ∏ e ∈ tops P Q, (X e : MvPolynomial (Bool × ℕ) ℝ) =
      (∏ a ∈ P, X (true, a)) * ∏ b ∈ Q, X (false, b) := by
  rw [tops, Finset.prod_union, Finset.prod_image, Finset.prod_image]
  · intro _ _ _ _ h; exact (Prod.mk.inj h).2
  · intro _ _ _ _ h; exact (Prod.mk.inj h).2
  · rw [Finset.disjoint_left]; simp

private lemma tops_sdiff (P Q P' Q' : Finset ℕ) :
    tops P Q \ tops P' Q' = tops (P \ P') (Q \ Q') := by
  ext ⟨b, a⟩; cases b <;> simp [mem_tops]

private lemma tops_subset_iff {P Q P' Q' : Finset ℕ} :
    tops P Q ⊆ tops P' Q' ↔ P ⊆ P' ∧ Q ⊆ Q' := by
  simp only [Finset.subset_iff, Prod.forall, Bool.forall_bool, mem_tops, cond_false, cond_true]
  tauto

private lemma disjoint_tops_iff {P Q P' Q' : Finset ℕ} :
    Disjoint (tops P Q) (tops P' Q') ↔ Disjoint P P' ∧ Disjoint Q Q' := by
  simp only [Finset.disjoint_left, Prod.forall, Bool.forall_bool, mem_tops, cond_false,
    cond_true]
  tauto

private lemma disjoint_sdiff_iff {s t u : Finset ℕ} (h : Disjoint t u) :
    Disjoint (s \ t) u ↔ Disjoint s u := by
  rw [disjoint_sdiff_comm, h.symm.sdiff_eq_left]
/-- The partial derivative of a squarefree monomial. -/
private lemma pderiv_prod_X {τ : Type*} [DecidableEq τ] (T : Finset τ) (e : τ) :
    pderiv e (∏ x ∈ T, (X x : MvPolynomial τ ℝ)) =
      if e ∈ T then ∏ x ∈ T.erase e, X x else 0 := by
  have hz : ∀ S : Finset τ, e ∉ S → pderiv e (∏ x ∈ S, (X x : MvPolynomial τ ℝ)) = 0 := by
    intro S
    induction S using Finset.induction_on with
    | empty => intro _; rw [Finset.prod_empty]; exact Derivation.map_one_eq_zero _
    | insert a S haS ih =>
      intro hS
      rw [Finset.prod_insert haS, Derivation.leibniz,
        pderiv_X_of_ne (fun h : a = e ↦ hS (h ▸ Finset.mem_insert_self a S)),
        ih (fun h ↦ hS (Finset.mem_insert_of_mem h))]
      simp
  split_ifs with h
  · rw [← Finset.mul_prod_erase T _ h, Derivation.leibniz, pderiv_X_self,
      hz _ (Finset.notMem_erase e T)]
    simp
  · exact hz T h

/-- Substituting `0` for the variables in `B` in a squarefree monomial. -/
private lemma aeval_prod_X {τ : Type*} [DecidableEq τ] (R B : Finset τ) :
    aeval (R := ℝ) (fun e ↦ if e ∈ B then 0 else (X e : MvPolynomial τ ℝ))
        (∏ x ∈ R, (X x : MvPolynomial τ ℝ)) =
      if Disjoint R B then ∏ x ∈ R, X x else 0 := by
  rw [map_prod]
  simp only [aeval_X]
  split_ifs with h
  · exact Finset.prod_congr rfl fun x hx ↦ by rw [if_neg (Finset.disjoint_left.1 h hx)]
  · obtain ⟨x, hxR, hxB⟩ := Finset.not_disjoint_iff.1 h
    exact Finset.prod_eq_zero hxR (if_pos hxB)

private lemma descentTops_subset (σ : List ℕ) : σ.descentTops ⊆ σ.toFinset := by
  intro a ha
  simp only [List.descentTops, List.mem_toFinset, List.mem_map, List.mem_filter] at ha
  obtain ⟨⟨x, y⟩, ⟨hm, _⟩, rfl⟩ := ha
  exact List.mem_toFinset.2 (List.of_mem_zip hm).1

private lemma ascentTops_subset (σ : List ℕ) : σ.ascentTops ⊆ σ.toFinset := by
  intro a ha
  simp only [List.ascentTops, List.mem_toFinset, List.mem_map, List.mem_filter] at ha
  obtain ⟨⟨x, y⟩, ⟨hm, _⟩, rfl⟩ := ha
  exact List.mem_toFinset.2 (List.mem_of_mem_tail (List.of_mem_zip hm).2)

private lemma toFinset_of_mem_stackFiber {n : ℕ} {π σ : List ℕ} (hπ : π ∈ permWords n)
    (hσ : σ ∈ List.stackFiber π) : σ.toFinset = Finset.Icc 1 n := by
  simp only [List.stackFiber, Finset.mem_filter, List.mem_toFinset, List.mem_permutations] at hσ
  rw [List.toFinset_eq_of_perm _ _ hσ.1, hπ.2.1]
  ext a
  simp [idPermWord, List.mem_range'_1]
  omega

/-- Brändén–Huh's derivative closure, specialised to a single partial derivative. -/
private lemma isLorentzian_pderiv {σ : Type*} [Fintype σ]
    (hder : LorentzianNonnegDerivative σ) (i : σ) {f : MvPolynomial σ ℝ} (hf : f.IsLorentzian) :
    (pderiv i f).IsLorentzian := by
  classical
  simpa [Pi.single_apply, ite_smul] using hder (Pi.single i 1)
    (fun j ↦ by by_cases hj : j = i <;> simp [hj]) f hf

/-- Substituting `0` for the variables satisfying `s` preserves the Lorentzian property. -/
private lemma isLorentzian_aeval_ite_zero {σ : Type*} [Fintype σ]
    (hsub : LorentzianNonnegLinearSubstitution σ σ) (s : σ → Prop) [DecidablePred s]
    {f : MvPolynomial σ ℝ} (hf : f.IsLorentzian) :
    (aeval (fun i ↦ if s i then 0 else (X i : MvPolynomial σ ℝ)) f).IsLorentzian := by
  classical
  convert hsub (fun i j ↦ if ¬s i ∧ j = i then 1 else 0) (fun i j ↦ by positivity) f hf using 3
  funext i
  by_cases hi : s i <;> simp [hi, ite_smul]

/-- Substituting `0` for the variables in `B` commutes with reading a polynomial in a subtype of
the variables. -/
private lemma rename_aeval_ite_zero {τ : Type*} [DecidableEq τ] {U : Finset τ} (B : Finset τ)
    (q : MvPolynomial U ℝ) :
    rename Subtype.val (aeval (fun i : U ↦ if i.1 ∈ B then 0 else (X i : MvPolynomial U ℝ)) q) =
      aeval (fun e ↦ if e ∈ B then 0 else (X e : MvPolynomial τ ℝ)) (rename Subtype.val q) := by
  rw [← AlgHom.comp_apply, ← AlgHom.comp_apply]
  congr 1
  exact algHom_ext fun i ↦ by by_cases hi : i.1 ∈ B <;> simp [hi]

/-- One partial derivative in each variable of `S` applied to a Lorentzian sum of squarefree
monomials `∑_σ ∏_{e ∈ T σ} z_e`, read in the variables `U ⊇ S`, gives a Lorentzian polynomial:
the sum of `∏_{e ∈ T σ \ S} z_e` over those `σ` with `S ⊆ T σ`. -/
private lemma exists_isLorentzian_pderivs {τ ι : Type*} [DecidableEq τ] {U : Finset τ}
    (hder : LorentzianNonnegDerivative U) (s : Finset ι) (T : ι → Finset τ)
    {p : MvPolynomial U ℝ} (hp : rename Subtype.val p = ∑ σ ∈ s, ∏ e ∈ T σ, X e)
    (hL : p.IsLorentzian) {S : Finset τ} (hS : S ⊆ U) :
    ∃ q : MvPolynomial U ℝ,
      rename Subtype.val q = ∑ σ ∈ s.filter (fun σ ↦ S ⊆ T σ), ∏ e ∈ T σ \ S, X e ∧
      q.IsLorentzian := by
  induction S using Finset.induction_on with
  | empty => exact ⟨p, by simpa using hp, hL⟩
  | insert e S heS ih =>
    obtain ⟨q, hq, hqL⟩ := ih ((Finset.subset_insert e S).trans hS)
    refine ⟨pderiv ⟨e, hS (Finset.mem_insert_self e S)⟩ q, ?_, isLorentzian_pderiv hder _ hqL⟩
    rw [← pderiv_rename Subtype.val_injective, hq, map_sum, Finset.sum_filter, Finset.sum_filter]
    refine Finset.sum_congr rfl fun σ _ ↦ ?_
    by_cases hST : S ⊆ T σ <;> by_cases heT : e ∈ T σ <;>
      simp [hST, heT, heS, pderiv_prod_X, Finset.sdiff_insert, Finset.insert_subset_iff]

namespace List

/-- **Corollary 3.6, Lorentzian step.** For `n ≥ 1`, `π ∈ S_n` and finite sets
`A_d, B_d, A_a, B_a` of natural numbers, the polynomial
`G = ∑_σ ∏_{a ∈ DT(σ) ∖ A_d} x_a ∏_{b ∈ AT(σ) ∖ A_a} y_b`, the sum over the `σ ∈ s⁻¹(π)` with
`A_d ⊆ DT(σ)`, `DT(σ) ∩ B_d = ∅`, `A_a ⊆ AT(σ)` and `AT(σ) ∩ B_a = ∅`, is Lorentzian: it is the
image, under renaming along `{x, y} × [n] ↪ Bool × ℕ`, of a Lorentzian polynomial in the
variables `{x, y} × [n]`. This is stated given the Brändén–Huh theorems on M-convex supports,
nonnegative derivatives and nonnegative linear substitutions. -/
@[lognarayana "lem_conditional_top_lorentzian"]
public theorem isLorentzian_conditionalTopPolynomial {n : ℕ} (hn : 1 ≤ n) {π : List ℕ}
    (hπ : π ∈ permWords n) (A_d B_d A_a B_a : Finset ℕ)
    (hBH : NormalizedSupportPolyLorentzianOfMConvex
      ↥(Finset.univ ×ˢ Finset.Icc 1 n : Finset (Bool × ℕ)))
    (hder : LorentzianNonnegDerivative ↥(Finset.univ ×ˢ Finset.Icc 1 n : Finset (Bool × ℕ)))
    (hsub : LorentzianNonnegLinearSubstitution
      ↥(Finset.univ ×ˢ Finset.Icc 1 n : Finset (Bool × ℕ))
      ↥(Finset.univ ×ˢ Finset.Icc 1 n : Finset (Bool × ℕ))) :
    ∃ p : MvPolynomial ↥(Finset.univ ×ˢ Finset.Icc 1 n : Finset (Bool × ℕ)) ℝ,
      rename Subtype.val p =
        ∑ σ ∈ (stackFiber π).filter (fun σ ↦ A_d ⊆ σ.descentTops ∧
            _root_.Disjoint σ.descentTops B_d ∧ A_a ⊆ σ.ascentTops ∧
            _root_.Disjoint σ.ascentTops B_a),
          (∏ a ∈ σ.descentTops \ A_d, X (true, a)) * ∏ b ∈ σ.ascentTops \ A_a, X (false, b) ∧
      p.IsLorentzian := by
  -- if no word of the fiber meets the conditions, the polynomial is `0`
  by_cases hA : A_d ⊆ Finset.Icc 1 n ∧ A_a ⊆ Finset.Icc 1 n ∧ _root_.Disjoint A_d B_d ∧
      _root_.Disjoint A_a B_a
  swap
  · refine ⟨0, ?_, Or.inl rfl⟩
    rw [map_zero, Finset.filter_false_of_mem, Finset.sum_empty]
    rintro σ hσ ⟨h1, h2, h3, h4⟩
    have hσn := toFinset_of_mem_stackFiber hπ hσ
    exact hA ⟨hσn ▸ h1.trans (descentTops_subset σ), hσn ▸ h3.trans (ascentTops_subset σ),
      h2.mono_left h1, h4.mono_left h3⟩
  obtain ⟨hAd, hAa, hdd, hda⟩ := hA
  obtain ⟨p, hp, hL⟩ := List.isLorentzian_fiberTopPolynomial hn hπ hBH
  obtain ⟨q, hq, hqL⟩ := exists_isLorentzian_pderivs hder (List.stackFiber π)
    (fun σ ↦ tops σ.descentTops σ.ascentTops) (by simp_rw [hp, List.fiberTopPolynomial, prod_tops])
    hL (S := tops A_d A_a) fun ⟨b, a⟩ h ↦ Finset.mem_product.2
      ⟨Finset.mem_univ b, by cases b; exacts [hAa (mem_tops.1 h), hAd (mem_tops.1 h)]⟩
  refine ⟨aeval (fun i ↦ if i.1 ∈ tops B_d B_a then 0 else X i) q, ?_,
    isLorentzian_aeval_ite_zero hsub _ hqL⟩
  rw [rename_aeval_ite_zero, hq, map_sum, Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun σ _ ↦ ?_
  rw [aeval_prod_X, ← ite_and, tops_sdiff, prod_tops]
  refine if_congr ?_ rfl rfl
  rw [tops_subset_iff, disjoint_tops_iff, disjoint_sdiff_iff hdd, disjoint_sdiff_iff hda]
  tauto

end List

end

/-! ### Corollary 3.6 -/

section

open MvPolynomial

/-- For a list without repeated entries, `|DT(σ)| + |AT(σ)| = ℓ(σ) - 1`. -/
private lemma card_descentTops_add_card_ascentTops {σ : List ℕ} (hσ : σ.Nodup) :
    σ.descentTops.card + σ.ascentTops.card = σ.length - 1 := by
  rw [card_descentTops hσ, card_ascentTops hσ]
  have : σ.numDescents ≤ σ.length - 1 := (Finset.card_filter_le _ _).trans (by simp)
  omega

/-- The stack-sorting fiber of `π ∈ S_n` lies in `S_n`. -/
private lemma mem_permWords_of_mem_stackFiber {n : ℕ} {π σ : List ℕ} (hπ : π ∈ permWords n)
    (hσ : σ ∈ List.stackFiber π) : σ ∈ permWords n := by
  simp only [List.stackFiber, Finset.mem_filter, List.mem_toFinset, List.mem_permutations,
    hπ.2.1] at hσ
  exact mem_permWords_iff_perm.2 hσ.1

/-- The descent tops and ascent tops of `σ ∈ S_n` lie in `[n]`. -/
private lemma tops_subset_Icc {n : ℕ} {σ : List ℕ} (hσ : σ ∈ permWords n) :
    σ.descentTops ⊆ Finset.Icc 1 n ∧ σ.ascentTops ⊆ Finset.Icc 1 n := by
  rw [← hσ.2.2]
  exact ⟨descentTops_subset σ, ascentTops_subset σ⟩

/-- **Brändén–Huh**, weighted renaming: substituting `z_i ↦ w_i z_{f(i)}` with `w ≥ 0`
preserves the Lorentzian property. -/
private lemma isLorentzian_aeval_C_mul_X {σ τ : Type*} [Fintype σ] [Fintype τ]
    (hsub : LorentzianNonnegLinearSubstitution σ τ) {w : σ → ℝ} (hw : ∀ i, 0 ≤ w i) (f : σ → τ)
    {p : MvPolynomial σ ℝ} (hp : p.IsLorentzian) :
    (aeval (fun i ↦ C (w i) * X (f i) : σ → MvPolynomial τ ℝ) p).IsLorentzian := by
  classical
  convert hsub (fun i j ↦ if f i = j then w i else 0)
    (fun i j ↦ by split_ifs <;> simp [hw]) p hp using 3
  funext i
  simp [ite_smul, smul_eq_C_mul]

/-- The substitution `x_a ↦ α_a z_{a ∈ J_d}`, `y_b ↦ β_b z_{b ∈ J_a}`, where `z_{true} = x` and
`z_{false} = y` are the variables `0, 1 : Fin 2`; the Boolean tags `true`, `false` mark the
descent and ascent variables. -/
private noncomputable def xySubst (J_d J_a : Finset ℕ) (α β : ℕ → ℝ) :
    Bool × ℕ → MvPolynomial (Fin 2) ℝ
  | (true, a) => C (α a) * X (if a ∈ J_d then 0 else 1)
  | (false, b) => C (β b) * X (if b ∈ J_a then 0 else 1)

/-- Removing from `S` a set disjoint from `J` does not change `S ∩ J`. -/
private lemma sdiff_inter_eq_inter {A J : Finset ℕ} (S : Finset ℕ) (h : Disjoint J A) :
    (S \ A) ∩ J = S ∩ J := by
  rw [Finset.sdiff_inter_right_comm, Finset.sdiff_eq_self_of_disjoint
    (h.mono_left Finset.inter_subset_right)]

/-- `∏_{a ∈ S} c_a z_{i(a)}`, with `z_{i(a)} = x` on `J` and `y` off it, is
`(∏_{a ∈ S} c_a) x^{|S ∩ J|} y^{|S ∖ J|}`. -/
private lemma prod_C_mul_X_ite (S J : Finset ℕ) (f : ℕ → ℝ) :
    ∏ a ∈ S, (C (f a) * X (if a ∈ J then 0 else 1) : MvPolynomial (Fin 2) ℝ) =
      C (∏ a ∈ S, f a) * (X 0 ^ (S ∩ J).card * X 1 ^ (S \ J).card) := by
  rw [Finset.prod_mul_distrib, ← map_prod, Finset.prod_apply_ite, Finset.prod_const,
    Finset.prod_const, Finset.filter_mem_eq_inter, Finset.filter_notMem_eq_sdiff]

/-- One term of the homogenization identity: for `A_d ⊆ D`, `A_a ⊆ T` and `J_d, J_a`
disjoint from `A_d, A_a`, the degree-`(|D ∖ A_d| + |T ∖ A_a|)` homogenization of
`wt · x^{|D ∩ J_d| + |T ∩ J_a|}` is the image of `∏_{D ∖ A_d} x_a ∏_{T ∖ A_a} y_b` under
`xySubst`, scaled by `∏_{A_d} α ∏_{A_a} β`. -/
private lemma homogenize_term {D T A_d A_a J_d J_a : Finset ℕ} (α β : ℕ → ℝ)
    (hAd : A_d ⊆ D) (hAa : A_a ⊆ T) (hJd : Disjoint J_d A_d) (hJa : Disjoint J_a A_a) :
    (Polynomial.C ((∏ a ∈ D, α a) * ∏ b ∈ T, β b) *
        Polynomial.X ^ ((D ∩ J_d).card + (T ∩ J_a).card)).homogenize
        ((D \ A_d).card + (T \ A_a).card) =
      C ((∏ a ∈ A_d, α a) * ∏ b ∈ A_a, β b) * aeval (xySubst J_d J_a α β)
        ((∏ a ∈ D \ A_d, (X (true, a) : MvPolynomial (Bool × ℕ) ℝ)) *
          ∏ b ∈ T \ A_a, X (false, b)) := by
  have hd := sdiff_inter_eq_inter D hJd
  have ha := sdiff_inter_eq_inter T hJa
  have h1 := Finset.card_inter_add_card_sdiff (D \ A_d) J_d
  have h2 := Finset.card_inter_add_card_sdiff (T \ A_a) J_a
  rw [hd] at h1
  rw [ha] at h2
  rw [Polynomial.homogenize_C_mul, Polynomial.homogenize_X_pow (by omega),
    map_mul (aeval (R := ℝ) _), map_prod (aeval (R := ℝ) _), map_prod (aeval (R := ℝ) _)]
  simp only [aeval_X, xySubst, prod_C_mul_X_ite, hd, ha]
  rw [← Finset.prod_sdiff hAd, ← Finset.prod_sdiff hAa,
    show (D \ A_d).card + (T \ A_a).card - ((D ∩ J_d).card + (T ∩ J_a).card) =
      ((D \ A_d) \ J_d).card + ((T \ A_a) \ J_a).card by omega]
  simp only [map_mul, pow_add]
  ring

/-- The words of the conditional fiber `Ω`. -/
private abbrev condFiber (π : List ℕ) (A_d B_d A_a B_a : Finset ℕ) : Finset (List ℕ) :=
  (List.stackFiber π).filter fun σ ↦ A_d ⊆ σ.descentTops ∧
    _root_.Disjoint σ.descentTops B_d ∧ A_a ⊆ σ.ascentTops ∧ _root_.Disjoint σ.ascentTops B_a

/-- On `Ω`, `|DT(σ) ∖ A_d| + |AT(σ) ∖ A_a| = n - 1 - |A_d| - |A_a|`. -/
private lemma card_sdiff_add_card_sdiff {n : ℕ} {π σ : List ℕ} (hπ : π ∈ permWords n)
    {A_d B_d A_a B_a : Finset ℕ} (hσ : σ ∈ condFiber π A_d B_d A_a B_a) :
    (σ.descentTops \ A_d).card + (σ.ascentTops \ A_a).card = n - 1 - A_d.card - A_a.card := by
  obtain ⟨hσ, hAd, -, hAa, -⟩ := Finset.mem_filter.1 hσ
  have hσn := mem_permWords_of_mem_stackFiber hπ hσ
  have := card_descentTops_add_card_ascentTops hσn.1.1
  have := Finset.card_le_card hAd
  have := Finset.card_le_card hAa
  rw [Finset.card_sdiff_of_subset hAd, Finset.card_sdiff_of_subset hAa, hσn.2.1] at *
  omega

/-- **The homogenization identity.** The degree-`(n - 1 - |A_d| - |A_a|)` homogenization of the
conditional top polynomial is `(∏_{A_d} α ∏_{A_a} β) · G(xySubst)`, where
`G = ∑_{σ ∈ Ω} ∏_{DT(σ) ∖ A_d} x_a ∏_{AT(σ) ∖ A_a} y_b`. -/
private lemma homogenize_conditionalTopPolynomial {n : ℕ} {π : List ℕ} (hπ : π ∈ permWords n)
    {A_d B_d A_a B_a J_d J_a : Finset ℕ} (hJd : Disjoint J_d A_d) (hJa : Disjoint J_a A_a)
    (α β : ℕ → ℝ) :
    (List.conditionalTopPolynomial ℝ π A_d B_d A_a B_a J_d J_a α β).homogenize
        (n - 1 - A_d.card - A_a.card) =
      ((∏ a ∈ A_d, α a) * ∏ b ∈ A_a, β b) • aeval (xySubst J_d J_a α β)
        (∑ σ ∈ condFiber π A_d B_d A_a B_a,
          (∏ a ∈ σ.descentTops \ A_d, (X (true, a) : MvPolynomial (Bool × ℕ) ℝ)) *
            ∏ b ∈ σ.ascentTops \ A_a, X (false, b)) := by
  rw [List.conditionalTopPolynomial, Polynomial.homogenize_finsetSum, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun σ hσ ↦ ?_
  obtain ⟨-, hAd, -, hAa, -⟩ := Finset.mem_filter.1 hσ
  rw [← card_sdiff_add_card_sdiff hπ hσ, homogenize_term α β hAd hAa hJd hJa, smul_eq_C_mul]


namespace List

/-- **Corollary 3.6.** For `n ≥ 1`, `π ∈ S_n`, finite sets `A_d, B_d, A_a, B_a` such that some
`σ ∈ s⁻¹(π)` has `A_d ⊆ DT(σ) ⊆ [n] ∖ B_d` and `A_a ⊆ AT(σ) ⊆ [n] ∖ B_a`, weights `α, β`
positive on `[n]`, and `J_d ⊆ [n] ∖ (A_d ∪ B_d)`, `J_a ⊆ [n] ∖ (A_a ∪ B_a)`, the conditional top
polynomial is ultra-log-concave of order `n - 1 - |A_d| - |A_a|`. This is stated given the
Brändén–Huh theorems on M-convex supports, nonnegative derivatives and nonnegative linear
substitutions. -/
@[lognarayana "thm_conditional_ulc"]
public theorem isUltraLogConcave_conditionalTopPolynomial {n : ℕ} (hn : 1 ≤ n) {π : List ℕ}
    (hπ : π ∈ permWords n) (A_d B_d A_a B_a J_d J_a : Finset ℕ)
    (hΩ : ∃ σ ∈ stackFiber π, A_d ⊆ σ.descentTops ∧ σ.descentTops ⊆ Finset.Icc 1 n \ B_d ∧
      A_a ⊆ σ.ascentTops ∧ σ.ascentTops ⊆ Finset.Icc 1 n \ B_a)
    (α β : ℕ → ℝ) (hα : ∀ a ∈ Finset.Icc 1 n, 0 < α a) (hβ : ∀ b ∈ Finset.Icc 1 n, 0 < β b)
    (hJd : J_d ⊆ Finset.Icc 1 n \ (A_d ∪ B_d)) (hJa : J_a ⊆ Finset.Icc 1 n \ (A_a ∪ B_a))
    (hBH : NormalizedSupportPolyLorentzianOfMConvex
      ↥(Finset.univ ×ˢ Finset.Icc 1 n : Finset (Bool × ℕ)))
    (hder : LorentzianNonnegDerivative ↥(Finset.univ ×ˢ Finset.Icc 1 n : Finset (Bool × ℕ)))
    (hsub : LorentzianNonnegLinearSubstitution
      ↥(Finset.univ ×ˢ Finset.Icc 1 n : Finset (Bool × ℕ))
      ↥(Finset.univ ×ˢ Finset.Icc 1 n : Finset (Bool × ℕ)))
    (hsub₂ : LorentzianNonnegLinearSubstitution
      ↥(Finset.univ ×ˢ Finset.Icc 1 n : Finset (Bool × ℕ)) (Fin 2)) :
    (conditionalTopPolynomial ℝ π A_d B_d A_a B_a J_d J_a α β).IsUltraLogConcave
      (n - 1 - A_d.card - A_a.card) := by
  have hJd' : _root_.Disjoint J_d A_d := Finset.disjoint_of_subset_left hJd
    (Finset.sdiff_disjoint.mono_right Finset.subset_union_left)
  have hJa' : _root_.Disjoint J_a A_a := Finset.disjoint_of_subset_left hJa
    (Finset.sdiff_disjoint.mono_right Finset.subset_union_left)
  have hwt {σ} (hσ : σ ∈ condFiber π A_d B_d A_a B_a) :
      0 ≤ (∏ a ∈ σ.descentTops, α a) * ∏ b ∈ σ.ascentTops, β b := by
    obtain ⟨hD, hA⟩ := tops_subset_Icc (mem_permWords_of_mem_stackFiber hπ
      (Finset.mem_filter.1 hσ).1)
    exact mul_nonneg (Finset.prod_nonneg fun a ha ↦ (hα a (hD ha)).le)
      (Finset.prod_nonneg fun b hb ↦ (hβ b (hA hb)).le)
  have hcoeff (i : ℕ) : 0 ≤ (conditionalTopPolynomial ℝ π A_d B_d A_a B_a J_d J_a α β).coeff i := by
    rw [conditionalTopPolynomial, Polynomial.finsetSum_coeff]
    refine Finset.sum_nonneg fun σ hσ ↦ ?_
    rw [Polynomial.coeff_C_mul_X_pow]
    split_ifs
    exacts [hwt hσ, le_rfl]
  have hdeg : (conditionalTopPolynomial ℝ π A_d B_d A_a B_a J_d J_a α β).natDegree ≤
      n - 1 - A_d.card - A_a.card :=
    Polynomial.natDegree_sum_le_of_forall_le _ _ fun σ hσ ↦
      (Polynomial.natDegree_C_mul_X_pow_le _ _).trans <| by
        rw [← card_sdiff_add_card_sdiff hπ hσ, ← sdiff_inter_eq_inter _ hJd',
          ← sdiff_inter_eq_inter _ hJa']
        gcongr <;> exact Finset.inter_subset_left
  obtain ⟨σ₀, -, hA₀d, hD₀, hA₀a, hA₀⟩ := hΩ
  obtain ⟨p, hp, hpL⟩ :=
    isLorentzian_conditionalTopPolynomial hn hπ A_d B_d A_a B_a hBH hder hsub
  rw [← Polynomial.isLorentzian_homogenize_iff_isUltraLogConcave hcoeff hdeg,
    homogenize_conditionalTopPolynomial hπ hJd' hJa', ← hp, aeval_rename]
  refine IsLorentzian.smul ?_ (mul_nonneg
    (Finset.prod_nonneg fun a ha ↦ (hα a (Finset.mem_sdiff.1 (hD₀ (hA₀d ha))).1).le)
    (Finset.prod_nonneg fun b hb ↦ (hβ b (Finset.mem_sdiff.1 (hA₀ (hA₀a hb))).1).le))
  have hw (e : ↥(Finset.univ ×ˢ Finset.Icc 1 n : Finset (Bool × ℕ))) :
      0 ≤ if e.1.1 then α e.1.2 else β e.1.2 := by
    have ha := (Finset.mem_product.1 e.2).2
    split_ifs
    exacts [(hα _ ha).le, (hβ _ ha).le]
  have h := isLorentzian_aeval_C_mul_X hsub₂ hw
    (fun e ↦ if (e.1.1 ∧ e.1.2 ∈ J_d) ∨ (¬e.1.1 ∧ e.1.2 ∈ J_a) then 0 else 1) hpL
  rwa [show (fun e ↦ C _ * X _) = xySubst J_d J_a α β ∘ Subtype.val from
    funext fun ⟨⟨b, a⟩, _⟩ ↦ by cases b <;> simp [xySubst]] at h

end List

end
