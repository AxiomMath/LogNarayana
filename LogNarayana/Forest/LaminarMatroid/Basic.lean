/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import LogNarayana.Attr
public import LogNarayana.StackSorting.AdoptableForest.Defs
public import LogNarayana.StackSorting.Matchings.Defs
public import LogNarayana.StackSorting.AdoptableForest.Basic
public import LogNarayana.StackSorting.Matchings.Basic
public import LogNarayana.StackSorting.Descents.Defs
public import LogNarayana.Lorentzian.Hessian.Defs
public import LogNarayana.Matroid.Laminar.Defs
public import LogNarayana.Matroid.BasisGeneratingPolynomial.Defs
public import LogNarayana.Forest.LaminarMatroid.Defs
public import LogNarayana.Matroid.Laminar.Basic
public import LogNarayana.Lorentzian.Symbol.Basic
public import LogNarayana.Matroid.BasisGeneratingPolynomial.Basic
public import LogNarayana.Lorentzian.BrandenHuh.Basic

/-!
# The laminar matroid of a marked forest

Let `par` encode a forest on `[N] = {1, …, N}` and let `L` be a set of marked vertices. The
blocks `E_v = {x, y} × (V_v \ L)` of the subtrees `V_v` form a laminar family of subsets of the
ground set `E_{N,L} = {x, y} × ([N] \ L)`, and the forest independence family
`𝕀_{par,L} = {I ⊆ E_{N,L} : |I ∩ E_v| ≤ |V_v|}` is the family of independent sets of a laminar
matroid. Every member of `𝕀_{par,L}` has at most `N` elements.

For a postorder forest, the members of `𝕀_{par,L}` are in bijection with the triples
`(M, O, S)` of an open pair `(M, O)` and a choice `S ⊆ U(M) \ O`, through the choice set
`I(M, O, S)`; the inverse is the stack reconstruction, which reads `I` vertex by vertex and
pushes, skips or pops according to `c_v = |I ∩ {v⁺, v⁻}|`. Since `|I(M, O, S)| + |O| = N`, the
triples with `O = ∅` are exactly the members of size `N`, and expanding the forest matching
polynomial gives `Z_{par,L} = ∑_{I ∈ 𝕀_{par,L}, |I| = N} z^I`. Consequently, when
`Z_{par,L} ≠ 0`, the matroid has rank `N`, `Z_{par,L}` is its basis generating polynomial, its
coefficients are `0` or `1`, and it is Lorentzian.

## Main results

* `isLaminar_forestBlock`, `exists_matroid_indep_iff_mem_forestIndepFamily`,
  `Matroid.isLaminar_of_indep_iff_mem_forestIndepFamily`: the forest matroid exists and is
  laminar; `card_le_of_mem_forestIndepFamily`: its independent sets have at most `N` elements.
* `isHomogeneous_forestMatchingPoly`: `Z_{par,L}` is homogeneous of degree `N`.
* `Finset.card_openChoiceSet_add_card`, `Finset.card_openChoiceSet_inter_forestBlock_add`,
  `Finset.openChoiceSet_mem_forestIndepFamily`: size, deficit identity and independence of
  choice sets.
* `openChoiceSet_stackReconstruction`, `stackReconstruction_openChoiceSet`,
  `isOpenPair_stackReconstruction`, `Finset.bijOn_openChoiceSet_forestIndepFamily`: the
  choice-set bijection and its inverse, the stack reconstruction.
* `forestMatchingPoly_eq_sum_card_eq_prod_X`: `Z_{par,L} = ∑_{I ∈ 𝕀_{par,L}, |I| = N} z^I`.
* `Matroid.encard_eq_of_isBase_of_indep_iff_mem_forestIndepFamily`,
  `forestMatchingPoly_eq_sum_isBase_prod_X`, `coeff_forestMatchingPoly_eq_zero_or_eq_one`,
  `isLorentzian_forestMatchingPoly`: rank `N`, the basis identity, `0/1` coefficients and
  Lorentzianity.

## Implementation notes

Vertices are natural numbers, `[N] = Finset.Icc 1 N`, and `v⁺ = (true, v)`, `v⁻ = (false, v)`.
A matroid "on `E_{N,L}` with `𝕀(M) = 𝕀_{par,L}`" is a `Matroid (Bool × ℕ)` with
`M.E = ↑(forestGroundSet N L)` whose independent sets are the coercions of the members of
`forestIndepFamily N par L`. Results not needing a parent map or `L ⊆ [N]` are stated for every
`par : ℕ → Option ℕ` and finite `L`; polynomial identities hold over any commutative semiring.
`isLorentzian_forestMatchingPoly` exhibits `Z_{par,L}` as the renaming, along
`Bool × [N] ↪ Bool × ℕ`, of a Lorentzian polynomial in finitely many variables, and takes the
cited results of Brändén–Huh as hypotheses.

## References

* [LogNarayana], Sections 3 and 4, Example 3.5, Theorem 3.4.
* [BH] P. Brändén, J. Huh, *Lorentzian polynomials*, Ann. of Math. 192 (2020).
-/

open Finset

/-! ### Laminarity and the forest matroid -/

/-- A block is monotone in the subtree: `V_u ⊆ V_v` gives `E_u ⊆ E_v`. -/
private lemma forestBlock_subset_of_subset {N : ℕ} {par : ℕ → Option ℕ} {L : Finset ℕ}
    {u v : ℕ} (h : subtreeVertices N par u ⊆ subtreeVertices N par v) :
    (forestBlock N par L u : Set (Bool × ℕ)) ⊆ forestBlock N par L v :=
  coe_subset.2 <| product_subset_product le_rfl (sdiff_subset_sdiff h le_rfl)

/-- The ground set `E_{N,L}` consists of both copies of the unmarked vertices of `[N]`. -/
private lemma mem_forestGroundSet_iff {N : ℕ} {L : Finset ℕ} {x : Bool × ℕ} :
    x ∈ forestGroundSet N L ↔ x.2 ∈ Icc 1 N \ L := by
  simp [forestGroundSet]

/-- The block `E_v` consists of both copies of the unmarked vertices of `V_v`. -/
private lemma mem_forestBlock_iff {N : ℕ} {par : ℕ → Option ℕ} {L : Finset ℕ} {v : ℕ}
    {x : Bool × ℕ} : x ∈ forestBlock N par L v ↔ x.2 ∈ subtreeVertices N par v \ L := by
  simp [forestBlock]

/-- For any `par` and `L`, the blocks `E_v = forestBlock N par L v`, `v ∈ [N]`, are subsets of
the ground set `E_{N,L} = forestGroundSet N L` and form a laminar family. -/
@[lognarayana "lem_forest_blocks_laminar"]
public theorem isLaminar_forestBlock (N : ℕ) (par : ℕ → Option ℕ) (L : Finset ℕ) :
    (∀ v ∈ Finset.Icc 1 N, forestBlock N par L v ⊆ forestGroundSet N L) ∧
      IsLaminar (fun v : Finset.Icc 1 N => (forestBlock N par L v : Set (Bool × ℕ))) := by
  refine ⟨fun v _ => product_subset_product le_rfl
    (sdiff_subset_sdiff (by classical exact filter_subset _ _) le_rfl),
    fun u v ⟨x, hxu, hxv⟩ => ?_⟩
  rw [mem_coe, mem_forestBlock_iff, mem_sdiff] at hxu hxv
  exact (subtreeVertices_subset_or_subset_of_inter_nonempty
    ⟨x.2, mem_inter.2 ⟨hxu.1, hxv.1⟩⟩).imp
    forestBlock_subset_of_subset forestBlock_subset_of_subset

/-- In a finite family `S` of finsets any two of which are nested or disjoint, the `⊆`-maximal
members are pairwise disjoint and every member of `S` is contained in one of them. -/
private lemma exists_pairwiseDisjoint_cover_of_nested {α : Type*} [DecidableEq α]
    (S : Finset (Finset α))
    (hS : ∀ A ∈ S, ∀ B ∈ S, (A ∩ B).Nonempty → A ⊆ B ∨ B ⊆ A) :
    ∃ M ⊆ S, (M : Set (Finset α)).PairwiseDisjoint id ∧ ∀ A ∈ S, ∃ B ∈ M, A ⊆ B := by
  classical
  refine ⟨S.filter fun A => ∀ B ∈ S, A ⊆ B → B ⊆ A, filter_subset _ _, ?_, fun A hA => ?_⟩
  · intro A hA B hB hAB
    simp only [coe_filter, Set.mem_ofPred_eq] at hA hB
    refine disjoint_iff_inter_eq_empty.2 (not_nonempty_iff_eq_empty.1 fun hne => ?_)
    rcases hS A hA.1 B hB.1 hne with h | h
    · exact hAB (h.antisymm (hA.2 B hB.1 h))
    · exact hAB ((hB.2 A hA.1 h).antisymm h)
  · obtain ⟨B, hAB, hB⟩ := S.finite_toSet.exists_le_maximal (a := A) hA
    exact ⟨B, mem_filter.2 ⟨hB.1, fun C hC => hB.2 hC⟩, hAB⟩

/-- Membership in the forest independence family, unfolded. -/
private lemma mem_forestIndepFamily_iff {N : ℕ} {par : ℕ → Option ℕ} {L : Finset ℕ}
    {I : Finset (Bool × ℕ)} : I ∈ forestIndepFamily N par L ↔ I ⊆ forestGroundSet N L ∧
      ∀ v ∈ Icc 1 N, #(I ∩ forestBlock N par L v) ≤ #(subtreeVertices N par v) := by
  simp only [forestIndepFamily, mem_filter, mem_powerset]

/-- An element of a subset of `E_{N,L}` whose vertex lies in `V_v` lies in the block `E_v`. -/
private lemma mem_inter_forestBlock {N : ℕ} {par : ℕ → Option ℕ} {L : Finset ℕ}
    {I : Finset (Bool × ℕ)} (hI : I ⊆ forestGroundSet N L) {v : ℕ} {x : Bool × ℕ}
    (hx : x ∈ I) (hxv : x.2 ∈ subtreeVertices N par v) : x ∈ I ∩ forestBlock N par L v :=
  mem_inter.2 ⟨hx, mem_forestBlock_iff.2 <|
    mem_sdiff.2 ⟨hxv, (mem_sdiff.1 (mem_forestGroundSet_iff.1 (hI hx))).2⟩⟩

/-- Every member of the forest independence family `𝕀_{par,L}` on `[N]` has at most `N`
elements: the `⊆`-maximal subtrees partition `[N]`, and the capacity bounds of their blocks sum
to `N`. -/
@[lognarayana "lem_forest_indep_card_le"]
public theorem card_le_of_mem_forestIndepFamily (N : ℕ) (par : ℕ → Option ℕ) (L : Finset ℕ)
    {I : Finset (Bool × ℕ)} (hI : I ∈ forestIndepFamily N par L) : I.card ≤ N := by
  classical
  obtain ⟨hIE, hcap⟩ := mem_forestIndepFamily_iff.1 hI
  obtain ⟨M, hMS, hdisj, hcover⟩ := exists_pairwiseDisjoint_cover_of_nested
    ((Icc 1 N).image (subtreeVertices N par)) (by
      simp only [mem_image]
      rintro _ ⟨u, -, rfl⟩ _ ⟨v, -, rfl⟩
      exact subtreeVertices_subset_or_subset_of_inter_nonempty)
  have hM : ∀ A ∈ M, ∃ v ∈ Icc 1 N, subtreeVertices N par v = A := fun A hA =>
    mem_image.1 (hMS hA)
  calc #I ≤ #(M.biUnion fun A => I.filter (·.2 ∈ A)) := by
        refine card_le_card fun x hx => ?_
        have hx2 : x.2 ∈ Icc 1 N := (mem_sdiff.1 (mem_forestGroundSet_iff.1 (hIE hx))).1
        obtain ⟨A, hA, hxA⟩ := hcover _ (mem_image_of_mem _ hx2)
        exact mem_biUnion.2 ⟨A, hA, mem_filter.2 ⟨hx, hxA (mem_filter.2 ⟨hx2, 0, rfl⟩)⟩⟩
    _ ≤ ∑ A ∈ M, #(I.filter (·.2 ∈ A)) := card_biUnion_le
    _ ≤ ∑ A ∈ M, #A := sum_le_sum fun A hA => by
        obtain ⟨v, hv, rfl⟩ := hM A hA
        refine (card_le_card fun x hx => ?_).trans (hcap v hv)
        exact mem_inter_forestBlock hIE (mem_filter.1 hx).1 (mem_filter.1 hx).2
    _ = #(M.biUnion id) := (card_biUnion hdisj).symm
    _ ≤ #(Icc 1 N) := card_le_card <| biUnion_subset.2 fun A hA => by
        obtain ⟨v, -, rfl⟩ := hM A hA
        exact filter_subset _ _
    _ = N := by simp

/-- A finite set lies in `forestIndepFamily` exactly when it is capacity-bounded for the forest
blocks, indexed by `Icc 1 N`, with the subtree sizes as capacities. -/
private lemma mem_forestIndepFamily_iff_coe_mem (N : ℕ) (par : ℕ → Option ℕ) (L : Finset ℕ)
    (J : Finset (Bool × ℕ)) :
    J ∈ forestIndepFamily N par L ↔ (J : Set (Bool × ℕ)) ∈ capacityBoundedSets
      ↑(forestGroundSet N L) (fun v : Finset.Icc 1 N => (forestBlock N par L v : Set _))
      (fun v => (subtreeVertices N par v).card) := by
  rw [mem_forestIndepFamily_iff]
  simp only [capacityBoundedSets, Set.mem_ofPred_eq, coe_subset, ← coe_inter,
    Set.encard_coe_eq_coe_finsetCard, Nat.cast_le, Subtype.forall]

/-- A set is independent in the laminar matroid of the forest blocks iff it is the coercion of a
member of `forestIndepFamily`. -/
private lemma mem_capacityBoundedSets_iff (N : ℕ) (par : ℕ → Option ℕ) (L : Finset ℕ)
    (I : Set (Bool × ℕ)) :
    I ∈ capacityBoundedSets ↑(forestGroundSet N L)
        (fun v : Finset.Icc 1 N => (forestBlock N par L v : Set _))
        (fun v => (subtreeVertices N par v).card) ↔
      ∃ J ∈ forestIndepFamily N par L, (J : Set (Bool × ℕ)) = I := by
  refine ⟨fun h => ?_, ?_⟩
  · have hfin := (forestGroundSet N L).finite_toSet.subset h.1
    exact ⟨hfin.toFinset, (mem_forestIndepFamily_iff_coe_mem N par L _).2 (by simpa), by simp⟩
  · rintro ⟨J, hJ, rfl⟩
    exact (mem_forestIndepFamily_iff_coe_mem N par L J).1 hJ

/-- **The forest family is a matroid.** For a forest on `[N]` encoded by `par` and marked
vertices `L`, there is a matroid on the ground set `E_{N,L} = forestGroundSet N L` whose
independent sets are exactly the members of the forest independence family
`𝕀_{par,L} = forestIndepFamily N par L`. -/
@[lognarayana "lem_forest_matroid_exists"]
public theorem exists_matroid_indep_iff_mem_forestIndepFamily (N : ℕ) (par : ℕ → Option ℕ)
    (L : Finset ℕ) :
    ∃ M : Matroid (Bool × ℕ), M.E = ↑(forestGroundSet N L) ∧
      ∀ I : Set (Bool × ℕ), M.Indep I ↔
        ∃ J ∈ forestIndepFamily N par L, (J : Set (Bool × ℕ)) = I := by
  obtain ⟨M, hME, hM⟩ := (isLaminar_forestBlock N par L).2.exists_matroid_indep_iff
    (forestGroundSet N L).finite_toSet (fun v => #(subtreeVertices N par v))
  exact ⟨M, hME, fun I => (hM I).trans (mem_capacityBoundedSets_iff N par L I)⟩

/-- **The forest matroid is laminar.** A matroid on `E_{N,L} = forestGroundSet N L` whose
independent sets are exactly the members of `forestIndepFamily N par L` is a laminar matroid. -/
@[lognarayana "lem_forest_matroid_laminar"]
public theorem Matroid.isLaminar_of_indep_iff_mem_forestIndepFamily (N : ℕ)
    (par : ℕ → Option ℕ) (L : Finset ℕ) (M : Matroid (Bool × ℕ))
    (hE : M.E = ↑(forestGroundSet N L))
    (hI : ∀ I : Set (Bool × ℕ),
      M.Indep I ↔ ∃ J ∈ forestIndepFamily N par L, (J : Set (Bool × ℕ)) = I) :
    M.IsLaminar :=
  ⟨Finset.Icc 1 N, inferInstance, _, fun v => (subtreeVertices N par v).card,
    (isLaminar_forestBlock N par L).2, fun I => by
      rw [hI, hE, mem_capacityBoundedSets_iff]⟩

/-- The six-element set `{2⁺, 2⁻, 3^ε, 5⁺, 5⁻, 6^δ}` lies in the forest independence family of
the adoptable forest of `2135467` with marked vertices its descent set `{1, 4}`. -/
private lemma mem_forestIndepFamily_2135467 (ε δ : Bool) :
    ({(true, 2), (false, 2), (ε, 3), (true, 5), (false, 5), (δ, 6)} : Finset (Bool × ℕ)) ∈
      forestIndepFamily 6 ([2, 1, 3, 5, 4, 6, 7] : List ℕ).adoptableForest
        ([2, 1, 3, 5, 4, 6, 7] : List ℕ).descentSet := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := List.adoptableInterval_2135467
  rw [mem_forestIndepFamily_iff]
  simp only [forestBlock, List.descentSet_2135467]
  refine ⟨by unfold forestGroundSet; cases ε <;> cases δ <;> decide, fun v hv => ?_⟩
  obtain ⟨hv1, hv2⟩ := mem_Icc.mp hv
  rw [show subtreeVertices 6 _ v = _ from
    List.subtreeVertices_adoptableForest [2, 1, 3, 5, 4, 6, 7] hv1 hv2]
  interval_cases v <;> simp only [h1, h2, h3, h4, h5, h6] <;> cases ε <;> cases δ <;> decide

/-- For `π = 2135467` and any matroid `M` on `Bool × ℕ` with independent sets `𝕀_{𝓕_π, Des(π)}`, the
set `{2⁺, 2⁻, 3^ε, 5⁺, 5⁻, 6^δ}` is a base of `M` for all signs `ε, δ`: it is independent of size
`6`, the largest size of an independent set. -/
@[lognarayana "lem_ex_matching_bases"]
public theorem Matroid.isBase_two_three_five_six_of_indep_iff_mem_forestIndepFamily_2135467
    (M : Matroid (Bool × ℕ))
    (hI : ∀ I, M.Indep I ↔ ∃ J ∈ forestIndepFamily 6
      ([2, 1, 3, 5, 4, 6, 7] : List ℕ).adoptableForest ([2, 1, 3, 5, 4, 6, 7] : List ℕ).descentSet,
      ↑J = I)
    (ε δ : Bool) :
    M.IsBase {(true, 2), (false, 2), (ε, 3), (true, 5), (false, 5), (δ, 6)} := by
  set B : Finset (Bool × ℕ) := {(true, 2), (false, 2), (ε, 3), (true, 5), (false, 5), (δ, 6)}
  rw [show ({(true, 2), (false, 2), (ε, 3), (true, 5), (false, 5), (δ, 6)} : Set (Bool × ℕ)) = B
    by simp [B], Matroid.isBase_iff_maximal_indep]
  refine ⟨(hI _).2 ⟨B, mem_forestIndepFamily_2135467 ε δ, rfl⟩, fun J hJ hBJ => ?_⟩
  obtain ⟨J', hJ', rfl⟩ := (hI J).1 hJ
  refine (eq_of_subset_of_card_le (coe_subset.mp hBJ) ?_).symm.le
  exact (card_le_of_mem_forestIndepFamily _ _ _ hJ').trans
    (by simp only [B]; cases ε <;> cases δ <;> decide)

/-! ### Homogeneity and choice sets -/

/-- In a noncrossing partial matching a pair is determined by its left endpoint. -/
private lemma injOn_fst {N : ℕ} {M : Finset (ℕ × ℕ)} (hM : IsNoncrossingPartialMatching N M) :
    Set.InjOn Prod.fst (M : Set (ℕ × ℕ)) :=
  fun p hp q hq h => hM.eq_of_mem_of_mem p hp q hq p.1 (.inl rfl) (.inl h)

/-- In a noncrossing partial matching a pair is determined by its right endpoint. -/
private lemma injOn_snd {N : ℕ} {M : Finset (ℕ × ℕ)} (hM : IsNoncrossingPartialMatching N M) :
    Set.InjOn Prod.snd (M : Set (ℕ × ℕ)) :=
  fun p hp q hq h => hM.eq_of_mem_of_mem p hp q hq p.2 (.inr rfl) (.inr h)

/-- For a noncrossing partial matching, `|R(M)| = |M|`. -/
private lemma card_image_snd {N : ℕ} {M : Finset (ℕ × ℕ)}
    (hM : IsNoncrossingPartialMatching N M) : (M.image Prod.snd).card = M.card :=
  card_image_of_injOn (injOn_snd hM)

open MvPolynomial in
/-- The summand of `forestMatchingPoly` indexed by a noncrossing partial matching `M` on `[N]`
is homogeneous of degree `2|R(M)| + |U(M)| = 2|M| + |U(M)| = N`. -/
private lemma isHomogeneous_matchingTerm (R : Type*) [CommSemiring R] {N : ℕ}
    {M : Finset (ℕ × ℕ)} (hM : IsNoncrossingPartialMatching N M) :
    ((∏ v ∈ M.image Prod.snd, X (true, v) * X (false, v)) *
      ∏ v ∈ Finset.unmatchedVertices N M, (X (true, v) + X (false, v)) :
        MvPolynomial (Bool × ℕ) R).IsHomogeneous N := by
  convert (IsHomogeneous.prod _ (fun v => X (true, v) * X (false, v)) (fun _ => 2) fun _ _ =>
      (isHomogeneous_X R _).mul (isHomogeneous_X R _)).mul
    (IsHomogeneous.prod _ (fun v => X (true, v) + X (false, v)) (fun _ => 1) fun _ _ =>
      (isHomogeneous_X R _).add (isHomogeneous_X R _)) using 1
  simp only [sum_const, smul_eq_mul, mul_one, card_image_snd hM]
  linarith [hM.card_unmatchedVertices_add_two_mul_card]

/-- The forest matching polynomial `Z_{par,L}(x, y)` on `[N]` is homogeneous of degree `N`. -/
@[lognarayana "lem_forest_z_homogeneous"]
public theorem isHomogeneous_forestMatchingPoly (R : Type*) [CommSemiring R] (N : ℕ)
    (par : ℕ → Option ℕ) (L : Finset ℕ) :
    (forestMatchingPoly R N par L).IsHomogeneous N := by
  classical
  exact MvPolynomial.IsHomogeneous.sum _ _ _ fun M hM =>
    isHomogeneous_matchingTerm R (mem_filter.mp hM).2.isNoncrossingPartialMatching

/-- `(M, ∅)` is an open pair for `(par, L)` on `[N]` if and only if `M` is an admissible matching
for `(par, L)` on `[N]`. -/
@[lognarayana "lem_open_pair_empty_iff_admissible"]
public theorem isOpenPair_empty_iff_isAdmissibleMatching {N : ℕ} {par : ℕ → Option ℕ}
    {L : Finset ℕ} {M : Finset (ℕ × ℕ)} :
    IsOpenPair N par L M ∅ ↔ IsAdmissibleMatching N par L M :=
  ⟨fun h => ⟨h.isNoncrossingPartialMatching, h.isStrictAncestor,
      by simpa using h.subset_leftEndpoints_union⟩,
    fun h => ⟨h.isNoncrossingPartialMatching, h.isStrictAncestor, empty_subset _,
      by simp, by simpa using h.subset_leftEndpoints⟩⟩

/-- A vertex is unmatched iff it lies in `[N]` and is neither a left nor a right endpoint. -/
private lemma mem_unmatchedVertices_iff {N : ℕ} {M : Finset (ℕ × ℕ)} {u : ℕ} :
    u ∈ unmatchedVertices N M ↔
      u ∈ Icc 1 N ∧ u ∉ M.image Prod.fst ∧ u ∉ M.image Prod.snd := by
  simp [unmatchedVertices, not_or]

/-- `mem_unmatchedVertices_iff`, with the endpoint conditions stated pair by pair. -/
private lemma mem_unmatchedVertices_iff_forall {N : ℕ} {M : Finset (ℕ × ℕ)} {v : ℕ} :
    v ∈ unmatchedVertices N M ↔
      (1 ≤ v ∧ v ≤ N) ∧ (∀ b, (v, b) ∉ M) ∧ ∀ a, (a, v) ∉ M := by
  simp [mem_unmatchedVertices_iff]

/-- The right endpoints `R(M)` and the unmatched vertices `U(M)` are disjoint. -/
private lemma disjoint_image_snd_unmatchedVertices (N : ℕ) (M : Finset (ℕ × ℕ)) :
    Disjoint (M.image Prod.snd) (unmatchedVertices N M) :=
  disjoint_left.2 fun _ hx hx' => (mem_unmatchedVertices_iff.1 hx').2.2 hx

/-- The size of a choice set, for any finite set of pairs `M`:
`|I(M, O, S)| + |O| = 2|R(M)| + |U(M)|`. -/
private lemma card_openChoiceSet_add_card_eq {N : ℕ} {M : Finset (ℕ × ℕ)} {O S : Finset ℕ}
    (hO : O ⊆ unmatchedVertices N M) (hS : S ⊆ unmatchedVertices N M \ O) :
    #(openChoiceSet N M O S) + #O = 2 * #(M.image Prod.snd) + #(unmatchedVertices N M) := by
  classical
  have hRU := disjoint_image_snd_unmatchedVertices N M
  have hOS : Disjoint O S := disjoint_left.2 fun x hx hx' => (mem_sdiff.1 (hS hx')).2 hx
  have hOSU : O ∪ S ⊆ unmatchedVertices N M := union_subset hO (hS.trans sdiff_subset)
  rw [openChoiceSet,
    card_union_of_disjoint (disjoint_union_left.2
      ⟨disjoint_product.2 (.inr (hRU.mono_right sdiff_subset)),
        disjoint_product.2 (.inl (by simp))⟩),
    card_union_of_disjoint
      (disjoint_product.2 (.inr (hRU.mono_right (hS.trans sdiff_subset)))),
    card_product, card_product, card_product, card_sdiff_of_subset hOSU,
    card_union_of_disjoint hOS]
  have := card_le_card hOSU
  rw [card_union_of_disjoint hOS] at this
  simp only [card_univ, Fintype.card_bool, card_singleton]
  omega

/-- For a noncrossing partial matching `M` on `[N]`, `O ⊆ U(M)` and `S ⊆ U(M) \ O`, the choice
set satisfies `|I(M, O, S)| + |O| = N`. -/
@[lognarayana "lem_open_choice_card"]
public theorem Finset.card_openChoiceSet_add_card {N : ℕ} {M : Finset (ℕ × ℕ)} {O S : Finset ℕ}
    (hM : IsNoncrossingPartialMatching N M) (hO : O ⊆ Finset.unmatchedVertices N M)
    (hS : S ⊆ Finset.unmatchedVertices N M \ O) :
    (Finset.openChoiceSet N M O S).card + O.card = N := by
  rw [card_openChoiceSet_add_card_eq hO hS, card_image_snd hM]
  have := hM.card_unmatchedVertices_add_two_mul_card; omega

section Deficit

variable {N : ℕ} {M : Finset (ℕ × ℕ)} {O S L V : Finset ℕ}

private lemma disjoint_image_fst_snd (hM : IsNoncrossingPartialMatching N M) :
    Disjoint (M.image Prod.fst) (M.image Prod.snd) := by
  simp only [disjoint_left, mem_image, not_exists, not_and]
  rintro _ ⟨p, hp, rfl⟩ q hq hqp
  obtain rfl := hM.eq_of_mem_of_mem p hp q hq p.1 (Or.inl rfl) (Or.inr hqp.symm)
  exact (hM.fst_lt_snd p hp).ne' hqp

/-- A finset of `[N]` splits into its left endpoints, right endpoints and unmatched vertices. -/
private lemma card_eq_card_inter_add (hM : IsNoncrossingPartialMatching N M)
    (hV : V ⊆ Icc 1 N) :
    #V = #(M.image Prod.fst ∩ V) + #(M.image Prod.snd ∩ V) + #(M.unmatchedVertices N ∩ V) := by
  have hU : M.unmatchedVertices N ∩ V = V \ (M.image Prod.fst ∪ M.image Prod.snd) := by
    ext u
    have := @hV u
    simp only [mem_inter, mem_sdiff, mem_union, mem_unmatchedVertices_iff]
    tauto
  rw [hU, ← card_inter_add_card_sdiff V (M.image Prod.fst ∪ M.image Prod.snd),
    inter_union_distrib_left, card_union_of_disjoint
      ((disjoint_image_fst_snd hM).mono inter_subset_right inter_subset_right),
    inter_comm V, inter_comm V]

/-- Counting the points of `V` hit by an injective function on `M` through the pairs of `M`. -/
private lemma card_image_inter_of_injOn {f : ℕ × ℕ → ℕ} (hf : Set.InjOn f M) (V : Finset ℕ) :
    #(M.image f ∩ V) = #(M.filter fun p => f p ∈ V) := by
  rw [← filter_mem_eq_inter, filter_image,
    card_image_of_injOn (hf.mono (coe_subset.2 (filter_subset _ _)))]

private lemma inter_sdiff_eq_inter_of_disjoint {X : Finset ℕ} (h : Disjoint X L) :
    X ∩ (V \ L) = X ∩ V := by
  rw [← inter_sdiff_assoc, (h.mono_left inter_subset_left).sdiff_eq_left]

/-- The choice set meets `{x, y} × W` in both copies of each right endpoint in `W` and in one
copy of each vertex of `S ∩ W` and of `(U(M) \ (O ∪ S)) ∩ W`. -/
private lemma card_openChoiceSet_inter_product (hS : S ⊆ M.unmatchedVertices N)
    (W : Finset ℕ) :
    #(M.openChoiceSet N O S ∩ univ ×ˢ W) = 2 * #(M.image Prod.snd ∩ W) + #(S ∩ W) +
      #((M.unmatchedVertices N \ (O ∪ S)) ∩ W) := by
  have hSR : Disjoint S (M.image Prod.snd) :=
    disjoint_left.2 fun u hu => (mem_unmatchedVertices_iff.1 (hS hu)).2.2
  have hUR : Disjoint (M.unmatchedVertices N \ (O ∪ S)) (M.image Prod.snd) :=
    disjoint_left.2 fun u hu => (mem_unmatchedVertices_iff.1 (mem_sdiff.1 hu).1).2.2
  have hUS : Disjoint (M.unmatchedVertices N \ (O ∪ S)) S :=
    disjoint_left.2 fun u hu h => (mem_sdiff.1 hu).2 (mem_union_right _ h)
  rw [openChoiceSet, union_inter_distrib_right, union_inter_distrib_right, product_inter_product,
    product_inter_product, product_inter_product, inter_univ, inter_univ, inter_univ,
    card_union_of_disjoint, card_union_of_disjoint, card_product, card_product, card_product]
  · simp
  · exact disjoint_product.2 <| .inr <| (hSR.symm.mono inter_subset_left inter_subset_left)
  · refine disjoint_union_left.2 ⟨disjoint_product.2 <| .inr ?_, disjoint_product.2 <| .inr ?_⟩
    · exact hUR.symm.mono inter_subset_left inter_subset_left
    · exact hUS.symm.mono inter_subset_left inter_subset_left

/-- The deficit identity for a set `V ⊆ [N]` that contains the left endpoint of every pair of
`M` whose right endpoint it contains: `#(I ∩ ({x, y} × (V \ L)))` plus the number of pairs of `M`
leaving `V` plus `#(O ∩ V)` is `#V`. -/
private theorem card_openChoiceSet_inter_add (hM : IsNoncrossingPartialMatching N M)
    (hO : O ⊆ M.unmatchedVertices N) (hS : S ⊆ M.unmatchedVertices N \ O)
    (hL : L ⊆ M.leftEndpoints ∪ O) (hV : V ⊆ Icc 1 N)
    (hclosed : ∀ p ∈ M, p.2 ∈ V → p.1 ∈ V) :
    #(M.openChoiceSet N O S ∩ univ ×ˢ (V \ L)) + #{p ∈ M | p.1 ∈ V ∧ p.2 ∉ V} + #(O ∩ V) =
      #V := by
  have hLU : Disjoint (M.unmatchedVertices N \ O) L := disjoint_right.2 fun u hu h => by
    rcases mem_union.1 (hL hu) with h' | h'
    · exact (mem_unmatchedVertices_iff.1 (mem_sdiff.1 h).1).2.1 h'
    · exact (mem_sdiff.1 h).2 h'
  have hLR : Disjoint (M.image Prod.snd) L := disjoint_right.2 fun u hu h => by
    rcases mem_union.1 (hL hu) with h' | h'
    · exact disjoint_left.1 (disjoint_image_fst_snd hM) h' h
    · exact (mem_unmatchedVertices_iff.1 (hO h')).2.2 h
  have hU : M.unmatchedVertices N ∩ V =
      O ∩ V ∪ S ∩ V ∪ (M.unmatchedVertices N \ (O ∪ S)) ∩ V := by
    ext u
    have := @hO u; have := @hS u
    simp only [mem_inter, mem_union, mem_sdiff] at *
    tauto
  have hLE : #(M.image Prod.fst ∩ V) =
      #{p ∈ M | p.1 ∈ V ∧ p.2 ∈ V} + #{p ∈ M | p.1 ∈ V ∧ p.2 ∉ V} := by
    rw [card_image_inter_of_injOn (injOn_fst hM),
      ← card_filter_add_card_filter_not (s := M.filter fun p => p.1 ∈ V) (fun p => p.2 ∈ V),
      filter_filter, filter_filter]
  have hR : #(M.image Prod.snd ∩ V) = #{p ∈ M | p.1 ∈ V ∧ p.2 ∈ V} := by
    rw [card_image_inter_of_injOn (injOn_snd hM),
      filter_congr fun p hp => ⟨fun h => ⟨hclosed p hp h, h⟩, And.right⟩]
  rw [card_openChoiceSet_inter_product (hS.trans sdiff_subset),
    inter_sdiff_eq_inter_of_disjoint hLR, inter_sdiff_eq_inter_of_disjoint (hLU.mono_left hS),
    inter_sdiff_eq_inter_of_disjoint
      (hLU.mono_left (sdiff_subset_sdiff subset_rfl subset_union_left)),
    card_eq_card_inter_add hM hV, hU, card_union_of_disjoint, card_union_of_disjoint, hLE, hR]
  · omega
  · exact (disjoint_sdiff.mono_right hS).mono inter_subset_left inter_subset_left
  · exact disjoint_sdiff.mono (union_subset_union inter_subset_left inter_subset_left)
      inter_subset_left

end Deficit

/-- **The deficit identity.** For an open pair `(M, O)` for `(par, L)` on `[N]`,
`S ⊆ U(M) \ O` and any vertex `v`, the choice set `I = I(M, O, S)` satisfies
`|I ∩ E_v| + |{(a, b) ∈ M : a ∈ V_v, b ∉ V_v}| + |O ∩ V_v| = |V_v|`. The subtree `V_v`
contains the left endpoint of every pair whose right endpoint it contains, by transitivity of
the ancestor relation. -/
@[lognarayana "lem_open_choice_deficit"]
public theorem Finset.card_openChoiceSet_inter_forestBlock_add {N : ℕ} {par : ℕ → Option ℕ}
    {L : Finset ℕ} {M : Finset (ℕ × ℕ)} {O S : Finset ℕ} (hMO : IsOpenPair N par L M O)
    (hS : S ⊆ Finset.unmatchedVertices N M \ O) (v : ℕ) :
    (Finset.openChoiceSet N M O S ∩ forestBlock N par L v).card +
        (M.filter fun p => p.1 ∈ subtreeVertices N par v ∧ p.2 ∉ subtreeVertices N par v).card +
        (O ∩ subtreeVertices N par v).card =
      (subtreeVertices N par v).card := by
  classical
  have hM := hMO.isNoncrossingPartialMatching
  refine card_openChoiceSet_inter_add hM hMO.subset_unmatchedVertices hS
    hMO.subset_leftEndpoints_union (filter_subset _ _) fun p hp h => mem_filter.2 ⟨?_,
      (mem_filter.1 h).2.trans (hMO.isStrictAncestor p hp).1⟩
  have := hM.one_le_fst p hp; have := hM.fst_lt_snd p hp; have := hM.snd_le p hp
  simp only [mem_Icc]; omega

/-- An unmatched vertex outside `O` is an unmarked vertex of `[N]`. -/
private lemma mem_Icc_sdiff_of_mem_unmatchedVertices {N : ℕ} {par : ℕ → Option ℕ}
    {L : Finset ℕ} {M : Finset (ℕ × ℕ)} {O : Finset ℕ} (hMO : IsOpenPair N par L M O) {w : ℕ}
    (hw : w ∈ unmatchedVertices N M) (hwO : w ∉ O) : w ∈ Icc 1 N \ L := by
  obtain ⟨hw, hwl, -⟩ := mem_unmatchedVertices_iff.1 hw
  refine mem_sdiff.2 ⟨hw, fun hwL => ?_⟩
  rcases mem_union.1 (hMO.subset_leftEndpoints_union hwL) with h | h
  exacts [hwl h, hwO h]

/-- A right endpoint of an open pair's matching is an unmarked vertex of `[N]`. -/
private lemma snd_mem_Icc_sdiff {N : ℕ} {par : ℕ → Option ℕ} {L : Finset ℕ}
    {M : Finset (ℕ × ℕ)} {O : Finset ℕ} (hMO : IsOpenPair N par L M O) {p : ℕ × ℕ}
    (hp : p ∈ M) : p.2 ∈ Icc 1 N \ L := by
  have hM := hMO.isNoncrossingPartialMatching
  have h1 := hM.one_le_fst p hp
  have h2 := hM.fst_lt_snd p hp
  refine mem_sdiff.2 ⟨mem_Icc.2 ⟨by omega, hM.snd_le p hp⟩, fun hL => ?_⟩
  rcases mem_union.1 (hMO.subset_leftEndpoints_union hL) with h | h
  · obtain ⟨q, hq, hqe⟩ := mem_image.1 h
    obtain rfl := hM.eq_of_mem_of_mem p hp q hq p.2 (Or.inr rfl) (Or.inl hqe.symm)
    omega
  · exact (mem_unmatchedVertices_iff.1 (hMO.subset_unmatchedVertices h)).2.2
      (mem_image_of_mem _ hp)

/-- The choice set of an open pair lies in the ground set `{x, y} × ([N] \ L)`. -/
private lemma openChoiceSet_subset_forestGroundSet {N : ℕ} {par : ℕ → Option ℕ}
    {L : Finset ℕ} {M : Finset (ℕ × ℕ)} {O S : Finset ℕ} (hMO : IsOpenPair N par L M O)
    (hS : S ⊆ unmatchedVertices N M \ O) :
    openChoiceSet N M O S ⊆ forestGroundSet N L := by
  rintro ⟨c, u⟩ hx
  refine mem_forestGroundSet_iff.2 ?_
  simp only [openChoiceSet, mem_union, mem_product, mem_univ, true_and, mem_singleton] at hx
  rcases hx with (hx | ⟨_, hx⟩) | ⟨_, hx⟩
  · obtain ⟨p, hp, rfl⟩ := mem_image.1 hx
    exact snd_mem_Icc_sdiff hMO hp
  · obtain ⟨hu, huO⟩ := mem_sdiff.1 (hS hx)
    exact mem_Icc_sdiff_of_mem_unmatchedVertices hMO hu huO
  · simp only [mem_sdiff, mem_union, not_or] at hx
    exact mem_Icc_sdiff_of_mem_unmatchedVertices hMO hx.1 hx.2.1

/-- For an open pair `(M, O)` for `(par, L)` on `[N]` and `S ⊆ U(M) \ O`, the choice set
`I(M, O, S)` is independent: it belongs to the forest independence family `𝕀_{par,L}`. It
avoids the marked vertices, and the deficit identity gives the capacity bounds. -/
@[lognarayana "lem_open_choice_indep"]
public theorem Finset.openChoiceSet_mem_forestIndepFamily {N : ℕ} {par : ℕ → Option ℕ}
    {L : Finset ℕ} {M : Finset (ℕ × ℕ)} {O S : Finset ℕ} (hMO : IsOpenPair N par L M O)
    (hS : S ⊆ Finset.unmatchedVertices N M \ O) :
    Finset.openChoiceSet N M O S ∈ forestIndepFamily N par L := by
  refine mem_forestIndepFamily_iff.2 ⟨openChoiceSet_subset_forestGroundSet hMO hS, fun v _ => ?_⟩
  have := card_openChoiceSet_inter_forestBlock_add hMO hS v
  omega

/-! ### The stack reconstruction -/

/-- The number `c_v` of copies of `v` in `I`. -/
private abbrev cnt (I : Finset (Bool × ℕ)) (v : ℕ) : ℕ := (I ∩ {(true, v), (false, v)}).card

private lemma cnt_le (I : Finset (Bool × ℕ)) (v : ℕ) : cnt I v ≤ 2 :=
  (card_le_card inter_subset_right).trans card_le_two

/-- `c_v` counts which of the two copies `(true, v)`, `(false, v)` of `v` lie in `I`. -/
private lemma cnt_eq (I : Finset (Bool × ℕ)) (v : ℕ) :
    cnt I v =
      (if (true, v) ∈ I then 1 else 0) + (if (false, v) ∈ I then 1 else 0) := by
  rw [cnt, inter_comm, ← filter_mem_eq_inter, card_filter, sum_pair (by simp)]

/-- One step of the reconstruction: a push when `c_{w+1} = 0`, no change when `c_{w+1} ≠ 0` and
nothing is popped (which for `c_{w+1} = 2` means the stack is empty), or a pop of the top `u`
recording `(u, w + 1)` when `c_{w+1} = 2`. -/
private lemma reconstructionStates_succ_cases (I : Finset (Bool × ℕ)) (w : ℕ) :
    (cnt I (w + 1) = 0 ∧ reconstructionStates I (w + 1) =
      ((reconstructionStates I w).1 ++ [w + 1], (reconstructionStates I w).2)) ∨
    (cnt I (w + 1) ≠ 0 ∧ (cnt I (w + 1) = 2 → (reconstructionStates I w).1 = []) ∧
      reconstructionStates I (w + 1) = reconstructionStates I w) ∨
    (cnt I (w + 1) = 2 ∧ ∃ T u, (reconstructionStates I w).1 = T ++ [u] ∧
      reconstructionStates I (w + 1) = (T, insert (u, w + 1) (reconstructionStates I w).2)) := by
  have hle := cnt_le I (w + 1)
  rcases (show cnt I (w + 1) = 0 ∨ cnt I (w + 1) = 1 ∨ cnt I (w + 1) = 2 by omega)
    with h | h | h
  · exact Or.inl ⟨h, by simp only [cnt] at h; simp [reconstructionStates, h]⟩
  · refine Or.inr (Or.inl ⟨by omega, by omega, ?_⟩)
    simp only [cnt] at h; simp [reconstructionStates, h]
  · cases ht : (reconstructionStates I w).1.getLast? with
    | none =>
      refine Or.inr (Or.inl ⟨by omega, fun _ => List.getLast?_eq_none_iff.1 ht, ?_⟩)
      simp only [cnt] at h; simp [reconstructionStates, h, ht]
    | some u =>
      obtain ⟨T, hT⟩ := List.getLast?_eq_some_iff.1 ht
      refine Or.inr (Or.inr ⟨h, T, u, hT, ?_⟩)
      simp only [cnt] at h
      simp [reconstructionStates, h, hT]

/-- Every stack is strictly increasing with entries `≤ w`. -/
private lemma pairwise_and_le (I : Finset (Bool × ℕ)) (w : ℕ) :
    (reconstructionStates I w).1.Pairwise (· < ·) ∧
      ∀ x ∈ (reconstructionStates I w).1, x ≤ w := by
  induction w with
  | zero => simp [reconstructionStates]
  | succ w ih =>
    obtain ⟨hp, hle⟩ := ih
    rcases reconstructionStates_succ_cases I w with ⟨-, h⟩ | ⟨-, -, h⟩ | ⟨-, T, u, hT, h⟩ <;>
      rw [h]
    · refine ⟨List.pairwise_append.2 ⟨hp, by simp, fun x hx y hy => ?_⟩, fun x hx => ?_⟩
      · have := hle x hx; simp at hy; omega
      · rcases List.mem_append.1 hx with hx | hx
        · have := hle x hx; omega
        · simp at hx; omega
    · exact ⟨hp, fun x hx => (hle x hx).trans (by omega)⟩
    · rw [hT] at hp hle
      exact ⟨(List.pairwise_append.1 hp).1,
        fun x hx => (hle x (List.mem_append_left _ hx)).trans (by omega)⟩

/-- The counting identity: if every pop of the reconstruction between `m` and `m + k` removes
an entry `> m`, then the entries `> m` of `λ_{m+k}` number `k - ∑_{u ∈ (m, m+k]} c_u`. -/
private lemma countP_lt_add_sum_cnt (I : Finset (Bool × ℕ)) (m k : ℕ)
    (hpop : ∀ w, m ≤ w → w < m + k → cnt I (w + 1) = 2 →
      ∃ t, (reconstructionStates I w).1.getLast? = some t ∧ m < t) :
    (reconstructionStates I (m + k)).1.countP (fun x => m < x) +
      ∑ u ∈ Ioc m (m + k), cnt I u = k := by
  induction k with
  | zero =>
    simp only [add_zero, Ioc_self, sum_empty, List.countP_eq_zero]
    intro x hx
    simpa using (pairwise_and_le I m).2 x hx
  | succ k ih =>
    have ih := ih fun w h₁ h₂ => hpop w h₁ (by omega)
    have hpop := hpop (m + k) (by omega) (by omega)
    rw [← add_assoc, sum_Ioc_succ_top (by omega)]
    rcases reconstructionStates_succ_cases I (m + k) with
      ⟨h, he⟩ | ⟨h, hnil, he⟩ | ⟨h, T, u, hT, he⟩ <;> rw [he]
    · rw [List.countP_append, h]; simp; omega
    · obtain h1 | h2 : cnt I (m + k + 1) = 1 ∨ cnt I (m + k + 1) = 2 := by
        have := cnt_le I (m + k + 1); omega
      · rw [h1]; omega
      · obtain ⟨t, ht, -⟩ := hpop h2
        simp [hnil h2] at ht
    · obtain ⟨t, ht, hmt⟩ := hpop h
      rw [hT, List.getLast?_concat, Option.some.injEq] at ht
      rw [hT, List.countP_append] at ih
      subst ht
      simp [hmt] at ih
      rw [h]; dsimp only; omega

/-- In a strictly increasing list, the last entry is the largest. -/
private lemma le_getLast_of_pairwise {l : List ℕ} (hl : l.Pairwise (· < ·)) {x : ℕ}
    (hx : x ∈ l) : x ≤ l.getLast (List.ne_nil_of_mem hx) := by
  rw [← List.dropLast_append_getLast (List.ne_nil_of_mem hx)] at hl hx
  rcases List.mem_append.1 hx with hx | hx
  · exact ((List.pairwise_append.1 hl).2.2 x hx _ (by simp)).le
  · simp at hx; omega

/-- The copies of vertices of `V` in `I` are counted vertex by vertex. -/
private lemma sum_cnt_eq (I : Finset (Bool × ℕ)) (V : Finset ℕ) :
    ∑ u ∈ V, cnt I u = (I ∩ univ ×ˢ V).card := by
  rw [card_eq_sum_card_fiberwise (f := Prod.snd) (t := V) (by intro p; simp_all)]
  refine sum_congr rfl fun u hu => congrArg Finset.card ?_
  ext ⟨b, x⟩
  cases b <;> aesop

/-- The capacity bound of the block `E_v`, counted vertex by vertex. -/
private lemma sum_cnt_le_card {N : ℕ} {par : ℕ → Option ℕ} {L : Finset ℕ}
    {I : Finset (Bool × ℕ)} (hI : I ∈ forestIndepFamily N par L) {v : ℕ}
    (hv : v ∈ Icc 1 N) :
    ∑ u ∈ subtreeVertices N par v, cnt I u ≤ (subtreeVertices N par v).card := by
  rw [sum_cnt_eq]
  refine (card_le_card fun p hp => ?_).trans ((mem_forestIndepFamily_iff.1 hI).2 v hv)
  exact mem_inter_forestBlock (mem_forestIndepFamily_iff.1 hI).1 (mem_inter.1 hp).1
    (mem_product.1 (mem_inter.1 hp).2).2

/-- In a postorder forest on `[N]`, if `I ∈ 𝕀_{par,L}` contains both copies of `v ∈ [N]`
(`c_v = 2`), then the reconstruction stack `λ_{v-1}` is nonempty and its last entry lies in
`V_v \ {v}`.

For a postorder forest `V_v = (m, v]` with `m = v - |V_v|`; by strong induction every pop in
`(m, v)` removes an entry of `V_v`, so the entries `> m` of `λ_{v-1}` number
`|V_v| - 1 - ∑_{u ∈ (m, v)} c_u`, which is positive by the capacity bound at `v`. -/
@[lognarayana "lem_reconstruction_pop_in_subtree"]
public theorem exists_getLast?_reconstructionStates_mem_subtreeVertices {N : ℕ}
    {par : ℕ → Option ℕ} {L : Finset ℕ} {I : Finset (Bool × ℕ)} {v : ℕ}
    (hpar : IsPostorderForest N par) (hI : I ∈ forestIndepFamily N par L)
    (hv : v ∈ Finset.Icc 1 N) (hcv : (I ∩ {(true, v), (false, v)}).card = 2) :
    ∃ u, (reconstructionStates I (v - 1)).1.getLast? = some u ∧
      u ∈ subtreeVertices N par v \ {v} := by
  classical
  induction v using Nat.strong_induction_on with
  | _ v IH =>
  have hvV : v ∈ subtreeVertices N par v := mem_filter.2 ⟨hv, 0, rfl⟩
  have hsum := sum_cnt_le_card hI hv
  have hVeq : subtreeVertices N par v = Ioc (v - (subtreeVertices N par v).card) v := by
    have h0 : 0 ∉ subtreeVertices N par v := fun h => by simpa using (mem_filter.1 h).1
    nth_rw 1 [hpar.2 v hv] at h0 ⊢
    ext; simp at h0 ⊢; omega
  set V := subtreeVertices N par v
  set m := v - V.card
  have hmv : m < v := by have := hVeq ▸ hvV; simp at this; omega
  have hk := countP_lt_add_sum_cnt I m (v - 1 - m) fun w hmw hw hw2 => by
    have hwV : w + 1 ∈ V := by rw [hVeq]; simp; omega
    obtain ⟨t, ht, htV⟩ := IH (w + 1) (by omega) (filter_subset _ _ hwV) hw2
    refine ⟨t, ht, ?_⟩
    have htV' : t ∈ V := by
      obtain ⟨h1, -⟩ := mem_sdiff.1 htV
      exact mem_filter.2 ⟨(mem_filter.1 h1).1,
        (mem_filter.1 hwV).2.trans (mem_filter.1 h1).2⟩
    rw [hVeq] at htV'; simp at htV'; omega
  rw [show m + (v - 1 - m) = v - 1 by omega] at hk
  rw [hVeq, show v = v - 1 + 1 by omega, sum_Ioc_succ_top (by omega),
    ← show v = v - 1 + 1 by omega, Nat.card_Ioc] at hsum
  have hpos : 0 < (reconstructionStates I (v - 1)).1.countP (fun x => m < x) := by
    have : cnt I v = 2 := hcv
    omega
  obtain ⟨x, hx, hmx⟩ := List.countP_pos_iff.1 hpos
  obtain ⟨hp, hle⟩ := pairwise_and_le I (v - 1)
  have hxt := le_getLast_of_pairwise hp hx
  have htle := hle _ (List.getLast_mem (List.ne_nil_of_mem hx))
  refine ⟨_, List.getLast?_eq_some_getLast (List.ne_nil_of_mem hx), ?_⟩
  rw [mem_sdiff, hVeq, mem_Ioc, mem_singleton]
  simp at hmx
  omega

/-- The invariant of the reconstruction states used for the left inverse: recorded pairs have
`c = 2` on the right and `c = 0` on the left, stack entries have `c = 0`, and every `u ≤ w` with
`c_u = 0` is on the stack or a left endpoint. -/
private structure CountInv (I : Finset (Bool × ℕ)) (w : ℕ) (S : List ℕ × Finset (ℕ × ℕ)) :
    Prop where
  pairs : ∀ p ∈ S.2, 1 ≤ p.2 ∧ p.2 ≤ w ∧ cnt I p.2 = 2 ∧ cnt I p.1 = 0
  stack : ∀ u ∈ S.1, cnt I u = 0
  zero : ∀ u, 1 ≤ u → u ≤ w → cnt I u = 0 → u ∈ S.1 ∨ u ∈ S.2.leftEndpoints

namespace CountInv

variable {I : Finset (Bool × ℕ)} {w : ℕ} {S : List ℕ × Finset (ℕ × ℕ)}

private lemma pairs_succ (h : CountInv I w S) :
    ∀ p ∈ S.2, 1 ≤ p.2 ∧ p.2 ≤ w + 1 ∧ cnt I p.2 = 2 ∧ cnt I p.1 = 0 :=
  fun p hp => (h.pairs p hp).imp_right fun h' => ⟨by omega, h'.2⟩

/-- A step with `c_{w+1} ≠ 0` that leaves the state unchanged preserves the invariant. -/
private lemma keep (h : CountInv I w S) (hc : cnt I (w + 1) ≠ 0) : CountInv I (w + 1) S where
  pairs := h.pairs_succ
  stack := h.stack
  zero u h1 h2 h0 := by
    obtain h2 | rfl := Nat.le_succ_iff.mp h2
    exacts [h.zero u h1 h2 h0, absurd h0 hc]

/-- Pushing `w + 1` when `c_{w+1} = 0` preserves the invariant. -/
private lemma push (h : CountInv I w S) (hc : cnt I (w + 1) = 0) :
    CountInv I (w + 1) (S.1 ++ [w + 1], S.2) where
  pairs := h.pairs_succ
  stack u hu := by
    obtain hu | hu := List.mem_append.mp hu
    exacts [h.stack u hu, List.mem_singleton.mp hu ▸ hc]
  zero u h1 h2 h0 := by
    obtain h2 | rfl := Nat.le_succ_iff.mp h2
    · exact (h.zero u h1 h2 h0).imp_left (List.mem_append_left _)
    · simp

/-- Popping the top `u` of the stack `T ++ [u]` when `c_{w+1} = 2` preserves the invariant. -/
private lemma pop (h : CountInv I w S) (hc : cnt I (w + 1) = 2) {T : List ℕ} {u : ℕ}
    (hS : S.1 = T ++ [u]) : CountInv I (w + 1) (T, insert (u, w + 1) S.2) where
  pairs p hp := by
    obtain rfl | hp := mem_insert.mp hp
    exacts [⟨by omega, le_rfl, hc, h.stack u (by simp [hS])⟩, h.pairs_succ p hp]
  stack x hx := h.stack x (by simp [hS, hx])
  zero x h1 h2 h0 := by
    obtain h2 | rfl := Nat.le_succ_iff.mp h2
    · rcases h.zero x h1 h2 h0 with h' | h'
      · rw [hS] at h'
        by_cases hxu : x = u
        · exact Or.inr (mem_image.mpr ⟨(x, w + 1), by simp [hxu], rfl⟩)
        · exact Or.inl (by simpa [hxu] using h')
      · exact Or.inr (image_subset_image (subset_insert _ _) h')
    · simp [h0] at hc

end CountInv

private lemma countInv (I : Finset (Bool × ℕ)) : ∀ w, CountInv I w (reconstructionStates I w)
  | 0 => ⟨by simp [reconstructionStates], by simp [reconstructionStates], by omega⟩
  | w + 1 => by
    have ih := countInv I w
    rcases reconstructionStates_succ_cases I w with ⟨h0, h⟩ | ⟨h0, -, h⟩ | ⟨h2, T, u, hT, h⟩ <;>
      rw [h]
    exacts [ih.push h0, ih.keep h0, ih.pop h2 hT]

private lemma pairs_monotone (I : Finset (Bool × ℕ)) :
    Monotone fun w => (reconstructionStates I w).2 :=
  monotone_nat_of_le_succ fun w => by
    rcases reconstructionStates_succ_cases I w with ⟨-, h⟩ | ⟨-, -, h⟩ | ⟨-, T, u, -, h⟩ <;>
      simp [h, subset_insert]

/-- The right endpoints of `M_N` are exactly the `v ∈ [N]` with `c_v = 2`. -/
private lemma mem_right_iff {N : ℕ} {par : ℕ → Option ℕ} {L : Finset ℕ}
    {I : Finset (Bool × ℕ)} (hpar : IsPostorderForest N par)
    (hI : I ∈ forestIndepFamily N par L) (v : ℕ) :
    v ∈ (reconstructionStates I N).2.image Prod.snd ↔ v ∈ Icc 1 N ∧ cnt I v = 2 := by
  refine ⟨fun h => ?_, fun ⟨hv, hcv⟩ => ?_⟩
  · obtain ⟨p, hp, rfl⟩ := mem_image.mp h
    obtain ⟨h1, h2, h3, -⟩ := (countInv I N).pairs p hp
    exact ⟨mem_Icc.mpr ⟨h1, h2⟩, h3⟩
  obtain ⟨u, hu, -⟩ := exists_getLast?_reconstructionStates_mem_subtreeVertices hpar hI hv hcv
  obtain ⟨w, rfl⟩ : ∃ w, v = w + 1 := ⟨v - 1, by have := (mem_Icc.mp hv).1; omega⟩
  rw [Nat.add_sub_cancel] at hu
  have hmem : (u, w + 1) ∈ (reconstructionStates I (w + 1)).2 := by
    rcases reconstructionStates_succ_cases I w with ⟨h, -⟩ | ⟨-, h, -⟩ | ⟨-, T, u', hT, h⟩
    · omega
    · simp [h hcv] at hu
    · rw [hT, List.getLast?_concat, Option.some.injEq] at hu
      simp [h, hu]
  exact mem_image.mpr ⟨_, pairs_monotone I (mem_Icc.mp hv).2 hmem, rfl⟩

/-- A vertex `v ∈ [N]` is on the final stack or a left endpoint of `M_N` iff `c_v = 0`. -/
private lemma mem_stack_or_left_iff (I : Finset (Bool × ℕ)) {N v : ℕ}
    (hv : v ∈ Icc 1 N) :
    v ∈ (reconstructionStates I N).1 ∨ v ∈ (reconstructionStates I N).2.leftEndpoints ↔
      cnt I v = 0 := by
  refine ⟨fun h => h.elim ((countInv I N).stack v) fun h => ?_, fun h =>
    (countInv I N).zero v (mem_Icc.mp hv).1 (mem_Icc.mp hv).2 h⟩
  obtain ⟨p, hp, rfl⟩ := mem_image.mp h
  exact ((countInv I N).pairs p hp).2.2.2

/-- In a postorder forest `par` on `[N]` with marked vertices `L`, the choice set of the
reconstruction `(M_I, O_I, S_I)` of any `I ∈ 𝕀_{par,L}` is `I` itself: `I(M_I, O_I, S_I) = I`. The
right endpoints of `M_I` are the `v ∈ [N]` with `c_v = 2`, and the vertices on the final stack or
left endpoints are those with `c_v = 0`. -/
@[lognarayana "lem_reconstruction_left_inverse"]
public theorem openChoiceSet_stackReconstruction {N : ℕ} {par : ℕ → Option ℕ} {L : Finset ℕ}
    {I : Finset (Bool × ℕ)} (hpar : IsPostorderForest N par)
    (hI : I ∈ forestIndepFamily N par L) :
    Finset.openChoiceSet N (stackReconstruction N I).1 (stackReconstruction N I).2.1
      (stackReconstruction N I).2.2 = I := by
  have hground : ∀ {b v}, (b, v) ∈ I → v ∈ Icc 1 N := fun h =>
    (mem_sdiff.1 (mem_forestGroundSet_iff.1 ((mem_forestIndepFamily_iff.1 hI).1 h))).1
  ext ⟨b, v⟩
  by_cases hv : v ∈ Icc 1 N
  · have hz := mem_stack_or_left_iff I hv
    simp only [openChoiceSet, stackReconstruction, mem_unmatchedVertices_iff, mem_union,
      mem_product,
      mem_univ, true_and, mem_right_iff hpar hI, mem_singleton, mem_sdiff, mem_filter,
      List.mem_toFinset, cnt_eq, hv] at hz ⊢
    by_cases ht : (true, v) ∈ I <;> by_cases hf : (false, v) ∈ I <;> cases b <;>
      (simp_all; try tauto)
  · have h1 : (true, v) ∉ I := fun h => hv (hground h)
    have h2 : (false, v) ∉ I := fun h => hv (hground h)
    cases b <;> simp [openChoiceSet, stackReconstruction, mem_unmatchedVertices_iff,
      mem_right_iff hpar hI, hv, h1, h2]

/-- The invariant of a stack `S` and a set of pairs `M` after `w` steps used for the open-pair
property: the stack is strictly increasing in `[1, w]`, the pairs form a noncrossing partial
matching on `[w]` avoiding the stack, no stack entry lies strictly inside a pair, and every
`x ≤ w` with `c_x = 0` is on the stack or a left endpoint. -/
private structure MatchingInv (I : Finset (Bool × ℕ)) (w : ℕ) (S : List ℕ)
    (M : Finset (ℕ × ℕ)) : Prop where
  pw : S.Pairwise (· < ·)
  mem_S : ∀ x ∈ S, 1 ≤ x ∧ x ≤ w
  mem_M : ∀ p ∈ M, 1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ w
  disj : ∀ x ∈ S, ∀ p ∈ M, x ≠ p.1 ∧ x ≠ p.2
  match_ : ∀ p ∈ M, ∀ q ∈ M, ∀ x : ℕ, (x = p.1 ∨ x = p.2) → (x = q.1 ∨ x = q.2) → p = q
  nc : ∀ p ∈ M, ∀ q ∈ M, ¬ (p.1 < q.1 ∧ q.1 < p.2 ∧ p.2 < q.2)
  exp : ∀ x ∈ S, ∀ p ∈ M, ¬ (p.1 < x ∧ x < p.2)
  zero : ∀ x, 1 ≤ x → x ≤ w → cnt I x = 0 → x ∈ S ∨ ∃ p ∈ M, p.1 = x

/-- A push step preserves the invariant. -/
private lemma MatchingInv.succ_zero {I : Finset (Bool × ℕ)} {w : ℕ} {S : List ℕ}
    {M : Finset (ℕ × ℕ)} (h : MatchingInv I w S M) : MatchingInv I (w + 1) (S ++ [w + 1]) M where
  pw := List.pairwise_append.2 ⟨h.pw, by simp, fun x hx y hy => by
    simp at hy; have := h.mem_S x hx; omega⟩
  mem_S x hx := by
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with hx | hx
    · have := h.mem_S x hx; omega
    · omega
  mem_M p hp := by have := h.mem_M p hp; omega
  disj x hx p hp := by
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with hx | hx
    · exact h.disj x hx p hp
    · have := h.mem_M p hp; omega
  match_ := h.match_
  nc := h.nc
  exp x hx p hp := by
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with hx | hx
    · exact h.exp x hx p hp
    · have := h.mem_M p hp; omega
  zero x h1 h2 h0 := by
    rcases Nat.lt_or_ge x (w + 1) with hx | hx
    · exact (h.zero x h1 (by omega) h0).imp_left fun h' => by simp [h']
    · exact Or.inl (by simp; omega)

/-- A pop of the top `u` at a vertex with `c_{w+1} = 2` preserves the invariant. -/
private lemma MatchingInv.succ_two {I : Finset (Bool × ℕ)} {w u : ℕ} {T : List ℕ}
    {M : Finset (ℕ × ℕ)} (h : MatchingInv I w (T ++ [u]) M) (h2 : cnt I (w + 1) = 2) :
    MatchingInv I (w + 1) T (insert (u, w + 1) M) := by
  have hT : ∀ x ∈ T, x < u := fun x hx =>
    (List.pairwise_append.1 h.pw).2.2 x hx u (by simp)
  have hu := h.mem_S u (by simp)
  have hS : ∀ x ∈ T, x ∈ T ++ [u] := fun x hx => by simp [hx]
  have huM : ∀ p ∈ M, u ≠ p.1 ∧ u ≠ p.2 := h.disj u (by simp)
  constructor
  · exact (List.pairwise_append.1 h.pw).1
  · intro x hx; have := h.mem_S x (hS x hx); omega
  · intro p hp
    rcases mem_insert.1 hp with rfl | hp
    · simp; omega
    · have := h.mem_M p hp; omega
  · intro x hx p hp
    have hxu := hT x hx
    rcases mem_insert.1 hp with rfl | hp
    · have := h.mem_S x (hS x hx); simp; omega
    · exact h.disj x (hS x hx) p hp
  · intro p hp q hq x hpx hqx
    rcases mem_insert.1 hp with rfl | hp <;> rcases mem_insert.1 hq with rfl | hq
    · rfl
    · have := h.mem_M q hq; have := huM q hq; simp at hpx; omega
    · have := h.mem_M p hp; have := huM p hp; simp at hqx; omega
    · exact h.match_ p hp q hq x hpx hqx
  · intro p hp q hq
    rcases mem_insert.1 hp with rfl | hp <;> rcases mem_insert.1 hq with rfl | hq
    · simp
    · have := h.mem_M q hq; simp; omega
    · have := h.exp u (by simp) p hp; have := h.mem_M p hp; simp; omega
    · exact h.nc p hp q hq
  · intro x hx p hp
    rcases mem_insert.1 hp with rfl | hp
    · have := hT x hx; simp; omega
    · exact h.exp x (hS x hx) p hp
  · intro x h1 hx h0
    rcases Nat.lt_or_ge x (w + 1) with hxw | hxw
    · rcases h.zero x h1 (by omega) h0 with h' | ⟨p, hp, hpx⟩
      · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h'
        rcases h' with h' | rfl
        · exact Or.inl h'
        · exact Or.inr ⟨(x, w + 1), mem_insert_self _ _, rfl⟩
      · exact Or.inr ⟨p, mem_insert_of_mem hp, hpx⟩
    · obtain rfl : x = w + 1 := by omega
      omega

/-- A step with `c_{w+1} ≠ 0` that leaves the state unchanged preserves the invariant. -/
private lemma MatchingInv.succ_of_cnt_ne_zero {I : Finset (Bool × ℕ)} {w : ℕ} {S : List ℕ}
    {M : Finset (ℕ × ℕ)} (h : MatchingInv I w S M) (h0 : cnt I (w + 1) ≠ 0) :
    MatchingInv I (w + 1) S M where
  pw := h.pw
  mem_S x hx := by have := h.mem_S x hx; omega
  mem_M p hp := by have := h.mem_M p hp; omega
  disj := h.disj
  match_ := h.match_
  nc := h.nc
  exp := h.exp
  zero x h1 h2 hx0 := by
    obtain hxw | rfl := Nat.lt_or_eq_of_le h2
    · exact h.zero x h1 (by omega) hx0
    · exact absurd hx0 h0

/-- The invariant holds for every reconstruction state. -/
private lemma matchingInv (I : Finset (Bool × ℕ)) (w : ℕ) :
    MatchingInv I w (reconstructionStates I w).1 (reconstructionStates I w).2 := by
  induction w with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun x h1 h2 _ => by omega⟩ <;>
      simp [reconstructionStates]
  | succ w ih =>
    rcases reconstructionStates_succ_cases I w with ⟨-, h⟩ | ⟨h0, -, h⟩ | ⟨h2, T, u, hT, h⟩ <;>
      rw [h]
    · exact ih.succ_zero
    · exact ih.succ_of_cnt_ne_zero h0
    · exact (hT ▸ ih).succ_two h2

/-- For `w ≤ N`, every recorded pair `(u, v)` has `v` a strict ancestor of `u`. -/
private lemma strictAncestor_all {N : ℕ} {par : ℕ → Option ℕ} {L : Finset ℕ}
    {I : Finset (Bool × ℕ)} (hpar : IsPostorderForest N par)
    (hI : I ∈ forestIndepFamily N par L) (w : ℕ) (hw : w ≤ N) :
    ∀ p ∈ (reconstructionStates I w).2, IsStrictAncestor par p.2 p.1 := by
  induction w with
  | zero => simp [reconstructionStates]
  | succ w ih =>
    have ih := ih (by omega)
    rcases reconstructionStates_succ_cases I w with ⟨-, h⟩ | ⟨-, -, h⟩ | ⟨h2, T, u, hT, h⟩ <;>
      rw [h]
    iterate 2 exact ih
    · intro p hp
      rcases mem_insert.1 hp with rfl | hp
      · obtain ⟨u', hu', hmem⟩ := exists_getLast?_reconstructionStates_mem_subtreeVertices
          hpar hI (mem_Icc.2 ⟨by omega, hw⟩) h2
        simp only [Nat.add_sub_cancel, hT, List.getLast?_concat, Option.some.injEq] at hu'
        subst hu'
        simp only [subtreeVertices, mem_sdiff, mem_filter, mem_singleton] at hmem
        exact ⟨hmem.1.2, Ne.symm hmem.2⟩
      · exact ih p hp

/-- In a postorder forest `par` on `[N]` with marked vertices `L ⊆ [N]`, the first two components
`(M_I, O_I)` of the reconstruction of any `I ∈ 𝕀_{par,L}` form an open pair for `(par, L)`. -/
@[lognarayana "lem_reconstruction_open_pair"]
public theorem isOpenPair_stackReconstruction {N : ℕ} {par : ℕ → Option ℕ} {L : Finset ℕ}
    {I : Finset (Bool × ℕ)} (hpar : IsPostorderForest N par) (hL : L ⊆ Finset.Icc 1 N)
    (hI : I ∈ forestIndepFamily N par L) :
    IsOpenPair N par L (stackReconstruction N I).1 (stackReconstruction N I).2.1 := by
  have h := matchingInv I N
  simp only [stackReconstruction]
  refine ⟨⟨fun p hp => (h.mem_M p hp).1, fun p hp => (h.mem_M p hp).2.1,
    fun p hp => (h.mem_M p hp).2.2, h.match_, h.nc⟩, strictAncestor_all hpar hI N le_rfl,
    ?_, fun x hx => h.exp x (List.mem_toFinset.1 hx), ?_⟩
  · intro x hx
    have hx := List.mem_toFinset.1 hx
    simp only [mem_unmatchedVertices_iff, mem_Icc, mem_image, not_exists, not_and]
    exact ⟨h.mem_S x hx, fun p hp hpx => (h.disj x hx p hp).1 hpx.symm,
      fun p hp hpx => (h.disj x hx p hp).2 hpx.symm⟩
  · intro x hxL
    have hx := mem_Icc.1 (hL hxL)
    have h0 : cnt I x = 0 := by
      simp only [cnt, card_eq_zero, eq_empty_iff_forall_notMem, mem_inter]
      rintro q ⟨hq, hq'⟩
      have := (mem_sdiff.1 (mem_forestGroundSet_iff.1 ((mem_forestIndepFamily_iff.1 hI).1 hq))).2
      simp only [mem_insert, mem_singleton] at hq'
      rcases hq' with rfl | rfl <;> exact this hxL
    rcases h.zero x hx.1 hx.2 h0 with h' | ⟨p, hp, hpx⟩
    · exact mem_union_right _ (List.mem_toFinset.2 h')
    · exact mem_union_left _ (mem_image.2 ⟨p, hp, hpx⟩)

private lemma mem_openChoiceSet {N : ℕ} {M : Finset (ℕ × ℕ)} {O S : Finset ℕ} (b : Bool)
    (v : ℕ) : (b, v) ∈ openChoiceSet N M O S ↔
      v ∈ M.image Prod.snd ∨ (b = true ∧ v ∈ S) ∨
        (b = false ∧ v ∈ unmatchedVertices N M ∧ v ∉ O ∧ v ∉ S) := by
  simp [openChoiceSet]
  tauto

/-- The predicate selecting the entries of the stack after step `w`: `u ∈ O`, or `u` is a left
endpoint whose partner exceeds `w`. -/
private def onStack (M : Finset (ℕ × ℕ)) (O : Finset ℕ) (w u : ℕ) : Bool :=
  decide (u ∈ O ∨ ∃ p ∈ M, p.1 = u ∧ w < p.2)

/-- The expected stack after step `w`. -/
private def stackAt (M : Finset (ℕ × ℕ)) (O : Finset ℕ) (w : ℕ) : List ℕ :=
  (List.range' 1 w).filter (onStack M O w)

private lemma filter_or_eq_last {l : List ℕ} (hl : l.Pairwise (· < ·)) {a : ℕ} (ha : a ∈ l)
    (Q : ℕ → Bool) (hQa : Q a = false) (hQ : ∀ u ∈ l, a < u → Q u = false) :
    l.filter (fun u => Q u || decide (u = a)) = l.filter Q ++ [a] := by
  obtain ⟨s, t, rfl⟩ := List.append_of_mem ha
  rw [List.pairwise_append] at hl
  obtain ⟨-, ht, hst⟩ := hl
  have hs : ∀ u ∈ s, u ≠ a := fun u hu => (hst u hu a (by simp)).ne
  have hta : ∀ u ∈ t, a < u := fun u hu => List.rel_of_pairwise_cons ht hu
  have h1 : t.filter (fun u => Q u || decide (u = a)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro u hu
    simp [hQ u (by simp [hu]) (hta u hu), (hta u hu).ne']
  have h2 : t.filter Q = [] := by
    rw [List.filter_eq_nil_iff]
    intro u hu
    simp [hQ u (by simp [hu]) (hta u hu)]
  have h3 : s.filter (fun u => Q u || decide (u = a)) = s.filter Q :=
    List.filter_congr fun u hu => by simp [hs u hu]
  simp [List.filter_append, hQa, h1, h2, h3]

private lemma range'_one_succ (w : ℕ) : List.range' 1 (w + 1) = List.range' 1 w ++ [w + 1] := by
  simp [List.range'_concat, add_comm]

private lemma reconstructionStates_openChoiceSet_succ_of_mem {N : ℕ} {M : Finset (ℕ × ℕ)}
    {O S : Finset ℕ} (hM : IsNoncrossingPartialMatching N M) (hO : O ⊆ unmatchedVertices N M)
    (hOarc : ∀ u ∈ O, ∀ p ∈ M, ¬ (p.1 < u ∧ u < p.2))
    {w a : ℕ} (ha : (a, w + 1) ∈ M)
    (ih : reconstructionStates (openChoiceSet N M O S) w = (stackAt M O w, M.filter (·.2 ≤ w))) :
    reconstructionStates (openChoiceSet N M O S) (w + 1) =
      (stackAt M O (w + 1), M.filter (·.2 ≤ w + 1)) := by
  set I := openChoiceSet N M O S
  rw [reconstructionStates, ih, ← cnt]
  have haw : a < w + 1 := hM.fst_lt_snd _ ha
  have ha1 : 1 ≤ a := hM.one_le_fst _ ha
  have hpart : ∀ p ∈ M, p.2 = w + 1 → p = (a, w + 1) := fun p hp h =>
    injOn_snd hM hp ha h
  have hcard : cnt I (w + 1) = 2 := by
    rw [cnt_eq]
    have hRm : ∃ a, (a, w + 1) ∈ M := ⟨a, ha⟩
    simp [I, mem_openChoiceSet, hRm]
  have hnot : onStack M O (w + 1) (w + 1) = false := by
    simp only [onStack, decide_eq_false_iff_not, not_or, not_exists, not_and]
    refine ⟨fun h => ?_, fun p hp h1 h2 => ?_⟩
    · exact (mem_unmatchedVertices_iff_forall.1 (hO h)).2.2 a ha
    · have := hM.eq_of_mem_of_mem p hp _ ha _ (Or.inl h1.symm) (Or.inr rfl)
      subst this; simp at h1; omega
  have hcongr : ∀ u ∈ List.range' 1 w,
      onStack M O w u = (onStack M O (w + 1) u || decide (u = a)) := by
    intro u _
    simp only [onStack, Bool.decide_or, Bool.or_assoc]
    congr 1
    apply Bool.eq_iff_iff.2
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨p, hp, h1, h2⟩
      by_cases h3 : p.2 = w + 1
      · right; rw [hpart p hp h3] at h1; exact h1.symm
      · left; exact ⟨p, hp, h1, by omega⟩
    · rintro (⟨p, hp, h1, h2⟩ | rfl)
      · exact ⟨p, hp, h1, by omega⟩
      · exact ⟨_, ha, rfl, by simp⟩
  have hstack : stackAt M O w = stackAt M O (w + 1) ++ [a] := by
    rw [stackAt, List.filter_congr hcongr, filter_or_eq_last (List.pairwise_lt_range' ..)
      (by rw [List.mem_range'_1]; omega), stackAt, range'_one_succ w, List.filter_append]
    · simp [hnot]
    · simp only [onStack, decide_eq_false_iff_not, not_or, not_exists, not_and]
      refine ⟨fun h => (mem_unmatchedVertices_iff_forall.1 (hO h)).2.1 _ ha,
        fun p hp h1 h2 => ?_⟩
      obtain rfl := injOn_fst hM hp ha h1
      simp at h2
    · intro u hu hau
      rw [List.mem_range'_1] at hu
      simp only [onStack, decide_eq_false_iff_not, not_or, not_exists, not_and]
      refine ⟨fun h => hOarc u h _ ha ⟨hau, by omega⟩, fun p hp h1 h2 => ?_⟩
      by_cases h3 : p.2 = w + 1
      · rw [hpart p hp h3] at h1; simp at h1; omega
      · exact hM.noncrossing _ ha p hp ⟨by simp; omega, by simp; omega, by omega⟩
  rw [hcard, hstack]
  simp only [List.getLast?_concat, List.dropLast_concat, Prod.mk.injEq, true_and]
  ext p
  simp only [mem_insert, mem_filter]
  constructor
  · rintro (rfl | ⟨hp, h⟩)
    · exact ⟨ha, le_rfl⟩
    · exact ⟨hp, by omega⟩
  · rintro ⟨hp, h⟩
    by_cases h3 : p.2 = w + 1
    · exact Or.inl (hpart p hp h3)
    · exact Or.inr ⟨hp, by omega⟩

private lemma reconstructionStates_openChoiceSet_succ_of_not_mem {N : ℕ} {M : Finset (ℕ × ℕ)}
    {O S : Finset ℕ} (hM : IsNoncrossingPartialMatching N M) (hS : S ⊆ unmatchedVertices N M \ O)
    {w : ℕ} (hw : w + 1 ≤ N) (hR : ∀ a, (a, w + 1) ∉ M)
    (ih : reconstructionStates (openChoiceSet N M O S) w = (stackAt M O w, M.filter (·.2 ≤ w))) :
    reconstructionStates (openChoiceSet N M O S) (w + 1) =
      (stackAt M O (w + 1), M.filter (·.2 ≤ w + 1)) := by
  set I := openChoiceSet N M O S
  rw [reconstructionStates, ih, ← cnt]
  have hSU : ∀ v ∈ S, v ∈ unmatchedVertices N M ∧ v ∉ O := fun v hv => by simpa using hS hv
  have hR' : ∀ p ∈ M, p.2 ≠ w + 1 := fun p hp h => hR p.1 (by rw [← h]; exact hp)
  have hMf : M.filter (·.2 ≤ w + 1) = M.filter (·.2 ≤ w) := by
    ext p
    simp only [mem_filter, and_congr_right_iff]
    intro hp
    have := hR' p hp
    omega
  have hcongr : ∀ u ∈ List.range' 1 w, onStack M O (w + 1) u = onStack M O w u := by
    intro u _
    simp only [onStack]
    congr 1
    apply propext
    refine or_congr Iff.rfl ⟨fun ⟨p, hp, h1, h2⟩ => ⟨p, hp, h1, by omega⟩,
      fun ⟨p, hp, h1, h2⟩ => ⟨p, hp, h1, ?_⟩⟩
    have := hR' p hp
    omega
  have hsplit : stackAt M O (w + 1) =
      stackAt M O w ++ [w + 1].filter (onStack M O (w + 1)) := by
    rw [stackAt, range'_one_succ w, List.filter_append, List.filter_congr hcongr, stackAt]
  by_cases h0 : w + 1 ∈ O ∨ ∃ b, (w + 1, b) ∈ M
  · have hcard : cnt I (w + 1) = 0 := by
      rw [cnt_eq]
      have hnS : w + 1 ∉ S := fun h => by
        rcases h0 with h0 | ⟨b, hb⟩
        · exact (hSU _ h).2 h0
        · exact (mem_unmatchedVertices_iff_forall.1 (hSU _ h).1).2.1 b hb
      have hnU : w + 1 ∈ unmatchedVertices N M → w + 1 ∈ O := fun h => by
        rcases h0 with h0 | ⟨b, hb⟩
        · exact h0
        · exact absurd hb ((mem_unmatchedVertices_iff_forall.1 h).2.1 b)
      simp only [I, mem_openChoiceSet, mem_image]
      simpa [hR, hnS] using hnU
    have hon : onStack M O (w + 1) (w + 1) = true := by
      simp only [onStack, decide_eq_true_eq]
      rcases h0 with h0 | ⟨b, hb⟩
      · exact Or.inl h0
      · exact Or.inr ⟨_, hb, rfl, hM.fst_lt_snd _ hb⟩
    rw [hcard, hsplit, hMf]
    simp [hon]
  · push Not at h0
    have hUv : w + 1 ∈ unmatchedVertices N M :=
      mem_unmatchedVertices_iff_forall.2 ⟨⟨by omega, hw⟩, h0.2, hR⟩
    have hcard : cnt I (w + 1) = 1 := by
      rw [cnt_eq]
      simp only [I, mem_openChoiceSet, mem_image]
      by_cases hvS : w + 1 ∈ S <;> simp [hR, hvS, hUv, h0.1]
    have hoff : onStack M O (w + 1) (w + 1) = false := by
      simp only [onStack, decide_eq_false_iff_not, not_or, not_exists, not_and]
      exact ⟨h0.1, fun p hp h1 _ => h0.2 p.2 (by rw [← h1]; exact hp)⟩
    rw [hcard, hsplit, hMf]
    simp [hoff]

/-- The reconstruction states on `I(M, O, S)`: after step `w ≤ N` the stack is `stackAt M O w`
and the matching built so far consists of the pairs of `M` with right endpoint at most `w`. -/
private theorem reconstructionStates_openChoiceSet {N : ℕ} {M : Finset (ℕ × ℕ)}
    {O S : Finset ℕ} (hM : IsNoncrossingPartialMatching N M) (hO : O ⊆ unmatchedVertices N M)
    (hOarc : ∀ u ∈ O, ∀ p ∈ M, ¬ (p.1 < u ∧ u < p.2))
    (hS : S ⊆ unmatchedVertices N M \ O) :
    ∀ w ≤ N, reconstructionStates (openChoiceSet N M O S) w =
      (stackAt M O w, M.filter (·.2 ≤ w)) := by
  intro w
  induction w with
  | zero =>
    intro _
    rw [reconstructionStates]
    simp only [stackAt, List.range'_zero, List.filter_nil, Prod.mk.injEq, true_and]
    ext p
    simp only [notMem_empty, mem_filter, nonpos_iff_eq_zero, false_iff, not_and]
    exact fun hp => (Nat.zero_lt_of_lt (hM.fst_lt_snd p hp)).ne'
  | succ w ih =>
    intro hw
    by_cases hR : ∃ a, (a, w + 1) ∈ M
    · obtain ⟨a, ha⟩ := hR
      exact reconstructionStates_openChoiceSet_succ_of_mem hM hO hOarc ha (ih (by omega))
    · push Not at hR
      exact reconstructionStates_openChoiceSet_succ_of_not_mem hM hS hw hR (ih (by omega))

/-- If `M` is a noncrossing partial matching on `[N]`, `O ⊆ U(M)` contains no vertex lying
strictly inside an arc of `M`, and `S ⊆ U(M) \ O`, then the stack reconstruction of the choice
set `I(M, O, S)` is `(M, O, S)`: every left endpoint and every vertex of `O` is pushed, and
every right endpoint pops its own left endpoint. -/
@[lognarayana "lem_reconstruction_right_inverse"]
public theorem stackReconstruction_openChoiceSet {N : ℕ} {M : Finset (ℕ × ℕ)} {O S : Finset ℕ}
    (hM : IsNoncrossingPartialMatching N M) (hO : O ⊆ Finset.unmatchedVertices N M)
    (hOarc : ∀ u ∈ O, ∀ p ∈ M, ¬ (p.1 < u ∧ u < p.2))
    (hS : S ⊆ Finset.unmatchedVertices N M \ O) :
    stackReconstruction N (Finset.openChoiceSet N M O S) = (M, O, S) := by
  rw [stackReconstruction, reconstructionStates_openChoiceSet hM hO hOarc hS N le_rfl]
  refine Prod.ext (filter_true_of_mem fun p hp => hM.snd_le p hp) (Prod.ext ?_ ?_)
  · ext u
    simp only [stackAt, onStack, List.mem_toFinset, List.mem_filter, List.mem_range'_1,
      decide_eq_true_eq]
    constructor
    · rintro ⟨-, hu | ⟨p, hp, -, h⟩⟩
      · exact hu
      · exact absurd (hM.snd_le p hp) (by omega)
    · intro hu
      have := (mem_unmatchedVertices_iff_forall.1 (hO hu)).1
      exact ⟨by omega, Or.inl hu⟩
  · ext v
    simp only [mem_filter, mem_Icc, cnt_eq, mem_openChoiceSet, mem_image]
    constructor
    · rintro ⟨-, h1, h2⟩
      by_cases hR : ∃ a, (a, v) ∈ M
      · simp [hR] at h1
      · simpa [hR] using h2
    · intro hv
      have hv' := hS hv
      rw [mem_sdiff, mem_unmatchedVertices_iff_forall] at hv'
      have hR : ¬ ∃ a, (a, v) ∈ M := fun ⟨a, ha⟩ => hv'.1.2.2 a ha
      refine ⟨hv'.1.1, ?_, ?_⟩ <;> simp [hR, hv]

/-- The choice component `S_I` of the reconstruction consists of unmatched, non-open vertices. -/
private lemma choice_subset (N : ℕ) (I : Finset (Bool × ℕ)) :
    (stackReconstruction N I).2.2 ⊆
      unmatchedVertices N (stackReconstruction N I).1 \ (stackReconstruction N I).2.1 := by
  intro v hv
  simp only [stackReconstruction, mem_filter] at hv
  obtain ⟨hvN, hc, -⟩ := hv
  have h := countInv I N
  simp only [stackReconstruction, mem_sdiff, mem_unmatchedVertices_iff, mem_image,
    List.mem_toFinset, not_exists, not_and]
  refine ⟨⟨hvN, fun p hp hpv => ?_, fun p hp hpv => ?_⟩, fun hv => by simp [h.stack v hv] at hc⟩
  · subst hpv; simp [(h.pairs p hp).2.2.2] at hc
  · subst hpv; simp [(h.pairs p hp).2.2.1] at hc

/-- For a postorder forest `par` on `[N]` and `L ⊆ [N]`, the map `(M, O, S) ↦ I(M, O, S)` is a
bijection from the triples with `(M, O)` an open pair for `(par, L)` and `S ⊆ U(M) \ O` onto the
forest independence family `𝕀_{par,L}`; its inverse is the stack reconstruction. -/
@[lognarayana "lem_open_choice_bijection"]
public theorem Finset.bijOn_openChoiceSet_forestIndepFamily {N : ℕ} {par : ℕ → Option ℕ}
    {L : Finset ℕ} (hpar : IsPostorderForest N par) (hL : L ⊆ Finset.Icc 1 N) :
    Set.BijOn (fun t : Finset (ℕ × ℕ) × Finset ℕ × Finset ℕ =>
        Finset.openChoiceSet N t.1 t.2.1 t.2.2)
      {t | IsOpenPair N par L t.1 t.2.1 ∧ t.2.2 ⊆ Finset.unmatchedVertices N t.1 \ t.2.1}
      ↑(forestIndepFamily N par L) := by
  refine ⟨fun t ht => openChoiceSet_mem_forestIndepFamily ht.1 ht.2, ?_, fun I hI =>
    ⟨stackReconstruction N I, ⟨isOpenPair_stackReconstruction hpar hL hI, choice_subset N I⟩,
      openChoiceSet_stackReconstruction hpar hI⟩⟩
  rintro ⟨M, O, S⟩ ⟨hMO, hS⟩ ⟨M', O', S'⟩ ⟨hMO', hS'⟩ h
  rw [← stackReconstruction_openChoiceSet hMO.isNoncrossingPartialMatching
      hMO.subset_unmatchedVertices hMO.exposed hS,
    ← stackReconstruction_openChoiceSet hMO'.isNoncrossingPartialMatching
      hMO'.subset_unmatchedVertices hMO'.exposed hS']
  exact congrArg (stackReconstruction N) h

/-! ### The forest matching polynomial and the matroid -/

open MvPolynomial in
/-- The summand of `forestMatchingPoly` for `S ⊆ U(M)` is the monomial of `I(M, ∅, S)`. -/
private lemma prod_openChoiceSet_empty (R : Type*) [CommSemiring R] (N : ℕ)
    (M : Finset (ℕ × ℕ)) (S : Finset ℕ) (hS : S ⊆ unmatchedVertices N M) :
    (∏ v ∈ M.image Prod.snd, (X (true, v) * X (false, v) : MvPolynomial (Bool × ℕ) R)) *
        ((∏ v ∈ S, X (true, v)) * ∏ v ∈ unmatchedVertices N M \ S, X (false, v)) =
      ∏ e ∈ openChoiceSet N M ∅ S, X e := by
  have hRU := disjoint_image_snd_unmatchedVertices N M
  have h1 : Disjoint (univ ×ˢ M.image Prod.snd) ({true} ×ˢ S) :=
    disjoint_product.2 (Or.inr (hRU.mono_right hS))
  have h2 : Disjoint (univ ×ˢ M.image Prod.snd ∪ {true} ×ˢ S)
      ({false} ×ˢ (unmatchedVertices N M \ (∅ ∪ S))) :=
    disjoint_union_left.2 ⟨disjoint_product.2 (Or.inr (hRU.mono_right sdiff_subset)),
      disjoint_product.2 (Or.inl (by simp))⟩
  rw [openChoiceSet, prod_union h2, prod_union h1, prod_product_right, prod_product,
    prod_product, empty_union]
  simp [mul_comm, mul_assoc]

open Classical in
/-- The index set of the expanded `forestMatchingPoly` — admissible `M` and `S ⊆ U(M)` — is
exactly the set of triples `(M, ∅, S)` in the domain of the choice-set bijection. -/
private lemma mem_sigma_iff_isOpenPair_empty {N : ℕ} {par : ℕ → Option ℕ} {L : Finset ℕ}
    (M : Finset (ℕ × ℕ)) (S : Finset ℕ) :
    (⟨M, S⟩ : Σ _ : Finset (ℕ × ℕ), Finset ℕ) ∈
        ((Icc 1 N ×ˢ Icc 1 N).powerset.filter
          (fun M : Finset (ℕ × ℕ) => IsAdmissibleMatching N par L M)).sigma
          (fun M => (unmatchedVertices N M).powerset) ↔
      IsOpenPair N par L M ∅ ∧ S ⊆ unmatchedVertices N M \ ∅ := by
  simp only [mem_sigma, mem_filter, mem_powerset, sdiff_empty,
    isOpenPair_empty_iff_isAdmissibleMatching]
  refine and_congr_left fun _ => and_iff_right_of_imp fun hM p hp => ?_
  have := hM.isNoncrossingPartialMatching.one_le_fst _ hp
  have := hM.isNoncrossingPartialMatching.fst_lt_snd _ hp
  have := hM.isNoncrossingPartialMatching.snd_le _ hp
  simp only [mem_product, mem_Icc] at *
  omega

/-- Let `par` be a postorder forest on `[N]` and `L ⊆ [N]`. Then
`Z_{par,L} = ∑_{I ∈ 𝕀_{par,L}, |I| = N} z^I`, where `z^I = ∏_{e ∈ I} X e`: expanding
`∏_{v ∈ U(M)} (x_v + y_v)` gives the monomials of the choice sets `I(M, ∅, S)`, and these are the
members of size `N` by the choice-set bijection and `|I(M, O, S)| + |O| = N`. -/
@[lognarayana "lem_forest_z_indep"]
public theorem forestMatchingPoly_eq_sum_card_eq_prod_X (R : Type*) [CommSemiring R] {N : ℕ}
    {par : ℕ → Option ℕ} {L : Finset ℕ} (hpar : IsPostorderForest N par)
    (hL : L ⊆ Finset.Icc 1 N) :
    forestMatchingPoly R N par L =
      ∑ I ∈ (forestIndepFamily N par L).filter (fun I : Finset (Bool × ℕ) => I.card = N),
        ∏ e ∈ I, MvPolynomial.X e := by
  classical
  have hB := bijOn_openChoiceSet_forestIndepFamily hpar hL
  have hcard {M O S} (h : IsOpenPair N par L M O ∧ S ⊆ unmatchedVertices N M \ O) :=
    card_openChoiceSet_add_card h.1.isNoncrossingPartialMatching h.1.subset_unmatchedVertices h.2
  rw [forestMatchingPoly]
  simp_rw [prod_add, mul_sum]
  rw [sum_sigma']
  refine sum_bij (fun t _ => openChoiceSet N t.1 ∅ t.2) ?_ ?_ ?_ ?_
  · rintro ⟨M, S⟩ ht
    rw [mem_sigma_iff_isOpenPair_empty] at ht
    exact mem_filter.2 ⟨mem_coe.1 (hB.mapsTo (x := (M, ∅, S)) ht), by simpa using hcard ht⟩
  · rintro ⟨M, S⟩ ht ⟨M', S'⟩ ht' h
    rw [mem_sigma_iff_isOpenPair_empty] at ht ht'
    obtain ⟨rfl, h₂⟩ := Prod.ext_iff.1 (hB.injOn (x₁ := (M, ∅, S)) (x₂ := (M', ∅, S')) ht ht' h)
    obtain rfl : S = S' := congrArg Prod.snd h₂
    rfl
  · intro I hI
    obtain ⟨hI, hIN⟩ := mem_filter.1 hI
    obtain ⟨⟨M, O, S⟩, hMOS, rfl⟩ := hB.surjOn (mem_coe.2 hI)
    obtain rfl : O = ∅ := card_eq_zero.1 (by have := hcard hMOS; dsimp only at *; omega)
    exact ⟨⟨M, S⟩, (mem_sigma_iff_isOpenPair_empty M S).2 hMOS, rfl⟩
  · rintro ⟨M, S⟩ ht
    exact prod_openChoiceSet_empty R N M S (mem_powerset.1 (mem_sigma.1 ht).2)

/-- If the independent sets of a matroid are exactly the members of a finset family `F`, every
member of `F` has at most `n` elements and some member has exactly `n`, then every base has
`n` elements. -/
private lemma encard_eq_of_isBase_of_indep_iff {α : Type*} {M : Matroid α}
    {F : Finset (Finset α)} {n : ℕ} (hI : ∀ I, M.Indep I ↔ ∃ J ∈ F, (J : Set α) = I)
    (hle : ∀ J ∈ F, J.card ≤ n) (hex : ∃ J ∈ F, J.card = n) {B : Set α} (hB : M.IsBase B) :
    B.encard = n := by
  obtain ⟨J, hJ, hJn⟩ := hex
  obtain ⟨B₀, hB₀, hsub⟩ := ((hI _).2 ⟨J, hJ, rfl⟩).exists_isBase_superset
  rw [hB.encard_eq_encard_of_isBase hB₀]
  obtain ⟨J₀, hJ₀, rfl⟩ := (hI _).1 hB₀.indep
  rw [Set.encard_coe_eq_coe_finsetCard]
  exact_mod_cast (hle _ hJ₀).antisymm (hJn ▸ card_le_card (coe_subset.1 hsub))

/-- Let `par` be a postorder forest on `[N]` and `L ⊆ [N]` with `Z_{par,L} ≠ 0`. Every matroid `M`
on `Bool × ℕ` whose independent sets are exactly the members of `𝕀_{par,L}` has all its bases of
cardinality `N`: `Z_{par,L} ≠ 0` provides an independent set of size `N`, and none is larger. -/
@[lognarayana "thm_forest_matroid_rank"]
public theorem Matroid.encard_eq_of_isBase_of_indep_iff_mem_forestIndepFamily {N : ℕ}
    {par : ℕ → Option ℕ} {L : Finset ℕ} (hpar : IsPostorderForest N par)
    (hL : L ⊆ Finset.Icc 1 N) (hZ : forestMatchingPoly ℝ N par L ≠ 0) (M : Matroid (Bool × ℕ))
    (hI : ∀ I : Set (Bool × ℕ),
      M.Indep I ↔ ∃ J ∈ forestIndepFamily N par L, (J : Set (Bool × ℕ)) = I)
    {B : Set (Bool × ℕ)} (hB : M.IsBase B) : B.encard = N := by
  rw [forestMatchingPoly_eq_sum_card_eq_prod_X ℝ hpar hL] at hZ
  obtain ⟨J, hJ⟩ := nonempty_of_sum_ne_zero hZ
  exact encard_eq_of_isBase_of_indep_iff hI
    (fun _ ↦ card_le_of_mem_forestIndepFamily N par L) ⟨J, mem_filter.1 hJ⟩ hB

/-- If the independent sets of `M` are exactly the members of a family `F` of finite sets and
every base of `M` has `n` elements, then the bases of `M` are exactly the members of `F` with
`n` elements. -/
private lemma isBase_iff_mem_and_card_eq {α : Type*} {M : Matroid α} {F : Finset (Finset α)}
    {n : ℕ} (hI : ∀ I : Set α, M.Indep I ↔ ∃ J ∈ F, (J : Set α) = I)
    (hrank : ∀ {B : Set α}, M.IsBase B → B.encard = n) (B : Finset α) :
    M.IsBase (B : Set α) ↔ B ∈ F ∧ B.card = n := by
  constructor
  · intro hB
    obtain ⟨J, hJ, hJB⟩ := (hI _).1 hB.indep
    obtain rfl : J = B := by exact_mod_cast hJB
    exact ⟨hJ, by exact_mod_cast (Set.encard_coe_eq_coe_finsetCard J).symm.trans (hrank hB)⟩
  · rintro ⟨hBF, hcard⟩
    obtain ⟨B', hB', hsub⟩ := ((hI _).2 ⟨B, hBF, rfl⟩).exists_isBase_superset
    rwa [B.finite_toSet.eq_of_subset_of_encard_le hsub
      (by rw [hrank hB', Set.encard_coe_eq_coe_finsetCard, hcard])]

open Classical in
/-- Let `par` be a postorder forest on `[N]` and `L ⊆ [N]` with `Z_{par,L} ≠ 0`. For every
matroid `M` on `E_{N,L}` whose independent sets are exactly the members of `𝕀_{par,L}`,
`Z_{par,L} = ∑_{B ∈ 𝔹(M)} ∏_{e ∈ B} X e`, i.e. `∑_B ∏_{v⁺ ∈ B} x_v ∏_{v⁻ ∈ B} y_v`. -/
@[lognarayana "thm_forest_basis_identity"]
public theorem forestMatchingPoly_eq_sum_isBase_prod_X {N : ℕ} {par : ℕ → Option ℕ}
    {L : Finset ℕ} (hpar : IsPostorderForest N par) (hL : L ⊆ Finset.Icc 1 N)
    (hZ : forestMatchingPoly ℝ N par L ≠ 0) (M : Matroid (Bool × ℕ))
    (hE : M.E = ↑(forestGroundSet N L))
    (hI : ∀ I : Set (Bool × ℕ),
      M.Indep I ↔ ∃ J ∈ forestIndepFamily N par L, (J : Set (Bool × ℕ)) = I) :
    forestMatchingPoly ℝ N par L =
      ∑ B ∈ (forestGroundSet N L).powerset.filter
          (fun B : Finset (Bool × ℕ) => M.IsBase (B : Set (Bool × ℕ))),
        ∏ e ∈ B, MvPolynomial.X e := by
  rw [forestMatchingPoly_eq_sum_card_eq_prod_X ℝ hpar hL]
  refine sum_congr ?_ fun _ _ => rfl
  ext B
  rw [mem_filter, mem_filter, isBase_iff_mem_and_card_eq hI
    (Matroid.encard_eq_of_isBase_of_indep_iff_mem_forestIndepFamily hpar hL hZ M hI)]
  exact ⟨fun h => ⟨mem_powerset.2 <| coe_subset.1 <|
    hE ▸ ((hI _).2 ⟨B, h.1, rfl⟩).subset_ground, h⟩, And.right⟩

/-- A finite set is recovered from the exponent vector `∑ e ∈ I, single e 1` of its square-free
monomial, which is its indicator. -/
private lemma sum_single_one_injective {σ : Type*} :
    Function.Injective (fun I : Finset σ => ∑ e ∈ I, Finsupp.single e 1) := by
  classical
  intro I J h
  ext a
  have := DFunLike.congr_fun h a
  simp only [Finset.sum_apply', Finsupp.single_apply] at this
  simp at this
  split_ifs at this <;> tauto

open MvPolynomial in
/-- In a sum of square-free monomials over a family of distinct finite sets, every coefficient
is `0` or `1`. -/
private lemma coeff_sum_prod_X_eq_zero_or_eq_one {R σ : Type*} [CommSemiring R]
    (S : Finset (Finset σ)) (d : σ →₀ ℕ) :
    (∑ I ∈ S, ∏ e ∈ I, (X e : MvPolynomial σ R)).coeff d = 0 ∨
      (∑ I ∈ S, ∏ e ∈ I, (X e : MvPolynomial σ R)).coeff d = 1 := by
  classical
  simp only [X, ← monomial_sum_one, coeff_sum, coeff_monomial, sum_boole]
  have : #{I ∈ S | ∑ e ∈ I, Finsupp.single e 1 = d} ≤ 1 :=
    card_le_one.2 fun I hI J hJ =>
      sum_single_one_injective ((mem_filter.1 hI).2.trans (mem_filter.1 hJ).2.symm)
  interval_cases #{I ∈ S | ∑ e ∈ I, Finsupp.single e 1 = d} <;> simp

/-- For a postorder forest `par` on `[N]` and `L ⊆ [N]`, every coefficient of the forest
matching polynomial `Z_{par,L}` is `0` or `1`, since it is a sum of square-free monomials over
distinct sets. -/
@[lognarayana "thm_forest_z_coeffs_one"]
public theorem coeff_forestMatchingPoly_eq_zero_or_eq_one {R : Type*} [CommSemiring R] {N : ℕ}
    {par : ℕ → Option ℕ} {L : Finset ℕ} (hpar : IsPostorderForest N par)
    (hL : L ⊆ Finset.Icc 1 N) (d : Bool × ℕ →₀ ℕ) :
    (forestMatchingPoly R N par L).coeff d = 0 ∨ (forestMatchingPoly R N par L).coeff d = 1 := by
  classical
  rw [forestMatchingPoly_eq_sum_card_eq_prod_X R hpar hL]
  exact coeff_sum_prod_X_eq_zero_or_eq_one _ d

/-- If an embedding `f` covers the ground set of `M`, the bases of `M.comap f` are exactly the
finsets whose image under `f` is a base of `M`. -/
private lemma comap_isBase_coe_iff {α β : Type*} {M : Matroid β} (f : α ↪ β)
    (hf : M.E ⊆ Set.range f) (I : Finset α) :
    (M.comap f).IsBase I ↔ M.IsBase (I.map f : Set β) := by
  classical
  rw [Matroid.comap_isBase_iff, coe_map, Set.image_preimage_eq_of_subset hf,
    Matroid.isBasis_ground_iff]
  refine ⟨fun h => h.1, fun h => ⟨h, f.injective.injOn, ?_⟩⟩
  rw [← Set.image_subset_iff]
  exact h.subset_ground

open MvPolynomial in
/-- Let `f` be an embedding covering the ground set `M.E = E` of `M`. Renaming the basis
generating polynomial of `M.comap f` along `f` gives the basis generating polynomial of `M`,
written as a sum over the subsets of `E`. -/
private lemma rename_basisGeneratingPolynomial_comap {α β R : Type*} [Fintype α]
    [CommSemiring R] {M : Matroid β} (f : α ↪ β) {E : Finset β} (hE : M.E = E)
    (hf : M.E ⊆ Set.range f) :
    open scoped Classical in
    rename f ((M.comap f).basisGeneratingPolynomial R) =
      ∑ B ∈ E.powerset.filter (fun B : Finset β => M.IsBase (B : Set β)), ∏ e ∈ B, X e := by
  classical
  have hmap : (univ.filter fun B : Finset α => (M.comap f).IsBase B).map
      (mapEmbedding f).toEmbedding =
      E.powerset.filter (fun B : Finset β => M.IsBase (B : Set β)) := by
    ext J
    simp only [mem_map, mem_filter, mem_univ, true_and, comap_isBase_coe_iff f hf,
      RelEmbedding.coe_toEmbedding, mapEmbedding_apply, mem_powerset]
    refine ⟨fun ⟨I, hI, hIJ⟩ => hIJ ▸ ⟨?_, hI⟩, fun ⟨hJE, hJ⟩ => ?_⟩
    · exact_mod_cast hE ▸ hI.subset_ground
    · have hJ' : J ⊆ univ.map f := fun e he => by
        obtain ⟨a, rfl⟩ := hf (hE ▸ mem_coe.2 (hJE he))
        exact mem_map_of_mem f (mem_univ a)
      obtain ⟨I, -, rfl⟩ := subset_map_iff.1 hJ'
      exact ⟨I, hJ, rfl⟩
  rw [Matroid.basisGeneratingPolynomial, map_sum, ← hmap, sum_map]
  refine sum_congr (by congr) fun I _ => ?_
  simp [map_prod, prod_map]

open MvPolynomial in
/-- For a postorder forest `par` on `[N]` and `L ⊆ [N]`, the forest matching polynomial
`Z_{par,L}(x, y)` is Lorentzian: it is the image, under the inclusion of variables
`Bool × [N] ↪ Bool × ℕ`, of a Lorentzian polynomial in `ℝ[x_v, y_v : v ∈ [N]]`, namely the
basis generating polynomial of the forest matroid pulled back to `Bool × [N]`. -/
@[lognarayana "thm_forest_z_lorentzian"]
public theorem isLorentzian_forestMatchingPoly
    (hBH : ∀ (σ : Type) [Fintype σ], NormalizedSupportPolyLorentzianOfMConvex σ)
    {N : ℕ} {par : ℕ → Option ℕ} {L : Finset ℕ}
    (hpar : IsPostorderForest N par) (hL : L ⊆ Finset.Icc 1 N) :
    ∃ g : MvPolynomial (Bool × Finset.Icc 1 N) ℝ,
      rename (Prod.map id Subtype.val) g = forestMatchingPoly ℝ N par L ∧ g.IsLorentzian := by
  classical
  by_cases hZ : forestMatchingPoly ℝ N par L = 0
  · exact ⟨0, by simp [hZ], Or.inl rfl⟩
  let f : Bool × Finset.Icc 1 N ↪ Bool × ℕ :=
    ⟨Prod.map id Subtype.val, Function.injective_id.prodMap Subtype.val_injective⟩
  obtain ⟨M, hE, hM⟩ := exists_matroid_indep_iff_mem_forestIndepFamily N par L
  have hEf : M.E ⊆ Set.range f := by
    rintro ⟨b, v⟩ he
    rw [hE, mem_coe, mem_forestGroundSet_iff] at he
    exact ⟨(b, ⟨v, (mem_sdiff.1 he).1⟩), rfl⟩
  refine ⟨(M.comap f).basisGeneratingPolynomial ℝ, ?_,
    Matroid.isLorentzian_basisGeneratingPolynomial (hBH _) _⟩
  rw [forestMatchingPoly_eq_sum_isBase_prod_X hpar hL hZ M hE hM]
  exact rename_basisGeneratingPolynomial_comap (R := ℝ) f hE hEf
