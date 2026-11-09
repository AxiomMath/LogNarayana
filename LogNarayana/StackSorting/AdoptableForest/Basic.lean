/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib
public import LogNarayana.Attr
public import LogNarayana.StackSorting.AdoptableForest.Defs
public import LogNarayana.StackSorting.Descents.Defs
public import LogNarayana.StackSorting.FiberPolynomials.Defs
public import LogNarayana.StackSorting.Matchings.Basic
public import LogNarayana.AuxiliaryDefinitions

/-!
# The adoptable forest

A parent map `par` on `[N]` encodes a rooted forest in which every vertex has a smaller label
than its parent. Its ancestor-or-self relation is transitive (`IsAncestorOrSelf.trans`), a strict
ancestor has a larger label than its descendant (`IsStrictAncestor.lt`), and two subtrees which
meet are nested (`subtreeVertices_subset_or_subset_of_inter_nonempty`).

Fix `π = π₁ ⋯ π_n`. An adoptable pair `(a, b)` of `π` satisfies `π_a < π_{b+1}`
(`List.IsAdoptablePair.getElem_lt`), and overlapping adoptable pairs concatenate
(`List.IsAdoptablePair.concat`). The adoptable left endpoints `a` of a right endpoint `b` form the
interval `[ℓ_b, b - 1]`, the adoptable intervals `I_b = [ℓ_b, b]` are nested, and the subtree of
the adoptable forest `𝓕_π` rooted at `b` is exactly `I_b`. Consequently `𝓕_π` is a postorder
forest, the adoptable pairs are exactly its strict ancestor relations, and every descent of `π`
is a leaf of `𝓕_π`.

For a permutation `π ∈ S_n`, every pair of a matching `M ∈ 𝒜(π)` is adoptable, so `𝒜(π)` is the
set of admissible matchings of `𝓕_π` with marked set `Des(π)`. The section closes with the
running example `π = 2135467`: its descent set, adoptable intervals, its seven matchings
`M_1, …, M_7`, and its matching, homogeneous fiber and fiber descent polynomials.

## Main definitions

* `matching2135467`: the seven matchings `M_1, …, M_7` of `2135467`, indexed by `Fin 7`.

## Main results

* `IsAncestorOrSelf.trans`, `IsStrictAncestor.lt`,
  `subtreeVertices_subset_or_subset_of_inter_nonempty`: the forest of a parent map.
* `List.filter_isAdoptablePair_Ico_eq_Ico`: `{a ∈ [b - 1] : (a, b) adoptable} = [ℓ_b, b - 1]`.
* `List.adoptableInterval_subset_of_mem_of_lt`: adoptable intervals are nested.
* `List.subtreeVertices_adoptableForest`: the subtree of `𝓕_π` rooted at `b` is `I_b`.
* `List.isPostorderForest_adoptableForest`: `𝓕_π` is a postorder forest.
* `List.isAdoptablePair_iff_isStrictAncestor`: adoptable pairs are strict ancestor relations.
* `List.isLeaf_adoptableForest_of_mem_descentSet`: descents are leaves of `𝓕_π`.
* `List.fiberMatchings_eq_setOf_isAdoptablePair`,
  `List.fiberMatchings_eq_setOf_isAdmissibleMatching`: `𝒜(π)` via adoptable pairs and as the
  admissible matchings of `(𝓕_π, Des(π))`.
* `List.fiberMatchings_2135467`, `List.fiberMatchingPolynomial_2135467`,
  `List.fiberHomogPolynomial_2135467`, `List.fiberDescentPolynomial_2135467`: the running
  example.

## Implementation notes

The paper states the lemmas on adoptable pairs and the adoptable forest for `π ∈ S_n` with
`n ≥ 1`. Their arguments use only the combinatorics of adoptable pairs, so they are stated for an
arbitrary list over a preorder, with `n = π.length`; only the results on the matchings `𝒜(π)`
need `π` to be a permutation. Likewise the facts about parent maps hold for every
`par : ℕ → Option ℕ` and need the parent-map hypothesis only where the labels must increase.
Positions are `1`-indexed as in the paper, so `π_a` is `π[a - 1]`.

The example identities, stated over `ℝ` in the paper, are stated over an arbitrary
(commutative) semiring, since their coefficients are natural numbers.

## References

* [LogNarayana] *Log-Concavity in Narayana Transforms and Stack-Sorting Fibers*, Sections 3, 5
  and 6, Example 3.3.
-/

/-! ### Forests of parent maps -/

/-- The iterates of `o ↦ o.bind par` fix `none`. -/
private theorem iterate_bind_none (par : ℕ → Option ℕ) (k : ℕ) :
    (fun o : Option ℕ => o.bind par)^[k] none = none :=
  Function.iterate_fixed rfl k

/-- A parent is an ancestor-or-self. -/
private theorem isAncestorOrSelf_of_eq_some {par : ℕ → Option ℕ} {u w : ℕ}
    (h : par u = some w) : IsAncestorOrSelf par w u :=
  ⟨1, by simpa using h⟩

/-- The ancestor-or-self relation `⪰` of a parent map is transitive: if `w ⪰ v` and `v ⪰ u`,
then `w ⪰ u`. -/
@[lognarayana "lem_forest_ancestor_trans"]
public theorem IsAncestorOrSelf.trans {par : ℕ → Option ℕ} {u v w : ℕ}
    (hwv : IsAncestorOrSelf par w v) (hvu : IsAncestorOrSelf par v u) :
    IsAncestorOrSelf par w u := by
  obtain ⟨j, hj⟩ := hwv
  obtain ⟨i, hi⟩ := hvu
  exact ⟨j + i, by rw [Function.iterate_add_apply, hi, hj]⟩

/-- In the forest of a parent map, an ancestor-or-self of `v` has label at least `v`:
each application of `par` strictly increases the label. -/
private theorem le_of_isAncestorOrSelf {N : ℕ} {par : ℕ → Option ℕ} (hpar : IsParentMap N par)
    {u v : ℕ} (h : IsAncestorOrSelf par u v) : v ≤ u := by
  obtain ⟨k, hk⟩ := h
  induction k generalizing u with
  | zero => simp_all
  | succ k ih =>
    rw [Function.iterate_succ_apply'] at hk
    cases hx : (fun o : Option ℕ => o.bind par)^[k] (some v) with
    | none => simp [hx] at hk
    | some x => exact (ih hx).trans (hpar x u (by simpa [hx] using hk)).2.1.le

/-- If `par` is a parent map on `[N]` and `v` is a strict ancestor of `u`, then `u < v`. -/
@[lognarayana "lem_forest_strict_ancestor_lt"]
public theorem IsStrictAncestor.lt {N : ℕ} {par : ℕ → Option ℕ} (hpar : IsParentMap N par)
    {u v : ℕ} (h : IsStrictAncestor par v u) : u < v :=
  (le_of_isAncestorOrSelf hpar h.1).lt_of_ne h.2.symm

/-- A strict ancestor relation `v ≻ u` in a parent map on `[N]` forces `1 ≤ u` (the first step
leaves `u`) and `v ≤ N` (the last step lands on `v`). -/
private theorem IsStrictAncestor.one_le_and_le {N : ℕ} {par : ℕ → Option ℕ}
    (hpar : IsParentMap N par) {u v : ℕ} (h : IsStrictAncestor par v u) : 1 ≤ u ∧ v ≤ N := by
  obtain ⟨⟨_ | k, hk⟩, hne⟩ := h
  · exact absurd (Option.some_injective _ hk).symm hne
  constructor
  · rw [Function.iterate_succ_apply] at hk
    cases hpu : par u with
    | none => simp [hpu, iterate_bind_none] at hk
    | some p => exact (hpar u p hpu).1
  · rw [Function.iterate_succ_apply'] at hk
    obtain ⟨w, -, hw⟩ := Option.bind_eq_some_iff.1 hk
    exact (hpar w v hw).2.2

/-- If `v ⪰ u`, then `V_u ⊆ V_v`. -/
private theorem subtreeVertices_subset {N : ℕ} {par : ℕ → Option ℕ} {u v : ℕ}
    (h : IsAncestorOrSelf par v u) : subtreeVertices N par u ⊆ subtreeVertices N par v := by
  intro t ht
  simp only [subtreeVertices, Finset.mem_filter] at ht ⊢
  exact ⟨ht.1, h.trans ht.2⟩

/-- If the subtree vertex sets `V_u` and `V_v` of a parent map meet, they are nested:
`V_u ⊆ V_v` or `V_v ⊆ V_u`. A common vertex `w` reaches `u` and `v` in `i` and `j` steps, and the
one reached later is an ancestor-or-self of the other. -/
@[lognarayana "lem_forest_subtrees_nested"]
public theorem subtreeVertices_subset_or_subset_of_inter_nonempty {N : ℕ}
    {par : ℕ → Option ℕ} {u v : ℕ}
    (h : (subtreeVertices N par u ∩ subtreeVertices N par v).Nonempty) :
    subtreeVertices N par u ⊆ subtreeVertices N par v ∨
      subtreeVertices N par v ⊆ subtreeVertices N par u := by
  obtain ⟨w, hw⟩ := h
  simp only [Finset.mem_inter, subtreeVertices, Finset.mem_filter] at hw
  obtain ⟨⟨-, i, hi⟩, -, j, hj⟩ := hw
  have key : ∀ {i j u v}, (fun o : Option ℕ => o.bind par)^[i] (some w) = some u →
      (fun o : Option ℕ => o.bind par)^[j] (some w) = some v → i ≤ j →
      IsAncestorOrSelf par v u := fun hi hj hij =>
    ⟨_ - _, by rw [← hi, ← Function.iterate_add_apply, Nat.sub_add_cancel hij, hj]⟩
  rcases le_total i j with hij | hij
  · exact Or.inl (subtreeVertices_subset (key hi hj hij))
  · exact Or.inr (subtreeVertices_subset (key hj hi hij))

/-! ### Adoptable pairs and adoptable intervals -/

namespace List

section Preorder

variable {α : Type*} [Preorder α]

/-- If `(a, b)` is adoptable with respect to `π`, then `π_a < π_{b+1}` (positions `1`-indexed). -/
@[lognarayana "lem_adoptable_weak"]
public theorem IsAdoptablePair.getElem_lt {π : List α} {a b : ℕ} (h : π.IsAdoptablePair a b) :
    ∃ (ha : a - 1 < π.length) (hb : b < π.length), π[a - 1] < π[b] := by
  obtain ⟨h1, hab, hb, -, hlt⟩ := h
  exact ⟨by omega, hb, hlt a le_rfl hab.le⟩

/-- If `(a, c)` and `(b, d)` are adoptable pairs of `π` with `b ≤ c < d`, then `(a, d)` is
adoptable: `π_{c+1} ≤ π_d` because `(b, d)` is adoptable, so every entry from position `a` through
`c` lies below `π_d`. -/
@[lognarayana "lem_adoptable_concat"]
public theorem IsAdoptablePair.concat {π : List α} {a b c d : ℕ} (hac : π.IsAdoptablePair a c)
    (hbd : π.IsAdoptablePair b d) (hbc : b ≤ c) (hcd : c < d) :
    π.IsAdoptablePair a d := by
  obtain ⟨ha1, hac', hc, P1, Q1⟩ := hac
  obtain ⟨hb1, hbd', hd, P2, Q2⟩ := hbd
  have key : π[c] ≤ π[d - 1] := by simpa using P2 (c + 1) (by omega) (by omega)
  have hdd : π[d - 1] < π[d] := Q2 d (by omega) le_rfl
  refine ⟨ha1, by omega, hd, fun i hi hid => ?_, fun i hi hid => ?_⟩
  · by_cases hic : i ≤ c
    · exact ((Q1 i (by omega) hic).trans_le key).le
    · exact P2 i (by omega) hid
  · by_cases hib : b ≤ i
    · exact Q2 i hib hid
    · exact (Q1 i hi (by omega)).trans_le key |>.trans hdd

/-- Adoptability of `(a, b)` is inherited by `(a', b)` for `a ≤ a' < b`. -/
private theorem IsAdoptablePair.of_le {π : List α} {a a' b : ℕ} (h : π.IsAdoptablePair a b)
    (haa' : a ≤ a') (ha'b : a' < b) : π.IsAdoptablePair a' b := by
  obtain ⟨h1, -, hb, hmax, hlt⟩ := h
  exact ⟨h1.trans haa', ha'b, hb, fun i hi hib => hmax i (by omega) hib,
    fun i hi hib => hlt i (by omega) hib⟩

/-- `ℓ_b ≤ b`. -/
private theorem adoptableLeftBound_le_self (π : List α) (b : ℕ) : π.adoptableLeftBound b ≤ b :=
  Finset.min'_le _ _ (Finset.mem_insert_self _ _)

/-- `ℓ_b` is at most every `a` with `(a, b)` adoptable. -/
private theorem adoptableLeftBound_le {π : List α} {a b : ℕ} (h : π.IsAdoptablePair a b) :
    π.adoptableLeftBound b ≤ a := by
  classical
  exact Finset.min'_le _ _
    (Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨Finset.mem_Ico.2 ⟨h.1, h.2.1⟩, h⟩))

/-- `ℓ_b` is either `b` itself or an adoptable left endpoint for `b`. -/
private theorem adoptableLeftBound_eq_or_isAdoptablePair (π : List α) (b : ℕ) :
    π.adoptableLeftBound b = b ∨ π.IsAdoptablePair (π.adoptableLeftBound b) b := by
  classical
  have := Finset.min'_mem _
    (Finset.insert_nonempty b ((Finset.Ico 1 b).filter (π.IsAdoptablePair · b)))
  simp only [Finset.mem_insert, Finset.mem_filter] at this
  exact this.imp id And.right

/-- `1 ≤ ℓ_b` when `1 ≤ b`. -/
private theorem one_le_adoptableLeftBound (π : List α) {b : ℕ} (hb : 1 ≤ b) :
    1 ≤ π.adoptableLeftBound b := by
  rcases adoptableLeftBound_eq_or_isAdoptablePair π b with h | h
  · omega
  · exact h.1

open Classical in
/-- The left endpoints `a ∈ [b - 1]` of the adoptable pairs `(a, b)` of `π` form the interval
`[ℓ_b, b - 1]`, where `ℓ_b = π.adoptableLeftBound b`: adoptability of `(a, b)` passes to
`(a', b)` for `a ≤ a' < b`, and `ℓ_b` is the least adoptable left endpoint. -/
@[lognarayana "lem_adoptable_left_interval"]
public theorem filter_isAdoptablePair_Ico_eq_Ico (π : List α) (b : ℕ) :
    (Finset.Ico 1 b).filter (fun a => π.IsAdoptablePair a b) =
      Finset.Ico (π.adoptableLeftBound b) b := by
  ext a
  simp only [Finset.mem_filter, Finset.mem_Ico]
  refine ⟨fun ⟨⟨_, hab⟩, h⟩ => ⟨adoptableLeftBound_le h, hab⟩, fun ⟨hla, hab⟩ => ?_⟩
  rcases adoptableLeftBound_eq_or_isAdoptablePair π b with h | h
  · omega
  · exact ⟨⟨h.1.trans hla, hab⟩, h.of_le hla hab⟩

/-- `(a, b)` is adoptable exactly when `a` lies in `[ℓ_b, b - 1]`. -/
private theorem isAdoptablePair_iff_mem_Ico (π : List α) (a b : ℕ) :
    π.IsAdoptablePair a b ↔ a ∈ Finset.Ico (π.adoptableLeftBound b) b := by
  classical
  rw [← filter_isAdoptablePair_Ico_eq_Ico, Finset.mem_filter, Finset.mem_Ico]
  exact ⟨fun h => ⟨⟨h.1, h.2.1⟩, h⟩, And.right⟩

/-- Adoptable intervals are nested: if `c ∈ I_b` and `c < b`, then `I_c ⊆ I_b`. Either
`ℓ_c = c`, or an adoptable pair `(ℓ_c, c)` with `ℓ_c < ℓ_b` would concatenate with `(ℓ_b, b)` to
`(ℓ_c, b)`, against the minimality of `ℓ_b`. -/
@[lognarayana "lem_adoptable_intervals_nested"]
public theorem adoptableInterval_subset_of_mem_of_lt {π : List α} {b c : ℕ}
    (hc : c ∈ π.adoptableInterval b) (hcb : c < b) :
    π.adoptableInterval c ⊆ π.adoptableInterval b := by
  have hbc := (Finset.mem_Icc.1 hc).1
  refine Finset.Icc_subset_Icc ?_ hcb.le
  rcases adoptableLeftBound_eq_or_isAdoptablePair π c with h | h
  · omega
  rcases adoptableLeftBound_eq_or_isAdoptablePair π b with h' | h'
  · omega
  by_contra! hlt
  have := adoptableLeftBound_le (h.concat h' hbc hcb)
  omega

/-! ### The adoptable forest -/

/-- `b ∈ I_b`. -/
private theorem self_mem_adoptableInterval (π : List α) (b : ℕ) : b ∈ π.adoptableInterval b :=
  Finset.mem_Icc.2 ⟨adoptableLeftBound_le_self π b, le_rfl⟩

/-- The parent of `u` in the adoptable forest lies in `[u + 1, π.length - 1]`, and its adoptable
interval contains `u`. -/
private theorem of_adoptableForest_eq_some {π : List α} {u w : ℕ}
    (h : π.adoptableForest u = some w) :
    u + 1 ≤ w ∧ w ≤ π.length - 1 ∧ u ∈ π.adoptableInterval w := by
  unfold adoptableForest at h
  split_ifs at h with hne
  cases h
  have hm := Finset.min'_mem _ hne
  rw [Finset.mem_filter, Finset.mem_Icc] at hm
  exact ⟨hm.1.1, hm.1.2, hm.2⟩

/-- If `u ∈ I_b` with `u < b ≤ π.length - 1`, then `u` has a parent `w ≤ b`. -/
private theorem exists_adoptableForest_eq_some {π : List α} {u b : ℕ}
    (hu : u ∈ π.adoptableInterval b) (hub : u < b) (hb : b ≤ π.length - 1) :
    ∃ w, π.adoptableForest u = some w ∧ w ≤ b := by
  have hmem : b ∈ (Finset.Icc (u + 1) (π.length - 1)).filter (u ∈ π.adoptableInterval ·) :=
    Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨hub, hb⟩, hu⟩
  exact ⟨_, by rw [adoptableForest, dif_pos ⟨b, hmem⟩], Finset.min'_le _ _ hmem⟩

/-- The adoptable forest is a parent map on `[π.length - 1]`: a parent `p` of `a` satisfies
`a + 1 ≤ p ≤ π.length - 1` and `a ∈ I_p`, so `a ≥ ℓ_p ≥ 1`. -/
private theorem isParentMap_adoptableForest (π : List α) :
    IsParentMap (π.length - 1) π.adoptableForest := fun a p hp => by
  obtain ⟨h₁, h₂, h₃⟩ := of_adoptableForest_eq_some hp
  exact ⟨(one_le_adoptableLeftBound π (by omega)).trans (Finset.mem_Icc.1 h₃).1, h₁, h₂⟩

/-- `V_b ⊆ I_b`: every descendant of `b` in the adoptable forest lies in `I_b`. Each parent step
`u ↦ w` has `u ∈ I_w`, and the intervals along the path to `b` are nested. -/
private theorem mem_adoptableInterval_of_isAncestorOrSelf {π : List α} {b u : ℕ}
    (h : IsAncestorOrSelf π.adoptableForest b u) : u ∈ π.adoptableInterval b := by
  obtain ⟨k, hk⟩ := h
  induction k generalizing u with
  | zero =>
    cases hk
    exact self_mem_adoptableInterval π b
  | succ k ih =>
    cases hpu : π.adoptableForest u with
    | none => simp [Function.iterate_succ_apply, hpu, iterate_bind_none] at hk
    | some w =>
      simp only [Function.iterate_succ_apply, Option.bind_some, hpu] at hk
      have hw := ih hk
      have huw := (of_adoptableForest_eq_some hpu).2.2
      rcases eq_or_ne w b with rfl | hne
      · exact huw
      · exact adoptableInterval_subset_of_mem_of_lt hw
          (lt_of_le_of_ne (Finset.mem_Icc.1 hw).2 hne) huw

/-- `I_b ⊆ V_b`: for `b ≤ π.length - 1`, `b` is an ancestor-or-self of every `u ∈ I_b`. The
parent `w` of `u < b` satisfies `u < w ≤ b`, so `w ∈ I_b` and we recurse on `b - u`. -/
private theorem isAncestorOrSelf_of_mem_adoptableInterval {π : List α} {b u : ℕ}
    (hu : u ∈ π.adoptableInterval b) (hb : b ≤ π.length - 1) :
    IsAncestorOrSelf π.adoptableForest b u := by
  rcases eq_or_lt_of_le (Finset.mem_Icc.1 hu).2 with rfl | hub
  · exact ⟨0, rfl⟩
  obtain ⟨w, hpw, hwb⟩ := exists_adoptableForest_eq_some hu hub hb
  have hwu := (of_adoptableForest_eq_some hpw).1
  have hw : w ∈ π.adoptableInterval b :=
    Finset.mem_Icc.2 ⟨(Finset.mem_Icc.1 hu).1.trans (by omega), hwb⟩
  exact (isAncestorOrSelf_of_mem_adoptableInterval hw hb).trans (isAncestorOrSelf_of_eq_some hpw)
termination_by b - u

/-- In the adoptable forest of `π`, the subtree rooted at `b ∈ [π.length - 1]` has vertex set
the adoptable interval `I_b`: `V_b = I_b`. -/
@[lognarayana "lem_adoptable_forest_subtree"]
public theorem subtreeVertices_adoptableForest (π : List α) {b : ℕ} (hb₁ : 1 ≤ b)
    (hb₂ : b ≤ π.length - 1) :
    subtreeVertices (π.length - 1) π.adoptableForest b = π.adoptableInterval b := by
  classical
  ext u
  rw [subtreeVertices, Finset.mem_filter, Finset.mem_Icc]
  refine ⟨fun h => mem_adoptableInterval_of_isAncestorOrSelf h.2, fun hu => ⟨?_,
    isAncestorOrSelf_of_mem_adoptableInterval hu hb₂⟩⟩
  have hu' := Finset.mem_Icc.1 hu
  exact ⟨(one_le_adoptableLeftBound π hb₁).trans hu'.1, hu'.2.trans hb₂⟩

/-- The adoptable forest of `π` is a postorder forest on `[π.length - 1]`: the subtree rooted at
`v` is `I_v = [ℓ_v, v]`, of cardinality `v + 1 - ℓ_v`. -/
@[lognarayana "lem_adoptable_forest_postorder"]
public theorem isPostorderForest_adoptableForest (π : List α) :
    IsPostorderForest (π.length - 1) π.adoptableForest := by
  refine ⟨isParentMap_adoptableForest π, fun v hv => ?_⟩
  obtain ⟨hv₁, hv₂⟩ := Finset.mem_Icc.1 hv
  rw [subtreeVertices_adoptableForest π hv₁ hv₂, adoptableInterval, Nat.card_Icc,
    Nat.sub_sub_self (Nat.le_succ_of_le (adoptableLeftBound_le_self π v))]

/-- `(a, b)` is adoptable with respect to `π` if and only if `b` is a strict ancestor of `a` in
the adoptable forest of `π`. Both directions pass through `V_b = I_b` and the description
`[ℓ_b, b - 1]` of the adoptable left endpoints. -/
@[lognarayana "lem_adoptable_iff_ancestor"]
public theorem isAdoptablePair_iff_isStrictAncestor (π : List α) (a b : ℕ) :
    π.IsAdoptablePair a b ↔ IsStrictAncestor π.adoptableForest b a := by
  classical
  have hpar := isParentMap_adoptableForest π
  constructor
  · intro h
    obtain ⟨ha, -, hb, -⟩ := id h
    rw [isAdoptablePair_iff_mem_Ico, Finset.mem_Ico] at h
    have hV : a ∈ subtreeVertices (π.length - 1) π.adoptableForest b := by
      rw [subtreeVertices_adoptableForest π (by omega) (by omega), adoptableInterval,
        Finset.mem_Icc]
      omega
    exact ⟨(Finset.mem_filter.1 hV).2, h.2.ne'⟩
  · intro h
    have hab := h.lt hpar
    obtain ⟨ha, hbn⟩ := IsStrictAncestor.one_le_and_le hpar h
    have hV : a ∈ subtreeVertices (π.length - 1) π.adoptableForest b :=
      Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨ha, by omega⟩, h.1⟩
    rw [subtreeVertices_adoptableForest π (by omega) hbn, adoptableInterval,
      Finset.mem_Icc] at hV
    exact (isAdoptablePair_iff_mem_Ico π a b).2 (Finset.mem_Ico.2 ⟨hV.1, hab⟩)

/-- Every descent `b ∈ Des(π)` is a leaf of the adoptable forest of `π`. No pair `(a, b)` is
adoptable, since adoptability forces `π_b < π_{b+1}`; hence `ℓ_b = b`, and no vertex `u < b`
lies in `I_b`. -/
@[lognarayana "lem_adoptable_forest_descent_leaf"]
public theorem isLeaf_adoptableForest_of_mem_descentSet [DecidableRel (α := α) (· < ·)]
    (π : List α) {b : ℕ} (hb : b ∈ π.descentSet) : IsLeaf π.adoptableForest b := fun u hu => by
  unfold descentSet at hb
  obtain ⟨-, _, hdes⟩ := Finset.mem_filter.1 hb
  have hℓ : π.adoptableLeftBound b = b :=
    (adoptableLeftBound_eq_or_isAdoptablePair π b).resolve_right fun h =>
      lt_asymm hdes (h.2.2.2.2 b h.2.1.le le_rfl)
  obtain ⟨h₁, -, h₃⟩ := of_adoptableForest_eq_some hu
  have := (Finset.mem_Icc.1 h₃).1
  omega

end Preorder

end List

/-! ### Matchings of a permutation -/

section FiberMatchings

open BinaryTree

/-- The one-step "is a child subtree of" relation. -/
private abbrev ChildRel (α : Type*) : BinaryTree α → BinaryTree α → Prop :=
  fun S U => ∃ m L R, U = node m L R ∧ (S = L ∨ S = R)

/-- The postorder of a subtree is a factor of the postorder. -/
private theorem postorder_infix_of_reflTransGen {α : Type*} {S T : BinaryTree α}
    (h : Relation.ReflTransGen (ChildRel α) S T) :
    ∃ u v, T.postorder = u ++ S.postorder ++ v := by
  induction h with
  | refl => exact ⟨[], [], by simp⟩
  | tail _ hUW ih =>
    obtain ⟨u, v, huv⟩ := ih
    obtain ⟨m, L, R, rfl, rfl | rfl⟩ := hUW
    · exact ⟨u, v ++ R.postorder ++ [m], by simp [huv]⟩
    · exact ⟨L.postorder ++ u, v ++ [m], by simp [huv]⟩

/-- A subtree of a decreasing tree is decreasing. -/
private theorem isDecreasing_of_reflTransGen {α : Type*} [DecidableEq α] [LT α]
    {S T : BinaryTree α} (h : Relation.ReflTransGen (ChildRel α) S T)
    (hT : T.IsDecreasing) : S.IsDecreasing := by
  induction h with
  | refl => exact hT
  | tail _ hUW ih =>
    obtain ⟨m, L, R, rfl, rfl | rfl⟩ := hUW
    · exact ih hT.1
    · exact ih hT.2.1

/-- The letters of the postorder reading are the labels. -/
private theorem mem_postorder_iff_mem_labels {α : Type*} [DecidableEq α] {T : BinaryTree α}
    {x : α} : x ∈ T.postorder ↔ x ∈ T.labels := by
  induction T with
  | nil => simp
  | node m l r ihl ihr =>
    simp [ihl, ihr]
    tauto

/-- In a list without repeated letters, a letter sits at only one position. -/
private theorem eq_of_getElem?_eq_some_of_nodup {α : Type*} {l : List α} (hnd : l.Nodup)
    {i j : ℕ} {z : α} (hi : l[i]? = some z) (hj : l[j]? = some z) : i = j := by
  obtain ⟨h1, e1⟩ := List.getElem?_eq_some_iff.mp hi
  obtain ⟨h2, e2⟩ := List.getElem?_eq_some_iff.mp hj
  exact hnd.getElem_inj_iff.mp (e1.trans e2.symm)

/-- Every pair `(a, b)` of a matching `M ∈ 𝒜(π)` of a permutation `π ∈ S_n` is adoptable with
respect to `π`. By `BinaryTree.bijOn_treeMatching_treeRightChoices`, `M = M(T)` for a decreasing
tree `T` with postorder `π`; a pair `(a, b) ∈ M(T)` is a subtree
`⟨π_{b+1}; ⟨π_a; L₁, L₂⟩, ⟨d; R₁, R₂⟩⟩` of `T`, whose postorder sits at positions `a, …, b + 1`
of `π` since `π` has no repeated letters, with `d = π_b`. The decreasing condition then gives
both inequalities. -/
@[lognarayana "lem_fiber_matching_adoptable"]
public theorem List.isAdoptablePair_of_mem_fiberMatchings {n : ℕ} {π : List ℕ}
    (hπ : π ∈ permWords n) {M : Finset (ℕ × ℕ)} (hM : M ∈ π.fiberMatchings) {a b : ℕ}
    (hab : (a, b) ∈ M) : π.IsAdoptablePair a b := by
  classical
  have hnd := hπ.1.1
  obtain ⟨-, hblen, -⟩ := hM.2.2 (a, b) hab
  have hlen := hπ.2.1
  have hn : 1 ≤ n := by simp only at hblen; omega
  obtain ⟨T, ⟨⟨hTdec, -⟩, rfl⟩, hTM⟩ :=
    (bijOn_treeMatching_treeRightChoices hn hπ).surjOn
      (show (M, (∅ : Finset ℕ)) ∈ _ from ⟨hM, Finset.empty_subset _⟩)
  have hTM1 : T.treeMatching = M := congrArg Prod.fst hTM
  rw [← hTM1, treeMatching, Finset.mem_filter] at hab
  obtain ⟨hmem, ha2, hb2, L₁, L₂, d, R₁, R₂, hS⟩ := hab
  simp only [Finset.mem_product, Finset.mem_Icc] at hmem ha2 hb2 hS
  obtain ⟨u, v, huv⟩ := postorder_infix_of_reflTransGen hS
  have hdec := isDecreasing_of_reflTransGen hS hTdec
  generalize hx : T.postorder[b] = x at hS huv hdec
  generalize hy : T.postorder[a - 1] = y at hS huv hdec
  set w := T.postorder with hw
  set A := u ++ L₁.postorder ++ L₂.postorder
  set B := R₁.postorder ++ R₂.postorder ++ [d]
  have heq : w = A ++ y :: (B ++ x :: v) := by rw [huv]; simp [A, B]
  have hyA : w[A.length]? = some y := by rw [heq]; simp
  have hxB : w[A.length + 1 + B.length]? = some x := by
    rw [heq, List.getElem?_append_right (by omega)]
    simp [show A.length + 1 + B.length - A.length = B.length + 1 by omega]
  have hA : A.length = a - 1 :=
    eq_of_getElem?_eq_some_of_nodup hnd hyA (by rw [← hy]; exact List.getElem?_eq_getElem _)
  have hB : A.length + 1 + B.length = b :=
    eq_of_getElem?_eq_some_of_nodup hnd hxB (by rw [← hx]; exact List.getElem?_eq_getElem _)
  have hBmem : ∀ j, a ≤ j → j < b → ∀ (h : j < w.length), w[j] ∈ B := by
    intro j hj1 hj2 h
    have : w[j]? = B[j - a]? := by
      rw [heq, List.getElem?_append_right (by omega), List.getElem?_cons,
        if_neg (by omega), List.getElem?_append_left (by omega)]
      congr 1; omega
    rw [List.getElem?_eq_getElem h] at this
    exact List.mem_of_getElem? this.symm
  have hBpos : 0 < B.length := by simp [B]
  have hd : w[b - 1]? = some d := by
    rw [heq, List.getElem?_append_right (by omega), List.getElem?_cons, if_neg (by omega),
      List.getElem?_append_left (by omega)]
    simp [B, show b - 1 - A.length - 1 = R₁.postorder.length + R₂.postorder.length by
      simp only [B, List.length_append, List.length_singleton] at hB; omega]
  obtain ⟨⟨-, -, -, -⟩, ⟨-, -, -, hRd⟩, -, hlt⟩ := hdec
  have hBd : ∀ z ∈ B, z ≤ d := by
    intro z hz
    simp only [B, List.mem_append, List.mem_singleton, mem_postorder_iff_mem_labels] at hz
    rcases hz with (hz | hz) | rfl
    · exact (hRd z (Finset.mem_union_left _ hz)).le
    · exact (hRd z (Finset.mem_union_right _ hz)).le
    · exact le_rfl
  have hBx : ∀ z ∈ B, z < x := fun z hz => by
    apply hlt
    simp only [B, List.mem_append, List.mem_singleton, mem_postorder_iff_mem_labels] at hz
    simp only [labels, Finset.mem_union, Finset.mem_singleton]
    tauto
  refine ⟨hmem.1.1, by omega, hb2, fun i hi1 hi2 => ?_, fun i hi1 hi2 => ?_⟩
  · rw [(List.getElem?_eq_some_iff.mp hd).2]
    exact hBd _ (hBmem _ (by omega) (by omega) _)
  · rw [hx]
    rcases eq_or_lt_of_le hi1 with rfl | hi1
    · rw [hy]; exact hlt y (by simp)
    · exact hBx _ (hBmem _ (by omega) (by omega) _)

end FiberMatchings

namespace List

/-- For a permutation `π ∈ S_n`, the set `𝒜(π)` of matchings of `π` is the set of noncrossing
partial matchings `M` on `[n - 1]` with `Des(π) ⊆ LE(M)` such that every pair of `M` is adoptable
with respect to `π`: the pairs of a matching of `π` are adoptable, and an adoptable pair `(a, b)`
satisfies `π_a < π_{b+1}`. -/
@[lognarayana "lem_fiber_matchings_eq_adoptable"]
public theorem fiberMatchings_eq_setOf_isAdoptablePair {n : ℕ} {π : List ℕ}
    (hπ : π ∈ permWords n) :
    π.fiberMatchings =
      {M | IsNoncrossingPartialMatching (n - 1) M ∧ π.descentSet ⊆ M.leftEndpoints ∧
        ∀ p ∈ M, π.IsAdoptablePair p.1 p.2} := by
  ext M
  refine ⟨fun hM => ⟨hπ.2.1 ▸ hM.1, hM.2.1,
    fun p hp => isAdoptablePair_of_mem_fiberMatchings hπ hM hp⟩, ?_⟩
  rintro ⟨h1, h2, h3⟩
  exact ⟨hπ.2.1 ▸ h1, h2, fun p hp => (h3 p hp).getElem_lt⟩

/-- For `π ∈ S_n`, the matchings `𝒜(π)` of `π` are exactly the admissible matchings on `[n - 1]`
for the adoptable forest of `π` with marked set `Des(π)`. -/
@[lognarayana "lem_fiber_matchings_admissible"]
public theorem fiberMatchings_eq_setOf_isAdmissibleMatching {n : ℕ} {π : List ℕ}
    (hπ : π ∈ permWords n) :
    π.fiberMatchings = {M | IsAdmissibleMatching (n - 1) π.adoptableForest π.descentSet M} := by
  rw [fiberMatchings_eq_setOf_isAdoptablePair hπ]
  ext M
  simp only [Set.mem_ofPred_eq, isAdoptablePair_iff_isStrictAncestor]
  exact ⟨fun ⟨h₁, h₂, h₃⟩ => ⟨h₁, h₃, h₂⟩, fun h => ⟨h.1, h.3, h.2⟩⟩

end List

/-! ### The running example `2135467` -/

/-- The sizes of the seven matchings `M_1, …, M_7`. -/
private theorem card_matching2135467 (i : Fin 7) :
    (matching2135467 i).card = ![2, 2, 2, 2, 2, 3, 3] i := by
  revert i; decide

namespace List

/-- The descent set of the permutation `2135467 ∈ S_7` is `{1, 4}`. -/
@[lognarayana "lem_ex_descent_set"]
public theorem descentSet_2135467 : descentSet [2, 1, 3, 5, 4, 6, 7] = {1, 4} := by
  decide

/-- Adoptability for a list of naturals, with the index ranges as finsets, so that it is
decidable by evaluation. -/
private theorem isAdoptablePair_iff_getD (π : List ℕ) (a b : ℕ) :
    π.IsAdoptablePair a b ↔ 1 ≤ a ∧ a < b ∧ b < π.length ∧
      (∀ i ∈ Finset.Ioc a b, π.getD (i - 1) 0 ≤ π.getD (b - 1) 0) ∧
      ∀ i ∈ Finset.Icc a b, π.getD (i - 1) 0 < π.getD b 0 := by
  unfold IsAdoptablePair
  constructor
  · rintro ⟨h1, h2, hb, h3, h4⟩
    refine ⟨h1, h2, hb, fun i hi => ?_, fun i hi => ?_⟩
    · rw [Finset.mem_Ioc] at hi
      rw [getD_eq_getElem _ _ (by omega), getD_eq_getElem _ _ (by omega)]
      exact h3 i hi.1 hi.2
    · rw [Finset.mem_Icc] at hi
      rw [getD_eq_getElem _ _ (by omega), getD_eq_getElem _ _ hb]
      exact h4 i hi.1 hi.2
  · rintro ⟨h1, h2, hb, h3, h4⟩
    refine ⟨h1, h2, hb, fun i hi hi' => ?_, fun i hi hi' => ?_⟩
    · have := h3 i (Finset.mem_Ioc.2 ⟨hi, hi'⟩)
      rwa [getD_eq_getElem _ _ (by omega), getD_eq_getElem _ _ (by omega)] at this
    · have := h4 i (Finset.mem_Icc.2 ⟨hi, hi'⟩)
      rwa [getD_eq_getElem _ _ (by omega), getD_eq_getElem _ _ hb] at this

/-- The adoptable intervals of `2135467 ∈ S_7`: `I_1 = {1}`, `I_2 = [1, 2]`, `I_3 = [1, 3]`,
`I_4 = {4}`, `I_5 = [4, 5]`, `I_6 = [1, 6]`. -/
@[lognarayana "lem_ex_adoptable_intervals"]
public theorem adoptableInterval_2135467 :
    adoptableInterval [2, 1, 3, 5, 4, 6, 7] 1 = {1} ∧
    adoptableInterval [2, 1, 3, 5, 4, 6, 7] 2 = Finset.Icc 1 2 ∧
    adoptableInterval [2, 1, 3, 5, 4, 6, 7] 3 = Finset.Icc 1 3 ∧
    adoptableInterval [2, 1, 3, 5, 4, 6, 7] 4 = {4} ∧
    adoptableInterval [2, 1, 3, 5, 4, 6, 7] 5 = Finset.Icc 4 5 ∧
    adoptableInterval [2, 1, 3, 5, 4, 6, 7] 6 = Finset.Icc 1 6 := by
  simp only [adoptableInterval, adoptableLeftBound, isAdoptablePair_iff_getD]
  decide

/-- The adoptable pairs of `2135467`. -/
private def adoptablePairs2135467 : Finset (ℕ × ℕ) :=
  {(1, 2), (1, 3), (2, 3), (4, 5), (1, 6), (2, 6), (3, 6), (4, 6), (5, 6)}

/-- The left bound `ℓ_b` is read off the adoptable interval `I_b = [ℓ_b, b]`. -/
private theorem adoptableLeftBound_eq_of_adoptableInterval_eq {α : Type*} [Preorder α]
    {π : List α} {b c : ℕ} (h : π.adoptableInterval b = Finset.Icc c b) :
    π.adoptableLeftBound b = c :=
  ((Set.Icc_eq_Icc_iff (adoptableLeftBound_le_self π b)).1
    (by rw [← Finset.coe_Icc, ← Finset.coe_Icc, ← h])).1

/-- The left bounds `ℓ_1, …, ℓ_6` of `2135467`, read off its adoptable intervals. -/
private theorem adoptableLeftBound_2135467 :
    [2, 1, 3, 5, 4, 6, 7].adoptableLeftBound 1 = 1 ∧
    [2, 1, 3, 5, 4, 6, 7].adoptableLeftBound 2 = 1 ∧
    [2, 1, 3, 5, 4, 6, 7].adoptableLeftBound 3 = 1 ∧
    [2, 1, 3, 5, 4, 6, 7].adoptableLeftBound 4 = 4 ∧
    [2, 1, 3, 5, 4, 6, 7].adoptableLeftBound 5 = 4 ∧
    [2, 1, 3, 5, 4, 6, 7].adoptableLeftBound 6 = 1 := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := adoptableInterval_2135467
  rw [← Finset.Icc_self] at h1 h4
  exact ⟨adoptableLeftBound_eq_of_adoptableInterval_eq h1,
    adoptableLeftBound_eq_of_adoptableInterval_eq h2,
    adoptableLeftBound_eq_of_adoptableInterval_eq h3,
    adoptableLeftBound_eq_of_adoptableInterval_eq h4,
    adoptableLeftBound_eq_of_adoptableInterval_eq h5,
    adoptableLeftBound_eq_of_adoptableInterval_eq h6⟩

/-- The adoptable pairs `(a, b)` of `2135467` are those with `ℓ_b ≤ a < b`. -/
private theorem isAdoptablePair_2135467_iff (p : ℕ × ℕ) :
    [2, 1, 3, 5, 4, 6, 7].IsAdoptablePair p.1 p.2 ↔ p ∈ adoptablePairs2135467 := by
  classical
  obtain ⟨a, b⟩ := p
  have key := Finset.ext_iff.1 (filter_isAdoptablePair_Ico_eq_Ico [2, 1, 3, 5, 4, 6, 7] b) a
  simp only [Finset.mem_filter, Finset.mem_Ico] at key
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := adoptableLeftBound_2135467
  constructor
  · intro h
    obtain ⟨ha, hab, hb, -⟩ := id h
    have hl := (key.1 ⟨⟨ha, hab⟩, h⟩).1
    simp only [length_cons, length_nil] at hb
    interval_cases b <;> simp_all [adoptablePairs2135467] <;> omega
  · intro h
    have hab : a < b ∧ 1 ≤ a ∧ b ≤ 6 := by
      simp only [adoptablePairs2135467, Finset.mem_insert, Finset.mem_singleton,
        Prod.mk.injEq] at h
      omega
    refine (key.2 ⟨?_, hab.1⟩).2
    obtain ⟨hab, ha, hb⟩ := hab
    interval_cases b <;> simp only [adoptablePairs2135467, Finset.mem_insert,
      Finset.mem_singleton, Prod.mk.injEq] at h <;> simp_all

/-- A computable form of the defining conditions of `𝒜(2135467)`. -/
private abbrev IsGoodMatching2135467 (M : Finset (ℕ × ℕ)) : Prop :=
  (∀ p ∈ M, 1 ≤ p.1) ∧ (∀ p ∈ M, p.1 < p.2) ∧ (∀ p ∈ M, p.2 ≤ 6) ∧
  (∀ p ∈ M, ∀ q ∈ M, (p.1 = q.1 ∨ p.1 = q.2 ∨ p.2 = q.1 ∨ p.2 = q.2) → p = q) ∧
  (∀ p ∈ M, ∀ q ∈ M, ¬ (p.1 < q.1 ∧ q.1 < p.2 ∧ p.2 < q.2)) ∧
  ({1, 4} : Finset ℕ) ⊆ M.image Prod.fst

private theorem isNoncrossingPartialMatching_iff_isGoodMatching2135467 (M : Finset (ℕ × ℕ)) :
    IsNoncrossingPartialMatching 6 M ∧ ({1, 4} : Finset ℕ) ⊆ M.leftEndpoints ↔
      IsGoodMatching2135467 M := by
  constructor
  · rintro ⟨⟨h1, h2, h3, h4, h5⟩, h6⟩
    refine ⟨h1, h2, h3, fun p hp q hq h => ?_, h5, h6⟩
    rcases h with h | h | h | h
    · exact h4 p hp q hq p.1 (Or.inl rfl) (Or.inl h)
    · exact h4 p hp q hq p.1 (Or.inl rfl) (Or.inr h)
    · exact h4 p hp q hq p.2 (Or.inr rfl) (Or.inl h)
    · exact h4 p hp q hq p.2 (Or.inr rfl) (Or.inr h)
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    refine ⟨⟨h1, h2, h3, fun p hp q hq x hx hy => h4 p hp q hq ?_, h5⟩, h6⟩
    rcases hx with rfl | rfl <;> rcases hy with h | h <;> simp [h]

/-- The good subsets of the adoptable pairs are exactly `M_1, …, M_7`. -/
private theorem isGoodMatching2135467_iff :
    ∀ M ∈ adoptablePairs2135467.powerset,
      IsGoodMatching2135467 M ↔ M ∈ Finset.univ.image matching2135467 := by
  decide +kernel

private theorem matching2135467_subset (i : Fin 7) :
    matching2135467 i ⊆ adoptablePairs2135467 := by
  revert i; decide +kernel

/-- `2135467` is a permutation of `[7]`. -/
private theorem mem_permWords_2135467 : [2, 1, 3, 5, 4, 6, 7] ∈ permWords 7 :=
  ⟨⟨by decide, by decide⟩, rfl, by decide⟩

/-- For `π = 2135467`, the set of matchings of `π` is `{M_1, …, M_7}`: by
`List.fiberMatchings_eq_setOf_isAdoptablePair` they are the noncrossing partial matchings on
`[6]`, made of the adoptable pairs read off the adoptable intervals, whose left endpoints contain
`Des(π) = {1, 4}`, and these are enumerated. -/
@[lognarayana "lem_ex_fiber_matchings"]
public theorem fiberMatchings_2135467 :
    [2, 1, 3, 5, 4, 6, 7].fiberMatchings = Set.range matching2135467 := by
  rw [fiberMatchings_eq_setOf_isAdoptablePair (n := 7) mem_permWords_2135467,
    descentSet_2135467]
  ext M
  simp only [Set.mem_ofPred_eq, Set.mem_range, isAdoptablePair_2135467_iff, ← Finset.subset_iff]
  constructor
  · rintro ⟨h1, h2, h3⟩
    simpa using (isGoodMatching2135467_iff M (Finset.mem_powerset.2 h3)).1
      ((isNoncrossingPartialMatching_iff_isGoodMatching2135467 M).1 ⟨h1, h2⟩)
  · rintro ⟨i, rfl⟩
    have hm := Finset.mem_powerset.2 (matching2135467_subset i)
    exact ((isNoncrossingPartialMatching_iff_isGoodMatching2135467 _).2
      ((isGoodMatching2135467_iff _ hm).2 (by simp))).imp_right (⟨·, matching2135467_subset i⟩)

open Polynomial in
/-- The matching polynomial of `2135467` is `Γ_{2135467}(z) = 5 z² + 2 z³`: of its seven
matchings, five have two arcs and two have three. -/
@[lognarayana "lem_ex_gamma"]
public theorem fiberMatchingPolynomial_2135467 (R : Type*) [CommSemiring R] :
    fiberMatchingPolynomial R [2, 1, 3, 5, 4, 6, 7] = 5 * X ^ 2 + 2 * X ^ 3 := by
  rw [fiberMatchingPolynomial, fiberMatchings_2135467,
    finsum_mem_range (by decide : Function.Injective matching2135467), finsum_eq_sum_of_fintype]
  simp [Fin.sum_univ_seven, card_matching2135467]
  ring

open MvPolynomial in
/-- The homogeneous fiber polynomial of `2135467` is
`H_{2135467}(x, y) = 5 x² y² (x + y)² + 2 x³ y³`. -/
@[lognarayana "lem_ex_homog"]
public theorem fiberHomogPolynomial_2135467 (R : Type*) [CommSemiring R] :
    fiberHomogPolynomial R [2, 1, 3, 5, 4, 6, 7] =
      5 * X 0 ^ 2 * X 1 ^ 2 * (X 0 + X 1) ^ 2 + 2 * X 0 ^ 3 * X 1 ^ 3 := by
  rw [fiberHomogPolynomial_eq_finsum_fiberMatchings R (by norm_num) mem_permWords_2135467,
    fiberMatchings_2135467, finsum_mem_range (by decide), finsum_eq_sum_of_fintype]
  simp [Fin.sum_univ_seven, card_matching2135467]
  ring

open Polynomial in
/-- The fiber descent polynomial over `R` is the image of the one over `ℕ`. -/
private theorem fiberDescentPolynomial_eq_map (R : Type*) [Semiring R] (π : List ℕ) :
    fiberDescentPolynomial R π = (fiberDescentPolynomial ℕ π).map (Nat.castRingHom R) := by
  simp [fiberDescentPolynomial, Polynomial.map_sum]

open Polynomial in
/-- The fiber descent polynomial of `2135467` is `D_{2135467}(x) = 5x² + 12x³ + 5x⁴`. The
identity is proved over `ℕ` from the seven matchings and transported to `R`. -/
@[lognarayana "lem_ex_descent_poly"]
public theorem fiberDescentPolynomial_2135467 (R : Type*) [Semiring R] :
    fiberDescentPolynomial R [2, 1, 3, 5, 4, 6, 7] =
      C 5 * X ^ 2 + C 12 * X ^ 3 + C 5 * X ^ 4 := by
  have hℕ : fiberDescentPolynomial ℕ [2, 1, 3, 5, 4, 6, 7] =
      C 5 * X ^ 2 + C 12 * X ^ 3 + C 5 * X ^ 4 := by
    rw [fiberDescentPolynomial_eq_finsum_fiberMatchings ℕ (by norm_num) mem_permWords_2135467,
      fiberMatchings_2135467, finsum_mem_range (by decide), finsum_eq_sum_of_fintype]
    simp [Fin.sum_univ_seven, card_matching2135467, map_ofNat C]
    ring
  rw [fiberDescentPolynomial_eq_map, hℕ]
  simp [map_ofNat C]

end List
