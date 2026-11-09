/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib
public import LogNarayana.Attr
public import LogNarayana.Forest.Operations.Defs
public import LogNarayana.StackSorting.AdoptableForest.Defs
public import LogNarayana.StackSorting.AdoptableForest.Basic

/-!
# Operations on marked forests

A *marked postorder forest* on `[N] = {1, …, N}` is a postorder forest `par` on `[N]`
(`IsPostorderForest`) together with a set `L ⊆ [N]` of marked vertices, each of which is a leaf
(`IsLeaf`). This file shows that the operations of concatenation (`forestConcatParent`,
`forestConcatMarked`) and of adjoining a root (`forestAdjoinRootParent`) preserve marked
postorder forests, describes the strict ancestor relation of their results, and proves that every
nonempty marked postorder forest decomposes by its last tree.

In the concatenation of `par` on `[N]` and `par'` on `[N']`, `b` is a strict ancestor of `a`
exactly when both lie in the first forest and `b` is a strict ancestor of `a` there, or both lie
in the shifted second forest and `b - N` is a strict ancestor of `a - N` in `par'`. After
adjoining a root `N + 1`, the strict ancestors of `u ∈ [N]` are `N + 1` and the strict ancestors
of `u` in `par`. In both cases the subtrees are intervals ending at their root, so the result is
again a postorder forest, and marked vertices remain leaves.

Every nonempty marked postorder forest `(par, L)` on `[N]` is the concatenation of a marked
postorder forest on `[N₁]` with a marked postorder forest `G` on `[N₂]`, `N₁ + N₂ = N`,
`N₂ ≥ 1`, where `G` is either the marked singleton (`markedSingleton`, and then `N₂ = 1`) or is
obtained from a marked postorder forest on `[N₂ - 1]` by adjoining an unmarked root. The vertex
`N` is a root whose subtree is an interval `[N₁ + 1, N]`; the vertices `[N₁]` form a postorder
forest, and the shift of `[N₁ + 1, N]` down by `N₁` is a postorder tree on `[N₂]`.

## Main results

* `isStrictAncestor_forestConcatParent_iff`: the strict ancestor relation of a concatenation.
* `isPostorderForest_forestConcatParent`: the concatenation of marked postorder forests is a
  marked postorder forest.
* `isStrictAncestor_forestAdjoinRootParent_iff`: the strict ancestors of `u ∈ [N]` after
  adjoining a root are the new root and the strict ancestors of `u` in the forest.
* `isPostorderForest_forestAdjoinRootParent`: adjoining a root to a marked postorder forest gives
  a marked postorder forest.
* `exists_forestConcat_eq_of_isPostorderForest`: the decomposition of a nonempty marked
  postorder forest by its last tree.

## Implementation notes

A marked postorder forest `(par, L)` on `[N]` is not bundled: it is written out as the three
conditions `IsPostorderForest N par`, `L ⊆ Finset.Icc 1 N` and `∀ v ∈ L, IsLeaf par v`, both in
the hypotheses and in the conclusions. Identities between marked forests are stated
componentwise: equality of the parent maps as functions `ℕ → Option ℕ`, and equality of the
marked sets. The two ancestor lemmas only need `IsParentMap`, not the subtree-interval condition
of `IsPostorderForest`, and hold for all labels; the marked sets do not enter the parent maps, so
they do not appear in them.

## References

* [LogNarayana] *Log-Concavity in Narayana Transforms and Stack-Sorting Fibers*, Section 4.
-/

/-! ### Strict ancestors in a concatenation -/

/-- Iterates of `none` under `Option.bind par` stay `none`. -/
private lemma iterate_bind_none (par : ℕ → Option ℕ) (k : ℕ) :
    (fun o : Option ℕ => o.bind par)^[k] none = none :=
  Function.iterate_fixed rfl k

/-- A strict iterated parent `b` of `a` under a parent map on `[N]` satisfies `1 ≤ a < b ≤ N`. -/
private lemma bounds_of_iterate_succ {N : ℕ} {par : ℕ → Option ℕ} (hpar : IsParentMap N par)
    (k : ℕ) : ∀ a b, (fun o : Option ℕ => o.bind par)^[k + 1] (some a) = some b →
      1 ≤ a ∧ a < b ∧ b ≤ N := by
  induction k with
  | zero => exact fun a b h => hpar a b (by simpa using h)
  | succ k ih =>
    intro a b h
    rw [Function.iterate_succ_apply] at h
    cases hp : par a with
    | none => simp [hp, iterate_bind_none] at h
    | some p =>
      simp only [Option.bind_some, hp] at h
      have := hpar a p hp
      have := ih p b h
      omega

/-- A strict ancestor `b` of `a` under a parent map on `[N]` satisfies `1 ≤ a < b ≤ N`. -/
private lemma bounds_of_isStrictAncestor {N : ℕ} {par : ℕ → Option ℕ} (hpar : IsParentMap N par)
    {a b : ℕ} (h : IsStrictAncestor par b a) : 1 ≤ a ∧ a < b ∧ b ≤ N := by
  obtain ⟨⟨_ | k, hk⟩, hne⟩ := h
  · simp_all
  · exact bounds_of_iterate_succ hpar k a b hk

/-- An ancestor-or-self of `a` under a parent map is at least `a`. -/
private lemma le_of_isAncestorOrSelf {N : ℕ} {par : ℕ → Option ℕ} (hpar : IsParentMap N par)
    {a b : ℕ} (h : IsAncestorOrSelf par b a) : a ≤ b := by
  by_cases hab : b = a
  · exact hab.ge
  · exact (bounds_of_isStrictAncestor hpar ⟨h, hab⟩).2.1.le

/-- On options bounded by `N`, iterating the concatenated parent map is iterating `par`. -/
private lemma iterate_forestConcatParent_of_le {N : ℕ} {par par' : ℕ → Option ℕ}
    (hpar : IsParentMap N par) (k : ℕ) : ∀ o : Option ℕ, (∀ w ∈ o, w ≤ N) →
      (fun o : Option ℕ => o.bind (forestConcatParent N par par'))^[k] o =
        (fun o : Option ℕ => o.bind par)^[k] o := by
  induction k with
  | zero => exact fun _ _ => rfl
  | succ k ih =>
    rintro (_ | w) ho
    · simp [iterate_bind_none]
    · have hw : w ≤ N := ho w rfl
      simp only [Function.iterate_succ_apply, Option.bind_some, forestConcatParent, hw, if_true]
      exact ih _ fun x hx => (hpar w x hx).2.2

/-- Iterating the concatenated parent map on `N + ·` shifts the iterates of `par'`. -/
private lemma iterate_forestConcatParent_map {N N' : ℕ} {par par' : ℕ → Option ℕ}
    (hpar : IsParentMap N par) (hpar' : IsParentMap N' par') (k : ℕ) : ∀ o : Option ℕ,
      (fun o : Option ℕ => o.bind (forestConcatParent N par par'))^[k] (o.map (N + ·)) =
        ((fun o : Option ℕ => o.bind par')^[k] o).map (N + ·) := by
  induction k with
  | zero => exact fun _ => rfl
  | succ k ih =>
    intro o
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ← ih]
    congr 1
    rcases o with _ | _ | v
    · rfl
    · -- the vertex `N + 0 = N` is a root of `par`, and `0` is not a vertex of `par'`
      have h0 : par' 0 = none := Option.eq_none_iff_forall_ne_some.2 fun p h => by
        simpa using (hpar' 0 p h).1
      have hN : par N = none := Option.eq_none_iff_forall_ne_some.2 fun p h => by
        have := hpar N p h; omega
      simp [forestConcatParent, h0, hN]
    · simp [forestConcatParent]

/-- In the concatenation, the ancestors of a vertex `a ≤ N` are its ancestors under `par`. -/
private lemma isAncestorOrSelf_forestConcatParent_iff_of_le {N : ℕ} {par par' : ℕ → Option ℕ}
    (hpar : IsParentMap N par) {a : ℕ} (ha : a ≤ N) (b : ℕ) :
    IsAncestorOrSelf (forestConcatParent N par par') b a ↔ IsAncestorOrSelf par b a := by
  simp only [IsAncestorOrSelf,
    iterate_forestConcatParent_of_le hpar _ (some a) (by simpa using ha)]

/-- In the concatenation, the ancestors of `N + v` are `N` plus the ancestors of `v` under
`par'`. -/
private lemma isAncestorOrSelf_forestConcatParent_add_iff {N N' : ℕ} {par par' : ℕ → Option ℕ}
    (hpar : IsParentMap N par) (hpar' : IsParentMap N' par') (v b : ℕ) :
    IsAncestorOrSelf (forestConcatParent N par par') b (N + v) ↔
      ∃ c, IsAncestorOrSelf par' c v ∧ N + c = b := by
  have h k := iterate_forestConcatParent_map (par := par) hpar hpar' k (some v)
  simp only [Option.map_some] at h
  simp only [IsAncestorOrSelf, h, Option.map_eq_some_iff]
  exact ⟨fun ⟨k, c, hk, hc⟩ => ⟨c, ⟨k, hk⟩, hc⟩, fun ⟨c, ⟨k, hk⟩, hc⟩ => ⟨k, c, hk, hc⟩⟩

/-- In the concatenation of parent maps `par` on `[N]` and `par'` on `[N']` (e.g. postorder
forests), `b` is a strict ancestor of `a` iff either `a, b ∈ [N]` and `b` is a strict ancestor of
`a` in `par`, or `a, b > N` and `b - N` is a strict ancestor of `a - N` in `par'`. -/
@[lognarayana "lem_forest_concat_ancestor"]
public theorem isStrictAncestor_forestConcatParent_iff {N N' : ℕ} {par par' : ℕ → Option ℕ}
    (hpar : IsParentMap N par) (hpar' : IsParentMap N' par') (a b : ℕ) :
    IsStrictAncestor (forestConcatParent N par par') b a ↔
      (a ∈ Finset.Icc 1 N ∧ b ∈ Finset.Icc 1 N ∧ IsStrictAncestor par b a) ∨
        (N < a ∧ N < b ∧ IsStrictAncestor par' (b - N) (a - N)) := by
  simp only [Finset.mem_Icc]
  by_cases ha : a ≤ N
  · rw [IsStrictAncestor, isAncestorOrSelf_forestConcatParent_iff_of_le hpar ha,
      ← IsStrictAncestor]
    refine ⟨fun h => .inl ?_, by rintro (⟨-, -, h⟩ | ⟨h, -⟩) <;> first | exact h | omega⟩
    have := bounds_of_isStrictAncestor hpar h
    exact ⟨⟨this.1, ha⟩, ⟨by omega, this.2.2⟩, h⟩
  · obtain ⟨v, rfl⟩ : ∃ v, a = N + v := ⟨a - N, by omega⟩
    simp only [IsStrictAncestor, isAncestorOrSelf_forestConcatParent_add_iff hpar hpar',
      Nat.add_sub_cancel_left]
    constructor
    · rintro ⟨⟨c, hc, rfl⟩, hne⟩
      have := le_of_isAncestorOrSelf hpar' hc
      exact .inr ⟨by omega, by omega, by simpa using hc, by omega⟩
    · rintro (⟨h, -⟩ | ⟨-, hb, hc, hne⟩)
      · omega
      · exact ⟨⟨b - N, hc, by omega⟩, by omega⟩

/-! ### Concatenation of marked postorder forests -/

/-- Ancestor-or-self is strict ancestor or equality. -/
private lemma isAncestorOrSelf_iff {par : ℕ → Option ℕ} {u v : ℕ} :
    IsAncestorOrSelf par u v ↔ IsStrictAncestor par u v ∨ v = u := by
  by_cases h : u = v
  · subst h; simpa [IsStrictAncestor] using ⟨0, rfl⟩
  · simp [IsStrictAncestor, h, Ne.symm h]

/-- The concatenation of parent maps on `[N]` and `[N']` is a parent map on `[N + N']`. -/
private lemma isParentMap_forestConcatParent {N N' : ℕ} {par par' : ℕ → Option ℕ}
    (hpar : IsParentMap N par) (hpar' : IsParentMap N' par') :
    IsParentMap (N + N') (forestConcatParent N par par') := by
  intro v p hp
  unfold forestConcatParent at hp
  split_ifs at hp with hv
  · have := hpar v p hp; omega
  · obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp hp
    have := hpar' _ _ hq; omega

/-- The subtree of a vertex `v ≤ N` in a concatenation is its subtree in the first forest. -/
private lemma subtreeVertices_forestConcatParent_of_le {N N' : ℕ} {par par' : ℕ → Option ℕ}
    (hpar : IsParentMap N par) (hpar' : IsParentMap N' par') {v : ℕ}
    (hv : v ∈ Finset.Icc 1 N) :
    subtreeVertices (N + N') (forestConcatParent N par par') v = subtreeVertices N par v := by
  ext u
  simp only [subtreeVertices, Finset.mem_filter, isAncestorOrSelf_iff,
    isStrictAncestor_forestConcatParent_iff hpar hpar']
  simp only [Finset.mem_Icc] at hv ⊢
  constructor
  · rintro ⟨hu, (⟨hu', -, h⟩ | ⟨-, h, -⟩) | rfl⟩
    · exact ⟨hu', Or.inl h⟩
    · omega
    · exact ⟨⟨hu.1, hv.2⟩, Or.inr rfl⟩
  · rintro ⟨hu, h | rfl⟩
    · exact ⟨⟨hu.1, by omega⟩, Or.inl (Or.inl ⟨hu, hv, h⟩)⟩
    · exact ⟨⟨hu.1, by omega⟩, Or.inr rfl⟩

/-- The subtree of a vertex `N + w` in a concatenation is the shift by `N` of the subtree of `w`
in the second forest. -/
private lemma subtreeVertices_forestConcatParent_add {N N' : ℕ} {par par' : ℕ → Option ℕ}
    (hpar : IsParentMap N par) (hpar' : IsParentMap N' par') {w : ℕ}
    (hw : w ∈ Finset.Icc 1 N') :
    subtreeVertices (N + N') (forestConcatParent N par par') (N + w) =
      (subtreeVertices N' par' w).map (addLeftEmbedding N) := by
  ext u
  simp only [subtreeVertices, Finset.mem_map, Finset.mem_filter, isAncestorOrSelf_iff,
    isStrictAncestor_forestConcatParent_iff hpar hpar', addLeftEmbedding_apply]
  simp only [Finset.mem_Icc] at hw ⊢
  constructor
  · rintro ⟨hu, (⟨-, hb, -⟩ | ⟨hu', -, h⟩) | rfl⟩
    · omega
    · refine ⟨u - N, ⟨⟨by omega, by omega⟩, Or.inl (by simpa using h)⟩, by omega⟩
    · exact ⟨w, ⟨hw, Or.inr rfl⟩, rfl⟩
  · rintro ⟨x, ⟨hx, h | rfl⟩, rfl⟩
    · exact ⟨⟨by omega, by omega⟩, Or.inl (Or.inr ⟨by omega, by omega, by simpa using h⟩)⟩
    · exact ⟨⟨by omega, by omega⟩, Or.inr rfl⟩

/-- In a postorder forest the subtree of `v` has at most `v` vertices: otherwise the interval
`[v - |V_v| + 1, v]` would contain `0`. -/
private lemma card_subtreeVertices_le {N : ℕ} {par : ℕ → Option ℕ} (hpar : IsPostorderForest N par)
    {v : ℕ} (hv : v ∈ Finset.Icc 1 N) : (subtreeVertices N par v).card ≤ v := by
  by_contra hc
  have h0 : 0 ∈ subtreeVertices N par v := by rw [hpar.2 v hv]; simp; omega
  simp [subtreeVertices] at h0

/-- The concatenation of postorder forests on `[N]` and `[N']` is a postorder forest on
`[N + N']`. -/
private lemma isPostorderForest_forestConcatParent_of_isPostorderForest {N N' : ℕ}
    {par par' : ℕ → Option ℕ}
    (hpar : IsPostorderForest N par) (hpar' : IsPostorderForest N' par') :
    IsPostorderForest (N + N') (forestConcatParent N par par') := by
  refine ⟨isParentMap_forestConcatParent hpar.1 hpar'.1, fun v hv => ?_⟩
  by_cases hvN : v ≤ N
  · have hv' : v ∈ Finset.Icc 1 N := by simp at hv ⊢; omega
    rw [subtreeVertices_forestConcatParent_of_le hpar.1 hpar'.1 hv']
    exact hpar.2 v hv'
  · obtain ⟨w, rfl⟩ : ∃ w, v = N + w := ⟨v - N, by omega⟩
    have hw : w ∈ Finset.Icc 1 N' := by simp at hv ⊢; omega
    have hc := card_subtreeVertices_le hpar' hw
    rw [subtreeVertices_forestConcatParent_add hpar.1 hpar'.1 hw, Finset.card_map,
      hpar'.2 w hw, Nat.card_Icc, Finset.map_add_left_Icc]
    congr 1; omega

/-- The marked set of a concatenation lies in `[N + N']`. -/
private lemma forestConcatMarked_subset {N N' : ℕ} {L L' : Finset ℕ}
    (hL : L ⊆ Finset.Icc 1 N) (hL' : L' ⊆ Finset.Icc 1 N') :
    forestConcatMarked N L L' ⊆ Finset.Icc 1 (N + N') := by
  intro v hv
  rcases Finset.mem_union.mp hv with hv | hv
  · have := Finset.mem_Icc.mp (hL hv); simp; omega
  · obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hv
    have := Finset.mem_Icc.mp (hL' hw); simp; omega

/-- A marked vertex of a concatenation of marked forests is a leaf: its children there are its
children in its own forest. -/
private lemma isLeaf_forestConcatParent {N N' : ℕ} {par par' : ℕ → Option ℕ} {L L' : Finset ℕ}
    (hpar : IsParentMap N par) (hpar' : IsParentMap N' par') (hL : L ⊆ Finset.Icc 1 N)
    (hLleaf : ∀ v ∈ L, IsLeaf par v) (hL' : L' ⊆ Finset.Icc 1 N')
    (hLleaf' : ∀ v ∈ L', IsLeaf par' v) {v : ℕ} (hv : v ∈ forestConcatMarked N L L') :
    IsLeaf (forestConcatParent N par par') v := by
  intro u hu
  simp only [forestConcatMarked, Finset.mem_union, Finset.mem_map,
    addLeftEmbedding_apply] at hv
  unfold forestConcatParent at hu
  split_ifs at hu with huN
  · rcases hv with hv | ⟨w, hw, rfl⟩
    · exact hLleaf v hv u hu
    · have := hpar u _ hu; have := Finset.mem_Icc.mp (hL' hw); omega
  · obtain ⟨q, hq, hqv⟩ := Option.map_eq_some_iff.mp hu
    rcases hv with hv | ⟨w, hw, rfl⟩
    · have := hpar' _ _ hq; have := Finset.mem_Icc.mp (hL hv); omega
    · obtain rfl : q = w := by omega
      exact hLleaf' q hw _ hq

/-- The concatenation of a marked postorder forest `(par, L)` on `[N]` with a marked postorder
forest `(par', L')` on `[N']` is a marked postorder forest on `[N + N']`: its parent map is a
postorder forest on `[N + N']`, and its marked set lies in `[N + N']` and consists of leaves. -/
@[lognarayana "lem_forest_concat_postorder"]
public theorem isPostorderForest_forestConcatParent {N N' : ℕ} {par par' : ℕ → Option ℕ}
    {L L' : Finset ℕ} (hpar : IsPostorderForest N par) (hL : L ⊆ Finset.Icc 1 N)
    (hLleaf : ∀ v ∈ L, IsLeaf par v) (hpar' : IsPostorderForest N' par')
    (hL' : L' ⊆ Finset.Icc 1 N') (hLleaf' : ∀ v ∈ L', IsLeaf par' v) :
    IsPostorderForest (N + N') (forestConcatParent N par par') ∧
      forestConcatMarked N L L' ⊆ Finset.Icc 1 (N + N') ∧
      ∀ v ∈ forestConcatMarked N L L', IsLeaf (forestConcatParent N par par') v :=
  ⟨isPostorderForest_forestConcatParent_of_isPostorderForest hpar hpar',
    forestConcatMarked_subset hL hL',
    fun _ hv => isLeaf_forestConcatParent hpar.1 hpar'.1 hL hLleaf hL' hLleaf' hv⟩

/-! ### Strict ancestors after adjoining a root -/

/-- Iterates of `par` from `u ∈ [N]` stay in `[N]` and agree with those of the adjoined map. -/
private lemma iterate_forestAdjoinRootParent_of_iterate {N : ℕ} {par : ℕ → Option ℕ}
    (hpar : IsParentMap N par) {u : ℕ} (hu : 1 ≤ u ∧ u ≤ N) :
    ∀ k w, (fun o : Option ℕ => o.bind par)^[k] (some u) = some w →
      (1 ≤ w ∧ w ≤ N) ∧
        (fun o : Option ℕ => o.bind (forestAdjoinRootParent N par))^[k] (some u) = some w := by
  intro k
  induction k with
  | zero => rintro w ⟨⟩; exact ⟨hu, rfl⟩
  | succ k ih =>
    intro w h
    rw [Function.iterate_succ_apply'] at h ⊢
    cases hx : (fun o : Option ℕ => o.bind par)^[k] (some u) with
    | none => simp [hx] at h
    | some x =>
      rw [hx, Option.bind_some] at h
      obtain ⟨hxN, hg⟩ := ih x hx
      have := hpar x w h
      exact ⟨⟨by omega, this.2.2⟩, by simp [hg, forestAdjoinRootParent, hxN, h]⟩

/-- Iterates of the adjoined map from `u ∈ [N]` are iterates of `par` or the new root. -/
private lemma iterate_of_iterate_forestAdjoinRootParent {N : ℕ} {par : ℕ → Option ℕ}
    (hpar : IsParentMap N par) {u : ℕ} (hu : 1 ≤ u ∧ u ≤ N) :
    ∀ k w, (fun o : Option ℕ => o.bind (forestAdjoinRootParent N par))^[k] (some u) = some w →
      (fun o : Option ℕ => o.bind par)^[k] (some u) = some w ∨ w = N + 1 := by
  intro k
  induction k with
  | zero => exact fun w h => .inl h
  | succ k ih =>
    intro w h
    rw [Function.iterate_succ_apply'] at h ⊢
    cases hx : (fun o : Option ℕ => o.bind (forestAdjoinRootParent N par))^[k] (some u) with
    | none => simp [hx] at h
    | some x =>
      rw [hx, Option.bind_some] at h
      rcases ih x hx with hf | rfl
      · have hxN := (iterate_forestAdjoinRootParent_of_iterate hpar hu k x hf).1
        rw [hf, Option.bind_some]
        simp only [forestAdjoinRootParent, hxN, and_self, if_true, Option.some.injEq] at h
        cases hp : par x <;> simp_all [eq_comm]
      · simp [forestAdjoinRootParent] at h

/-- The new root is an ancestor of every vertex of `[N]`. -/
private lemma isAncestorOrSelf_forestAdjoinRootParent_root {N : ℕ} {par : ℕ → Option ℕ}
    (hpar : IsParentMap N par) {w : ℕ} (hw : 1 ≤ w ∧ w ≤ N) :
    IsAncestorOrSelf (forestAdjoinRootParent N par) (N + 1) w := by
  cases hp : par w with
  | none => exact ⟨1, by simp [forestAdjoinRootParent, hw, hp]⟩
  | some p =>
    have := hpar w p hp
    obtain ⟨k, hk⟩ :=
      isAncestorOrSelf_forestAdjoinRootParent_root hpar (w := p) ⟨by omega, this.2.2⟩
    exact ⟨k + 1, by simpa [Function.iterate_succ_apply, forestAdjoinRootParent, hw, hp] using hk⟩
termination_by N - w
decreasing_by omega

/-- For a parent map `par` on `[N]` and `u ∈ [N]`, the ancestors-or-self of `u` after adjoining
the root `N + 1` are `N + 1` and the ancestors-or-self of `u` for `par`. -/
private lemma isAncestorOrSelf_forestAdjoinRootParent_iff {N : ℕ} {par : ℕ → Option ℕ}
    (hpar : IsParentMap N par) {u v : ℕ} (hu : 1 ≤ u ∧ u ≤ N) :
    IsAncestorOrSelf (forestAdjoinRootParent N par) v u ↔
      v = N + 1 ∨ IsAncestorOrSelf par v u := by
  refine ⟨fun ⟨k, hk⟩ =>
    (iterate_of_iterate_forestAdjoinRootParent hpar hu k v hk).symm.imp_right (⟨k, ·⟩), ?_⟩
  rintro (rfl | ⟨k, hk⟩)
  exacts [isAncestorOrSelf_forestAdjoinRootParent_root hpar hu,
    ⟨k, (iterate_forestAdjoinRootParent_of_iterate hpar hu k v hk).2⟩]

/-- In the tree obtained from a forest with parent map `par` on `[N]` by adjoining a root `N + 1`,
for `u ∈ [N]`, `v` is a strict ancestor of `u` iff `v = N + 1` or `v` is a strict ancestor of `u`
in `par`. -/
@[lognarayana "lem_forest_adjoin_root_ancestor"]
public theorem isStrictAncestor_forestAdjoinRootParent_iff {N : ℕ} {par : ℕ → Option ℕ}
    (hpar : IsParentMap N par) {u v : ℕ} (hu : u ∈ Finset.Icc 1 N) :
    IsStrictAncestor (forestAdjoinRootParent N par) v u ↔
      v = N + 1 ∨ IsStrictAncestor par v u := by
  have hu := Finset.mem_Icc.mp hu
  rw [IsStrictAncestor, IsStrictAncestor, isAncestorOrSelf_forestAdjoinRootParent_iff hpar hu]
  refine ⟨fun ⟨h, hne⟩ => h.imp_right (⟨·, hne⟩), ?_⟩
  rintro (rfl | ⟨h, hne⟩)
  exacts [⟨.inl rfl, by omega⟩, ⟨.inr h, hne⟩]

/-! ### Adjoining a root to a marked postorder forest -/

/-- Adjoining a root to a parent map on `[N]` gives a parent map on `[N + 1]`. -/
private lemma isParentMap_forestAdjoinRootParent {N : ℕ} {par : ℕ → Option ℕ}
    (hpar : IsParentMap N par) : IsParentMap (N + 1) (forestAdjoinRootParent N par) := by
  intro v p hp
  unfold forestAdjoinRootParent at hp
  split_ifs at hp with hv
  · cases hq : par v with
    | none => simp [hq] at hp; omega
    | some q => simp [hq] at hp; have := hpar v q hq; omega

/-- The new root `N + 1` is a strict descendant of no vertex. -/
private lemma not_isStrictAncestor_forestAdjoinRootParent_root {N : ℕ} {par : ℕ → Option ℕ}
    {v : ℕ} : ¬ IsStrictAncestor (forestAdjoinRootParent N par) v (N + 1) := by
  rintro ⟨⟨k, hk⟩, hne⟩
  cases k with
  | zero => exact hne (Option.some_injective _ hk).symm
  | succ k =>
    have h0 : (some (N + 1)).bind (forestAdjoinRootParent N par) = none := by
      simp [forestAdjoinRootParent]
    rw [Function.iterate_succ_apply, h0,
      Function.iterate_fixed (f := fun o : Option ℕ => o.bind (forestAdjoinRootParent N par))
        (x := none) rfl] at hk
    simp at hk

/-- The subtree of `v ∈ [N]` after adjoining a root is its subtree in the forest. -/
private lemma subtreeVertices_forestAdjoinRootParent_of_le {N : ℕ} {par : ℕ → Option ℕ}
    (hpar : IsParentMap N par) {v : ℕ} (hv : v ∈ Finset.Icc 1 N) :
    subtreeVertices (N + 1) (forestAdjoinRootParent N par) v = subtreeVertices N par v := by
  ext u
  simp only [subtreeVertices, Finset.mem_filter, isAncestorOrSelf_iff]
  simp only [Finset.mem_Icc] at hv
  by_cases hu : u = N + 1
  · subst hu
    simp only [Finset.mem_Icc, not_isStrictAncestor_forestAdjoinRootParent_root, false_or]
    omega
  · by_cases hu' : u ∈ Finset.Icc 1 N
    · rw [isStrictAncestor_forestAdjoinRootParent_iff hpar hu']
      simp only [Finset.mem_Icc] at hu' ⊢
      have : v ≠ N + 1 := by omega
      simp [this]; omega
    · simp only [Finset.mem_Icc] at hu' ⊢
      constructor <;> rintro ⟨h1, -⟩ <;> omega

/-- The subtree of the new root `N + 1` is all of `[N + 1]`. -/
private lemma subtreeVertices_forestAdjoinRootParent_root {N : ℕ} {par : ℕ → Option ℕ}
    (hpar : IsParentMap N par) :
    subtreeVertices (N + 1) (forestAdjoinRootParent N par) (N + 1) = Finset.Icc 1 (N + 1) := by
  ext u
  simp only [subtreeVertices, Finset.mem_filter, and_iff_left_iff_imp, isAncestorOrSelf_iff]
  intro hu
  by_cases h : u = N + 1
  · exact Or.inr h
  · have hu' : u ∈ Finset.Icc 1 N := by simp only [Finset.mem_Icc] at hu ⊢; omega
    exact Or.inl ((isStrictAncestor_forestAdjoinRootParent_iff hpar hu').2 (Or.inl rfl))

/-- Adjoining a root to a postorder forest on `[N]` gives a postorder forest on `[N + 1]`. -/
private lemma isPostorderForest_forestAdjoinRootParent_of_isPostorderForest {N : ℕ}
    {par : ℕ → Option ℕ}
    (hpar : IsPostorderForest N par) :
    IsPostorderForest (N + 1) (forestAdjoinRootParent N par) := by
  refine ⟨isParentMap_forestAdjoinRootParent hpar.1, fun v hv => ?_⟩
  rcases eq_or_ne v (N + 1) with rfl | h
  · simp [subtreeVertices_forestAdjoinRootParent_root hpar.1]
  · have hv' : v ∈ Finset.Icc 1 N := by simp only [Finset.mem_Icc] at hv ⊢; omega
    rw [subtreeVertices_forestAdjoinRootParent_of_le hpar.1 hv']
    exact hpar.2 v hv'

/-- A leaf `v ∈ [N]` of `par` stays a leaf after adjoining the root `N + 1`. -/
private lemma isLeaf_forestAdjoinRootParent {N : ℕ} {par : ℕ → Option ℕ} {v : ℕ}
    (hv : v ≤ N) (hleaf : IsLeaf par v) : IsLeaf (forestAdjoinRootParent N par) v := by
  intro u hu
  unfold forestAdjoinRootParent at hu
  split_ifs at hu
  cases hq : par u with
  | none => simp [hq] at hu; omega
  | some q => exact hleaf u (by simpa [hq] using hu)

/-- Adjoining a root to a marked postorder forest `(par, L)` on `[N]` gives a marked postorder
forest on `[N + 1]`: its parent map `forestAdjoinRootParent N par` is a postorder forest on
`[N + 1]`, and its marked set `L` lies in `[N + 1]` and consists of leaves. -/
@[lognarayana "lem_forest_adjoin_root_postorder"]
public theorem isPostorderForest_forestAdjoinRootParent {N : ℕ} {par : ℕ → Option ℕ}
    {L : Finset ℕ} (hpar : IsPostorderForest N par) (hL : L ⊆ Finset.Icc 1 N)
    (hLleaf : ∀ v ∈ L, IsLeaf par v) :
    IsPostorderForest (N + 1) (forestAdjoinRootParent N par) ∧
      L ⊆ Finset.Icc 1 (N + 1) ∧
      ∀ v ∈ L, IsLeaf (forestAdjoinRootParent N par) v :=
  ⟨isPostorderForest_forestAdjoinRootParent_of_isPostorderForest hpar,
    hL.trans (Finset.Icc_subset_Icc_right (Nat.le_succ _)),
    fun v hv => isLeaf_forestAdjoinRootParent (Finset.mem_Icc.mp (hL hv)).2 (hLleaf v hv)⟩

/-! ### Decomposition by the last tree -/

/-- Iterates of a parent map with fewer edges are iterates of the larger one. -/
private lemma iterate_of_le {par par' : ℕ → Option ℕ}
    (h : ∀ x y, par' x = some y → par x = some y) {v : ℕ} :
    ∀ j x, (fun o : Option ℕ => o.bind par')^[j] (some v) = some x →
      (fun o : Option ℕ => o.bind par)^[j] (some v) = some x := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    intro x hj
    rw [Function.iterate_succ_apply'] at hj ⊢
    cases hy : (fun o : Option ℕ => o.bind par')^[j] (some v) with
    | none => rw [hy] at hj; simp at hj
    | some y => rw [hy] at hj; rw [ih y hy]; exact h _ _ hj

/-- Iterates of `par` landing in a set `P` closed under taking children, all of whose incoming
edges are kept in `par'`, are iterates of `par'`. -/
private lemma iterate_of_restrict {par par' : ℕ → Option ℕ} (P : ℕ → Prop)
    (h : ∀ x y, par x = some y → P y → P x ∧ par' x = some y) {v : ℕ} :
    ∀ j x, (fun o : Option ℕ => o.bind par)^[j] (some v) = some x → P x →
      (fun o : Option ℕ => o.bind par')^[j] (some v) = some x := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    intro x hj hx
    rw [Function.iterate_succ_apply'] at hj ⊢
    cases hy : (fun o : Option ℕ => o.bind par)^[j] (some v) with
    | none => rw [hy] at hj; simp at hj
    | some y =>
      rw [hy] at hj
      obtain ⟨hPy, hy'⟩ := h y x hj hx
      rw [ih y hy hPy]
      exact hy'

private lemma isAncestorOrSelf_iff_of_restrict {par par' : ℕ → Option ℕ} (P : ℕ → Prop)
    (h1 : ∀ x y, par' x = some y → par x = some y)
    (h2 : ∀ x y, par x = some y → P y → P x ∧ par' x = some y) {a v : ℕ} (ha : P a) :
    IsAncestorOrSelf par' a v ↔ IsAncestorOrSelf par a v :=
  ⟨fun ⟨j, hj⟩ => ⟨j, iterate_of_le h1 j a hj⟩,
    fun ⟨j, hj⟩ => ⟨j, iterate_of_restrict P h2 j a hj ha⟩⟩

/-- Restricting a parent map to an initial segment `[M']` closed under taking children keeps
the subtrees of its vertices. -/
private lemma subtreeVertices_eq_of_restrict {M M' : ℕ} {par par' : ℕ → Option ℕ}
    (hpar : IsParentMap M par) (hM : M' ≤ M)
    (h1 : ∀ x y, par' x = some y → par x = some y)
    (h2 : ∀ x y, par x = some y → y ≤ M' → x ≤ M' ∧ par' x = some y) {v : ℕ} (hv : v ≤ M') :
    subtreeVertices M' par' v = subtreeVertices M par v := by
  ext u
  simp only [subtreeVertices, Finset.mem_filter, Finset.mem_Icc,
    isAncestorOrSelf_iff_of_restrict (· ≤ M') h1 h2 hv]
  constructor
  · rintro ⟨⟨h1u, hu⟩, ha⟩
    exact ⟨⟨h1u, by omega⟩, ha⟩
  · rintro ⟨⟨h1u, hu⟩, ha⟩
    exact ⟨⟨h1u, (le_of_isAncestorOrSelf hpar ha).trans hv⟩, ha⟩

private lemma isPostorderForest_of_restrict {M M' : ℕ} {par par' : ℕ → Option ℕ}
    (hpar : IsPostorderForest M par) (hM : M' ≤ M)
    (h1 : ∀ x y, par' x = some y → par x = some y)
    (h2 : ∀ x y, par x = some y → y ≤ M' → x ≤ M' ∧ par' x = some y)
    (hpm : IsParentMap M' par') : IsPostorderForest M' par' := by
  refine ⟨hpm, fun v hv => ?_⟩
  have hv' := Finset.mem_Icc.mp hv
  rw [subtreeVertices_eq_of_restrict hpar.1 hM h1 h2 hv'.2]
  exact hpar.2 v (Finset.mem_Icc.mpr ⟨hv'.1, hv'.2.trans hM⟩)

/-- The iterates of a parent map shifted down by `M` are the shifted iterates, and they stay
above `M`. -/
private lemma iterate_shift {par parG : ℕ → Option ℕ} {M N : ℕ} (hpar : IsParentMap N par)
    (hG : ∀ u, 1 ≤ u → parG u = (par (M + u)).map (· - M)) {u : ℕ} (hu : 1 ≤ u) :
    ∀ j, (fun o : Option ℕ => o.bind parG)^[j] (some u) =
        ((fun o : Option ℕ => o.bind par)^[j] (some (M + u))).map (· - M) ∧
      ∀ w, (fun o : Option ℕ => o.bind par)^[j] (some (M + u)) = some w → M < w := by
  intro j
  induction j with
  | zero =>
    refine ⟨by simp, fun w hw => ?_⟩
    simp at hw
    omega
  | succ j ih =>
    obtain ⟨ih1, ih2⟩ := ih
    simp only [Function.iterate_succ_apply']
    rw [ih1]
    cases hw : (fun o : Option ℕ => o.bind par)^[j] (some (M + u)) with
    | none => simp
    | some w =>
      have hMw := ih2 w hw
      simp only [Option.map_some, Option.bind_some]
      refine ⟨?_, fun w' hw' => ?_⟩
      · rw [hG _ (by omega), show M + (w - M) = w by omega]
      · have := hpar _ _ hw'
        omega

private lemma isAncestorOrSelf_shift_iff {par parG : ℕ → Option ℕ} {M N : ℕ}
    (hpar : IsParentMap N par) (hG : ∀ u, 1 ≤ u → parG u = (par (M + u)).map (· - M))
    {u a : ℕ} (hu : 1 ≤ u) :
    IsAncestorOrSelf parG a u ↔ IsAncestorOrSelf par (M + a) (M + u) := by
  constructor
  · rintro ⟨j, hj⟩
    obtain ⟨h1, h2⟩ := iterate_shift hpar hG hu j
    rw [h1] at hj
    obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp hj
    have := h2 w hw
    exact ⟨j, by rw [hw, show M + (w - M) = w by omega]⟩
  · rintro ⟨j, hj⟩
    exact ⟨j, by rw [(iterate_shift hpar hG hu j).1, hj]; simp⟩

/-- A vertex with a strict ancestor has a parent. -/
private lemma exists_parent_of_isAncestorOrSelf {par : ℕ → Option ℕ} {a w : ℕ}
    (h : IsAncestorOrSelf par a w) (hne : a ≠ w) : ∃ p, par w = some p := by
  obtain ⟨j, hj⟩ := h
  cases j with
  | zero => exact absurd (Option.some_injective _ hj).symm hne
  | succ j =>
    rw [Function.iterate_succ_apply] at hj
    cases hp : par w with
    | none => simp [hp, iterate_bind_none] at hj
    | some p => exact ⟨p, rfl⟩

/-- A vertex with a strict descendant has a child. -/
private lemma exists_child_of_isAncestorOrSelf {par : ℕ → Option ℕ} {a w : ℕ}
    (h : IsAncestorOrSelf par a w) (hne : a ≠ w) : ∃ u, par u = some a := by
  obtain ⟨j, hj⟩ := h
  cases j with
  | zero => exact absurd (Option.some_injective _ hj).symm hne
  | succ j =>
    rw [Function.iterate_succ_apply'] at hj
    cases hu : (fun o : Option ℕ => o.bind par)^[j] (some w) with
    | none => rw [hu] at hj; simp at hj
    | some u => rw [hu] at hj; exact ⟨u, hj⟩

/-- Restricting a postorder forest on `[N]` to an initial segment `[M]` that no edge leaves
gives a postorder forest on `[M]`. -/
private lemma isPostorderForest_restrict_le {N M : ℕ} {par : ℕ → Option ℕ}
    (hpar : IsPostorderForest N par) (hM : M ≤ N)
    (hclosed : ∀ v p, par v = some p → v ≤ M → p ≤ M) :
    IsPostorderForest M (fun v => if v ≤ M then par v else none) := by
  refine isPostorderForest_of_restrict hpar hM (fun x y h => ?_) (fun x y h hy => ?_)
    (fun v p h => ?_)
  · split_ifs at h
    exact h
  · have := hpar.1 _ _ h
    exact ⟨by omega, by simp [show x ≤ M by omega, h]⟩
  · split_ifs at h with hv
    have := hpar.1 _ _ h
    exact ⟨this.1, this.2.1, hclosed _ _ h hv⟩

/-- Deleting the root `k` of a postorder tree on `[k]` leaves a postorder forest on `[k - 1]`. -/
private lemma isPostorderForest_delete_root {k : ℕ} {par : ℕ → Option ℕ}
    (hpar : IsPostorderForest k par) :
    IsPostorderForest (k - 1) (fun u => if par u = some k then none else par u) := by
  refine isPostorderForest_of_restrict hpar (by omega) (fun x y h => ?_) (fun x y h hy => ?_)
    (fun v p h => ?_)
  · split_ifs at h
    exact h
  · have := hpar.1 _ _ h
    refine ⟨by omega, ?_⟩
    rw [if_neg (by rw [h]; intro h'; simp at h'; omega)]
    exact h
  · split_ifs at h with hk
    have := hpar.1 _ _ h
    have : p ≠ k := fun hpk => hk (hpk ▸ h)
    exact ⟨by omega, by omega, by omega⟩

/-- The vertices of a postorder forest on `[N]` above `M`, if they are closed under taking
descendants, form a postorder forest on `[N - M]` once shifted down by `M`. -/
private lemma isPostorderForest_shift {N M : ℕ} {par : ℕ → Option ℕ}
    (hpar : IsPostorderForest N par) (hM : M ≤ N)
    (hdesc : ∀ a w, M < a → a ≤ N → 1 ≤ w → w ≤ N → IsAncestorOrSelf par a w → M < w) :
    IsPostorderForest (N - M) (fun u => if 1 ≤ u then (par (M + u)).map (· - M) else none) := by
  classical
  set parG : ℕ → Option ℕ := fun u => if 1 ≤ u then (par (M + u)).map (· - M) else none
  have hG : ∀ u, 1 ≤ u → parG u = (par (M + u)).map (· - M) := fun u hu => if_pos hu
  have hpmG : IsParentMap (N - M) parG := by
    intro u p h
    simp only [parG] at h
    split_ifs at h with hu
    obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp h
    have := hpar.1 _ _ hq
    omega
  have hsubG : ∀ a, 1 ≤ a → a ≤ N - M → subtreeVertices N par (M + a) =
      (subtreeVertices (N - M) parG a).map (addLeftEmbedding M) := by
    intro a ha1 hak
    ext w
    simp only [Finset.mem_map, subtreeVertices, Finset.mem_filter, Finset.mem_Icc,
      addLeftEmbedding_apply]
    constructor
    · rintro ⟨⟨hw1, hwN⟩, hw⟩
      have hMw := hdesc (M + a) w (by omega) (by omega) hw1 hwN hw
      refine ⟨w - M, ⟨⟨by omega, by omega⟩, ?_⟩, by omega⟩
      rw [isAncestorOrSelf_shift_iff hpar.1 hG (by omega), show M + (w - M) = w by omega]
      exact hw
    · rintro ⟨u, ⟨⟨hu1, huk⟩, hu⟩, rfl⟩
      exact ⟨⟨by omega, by omega⟩, (isAncestorOrSelf_shift_iff hpar.1 hG hu1).mp hu⟩
  refine ⟨hpmG, fun a ha => ?_⟩
  obtain ⟨ha1, hak⟩ := Finset.mem_Icc.mp ha
  have hU := hpar.2 (M + a) (by simp; omega)
  rw [hsubG a ha1 hak, Finset.card_map] at hU
  have hc1 : 1 ≤ (subtreeVertices (N - M) parG a).card :=
    Finset.card_pos.mpr ⟨a, Finset.mem_filter.mpr ⟨ha, 0, rfl⟩⟩
  have hc : (subtreeVertices (N - M) parG a).card ≤ a := by
    have hx : M + a + 1 - (subtreeVertices (N - M) parG a).card ∈
        (subtreeVertices (N - M) parG a).map (addLeftEmbedding M) := by
      rw [hU, Finset.mem_Icc]; omega
    obtain ⟨u, hu, hu'⟩ := Finset.mem_map.mp hx
    have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hu).1).1
    rw [addLeftEmbedding_apply] at hu'
    omega
  ext u
  rw [← Finset.mem_map' (addLeftEmbedding M), hU, Finset.mem_Icc, Finset.mem_Icc,
    addLeftEmbedding_apply]
  omega

/-- A parent map on `[N]` is the concatenation of its restriction to `[M]` with its shift
by `M`. -/
private lemma eq_forestConcatParent_restrict_shift {N M : ℕ} {par : ℕ → Option ℕ}
    (hpar : IsParentMap N par) :
    par = forestConcatParent M (fun v => if v ≤ M then par v else none)
      (fun u => if 1 ≤ u then (par (M + u)).map (· - M) else none) := by
  funext v
  simp only [forestConcatParent]
  by_cases hv : v ≤ M
  · rw [if_pos hv, if_pos hv]
  · rw [if_neg hv, if_pos (by omega), show M + (v - M) = v by omega]
    cases h : par v with
    | none => rfl
    | some p =>
      have := hpar _ _ h
      simp only [Option.map_some]
      congr 1
      omega

/-- A finite set of naturals is the concatenation of its part `≤ M` with its part `> M`
shifted down by `M`. -/
private lemma eq_forestConcatMarked_filter (L : Finset ℕ) (M : ℕ) :
    L = forestConcatMarked M (L.filter (· ≤ M)) ((L.filter (M < ·)).image (· - M)) := by
  ext w
  simp only [forestConcatMarked, Finset.mem_union, Finset.mem_map, addLeftEmbedding_apply,
    Finset.mem_filter, Finset.mem_image]
  constructor
  · intro hw
    by_cases h : w ≤ M
    · exact Or.inl ⟨hw, h⟩
    · exact Or.inr ⟨w - M, ⟨w, ⟨hw, by omega⟩, rfl⟩, by omega⟩
  · rintro (⟨hw, _⟩ | ⟨_, ⟨x, ⟨hx, hx'⟩, rfl⟩, rfl⟩)
    · exact hw
    · rwa [show M + (x - M) = x by omega]

/-- The subtree of the last root `N` of a postorder forest on `[N]` is a final segment
`(M, N]`. -/
private lemma exists_lt_forall_isAncestorOrSelf_iff {N : ℕ} {par : ℕ → Option ℕ}
    (hpar : IsPostorderForest N par) (hN : 1 ≤ N) :
    ∃ M < N, ∀ w, 1 ≤ w → w ≤ N → (IsAncestorOrSelf par N w ↔ M < w) := by
  classical
  obtain ⟨k, hk⟩ : ∃ k, (subtreeVertices N par N).card = k := ⟨_, rfl⟩
  have hS := hpar.2 N (by simp; omega)
  rw [hk] at hS
  have hmem : ∀ w, w ∈ subtreeVertices N par N ↔ 1 ≤ w ∧ w ≤ N ∧ IsAncestorOrSelf par N w := by
    intro w
    rw [subtreeVertices, Finset.mem_filter, Finset.mem_Icc, and_assoc]
  have hk1 : 1 ≤ k := hk ▸ Finset.card_pos.mpr ⟨N, (hmem N).mpr ⟨hN, le_rfl, 0, rfl⟩⟩
  refine ⟨N - k, by omega, fun w hw1 hwN => ?_⟩
  have hw := hmem w
  rw [hS, Finset.mem_Icc] at hw
  constructor
  · intro h
    have := hw.mpr ⟨hw1, hwN, h⟩
    omega
  · intro h
    exact (hw.mp ⟨by omega, hwN⟩).2.2

/-- If the subtree of the last root `N` is `(M, N]`, the restriction to `[M]` is a postorder
forest. -/
private lemma isPostorderForest_restrict_of_isAncestorOrSelf_iff {N M : ℕ}
    {par : ℕ → Option ℕ} (hpar : IsPostorderForest N par) (hM : M < N)
    (hanc : ∀ w, 1 ≤ w → w ≤ N → (IsAncestorOrSelf par N w ↔ M < w)) :
    IsPostorderForest M (fun v => if v ≤ M then par v else none) := by
  refine isPostorderForest_restrict_le hpar hM.le fun v p hvp hv => ?_
  by_contra hp
  have hp' := hpar.1 _ _ hvp
  have h1 : IsAncestorOrSelf par p v := ⟨1, by simpa using hvp⟩
  have := (hanc v hp'.1 (by omega)).mp (((hanc p (by omega) hp'.2.2).mpr (by omega)).trans h1)
  omega

/-- If the subtree of the last root `N` is `(M, N]`, it is a postorder tree on `[N - M]` once
shifted down by `M`. -/
private lemma isPostorderForest_shift_of_isAncestorOrSelf_iff {N M : ℕ} {par : ℕ → Option ℕ}
    (hpar : IsPostorderForest N par) (hM : M < N)
    (hanc : ∀ w, 1 ≤ w → w ≤ N → (IsAncestorOrSelf par N w ↔ M < w)) :
    IsPostorderForest (N - M) (fun u => if 1 ≤ u then (par (M + u)).map (· - M) else none) :=
  isPostorderForest_shift hpar hM.le fun a w ha haN hw1 hwN h =>
    (hanc w hw1 hwN).mp (((hanc a (by omega) haN).mpr ha).trans h)

/-- The marked leaves of a forest on `[N]` lying in `[M]` are marked leaves of its restriction
to `[M]`. -/
private lemma filter_le_subset_and_isLeaf {N M : ℕ} {par : ℕ → Option ℕ} {L : Finset ℕ}
    (hL : L ⊆ Finset.Icc 1 N) (hLleaf : ∀ v ∈ L, IsLeaf par v) :
    L.filter (· ≤ M) ⊆ Finset.Icc 1 M ∧
      ∀ v ∈ L.filter (· ≤ M), IsLeaf (fun v => if v ≤ M then par v else none) v := by
  refine ⟨fun w hw => ?_, fun v hv u hu => ?_⟩
  · rw [Finset.mem_filter] at hw
    have := Finset.mem_Icc.mp (hL hw.1)
    rw [Finset.mem_Icc]
    omega
  · rw [Finset.mem_filter] at hv
    dsimp only at hu
    split_ifs at hu
    exact hLleaf v hv.1 u hu

/-- The marked leaves of a forest on `[N]` above `M`, shifted down by `M`, are marked leaves of
its shift by `M`. -/
private lemma image_filter_lt_subset_and_isLeaf {N M : ℕ} {par : ℕ → Option ℕ}
    {L : Finset ℕ} (hpar : IsParentMap N par) (hL : L ⊆ Finset.Icc 1 N)
    (hLleaf : ∀ v ∈ L, IsLeaf par v) :
    (L.filter (M < ·)).image (· - M) ⊆ Finset.Icc 1 (N - M) ∧
      ∀ v ∈ (L.filter (M < ·)).image (· - M),
        IsLeaf (fun u => if 1 ≤ u then (par (M + u)).map (· - M) else none) v := by
  refine ⟨fun a ha => ?_, fun a ha u hu => ?_⟩
  · simp only [Finset.mem_image, Finset.mem_filter] at ha
    obtain ⟨w, ⟨hw, hw'⟩, rfl⟩ := ha
    have := Finset.mem_Icc.mp (hL hw)
    rw [Finset.mem_Icc]
    omega
  · simp only [Finset.mem_image, Finset.mem_filter] at ha
    obtain ⟨w, ⟨hw, hw'⟩, rfl⟩ := ha
    dsimp only at hu
    split_ifs at hu
    obtain ⟨q, hq, hqw⟩ := Option.map_eq_some_iff.mp hu
    have := hpar _ _ hq
    obtain rfl : q = w := by omega
    exact hLleaf q hw _ hq

/-- If the last root `N` is a marked leaf and its subtree is `(M, N]`, then `M = N - 1` and the
shifted last tree is the marked singleton. -/
private lemma eq_markedSingleton_of_isLeaf {N M : ℕ} {par : ℕ → Option ℕ} {L : Finset ℕ}
    (hpar : IsParentMap N par) (hL : L ⊆ Finset.Icc 1 N) (hM : M < N)
    (hanc : ∀ w, 1 ≤ w → w ≤ N → (IsAncestorOrSelf par N w ↔ M < w)) (hNL : N ∈ L)
    (hleaf : IsLeaf par N) :
    ((fun u => if 1 ≤ u then (par (M + u)).map (· - M) else none),
      (L.filter (M < ·)).image (· - M)) = markedSingleton ∧ N - M = 1 := by
  have hNM : N - M = 1 := by
    by_contra hne
    obtain ⟨u, hu⟩ := exists_child_of_isAncestorOrSelf
      ((hanc (N - 1) (by omega) (by omega)).mpr (by omega)) (by omega)
    exact hleaf u hu
  refine ⟨Prod.ext (funext fun u => ?_) ?_, hNM⟩
  · change (if 1 ≤ u then (par (M + u)).map (· - M) else none) = none
    split_ifs
    · cases h : par (M + u) with
      | none => rfl
      | some p =>
        have := hpar _ _ h
        omega
    · rfl
  · change (L.filter (M < ·)).image (· - M) = {1}
    ext a
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨w, ⟨hw, hw'⟩, rfl⟩
      have := Finset.mem_Icc.mp (hL hw)
      omega
    · rintro rfl
      exact ⟨N, ⟨hNL, hM⟩, by omega⟩

/-- If the last root `N` is unmarked and its subtree is `(M, N]`, the shifted last tree is
obtained by adjoining a root to the marked forest left by deleting its root. -/
private lemma exists_forestAdjoinRootParent_eq {N M : ℕ} {par parG : ℕ → Option ℕ}
    {L LG : Finset ℕ} (hpar : IsParentMap N par) (hL : L ⊆ Finset.Icc 1 N) (hM : M < N)
    (hanc : ∀ w, 1 ≤ w → w ≤ N → (IsAncestorOrSelf par N w ↔ M < w))
    (hparG : ∀ u, parG u = if 1 ≤ u then (par (M + u)).map (· - M) else none)
    (hLG : LG = (L.filter (M < ·)).image (· - M)) (hFG : IsPostorderForest (N - M) parG)
    (hLGleaf : ∀ v ∈ LG, IsLeaf parG v) (hNL : N ∉ L) :
    ∃ (par₂ : ℕ → Option ℕ) (L₂ : Finset ℕ),
      (IsPostorderForest (N - M - 1) par₂ ∧ L₂ ⊆ Finset.Icc 1 (N - M - 1) ∧
        ∀ v ∈ L₂, IsLeaf par₂ v) ∧
      parG = forestAdjoinRootParent (N - M - 1) par₂ ∧ LG = L₂ := by
  obtain ⟨par₂, hpar₂⟩ : ∃ f : ℕ → Option ℕ,
      ∀ u, f u = if parG u = some (N - M) then none else parG u := ⟨_, fun _ => rfl⟩
  refine ⟨par₂, LG, ⟨?_, fun a ha => ?_, fun v hv u hu => ?_⟩, ?_, rfl⟩
  · rw [show par₂ = _ from funext hpar₂]
    exact isPostorderForest_delete_root hFG
  · subst hLG
    simp only [Finset.mem_image, Finset.mem_filter] at ha
    obtain ⟨w, ⟨hw, hw'⟩, rfl⟩ := ha
    have := Finset.mem_Icc.mp (hL hw)
    have : w ≠ N := fun h => hNL (h ▸ hw)
    rw [Finset.mem_Icc]
    omega
  · rw [hpar₂] at hu
    split_ifs at hu
    exact hLGleaf v hv u hu
  funext v
  unfold forestAdjoinRootParent
  split_ifs with hv
  · obtain ⟨p, hp⟩ : ∃ p, parG v = some p := by
      obtain ⟨q, hq⟩ := exists_parent_of_isAncestorOrSelf
        ((hanc (M + v) (by omega) (by omega)).mpr (by omega)) (by omega)
      rw [hparG, if_pos hv.1, hq]
      exact ⟨_, rfl⟩
    rw [hpar₂, hp]
    split_ifs with h
    · obtain rfl := Option.some.inj h
      exact congrArg some (show N - M = N - M - 1 + 1 by omega)
    · rfl
  · rw [hparG]
    split_ifs
    · cases h : par (M + v) with
      | none => rfl
      | some p =>
        have := hpar _ _ h
        omega
    · rfl

/-- **Recursive decomposition of marked forests.** A marked postorder forest `(par, L)` on `[N]`
with `N ≥ 1` is the concatenation of a marked postorder forest `(par₁, L₁)` on `[N₁]` and a
marked postorder forest `(parG, LG)` on `[N₂]`, with `N₁ + N₂ = N` and `N₂ ≥ 1`, where
`(parG, LG)` is either the marked singleton (and `N₂ = 1`) or the tree obtained from a marked
postorder forest `(par₂, L₂)` on `[N₂ - 1]` by adjoining an unmarked root. -/
@[lognarayana "lem_forest_decomposition"]
public theorem exists_forestConcat_eq_of_isPostorderForest {N : ℕ} {par : ℕ → Option ℕ}
    {L : Finset ℕ} (hpar : IsPostorderForest N par) (hL : L ⊆ Finset.Icc 1 N)
    (hLleaf : ∀ v ∈ L, IsLeaf par v) (hN : 1 ≤ N) :
    ∃ N₁ N₂ : ℕ, N₁ + N₂ = N ∧ 1 ≤ N₂ ∧
      ∃ (par₁ : ℕ → Option ℕ) (L₁ : Finset ℕ),
        (IsPostorderForest N₁ par₁ ∧ L₁ ⊆ Finset.Icc 1 N₁ ∧ ∀ v ∈ L₁, IsLeaf par₁ v) ∧
      ∃ (parG : ℕ → Option ℕ) (LG : Finset ℕ),
        (IsPostorderForest N₂ parG ∧ LG ⊆ Finset.Icc 1 N₂ ∧ ∀ v ∈ LG, IsLeaf parG v) ∧
        par = forestConcatParent N₁ par₁ parG ∧ L = forestConcatMarked N₁ L₁ LG ∧
        (((parG, LG) = markedSingleton ∧ N₂ = 1) ∨
          ∃ (par₂ : ℕ → Option ℕ) (L₂ : Finset ℕ),
            (IsPostorderForest (N₂ - 1) par₂ ∧ L₂ ⊆ Finset.Icc 1 (N₂ - 1) ∧
              ∀ v ∈ L₂, IsLeaf par₂ v) ∧
            parG = forestAdjoinRootParent (N₂ - 1) par₂ ∧ LG = L₂) := by
  obtain ⟨M, hM, hanc⟩ := exists_lt_forall_isAncestorOrSelf_iff hpar hN
  have hFG := isPostorderForest_shift_of_isAncestorOrSelf_iff hpar hM hanc
  obtain ⟨hLGsub, hLGleaf⟩ := image_filter_lt_subset_and_isLeaf (M := M) hpar.1 hL hLleaf
  refine ⟨M, N - M, by omega, by omega, _, _,
    ⟨isPostorderForest_restrict_of_isAncestorOrSelf_iff hpar hM hanc,
      filter_le_subset_and_isLeaf (M := M) hL hLleaf⟩, _, _, ⟨hFG, hLGsub, hLGleaf⟩,
    eq_forestConcatParent_restrict_shift hpar.1, eq_forestConcatMarked_filter L M, ?_⟩
  by_cases hNL : N ∈ L
  · exact Or.inl (eq_markedSingleton_of_isLeaf hpar.1 hL hM hanc hNL (hLleaf N hNL))
  · exact Or.inr (exists_forestAdjoinRootParent_eq hpar.1 hL hM hanc (fun _ => rfl) rfl hFG
      hLGleaf hNL)
