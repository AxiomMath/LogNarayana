/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module
public import Mathlib
public import LogNarayana.Attr
public import LogNarayana.Zonotope.TreeZonotope.Defs
public import LogNarayana.Nestohedron.Fertilitope.Defs
public import LogNarayana.Zonotope.OrientationSum.Defs
public import LogNarayana.Polynomial.RealStable.Defs
public import LogNarayana.Narayana.Polynomials.Defs
public import LogNarayana.Zonotope.OrientationSum.Basic
public import LogNarayana.Polynomial.RealStable.Basic
public import LogNarayana.Narayana.Polynomials.Basic

/-!
# Lattice points of tree zonotopes

Let `G` be a forest on the vertex set `V` and `a` an integer vector. Every lattice point of the
polytope `P_{G,a} = a + ∑_e Δ_{{s(e), t(e)}}` is `a + indeg_h` for exactly one orientation `h`
of `G`, so `h ↦ a + indeg_h` is a bijection from the orientations `Or(G)` onto the lattice
points of `P_{G,a}`. The proof deletes a leaf edge, which a nonempty finite forest always has.

Reindexing along this bijection, the sum `∑_q ∏_v Ñ_{q_v - 1}(x)` over the lattice points of a
tree zonotope with `a > 0` is the orientation sum `O_{G,a}`: it is real-rooted, has nonnegative
coefficients and a positive constant term, so all of its zeros are negative. Since every lattice
point has `q_v ≥ 1`, the Narayana sum `∑_q ∏_v N_{q_v}(x)` is `x^{|V|}` times it, hence
real-rooted. For the path `1 - 2 - 3 - 4` and `a = 𝟏` the eight lattice points and the value
`8 + 28x + 28x² + 8x³ = 4(1 + x)(x + 2)(2x + 1)` of the sum are computed explicitly.

## Main results

* `LooplessMultigraph.IsForest.exists_unique_incident_edge`: a nonempty finite forest has a
  vertex incident to exactly one edge.
* `Polynomial.hasOnlyNegativeRoots_of_splits_of_coeff_nonneg`: a real-rooted `f ∈ ℝ[x]` with
  nonnegative coefficients and `f(0) > 0` has only negative real zeros.
* `LooplessMultigraph.add_indegree_mem_latticePoints_zonotope`: `a + indeg_h ∈ P_{G,a} ∩ ℤ^V`.
* `LooplessMultigraph.IsForest.existsUnique_orientation_of_mem_latticePoints_zonotope`: every
  lattice point of a forest zonotope comes from a unique orientation.
* `LooplessMultigraph.IsForest.bijOn_add_indegree_orientations_latticePoints_zonotope`: the
  orientations parametrize the lattice points.
* `LooplessMultigraph.latticePoints_zonotope_path_four`,
  `LooplessMultigraph.finsum_latticePoints_zonotope_path_four`,
  `LooplessMultigraph.finsum_latticePoints_zonotope_path_four_eq_mul`: the path on four vertices.
* `LooplessMultigraph.IsForest.hasOnlyNegativeRoots_finsum_latticePoints_zonotope`: the shifted
  Narayana sum over a tree zonotope has only negative zeros.
* `LooplessMultigraph.IsForest.splits_finsum_latticePoints_zonotope`: the Narayana sum over a
  tree zonotope is real-rooted.

## Implementation notes

The paper takes the vertex set `[r]` and real scalars. The lattice-point lemmas are stated for
an arbitrary vertex type with decidable equality, finitely many edges, and any linearly ordered
ring `R` with strict order; the integer vectors `a` and `indeg_h` enter through the casts
`ℤ → R` and `ℕ → R`. In the Narayana sums, a lattice point of `P_{G,a} ⊆ ℝ^V` is an integer
vector `q : V → ℤ` whose cast lies in `(P_{G,a}).latticePoints`, its coordinates are read in `ℕ`
through `Int.toNat`, and the sum is a `finsum` (the set is finite, being in bijection with the
orientations). The cited results the proofs rest on are taken as hypotheses:
`RealStablePreserverOfSymbol` (Borcea–Brändén), `ShiftedNarayanaGammaExpansion` and
`ShiftedNarayanaNegRealRoots` (Liu–Wang).

## References

* [LogNarayana] *Log-Concavity in Narayana Transforms and Stack-Sorting Fibers*, Section on
  lattice points of tree zonotopes.
-/

/-! ### Leaves of forests -/

namespace LooplessMultigraph

section Leaf

open SimpleGraph

variable {V E : Type*}

/-- An acyclic simple graph with finitely many edges and at least one edge has a vertex `u` with
exactly one neighbour `w`: the start of a longest path. -/
private lemma exists_adj_forall_adj_eq {V : Type*} {S : SimpleGraph V} [Finite S.edgeSet]
    (h : S.IsAcyclic) {a b : V} (hab : S.Adj a b) :
    ∃ u w, S.Adj u w ∧ ∀ x, S.Adj u x → x = w := by
  have : Nonempty V := ⟨a⟩
  obtain ⟨u, v, p, hp, hmax⟩ := Walk.exists_isPath_forall_isPath_length_le_length S
  have hnil : ¬p.Nil := fun hn => by
    simpa [Walk.length_eq_zero_iff.mpr hn] using hmax _ _ _ (Path.singleton hab).2
  refine ⟨u, p.snd, p.adj_snd hnil, fun x hx => h.eq_snd_of_adj_start hp hx ?_⟩
  by_contra hns
  simpa using hmax _ _ _ (hp.cons (by simpa using hns) (h := hx.symm))

/-- A forest with finitely many edges and at least one edge has a vertex `v` and an edge `e₀`
with `v` an endpoint of `e₀`, such that `e₀` is the only edge having `v` as an endpoint. -/
@[lognarayana "lem_forest_leaf"]
public theorem IsForest.exists_unique_incident_edge [Finite E] [Nonempty E]
    {G : LooplessMultigraph V E} (hG : G.IsForest) :
    ∃ (v : V) (e₀ : E), (G.src e₀ = v ∨ G.tgt e₀ = v) ∧
      ∀ e : E, (G.src e = v ∨ G.tgt e = v) → e = e₀ := by
  obtain ⟨hinj, hac⟩ := hG
  set S := fromEdgeSet (Set.range fun e => s(G.src e, G.tgt e))
  have hadj (e : E) : S.Adj (G.src e) (G.tgt e) :=
    (fromEdgeSet_adj _).mpr ⟨⟨e, rfl⟩, G.src_ne_tgt e⟩
  have : Finite S.edgeSet := by
    rw [edgeSet_fromEdgeSet]; exact ((Set.finite_range _).subset Set.sdiff_subset).to_subtype
  obtain ⟨u, w, huw, huniq⟩ := exists_adj_forall_adj_eq hac (hadj (Classical.arbitrary E))
  obtain ⟨⟨e₀, he₀⟩, -⟩ := (fromEdgeSet_adj _).mp huw
  refine ⟨u, e₀, ?_, fun e he => hinj ?_⟩
  · have hu : u ∈ s(G.src e₀, G.tgt e₀) := by
      simp only at he₀; rw [he₀]; exact Sym2.mem_mk_left _ _
    simpa [eq_comm] using hu
  · simp only [he₀]
    rcases he with h | h
    · rw [← huniq _ (h ▸ hadj e), h]
    · rw [← huniq _ (h ▸ (hadj e).symm), h, Sym2.eq_swap]

end Leaf

end LooplessMultigraph

/-! ### Polynomials with nonnegative coefficients -/

section NonnegCoeff

open Polynomial

/-- A polynomial with nonnegative coefficients is at least its constant term at every
nonnegative point. -/
private lemma eval_zero_le_eval_of_coeff_nonneg {R : Type*} [CommSemiring R] [PartialOrder R]
    [IsOrderedRing R] {f : R[X]} (hcoeff : ∀ n, 0 ≤ f.coeff n) {r : R} (hr : 0 ≤ r) :
    f.eval 0 ≤ f.eval r := by
  rw [← coeff_zero_eq_eval_zero, eval_eq_sum_range]
  simpa using Finset.single_le_sum (f := fun i => f.coeff i * r ^ i)
    (fun i _ => mul_nonneg (hcoeff i) (pow_nonneg hr i)) (Finset.mem_range.2 f.natDegree.succ_pos)

/-- A real-rooted real polynomial with nonnegative coefficients and positive value at `0` has
only negative real zeros. -/
@[lognarayana "lem_nonneg_coeff_pos_const_negative_zeros"]
public theorem Polynomial.hasOnlyNegativeRoots_of_splits_of_coeff_nonneg {f : Polynomial ℝ}
    (hf : f.Splits) (hcoeff : ∀ n, 0 ≤ f.coeff n) (h0 : 0 < f.eval 0) :
    f.HasOnlyNegativeRoots :=
  ⟨hf, fun _ hr => not_le.mp fun hr0 => h0.not_ge <|
    (mem_roots'.mp hr).2 ▸ eval_zero_le_eval_of_coeff_nonneg hcoeff hr0⟩

end NonnegCoeff

namespace LooplessMultigraph

/-! ### Orientation points of `P_{G,a}` -/

section OrientationMem

variable {R : Type*} {V E : Type*} [Ring R] [PartialOrder R] [DecidableEq V] [Fintype E]

/-- For an orientation `h ∈ Or(G)` and an integer vector `a`, the point
`a + (indeg_h(v))_v` is a lattice point of the polytope `P_{G,a}`. -/
@[lognarayana "lem_tree_zonotope_orientation_mem"]
public theorem add_indegree_mem_latticePoints_zonotope (G : LooplessMultigraph V E) (a : V → ℤ)
    {h : E → V} (hh : h ∈ G.orientations) :
    (fun v => (a v : R) + (indegree h v : R)) ∈
      (G.zonotope (fun v => (a v : R))).latticePoints := by
  refine ⟨⟨fun e => Pi.single (h e) 1, fun e => subset_convexHull _ _ ⟨h e, ?_, rfl⟩, ?_⟩,
    fun v => ⟨a v + indegree h v, by push_cast; rfl⟩⟩
  · rcases hh e with he | he <;> simp [he]
  · funext v
    simp [indegree, Finsupp.finsetSum_apply, Finset.sum_apply, Pi.single_apply,
      Finsupp.single_apply, eq_comm]

end OrientationMem

/-! ### Unique orientations of lattice points -/

section UniqueOrientation

variable {V : Type*} [DecidableEq V]

/-- The multigraph `G` with the edge `e₀` deleted. -/
private def deleteEdge {E : Type*} (G : LooplessMultigraph V E) (e₀ : E) :
    LooplessMultigraph V {e // e ≠ e₀} where
  src e := G.src e
  tgt e := G.tgt e
  src_ne_tgt e := G.src_ne_tgt e

omit [DecidableEq V] in
private lemma isForest_deleteEdge {E : Type*} {G : LooplessMultigraph V E} (hG : G.IsForest)
    (e₀ : E) : (deleteEdge G e₀).IsForest := by
  refine ⟨fun e e' h => Subtype.val_injective (hG.1 h), hG.2.anti ?_⟩
  apply SimpleGraph.fromEdgeSet_mono
  rintro _ ⟨e, rfl⟩
  exact ⟨e.1, rfl⟩

omit [DecidableEq V] in
private lemma indegree_eq_single_add {E : Type*} [Fintype E] [DecidableEq E] (h : E → V)
    (e₀ : E) : indegree h = Finsupp.single (h e₀) 1 + indegree (fun e : {e // e ≠ e₀} => h e) :=
  Fintype.sum_eq_add_sum_subtype_ne _ e₀

private lemma indegree_apply {E : Type*} [Fintype E] (h : E → V) (v : V) :
    indegree h v = ∑ e, if h e = v then 1 else 0 := by
  simp [indegree, Finsupp.finsetSum_apply, Finsupp.single_apply]

private lemma mem_coordSimplex_pair {R : Type*} [Ring R] [PartialOrder R] [IsOrderedRing R]
    {x y : V} {p : V → R} :
    p ∈ coordSimplex R {x, y} ↔ ∃ α β : R, 0 ≤ α ∧ 0 ≤ β ∧ α + β = 1 ∧
      p = α • Pi.single x 1 + β • Pi.single y 1 := by
  rw [coordSimplex, Set.image_pair, convexHull_pair, segment, Set.mem_ofPred_eq]
  simp only [eq_comm]

private lemma coordSimplex_pair_apply_eq_zero {R : Type*} [Ring R] [PartialOrder R]
    [IsOrderedRing R] {x y w : V} {p : V → R} (hp : p ∈ coordSimplex R {x, y}) (hx : x ≠ w)
    (hy : y ≠ w) : p w = 0 := by
  obtain ⟨α, β, -, -, -, rfl⟩ := mem_coordSimplex_pair.1 hp
  simp [hx.symm, hy.symm]

/-- A point of the segment `[e_x, e_y]` with an integer `x`-coordinate is `e_x` or `e_y`. -/
private lemma eq_single_of_mem_coordSimplex_pair_left {R : Type*} [Ring R] [LinearOrder R]
    [IsStrictOrderedRing R] {x y : V} {p : V → R} (hp : p ∈ coordSimplex R {x, y})
    (hxy : x ≠ y) (hint : p x ∈ Set.range (Int.cast : ℤ → R)) :
    p = Pi.single x 1 ∨ p = Pi.single y 1 := by
  obtain ⟨α, β, hα, hβ, hαβ, rfl⟩ := mem_coordSimplex_pair.1 hp
  obtain ⟨n, hn⟩ := hint
  have hn' : (n : R) = α := by simpa [Pi.single_apply, hxy.symm] using hn
  have h0 : 0 ≤ n := by exact_mod_cast hn' ▸ hα
  have h1 : n ≤ 1 := by exact_mod_cast hn' ▸ (le_add_of_nonneg_right hβ).trans_eq hαβ
  obtain rfl | rfl : n = 0 ∨ n = 1 := by omega
  · obtain rfl : α = 0 := by simpa using hn'.symm
    obtain rfl : β = 1 := by simpa using hαβ
    simp
  · obtain rfl : α = 1 := by simpa using hn'.symm
    obtain rfl : β = 0 := by simpa using hαβ
    simp

/-- A point of an edge segment with an integer coordinate at an endpoint is a vertex. -/
private lemma eq_single_of_mem_coordSimplex_pair {R : Type*} [Ring R] [LinearOrder R]
    [IsStrictOrderedRing R] {x y v : V} {p : V → R} (hp : p ∈ coordSimplex R {x, y})
    (hxy : x ≠ y) (hv : x = v ∨ y = v) (hint : p v ∈ Set.range (Int.cast : ℤ → R)) :
    ∃ z, (z = x ∨ z = y) ∧ p = Pi.single z 1 := by
  rcases hv with rfl | rfl
  · rcases eq_single_of_mem_coordSimplex_pair_left hp hxy hint with h | h
    exacts [⟨_, Or.inl rfl, h⟩, ⟨_, Or.inr rfl, h⟩]
  · rw [Set.pair_comm] at hp
    rcases eq_single_of_mem_coordSimplex_pair_left hp hxy.symm hint with h | h
    exacts [⟨_, Or.inr rfl, h⟩, ⟨_, Or.inl rfl, h⟩]

/-- Existence: a sum of edge-segment points with integer coordinates is an in-degree vector. -/
private theorem exists_orientation (R : Type*) [Ring R] [LinearOrder R] [IsStrictOrderedRing R]
    (n : ℕ) {E : Type*} [Fintype E] (G : LooplessMultigraph V E) (hn : Fintype.card E = n)
    (hG : G.IsForest) (p : E → V → R) (hp : ∀ e, p e ∈ coordSimplex R {G.src e, G.tgt e})
    (hint : ∀ v, ∑ e, p e v ∈ Set.range (Int.cast : ℤ → R)) :
    ∃ h ∈ G.orientations, ∀ v, ∑ e, p e v = (indegree h v : R) := by
  classical
  induction n generalizing E with
  | zero =>
    have : IsEmpty E := Fintype.card_eq_zero_iff.1 hn
    exact ⟨fun e => isEmptyElim e, fun e => isEmptyElim e, fun v => by simp [indegree_apply]⟩
  | succ n ih =>
    have : Nonempty E := Fintype.card_pos_iff.1 (by omega)
    obtain ⟨v, e₀, hv, hleaf⟩ := hG.exists_unique_incident_edge
    have hzero : ∀ e : {e // e ≠ e₀}, p e v = 0 := fun e =>
      coordSimplex_pair_apply_eq_zero (hp e) (fun h => e.2 (hleaf e (Or.inl h)))
        (fun h => e.2 (hleaf e (Or.inr h)))
    have hsplit : ∀ w, ∑ e, p e w = p e₀ w + ∑ e : {e // e ≠ e₀}, p e w := fun w =>
      Fintype.sum_eq_add_sum_subtype_ne (fun e => p e w) e₀
    have hv' : p e₀ v ∈ Set.range (Int.cast : ℤ → R) := by
      simpa [hsplit, hzero] using hint v
    obtain ⟨y, hy, hpy⟩ := eq_single_of_mem_coordSimplex_pair (hp e₀) (G.src_ne_tgt e₀) hv hv'
    obtain ⟨h', hh', hind'⟩ := ih (deleteEdge G e₀)
      (by rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]; omega)
      (isForest_deleteEdge hG e₀) (fun e => p e) (fun e => hp e) (fun w => by
        obtain ⟨m, hm⟩ := hint w
        refine ⟨m - (Pi.single y (1 : ℤ) : V → ℤ) w, ?_⟩
        rw [hsplit, hpy] at hm
        have : ((Pi.single y (1 : ℤ) : V → ℤ) w : R) = (Pi.single y (1 : R) : V → R) w := by
          simp only [Pi.single_apply]; split_ifs <;> simp
        rw [Int.cast_sub, hm, this]; abel)
    refine ⟨fun e => if he : e = e₀ then y else h' ⟨e, he⟩, fun e => ?_, fun w => ?_⟩
    · by_cases he : e = e₀
      · subst he; simpa using hy
      · simp only [dif_neg he]; exact hh' ⟨e, he⟩
    · rw [indegree_eq_single_add _ e₀, hsplit, hpy]
      have hr : (fun e : {e // e ≠ e₀} => if he : (e : E) = e₀ then y else h' ⟨e, he⟩) = h' := by
        funext e; simp [e.2]
      simp only [dif_pos, hr, Finsupp.add_apply, Nat.cast_add]
      rw [← hind' w]
      congr 1
      by_cases hw : w = y
      · subst hw; simp
      · simp [hw]

omit [DecidableEq V] in
/-- Uniqueness: on a forest, an orientation is determined by its in-degree vector. -/
private theorem eq_of_indegree_eq (n : ℕ) {E : Type*} [Fintype E] (G : LooplessMultigraph V E)
    (hn : Fintype.card E = n) (hG : G.IsForest) {h₁ h₂ : E → V} (hh₁ : h₁ ∈ G.orientations)
    (hh₂ : h₂ ∈ G.orientations) (heq : indegree h₁ = indegree h₂) : h₁ = h₂ := by
  classical
  induction n generalizing E with
  | zero =>
    have : IsEmpty E := Fintype.card_eq_zero_iff.1 hn
    exact funext fun e => isEmptyElim e
  | succ n ih =>
    have : Nonempty E := Fintype.card_pos_iff.1 (by omega)
    obtain ⟨v, e₀, hv, hleaf⟩ := hG.exists_unique_incident_edge
    have hrest : ∀ h ∈ G.orientations, indegree (fun e : {e // e ≠ e₀} => h e) v = 0 := by
      intro h hh
      rw [indegree_apply]
      refine Finset.sum_eq_zero fun e _ => if_neg fun hev => e.2 (hleaf e ?_)
      rcases hh e with h' | h' <;> [exact Or.inl (h' ▸ hev); exact Or.inr (h' ▸ hev)]
    have key := congrArg (· v) heq
    simp only [indegree_eq_single_add _ e₀, Finsupp.add_apply, hrest _ hh₁, hrest _ hh₂,
      add_zero, Finsupp.single_apply] at key
    have he₀ : h₁ e₀ = h₂ e₀ := by
      have hne := G.src_ne_tgt e₀
      rcases hh₁ e₀ with h1 | h1 <;> rcases hh₂ e₀ with h2 | h2 <;> rcases hv with hv | hv <;>
        rw [h1, h2] at key ⊢ <;> subst hv <;> simp_all [eq_comm]
    have hr : (fun e : {e // e ≠ e₀} => h₁ e) = fun e : {e // e ≠ e₀} => h₂ e := by
      refine ih (deleteEdge G e₀)
        (by rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]; omega)
        (isForest_deleteEdge hG e₀) (fun e => hh₁ e) (fun e => hh₂ e) ?_
      have := heq
      rw [indegree_eq_single_add _ e₀, indegree_eq_single_add h₂ e₀, he₀] at this
      exact add_left_cancel this
    funext e
    by_cases he : e = e₀
    · subst he; exact he₀
    · exact congrFun hr ⟨e, he⟩

end UniqueOrientation

section Bijection

variable {R : Type*} {V E : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R]
  [DecidableEq V] [Fintype E]

/-- For a forest `G`, an integer vector `a` and a lattice point `q` of `P_{G,a}`, there is
exactly one orientation `h ∈ Or(G)` with `q = a + (indeg_h(v))_v`. -/
@[lognarayana "lem_tree_zonotope_unique_orientation"]
public theorem IsForest.existsUnique_orientation_of_mem_latticePoints_zonotope
    {G : LooplessMultigraph V E} (hG : G.IsForest) (a : V → ℤ) {q : V → R}
    (hq : q ∈ (G.zonotope (fun v => (a v : R))).latticePoints) :
    ∃! h : E → V, h ∈ G.orientations ∧ q = fun v => (a v : R) + (indegree h v : R) := by
  obtain ⟨⟨p, hp, rfl⟩, hint⟩ := hq
  have hint' : ∀ v, ∑ e, p e v ∈ Set.range (Int.cast : ℤ → R) := fun v => by
    obtain ⟨m, hm⟩ := hint v
    refine ⟨m - a v, ?_⟩
    rw [Int.cast_sub, hm]
    simp
  obtain ⟨h, hh, hind⟩ := exists_orientation R _ G rfl hG p hp hint'
  have hpt : ((fun v => (a v : R)) + ∑ e, p e) = fun v => (a v : R) + (indegree h v : R) := by
    funext v; simp [Finset.sum_apply, hind]
  refine ⟨h, ⟨hh, hpt⟩, ?_⟩
  rintro h' ⟨hh', hq'⟩
  refine eq_of_indegree_eq _ G rfl hG hh' hh (Finsupp.ext fun v => ?_)
  have := congrFun (hq'.symm.trans hpt) v
  exact_mod_cast add_left_cancel this

/-- For a forest `G` and an integer vector `a`, the map `h ↦ a + (indeg_h(v))_v` is a bijection
from the orientations `Or(G)` onto the lattice points of the zonotope `P_{G,a}`. -/
@[lognarayana "lem_tree_zonotope_orientation_bijection"]
public theorem IsForest.bijOn_add_indegree_orientations_latticePoints_zonotope
    {G : LooplessMultigraph V E} (hG : G.IsForest) (a : V → ℤ) :
    Set.BijOn (fun h : E → V => fun v => (a v : R) + (indegree h v : R)) G.orientations
      (G.zonotope (fun v => (a v : R))).latticePoints := by
  refine ⟨fun h hh => G.add_indegree_mem_latticePoints_zonotope a hh,
    fun h₁ hh₁ h₂ hh₂ heq => ?_, fun q hq => ?_⟩
  · exact (hG.existsUnique_orientation_of_mem_latticePoints_zonotope a
      (G.add_indegree_mem_latticePoints_zonotope (R := R) a hh₁)).unique ⟨hh₁, rfl⟩ ⟨hh₂, heq⟩
  · obtain ⟨h, ⟨hh, rfl⟩, -⟩ := hG.existsUnique_orientation_of_mem_latticePoints_zonotope a hq
    exact ⟨h, hh, rfl⟩

end Bijection

/-! ### The path on four vertices -/

section PathFour

open SimpleGraph Polynomial

/-- The path on `Fin 4` with edges `i — i + 1`. -/
private abbrev pathFour : LooplessMultigraph (Fin 4) (Fin 3) :=
  ⟨Fin.castSucc, Fin.succ, fun i => (Fin.castSucc_lt_succ (i := i)).ne⟩

private lemma isForest_pathFour : pathFour.IsForest := by
  have hinj : Function.Injective (fun e : Fin 3 => s(Fin.castSucc e, Fin.succ e)) := by decide
  refine ⟨hinj, ?_⟩
  have hP : SimpleGraph.fromEdgeSet (Set.range fun e : Fin 3 => s(Fin.castSucc e, Fin.succ e)) =
      pathGraph 4 := by
    ext u v
    simp only [fromEdgeSet_adj, Set.mem_range, pathGraph_adj]
    fin_cases u <;> fin_cases v <;> simp [Fin.exists_fin_succ]
  refine ((isTree_iff_connected_and_card).2 ⟨hP ▸ pathGraph_connected 3, ?_⟩).isAcyclic
  rw [edgeSet_fromEdgeSet, sdiff_eq_left.2, Nat.card_range_of_injective hinj]
  · simp
  · rw [Set.disjoint_left]
    rintro _ ⟨e, rfl⟩ hd
    exact (Fin.castSucc_lt_succ (i := e)).ne (Sym2.mk_isDiag_iff.1 hd)

private lemma indegree_apply_fin_three (h : Fin 3 → Fin 4) (v : Fin 4) :
    indegree h v = (if h 0 = v then 1 else 0) + (if h 1 = v then 1 else 0) +
      (if h 2 = v then 1 else 0) := by
  simp [indegree, Fin.sum_univ_three, Finsupp.single_apply]

/-- The eight orientations of the path `1 - 2 - 3 - 4`: each edge `i — i + 1` points to `i` or
to `i + 1`. -/
private lemma orientations_pathFour : pathFour.orientations =
    {![0, 1, 2], ![0, 1, 3], ![0, 2, 2], ![0, 2, 3],
      ![1, 1, 2], ![1, 1, 3], ![1, 2, 2], ![1, 2, 3]} := by
  ext h
  simp only [orientations, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  revert h
  decide

/-- For the path `1 - 2 - 3 - 4` (vertices `Fin 4`, edge `i : Fin 3` joining `i` and `i + 1`)
and the translate `𝟏 = (1,1,1,1)`, the lattice points of the zonotope `P_{G,𝟏}` are exactly the
eight points `(2,2,2,1)`, `(2,2,1,2)`, `(2,1,3,1)`, `(2,1,2,2)`, `(1,3,2,1)`, `(1,3,1,2)`,
`(1,2,3,1)`, `(1,2,2,2)`. -/
@[lognarayana "lem_path_zonotope_lattice_points"]
public theorem latticePoints_zonotope_path_four :
    ((⟨Fin.castSucc, Fin.succ, fun i => (Fin.castSucc_lt_succ (i := i)).ne⟩ :
        LooplessMultigraph (Fin 4) (Fin 3)).zonotope (fun _ => (1 : ℝ))).latticePoints =
      {![2, 2, 2, 1], ![2, 2, 1, 2], ![2, 1, 3, 1], ![2, 1, 2, 2],
        ![1, 3, 2, 1], ![1, 3, 1, 2], ![1, 2, 3, 1], ![1, 2, 2, 2]} := by
  have hB := isForest_pathFour.bijOn_add_indegree_orientations_latticePoints_zonotope
    (R := ℝ) (fun _ => 1)
  simp only [Int.cast_one] at hB
  rw [← hB.image_eq, orientations_pathFour]
  simp only [Set.image_insert_eq, Set.image_singleton]
  iterate 7 (refine congr_arg₂ (@insert _ (Set (Fin 4 → ℝ)) _) ?_ ?_; swap)
  all_goals simp [indegree_apply_fin_three, funext_iff, Fin.forall_fin_succ]; norm_num

/-- The lattice points of the zonotope of the path `1 - 2 - 3 - 4`, as membership of an integer
vector in the explicit eight-element `Finset`. -/
private lemma mem_latticePoints_zonotope_path_four_iff (q : Fin 4 → ℤ) :
    (fun v => (q v : ℝ)) ∈
        ((⟨Fin.castSucc, Fin.succ, fun i => (Fin.castSucc_lt_succ (i := i)).ne⟩ :
          LooplessMultigraph (Fin 4) (Fin 3)).zonotope (fun _ => (1 : ℝ))).latticePoints ↔
      q ∈ ({![2, 2, 2, 1], ![2, 2, 1, 2], ![2, 1, 3, 1], ![2, 1, 2, 2],
        ![1, 3, 2, 1], ![1, 3, 1, 2], ![1, 2, 3, 1], ![1, 2, 2, 2]} : Finset (Fin 4 → ℤ)) := by
  rw [latticePoints_zonotope_path_four]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton,
    funext_iff, Fin.forall_fin_succ, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, IsEmpty.forall_iff, and_true]
  norm_cast

/-- For the path `1 - 2 - 3 - 4` (vertices `Fin 4`, edge `i : Fin 3` joining `i` and `i + 1`)
and the translate `𝟏 = (1,1,1,1)`,
`∑_{q ∈ P_{G,𝟏} ∩ ℤ^4} ∏_v Ñ_{q_v - 1}(x) = 8 + 28x + 28x² + 8x³`. -/
@[lognarayana "lem_path_zonotope_narayana_sum"]
public theorem finsum_latticePoints_zonotope_path_four :
    (∑ᶠ (q : Fin 4 → ℤ) (_ : (fun v => (q v : ℝ)) ∈
        ((⟨Fin.castSucc, Fin.succ, fun i => (Fin.castSucc_lt_succ (i := i)).ne⟩ :
          LooplessMultigraph (Fin 4) (Fin 3)).zonotope (fun _ => (1 : ℝ))).latticePoints),
      ∏ v, shiftedNarayanaPolynomial (q v - 1).toNat) =
      8 + 28 * X + 28 * X ^ 2 + 8 * X ^ 3 := by
  simp_rw [mem_latticePoints_zonotope_path_four_iff, ← Finset.mem_coe, finsum_mem_coe_finset]
  simp [Finset.sum_insert, Fin.prod_univ_four, shiftedNarayanaPolynomial_zero,
    shiftedNarayanaPolynomial_one, shiftedNarayanaPolynomial_two]
  ring

/-- For the path `1 - 2 - 3 - 4` (vertices `Fin 4`, edge `i : Fin 3` joining `i` and `i + 1`)
and the translate `𝟏 = (1,1,1,1)`,
`∑_{q ∈ P_{G,𝟏} ∩ ℤ^4} ∏_v Ñ_{q_v - 1}(x) = 4(1 + x)(x + 2)(2x + 1)`. -/
@[lognarayana "lem_path_zonotope_narayana_sum_factored"]
public theorem finsum_latticePoints_zonotope_path_four_eq_mul :
    (∑ᶠ (q : Fin 4 → ℤ) (_ : (fun v => (q v : ℝ)) ∈
        ((⟨Fin.castSucc, Fin.succ, fun i => (Fin.castSucc_lt_succ (i := i)).ne⟩ :
          LooplessMultigraph (Fin 4) (Fin 3)).zonotope (fun _ => (1 : ℝ))).latticePoints),
      ∏ v, shiftedNarayanaPolynomial (q v - 1).toNat) =
      4 * (1 + X) * (X + 2) * (2 * X + 1) := by
  rw [finsum_latticePoints_zonotope_path_four]
  ring

end PathFour

/-! ### Narayana sums over tree zonotopes -/

section NarayanaSums

open Polynomial

universe u

variable {V E : Type u} [Fintype V] [DecidableEq V] [Fintype E]

/-- The coefficients of `Ñ_m` are nonnegative. -/
private lemma coeff_shiftedNarayanaPolynomial_nonneg (m n : ℕ) :
    0 ≤ (shiftedNarayanaPolynomial m).coeff n := by
  rw [shiftedNarayanaPolynomial, finsetSum_coeff]
  refine Finset.sum_nonneg fun j _ => ?_
  rw [coeff_C_mul_X_pow]
  split_ifs <;> positivity

/-- `Ñ_m(0) = 1`. -/
private lemma eval_zero_shiftedNarayanaPolynomial (m : ℕ) :
    (shiftedNarayanaPolynomial m).eval 0 = 1 := by
  rw [← coeff_zero_eq_eval_zero, shiftedNarayanaPolynomial, finsetSum_coeff]
  simp
  field_simp

/-- The coefficients of the orientation sum `O_{G,a}` are nonnegative: it is a sum of products
of shifted Narayana polynomials, each with nonnegative coefficients. -/
private lemma coeff_orientationSum_nonneg [DecidableEq E] (G : LooplessMultigraph V E)
    (a : V → ℕ) (n : ℕ) : 0 ≤ (G.orientationSum a).coeff n := by
  rw [orientationSum, finsetSum_coeff]
  refine Finset.sum_nonneg fun h _ => ?_
  refine Finset.prod_induction _ (fun p : ℝ[X] => ∀ n, 0 ≤ p.coeff n)
    (fun p q hp hq n => ?_) (fun n => ?_) (fun v _ => coeff_shiftedNarayanaPolynomial_nonneg _) n
  · rw [coeff_mul]
    exact Finset.sum_nonneg fun x _ => mul_nonneg (hp _) (hq _)
  · rw [coeff_one]; split_ifs <;> norm_num

/-- `O_{G,a}(0) = |Or(G)| > 0`. -/
private lemma eval_zero_orientationSum_pos [DecidableEq E] (G : LooplessMultigraph V E)
    (a : V → ℕ) : 0 < (G.orientationSum a).eval 0 := by
  simp only [orientationSum, eval_finsetSum, eval_prod, eval_zero_shiftedNarayanaPolynomial,
    Finset.prod_const_one, Finset.sum_const, nsmul_eq_mul, mul_one, Nat.cast_pos, Finset.card_pos]
  exact ⟨G.src, Fintype.mem_piFinset.2 fun e => by simp⟩

/-- For a forest `G` and a positive integer vector `a`, the Narayana sum over the lattice points
of the tree zonotope `P_{G,a}` is the orientation sum `O_{G,a}`: the lattice points are the
vectors `a + indeg_h`, each attained by exactly one orientation `h`. -/
private lemma finsum_latticePoints_zonotope_eq_orientationSum [DecidableEq E]
    {G : LooplessMultigraph V E} (hG : G.IsForest) (a : V → ℤ) (ha : ∀ v, 0 < a v) :
    (∑ᶠ (q : V → ℤ) (_ : (fun v => (q v : ℝ)) ∈
        (G.zonotope (fun v => (a v : ℝ))).latticePoints),
      ∏ v, shiftedNarayanaPolynomial (q v - 1).toNat) =
      G.orientationSum (fun v => (a v).toNat) := by
  set f : (E → V) → V → ℤ := fun h v => a v + (indegree h v : ℤ)
  have hB : Set.BijOn (fun h v => ((f h v : ℤ) : ℝ)) G.orientations
      (G.zonotope (fun v => (a v : ℝ))).latticePoints := by
    simpa [f] using hG.bijOn_add_indegree_orientations_latticePoints_zonotope (R := ℝ) a
  have hcast : Function.Injective (fun (q : V → ℤ) (v : V) => (q v : ℝ)) :=
    fun q q' hq => funext fun v => Int.cast_injective (congrFun hq v)
  have hS : {q : V → ℤ | (fun v => (q v : ℝ)) ∈
      (G.zonotope (fun v => (a v : ℝ))).latticePoints} = f '' G.orientations := by
    ext q
    simp only [Set.mem_ofPred_eq, ← hB.image_eq, Set.mem_image]
    exact exists_congr fun h => and_congr_right fun _ => hcast.eq_iff
  change ∑ᶠ q ∈ {q : V → ℤ | (fun v => (q v : ℝ)) ∈
      (G.zonotope (fun v => (a v : ℝ))).latticePoints}, _ = _
  have orientations_eq_piFinset : G.orientations =
      ↑(Fintype.piFinset fun e => ({G.src e, G.tgt e} : Finset V)) := by
    ext h; simp [orientations]
  rw [hS, finsum_mem_image fun h hh h' hh' e =>
      hB.injOn hh hh' (congrArg (fun q v => (q v : ℝ)) e), orientations_eq_piFinset,
    finsum_mem_coe_finset, orientationSum]
  refine Finset.sum_congr rfl fun h _ => Finset.prod_congr rfl fun v _ => ?_
  have := ha v
  congr 1
  simp only [f]
  omega

/-- For a forest `G` and a positive integer vector `a`, the polynomial
`∑_{q ∈ P_{G,a} ∩ ℤ^V} ∏_v Ñ_{q_v - 1}(x)` has only negative real zeros. -/
@[lognarayana "thm_tree_zonotope_negative"]
public theorem IsForest.hasOnlyNegativeRoots_finsum_latticePoints_zonotope
    (hBB : ∀ σ : Type u, RealStablePreserverOfSymbol σ)
    (hLW : ShiftedNarayanaNegRealRoots)
    {G : LooplessMultigraph V E} (hG : G.IsForest) (a : V → ℤ) (ha : ∀ v, 0 < a v) :
    (∑ᶠ (q : V → ℤ) (_ : (fun v => (q v : ℝ)) ∈
        (G.zonotope (fun v => (a v : ℝ))).latticePoints),
      ∏ v, shiftedNarayanaPolynomial (q v - 1).toNat).HasOnlyNegativeRoots := by
  classical
  rw [finsum_latticePoints_zonotope_eq_orientationSum hG a ha]
  exact hasOnlyNegativeRoots_of_splits_of_coeff_nonneg (splits_orientationSum hBB hLW G _)
    (coeff_orientationSum_nonneg G _) (eval_zero_orientationSum_pos G _)

omit [Fintype V] in
/-- Every lattice point of the zonotope `P_{G,a}` of a forest with `a > 0` has all
coordinates at least `1`: it is `a + indeg h` for an orientation `h`. -/
private lemma one_le_of_mem_latticePoints_zonotope {G : LooplessMultigraph V E}
    (hG : G.IsForest) {a : V → ℤ} (ha : ∀ v, 0 < a v) {q : V → ℤ}
    (hq : (fun v => (q v : ℝ)) ∈ (G.zonotope (fun v => (a v : ℝ))).latticePoints) (v : V) :
    1 ≤ q v := by
  obtain ⟨h, -, hh⟩ :=
    (hG.bijOn_add_indegree_orientations_latticePoints_zonotope (R := ℝ) a).surjOn hq
  have : (a v + indegree h v : ℝ) = q v := congrFun hh v
  have : a v + indegree h v = q v := by exact_mod_cast this
  linarith [ha v]

omit [DecidableEq V] in
/-- If every `q v ≥ 1`, then `∏_v N_{q_v} = x^{|V|} ∏_v Ñ_{q_v - 1}`. -/
private lemma prod_narayanaPolynomial_eq_X_pow_mul {q : V → ℤ} (hq : ∀ v, 1 ≤ q v) :
    ∏ v, narayanaPolynomial (q v).toNat =
      X ^ Fintype.card V * ∏ v, shiftedNarayanaPolynomial (q v - 1).toNat := by
  rw [← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [show (q v).toNat = (q v - 1).toNat + 1 by have := hq v; omega,
    narayanaPolynomial_succ_eq_X_mul]

/-- For a forest `G` and a positive integer vector `a`, the polynomial
`∑_{q ∈ P_{G,a} ∩ ℤ^V} ∏_v N_{q_v}(x)` is real-rooted. -/
@[lognarayana "thm_tree_zonotope_narayana_real_rooted"]
public theorem IsForest.splits_finsum_latticePoints_zonotope
    (hBB : ∀ σ : Type u, RealStablePreserverOfSymbol σ)
    (hLW : ShiftedNarayanaNegRealRoots)
    {G : LooplessMultigraph V E} (hG : G.IsForest) (a : V → ℤ) (ha : ∀ v, 0 < a v) :
    (∑ᶠ (q : V → ℤ) (_ : (fun v => (q v : ℝ)) ∈
        (G.zonotope (fun v => (a v : ℝ))).latticePoints),
      ∏ v, narayanaPolynomial (q v).toNat).Splits := by
  rw [(finsum_congr fun q => finsum_congr fun hq =>
      prod_narayanaPolynomial_eq_X_pow_mul (one_le_of_mem_latticePoints_zonotope hG ha hq)).trans
    (mul_finsum_mem (s := {q : V → ℤ | (fun v => (q v : ℝ)) ∈
      (G.zonotope (fun v => (a v : ℝ))).latticePoints}) _ _).symm]
  exact (Splits.X.pow _).mul
    (hG.hasOnlyNegativeRoots_finsum_latticePoints_zonotope hBB hLW a ha).1

end NarayanaSums

end LooplessMultigraph
