/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module
public import LogNarayana.Nestohedron.Fertilitope.Defs
public import LogNarayana.StackSorting.ValidHookConfigurations.Basic
public import LogNarayana.AuxiliaryDefinitions

/-!
# Coordinate simplices, binary nestohedra and fertilitopes

Every point of the coordinate simplex `Δ_J ⊆ R^ι` has nonnegative coordinates, vanishes off
`J`, and has coordinate sum `1`. Consequently every point `v` of a nestohedron
`Nest_𝓑(c) = ∑_{J ∈ 𝓑} c_J Δ_J` has coordinate sum `∑_{J ∈ 𝓑} c_J`, and when `𝓑` is a binary
building set and every `c_J > 0`, every coordinate of `v` is positive, since `{i} ∈ 𝓑` gives
`v_i ≥ c_{{i}}`. Together these bound every coordinate of a binary nestohedron in
`(0, ∑_{J ∈ 𝓑} c_J]`, so a binary nestohedron has finitely many lattice points.

Defant's theorems relating fertilitopes and integral binary nestohedra are recorded as
propositions, taken as hypotheses by the theorems that use them. The lattice points of the
fertilitope of `2135467` are computed directly.

## Main definitions

* `FertilitopeLatticePointsEq`: the lattice points of `Fer_π` are the valid compositions of `π`.
* `FertilitopeIsIntegralBinaryNestohedron`: a nonempty fertilitope is an integral binary
  nestohedron.
* `IntegralBinaryNestohedronRealization`: every integral binary nestohedron has the valid
  compositions of some permutation as its lattice points.

## Main results

* `coordSimplex_subset`: `Δ_J ⊆ {v | (∀ i, 0 ≤ v i) ∧ (∀ i ∉ J, v i = 0) ∧ ∑ i, v i = 1}`, and
  `coordSimplex_subset_fin`, its form over `ℝ` and `Fin r`.
* `sum_eq_sum_of_mem_nestohedron`: for `v ∈ nestohedron R 𝓑 c`, `∑ i, v i = ∑ J ∈ 𝓑, c J`.
* `pos_of_mem_nestohedron`: every coordinate of a point of a binary nestohedron is positive.
* `nestohedron_latticePoints_finite`: a binary nestohedron has finitely many lattice points.
* `List.latticePoints_fertilitope_2135467`: the lattice points of `Fer_{2135467}` are
  `(3,1,1), (2,1,2), (2,2,1), (1,2,2), (1,3,1)`.

## Implementation notes

The paper works in `ℝ^r` with `r ≥ 1`. The inclusion `coordSimplex_subset`, the coordinate
sum and the positivity hold over any ordered semiring and any (finite, resp. locally finite
linearly ordered) index type, with no hypothesis on `r` or `J`, and are stated so; the
coordinate sum needs neither the building-set condition nor `c_J > 0`.

In the cited propositions, valid compositions (tuples of naturals) are compared with points
of `ℝ^{k+1}` through the coordinatewise `Nat.cast`, as in `List.fertilitope`; in
`IntegralBinaryNestohedronRealization` the condition `des(π) = r - 1` is stated as
`π.numDescents + 1 = r`, which supplies the reindexing `Fin.cast`.

The lattice points of `Fer_{2135467}` are computed without Defant's theorem: the fertilitope is
the convex hull of the five valid compositions, which lies in the convex set
`{v | v_i ≥ 1, v_0 + v_1 + v_2 = 5, v_2 ≤ 2}`, whose integer points are exactly those five.

## References

* [LogNarayana], Section on coordinate simplices, binary nestohedra and fertilitopes.
* [Fertilitopes], Theorems 3.1 and 3.2.
-/


open scoped Pointwise

section CoordSimplex

variable {R : Type*} {ι : Type*} [Semiring R] [PartialOrder R]

/-- The coordinate simplex `Δ_J` is contained in the set of `v ∈ R^ι` with nonnegative
coordinates, vanishing outside `J`, and with coordinate sum `1`. -/
@[lognarayana "lem_coord_simplex_subset"]
public theorem coordSimplex_subset [IsOrderedRing R] [Fintype ι] [DecidableEq ι] {J : Set ι} :
    coordSimplex R J ⊆
      {v : ι → R | (∀ i, 0 ≤ v i) ∧ (∀ i, i ∉ J → v i = 0) ∧ ∑ i, v i = 1} := by
  refine convexHull_min ?_ fun v hv w hw a b ha hb hab => ⟨fun i => ?_, fun i hi => ?_, ?_⟩
  · rintro _ ⟨j, hj, rfl⟩
    refine ⟨fun i => ?_, fun i hi => Pi.single_eq_of_ne (by rintro rfl; exact hi hj) _, by simp⟩
    by_cases h : i = j <;> simp [h]
  · simpa using add_nonneg (mul_nonneg ha (hv.1 i)) (mul_nonneg hb (hw.1 i))
  · simp [hv.2.1 i hi, hw.2.1 i hi]
  · simp [Finset.sum_add_distrib, ← Finset.mul_sum, hv.2.2, hw.2.2, hab]

/-- The paper's form of `coordSimplex_subset`: for `r ≥ 1` and nonempty `J ⊆ [r]`, the
coordinate simplex `Δ_J ⊆ ℝ^r` lies in the set of `v` with nonnegative coordinates,
vanishing outside `J`, and with coordinate sum `1`. -/
public theorem coordSimplex_subset_fin (r : ℕ) (_hr : 1 ≤ r) (J : Set (Fin r))
    (_hJ : J.Nonempty) :
    coordSimplex ℝ J ⊆
      {v : Fin r → ℝ | (∀ i, 0 ≤ v i) ∧ (∀ i, i ∉ J → v i = 0) ∧ ∑ i, v i = 1} :=
  coordSimplex_subset

/-- Every point of the coordinate simplex has nonnegative coordinates (no finiteness of `ι`
needed, unlike `coordSimplex_subset`). -/
private theorem nonneg_of_mem_coordSimplex [IsOrderedRing R] [DecidableEq ι] {J : Set ι}
    {v : ι → R} (hv : v ∈ coordSimplex R J) : 0 ≤ v :=
  convexHull_min (by rintro _ ⟨j, -, rfl⟩; exact Pi.single_nonneg.mpr zero_le_one)
    (convex_Ici 0) hv

/-- Every point of the coordinate simplex has coordinate sum `1` (no ordered-ring structure
needed, unlike `coordSimplex_subset`). -/
private theorem sum_eq_one_of_mem_coordSimplex [Fintype ι] [DecidableEq ι] {J : Set ι}
    {v : ι → R} (hv : v ∈ coordSimplex R J) : ∑ i, v i = 1 := by
  have hconv : Convex R {w : ι → R | ∑ i, w i = 1} := fun x hx y hy a b _ _ hab => by
    simp_all [Finset.sum_add_distrib, ← Finset.mul_sum]
  exact convexHull_min (by rintro _ ⟨j, -, rfl⟩; simp) hconv hv

end CoordSimplex

section Nestohedron

variable {R : Type*} {ι : Type*} [Semiring R] [PartialOrder R] [Fintype ι] [DecidableEq ι]

/-- Every point `v` of the nestohedron `∑_{J ∈ 𝓑} c_J Δ_J` has coordinate sum
`∑_i v_i = ∑_{J ∈ 𝓑} c_J`. -/
@[lognarayana "lem_nestohedron_coordinate_sum"]
public theorem sum_eq_sum_of_mem_nestohedron {𝓑 : Finset (Finset ι)} {c : Finset ι → R}
    {v : ι → R} (hv : v ∈ nestohedron R 𝓑 c) : ∑ i, v i = ∑ J ∈ 𝓑, c J := by
  unfold nestohedron at hv
  induction 𝓑 using Finset.induction_on generalizing v with
  | empty => simp_all
  | insert J 𝓑 hJ ih =>
    rw [Finset.sum_insert hJ] at hv
    obtain ⟨_, ⟨w, hw, rfl⟩, y, hy, rfl⟩ := hv
    rw [Finset.sum_insert hJ, ← ih hy]
    simp [Finset.sum_add_distrib, ← Finset.mul_sum, sum_eq_one_of_mem_coordSimplex hw]

end Nestohedron

section BinaryNestohedron

variable {R : Type*} {α : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R]

/-- The `i`-th coordinate of a point of `∑_{J ∈ 𝓑} c_J Δ_J` with nonnegative `c_J` is
nonnegative, and at least `c_{{i}}` when `{i} ∈ 𝓑`. -/
private theorem nonneg_and_le_of_mem_sum [DecidableEq α] {𝓑 : Finset (Finset α)}
    {c : Finset α → R} (hc : ∀ J ∈ 𝓑, 0 ≤ c J) {v : α → R}
    (hv : v ∈ ∑ J ∈ 𝓑, c J • coordSimplex R (J : Set α)) (i : α) :
    0 ≤ v i ∧ ({i} ∈ 𝓑 → c {i} ≤ v i) := by
  induction 𝓑 using Finset.induction_on generalizing v with
  | empty => simp_all
  | insert J 𝓑 hJ ih =>
    rw [Finset.sum_insert hJ] at hv
    obtain ⟨_, ⟨w, hw, rfl⟩, y, hy, rfl⟩ := hv
    obtain ⟨ih1, ih2⟩ := ih (fun K hK => hc K (Finset.mem_insert_of_mem hK)) hy
    have hx0 : 0 ≤ c J * w i :=
      mul_nonneg (hc J (Finset.mem_insert_self J 𝓑)) (nonneg_of_mem_coordSimplex hw i)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    refine ⟨add_nonneg hx0 ih1, fun hi => ?_⟩
    by_cases hJi : J = {i}
    · subst hJi
      have hw : w = Pi.single i 1 := by simpa [coordSimplex] using hw
      simpa [hw] using le_add_of_nonneg_right ih1
    · exact le_add_of_nonneg_of_le hx0
        (ih2 ((Finset.mem_insert.mp hi).resolve_left (Ne.symm hJi)))

variable [LinearOrder α] [LocallyFiniteOrder α]

/-- Every coordinate of a point of a binary nestohedron `∑_{J ∈ 𝓑} c_J Δ_J`, with `𝓑` a binary
building set and all `c_J > 0`, is positive. -/
@[lognarayana "lem_nestohedron_positive"]
public theorem pos_of_mem_nestohedron {𝓑 : Finset (Finset α)} (h𝓑 : IsBinaryBuildingSet 𝓑)
    {c : Finset α → R} (hc : ∀ J ∈ 𝓑, 0 < c J) {v : α → R} (hv : v ∈ nestohedron R 𝓑 c)
    (i : α) : 0 < v i :=
  have hi := h𝓑.singleton_mem i
  (hc _ hi).trans_le ((nonneg_and_le_of_mem_sum (fun J hJ => (hc J hJ).le) hv i).2 hi)

end BinaryNestohedron

/-- For a binary building set `𝓑` on `[r]` and coefficients `c_J > 0`, the binary nestohedron
`Nest_𝓑(c)` contains only finitely many lattice points: `Nest_𝓑(c) ∩ ℤ^r` is finite. Every
coordinate of a point lies in `(0, ∑ J ∈ 𝓑, c J]`, by `pos_of_mem_nestohedron` and
`sum_eq_sum_of_mem_nestohedron`. -/
@[lognarayana "lem_nestohedron_lattice_finite"]
public theorem nestohedron_latticePoints_finite {r : ℕ}
    {𝓑 : Finset (Finset (Fin r))} (h𝓑 : IsBinaryBuildingSet 𝓑) {c : Finset (Fin r) → ℝ}
    (hc : ∀ J ∈ 𝓑, 0 < c J) :
    (nestohedron ℝ 𝓑 c).latticePoints.Finite := by
  refine ((Set.Finite.pi fun _ : Fin r => Set.finite_Icc (1 : ℤ) ⌊∑ J ∈ 𝓑, c J⌋).image
    fun z i => (z i : ℝ)).subset ?_
  rintro v ⟨hv, hz⟩
  choose z hz using hz
  have hpos := pos_of_mem_nestohedron h𝓑 hc hv
  refine ⟨z, fun i _ => ⟨?_, Int.le_floor.mpr ?_⟩, funext hz⟩
  · exact_mod_cast (hz i).symm ▸ hpos i
  · rw [hz i, ← sum_eq_sum_of_mem_nestohedron hv]
    exact Finset.single_le_sum (fun j _ => (hpos j).le) (Finset.mem_univ i)

/-- **Lattice points of the fertilitope** (C. Defant, *Fertilitopes*, 2023, Theorem 3.1): for
every `n ≥ 1` and every permutation `π ∈ S_n`, the lattice points of the fertilitope
`List.fertilitope ℝ π` are exactly the valid compositions `List.validCompositions π`, viewed
in `ℝ^{des(π)+1}` via the coordinatewise cast. -/
@[expose, lognarayana "thm_ext_fertilitope_lattice_points"]
public def FertilitopeLatticePointsEq : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ π ∈ permWords n,
    (List.fertilitope ℝ π).latticePoints =
      (fun q i => (q i : ℝ)) '' (π.validCompositions : Set (Fin (π.numDescents + 1) → ℕ))

/-- **Fertilitopes are integral binary nestohedra** (C. Defant, *Fertilitopes*, 2023,
Theorem 3.2): for every `n ≥ 1` and every permutation `π ∈ S_n` whose set of valid
compositions `List.validCompositions π` is nonempty, the fertilitope `List.fertilitope ℝ π`
is an integral binary nestohedron in `ℝ^{des(π)+1}`. -/
@[expose, lognarayana "thm_ext_fertilitope_is_nestohedron"]
public def FertilitopeIsIntegralBinaryNestohedron : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ π ∈ permWords n, π.validCompositions.Nonempty →
    IsIntegralBinaryNestohedron ℝ (List.fertilitope ℝ π)

namespace List

/-- A convex set containing the five valid compositions of `2135467`, whose integer points are
exactly those five. -/
private def region2135467 : Set (Fin 3 → ℝ) :=
  {v | 1 ≤ v 0 ∧ 1 ≤ v 1 ∧ 1 ≤ v 2 ∧ v 0 + v 1 + v 2 = 5 ∧ v 2 ≤ 2}

private lemma convex_region2135467 : Convex ℝ region2135467 := by
  intro x hx y hy a b ha hb hab
  simp only [region2135467, Set.mem_ofPred_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at *
  obtain ⟨h1, h2, h3, h4, h5⟩ := hx
  obtain ⟨g1, g2, g3, g4, g5⟩ := hy
  refine ⟨by nlinarith, by nlinarith, by nlinarith, ?_, by nlinarith⟩
  linear_combination a * h4 + b * g4 + 5 * hab

private lemma mem_five_of_mem_region2135467 {v : Fin 3 → ℝ} (hR : v ∈ region2135467)
    (hz : ∀ i, v i ∈ Set.range (Int.cast : ℤ → ℝ)) :
    v ∈ ({![3, 1, 1], ![2, 1, 2], ![2, 2, 1], ![1, 2, 2], ![1, 3, 1]} : Set (Fin 3 → ℝ)) := by
  obtain ⟨a, ha⟩ := hz 0
  obtain ⟨b, hb⟩ := hz 1
  obtain ⟨c, hc⟩ := hz 2
  obtain ⟨h1, h2, h3, h4, h5⟩ := hR
  rw [← ha] at h1 h4
  rw [← hb] at h2 h4
  rw [← hc] at h3 h4 h5
  have h1' : 1 ≤ a := by exact_mod_cast h1
  have h2' : 1 ≤ b := by exact_mod_cast h2
  have h3' : 1 ≤ c := by exact_mod_cast h3
  have h5' : c ≤ 2 := by exact_mod_cast h5
  have h4' : a + b + c = 5 := by exact_mod_cast h4
  have hv : v = ![(a : ℝ), b, c] := by
    ext i
    fin_cases i <;> simp [ha, hb, hc]
  subst hv
  have ha3 : a ≤ 3 := by omega
  have hb3 : b ≤ 3 := by omega
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  obtain rfl : c = 5 - a - b := by omega
  interval_cases a <;> interval_cases b <;> first | omega | norm_num

/-- The lattice points of the convex hull of the five triples, stated for any `S` equal to
them so that the dependent index type `Fin (numDescents + 1)` can be fixed to `Fin 3`. -/
private lemma latticePoints_convexHull_five (S : Finset (Fin 3 → ℕ))
    (hS : S = {![3, 1, 1], ![2, 1, 2], ![2, 2, 1], ![1, 2, 2], ![1, 3, 1]}) :
    (convexHull ℝ ((fun q i => (q i : ℝ)) '' (S : Set (Fin 3 → ℕ)))).latticePoints =
      ({![3, 1, 1], ![2, 1, 2], ![2, 2, 1], ![1, 2, 2], ![1, 3, 1]} : Set (Fin 3 → ℝ)) := by
  have cast_vec3 (a b c : ℕ) : (fun q i => (q i : ℝ)) ![a, b, c] = ![(a : ℝ), b, c] := by
    ext i
    fin_cases i <;> rfl
  have hF : (fun q i => (q i : ℝ)) '' (S : Set (Fin 3 → ℕ)) =
      ({![3, 1, 1], ![2, 1, 2], ![2, 2, 1], ![1, 2, 2], ![1, 3, 1]} : Set (Fin 3 → ℝ)) := by
    subst hS
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.image_insert_eq,
      Set.image_singleton, cast_vec3, Nat.cast_ofNat, Nat.cast_one]
  rw [hF]
  ext v
  constructor
  · rintro ⟨hv, hz⟩
    refine mem_five_of_mem_region2135467 (convexHull_min ?_ convex_region2135467 hv) hz
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl <;> simp [region2135467] <;> norm_num
  · intro hv
    refine ⟨subset_convexHull ℝ _ hv, fun i => ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl <;> fin_cases i <;> simp only [Nat.succ_eq_add_one,
      Nat.reduceAdd, Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val,
      Matrix.cons_val_zero, Matrix.cons_val_one, Set.mem_range, Int.cast_eq_one, exists_eq]
    all_goals exact ⟨_, Int.cast_ofNat _⟩

/-- The lattice points of the fertilitope of `π = 2135467` are
`(3,1,1), (2,1,2), (2,2,1), (1,2,2), (1,3,1)`. -/
@[lognarayana "lem_fertilitope_example_lattice_points"]
public theorem latticePoints_fertilitope_2135467 :
    (fertilitope ℝ [2, 1, 3, 5, 4, 6, 7]).latticePoints =
      ({![3, 1, 1], ![2, 1, 2], ![2, 2, 1], ![1, 2, 2], ![1, 3, 1]} : Set (Fin 3 → ℝ)) :=
  latticePoints_convexHull_five _ validCompositions_2135467

end List
