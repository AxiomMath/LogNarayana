/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module
public import LogNarayana.StackSorting.ValidHookConfigurations.Defs
public import LogNarayana.Narayana.Polynomials.Defs
public import LogNarayana.Narayana.Polynomials.Basic
public import LogNarayana.StackSorting.FiberPolynomials.Defs
public import LogNarayana.StackSorting.StackSort.Basic
public import LogNarayana.AuxiliaryDefinitions

/-!
# Hooks, valid hook configurations and valid compositions

This file develops the combinatorics of hooks of a permutation `π ∈ S_n`, of its valid hook
configurations `VHC(π)` and of its valid compositions `𝒱(π)`, and records the two results of
Defant that relate them to the stack-sorting fiber of `π`.

Two hooks `(i, j)`, `(i', j')` of `π` with `i < i'` have intersecting regions exactly when
`j = j'`, or `i' ≤ j` and `π_{i'} ≤ π_j ≤ π_{j'}`. Both regions are `L`-shapes, a vertical
segment followed by a horizontal one; the vertical segment of `(i, j)` lies strictly left of the
second region, so only the horizontal segment of `(i, j)`, at height `π_j`, can meet it.

In a valid hook configuration `𝓗` distinct hooks have distinct southwest endpoints (by (V1),
`(i, j) ↦ i` maps `𝓗` onto `Des(π)` and `|𝓗| = |Des(π)|`) and distinct northeast endpoints (two
hooks `(i, j)`, `(i', j)` with `i < i'` meet at `(i', π_j)`, against (V3)). Consequently every
valid composition of `π` is a composition of `n - des(π)` into `des(π) + 1` parts: the free
positions number `n - des(π)`, each of them receives exactly one colour, position `1` is blue,
and the position right after the `t`-th descent receives the colour of the hook starting there.

For the identity `ι_n`, `VHC(ι_n) = {∅}` and `𝒱(ι_n) = {(n)}`. For `π = 2135467`,
`VHC(π)` consists of five configurations, `𝒱(π) = {(3,1,1), (2,1,2), (2,2,1), (1,2,2), (1,3,1)}`
and `x D_π(x) = 5x³ + 12x⁴ + 5x⁵`.

## Main definitions

* `RefinedFertilityFormula`: Defant's refined fertility formula
  `x D_π(x) = ∑_{𝐪 ∈ 𝒱(π)} N_𝐪(x)`, a cited result.
* `HookCompositionInjOn`: Defant's observation that `𝓗 ↦ 𝐪_𝓗` is injective on `VHC(π)`, a cited
  result.

## Main results

* `List.hookRegion_inter_nonempty_iff`: when the regions of two hooks meet.
* `List.injOn_fst_of_mem_validHookConfigurations`,
  `List.injOn_snd_of_mem_validHookConfigurations`: the southwest, resp. northeast, endpoints of
  the hooks of a valid hook configuration are distinct.
* `List.mem_compositionTuple_of_mem_validCompositions`: `𝒱(π) ⊆ Comp(n - k, k + 1)`.
* `List.validHookConfigurations_idPermWord`, `List.validCompositions_idPermWord`: the identity.
* `List.validHookConfigurations_2135467`, `List.validCompositions_2135467`,
  `List.X_mul_fiberDescentPolynomial_2135467`: the example `π = 2135467`.
* `List.X_mul_fiberDescentPolynomial_idPermWord`: `x D_{ι_n}(x) = N_n(x)` for `n ≥ 1`, by the
  decomposition of the fiber of `ι_n` at the maximum and the quadratic recurrence of `Ñ_m`.

## Implementation notes

Letters are read as `π.getD (k - 1) 0` at `1`-based positions `k`, as in `List.hookRegion`; for
the positions of a hook this is `π[k - 1]`. The injectivity lemmas only use (V1), resp. (V3) and
the shape of hooks, and are stated for every word `π : List ℕ`, not only for permutations.

The tuples of `𝒱(π)` are indexed by `Fin (des(π) + 1)`. For `π = 2135467`, `des(π) = 2` holds
by computation, so the index type is `Fin 3` definitionally and the triples are written
`![a, b, c]`. For `ι_n` the index type is `Fin 1` only after the proof that `des(ι_n) = 0`, so
`List.validCompositions_idPermWord` asserts that equality as well, and writes `(n)` as
`fun _ ↦ n`.

The paper derives `x D_{2135467}(x)` from the refined fertility formula and the five valid
compositions of `2135467`. Since that formula is a cited result, here the identity is instead
checked by evaluating the fiber in the kernel: `List.stackSort`, defined by well-founded
recursion, is replaced by a structurally recursive fuel-bounded copy which agrees with it on
lists no longer than the fuel, and `List.permutations` by `List.permutations'`, which enumerates
the same permutations.

The cited results are recorded as propositions, to be taken as hypotheses by the theorems that
use them; `narayanaTupleProd q` is by definition `∏ i, narayanaPolynomial (q i)`, so the
product form of the refined fertility formula is not stated separately.

## References

* [LogNarayana], Section 2.3.
* [Fertilitopes], Remark 2.2 and Corollary 2.4.
-/

open Polynomial

namespace List

/-! ### Intersections of hook regions -/

/-- A hook `(i, j)` of `π` has `1 ≤ i < j ≤ ℓ` and `πᵢ < πⱼ` (letters read with `getD`). -/
private lemma of_mem_hooks {π : List ℕ} {p : ℕ × ℕ} (h : p ∈ π.hooks) :
    1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ π.length ∧ π.getD (p.1 - 1) 0 < π.getD (p.2 - 1) 0 := by
  simp only [hooks, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at h
  obtain ⟨⟨⟨h1, -⟩, -, h2⟩, h3, h4, h5, h6⟩ := h
  refine ⟨h1, h3, h2, ?_⟩
  rwa [getD_eq_getElem _ _ h4, getD_eq_getElem _ _ h5]

/-- A point lies on a vertical segment iff it has its first coordinate and its second
coordinate lies in the interval. -/
private lemma mem_segment_vert {x y₁ y₂ : ℝ} {p : ℝ × ℝ} :
    p ∈ segment ℝ (x, y₁) (x, y₂) ↔ p.1 = x ∧ p.2 ∈ Set.uIcc y₁ y₂ := by
  rw [← Prod.image_mk_segment_right, segment_eq_uIcc]
  constructor
  · rintro ⟨y, hy, rfl⟩; exact ⟨rfl, hy⟩
  · rintro ⟨h1, h2⟩; exact ⟨p.2, h2, by ext <;> simp [h1]⟩

/-- A point lies on a horizontal segment iff it has its second coordinate and its first
coordinate lies in the interval. -/
private lemma mem_segment_horiz {x₁ x₂ y : ℝ} {p : ℝ × ℝ} :
    p ∈ segment ℝ (x₁, y) (x₂, y) ↔ p.2 = y ∧ p.1 ∈ Set.uIcc x₁ x₂ := by
  rw [← Prod.image_mk_segment_left, segment_eq_uIcc]
  constructor
  · rintro ⟨x, hx, rfl⟩; exact ⟨rfl, hx⟩
  · rintro ⟨h1, h2⟩; exact ⟨p.1, h2, by ext <;> simp [h1]⟩

/-- Two `L`-shapes in the plane, the first with corner column `x` strictly left of the second's
`x'`, meet iff the horizontal arm of the first (at height `b`, reaching to `X`) crosses the
vertical arm `{x'} × [c, d]` of the second. -/
private lemma lShapes_inter_nonempty_iff {x X x' X' a b c d : ℝ} (hx : x ≤ X) (hx' : x' ≤ X')
    (hcd : c ≤ d) (hxx' : x < x') :
    ((segment ℝ (x, a) (x, b) ∪ segment ℝ (x, b) (X, b)) ∩
        (segment ℝ (x', c) (x', d) ∪ segment ℝ (x', d) (X', d))).Nonempty ↔
      x' ≤ X ∧ c ≤ b ∧ b ≤ d := by
  simp only [Set.Nonempty, Set.mem_inter_iff, Set.mem_union, mem_segment_vert,
    mem_segment_horiz, Set.uIcc_of_le hx, Set.uIcc_of_le hx', Set.uIcc_of_le hcd, Set.mem_Icc,
    Prod.exists]
  constructor
  · rintro ⟨u, v, ⟨hu, -⟩ | ⟨rfl, -, hu⟩, ⟨rfl, hv⟩ | ⟨rfl, hu', -⟩⟩ <;>
      first | exact ⟨hu, hv⟩ | exact ⟨by linarith, hcd, le_rfl⟩ | (exfalso; linarith)
  · rintro ⟨h₁, h₂, h₃⟩
    exact ⟨x', b, Or.inr ⟨rfl, hxx'.le, h₁⟩, Or.inl ⟨rfl, h₂, h₃⟩⟩

/-- Two hooks `(i, j)` and `(i', j')` of a list `π` with `i < i'` have intersecting regions if and
only if `j = j'`, or `i' ≤ j` and `π_{i'} ≤ π_j ≤ π_{j'}`. -/
@[lognarayana "lem_hook_regions_intersect_iff"]
public theorem hookRegion_inter_nonempty_iff {π : List ℕ}
    {i j i' j' : ℕ} (h : (i, j) ∈ π.hooks) (h' : (i', j') ∈ π.hooks)
    (hii' : i < i') :
    (π.hookRegion (i, j) ∩ π.hookRegion (i', j')).Nonempty ↔
      j = j' ∨ (i' ≤ j ∧ π.getD (i' - 1) 0 ≤ π.getD (j - 1) 0 ∧
        π.getD (j - 1) 0 ≤ π.getD (j' - 1) 0) := by
  obtain ⟨-, hij, -, -⟩ := of_mem_hooks h
  obtain ⟨-, hij', -, hcd⟩ := of_mem_hooks h'
  rw [hookRegion, hookRegion, lShapes_inter_nonempty_iff (by exact_mod_cast hij.le)
    (by exact_mod_cast hij'.le) (by exact_mod_cast hcd.le) (by exact_mod_cast hii')]
  norm_cast
  refine ⟨Or.inr, ?_⟩
  rintro (rfl | h)
  exacts [⟨hij'.le, hcd.le, le_rfl⟩, h]

/-! ### Endpoints of the hooks of a valid hook configuration -/

/-- The conditions defining a valid hook configuration, unpacked. -/
private lemma of_mem_validHookConfigurations {π : List ℕ} {𝓗 : Finset (ℕ × ℕ)}
    (h𝓗 : 𝓗 ∈ π.validHookConfigurations) :
    𝓗 ⊆ π.hooks ∧ (𝓗.card = π.numDescents ∧ 𝓗.image Prod.fst = π.descentSet) ∧
    (∀ p ∈ 𝓗, ∀ k ∈ Finset.Icc p.1 p.2, π.getD (k - 1) 0 ≤ π.getD (p.2 - 1) 0) ∧
    (∀ p ∈ 𝓗, ∀ q ∈ 𝓗, p ≠ q → (π.hookRegion p ∩ π.hookRegion q).Nonempty →
      p.2 = q.1 ∨ q.2 = p.1) := by
  simpa only [validHookConfigurations, Finset.mem_filter, Finset.mem_powerset] using h𝓗

/-- The southwest endpoints of the hooks of a valid hook configuration are distinct: the map
`(i, j) ↦ i` is injective on every `𝓗 ∈ VHC(π)`. -/
@[lognarayana "lem_vhc_sw_injective"]
public theorem injOn_fst_of_mem_validHookConfigurations {π : List ℕ} {𝓗 : Finset (ℕ × ℕ)}
    (h𝓗 : 𝓗 ∈ π.validHookConfigurations) : Set.InjOn Prod.fst (𝓗 : Set (ℕ × ℕ)) := by
  obtain ⟨-, ⟨hcard, himage⟩, -⟩ := of_mem_validHookConfigurations h𝓗
  exact Finset.injOn_of_card_image_eq (by rw [himage, hcard, numDescents])

/-- If `i < i' ≤ j`, the regions of `(i, j)` and `(i', j)` meet at `(i', π_j)`: it is the top of
the vertical arm of `(i', j)` and lies on the horizontal arm of `(i, j)`. -/
private lemma hookRegion_inter_nonempty_of_snd_eq (π : List ℕ) {i i' j : ℕ} (hii' : i < i')
    (hi'j : i' ≤ j) : (π.hookRegion (i, j) ∩ π.hookRegion (i', j)).Nonempty := by
  refine ⟨((i' : ℝ), (π.getD (j - 1) 0 : ℝ)), Or.inr ?_, Or.inl (right_mem_segment _ _ _)⟩
  rw [← Prod.image_mk_segment_left, segment_eq_Icc (by exact_mod_cast (hii'.le.trans hi'j))]
  exact ⟨i', ⟨by exact_mod_cast hii'.le, by exact_mod_cast hi'j⟩, rfl⟩

/-- The northeast endpoints of the hooks of a valid hook configuration are distinct: the map
`(i, j) ↦ j` is injective on every `𝓗 ∈ VHC(π)`. -/
@[lognarayana "lem_vhc_ne_injective"]
public theorem injOn_snd_of_mem_validHookConfigurations {π : List ℕ} {𝓗 : Finset (ℕ × ℕ)}
    (h𝓗 : 𝓗 ∈ π.validHookConfigurations) : Set.InjOn Prod.snd (𝓗 : Set (ℕ × ℕ)) := by
  obtain ⟨hsub, -, -, hV3⟩ := of_mem_validHookConfigurations h𝓗
  -- two hooks `(i, j)`, `(i', j)` with `i < i'` meet, so (V3) gives `j = i'` or `j = i`
  have key : ∀ {i i' j}, (i, j) ∈ 𝓗 → (i', j) ∈ 𝓗 → ¬ i < i' := fun h h' hii' => by
    obtain ⟨-, hj', -⟩ := of_mem_hooks (hsub h')
    rcases hV3 _ h _ h' (by simp [hii'.ne])
        (hookRegion_inter_nonempty_of_snd_eq π hii' hj'.le) with e | e <;>
      simp at e <;> omega
  rintro ⟨i, j⟩ hp ⟨i', j'⟩ hq (rfl : j = j')
  rw [le_antisymm (not_lt.1 (key hq hp)) (not_lt.1 (key hp hq))]

/-! ### Valid compositions are compositions -/

/-- A descent `d` of `π` has `1 ≤ d < ℓ` and `π_{d+1} < π_d` (letters read with `getD`). -/
private lemma of_mem_descentSet {π : List ℕ} {d : ℕ} (h : d ∈ π.descentSet) :
    1 ≤ d ∧ d < π.length ∧ π.getD d 0 < π.getD (d - 1) 0 := by
  simp only [descentSet, Finset.mem_filter, Finset.mem_Ico] at h
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := h
  refine ⟨h1, h2, ?_⟩
  rwa [getD_eq_getElem _ _ h3, getD_eq_getElem _ _ (by omega)]

/-- Letters of a duplicate-free list at in-range positions determine the positions. -/
private lemma eq_of_getD_eq_of_nodup {π : List ℕ} (hπ : π.Nodup) {a b : ℕ} (ha : a < π.length)
    (hb : b < π.length) (h : π.getD a 0 = π.getD b 0) : a = b := by
  rw [getD_eq_getElem _ _ ha, getD_eq_getElem _ _ hb] at h
  exact hπ.getElem_inj_iff.1 h

/-- A position `u` covered by some hook of a valid hook configuration is coloured by exactly one
descent: there is a unique `t` such that the lowest hook covering `u` starts at the `t`-th
descent. -/
private lemma existsUnique_colour {π : List ℕ} (hπ : π.Nodup) {𝓗 : Finset (ℕ × ℕ)}
    (h𝓗 : 𝓗 ∈ π.validHookConfigurations) {u : ℕ} (hcov : ∃ p ∈ 𝓗, p.1 < u ∧ u < p.2) :
    ∃! t : Fin π.numDescents, ∃ p ∈ 𝓗, p.1 = π.descentSet.orderEmbOfFin rfl t ∧ p.1 < u ∧
      u < p.2 ∧ ∀ p' ∈ 𝓗, p'.1 < u → u < p'.2 →
        π.getD (p.2 - 1) 0 ≤ π.getD (p'.2 - 1) 0 := by
  obtain ⟨hsub, ⟨-, himg⟩, -, -⟩ := of_mem_validHookConfigurations h𝓗
  obtain ⟨p₀, hp₀, hp₀u⟩ := hcov
  obtain ⟨p, hpC, hmin⟩ := (𝓗.filter fun p => p.1 < u ∧ u < p.2).exists_min_image
    (fun p => π.getD (p.2 - 1) 0) ⟨p₀, Finset.mem_filter.2 ⟨hp₀, hp₀u⟩⟩
  obtain ⟨hp, hpu⟩ := Finset.mem_filter.1 hpC
  have hd : p.1 ∈ Set.range (π.descentSet.orderEmbOfFin rfl) := by
    rw [Finset.range_orderEmbOfFin, ← himg]
    exact Finset.mem_coe.2 (Finset.mem_image_of_mem _ hp)
  obtain ⟨t, ht⟩ := hd
  refine ⟨t, ⟨p, hp, ht.symm, hpu.1, hpu.2,
    fun p' hp' h1 h2 => hmin p' (Finset.mem_filter.2 ⟨hp', h1, h2⟩)⟩, ?_⟩
  rintro t' ⟨p', hp', ht', h1, h2, hmin'⟩
  have e := le_antisymm (hmin' p hp hpu.1 hpu.2) (hmin p' (Finset.mem_filter.2 ⟨hp', h1, h2⟩))
  obtain ⟨-, -, hpl, -⟩ := of_mem_hooks (hsub hp)
  obtain ⟨-, -, hp'l, -⟩ := of_mem_hooks (hsub hp')
  have e2 := eq_of_getD_eq_of_nodup hπ (by omega) (by omega) e
  have : p' = p := injOn_snd_of_mem_validHookConfigurations h𝓗 hp' hp (by omega)
  subst this
  exact (π.descentSet.orderEmbOfFin rfl).injective (ht'.symm.trans ht.symm)

/-- For a valid hook configuration, the position `u = d + 1` right after a descent `d` is free,
covered by the hook starting at `d`, and that hook is the lowest one covering it. -/
private lemma colour_succ_descent {π : List ℕ}
    {𝓗 : Finset (ℕ × ℕ)} (h𝓗 : 𝓗 ∈ π.validHookConfigurations) {d : ℕ}
    (hd : d ∈ π.descentSet) :
    d + 1 ∈ Finset.Icc 1 π.length ∧ d + 1 ∉ 𝓗.image Prod.snd ∧
      ∃ p ∈ 𝓗, p.1 = d ∧ p.1 < d + 1 ∧ d + 1 < p.2 ∧ ∀ p' ∈ 𝓗, p'.1 < d + 1 → d + 1 < p'.2 →
        π.getD (p.2 - 1) 0 ≤ π.getD (p'.2 - 1) 0 := by
  obtain ⟨hsub, ⟨-, himg⟩, hV2, hV3⟩ := of_mem_validHookConfigurations h𝓗
  obtain ⟨hd1, hdl, hdesc⟩ := of_mem_descentSet hd
  rw [← himg] at hd
  obtain ⟨h, hh, hhd⟩ := Finset.mem_image.1 hd
  obtain ⟨-, hhlt, hhl, hhlet⟩ := of_mem_hooks (hsub hh)
  rw [hhd] at hhlt hhlet
  have hdu : d + 1 - 1 = d := by omega
  -- `j ≠ d + 1`, as `π_{d+1} < π_d < π_j`
  have hju : d + 1 < h.2 := by
    rcases Nat.lt_or_ge (d + 1) h.2 with hlt | hge
    · exact hlt
    · have : h.2 = d + 1 := by omega
      rw [this, hdu] at hhlet
      omega
  refine ⟨Finset.mem_Icc.2 ⟨by omega, by omega⟩, ?_, h, hh, hhd, by omega, hju, ?_⟩
  · intro hmem
    obtain ⟨p, hp, hpu⟩ := Finset.mem_image.1 hmem
    obtain ⟨-, hplt, -, hplet⟩ := of_mem_hooks (hsub hp)
    have := hV2 p hp d (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
    rw [hpu, hdu] at this
    omega
  · -- a lower hook `(i', j')` covering `d + 1` would start before `d` and meet `h`
    intro p' hp' h1 h2
    by_contra hlt
    push Not at hlt
    have hne : p' ≠ h := by
      rintro rfl
      exact lt_irrefl _ hlt
    have hi' : p'.1 ≠ d := fun e =>
      hne (injOn_fst_of_mem_validHookConfigurations h𝓗 hp' hh (e.trans hhd.symm))
    have hV2' := hV2 p' hp' d (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
    have hmeet := (hookRegion_inter_nonempty_iff (i := p'.1) (j := p'.2)
      (i' := h.1) (j' := h.2) (hsub hp') (hsub hh) (by omega)).2
      (Or.inr ⟨by omega, by rw [hhd]; exact hV2', hlt.le⟩)
    rcases hV3 p' hp' h hh hne hmeet with e | e <;> omega

/-- The free positions of `π` with respect to a valid hook configuration number `n - des(π)`. -/
private lemma card_free {n : ℕ} {π : List ℕ} (hπ : π ∈ permWords n) {𝓗 : Finset (ℕ × ℕ)}
    (h𝓗 : 𝓗 ∈ π.validHookConfigurations) :
    ((Finset.Icc 1 π.length).filter fun u => u ∉ 𝓗.image Prod.snd).card = n - π.numDescents := by
  obtain ⟨hsub, ⟨hcard, -⟩, -, -⟩ := of_mem_validHookConfigurations h𝓗
  have himg : 𝓗.image Prod.snd ⊆ Finset.Icc 1 π.length := by
    intro u hu
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hu
    obtain ⟨h1, h2, h3, -⟩ := of_mem_hooks (hsub hp)
    exact Finset.mem_Icc.2 ⟨by omega, h3⟩
  rw [← Finset.sdiff_eq_filter, Finset.card_sdiff_of_subset himg,
    Finset.card_image_of_injOn (injOn_snd_of_mem_validHookConfigurations h𝓗), hcard,
    Nat.card_Icc, hπ.2.1, Nat.add_sub_cancel]

/-- Every position `u` is counted exactly once: either no hook of a valid hook configuration
covers it, or it has exactly one colour. -/
private lemma uncovered_add_card_colours {π : List ℕ} (hπ : π.Nodup) {𝓗 : Finset (ℕ × ℕ)}
    (h𝓗 : 𝓗 ∈ π.validHookConfigurations) (u : ℕ) :
    (if ∀ p ∈ 𝓗, ¬(p.1 < u ∧ u < p.2) then 1 else 0) +
      (Finset.univ.filter fun t : Fin π.numDescents => ∃ p ∈ 𝓗,
        p.1 = π.descentSet.orderEmbOfFin rfl t ∧ p.1 < u ∧ u < p.2 ∧
          ∀ p' ∈ 𝓗, p'.1 < u → u < p'.2 → π.getD (p.2 - 1) 0 ≤ π.getD (p'.2 - 1) 0).card =
      1 := by
  by_cases hcov : ∃ p ∈ 𝓗, p.1 < u ∧ u < p.2
  · obtain ⟨t, ht, huniq⟩ := existsUnique_colour hπ h𝓗 hcov
    obtain ⟨p, hp, hpu⟩ := hcov
    rw [if_neg fun h => h p hp hpu, zero_add, Finset.card_eq_one]
    refine ⟨t, Finset.ext fun t' => ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨huniq t', fun h => h ▸ ht⟩
  · push Not at hcov
    rw [if_pos fun p hp h => (hcov p hp h.1).not_gt h.2, Finset.card_eq_zero.2]
    refine Finset.filter_eq_empty_iff.2 fun t _ => ?_
    rintro ⟨p, hp, -, h1, h2, -⟩
    exact (hcov p hp h1).not_gt h2

/-- For `π ∈ S_n` with `n ≥ 1` and `k = des(π)`, every valid composition of `π` is a composition
of `n - k` into `k + 1` parts. -/
@[lognarayana "lem_valid_composition_sum"]
public theorem mem_compositionTuple_of_mem_validCompositions {n : ℕ} (hn : 1 ≤ n) {π : List ℕ}
    (hπ : π ∈ permWords n) {q : Fin (π.numDescents + 1) → ℕ} (hq : q ∈ π.validCompositions) :
    q ∈ Finset.Nat.compositionTuple (π.numDescents + 1) (n - π.numDescents) := by
  obtain ⟨𝓗, h𝓗, rfl⟩ := Finset.mem_image.1 hq
  obtain ⟨hsub, -, -, -⟩ := of_mem_validHookConfigurations h𝓗
  simp only [Finset.Nat.compositionTuple, Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple]
  refine ⟨?_, fun i => Fin.cases ?_ (fun t => ?_) i⟩
  · -- the parts count the free positions, each exactly once
    rw [Fin.sum_univ_succ]
    simp only [hookComposition, Fin.cases_zero, Fin.cases_succ, Finset.card_filter]
    rw [Finset.sum_comm, ← Finset.sum_add_distrib, ← card_free hπ h𝓗, Finset.card_filter]
    refine Finset.sum_congr rfl fun u _ => ?_
    by_cases hu : u ∈ 𝓗.image Prod.snd
    · simp [hu]
    simp only [hu, not_false_eq_true, true_and, if_true]
    rw [← Finset.card_filter]
    exact uncovered_add_card_colours hπ.1.1 h𝓗 u
  · -- position `1` is free and blue
    simp only [hookComposition, Fin.cases_zero]
    refine Finset.one_le_card.2 ⟨1, Finset.mem_filter.2 ⟨?_, ?_, fun p hp h => ?_⟩⟩
    · rw [hπ.2.1]; exact Finset.mem_Icc.2 ⟨le_rfl, hn⟩
    · rintro hmem
      obtain ⟨p, hp, hpu⟩ := Finset.mem_image.1 hmem
      have := of_mem_hooks (hsub hp)
      omega
    · have := of_mem_hooks (hsub hp)
      omega
  · -- the position after the `t`-th descent has colour `t`
    obtain ⟨hI, hfree, hcol⟩ :=
      colour_succ_descent h𝓗 (Finset.orderEmbOfFin_mem π.descentSet rfl t)
    simp only [hookComposition, Fin.cases_succ]
    exact Finset.one_le_card.2 ⟨_, Finset.mem_filter.2 ⟨hI, hfree, hcol⟩⟩

/-! ### The identity permutation -/

/-- The identity word `ι_n = 12⋯n` has no descents. -/
private lemma descentSet_idPermWord (n : ℕ) : (idPermWord n).descentSet = ∅ := by
  ext i
  simp only [descentSet, idPermWord, Finset.mem_filter, Finset.notMem_empty, iff_false,
    not_and, not_exists, getElem_range', not_lt]
  omega

private lemma numDescents_idPermWord (n : ℕ) : (idPermWord n).numDescents = 0 := by
  simp [numDescents, descentSet_idPermWord]

/-- For every `n`, the only valid hook configuration of the identity permutation `ι_n` is the empty
one: `VHC(ι_n) = {∅}`. -/
@[lognarayana "lem_vhc_identity"]
public theorem validHookConfigurations_idPermWord {n : ℕ} :
    (idPermWord n).validHookConfigurations = {∅} := by
  ext 𝓗
  simp only [validHookConfigurations, Finset.mem_filter, Finset.mem_singleton, numDescents,
    descentSet_idPermWord, Finset.card_empty, Finset.card_eq_zero]
  exact ⟨fun h => h.2.1.1, by rintro rfl; simp⟩

/-- For every `n`, the identity permutation `ι_n` has no descents and its only valid composition is
`(n) ∈ ℤ_{≥0}^1`: `𝒱(ι_n) = {(n)}`. -/
@[lognarayana "lem_valid_compositions_identity"]
public theorem validCompositions_idPermWord {n : ℕ} :
    (idPermWord n).numDescents = 0 ∧
      (idPermWord n).validCompositions = {fun _ ↦ n} := by
  refine ⟨numDescents_idPermWord n, ?_⟩
  rw [validCompositions, validHookConfigurations_idPermWord, Finset.image_singleton,
    Finset.singleton_inj]
  funext i
  refine Fin.cases ?_ (fun t => ?_) i
  · simp [hookComposition, idPermWord]
    rfl
  · simpa [numDescents_idPermWord] using t.2

/-! ### The permutation `2135467` -/

private lemma mem_permWords_2135467 : [2, 1, 3, 5, 4, 6, 7] ∈ permWords 7 := by
  simp only [permWords, words, IsWord, Set.mem_ofPred_eq]
  decide

private lemma descentSet_2135467 : [2, 1, 3, 5, 4, 6, 7].descentSet = {1, 4} := by decide

/-- Condition (V3) on a two-element set `{a, b}` reduces to the single unordered pair. -/
private lemma pair_cond_iff {β : Type*} (R : ℕ × ℕ → Set β) {a b : ℕ × ℕ} (hab : a ≠ b) :
    (∀ p ∈ ({a, b} : Finset (ℕ × ℕ)), ∀ q ∈ ({a, b} : Finset (ℕ × ℕ)), p ≠ q →
        (R p ∩ R q).Nonempty → p.2 = q.1 ∨ q.2 = p.1) ↔
      ((R a ∩ R b).Nonempty → a.2 = b.1 ∨ b.2 = a.1) := by
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq,
    ne_eq, not_true_eq_false, false_imp_iff, true_and, and_true, hab, not_false_eq_true,
    true_imp_iff, Ne.symm hab, Set.inter_comm (R b) (R a)]
  exact ⟨fun h => h.1, fun h => ⟨h, fun hn => (h hn).symm⟩⟩

/-- Condition (V3) on a candidate `{(1, j), (4, j')}`, as a decidable statement about letters. -/
private lemma pair_V3_iff {j j' : ℕ} (h : (1, j) ∈ [2, 1, 3, 5, 4, 6, 7].hooks)
    (h' : (4, j') ∈ [2, 1, 3, 5, 4, 6, 7].hooks) :
    (∀ p ∈ ({(1, j), (4, j')} : Finset (ℕ × ℕ)), ∀ q ∈ ({(1, j), (4, j')} : Finset (ℕ × ℕ)),
        p ≠ q → ([2, 1, 3, 5, 4, 6, 7].hookRegion p ∩
          [2, 1, 3, 5, 4, 6, 7].hookRegion q).Nonempty → p.2 = q.1 ∨ q.2 = p.1) ↔
      (j = j' ∨ (4 ≤ j ∧ 5 ≤ [2, 1, 3, 5, 4, 6, 7].getD (j - 1) 0 ∧
          [2, 1, 3, 5, 4, 6, 7].getD (j - 1) 0 ≤ [2, 1, 3, 5, 4, 6, 7].getD (j' - 1) 0) →
        j = 4 ∨ j' = 1) := by
  rw [pair_cond_iff _ (by simp),
    hookRegion_inter_nonempty_iff h h' (by norm_num)]
  rfl

/-- Conditions (V1) and (V2) leave eight candidates `{(1, j), (4, j')}`. -/
private lemma mem_candidates {𝓗 : Finset (ℕ × ℕ)} (hsub : 𝓗 ⊆ [2, 1, 3, 5, 4, 6, 7].hooks)
    (hcard : 𝓗.card = 2) (himg : 𝓗.image Prod.fst = {1, 4})
    (hV2 : ∀ p ∈ 𝓗, ∀ k ∈ Finset.Icc p.1 p.2,
      [2, 1, 3, 5, 4, 6, 7].getD (k - 1) 0 ≤ [2, 1, 3, 5, 4, 6, 7].getD (p.2 - 1) 0) :
    𝓗 ∈ ({{(1, 3), (4, 6)}, {(1, 3), (4, 7)}, {(1, 4), (4, 6)}, {(1, 4), (4, 7)},
        {(1, 6), (4, 6)}, {(1, 6), (4, 7)}, {(1, 7), (4, 6)}, {(1, 7), (4, 7)}} :
      Finset (Finset (ℕ × ℕ))) := by
  have hS : 𝓗 ⊆ [2, 1, 3, 5, 4, 6, 7].hooks.filter (fun p =>
      p.1 ∈ ({1, 4} : Finset ℕ) ∧ ∀ k ∈ Finset.Icc p.1 p.2,
        [2, 1, 3, 5, 4, 6, 7].getD (k - 1) 0 ≤ [2, 1, 3, 5, 4, 6, 7].getD (p.2 - 1) 0) :=
    fun p hp => Finset.mem_filter.2 ⟨hsub hp, himg ▸ Finset.mem_image_of_mem _ hp, hV2 p hp⟩
  have key : (Finset.powerset ([2, 1, 3, 5, 4, 6, 7].hooks.filter (fun p =>
      p.1 ∈ ({1, 4} : Finset ℕ) ∧ ∀ k ∈ Finset.Icc p.1 p.2,
        [2, 1, 3, 5, 4, 6, 7].getD (k - 1) 0 ≤ [2, 1, 3, 5, 4, 6, 7].getD (p.2 - 1) 0))).filter
      (fun H => H.card = 2 ∧ H.image Prod.fst = {1, 4}) =
      {{(1, 3), (4, 6)}, {(1, 3), (4, 7)}, {(1, 4), (4, 6)}, {(1, 4), (4, 7)},
        {(1, 6), (4, 6)}, {(1, 6), (4, 7)}, {(1, 7), (4, 6)}, {(1, 7), (4, 7)}} := by
    decide
  exact key ▸ Finset.mem_filter.2 ⟨Finset.mem_powerset.2 hS, hcard, himg⟩

/-- The valid hook configurations of `π = 2135467` are exactly the five sets
`{(1,3),(4,6)}`, `{(1,3),(4,7)}`, `{(1,4),(4,6)}`, `{(1,4),(4,7)}` and `{(1,7),(4,6)}`. -/
@[lognarayana "lem_vhc_example"]
public theorem validHookConfigurations_2135467 :
    [2, 1, 3, 5, 4, 6, 7].validHookConfigurations =
      {{(1, 3), (4, 6)}, {(1, 3), (4, 7)}, {(1, 4), (4, 6)}, {(1, 4), (4, 7)},
        {(1, 7), (4, 6)}} := by
  ext 𝓗
  simp only [validHookConfigurations, Finset.mem_filter, Finset.mem_powerset, numDescents,
    descentSet_2135467, Finset.card_pair (show (1 : ℕ) ≠ 4 by decide)]
  constructor
  · rintro ⟨hsub, ⟨hcard, himg⟩, hV2, hV3⟩
    have hC := mem_candidates hsub hcard himg hV2
    simp only [Finset.mem_insert, Finset.mem_singleton] at hC ⊢
    rcases hC with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first
      | simp
      | (rw [pair_V3_iff (hsub (by simp)) (hsub (by simp))] at hV3; revert hV3; decide)
  · intro h
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with rfl | rfl | rfl | rfl | rfl <;>
      refine ⟨by decide, ⟨by decide, by decide⟩, by decide, ?_⟩ <;>
      rw [pair_V3_iff (by decide) (by decide)] <;> decide

/-- The descents of `2135467` in increasing order are `d₁ = 1` and `d₂ = 4`. -/
private lemma orderEmbOfFin_descentSet_2135467 (t : Fin [2, 1, 3, 5, 4, 6, 7].numDescents) :
    ([2, 1, 3, 5, 4, 6, 7].descentSet.orderEmbOfFin rfl t : ℕ) =
      if (t : ℕ) = 0 then 1 else 4 := by
  have hc : [2, 1, 3, 5, 4, 6, 7].descentSet.card = 2 := by decide
  obtain ⟨t, ht⟩ := t
  obtain rfl | rfl : t = 0 ∨ t = 1 := by
    simp only [numDescents, hc] at ht
    omega
  · rw [Finset.orderEmbOfFin_zero rfl ht]
    simp [descentSet_2135467, Finset.min'_insert]
  · have : (⟨1, ht⟩ : Fin [2, 1, 3, 5, 4, 6, 7].numDescents) =
        ⟨[2, 1, 3, 5, 4, 6, 7].descentSet.card - 1, by omega⟩ :=
      Fin.ext (by simp only [hc])
    rw [this, Finset.orderEmbOfFin_last rfl (by omega)]
    simp [descentSet_2135467, Finset.max'_insert]

/-- The valid compositions of `π = 2135467` are exactly
`(3,1,1)`, `(2,1,2)`, `(2,2,1)`, `(1,2,2)` and `(1,3,1)`. -/
@[lognarayana "lem_valid_compositions_example"]
public theorem validCompositions_2135467 :
    [2, 1, 3, 5, 4, 6, 7].validCompositions =
      {![3, 1, 1], ![2, 1, 2], ![2, 2, 1], ![1, 2, 2], ![1, 3, 1]} := by
  rw [validCompositions, validHookConfigurations_2135467]
  simp only [Finset.image_insert, Finset.image_singleton]
  refine congrArg₂ insert ?_ <| congrArg₂ insert ?_ <| congrArg₂ insert ?_ <|
    congrArg₂ insert ?_ <| congrArg singleton ?_ <;>
  funext i <;> fin_cases i <;>
    simp only [hookComposition, Finset.image_insert, Finset.image_singleton, Finset.mem_insert,
      Finset.mem_singleton, not_or, not_and, not_lt, forall_eq_or_imp, forall_eq, length_cons,
      length_nil, zero_add, Nat.reduceAdd, orderEmbOfFin_descentSet_2135467, getD_eq_getElem?_getD,
      Nat.add_one_sub_one, Nat.reduceLT, getElem?_pos, getElem_cons_succ, getElem_cons_zero,
      Option.getD_some, exists_eq_or_imp, left_eq_ite_iff, OfNat.one_ne_ofNat, imp_false,
      Decidable.not_not, Std.le_refl, implies_true, Nat.reduceLeDiff, and_self, and_true,
      ↓existsAndEq, right_eq_ite_iff, OfNat.ofNat_ne_one, true_and, Fin.zero_eta, Fin.isValue,
      Fin.cases_zero, Nat.succ_eq_add_one, Matrix.cons_val, Fin.cases_succ', not_true_eq_false,
      false_and, or_false, Nat.lt_add_one] <;> decide

/-- Fuel-bounded copy of `List.stackSort`, structurally recursive so the kernel can evaluate it. -/
private def stackSortFuel : ℕ → List ℕ → List ℕ
  | 0, _ => []
  | _ + 1, [] => []
  | k + 1, a :: l =>
    stackSortFuel k ((a :: l).take ((a :: l).idxOf (l.foldr max a))) ++
      stackSortFuel k ((a :: l).drop ((a :: l).idxOf (l.foldr max a) + 1)) ++ [l.foldr max a]

private theorem foldr_max_mem (a : ℕ) (l : List ℕ) : l.foldr max a ∈ a :: l := by
  induction l with
  | nil => simp
  | cons b l ih =>
    simp only [foldr_cons, mem_cons] at ih ⊢
    rcases max_choice b (l.foldr max a) with h | h <;> rw [h]
    · simp
    · rcases ih with h' | h' <;> simp [h']

private theorem stackSortFuel_eq :
    ∀ (k : ℕ) (l : List ℕ), l.length ≤ k → stackSortFuel k l = l.stackSort := by
  intro k
  induction k with
  | zero =>
    intro l h
    obtain rfl := length_eq_zero_iff.1 (Nat.le_zero.1 h)
    simp [stackSortFuel, stackSort]
  | succ k ih =>
    intro l h
    cases l with
    | nil => simp [stackSortFuel, stackSort]
    | cons a l =>
      rw [stackSort]
      have := idxOf_lt_length_of_mem (foldr_max_mem a l)
      simp only [stackSortFuel]
      simp only [length_cons] at h this
      rw [ih, ih]
      · simp only [length_drop, length_cons]
        omega
      · simp only [length_take, length_cons]
        omega

/-- The fiber descent polynomial as a list sum over the kernel-computable enumeration of the
fiber: `permutations'` in place of `permutations`, `stackSortFuel` in place of `stackSort`. -/
private theorem fiberDescentPolynomial_eq_sum (R : Type*) [Semiring R] (π : List ℕ) :
    π.fiberDescentPolynomial R =
      ((((idPermWord π.length).permutations'.filter
        fun σ => stackSortFuel π.length σ = π).map numDescents).map ((X : R[X]) ^ ·)).sum := by
  have hnd := (permutations_perm_permutations' (idPermWord π.length)).nodup_iff.mp
    (nodup_permutations _ (nodup_range' ..))
  rw [map_map, ← sum_toFinset _ (hnd.filter _), fiberDescentPolynomial, stackFiber,
    toFinset_eq_of_perm _ _ (permutations_perm_permutations' _), toFinset_filter]
  refine Finset.sum_congr (Finset.filter_congr fun σ hσ => ?_) fun _ _ => rfl
  rw [mem_toFinset, mem_permutations'] at hσ
  rw [stackSortFuel_eq _ σ (by simp [hσ.length_eq, idPermWord]), decide_eq_true_iff]

/-- The fiber of `2135467` has 22 elements, with descent numbers `2` (five times), `3` (twelve
times) and `4` (five times). -/
private theorem numDescents_stackFiber_2135467 :
    (((idPermWord 7).permutations'.filter fun σ => stackSortFuel 7 σ = [2, 1, 3, 5, 4, 6, 7]).map
      numDescents) = [2, 2, 3, 3, 2, 2, 3, 3, 3, 3, 4, 4, 3, 2, 3, 3, 3, 3, 4, 3, 4, 4] := by
  decide +kernel

/-- For `π = 2135467`, `x D_π(x) = 5x³ + 12x⁴ + 5x⁵`. In particular the fertility of `π` is
`D_π(1) = 22`. -/
@[lognarayana "lem_fiber_descent_example"]
public theorem X_mul_fiberDescentPolynomial_2135467 :
    (X : ℝ[X]) * [2, 1, 3, 5, 4, 6, 7].fiberDescentPolynomial ℝ =
      5 * X ^ 3 + 12 * X ^ 4 + 5 * X ^ 5 := by
  rw [fiberDescentPolynomial_eq_sum, show [2, 1, 3, 5, 4, 6, 7].length = 7 from rfl,
    numDescents_stackFiber_2135467]
  simp only [map_cons, map_nil, sum_cons, sum_nil]
  ring

end List

/-! ### Cited results of Defant -/

/-- **Valid hook configurations are determined by their compositions** (C. Defant,
*Fertilitopes*, 2023, Remark 2.2): for every `n ≥ 1` and every permutation `π ∈ S_n`, the map
`List.hookComposition π` is injective on the valid hook configurations
`List.validHookConfigurations π`. -/
@[expose, lognarayana "thm_ext_vhc_composition_injective"]
public def HookCompositionInjOn : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ π ∈ permWords n,
    Set.InjOn π.hookComposition (π.validHookConfigurations : Set (Finset (ℕ × ℕ)))

/-! ### The fiber descent polynomial of the identity -/

namespace List

open Finset

/-- The empty word has no descents. -/
private lemma numDescents_nil : ([] : List ℕ).numDescents = 0 := by
  simp [numDescents, descentSet]

/-- A one-letter word has no descents. -/
private lemma numDescents_singleton (a : ℕ) : [a].numDescents = 0 := by
  simp [numDescents, descentSet]

/-- `des(a b l) = des(b l) + [b < a]`. -/
private lemma numDescents_cons_cons (a b : ℕ) (l : List ℕ) :
    (a :: b :: l).numDescents = (b :: l).numDescents + if b < a then 1 else 0 := by
  have h : (a :: b :: l).descentSet =
      (b :: l).descentSet.map (addRightEmbedding 1) ∪ (if b < a then {1} else ∅) := by
    ext i
    simp only [descentSet, Finset.mem_union, Finset.mem_map, Finset.mem_filter, Finset.mem_Ico,
      addRightEmbedding_apply, length_cons]
    rcases i with _ | _ | i
    · split_ifs <;> simp
    · split_ifs with hba <;> simp [hba]
    · have hi : i + 1 + 1 ∉ (if b < a then ({1} : Finset ℕ) else ∅) := by
        split_ifs <;> simp
      rw [or_iff_left hi]
      constructor
      · rintro ⟨⟨_, h1⟩, h2, h3⟩
        exact ⟨i + 1, ⟨⟨by omega, by omega⟩, by omega, by simpa using h3⟩, rfl⟩
      · rintro ⟨x, ⟨⟨h0, h1⟩, h2, h3⟩, hx⟩
        obtain rfl : x = i + 1 := by omega
        exact ⟨⟨by omega, by omega⟩, by omega, by simpa using h3⟩
  have hd : _root_.Disjoint ((b :: l).descentSet.map (addRightEmbedding 1))
      (if b < a then ({1} : Finset ℕ) else (∅ : Finset ℕ)) := by
    split_ifs
    · simp only [Finset.disjoint_singleton_right, Finset.mem_map, addRightEmbedding_apply,
        not_exists, not_and]
      intro x hx h
      simp [descentSet] at hx
      omega
    · simp
  rw [numDescents, h, Finset.card_union_of_disjoint hd, Finset.card_map]
  split_ifs <;> simp


/-- If `m` exceeds every letter of `L` and `R`, then
`des(L m R) = des(L) + des(R) + [R ≠ ∅]`. -/
private lemma numDescents_append_cons {L R : List ℕ} {m : ℕ} (hL : ∀ x ∈ L, x < m)
    (hR : ∀ x ∈ R, x < m) :
    (L ++ m :: R).numDescents = L.numDescents + R.numDescents + if R = [] then 0 else 1 := by
  induction L with
  | nil =>
    cases R with
    | nil => simp [numDescents_singleton, numDescents_nil]
    | cons b R => simp [numDescents_cons_cons, numDescents_nil, hR b (by simp)]
  | cons a L ih =>
    have ih := ih fun x hx => hL x (by simp [hx])
    have ha := hL a (by simp)
    cases L with
    | nil =>
      simp only [nil_append] at ih
      simp only [cons_append, nil_append, numDescents_cons_cons, ih, numDescents_singleton,
        numDescents_nil, if_neg (not_lt.2 ha.le)]
      omega
    | cons b L =>
      simp only [cons_append] at ih ⊢
      rw [numDescents_cons_cons, ih, numDescents_cons_cons a b L]
      omega

/-- A right fold of `max` over `a :: l` is the maximum `m` of `a :: l`. -/
private theorem foldr_max_eq {a m : ℕ} {l : List ℕ}
    (hm : m ∈ a :: l) (hle : ∀ x ∈ a :: l, x ≤ m) : l.foldr max a = m := by
  refine le_antisymm ?_ ?_
  · clear hm
    induction l <;> simp_all
  · clear hle
    induction l with
    | nil => simp_all
    | cons b l ih =>
      simp only [List.mem_cons, List.foldr_cons, le_max_iff] at *
      rcases hm with h | rfl | h
      · exact .inr (ih (.inl h))
      · exact .inl le_rfl
      · exact .inr (ih (.inr h))

/-- The stack-sorting map splits a word at its maximum `m` when `m` follows only smaller
letters: `s(L m R) = s(L) s(R) m`. -/
private theorem stackSort_append_cons {L R : List ℕ} {m : ℕ}
    (hL : ∀ x ∈ L, x < m) (hR : ∀ x ∈ R, x ≤ m) :
    (L ++ m :: R).stackSort = L.stackSort ++ R.stackSort ++ [m] := by
  obtain ⟨a, l, hal⟩ : ∃ a l, L ++ m :: R = a :: l := by
    cases L with
    | nil => exact ⟨m, R, rfl⟩
    | cons a L => exact ⟨a, L ++ m :: R, rfl⟩
  have hf : l.foldr max a = m := foldr_max_eq (by simp [← hal]) <| hal ▸ by
    simpa [or_imp, forall_and] using ⟨fun x hx => (hL x hx).le, hR⟩
  have hidx : (L ++ m :: R).idxOf m = L.length := by
    rw [List.idxOf_append_of_notMem (fun h => lt_irrefl _ (hL m h))]
    simp
  rw [hal, List.stackSort.eq_2, hf, ← hal, hidx, List.take_left, ← List.drop_drop,
    List.drop_left]
  rfl

/-- The words `σ` (rearrangements of `a (a+1) ⋯ (a+n-1)`) with `s(σ) = a (a+1) ⋯ (a+n-1)`. -/
private def idFiber (a n : ℕ) : Finset (List ℕ) :=
  (range' a n).permutations.toFinset.filter fun σ ↦ σ.stackSort = range' a n

/-- A word lies in `idFiber a n` iff it stack-sorts to `a (a+1) ⋯ (a+n-1)`. -/
private lemma mem_idFiber {a n : ℕ} {σ : List ℕ} : σ ∈ idFiber a n ↔ σ.stackSort = range' a n := by
  simp only [idFiber, Finset.mem_filter, mem_toFinset, mem_permutations, and_iff_right_iff_imp]
  intro h
  exact h ▸ (stackSort_perm σ).symm

/-- The words of `idFiber a n` have length `n`. -/
private lemma length_of_mem_idFiber {a n : ℕ} {σ : List ℕ} (h : σ ∈ idFiber a n) :
    σ.length = n := by
  rw [← (stackSort_perm σ).length_eq, mem_idFiber.1 h, length_range']

/-- The letters of a word of `idFiber a n` lie in `[a, a + n)`. -/
private lemma mem_range'_of_mem_idFiber {a n : ℕ} {σ : List ℕ} (h : σ ∈ idFiber a n) {x : ℕ}
    (hx : x ∈ σ) : a ≤ x ∧ x < a + n := by
  have := (mem_idFiber.1 h ▸ (stackSort_perm σ)).mem_iff.2 hx
  simpa [mem_range'_1] using this

/-- `s(σ) = a ⋯ (a+n)` iff `σ = L (a+n) R` with `s(L) = a ⋯ (a+k-1)` and
`s(R) = (a+k) ⋯ (a+n-1)` for some `k + j = n`. -/
private lemma stackSort_eq_range'_succ_iff {a n : ℕ} {σ : List ℕ} :
    σ.stackSort = range' a (n + 1) ↔ ∃ kj ∈ antidiagonal n, ∃ L R,
      L ∈ idFiber a kj.1 ∧ R ∈ idFiber (a + kj.1) kj.2 ∧ σ = L ++ (a + n) :: R := by
  have hsplit : range' a (n + 1) = range' a n ++ [a + n] := by
    simpa using (range'_append_1 : range' a n ++ range' (a + n) 1 = _).symm
  constructor
  · intro h
    have hp : σ ~ range' a (n + 1) := h ▸ (stackSort_perm σ).symm
    have hmem : a + n ∈ σ := hp.mem_iff.2 (by simp [mem_range'_1])
    obtain ⟨L, R, rfl⟩ := List.append_of_mem hmem
    have hnd : (L ++ (a + n) :: R).Nodup := hp.nodup_iff.2 (nodup_range' ..)
    have hle : ∀ x ∈ L ++ (a + n) :: R, x ≤ a + n := fun x hx => by
      have := mem_range'_1.1 (hp.mem_iff.1 hx)
      omega
    rw [nodup_append] at hnd
    have hL : ∀ x ∈ L, x < a + n := fun x hx =>
      lt_of_le_of_ne (hle x (by simp [hx])) (hnd.2.2 x hx (a + n) (by simp))
    have hR : ∀ x ∈ R, x < a + n := fun x hx =>
      lt_of_le_of_ne (hle x (by simp [hx])) (fun he => (nodup_cons.1 hnd.2.1).1 (he ▸ hx))
    rw [stackSort_append_cons hL (fun x hx => (hR x hx).le), hsplit] at h
    have h2 : L.stackSort ++ R.stackSort = range' a n := append_cancel_right h
    have hk : L.stackSort.length = L.length := (stackSort_perm L).length_eq
    have hkn : L.length ≤ n := by
      have := congrArg length h2
      simp only [length_append, length_range'] at this
      omega
    rw [← Nat.add_sub_cancel' hkn, ← range'_append_1] at h2
    obtain ⟨h3, h4⟩ := List.append_inj h2 (by simp [hk])
    exact ⟨(L.length, n - L.length), by simp; omega, L, R, mem_idFiber.2 h3, mem_idFiber.2 h4, rfl⟩
  · rintro ⟨⟨k, j⟩, hkj, L, R, hL, hR, rfl⟩
    simp only [HasAntidiagonal.mem_antidiagonal] at hkj
    have hLm : ∀ x ∈ L, x < a + n := fun x hx => by
      have := mem_range'_of_mem_idFiber hL hx
      omega
    have hRm : ∀ x ∈ R, x ≤ a + n := fun x hx => by
      have := mem_range'_of_mem_idFiber hR hx
      simp only at this
      omega
    rw [stackSort_append_cons hLm hRm, mem_idFiber.1 hL, mem_idFiber.1 hR, range'_append_1,
      hkj, hsplit]

/-- The fiber of `a ⋯ (a+n)` as the disjoint union, over `k + j = n`, of the words `L (a+n) R`
with `L` in the fiber of `a ⋯ (a+k-1)` and `R` in that of `(a+k) ⋯ (a+n-1)`. -/
private lemma idFiber_succ (a n : ℕ) : idFiber a (n + 1) = (antidiagonal n).biUnion
    fun kj ↦ (idFiber a kj.1 ×ˢ idFiber (a + kj.1) kj.2).image fun p ↦ p.1 ++ (a + n) :: p.2 := by
  ext σ
  rw [mem_idFiber, stackSort_eq_range'_succ_iff]
  simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_product, Prod.exists]
  exact ⟨fun ⟨k, j, hkj, L, R, hL, hR, h⟩ => ⟨k, j, hkj, L, R, ⟨hL, hR⟩, h.symm⟩,
    fun ⟨k, j, hkj, L, R, ⟨hL, hR⟩, h⟩ => ⟨k, j, hkj, L, R, hL, hR, h.symm⟩⟩

/-- `1, Ñ_0, Ñ_1, …`: the descent generating function of the fiber of the identity. -/
private noncomputable def fiberE : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => shiftedNarayanaPolynomial n

/-- The Catalan-type recurrence `E_{n+1} = ∑_{k+j=n} E_k E_j x^{[j ≠ 0]}`, from the quadratic
recurrence of the shifted Narayana polynomials. -/
private lemma sum_antidiagonal_fiberE (n : ℕ) :
    ∑ kj ∈ antidiagonal n, fiberE kj.1 * fiberE kj.2 * X ^ (if kj.2 = 0 then 0 else 1) =
      fiberE (n + 1) := by
  rcases n with _ | m
  · simp [fiberE, shiftedNarayanaPolynomial_zero]
  rw [Finset.Nat.sum_antidiagonal_succ]
  rcases m with _ | m
  · simp [fiberE, shiftedNarayanaPolynomial_zero, shiftedNarayanaPolynomial_one]
    ring
  rw [Finset.Nat.sum_antidiagonal_succ']
  simp only [fiberE, if_true, if_neg (Nat.succ_ne_zero _), pow_zero, pow_one, mul_one, one_mul]
  rw [shiftedNarayanaPolynomial_add_two, Finset.mul_sum]
  have : ∑ x ∈ antidiagonal m,
      shiftedNarayanaPolynomial x.1 * shiftedNarayanaPolynomial x.2 * X =
      ∑ x ∈ antidiagonal m,
        X * (shiftedNarayanaPolynomial x.1 * shiftedNarayanaPolynomial x.2) :=
    Finset.sum_congr rfl fun _ _ => by ring
  linear_combination this

/-- The only word stack-sorting to the empty word is the empty word. -/
private lemma idFiber_zero (a : ℕ) : idFiber a 0 = {[]} := by
  ext σ
  rw [mem_idFiber, Finset.mem_singleton, range'_zero]
  exact ⟨fun h => (h ▸ stackSort_perm σ).symm.eq_nil, by rintro rfl; exact stackSort.eq_1⟩

/-- The pieces of the splitting `idFiber_succ` are pairwise disjoint: the position of the
maximum `a + n` determines `k`. -/
private lemma pairwiseDisjoint_idFiber_split (a n : ℕ) :
    ((antidiagonal n : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)).PairwiseDisjoint fun kj ↦
      (idFiber a kj.1 ×ˢ idFiber (a + kj.1) kj.2).image fun p ↦ p.1 ++ (a + n) :: p.2 := by
  intro kj hkj kj' hkj' hne
  simp only [Function.onFun]
  rw [Finset.disjoint_left]
  intro σ h1 h2
  simp only [Finset.mem_image, Finset.mem_product, Prod.exists] at h1 h2
  obtain ⟨L, R, ⟨hL, hR⟩, rfl⟩ := h1
  obtain ⟨L', R', ⟨hL', hR'⟩, he⟩ := h2
  have hnot : ∀ {L : List ℕ} {b k : ℕ}, L ∈ idFiber b k → b + k ≤ a + n → a + n ∉ L :=
    fun h hb hm => by
      have := mem_range'_of_mem_idFiber h hm
      omega
  have hk := HasAntidiagonal.mem_antidiagonal.1 (Finset.mem_coe.1 hkj)
  have hk' := HasAntidiagonal.mem_antidiagonal.1 (Finset.mem_coe.1 hkj')
  have i1 := congrArg (·.idxOf (a + n)) he
  rw [idxOf_append_of_notMem (hnot hL' (by omega)), idxOf_append_of_notMem (hnot hL (by omega)),
    idxOf_cons_self, idxOf_cons_self, length_of_mem_idFiber hL, length_of_mem_idFiber hL'] at i1
  exact hne (Prod.ext (by omega) (by omega))

/-- The descent generating function of `idFiber a n` is `E_n`, whatever `a`. -/
private lemma sum_idFiber (n : ℕ) :
    ∀ a, ∑ σ ∈ idFiber a n, (X : ℝ[X]) ^ σ.numDescents = fiberE n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro a
  rcases n with _ | n
  · simp [idFiber_zero, fiberE, numDescents_nil]
  rw [idFiber_succ, Finset.sum_biUnion (pairwiseDisjoint_idFiber_split a n),
    ← sum_antidiagonal_fiberE]
  refine Finset.sum_congr rfl fun kj hkj => ?_
  have hkj' := HasAntidiagonal.mem_antidiagonal.1 hkj
  rw [Finset.sum_image, Finset.sum_product, ← ih kj.1 (by omega) a,
    ← ih kj.2 (by omega) (a + kj.1), Finset.sum_mul, Finset.sum_mul]
  · refine Finset.sum_congr rfl fun L hL => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun R hR => ?_
    have hLm : ∀ x ∈ L, x < a + n := fun x hx => by
      have := mem_range'_of_mem_idFiber hL hx
      omega
    have hRm : ∀ x ∈ R, x < a + n := fun x hx => by
      have := mem_range'_of_mem_idFiber hR hx
      omega
    have hRl : R = [] ↔ kj.2 = 0 := by
      rw [← length_of_mem_idFiber hR, length_eq_zero_iff]
    simp only
    rw [numDescents_append_cons hLm hRm, pow_add, pow_add]
    simp only [hRl]
  · rintro ⟨L, R⟩ hp ⟨L', R'⟩ hp' he
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe] at hp hp' he
    have := List.append_inj he
      (by rw [length_of_mem_idFiber hp.1, length_of_mem_idFiber hp'.1])
    simp_all

/-- For `n ≥ 1`, `x D_{ι_n}(x) = N_n(x)`: the fiber descent polynomial of the identity permutation
`ι_n`, multiplied by `x`, is the Narayana polynomial `N_n`. Splitting `σ = L n R` at its maximum,
`s(σ) = s(L) s(R) n` is the identity iff `s(L) = 1 ⋯ k` and `s(R) = (k+1) ⋯ (n-1)`, and
`des(σ) = des(L) + des(R) + [R ≠ ∅]`; so `D_{ι_n}` satisfies the quadratic recurrence of
`Ñ_{n-1}`, and `x Ñ_{n-1} = N_n`. -/
@[lognarayana "lem_identity_fiber_narayana"]
public theorem X_mul_fiberDescentPolynomial_idPermWord {n : ℕ} (hn : 1 ≤ n) :
    (X : ℝ[X]) * (idPermWord n).fiberDescentPolynomial ℝ = narayanaPolynomial n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have : (idPermWord (m + 1)).fiberDescentPolynomial ℝ = fiberE (m + 1) := by
    rw [fiberDescentPolynomial, stackFiber, idPermWord, length_range']
    exact sum_idFiber (m + 1) 1
  rw [this, fiberE, narayanaPolynomial_succ_eq_X_mul]

end List
