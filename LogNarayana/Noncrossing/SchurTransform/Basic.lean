/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib
public import LogNarayana.Attr
public import LogNarayana.Noncrossing.SchurTransform.Defs
public import LogNarayana.Narayana.Transform.Defs
public import LogNarayana.Narayana.Polynomials.Defs
public import LogNarayana.Noncrossing.CaseTwo.Defs
public import LogNarayana.Noncrossing.RestrictedRefinement.Defs
public import LogNarayana.Nestohedron.Fertilitope.Defs
public import LogNarayana.Polynomial.RealStable.Defs
public import LogNarayana.Polynomial.LogConcave.Defs
public import LogNarayana.Narayana.Polynomials.Basic
public import LogNarayana.Noncrossing.CaseTwo.Basic
public import LogNarayana.Nestohedron.QuadraticReplacement.Basic
public import LogNarayana.Noncrossing.RestrictedRefinement.Basic
public import LogNarayana.Nestohedron.Fertilitope.Basic
public import LogNarayana.Polynomial.RealStable.Basic
public import LogNarayana.Lorentzian.BrandenHuh.Basic
public import LogNarayana.Lorentzian.Symbol.Basic
public import LogNarayana.StackSorting.ValidHookConfigurations.Basic

/-!
# Determinant-twisted Schur polynomials

For the hook-like shapes `(a + d, a^{r-1})`, a semistandard tableau is forced in its first `a`
columns and free only in the weakly increasing tail of its first row, so the Kostka number
`K_{(a+d, a^{r-1}), α}` is `1` when `α ≥ a` coordinatewise and `|α| = a r + d`, and `0`
otherwise. Hence `s_{(a+d, a^{r-1})} = (z₁ ⋯ zᵣ)^a h_d`, and its Narayana transform is
`Φ_{(a+d, a^{r-1}),r} = ∑_{|b| = d} ∏ᵢ Ñ_{a + bᵢ}`. Multiplied by `x^r`, this is the Narayana sum
over the lattice points of the integral binary nestohedron `(a+1)𝟏 + dΔ_{[r]}`; it is therefore
log-concave, and it is a multiple of the restricted noncrossing refinement polynomial
`R^{(a+1)}_{r(a+1)+d,r}`, which for `a = 1` is real-rooted.

For the one-row shape `(d)`, the series `W = z V` with `V = ∑ Ñ_m z^m` satisfies
`W = z (1 + W)(1 + x W)`, and Lagrange inversion gives
`Φ_{(d),r}(x) = r/(r+d) ∑_j C(r+d, j) C(r+d, d-j) x^j = r/(r+d) (1-x)^d P^{(r,r)}_d((1+x)/(1-x))`.
The zeros of the Jacobi polynomial `P^{(r,r)}_d` in `(-1, 1)` are carried to `d` distinct
negative zeros of `Φ_{(d),r}`.

## Main results

* `PartitionAtMostParts.kostkaNumber_hook`: the Kostka numbers of `(a + d, a^{r-1})`.
* `PartitionAtMostParts.schurPolynomial_hook`: `s_{(a+d, a^{r-1})} = (z₁ ⋯ zᵣ)^a h_d`.
* `PartitionAtMostParts.schurNarayanaTransform_hook`: `Φ_{(a+d, a^{r-1}),r}` as a sum of
  products of shifted Narayana polynomials.
* `shiftedNarayanaGenSeries_eq_mul`: `V = (1 + z V)(1 + x z V)`.
* `PartitionAtMostParts.schurNarayanaTransform_row`: the closed form of `Φ_{(d),r}`.
* `PartitionAtMostParts.eval_schurNarayanaTransform_row`: the Jacobi form of `Φ_{(d),r}`.
* `PartitionAtMostParts.hasOnlyNegativeRoots_schurNarayanaTransform_row`: `Φ_{(d),r}` has only
  negative real zeros.
* `PartitionAtMostParts.finsum_latticePoints_prod_narayanaPolynomial_hook`:
  `x^r Φ_{(a+d, a^{r-1}),r}` as a lattice-point sum of products of Narayana polynomials.
* `PartitionAtMostParts.restrictedNoncrossingRefinementPoly_eq_schurNarayanaTransform_hook`:
  `R^{(a+1)}_{n,r}` as a multiple of `x^r Φ_{(a+d, a^{r-1}),r}`.
* `PartitionAtMostParts.splits_schurNarayanaTransform_hook_one`: `Φ_{(d+1, 1^{r-1}),r}` is
  real-rooted.
* `PartitionAtMostParts.isLogConcave_schurNarayanaTransform_hook`: `Φ_{(a+d, a^{r-1}),r}` is
  log-concave.
* `PartitionAtMostParts.isLogConcave_schurNarayanaTransform_two`: `Φ_{μ,2}` is log-concave for
  every `μ ∈ Par₂`.

## Implementation notes

The results the proofs cite from the literature — Kreweras' block-size count, the zeros of
Jacobi polynomials, the closure properties of real stability and of Lorentzian polynomials, the
symbol theorem of Brändén–Huh, the realization of integral binary nestohedra by fertilitopes and
the refined fertility formula — are taken as hypotheses; Lagrange inversion
(`PowerSeries.lagrangeInversion`) and the γ-expansion of the shifted Narayana polynomials
(`shiftedNarayanaGammaExpansion_holds`) are proved. Real-rootedness of a real polynomial is
`Polynomial.Splits`.

## References

* [LogNarayana] *Log-Concavity in Narayana Transforms and Stack-Sorting Fibers*, Sections 7
  and 8.
* [DLMF] *NIST Digital Library of Mathematical Functions*, §§18.2(vi) and 18.5.
* [BH] P. Brändén, J. Huh, *Lorentzian polynomials*.
-/

/-! ### Kostka numbers of hook shapes -/

namespace PartitionAtMostParts

section KostkaHook

private lemma mem_hook {r a d : ℕ} {i j : ℕ} :
    (i, j) ∈ (hook r a d).youngDiagram ↔ i < r ∧ j < (if i = 0 then a + d else a) := by
  simp only [youngDiagram, YoungDiagram.mem_ofRowLens, List.length_ofFn, List.getElem_ofFn]
  exact ⟨fun ⟨h1, h2⟩ => ⟨h1, by simpa [hook] using h2⟩,
    fun ⟨h1, h2⟩ => ⟨h1, by simpa [hook] using h2⟩⟩

/-- Entries down a column of length `r` of `T ∈ SSYT_r(hook)` in the first `a` columns grow by
at least one per row. -/
private lemma col_add {r a d : ℕ} (T : SemistandardYoungTableau (hook r a d).youngDiagram)
    {i j : ℕ} (hj : j < a) : ∀ k, i + k < r → T i j + k ≤ T (i + k) j := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    have h1 := ih (by omega)
    have h2 : T (i + k) j < T (i + (k + 1)) j :=
      T.col_strict (by omega) (mem_hook.2 ⟨hk, by split_ifs <;> omega⟩)
    omega

private lemma col_eq {r a d : ℕ} {T : SemistandardYoungTableau (hook r a d).youngDiagram}
    (hT : T ∈ (hook r a d).semistandardYoungTableaux) {i j : ℕ} (hi : i < r) (hj : j < a) :
    T i j = i := by
  have h1 := col_add T (i := 0) hj i (by omega)
  have h2 := col_add T (i := i) hj (r - 1 - i) (by omega)
  have h3 := hT (i + (r - 1 - i)) j (mem_hook.2 ⟨by omega, by split_ifs <;> omega⟩)
  simp at h1
  omega

/-- The content of `T ∈ SSYT_r(hook)`: each letter `v < r` occurs `a` times in the first `a`
columns, plus the number of times it occurs in the tail `T 0 (a + l)`, `l < d`, of row `0`. -/
private lemma content_eq {r a d : ℕ} {T : SemistandardYoungTableau (hook r a d).youngDiagram}
    (hT : T ∈ (hook r a d).semistandardYoungTableaux) (v : Fin r) :
    T.content r v = a + (Finset.univ.filter fun l : Fin d => T 0 (a + l) = v).card := by
  classical
  have hset : ((hook r a d).youngDiagram.cells.filter fun c => T c.1 c.2 = v) =
      (Finset.range a).image (fun j => ((v : ℕ), j)) ∪
        (Finset.univ.filter fun l : Fin d => T 0 (a + l) = v).image
          (fun l : Fin d => ((0 : ℕ), a + (l : ℕ))) := by
    ext ⟨i, j⟩
    simp only [Finset.mem_filter, YoungDiagram.mem_cells, Finset.mem_union, Finset.mem_image,
      Finset.mem_range, Finset.mem_univ, true_and, Prod.mk.injEq, mem_hook]
    constructor
    · rintro ⟨⟨hi, hj⟩, hv⟩
      by_cases hja : j < a
      · left
        refine ⟨j, hja, ?_, rfl⟩
        rw [col_eq hT hi hja] at hv
        exact hv.symm
      · right
        obtain rfl : i = 0 := by
          by_contra h
          simp [h] at hj
          omega
        simp only [↓reduceIte] at hj
        refine ⟨⟨j - a, by omega⟩, ?_, rfl, by simp; omega⟩
        simp only
        rw [show a + (j - a) = j by omega]
        exact hv
    · rintro (⟨j', hj', rfl, rfl⟩ | ⟨l, hl, rfl, rfl⟩)
      · exact ⟨⟨v.2, by split_ifs <;> omega⟩, col_eq hT v.2 hj'⟩
      · exact ⟨⟨by have := v.2; omega, by simp⟩, hl⟩
  unfold SemistandardYoungTableau.content
  rw [hset, Finset.card_union_of_disjoint, Finset.card_image_of_injective,
    Finset.card_image_of_injective, Finset.card_range]
  · exact fun x y h => Fin.ext (by simpa using h)
  · exact fun x y h => by simpa using h
  · rw [Finset.disjoint_left]
    simp only [Finset.mem_image, Finset.mem_range, Finset.mem_filter, Finset.mem_univ, true_and]
    rintro _ ⟨j, hj, rfl⟩ ⟨l, _, h⟩
    simp at h
    omega

private lemma count_ofFn {n : ℕ} (g : Fin n → ℕ) (v : ℕ) :
    (List.ofFn g).count v = (Finset.univ.filter fun l => g l = v).card := by
  rw [← Multiset.coe_count, ← Fin.univ_val_map, Multiset.count_map]
  simp [Finset.card_def, Finset.filter_val, eq_comm]

/-- A monotone sequence of naturals is determined by how often it takes each value. -/
private lemma eq_of_monotone_of_card_fiber {n : ℕ} {g g' : Fin n → ℕ} (hg : Monotone g)
    (hg' : Monotone g')
    (h : ∀ v, (Finset.univ.filter fun l => g l = v).card =
      (Finset.univ.filter fun l => g' l = v).card) : g = g' := by
  apply List.ofFn_injective
  refine List.Perm.eq_of_sortedLE hg.sortedLE_ofFn hg'.sortedLE_ofFn ?_
  rw [List.perm_iff_count]
  intro v
  rw [count_ofFn, count_ofFn, h]

private lemma tail_monotone {r a d : ℕ} (T : SemistandardYoungTableau (hook r a d).youngDiagram)
    (hr : 1 ≤ r) : Monotone fun l : Fin d => T 0 (a + l) := by
  intro l₁ l₂ hl
  rcases eq_or_lt_of_le hl with h | h
  · rw [h]
  · exact T.row_weak (by simpa using h) (mem_hook.2 ⟨hr, by simp⟩)

private lemma tail_lt {r a d : ℕ} {T : SemistandardYoungTableau (hook r a d).youngDiagram}
    (hT : T ∈ (hook r a d).semistandardYoungTableaux) (hr : 1 ≤ r) (l : Fin d) :
    T 0 (a + l) < r :=
  hT 0 _ (mem_hook.2 ⟨hr, by simp⟩)

/-- A tableau in `SSYT_r(hook r a d)` is determined by its content: the first `a` columns are
forced by `col_eq`, and the weakly increasing tail of row `0` by its fibre sizes. -/
private lemma tableau_unique {r a d : ℕ} (hr : 1 ≤ r)
    {T T' : SemistandardYoungTableau (hook r a d).youngDiagram}
    (hT : T ∈ (hook r a d).semistandardYoungTableaux)
    (hT' : T' ∈ (hook r a d).semistandardYoungTableaux)
    (h : T.content r = T'.content r) : T = T' := by
  have htail : (fun l : Fin d => T 0 (a + l)) = fun l : Fin d => T' 0 (a + l) := by
    refine eq_of_monotone_of_card_fiber (tail_monotone T hr) (tail_monotone T' hr) fun v => ?_
    by_cases hv : v < r
    · have := congrFun h ⟨v, hv⟩
      rw [content_eq hT, content_eq hT'] at this
      simpa using this
    · have h0 : ∀ S ∈ (hook r a d).semistandardYoungTableaux,
          (Finset.univ.filter fun l : Fin d => S 0 (a + l) = v) = ∅ := fun S hS =>
        Finset.filter_eq_empty_iff.2 fun l _ h => hv (h ▸ tail_lt hS hr l)
      rw [h0 T hT, h0 T' hT']
  ext i j
  by_cases hc : (i, j) ∈ (hook r a d).youngDiagram
  · obtain ⟨hi, hj⟩ := mem_hook.1 hc
    by_cases hja : j < a
    · rw [col_eq hT hi hja, col_eq hT' hi hja]
    · have hi0 : i = 0 := by by_contra h0; simp [h0] at hj; omega
      subst hi0
      simp at hj
      have := congrFun htail ⟨j - a, by omega⟩
      simp only at this
      rwa [show a + (j - a) = j by omega] at this
  · rw [T.zeros hc, T'.zeros hc]

private lemma condition_of_mem {r a d : ℕ} (hr : 1 ≤ r) {α : Fin r → ℕ}
    {T : SemistandardYoungTableau (hook r a d).youngDiagram}
    (hT : T ∈ (hook r a d).semistandardYoungTableaux) (h : T.content r = α) :
    (∀ i, a ≤ α i) ∧ ∑ i, α i = a * r + d := by
  classical
  subst h
  refine ⟨fun i => by rw [content_eq hT]; omega, ?_⟩
  simp_rw [content_eq hT]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [mul_comm]
  congr 1
  let f : Fin d → Fin r := fun l => ⟨T 0 (a + l), tail_lt hT hr l⟩
  have := Finset.card_eq_sum_card_fiberwise (f := f) (s := Finset.univ) (t := Finset.univ)
    (by simp [Set.MapsTo])
  simp only [Finset.card_univ, Fintype.card_fin] at this
  refine Eq.trans ?_ this.symm
  refine Finset.sum_congr rfl fun v _ => ?_
  congr 1
  ext l
  simp [f, Fin.ext_iff]

/-- If `α ≥ a` coordinatewise and `|α| = a r + d`, the filling with `i` in row `i` of the first
`a` columns and the letters `v` repeated `α v - a` times, in weakly increasing order, along the
tail of row `0` is a tableau of shape `hook r a d` and content `α`. -/
private lemma exists_mem_of_condition {r a d : ℕ} (hr : 1 ≤ r) {α : Fin r → ℕ}
    (h : (∀ i, a ≤ α i) ∧ ∑ i, α i = a * r + d) :
    ∃ T ∈ (hook r a d).semistandardYoungTableaux, T.content r = α := by
  classical
  obtain ⟨hα, hsum⟩ := h
  set M : Multiset ℕ := ∑ v : Fin r, (α v - a) • {(v : ℕ)} with hM
  set L : List ℕ := M.sort (· ≤ ·) with hLdef
  have hL : L.length = d := by
    have h1 : ∑ v : Fin r, (α v - a) + ∑ _v : Fin r, a = ∑ v, α v := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun v _ => Nat.sub_add_cancel (hα v)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h1
    rw [hLdef, Multiset.length_sort, hM, Multiset.card_sum]
    simp only [Multiset.card_nsmul, Multiset.card_singleton, mul_one]
    rw [mul_comm] at hsum
    omega
  have hsorted : L.SortedLE := (Multiset.pairwise_sort M _).sortedLE
  have hmemL : ∀ x ∈ L, x < r := by
    intro x hx
    rw [hLdef, Multiset.mem_sort, hM, Multiset.mem_sum] at hx
    obtain ⟨v, _, hv⟩ := hx
    rw [Multiset.mem_nsmul] at hv
    rw [Multiset.mem_singleton.1 hv.2]
    exact v.2
  have hcount : ∀ v : Fin r, L.count (v : ℕ) = α v - a := by
    intro v
    rw [← Multiset.coe_count, hLdef, Multiset.sort_eq, hM, Multiset.count_sum']
    simp only [Multiset.count_nsmul, Multiset.count_singleton, Fin.val_inj, mul_ite, mul_one,
      mul_zero]
    rw [Finset.sum_ite_eq]
    simp
  let e : ℕ → ℕ → ℕ := fun i j =>
    if i < r ∧ j < (if i = 0 then a + d else a) then
      (if i = 0 then (if j < a then 0 else L.getD (j - a) 0) else i) else 0
  let T : SemistandardYoungTableau (hook r a d).youngDiagram :=
    { entry := e
      row_weak' := by
        intro i j1 j2 hj hc
        obtain ⟨hi, hj2⟩ := mem_hook.1 hc
        have hj1 : j1 < (if i = 0 then a + d else a) := lt_trans hj hj2
        simp only [e, hi, hj1, hj2, and_self, if_true]
        by_cases hi0 : i = 0
        · subst hi0
          simp only [if_true] at hj2 ⊢
          by_cases hja : j1 < a
          · simp [hja]
          · have hja2 : ¬ j2 < a := by omega
            simp only [hja, hja2, if_false]
            rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
            exact hsorted.getElem_le_getElem_of_le (by omega)
        · simp [hi0]
      col_strict' := by
        intro i1 i2 j hi hc
        obtain ⟨hi2, hj⟩ := mem_hook.1 hc
        have hi20 : i2 ≠ 0 := by omega
        simp only [hi20, if_false] at hj
        have hj1 : j < (if i1 = 0 then a + d else a) := by split_ifs <;> omega
        simp only [e, hi2, hj, hj1, hi20, show i1 < r by omega, and_self, if_true, if_false]
        split_ifs <;> omega
      zeros' := by
        intro i j hc
        have : ¬ (i < r ∧ j < (if i = 0 then a + d else a)) := fun h => hc (mem_hook.2 h)
        simp only [e, this, if_false] }
  have hTe : ∀ i j, T i j = e i j := fun _ _ => rfl
  have hT : T ∈ (hook r a d).semistandardYoungTableaux := by
    intro i j hc
    have hc' := mem_hook.1 hc
    rw [hTe]
    simp only [e, hc', and_self, if_true]
    split_ifs with h0 hja
    · omega
    · subst h0
      simp only [if_true] at hc'
      rw [List.getD_eq_getElem _ _ (by omega)]
      exact hmemL _ (List.getElem_mem _)
    · exact hc'.1
  refine ⟨T, hT, funext fun v => ?_⟩
  rw [content_eq hT]
  have hofFn : List.ofFn (fun l : Fin d => T 0 (a + l)) = L := by
    refine List.ext_getElem (by simp [hL]) fun n h1 h2 => ?_
    simp only [List.getElem_ofFn, hTe, e]
    simp only [List.length_ofFn] at h1
    rw [if_pos ⟨hr, by simp; omega⟩]
    simp only [if_true, show ¬ a + n < a by omega, if_false, Nat.add_sub_cancel_left]
    rw [List.getD_eq_getElem _ _ h2]
  rw [← count_ofFn, hofFn, hcount]
  have := hα v
  omega

end KostkaHook


/-- The Kostka number of the shape `(a + d, a^{r-1})` at `α` is `1` if `α i ≥ a` for every `i`
and `|α| = a r + d`, and `0` otherwise. -/
@[lognarayana "lem_kostka_hook_shape"]
public theorem kostkaNumber_hook {r : ℕ} (hr : 1 ≤ r) (a d : ℕ) (α : Fin r → ℕ) :
    (hook r a d).kostkaNumber α =
      if (∀ i, a ≤ α i) ∧ ∑ i, α i = a * r + d then 1 else 0 := by
  unfold kostkaNumber
  split_ifs with h
  · obtain ⟨T, hT, hTα⟩ := exists_mem_of_condition hr h
    rw [Set.ncard_eq_one]
    refine ⟨T, Set.eq_singleton_iff_unique_mem.2 ⟨⟨hT, hTα⟩, fun T' hT' => ?_⟩⟩
    exact tableau_unique hr hT'.1 hT (hT'.2.trans hTα.symm)
  · convert Set.ncard_empty (SemistandardYoungTableau (hook r a d).youngDiagram)
    ext T
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
    exact fun hT hTα => h (condition_of_mem hr hT hTα)

end PartitionAtMostParts

/-! ### The Schur polynomial of a hook shape -/

namespace PartitionAtMostParts

section SchurHook

open MvPolynomial

/-- A product of variables indexed by a multiset is the monomial of its multiplicities. -/
private lemma prod_map_X {R σ : Type*} [CommSemiring R] [DecidableEq σ] (s : Multiset σ) :
    (s.map (X : σ → MvPolynomial σ R)).prod = monomial (Multiset.toFinsupp s) 1 := by
  induction s using Multiset.induction with
  | empty => simp
  | cons i s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, ih, X, monomial_mul, one_mul,
      ← Multiset.singleton_add, Multiset.toFinsupp_add, Multiset.toFinsupp_singleton]

/-- The monomial expansion of `h_n` in `r` variables: the sum of `z^β` over `|β| = n`. -/
private lemma hsymm_eq_sum (R : Type*) [CommSemiring R] (r n : ℕ) :
    hsymm (Fin r) R n = ∑ β ∈ Finset.Nat.antidiagonalTuple r n,
      monomial (Finsupp.equivFunOnFinite.symm β) 1 := by
  rw [hsymm]
  simp only [prod_map_X]
  refine Finset.sum_bij' (fun s _ j => s.1.count j)
    (fun β hβ => ⟨Finsupp.toMultiset (Finsupp.equivFunOnFinite.symm β), by
      rw [Finset.Nat.mem_antidiagonalTuple] at hβ
      rw [Finsupp.card_toMultiset, Finsupp.sum_fintype _ _ (fun _ => rfl)]
      simpa using hβ⟩) ?_ (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro s _
    rw [Finset.Nat.mem_antidiagonalTuple]
    simp
  · intro s _
    ext1
    simp [Multiset.ext]
  · intro β _
    funext j
    simp
  · intro s _
    refine congrArg (monomial · (1 : R)) ?_
    ext j
    simp [Multiset.toFinsupp_apply]

/-- The size of the shape `(a + d, a^{r-1})` is `a r + d`. -/
private lemma sum_hook {r : ℕ} (hr : 1 ≤ r) (a d : ℕ) : ∑ i, (hook r a d).1 i = a * r + d := by
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  simp [hook, Fin.sum_univ_succ]
  ring

/-- `(z₁ ⋯ zᵣ)^a` is the monomial with every exponent `a`. -/
private lemma prod_X_pow {R σ : Type*} [CommSemiring R] [Fintype σ] (a : ℕ) :
    (∏ i : σ, X i : MvPolynomial σ R) ^ a =
      monomial (Finsupp.equivFunOnFinite.symm fun _ => a) 1 := by
  rw [← Finset.prod_pow, Finset.prod_congr rfl fun i _ => X_pow_eq_monomial, ← monomial_sum_one,
    Finsupp.equivFunOnFinite_symm_eq_sum]

/-- Shifting by `a` is a bijection from the exponent vectors of total degree `d` onto those of
total degree `a r + d` with every entry at least `a`. -/
private lemma sum_filter_antidiagonalTuple_le {M : Type*} [AddCommMonoid M] (r a d : ℕ)
    (f : (Fin r → ℕ) → M) :
    ∑ α ∈ Finset.Nat.antidiagonalTuple r (a * r + d) with ∀ i, a ≤ α i, f α =
      ∑ β ∈ Finset.Nat.antidiagonalTuple r d, f (fun i => a + β i) := by
  symm
  refine Finset.sum_nbij' (fun β i => a + β i) (fun α i => α i - a) ?_ ?_ ?_ ?_ (fun _ _ => rfl)
  · intro β hβ
    simp only [Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple] at hβ ⊢
    exact ⟨by simp [Finset.sum_add_distrib, hβ, mul_comm], fun i => Nat.le_add_right _ _⟩
  · intro α hα
    simp only [Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple] at hα ⊢
    rw [Finset.sum_tsub_distrib _ fun i _ => hα.2 i, hα.1]
    simp [mul_comm]
  · intro β _
    simp
  · intro α hα
    simp only [Finset.mem_filter] at hα
    funext i
    have := hα.2 i
    simp only
    omega


/-- For `r ≥ 1`, the Schur polynomial of `(a + d, a^{r-1})` is
`(z₁ ⋯ zᵣ)^a · h_d(z₁, …, zᵣ)`. -/
@[lognarayana "lem_schur_hook_shape_eq"]
public theorem schurPolynomial_hook (R : Type*) [CommSemiring R] {r : ℕ} (hr : 1 ≤ r)
    (a d : ℕ) :
    (hook r a d).schurPolynomial R = (∏ i : Fin r, X i) ^ a * hsymm (Fin r) R d := by
  rw [schurPolynomial, sum_hook hr, Finset.sum_congr rfl (g := fun α =>
      if ∀ i, a ≤ α i then monomial (Finsupp.equivFunOnFinite.symm α) (1 : R) else 0)
      fun α hα => by
        simp only [kostkaNumber_hook hr, Finset.Nat.mem_antidiagonalTuple.1 hα, and_true]
        split_ifs <;> simp, ← Finset.sum_filter,
    sum_filter_antidiagonalTuple_le, prod_X_pow, hsymm_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [monomial_mul, one_mul]
  refine congrArg (monomial · (1 : R)) ?_
  ext
  simp

/-! ### The Narayana transform of a hook-shaped Schur polynomial -/

private lemma narayanaTransform_monomial_one {σ : Type*} (α : σ →₀ ℕ) :
    narayanaTransform σ (monomial α 1) = α.prod fun _ k => shiftedNarayanaPolynomial k := by
  rw [← congrFun (coe_basisMonomials σ ℝ) α, narayanaTransform, Module.Basis.constr_basis]

/-- For `r ≥ 1`, the Narayana transform of the Schur polynomial of the hook shape
`(a + d, a^{r-1})` is `∑_{b ∈ ℕ^r, |b| = d} ∏_i Ñ_{a + b_i}`. -/
@[lognarayana "lem_schur_transform_hook_shape"]
public theorem schurNarayanaTransform_hook {r : ℕ} (hr : 1 ≤ r) (a d : ℕ) :
    (hook r a d).schurNarayanaTransform =
      ∑ b ∈ Finset.Nat.antidiagonalTuple r d,
        ∏ i : Fin r, shiftedNarayanaPolynomial (a + b i) := by
  rw [schurNarayanaTransform, schurPolynomial_hook ℝ hr, hsymm_eq_sum, prod_X_pow, Finset.mul_sum,
    map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [monomial_mul, one_mul, narayanaTransform_monomial_one,
    Finsupp.prod_fintype _ _ fun _ => shiftedNarayanaPolynomial_zero]
  simp

end SchurHook

end PartitionAtMostParts

/-! ### The functional equation of the shifted Narayana generating series -/

section ShiftedGFEquation

open Polynomial

/-- The shifted Narayana generating series `V = shiftedNarayanaGenSeries` satisfies
`V = (1 + z V)(1 + x z V)` in `ℝ[x]⟦z⟧`. -/
@[lognarayana "lem_shifted_narayana_gf_equation"]
public theorem shiftedNarayanaGenSeries_eq_mul :
    shiftedNarayanaGenSeries =
      (1 + PowerSeries.X * shiftedNarayanaGenSeries) *
        (1 + PowerSeries.C (Polynomial.X : ℝ[X]) * PowerSeries.X * shiftedNarayanaGenSeries) := by
  set V := shiftedNarayanaGenSeries
  have hV : ∀ n, PowerSeries.coeff n V = shiftedNarayanaPolynomial n := fun n => by
    simp [V, shiftedNarayanaGenSeries]
  have hR : (1 + PowerSeries.X * V) *
      (1 + PowerSeries.C (Polynomial.X : Polynomial ℝ) * PowerSeries.X * V) =
      1 + PowerSeries.X * (PowerSeries.C (1 + Polynomial.X) * V +
        PowerSeries.X * (PowerSeries.C Polynomial.X * (V * V))) := by
    rw [map_add, map_one]; ring
  rw [hR]
  ext n
  rcases n with _ | _ | m
  · simp [hV, shiftedNarayanaPolynomial_zero]
  · rw [map_add, PowerSeries.coeff_succ_X_mul, map_add, PowerSeries.coeff_zero_X_mul,
      PowerSeries.coeff_C_mul, hV, hV, shiftedNarayanaPolynomial_zero,
      shiftedNarayanaPolynomial_one]
    simp
  · rw [map_add, PowerSeries.coeff_succ_X_mul, map_add, PowerSeries.coeff_succ_X_mul,
      PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul, hV, hV,
      shiftedNarayanaPolynomial_add_two]
    simp [hV]

end ShiftedGFEquation

/-! ### The one-row shape -/

namespace PartitionAtMostParts

section OneRow

open Polynomial

/-- From the cited location of the zeros of Jacobi polynomials (all `d` zeros of `P^{(α,β)}_d`
are simple and lie in `(-1, 1)`): the roots of `P^{(α,β)}_d` are `t₁ < ⋯ < t_d` in `(-1, 1)`,
each once. -/
public theorem _root_.Polynomial.JacobiRootsSimpleInIoo.exists_strictMono
    (hJ : Polynomial.JacobiRootsSimpleInIoo) (α β d : ℕ) :
    ∃ t : Fin d → ℝ, StrictMono t ∧ (∀ i, t i ∈ Set.Ioo (-1 : ℝ) 1) ∧
      (jacobi α β d).roots = Finset.univ.val.map t := by
  obtain ⟨hcard, hnd, hIoo⟩ := hJ α β d
  set s := (jacobi α β d).roots
  have hF : s.toFinset.card = d := by rw [Multiset.toFinset_card_of_nodup hnd, hcard]
  refine ⟨s.toFinset.orderEmbOfFin hF, (s.toFinset.orderEmbOfFin hF).strictMono,
    fun i => hIoo _ (Multiset.mem_toFinset.1 (s.toFinset.orderEmbOfFin_mem hF i)), ?_⟩
  have := congrArg Finset.val (Finset.map_orderEmbOfFin_univ s.toFinset hF)
  rw [Finset.map_val, Multiset.toFinset_val, hnd.dedup] at this
  exact this.symm

/-- The `n`-th coefficient of `f ^ k` is the sum over `k`-tuples summing to `n` of the
products of coefficients. -/
private lemma coeff_pow_eq_sum_antidiagonalTuple {R : Type*} [CommSemiring R]
    (f : PowerSeries R) (k n : ℕ) :
    PowerSeries.coeff n (f ^ k) =
      ∑ b ∈ Finset.Nat.antidiagonalTuple k n, ∏ i : Fin k, PowerSeries.coeff (b i) f := by
  classical
  rw [← Finset.piAntidiag_univ_fin_eq_antidiagonalTuple, ← Fin.prod_const, PowerSeries.coeff_prod,
    Finset.finsuppAntidiag, Finset.sum_map]
  exact Finset.sum_attach _ (fun g : Fin k → ℕ => ∏ i, PowerSeries.coeff (g i) f)

/-- The coefficients of `(1 + a X) ^ n`. -/
private lemma coeff_one_add_C_mul_X_pow {R : Type*} [CommSemiring R] (a : R) (n k : ℕ) :
    ((1 + C a * X) ^ n).coeff k = a ^ k * (n.choose k : R) := by
  rw [add_comm, add_pow, finsetSum_coeff]
  simp only [one_pow, mul_one, mul_pow, ← C_pow, mul_right_comm _ (X ^ _), ← C_eq_natCast,
    ← C_mul, coeff_C_mul_X_pow, Finset.sum_ite_eq, Finset.mem_range]
  split_ifs with h
  · rfl
  · simp [Nat.choose_eq_zero_of_lt (by omega : n < k)]

/-- The coefficients of `((1 + X)(1 + a X)) ^ n`: `[X^d]` is
`∑_{j ≤ d} C(n, j) C(n, d - j) a^j`. -/
private lemma coeff_one_add_X_mul_one_add_C_mul_X_pow {R : Type*} [CommSemiring R] (a : R)
    (n d : ℕ) :
    (((1 + X) * (1 + C a * X)) ^ n).coeff d =
      ∑ j ∈ Finset.range (d + 1), ((n.choose j * n.choose (d - j) : ℕ) : R) * a ^ j := by
  rw [mul_pow, coeff_mul, ← Finset.Nat.sum_antidiagonal_swap,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Prod.swap_prod_mk, coeff_one_add_X_pow, coeff_one_add_C_mul_X_pow]
  push_cast
  ring

/-- With `W = z V`, the coefficient `[z^{d+r}] W^r` is the Narayana transform of the one-row
Schur polynomial `s_{(d)}` in `r` variables (the hook formula at `a = 0`). -/
private lemma coeff_X_mul_shiftedNarayanaGenSeries_pow {r : ℕ} (hr : 1 ≤ r) (d : ℕ) :
    PowerSeries.coeff (d + r) ((PowerSeries.X * shiftedNarayanaGenSeries) ^ r) =
      (row r d).schurNarayanaTransform := by
  rw [mul_pow, PowerSeries.coeff_X_pow_mul', if_pos (by omega), Nat.add_sub_cancel,
    coeff_pow_eq_sum_antidiagonalTuple, show row r d = hook r 0 d from rfl,
    schurNarayanaTransform_hook hr 0 d]
  simp [shiftedNarayanaGenSeries, PowerSeries.coeff_mk]

/-- Lagrange inversion for `W = z V`, which satisfies `W = z (1 + W)(1 + x W)`:
`(r + d) Φ[s_{(d)}] = r ∑_{j ≤ d} C(r+d, j) C(r+d, d-j) x^j`. -/
private lemma C_add_mul_schurNarayanaTransform_row
    {r : ℕ} (hr : 1 ≤ r)
    (d : ℕ) :
    C ((r : ℝ) + d) * (row r d).schurNarayanaTransform =
      C (r : ℝ) * ∑ j ∈ Finset.range (d + 1),
        C (((r + d).choose j * (r + d).choose (d - j) : ℕ) : ℝ) * X ^ j := by
  have key := PowerSeries.lagrangeInversion ℝ[X] ((1 + X) * (1 + C X * X))
    (PowerSeries.X * shiftedNarayanaGenSeries) (by simp) ?_ r (d + r) hr (by omega)
  · rw [coeff_X_mul_shiftedNarayanaGenSeries_pow hr, Nat.add_sub_cancel,
      coeff_one_add_X_mul_one_add_C_mul_X_pow, add_comm d] at key
    simpa [map_natCast] using key
  · simp only [map_mul, map_add, map_one, aeval_X, aeval_C, PowerSeries.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply]
    conv_lhs => rw [shiftedNarayanaGenSeries_eq_mul]
    ring

/-- For `r ≥ 1`, the Narayana transform of the one-row Schur polynomial `s_{(d)}` in `r`
variables is `r / (r + d) * ∑_{j=0}^{d} C(r+d, j) C(r+d, d-j) x^j`. -/
@[lognarayana "lem_schur_one_row_formula"]
public theorem schurNarayanaTransform_row
    {r : ℕ}
    (hr : 1 ≤ r) (d : ℕ) :
    (row r d).schurNarayanaTransform =
      C ((r : ℝ) / (r + d)) *
        ∑ j ∈ Finset.range (d + 1),
          C (((r + d).choose j * (r + d).choose (d - j) : ℕ) : ℝ) * X ^ j := by
  rw [div_eq_inv_mul, C_mul, mul_assoc, ← C_add_mul_schurNarayanaTransform_row hr d,
    ← mul_assoc, ← C_mul, inv_mul_cancel₀ (by positivity), C_1, one_mul]

/-- Clearing the denominator of the Möbius substitution `t = (1+x)/(1-x)` in the Jacobi
polynomial: `(1-x)^d P^{(α,β)}_d((1+x)/(1-x)) = ∑_ℓ C(d+α, d-ℓ) C(d+β, ℓ) x^ℓ`. -/
private lemma one_sub_pow_mul_eval_jacobi (α β d : ℕ) {x : ℝ} (hx : x ≠ 1) :
    (1 - x) ^ d * (jacobi α β d).eval ((1 + x) / (1 - x)) =
      ∑ ℓ ∈ Finset.range (d + 1),
        (((d + α).choose (d - ℓ) * (d + β).choose ℓ : ℕ) : ℝ) * x ^ ℓ := by
  have h1 : (1 : ℝ) - x ≠ 0 := sub_ne_zero.mpr hx.symm
  simp only [jacobi, eval_finsetSum, eval_mul, eval_pow, eval_C, eval_sub, eval_add, eval_X,
    eval_one, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ℓ hℓ => ?_
  have hℓd : ℓ ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hℓ)
  have ha : (2 : ℝ)⁻¹ * ((1 + x) / (1 - x) - 1) = x / (1 - x) := by field_simp; ring
  have hb : (2 : ℝ)⁻¹ * ((1 + x) / (1 - x) + 1) = 1 / (1 - x) := by field_simp; ring
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hℓd
  rw [ha, hb, Nat.add_sub_cancel_left, pow_add, div_pow, div_pow, one_pow]
  field_simp

/-- For `r ≥ 1` and every real `x ≠ 1`,
`Φ_{(d),r}(x) = r/(r+d) · (1-x)^d · P^{(r,r)}_d((1+x)/(1-x))`. -/
@[lognarayana "lem_jacobi_one_row"]
public theorem eval_schurNarayanaTransform_row
    {r : ℕ} (hr : 1 ≤ r) (d : ℕ) {x : ℝ} (hx : x ≠ 1) :
    (row r d).schurNarayanaTransform.eval x =
      (r : ℝ) / (r + d) * (1 - x) ^ d *
        (Polynomial.jacobi r r d).eval ((1 + x) / (1 - x)) := by
  rw [schurNarayanaTransform_row hr d, mul_assoc, one_sub_pow_mul_eval_jacobi _ _ _ hx,
    add_comm d r]
  simp only [eval_mul, eval_C, eval_finsetSum, eval_pow, eval_X, Nat.mul_comm]

/-- A nonzero polynomial of degree at most `d` with `d` distinct negative roots has only negative
roots: those `d` roots are all of them. -/
private lemma hasOnlyNegativeRoots_of_injective {K : Type*} [Field K] [LT K] {f : K[X]}
    (hf : f ≠ 0) {d : ℕ} (hdeg : f.natDegree ≤ d) {x : Fin d → K} (hx : Function.Injective x)
    (hroot : ∀ i, f.IsRoot (x i)) (hneg : ∀ i, x i < 0) : f.HasOnlyNegativeRoots := by
  have hnd : (Finset.univ.val.map x).Nodup := Finset.univ.nodup.map hx
  have hcard : Multiset.card (Finset.univ.val.map x) = d := by simp
  have heq : Finset.univ.val.map x = f.roots :=
    Multiset.eq_of_le_of_card_le
      ((Multiset.le_iff_subset hnd).mpr fun y hy => by
        obtain ⟨i, -, rfl⟩ := Multiset.mem_map.mp hy
        exact (mem_roots hf).mpr (hroot i))
      ((card_roots' f).trans (hdeg.trans hcard.ge))
  refine ⟨?_, fun y hy => ?_⟩
  · rw [splits_iff_card_roots, ← heq, hcard]
    exact le_antisymm (hcard ▸ heq ▸ card_roots' f) hdeg
  · obtain ⟨i, -, rfl⟩ := Multiset.mem_map.mp (heq ▸ hy)
    exact hneg i

private lemma eval_one_jacobi (α β d : ℕ) : (jacobi α β d).eval 1 = ((d + α).choose d : ℝ) := by
  rw [jacobi, eval_finsetSum, Finset.sum_eq_single 0 (fun b _ hb => by simp [zero_pow hb])
    (by simp)]
  norm_num


/-- For `r ≥ 1` and every `d`, the Narayana transform `Φ_{(d),r}` of the one-row shape `(d)`
has only negative real zeros. -/
@[lognarayana "thm_schur_one_row_neg_real_rooted"]
public theorem hasOnlyNegativeRoots_schurNarayanaTransform_row
    (hJ : Polynomial.JacobiRootsSimpleInIoo)
    {r : ℕ} (hr : 1 ≤ r) (d : ℕ) :
    (row r d).schurNarayanaTransform.HasOnlyNegativeRoots := by
  obtain ⟨t, ht, htI, hroots⟩ := hJ.exists_strictMono r r d
  have hpos : ∀ i, 0 < t i + 1 := fun i => by linarith [(htI i).1]
  have hneg : ∀ i, (t i - 1) / (t i + 1) < 0 := fun i =>
    div_neg_of_neg_of_pos (by linarith [(htI i).2]) (hpos i)
  refine hasOnlyNegativeRoots_of_injective (fun h => ?_) ?_ (x := fun i => (t i - 1) / (t i + 1))
    (fun i j hij => ht.injective ?_) (fun i => ?_) hneg
  · -- `Φ(0) = r/(r+d)·C(d+r,d) ≠ 0`
    have := eval_schurNarayanaTransform_row hr d zero_ne_one
    rw [h, eval_zero, add_zero, sub_zero, div_one, one_pow, mul_one, eval_one_jacobi] at this
    have hr' : (0 : ℝ) < r := by exact_mod_cast hr
    refine (mul_pos (div_pos hr' (by positivity)) ?_).ne this
    exact_mod_cast Nat.choose_pos (Nat.le_add_right d r)
  · rw [schurNarayanaTransform_row hr d]
    refine (natDegree_C_mul_le _ _).trans <| natDegree_sum_le_of_forall_le _ _ fun j hj => ?_
    exact (natDegree_C_mul_le _ _).trans (by simpa [Nat.lt_succ_iff] using hj)
  · rw [div_eq_div_iff (hpos i).ne' (hpos j).ne'] at hij
    linarith
  · have hPt : (jacobi r r d).IsRoot (t i) :=
      isRoot_of_mem_roots (hroots ▸ Multiset.mem_map_of_mem _ (Finset.mem_univ_val _))
    have hx1 : (t i - 1) / (t i + 1) ≠ 1 := by linarith [hneg i]
    have hsub : (1 + (t i - 1) / (t i + 1)) / (1 - (t i - 1) / (t i + 1)) = t i := by
      field_simp [(hpos i).ne']
      ring
    simp only [IsRoot, eval_schurNarayanaTransform_row hr d hx1, hsub, hPt.eq_zero, mul_zero]

end OneRow

end PartitionAtMostParts

/-! ### Lattice-point sums for hook shapes -/

namespace PartitionAtMostParts

section LatticePoints

open Polynomial Pointwise

/-- The integer vectors `q ∈ ℤ^r` with `c ≤ qᵢ` for all `i` and `∑ qᵢ = cr + d` are exactly
the vectors `(c + bᵢ)ᵢ` with `b ∈ ℕ^r`, `|b| = d`. -/
private lemma setOf_le_sum_eq_eq_image_antidiagonalTuple (r c d : ℕ) :
    {q : Fin r → ℤ | (∀ i, (c : ℤ) ≤ q i) ∧ ∑ i, q i = c * r + d} =
      (fun b : Fin r → ℕ => fun i => ((c + b i : ℕ) : ℤ)) ''
        ↑(Finset.Nat.antidiagonalTuple r d) := by
  ext q
  simp only [Set.mem_ofPred_eq, Set.mem_image, Finset.mem_coe,
    Finset.Nat.mem_antidiagonalTuple]
  constructor
  · rintro ⟨hq, hs⟩
    have hn (i) : ((q i - c).toNat : ℤ) = q i - c := Int.toNat_of_nonneg (by linarith [hq i])
    refine ⟨fun i => (q i - c).toNat, ?_, funext fun i => by push_cast; rw [hn]; ring⟩
    have : ((∑ i, (q i - c).toNat : ℕ) : ℤ) = d := by
      push_cast [hn]
      rw [Finset.sum_sub_distrib, hs]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Int.nsmul_eq_mul]
      ring
    exact_mod_cast this
  · rintro ⟨b, hb, rfl⟩
    refine ⟨fun i => by simp, ?_⟩
    have : ∑ i, (c + b i) = c * r + d := by simp [Finset.sum_add_distrib, hb, mul_comm]
    beta_reduce
    exact_mod_cast this

/-- The translated dilated simplex `(a+1)𝟏 + dΔ_{[r]}`, written as a translate of a pointwise
dilation, is the image of `Δ_{[r]}` under `y ↦ (a+1)𝟏 + d y`. -/
private lemma image_add_smul_coordSimplex (r a d : ℕ) :
    (fun v : Fin r → ℝ => (fun _ => (a : ℝ) + 1) + v) ''
        ((d : ℝ) • coordSimplex ℝ (Set.univ : Set (Fin r))) =
      (fun y : Fin r → ℝ => (((a + 1 : ℕ) : ℤ) : ℝ) • (1 : Fin r → ℝ) + (d : ℝ) • y) ''
        coordSimplex ℝ (Set.univ : Set (Fin r)) := by
  rw [← Set.image_smul, Set.image_image]
  congr 1
  funext y
  ext i
  simp

/-- The lattice points of `(a+1)𝟏 + dΔ_{[r]}` are the vectors `(a + 1 + bᵢ)ᵢ` with
`b ∈ ℕ^r`, `|b| = d`. -/
private lemma latticePoints_eq {r : ℕ} (hr : 1 ≤ r) (a d : ℕ) :
    ((fun v : Fin r → ℝ => (fun _ => (a : ℝ) + 1) + v) ''
          ((d : ℝ) • coordSimplex ℝ (Set.univ : Set (Fin r)))).latticePoints =
      (fun b : Fin r → ℕ => fun i => ((a + 1 + b i : ℕ) : ℝ)) ''
        ↑(Finset.Nat.antidiagonalTuple r d) := by
  rw [image_add_smul_coordSimplex, latticePoints_image_smul_coordSimplex_univ hr,
    setOf_le_sum_eq_eq_image_antidiagonalTuple, Set.image_image]
  simp only [Int.cast_natCast]

/-- For `r ≥ 1`, `x^r Φ_{(a+d, a^{r-1}), r}(x)` is the sum over the lattice points `q` of the
dilated, translated simplex `(a+1)𝟏 + dΔ_{[r]}` of the products `∏ᵢ N_{qᵢ}(x)`. -/
@[lognarayana "lem_schur_hook_narayana_sum"]
public theorem finsum_latticePoints_prod_narayanaPolynomial_hook {r : ℕ} (hr : 1 ≤ r)
    (a d : ℕ) :
    X ^ r * (hook r a d).schurNarayanaTransform =
      ∑ᶠ q ∈ ((fun v : Fin r → ℝ => (fun _ => (a : ℝ) + 1) + v) ''
          ((d : ℝ) • coordSimplex ℝ (Set.univ : Set (Fin r)))).latticePoints,
        ∏ i, _root_.narayanaPolynomial ⌊q i⌋₊ := by
  rw [latticePoints_eq hr a d, finsum_mem_image, finsum_mem_coe_finset,
    schurNarayanaTransform_hook hr, Finset.mul_sum]
  · refine Finset.sum_congr rfl fun b _ => ?_
    simp only [Nat.floor_natCast, add_right_comm a 1, narayanaPolynomial_succ_eq_X_mul,
      Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  · exact fun b _ c _ h => funext fun i => by simpa using congrFun h i

/-! ### Restricted noncrossing refinements and real-rootedness -/

/-- The integer compositions with parts at least `b` are the casts of the natural ones. -/
private lemma setOf_int_eq_image (r b n : ℕ) :
    {q : Fin r → ℤ | (∀ i, ((b : ℕ) : ℤ) ≤ q i) ∧ ∑ i, q i = n} =
      (fun p : Fin r → ℕ => fun i => (p i : ℤ)) ''
        ↑((Finset.Nat.antidiagonalTuple r n).filter (fun p => ∀ i, b ≤ p i)) := by
  ext q
  simp only [Set.mem_ofPred_eq, Set.mem_image, Finset.coe_filter, Finset.Nat.mem_antidiagonalTuple]
  constructor
  · rintro ⟨hb, hs⟩
    have h0 : ∀ i, 0 ≤ q i := fun i => (Int.natCast_nonneg b).trans (hb i)
    refine ⟨fun i => (q i).toNat, ⟨?_, fun i => by simpa [← Int.ofNat_le, h0 i] using hb i⟩,
      funext fun i => Int.toNat_of_nonneg (h0 i)⟩
    exact_mod_cast (by push_cast [Int.toNat_of_nonneg (h0 _)]; exact hs :
      ((∑ i, (q i).toNat : ℕ) : ℤ) = n)
  · rintro ⟨p, ⟨hs, hb⟩, rfl⟩
    exact ⟨fun i => Int.ofNat_le.2 (hb i), by rw [← hs]; push_cast; rfl⟩

/-- A sum over the lattice points of `(a+1)𝟏 + dΔ_{[r]}` of `∏ᵢ f ⌊qᵢ⌋₊` is the sum of
`∏ᵢ f pᵢ` over the compositions `p` of `r(a+1) + d` into `r` parts each at least `a + 1`. -/
private lemma finsum_latticePoints_eq_sum_antidiagonalTuple {M : Type*} [CommSemiring M]
    {r : ℕ} (hr : 1 ≤ r) (a d : ℕ) (f : ℕ → M) :
    ∑ᶠ q ∈ ((fun v : Fin r → ℝ => (fun _ => (a : ℝ) + 1) + v) ''
          ((d : ℝ) • coordSimplex ℝ (Set.univ : Set (Fin r)))).latticePoints,
        ∏ i, f ⌊q i⌋₊ =
      ∑ p ∈ (Finset.Nat.antidiagonalTuple r (r * (a + 1) + d)).filter (fun p => ∀ i, a + 1 ≤ p i),
        ∏ i, f (p i) := by
  have hsum : (((a + 1 : ℕ) : ℤ) * r + d) = ((r * (a + 1) + d : ℕ) : ℤ) := by push_cast; ring
  rw [image_add_smul_coordSimplex, latticePoints_image_smul_coordSimplex_univ hr, hsum,
    setOf_int_eq_image r (a + 1), Set.image_image,
    finsum_mem_image (g := fun p : Fin r → ℕ => fun i => (((p i : ℤ)) : ℝ))
      (fun p₁ _ p₂ _ h => funext fun i => by simpa using congrFun h i), finsum_mem_coe_finset]
  simp

end LatticePoints

section RestrictedNC


open Finset Polynomial

/-- For `r ≥ 1` and `a, d ≥ 0`, with `n = r(a+1) + d`:
`R^{(a+1)}_{n,r}(x) = n! / (r! (ra+d+1)!) · x^r · Φ_{(a+d,a^{r-1}),r}(x)`, given Kreweras'
block-size count. -/
@[lognarayana "lem_restricted_nc_schur"]
public theorem restrictedNoncrossingRefinementPoly_eq_schurNarayanaTransform_hook
    (hKr : Finpartition.KrewerasBlockSizeCount)
    {r : ℕ} (hr : 1 ≤ r) (a d : ℕ) :
    restrictedNoncrossingRefinementPoly ℝ (Icc 1 (r * (a + 1) + d)) (a + 1) r =
      C (((r * (a + 1) + d).factorial : ℝ) / (r.factorial * (r * a + d + 1).factorial)) *
        X ^ r * (hook r a d).schurNarayanaTransform := by
  rw [← restrictedNoncrossingDeformedNarayanaPoly_one hKr,
    restrictedNoncrossingDeformedNarayanaPoly_eq_sum_antidiagonalTuple hKr _ r (a + 1)
      (by omega) 1, show r * (a + 1) + d - r + 1 = r * a + d + 1 by rw [Nat.mul_succ]; omega,
    mul_assoc, finsum_latticePoints_prod_narayanaPolynomial_hook hr a d,
    finsum_latticePoints_eq_sum_antidiagonalTuple hr]
  refine congrArg _ (Finset.sum_congr rfl fun p hp => Finset.prod_congr rfl fun i _ => ?_)
  exact deformedNarayanaPolynomial_one (by have := (mem_filter.1 hp).2 i; omega)

/-- If `C c * X ^ r * p` splits with `c ≠ 0`, then so does `p`. -/
private lemma splits_of_splits_C_mul_X_pow_mul {K : Type*} [Field K] {c : K} (hc : c ≠ 0)
    {r : ℕ} {p : K[X]} (h : (C c * X ^ r * p).Splits) : p.Splits := by
  rcases eq_or_ne p 0 with rfl | hp
  · exact Splits.zero
  exact h.of_dvd (by simp [hc, hp]) (dvd_mul_left _ _)

/-- For `r ≥ 1` and `d ∈ ℕ`, the polynomial `Φ_{(d+1,1^{r-1}),r}(x)` is real-rooted. -/
@[lognarayana "thm_schur_hook_one_real_rooted"]
public theorem splits_schurNarayanaTransform_hook_one
    (hKr : Finpartition.KrewerasBlockSizeCount)
    (hD : ∀ σ : Type, IsRealStablePDerivClosed σ)
    (hS : ∀ (σ : Type) [DecidableEq σ], IsRealStableSpecializeClosed σ)
    {r : ℕ} (hr : 1 ≤ r) (d : ℕ) :
    (hook r 1 d).schurNarayanaTransform.Splits := by
  have h := splits_restrictedNoncrossingRefinementPoly_two hKr hD hS (r * (1 + 1) + d) r
  rw [restrictedNoncrossingRefinementPoly_eq_schurNarayanaTransform_hook hKr hr 1 d] at h
  exact splits_of_splits_C_mul_X_pow_mul (by positivity) h

end RestrictedNC

/-! ### Log-concavity -/

section LogConcave

open Polynomial Pointwise

/-- If `X ^ r * f` is log-concave, so is `f`. -/
private lemma isLogConcave_of_X_pow_mul {f : ℝ[X]} (r : ℕ) (h : (X ^ r * f).IsLogConcave) :
    f.IsLogConcave := by
  obtain ⟨h₀, h₁⟩ := h
  refine ⟨fun j => ?_, fun j => ?_⟩
  · simpa [coeff_X_pow_mul] using h₀ (j + r)
  · simpa only [show j + r + 2 = j + 2 + r by omega, show j + r + 1 = j + 1 + r by omega,
      coeff_X_pow_mul] using h₁ (j + r)

/-- Points of the standard simplex have nonnegative coordinates. -/
private lemma nonneg_of_mem_coordSimplex {r : ℕ} {y : Fin r → ℝ}
    (hy : y ∈ coordSimplex ℝ (Set.univ : Set (Fin r))) : 0 ≤ y := by
  refine convexHull_min ?_ (convex_Ici (0 : Fin r → ℝ)) hy
  rintro _ ⟨j, -, rfl⟩
  exact Pi.single_nonneg.2 zero_le_one

/-- Every coordinate of a point of `(a+1)𝟏 + dΔ_{[r]}` has floor at least `1`. -/
private lemma one_le_floor_of_mem_image_add_smul_coordSimplex {r a d : ℕ} {q : Fin r → ℝ}
    (hq : q ∈ (fun v : Fin r → ℝ => (fun _ => (a : ℝ) + 1) + v) ''
        ((d : ℝ) • coordSimplex ℝ (Set.univ : Set (Fin r)))) (i : Fin r) :
    1 ≤ ⌊q i⌋₊ := by
  rw [image_add_smul_coordSimplex] at hq
  obtain ⟨y, hy, rfl⟩ := hq
  apply Nat.le_floor
  have := mul_nonneg (Nat.cast_nonneg d : (0 : ℝ) ≤ d) (nonneg_of_mem_coordSimplex hy i)
  simp only [Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
  push_cast
  linarith [(Nat.cast_nonneg a : (0 : ℝ) ≤ a)]


/-- For `a d : ℕ` and `r ≥ 1`, the Narayana transform `Φ_{(a+d,a^{r-1}),r}` of the hook-shaped
Schur polynomial `s_{(a+d,a^{r-1})}(z₁, …, zᵣ)` is log-concave. -/
@[lognarayana "thm_schur_hook_shape_lc"]
public theorem isLogConcave_schurNarayanaTransform_hook
    (hreal : IntegralBinaryNestohedronRealization)
    (hfert : RefinedFertilityFormula)
    (hsub : ∀ (σ τ : Type) [Fintype σ] [Fintype τ],
      MvPolynomial.LorentzianNonnegLinearSubstitution σ τ)
    (hder : ∀ (σ : Type) [Fintype σ], MvPolynomial.LorentzianNonnegDerivative σ)
    (hmul : ∀ (σ : Type) [Fintype σ], MvPolynomial.LorentzianMul σ)
    (hBH : ∀ (σ : Type) [Fintype σ],
      MvPolynomial.NormalizedSupportPolyLorentzianOfMConvex σ)
    (hsym : ∀ (σ τ : Type) [Fintype σ] [Fintype τ],
      MvPolynomial.BrandenHuhSymbolTheorem σ τ)
    {r : ℕ} (hr : 1 ≤ r) (a d : ℕ) :
    (hook r a d).schurNarayanaTransform.IsLogConcave := by
  apply isLogConcave_of_X_pow_mul r
  rw [finsum_latticePoints_prod_narayanaPolynomial_hook hr a d,
    finsum_mem_congr rfl fun q hq => Finset.prod_congr rfl fun i _ =>
      (deformedNarayanaPolynomial_one
        (one_le_floor_of_mem_image_add_smul_coordSimplex hq.1 i)).symm,
    image_add_smul_coordSimplex]
  exact isLogConcave_finsum_latticePoints_prod_deformedNarayanaPolynomial hreal hfert
    hsub hder hmul hBH hsym zero_le_one one_le_two hr
    (isIntegralBinaryNestohedron_image_smul_coordSimplex_univ hr (by omega) d)

/-- A two-row shape `(μ₁, μ₂)` is the hook `(μ₂ + (μ₁ - μ₂), μ₂)`. -/
private lemma eq_hook_two (μ : PartitionAtMostParts 2) :
    μ = hook 2 (μ.1 1) (μ.1 0 - μ.1 1) := by
  have h : μ.1 1 ≤ μ.1 0 := μ.2 (by decide)
  apply Subtype.ext
  funext i
  fin_cases i <;> simp [hook]
  all_goals omega


/-- For every partition `μ = (μ₁, μ₂)` with at most two parts, the Narayana transform `Φ_{μ,2}`
of the Schur polynomial `s_μ(z₁, z₂)` is log-concave. -/
@[lognarayana "thm_schur_two_rows_lc"]
public theorem isLogConcave_schurNarayanaTransform_two
    (hreal : IntegralBinaryNestohedronRealization)
    (hfert : RefinedFertilityFormula)
    (hsub : ∀ (σ τ : Type) [Fintype σ] [Fintype τ],
      MvPolynomial.LorentzianNonnegLinearSubstitution σ τ)
    (hder : ∀ (σ : Type) [Fintype σ], MvPolynomial.LorentzianNonnegDerivative σ)
    (hmul : ∀ (σ : Type) [Fintype σ], MvPolynomial.LorentzianMul σ)
    (hBH : ∀ (σ : Type) [Fintype σ],
      MvPolynomial.NormalizedSupportPolyLorentzianOfMConvex σ)
    (hsym : ∀ (σ τ : Type) [Fintype σ] [Fintype τ],
      MvPolynomial.BrandenHuhSymbolTheorem σ τ)
    (μ : PartitionAtMostParts 2) :
    μ.schurNarayanaTransform.IsLogConcave := by
  rw [eq_hook_two μ]
  exact isLogConcave_schurNarayanaTransform_hook hreal hfert hsub hder hmul hBH hsym
    (by norm_num) _ _

end LogConcave

end PartitionAtMostParts
