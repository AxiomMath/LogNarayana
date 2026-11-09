/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib
public import LogNarayana.Attr
public import LogNarayana.Nestohedron.Fertilitope.Defs
public import LogNarayana.StackSorting.FiberPolynomials.Defs
public import LogNarayana.Narayana.Polynomials.Defs
public import LogNarayana.Polynomial.LogConcave.Defs
public import LogNarayana.StackSorting.ValidHookConfigurations.Defs
public import LogNarayana.Polynomial.LogConcave.Basic
public import LogNarayana.StackSorting.ValidHookConfigurations.Basic
public import LogNarayana.Nestohedron.Fertilitope.Basic
public import LogNarayana.StackSorting.FiberMatroid.Basic
public import LogNarayana.Lorentzian.BrandenHuh.Basic
public import LogNarayana.Lorentzian.Symbol.Basic

/-!
# Narayana sums on integral binary nestohedra

An integral binary nestohedron `P ⊆ ℝ^r` is a nonempty polytope (a Minkowski sum of positive
multiples of nonempty coordinate simplices) whose vertices have integer coordinates. Since a
nonempty compact convex set has an extreme point, `P ∩ ℤ^r` is nonempty; reading the coordinate
sum off such a lattice point shows that `P` lies in a hyperplane `∑_i p_i = S` with `S ∈ ℤ_{≥0}`.

For `r ≥ 1` and such `P` and `S`, the Narayana sum `∑_{q ∈ ℤ_{≥0}^r ∩ P} ∏_{i=1}^r N_{q_i}(x)`
is ultra-log-concave of order `S + r - 1`: realizing `P ∩ ℤ^r` as the valid compositions of a
permutation `π ∈ S_n`, the refined fertility formula identifies the sum with `x · D_π`, where
`D_π` is the fiber descent polynomial, which is ultra-log-concave of order `n - 1`.

## Main results

* `IsIntegralBinaryNestohedron.latticePoints_nonempty`: an integral binary nestohedron in
  `ℝ^r` has a lattice point.
* `exists_nat_sum_eq_of_isIntegralBinaryNestohedron`: the coordinate sum is a constant
  `S : ℕ` on an integral binary nestohedron.
* `isUltraLogConcave_finsum_prod_narayanaPolynomial`: the Narayana sum over `ℤ_{≥0}^r ∩ P` is
  ultra-log-concave of order `S + r - 1` (Eq. (1.4)).

## Implementation notes

The paper assumes `r ≥ 1` throughout; the first two results hold without it (for `r = 0`,
`P = {0}`), so that hypothesis is dropped there. The level `S ∈ ℤ_{≥0}` is taken in `ℕ` and
cast to `ℝ`. The index set `ℤ_{≥0}^r ∩ P` is the set of `q : Fin r → ℕ` whose coordinatewise
cast lies in `P`, and the sum is the finite sum `∑ᶠ` over it. The cited results the main theorem
rests on are explicit hypotheses: Defant's realization of integral binary nestohedra by valid
compositions (`IntegralBinaryNestohedronRealization`), Defant's refined fertility formula
(`RefinedFertilityFormula`), and the Brändén–Huh results on nonnegative linear substitutions
(`MvPolynomial.LorentzianNonnegLinearSubstitution`) and on normalized support polynomials of
M-convex sets (`MvPolynomial.NormalizedSupportPolyLorentzianOfMConvex`).

## References

* [LogNarayana], Eq. (1.4) and the section on fertilitopes and binary nestohedra.
-/

open Polynomial

/-! ### Lattice points and the coordinate sum -/

section LatticePoint

open scoped Pointwise

variable {ι : Type*} [DecidableEq ι]

/-- The coordinate simplex on a finite set of coordinates is compact. -/
private lemma isCompact_coordSimplex {J : Set ι} (hJ : J.Finite) :
    IsCompact (coordSimplex ℝ J) :=
  (hJ.image _).isCompact_convexHull (𝕜 := ℝ)

/-- The coordinate simplex on a nonempty set of coordinates is nonempty. -/
private lemma coordSimplex_nonempty {J : Set ι} (hJ : J.Nonempty) :
    (coordSimplex ℝ J).Nonempty :=
  convexHull_nonempty_iff.2 (hJ.image _)

/-- A nestohedron whose building set consists of nonempty sets is a nonempty compact set,
as a finite Minkowski sum of nonempty compact dilated simplices. -/
private lemma isCompact_nestohedron_and_nonempty {𝓑 : Finset (Finset ι)}
    (h𝓑 : ∀ J ∈ 𝓑, J.Nonempty) (c : Finset ι → ℝ) :
    IsCompact (nestohedron ℝ 𝓑 c) ∧ (nestohedron ℝ 𝓑 c).Nonempty :=
  Finset.sum_induction _ (fun S : Set (ι → ℝ) => IsCompact S ∧ S.Nonempty)
    (fun _ _ hA hB => ⟨hA.1.add hB.1, hA.2.add hB.2⟩)
    ⟨isCompact_singleton, Set.singleton_nonempty _⟩ fun J hJ =>
      ⟨(isCompact_coordSimplex J.finite_toSet).smul _,
        (coordSimplex_nonempty (Finset.coe_nonempty.2 (h𝓑 J hJ))).smul_set⟩

end LatticePoint

/-- An integral binary nestohedron `P ⊆ ℝ^r` contains a lattice point:
`P ∩ ℤ^r ≠ ∅`. -/
@[lognarayana "lem_nestohedron_lattice_point_exists"]
public theorem IsIntegralBinaryNestohedron.latticePoints_nonempty {r : ℕ}
    {P : Set (Fin r → ℝ)} (hP : IsIntegralBinaryNestohedron ℝ P) :
    P.latticePoints.Nonempty := by
  obtain ⟨⟨𝓑, h𝓑, c, -, rfl⟩, hext⟩ := hP
  have key := isCompact_nestohedron_and_nonempty (𝓑 := 𝓑) (fun J hJ => by
    obtain ⟨a, b, hab, rfl⟩ := h𝓑.exists_eq_Icc J hJ
    exact Finset.nonempty_Icc.2 hab) c
  obtain ⟨x, hx⟩ := key.1.extremePoints_nonempty key.2
  exact ⟨x, hext hx⟩

/-- The coordinate sum is constant, equal to a nonnegative integer `S`, on an integral binary
nestohedron `P ⊆ ℝ^r`. -/
@[lognarayana "lem_nestohedron_coordinate_sum_nat"]
public theorem exists_nat_sum_eq_of_isIntegralBinaryNestohedron {r : ℕ} {P : Set (Fin r → ℝ)}
    (hP : IsIntegralBinaryNestohedron ℝ P) : ∃ S : ℕ, ∀ p ∈ P, ∑ i, p i = (S : ℝ) := by
  obtain ⟨q, hqP, hqZ⟩ := IsIntegralBinaryNestohedron.latticePoints_nonempty hP
  obtain ⟨⟨𝓑, h𝓑, c, hc, rfl⟩, -⟩ := hP
  choose z hz using hqZ
  refine ⟨∑ i, (z i).toNat, fun p hp => ?_⟩
  rw [sum_eq_sum_of_mem_nestohedron hp, ← sum_eq_sum_of_mem_nestohedron hqP, Nat.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hzi := pos_of_mem_nestohedron h𝓑 hc hqP i
  rw [← hz i] at hzi ⊢
  exact_mod_cast (Int.toNat_of_nonneg (by exact_mod_cast hzi.le)).symm

/-! ### The Narayana sum -/

/-- If the lattice points of `P` are the casts of a finset `A` of natural vectors, then the
cast of a natural vector lies in `P` exactly when the vector lies in `A`. -/
private lemma natCast_mem_iff_of_latticePoints_eq {ι : Type*} {P : Set (ι → ℝ)}
    {A : Finset (ι → ℕ)} (hA : P.latticePoints = (fun q i => (q i : ℝ)) '' (A : Set (ι → ℕ)))
    (q : ι → ℕ) : (fun i => (q i : ℝ)) ∈ P ↔ q ∈ A := by
  refine ⟨fun hq => ?_, fun hq => ?_⟩
  · have h : (fun i => (q i : ℝ)) ∈ P.latticePoints := ⟨hq, fun i => ⟨(q i : ℤ), by simp⟩⟩
    obtain ⟨q', hq', heq⟩ := hA ▸ h
    obtain rfl : q' = q := funext fun i => by simpa using congrFun heq i
    exact hq'
  · exact (hA.symm ▸ ⟨q, hq, rfl⟩ : (fun i => (q i : ℝ)) ∈ P.latticePoints).1

/-- A finite sum over the natural vectors whose casts lie in `P` is the sum over `A`, when the
lattice points of `P` are exactly the casts of `A`. -/
private lemma finsum_natCast_mem_eq_sum {ι M : Type*} [AddCommMonoid M] {P : Set (ι → ℝ)}
    {A : Finset (ι → ℕ)} (hA : P.latticePoints = (fun q i => (q i : ℝ)) '' (A : Set (ι → ℕ)))
    (f : (ι → ℕ) → M) : ∑ᶠ (q : ι → ℕ) (_ : (fun i => (q i : ℝ)) ∈ P), f q = ∑ q ∈ A, f q := by
  rw [← finsum_mem_coe_finset]
  exact finsum_congr fun q => by rw [natCast_mem_iff_of_latticePoints_eq hA, Finset.mem_coe]

/-- A valid composition of `π ∈ S_n` has sum `n - des(π)`, which is at least `des(π) + 1`; hence
`n = ∑ q + des(π)`. -/
private lemma eq_sum_add_numDescents {n : ℕ} (hn : 1 ≤ n) {π : List ℕ} (hπ : π ∈ permWords n)
    {q : Fin (π.numDescents + 1) → ℕ} (hq : q ∈ π.validCompositions) :
    n = ∑ i, q i + π.numDescents := by
  have h := List.mem_compositionTuple_of_mem_validCompositions hn hπ hq
  simp only [Finset.Nat.compositionTuple, Finset.mem_filter,
    Finset.Nat.mem_antidiagonalTuple] at h
  have : π.numDescents + 1 ≤ ∑ i, q i := by
    simpa using Finset.card_nsmul_le_sum Finset.univ q 1 fun i _ => h.2 i
  omega

/-- The sum of the Narayana tuple products over the valid compositions of `π ∈ S_n` is
ultra log-concave of order `n`: by the refined fertility formula it is `x · D_π`, and `D_π` is
ultra log-concave of order `n - 1`. -/
private lemma isUltraLogConcave_sum_narayanaTupleProd (hfert : RefinedFertilityFormula)
    (hsub : ∀ (σ τ : Type) [Fintype σ] [Fintype τ],
      MvPolynomial.LorentzianNonnegLinearSubstitution σ τ)
    (hBH : ∀ (σ : Type) [Fintype σ], MvPolynomial.NormalizedSupportPolyLorentzianOfMConvex σ)
    {n : ℕ} (hn : 1 ≤ n) {π : List ℕ} (hπ : π ∈ permWords n) :
    (∑ q ∈ π.validCompositions, narayanaTupleProd q).IsUltraLogConcave n := by
  have h := (List.isUltraLogConcave_fiberDescentPolynomial hn hπ (hBH _) (hsub _ _)).mul_X
  rwa [mul_comm, hfert n hn π hπ, Nat.sub_add_cancel hn] at h

/-- For `r ≥ 1`, an integral binary nestohedron `P ⊆ ℝ^r` on which the coordinate sum is the
constant `S ∈ ℤ_{≥0}`, the Narayana sum `∑_{q ∈ ℤ_{≥0}^r ∩ P} ∏_i N_{q_i}(x)` is
ultra-log-concave of order `S + r - 1`. -/
@[lognarayana "thm_nestohedron_narayana_ulc"]
public theorem isUltraLogConcave_finsum_prod_narayanaPolynomial
    (hreal : IntegralBinaryNestohedronRealization) (hfert : RefinedFertilityFormula)
    (hsub₀ : ∀ (σ τ : Type) [Fintype σ] [Fintype τ],
      MvPolynomial.LorentzianNonnegLinearSubstitution σ τ)
    (hBH₀ : ∀ (σ : Type) [Fintype σ], MvPolynomial.NormalizedSupportPolyLorentzianOfMConvex σ)
    {r : ℕ} (hr : 1 ≤ r)
    {P : Set (Fin r → ℝ)} (hP : IsIntegralBinaryNestohedron ℝ P) {S : ℕ}
    (hS : ∀ p ∈ P, ∑ i, p i = (S : ℝ)) :
    (∑ᶠ (q : Fin r → ℕ) (_ : (fun i => (q i : ℝ)) ∈ P),
        ∏ i, narayanaPolynomial (q i)).IsUltraLogConcave (S + r - 1) := by
  obtain ⟨n, hn, π, hπ, rfl, hlat⟩ := hreal r hr P hP
  simp only [Fin.cast_eq_self] at hlat
  -- the level `S` is read off any lattice point, which is a valid composition
  obtain ⟨p, hpP, hpint⟩ := hP.latticePoints_nonempty
  obtain ⟨q, hq, rfl⟩ := hlat ▸ (show p ∈ P.latticePoints from ⟨hpP, hpint⟩)
  have hqS : ∑ i, q i = S := by exact_mod_cast (by simpa using hS _ hpP : (∑ i, (q i : ℝ)) = S)
  rw [finsum_natCast_mem_eq_sum hlat,
    show S + (π.numDescents + 1) - 1 = n by have := eq_sum_add_numDescents hn hπ hq; omega]
  exact isUltraLogConcave_sum_narayanaTupleProd hfert hsub₀ hBH₀ hn hπ
