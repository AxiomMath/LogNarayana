/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib
public import LogNarayana.Attr
public import LogNarayana.Zonotope.OrientationSum.Defs
public import LogNarayana.Lorentzian.MConvex.Defs
public import LogNarayana.Polynomial.RealStable.Defs
public import LogNarayana.Narayana.Transform.Defs
public import LogNarayana.Polynomial.RealStable.Basic
public import LogNarayana.Narayana.Polynomials.Basic
public import LogNarayana.Narayana.RealRootedTransform.Basic

/-!
# Orientation sums

Let `G` be a loopless multigraph, `a` an exponent vector on its vertices and `b c` edge weights.
Expanding the edge product of the weighted orientation polynomial
`F^{b,c}_{G,a}(z) = ∏_v z_v ^ (a_v - 1) * ∏_e (b_e z_{src e} + c_e z_{tgt e})` chooses, for each
edge, the endpoint toward which it is oriented, so `F^{b,c}_{G,a}` is a sum over the orientations
`h` of `G` of weighted monomials `∏_v z_v ^ (a_v - 1 + indeg_h(v))`. It is homogeneous of degree
`∑_v (a_v - 1) + |E|`, has nonnegative coefficients when `b, c ≥ 0`, and is real-stable when
moreover `b_e + c_e > 0` for every edge.

The Narayana transform sends the monomial `∏_v z_v ^ m_v` to `∏_v Ñ_{m_v}`, so the weighted
orientation sum is `O^{b,c}_{G,a} = 𝒩(F^{b,c}_{G,a})`. The stable-transform theorem then shows
that weighted orientation sums, and in particular orientation sums (`b = c = 1`), are
real-rooted.

## Main results

* `LooplessMultigraph.weightedOrientationPoly_eq_sum_orientations`,
  `LooplessMultigraph.orientationPoly_eq_sum_orientations`: the expansions over orientations.
* `LooplessMultigraph.isHomogeneous_weightedOrientationPoly`: `F^{b,c}_{G,a}` is homogeneous.
* `LooplessMultigraph.hasNonnegCoeffs_weightedOrientationPoly`: nonnegative coefficients.
* `LooplessMultigraph.isRealStable_weightedOrientationPoly`: `F^{b,c}_{G,a}` is real-stable.
* `LooplessMultigraph.weightedOrientationSum_eq_narayanaTransform`:
  `O^{b,c}_{G,a} = 𝒩(F^{b,c}_{G,a})`.
* `LooplessMultigraph.splits_weightedOrientationSum`: weighted orientation sums are real-rooted.
* `LooplessMultigraph.splits_orientationSum`: orientation sums are real-rooted.

## Implementation notes

The paper's positivity of the exponent vector `a` is not needed: with `a v - 1` taken in `ℕ`
the identities hold for every `a : V → ℕ`. The real-rootedness theorems take the cited results
they rest on (the Borcea–Brändén symbol theorem and the two facts on shifted Narayana
polynomials) as hypotheses.

## References

* [LogNarayana] *Log-Concavity in Narayana Transforms and Stack-Sorting Fibers*, Section on
  orientation sums.
-/

namespace LooplessMultigraph

open MvPolynomial

/-! ### Expansion over orientations -/

/-- Regrouping a product over edges by head vertex: `∏ e, f (h e) = ∏ v, f v ^ indeg_h(v)`. -/
private lemma prod_comp_eq_prod_pow_indegree {V E M : Type*} [Fintype V]
    [Fintype E] [CommMonoid M] (h : E → V) (f : V → M) :
    ∏ e, f (h e) = ∏ v, f v ^ indegree h v := by
  classical
  rw [← Finset.prod_fiberwise Finset.univ h (fun e => f (h e))]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [Finset.prod_congr rfl fun e he => by rw [(Finset.mem_filter.1 he).2], Finset.prod_const]
  simp [indegree, Finsupp.finsetSum_apply, Finsupp.single_apply]

/-- Each edge factor is a sum over the two endpoints of the edge, weighted by `b` at the source
and `c` at the target. -/
private lemma edgeFactor_eq_sum {V E R : Type*} [DecidableEq V] [CommSemiring R]
    (G : LooplessMultigraph V E) (b c : E → R) (e : E) :
    C (b e) * X (G.src e) + C (c e) * X (G.tgt e) =
      ∑ u ∈ ({G.src e, G.tgt e} : Finset V),
        C ((if u = G.src e then b e else 0) + (if u = G.tgt e then c e else 0)) * X u := by
  have hne := G.src_ne_tgt e
  simp [Finset.sum_pair hne, hne, hne.symm]

section Expansion

variable {V E R : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  [CommSemiring R]

/-- The weighted orientation polynomial expands over orientations:
`F^{b,c}_{G,a}(z) = ∑_{h ∈ Or(G)} ∏_e (b_e [h e = src e] + c_e [h e = tgt e]) *
∏_v z_v ^ (a_v - 1 + indeg_h(v))`. -/
@[lognarayana "lem_weighted_orientation_poly_expansion"]
public theorem weightedOrientationPoly_eq_sum_orientations (G : LooplessMultigraph V E)
    (a : V → ℕ) (b c : E → R) :
    G.weightedOrientationPoly a b c =
      ∑ h ∈ Fintype.piFinset (fun e => ({G.src e, G.tgt e} : Finset V)),
        C (∏ e, ((if h e = G.src e then b e else 0) + (if h e = G.tgt e then c e else 0))) *
          ∏ v, X v ^ (a v - 1 + indegree h v) := by
  rw [weightedOrientationPoly]
  simp_rw [edgeFactor_eq_sum, Finset.prod_univ_sum, Finset.mul_sum, Finset.prod_mul_distrib,
    prod_comp_eq_prod_pow_indegree _ X, ← map_prod, pow_add, Finset.prod_mul_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

end Expansion

/-- With unit weights, an edge pointed at one of its two (distinct) endpoints has weight `1`. -/
private lemma edgeWeight_one {V E R : Type*} [DecidableEq V] [AddMonoidWithOne R]
    (G : LooplessMultigraph V E) {e : E} {v : V} (hv : v ∈ ({G.src e, G.tgt e} : Finset V)) :
    ((if v = G.src e then (1 : R) else 0) + if v = G.tgt e then 1 else 0) = 1 := by
  rcases Finset.mem_insert.1 hv with rfl | hv
  · simp [G.src_ne_tgt e]
  · rw [Finset.mem_singleton.1 hv]; simp [(G.src_ne_tgt e).symm]

section Expansion

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- The orientation polynomial expands over orientations:
`F_{G,a}(z) = ∑_{h ∈ Or(G)} ∏_v z_v ^ (a_v - 1 + indeg_h(v))`. -/
@[lognarayana "lem_orientation_poly_expansion"]
public theorem orientationPoly_eq_sum_orientations (R : Type*) [CommSemiring R]
    (G : LooplessMultigraph V E) (a : V → ℕ) :
    G.orientationPoly R a =
      ∑ h ∈ Fintype.piFinset (fun e => ({G.src e, G.tgt e} : Finset V)),
        ∏ v, X v ^ (a v - 1 + indegree h v) := by
  have hF : G.orientationPoly R a = G.weightedOrientationPoly a 1 1 := by
    simp [weightedOrientationPoly, orientationPoly]
  rw [hF, weightedOrientationPoly_eq_sum_orientations]
  refine Finset.sum_congr rfl fun h hh => ?_
  simp [edgeWeight_one G (Fintype.mem_piFinset.1 hh _)]

end Expansion

/-! ### Homogeneity, nonnegativity and real stability -/

section Homogeneous

variable {V E R : Type*} [Fintype V] [Fintype E] [CommSemiring R]

/-- The weighted orientation polynomial `F^{b,c}_{G,a}` is homogeneous of degree
`∑_v (a_v - 1) + |E|`. -/
@[lognarayana "lem_weighted_orientation_poly_homogeneous"]
public theorem isHomogeneous_weightedOrientationPoly (G : LooplessMultigraph V E) (a : V → ℕ)
    (b c : E → R) :
    (G.weightedOrientationPoly a b c).IsHomogeneous (∑ v, (a v - 1) + Fintype.card E) := by
  rw [weightedOrientationPoly, Fintype.card_eq_sum_ones]
  exact (IsHomogeneous.prod _ _ _ fun v _ => isHomogeneous_X_pow v _).mul
    (IsHomogeneous.prod _ _ _ fun e _ =>
      (isHomogeneous_C_mul_X _ _).add (isHomogeneous_C_mul_X _ _))

end Homogeneous

/-- A product of powers of variables is the monomial `monomial (∑ v, single v (n v)) 1`, so each
of its coefficients is `0` or `1`, hence nonnegative. -/
private lemma coeff_prod_X_pow_nonneg {V R : Type*} [Fintype V] [CommSemiring R]
    [PartialOrder R] [IsOrderedRing R] (n : V → ℕ) (α : V →₀ ℕ) :
    0 ≤ (∏ v, X v ^ n v : MvPolynomial V R).coeff α := by
  classical
  simp only [X_pow_eq_monomial, ← monomial_sum_one, coeff_monomial]
  split_ifs <;> simp

section Nonneg

variable {V E R : Type*} [Fintype V] [Fintype E] [CommSemiring R] [PartialOrder R]
  [IsOrderedRing R]

/-- For nonnegative edge weights `b c`, the weighted orientation polynomial `F^{b,c}_{G,a}` has
nonnegative coefficients. -/
@[lognarayana "lem_weighted_orientation_poly_nonneg"]
public theorem hasNonnegCoeffs_weightedOrientationPoly (G : LooplessMultigraph V E) (a : V → ℕ)
    {b c : E → R} (hb : 0 ≤ b) (hc : 0 ≤ c) :
    (G.weightedOrientationPoly a b c).HasNonnegCoeffs := by
  intro α
  classical
  rw [weightedOrientationPoly_eq_sum_orientations, coeff_sum]
  refine Finset.sum_nonneg fun h _ => ?_
  rw [coeff_C_mul]
  exact mul_nonneg (Finset.prod_nonneg fun e _ =>
    add_nonneg (ite_nonneg (hb e) le_rfl) (ite_nonneg (hc e) le_rfl)) (coeff_prod_X_pow_nonneg _ α)

end Nonneg

/-- A combination of two points of the open upper half-plane with nonnegative real weights,
not both zero, lies in the open upper half-plane. -/
private lemma im_ofReal_mul_add_ofReal_mul_pos {b c : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hbc : 0 < b + c) {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) :
    0 < (b * z + c * w).im := by
  simp only [Complex.add_im, Complex.im_ofReal_mul]
  nlinarith [mul_pos hbc (lt_min hz hw), mul_le_mul_of_nonneg_left (min_le_left z.im w.im) hb,
    mul_le_mul_of_nonneg_left (min_le_right z.im w.im) hc]

section RealStable

variable {V E : Type*} [Fintype V] [Fintype E]

/-- For nonnegative edge weights `b c` with `0 < b e + c e` for every edge `e`, the weighted
orientation polynomial `F^{b,c}_{G,a}` is real-stable. -/
@[lognarayana "lem_weighted_orientation_poly_real_stable"]
public theorem isRealStable_weightedOrientationPoly (G : LooplessMultigraph V E) (a : V → ℕ)
    {b c : E → ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c) (hbc : ∀ e, 0 < b e + c e) :
    (G.weightedOrientationPoly a b c).IsRealStable := by
  intro ζ hζ
  simp only [weightedOrientationPoly, map_mul, map_prod, map_pow, map_add, aeval_C, aeval_X,
    Complex.coe_algebraMap]
  exact mul_ne_zero (Finset.prod_ne_zero_iff.2 fun v _ =>
      pow_ne_zero _ fun h => by simpa [h] using hζ v)
    (Finset.prod_ne_zero_iff.2 fun e _ h => by
      simpa [h] using im_ofReal_mul_add_ofReal_mul_pos (hb e) (hc e) (hbc e)
        (hζ (G.src e)) (hζ (G.tgt e)))

end RealStable

/-! ### Orientation sums as Narayana transforms -/

/-- The Narayana transform of `C w * ∏ v, X v ^ n v` is `C w * ∏ v, Ñ_{n v}`. -/
private lemma narayanaTransform_C_mul_prod_X_pow {V : Type*} [Fintype V] (w : ℝ) (n : V → ℕ) :
    narayanaTransform V (C w * ∏ v, X v ^ n v) =
      Polynomial.C w * ∏ v, shiftedNarayanaPolynomial (n v) := by
  have hmon : (C w * ∏ v, X v ^ n v : MvPolynomial V ℝ) =
      w • monomial (Finsupp.equivFunOnFinite.symm n) 1 := by
    rw [smul_monomial, smul_eq_mul, mul_one, monomial_eq, Finsupp.prod_fintype _ _ (by simp)]
    simp
  rw [hmon, map_smul, ← congrFun (coe_basisMonomials V ℝ) _, narayanaTransform,
    Module.Basis.constr_basis, Polynomial.smul_eq_C_mul,
    Finsupp.prod_fintype _ _ fun _ => by simp [shiftedNarayanaPolynomial]]
  simp

section Transform

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- The weighted orientation sum is the Narayana transform of the weighted orientation
polynomial: `O^{b,c}_{G,a} = 𝒩(F^{b,c}_{G,a})`. -/
@[lognarayana "lem_weighted_orientation_sum_eq_transform"]
public theorem weightedOrientationSum_eq_narayanaTransform (G : LooplessMultigraph V E)
    (a : V → ℕ) (b c : E → ℝ) :
    G.weightedOrientationSum a b c =
      MvPolynomial.narayanaTransform V (G.weightedOrientationPoly a b c) := by
  rw [weightedOrientationPoly_eq_sum_orientations, map_sum]
  simp only [narayanaTransform_C_mul_prod_X_pow, weightedOrientationSum]

end Transform

/-! ### Real-rootedness -/

section RealRooted

open Polynomial

universe u

variable {V E : Type u} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- **Weighted orientation sums are real-rooted**: for a loopless multigraph `G`, exponents `a`
and nonnegative edge weights `b c` with `b e + c e > 0` on every edge, the weighted orientation
sum `O^{b,c}_{G,a}` splits over `ℝ`. -/
@[lognarayana "thm_weighted_orientation_sum_real_rooted"]
public theorem splits_weightedOrientationSum
    (hBB : ∀ σ : Type u, RealStablePreserverOfSymbol σ)
    (hLW : ShiftedNarayanaNegRealRoots)
    (G : LooplessMultigraph V E) (a : V → ℕ) {b c : E → ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hbc : ∀ e, 0 < b e + c e) :
    (G.weightedOrientationSum a b c).Splits := by
  have hst := G.isRealStable_weightedOrientationPoly a hb hc hbc
  rw [G.weightedOrientationSum_eq_narayanaTransform]
  exact splits_narayanaTransform_of_isRealStable hBB hLW
    (G.isHomogeneous_weightedOrientationPoly a b c) hst
    (G.hasNonnegCoeffs_weightedOrientationPoly a hb hc)

/-- With unit edge weights the weighted orientation sum is the orientation sum. -/
private theorem weightedOrientationSum_one_one (G : LooplessMultigraph V E) (a : V → ℕ) :
    G.weightedOrientationSum a 1 1 = G.orientationSum a := by
  refine Finset.sum_congr rfl fun h hh => ?_
  rw [Finset.prod_eq_one, Polynomial.C_1, one_mul]
  intro e _
  rcases Finset.mem_insert.1 (Fintype.mem_piFinset.1 hh e) with he | he
  · simp [he, G.src_ne_tgt e]
  · simp [Finset.mem_singleton.1 he, (G.src_ne_tgt e).symm]

/-- **Orientation sums are real-rooted**: for a loopless multigraph `G` and exponents `a`, the
orientation sum `O_{G,a}` splits over `ℝ`. -/
@[lognarayana "thm_orientation_sum_real_rooted"]
public theorem splits_orientationSum
    (hBB : ∀ σ : Type u, RealStablePreserverOfSymbol σ)
    (hLW : ShiftedNarayanaNegRealRoots)
    (G : LooplessMultigraph V E) (a : V → ℕ) :
    (G.orientationSum a).Splits := by
  rw [← weightedOrientationSum_one_one]
  exact splits_weightedOrientationSum hBB hLW G a zero_le_one zero_le_one
    fun _ => by norm_num

end RealRooted

end LooplessMultigraph
