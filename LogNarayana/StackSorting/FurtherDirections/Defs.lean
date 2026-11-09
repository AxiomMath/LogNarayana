/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module
public import Mathlib
public import LogNarayana.Attr
public import LogNarayana.Polynomial.LogConcave.Defs
public import LogNarayana.AuxiliaryDefinitions

/-!
# Polytopes, the non-log-concave example, and two cited results on real roots

The definitions documented here are stated in `LogNarayana.Definitions` and
`LogNarayana.AuxiliaryDefinitions`, which this module imports.

For `P ⊆ ℝ^ι` and points `x ≠ y`, the segment `[x, y]` is an *edge* of `P` if it is the set of
points of `P` at which some linear functional `ℓ` attains its maximum over `P`. A set `P` is an
*integral polytope* if it is the convex hull of a finite nonempty set of points and its extreme
points lie in `ℤ^ι`, and a *generalized permutohedron* if it is the convex hull of a finite
nonempty set of points and every edge `[x, y]` satisfies `y - x = c (eᵢ - eⱼ)` with `i ≠ j`.

For `S ⊆ [5]` the point `v_S ∈ ℤ^27` is `(a, 1 + 1_S)` when `S = {1, 2}` and `(b, 1 + 1_S)`
otherwise, with `a = (23, 1, …, 1)` and `b = (2, …, 2)` in `ℤ^22`. The polytope `P^nlc ⊆ ℝ^27`
is the convex hull of the ten points `v_S` with `|S| = 2`; its Narayana sum is not
log-concave.

Two cited results are recorded as propositions, to be taken as hypotheses: the theorem of
Brändén and Gal relating real-rootedness of `h(x) = ∑_j γ_j x^j (1 + x)^{d - 2j}` and of its
gamma polynomial `γ(z) = ∑_j γ_j z^j`, and Newton's inequalities, which make a real-rooted
polynomial with nonnegative coefficients log-concave.

## Main definitions

* `IsPolytopeEdge P x y`: the segment `[x, y]` is an edge of `P : Set (ι → ℝ)`.
* `IsIntegralPolytope P`: the set `P : Set (ι → ℝ)` is an integral polytope.
* `IsGeneralizedPermutohedron P`: `P : Set (ι → ℝ)` is a generalized permutohedron.
* `nlcVertex S`: the point `v_S : Fin 27 → ℤ`.
* `nlcPolytope`: the set `conv {v_S : S ⊆ [5], |S| = 2} ⊆ ℝ^27`.
* `Polynomial.GammaRealRootedIff`: the cited theorem of Brändén and Gal.
* `Polynomial.NewtonInequalities`: the cited consequence of Newton's inequalities.

## Implementation notes

The paper works in `ℝ^r` with `r ≥ 1`; the polytope notions are stated for an arbitrary index
type `ι`, the case `ι = Fin r` being the paper's, and the positivity of `r` plays no role. The
segment is Mathlib's `segment ℝ x y` and the functional of an edge an `ℝ`-linear map
`(ι → ℝ) →ₗ[ℝ] ℝ`; for finite `ι` such functionals are continuous, so the condition agrees with
Mathlib's `IsExposed ℝ P (segment ℝ x y)`. Extreme points are `Set.extremePoints ℝ P`, a point
lies in `ℤ^ι` when each coordinate is in the range of `ℤ → ℝ`, and `eᵢ` is `Pi.single i 1`.

For the example, indices are `0`-based: `[5]` is `Fin 5`, so the paper's `{1, 2}` is `{0, 1}`.
The point `v_S` is `Fin.append` of its first `22` and its last `5` coordinates; the formula is
given for every `S ⊆ [5]`, though the paper only uses it for `2`-element subsets. The integer
points are cast coordinatewise to `ℝ`.

Real-rootedness is `Polynomial.Splits` over `ℝ`, and "every real zero is `≤ 0`" is
`∀ r ∈ f.roots, r ≤ 0`. In `GammaRealRootedIff` a symmetric polynomial `h` with center of
symmetry `n/2` is `natDegree h ≤ n` with `h_i = h_{n-i}` for `i ≤ n`, and its γ-vector is a
function `γ : ℕ → ℝ` with `h = ∑_{i ≤ ⌊n/2⌋} γ_i x^i (1 + x)^{n - 2i}`, of which only the values at
`0, …, ⌊n/2⌋` enter. The zero polynomial splits and is log-concave,
so `NewtonInequalities` needs no nonvanishing hypothesis.

## References

* [LogNarayana] *Log-Concavity in Narayana Transforms and Stack-Sorting Fibers*, Sections 1
  and 9.
* [FPV] L. Ferroni, G. Panova, L. Venturello, Theorem 1.1, attributed to P. Brändén and
  S. R. Gal.
* [StanleyLC] R. P. Stanley, *Log-concave and unimodal sequences in algebra, combinatorics,
  and geometry*, Ann. New York Acad. Sci. 576 (1989), Theorem 2.
-/

@[expose] public section

/-! ### Edges, integral polytopes and generalized permutohedra -/

/-! ### The non-log-concave example polytope -/

end

/-! ### Cited results on real-rooted polynomials -/

namespace Polynomial

end Polynomial
