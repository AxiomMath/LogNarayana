/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module
public import Mathlib
public import LogNarayana.Attr
public import LogNarayana.Narayana.Polynomials.Defs
public import LogNarayana.AuxiliaryDefinitions

/-!
# Loopless multigraphs, orientations and orientation sums

The definitions documented here are stated in `LogNarayana.Definitions` and
`LogNarayana.AuxiliaryDefinitions`, which this module imports.

A *loopless multigraph* with vertex type `V` and edge type `E` assigns to every edge `e` two
distinct endpoints `src e ≠ tgt e`; parallel edges are allowed. An *orientation* is a choice, for
every edge `e`, of one of its endpoints `h e ∈ {src e, tgt e}`, toward which `e` is oriented, and
the *in-degree* of a vertex `v` under `h` is `indeg_h(v) = |{e : h e = v}|`.

For an exponent vector `a` and edge weights `b c`, the *weighted orientation polynomial* is
`F^{b,c}_{G,a}(z) = ∏_v z_v ^ (a_v - 1) * ∏_e (b_e z_{src e} + c_e z_{tgt e})`, and the
*orientation polynomial* `F_{G,a}` is its case `b = c = 1`. The *weighted orientation sum* is
`O^{b,c}_{G,a}(x) = ∑_{h ∈ Or(G)} w_h ∏_v Ñ_{a_v - 1 + indeg_h(v)}(x)`, where
`w_h = ∏_e (b_e [h e = src e] + c_e [h e = tgt e])` and `Ñ_m` is the shifted Narayana polynomial,
and the *orientation sum* `O_{G,a}` is its case `b = c = 1`.

## Main definitions

* `LooplessMultigraph V E`: a loopless multigraph on the vertex type `V` with edge type `E`.
* `LooplessMultigraph.orientations G`: the set `Or(G)` of orientations of `G`.
* `LooplessMultigraph.indegree h`: the in-degree vector `v ↦ |{e : h e = v}|` of `h : E → V`.
* `LooplessMultigraph.orientationPoly R G a`: the orientation polynomial `F_{G,a}`.
* `LooplessMultigraph.weightedOrientationPoly G a b c`: the polynomial `F^{b,c}_{G,a}`.
* `LooplessMultigraph.orientationSum G a`: the orientation sum `O_{G,a} ∈ ℝ[x]`.
* `LooplessMultigraph.weightedOrientationSum G a b c`: the polynomial `O^{b,c}_{G,a} ∈ ℝ[x]`.

## Implementation notes

The paper works on the vertex set `[r]` with a finite edge set; this is the instance `V = Fin r`
with `[Fintype E]`. Neither finiteness is part of the structure: it is assumed, as a typeclass on
`E` (and `V`), exactly where a sum or product over edges (or vertices) is formed. The order of
the two endpoints of an edge only names them, so that edge weights such as
`b_e z_{src e} + c_e z_{tgt e}` can be written down.

`Or(G)` is a `Set (E → V)`; in the orientation sums it is realised as the finite set
`Fintype.piFinset fun e => {G.src e, G.tgt e}`, whose members are exactly the orientations. The
in-degree vector is `∑ e, Finsupp.single (h e) 1`, which depends only on the map `h`.

The exponent vector is `a : V → ℕ`, with `a v - 1` taken in `ℕ`; for the paper's positive `a`
this is the paper's exponent, and results needing `0 < a v` assume it. The polynomials `F` have
coefficients in any commutative semiring; the sums `O` are real, as `Ñ_m` is.

## References

* [LogNarayana] *Log-Concavity in Narayana Transforms and Stack-Sorting Fibers*, Section on
  orientation sums.
-/

@[expose] public section

namespace LooplessMultigraph

section Orientations

variable {V E : Type*}

end Orientations

section Indegree

variable {V E : Type*} [Fintype E]

end Indegree

section OrientationPoly

variable {V E : Type*} [Fintype V] [Fintype E]

end OrientationPoly

section WeightedOrientationPoly

variable {V E R : Type*} [Fintype V] [Fintype E] [CommSemiring R]

end WeightedOrientationPoly

section OrientationSums

open Polynomial

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

end OrientationSums

end LooplessMultigraph

end
