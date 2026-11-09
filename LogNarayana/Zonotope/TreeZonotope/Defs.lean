/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module
public import Mathlib
public import LogNarayana.Attr
public import LogNarayana.Nestohedron.Fertilitope.Defs
public import LogNarayana.Zonotope.OrientationSum.Defs
public import LogNarayana.AuxiliaryDefinitions

/-!
# Forests and tree zonotopes

The definitions documented here are stated in `LogNarayana.Definitions` and
`LogNarayana.AuxiliaryDefinitions`, which this module imports.

A loopless multigraph `G` is a *forest* when it has no parallel edges — the map sending an edge
`e` to its unordered pair of endpoints `s(G.src e, G.tgt e) : Sym2 V` is injective — and the
simple graph on `V` whose edges are exactly these unordered pairs is acyclic.

For a loopless multigraph `G = (E, s, t)` on the vertex type `V` with finitely many edges and a
point `a : V → R`, the polytope `P_{G,a}` is the Minkowski sum
`a + ∑_{e ∈ E} Δ_{{s(e), t(e)}}` of the translate `a` and the edge simplices (segments)
`Δ_{{s(e), t(e)}} = conv {e_{s(e)}, e_{t(e)}}`. When `G` is a forest and `a` has positive
integer coordinates, this is the tree zonotope `P_{T,a}`.

## Main definitions

* `LooplessMultigraph.IsForest`: the loopless multigraph `G` is a forest.
* `LooplessMultigraph.zonotope G a`: the set `{a + ∑ e, p e | p e ∈ Δ_{{src e, tgt e}} ∀ e}`.

## Implementation notes

The underlying simple graph of `G` is `SimpleGraph.fromEdgeSet` of the range of the endpoint
map; since `G` is loopless no edge is diagonal, so its adjacency is exactly
"`s(u, v) = s(G.src e, G.tgt e)` for some edge `e`".

The paper works on the vertex set `[r]`, with scalars `ℝ` and `a ∈ ℤ^r`; we allow an arbitrary
vertex type, an arbitrary ordered semiring of scalars `R` and an arbitrary translate `a : V → R`
(an integer vector enters through the cast `fun v => (a v : ℝ)`). The Minkowski sum is written
out as the set of sums of one point chosen from each edge simplex, which is the paper's own
description. No forest or positivity hypothesis is needed to form the set.

## References

* [LogNarayana] *Log-Concavity in Narayana Transforms and Stack-Sorting Fibers*, Section on
  lattice points of tree zonotopes.
-/

@[expose] public section

namespace LooplessMultigraph

section Forest

variable {V E : Type*}

end Forest

end LooplessMultigraph

end


section Zonotope

variable {R : Type*} {V E : Type*} [Semiring R] [PartialOrder R] [DecidableEq V] [Fintype E]

end Zonotope
