/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module
public import LogNarayana.StackSorting.ValidHookConfigurations.Defs
public import LogNarayana.AuxiliaryDefinitions

/-!
# Coordinate simplices, binary nestohedra and fertilitopes

The definitions documented here are stated in `LogNarayana.Definitions` and
`LogNarayana.AuxiliaryDefinitions`, which this module imports.

For a set `J` of coordinates, the coordinate simplex `Δ_J ⊆ R^ι` is the convex hull of the
standard basis vectors `e_j`, `j ∈ J`. A *binary building set* on a finite linear order `α` (in
the paper `α = [r]`) is a laminar collection `𝓑` of nonempty intervals containing every
singleton. The *nestohedron* `Nest_𝓑(c) = ∑_{J ∈ 𝓑} c_J Δ_J` is a Minkowski sum of dilated
coordinate simplices; it is a *binary nestohedron* when `𝓑` is a binary building set and every
`c_J` is positive, and an *integral* one when moreover all its vertices are lattice points.
The *fertilitope* `Fer_π = conv 𝒱(π) ⊆ ℝ^{des(π)+1}` of a permutation `π` is the convex hull of
its valid compositions; by [Fertilitopes] it is an integral binary nestohedron.

## Main definitions

* `Set.latticePoints P`: the points `P ∩ ℤ^ι` of `P ⊆ R^ι` with integer coordinates.
* `coordSimplex R J`: the convex hull of `{Pi.single j 1 | j ∈ J}` in `ι → R`.
* `IsBinaryBuildingSet 𝓑`: `𝓑 : Finset (Finset α)` is a binary building set.
* `nestohedron R 𝓑 c`: the Minkowski sum `∑ J ∈ 𝓑, c J • coordSimplex R J`.
* `IsBinaryNestohedron R P`: `P` is `nestohedron R 𝓑 c` for a binary building set `𝓑` and
  coefficients positive on `𝓑`.
* `IsIntegralBinaryNestohedron R P`: `P` is a binary nestohedron whose extreme points are
  lattice points.
* `List.fertilitope R π`: the convex hull of the valid compositions of `π`, cast into `R`.

## Implementation notes

The paper works over `ℝ` in `ℝ^r` with `r ≥ 1`, coordinates indexed by `[r] = Fin r`. Here the
scalars are any ordered semiring (a ring where integers enter), the coordinates any index type
or, for building sets, any locally finite linear order; the paper's case is `R = ℝ`,
`α = Fin r`. None of `r ≥ 1`, `J ≠ ∅`, `IsBinaryBuildingSet 𝓑` or `0 < c J` is needed to form
the objects, so they are not hypotheses of the definitions. Building sets are `Finset`s of
`Finset`s, which records their finiteness and lets one sum over their members; the
coefficients `c` are a function on all of `Finset α`, of which only the values on `𝓑` are used.

The Minkowski sum is the pointwise sum of sets in `Set (ι → R)`; that it is the set of points
`∑_J c_J v_J` with `v_J ∈ Δ_J` is `Set.image_finsetSum_pi`. Vertices of a nestohedron are its
extreme points `Set.extremePoints R P`.

The fertilitope's coordinates are indexed by `Fin (π.numDescents + 1)`, literally `Fin r` for
`r = des(π) + 1`, so it compares directly with nestohedra in `Fin r → R`. As for
`List.validCompositions`, it is defined for every word `π : List ℕ`.

## References

* [LogNarayana], Section on coordinate simplices, binary nestohedra and fertilitopes.
* [Fertilitopes], Section 2.1.
-/

open scoped Pointwise

@[expose] public section

section Simplex

variable (R : Type*) {ι : Type*} [Semiring R] [PartialOrder R] [DecidableEq ι]

end Simplex

section BuildingSet

variable {α : Type*} [LinearOrder α] [LocallyFiniteOrder α]

end BuildingSet

section Nestohedron

variable (R : Type*) {α : Type*}

end Nestohedron

namespace List

variable (R : Type*) [Semiring R] [PartialOrder R]

end List

end
