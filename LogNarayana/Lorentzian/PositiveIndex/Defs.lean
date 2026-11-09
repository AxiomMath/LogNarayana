/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module
public import Mathlib
public import LogNarayana.Attr
public import LogNarayana.AuxiliaryDefinitions

/-!
# The positive index of a square matrix

The definitions documented here are stated in `LogNarayana.Definitions` and
`LogNarayana.AuxiliaryDefinitions`, which this module imports.

Given a square matrix `A` indexed by a finite type `σ`, a submodule `W` of `σ → R` is
`A`-positive when the quadratic form `v ↦ vᵀ A v` is strictly positive on every nonzero
vector of `W`; that is, the restriction of this form to `W` is positive definite. The
positive index `p(A)` is the largest dimension of an `A`-positive subspace, and `A` has at
most one positive eigenvalue when `p(A) ≤ 1`. For a real symmetric matrix, `p(A)` is the
number of positive eigenvalues counted with multiplicity, which explains the name.

## Main definitions

* `Matrix.IsPositiveSubspace`: `W` is `A`-positive.
* `Matrix.posIndex`: the positive index of `A`.
* `Matrix.HasAtMostOnePosEigenvalue`: the condition `A.posIndex ≤ 1`.

## Implementation notes

The paper works over `ℝ`; the definitions are stated over any commutative ring with a
partial order, which is all that the condition `0 < vᵀ A v` needs. No symmetry of `A` is
assumed, matching the paper.

The positive index is the supremum in `ℕ` of `Module.finrank R W` over the `A`-positive
submodules `W`. Since `⊥` is always `A`-positive and every submodule of `σ → R` has rank at
most `Fintype.card σ` (over a field), this set is nonempty and bounded, so the supremum is
attained. Since `(A.toQuadraticForm') v = v ⬝ᵥ (A *ᵥ v)`, over a linearly ordered field the
positive index of any square matrix `A` (symmetric or not) equals `sigPos A.toQuadraticForm'`;
the definition is kept in terms of `Matrix.IsPositiveSubspace` so that it needs only a partial
order on `R`.

`Matrix.HasAtMostOnePosEigenvalue` is phrased through the positive index rather than through
eigenvalues, so it needs no symmetry hypothesis and no spectral theorem; it is an `abbrev`, so
that lemmas about `Matrix.posIndex` apply to it directly.
-/

namespace Matrix

variable {σ R : Type*} [Fintype σ] [CommRing R] [PartialOrder R]

end Matrix
