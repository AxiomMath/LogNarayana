/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import LogNarayana.Attr
public import LogNarayana.AuxiliaryDefinitions

/-!
# Log-concave functions

The definitions documented here are stated in `LogNarayana.Definitions` and
`LogNarayana.AuxiliaryDefinitions`, which this module imports.

A nonnegative function `g` on a convex subset `s` of a real vector space is *log-concave* if
`g (t • u + (1 - t) • v) ≥ g u ^ t * g v ^ (1 - t)` for all `u v ∈ s` and `0 < t < 1`, the
powers being real powers (`Real.rpow`, so that `0 ^ t = 0` for `t > 0`). Where `g` is positive
this says that `log ∘ g` is concave; the formulation by powers allows `g` to vanish.

## Main definitions

* `LogConcaveOn s g`: `s` is convex, `g` is nonnegative on `s`, and `g` is log-concave on `s`.

## Implementation notes

The paper works on a convex subset of `ℝ^σ`; we allow any real vector space `E`. As with
Mathlib's `ConcaveOn`, convexity of the domain is part of the predicate, and the codomain
`ℝ≥0` of the paper is encoded by the nonnegativity clause on a real-valued function.
-/


@[expose] public section

end
