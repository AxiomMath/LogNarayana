/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module
public import Mathlib
public import LogNarayana.Attr
public import LogNarayana.Troupe.PostorderPolynomial.Defs
public import LogNarayana.StackSorting.StackSort.Defs
public import LogNarayana.Troupe.LocalRules.Defs
public import LogNarayana.AuxiliaryDefinitions

/-!
# The Schröder postorder polynomial

The definitions documented here are stated in `LogNarayana.Definitions` and
`LogNarayana.AuxiliaryDefinitions`, which this module imports.

For a permutation `π ∈ S_n`, the *Schröder postorder polynomial* is
`𝒞_π(z, w) = ∑ z^{black(𝒯)} w^{white(𝒯)}`, the sum running over the decreasing labelings
`𝒯 ∈ ↓𝐒↓` of Schröder two-colored binary trees whose postorder reading `𝒫(𝒯)` is `π`.

## Main definitions

* `List.schroederFiberPolynomial R C π`: the polynomial `𝒞_π(z, w) ∈ R[z, w]`.

## Implementation notes

The two variables are those of `MvPolynomial (Fin 2) R`, with `z = X 0` and `w = X 1`, as for
`List.fiberHomogPolynomial`. The paper works over `ℝ`; the coefficients are taken in any
commutative semiring `R`, the paper's polynomial being `List.schroederFiberPolynomial ℝ C π`.
The sum is a `finsum` over the set of decreasing labelings `𝒯` with
`(𝒯.map Prod.fst).postorder = π`; this set is finite, since such a `𝒯` has `π.length` vertices
labelled in `[π.length]`. The polynomial is defined for every list `π`; it vanishes unless `π` is
a permutation word.

## References

* [LogNarayana] *Log-Concavity in Narayana Transforms and Stack-Sorting Fibers*, Section 5.
-/

@[expose] public section

open MvPolynomial

namespace List

end List

end
