/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib
public import LogNarayana.Attr
public import LogNarayana.StackSorting.Descents.Defs
public import LogNarayana.StackSorting.StackSort.Defs
public import LogNarayana.StackSorting.ValidHookConfigurations.Defs
public import LogNarayana.AuxiliaryDefinitions

/-!
# The valid-composition polynomial of a permutation

The definitions documented here are stated in `LogNarayana.Definitions` and
`LogNarayana.AuxiliaryDefinitions`, which this module imports.

Let `π ∈ S_n` with `k = des(π)` descents, and let `𝒱(π)` be its set of valid compositions. The
*valid-composition polynomial* of `π` is the generating polynomial of `𝒱(π)`, shifted down by one
in every coordinate:
`F_π(z₀, …, z_k) = ∑_{𝐪 ∈ 𝒱(π)} ∏_{i=0}^{k} z_i^{q_i - 1}`,
where `q_i - 1` is the truncated difference in `ℤ_{≥0}`.

## Main definitions

* `List.validCompositionPoly R π`: the polynomial `F_π` in `MvPolynomial (Fin (des(π) + 1)) R`.

## Implementation notes

The paper works over `ℝ`; the definition is made over any commutative semiring `R`, and the
paper's polynomial is `List.validCompositionPoly ℝ π`. Each summand `∏ z_i^{q_i - 1}` is the
monomial with exponent `fun i => q i - 1` (truncated subtraction on `ℕ`), written as a product of
powers of the variables `MvPolynomial.X i`. As for `List.validCompositions`, the definition is made
for every word `π : List ℕ`; for a permutation of `[n]` it is the paper's polynomial.

## References

* [LogNarayana], Section 6.
* [Fertilitopes], Section 2.1.
-/

namespace List

end List
