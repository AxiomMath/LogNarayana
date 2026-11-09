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
# Appell sequences and the signed Appell sequence

The definitions documented here are stated in `LogNarayana.Definitions` and
`LogNarayana.AuxiliaryDefinitions`, which this module imports.

A sequence of polynomials `(f m)_{m ≥ 0}` is an *Appell sequence* if `f m` has degree exactly `m`
for every `m` and the formal derivative lowers the index: `(f m)' = m • f (m - 1)` for `m ≥ 1`.

For `m ≥ 0` the *signed Appell polynomial* is
`η_m(t) = ∑_{j=0}^{⌊m/2⌋} (-1)^j C_j (m choose 2j) t^(m-2j)`,
where `C_j = (1/(j+1)) (2j choose j)` is the `j`-th Catalan number. It is monic of degree `m`,
and the sequence `(η_m)_{m ≥ 0}` is an Appell sequence with `η_m' = m η_{m-1}`.

## Main definitions

* `Polynomial.IsAppell`: the predicate that `f : ℕ → R[X]` is an Appell sequence.
* `Polynomial.signedAppell R m`: the polynomial `η_m` with coefficients in a ring `R`.

## Implementation notes

The paper works over `ℝ`. `IsAppell` is stated over an arbitrary semiring `R`, the derivative
condition being written for index `m + 1` as `derivative (f (m + 1)) = (m + 1) • f m`, which
avoids natural-number subtraction. The degree condition uses `Polynomial.degree`, so `f 0` is a
nonzero constant.

The coefficients of `η_m` are integers, so the polynomial is defined over an arbitrary ring `R`,
through the casts `ℕ → R`; the paper's `η_m` is `Polynomial.signedAppell ℝ m`. The Catalan
numbers are Mathlib's `catalan`.

## References

* [LogNarayana], Section 6 (the signed Appell sequence).
-/

namespace Polynomial


section signedAppell

variable (R : Type*) [Ring R]

end signedAppell

end Polynomial
