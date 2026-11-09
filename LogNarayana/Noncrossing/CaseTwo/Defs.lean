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
# The Narayana generating series and the Lagrange inversion formula

The definitions documented here are stated in `LogNarayana.Definitions` and
`LogNarayana.AuxiliaryDefinitions`, which this module imports.

The ordinary generating series of the Narayana polynomials is
`U(z) = ∑_{q ≥ 1} N_q(x) z^q`, a formal power series in `z` with coefficients in `ℝ[x]`.
Its constant coefficient is `0`: the term `N₀ = 1` is not part of the sum.

Let `R` be a commutative ring, `φ ∈ R[u]` a polynomial, and `G ∈ R⟦z⟧` a power series with
vanishing constant term satisfying `G = z φ(G)`. The Lagrange inversion formula states that for
all `1 ≤ k ≤ n`,
`n [z^n] G^k = k [u^(n-k)] φ(u)^n`.
In Stanley's formulation, `G` is the compositional inverse of `F(u) = u / φ(u)`. It is a cited
result, recorded here as a proposition; it is proved for every commutative ring in
`LogNarayana.PowerSeries.LagrangeInversion` (`PowerSeries.lagrangeInversion`).

## Main definitions

* `narayanaGenSeries` : the power series `U(z) ∈ ℝ[x]⟦z⟧`.
* `PowerSeries.LagrangeInversion R`: the Lagrange inversion formula over `R`, as a proposition.

## Implementation notes

The value `φ(G)` is `Polynomial.aeval G φ`, using the `R`-algebra structure of `R⟦X⟧`. The
Lagrange inversion formula is posed over an arbitrary commutative ring, without the hypothesis
`φ(0) ≠ 0`: the identity is one between integer polynomials in the coefficients of `φ`, so it
specialises from the characteristic-zero case to every commutative ring; and when `φ(0) = 0` the
equation forces `G = 0` while `φ ^ n` has order at least `n > n - k`, so both sides vanish.

## References

* [LogNarayana], Sections 2.1 and 7.
* [R. P. Stanley, *Enumerative Combinatorics, Vol. 2*][stanley1999], Theorem 5.4.2.
-/


namespace PowerSeries

end PowerSeries
