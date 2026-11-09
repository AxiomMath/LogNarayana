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
# Deformed Narayana polynomials

The definitions documented here are stated in `LogNarayana.Definitions` and
`LogNarayana.AuxiliaryDefinitions`, which this module imports.

For a parameter `λ` and an integer `q ≥ 1`, the *deformed Narayana polynomial* is
`N_q^{(λ)}(x) = x · Q_{q-1}(1 + x, λ x)
  = x ∑_{j=0}^{⌊(q-1)/2⌋} C_j (q-1 choose 2j) (λ x)^j (1 + x)^(q-1-2j)`,
where `Q_m` is `narayanaQ` and `C_j` are the Catalan numbers. At `λ = 1` it is the Narayana
polynomial `N_q`, and its sums over the lattice points of an integral binary nestohedron are
the deformed Narayana sums studied through quadratic replacements on fertilitopes.

## Main definitions

* `deformedNarayanaPolynomial R lam q` : the polynomial `N_q^{(λ)}(x) ∈ R[X]`.

## Implementation notes

The paper works over `ℝ`; since `Q_m` has natural-number coefficients, the definition is
stated over any commutative semiring `R` with `lam : R` for `λ`, the paper's polynomial being
the case `R = ℝ`. The paper only uses `q ≥ 1`; for `q = 0` the truncated subtraction gives
`Q_0 = 1`, so the value is `x`.

## References

* [LogNarayana]
-/

open Polynomial

