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
# Narayana polynomials and their γ-expansion

The *Narayana polynomials* are `N₀(x) = 1` and, for `q ≥ 1`,
`N_q(x) = ∑_{j=1}^{q} (1/q) (q choose j) (q choose j-1) xʲ`, the generating polynomials of the
Narayana numbers. The *shifted Narayana polynomial* is `Ñ_m(x) = N_{m+1}(x) / x`, that is
`Ñ_m(x) = ∑_{j=0}^{m} (1/(m+1)) (m+1 choose j+1) (m+1 choose j) xʲ`.

The γ-expansion of `Ñ_m` is carried by the polynomials
`M_m(z) = ∑_{j=0}^{⌊m/2⌋} C_j (m choose 2j) zʲ` and
`Q_m(A, B) = ∑_{j=0}^{⌊m/2⌋} C_j (m choose 2j) Bʲ A^(m-2j)`, with `C_j` the Catalan numbers:
`Ñ_m(x) = Q_m(1 + x, x)`.

This file also records the coefficient conditions under which the paper studies these
polynomials: symmetry and γ-nonnegativity with respect to an integer `d`, and unimodality.

## Main definitions

* `narayanaPolynomial q` : the Narayana polynomial `N_q(x) ∈ ℝ[X]`.
* `narayanaTupleProd q` : the product `∏ i, N_{q i}(x)` over a tuple `q : I → ℕ`.
* `shiftedNarayanaPolynomial m` : the shifted Narayana polynomial `Ñ_m(x) ∈ ℝ[X]`.
* `narayanaM R m` : the polynomial `M_m(z)` in `R[X]`.
* `narayanaQ R m` : the polynomial `Q_m(A, B)` in `MvPolynomial (Fin 2) R`, with `A = X 0` and
  `B = X 1`.
* `IsSymmetricWRT d f` : the polynomial `f` is symmetric with respect to `d`.
* `IsUnimodalPolynomial f` : the coefficients of `f` up to `f.natDegree` are unimodal.
* `IsGammaNonnegWRT d f` : the polynomial `f` is γ-nonnegative with respect to `d`.

## Implementation notes

For `q = 0` the sum defining `N_q` is empty, so the value `N₀ = 1` is a separate case. The
paper defines `Ñ_m` as the quotient `N_{m+1}(x)/x`; here it is defined by its explicit
coefficient formula, which needs no division of polynomials.

`narayanaTupleProd` is an `abbrev` for the `Finset.univ` product, so the big-operator API
(`Fintype.prod_unique`, `Fin.prod_univ_succ`, …) applies to it directly.

The paper works over `ℝ`. Since the coefficients of `M_m` and `Q_m` are natural numbers, these
are stated over an arbitrary commutative semiring `R`; the paper's polynomials are the case
`R = ℝ`. The evaluation `Q_m(F, G)` in a commutative `R`-algebra is
`MvPolynomial.aeval ![F, G] (narayanaQ R m)`. Likewise symmetry and unimodality only involve
coefficients and are stated over a semiring (with a preorder for unimodality), and
γ-nonnegativity over a commutative semiring with a partial order.

Throughout, natural-number division `m / 2` is `⌊m/2⌋`, and `m - 2 * j` is the true difference
on the range of summation `j ≤ m / 2`.

In `IsSymmetricWRT` and `IsGammaNonnegWRT` the integer `d` is part of the data: `X` is
symmetric with respect to `2` but not `1`, and `1 + X` is γ-nonnegative with respect to `1` but
not `0`. The γ-coefficients are a function `ℕ → R` of which only the values at `j ≤ d / 2`
enter; since the polynomials `xʲ (1 + x)^(d-2j)` are linearly independent, they are unique
when they exist.

## References

* [LogNarayana], Section 2 (symmetry, unimodality, γ-nonnegativity) and Section 2.1
  (Narayana polynomials).
-/

open Polynomial Finset

/-- A polynomial `f` is *symmetric with respect to `d`* if `[x^j]f = 0` for every `j > d`
and `[x^j]f = [x^{d-j}]f` for `0 ≤ j ≤ d`. -/
@[expose, lognarayana "def_poly_symmetric"]
public def IsSymmetricWRT {R : Type*} [Semiring R] (d : ℕ) (f : R[X]) : Prop :=
  (∀ j, d < j → f.coeff j = 0) ∧ ∀ j ≤ d, f.coeff j = f.coeff (d - j)

/-- A polynomial `f` is *unimodal* if there is a mode `t ≤ f.natDegree` such that
`f.coeff j ≤ f.coeff (j + 1)` for `j < t` and `f.coeff (j + 1) ≤ f.coeff j` for
`t ≤ j < f.natDegree`. The degree of `0` is `0`, as in the paper. -/
@[expose, lognarayana "def_poly_unimodal"]
public def IsUnimodalPolynomial {R : Type*} [Semiring R] [Preorder R] (f : R[X]) : Prop :=
  ∃ t ≤ f.natDegree, (∀ j < t, f.coeff j ≤ f.coeff (j + 1)) ∧
    ∀ j, t ≤ j → j < f.natDegree → f.coeff (j + 1) ≤ f.coeff j

/-- A polynomial `f` is *γ-nonnegative with respect to `d`* if there are `γⱼ ≥ 0`,
`0 ≤ j ≤ ⌊d/2⌋`, with `f = ∑_{j=0}^{⌊d/2⌋} γⱼ xʲ (1 + x)^(d - 2j)`. -/
@[expose, lognarayana "def_gamma_nonneg"]
public def IsGammaNonnegWRT {R : Type*} [CommSemiring R] [PartialOrder R] (d : ℕ)
    (f : R[X]) : Prop :=
  ∃ γ : ℕ → R, (∀ j ≤ d / 2, 0 ≤ γ j) ∧
    f = ∑ j ∈ range (d / 2 + 1), C (γ j) * X ^ j * (1 + X) ^ (d - 2 * j)
