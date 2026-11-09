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
# Real stability, negative real-rootedness and homogenization

The definitions documented here are stated in `LogNarayana.Definitions` and
`LogNarayana.AuxiliaryDefinitions`, which this module imports.

This file collects the notions of zero-freeness used for real polynomials.

A real univariate polynomial `f` *has only negative real zeros* if it is real-rooted, i.e. it
splits into linear factors over `ℝ`, and every root of `f` (counted in its multiset of roots) is
negative. The zero polynomial splits and has no roots, so it has only negative real zeros.

A multivariate polynomial `f` with real coefficients in the variables `zᵢ`, `i ∈ σ`, is
*real-stable* if it has no zero in the product of open upper half-planes: `f(ζ) ≠ 0` for every
`ζ ∈ ℂ^σ` with `Im ζᵢ > 0` for all `i`.

Given a polynomial `f` in the variables `zᵢ`, `i ∈ σ`, and a natural number `D`, the
homogenization of `f` of degree `D` is the polynomial in the variables `zᵢ` and one new
variable `y` obtained by padding every monomial `z^α` of `f` with `|α| ≤ D` by `y ^ (D - |α|)`:
`f^{hom,D} = ∑_{|α| ≤ D} [z^α] f · z^α y^(D - |α|)`.
When `f.totalDegree ≤ D` this is `y ^ D f(z / y)`, homogeneous of degree `D`.

## Main definitions

* `Polynomial.HasOnlyNegativeRoots f`: the polynomial `f` splits and all of its roots are
  negative.
* `MvPolynomial.homogenize f D`: the homogenization of `f` of degree `D`, a polynomial in
  `MvPolynomial (Option σ) R`.
* `MvPolynomial.IsRealStable f`: the real polynomial `f` does not vanish on the product of open
  upper half-planes.

## Implementation notes

`Polynomial.HasOnlyNegativeRoots` is stated over an arbitrary integral domain `R` carrying a
relation `<`; the paper's notion is the case `R = ℝ`, where splitting over `ℝ` is
real-rootedness. Real-rootedness is expressed by `Polynomial.Splits`, and the roots by the
multiset `Polynomial.roots`.

In `MvPolynomial.homogenize` the new variable `y` is `X none`, and `zᵢ` is `X (some i)`. The
definition makes sense for every `f`; monomials of degree larger than `D` are dropped, so the
hypothesis `f.totalDegree ≤ D` is only needed for the lemmas relating `homogenize f D` to `f`
(e.g. that setting `y = 1` recovers `f`). This is the multivariate analogue of
`Polynomial.homogenize`, which is the case of one variable `z`.

In `MvPolynomial.IsRealStable` the polynomial is evaluated at a complex point through the
`ℝ`-algebra structure of `ℂ`, that is, with `MvPolynomial.aeval`. The index type `σ` is
arbitrary; only the finitely many variables occurring in `f` matter. With this definition the
zero polynomial is not real-stable, in agreement with the paper's phrasing "real-stable or
zero".

## References

* [LogNarayana]
-/

namespace MvPolynomial

end MvPolynomial
