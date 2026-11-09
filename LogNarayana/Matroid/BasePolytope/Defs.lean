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
# Matroid base polytopes and matroid Narayana polynomials

The definitions documented here are stated in `LogNarayana.Definitions` and
`LogNarayana.AuxiliaryDefinitions`, which this module imports.

For a matroid `M` whose ground set lies in a type `α`, the *base polytope* `P_M` is the convex
hull of the indicator vectors `𝟏_B` of the bases `B` of `M`. For `m ≥ 0`, the *homogenized
shifted Narayana polynomial* is `hom_m(Ñ_m)(x, y) = y^m Ñ_m(x / y)`. For `α` finite and
`a : α → ℕ`, the *matroid Narayana polynomial* is
`F_{M,a}(x, y) = ∑_{B ∈ 𝔹(M)} ∏_{i ∈ B} hom(Ñ_{a_i + 1}) ∏_{i ∉ B} hom(Ñ_{a_i})`, and it is the
image of the basis generating polynomial of `M` under the *matroid Narayana operator* `T_a`,
the linear map on multiaffine polynomials with
`T_a(z^B) = ∏_{i ∈ B} hom(Ñ_{a_i + 1}) ∏_{i ∉ B} hom(Ñ_{a_i})`.

## Main definitions

* `homogShiftedNarayanaPolynomial m`: the polynomial `hom_m(Ñ_m)(x, y) ∈ ℝ[x, y]`.
* `Matroid.basePolytope R M`: the convex hull of `{𝟏_B | B a base of M}` in `α → R`.
* `MvPolynomial.matroidNarayanaOperator a`: the operator
  `T_a : restrictSupport ℝ (Set.Iic 𝟙) →ₗ[ℝ] MvPolynomial (Fin 2) ℝ`.
* `Matroid.narayanaPolynomial M a`: the polynomial `F_{M,a} ∈ ℝ[x, y]`.

## Implementation notes

The bivariate polynomial ring is `MvPolynomial (Fin 2) ℝ`, with `x = X 0` and `y = X 1`, and the
homogenization is Mathlib's `Polynomial.homogenize`, which sends `X ^ j` to
`X 0 ^ j * X 1 ^ (m - j)` for `j ≤ m`. Since `Ñ_m` has degree `m`, this is `y^m Ñ_m(x / y)`.
`homogShiftedNarayanaPolynomial` is an `abbrev`, so that the `Polynomial.homogenize` API applies
to it directly.

The paper works over `ℝ` with ground set `[r]`. The base polytope is defined for any partially
ordered semiring of scalars `R` and any type `α` carrying the matroid, the paper's polytope being
`Matroid.basePolytope ℝ M` for `M : Matroid (Fin r)`; the indicator vector of `B` is
`B.indicator 1`, which needs no finiteness of `B`. The operator and the matroid Narayana
polynomial take their variables indexed by an arbitrary finite type `α`, and `[r]` is the case
`α = Fin r`.

The space of multiaffine polynomials is `MvPolynomial.restrictSupport ℝ (Set.Iic 𝟙)`, where
`𝟙 = Finsupp.equivFunOnFinite.symm 1` is the all-ones multi-index, the domain shape used by
`MvPolynomial.algebraicSymbol` and `MvPolynomial.IsHomogeneousOperator` with `κ = 𝟙`. The
operator is the restriction (`LinearMap.domRestrict`) of the `ℝ`-linear map on all of
`MvPolynomial α ℝ` sending `z^β` to `∏_i hom(Ñ_{a_i + β_i})`, built on the monomial basis
`MvPolynomial.basisMonomials`. A multiaffine monomial `z^B` has exponent the indicator of `B`,
so `a_i + β_i` is `a_i + 1` for `i ∈ B` and `a_i` otherwise, which is the paper's formula.

In `Matroid.narayanaPolynomial` the bases are enumerated as the finsets `B : Finset α` with
`M.IsBase ↑B`, as in `Matroid.basisGeneratingPolynomial`.

## References

* [LogNarayana], Section 8 and eq. (8.1).
-/

open Polynomial

@[expose] public section

end

