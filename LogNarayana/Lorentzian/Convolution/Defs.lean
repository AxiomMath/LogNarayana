/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib
public import LogNarayana.Attr
public import LogNarayana.Lorentzian.SimplexIntegration.Defs
public import LogNarayana.AuxiliaryDefinitions

/-!
# Convolution in the variable `t`

The definitions documented here are stated in `LogNarayana.Definitions` and
`LogNarayana.AuxiliaryDefinitions`, which this module imports.

For polynomials `F G ∈ R[x, t]`, the convolution `F * G ∈ R[x, t]` is
`𝔍_2 (F(x, u_1) G(x, u_2))`, where `F(x, u_1)` and `G(x, u_2)` are obtained by renaming
`t ↦ u_1`, respectively `t ↦ u_2`, and fixing every `x_j`. Over `ℝ` this is the continuous
convolution `∫_0^t F(x, s) G(x, t - s) ds`.

## Main definitions

* `MvPolynomial.tConvolution`: the convolution `F * G = 𝔍_2 (F(x, u_1) G(x, u_2))`.

## Implementation notes

As for `MvPolynomial.simplexIntegral`, `R[x, t]` is `MvPolynomial (Option σ) R` with
`t = X none` and `x_j = X (some j)`, and `R[x, u_1, u_2]` is `MvPolynomial (σ ⊕ Fin 2) R` with
`x_j = X (Sum.inl j)` and `u_i = X (Sum.inr i)`. The renaming `t ↦ u_i`, `x_j ↦ x_j` is
`MvPolynomial.rename` along `fun o => o.elim (Sum.inr i) Sum.inl`. The paper works over `ℝ`;
the definition only needs a commutative semiring that is a `ℚ`-algebra.

## References

* [LogNarayana]
-/

namespace MvPolynomial

variable {σ : Type*} {R : Type*} [CommSemiring R] [Algebra ℚ R]

end MvPolynomial
