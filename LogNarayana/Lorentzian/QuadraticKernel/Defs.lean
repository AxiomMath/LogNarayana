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
# The quadratic kernel

The definitions documented here are stated in `LogNarayana.Definitions` and
`LogNarayana.AuxiliaryDefinitions`, which this module imports.

For polynomials `A, B` in the variables `x`, the kernel `K_{A,B}` is the polynomial in the
variables `x` and one new variable `t` given by `K_{A,B}(x, t) = B(x) + A(x) t + t² / 2`.
It is the second factor of a convolution whose second `t`-derivative is the root operator
`U ↦ A U + ∫₀ᵗ U(x, s) ds + B ∂_t U`.

## Main definitions

* `MvPolynomial.quadraticKernel`: the kernel `K_{A,B} = B + A t + t² / 2`.

## Implementation notes

The paper works over `ℝ` in `ℝ[x, t]`. Here the variables of `ℝ[x, t]` are `Option σ`: the
new variable `t` is `X none`, and `x_i` is `X (some i)`, so `A` and `B` are embedded by
`rename some`; this is the convention of `MvPolynomial.homogenize`. The definition needs only
the scalar `1 / 2`, so it is made over any semifield `R`, with `t² / 2` written `C 2⁻¹ * t²`.

## References

* [LogNarayana]
-/

namespace MvPolynomial

variable {σ : Type*} {R : Type*} [Semifield R]

end MvPolynomial
