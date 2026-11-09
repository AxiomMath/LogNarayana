/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module
public import LogNarayana.Lorentzian.Convolution.Defs
public import LogNarayana.AuxiliaryDefinitions

/-!
# Higher-degree kernels

The definitions documented here are stated in `LogNarayana.Definitions` and
`LogNarayana.AuxiliaryDefinitions`, which this module imports.

For variables `z = (z_i)_{i ∈ σ}` and one more variable `t`, the elementary kernel of order `m`
is the polynomial
`K_m(z, t) = ∑_{j=0}^m e_j(z) t^{m-j} / (m-j)!`,
where `e_j` is the `j`-th elementary symmetric polynomial in the `z_i` (so `e_0 = 1` and
`e_j = 0` for `j > #σ`). It is the coefficientwise limit as `k → ∞` of the approximants
`f_{m,k}(z, t) = e_m(z, t/k, …, t/k)` (with `k` copies of `t/k`), and is real-stable and
Lorentzian.

A kernel `K ∈ R[x, t]` of degree `m` in `t` defines the higher kernel operator
`𝓡^{(m)}_K U = ∂_t^m (U * K)`, where `*` is the convolution in `t`. Writing
`K = ∑_{h=0}^m K_h(x) t^h`, its kernel coefficients `W_j(K) = (m - j)! K_{m-j}(x)` are the
coefficients of `𝓡^{(m)}_K` written in terms of `U`, its derivatives and its antiderivative
in `t`.

## Main definitions

* `MvPolynomial.elementaryKernel`: the kernel `K_m(z, t) = ∑_{j=0}^m e_j(z) t^{m-j} / (m-j)!`.
* `MvPolynomial.elementaryKernelApproximant`: the polynomial `e_m(z, t/k, …, t/k)`.
* `MvPolynomial.higherKernelOperator`: the `R`-linear operator `U ↦ ∂_t^m (U * K)`.
* `MvPolynomial.kernelCoeff`: the linear map `K ↦ W_j(K) = (m - j)! K_{m-j}`.

## Implementation notes

The paper works over `ℝ` in `ℝ[x, t]`. Here the variables are `Option σ`: the variable `t` is
`X none` and `x_i` is `X (some i)`, as for `MvPolynomial.quadraticKernel`, so `e_j(z)` is
embedded by `rename some`, and `∂_t` is `MvPolynomial.pderiv none`. The coefficient `K_h(x)` of
`t^h` is read off through `MvPolynomial.optionEquivLeft`, which views `K` as a polynomial in `t`
with coefficients in the variables `x`.

Each definition is made under the weakest hypotheses on the scalars it needs: the elementary
kernel and its approximants need the inverses of `(m - j)!` and of `k`, so live over a
semifield, with `t^{m-j} / (m-j)!` written `C ((m-j)!)⁻¹ * t^{m-j}`; the higher kernel operator
needs a `ℚ`-algebra, the base of `MvPolynomial.tConvolution`; the kernel coefficients need only
a commutative semiring. The `r + k` variables of `e_m(z, w_1, …, w_k)` are `σ ⊕ Fin k`, and the
substitution `z_i ↦ z_i`, `w_l ↦ t/k` is `MvPolynomial.aeval` of `Sum.elim`.

The paper assumes `m ≥ 1` and `k ≥ 1`, a `t`-degree bound on `K` and `j ≤ m`; none of these is
needed to define the objects. In particular `K_0 = 1`, `f_{m,0} = e_m(z)`, and for `j > m` the
truncated subtraction gives `m - j = 0`, a value of `W_j` the paper does not use.

## References

* [LogNarayana]
-/

namespace MvPolynomial

section Semifield

variable (σ : Type*) (R : Type*) [Fintype σ] [Semifield R]

end Semifield

section QAlgebra

variable {σ : Type*} {R : Type*} [CommSemiring R] [Algebra ℚ R]

end QAlgebra

section CommSemiring

variable {σ : Type*} {R : Type*} [CommSemiring R]

end CommSemiring

end MvPolynomial

