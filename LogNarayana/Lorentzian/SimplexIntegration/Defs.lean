/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module
public import LogNarayana.Lorentzian.MConvex.Basic
public import LogNarayana.AuxiliaryDefinitions

/-!
# Integration over a simplex

The definitions documented here are stated in `LogNarayana.Definitions` and
`LogNarayana.AuxiliaryDefinitions`, which this module imports.

For `m ≥ 1`, the simplex integration operator `𝔍_m : R[x, u_1, …, u_m] → R[x, t]` is the linear
map sending each monomial `x^α u^γ` to `γ! / (|γ| + m - 1)! • x^α t^(|γ| + m - 1)`. Over `ℝ`,
evaluated at `(ξ, θ)` with `θ ≥ 0`, it is the integral over the corner simplex `Δ_{m-1}(θ)` of
`G(ξ, s_1, …, s_{m-1}, θ - ∑ s_i)`; this is the Dirichlet integral of a monomial.

The `u`-factor of the algebraic symbol of `𝔍_m` is the polynomial
`Ψ_{m,κ}(t, v) = ∑_{0 ≤ γ ≤ κ} (κ choose γ) · γ! / (|γ| + m - 1)! · t^(|γ| + m - 1) · v^(κ - γ)`,
which is `κ!` times the normalized support polynomial of the M-convex exponent set
`J_{m,κ} = {(|κ| + m - 1 - |β|, β) : 0 ≤ β ≤ κ} ⊆ ℕ^{1+m}`.

## Main definitions

* `Finsupp.jKappa`: the finite set `J_{m,κ}` of exponents in `Option (Fin m) →₀ ℕ`.
* `MvPolynomial.psiKappa`: the polynomial `Ψ_{m,κ}` in `MvPolynomial (Option (Fin m)) R`.
* `MvPolynomial.simplexIntegral`: the `R`-linear map
  `MvPolynomial (σ ⊕ Fin m) R → MvPolynomial (Option σ) R` with
  `x^α u^γ ↦ (γ! / (|γ| + m - 1)!) • x^α t^(|γ| + m - 1)`.
* `cornerSimplex ι θ`: the set `{s : ι → R | (∀ i, 0 ≤ s i) ∧ ∑ i, s i ≤ θ}`.

## Implementation notes

The paper works over `ℝ`. The domain `R[x, u]` of `MvPolynomial.simplexIntegral` is
`MvPolynomial (σ ⊕ Fin m) R`, with `x_j = X (Sum.inl j)` and `u_i = X (Sum.inr i)`; a monomial
exponent splits as `(α, γ)` by `Finsupp.sumFinsuppEquivProdFinsupp`. The codomain `R[x, t]` is
`MvPolynomial (Option σ) R`, with `t = X none` and `x_j = X (some j)`, as for
`MvPolynomial.elementaryKernel`; likewise `Ψ_{m,κ}` and `J_{m,κ}` index `t` by `none` and `v_i`
by `some i`. The operator and `Ψ_{m,κ}` only divide by factorials, so they are defined over any
commutative semiring that is a `ℚ`-algebra, with rational scalars mapped into `R`. The operator
is defined through the monomial basis `MvPolynomial.basisMonomials`, so
`Module.Basis.constr_basis` gives its value on each monomial, which characterises it.

The paper assumes `m ≥ 1`. The definitions are total in `m`: for `m = 0` the exponent
`|γ| - 1` is truncated subtraction and the value has no meaning, while for `m ≥ 1` and `β ≤ κ`
the truncated subtraction `|κ| + m - 1 - |β|` in `J_{m,κ}` is exact. The set `J_{m,κ}` is a
`Finset`, as it is finite and is fed to normalized support polynomials; its coercion to a `Set`
is the set of the paper.

The paper's region is `cornerSimplex (Fin (m - 1)) θ` with `R = ℝ` and `θ ≥ 0`; integrals
over it are with respect to `MeasureTheory.volume` on `Fin (m - 1) → ℝ`, the product of the
one-dimensional Lebesgue measures (`MeasureTheory.volume_pi`). The set makes sense for any
finite index type, any ordered additive commutative monoid of scalars and any `θ`, so none of
the paper's restrictions is imposed.

## References

* [LogNarayana]
-/

namespace Finsupp

end Finsupp

namespace MvPolynomial

variable (σ : Type*) (R : Type*) [CommSemiring R] [Algebra ℚ R]

end MvPolynomial

section

variable (ι : Type*) {R : Type*} [Fintype ι] [AddCommMonoid R] [PartialOrder R]

end

