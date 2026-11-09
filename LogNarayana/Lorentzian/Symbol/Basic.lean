/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module
public import LogNarayana.Lorentzian.Hessian.Defs
public import LogNarayana.Lorentzian.Symbol.Defs
public import LogNarayana.AuxiliaryDefinitions

/-!
# Lorentzian-preserving operators, cited from the literature

This file records four results from the literature on linear operators that preserve Lorentzian
polynomials in `ℝ[z_i : i ∈ σ]`. Each is stated as a proposition, to be taken as a hypothesis by
the results that use it.

* The symbol theorem of Brändén–Huh [BH, Theorem 3.2]: let `κ : σ →₀ ℕ`, `ℓ : ℤ`, and let
  `T : ℝ_κ[z_i : i ∈ σ] → ℝ[x_j : j ∈ τ]` be a linear operator that is homogeneous of degree `ℓ`.
  If the algebraic symbol `Sym_κ(T)(x, w)` is Lorentzian, then `T f` is Lorentzian for every
  Lorentzian `f ∈ ℝ_κ[z]`.
* For the full factorial normalization `𝓔 : z^α ↦ z^α / α!`, if `𝓔(f)` and `𝓔(g)` are
  Lorentzian, then so is `𝓔(fg)` [BH, Corollary 3.8].
* For a finite M-convex set `J` of multi-indices, the normalized support polynomial
  `E_J(z) = ∑_{α ∈ J} z^α / α!` is Lorentzian; this is the implication (7) ⇒ (4) of
  [BH, Theorem 3.10].
* For a Lorentzian `F` and a variable `t ∈ σ`, the antiderivative `∫₀ᵗ F ds` with respect to
  `z_t`, vanishing at `z_t = 0`, is Lorentzian [RSW, Corollary 5.9].

## Main definitions

* `MvPolynomial.BrandenHuhSymbolTheorem σ τ`: the statement of [BH, Theorem 3.2] for operators
  from polynomials in the variables `σ` to polynomials in the variables `τ`.
* `MvPolynomial.FullFactorialNormalizationMulLorentzian σ`: the full factorial normalization of a
  product is Lorentzian whenever the normalizations of the factors are.
* `MvPolynomial.NormalizedSupportPolyLorentzianOfMConvex σ`: the normalized support polynomial of
  every M-convex set is Lorentzian.
* `MvPolynomial.AntiderivativeLorentzian σ`: the antiderivative `MvPolynomial.antiderivative t`
  with respect to any variable `t` preserves the Lorentzian property.

## Implementation notes

The space `ℝ_κ[z]` is `MvPolynomial.restrictSupport ℝ (Set.Iic κ)`, homogeneity of an operator
is `MvPolynomial.IsHomogeneousOperator`, and the symbol is `MvPolynomial.algebraicSymbol`, a
polynomial in `MvPolynomial (τ ⊕ σ) ℝ`. The variable types are finite, as
`MvPolynomial.IsLorentzian` requires, and each proposition is indexed by them so that it can be
assumed for exactly the types at which it is used.

An M-convex set is finite by `Set.IsMConvex`, so `J` is taken as a `Finset` and its M-convexity
is asked of its underlying set.

## References

* [BH] P. Brändén, J. Huh, *Lorentzian polynomials*, Ann. of Math. 192 (2020).
* [RSW] J. Ross, H. Süss, T. Wannerer, *Dually Lorentzian polynomials*, Monatsh. Math. 208
  (2025), 495–524.
-/

@[expose] public section

namespace MvPolynomial

/-- **Ross–Süss–Wannerer** [RSW, Corollary 5.9]: for a finite variable type `σ`, a variable
`t : σ` and a Lorentzian polynomial `f ∈ ℝ[z_i : i ∈ σ]`, the antiderivative
`MvPolynomial.antiderivative t f` is Lorentzian. -/
@[lognarayana "thm_ext_rsw_antiderivative"]
def AntiderivativeLorentzian (σ : Type*) [Fintype σ] : Prop :=
  ∀ (t : σ) (f : MvPolynomial σ ℝ), f.IsLorentzian → (antiderivative t f).IsLorentzian

end MvPolynomial

end
