/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module
public import LogNarayana.Narayana.Transform.Defs

/-!
# The Narayana transform of a finite sum of monomials

For a finite set of variables `σ`, a finite index set `I`, real weights `w_h` and exponents
`β(h) ∈ ℤ_{≥0}^σ`, the Narayana transform of `∑_{h ∈ I} w_h z^{β(h)}` is
`∑_{h ∈ I} w_h ∏_{i ∈ σ} Ñ_{β(h)_i}(x)`.

## Main results

* `MvPolynomial.narayanaTransform_sum_smul_monomial` : the formula above.

## Implementation notes

The identity is stated as an equality of polynomials in `ℝ[X]`, which is equivalent to the
pointwise identity at every real `x` since `ℝ` is infinite.

## References

* [LogNarayana], Section 6.
-/

open Polynomial

namespace MvPolynomial

/-- The Narayana transform of a monomial: `𝒩(c z^α) = c ∏_i Ñ_{α_i}`. -/
public theorem narayanaTransform_monomial {σ : Type*} (α : σ →₀ ℕ) (c : ℝ) :
    narayanaTransform σ (monomial α c) = c • α.prod fun _ k => shiftedNarayanaPolynomial k := by
  rw [← mul_one c, ← smul_eq_mul, ← MvPolynomial.smul_monomial, map_smul,
    ← congrFun (coe_basisMonomials σ ℝ) α, narayanaTransform, Module.Basis.constr_basis,
    smul_eq_mul, mul_one]

/-- The Narayana transform of a finite weighted sum of monomials:
`𝒩(∑_{h ∈ I} w_h z^{β(h)}) = ∑_{h ∈ I} w_h ∏_{i ∈ σ} Ñ_{β(h)_i}`. By linearity this reduces
to a single monomial. -/
@[lognarayana "lem_narayana_transform_finset_sum"]
public theorem narayanaTransform_sum_smul_monomial {σ ι : Type*} [Fintype σ] (I : Finset ι)
    (w : ι → ℝ) (β : ι → σ →₀ ℕ) :
    narayanaTransform σ (∑ h ∈ I, w h • monomial (β h) (1 : ℝ)) =
      ∑ h ∈ I, w h • ∏ i, shiftedNarayanaPolynomial (β h i) := by
  simp only [map_sum, map_smul, narayanaTransform_monomial, one_smul,
    Finsupp.prod_fintype _ (fun _ k => shiftedNarayanaPolynomial k) fun _ => by
      simp [shiftedNarayanaPolynomial]]

end MvPolynomial
