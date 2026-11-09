/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module
public import LogNarayana.Lorentzian.BrandenHuh.Defs
public import LogNarayana.Lorentzian.Hessian.Defs
public import LogNarayana.AuxiliaryDefinitions

/-!
# Properties of Lorentzian polynomials cited from Brändén–Huh

This file records the properties of Lorentzian polynomials in `ℝ[z_i : i ∈ σ]` that are used
from Brändén–Huh [BH]: a coefficientwise limit of Lorentzian polynomials of a fixed degree is
Lorentzian; nonnegative linear substitutions of the variables, nonnegative combinations of
partial derivatives and products preserve the Lorentzian property; and every nonzero derivative
of a Lorentzian polynomial is log-concave on the open positive orthant. Each is stated as a
proposition, to be taken as a hypothesis by the results that use it.

It also proves that a positive function is log-concave exactly when its logarithm is concave,
which translates the last property into the language of `LogConcaveOn`.

## Main definitions

* `MvPolynomial.IsLorentzianClosed`: the Lorentzian polynomials of degree `d` form a closed
  subset of the space of homogeneous polynomials of degree `d` [BH, Theorem 2.25].
* `MvPolynomial.LorentzianNonnegLinearSubstitution`: nonnegative linear substitutions of
  variables preserve the Lorentzian property [BH, Theorem 2.10].
* `MvPolynomial.LorentzianNonnegDerivative`: nonnegative combinations of partial derivatives
  preserve the Lorentzian property [BH, Corollary 2.11].
* `MvPolynomial.LorentzianMul`: the product of two Lorentzian polynomials is Lorentzian
  [BH, Corollary 2.32].
* `MvPolynomial.LorentzianLogConcave`: every nonzero derivative of a Lorentzian polynomial is
  log-concave on the positive orthant [BH, Theorem 2.30].

## Main results

* `logConcaveOn_iff_concaveOn_log`: for `g` positive on `s`, `LogConcaveOn s g` holds iff
  `ConcaveOn ℝ s (Real.log ∘ g)`.
* `MvPolynomial.IsLorentzianClosed.isLorentzian_of_eventually`: an eventually Lorentzian
  homogeneous sequence of degree `d` has a Lorentzian coefficientwise limit.

## Implementation notes

Each cited proposition is parametrized by the finite variable types in use, so that it can be
taken as a hypothesis for exactly those types. `MvPolynomial.IsLorentzianClosed` is the closedness
of `L^d_σ` in the finite-dimensional space `H^d_σ`, stated for sequences converging
coefficientwise; the form with approximants that are only eventually in `L^d_σ` and a limit not
assumed homogeneous is `MvPolynomial.IsLorentzianClosed.isLorentzian_of_eventually`. The partial
derivative `∂_i` is
`MvPolynomial.pderiv i`, the derivative `∂^α` is `MvPolynomial.iteratedPDeriv α`, and the
positive orthant is `Set.univ.pi fun _ ↦ Set.Ioi 0`.

The paper states the log-concavity criterion on a convex subset of `ℝ^σ`; we allow any real
vector space. Both `LogConcaveOn` and `ConcaveOn` include convexity of the domain, so it is not a
hypothesis of `logConcaveOn_iff_concaveOn_log`.

## References

* [BH] P. Brändén, J. Huh, *Lorentzian polynomials*, Ann. of Math. 192 (2020).
-/


/-- For positive reals, the weighted geometric mean `a ^ t * b ^ (1 - t)` is at most `c` iff the
weighted arithmetic mean of the logarithms is at most `log c`. -/
private lemma rpow_mul_rpow_le_iff_log_le {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (t : ℝ) :
    a ^ t * b ^ (1 - t) ≤ c ↔ t * Real.log a + (1 - t) * Real.log b ≤ Real.log c := by
  rw [← Real.log_le_log_iff (by positivity) hc,
    Real.log_mul (by positivity) (by positivity), Real.log_rpow ha, Real.log_rpow hb]

/-- A positive function is log-concave on `s` iff its logarithm is concave on `s`. -/
@[lognarayana "lem_log_concave_function_iff_log"]
public theorem logConcaveOn_iff_concaveOn_log {E : Type*} [AddCommGroup E] [Module ℝ E]
    {s : Set E} {g : E → ℝ} (hg : ∀ x ∈ s, 0 < g x) :
    LogConcaveOn s g ↔ ConcaveOn ℝ s (Real.log ∘ g) := by
  rw [concaveOn_iff_forall_pos]
  constructor
  · rintro ⟨hs, -, h⟩
    refine ⟨hs, fun u hu v hv a b ha hb hab => ?_⟩
    obtain rfl : b = 1 - a := by linarith
    simpa using (rpow_mul_rpow_le_iff_log_le (hg u hu) (hg v hv)
      (hg _ (hs hu hv ha.le hb.le hab)) a).1 (h hu hv ha (by linarith))
  · rintro ⟨hs, h⟩
    refine ⟨hs, fun x hx => (hg x hx).le, fun u hu v hv t ht ht1 => ?_⟩
    rw [rpow_mul_rpow_le_iff_log_le (hg u hu) (hg v hv)
      (hg _ (hs hu hv ht.le (by linarith) (by ring))) t]
    simpa using h hu hv ht (by linarith) (by ring)

namespace MvPolynomial

open Filter Topology

@[expose] public section

/-- **Brändén–Huh** [BH, Theorem 2.30, (3) ⇒ (2)]: for a finite variable type `σ`, a Lorentzian
polynomial `f ∈ ℝ[z_i : i ∈ σ]` and a multi-index `α` with `∂^α f ≠ 0`, the function
`x ↦ log (∂^α f (x))` is concave on the open positive orthant. On that orthant `∂^α f` is
positive, so the logarithm is applied to positive values. -/
@[lognarayana "thm_ext_bh_log_concave"]
def LorentzianLogConcave (σ : Type*) [Fintype σ] : Prop :=
  ∀ f : MvPolynomial σ ℝ, f.IsLorentzian → ∀ α : σ →₀ ℕ, iteratedPDeriv α f ≠ 0 →
    ConcaveOn ℝ (Set.univ.pi fun _ ↦ Set.Ioi 0)
      (fun x : σ → ℝ ↦ Real.log (eval x (iteratedPDeriv α f)))

end

/-- The form of `IsLorentzianClosed` used by the proofs: if the polynomials `F k` are eventually
Lorentzian and homogeneous of degree `d` and converge coefficientwise to `f`, then `f` is
Lorentzian. The limit `f` is homogeneous of degree `d`, since a coefficient of `f` that is
nonzero is eventually a nonzero coefficient of some `F k`; and the shifted sequence
`k ↦ F (k + N)` lies in `L^d_σ` for all `k`. -/
public theorem IsLorentzianClosed.isLorentzian_of_eventually {σ : Type*} [Fintype σ]
    (h : IsLorentzianClosed σ) (d : ℕ) (F : ℕ → MvPolynomial σ ℝ) (f : MvPolynomial σ ℝ)
    (hF : ∀ᶠ k in atTop, (F k).IsLorentzian ∧ (F k).IsHomogeneous d)
    (hlim : ∀ α : σ →₀ ℕ, Tendsto (fun k ↦ (F k).coeff α) atTop (𝓝 (f.coeff α))) :
    f.IsLorentzian := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 hF
  have hf : f.IsHomogeneous d := fun α hα => by
    obtain ⟨k, hk, hkN⟩ := (((hlim α).eventually_ne hα).and (eventually_ge_atTop N)).exists
    exact (hN k hkN).2 hk
  exact h d (fun k => F (k + N)) f (fun k => hN _ (Nat.le_add_left _ _)) hf
    fun α => (hlim α).comp (tendsto_add_atTop_nat N)

end MvPolynomial
