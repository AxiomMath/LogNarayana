/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib
public import LogNarayana.Attr
public import LogNarayana.Matroid.BasePolytope.Defs
public import LogNarayana.Nestohedron.Fertilitope.Defs
public import LogNarayana.Lorentzian.Hessian.Defs
public import LogNarayana.Lorentzian.Symbol.Defs
public import LogNarayana.Polynomial.LogConcave.Defs
public import LogNarayana.Matroid.BasisGeneratingPolynomial.Defs
public import LogNarayana.Narayana.Polynomials.Defs
public import LogNarayana.Polynomial.RealStable.Defs
public import LogNarayana.Narayana.Transform.Defs
public import LogNarayana.Lorentzian.Symbol.Basic
public import LogNarayana.Polynomial.LogConcave.Basic
public import LogNarayana.Matroid.BasisGeneratingPolynomial.Basic
public import LogNarayana.Narayana.Polynomials.Basic
public import LogNarayana.Polynomial.RealStable.Basic
public import LogNarayana.Lorentzian.Bivariate
public import LogNarayana.Narayana.RealRootedTransform.Basic
public import LogNarayana.Narayana.Transform.Basic

/-!
# Narayana sums on matroid base polytopes

Let `M` be a matroid on a finite type `α` and `a : α → ℕ`. The lattice points of the translated
base polytope `𝟏 + a + P_M` are the vectors `𝟏 + a + 𝟏_B`, `B` a base of `M`, so the Narayana sum
`∑_{q ∈ (𝟏 + a + P_M) ∩ ℤ^α} ∏ᵢ N_{qᵢ}(x)` is `x^{|α|} F_{M,a}(x, 1)`, where `F_{M,a}` is the
matroid Narayana polynomial.

The polynomial `F_{M,a}` is the image of the basis generating polynomial `B_M` under the matroid
Narayana operator `T_a`, whose symbol factors as
`∏_i (hom(Ñ_{a_i + 1})(x, y) + w_i hom(Ñ_{a_i})(x, y))`. Each factor is real-stable: the zeros of
`Ñ_m` and `Ñ_{m+1}` interlace, the pencil of two interlacing real-rooted polynomials is
real-stable (by a partial fraction argument), and homogenization preserves real stability. So the
symbol is Lorentzian, and by the Brändén–Huh symbol theorem `F_{M,a}` is Lorentzian; its
dehomogenization `F_{M,a}(x, 1)` is ultra-log-concave, and the Narayana sum is log-concave. When
`B_M` is real-stable, `F_{M,a}(x, 1)` is the Narayana transform of `z^a B_M`, hence real-rooted,
and so is the Narayana sum.

## Main results

* `Polynomial.aeval_div_aeval_prod_X_sub_C_eq_sum`: partial fractions over distinct real roots.
* `MvPolynomial.isRealStable_prod_X_sub_C_add_X_mul_prod_X_sub_C`: interlacing pencils are
  real-stable.
* `MvPolynomial.isRealStable_aeval_shiftedNarayanaPolynomial_add_X_mul`: `Ñ_{m+1} + u Ñ_m` is
  real-stable.
* `MvPolynomial.isRealStable_rename_homogShiftedNarayanaPolynomial_add_X_mul`: its
  homogenization `hom(Ñ_{m+1}) + u hom(Ñ_m)` is real-stable.
* `MvPolynomial.algebraicSymbol_matroidNarayanaOperator`: the factorization of the symbol of
  `T_a`.
* `MvPolynomial.isLorentzian_algebraicSymbol_matroidNarayanaOperator`: the symbol is Lorentzian.
* `Matroid.isHomogeneous_narayanaPolynomial`: `F_{M,a}` is homogeneous of degree `|a| + k`.
* `Matroid.isLorentzian_narayanaPolynomial`: `F_{M,a}` is Lorentzian (Proposition 8.1).
* `Matroid.isUltraLogConcave_aeval_narayanaPolynomial`: `F_{M,a}(x, 1)` is ultra-log-concave.
* `Matroid.splits_aeval_narayanaPolynomial`: `F_{M,a}(x, 1)` is real-rooted when `B_M` is
  real-stable.
* `Matroid.latticePoints_basePolytope`, `Matroid.latticePoints_translate_basePolytope`: the
  lattice points of `P_M` and of `𝟏 + a + P_M`.
* `Matroid.finsum_latticePoints_prod_narayanaPolynomial`: the Narayana sum is
  `x^{|α|} F_{M,a}(x, 1)`.
* `Matroid.isLogConcave_finsum_latticePoints_prod_narayanaPolynomial`: the Narayana sum is
  log-concave.
* `Matroid.splits_finsum_latticePoints_prod_narayanaPolynomial`: the Narayana sum is real-rooted
  when `B_M` is real-stable.

## Implementation notes

The ground set `[r]` is generalized to an arbitrary finite type `α`, and the hypothesis `r ≥ 1`
is dropped throughout. The rank of `M` is given, where it enters a statement, as
`M.eRank = k`. Real-rootedness is `Polynomial.Splits`, and the substitution `y = 1` is
`MvPolynomial.aeval ![Polynomial.X, 1]`, with `x = X 0` and `y = X 1`. The cited results the
proofs rest on (real roots and interlacing of the shifted Narayana polynomials, homogenization of
real-stable polynomials, the Brändén–Huh criteria and the Borcea–Brändén symbol theorem) are
taken as hypotheses; the γ-expansion of `Ñ_m` is proved
(`shiftedNarayanaGammaExpansion_holds`).

## References

* [LogNarayana], Section 8 and Proposition 8.1.
* [BH] P. Brändén, J. Huh, *Lorentzian polynomials*, Proposition 2.2 and Corollary 3.9.
-/

/-! ### Partial fractions over distinct real roots -/

section PartialFraction

open Polynomial

/-- Partial fraction decomposition of `h / nodal s v` over a field, for `deg h < #s`. -/
private lemma eval_div_eval_nodal_eq_sum {F ι : Type*} [Field F] {s : Finset ι}
    {v : ι → F} (hv : Set.InjOn v s) {h : F[X]} (hh : h.degree < s.card) {x : F}
    (hx : (Lagrange.nodal s v).eval x ≠ 0) :
    h.eval x / (Lagrange.nodal s v).eval x =
      ∑ i ∈ s, h.eval (v i) / ((derivative (Lagrange.nodal s v)).eval (v i) * (x - v i)) := by
  classical
  have hxv : ∀ i ∈ s, x ≠ v i := fun i hi hxi =>
    hx (hxi ▸ Lagrange.eval_nodal_at_node hi)
  conv_lhs => rw [Lagrange.eq_interpolate hv hh]
  rw [Lagrange.eval_interpolate_not_at_node _ hxv, mul_div_cancel_left₀ _ hx]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Lagrange.nodalWeight_eq_eval_derivative_nodal hi, div_eq_mul_inv, mul_inv]
  ring

private lemma map_prod_X_sub_C_eq_nodal {m : ℕ} (ρ : Fin m → ℝ) :
    (∏ j, (X - C (ρ j))).map (algebraMap ℝ ℂ) =
      Lagrange.nodal Finset.univ (fun j => (ρ j : ℂ)) := by
  simp [Lagrange.nodal, Polynomial.map_prod]

private lemma ofReal_eval_eq_eval_map (p : ℝ[X]) (x : ℝ) :
    ((p.eval x : ℝ) : ℂ) = (p.map (algebraMap ℝ ℂ)).eval (x : ℂ) := by
  rw [eval_map, ← Complex.coe_algebraMap, eval₂_at_apply]

end PartialFraction


section

open Polynomial

namespace Polynomial

/-- Partial fraction decomposition of `h / ∏ⱼ (X - ρⱼ)` over distinct real roots `ρⱼ`,
for `deg h < m`, evaluated at a complex point `ζ` off the roots. -/
@[lognarayana "lem_partial_fraction_distinct_roots"]
public theorem aeval_div_aeval_prod_X_sub_C_eq_sum {m : ℕ} (ρ : Fin m → ℝ)
    (hρ : Function.Injective ρ) (h : ℝ[X]) (hh : h.degree < m) (ζ : ℂ)
    (hζ : aeval ζ (∏ j, (X - C (ρ j))) ≠ 0) :
    aeval ζ h / aeval ζ (∏ j, (X - C (ρ j))) =
      ∑ j, ((h.eval (ρ j) : ℝ) : ℂ) /
        ((((derivative (∏ i, (X - C (ρ i)))).eval (ρ j) : ℝ) : ℂ) * (ζ - (ρ j : ℂ))) := by
  simp only [← eval_map_algebraMap, ofReal_eval_eq_eval_map, ← derivative_map,
    map_prod_X_sub_C_eq_nodal] at hζ ⊢
  exact eval_div_eval_nodal_eq_sum (fun i _ j _ hij => hρ (Complex.ofReal_injective hij))
    (by simpa using hh) hζ

end Polynomial

end

/-! ### Interlacing pencils are real-stable -/

section Interlacing

open Finset Polynomial

/-- A real product is `(-1)` to the number of its negative factors times the product of the
absolute values. -/
private lemma prod_eq_neg_one_pow_mul_prod_abs {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ∏ i ∈ s, f i = (-1) ^ #{i ∈ s | f i < 0} * ∏ i ∈ s, |f i| := by
  have : ∀ i ∈ s, f i = (if f i < 0 then -1 else 1) * |f i| := by
    intro i _
    split_ifs with h
    · rw [abs_of_neg h]; ring
    · rw [abs_of_nonneg (not_lt.1 h)]; ring
  rw [prod_congr rfl this, prod_mul_distrib, prod_ite, prod_const, prod_const, one_pow, mul_one]

/-- A strictly interlacing chain `θ₁ < ρ₁ < θ₂ < ⋯ < ρₘ < θₘ₊₁` is strictly increasing in both
its families. -/
private lemma strictMono_of_interlacing {m : ℕ} {θ : Fin (m + 1) → ℝ} {ρ : Fin m → ℝ}
    (hθρ : ∀ i : Fin m, θ i.castSucc < ρ i) (hρθ : ∀ i : Fin m, ρ i < θ i.succ) :
    StrictMono θ ∧ StrictMono ρ := by
  have hθ : StrictMono θ := Fin.strictMono_iff_lt_succ.2 fun i => (hθρ i).trans (hρθ i)
  refine ⟨hθ, fun i k hik => ((hρθ i).trans_le (hθ.monotone ?_)).trans (hθρ k)⟩
  rw [Fin.le_def]; simp; omega

/-- Under strict interlacing, `f(ρⱼ) g'(ρⱼ) < 0`. -/
private lemma eval_mul_eval_derivative_neg {m : ℕ} (θ : Fin (m + 1) → ℝ) (ρ : Fin m → ℝ)
    (hθρ : ∀ i : Fin m, θ i.castSucc < ρ i) (hρθ : ∀ i : Fin m, ρ i < θ i.succ) (j : Fin m) :
    (∏ i, (X - C (θ i))).eval (ρ j) * (derivative (∏ i, (X - C (ρ i)))).eval (ρ j) < 0 := by
  obtain ⟨hθ, hρ⟩ := strictMono_of_interlacing hθρ hρθ
  have h1 : ∀ i : Fin (m + 1), j.castSucc < i → ρ j < θ i := fun i hi =>
    (hρθ j).trans_le (hθ.monotone (Fin.castSucc_lt_iff_succ_le.1 hi))
  have h2 : ∀ i : Fin (m + 1), ¬ j.castSucc < i → θ i < ρ j := fun i hi =>
    (hθ.monotone (not_lt.1 hi)).trans_lt (hθρ j)
  rw [show (∏ i, (X - C (ρ i))) = Lagrange.nodal univ ρ from rfl,
    Lagrange.eval_nodal_derivative_eval_node_eq (mem_univ j), Lagrange.eval_nodal]
  simp only [eval_prod, eval_sub, eval_X, eval_C]
  rw [prod_eq_neg_one_pow_mul_prod_abs univ (fun i => ρ j - θ i),
    prod_eq_neg_one_pow_mul_prod_abs (univ.erase j) (fun i => ρ j - ρ i)]
  have hA : {i ∈ (univ : Finset (Fin (m + 1))) | ρ j - θ i < 0} = Ioi j.castSucc := by
    ext i
    simp only [mem_filter, mem_univ, true_and, sub_neg, mem_Ioi]
    exact ⟨fun h => not_not.1 fun hc => (h2 i hc).not_gt h, h1 i⟩
  have hB : {i ∈ univ.erase j | ρ j - ρ i < 0} = Ioi j := by
    ext i
    simp only [mem_filter, mem_erase, mem_univ, and_true, sub_neg, mem_Ioi]
    exact ⟨fun h => hρ.lt_iff_lt.1 h.2, fun hi => ⟨hi.ne', hρ hi⟩⟩
  have hP : 0 < ∏ i, |ρ j - θ i| := prod_pos fun i _ => abs_pos.2 <| sub_ne_zero.2 <| by
    by_cases hi : j.castSucc < i
    · exact (h1 i hi).ne
    · exact (h2 i hi).ne'
  have hQ : 0 < ∏ i ∈ univ.erase j, |ρ j - ρ i| := prod_pos fun i hi => abs_pos.2 <|
    sub_ne_zero.2 <| hρ.injective.ne (mem_erase.1 hi).1.symm
  rw [hA, hB, Fin.card_Ioi, Fin.card_Ioi, Fin.val_castSucc,
    show m + 1 - 1 - (j : ℕ) = (m - 1 - j) + 1 by omega, pow_succ]
  nlinarith [mul_pos hP hQ, show ((-1 : ℝ) ^ (m - 1 - (j : ℕ))) * (-1) ^ (m - 1 - (j : ℕ)) = 1 by
    rw [← mul_pow]; simp]

/-- A summand `a / (b (ζ - ρ))` with `a b ≤ 0` has nonnegative imaginary part for `Im ζ > 0`. -/
private lemma im_div_mul_sub_nonneg (a b ρ : ℝ) (hab : a * b ≤ 0) (z : ℂ) (hz : 0 < z.im) :
    0 ≤ ((a : ℂ) / ((b : ℂ) * (z - ρ))).im := by
  rw [Complex.div_im]
  simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im, Complex.sub_re,
    Complex.sub_im, zero_mul, zero_div, zero_sub, add_zero]
  rw [neg_nonneg]
  apply div_nonpos_of_nonpos_of_nonneg _ (Complex.normSq_nonneg _)
  nlinarith

/-- A real-rooted polynomial does not vanish on the upper half-plane. -/
private lemma aeval_prod_X_sub_C_ne_zero {m : ℕ} (ρ : Fin m → ℝ) {z : ℂ} (hz : 0 < z.im) :
    aeval z (∏ j, (X - C (ρ j))) ≠ 0 := by
  simp only [map_prod, map_sub, aeval_X, aeval_C, prod_ne_zero_iff, sub_ne_zero]
  intro j _ h
  simp [h] at hz

/-- For strictly interlacing `f` and `g` and `Im z > 0`, `Im (f(z) / g(z)) ≥ Im z`. -/
private lemma im_le_im_aeval_div_aeval {m : ℕ} (θ : Fin (m + 1) → ℝ) (ρ : Fin m → ℝ)
    (hθρ : ∀ i : Fin m, θ i.castSucc < ρ i) (hρθ : ∀ i : Fin m, ρ i < θ i.succ)
    {z : ℂ} (hz : 0 < z.im) :
    z.im ≤ (aeval z (∏ i, (X - C (θ i))) / aeval z (∏ j, (X - C (ρ j)))).im := by
  set F : ℝ[X] := ∏ i, (X - C (θ i))
  set G : ℝ[X] := ∏ j, (X - C (ρ j))
  have hF : F.Monic := monic_prod_of_monic _ _ fun i _ => monic_X_sub_C _
  have hG : G.Monic := monic_prod_of_monic _ _ fun i _ => monic_X_sub_C _
  have hFdeg : F.natDegree = m + 1 := by
    rw [natDegree_prod_of_monic _ _ fun i _ => monic_X_sub_C _]; simp
  have hGdeg : G.natDegree = m := by
    rw [natDegree_prod_of_monic _ _ fun i _ => monic_X_sub_C _]; simp
  have hGz := aeval_prod_X_sub_C_ne_zero ρ hz
  have hdiv : F %ₘ G + G * (F /ₘ G) = F := modByMonic_add_div F G
  -- The quotient `q = F /ₘ G` is monic of degree one, so `Im q(z) = Im z`.
  have hq : (F /ₘ G).Monic := by
    rw [Monic, leadingCoeff_divByMonic_of_monic hG (by
      rw [degree_eq_natDegree hG.ne_zero, degree_eq_natDegree hF.ne_zero, hGdeg, hFdeg]
      exact_mod_cast Nat.le_succ m), hF.leadingCoeff]
  have hqim : (aeval z (F /ₘ G)).im = z.im := by
    rw [hq.eq_X_add_C (by rw [natDegree_divByMonic F hG, hFdeg, hGdeg]; omega)]; simp
  -- The remainder `h = F %ₘ G` has the partial fraction expansion over the roots of `G`.
  have hpf := aeval_div_aeval_prod_X_sub_C_eq_sum ρ (strictMono_of_interlacing hθρ hρθ).2.injective
    _ (by simpa [degree_eq_natDegree hG.ne_zero, hGdeg] using degree_modByMonic_lt F hG) z hGz
  conv_rhs => rw [← hdiv, map_add, map_mul, add_div, mul_div_cancel_left₀ _ hGz, hpf,
    Complex.add_im, Complex.im_sum, hqim]
  refine le_add_of_nonneg_left (sum_nonneg fun j _ => im_div_mul_sub_nonneg _ _ _ ?_ z hz)
  have hev := congrArg (eval (ρ j)) hdiv
  rw [eval_add, eval_mul,
    show G.eval (ρ j) = 0 by rw [eval_prod]; exact prod_eq_zero (mem_univ j) (by simp),
    zero_mul, add_zero] at hev
  rw [hev]
  exact (eval_mul_eval_derivative_neg θ ρ hθρ hρθ j).le

end Interlacing

namespace MvPolynomial

/-- If `θ₁ < ρ₁ < θ₂ < ⋯ < ρₘ < θₘ₊₁`, then `∏ᵢ (x - θᵢ) + u ∏ⱼ (x - ρⱼ)` is real-stable,
with `x = X 0` and `u = X 1`. -/
@[lognarayana "lem_interlacing_pencil_real_stable"]
public theorem isRealStable_prod_X_sub_C_add_X_mul_prod_X_sub_C {m : ℕ}
    (θ : Fin (m + 1) → ℝ) (ρ : Fin m → ℝ)
    (hθρ : ∀ i : Fin m, θ i.castSucc < ρ i) (hρθ : ∀ i : Fin m, ρ i < θ i.succ) :
    (∏ i, (X 0 - C (θ i)) + X 1 * ∏ j, (X 0 - C (ρ j)) :
      MvPolynomial (Fin 2) ℝ).IsRealStable := by
  intro ζ hζ
  have hG := aeval_prod_X_sub_C_ne_zero ρ (hζ 0)
  have him := im_le_im_aeval_div_aeval θ ρ hθρ hρθ (hζ 0)
  simp only [map_add, map_mul, map_prod, map_sub, aeval_X, aeval_C, Polynomial.aeval_X,
    Polynomial.aeval_C] at hG him ⊢
  intro h
  rw [show _ / _ = -ζ 1 by rw [div_eq_iff hG]; linear_combination h, Complex.neg_im] at him
  linarith [hζ 0, hζ 1]

end MvPolynomial

/-! ### Shifted Narayana pencils are real-stable -/

section ShiftedPencil

open Polynomial

/-- A monic real polynomial of degree `n` whose negative zeros form a set of cardinality `n`
factors as `∏ (X - C (ρ i))` over a strictly increasing family `ρ` of its zeros. -/
private theorem exists_strictMono_eq_prod {p : ℝ[X]} {n : ℕ} (hp : p.IsMonicOfDegree n)
    (hS : {ρ : ℝ | ρ < 0 ∧ p.IsRoot ρ}.encard = n) :
    ∃ ρ : Fin n → ℝ, StrictMono ρ ∧ (∀ i, p.IsRoot (ρ i)) ∧ p = ∏ i, (X - C (ρ i)) := by
  have hfin := Set.finite_of_encard_eq_coe hS
  have hcard : hfin.toFinset.card = n := by
    rw [hfin.encard_eq_coe_toFinset_card] at hS; exact_mod_cast hS
  set ρ := hfin.toFinset.orderEmbOfFin hcard
  have hroot (i) : p.IsRoot (ρ i) :=
    (hfin.mem_toFinset.mp (hfin.toFinset.orderEmbOfFin_mem hcard i)).2
  refine ⟨ρ, ρ.strictMono, hroot, ?_⟩
  rcases eq_or_ne n 0 with rfl | hn
  · simp [isMonicOfDegree_zero_iff.mp hp]
  have hq : (∏ i, (X - C (ρ i))).IsMonicOfDegree n :=
    ⟨by simp [natDegree_prod_of_monic _ _ fun i _ => monic_X_sub_C (ρ i)], monic_prod_X_sub_C _ _⟩
  rw [← sub_eq_zero]
  refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ ρ.injective (fun i => ?_)
    (by simpa using hp.natDegree_sub_lt hn hq)
  simp [(hroot i).eq_zero, eval_prod, Finset.prod_eq_zero_iff, sub_eq_zero]

end ShiftedPencil

namespace MvPolynomial

/-- For every `m`, `Ñ_{m+1}(x) + u Ñ_m(x)` is real-stable, with `x = X 0` and `u = X 1`. -/
@[lognarayana "lem_shifted_narayana_pencil_real_stable"]
public theorem isRealStable_aeval_shiftedNarayanaPolynomial_add_X_mul
    (hRR : ShiftedNarayanaNegRealRoots) (hInt : ShiftedNarayanaInterlacing) (m : ℕ) :
    (Polynomial.aeval (X 0) (shiftedNarayanaPolynomial (m + 1)) +
        X 1 * Polynomial.aeval (X 0) (shiftedNarayanaPolynomial m) :
      MvPolynomial (Fin 2) ℝ).IsRealStable := by
  obtain ⟨ρ, hρ, hρr, hρe⟩ :=
    exists_strictMono_eq_prod (isMonicOfDegree_shiftedNarayanaPolynomial m) (hRR m)
  obtain ⟨θ, hθ, hθr, hθe⟩ :=
    exists_strictMono_eq_prod (isMonicOfDegree_shiftedNarayanaPolynomial (m + 1)) (hRR (m + 1))
  have h := hInt m ρ θ hρ hθ hρr hθr
  rw [hρe, hθe]
  simpa [Polynomial.aeval_prod] using
    MvPolynomial.isRealStable_prod_X_sub_C_add_X_mul_prod_X_sub_C θ ρ (fun i => (h i).1)
      (fun i => (h i).2)

end MvPolynomial

/-! ### Homogenized shifted Narayana pencils are real-stable -/

section HomogPencil

open MvPolynomial

private lemma homogenize_eq_sum_of_subset {σ : Type*} (f : MvPolynomial σ ℝ) (D : ℕ)
    {s : Finset (σ →₀ ℕ)} (hs : f.support ⊆ s) :
    f.homogenize D = ∑ α ∈ s, if α.degree ≤ D then
      monomial (α.mapDomain Option.some + Finsupp.single none (D - α.degree)) (f.coeff α)
      else 0 := by
  rw [homogenize, Finset.sum_filter]
  exact Finset.sum_subset hs fun α _ hα => by simp [notMem_support_iff.mp hα]

private lemma homogenize_add {σ : Type*} (f g : MvPolynomial σ ℝ) (D : ℕ) :
    (f + g).homogenize D = f.homogenize D + g.homogenize D := by
  classical
  rw [homogenize_eq_sum_of_subset (f + g) D (support_add (p := f) (q := g)),
    homogenize_eq_sum_of_subset f D Finset.subset_union_left,
    homogenize_eq_sum_of_subset g D Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun α _ => ?_
  split_ifs <;> simp [coeff_add]

private lemma homogenize_sum {σ ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ ℝ) (D : ℕ) :
    (∑ i ∈ s, f i).homogenize D = ∑ i ∈ s, (f i).homogenize D := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [homogenize]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, homogenize_add, ih]

private lemma homogenize_monomial {σ : Type*} (α : σ →₀ ℕ) (c : ℝ) (D : ℕ) (h : α.degree ≤ D) :
    (monomial α c).homogenize D =
      monomial (α.mapDomain Option.some + Finsupp.single none (D - α.degree)) c := by
  classical
  rw [homogenize_eq_sum_of_subset _ D (support_monomial_subset (a := c)),
    Finset.sum_singleton, if_pos h, coeff_monomial, if_pos rfl]

/-- The coefficients of `Ñ_n`. -/
private noncomputable abbrev cf (n j : ℕ) : ℝ :=
  ((n + 1 : ℕ) : ℝ)⁻¹ * ((n + 1).choose (j + 1) : ℝ) * ((n + 1).choose j : ℝ)

private lemma cf_nonneg (n j : ℕ) : 0 ≤ cf n j := by positivity

/-- `X 1 ^ k * Ñ_n(X 0)` as a sum of monomials. -/
private lemma X_pow_mul_aeval (n k : ℕ) :
    (X 1 ^ k * Polynomial.aeval (X 0) (shiftedNarayanaPolynomial n) : MvPolynomial (Fin 2) ℝ) =
      ∑ j ∈ Finset.range (n + 1),
        monomial (Finsupp.single 0 j + Finsupp.single 1 k) (cf n j) := by
  simp only [shiftedNarayanaPolynomial, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, Polynomial.aeval_C, Polynomial.aeval_X_pow, algebraMap_eq, X_pow_eq_monomial,
    X_pow_eq_monomial, C_mul_monomial, monomial_mul, add_comm (Finsupp.single (1 : Fin 2) k),
    mul_one, one_mul]

/-- The variable map `Option (Fin 2) → Fin 3`. -/
private def φ : Option (Fin 2) → Fin 3 := fun o => o.elim 1 ![0, 2]

private lemma rename_homogenize (n k : ℕ) :
    rename φ ((X 1 ^ k * Polynomial.aeval (X 0) (shiftedNarayanaPolynomial n) :
      MvPolynomial (Fin 2) ℝ).homogenize (n + k)) =
      X 2 ^ k * rename Fin.castSucc (homogShiftedNarayanaPolynomial n) := by
  rw [X_pow_mul_aeval, homogenize_sum, map_sum, homogShiftedNarayanaPolynomial,
    shiftedNarayanaPolynomial, Polynomial.homogenize_finsetSum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [homogenize_monomial _ _ _ (by simp [map_add]; omega), rename_monomial,
    Polynomial.homogenize_C_mul, Polynomial.homogenize_X_pow hj]
  simp only [map_mul, map_pow, rename_X, rename_C]
  simp only [X_pow_eq_monomial, monomial_mul, map_add,
    Finsupp.degree_single, Finsupp.mapDomain_add, Finsupp.mapDomain_single]
  rw [← map_mul, ← map_mul, C_mul_monomial, monomial_mul, one_mul, mul_one, mul_one,
    show φ (some 0) = 0 from rfl, show φ (some 1) = 2 from rfl, show φ none = 1 from rfl,
    show (Fin.castSucc 0 : Fin 3) = 0 from rfl, show (Fin.castSucc 1 : Fin 3) = 1 from rfl,
    Nat.add_sub_add_right]
  congr 1
  rw [add_right_comm, add_comm]

private lemma totalDegree_X_pow_mul_aeval (n k : ℕ) :
    (X 1 ^ k * Polynomial.aeval (X 0) (shiftedNarayanaPolynomial n) :
      MvPolynomial (Fin 2) ℝ).totalDegree ≤ n + k := by
  rw [X_pow_mul_aeval]
  refine totalDegree_finsetSum_le fun j hj => (totalDegree_monomial_le _ _).trans ?_
  have hj : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [Finsupp.sum_add_index' (by simp) (by simp), Finsupp.sum_single_index rfl,
    Finsupp.sum_single_index rfl]
  simpa using hj

private lemma coeff_X_pow_mul_aeval_nonneg (n k : ℕ) (α : Fin 2 →₀ ℕ) :
    0 ≤ (X 1 ^ k * Polynomial.aeval (X 0) (shiftedNarayanaPolynomial n) :
      MvPolynomial (Fin 2) ℝ).coeff α := by
  rw [X_pow_mul_aeval, coeff_sum]
  exact Finset.sum_nonneg fun j _ => by
    rw [coeff_monomial]; split_ifs
    · exact cf_nonneg n j
    · exact le_rfl

/-- The pencil `Ñ_{m+1}(x) + u Ñ_m(x)` over `Fin 2`, with `x = X 0` and `u = X 1`. -/
private noncomputable abbrev pencil (m : ℕ) : MvPolynomial (Fin 2) ℝ :=
  Polynomial.aeval (X 0) (shiftedNarayanaPolynomial (m + 1)) +
    X 1 * Polynomial.aeval (X 0) (shiftedNarayanaPolynomial m)

/-- The degree `m + 1` homogenization of the pencil, renamed into `Fin 3`, is
`hom(Ñ_{m+1})(x, y) + u hom(Ñ_m)(x, y)`. -/
private lemma rename_homogenize_pencil (m : ℕ) :
    rename φ ((pencil m).homogenize (m + 1)) =
      rename Fin.castSucc (homogShiftedNarayanaPolynomial (m + 1)) +
        X 2 * rename Fin.castSucc (homogShiftedNarayanaPolynomial m) := by
  have e1 := rename_homogenize (m + 1) 0
  have e2 := rename_homogenize m 1
  simp only [pow_zero, one_mul, pow_one, add_zero] at e1 e2
  rw [homogenize_add, map_add, e1, e2]

private lemma totalDegree_pencil_le (m : ℕ) : (pencil m).totalDegree ≤ m + 1 :=
  (totalDegree_add _ _).trans <| max_le
    (by simpa using totalDegree_X_pow_mul_aeval (m + 1) 0)
    (by simpa using totalDegree_X_pow_mul_aeval m 1)

private lemma coeff_pencil_nonneg (m : ℕ) (α : Fin 2 →₀ ℕ) : 0 ≤ (pencil m).coeff α := by
  rw [coeff_add]
  exact add_nonneg (by simpa using coeff_X_pow_mul_aeval_nonneg (m + 1) 0 α)
    (by simpa using coeff_X_pow_mul_aeval_nonneg m 1 α)

end HomogPencil

namespace MvPolynomial

/-- For every `m`, `hom(Ñ_{m+1})(x, y) + u hom(Ñ_m)(x, y)` is real-stable, with `x = X 0`,
`y = X 1` and `u = X 2`. -/
@[lognarayana "lem_homog_shifted_narayana_pencil_real_stable"]
public theorem isRealStable_rename_homogShiftedNarayanaPolynomial_add_X_mul
    (hRR : ShiftedNarayanaNegRealRoots) (hInt : ShiftedNarayanaInterlacing)
    (hHom : ∀ σ : Type, IsRealStableHomogenizeOfNonneg σ) (m : ℕ) :
    (rename Fin.castSucc (homogShiftedNarayanaPolynomial (m + 1)) +
        X 2 * rename Fin.castSucc (homogShiftedNarayanaPolynomial m) :
      MvPolynomial (Fin 3) ℝ).IsRealStable :=
  rename_homogenize_pencil m ▸
    (IsRealStableHomogenizeOfNonneg.isRealStable_homogenize_of_totalDegree_le (hHom (Fin 2))
      (coeff_pencil_nonneg m) (isRealStable_aeval_shiftedNarayanaPolynomial_add_X_mul hRR hInt m)
      (totalDegree_pencil_le m)).rename φ

end MvPolynomial

/-! ### The symbol of the matroid Narayana operator -/

section OperatorSymbol

open MvPolynomial

/-- Expanding a product of binomials: `∏_i (f_i 0 + f_i 1)` is the sum over `β ≤ 𝟙` of
`∏_i f_i (β_i)`. -/
private lemma prod_add_eq_sum_Iic_one {α R : Type*} [Fintype α] [DecidableEq α]
    [CommSemiring R] (f : α → ℕ → R) :
    ∏ i, (f i 0 + f i 1) =
      ∑ β ∈ Finset.Iic (Finsupp.equivFunOnFinite.symm 1 : α →₀ ℕ), ∏ i, f i (β i) := by
  have h : ∀ i, f i 0 + f i 1 = ∑ j ∈ Finset.range 2, f i j := fun i => by
    simp [Finset.sum_range_succ]
  simp_rw [h, Finset.prod_univ_sum]
  refine (Finset.sum_nbij' (fun β : α →₀ ℕ => ⇑β) (fun g => Finsupp.equivFunOnFinite.symm g)
    ?_ ?_ (by simp) (by simp) (fun _ _ => rfl)).symm
  · intro β hβ
    simp only [Finset.mem_Iic] at hβ
    simpa [Nat.lt_succ_iff] using fun i => hβ i
  · intro g hg
    simp only [Fintype.mem_piFinset, Finset.mem_range] at hg
    simpa [Finsupp.le_def, Nat.lt_succ_iff] using hg

private lemma choose_eq_one_of_le_one {α : Type*} [Finite α] {β : α →₀ ℕ}
    (hβ : β ≤ Finsupp.equivFunOnFinite.symm 1) :
    (Finsupp.equivFunOnFinite.symm 1 : α →₀ ℕ).choose β = 1 := by
  refine Finset.prod_eq_one fun i _ => ?_
  have := hβ i
  simp only [Finsupp.equivFunOnFinite_symm_apply_apply, Pi.one_apply] at this ⊢
  interval_cases h : β i <;> simp

/-- `T_a(z^β) = ∏_i hom(Ñ_{a_i + β_i})`. -/
private lemma matroidNarayanaOperator_monomial {α : Type*} [Fintype α] (a : α → ℕ)
    {β : α →₀ ℕ} (hβ) :
    matroidNarayanaOperator a ⟨monomial β 1, hβ⟩ =
      ∏ i, homogShiftedNarayanaPolynomial (a i + β i) := by
  rw [matroidNarayanaOperator, LinearMap.domRestrict_apply]
  change ((basisMonomials α ℝ).constr ℝ _) (monomial β 1) = _
  rw [← congrFun (coe_basisMonomials α ℝ) β, Module.Basis.constr_basis]

end OperatorSymbol

section

open Polynomial

/-- The algebraic symbol `Sym_𝟙(T_a)` of the matroid Narayana operator is
`∏_i (hom(Ñ_{a_i + 1})(x, y) + w_i hom(Ñ_{a_i})(x, y))`, where `x, y` are the variables
`X (Sum.inl j)` and `w_i = X (Sum.inr i)`. -/
@[lognarayana "lem_matroid_narayana_operator_symbol"]
public theorem MvPolynomial.algebraicSymbol_matroidNarayanaOperator {α : Type*} [Fintype α]
    (a : α → ℕ) :
    algebraicSymbol (Finsupp.equivFunOnFinite.symm 1) (matroidNarayanaOperator a) =
      ∏ i, (rename Sum.inl (homogShiftedNarayanaPolynomial (a i + 1)) +
        X (Sum.inr i) * rename Sum.inl (homogShiftedNarayanaPolynomial (a i))) := by
  classical
  have hR : ∀ i, rename Sum.inl (homogShiftedNarayanaPolynomial (a i + 1)) +
      X (Sum.inr i) * rename Sum.inl (homogShiftedNarayanaPolynomial (a i)) =
        (rename Sum.inl (homogShiftedNarayanaPolynomial (a i + 0)) * X (Sum.inr i) ^ (1 - 0) +
        rename Sum.inl (homogShiftedNarayanaPolynomial (a i + 1)) * X (Sum.inr i) ^ (1 - 1) :
          MvPolynomial (Fin 2 ⊕ α) ℝ) := fun i => by
    simp [mul_comm, add_comm]
  rw [Finset.prod_congr rfl fun i _ => hR i, prod_add_eq_sum_Iic_one
    (fun i j => rename Sum.inl (homogShiftedNarayanaPolynomial (a i + j)) *
      X (Sum.inr i) ^ (1 - j)),
    algebraicSymbol, ← Finset.sum_attach (Finset.Iic _)]
  refine Finset.sum_congr rfl ?_
  rintro ⟨β, hβ⟩ -
  rw [choose_eq_one_of_le_one (Finset.mem_Iic.1 hβ), matroidNarayanaOperator_monomial,
    Nat.cast_one, C_1, one_mul, monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (by simp),
    map_prod, map_prod, ← Finset.prod_mul_distrib]
  simp

end

/-! ### The symbol of the matroid Narayana operator is Lorentzian -/

section SymbolLorentzian

open MvPolynomial

variable {τ : Type*}

/-- The real polynomials with nonnegative coefficients form a subsemiring. -/
private def nonnegCoeffs (τ : Type*) : Subsemiring (MvPolynomial τ ℝ) where
  carrier := {f | f.HasNonnegCoeffs}
  zero_mem' _ := by simp
  one_mem' α := by classical rw [coeff_one]; split_ifs <;> simp
  add_mem' hf hg α := by rw [coeff_add]; exact add_nonneg (hf α) (hg α)
  mul_mem' hf hg α := by
    classical
    rw [coeff_mul]; exact Finset.sum_nonneg fun _ _ => mul_nonneg (hf _) (hg _)

private lemma X_mem_nonnegCoeffs (i : τ) : X i ∈ nonnegCoeffs τ := fun α => by
  classical
  rw [coeff_X]; split_ifs <;> simp

private lemma rename_mem_nonnegCoeffs {υ : Type*} {g : τ → υ} (hg : Function.Injective g)
    {f : MvPolynomial τ ℝ} (hf : f ∈ nonnegCoeffs τ) : rename g f ∈ nonnegCoeffs υ := by
  intro α
  classical
  by_cases h : ∃ u : τ →₀ ℕ, u.mapDomain g = α
  · obtain ⟨u, rfl⟩ := h
    rw [coeff_rename_mapDomain g hg]; exact hf u
  · rw [coeff_rename_eq_zero g f α fun u hu => (h ⟨u, hu⟩).elim]

private lemma homogShiftedNarayanaPolynomial_mem_nonnegCoeffs (m : ℕ) :
    homogShiftedNarayanaPolynomial m ∈ nonnegCoeffs (Fin 2) := fun β => by
  rw [Polynomial.coeff_homogenize]
  split_ifs
  · rw [shiftedNarayanaPolynomial, Polynomial.finsetSum_coeff]
    exact Finset.sum_nonneg fun j _ => by
      rw [Polynomial.coeff_C_mul_X_pow]; split_ifs <;> positivity
  · exact le_rfl

private lemma isRealStable_prod {ι : Type*} (s : Finset ι) {f : ι → MvPolynomial τ ℝ}
    (hf : ∀ i ∈ s, (f i).IsRealStable) : (∏ i ∈ s, f i).IsRealStable := by
  classical
  induction s using Finset.induction_on with
  | empty => intro ζ _; simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact (hf a (Finset.mem_insert_self _ _)).mul
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-- The `i`-th factor of the symbol is real-stable: it is the three-variable pencil
`hom(Ñ_{m+1})(x, y) + u hom(Ñ_m)(x, y)` with `u` renamed to `w_i`. -/
private lemma isRealStable_symbol_factor (hRR : ShiftedNarayanaNegRealRoots)
    (hInt : ShiftedNarayanaInterlacing) (hHom : ∀ σ : Type, IsRealStableHomogenizeOfNonneg σ)
    {α : Type} (i : α) (m : ℕ) :
    (rename Sum.inl (homogShiftedNarayanaPolynomial (m + 1)) +
      X (Sum.inr i) * rename Sum.inl (homogShiftedNarayanaPolynomial m) :
        MvPolynomial (Fin 2 ⊕ α) ℝ).IsRealStable := by
  have hc : (![Sum.inl 0, Sum.inl 1, Sum.inr i] : Fin 3 → Fin 2 ⊕ α) ∘ Fin.castSucc =
      Sum.inl := by
    funext j; fin_cases j <;> rfl
  simpa [rename_rename, hc] using
    (isRealStable_rename_homogShiftedNarayanaPolynomial_add_X_mul hRR hInt hHom m).rename
      (![Sum.inl 0, Sum.inl 1, Sum.inr i] : Fin 3 → Fin 2 ⊕ α)

end SymbolLorentzian

/-- For every finite `α` and `a : α → ℕ`, the algebraic symbol `Sym_𝟙(T_a)` of the matroid
Narayana operator is Lorentzian. -/
@[lognarayana "lem_matroid_narayana_symbol_lorentzian"]
public theorem MvPolynomial.isLorentzian_algebraicSymbol_matroidNarayanaOperator
    (hRR : ShiftedNarayanaNegRealRoots) (hInt : ShiftedNarayanaInterlacing)
    (hHom : ∀ σ : Type, IsRealStableHomogenizeOfNonneg σ)
    {α : Type} [Fintype α] (hLor : IsLorentzianOfRealStable (Fin 2 ⊕ α)) (a : α → ℕ) :
    (algebraicSymbol (Finsupp.equivFunOnFinite.symm 1)
      (matroidNarayanaOperator a)).IsLorentzian := by
  rw [algebraicSymbol_matroidNarayanaOperator]
  have hN (m : ℕ) := rename_mem_nonnegCoeffs (υ := Fin 2 ⊕ α) Sum.inl_injective
    (homogShiftedNarayanaPolynomial_mem_nonnegCoeffs m)
  refine hLor _ ⟨∑ i, (a i + 1), ?_⟩
    (isRealStable_prod _ fun i _ => isRealStable_symbol_factor hRR hInt hHom i (a i))
    (Subsemiring.prod_mem _ fun i _ =>
      add_mem (hN _) (mul_mem (X_mem_nonnegCoeffs _) (hN _)))
  refine IsHomogeneous.prod _ _ _ fun i _ => .add ?_ ?_
  · exact (Polynomial.isHomogeneous_homogenize _).rename_isHomogeneous
  · rw [add_comm]
    exact (isHomogeneous_X _ _).mul (Polynomial.isHomogeneous_homogenize _).rename_isHomogeneous

/-! ### Homogeneity of the matroid Narayana polynomial -/

/-- Every base of a matroid of rank `k` has `k` elements. -/
private lemma card_eq_of_isBase {α : Type*} {M : Matroid α} {k : ℕ} (hk : M.eRank = k)
    {B : Finset α} (hB : M.IsBase (B : Set α)) : B.card = k := by
  have := hB.encard_eq_eRank
  rw [Set.encard_coe_eq_coe_finsetCard, hk] at this
  exact_mod_cast this

/-- Raising each exponent on `B` by one adds `#B` to the total. -/
private lemma sum_add_one_add_sum_compl {α : Type*} [Fintype α] [DecidableEq α]
    (B : Finset α) (a : α → ℕ) :
    ∑ i ∈ B, (a i + 1) + ∑ i ∈ Bᶜ, a i = ∑ i, a i + B.card := by
  rw [Finset.sum_add_distrib, add_right_comm, Finset.sum_add_sum_compl]
  simp

/-- The matroid Narayana polynomial `F_{M,a}` of a matroid `M` of rank `k` is homogeneous of
degree `∑ i, a i + k`. -/
@[lognarayana "lem_matroid_narayana_homogeneous"]
public theorem Matroid.isHomogeneous_narayanaPolynomial {α : Type*} [Fintype α]
    (M : Matroid α) {k : ℕ} (hk : M.eRank = k) (a : α → ℕ) :
    (M.narayanaPolynomial a).IsHomogeneous (∑ i, a i + k) := by
  classical
  refine MvPolynomial.IsHomogeneous.sum _ _ _ fun B hB => ?_
  rw [← card_eq_of_isBase hk (by simpa using hB), ← sum_add_one_add_sum_compl]
  exact (MvPolynomial.IsHomogeneous.prod _ _ _ fun i _ =>
      Polynomial.isHomogeneous_homogenize _).mul
    (MvPolynomial.IsHomogeneous.prod _ _ _ fun i _ => Polynomial.isHomogeneous_homogenize _)

/-! ### Matroid Narayana polynomials are Lorentzian -/

section MatroidLorentzian

open MvPolynomial

variable {α : Type*} [Fintype α]

/-- `T_a` is homogeneous of degree `|a| = ∑ a_i`. -/
private lemma isHomogeneousOperator_matroidNarayanaOperator (a : α → ℕ) :
    IsHomogeneousOperator (Finsupp.equivFunOnFinite.symm 1) (∑ i, a i : ℕ)
      (matroidNarayanaOperator a) := by
  rintro β _ ⟨f, hmem⟩ rfl _
  refine ⟨∑ i, (a i + β i), ?_, ?_⟩
  · rw [Finset.sum_add_distrib, Finsupp.degree_eq_sum]
    push_cast; ring
  · rw [matroidNarayanaOperator_monomial]
    exact IsHomogeneous.prod _ _ _ fun i _ => Polynomial.isHomogeneous_homogenize _

omit [Fintype α] in
/-- The square-free monomial `z^B` is multiaffine. -/
private lemma prod_X_mem_restrictSupport [Finite α] (B : Finset α) :
    (∏ e ∈ B, X e : MvPolynomial α ℝ) ∈
      restrictSupport ℝ (Set.Iic (Finsupp.equivFunOnFinite.symm 1)) := by
  classical
  simp only [X, ← monomial_sum_one]
  refine (monomial_mem_restrictSupport ℝ).2 (Or.inl fun i => ?_)
  simp only [Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply,
    Finset.sum_ite_eq', Finsupp.equivFunOnFinite_symm_apply_apply, Pi.one_apply]
  split_ifs <;> simp

/-- `T_a(z^B) = ∏_{i ∈ B} hom(Ñ_{a_i + 1}) ∏_{i ∉ B} hom(Ñ_{a_i})`. -/
private lemma matroidNarayanaOperator_prod_X [DecidableEq α] (a : α → ℕ) (B : Finset α) :
    matroidNarayanaOperator a ⟨_, prod_X_mem_restrictSupport B⟩ =
      (∏ i ∈ B, homogShiftedNarayanaPolynomial (a i + 1)) *
        ∏ i ∈ Bᶜ, homogShiftedNarayanaPolynomial (a i) := by
  have hX : (∏ e ∈ B, X e : MvPolynomial α ℝ) = monomial (∑ e ∈ B, Finsupp.single e 1) 1 := by
    simp [X, ← monomial_sum_one]
  rw [show (⟨_, prod_X_mem_restrictSupport B⟩ :
      restrictSupport ℝ (Set.Iic (Finsupp.equivFunOnFinite.symm 1))) =
      ⟨_, hX ▸ prod_X_mem_restrictSupport B⟩ from Subtype.ext hX,
    matroidNarayanaOperator_monomial, ← Finset.prod_mul_prod_compl B]
  congr 1 <;> refine Finset.prod_congr rfl fun i hi => ?_
  · simp [Finsupp.single_apply, hi]
  · simp [Finsupp.single_apply, Finset.mem_compl.1 hi]

/-- `T_a` sends the basis generating polynomial `B_M` to the matroid Narayana polynomial
`F_{M,a}`. -/
private theorem matroidNarayanaOperator_basisGeneratingPolynomial (M : Matroid α) (a : α → ℕ) :
    matroidNarayanaOperator a ⟨M.basisGeneratingPolynomial ℝ,
      Submodule.sum_mem _ fun B _ => prod_X_mem_restrictSupport B⟩ = M.narayanaPolynomial a := by
  classical
  have hsum : (⟨M.basisGeneratingPolynomial ℝ,
      Submodule.sum_mem _ fun B _ => prod_X_mem_restrictSupport B⟩ :
        restrictSupport ℝ (Set.Iic (Finsupp.equivFunOnFinite.symm 1))) =
      ∑ B ∈ Finset.univ.filter (fun B : Finset α => M.IsBase (B : Set α)),
        ⟨_, prod_X_mem_restrictSupport B⟩ :=
    Subtype.ext (by simp [Matroid.basisGeneratingPolynomial])
  rw [hsum, map_sum, Matroid.narayanaPolynomial]
  exact Finset.sum_congr rfl fun B _ => matroidNarayanaOperator_prod_X a B

end MatroidLorentzian

/-- **Matroid Narayana polynomials are Lorentzian** [LogNarayana, Proposition 8.1]: for a matroid
`M` on a finite type `α` and `a : α → ℕ`, `M.narayanaPolynomial a` is Lorentzian. -/
@[lognarayana "prop_matroid_narayana_lorentzian"]
public theorem Matroid.isLorentzian_narayanaPolynomial
    (hRR : ShiftedNarayanaNegRealRoots) (hInt : ShiftedNarayanaInterlacing)
    (hHom : ∀ σ : Type, IsRealStableHomogenizeOfNonneg σ)
    {α : Type} [Fintype α] (hLor : IsLorentzianOfRealStable (Fin 2 ⊕ α))
    (hBH : MvPolynomial.NormalizedSupportPolyLorentzianOfMConvex α)
    (hSym : MvPolynomial.BrandenHuhSymbolTheorem α (Fin 2))
    (M : Matroid α) (a : α → ℕ) :
    (M.narayanaPolynomial a).IsLorentzian :=
  matroidNarayanaOperator_basisGeneratingPolynomial M a ▸
    hSym _ _ _ (isHomogeneousOperator_matroidNarayanaOperator a)
      (MvPolynomial.isLorentzian_algebraicSymbol_matroidNarayanaOperator hRR hInt hHom hLor a) _
      (M.isLorentzian_basisGeneratingPolynomial hBH)

/-! ### Ultra-log-concavity at `y = 1` -/

section ULC

open Polynomial

/-- A Lorentzian polynomial has nonnegative coefficients. -/
private lemma hasNonnegCoeffs_of_isLorentzian {σ R : Type*} [Fintype σ] [CommRing R]
    [PartialOrder R] {F : MvPolynomial σ R} (hF : F.IsLorentzian) : F.HasNonnegCoeffs := by
  rcases hF with rfl | ⟨-, -, h, -⟩
  · simp [MvPolynomial.HasNonnegCoeffs]
  · exact h

/-- If the degree-`d` homogenization of `f` (with `deg f ≤ d`) has nonnegative coefficients,
so does `f`. -/
private lemma coeff_nonneg_of_hasNonnegCoeffs_homogenize {R : Type*} [CommRing R]
    [PartialOrder R] {f : R[X]} {d : ℕ} (hdeg : f.natDegree ≤ d)
    (h : (f.homogenize d).HasNonnegCoeffs) (i : ℕ) : 0 ≤ f.coeff i := by
  by_cases hi : i ≤ d
  · have := h (Finsupp.single 0 i + Finsupp.single 1 (d - i))
    simp only [coeff_homogenize, Finsupp.add_apply, Finsupp.single_apply] at this
    simpa [Nat.add_sub_cancel' hi] using this
  · rw [coeff_eq_zero_of_natDegree_lt (by omega)]

end ULC

/-- **Ultra-log-concavity at `y = 1`** [LogNarayana, Proposition 8.1]: for a matroid `M` of rank
`k` on a finite type `α` and `a : α → ℕ`, `F_{M,a}(x, 1)` is ultra-log-concave of order
`∑ i, a i + k`. -/
@[lognarayana "prop_matroid_narayana_ulc"]
public theorem Matroid.isUltraLogConcave_aeval_narayanaPolynomial
    (hRR : ShiftedNarayanaNegRealRoots) (hInt : ShiftedNarayanaInterlacing)
    (hHom : ∀ σ : Type, IsRealStableHomogenizeOfNonneg σ)
    {α : Type} [Fintype α] (hLor : IsLorentzianOfRealStable (Fin 2 ⊕ α))
    (hBH : MvPolynomial.NormalizedSupportPolyLorentzianOfMConvex α)
    (hSym : MvPolynomial.BrandenHuhSymbolTheorem α (Fin 2))
    (M : Matroid α) {k : ℕ} (hk : M.eRank = k) (a : α → ℕ) :
    (MvPolynomial.aeval ![(Polynomial.X : Polynomial ℝ), 1]
      (M.narayanaPolynomial a)).IsUltraLogConcave (∑ i, a i + k) := by
  have hF := M.isHomogeneous_narayanaPolynomial hk a
  have hL := M.isLorentzian_narayanaPolynomial hRR hInt hHom hLor hBH hSym a
  have hhom := Polynomial.homogenize_eq_of_isHomogeneous hF rfl
  have hdeg : (MvPolynomial.aeval ![(Polynomial.X : Polynomial ℝ), 1]
      (M.narayanaPolynomial a)).natDegree ≤ ∑ i, a i + k := by
    simpa using MvPolynomial.aeval_natDegree_le _ hF.totalDegree_le _ (n := 1)
      (fun i => by fin_cases i <;> simp)
  rw [← Polynomial.isLorentzian_homogenize_iff_isUltraLogConcave
    (coeff_nonneg_of_hasNonnegCoeffs_homogenize hdeg
      (by rw [hhom]; exact hasNonnegCoeffs_of_isLorentzian hL)) hdeg, hhom]
  exact hL

/-! ### Real-rootedness at `y = 1` -/

section RealRooted

open MvPolynomial Polynomial

variable {α : Type*} [Fintype α]

open Classical in
/-- The exponent `a + 1_B`. -/
private noncomputable def shiftExp (a : α → ℕ) (B : Finset α) : α →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i => a i + if i ∈ B then 1 else 0

open Classical in
private lemma shiftExp_apply (a : α → ℕ) (B : Finset α) (i : α) :
    shiftExp a B i = a i + if i ∈ B then 1 else 0 := rfl

open Classical in
/-- `z^a B_M = ∑_B z^{a + 1_B}`. -/
private lemma monomial_mul_basisGeneratingPolynomial (M : Matroid α) (a : α → ℕ) :
    monomial (Finsupp.equivFunOnFinite.symm a) 1 * M.basisGeneratingPolynomial ℝ =
      ∑ B ∈ Finset.univ.filter (fun B : Finset α => M.IsBase (B : Set α)),
        monomial (shiftExp a B) 1 := by
  rw [Matroid.basisGeneratingPolynomial, Finset.mul_sum]
  refine Finset.sum_congr rfl fun B _ => ?_
  rw [show ∏ e ∈ B, (X e : MvPolynomial α ℝ) = monomial (∑ e ∈ B, Finsupp.single e 1) 1 by
    simp [MvPolynomial.X, ← monomial_sum_one], monomial_mul, one_mul]
  refine congrArg (MvPolynomial.monomial · (1 : ℝ)) (Finsupp.ext fun i => ?_)
  simp [shiftExp_apply, Finsupp.single_apply]

/-- A monomial with coefficient `1` is real-stable. -/
private lemma isRealStable_monomial_one {σ : Type*} (β : σ →₀ ℕ) :
    (monomial β (1 : ℝ)).IsRealStable := fun ζ hζ => by
  rw [MvPolynomial.aeval_monomial, map_one, one_mul]
  exact Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ fun h => by simpa [h] using hζ i

open Classical in
/-- `∑_B z^{a + 1_B}` is homogeneous of degree `∑ a + |B₀|` for any base `B₀`. -/
private lemma isHomogeneous_sum_monomial_shiftExp {M : Matroid α} (a : α → ℕ) {B₀ : Finset α}
    (hB₀ : M.IsBase (B₀ : Set α)) :
    (∑ B ∈ Finset.univ.filter (fun B : Finset α => M.IsBase (B : Set α)),
      monomial (shiftExp a B) (1 : ℝ)).IsHomogeneous (∑ i, a i + B₀.card) := by
  refine IsHomogeneous.sum _ _ _ fun B hB => isHomogeneous_monomial _ ?_
  rw [Finset.mem_filter] at hB
  simpa [Finsupp.degree_eq_sum, shiftExp_apply, Finset.sum_add_distrib, Finset.sum_boole,
    Set.ncard_coe_finset] using hB.2.ncard_eq_ncard_of_isBase hB₀

open Classical in
/-- The Narayana transform of `∑_B z^{a + 1_B}` is `F_{M,a}(x, 1)`. -/
private lemma narayanaTransform_sum_monomial_shiftExp (M : Matroid α) (a : α → ℕ) :
    narayanaTransform α (∑ B ∈ Finset.univ.filter (fun B : Finset α => M.IsBase (B : Set α)),
      monomial (shiftExp a B) (1 : ℝ)) =
      aeval ![(X : ℝ[X]), 1] (M.narayanaPolynomial a) := by
  have hom (m : ℕ) : aeval ![(X : ℝ[X]), 1] (homogShiftedNarayanaPolynomial m) =
      shiftedNarayanaPolynomial m :=
    aeval_homogenize_X_one _ (isMonicOfDegree_shiftedNarayanaPolynomial m).natDegree_eq.le
  rw [map_sum, Matroid.narayanaPolynomial, map_sum]
  refine Finset.sum_congr rfl fun B _ => ?_
  rw [narayanaTransform_monomial, one_smul,
    Finsupp.prod_fintype _ _ fun _ => shiftedNarayanaPolynomial_zero, map_mul, map_prod, map_prod,
    ← Finset.prod_mul_prod_compl B]
  congr 1 <;> refine Finset.prod_congr rfl fun i hi => ?_
  · rw [hom, shiftExp_apply, if_pos hi]
  · rw [hom, shiftExp_apply, if_neg (Finset.mem_compl.mp hi), add_zero]

end RealRooted

/-- **Real-rootedness for real-stable matroids** [LogNarayana, Proposition 8.1]: for a matroid
`M` on a finite type `α` and `a : α → ℕ`, if the basis generating polynomial `B_M` is
real-stable, then `F_{M,a}(x, 1)` is real-rooted. -/
@[lognarayana "prop_matroid_narayana_real_rooted"]
public theorem Matroid.splits_aeval_narayanaPolynomial.{u}
    (hBB : ∀ τ : Type u, RealStablePreserverOfSymbol τ)
    (hLW : ShiftedNarayanaNegRealRoots)
    {α : Type u} [Fintype α] (M : Matroid α) (a : α → ℕ)
    (hB : (M.basisGeneratingPolynomial ℝ).IsRealStable) :
    (MvPolynomial.aeval ![(Polynomial.X : Polynomial ℝ), 1]
      (M.narayanaPolynomial a)).Splits := by
  classical
  have hGst := monomial_mul_basisGeneratingPolynomial M a ▸
    (isRealStable_monomial_one _).mul hB
  obtain ⟨B₀, hB₀⟩ := M.exists_isBase
  rw [← narayanaTransform_sum_monomial_shiftExp]
  refine MvPolynomial.splits_narayanaTransform_of_isRealStable hBB hLW
    (isHomogeneous_sum_monomial_shiftExp a (B₀ := (Set.toFinite B₀).toFinset) (by simpa))
    hGst fun β => ?_
  rw [MvPolynomial.coeff_sum]
  exact Finset.sum_nonneg fun B _ => by rw [MvPolynomial.coeff_monomial]; split_ifs <;> norm_num

/-! ### Lattice points of base polytopes -/

section LatticePoints

open Set

/-- Every indicator vector lies in the unit cube. -/
private lemma indicator_one_mem_cube {α : Type*} (B : Set α) :
    B.indicator (1 : α → ℝ) ∈ univ.pi fun _ => Icc (0 : ℝ) 1 := fun i _ => by
  by_cases hi : i ∈ B <;> simp [hi]

/-- A lattice point of the unit cube is an extreme point of the cube. -/
private lemma latticePoints_cube_subset_extremePoints {α : Type*} :
    (univ.pi fun _ : α => Icc (0 : ℝ) 1).latticePoints ⊆
      (univ.pi fun _ : α => Icc (0 : ℝ) 1).extremePoints ℝ := by
  rintro q ⟨hq, hint⟩
  rw [extremePoints_pi]
  intro i _
  obtain ⟨n, hn⟩ := hint i
  obtain ⟨h0, h1⟩ := hq i (mem_univ _)
  rw [extremePoints_Icc zero_le_one, ← hn] at *
  have : (0 : ℤ) ≤ n := by exact_mod_cast h0
  have : n ≤ 1 := by exact_mod_cast h1
  interval_cases n <;> simp

end LatticePoints

/-- The lattice points of the base polytope of a matroid `M` are exactly the indicator vectors
`𝟏_B` of the bases `B` of `M`. -/
@[lognarayana "lem_base_polytope_lattice_points"]
public theorem Matroid.latticePoints_basePolytope {α : Type*} (M : Matroid α) :
    (M.basePolytope ℝ).latticePoints =
      (fun B : Set α => B.indicator (1 : α → ℝ)) '' {B | M.IsBase B} := by
  have hPC : M.basePolytope ℝ ⊆ Set.univ.pi fun _ => Set.Icc (0 : ℝ) 1 :=
    convexHull_min (by rintro _ ⟨B, -, rfl⟩; exact indicator_one_mem_cube B)
      (convex_pi fun _ _ => convex_Icc 0 1)
  refine Set.Subset.antisymm (fun q hq => extremePoints_convexHull_subset
    (inter_extremePoints_subset_extremePoints_of_subset hPC
      ⟨hq.1, latticePoints_cube_subset_extremePoints ⟨hPC hq.1, hq.2⟩⟩)) ?_
  rintro _ ⟨B, hB, rfl⟩
  refine ⟨subset_convexHull ℝ _ ⟨B, hB, rfl⟩, fun i => ?_⟩
  by_cases hi : i ∈ B
  · exact ⟨1, by simp [hi]⟩
  · exact ⟨0, by simp [hi]⟩

/-- Translating by an integer vector commutes with taking lattice points. -/
private lemma latticePoints_image_add_left {R ι : Type*} [Ring R] (P : Set (ι → R))
    {c : ι → R} (hc : ∀ i, c i ∈ Set.range (Int.cast : ℤ → R)) :
    ((c + ·) '' P).latticePoints = (c + ·) '' P.latticePoints := by
  ext q
  constructor
  · rintro ⟨⟨v, hv, rfl⟩, hq⟩
    refine ⟨v, ⟨hv, fun i => ?_⟩, rfl⟩
    obtain ⟨m, hm⟩ := hq i
    obtain ⟨n, hn⟩ := hc i
    exact ⟨m - n, by simp_all⟩
  · rintro ⟨v, ⟨hv, hvi⟩, rfl⟩
    refine ⟨⟨v, hv, rfl⟩, fun i => ?_⟩
    obtain ⟨m, hm⟩ := hvi i
    obtain ⟨n, hn⟩ := hc i
    exact ⟨n + m, by simp_all⟩

/-- The lattice points of the translate `𝟏 + a + P_M` of the base polytope of a matroid `M`
by a nonnegative integer vector `a` are exactly the vectors `𝟏 + a + 𝟏_B`, `B` a base of `M`. -/
@[lognarayana "lem_translated_base_polytope_lattice_points"]
public theorem Matroid.latticePoints_translate_basePolytope {α : Type*} (M : Matroid α)
    (a : α → ℕ) :
    ((fun v : α → ℝ => 1 + (fun i => (a i : ℝ)) + v) '' M.basePolytope ℝ).latticePoints =
      (fun B : Set α => 1 + (fun i => (a i : ℝ)) + B.indicator (1 : α → ℝ)) ''
        {B | M.IsBase B} := by
  rw [latticePoints_image_add_left _ fun i => ⟨1 + a i, by simp⟩,
    M.latticePoints_basePolytope, Set.image_image]

/-! ### The Narayana sum over a translated base polytope -/

section NarayanaSum

open Polynomial

/-- Dehomogenizing `hom_m(Ñ_m)` at `y = 1` recovers `Ñ_m`. -/
private lemma aeval_homogShiftedNarayanaPolynomial (m : ℕ) :
    MvPolynomial.aeval ![(X : ℝ[X]), 1] (homogShiftedNarayanaPolynomial m) =
      shiftedNarayanaPolynomial m :=
  aeval_homogenize_X_one _ (isMonicOfDegree_shiftedNarayanaPolynomial m).natDegree_eq.le

/-- Over a finite type, the sets satisfying `p` are the coercions of the finsets satisfying
`p`. -/
private lemma setOf_eq_image_coe_filter {α : Type*} [Fintype α] (p : Set α → Prop)
    [DecidablePred fun s : Finset α => p ↑s] :
    {B : Set α | p B} =
      (fun s : Finset α => (s : Set α)) '' ↑(Finset.univ.filter fun s : Finset α => p ↑s) := by
  ext B
  simp only [Set.mem_ofPred_eq, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_image]
  exact ⟨fun h => let ⟨s, hs⟩ := B.toFinite.exists_finset_coe; ⟨s, hs ▸ h, hs⟩,
    fun ⟨s, hs, h⟩ => h ▸ hs⟩

/-- The term of the lattice-point sum at the vertex `1 + a + 1_B`: since
`⌊1 + aᵢ + [i ∈ B]⌋₊ = (aᵢ + [i ∈ B]) + 1` and `N_{m+1} = x Ñ_m`, the product of Narayana
polynomials is `x^{|α|}` times the dehomogenized summand of `F_{M,a}` at `B`. -/
private lemma prod_narayanaPolynomial_floor_vertex {α : Type*} [Fintype α] [DecidableEq α]
    (a : α → ℕ) (B : Finset α) :
    ∏ i, narayanaPolynomial ⌊(1 + (fun i => (a i : ℝ)) + (B : Set α).indicator (1 : α → ℝ)) i⌋₊ =
      X ^ Fintype.card α * MvPolynomial.aeval ![(X : ℝ[X]), 1]
        ((∏ i ∈ B, homogShiftedNarayanaPolynomial (a i + 1)) *
          ∏ i ∈ Bᶜ, homogShiftedNarayanaPolynomial (a i)) := by
  have hfloor : ∀ i, ⌊(1 + (fun i => (a i : ℝ)) + (B : Set α).indicator (1 : α → ℝ)) i⌋₊ =
      (a i + if i ∈ B then 1 else 0) + 1 := fun i => by
    rw [← Nat.floor_natCast (R := ℝ) ((a i + if i ∈ B then 1 else 0) + 1)]
    simp only [Pi.add_apply, Pi.one_apply, Set.indicator_apply, Finset.mem_coe]
    split_ifs <;> push_cast <;> ring_nf
  simp only [hfloor, narayanaPolynomial_succ_eq_X_mul, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, map_mul, map_prod, aeval_homogShiftedNarayanaPolynomial,
    ← Finset.prod_mul_prod_compl B (fun i => shiftedNarayanaPolynomial (a i + _))]
  congr 2 <;> refine Finset.prod_congr rfl fun i hi => ?_
  · rw [if_pos hi]
  · rw [if_neg (Finset.mem_compl.mp hi), add_zero]

end NarayanaSum

/-- The sum over the lattice points `q` of the translated base polytope `𝟏 + a + P_M` of the
products `∏ᵢ N_{qᵢ}(x)` of Narayana polynomials equals `x^{|α|} F_{M,a}(x, 1)`. -/
@[lognarayana "lem_base_polytope_narayana_sum_eq"]
public theorem Matroid.finsum_latticePoints_prod_narayanaPolynomial {α : Type*} [Fintype α]
    (M : Matroid α) (a : α → ℕ) :
    (∑ᶠ q ∈ ((fun v : α → ℝ => 1 + (fun i => (a i : ℝ)) + v) '' M.basePolytope ℝ).latticePoints,
        ∏ i, _root_.narayanaPolynomial ⌊q i⌋₊) =
      Polynomial.X ^ Fintype.card α *
        MvPolynomial.aeval ![(Polynomial.X : Polynomial ℝ), 1] (M.narayanaPolynomial a) := by
  classical
  have hinj : Function.Injective fun B : Set α =>
      1 + (fun i => (a i : ℝ)) + B.indicator (1 : α → ℝ) :=
    fun B C h => Set.ext fun i => by
      have := congrFun (add_left_cancel h) i
      by_cases hB : i ∈ B <;> by_cases hC : i ∈ C <;> simp_all
  rw [Matroid.latticePoints_translate_basePolytope, setOf_eq_image_coe_filter, Set.image_image,
    finsum_mem_image fun _ _ _ _ h => Finset.coe_injective (hinj h), finsum_mem_coe_finset,
    Matroid.narayanaPolynomial, map_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun B _ => prod_narayanaPolynomial_floor_vertex a B

/-! ### Log-concavity and real-rootedness of the Narayana sum -/

/-- Multiplying an ultra-log-concave polynomial of order `d` by `X ^ n` gives one of order
`d + n`. -/
private theorem isUltraLogConcave_mul_X_pow {d : ℕ} {f : Polynomial ℝ}
    (hf : f.IsUltraLogConcave d) (n : ℕ) :
    (f * Polynomial.X ^ n).IsUltraLogConcave (d + n) := by
  induction n with
  | zero => simpa using hf
  | succ n ih => simpa [pow_succ, mul_assoc, add_assoc] using ih.mul_X

/-- **Narayana sums on base polytopes are log-concave** [LogNarayana, Section 8]: for a matroid
`M` on a finite type `α` and `a : α → ℕ`, the polynomial
`∑_{q ∈ (𝟏 + a + P_M) ∩ ℤ^α} ∏ i, N_{q i}(x)` is log-concave. -/
@[lognarayana "thm_base_polytope_narayana_lc"]
public theorem Matroid.isLogConcave_finsum_latticePoints_prod_narayanaPolynomial
    (hRR : ShiftedNarayanaNegRealRoots) (hInt : ShiftedNarayanaInterlacing)
    (hHom : ∀ σ : Type, IsRealStableHomogenizeOfNonneg σ)
    {α : Type} [Fintype α] (hLor : IsLorentzianOfRealStable (Fin 2 ⊕ α))
    (hBH : MvPolynomial.NormalizedSupportPolyLorentzianOfMConvex α)
    (hSym : MvPolynomial.BrandenHuhSymbolTheorem α (Fin 2))
    (M : Matroid α) (a : α → ℕ) :
    (∑ᶠ q ∈ ((fun v : α → ℝ => 1 + (fun i => (a i : ℝ)) + v) ''
        M.basePolytope ℝ).latticePoints,
      ∏ i, _root_.narayanaPolynomial ⌊q i⌋₊).IsLogConcave := by
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp (M.eRank_ne_top_iff.2 inferInstance)
  rw [Matroid.finsum_latticePoints_prod_narayanaPolynomial, mul_comm]
  exact (isUltraLogConcave_mul_X_pow (M.isUltraLogConcave_aeval_narayanaPolynomial
    hRR hInt hHom hLor hBH hSym hk.symm a) _).isLogConcave

/-- **Narayana sums on base polytopes are real-rooted** [LogNarayana, Section 8]: for a matroid
`M` on a finite type `α` with real-stable basis generating polynomial and `a : α → ℕ`, the
polynomial `∑_{q ∈ (𝟏 + a + P_M) ∩ ℤ^α} ∏ i, N_{q i}(x)` is real-rooted. -/
@[lognarayana "thm_base_polytope_narayana_real_rooted"]
public theorem Matroid.splits_finsum_latticePoints_prod_narayanaPolynomial.{u}
    (hBB : ∀ τ : Type u, RealStablePreserverOfSymbol τ)
    (hLW : ShiftedNarayanaNegRealRoots)
    {α : Type u} [Fintype α] (M : Matroid α) (a : α → ℕ)
    (hB : (M.basisGeneratingPolynomial ℝ).IsRealStable) :
    (∑ᶠ q ∈ ((fun v : α → ℝ => 1 + (fun i => (a i : ℝ)) + v) ''
        M.basePolytope ℝ).latticePoints,
      ∏ i, _root_.narayanaPolynomial ⌊q i⌋₊).Splits := by
  rw [Matroid.finsum_latticePoints_prod_narayanaPolynomial]
  exact (Polynomial.Splits.X.pow _).mul
    (Matroid.splits_aeval_narayanaPolynomial hBB hLW M a hB)
