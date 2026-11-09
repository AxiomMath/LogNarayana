/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib
public import LogNarayana.Attr
public import LogNarayana.Forest.OpenPairPolynomial.Defs
public import LogNarayana.Forest.PartialMatching.Defs
public import LogNarayana.Lorentzian.Symbol.Defs
public import LogNarayana.Lorentzian.Convolution.Defs
public import LogNarayana.Lorentzian.Convolution.Basic
public import LogNarayana.StackSorting.Matchings.Defs
public import LogNarayana.Forest.LaminarMatroid.Defs
public import LogNarayana.Forest.Operations.Defs
public import LogNarayana.Forest.Operations.Basic

/-!
# The weighted open-pair polynomial and its recurrences

The operator `δ_t` removes one factor of `t`: `t · δ_t f = f(x, t) - f(x, 0)`. The factorial
normalization `𝓝_t` turns products into derivatives of convolutions,
`𝓝_t (P Q) = ∂_t ((𝓝_t P) * (𝓝_t Q))`, and, for `A, B` free of `t`, intertwines the operator
`P ↦ (A + t) P + B δ_t P` with the root operator:
`𝓝_t((A + t) P + B δ_t P) = 𝓡_{A,B}(𝓝_t P)`.

The vertex-weighted open-pair polynomial `P^{A,B}_{par,L}` of a marked forest obeys two
recurrences. The polynomial of a concatenation of two marked forests is the product of their
polynomials, the second weighted by the shifted families. Adjoining an unmarked root `N + 1`
turns `P` into `(A_{N+1} + t) P + B_{N+1} δ_t P`: the open pairs of the new forest fall into the
classes in which `N + 1` is unmatched and not open, open, or matched to the largest open vertex.
The marked singleton has polynomial `t`. When `A` is homogeneous of degree `1` and `B` of degree
`2`, the weighted open-pair polynomial on `[N]` is homogeneous of degree `N`.

## Main results

* `MvPolynomial.X_mul_divX`: `X t * divX t f = f - f|_{t = 0}`.
* `MvPolynomial.factorialNormalization_mul`: `𝓝_t (P Q) = ∂_t ((𝓝_t P) * (𝓝_t Q))`.
* `MvPolynomial.factorialNormalization_add_X_mul_add_mul_divX`: the normalized root recurrence.
* `isHomogeneous_weightedOpenPairPolynomial`: `P^{A,B}_{par,L}` is homogeneous of degree `N`.
* `vertexWeightedOpenPairPolynomial_markedSingleton`: `P^{A,B}_𝒮(x, t) = t`.
* `vertexWeightedOpenPairPolynomial_forestConcat`: the product formula for a concatenation.
* `vertexWeightedOpenPairPolynomial_forestAdjoinRoot`: the root recurrence.

## Implementation notes

The paper works in `ℝ[x, t]`. For `δ_t` and the factorial normalization the ring is
`MvPolynomial σ R` with `t : σ` one of its variables (or `MvPolynomial (Option σ) R` with
`t = none` where the convolution in `t` is involved), over a commutative ring for subtraction and
a `ℚ`-algebra for the normalization. The substitution `f(x, 0)` is
`aeval (Function.update X t 0) f`, and that `A, B` lie in `ℝ[x]` is expressed as
`t ∉ A.vars`, `t ∉ B.vars`.

For the open-pair polynomials, `R[x, t]` is `MvPolynomial (Option σ) R` with `t = X none`, over
any commutative semiring. The paper states the recurrences for marked postorder forests; they
hold for parent maps `par` on `[N]` with marked sets `L ⊆ [N]`, since neither the postorder
labelling nor the leafness of marked vertices is used. The hypothesis `L' ⊆ [N']` of the
concatenation formula cannot be dropped: a mark `0 ∈ L'` is shifted to `N ∈ [N]`, so with
`N = 1`, `N' = 0`, `L = ∅`, `L' = {0}` and `A = B = 0` the left side is `X none` while the right
side is `0`. Homogeneity needs only that `M` is a partial matching on `[N]` with `O ⊆ U(M)`.

## References

* [LogNarayana] *Log-Concavity in Narayana Transforms and Stack-Sorting Fibers*, Section 7.
-/

namespace MvPolynomial

/-! ### Removing one factor of a variable -/

section DivX

variable {σ : Type*} {R : Type*} [CommRing R] [DecidableEq σ]

omit [DecidableEq σ] in
/-- `δ_t` kills constants. -/
private lemma divX_C (t : σ) (a : R) : divX t (C a : MvPolynomial σ R) = 0 := by
  classical
  ext s
  simp [coeff_C, eq_comm (a := (0 : σ →₀ ℕ))]

omit [DecidableEq σ] in
/-- `δ_t` commutes with multiplication by a variable other than `t`. -/
private lemma divX_mul_X_of_ne {t n : σ} (h : n ≠ t) (p : MvPolynomial σ R) :
    divX t (p * X n) = divX t p * X n := by
  classical
  ext s
  simp only [divX, coeff_divMonomial, coeff_mul_X', Finsupp.mem_support_iff]
  rw [Finsupp.add_apply, Finsupp.single_eq_of_ne h, zero_add]
  split_ifs
  · rw [add_tsub_assoc_of_le (by simpa [Finsupp.single_le_iff, Nat.one_le_iff_ne_zero])]
  · rfl

/-- Multiplying `δ_t f` by `t` gives `f(x, t) - f(x, 0)`. -/
@[lognarayana "lem_t_drop_mul_t"]
public theorem X_mul_divX (t : σ) (f : MvPolynomial σ R) :
    X t * divX t f = f - aeval (Function.update X t 0) f := by
  rw [eq_sub_iff_add_eq]
  induction f using MvPolynomial.induction_on with
  | C a => simp [divX_C]
  | add p q hp hq =>
    simp only [divX, add_divMonomial, map_add] at *
    linear_combination hp + hq
  | mul_X p n hp =>
    by_cases h : n = t
    · subst h
      simp [divX, mul_X_divMonomial, mul_comm]
    · rw [divX_mul_X_of_ne h, map_mul, aeval_X, Function.update_of_ne h]
      linear_combination X n * hp

end DivX

/-! ### Factorial normalization of products and of the root recurrence -/

section FactorialNormalization

variable {σ R : Type*} [CommSemiring R] [Algebra ℚ R]

private lemma tConvolution_add_left (F F' G : MvPolynomial (Option σ) R) :
    tConvolution (F + F') G = tConvolution F G + tConvolution F' G := by
  simp only [tConvolution, map_add, add_mul]

private lemma tConvolution_add_right (F G G' : MvPolynomial (Option σ) R) :
    tConvolution F (G + G') = tConvolution F G + tConvolution F G' := by
  simp only [tConvolution, map_add, mul_add]

private lemma tConvolution_smul_left (c : R) (F G : MvPolynomial (Option σ) R) :
    tConvolution (c • F) G = c • tConvolution F G := by
  simp only [tConvolution, map_smul, smul_mul_assoc]

private lemma tConvolution_smul_right (c : R) (F G : MvPolynomial (Option σ) R) :
    tConvolution F (c • G) = c • tConvolution F G := by
  simp only [tConvolution, map_smul, mul_smul_comm]

/-- An exponent on `Option σ` splits into its `none` part and its `some` part. -/
private lemma single_none_add_mapDomain_some (u : Option σ →₀ ℕ) :
    Finsupp.single none (u none) + u.some.mapDomain some = u := by
  ext (_ | j)
  · simp [Finsupp.mapDomain_of_notMem_range]
  · simp [Finsupp.mapDomain_apply (Option.some_injective σ)]

private lemma single_none_add_mapDomain_some_apply_none (a : ℕ) (α : σ →₀ ℕ) :
    (Finsupp.single none a + α.mapDomain some : Option σ →₀ ℕ) none = a := by
  simp [Finsupp.mapDomain_of_notMem_range]

/-- Lowering the `t`-degree of `x^(α + β) t^(a + b + 1)` by one gives the product exponent of
`x^α t^a` and `x^β t^b`. -/
private lemma single_none_succ_add_mapDomain_some_sub (a b : ℕ) (α β : σ →₀ ℕ) :
    Finsupp.single none (a + b + 1) + (α + β).mapDomain some - Finsupp.single none 1 =
      Finsupp.single none a + α.mapDomain some + (Finsupp.single none b + β.mapDomain some) := by
  ext (_ | j)
  · simp [Finsupp.mapDomain_of_notMem_range]
  · simp [Finsupp.mapDomain_apply (Option.some_injective σ)]

omit [Algebra ℚ R] in
private lemma monomial_eq_smul {τ : Type*} (u : τ →₀ ℕ) (c : R) :
    (monomial u c : MvPolynomial τ R) = c • monomial u 1 := by
  rw [smul_monomial, smul_eq_mul, mul_one]

private lemma factorialNormalization_monomial (t : σ) (α : σ →₀ ℕ) (c : R) :
    factorialNormalization t (monomial α c) =
      monomial α (c * algebraMap ℚ R (1 / ((α t).factorial : ℚ))) := by
  rw [factorialNormalization, monomial_eq_smul α c, map_smul,
    show (monomial α 1 : MvPolynomial σ R) = basisMonomials σ R α by rw [coe_basisMonomials],
    Module.Basis.constr_basis, smul_monomial, smul_eq_mul]

/-- `tConvolution_monomial_monomial` with arbitrary coefficients. -/
private lemma tConvolution_monomial_monomial' (α β : σ →₀ ℕ) (a b : ℕ) (c d : R) :
    tConvolution (monomial (Finsupp.single none a + α.mapDomain some) c)
        (monomial (Finsupp.single none b + β.mapDomain some) d) =
      monomial (Finsupp.single none (a + b + 1) + (α + β).mapDomain some)
        (c * d * algebraMap ℚ R
          ((a.factorial * b.factorial : ℚ) / ((a + b + 1).factorial : ℚ))) := by
  rw [monomial_eq_smul _ c, monomial_eq_smul _ d, tConvolution_smul_left,
    tConvolution_smul_right, tConvolution_monomial_monomial, smul_smul, smul_monomial, smul_eq_mul]

/-- The scalar identity behind the monomial case:
`1 / (a + b)! = (1 / a!) (1 / b!) (a! b! / (a + b + 1)!) (a + b + 1)`. -/
private lemma one_div_factorial_add (a b : ℕ) :
    (1 / ((a + b).factorial : ℚ)) = 1 / (a.factorial : ℚ) * (1 / (b.factorial : ℚ)) *
      ((a.factorial * b.factorial : ℚ) / ((a + b + 1).factorial : ℚ)) * ((a + b + 1 : ℕ) : ℚ) := by
  rw [Nat.factorial_succ]
  push_cast
  field_simp

/-- The identity on monomials `x^α t^a` and `x^β t^b`. -/
private lemma factorialNormalization_monomial_mul_monomial (α β : σ →₀ ℕ) (a b : ℕ) (c d : R) :
    factorialNormalization none (monomial (Finsupp.single none a + α.mapDomain some) c *
        monomial (Finsupp.single none b + β.mapDomain some) d) =
      pderiv none (tConvolution
        (factorialNormalization none (monomial (Finsupp.single none a + α.mapDomain some) c))
        (factorialNormalization none (monomial (Finsupp.single none b + β.mapDomain some) d))) := by
  rw [monomial_mul, factorialNormalization_monomial, factorialNormalization_monomial,
    factorialNormalization_monomial, Finsupp.add_apply, single_none_add_mapDomain_some_apply_none,
    single_none_add_mapDomain_some_apply_none, tConvolution_monomial_monomial', pderiv_monomial,
    single_none_succ_add_mapDomain_some_sub, single_none_add_mapDomain_some_apply_none,
    ← map_natCast (algebraMap ℚ R), one_div_factorial_add]
  simp only [map_mul]
  congr 1
  ring

/-- **Factorial normalization of a product**: `𝓝_t (P Q) = ∂_t ((𝓝_t P) * (𝓝_t Q))`, with
`*` the convolution in `t`. -/
@[lognarayana "lem_normalized_product"]
public theorem factorialNormalization_mul (P Q : MvPolynomial (Option σ) R) :
    factorialNormalization none (P * Q) =
      pderiv none (tConvolution (factorialNormalization none P)
        (factorialNormalization none Q)) := by
  induction P using MvPolynomial.induction_on' with
  | add p p' hp hp' => rw [add_mul, map_add, hp, hp', map_add, tConvolution_add_left, map_add]
  | monomial u c =>
    induction Q using MvPolynomial.induction_on' with
    | add q q' hq hq' => rw [mul_add, map_add, hq, hq', map_add, tConvolution_add_right, map_add]
    | monomial v d =>
      rw [← single_none_add_mapDomain_some u, ← single_none_add_mapDomain_some v]
      exact factorialNormalization_monomial_mul_monomial _ _ _ _ c d

omit [Algebra ℚ R] in
/-- A linear map built by `Basis.constr` on the monomial basis, evaluated on a monomial. -/
private lemma constr_basisMonomials_monomial (g : (σ →₀ ℕ) → MvPolynomial σ R) (α : σ →₀ ℕ)
    (c : R) : (basisMonomials σ R).constr R g (monomial α c) = c • g α := by
  have h : (monomial α 1 : MvPolynomial σ R) = basisMonomials σ R α := by
    rw [coe_basisMonomials]
  rw [← mul_one c, ← smul_eq_mul, ← smul_monomial, map_smul, h, Module.Basis.constr_basis,
    smul_eq_mul, mul_one]

/-- The value of `antiderivative t` on a monomial. -/
private lemma antiderivative_monomial' (t : σ) (α : σ →₀ ℕ) (c : R) :
    antiderivative t (monomial α c) =
      monomial (α + Finsupp.single t 1) (c * algebraMap ℚ R (1 / ((α t : ℚ) + 1))) := by
  rw [antiderivative, constr_basisMonomials_monomial, smul_monomial, smul_eq_mul]

/-- The coefficients of `factorialNormalization t f`. -/
private lemma coeff_factorialNormalization (t : σ) (f : MvPolynomial σ R) (γ : σ →₀ ℕ) :
    coeff γ (factorialNormalization t f) =
      coeff γ f * algebraMap ℚ R (1 / ((γ t).factorial : ℚ)) := by
  classical
  induction f using MvPolynomial.induction_on' with
  | add p q hp hq => simp [hp, hq, add_mul]
  | monomial α c =>
    rw [factorialNormalization_monomial, coeff_monomial, coeff_monomial]
    split_ifs with h
    · rw [h]
    · rw [zero_mul]

/-- `factorialNormalization t` commutes with multiplication by a polynomial free of `t`. -/
private lemma factorialNormalization_mul_left (t : σ) {A : MvPolynomial σ R} (hA : t ∉ A.vars)
    (P : MvPolynomial σ R) :
    factorialNormalization t (A * P) = A * factorialNormalization t P := by
  classical
  induction P using MvPolynomial.induction_on' with
  | add p q hp hq => rw [mul_add, map_add, hp, hq, map_add, mul_add]
  | monomial α c =>
    conv_lhs => rw [A.as_sum]
    conv_rhs => rw [A.as_sum]
    rw [Finset.sum_mul, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun v hv => ?_
    have hvt : v t = 0 := by
      by_contra h
      exact hA ((mem_vars_iff_mem_support t).2 ⟨v, hv, Finsupp.mem_support_iff.2 h⟩)
    rw [factorialNormalization_monomial, monomial_mul, monomial_mul,
      factorialNormalization_monomial, Finsupp.add_apply, hvt, zero_add, mul_assoc]

/-- `factorialNormalization t` turns multiplication by `t` into the antiderivative. -/
private lemma factorialNormalization_X_mul (t : σ) (P : MvPolynomial σ R) :
    factorialNormalization t (X t * P) = antiderivative t (factorialNormalization t P) := by
  classical
  induction P using MvPolynomial.induction_on' with
  | add p q hp hq => rw [mul_add, map_add, hp, hq, map_add, map_add]
  | monomial α c =>
    rw [X, monomial_mul, factorialNormalization_monomial, factorialNormalization_monomial,
      antiderivative_monomial', one_mul, add_comm (Finsupp.single t 1) α, Finsupp.add_apply,
      Finsupp.single_eq_same, mul_assoc, ← map_mul]
    congr 3
    rw [Nat.factorial_succ]
    push_cast
    field_simp

/-- `factorialNormalization t` turns `δ_t` into `∂_t`. -/
private lemma factorialNormalization_divX (t : σ) (P : MvPolynomial σ R) :
    factorialNormalization t (divX t P) = pderiv t (factorialNormalization t P) := by
  ext γ
  rw [coeff_factorialNormalization, coeff_pderiv, coeff_factorialNormalization, divX,
    coeff_divMonomial, add_comm (Finsupp.single t 1) γ, Finsupp.add_apply,
    Finsupp.single_eq_same, mul_assoc]
  congr 1
  have : ((γ t : R) + 1) = algebraMap ℚ R ((γ t : ℚ) + 1) := by simp
  rw [this, ← map_mul]
  congr 1
  rw [Nat.factorial_succ]
  push_cast
  field_simp

/-- **Normalized root recurrence**: for `A, B` not involving `t`,
`𝓝_t((A + t) P + B δ_t P) = 𝓡_{A,B}(𝓝_t P)`. -/
@[lognarayana "lem_normalized_root"]
public theorem factorialNormalization_add_X_mul_add_mul_divX (t : σ) {A B : MvPolynomial σ R}
    (hA : t ∉ A.vars) (hB : t ∉ B.vars) (P : MvPolynomial σ R) :
    factorialNormalization t ((A + X t) * P + B * divX t P) =
      rootOperator t A B (factorialNormalization t P) := by
  rw [add_mul, map_add, map_add, factorialNormalization_mul_left t hA,
    factorialNormalization_X_mul, factorialNormalization_mul_left t hB,
    factorialNormalization_divX]
  rfl

end FactorialNormalization

end MvPolynomial

open MvPolynomial

/-! ### The open-pair polynomials -/

/-- `t ^ |O| * ∏_{(a,b) ∈ M} B_b * ∏_{v ∈ U(M) \ O} A_v`, the summand of `(M, O)`. -/
private noncomputable def weight {R σ : Type*} [CommSemiring R] (N : ℕ)
    (A B : ℕ → MvPolynomial σ R) (MO : Finset (ℕ × ℕ) × Finset ℕ) : MvPolynomial (Option σ) R :=
  X none ^ MO.2.card * (∏ p ∈ MO.1, rename some (B p.2)) *
    ∏ v ∈ Finset.unmatchedVertices N MO.1 \ MO.2, rename some (A v)

open scoped Classical in
/-- The finite set of open pairs of `(par, L)` on `[N]`. -/
private noncomputable def openPairs (N : ℕ) (par : ℕ → Option ℕ) (L : Finset ℕ) :
    Finset (Finset (ℕ × ℕ) × Finset ℕ) :=
  ((Finset.Icc 1 N ×ˢ Finset.Icc 1 N).powerset ×ˢ (Finset.Icc 1 N).powerset).filter
      (fun MO : Finset (ℕ × ℕ) × Finset ℕ => IsOpenPair N par L MO.1 MO.2)

private lemma vertexWeightedOpenPairPolynomial_eq {R σ : Type*} [CommSemiring R] (N : ℕ)
    (par : ℕ → Option ℕ) (L : Finset ℕ) (A B : ℕ → MvPolynomial σ R) :
    vertexWeightedOpenPairPolynomial N par L A B = ∑ MO ∈ openPairs N par L, weight N A B MO :=
  rfl

private lemma mem_unmatchedVertices_iff {N : ℕ} {M : Finset (ℕ × ℕ)} {x : ℕ} :
    x ∈ Finset.unmatchedVertices N M ↔ (1 ≤ x ∧ x ≤ N) ∧ ∀ p ∈ M, p.1 ≠ x ∧ p.2 ≠ x := by
  simp only [Finset.unmatchedVertices, Finset.leftEndpoints, Finset.mem_sdiff, Finset.mem_Icc,
    Finset.mem_union, Finset.mem_image, not_or, not_exists, not_and]
  constructor
  · rintro ⟨h, h1, h2⟩; exact ⟨h, fun p hp => ⟨h1 p hp, h2 p hp⟩⟩
  · rintro ⟨h, h'⟩; exact ⟨h, fun p hp => (h' p hp).1, fun p hp => (h' p hp).2⟩

private lemma mem_openPairs {N : ℕ} {par : ℕ → Option ℕ} {L : Finset ℕ}
    {MO : Finset (ℕ × ℕ) × Finset ℕ} :
    MO ∈ openPairs N par L ↔ IsOpenPair N par L MO.1 MO.2 := by
  classical
  simp only [openPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_powerset,
    and_iff_right_iff_imp]
  intro h
  have hM := h.isNoncrossingPartialMatching
  refine ⟨fun p hp => ?_, fun u hu => ?_⟩
  · have := hM.one_le_fst p hp; have := hM.fst_lt_snd p hp; have := hM.snd_le p hp
    simp only [Finset.mem_product, Finset.mem_Icc]; omega
  · exact Finset.mem_Icc.2 (mem_unmatchedVertices_iff.1 (h.subset_unmatchedVertices hu)).1

/-! ### Homogeneity -/

/-- A partial matching on `[N]` leaves `N - 2 |M|` vertices unmatched: its `2 |M|` endpoints are
distinct and lie in `[N]`. The noncrossing condition is not used. -/
private theorem card_unmatchedVertices_add {N : ℕ} {M : Finset (ℕ × ℕ)}
    (hM : IsNoncrossingPartialMatching N M) :
    (Finset.unmatchedVertices N M).card + 2 * M.card = N := by
  have hdisj : Disjoint (M.image Prod.fst) (M.image Prod.snd) := by
    simp only [Finset.disjoint_left, Finset.mem_image, not_exists, not_and]
    rintro _ ⟨p, hp, rfl⟩ q hq hqp
    obtain rfl := hM.eq_of_mem_of_mem p hp q hq p.1 (Or.inl rfl) (Or.inr hqp.symm)
    exact (hM.fst_lt_snd p hp).ne hqp.symm
  have hcard : (M.leftEndpoints ∪ M.image Prod.snd).card = 2 * M.card := by
    rw [Finset.card_union_of_disjoint hdisj,
      Finset.card_image_of_injOn fun p hp q hq h =>
        hM.eq_of_mem_of_mem p hp q hq p.1 (Or.inl rfl) (Or.inl h),
      Finset.card_image_of_injOn fun p hp q hq h =>
        hM.eq_of_mem_of_mem p hp q hq p.2 (Or.inr rfl) (Or.inr h), two_mul]
  have hsub : M.leftEndpoints ∪ M.image Prod.snd ⊆ Finset.Icc 1 N := by
    simp only [Finset.union_subset_iff, Finset.image_subset_iff, Finset.mem_Icc]
    exact ⟨fun p hp => ⟨hM.one_le_fst p hp, (hM.fst_lt_snd p hp).le.trans (hM.snd_le p hp)⟩,
      fun p hp => ⟨(hM.one_le_fst p hp).trans (hM.fst_lt_snd p hp).le, hM.snd_le p hp⟩⟩
  have := Finset.card_le_card hsub
  rw [hcard, Nat.card_Icc] at this
  rw [Finset.unmatchedVertices, Finset.card_sdiff_of_subset hsub, Nat.card_Icc, hcard]
  omega

/-- For `A` homogeneous of degree `1` and `B` homogeneous of degree `2`, the weighted open-pair
polynomial `P^{A,B}_{par,L}(x, t)` on `[N]` is homogeneous of degree `N`. -/
@[lognarayana "lem_weighted_open_poly_homogeneous"]
public theorem isHomogeneous_weightedOpenPairPolynomial {R σ : Type*} [CommSemiring R]
    (N : ℕ) (par : ℕ → Option ℕ) (L : Finset ℕ) {A B : MvPolynomial σ R}
    (hA : A.IsHomogeneous 1) (hB : B.IsHomogeneous 2) :
    (weightedOpenPairPolynomial N par L A B).IsHomogeneous N := by
  classical
  refine IsHomogeneous.sum _ _ _ fun ⟨M, O⟩ hMO => ?_
  have hop : IsOpenPair N par L M O := (Finset.mem_filter.mp hMO).2
  convert ((isHomogeneous_X_pow (R := R) none O.card).mul
    (IsHomogeneous.prod M _ (fun _ => 2) fun _ _ => hB.rename_isHomogeneous)).mul
    (IsHomogeneous.prod _ _ (fun _ => 1) fun _ _ => hA.rename_isHomogeneous) using 1
  have := card_unmatchedVertices_add hop.isNoncrossingPartialMatching
  have := Finset.card_le_card hop.subset_unmatchedVertices
  simp only [Finset.sum_const, smul_eq_mul, mul_one,
    Finset.card_sdiff_of_subset hop.subset_unmatchedVertices]
  omega

/-! ### The marked singleton -/

/-- The open pairs of the marked singleton: `(M, O)` is one iff `M = ∅` and `O = {1}`. -/
private lemma isOpenPair_markedSingleton_iff (M : Finset (ℕ × ℕ)) (O : Finset ℕ) :
    IsOpenPair 1 markedSingleton.1 markedSingleton.2 M O ↔ M = ∅ ∧ O = {1} := by
  constructor
  · intro h
    have hM : M = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun p hp => ?_
      have h1 := h.isNoncrossingPartialMatching.one_le_fst p hp
      have h2 := h.isNoncrossingPartialMatching.fst_lt_snd p hp
      have h3 := h.isNoncrossingPartialMatching.snd_le p hp
      omega
    subst hM
    refine ⟨rfl, Finset.Subset.antisymm ?_ ?_⟩
    · simpa [Finset.unmatchedVertices] using h.subset_unmatchedVertices
    · simpa [markedSingleton, Finset.leftEndpoints] using h.subset_leftEndpoints_union
  · rintro ⟨rfl, rfl⟩
    exact
      { isNoncrossingPartialMatching := ⟨by simp, by simp, by simp, by simp, by simp⟩
        isStrictAncestor := by simp
        subset_unmatchedVertices := by simp [Finset.unmatchedVertices]
        exposed := by simp
        subset_leftEndpoints_union := by simp [markedSingleton] }

/-- The vertex-weighted open-pair polynomial of the marked singleton `𝒮` on `[1]` is `t`, for
all weight families `A`, `B`. -/
@[lognarayana "lem_weighted_open_poly_marked_singleton"]
public theorem vertexWeightedOpenPairPolynomial_markedSingleton {R σ : Type*} [CommSemiring R]
    (A B : ℕ → MvPolynomial σ R) :
    vertexWeightedOpenPairPolynomial 1 markedSingleton.1 markedSingleton.2 A B = X none := by
  rw [vertexWeightedOpenPairPolynomial, Finset.sum_eq_single_of_mem (∅, {1})]
  · simp [Finset.unmatchedVertices]
  · simp [isOpenPair_markedSingleton_iff]
  · rintro ⟨M, O⟩ h hne
    simp_all [isOpenPair_markedSingleton_iff]

/-! ### Concatenation -/

/-- The shift `(a, b) ↦ (N + a, N + b)` of a pair. -/
private def shift (N : ℕ) (p : ℕ × ℕ) : ℕ × ℕ := (N + p.1, N + p.2)

/-- The unshift `(a, b) ↦ (a - N, b - N)` of a pair. -/
private def unshift (N : ℕ) (p : ℕ × ℕ) : ℕ × ℕ := (p.1 - N, p.2 - N)

private lemma shift_fst (N : ℕ) (p : ℕ × ℕ) : (shift N p).1 = N + p.1 := rfl
private lemma shift_snd (N : ℕ) (p : ℕ × ℕ) : (shift N p).2 = N + p.2 := rfl
private lemma unshift_fst (N : ℕ) (p : ℕ × ℕ) : (unshift N p).1 = p.1 - N := rfl
private lemma unshift_snd (N : ℕ) (p : ℕ × ℕ) : (unshift N p).2 = p.2 - N := rfl

private lemma shift_injective (N : ℕ) : Function.Injective (shift N) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  simp only [shift, Prod.mk.injEq] at h
  ext <;> omega

/-- The unmatched vertices of `M₁ ∪ (N + M₂)` are those of `M₁` and the shifts of those of
`M₂`. -/
private lemma unmatchedVertices_union_image_shift {N N' : ℕ} {M₁ M₂ : Finset (ℕ × ℕ)}
    (hM₁ : IsNoncrossingPartialMatching N M₁) (hM₂ : IsNoncrossingPartialMatching N' M₂) :
    Finset.unmatchedVertices (N + N') (M₁ ∪ M₂.image (shift N)) =
      Finset.unmatchedVertices N M₁ ∪ (Finset.unmatchedVertices N' M₂).image (N + ·) := by
  ext x
  simp only [mem_unmatchedVertices_iff, Finset.forall_mem_union, Finset.forall_mem_image,
    shift_fst, shift_snd]
  simp only [Finset.mem_union, Finset.mem_image, mem_unmatchedVertices_iff]
  constructor
  · rintro ⟨hx, h1, h2⟩
    by_cases hxN : x ≤ N
    · exact Or.inl ⟨⟨hx.1, hxN⟩, h1⟩
    · refine Or.inr ⟨x - N, ⟨⟨by omega, by omega⟩, fun q hq => ?_⟩, by omega⟩
      have := h2 hq; omega
  · rintro (⟨hx, h1⟩ | ⟨y, ⟨hy, h2⟩, rfl⟩)
    · refine ⟨⟨hx.1, by omega⟩, h1, fun q hq => ?_⟩
      have := hM₂.one_le_fst q hq; have := hM₂.fst_lt_snd q hq; omega
    · refine ⟨⟨by omega, by omega⟩, fun p hp => ?_, fun q hq => ?_⟩
      · have := hM₁.fst_lt_snd p hp; have := hM₁.snd_le p hp; omega
      · have := h2 q hq; omega

/-- `Φ` is well defined: the union of an open pair of `(par, L)` and the shift of an open pair of
`(par', L')` is an open pair of the concatenation. -/
private lemma isOpenPair_union_shift {N N' : ℕ} {par par' : ℕ → Option ℕ} {L L' : Finset ℕ}
    (hpar : IsParentMap N par) (hpar' : IsParentMap N' par')
    {M₁ M₂ : Finset (ℕ × ℕ)} {O₁ O₂ : Finset ℕ}
    (h₁ : IsOpenPair N par L M₁ O₁) (h₂ : IsOpenPair N' par' L' M₂ O₂) :
    IsOpenPair (N + N') (forestConcatParent N par par') (forestConcatMarked N L L')
      (M₁ ∪ M₂.image (shift N)) (O₁ ∪ O₂.image (N + ·)) := by
  have hM₁ := h₁.isNoncrossingPartialMatching
  have hM₂ := h₂.isNoncrossingPartialMatching
  have b₁ : ∀ p ∈ M₁, 1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ N := fun p hp =>
    ⟨hM₁.one_le_fst p hp, hM₁.fst_lt_snd p hp, hM₁.snd_le p hp⟩
  have b₂ : ∀ p ∈ M₂, 1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ N' := fun p hp =>
    ⟨hM₂.one_le_fst p hp, hM₂.fst_lt_snd p hp, hM₂.snd_le p hp⟩
  have o₁ : ∀ u ∈ O₁, 1 ≤ u ∧ u ≤ N := fun u hu =>
    (mem_unmatchedVertices_iff.1 (h₁.subset_unmatchedVertices hu)).1
  have o₂ : ∀ u ∈ O₂, 1 ≤ u ∧ u ≤ N' := fun u hu =>
    (mem_unmatchedVertices_iff.1 (h₂.subset_unmatchedVertices hu)).1
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · simp only [Finset.forall_mem_union, Finset.forall_mem_image, shift_fst]
    exact ⟨fun p hp => (b₁ p hp).1, fun p hp => by have := b₂ p hp; omega⟩
  · simp only [Finset.forall_mem_union, Finset.forall_mem_image, shift_fst, shift_snd]
    exact ⟨fun p hp => (b₁ p hp).2.1, fun p hp => by have := b₂ p hp; omega⟩
  · simp only [Finset.forall_mem_union, Finset.forall_mem_image, shift_snd]
    exact ⟨fun p hp => by have := b₁ p hp; omega, fun p hp => by have := b₂ p hp; omega⟩
  · simp only [Finset.forall_mem_union, Finset.forall_mem_image, shift_fst, shift_snd]
    refine ⟨fun p hp => ⟨fun q hq => hM₁.eq_of_mem_of_mem p hp q hq, fun q hq x hx hx' => ?_⟩,
      fun p hp => ⟨fun q hq x hx hx' => ?_, fun q hq x hx hx' => ?_⟩⟩
    · have := b₁ p hp; have := b₂ q hq; omega
    · have := b₂ p hp; have := b₁ q hq; omega
    · rw [hM₂.eq_of_mem_of_mem p hp q hq (x - N) (by omega) (by omega)]
  · simp only [Finset.forall_mem_union, Finset.forall_mem_image, shift_fst, shift_snd]
    refine ⟨fun p hp => ⟨fun q hq => hM₁.noncrossing p hp q hq, fun q hq => ?_⟩,
      fun p hp => ⟨fun q hq => ?_, fun q hq => ?_⟩⟩
    · have := b₁ p hp; have := b₂ q hq; omega
    · have := b₂ p hp; have := b₁ q hq; omega
    · have := hM₂.noncrossing p hp q hq; omega
  · simp only [Finset.forall_mem_union, Finset.forall_mem_image, shift_fst, shift_snd,
      isStrictAncestor_forestConcatParent_iff hpar hpar']
    refine ⟨fun p hp => Or.inl ⟨?_, ?_, h₁.isStrictAncestor p hp⟩, fun p hp => Or.inr ⟨?_, ?_, ?_⟩⟩
    · have := b₁ p hp; simp only [Finset.mem_Icc]; omega
    · have := b₁ p hp; simp only [Finset.mem_Icc]; omega
    · have := b₂ p hp; omega
    · have := b₂ p hp; omega
    · simpa using h₂.isStrictAncestor p hp
  · rw [unmatchedVertices_union_image_shift hM₁ hM₂]
    exact Finset.union_subset_union h₁.subset_unmatchedVertices
      (Finset.image_subset_image h₂.subset_unmatchedVertices)
  · simp only [Finset.forall_mem_union, Finset.forall_mem_image, shift_fst, shift_snd]
    refine ⟨fun u hu => ⟨fun p hp => h₁.exposed u hu p hp, fun p hp => ?_⟩,
      fun u hu => ⟨fun p hp => ?_, fun p hp => ?_⟩⟩
    · have := o₁ u hu; omega
    · have := o₂ u hu; have := b₁ p hp; omega
    · have := h₂.exposed u hu p hp; omega
  · intro v hv
    simp only [forestConcatMarked, Finset.mem_union, Finset.mem_map, addLeftEmbedding_apply] at hv
    simp only [Finset.leftEndpoints, Finset.mem_union, Finset.mem_image]
    rcases hv with hv | ⟨w, hw, rfl⟩
    · have := h₁.subset_leftEndpoints_union hv
      simp only [Finset.leftEndpoints, Finset.mem_union, Finset.mem_image] at this
      rcases this with ⟨p, hp, rfl⟩ | hv
      · exact Or.inl ⟨p, Or.inl hp, rfl⟩
      · exact Or.inr (Or.inl hv)
    · have := h₂.subset_leftEndpoints_union hw
      simp only [Finset.leftEndpoints, Finset.mem_union, Finset.mem_image] at this
      rcases this with ⟨p, hp, rfl⟩ | hw
      · exact Or.inl ⟨shift N p, Or.inr ⟨p, hp, rfl⟩, rfl⟩
      · exact Or.inr (Or.inr ⟨w, hw, rfl⟩)

/-- Each pair of an open pair of the concatenation lies in `[N]` or in `N + [N']`. -/
private lemma pair_cases {N N' : ℕ} {par par' : ℕ → Option ℕ} {L'' : Finset ℕ}
    (hpar : IsParentMap N par) (hpar' : IsParentMap N' par')
    {M : Finset (ℕ × ℕ)} {O : Finset ℕ}
    (h : IsOpenPair (N + N') (forestConcatParent N par par') L'' M O) (p : ℕ × ℕ) (hp : p ∈ M) :
    (1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ N ∧ IsStrictAncestor par p.2 p.1) ∨
      (N < p.1 ∧ p.1 < p.2 ∧ p.2 ≤ N + N' ∧ IsStrictAncestor par' (p.2 - N) (p.1 - N)) := by
  have hM := h.isNoncrossingPartialMatching
  have := hM.fst_lt_snd p hp
  have := hM.snd_le p hp
  rcases (isStrictAncestor_forestConcatParent_iff hpar hpar' _ _).1 (h.isStrictAncestor p hp) with
    ⟨ha, hb, h'⟩ | ⟨ha, hb, h'⟩
  · simp only [Finset.mem_Icc] at ha hb
    exact Or.inl ⟨ha.1, by omega, hb.2, h'⟩
  · exact Or.inr ⟨ha, by omega, by omega, h'⟩

/-- The first component of the inverse of `Φ` is an open pair of `(par, L)`. -/
private lemma isOpenPair_filter_le {N N' : ℕ} {par par' : ℕ → Option ℕ} {L L' : Finset ℕ}
    (hpar : IsParentMap N par) (hpar' : IsParentMap N' par') (hL : L ⊆ Finset.Icc 1 N)
    {M : Finset (ℕ × ℕ)} {O : Finset ℕ}
    (h : IsOpenPair (N + N') (forestConcatParent N par par') (forestConcatMarked N L L') M O) :
    IsOpenPair N par L (M.filter (fun p => p.2 ≤ N)) (O.filter (· ≤ N)) := by
  have hM := h.isNoncrossingPartialMatching
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · exact fun p hp => hM.one_le_fst p (Finset.mem_filter.1 hp).1
  · exact fun p hp => hM.fst_lt_snd p (Finset.mem_filter.1 hp).1
  · exact fun p hp => (Finset.mem_filter.1 hp).2
  · exact fun p hp q hq => hM.eq_of_mem_of_mem p (Finset.mem_filter.1 hp).1 q
      (Finset.mem_filter.1 hq).1
  · exact fun p hp q hq => hM.noncrossing p (Finset.mem_filter.1 hp).1 q (Finset.mem_filter.1 hq).1
  · intro p hp
    rw [Finset.mem_filter] at hp
    rcases pair_cases hpar hpar' h p hp.1 with h' | h'
    · exact h'.2.2.2
    · omega
  · intro u hu
    rw [Finset.mem_filter] at hu
    have := mem_unmatchedVertices_iff.1 (h.subset_unmatchedVertices hu.1)
    exact mem_unmatchedVertices_iff.2 ⟨⟨this.1.1, hu.2⟩, fun p hp =>
      this.2 p (Finset.mem_filter.1 hp).1⟩
  · exact fun u hu p hp => h.exposed u (Finset.mem_filter.1 hu).1 p (Finset.mem_filter.1 hp).1
  · intro v hv
    have hvN := (Finset.mem_Icc.1 (hL hv)).2
    have := h.subset_leftEndpoints_union
      (Finset.mem_union_left _ hv : v ∈ forestConcatMarked N L L')
    simp only [Finset.leftEndpoints, Finset.mem_union, Finset.mem_image, Finset.mem_filter]
      at this ⊢
    rcases this with ⟨p, hp, rfl⟩ | hv
    · refine Or.inl ⟨p, ⟨hp, ?_⟩, rfl⟩
      rcases pair_cases hpar hpar' h p hp with h' | h'
      · exact h'.2.2.1
      · omega
    · exact Or.inr ⟨hv, hvN⟩

/-- The second component of the inverse of `Φ` is an open pair of `(par', L')`. -/
private lemma isOpenPair_filter_not_le {N N' : ℕ} {par par' : ℕ → Option ℕ} {L L' : Finset ℕ}
    (hpar : IsParentMap N par) (hpar' : IsParentMap N' par') (hL' : L' ⊆ Finset.Icc 1 N')
    {M : Finset (ℕ × ℕ)} {O : Finset ℕ}
    (h : IsOpenPair (N + N') (forestConcatParent N par par') (forestConcatMarked N L L') M O) :
    IsOpenPair N' par' L' ((M.filter (fun p => ¬ p.2 ≤ N)).image (unshift N))
      ((O.filter (¬ · ≤ N)).image (· - N)) := by
  have hM := h.isNoncrossingPartialMatching
  have c : ∀ p ∈ M, ¬ p.2 ≤ N →
      N < p.1 ∧ p.1 < p.2 ∧ p.2 ≤ N + N' ∧ IsStrictAncestor par' (p.2 - N) (p.1 - N) := by
    intro p hp hpN
    rcases pair_cases hpar hpar' h p hp with h' | h'
    · omega
    · exact h'
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · simp only [Finset.forall_mem_image, Finset.mem_filter, and_imp, unshift_fst]
    exact fun p hp hpN => by have := c p hp hpN; omega
  · simp only [Finset.forall_mem_image, Finset.mem_filter, and_imp, unshift_fst, unshift_snd]
    exact fun p hp hpN => by have := c p hp hpN; omega
  · simp only [Finset.forall_mem_image, Finset.mem_filter, and_imp, unshift_snd]
    exact fun p hp hpN => by have := c p hp hpN; omega
  · simp only [Finset.forall_mem_image, Finset.mem_filter, and_imp, unshift_fst, unshift_snd]
    intro p hp hpN q hq hqN x hx hx'
    have := c p hp hpN; have := c q hq hqN
    rw [hM.eq_of_mem_of_mem p hp q hq (N + x) (by omega) (by omega)]
  · simp only [Finset.forall_mem_image, Finset.mem_filter, and_imp, unshift_fst, unshift_snd]
    intro p hp hpN q hq hqN
    have := c p hp hpN; have := c q hq hqN; have := hM.noncrossing p hp q hq
    omega
  · simp only [Finset.forall_mem_image, Finset.mem_filter, and_imp, unshift_fst, unshift_snd]
    exact fun p hp hpN => (c p hp hpN).2.2.2
  · intro u hu
    simp only [Finset.mem_image, Finset.mem_filter] at hu
    obtain ⟨w, ⟨hw, hwN⟩, rfl⟩ := hu
    have hwU := mem_unmatchedVertices_iff.1 (h.subset_unmatchedVertices hw)
    refine mem_unmatchedVertices_iff.2 ⟨⟨by omega, by omega⟩, ?_⟩
    simp only [Finset.forall_mem_image, Finset.mem_filter, and_imp, unshift_fst, unshift_snd]
    intro p hp hpN
    have := c p hp hpN; have := hwU.2 p hp
    omega
  · simp only [Finset.forall_mem_image, Finset.mem_filter, and_imp, unshift_fst, unshift_snd]
    intro w hw hwN p hp hpN
    have := c p hp hpN; have := h.exposed w hw p hp
    omega
  · intro v hv
    have hv1 := (Finset.mem_Icc.1 (hL' hv)).1
    have := h.subset_leftEndpoints_union
      (Finset.mem_union_right _ (Finset.mem_map_of_mem _ hv) : N + v ∈ forestConcatMarked N L L')
    simp only [Finset.leftEndpoints, Finset.mem_union, Finset.mem_image, Finset.mem_filter]
      at this ⊢
    rcases this with ⟨p, hp, hpv⟩ | hv
    · have := hM.fst_lt_snd p hp
      refine Or.inl ⟨unshift N p, ⟨p, ⟨hp, by omega⟩, rfl⟩, ?_⟩
      simp only [unshift_fst]; omega
    · exact Or.inr ⟨N + v, ⟨hv, by omega⟩, by omega⟩

/-- `(A ∪ B) \ (C ∪ D) = (A \ C) ∪ (B \ D)` when `A` misses `D` and `B` misses `C`. -/
private lemma union_sdiff_union_of_disjoint {α : Type*} [DecidableEq α] {A B C D : Finset α}
    (hAD : Disjoint A D) (hBC : Disjoint B C) : (A ∪ B) \ (C ∪ D) = (A \ C) ∪ (B \ D) := by
  ext x
  have h1 : x ∈ A → x ∉ D := fun h => Finset.disjoint_left.1 hAD h
  have h2 : x ∈ B → x ∉ C := fun h => Finset.disjoint_left.1 hBC h
  simp only [Finset.mem_union, Finset.mem_sdiff]
  tauto

/-- The summand of `Φ((M₁, O₁), (M₂, O₂))` is the product of the summands of `(M₁, O₁)` and of
`(M₂, O₂)`, the latter for the shifted families. -/
private lemma weight_union_shift {R σ : Type*} [CommSemiring R] {N N' : ℕ}
    (A B : ℕ → MvPolynomial σ R) {M₁ M₂ : Finset (ℕ × ℕ)} {O₁ O₂ : Finset ℕ}
    (hM₁ : IsNoncrossingPartialMatching N M₁) (hM₂ : IsNoncrossingPartialMatching N' M₂)
    (hO₁ : O₁ ⊆ Finset.unmatchedVertices N M₁) (hO₂ : O₂ ⊆ Finset.unmatchedVertices N' M₂) :
    weight (N + N') A B (M₁ ∪ M₂.image (shift N), O₁ ∪ O₂.image (N + ·)) =
      weight N A B (M₁, O₁) * weight N' (fun v => A (N + v)) (fun v => B (N + v)) (M₂, O₂) := by
  have o₁ : ∀ u ∈ O₁, 1 ≤ u ∧ u ≤ N := fun u hu => (mem_unmatchedVertices_iff.1 (hO₁ hu)).1
  have o₂ : ∀ u ∈ O₂, 1 ≤ u ∧ u ≤ N' := fun u hu => (mem_unmatchedVertices_iff.1 (hO₂ hu)).1
  have hinj : Function.Injective (N + · : ℕ → ℕ) := add_right_injective N
  have hdO : Disjoint O₁ (O₂.image (N + ·)) := by
    rw [Finset.disjoint_left]
    intro u hu hu'
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hu'
    have := o₁ _ hu; have := o₂ w hw; omega
  have hdM : Disjoint M₁ (M₂.image (shift N)) := by
    rw [Finset.disjoint_left]
    intro p hp hp'
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hp'
    have := hM₁.snd_le _ hp; have := hM₂.one_le_fst q hq; have := hM₂.fst_lt_snd q hq
    have := shift_snd N q; omega
  have hdU : ∀ {S T : Finset ℕ}, S ⊆ Finset.unmatchedVertices N M₁ →
      T ⊆ Finset.unmatchedVertices N' M₂ → Disjoint S (T.image (N + ·)) := by
    intro S T hS hT
    rw [Finset.disjoint_left]
    intro u hu hu'
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hu'
    have := (mem_unmatchedVertices_iff.1 (hS hu)).1
    have := (mem_unmatchedVertices_iff.1 (hT hw)).1
    omega
  have hU : Finset.unmatchedVertices (N + N') (M₁ ∪ M₂.image (shift N)) \
      (O₁ ∪ O₂.image (N + ·)) = (Finset.unmatchedVertices N M₁ \ O₁) ∪
        (Finset.unmatchedVertices N' M₂ \ O₂).image (N + ·) := by
    rw [unmatchedVertices_union_image_shift hM₁ hM₂,
      union_sdiff_union_of_disjoint (hdU subset_rfl hO₂) (hdU hO₁ subset_rfl).symm,
      Finset.image_sdiff_of_injOn hinj.injOn hO₂]
  unfold weight
  rw [hU, Finset.card_union_of_disjoint hdO, Finset.card_image_of_injective _ hinj,
    Finset.prod_union hdM, Finset.prod_image (fun x _ y _ h => shift_injective N h),
    Finset.prod_union (hdU Finset.sdiff_subset Finset.sdiff_subset),
    Finset.prod_image (fun x _ y _ h => hinj h), pow_add]
  simp only [shift_snd]
  ring

/-- The splitting map undoes `Φ`: splitting `(M₁ ∪ (N + M₂), O₁ ∪ (N + O₂))` along `[N]`
recovers `((M₁, O₁), (M₂, O₂))`. -/
private lemma split_union_shift {N N' : ℕ} {M₁ M₂ : Finset (ℕ × ℕ)} {O₁ O₂ : Finset ℕ}
    (hM₁ : IsNoncrossingPartialMatching N M₁) (hM₂ : IsNoncrossingPartialMatching N' M₂)
    (hO₁ : O₁ ⊆ Finset.unmatchedVertices N M₁) (hO₂ : O₂ ⊆ Finset.unmatchedVertices N' M₂) :
    (((M₁ ∪ M₂.image (shift N)).filter (fun p => p.2 ≤ N),
        (O₁ ∪ O₂.image (N + ·)).filter (· ≤ N)),
      (((M₁ ∪ M₂.image (shift N)).filter (fun p => ¬ p.2 ≤ N)).image (unshift N),
        ((O₁ ∪ O₂.image (N + ·)).filter (¬ · ≤ N)).image (· - N))) = ((M₁, O₁), (M₂, O₂)) := by
  have o₁ : ∀ u ∈ O₁, 1 ≤ u ∧ u ≤ N := fun u hu => (mem_unmatchedVertices_iff.1 (hO₁ hu)).1
  have o₂ : ∀ u ∈ O₂, 1 ≤ u ∧ u ≤ N' := fun u hu => (mem_unmatchedVertices_iff.1 (hO₂ hu)).1
  have hq : ∀ q ∈ M₂, ¬ (shift N q).2 ≤ N := fun q hq => by
    have := hM₂.one_le_fst q hq; have := hM₂.fst_lt_snd q hq; rw [shift_snd]; omega
  have hu : ∀ u ∈ O₂, ¬ N + u ≤ N := fun u hu => by have := o₂ u hu; omega
  simp only [Finset.filter_union, Prod.mk.injEq]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [Finset.filter_true_of_mem (fun p hp => hM₁.snd_le p hp),
      Finset.filter_false_of_mem (Finset.forall_mem_image.2 hq), Finset.union_empty]
  · rw [Finset.filter_true_of_mem (fun u hu => (o₁ u hu).2),
      Finset.filter_false_of_mem (Finset.forall_mem_image.2 hu), Finset.union_empty]
  · rw [Finset.filter_false_of_mem (fun p hp => not_not.2 (hM₁.snd_le p hp)),
      Finset.filter_true_of_mem (p := fun p : ℕ × ℕ => ¬ p.2 ≤ N) (Finset.forall_mem_image.2 hq),
      Finset.empty_union, Finset.image_image]
    conv_rhs => rw [← Finset.image_id (s := M₂)]
    exact Finset.image_congr fun q _ => by simp [unshift, shift]
  · rw [Finset.filter_false_of_mem (fun u hu => not_not.2 (o₁ u hu).2),
      Finset.filter_true_of_mem (p := (¬ · ≤ N)) (Finset.forall_mem_image.2 hu),
      Finset.empty_union, Finset.image_image]
    conv_rhs => rw [← Finset.image_id (s := O₂)]
    exact Finset.image_congr fun u _ => by simp

/-- `Φ` undoes the splitting map on open pairs of the concatenation. -/
private lemma union_shift_split {N N' : ℕ} {par par' : ℕ → Option ℕ} {L'' : Finset ℕ}
    (hpar : IsParentMap N par) (hpar' : IsParentMap N' par')
    {M : Finset (ℕ × ℕ)} {O : Finset ℕ}
    (h : IsOpenPair (N + N') (forestConcatParent N par par') L'' M O) :
    (M.filter (fun p => p.2 ≤ N) ∪ ((M.filter (fun p => ¬ p.2 ≤ N)).image (unshift N)).image
        (shift N),
      O.filter (· ≤ N) ∪ ((O.filter (¬ · ≤ N)).image (· - N)).image (N + ·)) = (M, O) := by
  simp only [Finset.image_image, Prod.mk.injEq]
  constructor
  · conv_rhs => rw [← Finset.filter_union_filter_not_eq (fun p : ℕ × ℕ => p.2 ≤ N) M]
    congr 1
    conv_rhs => rw [← Finset.image_id (s := M.filter _)]
    refine Finset.image_congr fun p hp => ?_
    have hp := Finset.mem_filter.1 (Finset.mem_coe.1 hp)
    rcases pair_cases hpar hpar' h p hp.1 with h' | h'
    · exact absurd h'.2.2.1 hp.2
    · simp only [Function.comp_apply, shift, unshift, id]; ext <;> simp <;> omega
  · conv_rhs => rw [← Finset.filter_union_filter_not_eq (· ≤ N) O]
    congr 1
    conv_rhs => rw [← Finset.image_id (s := O.filter _)]
    refine Finset.image_congr fun u hu => ?_
    have hu := Finset.mem_filter.1 (Finset.mem_coe.1 hu)
    simp only [Function.comp_apply, id]; omega

/-- The vertex-weighted open-pair polynomial of the concatenation of two marked forests
is the product of the polynomials of the two forests, the second weighted by the shifted
families `A (N + ·)`, `B (N + ·)`. -/
@[lognarayana "lem_weighted_open_poly_concat"]
public theorem vertexWeightedOpenPairPolynomial_forestConcat {R σ : Type*} [CommSemiring R]
    {N N' : ℕ} {par par' : ℕ → Option ℕ} {L L' : Finset ℕ}
    (hpar : IsParentMap N par) (hL : L ⊆ Finset.Icc 1 N) (hpar' : IsParentMap N' par')
    (hL' : L' ⊆ Finset.Icc 1 N')
    (A B : ℕ → MvPolynomial σ R) :
    vertexWeightedOpenPairPolynomial (N + N') (forestConcatParent N par par')
        (forestConcatMarked N L L') A B =
      vertexWeightedOpenPairPolynomial N par L A B *
        vertexWeightedOpenPairPolynomial N' par' L' (fun v => A (N + v)) (fun v => B (N + v)) := by
  classical
  simp only [vertexWeightedOpenPairPolynomial_eq, Finset.sum_mul_sum, ← Finset.sum_product']
  symm
  refine Finset.sum_nbij'
    (fun x => (x.1.1 ∪ x.2.1.image (shift N), x.1.2 ∪ x.2.2.image (N + ·)))
    (fun MO => ((MO.1.filter (fun p => p.2 ≤ N), MO.2.filter (· ≤ N)),
      ((MO.1.filter (fun p => ¬ p.2 ≤ N)).image (unshift N),
        (MO.2.filter (¬ · ≤ N)).image (· - N)))) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨⟨M₁, O₁⟩, ⟨M₂, O₂⟩⟩ hx
    rw [Finset.mem_product, mem_openPairs, mem_openPairs] at hx
    exact mem_openPairs.2 (isOpenPair_union_shift hpar hpar' hx.1 hx.2)
  · rintro ⟨M, O⟩ hx
    rw [mem_openPairs] at hx
    exact Finset.mem_product.2 ⟨mem_openPairs.2 (isOpenPair_filter_le hpar hpar' hL hx),
      mem_openPairs.2 (isOpenPair_filter_not_le hpar hpar' hL' hx)⟩
  · rintro ⟨⟨M₁, O₁⟩, ⟨M₂, O₂⟩⟩ hx
    rw [Finset.mem_product, mem_openPairs, mem_openPairs] at hx
    exact split_union_shift hx.1.isNoncrossingPartialMatching hx.2.isNoncrossingPartialMatching
      hx.1.subset_unmatchedVertices hx.2.subset_unmatchedVertices
  · rintro ⟨M, O⟩ hx
    exact union_shift_split hpar hpar' (mem_openPairs.1 hx)
  · rintro ⟨⟨M₁, O₁⟩, ⟨M₂, O₂⟩⟩ hx
    rw [Finset.mem_product, mem_openPairs, mem_openPairs] at hx
    exact (weight_union_shift A B hx.1.isNoncrossingPartialMatching
      hx.2.isNoncrossingPartialMatching hx.1.subset_unmatchedVertices
      hx.2.subset_unmatchedVertices).symm

/-! ### Adjoining a root -/

/-- The `t`-free factor `∏_{(a,b) ∈ M} B_b * ∏_{v ∈ U(M) \ O} A_v` of the summand of `(M, O)`. -/
private noncomputable def weightFree {R σ : Type*} [CommSemiring R] (N : ℕ)
    (A B : ℕ → MvPolynomial σ R) (MO : Finset (ℕ × ℕ) × Finset ℕ) : MvPolynomial σ R :=
  (∏ p ∈ MO.1, B p.2) * ∏ v ∈ Finset.unmatchedVertices N MO.1 \ MO.2, A v

private lemma weight_eq {R σ : Type*} [CommSemiring R] (N : ℕ) (A B : ℕ → MvPolynomial σ R)
    (MO : Finset (ℕ × ℕ) × Finset ℕ) :
    weight N A B MO = X none ^ MO.2.card * rename some (weightFree N A B MO) := by
  simp [weight, weightFree, map_prod, mul_assoc]

/-- `δ_t` kills polynomials free of `t`. -/
private lemma divX_rename_some {R σ : Type*} [CommSemiring R] (g : MvPolynomial σ R) :
    divX none (rename (some : σ → Option σ) g) = 0 := by
  ext α
  rw [divX, coeff_divMonomial, coeff_zero]
  refine coeff_rename_eq_zero _ _ _ fun u hu => ?_
  have := congrArg (· none) hu
  simp [Finsupp.mapDomain_of_notMem_range] at this
  omega

private lemma divX_X_pow_mul_rename {R σ : Type*} [CommSemiring R] (k : ℕ)
    (g : MvPolynomial σ R) :
    divX none (X none ^ k * rename some g) =
      if k = 0 then 0 else X none ^ (k - 1) * rename some g := by
  rcases k with _ | k
  · simp [divX_rename_some]
  · rw [if_neg k.succ_ne_zero, Nat.add_sub_cancel, pow_succ', mul_assoc, divX, X,
      divMonomial_monomial_mul]

private lemma divX_sum {R σ ι : Type*} [CommSemiring R] (s : Finset ι)
    (f : ι → MvPolynomial (Option σ) R) :
    divX none (∑ i ∈ s, f i) = ∑ i ∈ s, divX none (f i) := by
  ext α
  simp [coeff_divMonomial, coeff_sum]

/-- `δ_t P` is the sum over the open pairs with `O ≠ ∅` of `t ^ (|O| - 1)` times the `t`-free
factor. -/
private lemma divX_vertexWeightedOpenPairPolynomial {R σ : Type*} [CommSemiring R] (N : ℕ)
    (par : ℕ → Option ℕ) (L : Finset ℕ) (A B : ℕ → MvPolynomial σ R) :
    divX none (vertexWeightedOpenPairPolynomial N par L A B) =
      ∑ MO ∈ (openPairs N par L).filter (fun MO => MO.2.Nonempty),
        X none ^ (MO.2.card - 1) * rename some (weightFree N A B MO) := by
  rw [vertexWeightedOpenPairPolynomial_eq, divX_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun MO _ => ?_
  rw [weight_eq, divX_X_pow_mul_rename]
  by_cases h : MO.2.Nonempty
  · rw [if_neg (Finset.card_ne_zero.mpr h), if_pos h]
  · rw [Finset.not_nonempty_iff_eq_empty.mp h]
    simp

private lemma mem_leftEndpoints {x : ℕ} {M : Finset (ℕ × ℕ)} :
    x ∈ M.leftEndpoints ↔ ∃ p ∈ M, p.1 = x := by
  simp [Finset.leftEndpoints]

/-- No pair of a matching on `[N]` has right endpoint `N + 1`. -/
private lemma snd_ne_succ_of_isOpenPair {N : ℕ} {par : ℕ → Option ℕ} {L : Finset ℕ}
    {M : Finset (ℕ × ℕ)} {O : Finset ℕ} (h : IsOpenPair N par L M O) :
    ∀ p ∈ M, p.2 ≠ N + 1 := fun p hp => by
  have := h.isNoncrossingPartialMatching.snd_le p hp
  omega

/-- The vertex `N + 1` is not open in an open pair on `[N]`. -/
private lemma succ_notMem_of_isOpenPair {N : ℕ} {par : ℕ → Option ℕ} {L : Finset ℕ}
    {M : Finset (ℕ × ℕ)} {O : Finset ℕ} (h : IsOpenPair N par L M O) : N + 1 ∉ O := fun hO => by
  have := (mem_unmatchedVertices_iff.mp (h.subset_unmatchedVertices hO)).1
  omega

/-- If `(b, n)` is the only pair of `M` with right endpoint `n`, filtering `M` by it gives
`{(b, n)}`. -/
private lemma filter_snd_eq_singleton {M : Finset (ℕ × ℕ)} {b n : ℕ} (hb : (b, n) ∈ M)
    (huniq : ∀ p ∈ M, p.2 = n → p = (b, n)) : M.filter (·.2 = n) = {(b, n)} :=
  Finset.eq_singleton_iff_unique_mem.mpr ⟨Finset.mem_filter.mpr ⟨hb, rfl⟩,
    fun p hp => huniq p (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hp).2⟩

/-- If `(b, n)` is the only pair of `M` with right endpoint `n`, reinserting it into the pairs
with right endpoint `≠ n` recovers `M`. -/
private lemma insert_filter_snd_ne_eq {M : Finset (ℕ × ℕ)} {b n : ℕ} (hb : (b, n) ∈ M)
    (huniq : ∀ p ∈ M, p.2 = n → p = (b, n)) : insert (b, n) (M.filter (·.2 ≠ n)) = M := by
  ext p
  simp only [Finset.mem_insert, Finset.mem_filter]
  by_cases hp2 : p.2 = n
  · constructor
    · rintro (rfl | ⟨_, hne⟩)
      exacts [hb, absurd hp2 hne]
    · exact fun hp => .inl (huniq p hp hp2)
  · constructor
    · rintro (rfl | ⟨hp, _⟩)
      exacts [absurd rfl hp2, hp]
    · exact fun hp => .inr ⟨hp, hp2⟩

/-- Matching an open vertex `a` to `N + 1` leaves the unmatched non-open vertices unchanged. -/
private lemma unmatchedVertices_succ_insert_sdiff_erase {N a : ℕ} {M : Finset (ℕ × ℕ)}
    {O : Finset ℕ} (ha : a ∈ O) :
    Finset.unmatchedVertices (N + 1) (insert (a, N + 1) M) \ O.erase a =
      Finset.unmatchedVertices N M \ O := by
  ext x
  simp only [Finset.mem_sdiff, mem_unmatchedVertices_iff, Finset.forall_mem_insert,
    Finset.mem_erase, not_and]
  constructor
  · rintro ⟨⟨hx, ⟨hxa, hxN⟩, hp⟩, hxO⟩
    exact ⟨⟨⟨hx.1, by omega⟩, hp⟩, fun hO => hxO (Ne.symm hxa) hO⟩
  · rintro ⟨⟨hx, hp⟩, hxO⟩
    exact ⟨⟨⟨hx.1, by omega⟩, ⟨fun hxa => hxO (hxa ▸ ha), by omega⟩, hp⟩,
      fun _ hO => absurd hO hxO⟩

/-- An open pair of `(par, L)` is an open pair of `(par°, L)`. -/
private lemma isOpenPair_forestAdjoinRootParent {N : ℕ} {par : ℕ → Option ℕ} {L : Finset ℕ}
    (hpar : IsParentMap N par) {M : Finset (ℕ × ℕ)} {O : Finset ℕ} (h : IsOpenPair N par L M O) :
    IsOpenPair (N + 1) (forestAdjoinRootParent N par) L M O := by
  have hm := h.isNoncrossingPartialMatching
  refine ⟨⟨hm.one_le_fst, hm.fst_lt_snd, fun p hp => (hm.snd_le p hp).trans N.le_succ,
    hm.eq_of_mem_of_mem, hm.noncrossing⟩, fun p hp => ?_, fun x hx => ?_, h.exposed,
    h.subset_leftEndpoints_union⟩
  · have h1 := hm.one_le_fst p hp
    have h2 := hm.fst_lt_snd p hp
    have h3 := hm.snd_le p hp
    exact (isStrictAncestor_forestAdjoinRootParent_iff hpar (u := p.1)
      (Finset.mem_Icc.mpr ⟨h1, by omega⟩)).mpr
      (.inr (h.isStrictAncestor p hp))
  · have := mem_unmatchedVertices_iff.mp (h.subset_unmatchedVertices hx)
    exact mem_unmatchedVertices_iff.mpr ⟨⟨this.1.1, by omega⟩, this.2⟩

/-- An open pair of `(par°, L)` on `[N + 1]` in which `N + 1` is neither matched nor open is an
open pair of `(par, L)` on `[N]`, and conversely. -/
private lemma isOpenPair_forestAdjoinRootParent_iff {N : ℕ} {par : ℕ → Option ℕ}
    {L : Finset ℕ} (hpar : IsParentMap N par) {M : Finset (ℕ × ℕ)} {O : Finset ℕ}
    (hM : ∀ p ∈ M, p.2 ≠ N + 1) (hO : N + 1 ∉ O) :
    IsOpenPair (N + 1) (forestAdjoinRootParent N par) L M O ↔ IsOpenPair N par L M O := by
  refine ⟨fun h => ?_, isOpenPair_forestAdjoinRootParent hpar⟩
  have hm := h.isNoncrossingPartialMatching
  have hsnd : ∀ p ∈ M, p.2 ≤ N := fun p hp => by
    have := hm.snd_le p hp
    have := hM p hp
    omega
  refine ⟨⟨hm.one_le_fst, hm.fst_lt_snd, hsnd, hm.eq_of_mem_of_mem, hm.noncrossing⟩,
    fun p hp => ?_, fun x hx => ?_, h.exposed, h.subset_leftEndpoints_union⟩
  · have h1 := hm.one_le_fst p hp
    have h2 := hm.fst_lt_snd p hp
    have h3 := hsnd p hp
    exact ((isStrictAncestor_forestAdjoinRootParent_iff hpar (u := p.1)
      (Finset.mem_Icc.mpr ⟨h1, by omega⟩)).mp
      (h.isStrictAncestor p hp)).resolve_left (hM p hp)
  · have := mem_unmatchedVertices_iff.mp (h.subset_unmatchedVertices hx)
    have hne : x ≠ N + 1 := fun h => hO (h ▸ hx)
    exact mem_unmatchedVertices_iff.mpr ⟨⟨this.1.1, by omega⟩, this.2⟩

/-- The open pairs of `(par°, L)` in which `N + 1` is open are the `(M, O ∪ {N + 1})` for the open
pairs `(M, O)` of `(par, L)`. -/
private lemma isOpenPair_forestAdjoinRootParent_insert_iff {N : ℕ} {par : ℕ → Option ℕ}
    {L : Finset ℕ} (hpar : IsParentMap N par) (hL : L ⊆ Finset.Icc 1 N) {M : Finset (ℕ × ℕ)}
    {O : Finset ℕ} (hO : N + 1 ∉ O) :
    IsOpenPair (N + 1) (forestAdjoinRootParent N par) L M (insert (N + 1) O) ↔
      IsOpenPair N par L M O := by
  have hL' : N + 1 ∉ L := fun h => by have := Finset.mem_Icc.mp (hL h); omega
  constructor
  · intro h
    have hU := (mem_unmatchedVertices_iff.mp
      (h.subset_unmatchedVertices (Finset.mem_insert_self _ _))).2
    refine (isOpenPair_forestAdjoinRootParent_iff hpar (fun p hp => (hU p hp).2) hO).mp
      ⟨h.isNoncrossingPartialMatching, h.isStrictAncestor,
        (Finset.subset_insert _ _).trans h.subset_unmatchedVertices,
        fun u hu => h.exposed u (Finset.mem_insert_of_mem hu), fun x hx => ?_⟩
    have := h.subset_leftEndpoints_union hx
    simp only [Finset.mem_union, Finset.mem_insert] at this ⊢
    rcases this with h | rfl | h
    exacts [.inl h, absurd hx hL', .inr h]
  · intro h
    have hm := h.isNoncrossingPartialMatching
    have h' := isOpenPair_forestAdjoinRootParent hpar h
    refine ⟨h'.isNoncrossingPartialMatching, h'.isStrictAncestor,
      Finset.insert_subset ?_ h'.subset_unmatchedVertices, ?_,
      h'.subset_leftEndpoints_union.trans (Finset.union_subset_union_right
        (Finset.subset_insert _ _))⟩
    · refine mem_unmatchedVertices_iff.mpr ⟨⟨by omega, le_rfl⟩, fun p hp => ?_⟩
      have := hm.snd_le p hp
      have := hm.fst_lt_snd p hp
      omega
    · intro u hu p hp
      rcases Finset.mem_insert.mp hu with rfl | hu
      · have := hm.snd_le p hp; omega
      · exact h.exposed u hu p hp

/-- Matching the root `N + 1` to `a = max O` turns an open pair `(M, O)` of `(par, L)` into an
open pair `(M ∪ {(a, N + 1)}, O \ {a})` of `(par°, L)`. -/
private lemma isOpenPair_forestAdjoinRootParent_insert_max {N : ℕ} {par : ℕ → Option ℕ}
    {L : Finset ℕ} (hpar : IsParentMap N par) {M : Finset (ℕ × ℕ)} {O : Finset ℕ} {a : ℕ}
    (h : IsOpenPair N par L M O) (ha : a ∈ O) (hmax : ∀ u ∈ O, u ≤ a) :
    IsOpenPair (N + 1) (forestAdjoinRootParent N par) L (insert (a, N + 1) M) (O.erase a) := by
  have hm := h.isNoncrossingPartialMatching
  have haU := mem_unmatchedVertices_iff.mp (h.subset_unmatchedVertices ha)
  have h' := isOpenPair_forestAdjoinRootParent hpar h
  have hm' := h'.isNoncrossingPartialMatching
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · simp only [Finset.forall_mem_insert]; exact ⟨haU.1.1, hm'.one_le_fst⟩
  · simp only [Finset.forall_mem_insert]; exact ⟨by omega, hm'.fst_lt_snd⟩
  · simp only [Finset.forall_mem_insert]; exact ⟨le_rfl, hm'.snd_le⟩
  · have key : ∀ q ∈ M, ∀ x : ℕ, (x = a ∨ x = N + 1) → ¬ (x = q.1 ∨ x = q.2) := by
      rintro q hq x (rfl | rfl) (h1 | h1)
      · exact (haU.2 q hq).1 h1.symm
      · exact (haU.2 q hq).2 h1.symm
      · have := hm.fst_lt_snd q hq; have := hm.snd_le q hq; omega
      · have := hm.snd_le q hq; omega
    simp only [Finset.forall_mem_insert]
    refine ⟨⟨fun x hx _ => trivial, fun q hq x hx hx' => absurd hx' (key q hq x hx)⟩,
      fun p hp => ⟨fun x hx hx' => absurd hx (key p hp x hx'), hm'.eq_of_mem_of_mem p hp⟩⟩
  · simp only [Finset.forall_mem_insert]
    refine ⟨⟨by omega, fun q hq => ?_⟩, fun p hp => ⟨fun hc => ?_, hm'.noncrossing p hp⟩⟩
    · have := hm.snd_le q hq; omega
    · exact h.exposed a ha p hp ⟨hc.1, hc.2.1⟩
  · simp only [Finset.forall_mem_insert]
    exact ⟨(isStrictAncestor_forestAdjoinRootParent_iff hpar
      (Finset.mem_Icc.mpr haU.1)).mpr (.inl rfl),
      h'.isStrictAncestor⟩
  · intro u hu
    obtain ⟨hua, hu⟩ := Finset.mem_erase.mp hu
    have := mem_unmatchedVertices_iff.mp (h'.subset_unmatchedVertices hu)
    refine mem_unmatchedVertices_iff.mpr ⟨this.1, ?_⟩
    simp only [Finset.forall_mem_insert]
    refine ⟨⟨Ne.symm hua, ?_⟩, this.2⟩
    have := (mem_unmatchedVertices_iff.mp (h.subset_unmatchedVertices hu)).1; omega
  · intro u hu
    obtain ⟨hua, hu⟩ := Finset.mem_erase.mp hu
    simp only [Finset.forall_mem_insert]
    exact ⟨fun hc => by have := hmax u hu; omega, h.exposed u hu⟩
  · intro x hx
    have := h.subset_leftEndpoints_union hx
    simp only [Finset.mem_union, mem_leftEndpoints, Finset.exists_mem_insert,
      Finset.mem_erase] at this ⊢
    by_cases hxa : x = a
    · exact .inl (.inl hxa.symm)
    · rcases this with h | h
      exacts [.inl (.inr h), .inr ⟨hxa, h⟩]

/-- Conversely, unmatching the root `N + 1` from its partner `b` in an open pair `(M', O')` of
`(par°, L)` gives an open pair `(M' \ {(b, N + 1)}, O' ∪ {b})` of `(par, L)`, in which `b` is the
largest open vertex. -/
private lemma isOpenPair_of_forestAdjoinRootParent_mem {N : ℕ} {par : ℕ → Option ℕ}
    {L : Finset ℕ} (hpar : IsParentMap N par) {M : Finset (ℕ × ℕ)} {O : Finset ℕ} {b : ℕ}
    (h : IsOpenPair (N + 1) (forestAdjoinRootParent N par) L M O) (hb : (b, N + 1) ∈ M) :
    (∀ p ∈ M, p.2 = N + 1 → p = (b, N + 1)) ∧ (∀ u ∈ O, u < b) ∧
      IsOpenPair N par L (M.filter (·.2 ≠ N + 1)) (insert b O) := by
  have hm := h.isNoncrossingPartialMatching
  have huniq : ∀ p ∈ M, p.2 = N + 1 → p = (b, N + 1) := fun p hp hp2 =>
    hm.eq_of_mem_of_mem p hp _ hb (N + 1) (.inr hp2.symm) (.inr rfl)
  have hlt : ∀ u ∈ O, u < b := fun u hu => by
    have hU := mem_unmatchedVertices_iff.mp (h.subset_unmatchedVertices hu)
    have h1 := hU.2 _ hb
    have h2 := h.exposed u hu _ hb
    simp only at h1 h2
    omega
  have hb1 := hm.one_le_fst _ hb
  have hb2 := hm.fst_lt_snd _ hb
  simp only at hb1 hb2
  refine ⟨huniq, hlt, (isOpenPair_forestAdjoinRootParent_iff hpar
    (fun p hp => (Finset.mem_filter.mp hp).2) ?_).mp ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩⟩
  · rw [Finset.mem_insert, not_or]
    refine ⟨by omega, fun hN => ?_⟩
    exact ((mem_unmatchedVertices_iff.mp (h.subset_unmatchedVertices hN)).2 _ hb).2 rfl
  · exact fun p hp => hm.one_le_fst p (Finset.mem_filter.mp hp).1
  · exact fun p hp => hm.fst_lt_snd p (Finset.mem_filter.mp hp).1
  · exact fun p hp => hm.snd_le p (Finset.mem_filter.mp hp).1
  · exact fun p hp q hq => hm.eq_of_mem_of_mem p (Finset.mem_filter.mp hp).1 q
      (Finset.mem_filter.mp hq).1
  · exact fun p hp q hq => hm.noncrossing p (Finset.mem_filter.mp hp).1 q
      (Finset.mem_filter.mp hq).1
  · exact fun p hp => h.isStrictAncestor p (Finset.mem_filter.mp hp).1
  · intro u hu
    rcases Finset.mem_insert.mp hu with rfl | hu
    · refine mem_unmatchedVertices_iff.mpr ⟨⟨hb1, by omega⟩, fun p hp => ?_⟩
      obtain ⟨hp, hp2⟩ := Finset.mem_filter.mp hp
      refine ⟨fun he => hp2 ?_, fun he => hp2 ?_⟩
      · rw [hm.eq_of_mem_of_mem p hp _ hb p.1 (.inl rfl) (.inl he)]
      · rw [hm.eq_of_mem_of_mem p hp _ hb p.2 (.inr rfl) (.inl he)]
    · have := mem_unmatchedVertices_iff.mp (h.subset_unmatchedVertices hu)
      exact mem_unmatchedVertices_iff.mpr ⟨this.1, fun p hp => this.2 p (Finset.mem_filter.mp hp).1⟩
  · intro u hu p hp
    obtain ⟨hp, hp2⟩ := Finset.mem_filter.mp hp
    rcases Finset.mem_insert.mp hu with rfl | hu
    · rintro ⟨h1, h2⟩
      have := hm.snd_le p hp
      exact hm.noncrossing p hp _ hb ⟨h1, h2, by simp only; omega⟩
    · exact h.exposed u hu p hp
  · intro x hx
    have := h.subset_leftEndpoints_union hx
    simp only [Finset.mem_union, mem_leftEndpoints, Finset.mem_filter, Finset.mem_insert]
      at this ⊢
    rcases this with ⟨p, hp, rfl⟩ | h
    · by_cases hp2 : p.2 = N + 1
      · exact .inr (.inl (by rw [huniq p hp hp2]))
      · exact .inl ⟨p, ⟨hp, hp2⟩, rfl⟩
    · exact .inr (.inr h)

/-- Case `N + 1` unmatched and not open. -/
private lemma sum_case_unmatched {R σ : Type*} [CommSemiring R] {N : ℕ}
    {par : ℕ → Option ℕ} {L : Finset ℕ} (hpar : IsParentMap N par) (A B : ℕ → MvPolynomial σ R) :
    ∑ MO ∈ (openPairs (N + 1) (forestAdjoinRootParent N par) L).filter
        (fun MO => ¬ N + 1 ∈ MO.2 ∧ ¬ N + 1 ∈ MO.1.image Prod.snd), weight (N + 1) A B MO =
      ∑ MO ∈ openPairs N par L, rename some (A (N + 1)) * weight N A B MO := by
  have hset : (openPairs (N + 1) (forestAdjoinRootParent N par) L).filter
      (fun MO => ¬ N + 1 ∈ MO.2 ∧ ¬ N + 1 ∈ MO.1.image Prod.snd) = openPairs N par L := by
    ext ⟨M, O⟩
    simp only [Finset.mem_filter, mem_openPairs, Finset.mem_image, not_exists, not_and]
    constructor
    · rintro ⟨h, hO, hM⟩
      exact (isOpenPair_forestAdjoinRootParent_iff hpar hM hO).mp h
    · exact fun h => ⟨isOpenPair_forestAdjoinRootParent hpar h, succ_notMem_of_isOpenPair h,
        snd_ne_succ_of_isOpenPair h⟩
  rw [hset]
  refine Finset.sum_congr rfl fun ⟨M, O⟩ hMO => ?_
  have h := mem_openPairs.mp hMO
  have hm := h.isNoncrossingPartialMatching
  have hU : Finset.unmatchedVertices (N + 1) M \ O =
      insert (N + 1) (Finset.unmatchedVertices N M \ O) := by
    ext x
    simp only [Finset.mem_sdiff, mem_unmatchedVertices_iff, Finset.mem_insert]
    constructor
    · rintro ⟨⟨hx, hp⟩, hxO⟩
      by_cases hxN : x = N + 1
      · exact .inl hxN
      · exact .inr ⟨⟨⟨hx.1, by omega⟩, hp⟩, hxO⟩
    · rintro (rfl | ⟨⟨hx, hp⟩, hxO⟩)
      · refine ⟨⟨⟨by omega, le_rfl⟩, fun p hp => ?_⟩, fun hO => ?_⟩
        · have := hm.snd_le p hp; have := hm.fst_lt_snd p hp; omega
        · exact succ_notMem_of_isOpenPair h hO
      · exact ⟨⟨⟨hx.1, by omega⟩, hp⟩, hxO⟩
  have hN : N + 1 ∉ Finset.unmatchedVertices N M \ O := fun hN => by
    have := (mem_unmatchedVertices_iff.mp (Finset.mem_sdiff.mp hN).1).1; omega
  simp only [weight, hU, Finset.prod_insert hN]
  ring

/-- Case `N + 1` open. -/
private lemma sum_case_open {R σ : Type*} [CommSemiring R] {N : ℕ}
    {par : ℕ → Option ℕ} {L : Finset ℕ} (hpar : IsParentMap N par) (hL : L ⊆ Finset.Icc 1 N)
    (A B : ℕ → MvPolynomial σ R) :
    ∑ MO ∈ (openPairs (N + 1) (forestAdjoinRootParent N par) L).filter (fun MO => N + 1 ∈ MO.2),
        weight (N + 1) A B MO =
      ∑ MO ∈ openPairs N par L, X none * weight N A B MO := by
  have hO : ∀ MO ∈ openPairs N par L, N + 1 ∉ MO.2 := fun MO hMO =>
    succ_notMem_of_isOpenPair (mem_openPairs.mp hMO)
  symm
  refine Finset.sum_nbij' (fun MO => (MO.1, insert (N + 1) MO.2))
    (fun MO => (MO.1, MO.2.erase (N + 1))) ?_ ?_ ?_ ?_ ?_
  · intro MO hMO
    simp only [Finset.mem_filter, mem_openPairs, Finset.mem_insert_self, and_true]
    exact (isOpenPair_forestAdjoinRootParent_insert_iff hpar hL (hO MO hMO)).mpr
      (mem_openPairs.mp hMO)
  · intro MO hMO
    simp only [Finset.mem_filter, mem_openPairs] at hMO
    rw [mem_openPairs]
    refine (isOpenPair_forestAdjoinRootParent_insert_iff hpar hL
      (Finset.notMem_erase _ _)).mp ?_
    rw [Finset.insert_erase hMO.2]
    exact hMO.1
  · intro MO hMO
    simp [Finset.erase_insert (hO MO hMO)]
  · intro MO hMO
    simp [Finset.insert_erase (Finset.mem_filter.mp hMO).2]
  · rintro ⟨M, O⟩ hMO
    have hU : Finset.unmatchedVertices (N + 1) M \ insert (N + 1) O =
        Finset.unmatchedVertices N M \ O := by
      ext x
      simp only [Finset.mem_sdiff, mem_unmatchedVertices_iff, Finset.mem_insert, not_or]
      constructor
      · rintro ⟨⟨hx, hp⟩, hxN, hxO⟩
        exact ⟨⟨⟨hx.1, by omega⟩, hp⟩, hxO⟩
      · rintro ⟨⟨hx, hp⟩, hxO⟩
        exact ⟨⟨⟨hx.1, by omega⟩, hp⟩, by omega, hxO⟩
    simp only [weight, hU, Finset.card_insert_of_notMem (hO _ hMO)]
    ring

/-- Case `N + 1` matched. -/
private lemma sum_case_matched {R σ : Type*} [CommSemiring R] {N : ℕ}
    {par : ℕ → Option ℕ} {L : Finset ℕ} (hpar : IsParentMap N par) (A B : ℕ → MvPolynomial σ R) :
    ∑ MO ∈ (openPairs (N + 1) (forestAdjoinRootParent N par) L).filter
        (fun MO => ¬ N + 1 ∈ MO.2 ∧ N + 1 ∈ MO.1.image Prod.snd), weight (N + 1) A B MO =
      ∑ MO ∈ (openPairs N par L).filter (fun MO => MO.2.Nonempty),
        rename some (B (N + 1)) *
          (X none ^ (MO.2.card - 1) * rename some (weightFree N A B MO)) := by
  classical
  symm
  refine Finset.sum_nbij' (fun MO => (insert (MO.2.sup id, N + 1) MO.1, MO.2.erase (MO.2.sup id)))
    (fun MO => (MO.1.filter (·.2 ≠ N + 1),
      insert ((MO.1.filter (·.2 = N + 1)).sup Prod.fst) MO.2)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨M, O⟩ hMO
    obtain ⟨hMO, hne⟩ := Finset.mem_filter.mp hMO
    have h := mem_openPairs.mp hMO
    obtain ⟨a, ha, hsup⟩ := Finset.exists_mem_eq_sup O hne id
    simp only [hsup, id] at ha ⊢
    have hmax : ∀ u ∈ O, u ≤ a := fun u hu => by
      have := Finset.le_sup (f := id) hu
      rwa [hsup] at this
    simp only [Finset.mem_filter, mem_openPairs, Finset.mem_image, Finset.mem_erase,
      Finset.exists_mem_insert]
    refine ⟨isOpenPair_forestAdjoinRootParent_insert_max hpar h ha hmax, fun ⟨_, hN⟩ => ?_,
      by simp⟩
    have := hmax _ hN
    have := (mem_unmatchedVertices_iff.mp (h.subset_unmatchedVertices ha)).1
    omega
  · rintro ⟨M, O⟩ hMO
    simp only [Finset.mem_filter, mem_openPairs, Finset.mem_image] at hMO
    obtain ⟨h, -, ⟨b, c⟩, hb, rfl⟩ := hMO
    obtain ⟨huniq, -, h'⟩ := isOpenPair_of_forestAdjoinRootParent_mem hpar h hb
    have hfilt := filter_snd_eq_singleton hb huniq
    simp only [Finset.mem_filter, mem_openPairs, hfilt, Finset.sup_singleton]
    exact ⟨h', Finset.insert_nonempty _ _⟩
  · rintro ⟨M, O⟩ hMO
    obtain ⟨hMO, hne⟩ := Finset.mem_filter.mp hMO
    have h := mem_openPairs.mp hMO
    obtain ⟨a, ha, hsup⟩ := Finset.exists_mem_eq_sup O hne id
    simp only [hsup, id]
    have h1 : (insert (a, N + 1) M).filter (·.2 ≠ N + 1) = M := by
      rw [Finset.filter_insert, if_neg (by simp)]
      exact Finset.filter_true_of_mem (snd_ne_succ_of_isOpenPair h)
    have h2 : (insert (a, N + 1) M).filter (·.2 = N + 1) = {(a, N + 1)} := by
      rw [Finset.filter_insert, if_pos rfl,
        Finset.filter_false_of_mem (snd_ne_succ_of_isOpenPair h)]
      rfl
    simp only [h1, h2, Finset.sup_singleton, Finset.insert_erase ha]
  · rintro ⟨M, O⟩ hMO
    simp only [Finset.mem_filter, mem_openPairs, Finset.mem_image] at hMO
    obtain ⟨h, -, ⟨b, c⟩, hb, rfl⟩ := hMO
    obtain ⟨huniq, hlt, -⟩ := isOpenPair_of_forestAdjoinRootParent_mem hpar h hb
    have hfilt := filter_snd_eq_singleton hb huniq
    have hsup : (insert b O).sup id = b :=
      le_antisymm (Finset.sup_le fun u hu => by
        rcases Finset.mem_insert.mp hu with rfl | hu
        exacts [le_rfl, (hlt u hu).le]) (Finset.le_sup (f := id) (Finset.mem_insert_self _ _))
    have hbO : b ∉ O := fun hbO => lt_irrefl _ (hlt b hbO)
    simp only [hfilt, Finset.sup_singleton, hsup, Finset.erase_insert hbO, Prod.mk.injEq,
      and_true]
    exact insert_filter_snd_ne_eq hb huniq
  · rintro ⟨M, O⟩ hMO
    obtain ⟨hMO, hne⟩ := Finset.mem_filter.mp hMO
    have h := mem_openPairs.mp hMO
    have hm := h.isNoncrossingPartialMatching
    obtain ⟨a, ha, hsup⟩ := Finset.exists_mem_eq_sup O hne id
    simp only [hsup, id]
    have haM : (a, N + 1) ∉ M := fun haM => by have := hm.snd_le _ haM; simp at this
    simp only [weight, weightFree, Finset.prod_insert haM,
      unmatchedVertices_succ_insert_sdiff_erase ha, Finset.card_erase_of_mem ha,
      map_mul, map_prod]
    ring

/-- Root recurrence: adjoining an unmarked root `N + 1` to a forest `par` on `[N]` with marked set
`L ⊆ [N]` turns its vertex-weighted open-pair polynomial `P` into
`(A_{N+1} + t) P + B_{N+1} δ_t P`. -/
@[lognarayana "lem_weighted_open_poly_root"]
public theorem vertexWeightedOpenPairPolynomial_forestAdjoinRoot {R σ : Type*}
    [CommSemiring R] {N : ℕ} {par : ℕ → Option ℕ} {L : Finset ℕ}
    (hpar : IsParentMap N par) (hL : L ⊆ Finset.Icc 1 N) (A B : ℕ → MvPolynomial σ R) :
    vertexWeightedOpenPairPolynomial (N + 1) (forestAdjoinRootParent N par) L A B =
      (rename some (A (N + 1)) + X none) * vertexWeightedOpenPairPolynomial N par L A B +
        rename some (B (N + 1)) * divX none (vertexWeightedOpenPairPolynomial N par L A B) := by
  classical
  set S := openPairs (N + 1) (forestAdjoinRootParent N par) L
  have hsplit : ∑ MO ∈ S.filter (fun MO => ¬ N + 1 ∈ MO.2), weight (N + 1) A B MO =
      ∑ MO ∈ S.filter (fun MO => ¬ N + 1 ∈ MO.2 ∧ N + 1 ∈ MO.1.image Prod.snd),
        weight (N + 1) A B MO +
      ∑ MO ∈ S.filter (fun MO => ¬ N + 1 ∈ MO.2 ∧ ¬ N + 1 ∈ MO.1.image Prod.snd),
        weight (N + 1) A B MO := by
    rw [← Finset.sum_filter_add_sum_filter_not (S.filter _)
      (fun MO => N + 1 ∈ MO.1.image Prod.snd), Finset.filter_filter, Finset.filter_filter]
  rw [divX_vertexWeightedOpenPairPolynomial, vertexWeightedOpenPairPolynomial_eq,
    vertexWeightedOpenPairPolynomial_eq,
    ← Finset.sum_filter_add_sum_filter_not S (fun MO => N + 1 ∈ MO.2), hsplit,
    sum_case_open hpar hL, sum_case_matched hpar, sum_case_unmatched hpar, add_mul,
    Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  abel
