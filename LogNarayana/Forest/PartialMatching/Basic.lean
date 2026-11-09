/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module
public import LogNarayana.Forest.PartialMatching.Defs
public import LogNarayana.Matroid.BasisGeneratingPolynomial.Basic
public import LogNarayana.Lorentzian.BrandenHuh.Basic
public import LogNarayana.Forest.LaminarMatroid.Defs
public import LogNarayana.Forest.LaminarMatroid.Basic

/-!
# Partial matchings and factorial normalization

This file proves that the factorial normalization in `t` of the open-matching polynomial of a
postorder forest is Lorentzian.

The route goes through matroids. For a matroid `M` and `r ∈ ℕ`, the independent sets of `M`
with at most `r` elements form a matroid, the truncation of `M` to rank `r`, whose bases are
the independent sets of size exactly `r` when `M` has one. Truncating the direct sum of a
matroid `M` of rank at most `N` with a free matroid on `k ≥ N` new elements to rank `N`, and
substituting `w_κ ↦ t / k` in its basis generating polynomial, gives the Lorentzian polynomial
`∑_{I ∈ 𝕀(M)} (k choose (N - |I|)) k^{-(N - |I|)} z^I t^{N - |I|}`. Since
`choose k h / k ^ h → 1 / h!`, these converge coefficientwise to
`∑_{I ∈ 𝕀(M)} z^I t^{N - |I|} / (N - |I|)!`, which is therefore Lorentzian.

The open-matching polynomial `P_{par,L}(x, y, t)` of a postorder forest is the generating
polynomial `∑_{I ∈ 𝕀_{par,L}} z^I t^{N - |I|}` of the forest independence family, the family of
independent sets of a matroid of rank at most `N`, so its factorial normalization `𝓝_t P_{par,L}`
is of the form above. At `t = 0`, both `P_{par,L}` and `𝓝_t P_{par,L}` specialize to the forest
matching polynomial `Z_{par,L}(x, y)`.

## Main results

* `Matroid.exists_indep_iff_mem_truncationFamily`: the truncation of a matroid is a matroid.
* `Matroid.isBase_iff_of_indep_iff_mem_truncationFamily`: the bases of the truncation to rank `r`
  are the independent sets of size `r`.
* `Nat.tendsto_choose_div_pow_atTop`: `choose k h / k ^ h → 1 / h!` as `k → ∞`.
* `Matroid.isLorentzian_sum_indep_choose_div_pow_mul_X_pow`: truncated free extensions give
  Lorentzian polynomials.
* `Matroid.isLorentzian_sum_indep_mul_X_pow_div_factorial`: the normalized independent-set
  polynomial of a matroid of rank at most `N` is Lorentzian.
* `MvPolynomial.factorialNormalization_forestOpenPoly`: `𝓝_t` divides the term of an open pair
  `(M, O)` of `P_{par,L}` by `|O|!`.
* `aeval_none_zero_forestOpenPoly`, `MvPolynomial.aeval_factorialNormalization_forestOpenPoly`:
  `P_{par,L}` and `𝓝_t P_{par,L}` at `t = 0` are `Z_{par,L}`.
* `forestOpenPoly_eq_sum_forestIndepFamily`: `P_{par,L} = ∑_{I ∈ 𝕀_{par,L}} z^I t^{N - |I|}`.
* `isLorentzian_factorialNormalization_forestOpenPoly`: `𝓝_t P_{par,L}` is Lorentzian.

## Implementation notes

The truncation results are stated for arbitrary matroids, with sizes measured by `Set.encard`;
the paper's finite ground set is not needed, since augmentation between finite independent
sets holds in every matroid.

For a matroid on a finite type `α`, the polynomials live in `MvPolynomial (Option α) ℝ`, with
`z_e = X (some e)` and `t = X none`, and the independent sets are enumerated as the finsets `I`
with `M.Indep ↑I`. For the open-matching polynomial the variables are `Option (Bool × ℕ)`, with
`t = X none`, `x_v = X (some (true, v))` and `y_v = X (some (false, v))`. The substitution
`t = 0` is the algebra map `aeval (Option.elim' 0 X)` onto `MvPolynomial (Bool × ℕ) R`. The
identities for `forestOpenPoly` other than `forestOpenPoly_eq_sum_forestIndepFamily` hold for
every `par : ℕ → Option ℕ` and every finite `L ⊆ ℕ`, so the paper's hypotheses that `par` is a
parent map and `L ⊆ [N]` are not imposed there.

Being Lorentzian is a property of polynomials in finitely many variables, while the variable
type of `forestOpenPoly` is infinite. The main theorem therefore says that `𝓝_t P_{par,L}` is the
image, under the injective renaming induced by `Bool × [N] ↪ Bool × ℕ`, of a Lorentzian
polynomial in `ℝ[x_v, y_v, t : v ∈ [N]]`.

Three results of Brändén–Huh are cited, not proved, and enter as hypotheses: normalized support
polynomials of M-convex sets are Lorentzian [BH, Theorem 3.10], nonnegative linear
substitutions preserve Lorentzian polynomials [BH, Theorem 2.10], and the Lorentzian
polynomials of a fixed degree are closed under coefficientwise limits [BH, Theorem 2.25].

## References

* [LogNarayana] *Log-Concavity in Narayana Transforms and Stack-Sorting Fibers*, Sections 3, 4.
* [BH] P. Brändén, J. Huh, *Lorentzian polynomials*, Ann. of Math. 192 (2020).
-/

open Filter Topology Asymptotics MvPolynomial

universe u

/-! ### Truncations of matroids -/

namespace Matroid

/-- **Truncation.** For a matroid `M` and `r : ℕ`, the independent sets of `M` with at most `r`
elements are the independent sets of a matroid on the ground set of `M`. -/
@[lognarayana "lem_truncation_matroid_exists"]
public theorem exists_indep_iff_mem_truncationFamily {α : Type*} (M : Matroid α) (r : ℕ) :
    ∃ N : Matroid α, N.E = M.E ∧ ∀ I : Set α, N.Indep I ↔ I ∈ M.truncationFamily r :=
  ⟨(IndepMatroid.ofBddAugment M.E (fun I ↦ M.Indep I ∧ I.encard ≤ r)
    ⟨M.empty_indep, by simp⟩
    (fun I J hJ hIJ ↦ ⟨hJ.1.subset hIJ, (Set.encard_le_encard hIJ).trans hJ.2⟩)
    (fun I J hI hJ hIJ ↦
      let ⟨e, he, hins⟩ := hI.1.augment hJ.1 hIJ
      ⟨e, he.1, he.2, hins, (Set.encard_insert_of_notMem he.2).trans_le
        ((Order.add_one_le_of_lt hIJ).trans hJ.2)⟩)
    ⟨r, fun I hI ↦ hI.2⟩
    (fun I hI ↦ hI.1.subset_ground)).matroid, rfl, fun _ ↦ Iff.rfl⟩

/-- **Bases of a truncation.** If `M` has an independent set with `r` elements and the
independent sets of `N` are the independent sets of `M` with at most `r` elements, then the bases
of `N` are the independent sets of `M` with exactly `r` elements. -/
@[lognarayana "lem_truncation_bases"]
public theorem isBase_iff_of_indep_iff_mem_truncationFamily {α : Type*} {M N : Matroid α}
    {r : ℕ} (hr : ∃ I, M.Indep I ∧ I.encard = r)
    (hN : ∀ I : Set α, N.Indep I ↔ I ∈ M.truncationFamily r) (B : Set α) :
    N.IsBase B ↔ M.Indep B ∧ B.encard = r := by
  rw [isBase_iff_maximal_indep]
  constructor
  · intro hB
    obtain ⟨hBM, hBr⟩ := (hN B).1 hB.prop
    refine ⟨hBM, hBr.antisymm (not_lt.1 fun hlt ↦ ?_)⟩
    obtain ⟨J, hJ, hJr⟩ := hr
    obtain ⟨e, he, hins⟩ := hBM.augment hJ (hJr ▸ hlt)
    have hNins : N.Indep (insert e B) := (hN _).2
      ⟨hins, (Set.encard_insert_of_notMem he.2).trans_le (Order.add_one_le_of_lt hlt)⟩
    exact he.2 (hB.eq_of_subset hNins (Set.subset_insert e B) ▸ Set.mem_insert e B)
  · rintro ⟨hBM, hBr⟩
    refine ⟨(hN B).2 ⟨hBM, hBr.le⟩, fun J hJ hBJ ↦ ?_⟩
    exact ((Set.finite_of_encard_eq_coe hBr).eq_of_subset_of_encard_le hBJ
      (((hN J).1 hJ).2.trans hBr.ge)).ge

end Matroid

/-! ### The limit of `choose k h / k ^ h` -/

namespace Nat

/-- For every `h ∈ ℕ`, `choose k h / k ^ h → 1 / h!` as `k → ∞`: by `isEquivalent_choose`,
`choose k h` is asymptotically equivalent to `k ^ h / h!`. -/
@[lognarayana "lem_binom_ratio_limit"]
public theorem tendsto_choose_div_pow_atTop (h : ℕ) :
    Tendsto (fun k : ℕ => (k.choose h : ℝ) / (k : ℝ) ^ h) atTop (𝓝 (1 / (h ! : ℝ))) := by
  refine ((isEquivalent_choose h).div IsEquivalent.refl).symm.tendsto_nhds <|
    tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with k hk
  simp [hk, div_right_comm _ (_ : ℝ) ((k : ℝ) ^ h)]

end Nat

/-! ### Independent-set polynomials of matroids of bounded rank -/

namespace Matroid

/-- An independent set of a matroid whose bases have at most `N` elements has at most `N`
elements. -/
private lemma card_le_of_indep {α : Type*} {M : Matroid α} {N : ℕ}
    (hN : ∀ B, M.IsBase B → B.encard ≤ N) {I : Finset α} (hI : M.Indep ↑I) : I.card ≤ N := by
  obtain ⟨B, hB, hIB⟩ := hI.exists_isBase_superset
  exact_mod_cast (Set.encard_coe_eq_coe_finsetCard I ▸ Set.encard_le_encard hIB).trans (hN B hB)

/-- The rank-`N` truncation of `M ⊕ U_{k,k}`: its bases are the `N`-sets whose part in `α` is
independent in `M`. -/
private lemma exists_isBase_iff_indep_toLeft {α : Type u} (M : Matroid α) {N k : ℕ}
    (hk : N ≤ k) : ∃ MN : Matroid (α ⊕ ULift.{u} (Fin k)), ∀ B : Finset (α ⊕ ULift.{u} (Fin k)),
      MN.IsBase ↑B ↔ M.Indep ↑B.toLeft ∧ B.card = N := by
  let Mp : Matroid (α ⊕ ULift.{u} (Fin k)) := M.sum (freeOn Set.univ)
  obtain ⟨MN, -, hMN⟩ := Mp.exists_indep_iff_mem_truncationFamily N
  obtain ⟨J, -, hJ⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset (ULift.{u} (Fin k)))) (n := N) (by simpa using hk)
  have hr : ∃ I, Mp.Indep I ∧ I.encard = N :=
    ⟨((J.map Function.Embedding.inr : Finset (α ⊕ ULift.{u} (Fin k))) : Set _), by simp [Mp],
      by rw [Set.encard_coe_eq_coe_finsetCard, Finset.card_map, hJ]⟩
  refine ⟨MN, fun B => ?_⟩
  rw [isBase_iff_of_indep_iff_mem_truncationFamily hr hMN]
  have hl : Sum.inl ⁻¹' (B : Set (α ⊕ ULift.{u} (Fin k))) = (B.toLeft : Set α) := by ext; simp
  simp [Mp, Set.encard_coe_eq_coe_finsetCard, hl]

/-- Summing `c ^ |J|` over the `m`-subsets `J` of a `k`-set, written as the subsets with
`n + |J| = N` where `m = N - n`. -/
private lemma sum_filter_add_card_eq {k n N : ℕ} (hn : n ≤ N) {R : Type*} [CommSemiring R]
    (c : R) : ∑ J ∈ (Finset.univ : Finset (Finset (ULift.{u} (Fin k)))).filter
      (fun J => n + J.card = N), c ^ J.card = (k.choose (N - n) : R) * c ^ (N - n) := by
  have hf : (Finset.univ : Finset (Finset (ULift.{u} (Fin k)))).filter (fun J => n + J.card = N)
      = Finset.powersetCard (N - n) Finset.univ := by
    ext J; simp; omega
  rw [hf, Finset.sum_congr rfl fun J hJ => by rw [(Finset.mem_powersetCard.1 hJ).2],
    Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_ulift,
    Fintype.card_fin, nsmul_eq_mul]

/-- The substitution `z_e ↦ z_e`, `w_κ ↦ t / k` sends the basis generating polynomial of the
rank-`N` truncation of `M ⊕ U_{k,k}` to
`∑_{I ∈ 𝕀(M)} (k choose (N - |I|)) k^{-(N - |I|)} z^I t^{N - |I|}`. -/
private lemma aeval_basisGeneratingPolynomial_eq {α : Type u} [Fintype α] {M : Matroid α}
    {N : ℕ} (hN : ∀ B, M.IsBase B → B.encard ≤ N) {k : ℕ}
    {MN : Matroid (α ⊕ ULift.{u} (Fin k))}
    (hbase : ∀ B : Finset (α ⊕ ULift.{u} (Fin k)),
      MN.IsBase ↑B ↔ M.Indep ↑B.toLeft ∧ B.card = N) :
    open scoped Classical in
    aeval (Sum.elim (fun e => X (some e)) (fun _ => (1 / (k : ℝ)) • X none))
        (MN.basisGeneratingPolynomial ℝ) =
      ∑ I ∈ (Finset.univ : Finset (Finset α)).filter (fun I : Finset α => M.Indep (I : Set α)),
        C ((k.choose (N - I.card) : ℝ) / (k : ℝ) ^ (N - I.card)) *
          (∏ e ∈ I, X (some e)) * X none ^ (N - I.card) := by
  classical
  let e : Finset α × Finset (ULift.{u} (Fin k)) ≃ Finset (α ⊕ ULift.{u} (Fin k)) :=
    ⟨fun p => p.1.disjSum p.2, fun s => (s.toLeft, s.toRight), fun p => by simp,
      fun s => Finset.toLeft_disjSum_toRight⟩
  unfold basisGeneratingPolynomial
  simp only [map_sum, map_prod, aeval_X]
  rw [Finset.sum_filter, Finset.sum_filter, ← e.sum_comp, Fintype.sum_prod_type]
  refine Fintype.sum_congr _ _ fun I => ?_
  simp only [e, Equiv.coe_fn_mk, hbase, Finset.toLeft_disjSum, Finset.card_disjSum,
    Finset.prod_disjSum, Sum.elim_inl, Sum.elim_inr, Finset.prod_const]
  by_cases hI : M.Indep (I : Set α)
  · simp only [hI, true_and, if_true]
    rw [← Finset.sum_filter, ← Finset.mul_sum, sum_filter_add_card_eq (card_le_of_indep hN hI)]
    simp only [smul_eq_C_mul, div_eq_mul_inv, map_mul, map_pow, map_natCast,
      one_mul, ← inv_pow]
    ring
  · simp [hI]

/-- **Truncated free extensions.** Let `M` be a matroid on a finite type `α`, `N` a bound on
the size of its bases, and `k ≥ N` with `k ≥ 1`. Then
`∑_{I ∈ 𝕀(M)} (k choose (N - |I|)) k^{-(N - |I|)} z^I t^{N - |I|}` is Lorentzian, given the
Brändén–Huh theorems on normalized support polynomials of M-convex sets and on nonnegative
linear substitutions: it is the image of the basis generating polynomial of the rank-`N`
truncation of `M ⊕ U_{k,k}` under the nonnegative substitution `w_κ ↦ t / k`. -/
@[lognarayana "lem_partial_matroid_approx"]
public theorem isLorentzian_sum_indep_choose_div_pow_mul_X_pow
    {α : Type u} [Fintype α]
    (hBH : ∀ (σ : Type u) [Fintype σ], NormalizedSupportPolyLorentzianOfMConvex σ)
    (hsub : ∀ (σ τ : Type u) [Fintype σ] [Fintype τ], LorentzianNonnegLinearSubstitution σ τ)
    (M : Matroid α) (N : ℕ) (hN : ∀ B, M.IsBase B → B.encard ≤ N) (k : ℕ) (hk : N ≤ k)
    (hk1 : 1 ≤ k) :
    open scoped Classical in
    (∑ I ∈ (Finset.univ : Finset (Finset α)).filter
        (fun I : Finset α => M.Indep (I : Set α)),
      C ((k.choose (N - I.card) : ℝ) / (k : ℝ) ^ (N - I.card)) *
        (∏ e ∈ I, X (some e)) * X none ^ (N - I.card) :
      MvPolynomial (Option α) ℝ).IsLorentzian := by
  classical
  obtain ⟨MN, hbase⟩ := exists_isBase_iff_indep_toLeft M hk
  -- the nonnegative substitution `z_e ↦ z_e`, `w_κ ↦ t / k`
  let a : (α ⊕ ULift.{u} (Fin k)) → Option α → ℝ :=
    Sum.elim (fun e j => if j = some e then 1 else 0) (fun _ j => if j = none then 1 / k else 0)
  have hg : (fun i => ∑ j, a i j • (X j : MvPolynomial (Option α) ℝ)) =
      Sum.elim (fun e => X (some e)) (fun _ => (1 / (k : ℝ)) • X none) := by
    funext i
    rcases i with e | κ <;> simp [a, ite_smul]
  have h := hsub _ _ a (by
      rintro (e | κ) j <;> simp only [one_div, Sum.elim_inl, Sum.elim_inr, a] <;> split_ifs <;>
        positivity) _
    (MN.isLorentzian_basisGeneratingPolynomial (hBH _))
  rwa [hg, aeval_basisGeneratingPolynomial_eq hN hbase] at h

/-- The monomial `c · z^I · t^(N - |I|)` is homogeneous of degree `N` when `|I| ≤ N`. -/
private lemma isHomogeneous_C_mul_prod_X_mul_X_pow {α : Type u} (c : ℝ) {I : Finset α}
    {N : ℕ} (hI : I.card ≤ N) :
    (C c * (∏ e ∈ I, X (some e)) * X none ^ (N - I.card) :
      MvPolynomial (Option α) ℝ).IsHomogeneous N := by
  have h := ((isHomogeneous_C _ c).mul (IsHomogeneous.prod I _ (fun _ => 1)
    fun e _ => isHomogeneous_X ℝ (some e))).mul ((isHomogeneous_X ℝ none).pow (N - I.card))
  convert h using 1
  simp only [Finset.sum_const, smul_eq_mul, mul_one, zero_add]
  omega

/-- If the scalars `a k I` converge to `b I`, then every coefficient of `∑ I, a k I • m I`
converges to the corresponding coefficient of `∑ I, b I • m I`. -/
private lemma tendsto_coeff_sum_C_mul {σ ι κ : Type*} {l : Filter κ} {S : Finset ι}
    {a : κ → ι → ℝ} {b : ι → ℝ} (m : ι → MvPolynomial σ ℝ)
    (h : ∀ I ∈ S, Tendsto (a · I) l (𝓝 (b I))) (β : σ →₀ ℕ) :
    Tendsto (fun k => (∑ I ∈ S, C (a k I) * m I).coeff β) l
      (𝓝 ((∑ I ∈ S, C (b I) * m I).coeff β)) := by
  simp only [coeff_sum, coeff_C_mul]
  exact tendsto_finsetSum _ fun I hI => (h I hI).mul_const _

/-- **Independent-set polynomials are Lorentzian.** Let `M` be a matroid on a finite type `α`
and `N` a bound on the size of its bases. Then `∑_{I ∈ 𝕀(M)} z^I t^{N - |I|} / (N - |I|)!` is
Lorentzian, given the Brändén–Huh theorems on normalized support polynomials of M-convex sets,
on nonnegative linear substitutions, and on closedness of the Lorentzian class: it is the
coefficientwise limit as `k → ∞` of the homogeneous Lorentzian polynomials
`isLorentzian_sum_indep_choose_div_pow_mul_X_pow`, by `Nat.tendsto_choose_div_pow_atTop`. -/
@[lognarayana "prop_partial_matroid_lorentzian"]
public theorem isLorentzian_sum_indep_mul_X_pow_div_factorial
    {α : Type u} [Fintype α]
    (hBH : ∀ (σ : Type u) [Fintype σ], NormalizedSupportPolyLorentzianOfMConvex σ)
    (hsub : ∀ (σ τ : Type u) [Fintype σ] [Fintype τ], LorentzianNonnegLinearSubstitution σ τ)
    (hclosed : IsLorentzianClosed (Option α))
    (M : Matroid α) (N : ℕ) (hN : ∀ B, M.IsBase B → B.encard ≤ N) :
    open scoped Classical in
    (∑ I ∈ (Finset.univ : Finset (Finset α)).filter
        (fun I : Finset α => M.Indep (I : Set α)),
      (∏ e ∈ I, X (some e)) * C (1 / ((N - I.card).factorial : ℝ)) * X none ^ (N - I.card) :
      MvPolynomial (Option α) ℝ).IsLorentzian := by
  classical
  set S := (Finset.univ : Finset (Finset α)).filter (fun I : Finset α => M.Indep (I : Set α))
  let m : Finset α → MvPolynomial (Option α) ℝ :=
    fun I => (∏ e ∈ I, X (some e)) * X none ^ (N - I.card)
  rw [show (∑ I ∈ S, (∏ e ∈ I, X (some e)) * C (1 / ((N - I.card).factorial : ℝ)) *
      X none ^ (N - I.card)) = ∑ I ∈ S, C (1 / ((N - I.card).factorial : ℝ)) * m I from
    Finset.sum_congr rfl fun _ _ => by ring]
  refine hclosed.isLorentzian_of_eventually N
    (fun k => ∑ I ∈ S, C ((k.choose (N - I.card) : ℝ) / k ^ (N - I.card)) * m I) _
    ?_ ?_
  · filter_upwards [eventually_ge_atTop (max N 1)] with k hk
    simp only [m, ← mul_assoc]
    exact ⟨isLorentzian_sum_indep_choose_div_pow_mul_X_pow hBH hsub M N hN k
      (le_of_max_le_left hk) (le_of_max_le_right hk), IsHomogeneous.sum _ _ _ fun I hI =>
        isHomogeneous_C_mul_prod_X_mul_X_pow _ (card_le_of_indep hN (Finset.mem_filter.1 hI).2)⟩
  · intro β
    exact tendsto_coeff_sum_C_mul m (fun I _ => Nat.tendsto_choose_div_pow_atTop _) β

end Matroid

/-! ### The open-matching polynomial and its factorial normalization -/

namespace MvPolynomial

/-- The factorial normalization on a single monomial. -/
private lemma factorialNormalization_monomial {σ R : Type*} [CommSemiring R] [Algebra ℚ R]
    (t : σ) (α : σ →₀ ℕ) (c : R) :
    factorialNormalization t (monomial α c) =
      monomial α (c * algebraMap ℚ R (1 / ((α t).factorial : ℚ))) := by
  have h : monomial α c = c • (basisMonomials σ R) α := by
    simp [coe_basisMonomials, smul_monomial]
  rw [h, map_smul, factorialNormalization, Module.Basis.constr_basis, smul_monomial, smul_eq_mul]

/-- If `f` does not involve `t`, then `𝓝_t (t ^ k * f) = t ^ k * f / k!`. -/
private lemma factorialNormalization_X_pow_mul {σ R : Type*} [CommSemiring R] [Algebra ℚ R]
    (t : σ) (f : MvPolynomial σ R) (hf : t ∉ f.vars) (k : ℕ) :
    factorialNormalization t (X t ^ k * f) =
      C (algebraMap ℚ R (1 / (k.factorial : ℚ))) * X t ^ k * f := by
  classical
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  rw [Finset.mul_sum, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmt : m t = 0 := by
    by_contra h
    exact hf ((mem_vars_iff_mem_support t).2 ⟨m, hm, Finsupp.mem_support_iff.2 h⟩)
  rw [X_pow_eq_monomial, monomial_mul, factorialNormalization_monomial, C_mul_monomial,
    monomial_mul]
  simp [hmt, mul_comm]

/-- A polynomial renamed along `some` does not involve `none`, so
`𝓝_t (t ^ k * rename some f) = t ^ k * rename some f / k!` for `t = X none`. -/
private lemma factorialNormalization_X_none_pow_mul_rename_some {β R : Type*} [CommSemiring R]
    [Algebra ℚ R] (f : MvPolynomial β R) (k : ℕ) :
    factorialNormalization none (X none ^ k * rename some f) =
      C (algebraMap ℚ R (1 / (k.factorial : ℚ))) * X none ^ k * rename some f := by
  classical
  exact factorialNormalization_X_pow_mul _ _ (fun hn => by simpa using vars_rename _ _ hn) k

open Classical in
/-- The factorial normalization in `t` of the open-matching polynomial:
`𝓝_t P_{par,L}(x, y, t) = ∑_{(M,O)} t^{|O|} / |O|! ∏_{v ∈ R(M)} x_v y_v
∏_{v ∈ U(M) \ O} (x_v + y_v)`, the sum over all open pairs `(M, O)` for `(par, L)` on `[N]`.
Each term of `forestOpenPoly` is `t ^ |O|` times a polynomial not involving `t`. -/
@[lognarayana "lem_forest_open_poly_normalized"]
public theorem factorialNormalization_forestOpenPoly (R : Type*) [CommSemiring R] [Algebra ℚ R]
    (N : ℕ) (par : ℕ → Option ℕ) (L : Finset ℕ) :
    factorialNormalization none (forestOpenPoly R N par L) =
      ∑ p ∈ (((Finset.Icc 1 N ×ˢ Finset.Icc 1 N).powerset ×ˢ (Finset.Icc 1 N).powerset).filter
          fun p : Finset (ℕ × ℕ) × Finset ℕ => IsOpenPair N par L p.1 p.2),
        C (algebraMap ℚ R (1 / (p.2.card.factorial : ℚ))) * X none ^ p.2.card *
          (∏ v ∈ p.1.image Prod.snd, X (some (true, v)) * X (some (false, v))) *
          ∏ v ∈ Finset.unmatchedVertices N p.1 \ p.2,
            (X (some (true, v)) + X (some (false, v))) := by
  rw [forestOpenPoly, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  have h : (∏ v ∈ p.1.image Prod.snd, X (some (true, v)) * X (some (false, v))) *
      ∏ v ∈ Finset.unmatchedVertices N p.1 \ p.2, (X (some (true, v)) + X (some (false, v))) =
      rename some ((∏ v ∈ p.1.image Prod.snd, X (true, v) * X (false, v)) *
        ∏ v ∈ Finset.unmatchedVertices N p.1 \ p.2, (X (true, v) + X (false, v)) :
          MvPolynomial (Bool × ℕ) R) := by
    simp [map_prod]
  rw [mul_assoc, mul_assoc, h, factorialNormalization_X_none_pow_mul_rename_some]

end MvPolynomial

open Classical in
/-- The open pairs `(M, ∅)` on `[N]` are the pairs `(M, ∅)` with `M` an admissible matching. -/
private lemma filter_openPairs_snd_eq_empty (N : ℕ) (par : ℕ → Option ℕ) (L : Finset ℕ) :
    ((((Finset.Icc 1 N ×ˢ Finset.Icc 1 N).powerset ×ˢ (Finset.Icc 1 N).powerset).filter
        fun p : Finset (ℕ × ℕ) × Finset ℕ => IsOpenPair N par L p.1 p.2).filter
        fun p => p.2 = ∅) =
      ((Finset.Icc 1 N ×ˢ Finset.Icc 1 N).powerset.filter
        (IsAdmissibleMatching N par L)).map (.sectL _ ∅) := by
  ext ⟨M, O⟩
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_powerset, Finset.mem_map,
    Function.Embedding.sectL_apply, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨⟨hM, -⟩, h⟩, rfl⟩
    exact ⟨M, ⟨hM, isOpenPair_empty_iff_isAdmissibleMatching.mp h⟩, rfl, rfl⟩
  · rintro ⟨M, ⟨hM, h⟩, rfl, rfl⟩
    exact ⟨⟨⟨hM, Finset.empty_subset _⟩, isOpenPair_empty_iff_isAdmissibleMatching.mpr h⟩, rfl⟩

/-- Substituting `t = 0` in the open-matching polynomial `P_{par,L}(x, y, t)` gives the forest
matching polynomial `Z_{par,L}(x, y)`: the terms of the open pairs `(M, O)` with `O ≠ ∅` vanish,
and the open pairs `(M, ∅)` are the admissible matchings `M`. -/
@[lognarayana "lem_forest_open_poly_at_zero"]
public theorem aeval_none_zero_forestOpenPoly (R : Type*) [CommSemiring R] (N : ℕ)
    (par : ℕ → Option ℕ) (L : Finset ℕ) :
    MvPolynomial.aeval (fun o : Option (Bool × ℕ) => o.elim 0 MvPolynomial.X)
        (forestOpenPoly R N par L) = forestMatchingPoly R N par L := by
  classical
  rw [forestOpenPoly, map_sum, ← Finset.sum_filter_of_ne (p := fun p => p.2 = ∅),
    filter_openPairs_snd_eq_empty, Finset.sum_map, forestMatchingPoly]
  · simp [map_prod]
  · rintro ⟨M, O⟩ - h
    contrapose! h
    simp [zero_pow (Finset.card_ne_zero.mpr h)]

namespace MvPolynomial

/-- Substituting `t = 0` in the factorial normalization `𝓝_t P_{par,L}(x, y, t)` of the
open-matching polynomial gives the forest matching polynomial `Z_{par,L}(x, y)`: by
`factorialNormalization_forestOpenPoly`, only the terms of the open pairs `(M, ∅)` survive, and
these are the admissible matchings `M`. -/
@[lognarayana "lem_forest_open_poly_normalized_at_zero"]
public theorem aeval_factorialNormalization_forestOpenPoly (R : Type*) [CommSemiring R]
    [Algebra ℚ R] (N : ℕ) (par : ℕ → Option ℕ) (L : Finset ℕ) :
    aeval (Option.elim' 0 X : Option (Bool × ℕ) → MvPolynomial (Bool × ℕ) R)
        (factorialNormalization none (forestOpenPoly R N par L)) =
      forestMatchingPoly R N par L := by
  classical
  rw [factorialNormalization_forestOpenPoly, map_sum,
    ← Finset.sum_filter_of_ne (p := fun p => p.2 = ∅), filter_openPairs_snd_eq_empty,
    Finset.sum_map, forestMatchingPoly]
  · simp [map_prod]
  · rintro ⟨M, O⟩ - h
    contrapose! h
    simp only [map_mul, map_pow, aeval_X, Option.elim'_none,
      zero_pow (Finset.card_ne_zero.mpr h), mul_zero, zero_mul]

end MvPolynomial

/-! ### The open-matching polynomial of a postorder forest -/

/-- The monomial `z^{I(M,O,S)}` splits along the three disjoint pieces of the choice set. -/
private lemma prod_openChoiceSet (R : Type*) [CommSemiring R] (N : ℕ) (M : Finset (ℕ × ℕ))
    (O S : Finset ℕ) (hS : S ⊆ Finset.unmatchedVertices N M \ O) :
    ∏ e ∈ Finset.openChoiceSet N M O S, (X (some e) : MvPolynomial (Option (Bool × ℕ)) R) =
      (∏ v ∈ M.image Prod.snd, X (some (true, v)) * X (some (false, v))) *
        (∏ v ∈ S, X (some (true, v))) *
        ∏ v ∈ (Finset.unmatchedVertices N M \ O) \ S, X (some (false, v)) := by
  classical
  have hRU : Disjoint (M.image Prod.snd) (Finset.unmatchedVertices N M) := by
    rw [Finset.unmatchedVertices]
    exact Finset.disjoint_sdiff.mono_left (Finset.subset_union_right)
  have hRS : Disjoint (M.image Prod.snd) S :=
    hRU.mono_right (hS.trans Finset.sdiff_subset)
  have hRT : Disjoint (M.image Prod.snd) (Finset.unmatchedVertices N M \ (O ∪ S)) :=
    hRU.mono_right Finset.sdiff_subset
  rw [Finset.openChoiceSet, Finset.prod_union, Finset.prod_union, Finset.prod_product,
    Finset.prod_product, Finset.prod_product, Finset.prod_singleton, Finset.prod_singleton]
  · have h : (Finset.unmatchedVertices N M \ O) \ S =
        Finset.unmatchedVertices N M \ (O ∪ S) := by
      ext; simp [and_assoc]
    simp [h, Finset.prod_mul_distrib]
  · rw [Finset.disjoint_left]
    rintro ⟨b, v⟩ h1 h2
    simp only [Finset.mem_product, Finset.mem_singleton] at h1 h2
    exact Finset.disjoint_left.mp hRS h1.2 h2.2
  · rw [Finset.disjoint_left]
    rintro ⟨b, v⟩ h1 h2
    simp only [Finset.mem_union, Finset.mem_product, Finset.mem_singleton,
      Finset.mem_univ, true_and, Finset.mem_sdiff] at h1 h2
    rcases h1 with h1 | ⟨rfl, -⟩
    · exact Finset.disjoint_left.mp hRT h1 (by simp_all)
    · simp at h2

/-- Membership in the flattened index set of `forestOpenPoly` after expanding each term: the
ambient box condition is implied by being an open pair. -/
private lemma mem_sigma_openPairs_iff {N : ℕ} {par : ℕ → Option ℕ} {L : Finset ℕ}
    [DecidablePred fun p : Finset (ℕ × ℕ) × Finset ℕ => IsOpenPair N par L p.1 p.2]
    (x : (_ : Finset (ℕ × ℕ) × Finset ℕ) × Finset ℕ) :
    x ∈ (((Finset.Icc 1 N ×ˢ Finset.Icc 1 N).powerset ×ˢ (Finset.Icc 1 N).powerset).filter
        fun p : Finset (ℕ × ℕ) × Finset ℕ => IsOpenPair N par L p.1 p.2).sigma
          (fun p => (Finset.unmatchedVertices N p.1 \ p.2).powerset) ↔
      IsOpenPair N par L x.1.1 x.1.2 ∧ x.2 ⊆ Finset.unmatchedVertices N x.1.1 \ x.1.2 := by
  simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_product, Finset.mem_powerset]
  refine ⟨fun h => ⟨h.1.2, h.2⟩, fun ⟨hMO, hS⟩ => ⟨⟨⟨fun p hp => ?_, ?_⟩, hMO⟩, hS⟩⟩
  · have h := hMO.isNoncrossingPartialMatching
    have := h.one_le_fst p hp; have := h.fst_lt_snd p hp; have := h.snd_le p hp
    simp only [Finset.mem_product, Finset.mem_Icc]
    omega
  · exact hMO.subset_unmatchedVertices.trans Finset.sdiff_subset

/-- The term of an open pair `(M, O)` in `forestOpenPoly` expands, over the choices
`S ⊆ U(M) \ O`, into the monomials `z^{I(M,O,S)} t^{N - |I(M,O,S)|}`. -/
private lemma openPair_term_eq_sum (R : Type*) [CommSemiring R] {N : ℕ} {par : ℕ → Option ℕ}
    {L : Finset ℕ} {M : Finset (ℕ × ℕ)} {O : Finset ℕ} (hMO : IsOpenPair N par L M O) :
    (X none ^ O.card * (∏ v ∈ M.image Prod.snd, X (some (true, v)) * X (some (false, v))) *
        ∏ v ∈ Finset.unmatchedVertices N M \ O, (X (some (true, v)) + X (some (false, v))) :
          MvPolynomial (Option (Bool × ℕ)) R) =
      ∑ S ∈ (Finset.unmatchedVertices N M \ O).powerset,
        (∏ e ∈ Finset.openChoiceSet N M O S, X (some e)) *
          X none ^ (N - (Finset.openChoiceSet N M O S).card) := by
  rw [Finset.prod_add, Finset.mul_sum]
  refine Finset.sum_congr rfl fun S hS => ?_
  rw [Finset.mem_powerset] at hS
  have := Finset.card_openChoiceSet_add_card hMO.isNoncrossingPartialMatching
    hMO.subset_unmatchedVertices hS
  rw [prod_openChoiceSet R N M O S hS,
    show N - (Finset.openChoiceSet N M O S).card = O.card by omega]
  ring

open Classical in
/-- Expanding every term, `forestOpenPoly` is a sum over the triples `(M, O, S)` of the
monomials `z^{I(M,O,S)} t^{N - |I(M,O,S)|}`. -/
private lemma forestOpenPoly_eq_sum_sigma (R : Type*) [CommSemiring R] (N : ℕ)
    (par : ℕ → Option ℕ) (L : Finset ℕ) :
    forestOpenPoly R N par L =
      ∑ x ∈ (((Finset.Icc 1 N ×ˢ Finset.Icc 1 N).powerset ×ˢ (Finset.Icc 1 N).powerset).filter
        fun p : Finset (ℕ × ℕ) × Finset ℕ => IsOpenPair N par L p.1 p.2).sigma
          (fun p => (Finset.unmatchedVertices N p.1 \ p.2).powerset),
        (∏ e ∈ Finset.openChoiceSet N x.1.1 x.1.2 x.2, X (some e)) *
          X none ^ (N - (Finset.openChoiceSet N x.1.1 x.1.2 x.2).card) := by
  rw [forestOpenPoly, Finset.sum_sigma]
  exact Finset.sum_congr rfl fun p hp => openPair_term_eq_sum R (Finset.mem_filter.mp hp).2

/-- For a postorder forest `par` on `[N]` and `L ⊆ [N]`, the open-matching polynomial is the
generating polynomial of the forest independence family:
`P_{par,L}(x, y, t) = ∑_{I ∈ 𝕀_{par,L}} z^I t^{N - |I|}`, with `z_{v⁺} = x_v`, `z_{v⁻} = y_v`.
Expanding `∏_{v ∈ U(M) \ O} (x_v + y_v)` writes the term of an open pair `(M, O)` as a sum over
`S ⊆ U(M) \ O` of `z^{I(M,O,S)} t^{N - |I(M,O,S)|}`, and `(M, O, S) ↦ I(M, O, S)` is a bijection
onto `𝕀_{par,L}` (`Finset.bijOn_openChoiceSet_forestIndepFamily`). -/
@[lognarayana "lem_forest_open_poly_indep"]
public theorem forestOpenPoly_eq_sum_forestIndepFamily (R : Type*) [CommSemiring R] {N : ℕ}
    {par : ℕ → Option ℕ} (hpar : IsPostorderForest N par) {L : Finset ℕ}
    (hL : L ⊆ Finset.Icc 1 N) :
    forestOpenPoly R N par L =
      ∑ I ∈ forestIndepFamily N par L,
        (∏ e ∈ I, MvPolynomial.X (some e)) * MvPolynomial.X none ^ (N - I.card) := by
  classical
  have hbij := Finset.bijOn_openChoiceSet_forestIndepFamily hpar hL
  rw [forestOpenPoly_eq_sum_sigma]
  refine Finset.sum_nbij (fun x => Finset.openChoiceSet N x.1.1 x.1.2 x.2) ?_ ?_ ?_
    fun _ _ => rfl
  · rintro ⟨⟨M, O⟩, S⟩ hx
    exact Finset.mem_coe.mp (hbij.mapsTo (x := (M, O, S)) ((mem_sigma_openPairs_iff _).mp hx))
  · rintro ⟨⟨M, O⟩, S⟩ hx ⟨⟨M', O'⟩, S'⟩ hy h
    have := hbij.injOn (x₁ := (M, O, S)) (x₂ := (M', O', S'))
      ((mem_sigma_openPairs_iff _).mp hx) ((mem_sigma_openPairs_iff _).mp hy) h
    simp only [Prod.mk.injEq] at this
    obtain ⟨rfl, rfl, rfl⟩ := this
    rfl
  · intro I hI
    obtain ⟨⟨M, O, S⟩, hMOS, rfl⟩ := hbij.surjOn hI
    exact ⟨⟨(M, O), S⟩, (mem_sigma_openPairs_iff _).mpr hMOS, rfl⟩

/-- The factorial normalization in `t = none` of `z^I t^k` is `z^I t^k / k!`. -/
private lemma factorialNormalization_prod_X_some_mul_X_none_pow {β R : Type*} [CommSemiring R]
    [Algebra ℚ R] (I : Finset β) (k : ℕ) :
    factorialNormalization none ((∏ e ∈ I, X (some e)) * X none ^ k :
        MvPolynomial (Option β) R) =
      (∏ e ∈ I, X (some e)) * C (algebraMap ℚ R (1 / (k.factorial : ℚ))) * X none ^ k := by
  have h : (∏ e ∈ I, X (some e) : MvPolynomial (Option β) R) = rename some (∏ e ∈ I, X e) := by
    simp [map_prod]
  rw [mul_comm, h, factorialNormalization_X_none_pow_mul_rename_some]
  ring

/-- If the independent sets of `M` are the members of a family `F` of finsets, then the
independent finsets of `M.comap f` are those whose image under `f` lies in `F`. -/
private lemma comap_indep_coe_iff {α β : Type*} {M : Matroid β}
    {F : Finset (Finset β)} (hM : ∀ I, M.Indep I ↔ ∃ J ∈ F, (J : Set β) = I) (f : α ↪ β)
    (I : Finset α) : (M.comap f).Indep I ↔ I.map f ∈ F := by
  classical
  simp [Matroid.comap_indep_iff, hM, f.injective.injOn, ← Finset.coe_map]

/-- Under the hypotheses of `comap_indep_coe_iff`, if moreover every member of `F` lies in the
range of `f`, then mapping the independent finsets of `M.comap f` along `f` gives `F`. -/
private lemma map_filter_comap_indep {α β : Type*} [Fintype α] {M : Matroid β}
    {F : Finset (Finset β)} (hM : ∀ I, M.Indep I ↔ ∃ J ∈ F, (J : Set β) = I) (f : α ↪ β)
    [DecidablePred fun I : Finset α => (M.comap f).Indep I]
    (hF : ∀ J ∈ F, ∀ e ∈ J, e ∈ Set.range f) :
    (Finset.univ.filter fun I : Finset α => (M.comap f).Indep I).map
      (Finset.mapEmbedding f).toEmbedding = F := by
  classical
  ext J
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
    comap_indep_coe_iff hM, RelEmbedding.coe_toEmbedding, Finset.mapEmbedding_apply]
  refine ⟨fun ⟨I, hI, hIJ⟩ => hIJ ▸ hI, fun hJ => ?_⟩
  have hJ' : J ⊆ Finset.univ.map f := fun e he => by
    obtain ⟨a, rfl⟩ := hF J hJ e he
    exact Finset.mem_map_of_mem f (Finset.mem_univ a)
  obtain ⟨I, -, rfl⟩ := Finset.subset_map_iff.1 hJ'
  exact ⟨I, hJ, rfl⟩

/-- Every member of the forest independence family lies in `Bool × [N]`. -/
private lemma mem_Icc_of_mem_forestIndepFamily {N : ℕ} {par : ℕ → Option ℕ} {L : Finset ℕ}
    {J : Finset (Bool × ℕ)} (hJ : J ∈ forestIndepFamily N par L) {e : Bool × ℕ} (he : e ∈ J) :
    e.2 ∈ Finset.Icc 1 N := by
  simp only [forestIndepFamily, Finset.mem_filter, Finset.mem_powerset] at hJ
  have := hJ.1 he
  simp only [forestGroundSet, Finset.mem_product, Finset.mem_sdiff] at this
  exact this.2.1

/-- For a postorder forest `par` on `[N]` and `L ⊆ [N]`, the factorial normalization
`𝓝_t P_{par,L}(x, y, t)` of the open-matching polynomial is Lorentzian: it is the image, under the
inclusion of variables `Bool × [N] ↪ Bool × ℕ`, of a Lorentzian polynomial in
`ℝ[x_v, y_v, t : v ∈ [N]]`. By `forestOpenPoly_eq_sum_forestIndepFamily`, `𝓝_t P_{par,L}` is the
normalized independent-set polynomial of the forest matroid pulled back to `Bool × [N]`, which
is Lorentzian by `Matroid.isLorentzian_sum_indep_mul_X_pow_div_factorial`. -/
@[lognarayana "thm_forest_open_poly_lorentzian"]
public theorem isLorentzian_factorialNormalization_forestOpenPoly
    (hBH : ∀ (σ : Type) [Fintype σ], NormalizedSupportPolyLorentzianOfMConvex σ)
    (hsub : ∀ (σ τ : Type) [Fintype σ] [Fintype τ], LorentzianNonnegLinearSubstitution σ τ)
    (hclosed : ∀ (σ : Type) [Fintype σ], IsLorentzianClosed σ)
    {N : ℕ} {par : ℕ → Option ℕ} {L : Finset ℕ}
    (hpar : IsPostorderForest N par) (hL : L ⊆ Finset.Icc 1 N) :
    ∃ g : MvPolynomial (Option (Bool × Finset.Icc 1 N)) ℝ,
      rename (Option.map (Prod.map id Subtype.val)) g =
          factorialNormalization none (forestOpenPoly ℝ N par L) ∧
        g.IsLorentzian := by
  classical
  let f : Bool × Finset.Icc 1 N ↪ Bool × ℕ :=
    ⟨Prod.map id Subtype.val, Function.injective_id.prodMap Subtype.val_injective⟩
  obtain ⟨M, -, hM⟩ := exists_matroid_indep_iff_mem_forestIndepFamily N par L
  have hN : ∀ B, (M.comap f).IsBase B → B.encard ≤ N := by
    intro B hB
    obtain ⟨I, rfl⟩ := (Set.toFinite B).exists_finset_coe
    rw [Set.encard_coe_eq_coe_finsetCard]
    exact_mod_cast (Finset.card_map f).symm.trans_le
      (card_le_of_mem_forestIndepFamily N par L ((comap_indep_coe_iff hM f I).1 hB.indep))
  refine ⟨_, ?_, Matroid.isLorentzian_sum_indep_mul_X_pow_div_factorial hBH hsub
    (hclosed _) (M.comap f) N hN⟩
  rw [forestOpenPoly_eq_sum_forestIndepFamily ℝ hpar hL, map_sum, map_sum,
    ← map_filter_comap_indep hM f fun J hJ e he =>
      ⟨(e.1, ⟨e.2, mem_Icc_of_mem_forestIndepFamily hJ he⟩), rfl⟩, Finset.sum_map]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [factorialNormalization_prod_X_some_mul_X_none_pow]
  simp [map_prod, Finset.prod_map, f]
