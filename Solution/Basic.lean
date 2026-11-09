/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import LogNarayana

/-! # Satisfying the formal challenge -/

section

open Finset

namespace Polynomial

/-- **Lemma 6.1.** The signed Appell polynomial `η_m` is `t^m` plus terms of degree less than `m`:
`deg (η_m - t^m) < m`. -/
public theorem _root_.LogNarayana.Challenge.Polynomial.degree_signedAppell_sub_X_pow_lt
    (R : Type*) [Ring R] (m : ℕ) :
    (signedAppell R m - X ^ m).degree < (m : WithBot ℕ) :=
  @_root_.Polynomial.degree_signedAppell_sub_X_pow_lt R _ m

/-- **Lemma 6.1.** The signed Appell polynomials form an Appell sequence: `η_m' = m η_{m-1}`. -/
public theorem _root_.LogNarayana.Challenge.Polynomial.derivative_signedAppell
    (R : Type*) [Ring R] (m : ℕ) :
    derivative (signedAppell R m) = (m : R[X]) * signedAppell R (m - 1) :=
  @_root_.Polynomial.derivative_signedAppell R _ m

/-- **Lemma 6.1.** The signed Appell polynomials satisfy the binomial identity `η_d(z + w) =
∑_{m=0}^{d} (d choose m) η_m(z) w^(d-m)`. -/
public theorem _root_.LogNarayana.Challenge.Polynomial.aeval_add_signedAppell
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (d : ℕ) (z w : S) :
    aeval (z + w) (signedAppell R d) =
      ∑ m ∈ range (d + 1), (d.choose m : S) * aeval z (signedAppell R m) * w ^ (d - m) :=
  @_root_.Polynomial.aeval_add_signedAppell R S _ _ _ d z w

/-- **Lemma 6.1.** For every `m ≥ 0`, the set `{t ∈ ℝ : η_m(t) = 0}` of real zeros of the signed
Appell polynomial has exactly `m` elements. -/
public theorem _root_.LogNarayana.Challenge.Polynomial.encard_setOf_eval_signedAppell_eq_zero
    (hN : ShiftedNarayanaNegRealRoots)
    (m : ℕ) :
    {t : ℝ | (signedAppell ℝ m).eval t = 0}.encard = m :=
  @_root_.Polynomial.encard_setOf_eval_signedAppell_eq_zero hN m

end Polynomial

end

section

open MeasureTheory Set

namespace MvPolynomial

section Homogeneous

variable {σ R : Type*} [CommSemiring R] [Algebra ℚ R] {m : ℕ}

namespace IsHomogeneous

/-- **Theorem 4.1.** For `m ≥ 1`, the simplex integration operator `𝔍_m` sends a polynomial
homogeneous of degree `d` to one homogeneous of degree `d + m - 1`: it sends `x^α u^γ` to a multiple
of `x^α t^(|γ| + m - 1)`. -/
public theorem _root_.LogNarayana.Challenge.MvPolynomial.IsHomogeneous.simplexIntegral
    (hm : 1 ≤ m) {d : ℕ}
    {G : MvPolynomial (σ ⊕ Fin m) R} (hG : G.IsHomogeneous d) :
    (MvPolynomial.simplexIntegral σ R m G).IsHomogeneous (d + m - 1) :=
  @_root_.MvPolynomial.IsHomogeneous.simplexIntegral σ R _ _ m hm d G hG

end IsHomogeneous

end Homogeneous

section Lorentzian

namespace IsLorentzian

/-- **Theorem 4.1.** **Simplex integration preserves the Lorentzian property** (after [BH, Theorems
3.2 and 3.10]): for `m ≥ 2` and a Lorentzian polynomial `G(x, u_1, …, u_m)`, the polynomial `𝔍_m G
(x, t)` is Lorentzian, given the cited results of Brändén–Huh on linear substitutions, products,
M-convex supports, and the symbol theorem for operators `ℝ[x, u] → ℝ[x, t]`. -/
public theorem _root_.LogNarayana.Challenge.MvPolynomial.IsLorentzian.simplexIntegral
    {σ : Type*} [Fintype σ] {m : ℕ} (hm : 2 ≤ m)
    (hsub : LorentzianNonnegLinearSubstitution (Option (Fin m)) (Option σ ⊕ (σ ⊕ Fin m)))
    (hmul : LorentzianMul (Option σ ⊕ (σ ⊕ Fin m)))
    (hBH : NormalizedSupportPolyLorentzianOfMConvex (Option (Fin m)))
    (hsym : BrandenHuhSymbolTheorem (σ ⊕ Fin m) (Option σ))
    {G : MvPolynomial (σ ⊕ Fin m) ℝ} (hG : G.IsLorentzian) :
    (MvPolynomial.simplexIntegral σ ℝ m G).IsLorentzian :=
  @_root_.MvPolynomial.IsLorentzian.simplexIntegral σ _ m hm hsub hmul hBH hsym G hG

end IsLorentzian

end Lorentzian

end MvPolynomial

end

section

universe u

open Finsupp (single)

namespace MvPolynomial

section AntiderivativeLorentzian

variable {σ : Type*}

namespace IsLorentzian

/-- **Corollary 4.2.** **Antiderivatives preserve the Lorentzian property**: if `F ∈ ℝ[z_i : i ∈ σ]`
is Lorentzian, then its antiderivative `∫₀ᵗ F ds` with respect to the variable `t` is Lorentzian. -/
public theorem _root_.LogNarayana.Challenge.MvPolynomial.IsLorentzian.antiderivative
    {σ : Type*} [Fintype σ] {F : MvPolynomial σ ℝ}
    (hF : F.IsLorentzian) (t : σ) : (MvPolynomial.antiderivative t F).IsLorentzian :=
  @_root_.MvPolynomial.IsLorentzian.antiderivative σ _ F hF t

end IsLorentzian

end AntiderivativeLorentzian

section ConvolutionLorentzian

namespace IsLorentzian

/-- **Corollary 4.2.** **Convolution preserves the Lorentzian property**: if `F G ∈ ℝ[x, t]` are
(homogeneous) Lorentzian polynomials, then their convolution `F * G` in the variable `t` is
Lorentzian. -/
public theorem _root_.LogNarayana.Challenge.MvPolynomial.IsLorentzian.tConvolution
    (hsub : ∀ (σ τ : Type u) [Fintype σ] [Fintype τ], LorentzianNonnegLinearSubstitution σ τ)
    (hmul : ∀ (σ : Type u) [Fintype σ], LorentzianMul σ)
    (hsym : ∀ (σ τ : Type u) [Fintype σ] [Fintype τ], BrandenHuhSymbolTheorem σ τ)
    (hBH : ∀ (σ : Type u) [Fintype σ], NormalizedSupportPolyLorentzianOfMConvex σ)
    {σ : Type u} [Fintype σ] {F G : MvPolynomial (Option σ) ℝ}
    (hF : F.IsLorentzian) (hG : G.IsLorentzian) :
    (MvPolynomial.tConvolution F G).IsLorentzian :=
  @_root_.MvPolynomial.IsLorentzian.tConvolution hsub hmul hsym hBH σ _ F G hF hG

end IsLorentzian

end ConvolutionLorentzian

end MvPolynomial

end

section

section

open BinaryTree

variable {α : Type*}

namespace BinaryTree

/-- **Proposition 3.1.** **Matchings with choices and trees with fixed postorder.** Let `n ≥ 1` and
`π ∈ S_n`. The map `T ↦ (M(T), C(T))` is a bijection from `{T ∈ DBT([n]) : 𝒫(T) = π}` onto the set
of pairs `(M, C)` with `M ∈ 𝒜(π)` and `C ⊆ U(M)`, the unmatched vertices of `M` in `[n - 1]`. -/
public theorem _root_.LogNarayana.Challenge.BinaryTree.bijOn_treeMatching_treeRightChoices
    {n : ℕ} (hn : 1 ≤ n) {π : List ℕ}
    (hπS : π ∈ permWords n) :
    Set.BijOn (fun T : BinaryTree ℕ => (T.treeMatching, T.treeRightChoices))
      {T | T ∈ decreasingTrees (Finset.Icc 1 n) ∧ T.postorder = π}
      {p : Finset (ℕ × ℕ) × Finset ℕ |
        p.1 ∈ π.fiberMatchings ∧ p.2 ⊆ Finset.unmatchedVertices (n - 1) p.1} :=
  @_root_.BinaryTree.bijOn_treeMatching_treeRightChoices n hn π hπS

end BinaryTree

end

section

open Polynomial

namespace List

/-- **Proposition 3.1.** For `n ≥ 1` and `π ∈ S_n`, `D_π(x) = ∑_{M ∈ 𝒜(π)} x^{|M|} (1 + x)^{n - 1 -
2|M|}`. -/
public theorem _root_.LogNarayana.Challenge.List.fiberDescentPolynomial_eq_finsum_fiberMatchings
    (R : Type*) [CommSemiring R]
    {n : ℕ} (hn : 1 ≤ n) {π : List ℕ} (hπ : π ∈ permWords n) :
    fiberDescentPolynomial R π =
      ∑ᶠ M ∈ π.fiberMatchings, (X : R[X]) ^ M.card * (1 + X) ^ (n - 1 - 2 * M.card) :=
  @_root_.List.fiberDescentPolynomial_eq_finsum_fiberMatchings R _ n hn π hπ

end List

end

section

open Polynomial

namespace List

/-- **Proposition 3.1.** For `n ≥ 1`, `π ∈ S_n` and `x ≠ -1`, `D_π(x) = (1 + x)^{n - 1} Γ_π(x / (1 +
x)^2)`. -/
public theorem
    _root_.LogNarayana.Challenge.List.eval_fiberDescentPolynomial_eq_pow_mul_eval_fiberMatchingPolynomial
    {K : Type*} [Field K] {n : ℕ} (hn : 1 ≤ n) {π : List ℕ} (hπ : π ∈ permWords n)
    {x : K} (hx : 1 + x ≠ 0) :
    (fiberDescentPolynomial K π).eval x =
      (1 + x) ^ (n - 1) * (fiberMatchingPolynomial K π).eval (x / (1 + x) ^ 2) :=
  @_root_.List.eval_fiberDescentPolynomial_eq_pow_mul_eval_fiberMatchingPolynomial K _ n hn π hπ x
    hx

end List

end

end

section

namespace MvPolynomial

open Matrix

variable {p : ℕ}

/-- **Lemma 4.3.** Let `a ∈ ℝ_{≥0}^p`, `A = ∑ⱼ aⱼ xⱼ`, and `B` homogeneous of degree `2` with
nonnegative coefficients. The kernel `K_{A,B} = B + A t + t² / 2` is Lorentzian if and only if
`Hess B - a aᵀ` is negative semidefinite. -/
public theorem _root_.LogNarayana.Challenge.MvPolynomial.isLorentzian_quadraticKernel_iff
    {p : ℕ} {a : Fin p → ℝ} (ha : ∀ j, 0 ≤ a j)
    {B : MvPolynomial (Fin p) ℝ} (hB : B.IsHomogeneous 2) (hBnn : B.HasNonnegCoeffs) :
    (quadraticKernel (∑ j, C (a j) * X j) B).IsLorentzian ↔
      (-(hessianAtZero B - Matrix.vecMulVec a a)).PosSemidef :=
  @_root_.MvPolynomial.isLorentzian_quadraticKernel_iff p a ha B hB hBnn

end MvPolynomial

namespace MvPolynomial

universe u

section RootOperator

/-- **Lemma 4.3.** Let `σ` be finite, `a ∈ ℝ_{≥0}^σ`, `A = ∑ⱼ aⱼ xⱼ`, and `B` homogeneous of degree
`2` with nonnegative coefficients such that `Hess B - a aᵀ ⪯ 0`. Then for every Lorentzian
`U ∈ ℝ[x, t]`, the polynomial `𝓡_{A,B}(U)` is Lorentzian. -/
public theorem _root_.LogNarayana.Challenge.MvPolynomial.isLorentzian_rootOperator
    {σ : Type u} [Fintype σ]
    (hsub : ∀ (τ τ' : Type u) [Fintype τ] [Fintype τ'], LorentzianNonnegLinearSubstitution τ τ')
    (hmul : ∀ (τ : Type u) [Fintype τ], LorentzianMul τ)
    (hBH : ∀ (τ : Type u) [Fintype τ], NormalizedSupportPolyLorentzianOfMConvex τ)
    (hsym : ∀ (τ τ' : Type u) [Fintype τ] [Fintype τ'], BrandenHuhSymbolTheorem τ τ')
    (hder : ∀ (τ : Type u) [Fintype τ], LorentzianNonnegDerivative τ)
    {a : σ → ℝ} (ha : ∀ j, 0 ≤ a j)
    {B : MvPolynomial σ ℝ} (hB : B.IsHomogeneous 2) (hBnn : B.HasNonnegCoeffs)
    (hHess : (-(hessianAtZero B - Matrix.vecMulVec a a)).PosSemidef)
    {U : MvPolynomial (Option σ) ℝ} (hU : U.IsLorentzian) :
    (rootOperator none (rename some (∑ j, C (a j) * X j)) (rename some B) U).IsLorentzian :=
  @_root_.MvPolynomial.isLorentzian_rootOperator σ _ hsub hmul hBH hsym hder a ha B hB hBnn hHess U
    hU

end RootOperator

end MvPolynomial

end

section

namespace List

section Preorder

variable {α : Type*} [Preorder α]

/-- **Lemma 3.2.** The adoptable forest of `π` is a postorder forest on `[π.length - 1]`: the
subtree rooted at `v` is `I_v = [ℓ_v, v]`, of cardinality `v + 1 - ℓ_v`. -/
public theorem _root_.LogNarayana.Challenge.List.isPostorderForest_adoptableForest
    (π : List α) :
    IsPostorderForest (π.length - 1) π.adoptableForest :=
  @_root_.List.isPostorderForest_adoptableForest α _ π

/-- **Lemma 3.2.** `(a, b)` is adoptable with respect to `π` if and only if `b` is a strict ancestor
of `a` in the adoptable forest of `π`. Both directions pass through `V_b = I_b` and the description
`[ℓ_b, b - 1]` of the adoptable left endpoints. -/
public theorem _root_.LogNarayana.Challenge.List.isAdoptablePair_iff_isStrictAncestor
    (π : List α) (a b : ℕ) :
    π.IsAdoptablePair a b ↔ IsStrictAncestor π.adoptableForest b a :=
  @_root_.List.isAdoptablePair_iff_isStrictAncestor α _ π a b

/-- **Lemma 3.2.** Every descent `b ∈ Des(π)` is a leaf of the adoptable forest of `π`. No pair `(a,
b)` is adoptable, since adoptability forces `π_b < π_{b+1}`; hence `ℓ_b = b`, and no vertex `u < b`
lies in `I_b`. -/
public theorem _root_.LogNarayana.Challenge.List.isLeaf_adoptableForest_of_mem_descentSet
    [DecidableRel (α := α) (· < ·)]
    (π : List α) {b : ℕ} (hb : b ∈ π.descentSet) : IsLeaf π.adoptableForest b :=
  @_root_.List.isLeaf_adoptableForest_of_mem_descentSet α _ _ π b hb

end Preorder

end List

end

section

open Finset

namespace Matroid

/-- **Theorem 3.4.** Let `par` be a postorder forest on `[N]` and `L ⊆ [N]` with `Z_{par,L} ≠ 0`.
Every matroid `M` on `Bool × ℕ` whose independent sets are exactly the members of `𝕀_{par,L}` has
all its bases of cardinality `N`: `Z_{par,L} ≠ 0` provides an independent set of size `N`, and none
is larger. -/
public theorem
    _root_.LogNarayana.Challenge.Matroid.encard_eq_of_isBase_of_indep_iff_mem_forestIndepFamily
    {N : ℕ}
    {par : ℕ → Option ℕ} {L : Finset ℕ} (hpar : IsPostorderForest N par)
    (hL : L ⊆ Finset.Icc 1 N) (hZ : forestMatchingPoly ℝ N par L ≠ 0) (M : Matroid (Bool × ℕ))
    (hI : ∀ I : Set (Bool × ℕ),
      M.Indep I ↔ ∃ J ∈ forestIndepFamily N par L, (J : Set (Bool × ℕ)) = I)
    {B : Set (Bool × ℕ)} (hB : M.IsBase B) : B.encard = N :=
  @_root_.Matroid.encard_eq_of_isBase_of_indep_iff_mem_forestIndepFamily N par L hpar hL hZ M hI B
    hB

end Matroid

open Classical in
/-- **Theorem 3.4.** Let `par` be a postorder forest on `[N]` and `L ⊆ [N]` with `Z_{par,L} ≠ 0`.
For every matroid `M` on `E_{N,L}` whose independent sets are exactly the members of `𝕀_{par,L}`,
`Z_{par,L} = ∑_{B ∈ 𝔹(M)} ∏_{e ∈ B} X e`, i.e. `∑_B ∏_{v⁺ ∈ B} x_v ∏_{v⁻ ∈ B} y_v`. -/
public theorem _root_.LogNarayana.Challenge.forestMatchingPoly_eq_sum_isBase_prod_X
    {N : ℕ} {par : ℕ → Option ℕ}
    {L : Finset ℕ} (hpar : IsPostorderForest N par) (hL : L ⊆ Finset.Icc 1 N)
    (hZ : forestMatchingPoly ℝ N par L ≠ 0) (M : Matroid (Bool × ℕ))
    (hE : M.E = ↑(forestGroundSet N L))
    (hI : ∀ I : Set (Bool × ℕ),
      M.Indep I ↔ ∃ J ∈ forestIndepFamily N par L, (J : Set (Bool × ℕ)) = I) :
    forestMatchingPoly ℝ N par L =
      ∑ B ∈ (forestGroundSet N L).powerset.filter
          (fun B : Finset (Bool × ℕ) => M.IsBase (B : Set (Bool × ℕ))),
        ∏ e ∈ B, MvPolynomial.X e :=
  @_root_.forestMatchingPoly_eq_sum_isBase_prod_X N par L hpar hL hZ M hE hI

/-- **Theorem 3.4.** For a postorder forest `par` on `[N]` and `L ⊆ [N]`, every coefficient of the
forest matching polynomial `Z_{par,L}` is `0` or `1`, since it is a sum of square-free monomials
over distinct sets. -/
public theorem _root_.LogNarayana.Challenge.coeff_forestMatchingPoly_eq_zero_or_eq_one
    {R : Type*} [CommSemiring R] {N : ℕ}
    {par : ℕ → Option ℕ} {L : Finset ℕ} (hpar : IsPostorderForest N par)
    (hL : L ⊆ Finset.Icc 1 N) (d : Bool × ℕ →₀ ℕ) :
    (forestMatchingPoly R N par L).coeff d = 0 ∨ (forestMatchingPoly R N par L).coeff d = 1 :=
  @_root_.coeff_forestMatchingPoly_eq_zero_or_eq_one R _ N par L hpar hL d

open MvPolynomial in
/-- **Theorem 3.4.** For a postorder forest `par` on `[N]` and `L ⊆ [N]`, the forest matching
polynomial `Z_{par,L}(x, y)` is Lorentzian: it is the image, under the inclusion of variables `Bool
× [N] ↪ Bool × ℕ`, of a Lorentzian polynomial in `ℝ[x_v, y_v : v ∈ [N]]`, namely the basis
generating polynomial of the forest matroid pulled back to `Bool × [N]`. -/
public theorem _root_.LogNarayana.Challenge.isLorentzian_forestMatchingPoly
    (hBH : ∀ (σ : Type) [Fintype σ], NormalizedSupportPolyLorentzianOfMConvex σ)
    {N : ℕ} {par : ℕ → Option ℕ} {L : Finset ℕ}
    (hpar : IsPostorderForest N par) (hL : L ⊆ Finset.Icc 1 N) :
    ∃ g : MvPolynomial (Bool × Finset.Icc 1 N) ℝ,
      rename (Prod.map id Subtype.val) g = forestMatchingPoly ℝ N par L ∧ g.IsLorentzian :=
  @_root_.isLorentzian_forestMatchingPoly hBH N par L hpar hL

end

section

open MvPolynomial Matrix

universe u

/-- **Theorem 4.4.** For a marked postorder forest `(par, L)` on `[N]`, a linear form `A = aᵀ x`
with `a ≥ 0`, and a quadratic form `B` with nonnegative coefficients and `Hess B - a aᵀ ⪯ 0`, the
factorial normalization `𝓝_t P^{A,B}_{par,L}(x, t)` of the weighted open-pair polynomial is
Lorentzian. -/
public theorem
    _root_.LogNarayana.Challenge.isLorentzian_factorialNormalization_weightedOpenPairPolynomial
    {σ : Type u} [Fintype σ] {N : ℕ} {par : ℕ → Option ℕ} {L : Finset ℕ}
    (hsub : ∀ (σ τ : Type u) [Fintype σ] [Fintype τ], LorentzianNonnegLinearSubstitution σ τ)
    (hmul : ∀ (σ : Type u) [Fintype σ], LorentzianMul σ)
    (hsym : ∀ (σ τ : Type u) [Fintype σ] [Fintype τ], BrandenHuhSymbolTheorem σ τ)
    (hBH : ∀ (σ : Type u) [Fintype σ], NormalizedSupportPolyLorentzianOfMConvex σ)
    (hder : ∀ (σ : Type u) [Fintype σ], LorentzianNonnegDerivative σ)
    (hpar : IsPostorderForest N par) (hL : L ⊆ Finset.Icc 1 N)
    (hLleaf : ∀ v ∈ L, IsLeaf par v)
    (a : σ → ℝ) (B : MvPolynomial σ ℝ)
    (ha : ∀ i, 0 ≤ a i) (hB : B.IsHomogeneous 2) (hBnn : B.HasNonnegCoeffs)
    (hHess : ∀ w : σ → ℝ, w ⬝ᵥ ((hessianAtZero B - Matrix.vecMulVec a a) *ᵥ w) ≤ 0) :
    (factorialNormalization (none : Option σ)
      (weightedOpenPairPolynomial N par L (∑ i, a i • X i) B)).IsLorentzian :=
  @_root_.isLorentzian_factorialNormalization_weightedOpenPairPolynomial σ _ N par L hsub hmul hsym
    hBH hder hpar hL hLleaf a B ha hB hBnn hHess

open Classical in
/-- **Theorem 4.4.** For a marked postorder forest `(par, L)` on `[N]`, a linear form `A = aᵀ x`
with `a ≥ 0`, and a quadratic form `B` with nonnegative coefficients and `Hess B - a aᵀ ⪯ 0`, the
polynomial `∑_M B^{|M|} A^{N - 2|M|}`, summed over the admissible matchings `M` of `(par, L)`, is
Lorentzian. -/
public theorem _root_.LogNarayana.Challenge.isLorentzian_sum_admissibleMatching_pow_mul_pow
    {σ : Type u} [Fintype σ]
    (hsub : ∀ (σ τ : Type u) [Fintype σ] [Fintype τ], LorentzianNonnegLinearSubstitution σ τ)
    (hmul : ∀ (σ : Type u) [Fintype σ], LorentzianMul σ)
    (hsym : ∀ (σ τ : Type u) [Fintype σ] [Fintype τ], BrandenHuhSymbolTheorem σ τ)
    (hBH : ∀ (σ : Type u) [Fintype σ], NormalizedSupportPolyLorentzianOfMConvex σ)
    (hder : ∀ (σ : Type u) [Fintype σ], LorentzianNonnegDerivative σ)
    {N : ℕ} {par : ℕ → Option ℕ} {L : Finset ℕ}
    (hpar : IsPostorderForest N par) (hL : L ⊆ Finset.Icc 1 N)
    (hLleaf : ∀ v ∈ L, IsLeaf par v)
    (a : σ → ℝ) (B : MvPolynomial σ ℝ)
    (ha : ∀ i, 0 ≤ a i) (hB : B.IsHomogeneous 2) (hBnn : B.HasNonnegCoeffs)
    (hHess : ∀ w : σ → ℝ, w ⬝ᵥ ((hessianAtZero B - Matrix.vecMulVec a a) *ᵥ w) ≤ 0) :
    (∑ M ∈ (Finset.Icc 1 N ×ˢ Finset.Icc 1 N).powerset.filter
        (fun M : Finset (ℕ × ℕ) => IsAdmissibleMatching N par L M),
      B ^ M.card * (∑ i, a i • X i) ^ (N - 2 * M.card)).IsLorentzian :=
  @_root_.isLorentzian_sum_admissibleMatching_pow_mul_pow σ _ hsub hmul hsym hBH hder N par L hpar
    hL hLleaf a B ha hB hBnn hHess

end

section

open MvPolynomial

namespace List

/-- **Theorem 1.3.** **Peak-weighted fiber polynomials are Lorentzian.** For `n ≥ 1`, `π ∈ S_n` and
`λ ∈ [0, 2]`, the peak-weighted homogeneous fiber polynomial `H^λ_π(x, y)` is Lorentzian, given the
cited Brändén–Huh theorems on nonnegative linear substitutions, nonnegative derivatives, products,
normalized support polynomials of M-convex sets, and symbols of linear operators. -/
public theorem _root_.LogNarayana.Challenge.List.isLorentzian_fiberPeakPolynomial
    {n : ℕ} (hn : 1 ≤ n) {π : List ℕ}
    (hπ : π ∈ permWords n) {lam : ℝ} (hlam : lam ∈ Set.Icc (0 : ℝ) 2)
    (hsub : ∀ (σ τ : Type) [Fintype σ] [Fintype τ], LorentzianNonnegLinearSubstitution σ τ)
    (hder : ∀ (σ : Type) [Fintype σ], LorentzianNonnegDerivative σ)
    (hmul : ∀ (σ : Type) [Fintype σ], LorentzianMul σ)
    (hBH : ∀ (σ : Type) [Fintype σ], NormalizedSupportPolyLorentzianOfMConvex σ)
    (hsym : ∀ (σ τ : Type) [Fintype σ] [Fintype τ], BrandenHuhSymbolTheorem σ τ) :
    (fiberPeakPolynomial ℝ lam π).IsLorentzian :=
  @_root_.List.isLorentzian_fiberPeakPolynomial n hn π hπ lam hlam hsub hder hmul hBH hsym

end List

end

section

open Polynomial

namespace MvPolynomial

/-- **Theorem 4.6.** Let `P ⊆ ℝ^r`, `r ≥ 1`, be an integral binary nestohedron whose points all have
coordinate sum `S`, and let `A`, `B` be homogeneous of degrees `1` and `2`. Then `B^{r-1} ∑_{q ∈ P ∩
ℤ^r} ∏_i Q_{q_i - 1}(A, B)` is homogeneous of degree `S + r - 2`. -/
public theorem
    _root_.LogNarayana.Challenge.MvPolynomial.isHomogeneous_pow_mul_finsum_latticePoints_prod_narayanaQ
    {r : ℕ} (hr : 1 ≤ r) {P : Set (Fin r → ℝ)} (hP : IsIntegralBinaryNestohedron ℝ P)
    {S : ℕ} (hS : ∀ v ∈ P, ∑ i, v i = S)
    {σ : Type*} {A B : MvPolynomial σ ℝ} (hA : A.IsHomogeneous 1) (hB : B.IsHomogeneous 2) :
    (B ^ (r - 1) * ∑ᶠ q ∈ P.latticePoints,
      ∏ i, aeval ![A, B] (narayanaQ ℝ (⌊q i⌋₊ - 1))).IsHomogeneous (S + r - 2) :=
  @_root_.MvPolynomial.isHomogeneous_pow_mul_finsum_latticePoints_prod_narayanaQ r hr P hP S hS σ A
    B hA hB

section KernelPolytopeLorentzian

open Matrix

/-- **Theorem 4.6.** Let `P ⊆ ℝ^r`, `r ≥ 1`, be an integral binary nestohedron, `a ∈ ℝ_{≥0}^p`, `A =
aᵀ x`, and `B` homogeneous of degree `2` with nonnegative coefficients and `Hess B - a aᵀ ⪯ 0`. Then
`B^{r-1} ∑_{q ∈ P ∩ ℤ^r} ∏_i Q_{q_i - 1}(A, B)` is Lorentzian. -/
public theorem
    _root_.LogNarayana.Challenge.MvPolynomial.isLorentzian_pow_mul_finsum_latticePoints_prod_narayanaQ
    (hreal : IntegralBinaryNestohedronRealization)
    (hfert : RefinedFertilityFormula)
    (hsub : ∀ (σ τ : Type) [Fintype σ] [Fintype τ], LorentzianNonnegLinearSubstitution σ τ)
    (hder : ∀ (σ : Type) [Fintype σ], LorentzianNonnegDerivative σ)
    (hmul : ∀ (σ : Type) [Fintype σ], LorentzianMul σ)
    (hBH : ∀ (σ : Type) [Fintype σ], NormalizedSupportPolyLorentzianOfMConvex σ)
    (hsym : ∀ (σ τ : Type) [Fintype σ] [Fintype τ], BrandenHuhSymbolTheorem σ τ)
    {r : ℕ} (hr : 1 ≤ r) {P : Set (Fin r → ℝ)} (hP : IsIntegralBinaryNestohedron ℝ P)
    {p : ℕ} {a : Fin p → ℝ} (ha : ∀ j, 0 ≤ a j)
    {B : MvPolynomial (Fin p) ℝ} (hB : B.IsHomogeneous 2) (hBnn : B.HasNonnegCoeffs)
    (hHess : (-(hessianAtZero B - Matrix.vecMulVec a a)).PosSemidef) :
    (B ^ (r - 1) * ∑ᶠ q ∈ P.latticePoints,
      ∏ i, aeval ![∑ j, C (a j) * X j, B] (narayanaQ ℝ (⌊q i⌋₊ - 1))).IsLorentzian :=
  @_root_.MvPolynomial.isLorentzian_pow_mul_finsum_latticePoints_prod_narayanaQ hreal hfert hsub
    hder hmul hBH hsym r hr P hP p a ha B hB hBnn hHess

end KernelPolytopeLorentzian

/-- **Theorem 4.6.** Let `P ⊆ ℝ^r`, `r ≥ 1`, be an integral binary nestohedron, `a ∈ ℝ_{≥0}^p`, `A =
aᵀ x`, and `B` homogeneous of degree `2` with nonnegative coefficients and `Hess B - a aᵀ ⪯ 0`. Then
`∑_{q ∈ P ∩ ℤ^r} ∏_i (B · Q_{q_i - 1}(A, B))` is Lorentzian. -/
public theorem
    _root_.LogNarayana.Challenge.MvPolynomial.isLorentzian_finsum_latticePoints_prod_mul_narayanaQ
    (hreal : IntegralBinaryNestohedronRealization)
    (hfert : RefinedFertilityFormula)
    (hsub : ∀ (σ τ : Type) [Fintype σ] [Fintype τ], LorentzianNonnegLinearSubstitution σ τ)
    (hder : ∀ (σ : Type) [Fintype σ], LorentzianNonnegDerivative σ)
    (hmul : ∀ (σ : Type) [Fintype σ], LorentzianMul σ)
    (hBH : ∀ (σ : Type) [Fintype σ], NormalizedSupportPolyLorentzianOfMConvex σ)
    (hsym : ∀ (σ τ : Type) [Fintype σ] [Fintype τ], BrandenHuhSymbolTheorem σ τ)
    {r : ℕ} (hr : 1 ≤ r) {P : Set (Fin r → ℝ)} (hP : IsIntegralBinaryNestohedron ℝ P)
    {p : ℕ} {a : Fin p → ℝ} (ha : ∀ j, 0 ≤ a j)
    {B : MvPolynomial (Fin p) ℝ} (hB : B.IsHomogeneous 2) (hBnn : B.HasNonnegCoeffs)
    (hHess : (-(hessianAtZero B - Matrix.vecMulVec a a)).PosSemidef) :
    (∑ᶠ q ∈ P.latticePoints,
      ∏ i, (B * aeval ![∑ j, C (a j) * X j, B] (narayanaQ ℝ (⌊q i⌋₊ - 1)))).IsLorentzian :=
  @_root_.MvPolynomial.isLorentzian_finsum_latticePoints_prod_mul_narayanaQ hreal hfert hsub hder
    hmul hBH hsym r hr P hP p a ha B hB hBnn hHess

end MvPolynomial

namespace Polynomial

/-- **Corollary 4.7.** For `0 ≤ λ ≤ 2`, `r ≥ 1` and an integral binary nestohedron `P ⊆ ℝ^r`, the
deformed Narayana sum `∑_{q ∈ P ∩ ℤ^r} ∏_i N^{(λ)}_{q_i}(x)` is log-concave. -/
public theorem
    _root_.LogNarayana.Challenge.Polynomial.isLogConcave_finsum_latticePoints_prod_deformedNarayanaPolynomial
    (hreal : IntegralBinaryNestohedronRealization)
    (hfert : RefinedFertilityFormula)
    (hsub : ∀ (σ τ : Type) [Fintype σ] [Fintype τ],
      MvPolynomial.LorentzianNonnegLinearSubstitution σ τ)
    (hder : ∀ (σ : Type) [Fintype σ], MvPolynomial.LorentzianNonnegDerivative σ)
    (hmul : ∀ (σ : Type) [Fintype σ], MvPolynomial.LorentzianMul σ)
    (hBH : ∀ (σ : Type) [Fintype σ],
      MvPolynomial.NormalizedSupportPolyLorentzianOfMConvex σ)
    (hsym : ∀ (σ τ : Type) [Fintype σ] [Fintype τ],
      MvPolynomial.BrandenHuhSymbolTheorem σ τ)
    {lam : ℝ} (hlam₀ : 0 ≤ lam) (hlam₂ : lam ≤ 2)
    {r : ℕ} (hr : 1 ≤ r) {P : Set (Fin r → ℝ)} (hP : IsIntegralBinaryNestohedron ℝ P) :
    (∑ᶠ q ∈ P.latticePoints, ∏ i, deformedNarayanaPolynomial ℝ lam ⌊q i⌋₊).IsLogConcave :=
  @_root_.Polynomial.isLogConcave_finsum_latticePoints_prod_deformedNarayanaPolynomial hreal hfert
    hsub hder hmul hBH hsym lam hlam₀ hlam₂ r hr P hP

/-- **Corollary 4.7.** For `0 ≤ λ ≤ 2` and an integral binary nestohedron `P ⊆ ℝ^r` with `r ≥ 1`,
the coefficient sequence of `∑_{q ∈ P ∩ ℤ^r} ∏_i N^{(λ)}_{q_i}(x)` has no internal zeros. -/
public theorem
    _root_.LogNarayana.Challenge.Polynomial.hasNoInternalZeros_coeff_finsum_latticePoints_prod_deformedNarayanaPolynomial
    (hreal : IntegralBinaryNestohedronRealization)
    (hfert : RefinedFertilityFormula)
    (hsub : ∀ (σ τ : Type) [Fintype σ] [Fintype τ],
      MvPolynomial.LorentzianNonnegLinearSubstitution σ τ)
    (hder : ∀ (σ : Type) [Fintype σ], MvPolynomial.LorentzianNonnegDerivative σ)
    (hmul : ∀ (σ : Type) [Fintype σ], MvPolynomial.LorentzianMul σ)
    (hBH : ∀ (σ : Type) [Fintype σ],
      MvPolynomial.NormalizedSupportPolyLorentzianOfMConvex σ)
    (hsym : ∀ (σ τ : Type) [Fintype σ] [Fintype τ],
      MvPolynomial.BrandenHuhSymbolTheorem σ τ)
    {lam : ℝ} (hlam₀ : 0 ≤ lam) (hlam₂ : lam ≤ 2)
    {r : ℕ} (hr : 1 ≤ r) {P : Set (Fin r → ℝ)} (hP : IsIntegralBinaryNestohedron ℝ P) :
    HasNoInternalZeros
      (∑ᶠ q ∈ P.latticePoints, ∏ i, deformedNarayanaPolynomial ℝ lam ⌊q i⌋₊).natDegree
      (∑ᶠ q ∈ P.latticePoints, ∏ i, deformedNarayanaPolynomial ℝ lam ⌊q i⌋₊).coeff :=
  @_root_.Polynomial.hasNoInternalZeros_coeff_finsum_latticePoints_prod_deformedNarayanaPolynomial
    hreal hfert hsub hder hmul hBH hsym lam hlam₀ hlam₂ r hr P hP

end Polynomial

end

section

section

open Finset Polynomial

open Polynomial

namespace Polynomial

/-- **Theorem 7.1.** For integers `k, a ≥ 1` and `n` with `a k ≤ n` and `0 ≤ λ ≤ 2`, the restricted
noncrossing sum `R^{(a),λ}_{n,k}(x)` of deformed Narayana polynomials is log-concave. -/
public theorem
    _root_.LogNarayana.Challenge.Polynomial.isLogConcave_restrictedNoncrossingDeformedNarayanaPoly
    (hKr : Finpartition.KrewerasBlockSizeCount)
    (hreal : IntegralBinaryNestohedronRealization)
    (hfert : RefinedFertilityFormula)
    (hsub : ∀ (σ τ : Type) [Fintype σ] [Fintype τ],
      MvPolynomial.LorentzianNonnegLinearSubstitution σ τ)
    (hder : ∀ (σ : Type) [Fintype σ], MvPolynomial.LorentzianNonnegDerivative σ)
    (hmul : ∀ (σ : Type) [Fintype σ], MvPolynomial.LorentzianMul σ)
    (hBH : ∀ (σ : Type) [Fintype σ],
      MvPolynomial.NormalizedSupportPolyLorentzianOfMConvex σ)
    (hsym : ∀ (σ τ : Type) [Fintype σ] [Fintype τ],
      MvPolynomial.BrandenHuhSymbolTheorem σ τ)
    {n k a : ℕ} (hk : 1 ≤ k) (ha : 1 ≤ a) (hnak : a * k ≤ n)
    {lam : ℝ} (hlam₀ : 0 ≤ lam) (hlam₂ : lam ≤ 2) :
    (restrictedNoncrossingDeformedNarayanaPoly ℝ lam (Finset.Icc 1 n) a k).IsLogConcave :=
  @_root_.Polynomial.isLogConcave_restrictedNoncrossingDeformedNarayanaPoly hKr hreal hfert hsub
    hder hmul hBH hsym n k a hk ha hnak lam hlam₀ hlam₂

end Polynomial

end

section

open Finset Polynomial

open Polynomial

namespace Polynomial

/-- **Theorem 7.1.** For integers `k, a ≥ 1` and `n` with `a k ≤ n` and `0 ≤ λ ≤ 2`, the coefficient
sequence of the restricted noncrossing sum `R^{(a),λ}_{n,k}(x)` of deformed Narayana polynomials has
no internal zeros. -/
public theorem
    _root_.LogNarayana.Challenge.Polynomial.hasNoInternalZeros_coeff_restrictedNoncrossingDeformedNarayanaPoly
    (hKr : Finpartition.KrewerasBlockSizeCount)
    (hreal : IntegralBinaryNestohedronRealization)
    (hfert : RefinedFertilityFormula)
    (hsub : ∀ (σ τ : Type) [Fintype σ] [Fintype τ],
      MvPolynomial.LorentzianNonnegLinearSubstitution σ τ)
    (hder : ∀ (σ : Type) [Fintype σ], MvPolynomial.LorentzianNonnegDerivative σ)
    (hmul : ∀ (σ : Type) [Fintype σ], MvPolynomial.LorentzianMul σ)
    (hBH : ∀ (σ : Type) [Fintype σ],
      MvPolynomial.NormalizedSupportPolyLorentzianOfMConvex σ)
    (hsym : ∀ (σ τ : Type) [Fintype σ] [Fintype τ],
      MvPolynomial.BrandenHuhSymbolTheorem σ τ)
    {n k a : ℕ} (hk : 1 ≤ k) (ha : 1 ≤ a) (hnak : a * k ≤ n)
    {lam : ℝ} (hlam₀ : 0 ≤ lam) (hlam₂ : lam ≤ 2) :
    HasNoInternalZeros
      (restrictedNoncrossingDeformedNarayanaPoly ℝ lam (Finset.Icc 1 n) a k).natDegree
      (restrictedNoncrossingDeformedNarayanaPoly ℝ lam (Finset.Icc 1 n) a k).coeff :=
  @_root_.Polynomial.hasNoInternalZeros_coeff_restrictedNoncrossingDeformedNarayanaPoly hKr hreal
    hfert hsub hder hmul hBH hsym n k a hk ha hnak lam hlam₀ hlam₂

end Polynomial

end

section

open Polynomial

open Polynomial

namespace Polynomial

/-- **Theorem 7.1.** For integers `k, a ≥ 1` and `n` with `a k ≤ n`, the restricted noncrossing
refinement polynomial `R^{(a)}_{n,k}(x)` is log-concave. -/
public theorem
    _root_.LogNarayana.Challenge.Polynomial.isLogConcave_restrictedNoncrossingRefinementPoly
    (hKr : Finpartition.KrewerasBlockSizeCount)
    (hreal : IntegralBinaryNestohedronRealization)
    (hfert : RefinedFertilityFormula)
    (hsub : ∀ (σ τ : Type) [Fintype σ] [Fintype τ],
      MvPolynomial.LorentzianNonnegLinearSubstitution σ τ)
    (hder : ∀ (σ : Type) [Fintype σ], MvPolynomial.LorentzianNonnegDerivative σ)
    (hmul : ∀ (σ : Type) [Fintype σ], MvPolynomial.LorentzianMul σ)
    (hBH : ∀ (σ : Type) [Fintype σ],
      MvPolynomial.NormalizedSupportPolyLorentzianOfMConvex σ)
    (hsym : ∀ (σ τ : Type) [Fintype σ] [Fintype τ],
      MvPolynomial.BrandenHuhSymbolTheorem σ τ)
    {n k a : ℕ} (hk : 1 ≤ k) (ha : 1 ≤ a) (hnak : a * k ≤ n) :
    (restrictedNoncrossingRefinementPoly ℝ (Finset.Icc 1 n) a k).IsLogConcave :=
  @_root_.Polynomial.isLogConcave_restrictedNoncrossingRefinementPoly hKr hreal hfert hsub hder hmul
    hBH hsym n k a hk ha hnak

end Polynomial

end

section

open Polynomial

open Polynomial

namespace Polynomial

/-- **Theorem 7.1.** For integers `k, a ≥ 1` and `n` with `a k ≤ n`, the coefficient sequence of the
restricted noncrossing refinement polynomial `R^{(a)}_{n,k}(x)` has no internal zeros. -/
public theorem
    _root_.LogNarayana.Challenge.Polynomial.hasNoInternalZeros_coeff_restrictedNoncrossingRefinementPoly
    (hKr : Finpartition.KrewerasBlockSizeCount)
    (hreal : IntegralBinaryNestohedronRealization)
    (hfert : RefinedFertilityFormula)
    (hsub : ∀ (σ τ : Type) [Fintype σ] [Fintype τ],
      MvPolynomial.LorentzianNonnegLinearSubstitution σ τ)
    (hder : ∀ (σ : Type) [Fintype σ], MvPolynomial.LorentzianNonnegDerivative σ)
    (hmul : ∀ (σ : Type) [Fintype σ], MvPolynomial.LorentzianMul σ)
    (hBH : ∀ (σ : Type) [Fintype σ],
      MvPolynomial.NormalizedSupportPolyLorentzianOfMConvex σ)
    (hsym : ∀ (σ τ : Type) [Fintype σ] [Fintype τ],
      MvPolynomial.BrandenHuhSymbolTheorem σ τ)
    {n k a : ℕ} (hk : 1 ≤ k) (ha : 1 ≤ a) (hnak : a * k ≤ n) :
    HasNoInternalZeros
      (restrictedNoncrossingRefinementPoly ℝ (Finset.Icc 1 n) a k).natDegree
      (restrictedNoncrossingRefinementPoly ℝ (Finset.Icc 1 n) a k).coeff :=
  @_root_.Polynomial.hasNoInternalZeros_coeff_restrictedNoncrossingRefinementPoly hKr hreal hfert
    hsub hder hmul hBH hsym n k a hk ha hnak

end Polynomial

end

end

section

section NCTwoRealRooted

open Polynomial Finset

namespace Polynomial

/-- **Proposition 7.3.** For all `n k : ℕ`, the restricted noncrossing refinement polynomial
`R^{(2)}_{n,k}(x)` is real-rooted. -/
public theorem
    _root_.LogNarayana.Challenge.Polynomial.splits_restrictedNoncrossingRefinementPoly_two
    (hKr : Finpartition.KrewerasBlockSizeCount)
    (hder : ∀ σ : Type, IsRealStablePDerivClosed σ)
    (hspec : ∀ (σ : Type) [DecidableEq σ], IsRealStableSpecializeClosed σ)
    (n k : ℕ) :
    (restrictedNoncrossingRefinementPoly ℝ (Finset.Icc 1 n) 2 k).Splits :=
  @_root_.Polynomial.splits_restrictedNoncrossingRefinementPoly_two hKr hder hspec n k

end Polynomial

end NCTwoRealRooted

end

section

namespace PartitionAtMostParts

section LogConcave

open Polynomial Pointwise

/-- **Corollary 7.4.** For `a d : ℕ` and `r ≥ 1`, the Narayana transform `Φ_{(a+d,a^{r-1}),r}` of
the hook-shaped Schur polynomial `s_{(a+d,a^{r-1})}(z₁, …, zᵣ)` is log-concave. -/
public theorem
    _root_.LogNarayana.Challenge.PartitionAtMostParts.isLogConcave_schurNarayanaTransform_hook
    (hreal : IntegralBinaryNestohedronRealization)
    (hfert : RefinedFertilityFormula)
    (hsub : ∀ (σ τ : Type) [Fintype σ] [Fintype τ],
      MvPolynomial.LorentzianNonnegLinearSubstitution σ τ)
    (hder : ∀ (σ : Type) [Fintype σ], MvPolynomial.LorentzianNonnegDerivative σ)
    (hmul : ∀ (σ : Type) [Fintype σ], MvPolynomial.LorentzianMul σ)
    (hBH : ∀ (σ : Type) [Fintype σ],
      MvPolynomial.NormalizedSupportPolyLorentzianOfMConvex σ)
    (hsym : ∀ (σ τ : Type) [Fintype σ] [Fintype τ],
      MvPolynomial.BrandenHuhSymbolTheorem σ τ)
    {r : ℕ} (hr : 1 ≤ r) (a d : ℕ) :
    (hook r a d).schurNarayanaTransform.IsLogConcave :=
  @_root_.PartitionAtMostParts.isLogConcave_schurNarayanaTransform_hook hreal hfert hsub hder hmul
    hBH hsym r hr a d

/-- **Corollary 7.4.** For every partition `μ = (μ₁, μ₂)` with at most two parts, the Narayana
transform `Φ_{μ,2}` of the Schur polynomial `s_μ(z₁, z₂)` is log-concave. -/
public theorem
    _root_.LogNarayana.Challenge.PartitionAtMostParts.isLogConcave_schurNarayanaTransform_two
    (hreal : IntegralBinaryNestohedronRealization)
    (hfert : RefinedFertilityFormula)
    (hsub : ∀ (σ τ : Type) [Fintype σ] [Fintype τ],
      MvPolynomial.LorentzianNonnegLinearSubstitution σ τ)
    (hder : ∀ (σ : Type) [Fintype σ], MvPolynomial.LorentzianNonnegDerivative σ)
    (hmul : ∀ (σ : Type) [Fintype σ], MvPolynomial.LorentzianMul σ)
    (hBH : ∀ (σ : Type) [Fintype σ],
      MvPolynomial.NormalizedSupportPolyLorentzianOfMConvex σ)
    (hsym : ∀ (σ τ : Type) [Fintype σ] [Fintype τ],
      MvPolynomial.BrandenHuhSymbolTheorem σ τ)
    (μ : PartitionAtMostParts 2) :
    μ.schurNarayanaTransform.IsLogConcave :=
  @_root_.PartitionAtMostParts.isLogConcave_schurNarayanaTransform_two hreal hfert hsub hder hmul
    hBH hsym μ

end LogConcave

end PartitionAtMostParts

end

section

/-- **Remark after Proposition 9.5.** The polytope `P^nlc ⊆ ℝ^27` is not a generalized
permutohedron. -/
public theorem _root_.LogNarayana.Challenge.not_isGeneralizedPermutohedron_nlcPolytope :
    ¬ IsGeneralizedPermutohedron nlcPolytope :=
  @_root_.not_isGeneralizedPermutohedron_nlcPolytope

section NarayanaSum

open Polynomial

/-- **Proposition 9.5.** There is an integral polytope `P ⊆ ℝ_{>0}^{27}` contained in `{q : ∑ i, q i
= 51}` such that `∑_{q ∈ P ∩ ℤ^{27}} ∏_{i} N_{q_i}(x)` is not log-concave. -/
public theorem
    _root_.LogNarayana.Challenge.exists_isIntegralPolytope_not_isLogConcave_finsum_latticePoints_prod_narayanaPolynomial
    :
    ∃ P : Set (Fin 27 → ℝ), IsIntegralPolytope P ∧ (∀ q ∈ P, ∀ i, 0 < q i) ∧
      (∀ q ∈ P, ∑ i, q i = 51) ∧
      ¬ (∑ᶠ q ∈ P.latticePoints, ∏ i : Fin 27, narayanaPolynomial ⌊q i⌋₊).IsLogConcave :=
  @_root_.exists_isIntegralPolytope_not_isLogConcave_finsum_latticePoints_prod_narayanaPolynomial

end NarayanaSum

end

section

open Filter Topology Finset

namespace MvPolynomial

universe u

section HigherKernelOperator

namespace IsHomogeneous

/-- **Proposition 4.8.** **Degree of the higher kernel operator.** If `K ∈ ℝ[x, t]` is homogeneous
of degree `m` and `U` is homogeneous of degree `d`, then `𝓡^{(m)}_K U = ∂_t^m (U * K)` is
homogeneous of degree `d + 1`: the convolution has degree `d + m + 1`. -/
public theorem _root_.LogNarayana.Challenge.MvPolynomial.IsHomogeneous.higherKernelOperator
    {σ : Type*} {m : ℕ}
    {K : MvPolynomial (Option σ) ℝ} (hK : K.IsHomogeneous m)
    {U : MvPolynomial (Option σ) ℝ} {d : ℕ} (hU : U.IsHomogeneous d) :
    (MvPolynomial.higherKernelOperator m K U).IsHomogeneous (d + 1) :=
  @_root_.MvPolynomial.IsHomogeneous.higherKernelOperator σ m K hK U d hU

end IsHomogeneous

variable {σ R : Type*} [CommSemiring R]

/-- **Proposition 4.8.** The higher kernel operator expanded through the kernel coefficients: if `K`
has degree at most `m ≥ 1` in `t`, then `𝓡^{(m)}_K(U) = W_0 ∫₀ᵗ U ds + W_1 U + ∑_{j=2}^m W_j
∂_t^{j-1} U` with `W_j = kernelCoeff m j K`. Both sides are `R`-linear in `U`, so it suffices to
check monomials. -/
public theorem _root_.LogNarayana.Challenge.MvPolynomial.higherKernelOperator_eq_sum_kernelCoeff
    [Algebra ℚ R] {m : ℕ} (hm : 1 ≤ m)
    {K : MvPolynomial (Option σ) R} (hK : K.degreeOf none ≤ m) (U : MvPolynomial (Option σ) R) :
    higherKernelOperator m K U =
      rename some (kernelCoeff m 0 K) * antiderivative none U +
        rename some (kernelCoeff m 1 K) * U +
        ∑ j ∈ Finset.Icc 2 m, rename some (kernelCoeff m j K) * (pderiv none)^[j - 1] U :=
  @_root_.MvPolynomial.higherKernelOperator_eq_sum_kernelCoeff σ R _ _ m hm K hK U

end HigherKernelOperator

section Lorentzian_preserves

/-- **Proposition 4.8.** **Higher kernels preserve the Lorentzian property.** Let `m : ℕ` and let
`K ∈ ℝ[x, t]` be Lorentzian. Then for every Lorentzian `U ∈ ℝ[x, t]`, the polynomial
`𝓡^{(m)}_K U = ∂_t^m (U * K)` is Lorentzian. -/
public theorem _root_.LogNarayana.Challenge.MvPolynomial.isLorentzian_higherKernelOperator
    {σ : Type u} [Fintype σ]
    (hsub : ∀ (τ τ' : Type u) [Fintype τ] [Fintype τ'], LorentzianNonnegLinearSubstitution τ τ')
    (hmul : ∀ (τ : Type u) [Fintype τ], LorentzianMul τ)
    (hBH : ∀ (τ : Type u) [Fintype τ], NormalizedSupportPolyLorentzianOfMConvex τ)
    (hsym : ∀ (τ τ' : Type u) [Fintype τ] [Fintype τ'], BrandenHuhSymbolTheorem τ τ')
    (hder : ∀ (τ : Type u) [Fintype τ], LorentzianNonnegDerivative τ)
    {m : ℕ} {K : MvPolynomial (Option σ) ℝ} (hK : K.IsLorentzian)
    {U : MvPolynomial (Option σ) ℝ} (hU : U.IsLorentzian) :
    (higherKernelOperator m K U).IsLorentzian :=
  @_root_.MvPolynomial.isLorentzian_higherKernelOperator σ _ hsub hmul hBH hsym hder m K hK U hU

end Lorentzian_preserves

end MvPolynomial

end

section

namespace MvPolynomial

/-- **Proposition 6.2.** For a finite set `σ`, the Appell operator `𝔄` preserves real stability: if
`F ∈ ℝ[z_i : i ∈ σ]` is real-stable, so is `𝔄(F)`. -/
public theorem _root_.LogNarayana.Challenge.MvPolynomial.isRealStable_appellOperator
    (hLW : ShiftedNarayanaNegRealRoots) {σ : Type*} [Finite σ]
    (hBB : RealStablePreserverOfSymbol σ) {F : MvPolynomial σ ℝ} (hF : F.IsRealStable) :
    (appellOperator ℝ σ F).IsRealStable :=
  @_root_.MvPolynomial.isRealStable_appellOperator hLW σ _ hBB F hF

end MvPolynomial

end

section

universe u

open Polynomial

namespace MvPolynomial

namespace IsHomogeneous

/-- **Corollary 6.3.** **The deformed Narayana transform is real-rooted**: if `F ∈ ℝ[z_σ]` is
homogeneous of degree `D`, real-stable and has nonnegative coefficients, then for every real `λ ≥ 0`
the polynomial `𝒩_λ(F)` is real-rooted. -/
public theorem
    _root_.LogNarayana.Challenge.MvPolynomial.IsHomogeneous.splits_deformedNarayanaTransform
    (hBB : ∀ τ : Type u, RealStablePreserverOfSymbol τ)
    (hNR : ShiftedNarayanaNegRealRoots)
    {σ : Type u} [Finite σ] {D : ℕ} {F : MvPolynomial σ ℝ}
    (hD : F.IsHomogeneous D) (hstable : F.IsRealStable)
    (hnonneg : F.HasNonnegCoeffs) {lam : ℝ} (hlam : 0 ≤ lam) :
    (deformedNarayanaTransform ℝ lam σ F).Splits :=
  @_root_.MvPolynomial.IsHomogeneous.splits_deformedNarayanaTransform hBB hNR σ _ D F hD hstable
    hnonneg lam hlam

end IsHomogeneous

namespace IsHomogeneous

/-- **Theorem 1.4.** The Narayana transform of a real-stable polynomial `F ∈ ℝ[z_σ]` with
nonnegative coefficients, homogeneous of degree `D`, has only negative real zeros. -/
public theorem
    _root_.LogNarayana.Challenge.MvPolynomial.IsHomogeneous.hasOnlyNegativeRoots_narayanaTransform
    (hBB : ∀ τ : Type u, RealStablePreserverOfSymbol τ)
    (hNR : ShiftedNarayanaNegRealRoots)
    {σ : Type u} [Finite σ] {D : ℕ} {F : MvPolynomial σ ℝ}
    (hD : F.IsHomogeneous D) (hstable : F.IsRealStable)
    (hnonneg : F.HasNonnegCoeffs) :
    (narayanaTransform σ F).HasOnlyNegativeRoots :=
  @_root_.MvPolynomial.IsHomogeneous.hasOnlyNegativeRoots_narayanaTransform hBB hNR σ _ D F hD
    hstable hnonneg

end IsHomogeneous

/-- **Theorem 1.4.** If `F ∈ ℝ[z_σ]` is homogeneous of degree `D`, real-stable and has nonnegative
coefficients, then its Narayana transform `𝒩(F)` is real-rooted. -/
public theorem
    _root_.LogNarayana.Challenge.MvPolynomial.splits_narayanaTransform_of_isRealStable
    (hBB : ∀ τ : Type u, RealStablePreserverOfSymbol τ) (hLW : ShiftedNarayanaNegRealRoots)
    {σ : Type u} [Finite σ] {D : ℕ} {F : MvPolynomial σ ℝ}
    (hFhom : F.IsHomogeneous D) (hFst : F.IsRealStable) (hFnn : F.HasNonnegCoeffs) :
    (narayanaTransform σ F).Splits :=
  @_root_.MvPolynomial.splits_narayanaTransform_of_isRealStable hBB hLW σ _ D F hFhom hFst hFnn

end MvPolynomial

end

section

namespace LooplessMultigraph

section Bijection

variable {R : Type*} {V E : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R]
  [DecidableEq V] [Fintype E]

namespace IsForest

/-- **Lemma 6.4.** For a forest `G` and an integer vector `a`, the map `h ↦ a + (indeg_h(v))_v` is a
bijection from the orientations `Or(G)` onto the lattice points of the zonotope `P_{G,a}`. -/
public theorem
    _root_.LogNarayana.Challenge.LooplessMultigraph.IsForest.bijOn_add_indegree_orientations_latticePoints_zonotope
    {G : LooplessMultigraph V E} (hG : G.IsForest) (a : V → ℤ) :
    Set.BijOn (fun h : E → V => fun v => (a v : R) + (indegree h v : R)) G.orientations
      (G.zonotope (fun v => (a v : R))).latticePoints :=
  @_root_.LooplessMultigraph.IsForest.bijOn_add_indegree_orientations_latticePoints_zonotope R V E _
    _ _ _ _ G hG a

end IsForest

end Bijection

section NarayanaSums

open Polynomial

universe u

variable {V E : Type u} [Fintype V] [DecidableEq V] [Fintype E]

namespace IsForest

/-- **Theorem 6.5.** For a forest `G` and a positive integer vector `a`, the polynomial `∑_{q ∈
P_{G,a} ∩ ℤ^V} ∏_v Ñ_{q_v - 1}(x)` has only negative real zeros. -/
public theorem
    _root_.LogNarayana.Challenge.LooplessMultigraph.IsForest.hasOnlyNegativeRoots_finsum_latticePoints_zonotope
    (hBB : ∀ σ : Type u, RealStablePreserverOfSymbol σ)
    (hLW : ShiftedNarayanaNegRealRoots)
    {G : LooplessMultigraph V E} (hG : G.IsForest) (a : V → ℤ) (ha : ∀ v, 0 < a v) :
    (∑ᶠ (q : V → ℤ) (_ : (fun v => (q v : ℝ)) ∈
        (G.zonotope (fun v => (a v : ℝ))).latticePoints),
      ∏ v, shiftedNarayanaPolynomial (q v - 1).toNat).HasOnlyNegativeRoots :=
  @_root_.LooplessMultigraph.IsForest.hasOnlyNegativeRoots_finsum_latticePoints_zonotope V E _ _ _
    hBB hLW G hG a ha

end IsForest

namespace IsForest

/-- **Theorem 6.5.** For a forest `G` and a positive integer vector `a`, the polynomial `∑_{q ∈
P_{G,a} ∩ ℤ^V} ∏_v N_{q_v}(x)` is real-rooted. -/
public theorem
    _root_.LogNarayana.Challenge.LooplessMultigraph.IsForest.splits_finsum_latticePoints_zonotope
    (hBB : ∀ σ : Type u, RealStablePreserverOfSymbol σ)
    (hLW : ShiftedNarayanaNegRealRoots)
    {G : LooplessMultigraph V E} (hG : G.IsForest) (a : V → ℤ) (ha : ∀ v, 0 < a v) :
    (∑ᶠ (q : V → ℤ) (_ : (fun v => (q v : ℝ)) ∈
        (G.zonotope (fun v => (a v : ℝ))).latticePoints),
      ∏ v, narayanaPolynomial (q v).toNat).Splits :=
  @_root_.LooplessMultigraph.IsForest.splits_finsum_latticePoints_zonotope V E _ _ _ hBB hLW G hG a
    ha

end IsForest

end NarayanaSums

end LooplessMultigraph

end

section

namespace List

section ULC

open MvPolynomial

/-- **Theorem 5.1.** Let `L, a, b` be positive integers with `L ≤ 2ab`, and let `X_L, X_a, X_b` be
finite sets of colors with `|X_L| = L`, `|X_a| = a`, `|X_b| = b`. For `n ≥ 1` and `π ∈ S_n`, the
polynomial `D_{π,𝐔_{X_L,X_a,X_b}}(x)` is ultra-log-concave of order `n - 1`. -/
public theorem
    _root_.LogNarayana.Challenge.List.isUltraLogConcave_familyFiberDescentPolynomial_localColorFamily
    {C : Type*}
    [BinaryTree.TreeColors C] {X_L X_a X_b : Finset C} {L a b : ℕ} (hL0 : 0 < L) (ha0 : 0 < a)
    (hb0 : 0 < b) (hLab : L ≤ 2 * a * b) (hL : X_L.card = L) (ha : X_a.card = a)
    (hb : X_b.card = b) {n : ℕ} (hn : 1 ≤ n) {π : List ℕ} (hπ : π ∈ permWords n)
    (hsub : ∀ (σ τ : Type) [Fintype σ] [Fintype τ],
      MvPolynomial.LorentzianNonnegLinearSubstitution σ τ)
    (hder : ∀ (σ : Type) [Fintype σ], MvPolynomial.LorentzianNonnegDerivative σ)
    (hmul : ∀ (σ : Type) [Fintype σ], MvPolynomial.LorentzianMul σ)
    (hBH : ∀ (σ : Type) [Fintype σ], MvPolynomial.NormalizedSupportPolyLorentzianOfMConvex σ)
    (hsym : ∀ (σ τ : Type) [Fintype σ] [Fintype τ], MvPolynomial.BrandenHuhSymbolTheorem σ τ) :
    (familyFiberDescentPolynomial ℝ
      (BinaryTree.localColorFamily (X_L : Set C) X_a X_b) π).IsUltraLogConcave (n - 1) :=
  @_root_.List.isUltraLogConcave_familyFiberDescentPolynomial_localColorFamily C _ X_L X_a X_b L a b
    hL0 ha0 hb0 hLab hL ha hb n hn π hπ hsub hder hmul hBH hsym

end ULC

/-- **Theorem 5.1.** Let `L, a, b` be positive integers with `L ≤ 2ab`, and let `X_L, X_a, X_b` be
finite sets of colors with `|X_L| = L`, `|X_a| = a`, `|X_b| = b`. For `n ≥ 1` and `π ∈ S_n`, the
polynomial `D_{π,𝐔_{X_L,X_a,X_b}}(x)` is log-concave. -/
public theorem
    _root_.LogNarayana.Challenge.List.isLogConcave_familyFiberDescentPolynomial_localColorFamily
    {C : Type*}
    [BinaryTree.TreeColors C] {X_L X_a X_b : Finset C} {L a b : ℕ} (hL0 : 0 < L) (ha0 : 0 < a)
    (hb0 : 0 < b) (hLab : L ≤ 2 * a * b) (hL : X_L.card = L) (ha : X_a.card = a)
    (hb : X_b.card = b) {n : ℕ} (hn : 1 ≤ n) {π : List ℕ} (hπ : π ∈ permWords n)
    (hsub : ∀ (σ τ : Type) [Fintype σ] [Fintype τ],
      MvPolynomial.LorentzianNonnegLinearSubstitution σ τ)
    (hder : ∀ (σ : Type) [Fintype σ], MvPolynomial.LorentzianNonnegDerivative σ)
    (hmul : ∀ (σ : Type) [Fintype σ], MvPolynomial.LorentzianMul σ)
    (hBH : ∀ (σ : Type) [Fintype σ], MvPolynomial.NormalizedSupportPolyLorentzianOfMConvex σ)
    (hsym : ∀ (σ τ : Type) [Fintype σ] [Fintype τ], MvPolynomial.BrandenHuhSymbolTheorem σ τ) :
    (familyFiberDescentPolynomial ℝ
      (BinaryTree.localColorFamily (X_L : Set C) X_a X_b) π).IsLogConcave :=
  @_root_.List.isLogConcave_familyFiberDescentPolynomial_localColorFamily C _ X_L X_a X_b L a b hL0
    ha0 hb0 hLab hL ha hb n hn π hπ hsub hder hmul hBH hsym

end List

end

section

section

open MvPolynomial Set

namespace List

/-- **Theorem 1.2.** For `n ≥ 1` and `π ∈ S_n` with nonempty stack-sorting fiber, there is a laminar
matroid on `{x, y} × [n]` all of whose bases have `n - 1` elements and whose basis generating
polynomial is the fiber top polynomial `𝒟_π`. -/
public theorem
    _root_.LogNarayana.Challenge.List.exists_isLaminar_basisGeneratingPolynomial_eq_fiberTopPolynomial
    {n : ℕ} (hn : 1 ≤ n) {π : List ℕ} (hπ : π ∈ permWords n) (hfib : (stackFiber π).Nonempty) :
    ∃ M : Matroid ↥(Finset.univ ×ˢ Finset.Icc 1 n : Finset (Bool × ℕ)),
      M.E = Set.univ ∧ M.IsLaminar ∧ (∀ B, M.IsBase B → B.encard = ((n - 1 : ℕ) : ℕ∞)) ∧
      rename Subtype.val (M.basisGeneratingPolynomial ℝ) = fiberTopPolynomial ℝ π :=
  @_root_.List.exists_isLaminar_basisGeneratingPolynomial_eq_fiberTopPolynomial n hn π hπ hfib

end List

end

section

open MvPolynomial

namespace List

/-- **Theorem 1.2.** For `n ≥ 1` and `π ∈ S_n`, the fiber top polynomial `𝒟_π(x, y)` is Lorentzian:
it is the image, under renaming along the inclusion `{x, y} × [n] ↪ Bool × ℕ`, of a Lorentzian
polynomial in the variables `{x, y} × [n]`. This is stated given the Brändén–Huh theorem that
normalized support polynomials of M-convex sets are Lorentzian. -/
public theorem _root_.LogNarayana.Challenge.List.isLorentzian_fiberTopPolynomial
    {n : ℕ} (hn : 1 ≤ n) {π : List ℕ}
    (hπ : π ∈ permWords n)
    (hBH : NormalizedSupportPolyLorentzianOfMConvex
      ↥(Finset.univ ×ˢ Finset.Icc 1 n : Finset (Bool × ℕ))) :
    ∃ p : MvPolynomial ↥(Finset.univ ×ˢ Finset.Icc 1 n : Finset (Bool × ℕ)) ℝ,
      rename Subtype.val p = fiberTopPolynomial ℝ π ∧ p.IsLorentzian :=
  @_root_.List.isLorentzian_fiberTopPolynomial n hn π hπ hBH

end List

end

section

open List Polynomial

namespace List

/-- **Theorem 1.1.** For `n ≥ 1` and `π ∈ S_n`, the fiber descent polynomial `D_π(x)` is
ultra-log-concave of order `n - 1`. -/
public theorem _root_.LogNarayana.Challenge.List.isUltraLogConcave_fiberDescentPolynomial
    {n : ℕ} (hn : 1 ≤ n) {π : List ℕ}
    (hπ : π ∈ permWords n)
    (hBH : MvPolynomial.NormalizedSupportPolyLorentzianOfMConvex
      ↥(Finset.univ ×ˢ Finset.Icc 1 n : Finset (Bool × ℕ)))
    (hsub : MvPolynomial.LorentzianNonnegLinearSubstitution
      ↥(Finset.univ ×ˢ Finset.Icc 1 n : Finset (Bool × ℕ)) (Fin 2)) :
    (fiberDescentPolynomial ℝ π).IsUltraLogConcave (n - 1) :=
  @_root_.List.isUltraLogConcave_fiberDescentPolynomial n hn π hπ hBH hsub

end List

end

section

namespace List

/-- **Theorem 1.1.** For `n ≥ 1` and `π ∈ S_n`, the fiber descent polynomial `D_π(x)` is
log-concave. -/
public theorem _root_.LogNarayana.Challenge.List.isLogConcave_fiberDescentPolynomial
    {n : ℕ} (hn : 1 ≤ n) {π : List ℕ}
    (hπ : π ∈ permWords n)
    (hBH : MvPolynomial.NormalizedSupportPolyLorentzianOfMConvex
      ↥(Finset.univ ×ˢ Finset.Icc 1 n : Finset (Bool × ℕ)))
    (hsub : MvPolynomial.LorentzianNonnegLinearSubstitution
      ↥(Finset.univ ×ˢ Finset.Icc 1 n : Finset (Bool × ℕ)) (Fin 2)) :
    (fiberDescentPolynomial ℝ π).IsLogConcave :=
  @_root_.List.isLogConcave_fiberDescentPolynomial n hn π hπ hBH hsub

end List

end

section

open MvPolynomial

namespace List

/-- **Corollary 3.6.** For `n ≥ 1`, `π ∈ S_n`, finite sets `A_d, B_d, A_a, B_a` such that some `σ ∈
s⁻¹(π)` has `A_d ⊆ DT(σ) ⊆ [n] ∖ B_d` and `A_a ⊆ AT(σ) ⊆ [n] ∖ B_a`, weights `α, β` positive on
`[n]`, and `J_d ⊆ [n] ∖ (A_d ∪ B_d)`, `J_a ⊆ [n] ∖ (A_a ∪ B_a)`, the conditional top polynomial is
ultra-log-concave of order `n - 1 - |A_d| - |A_a|`. -/
public theorem _root_.LogNarayana.Challenge.List.isUltraLogConcave_conditionalTopPolynomial
    {n : ℕ} (hn : 1 ≤ n) {π : List ℕ}
    (hπ : π ∈ permWords n) (A_d B_d A_a B_a J_d J_a : Finset ℕ)
    (hΩ : ∃ σ ∈ stackFiber π, A_d ⊆ σ.descentTops ∧ σ.descentTops ⊆ Finset.Icc 1 n \ B_d ∧
      A_a ⊆ σ.ascentTops ∧ σ.ascentTops ⊆ Finset.Icc 1 n \ B_a)
    (α β : ℕ → ℝ) (hα : ∀ a ∈ Finset.Icc 1 n, 0 < α a) (hβ : ∀ b ∈ Finset.Icc 1 n, 0 < β b)
    (hJd : J_d ⊆ Finset.Icc 1 n \ (A_d ∪ B_d)) (hJa : J_a ⊆ Finset.Icc 1 n \ (A_a ∪ B_a))
    (hBH : NormalizedSupportPolyLorentzianOfMConvex
      ↥(Finset.univ ×ˢ Finset.Icc 1 n : Finset (Bool × ℕ)))
    (hder : LorentzianNonnegDerivative ↥(Finset.univ ×ˢ Finset.Icc 1 n : Finset (Bool × ℕ)))
    (hsub : LorentzianNonnegLinearSubstitution
      ↥(Finset.univ ×ˢ Finset.Icc 1 n : Finset (Bool × ℕ))
      ↥(Finset.univ ×ˢ Finset.Icc 1 n : Finset (Bool × ℕ)))
    (hsub₂ : LorentzianNonnegLinearSubstitution
      ↥(Finset.univ ×ˢ Finset.Icc 1 n : Finset (Bool × ℕ)) (Fin 2)) :
    (conditionalTopPolynomial ℝ π A_d B_d A_a B_a J_d J_a α β).IsUltraLogConcave
      (n - 1 - A_d.card - A_a.card) :=
  @_root_.List.isUltraLogConcave_conditionalTopPolynomial n hn π hπ A_d B_d A_a B_a J_d J_a hΩ α β
    hα hβ hJd hJa hBH hder hsub hsub₂

end List

end

end

section

namespace Matroid

/-- **Proposition 8.1.** The matroid Narayana polynomial `F_{M,a}` of a matroid `M` of rank `k` is
homogeneous of degree `∑ i, a i + k`. -/
public theorem _root_.LogNarayana.Challenge.Matroid.isHomogeneous_narayanaPolynomial
    {α : Type*} [Fintype α]
    (M : Matroid α) {k : ℕ} (hk : M.eRank = k) (a : α → ℕ) :
    (M.narayanaPolynomial a).IsHomogeneous (∑ i, a i + k) :=
  @_root_.Matroid.isHomogeneous_narayanaPolynomial α _ M k hk a

end Matroid

namespace Matroid

/-- **Proposition 8.1.** **Matroid Narayana polynomials are Lorentzian**: for a matroid `M` on a
finite type `α` and `a : α → ℕ`, `M.narayanaPolynomial a` is Lorentzian. -/
public theorem _root_.LogNarayana.Challenge.Matroid.isLorentzian_narayanaPolynomial
    (hRR : ShiftedNarayanaNegRealRoots) (hInt : ShiftedNarayanaInterlacing)
    (hHom : ∀ σ : Type, IsRealStableHomogenizeOfNonneg σ)
    {α : Type} [Fintype α] (hLor : IsLorentzianOfRealStable (Fin 2 ⊕ α))
    (hBH : MvPolynomial.NormalizedSupportPolyLorentzianOfMConvex α)
    (hSym : MvPolynomial.BrandenHuhSymbolTheorem α (Fin 2))
    (M : Matroid α) (a : α → ℕ) :
    (M.narayanaPolynomial a).IsLorentzian :=
  @_root_.Matroid.isLorentzian_narayanaPolynomial hRR hInt hHom α _ hLor hBH hSym M a

end Matroid

namespace Matroid

/-- **Proposition 8.1.** **Ultra-log-concavity at `y = 1`**: for a matroid `M` of rank `k` on a
finite type `α` and `a : α → ℕ`, `F_{M,a}(x, 1)` is ultra-log-concave of order `∑ i, a i + k`. -/
public theorem _root_.LogNarayana.Challenge.Matroid.isUltraLogConcave_aeval_narayanaPolynomial
    (hRR : ShiftedNarayanaNegRealRoots) (hInt : ShiftedNarayanaInterlacing)
    (hHom : ∀ σ : Type, IsRealStableHomogenizeOfNonneg σ)
    {α : Type} [Fintype α] (hLor : IsLorentzianOfRealStable (Fin 2 ⊕ α))
    (hBH : MvPolynomial.NormalizedSupportPolyLorentzianOfMConvex α)
    (hSym : MvPolynomial.BrandenHuhSymbolTheorem α (Fin 2))
    (M : Matroid α) {k : ℕ} (hk : M.eRank = k) (a : α → ℕ) :
    (MvPolynomial.aeval ![(Polynomial.X : Polynomial ℝ), 1]
      (M.narayanaPolynomial a)).IsUltraLogConcave (∑ i, a i + k) :=
  @_root_.Matroid.isUltraLogConcave_aeval_narayanaPolynomial hRR hInt hHom α _ hLor hBH hSym M k hk
    a

end Matroid

namespace Matroid

/-- **Proposition 8.1.** **Real-rootedness for real-stable matroids**: for a matroid `M` on a finite
type `α` and `a : α → ℕ`, if the basis generating polynomial `B_M` is real-stable, then `F_{M,a}(x,
1)` is real-rooted. -/
public theorem _root_.LogNarayana.Challenge.Matroid.splits_aeval_narayanaPolynomial.{u}
    (hBB : ∀ τ : Type u, RealStablePreserverOfSymbol τ)
    (hLW : ShiftedNarayanaNegRealRoots)
    {α : Type u} [Fintype α] (M : Matroid α) (a : α → ℕ)
    (hB : (M.basisGeneratingPolynomial ℝ).IsRealStable) :
    (MvPolynomial.aeval ![(Polynomial.X : Polynomial ℝ), 1]
      (M.narayanaPolynomial a)).Splits :=
  @_root_.Matroid.splits_aeval_narayanaPolynomial hBB hLW α _ M a hB

end Matroid

end

section

open Filter Topology Asymptotics MvPolynomial

universe u

namespace Matroid

/-- **Proposition 3.7.** **Independent-set polynomials are Lorentzian.** Let `M` be a matroid on a
finite type `α` and `N` a bound on the size of its bases. Then `∑_{I ∈ 𝕀(M)} z^I t^{N - |I|} / (N -
|I|)!` is Lorentzian, given the Brändén–Huh theorems on normalized support polynomials of M-convex
sets, on nonnegative linear substitutions, and on closedness of the Lorentzian class. -/
public theorem
    _root_.LogNarayana.Challenge.Matroid.isLorentzian_sum_indep_mul_X_pow_div_factorial
    {α : Type u} [Fintype α]
    (hBH : ∀ (σ : Type u) [Fintype σ], NormalizedSupportPolyLorentzianOfMConvex σ)
    (hsub : ∀ (σ τ : Type u) [Fintype σ] [Fintype τ], LorentzianNonnegLinearSubstitution σ τ)
    (hclosed : IsLorentzianClosed (Option α))
    (M : Matroid α) (N : ℕ) (hN : ∀ B, M.IsBase B → B.encard ≤ N) :
    open scoped Classical in
    (∑ I ∈ (Finset.univ : Finset (Finset α)).filter
        (fun I : Finset α => M.Indep (I : Set α)),
      (∏ e ∈ I, X (some e)) * C (1 / ((N - I.card).factorial : ℝ)) * X none ^ (N - I.card) :
      MvPolynomial (Option α) ℝ).IsLorentzian :=
  @_root_.Matroid.isLorentzian_sum_indep_mul_X_pow_div_factorial α _ hBH hsub hclosed M N hN

end Matroid

end

section

namespace List

section StableFiber

open Polynomial MvPolynomial

/-- **Corollary 6.7.** For `n ≥ 1` and `π ∈ S_n`, if `F_π` is real-stable then `D_π` is real-rooted.
-/
public theorem
    _root_.LogNarayana.Challenge.List.splits_fiberDescentPolynomial_of_isRealStable_validCompositionPoly
    (hBB : ∀ σ : Type, RealStablePreserverOfSymbol σ)
    (hroots : ShiftedNarayanaNegRealRoots)
    (hfert : RefinedFertilityFormula)
    {n : ℕ} (hn : 1 ≤ n) {π : List ℕ} (hπ : π ∈ permWords n)
    (hF : (validCompositionPoly ℝ π).IsRealStable) :
    (fiberDescentPolynomial ℝ π).Splits :=
  @_root_.List.splits_fiberDescentPolynomial_of_isRealStable_validCompositionPoly hBB hroots hfert n
    hn π hπ hF

end StableFiber

end List

end

section

open MvPolynomial

namespace List

/-- **Proposition 5.2.** **Schröder identity**: for `n ≥ 1` and `π ∈ S_n`, `𝒞_π(z, w) = (z + w)
H_π(z + w, z)`, where `z = X 0` and `w = X 1`. -/
public theorem _root_.LogNarayana.Challenge.List.schroederFiberPolynomial_eq
    (R : Type*) [CommSemiring R] (C : Type*)
    [BinaryTree.TreeColors C] [DecidableEq C] {n : ℕ} (hn : 1 ≤ n) {π : List ℕ}
    (hπ : π ∈ permWords n) :
    schroederFiberPolynomial R C π =
      (X 0 + X 1) * bind₁ ![X 0 + X 1, X 0] (fiberHomogPolynomial R π) :=
  @_root_.List.schroederFiberPolynomial_eq R _ C _ _ n hn π hπ

/-- **Proposition 5.2.** For `n ≥ 1` and `π ∈ S_n`, the Schröder postorder polynomial `𝒞_π(z, w)` is
Lorentzian, given the Brändén–Huh theorems that normalized support polynomials of M-convex sets are
Lorentzian, that nonnegative linear substitutions preserve Lorentzian polynomials, and that products
of Lorentzian polynomials are Lorentzian. -/
public theorem _root_.LogNarayana.Challenge.List.isLorentzian_schroederFiberPolynomial
    (C : Type*)
    [BinaryTree.TreeColors C] [DecidableEq C] {n : ℕ} (hn : 1 ≤ n) {π : List ℕ}
    (hπ : π ∈ permWords n)
    (hBH : NormalizedSupportPolyLorentzianOfMConvex
      ↥(Finset.univ ×ˢ Finset.Icc 1 n : Finset (Bool × ℕ)))
    (hsub : LorentzianNonnegLinearSubstitution
      ↥(Finset.univ ×ˢ Finset.Icc 1 n : Finset (Bool × ℕ)) (Fin 2))
    (hsub₂ : LorentzianNonnegLinearSubstitution (Fin 2) (Fin 2))
    (hmul : LorentzianMul (Fin 2)) :
    (schroederFiberPolynomial ℝ C π).IsLorentzian :=
  @_root_.List.isLorentzian_schroederFiberPolynomial C _ _ n hn π hπ hBH hsub hsub₂ hmul

/-- **Proposition 5.2.** For `n ≥ 1` and `π ∈ S_n`, the polynomial `𝒞_π(z, 1) ∈ ℝ[z]` is
ultra-log-concave of order `n`, given the Brändén–Huh theorems that normalized support polynomials
of M-convex sets are Lorentzian, that nonnegative linear substitutions preserve Lorentzian
polynomials, and that products of Lorentzian polynomials are Lorentzian. -/
public theorem
    _root_.LogNarayana.Challenge.List.isUltraLogConcave_schroederFiberPolynomial_eval_one
    (C : Type*)
    [BinaryTree.TreeColors C] [DecidableEq C] {n : ℕ} (hn : 1 ≤ n) {π : List ℕ}
    (hπ : π ∈ permWords n)
    (hBH : NormalizedSupportPolyLorentzianOfMConvex
      ↥(Finset.univ ×ˢ Finset.Icc 1 n : Finset (Bool × ℕ)))
    (hsub : LorentzianNonnegLinearSubstitution
      ↥(Finset.univ ×ˢ Finset.Icc 1 n : Finset (Bool × ℕ)) (Fin 2))
    (hsub₂ : LorentzianNonnegLinearSubstitution (Fin 2) (Fin 2))
    (hmul : LorentzianMul (Fin 2)) :
    (aeval ![Polynomial.X, 1] (schroederFiberPolynomial ℝ C π) : Polynomial ℝ).IsUltraLogConcave
      n :=
  @_root_.List.isUltraLogConcave_schroederFiberPolynomial_eval_one C _ _ n hn π hπ hBH hsub hsub₂
    hmul

end List

end


section

open Polynomial

/-- **Equation (1.4).** For `r ≥ 1` and an integral binary nestohedron `P ⊆ ℝ^r` on which the
coordinate sum is the constant `S`, the Narayana sum `∑_{q ∈ ℤ_{≥0}^r ∩ P} ∏_i N_{q_i}(x)` is
ultra-log-concave of order `S + r - 1`. -/
public theorem _root_.LogNarayana.Challenge.isUltraLogConcave_finsum_prod_narayanaPolynomial
    (hreal : IntegralBinaryNestohedronRealization) (hfert : RefinedFertilityFormula)
    (hsub₀ : ∀ (σ τ : Type) [Fintype σ] [Fintype τ],
      MvPolynomial.LorentzianNonnegLinearSubstitution σ τ)
    (hBH₀ : ∀ (σ : Type) [Fintype σ], MvPolynomial.NormalizedSupportPolyLorentzianOfMConvex σ)
    {r : ℕ} (hr : 1 ≤ r)
    {P : Set (Fin r → ℝ)} (hP : IsIntegralBinaryNestohedron ℝ P) {S : ℕ}
    (hS : ∀ p ∈ P, ∑ i, p i = (S : ℝ)) :
    (∑ᶠ (q : Fin r → ℕ) (_ : (fun i => (q i : ℝ)) ∈ P),
        ∏ i, narayanaPolynomial (q i)).IsUltraLogConcave (S + r - 1) :=
  _root_.isUltraLogConcave_finsum_prod_narayanaPolynomial hreal hfert hsub₀ hBH₀ hr hP hS

end

section

open Polynomial

namespace MvPolynomial

/-- **Example after Corollary 4.7.** Let `P ⊆ ℝ^r`, `r ≥ 1`, be an integral binary nestohedron and
`x = (x₁, …, x_m)`. Then `e₂(x)^{r-1} ∑_{q ∈ P ∩ ℤ^r} ∏_i Q_{q_i - 1}(e₁(x), e₂(x))` is
Lorentzian. -/
public theorem
    _root_.LogNarayana.Challenge.MvPolynomial.isLorentzian_esymm_two_pow_mul_finsum_latticePoints_prod_narayanaQ
    (hreal : IntegralBinaryNestohedronRealization) (hfert : RefinedFertilityFormula)
    (hsub : ∀ (σ τ : Type) [Fintype σ] [Fintype τ], LorentzianNonnegLinearSubstitution σ τ)
    (hder : ∀ (σ : Type) [Fintype σ], LorentzianNonnegDerivative σ)
    (hmul : ∀ (σ : Type) [Fintype σ], LorentzianMul σ)
    (hBH : ∀ (σ : Type) [Fintype σ], NormalizedSupportPolyLorentzianOfMConvex σ)
    (hsym : ∀ (σ τ : Type) [Fintype σ] [Fintype τ], BrandenHuhSymbolTheorem σ τ)
    (m : ℕ) {r : ℕ} (hr : 1 ≤ r) {P : Set (Fin r → ℝ)} (hP : IsIntegralBinaryNestohedron ℝ P) :
    (esymm (Fin m) ℝ 2 ^ (r - 1) * ∑ᶠ q ∈ P.latticePoints,
      ∏ i, aeval ![esymm (Fin m) ℝ 1, esymm (Fin m) ℝ 2]
        (narayanaQ ℝ (⌊q i⌋₊ - 1))).IsLorentzian :=
  _root_.MvPolynomial.isLorentzian_esymm_two_pow_mul_finsum_latticePoints_prod_narayanaQ hreal
    hfert hsub hder hmul hBH hsym m hr hP

end MvPolynomial

end

section

namespace MvPolynomial

universe u

/-- **Section 4.4.** For every finite variable type `σ` and every `m`, the elementary kernel
`K_m(z, t) = ∑_{j=0}^m e_j(z) t^{m-j} / (m-j)!` is real-stable. -/
public theorem _root_.LogNarayana.Challenge.MvPolynomial.isRealStable_elementaryKernel
    {σ : Type u} [Fintype σ] (m : ℕ)
    (hder : ∀ τ : Type u, IsRealStablePDerivClosed τ)
    (hspec : ∀ (τ : Type u) [DecidableEq τ], IsRealStableSpecializeClosed τ)
    (hlim : IsRealStableLimitClosed (Option σ)) :
    (elementaryKernel σ ℝ m).IsRealStable :=
  _root_.MvPolynomial.isRealStable_elementaryKernel m hder hspec hlim

/-- **Section 4.4.** For every finite variable type `σ` and every `m`, the elementary kernel
`K_m(z, t) = ∑_{j=0}^m e_j(z) t^{m-j} / (m-j)!` is Lorentzian. -/
public theorem _root_.LogNarayana.Challenge.MvPolynomial.isLorentzian_elementaryKernel
    {σ : Type u} [Fintype σ] (m : ℕ)
    (hder : ∀ τ : Type u, IsRealStablePDerivClosed τ)
    (hspec : ∀ (τ : Type u) [DecidableEq τ], IsRealStableSpecializeClosed τ)
    (hlim : IsRealStableLimitClosed (Option σ))
    (hBH : IsLorentzianOfRealStable (Option σ)) :
    (elementaryKernel σ ℝ m).IsLorentzian :=
  _root_.MvPolynomial.isLorentzian_elementaryKernel m hder hspec hlim hBH

end MvPolynomial

end

section

namespace Polynomial

/-- **End of Section 5.** For an integral binary nestohedron `P ⊆ ℝ^r`, `r ≥ 1`, the polynomial
`∑_{q ∈ P ∩ ℤ^r} ∏_{i=1}^{r} R_{q_i}(z)` is log-concave. -/
public theorem
    _root_.LogNarayana.Challenge.Polynomial.isLogConcave_finsum_latticePoints_prod_schroederFactor
    (hreal : IntegralBinaryNestohedronRealization)
    (htroupes : SchroederTreesBlackGenFunEq.{0, 0})
    (hrefined : SchroederRefinedFertilityFormula.{0, 0})
    (hsub : ∀ (σ τ : Type) [Fintype σ] [Fintype τ],
      MvPolynomial.LorentzianNonnegLinearSubstitution σ τ)
    (hmul : ∀ (σ : Type) [Fintype σ], MvPolynomial.LorentzianMul σ)
    (hBH : ∀ (σ : Type) [Fintype σ], MvPolynomial.NormalizedSupportPolyLorentzianOfMConvex σ)
    {r : ℕ} (hr : 1 ≤ r) {P : Set (Fin r → ℝ)} (hP : IsIntegralBinaryNestohedron ℝ P) :
    (∑ᶠ q ∈ P.latticePoints, ∏ i, schroederFactor ℝ ⌊q i⌋₊).IsLogConcave :=
  _root_.Polynomial.isLogConcave_finsum_latticePoints_prod_schroederFactor hreal htroupes hrefined
    hsub hmul hBH hr hP

end Polynomial

end

section

namespace LooplessMultigraph

open Polynomial

universe u

variable {V E : Type u} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- **Section 6.2.** For a loopless multigraph `G`, exponents `a` and nonnegative edge weights
`b c` with `b e + c e > 0` on every edge, the weighted orientation sum `O^{b,c}_{G,a}` is
real-rooted. -/
public theorem _root_.LogNarayana.Challenge.LooplessMultigraph.splits_weightedOrientationSum
    (hBB : ∀ σ : Type u, RealStablePreserverOfSymbol σ)
    (hLW : ShiftedNarayanaNegRealRoots)
    (G : LooplessMultigraph V E) (a : V → ℕ) {b c : E → ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hbc : ∀ e, 0 < b e + c e) :
    (G.weightedOrientationSum a b c).Splits :=
  _root_.LooplessMultigraph.splits_weightedOrientationSum hBB hLW G a hb hc hbc

/-- **Section 6.2.** For a loopless multigraph `G` and exponents `a`, the orientation sum
`O_{G,a}` is real-rooted. -/
public theorem _root_.LogNarayana.Challenge.LooplessMultigraph.splits_orientationSum
    (hBB : ∀ σ : Type u, RealStablePreserverOfSymbol σ)
    (hLW : ShiftedNarayanaNegRealRoots)
    (G : LooplessMultigraph V E) (a : V → ℕ) :
    (G.orientationSum a).Splits :=
  _root_.LooplessMultigraph.splits_orientationSum hBB hLW G a

end LooplessMultigraph

end

section

namespace PartitionAtMostParts

open Polynomial

/-- **After Corollary 7.4.** For `r ≥ 1` and every `d`, the Narayana transform `Φ_{(d),r}` of the
one-row shape `(d)` has only negative real zeros. -/
public theorem
    _root_.LogNarayana.Challenge.PartitionAtMostParts.hasOnlyNegativeRoots_schurNarayanaTransform_row
    (hJ : Polynomial.JacobiRootsSimpleInIoo)
    {r : ℕ} (hr : 1 ≤ r) (d : ℕ) :
    (row r d).schurNarayanaTransform.HasOnlyNegativeRoots :=
  _root_.PartitionAtMostParts.hasOnlyNegativeRoots_schurNarayanaTransform_row hJ hr d

/-- **After Corollary 7.4.** For `r ≥ 1` and `d ∈ ℕ`, the polynomial `Φ_{(d+1,1^{r-1}),r}(x)` is
real-rooted. -/
public theorem
    _root_.LogNarayana.Challenge.PartitionAtMostParts.splits_schurNarayanaTransform_hook_one
    (hKr : Finpartition.KrewerasBlockSizeCount)
    (hD : ∀ σ : Type, IsRealStablePDerivClosed σ)
    (hS : ∀ (σ : Type) [DecidableEq σ], IsRealStableSpecializeClosed σ)
    {r : ℕ} (hr : 1 ≤ r) (d : ℕ) :
    (hook r 1 d).schurNarayanaTransform.Splits :=
  _root_.PartitionAtMostParts.splits_schurNarayanaTransform_hook_one hKr hD hS hr d

end PartitionAtMostParts

end
