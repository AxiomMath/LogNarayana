/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib
public import LogNarayana.Attr
public import LogNarayana.Definitions

/-!
# Further definitions

Definitions used in the proofs, examples and cited results of [LogNarayana] that the statements of
the formal challenge do not mention. The definitions the challenge mentions are in
`LogNarayana.Definitions`.

## References

* [LogNarayana] *Log-Concavity in Narayana Transforms and Stack-Sorting Fibers*.
-/

section

namespace Polynomial

/-- A sequence `f : ℕ → R[X]` is an *Appell sequence* if `f m` has degree `m` for every `m`
and `derivative (f (m + 1)) = (m + 1) • f m` for every `m`. -/
@[lognarayana "def_appell_sequence"]
public structure IsAppell {R : Type*} [Semiring R] (f : ℕ → R[X]) : Prop where
  /-- The `m`-th polynomial has degree exactly `m`. -/
  degree_eq : ∀ m, (f m).degree = m
  /-- Differentiation lowers the index: `(f (m + 1))' = (m + 1) • f m`. -/
  derivative_succ : ∀ m, derivative (f (m + 1)) = (m + 1) • f m

end Polynomial

end

section

open Polynomial Finset

/-- The polynomial `M_m(z) = ∑_{j=0}^{⌊m/2⌋} C_j (m choose 2j) z^j`, with `C_j = catalan j`. -/
@[expose, lognarayana "def_narayana_m"]
public noncomputable def narayanaM (R : Type*) [CommSemiring R] (m : ℕ) : R[X] :=
  ∑ j ∈ range (m / 2 + 1), C ((catalan j : R) * (m.choose (2 * j) : R)) * X ^ j

end

section

universe u

open Polynomial

/-- **γ-expansion of the shifted Narayana polynomials** (P. Brändén, *Actions on permutations
and unimodality of descent polynomials*, 2008, eq. (4.1), credited there to Simion–Ullman;
C. Coker, *Enumerating a class of lattice paths*, 2003, eq. (4.4)): for every `m`,
`Ñ_m(x) = ∑_{j=0}^{⌊m/2⌋} catalan j * (m choose 2j) * x^j * (1+x)^(m-2j)`. The sum has the
shape of `IsGammaNonnegWRT`; the subtraction `m - 2 * j` never truncates for `j ≤ m / 2`. -/
@[expose, lognarayana "thm_ext_narayana_gamma"]
public def ShiftedNarayanaGammaExpansion : Prop :=
  ∀ m : ℕ, shiftedNarayanaPolynomial m =
    ∑ j ∈ Finset.range (m / 2 + 1),
      C ((catalan j : ℝ) * (m.choose (2 * j) : ℝ)) * X ^ j * (1 + X) ^ (m - 2 * j)

end

section

@[expose] public section

namespace BinaryTree

variable {α : Type*}

/-- The number `bin(T)` of binary vertices of `T`, i.e. vertices whose left and right subtrees
are both nonempty: `bin(∅) = 0` and `bin(⟨m; T_L, T_R⟩) = bin(T_L) + bin(T_R) + 1` if
`T_L ≠ ∅` and `T_R ≠ ∅`, and `bin(T_L) + bin(T_R)` otherwise. -/
@[lognarayana "def_binary_vertex_count", simp]
def numBinaryNodes : BinaryTree α → ℕ
  | nil => 0
  | node _ l r =>
      numBinaryNodes l + numBinaryNodes r +
        match l, r with
        | node _ _ _, node _ _ _ => 1
        | _, _ => 0

variable [DecidableEq α]

/-- The set `LC(T)` of labels of vertices of `T` having a left child: `LC(∅) = ∅` and
`LC(⟨m; T_L, T_R⟩) = LC(T_L) ∪ LC(T_R) ∪ {m}` if `T_L ≠ ∅`, and `LC(T_L) ∪ LC(T_R)` otherwise. -/
@[lognarayana "def_left_child_labels", simp]
def leftChildLabels : BinaryTree α → Finset α
  | nil => ∅
  | node m l r =>
      leftChildLabels l ∪ leftChildLabels r ∪
        match l with
        | nil => ∅
        | node _ _ _ => {m}

variable [LT α]

end BinaryTree

end

end

section

@[expose] public section

namespace BinaryTree

section VertexTypes

variable {α : Type*}

/-- The number `n_τ(T)` of vertices of `T` whose type (`BinaryTree.vertexType` of its two
subtrees) is `τ`. -/
@[lognarayana "def_vertex_type_count", simp]
public def numNodesOfType (τ : VertexType) : BinaryTree α → ℕ
  | nil => 0
  | node _ l r =>
      numNodesOfType τ l + numNodesOfType τ r + if vertexType l r = τ then 1 else 0

end VertexTypes

section Insertion

variable {C : Type*} [TreeColors C]

/-- The *insertion* `∇_v(T₁, T₂)` of the colored binary plane tree `T₂` into `T₁` at the vertex
`v` of `T₁` (indexed in preorder): the subtree `S` of `T₁` rooted at `v` is replaced by
`node black S T₂`, a new black vertex with left subtree `S` and right subtree `T₂`. -/
@[lognarayana "def_insertion"]
public def insertion : (T₁ : BinaryTree C) → Fin T₁.numNodes → BinaryTree C → BinaryTree C
  | nil, v, _ => v.elim0
  | node a l r, v, T₂ =>
    if h₀ : v.val = 0 then node TreeColors.black (node a l r) T₂
    else if h : v.val - 1 < l.numNodes then node a (insertion l ⟨v.val - 1, h⟩ T₂) r
    else node a l (insertion r ⟨v.val - 1 - l.numNodes,
      Nat.sub_lt_left_of_lt_add (Nat.le_of_not_lt h)
        (Nat.sub_lt_right_of_lt_add (Nat.one_le_iff_ne_zero.mpr h₀) v.isLt)⟩ T₂)

variable {M : Type*} [Add M]

/-- A statistic `f` on colored binary plane trees is *insertion-additive* if
`f (insertion T₁ v T₂) = f T₁ + f T₂` for every colored binary plane tree `T₁`, every vertex `v`
of `T₁` and every nonempty colored binary plane tree `T₂`. -/
@[lognarayana "def_insertion_additive"]
public def IsInsertionAdditive (f : BinaryTree C → M) : Prop :=
  ∀ (T₁ : BinaryTree C) (v : Fin T₁.numNodes) (T₂ : BinaryTree C), T₂ ≠ nil →
    f (insertion T₁ v T₂) = f T₁ + f T₂

end Insertion

end BinaryTree

end

end

section

@[expose] public section

namespace BinaryTree

/-- The set `𝐁 = 𝐔_{𝔗 × {black}}` of colored binary plane trees all of whose vertices are
`black`: the binary plane trees regarded as colored binary plane trees. -/
@[lognarayana "def_black_troupe"]
def blackTrees (C : Type*) [TreeColors C] : Set (BinaryTree C) :=
  localRuleFamily (Set.univ ×ˢ {TreeColors.black})

end BinaryTree

end

end

section

public section

namespace BinaryTree

section Troupe

variable {C : Type*} [TreeColors C]

/-- A *troupe* is a set `𝐓` of colored binary plane trees which is black-peaked (every vertex of
type `bin` of a tree in `𝐓` is `black`) and such that, for all nonempty `T₁`, `T₂` and every
vertex `v` of `T₁`, `T₁ ∈ 𝐓 ∧ T₂ ∈ 𝐓 ↔ ∇_v(T₁, T₂) ∈ 𝐓`. -/
@[lognarayana "def_troupe"]
public structure IsTroupe (𝒯 : Set (BinaryTree C)) : Prop where
  /-- Every vertex of type `bin` of a tree in `𝒯` is colored `black`. -/
  blackPeaked : ∀ T ∈ 𝒯,
    T ∈ localRuleFamily {p : VertexType × C | p.1 = .binary → p.2 = TreeColors.black}
  /-- `𝒯` is closed under insertion and under decomposition along an insertion. -/
  mem_and_mem_iff_insertion_mem : ∀ (T₁ : BinaryTree C) (v : Fin T₁.numNodes)
    (T₂ : BinaryTree C), T₂ ≠ nil → (T₁ ∈ 𝒯 ∧ T₂ ∈ 𝒯 ↔ insertion T₁ v T₂ ∈ 𝒯)

end Troupe

end BinaryTree

end

end

section

namespace Finsupp

/-- The exponent set `J_{m,κ} = {(|κ| + m - 1 - |β|, β) : 0 ≤ β ≤ κ}`, with the first coordinate
at `none` (the variable `t`) and `β_i` at `some i` (the variable `v_i`). -/
@[expose, lognarayana "def_j_kappa"]
public noncomputable def jKappa (m : ℕ) (κ : Fin m →₀ ℕ) : Finset (Option (Fin m) →₀ ℕ) :=
  (Finset.Iic κ).image fun β : Fin m →₀ ℕ =>
    single none (κ.degree + m - 1 - β.degree) + β.mapDomain Option.some

end Finsupp

namespace MvPolynomial

variable (σ : Type*) (R : Type*) [CommSemiring R] [Algebra ℚ R]

/-- The symbol factor `Ψ_{m,κ}(t, v) = ∑_{0 ≤ γ ≤ κ} (κ choose γ) · γ! / (|γ| + m - 1)! ·
t^(|γ| + m - 1) · v^(κ - γ)`, a polynomial in `t = X none` and `v_i = X (some i)`. -/
@[expose, lognarayana "def_psi_kappa"]
public noncomputable def psiKappa (m : ℕ) (κ : Fin m →₀ ℕ) : MvPolynomial (Option (Fin m)) R :=
  ∑ γ ∈ Finset.Iic κ,
    monomial (Finsupp.single none (γ.degree + m - 1) + (κ - γ).mapDomain some)
      (algebraMap ℚ R
        ((κ.choose γ : ℚ) * (γ.factorial : ℚ) / ((γ.degree + m - 1).factorial : ℚ)))

end MvPolynomial

section

variable (ι : Type*) {R : Type*} [Fintype ι] [AddCommMonoid R] [PartialOrder R]

/-- The corner simplex `Δ_ι(θ) = {s : ι → R | (∀ i, 0 ≤ s i) ∧ ∑ i, s i ≤ θ}` of points with
nonnegative coordinates and total mass at most `θ`. -/
@[expose, lognarayana "def_simplex_region"]
public def cornerSimplex (θ : R) : Set (ι → R) :=
  {s | (∀ i, 0 ≤ s i) ∧ ∑ i, s i ≤ θ}

end

end

section

@[expose] public section

namespace MvPolynomial

section Rational

variable (σ : Type*) (R : Type*) [CommSemiring R] [Algebra ℚ R]

/-- The full factorial normalization `𝓔`, the `R`-linear map on `MvPolynomial σ R` sending
each monomial `z^α` to `z^α / α!`. -/
@[lognarayana "def_full_factorial_normalization"]
noncomputable def fullFactorialNormalization : MvPolynomial σ R →ₗ[R] MvPolynomial σ R :=
  (basisMonomials σ R).constr R fun α => monomial α (algebraMap ℚ R (1 / (α.factorial : ℚ)))

variable {σ}

variable {R}

end Rational

end MvPolynomial

end

end

section

@[expose] public section

namespace MvPolynomial

/-- **Brändén–Huh** [BH, Corollary 3.8]: for a finite variable type `σ` and polynomials
`f g ∈ ℝ[z_i : i ∈ σ]`, if `fullFactorialNormalization σ ℝ f` and
`fullFactorialNormalization σ ℝ g` are Lorentzian, then so is
`fullFactorialNormalization σ ℝ (f * g)`. -/
@[lognarayana "thm_ext_bh_normalized_product"]
def FullFactorialNormalizationMulLorentzian (σ : Type*) [Fintype σ] : Prop :=
  ∀ f g : MvPolynomial σ ℝ, (fullFactorialNormalization σ ℝ f).IsLorentzian →
    (fullFactorialNormalization σ ℝ g).IsLorentzian →
    (fullFactorialNormalization σ ℝ (f * g)).IsLorentzian

end MvPolynomial

end

end

section

@[expose] public section

/-- A function `g : E → ℝ` is *log-concave* on `s` if `s` is convex, `g` is nonnegative on `s`,
and `g u ^ t * g v ^ (1 - t) ≤ g (t • u + (1 - t) • v)` for all `u v ∈ s` and `0 < t < 1`
(real powers). -/
@[lognarayana "def_log_concave_function"]
def LogConcaveOn {E : Type*} [AddCommGroup E] [Module ℝ E] (s : Set E) (g : E → ℝ) : Prop :=
  Convex ℝ s ∧ (∀ x ∈ s, 0 ≤ g x) ∧
    ∀ ⦃u⦄, u ∈ s → ∀ ⦃v⦄, v ∈ s → ∀ ⦃t : ℝ⦄, 0 < t → t < 1 →
      g u ^ t * g v ^ (1 - t) ≤ g (t • u + (1 - t) • v)

end

end

section

namespace Finset.Nat

/-- The compositions of `N` into `m` parts: the tuples `q : Fin m → ℕ` with `1 ≤ q i` for every
`i` and `∑ i, q i = N`. The paper's `Comp(N, k+1)` is `compositionTuple (k + 1) N`. -/
@[expose, lognarayana "def_composition"]
public def compositionTuple (m N : ℕ) : Finset (Fin m → ℕ) :=
  (antidiagonalTuple m N).filter fun q => ∀ i, 1 ≤ q i

end Finset.Nat

end

section

open scoped Pointwise

@[expose] public section

namespace List

variable (R : Type*) [Semiring R] [PartialOrder R]

/-- The fertilitope `Fer_π = conv 𝒱(π)` of `π`: the convex hull over `R` of the valid
compositions of `π`, viewed as points of `R^{des(π)+1}` via the coordinatewise cast. -/
@[lognarayana "def_fertilitope"]
noncomputable def fertilitope (π : List ℕ) : Set (Fin (π.numDescents + 1) → R) :=
  convexHull R
    ((fun q i => (q i : R)) '' (π.validCompositions : Set (Fin (π.numDescents + 1) → ℕ)))

end List

end

end

section

section ShiftedNarayanaGenSeries

open Polynomial

/-- The generating series `V(z) = ∑_{m ≥ 0} Ñ_m(x) z^m ∈ ℝ[x]⟦z⟧` of the shifted Narayana
polynomials `shiftedNarayanaPolynomial`. Its `m`-th coefficient is `Ñ_m(x)`
(`PowerSeries.coeff_mk`). -/
@[expose, lognarayana "def_shifted_narayana_gen_series"]
public noncomputable def shiftedNarayanaGenSeries : PowerSeries ℝ[X] :=
  PowerSeries.mk shiftedNarayanaPolynomial

end ShiftedNarayanaGenSeries

end

section

namespace Polynomial

/-- **Real zeros of γ-polynomials** (Brändén, Gal; [FPV, Theorem 1.1]): let `h(x)` be a
symmetric real polynomial with center of symmetry `n/2`, i.e. `deg h ≤ n` and `h_i = h_{n-i}`
for every `i`, and let `h(x) = ∑_{i ≤ ⌊n/2⌋} γ_i x^i (1 + x)^{n - 2i}`. Then the γ-polynomial
`γ_h(x) = ∑_{i ≤ ⌊n/2⌋} γ_i x^i` has only nonpositive real zeros if and only if `h(x)` does. -/
@[expose, lognarayana "thm_ext_fpv_gamma_real_rooted"]
public def GammaRealRootedIff : Prop :=
  ∀ (n : ℕ) (h : ℝ[X]), h.natDegree ≤ n → (∀ i ≤ n, h.coeff i = h.coeff (n - i)) →
    ∀ γ : ℕ → ℝ, h = ∑ i ∈ Finset.range (n / 2 + 1), C (γ i) * X ^ i * (1 + X) ^ (n - 2 * i) →
      let γh : ℝ[X] := ∑ i ∈ Finset.range (n / 2 + 1), C (γ i) * X ^ i
      (γh.Splits ∧ ∀ r ∈ γh.roots, r ≤ 0) ↔ (h.Splits ∧ ∀ r ∈ h.roots, r ≤ 0)

/-- **Newton's inequalities** ([StanleyLC, Theorem 2]): a real polynomial with nonnegative
coefficients and only real zeros is log-concave. -/
@[expose, lognarayana "thm_ext_newton_inequalities"]
public def NewtonInequalities : Prop :=
  ∀ f : ℝ[X], (∀ j, 0 ≤ f.coeff j) → f.Splits → f.IsLogConcave

end Polynomial

end

section

namespace MvPolynomial

section Semifield

variable (σ : Type*) (R : Type*) [Fintype σ] [Semifield R]

/-- The approximant `f_{m,k}(z, t) = e_m(z, t/k, …, t/k)` of the elementary kernel: the image
of `esymm (σ ⊕ Fin k) R m` under `z_i ↦ X (some i)` and `w_l ↦ t / k`, where `t = X none`. -/
@[expose, lognarayana "def_elementary_kernel_approximant"]
public noncomputable def elementaryKernelApproximant (m k : ℕ) : MvPolynomial (Option σ) R :=
  aeval (Sum.elim (fun i : σ => (X (some i) : MvPolynomial (Option σ) R))
      (fun _ : Fin k => C (k : R)⁻¹ * X none))
    (esymm (σ ⊕ Fin k) R m)

end Semifield

end MvPolynomial

end

section

@[expose] public section

namespace LooplessMultigraph

section OrientationPoly

variable {V E : Type*} [Fintype V] [Fintype E]

/-- The *orientation polynomial* `F_{G,a}` of a loopless multigraph `G` with exponent vector `a`:
`∏_v X v ^ (a v - 1) * ∏_e (X (src e) + X (tgt e))`, with coefficients in `R`. -/
@[lognarayana "def_orientation_poly"]
public noncomputable def orientationPoly (R : Type*) [CommSemiring R]
    (G : LooplessMultigraph V E) (a : V → ℕ) : MvPolynomial V R :=
  (∏ v, MvPolynomial.X v ^ (a v - 1)) *
    ∏ e, (MvPolynomial.X (G.src e) + MvPolynomial.X (G.tgt e))

end OrientationPoly

section WeightedOrientationPoly

variable {V E R : Type*} [Fintype V] [Fintype E] [CommSemiring R]

/-- The *weighted orientation polynomial* `F^{b,c}_{G,a}` of a loopless multigraph `G` with
exponent vector `a` and edge weights `b c : E → R`:
`∏_v X v ^ (a v - 1) * ∏_e (C (b e) * X (src e) + C (c e) * X (tgt e))`. -/
@[lognarayana "def_weighted_orientation_poly"]
public noncomputable def weightedOrientationPoly (G : LooplessMultigraph V E) (a : V → ℕ)
    (b c : E → R) : MvPolynomial V R :=
  (∏ v, MvPolynomial.X v ^ (a v - 1)) *
    ∏ e, (MvPolynomial.C (b e) * MvPolynomial.X (G.src e) +
      MvPolynomial.C (c e) * MvPolynomial.X (G.tgt e))

end WeightedOrientationPoly

end LooplessMultigraph

end

end

section

open Polynomial

@[expose] public section

/-- The base polytope `P_M = conv {𝟏_B | B ∈ 𝔹(M)} ⊆ R^α` of a matroid `M`: the convex hull
of the indicator vectors of its bases. -/
@[lognarayana "def_matroid_base_polytope"]
public def Matroid.basePolytope {α : Type*} (R : Type*) [Semiring R] [PartialOrder R]
    (M : Matroid α) : Set (α → R) :=
  convexHull R ((fun B : Set α => B.indicator 1) '' {B | M.IsBase B})

end

/-- The *matroid Narayana operator* `T_a` for `a : α → ℕ`: the `ℝ`-linear map on multiaffine
polynomials in `z_i` (`i ∈ α`) to `ℝ[x, y]` with
`T_a(z^B) = ∏_{i ∈ B} hom(Ñ_{a_i + 1}) ∏_{i ∉ B} hom(Ñ_{a_i})`. It is the restriction to
`restrictSupport ℝ (Set.Iic 𝟙)` of the linear map `z^β ↦ ∏_i hom(Ñ_{a_i + β_i})`. -/
@[expose, lognarayana "def_matroid_narayana_operator"]
public noncomputable def MvPolynomial.matroidNarayanaOperator {α : Type*} [Fintype α]
    (a : α → ℕ) :
    MvPolynomial.restrictSupport ℝ (Set.Iic (Finsupp.equivFunOnFinite.symm 1 : α →₀ ℕ)) →ₗ[ℝ]
      MvPolynomial (Fin 2) ℝ :=
  ((MvPolynomial.basisMonomials α ℝ).constr ℝ fun β =>
      ∏ i, homogShiftedNarayanaPolynomial (a i + β i)).domRestrict
    (MvPolynomial.restrictSupport ℝ (Set.Iic (Finsupp.equivFunOnFinite.symm 1)))

end

section

@[expose] public section

/-- The parent map of the concatenation of a forest with parent map `par` on `[N]` and a forest
with parent map `par'`: it agrees with `par` on `v ≤ N`, and sends `N + v` to `N + par' v`
(or to `none` when `par' v = none`). -/
@[lognarayana "def_forest_concat"]
public def forestConcatParent (N : ℕ) (par par' : ℕ → Option ℕ) : ℕ → Option ℕ :=
  fun v => if v ≤ N then par v else (par' (v - N)).map (N + ·)

/-- The marked set `L ∪ {N + v : v ∈ L'}` of the concatenation of a marked forest `(par, L)` on
`[N]` with a marked forest `(par', L')`. -/
@[lognarayana "def_forest_concat"]
public def forestConcatMarked (N : ℕ) (L L' : Finset ℕ) : Finset ℕ :=
  L ∪ L'.map (addLeftEmbedding N)

/-- The parent map `par°` on `[N + 1]` of the tree obtained from a forest with parent map `par` on
`[N]` by adjoining a root `N + 1`: for `v ∈ [N]` it is `par v` when that is defined and `N + 1`
otherwise, and it is `none` off `[N]` (in particular at the new root `N + 1`). -/
@[lognarayana "def_forest_adjoin_root"]
public def forestAdjoinRootParent (N : ℕ) (par : ℕ → Option ℕ) : ℕ → Option ℕ :=
  fun v => if 1 ≤ v ∧ v ≤ N then some ((par v).getD (N + 1)) else none

/-- The marked singleton `𝒮` on `[1]`: the first component is the parent map, which is `none`
everywhere (so `par 1 = ⊥`), the second the marked set `{1}`. -/
@[lognarayana "def_marked_singleton"]
public def markedSingleton : (ℕ → Option ℕ) × Finset ℕ :=
  (fun _ => none, {1})

end

end

section

/-- The *choice set*
`I(M, O, S) = {v⁺, v⁻ : v ∈ R(M)} ∪ {v⁺ : v ∈ S} ∪ {v⁻ : v ∈ U(M) \ (O ∪ S)}`,
where `v⁺ = (true, v)` and `v⁻ = (false, v)`, `R(M)` is the set of right endpoints of `M` and
`U(M)` the set of unmatched vertices of `M` in `[N]`. -/
@[expose, lognarayana "def_open_choice_set"]
public def Finset.openChoiceSet (N : ℕ) (M : Finset (ℕ × ℕ)) (O S : Finset ℕ) :
    Finset (Bool × ℕ) :=
  (Finset.univ ×ˢ M.image Prod.snd) ∪ ({true} ×ˢ S) ∪
    ({false} ×ˢ (Finset.unmatchedVertices N M \ (O ∪ S)))

/-- The *reconstruction states* `(λ_v, M_v)` of `I ⊆ {x, y} × [N]`, where `v⁺ = (true, v)` and
`v⁻ = (false, v)`. With `c_v = |I ∩ {v⁺, v⁻}|`, start from `(λ_0, M_0) = ([], ∅)`; at step `v`,
if `c_v = 0` append `v` to `λ_{v-1}`; if `c_v = 2` and `λ_{v-1}` has last entry `u`, remove that
entry and add the pair `(u, v)` to `M_{v-1}`; otherwise keep the state. -/
@[expose, lognarayana "def_reconstruction_states"]
public def reconstructionStates (I : Finset (Bool × ℕ)) : ℕ → List ℕ × Finset (ℕ × ℕ)
  | 0 => ([], ∅)
  | v + 1 =>
    let s := reconstructionStates I v
    match (I ∩ {(true, v + 1), (false, v + 1)}).card, s.1.getLast? with
    | 0, _ => (s.1 ++ [v + 1], s.2)
    | 2, some u => (s.1.dropLast, insert (u, v + 1) s.2)
    | _, _ => s

/-- The *reconstruction* `(M_I, O_I, S_I)` of `I ⊆ {x, y} × [N]` (with `v⁺ = (true, v)`,
`v⁻ = (false, v)`): `M_I = M_N` is the set of pairs of the `N`-th reconstruction state, `O_I` is
the set of entries of its stack `λ_N`, and `S_I` is the set of `v ∈ [N]` with
`|I ∩ {v⁺, v⁻}| = 1` and `v⁺ ∈ I`. -/
@[expose, lognarayana "def_stack_reconstruction"]
public def stackReconstruction (N : ℕ) (I : Finset (Bool × ℕ)) :
    Finset (ℕ × ℕ) × Finset ℕ × Finset ℕ :=
  ((reconstructionStates I N).2, (reconstructionStates I N).1.toFinset,
    (Finset.Icc 1 N).filter fun v =>
      (I ∩ {(true, v), (false, v)}).card = 1 ∧ (true, v) ∈ I)

end

section

open Classical in
/-- The *open-matching polynomial*
`P_{par,L}(x, y, t) = ∑_{(M,O)} t^{|O|} ∏_{v ∈ R(M)} x_v y_v ∏_{v ∈ U(M) \ O} (x_v + y_v)`,
the sum over all open pairs `(M, O)` for `(par, L)` on `[N]`, with `t = X none`,
`x_v = X (some (true, v))` and `y_v = X (some (false, v))`. -/
@[expose, lognarayana "def_forest_open_poly"]
public noncomputable def forestOpenPoly (R : Type*) [CommSemiring R] (N : ℕ)
    (par : ℕ → Option ℕ) (L : Finset ℕ) : MvPolynomial (Option (Bool × ℕ)) R :=
  ∑ p ∈ (((Finset.Icc 1 N ×ˢ Finset.Icc 1 N).powerset ×ˢ (Finset.Icc 1 N).powerset).filter
      fun p : Finset (ℕ × ℕ) × Finset ℕ => IsOpenPair N par L p.1 p.2),
    MvPolynomial.X none ^ p.2.card *
      (∏ v ∈ p.1.image Prod.snd,
        MvPolynomial.X (some (true, v)) * MvPolynomial.X (some (false, v))) *
      ∏ v ∈ Finset.unmatchedVertices N p.1 \ p.2,
        (MvPolynomial.X (some (true, v)) + MvPolynomial.X (some (false, v)))

namespace Matroid

variable {α : Type*}

/-- The family `𝕋_r(M) = {I ∈ 𝕀(M) : |I| ≤ r}` of independent sets of `M` with at most `r`
elements. -/
@[expose, lognarayana "def_matroid_truncation_family"]
public def truncationFamily (M : Matroid α) (r : ℕ) : Set (Set α) :=
  {I | M.Indep I ∧ I.encard ≤ r}

end Matroid

end

section

namespace List

/-- The position relabelling `ρ_π : (s, v) ↦ (s, π_{v+1})` of a word `π`, on `Bool × ℕ`
(`true` for the `x`-copy, `false` for the `y`-copy). Positions are `1`-indexed, so `π_{v+1}` is
`π.getD v 0`. -/
@[expose, lognarayana "def_position_relabel"]
public def positionRelabelMap (π : List ℕ) (e : Bool × ℕ) : Bool × ℕ :=
  (e.1, π.getD e.2 0)

/-- The renaming of variables induced by `ρ_π`: the `R`-algebra map sending `x_v ↦ x_{π_{v+1}}`
and `y_v ↦ y_{π_{v+1}}`. -/
@[lognarayana "def_position_relabel"]
public noncomputable abbrev positionRelabel (R : Type*) [CommSemiring R] (π : List ℕ) :
    MvPolynomial (Bool × ℕ) R →ₐ[R] MvPolynomial (Bool × ℕ) R :=
  MvPolynomial.rename (positionRelabelMap π)

end List

end

section

open Polynomial in
/-- The generating series `U(z) = ∑_{q ≥ 1} N_q(x) z^q ∈ ℝ[x]⟦z⟧` of the Narayana polynomials
`narayanaPolynomial`. Its `q`-th coefficient is `N_q(x)` for `q ≥ 1`, and its constant
coefficient is `0` (`PowerSeries.coeff_mk`). -/
@[expose, lognarayana "def_narayana_gen_series"]
public noncomputable def narayanaGenSeries : PowerSeries ℝ[X] :=
  PowerSeries.mk fun q => if q = 0 then 0 else narayanaPolynomial q

namespace PowerSeries

/-- The Lagrange inversion formula (Stanley, *Enumerative Combinatorics, Vol. 2*, 1999,
Theorem 5.4.2): over a commutative ring `R`, if `φ : R[X]` and `G : R⟦X⟧` satisfy
`constantCoeff G = 0` and `G = X * φ(G)`, then for all `1 ≤ k ≤ n`,
`n * coeff n (G ^ k) = k * (φ ^ n).coeff (n - k)`. -/
@[expose, lognarayana "thm_ext_lagrange_inversion"]
public def LagrangeInversion (R : Type*) [CommRing R] : Prop :=
  ∀ (φ : Polynomial R) (G : PowerSeries R), constantCoeff G = 0 →
    G = X * Polynomial.aeval G φ →
    ∀ k n : ℕ, 1 ≤ k → k ≤ n →
      (n : R) * coeff n (G ^ k) = (k : R) * (φ ^ n).coeff (n - k)

end PowerSeries

end

section

namespace MvPolynomial

open Polynomial

/-- The *diagonal Appell transform* `𝓗 : R[z_σ] → R[t]`: the `R`-linear map sending the monomial
`z^α` to `∏ i ∈ α.support, η_{α i}(t)`, where `η_m = Polynomial.signedAppell R m`, so that
`𝓗_F(t) = ∑_{α ∈ supp F} [z^α]F · ∏_i η_{α_i}(t)`. -/
@[expose, lognarayana "def_appell_diagonal"]
public noncomputable def appellDiagonal (σ : Type*) (R : Type*) [CommRing R] :
    MvPolynomial σ R →ₗ[R] R[X] :=
  (basisMonomials σ R).constr R fun α => α.prod fun _ m => signedAppell R m

/-- The *gamma transform* `Γ : R[z_σ] → R[u]`: the `R`-linear map sending the monomial `z^α` to
`∏ i ∈ α.support, M_{α i}(u)`, where `M_m = narayanaM R m`, so that
`Γ_F(u) = ∑_{α ∈ supp F} [z^α]F · ∏_i M_{α_i}(u)`. -/
@[expose, lognarayana "def_gamma_transform"]
public noncomputable def gammaTransform (σ : Type*) (R : Type*) [CommSemiring R] :
    MvPolynomial σ R →ₗ[R] R[X] :=
  (basisMonomials σ R).constr R fun α => α.prod fun _ m => narayanaM R m

end MvPolynomial

end

section

namespace MvPolynomial

variable {σ : Type*} {R : Type*} [CommSemiring R]

/-- The polynomial `δ_t f`: the terms of `f` divisible by the variable `t`, divided by `t`.
Writing `f = ∑_h f_h t^h` with `f_h` free of `t`, `δ_t f = ∑_{h ≥ 1} f_h t^(h-1)`. -/
@[lognarayana "def_t_drop"]
public noncomputable abbrev divX (t : σ) (f : MvPolynomial σ R) : MvPolynomial σ R :=
  f.divMonomial (Finsupp.single t 1)

end MvPolynomial

end

section

@[expose] public section

/-- The marked tree `(𝒯, {1, 2})` of the root-recurrence example, on `[3]`: the first component
is the parent map with `par 1 = par 2 = some 3` and `par 3 = none` (and `none` elsewhere), the
second the marked set `{1, 2}`. -/
@[lognarayana "def_ex_root_tree"]
public def rootRecurrenceExampleTree : (ℕ → Option ℕ) × Finset ℕ :=
  (fun v => if v = 1 ∨ v = 2 then some 3 else none, {1, 2})

end

end

section

/-- The seven matchings of the running example `2135467`, with `matching2135467 i = M_{i+1}`:
`M_1 = {(1,2),(4,5)}`, `M_2 = {(1,2),(4,6)}`, `M_3 = {(1,3),(4,5)}`, `M_4 = {(1,3),(4,6)}`,
`M_5 = {(1,6),(4,5)}`, `M_6 = {(1,2),(3,6),(4,5)}`, `M_7 = {(1,6),(2,3),(4,5)}`. -/
@[expose, lognarayana "not_ex_matchings"]
public def matching2135467 : Fin 7 → Finset (ℕ × ℕ) :=
  ![{(1, 2), (4, 5)}, {(1, 2), (4, 6)}, {(1, 3), (4, 5)}, {(1, 3), (4, 6)},
    {(1, 6), (4, 5)}, {(1, 2), (3, 6), (4, 5)}, {(1, 6), (2, 3), (4, 5)}]

end
