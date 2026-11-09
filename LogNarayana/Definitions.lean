/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib

/-!
# Definitions of the formal challenge

The definitions that the statements of `Challenge/Basic.lean` mention, repeated here verbatim and
in the same order, so that the library and the challenge elaborate them to the same constants.
Every other file of the library takes them from this one.
-/

section

namespace Polynomial

section signedAppell

variable (R : Type*) [Ring R]

/-- The *signed Appell polynomial* `η_m(t) = ∑_{j=0}^{⌊m/2⌋} (-1)^j C_j (m choose 2j) t^(m-2j)`,
where `C_j` is the `j`-th Catalan number. -/
@[expose]
public noncomputable def signedAppell (m : ℕ) : R[X] :=
  ∑ j ∈ Finset.range (m / 2 + 1),
    C ((-1) ^ j * (catalan j : R) * (m.choose (2 * j) : R)) * X ^ (m - 2 * j)

end signedAppell

end Polynomial

end

section

open Polynomial Finset

/-- The Narayana polynomial `N_q(x)`: equal to `1` for `q = 0`, and for `q ≥ 1` to `∑_{j=1}^{q}
q⁻¹ * (q choose j) * (q choose (j-1)) * x^j`. -/
@[expose]
public noncomputable def narayanaPolynomial (q : ℕ) : ℝ[X] :=
  if q = 0 then 1 else
    ∑ j ∈ Icc 1 q, C ((q : ℝ)⁻¹ * (q.choose j : ℝ) * (q.choose (j - 1) : ℝ)) * X ^ j

/-- The product of Narayana polynomials over a tuple: for `q : I → ℕ` with `I` finite,
`narayanaTupleProd q = ∏ i, N_{q i}(x)`. -/
public noncomputable abbrev narayanaTupleProd {I : Type*} [Fintype I] (q : I → ℕ) : ℝ[X] :=
  ∏ i, narayanaPolynomial (q i)

/-- The shifted Narayana polynomial
`Ñ_m(x) = ∑_{j=0}^{m} (m+1)⁻¹ * (m+1 choose j+1) * (m+1 choose j) * x^j`. -/
@[expose]
public noncomputable def shiftedNarayanaPolynomial (m : ℕ) : ℝ[X] :=
  ∑ j ∈ range (m + 1),
    C (((m + 1 : ℕ) : ℝ)⁻¹ * ((m + 1).choose (j + 1) : ℝ) * ((m + 1).choose j : ℝ)) * X ^ j

/-- The polynomial `Q_m(A, B) = ∑_{j=0}^{⌊m/2⌋} C_j (m choose 2j) B^j A^(m - 2j)` in the two
indeterminates `A = X 0` and `B = X 1`, with `C_j = catalan j`. For `F, G` in a commutative
`R`-algebra, `Q_m(F, G)` is `MvPolynomial.aeval ![F, G] (narayanaQ R m)`. -/
@[expose]
public noncomputable def narayanaQ (R : Type*) [CommSemiring R] (m : ℕ) :
    MvPolynomial (Fin 2) R :=
  ∑ j ∈ range (m / 2 + 1),
    MvPolynomial.C ((catalan j : R) * (m.choose (2 * j) : R)) *
      MvPolynomial.X 1 ^ j * MvPolynomial.X 0 ^ (m - 2 * j)

end

section

namespace List

variable {α : Type*} [LT α] [DecidableRel (α := α) (· < ·)]

/-- The *descent set* of a list `σ = σ₁ ⋯ σ_ℓ`: the `1`-based positions `i ∈ [ℓ - 1]` with `σᵢ >
σᵢ₊₁`. In `0`-based indexing, `i` is a descent iff `1 ≤ i < ℓ` and `σ[i] < σ[i - 1]`. -/
@[expose]
public def descentSet (σ : List α) : Finset ℕ :=
  {i ∈ Finset.Ico 1 σ.length |
    ∃ h : i < σ.length, σ[i] < σ[i - 1]'(Nat.lt_of_le_of_lt (Nat.sub_le i 1) h)}

/-- The *number of descents* `des(σ) = |Des(σ)|` of a list `σ`: the cardinality of its descent set
`List.descentSet σ`. -/
public abbrev numDescents (σ : List α) : ℕ :=
  σ.descentSet.card

/-- The *peak count* `peak(σ)` of a list `σ = σ₁ ⋯ σ_ℓ`: the number of `1`-based indices `i ∈ [2,
ℓ - 1]` with `σᵢ₋₁ < σᵢ` and `σᵢ > σᵢ₊₁`. -/
@[expose]
public def peakCount (σ : List α) : ℕ :=
  ({i ∈ Finset.Ico 2 σ.length |
    ∃ h : i < σ.length, σ[i - 2]'(Nat.lt_of_le_of_lt (Nat.sub_le i 2) h) <
      σ[i - 1]'(Nat.lt_of_le_of_lt (Nat.sub_le i 1) h) ∧
      σ[i] < σ[i - 1]'(Nat.lt_of_le_of_lt (Nat.sub_le i 1) h)} : Finset ℕ).card

variable [DecidableEq α]

/-- The set of *descent tops* `DT(σ)` of a list `σ = σ₁ ⋯ σ_ℓ`: the entries `σᵢ`, `i ∈ [ℓ - 1]`,
with `σᵢ > σᵢ₊₁`. -/
@[expose]
public def descentTops (σ : List α) : Finset α :=
  (((σ.zip σ.tail).filter fun p => p.2 < p.1).map Prod.fst).toFinset

/-- The set of *ascent tops* `AT(σ)` of a list `σ = σ₁ ⋯ σ_ℓ`: the entries `σᵢ₊₁`, `i ∈ [ℓ - 1]`,
with `σᵢ < σᵢ₊₁`. -/
@[expose]
public def ascentTops (σ : List α) : Finset α :=
  (((σ.zip σ.tail).filter fun p => p.1 < p.2).map Prod.snd).toFinset

end List

end

section

/-- A list of natural numbers is a *word* if its entries are pairwise distinct positive integers. -/
@[expose]
public def IsWord (σ : List ℕ) : Prop :=
  σ.Nodup ∧ ∀ a ∈ σ, 0 < a

/-- The set `𝒲` of all words. -/
@[expose]
public def words : Set (List ℕ) :=
  {σ | IsWord σ}

/-- The *set of letters* `Let(u)` of a finite sequence `u`: the finite set of its entries. -/
public abbrev List.letters {α : Type*} [DecidableEq α] (u : List α) : Finset α :=
  u.toFinset

/-- The set `S_n` of permutations of `[n]` in one-line notation: the words of length `n` whose set
of letters is `[n] = {1, …, n}`. -/
@[expose]
public def permWords (n : ℕ) : Set (List ℕ) :=
  {σ | σ ∈ words ∧ σ.length = n ∧ σ.letters = Finset.Icc 1 n}

/-- The identity permutation `ι_n = 1 2 ⋯ n`, as a word. -/
@[expose]
public def idPermWord (n : ℕ) : List ℕ :=
  List.range' 1 n

namespace List

variable {α : Type*} [LinearOrder α]

/-- West's *stack-sorting map*: `stackSort [] = []`, and for nonempty `σ = L m R`, where `m` is
the maximum of `σ` (split at its first occurrence), `stackSort σ = stackSort L ++ stackSort R ++
[m]`. -/
@[expose]
public def stackSort : List α → List α
  | [] => []
  | a :: l =>
    let m := l.foldr max a
    let p := (a :: l).idxOf m
    stackSort ((a :: l).take p) ++ stackSort ((a :: l).drop (p + 1)) ++ [m]
termination_by σ => σ.length
decreasing_by
  all_goals
    simp only [List.foldr_attach]
    have hm : l.foldr max a ∈ a :: l := by
      induction l with
      | nil => simp
      | cons b l ih =>
        simp only [foldr_cons, mem_cons] at ih ⊢
        rcases max_choice b (l.foldr max a) with h | h <;> rw [h]
        · simp
        · rcases ih with h' | h' <;> simp [h']
    have := List.idxOf_lt_length_of_mem hm
    simp only [length_take, length_drop, length_cons] at this ⊢
    omega

/-- The *stack-sorting fiber* `s⁻¹(π) = {σ ∈ S_n : s(σ) = π}` of `π`, where `n = π.length`: the
permutations `σ` of `[n]` (in one-line notation) with `σ.stackSort = π`. -/
@[expose]
public def stackFiber (π : List ℕ) : Finset (List ℕ) :=
  (idPermWord π.length).permutations.toFinset.filter fun σ ↦ σ.stackSort = π

end List

end

section

namespace List

open Polynomial in
/-- The *fiber descent polynomial* `D_π(x) = ∑_{σ ∈ s⁻¹(π)} x^{des(σ)}` of `π`, with coefficients
in a semiring `R`. -/
@[expose]
public noncomputable def fiberDescentPolynomial (R : Type*) [Semiring R] (π : List ℕ) : R[X] :=
  ∑ σ ∈ stackFiber π, X ^ σ.numDescents

open MvPolynomial

/-- The *homogeneous fiber polynomial* `H_π(x, y) = ∑_{σ ∈ s⁻¹(π)} x^{des(σ)} y^{n - 1 - des(σ)}`
of `π`, where `n = π.length`, `x = X 0` and `y = X 1`, with coefficients in a commutative semiring
`R`. -/
@[expose]
public noncomputable def fiberHomogPolynomial (R : Type*) [CommSemiring R] (π : List ℕ) :
    MvPolynomial (Fin 2) R :=
  ∑ σ ∈ stackFiber π, X 0 ^ σ.numDescents * X 1 ^ (π.length - 1 - σ.numDescents)

/-- The *peak-weighted homogeneous fiber polynomial* `H^λ_π(x, y) = ∑_{σ ∈ s⁻¹(π)} λ^{peak(σ)}
x^{des(σ)} y^{n - 1 - des(σ)}` of `π`, where `n = π.length`, `x = X 0` and `y = X 1`, with the
weight `lam = λ` and the coefficients in a commutative semiring `R`. -/
@[expose]
public noncomputable def fiberPeakPolynomial (R : Type*) [CommSemiring R] (lam : R)
    (π : List ℕ) : MvPolynomial (Fin 2) R :=
  ∑ σ ∈ stackFiber π,
    C (lam ^ σ.peakCount) * X 0 ^ σ.numDescents * X 1 ^ (π.length - 1 - σ.numDescents)

/-- The *fiber top polynomial* `𝒟_π(x, y) = ∑_{σ ∈ s⁻¹(π)} ∏_{a ∈ DT(σ)} x_a ∏_{b ∈ AT(σ)} y_b` of
`π`, with coefficients in a commutative semiring `R`, where `x_a = X (true, a)` and `y_a = X
(false, a)`. -/
@[expose]
public noncomputable def fiberTopPolynomial (R : Type*) [CommSemiring R] (π : List ℕ) :
    MvPolynomial (Bool × ℕ) R :=
  ∑ σ ∈ stackFiber π,
    (∏ a ∈ σ.descentTops, X (true, a)) * ∏ b ∈ σ.ascentTops, X (false, b)

end List

end

section

universe u

open Polynomial

/-- **Negative real zeros of the shifted Narayana polynomials** (L. L. Liu and Y. Wang, *A unified
approach to polynomial sequences with only real zeros*, 2007, Section 3.4, Proposition 3.2): for
every `m`, the polynomial `shiftedNarayanaPolynomial m` has exactly `m` distinct negative real
zeros. The count is `Set.encard`, which also records finiteness. -/
@[expose]
public def ShiftedNarayanaNegRealRoots : Prop :=
  ∀ m : ℕ, {ρ : ℝ | ρ < 0 ∧ (shiftedNarayanaPolynomial m).IsRoot ρ}.encard = m

/-- **Interlacing of the shifted Narayana polynomials** (L. L. Liu and Y. Wang, *A unified
approach to polynomial sequences with only real zeros*, 2007, Section 3.4): if `ρ : Fin m → ℝ` and
`θ : Fin (m + 1) → ℝ` are strictly increasing families of zeros of `shiftedNarayanaPolynomial m`
and `shiftedNarayanaPolynomial (m + 1)` respectively, then `θ i.castSucc < ρ i < θ i.succ` for
every `i : Fin m`. -/
@[expose]
public def ShiftedNarayanaInterlacing : Prop :=
  ∀ (m : ℕ) (ρ : Fin m → ℝ) (θ : Fin (m + 1) → ℝ), StrictMono ρ → StrictMono θ →
    (∀ i, (shiftedNarayanaPolynomial m).IsRoot (ρ i)) →
    (∀ i, (shiftedNarayanaPolynomial (m + 1)).IsRoot (θ i)) →
    ∀ i : Fin m, θ i.castSucc < ρ i ∧ ρ i < θ i.succ

end

section

@[expose] public section

namespace BinaryTree

variable {α : Type*}

/-- The *inorder reading* of a binary plane tree: the labels of the left subtree in inorder, then
the root label, then the labels of the right subtree in inorder. -/
def inorder : BinaryTree α → List α
  | nil => []
  | node m l r => inorder l ++ m :: inorder r

/-- The *postorder reading* of a binary plane tree: `postorder nil = []` and
`postorder (node m l r) = postorder l ++ postorder r ++ [m]`. -/
@[simp]
def postorder : BinaryTree α → List α
  | nil => []
  | node m l r => postorder l ++ postorder r ++ [m]

variable [DecidableEq α]

/-- The label set `Lab(T)` of a binary plane tree: `Lab(∅) = ∅` and `Lab(⟨m; T_L, T_R⟩) = {m} ∪
Lab(T_L) ∪ Lab(T_R)`. -/
@[simp]
def labels : BinaryTree α → Finset α
  | nil => ∅
  | node m l r => {m} ∪ labels l ∪ labels r

/-- The set `RC(T)` of labels of vertices of `T` having a right child: `RC(∅) = ∅` and `RC(⟨m;
T_L, T_R⟩) = RC(T_L) ∪ RC(T_R) ∪ {m}` if `T_R ≠ ∅`, and `RC(T_L) ∪ RC(T_R)` otherwise. -/
@[simp]
def rightChildLabels : BinaryTree α → Finset α
  | nil => ∅
  | node m l r =>
      rightChildLabels l ∪ rightChildLabels r ∪
        match r with
        | nil => ∅
        | node _ _ _ => {m}

variable [LT α]

/-- A binary plane tree is *decreasing* (`dec`) if its labels are pairwise distinct and every
vertex has a larger label than every vertex below it: `dec(∅)` holds, and `dec(⟨m; T_L, T_R⟩)`
holds iff `dec(T_L)`, `dec(T_R)`, `Lab(T_L) ∩ Lab(T_R) = ∅`, and `a < m` for all `a ∈ Lab(T_L) ∪
Lab(T_R)`. -/
@[simp]
def IsDecreasing : BinaryTree α → Prop
  | nil => True
  | node m l r => l.IsDecreasing ∧ r.IsDecreasing ∧ Disjoint l.labels r.labels ∧
      ∀ a ∈ l.labels ∪ r.labels, a < m

/-- The set `DBT(A)` of decreasing binary plane trees on the finite set `A`: the decreasing trees
whose label set is exactly `A`. -/
def decreasingTrees (A : Finset α) : Set (BinaryTree α) :=
  {T | T.IsDecreasing ∧ T.labels = A}

end BinaryTree

end

end

section

@[expose] public section

namespace BinaryTree

/-- A type of colors `C` with two distinguished distinct colors, `black` and `white`. -/
public class TreeColors (C : Type*) where
  /-- The color `black`: that of a new vertex created by insertion, and of every vertex of a
  binary plane tree regarded as a colored one. -/
  black : C
  /-- The color `white`. -/
  white : C
  /-- The two distinguished colors are distinct. -/
  black_ne_white : black ≠ white

/-- The four-element set `𝔗 = {leaf, lu, ru, bin}` of types of vertices of a binary plane tree. -/
public inductive VertexType
  /-- `leaf`: a vertex with no child. -/
  | leaf
  /-- `lu` (left-unary): a vertex with a left child and no right child. -/
  | leftUnary
  /-- `ru` (right-unary): a vertex with a right child and no left child. -/
  | rightUnary
  /-- `bin` (binary): a vertex with both a left and a right child. -/
  | binary
  deriving DecidableEq, Inhabited, Repr

section VertexTypes

variable {α : Type*}

/-- The type `type_T(v)` of a vertex `v = node a l r` of a binary plane tree, as a function of its
left subtree `l` and right subtree `r`: `leaf` if both are empty, `lu` if only `l` is nonempty,
`ru` if only `r` is nonempty, and `bin` if both are nonempty. -/
@[simp]
public def vertexType : BinaryTree α → BinaryTree α → VertexType
  | nil, nil => .leaf
  | node _ _ _, nil => .leftUnary
  | nil, node _ _ _ => .rightUnary
  | node _ _ _, node _ _ _ => .binary

end VertexTypes

section ColorCounts

variable {C : Type*} [TreeColors C] [DecidableEq C]

/-- The number `black(T)` of vertices of the colored binary plane tree `T` whose color is
`TreeColors.black`: `black(∅) = 0` and `black(⟨c; T_L, T_R⟩) = black(T_L) + black(T_R) + (if c =
black then 1 else 0)`. -/
@[simp]
public def numBlackNodes : BinaryTree C → ℕ
  | nil => 0
  | node c l r => numBlackNodes l + numBlackNodes r + if c = TreeColors.black then 1 else 0

/-- The number `white(T)` of vertices of the colored binary plane tree `T` whose color is
`TreeColors.white`: `white(∅) = 0` and `white(⟨c; T_L, T_R⟩) = white(T_L) + white(T_R) + (if c =
white then 1 else 0)`. -/
@[simp]
public def numWhiteNodes : BinaryTree C → ℕ
  | nil => 0
  | node c l r => numWhiteNodes l + numWhiteNodes r + if c = TreeColors.white then 1 else 0

end ColorCounts

end BinaryTree

end

end

section

@[expose] public section

namespace BinaryTree

/-- The family `𝐔_P` of colored binary plane trees cut out by the local rule `P ⊆ 𝔗 × C`: the
trees `T` such that `(type_T(v), χ(v)) ∈ P` for every vertex `v` of `T`, where `χ(v)` is the color
(label) of `v`. The empty tree belongs to every such family. -/
def localRuleFamily {C : Type*} (P : Set (VertexType × C)) : Set (BinaryTree C)
  | nil => True
  | node a l r => (vertexType l r, a) ∈ P ∧ localRuleFamily P l ∧ localRuleFamily P r

/-- The family `𝐔_{X_L,X_a,X_b}` of colored binary plane trees in which each leaf has a color in
`X_L`, each unary vertex with a left child a color in `X_a`, each unary vertex with a right child
a color in `X_b`, and each binary vertex is black: the family cut out by the local rule `({leaf} ×
X_L) ∪ ({lu} × X_a) ∪ ({ru} × X_b) ∪ {(bin, black)}`. -/
def localColorFamily {C : Type*} [TreeColors C] (X_L X_a X_b : Set C) : Set (BinaryTree C) :=
  localRuleFamily (({VertexType.leaf} ×ˢ X_L) ∪ ({VertexType.leftUnary} ×ˢ X_a) ∪
    ({VertexType.rightUnary} ×ˢ X_b) ∪ {(VertexType.binary, TreeColors.black)})

/-- The set `𝐒 = 𝐔_P` of *Schröder two-colored binary trees*, for the local rule `P = (𝔗 ×
{black}) ∪ {(leaf, white), (ru, white)}`: the colored binary plane trees all of whose vertices are
`black` or `white`, every vertex with a left child being `black`. -/
def schroederTrees (C : Type*) [TreeColors C] : Set (BinaryTree C) :=
  localRuleFamily ((Set.univ ×ˢ {TreeColors.black}) ∪
    {(.leaf, TreeColors.white), (.rightUnary, TreeColors.white)})

end BinaryTree

end

end

section

namespace Finsupp

variable {σ : Type*}

/-- The factorial of a multi-index: `α.factorial = ∏ i, (α i)!`, the product taken over the
support of `α` (the other factors are `0! = 1`). -/
@[expose]
public def factorial (α : σ →₀ ℕ) : ℕ :=
  α.prod fun _ n => n.factorial

/-- The binomial coefficient of multi-indices: `κ.choose α = ∏ i, (κ i).choose (α i)`, the product
taken over the support of `α` (the other factors are `(κ i).choose 0 = 1`). It vanishes unless `α
≤ κ`. -/
@[expose]
public def choose (κ α : σ →₀ ℕ) : ℕ :=
  α.prod fun i a => (κ i).choose a

end Finsupp

namespace MvPolynomial

variable {σ R : Type*} [CommSemiring R]

/-- The iterated partial derivative `∂^α` of multivariate polynomials, for a multi-index
`α : σ →₀ ℕ`: the `R`-linear map sending the monomial `z^β` to `(β! / (β - α)!) • z^(β - α)` if
`α ≤ β`, and to `0` otherwise. -/
@[expose]
public noncomputable def iteratedPDeriv (α : σ →₀ ℕ) : MvPolynomial σ R →ₗ[R] MvPolynomial σ R :=
  (basisMonomials σ R).constr ℕ fun β =>
    monomial (β - α) (if α ≤ β then ((β.factorial / (β - α).factorial : ℕ) : R) else 0)

end MvPolynomial

end

section

namespace MvPolynomial

variable (σ : Type*) (R : Type*) [CommSemiring R] [Algebra ℚ R]

/-- The simplex integration operator `𝔍_m`: the `R`-linear map from polynomials in `x_j = X
(Sum.inl j)` and `u_i = X (Sum.inr i)` to polynomials in `x_j = X (some j)` and `t = X none`,
sending the monomial `x^α u^γ` to `(γ! / (|γ| + m - 1)!) • x^α t^(|γ| + m - 1)`. -/
@[expose]
public noncomputable def simplexIntegral (m : ℕ) :
    MvPolynomial (σ ⊕ Fin m) R →ₗ[R] MvPolynomial (Option σ) R :=
  (basisMonomials (σ ⊕ Fin m) R).constr R fun β =>
    monomial
      (Finsupp.single none ((Finsupp.sumFinsuppEquivProdFinsupp β).2.degree + m - 1) +
        (Finsupp.sumFinsuppEquivProdFinsupp β).1.mapDomain some)
      (algebraMap ℚ R
        (((Finsupp.sumFinsuppEquivProdFinsupp β).2.factorial : ℚ) /
          (((Finsupp.sumFinsuppEquivProdFinsupp β).2.degree + m - 1).factorial : ℚ)))

end MvPolynomial

end

section

namespace MvPolynomial

variable {σ : Type*} {R : Type*} [CommSemiring R] [Algebra ℚ R]

/-- The convolution in `t` of `F G ∈ R[x, t]`: `𝔍_2 (F(x, u_1) G(x, u_2))`, where `F(x, u_i)`
renames `t = X none` to `u_i = X (Sum.inr i)` and `x_j = X (some j)` to `X (Sum.inl j)`. -/
@[expose]
public noncomputable def tConvolution (F G : MvPolynomial (Option σ) R) :
    MvPolynomial (Option σ) R :=
  simplexIntegral σ R 2
    (rename (fun o : Option σ => o.elim (Sum.inr 0) Sum.inl) F *
      rename (fun o : Option σ => o.elim (Sum.inr 1) Sum.inl) G)

end MvPolynomial

end

section

namespace Set

variable {σ : Type*}

/-- A set `J` of multi-indices is *M-convex* if it is finite, nonempty, homogeneous of some degree
`D`, and has the symmetric exchange property: for `α, β ∈ J` and `i` with `β i < α i` there is `j`
with `α j < β j` such that `α - e_i + e_j ∈ J` and `β - e_j + e_i ∈ J`. -/
@[expose]
public def IsMConvex (J : Set (σ →₀ ℕ)) : Prop :=
  J.Finite ∧ J.Nonempty ∧ (∃ D : ℕ, ∀ α ∈ J, α.degree = D) ∧
    ∀ α ∈ J, ∀ β ∈ J, ∀ i : σ, β i < α i →
      ∃ j : σ, α j < β j ∧
        α - Finsupp.single i 1 + Finsupp.single j 1 ∈ J ∧
        β - Finsupp.single j 1 + Finsupp.single i 1 ∈ J

end Set

namespace MvPolynomial

variable {σ : Type*} {R : Type*} [CommSemiring R] [LE R]

/-- A multivariate polynomial `f` has *nonnegative coefficients* if `0 ≤ f.coeff α` for every
exponent vector `α`. -/
@[expose]
public def HasNonnegCoeffs (f : MvPolynomial σ R) : Prop :=
  ∀ α : σ →₀ ℕ, 0 ≤ f.coeff α

end MvPolynomial

end

section

namespace Matrix

variable {σ R : Type*} [Fintype σ] [CommRing R] [PartialOrder R]

/-- A submodule `W ⊆ σ → R` is `A`-positive if `vᵀ A v > 0` for every nonzero `v ∈ W`. -/
@[expose] public def IsPositiveSubspace
    (A : Matrix σ σ R) (W : Submodule R (σ → R)) : Prop :=
  ∀ v ∈ W, v ≠ 0 → 0 < v ⬝ᵥ (A *ᵥ v)

/-- The positive index `p(A)` of a square matrix `A`: the supremum in `ℕ` of the dimensions of the
`A`-positive subspaces `W ⊆ σ → R`. -/
@[expose] public noncomputable def posIndex
    (A : Matrix σ σ R) : ℕ :=
  sSup {n | ∃ W : Submodule R (σ → R), A.IsPositiveSubspace W ∧ Module.finrank R W = n}

/-- A square matrix `A` *has at most one positive eigenvalue* if its positive index
`Matrix.posIndex A` is at most `1`. For a real symmetric matrix this says that at most one
eigenvalue, counted with multiplicity, is positive. -/
public abbrev HasAtMostOnePosEigenvalue
    (A : Matrix σ σ R) : Prop :=
  A.posIndex ≤ 1

end Matrix

end

section

namespace MvPolynomial

section Hessian

variable {σ R : Type*} [CommSemiring R]

/-- The *Hessian at the origin* `Hess(g)` of a multivariate polynomial `g`: the matrix whose `(i,
j)` entry is the constant coefficient of `∂^(e_i + e_j) g`, i.e. the second partial derivative
`∂²g / ∂z_i ∂z_j` evaluated at `0`. -/
@[expose]
public noncomputable def hessianAtZero (g : MvPolynomial σ R) : Matrix σ σ R :=
  Matrix.of fun i j =>
    constantCoeff (iteratedPDeriv (Finsupp.single i 1 + Finsupp.single j 1) g)

end Hessian

section Lorentzian

variable {σ R : Type*} [Fintype σ] [CommRing R] [PartialOrder R]

/-- A multivariate polynomial `f` is *Lorentzian* if `f = 0`, or there is `d` such that `f` is
homogeneous of degree `d` with nonnegative coefficients, and either `d ≤ 1`, or `2 ≤ d`, the support
of `f` is M-convex, and for every multi-index `α` with `|α| = d - 2` the Hessian of `∂^α f` has at
most one positive eigenvalue. -/
@[expose]
public def IsLorentzian (f : MvPolynomial σ R) : Prop :=
  f = 0 ∨ ∃ d : ℕ, f.IsHomogeneous d ∧ f.HasNonnegCoeffs ∧
    (d ≤ 1 ∨ (2 ≤ d ∧ (f.support : Set (σ →₀ ℕ)).IsMConvex ∧
      ∀ α : σ →₀ ℕ, α.degree = d - 2 →
        (hessianAtZero (iteratedPDeriv α f)).HasAtMostOnePosEigenvalue))

end Lorentzian

end MvPolynomial

end

section

@[expose] public section

namespace MvPolynomial

section BoundedDegree

variable {R σ τ : Type*} [CommSemiring R]

/-- A linear operator `T : R_κ[z_i : i ∈ σ] → R[x_j : j ∈ τ]` on the polynomials of degree at most
`κ i` in each variable `z i` is *homogeneous of degree `ℓ`* if for every `α ≤ κ` with `T (z ^ α) ≠
0`, the integer `|α| + ℓ` is nonnegative and `T (z ^ α)` is homogeneous of degree `|α| + ℓ`. -/
def IsHomogeneousOperator (κ : σ →₀ ℕ) (ℓ : ℤ)
    (T : restrictSupport R (Set.Iic κ) →ₗ[R] MvPolynomial τ R) : Prop :=
  ∀ α : σ →₀ ℕ, α ≤ κ → ∀ f : restrictSupport R (Set.Iic κ),
    (f : MvPolynomial σ R) = monomial α 1 → T f ≠ 0 →
      ∃ n : ℕ, (n : ℤ) = (α.degree : ℤ) + ℓ ∧ (T f).IsHomogeneous n

open scoped Classical in
/-- The *algebraic symbol* of a linear map `T : R_κ[z_i : i ∈ σ] → R[x_j : j ∈ τ]`:
`Sym_κ(T)(x, w) = ∑_{α ≤ κ} (κ choose α) T(z ^ α) w ^ (κ - α)`, a polynomial in the variables
`x_j = X (Sum.inl j)` and `w_i = X (Sum.inr i)`. -/
noncomputable def algebraicSymbol (κ : σ →₀ ℕ)
    (T : restrictSupport R (Set.Iic κ) →ₗ[R] MvPolynomial τ R) : MvPolynomial (τ ⊕ σ) R :=
  ∑ α ∈ (Finset.Iic κ).attach,
    C (κ.choose α : R) *
      rename Sum.inl
        (T ⟨monomial (α : σ →₀ ℕ) 1,
          (monomial_mem_restrictSupport R).2 (Or.inl (Finset.mem_Iic.1 α.2))⟩) *
      rename Sum.inr (monomial (κ - (α : σ →₀ ℕ)) 1)

end BoundedDegree

section Rational

variable (σ : Type*) (R : Type*) [CommSemiring R] [Algebra ℚ R]

variable {σ}

/-- The normalized support polynomial `E_J(z) = ∑_{α ∈ J} z^α / α!` of a finite set `J` of
multi-indices. -/
noncomputable def normalizedSupportPoly (J : Finset (σ →₀ ℕ)) : MvPolynomial σ R :=
  ∑ α ∈ J, monomial α (algebraMap ℚ R (1 / (α.factorial : ℚ)))

variable {R}

/-- The antiderivative `∫₀ᵗ F ds` with respect to the variable `t`: the `R`-linear map on
`MvPolynomial σ R` sending each monomial `z^α` to `z^(α + e_t) / (α_t + 1)`. -/
noncomputable def antiderivative (t : σ) : MvPolynomial σ R →ₗ[R] MvPolynomial σ R :=
  (basisMonomials σ R).constr R fun α =>
    monomial (α + Finsupp.single t 1) (algebraMap ℚ R (1 / ((α t : ℚ) + 1)))

end Rational

end MvPolynomial

end

end

section

@[expose] public section

namespace MvPolynomial

/-- The symbol theorem of Brändén–Huh [BH, Theorem 3.2]: for `κ : σ →₀ ℕ`, `ℓ : ℤ` and a linear
operator `T : ℝ_κ[z_i : i ∈ σ] → ℝ[x_j : j ∈ τ]` that is homogeneous of degree `ℓ`, if the
algebraic symbol `MvPolynomial.algebraicSymbol κ T` is Lorentzian, then `T f` is Lorentzian for
every Lorentzian `f ∈ ℝ_κ[z]`. -/
def BrandenHuhSymbolTheorem (σ τ : Type*) [Fintype σ] [Fintype τ] : Prop :=
  ∀ (κ : σ →₀ ℕ) (ℓ : ℤ) (T : restrictSupport ℝ (Set.Iic κ) →ₗ[ℝ] MvPolynomial τ ℝ),
    IsHomogeneousOperator κ ℓ T → (algebraicSymbol κ T).IsLorentzian →
      ∀ f : restrictSupport ℝ (Set.Iic κ), (f : MvPolynomial σ ℝ).IsLorentzian →
        (T f).IsLorentzian

/-- **Brändén–Huh** [BH, Theorem 3.10]: for a finite variable type `σ` and an M-convex set `J` of
multi-indices, the normalized support polynomial `E_J = ∑_{α ∈ J} z^α / α!` in `ℝ[z_i : i ∈ σ]` is
Lorentzian. -/
def NormalizedSupportPolyLorentzianOfMConvex (σ : Type*) [Fintype σ] : Prop :=
  ∀ J : Finset (σ →₀ ℕ), (J : Set (σ →₀ ℕ)).IsMConvex →
    (normalizedSupportPoly ℝ J).IsLorentzian

end MvPolynomial

end

end

section

namespace MvPolynomial

open Filter Topology

@[expose] public section

/-- **Brändén–Huh** [BH, Theorem 2.25]: for a finite variable type `σ` and `d : ℕ`, the set of
Lorentzian polynomials in the space `H^d_σ` of homogeneous polynomials of degree `d` in `ℝ[z_i : i
∈ σ]` is closed in `H^d_σ`: if `f_k ∈ H^d_σ` are Lorentzian and converge coefficientwise to `f ∈
H^d_σ`, then `f` is Lorentzian. -/
def IsLorentzianClosed (σ : Type*) [Fintype σ] : Prop :=
  ∀ (d : ℕ) (F : ℕ → MvPolynomial σ ℝ) (f : MvPolynomial σ ℝ),
    (∀ k, (F k).IsLorentzian ∧ (F k).IsHomogeneous d) → f.IsHomogeneous d →
    (∀ α : σ →₀ ℕ, Tendsto (fun k ↦ (F k).coeff α) atTop (𝓝 (f.coeff α))) →
    f.IsLorentzian

/-- **Brändén–Huh** [BH, Theorem 2.10]: for finite variable types `σ` and `τ`, a nonnegative real
matrix `a : σ → τ → ℝ` and a Lorentzian polynomial `f ∈ ℝ[z_i : i ∈ σ]`, the polynomial
`f(∑_j a_{ij} v_j)_{i ∈ σ} ∈ ℝ[v_j : j ∈ τ]` is Lorentzian. -/
def LorentzianNonnegLinearSubstitution (σ τ : Type*) [Fintype σ] [Fintype τ] : Prop :=
  ∀ (a : σ → τ → ℝ), (∀ i j, 0 ≤ a i j) → ∀ f : MvPolynomial σ ℝ, f.IsLorentzian →
    (aeval (fun i ↦ ∑ j, a i j • (X j : MvPolynomial τ ℝ)) f).IsLorentzian

/-- **Brändén–Huh** [BH, Corollary 2.11]: for a finite variable type `σ`, a nonnegative vector `a
: σ → ℝ` and a Lorentzian polynomial `f ∈ ℝ[z_i : i ∈ σ]`, the polynomial `∑_i a_i ∂_i f` is
Lorentzian. -/
def LorentzianNonnegDerivative (σ : Type*) [Fintype σ] : Prop :=
  ∀ (a : σ → ℝ), (∀ i, 0 ≤ a i) → ∀ f : MvPolynomial σ ℝ, f.IsLorentzian →
    (∑ i, a i • pderiv i f).IsLorentzian

/-- **Brändén–Huh** [BH, Theorem 2.30 and Corollary 2.32]: for a finite variable type `σ`, the
product of two Lorentzian polynomials in `ℝ[z_i : i ∈ σ]` is Lorentzian. -/
def LorentzianMul (σ : Type*) [Fintype σ] : Prop :=
  ∀ f g : MvPolynomial σ ℝ, f.IsLorentzian → g.IsLorentzian → (f * g).IsLorentzian

end

end MvPolynomial

end

section

namespace List

/-- The *hooks* of a list `σ = σ₁ ⋯ σ_ℓ`: the pairs `(i, j)` of `1`-based positions with `1 ≤ i <
j ≤ ℓ` and `σᵢ < σⱼ`. The index `i` is the southwest endpoint `(i, σᵢ)` of the hook and `j` its
northeast endpoint `(j, σⱼ)`. -/
@[expose]
public def hooks {α : Type*} [LT α] [DecidableRel (α := α) (· < ·)] (σ : List α) :
    Finset (ℕ × ℕ) :=
  {p ∈ Finset.Icc 1 σ.length ×ˢ Finset.Icc 1 σ.length |
    p.1 < p.2 ∧ ∃ (h₁ : p.1 - 1 < σ.length) (h₂ : p.2 - 1 < σ.length), σ[p.1 - 1] < σ[p.2 - 1]}

/-- The *region* `Γ_σ(i, j) ⊆ ℝ²` of the pair `p = (i, j)` of `1`-based positions of `σ`: the
closed vertical segment from `(i, σᵢ)` to `(i, σⱼ)` together with the closed horizontal segment
from `(i, σⱼ)` to `(j, σⱼ)`. When `p ∈ σ.hooks` this is the hook drawn on the plot of `σ`. -/
@[expose]
public def hookRegion (σ : List ℕ) (p : ℕ × ℕ) : Set (ℝ × ℝ) :=
  segment ℝ ((p.1 : ℝ), (σ.getD (p.1 - 1) 0 : ℝ)) ((p.1 : ℝ), (σ.getD (p.2 - 1) 0 : ℝ)) ∪
    segment ℝ ((p.1 : ℝ), (σ.getD (p.2 - 1) 0 : ℝ)) ((p.2 : ℝ), (σ.getD (p.2 - 1) 0 : ℝ))

/-- The finite set `VHC(π)` of *valid hook configurations* of a word `π`: the sets `𝓗` of hooks of
`π` such that (V1) `|𝓗| = des(π)` and the southwest endpoints of `𝓗` are exactly `Des(π)`; (V2)
for every `(i, j) ∈ 𝓗` and `i ≤ k ≤ j`, `πₖ ≤ πⱼ`; (V3) any two distinct hooks of `𝓗` whose
regions intersect satisfy `j = i'` or `j' = i`. -/
@[expose]
public noncomputable def validHookConfigurations (π : List ℕ) : Finset (Finset (ℕ × ℕ)) :=
  open Classical in
  π.hooks.powerset.filter fun 𝓗 =>
    (𝓗.card = π.numDescents ∧ 𝓗.image Prod.fst = π.descentSet) ∧
    (∀ p ∈ 𝓗, ∀ k ∈ Finset.Icc p.1 p.2, π.getD (k - 1) 0 ≤ π.getD (p.2 - 1) 0) ∧
    (∀ p ∈ 𝓗, ∀ q ∈ 𝓗, p ≠ q → (π.hookRegion p ∩ π.hookRegion q).Nonempty →
      p.2 = q.1 ∨ q.2 = p.1)

/-- The composition `𝐪_𝓗 = (q₀, q₁, …, q_k)` induced by a set `𝓗` of hooks of `π`, where `k =
des(π)` and `d₁ < ⋯ < d_k` are the descents. A position `u ∈ [n]` is free if it is not the
northeast endpoint of a hook of `𝓗`, and `(i, j) ∈ 𝓗` covers `u` if `i < u < j`. Then `q₀` is the
number of free `u` covered by no hook of `𝓗`, and `qₜ` the number of free `u` covered by a hook
`(dₜ, j) ∈ 𝓗` with `πⱼ ≤ π_{j'}` for every hook `(i', j') ∈ 𝓗` covering `u`. -/
@[expose]
public def hookComposition (π : List ℕ) (𝓗 : Finset (ℕ × ℕ)) :
    Fin (π.numDescents + 1) → ℕ :=
  Fin.cases
    ({u ∈ Finset.Icc 1 π.length |
      u ∉ 𝓗.image Prod.snd ∧ ∀ p ∈ 𝓗, ¬(p.1 < u ∧ u < p.2)}.card)
    (fun t => {u ∈ Finset.Icc 1 π.length |
      u ∉ 𝓗.image Prod.snd ∧
        ∃ p ∈ 𝓗, p.1 = π.descentSet.orderEmbOfFin rfl t ∧ p.1 < u ∧ u < p.2 ∧
          ∀ p' ∈ 𝓗, p'.1 < u → u < p'.2 → π.getD (p.2 - 1) 0 ≤ π.getD (p'.2 - 1) 0}.card)

/-- The set `𝒱(π) = {𝐪_𝓗 : 𝓗 ∈ VHC(π)}` of valid compositions of `π`: the compositions induced by
the valid hook configurations of `π`. -/
@[expose]
public noncomputable def validCompositions (π : List ℕ) :
    Finset (Fin (π.numDescents + 1) → ℕ) :=
  π.validHookConfigurations.image π.hookComposition

end List

end

section

open scoped Pointwise

@[expose] public section

/-- The lattice points `P ∩ ℤ^ι` of a set `P ⊆ R^ι`: the vectors of `P` all of whose coordinates
lie in the image of `ℤ`. -/
abbrev Set.latticePoints {R ι : Type*} [Ring R] (P : Set (ι → R)) : Set (ι → R) :=
  {v | v ∈ P ∧ ∀ i, v i ∈ Set.range (Int.cast : ℤ → R)}

section Simplex

variable (R : Type*) {ι : Type*} [Semiring R] [PartialOrder R] [DecidableEq ι]

/-- The coordinate simplex `Δ_J = conv {e_j : j ∈ J}` in `ι → R`, where `e_j = Pi.single j 1` is
the `j`-th standard basis vector. -/
def coordSimplex (J : Set ι) : Set (ι → R) :=
  convexHull R ((fun j : ι => (Pi.single j 1 : ι → R)) '' J)

/-- The nestohedron `Nest_𝓑(c) = ∑_{J ∈ 𝓑} c_J Δ_J`, the Minkowski sum of the coordinate simplices
`Δ_J = coordSimplex R J` dilated by `c_J`. It is a binary nestohedron when `𝓑` is a binary
building set and every `c_J` is positive. -/
def nestohedron (𝓑 : Finset (Finset ι)) (c : Finset ι → R) : Set (ι → R) :=
  ∑ J ∈ 𝓑, c J • coordSimplex R (J : Set ι)

end Simplex

section BuildingSet

variable {α : Type*} [LinearOrder α] [LocallyFiniteOrder α]

/-- A finite collection `𝓑` of subsets of `α` is a *binary building set* if every member is a
nonempty interval `[a, b]`, every singleton `{i}` is a member, and any two members are disjoint or
nested. -/
structure IsBinaryBuildingSet (𝓑 : Finset (Finset α)) : Prop where
  /-- Every member of `𝓑` is a nonempty interval `[a, b]`. -/
  exists_eq_Icc : ∀ J ∈ 𝓑, ∃ a b, a ≤ b ∧ J = Finset.Icc a b
  /-- Every singleton belongs to `𝓑`. -/
  singleton_mem : ∀ i : α, {i} ∈ 𝓑
  /-- Any two members of `𝓑` are disjoint or one contains the other. -/
  disjoint_or_subset_or_subset :
    ∀ J ∈ 𝓑, ∀ K ∈ 𝓑, Disjoint J K ∨ J ⊆ K ∨ K ⊆ J

end BuildingSet

section Nestohedron

variable (R : Type*) {α : Type*}

/-- A set `P ⊆ α → R` is a *binary nestohedron* if `P = Nest_𝓑(c)` for a binary building set `𝓑`
on `α` and coefficients `c` with `0 < c J` for every `J ∈ 𝓑`. -/
def IsBinaryNestohedron [Semiring R] [PartialOrder R] [LinearOrder α] [LocallyFiniteOrder α]
    (P : Set (α → R)) : Prop :=
  ∃ 𝓑 : Finset (Finset α), IsBinaryBuildingSet 𝓑 ∧
    ∃ c : Finset α → R, (∀ J ∈ 𝓑, 0 < c J) ∧ P = nestohedron R 𝓑 c

/-- A set `P ⊆ α → R` is an *integral binary nestohedron* if it is a binary nestohedron and every
extreme point of `P` has integer coordinates. -/
def IsIntegralBinaryNestohedron [Ring R] [PartialOrder R] [LinearOrder α]
    [LocallyFiniteOrder α] (P : Set (α → R)) : Prop :=
  IsBinaryNestohedron R P ∧ P.extremePoints R ⊆ P.latticePoints

end Nestohedron

end

end

section

open Polynomial

/-- **The refined fertility formula** (C. Defant, *Fertilitopes*, 2023, Corollary 2.4): for every
`n ≥ 1` and every permutation `π ∈ S_n`, `x D_π(x) = ∑_{𝐪 ∈ 𝒱(π)} N_𝐪(x)`, i.e. `X *
List.fiberDescentPolynomial ℝ π = ∑ q ∈ π.validCompositions, narayanaTupleProd q`, where
`narayanaTupleProd q = ∏ i, narayanaPolynomial (q i)`. -/
@[expose]
public def RefinedFertilityFormula : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ π ∈ permWords n,
    (X : ℝ[X]) * π.fiberDescentPolynomial ℝ = ∑ q ∈ π.validCompositions, narayanaTupleProd q

end

section

open scoped Pointwise

/-- **Realization of integral binary nestohedra** (C. Defant, *Fertilitopes*, 2023, Theorems 3.1
and 3.2): for every `r ≥ 1` and every integral binary nestohedron `P ⊆ ℝ^r` there are `n ≥ 1` and
a permutation `π ∈ S_n` with `des(π) = r - 1` whose valid compositions `List.validCompositions π`
are exactly the lattice points of `P`. -/
@[expose]
public def IntegralBinaryNestohedronRealization : Prop :=
  ∀ (r : ℕ), 1 ≤ r → ∀ (P : Set (Fin r → ℝ)), IsIntegralBinaryNestohedron ℝ P →
    ∃ n : ℕ, 1 ≤ n ∧ ∃ π ∈ permWords n, ∃ h : π.numDescents + 1 = r,
      P.latticePoints =
        (fun q i => (q (Fin.cast h.symm i) : ℝ)) ''
          (π.validCompositions : Set (Fin (π.numDescents + 1) → ℕ))

end

section

@[expose] public section

open Polynomial

namespace BinaryTree

section DecreasingColoredTrees

variable {α : Type*} [DecidableEq α] [LT α] (C : Type*)

/-- The set of *decreasing colored binary plane trees on `A`*: trees whose vertices carry a label
in `α` and a color in `C`, such that the tree of labels `T.map Prod.fst` is a decreasing binary
plane tree on `A`. The color of a vertex is the second component of its entry. -/
public def decreasingColoredTrees (A : Finset α) : Set (BinaryTree (α × C)) :=
  {T | T.map Prod.fst ∈ decreasingTrees A}

end DecreasingColoredTrees

section Skeleton

variable {α C : Type*}

/-- The *skeleton* of a tree whose vertices carry (label, color) pairs: the colored binary plane
tree of the same shape whose vertices carry only the colors, the labels being forgotten. -/
public abbrev skeleton (T : BinaryTree (α × C)) : BinaryTree C :=
  T.map Prod.snd

end Skeleton

section DecreasingLabelings

variable {C : Type*}

/-- The set `↓T↓` of *decreasing labelings* of a colored binary plane tree `T`: the decreasing
colored binary plane trees on `{1, …, n}`, where `n` is the number of vertices of `T`, whose
skeleton is `T`. -/
public def decreasingLabelings (T : BinaryTree C) : Set (BinaryTree (ℕ × C)) :=
  {𝒯 | 𝒯 ∈ decreasingColoredTrees C (Finset.Icc 1 T.numNodes) ∧ 𝒯.skeleton = T}

/-- The set `↓U↓` of decreasing labelings of a family `U` of colored binary plane trees: the union
over `T ∈ U` of the sets `↓T↓ = T.decreasingLabelings`. -/
public abbrev familyDecreasingLabelings (U : Set (BinaryTree C)) : Set (BinaryTree (ℕ × C)) :=
  ⋃ T ∈ U, T.decreasingLabelings

end DecreasingLabelings

end BinaryTree

namespace List

variable {C : Type*}

/-- The *fiber descent polynomial* `D_{π,U}(x) = ∑_{𝒯 ∈ ↓U↓, 𝒫(𝒯) = π} x^{des(ℐ(𝒯))}` of a family
`U` of colored binary plane trees at `π`, with coefficients in a semiring `R`: the sum runs over
the decreasing labelings `𝒯` of members of `U` whose postorder reading is `π`, and the exponent is
the number of descents of the inorder reading of `𝒯`. -/
public noncomputable def familyFiberDescentPolynomial (R : Type*) [Semiring R]
    (U : Set (BinaryTree C)) (π : List ℕ) : R[X] :=
  ∑ᶠ (𝒯 : BinaryTree (ℕ × C))
    (_ : 𝒯 ∈ BinaryTree.familyDecreasingLabelings U ∧ (𝒯.map Prod.fst).postorder = π),
    X ^ (𝒯.map Prod.fst).inorder.numDescents

end List

end

end

section

namespace MvPolynomial

open Polynomial in
/-- The Narayana transform `𝒩 : ℝ[z_σ] → ℝ[x]`: the `ℝ`-linear map sending the monomial `z^α` to
`∏ i ∈ α.support, Ñ_{α i}(x)`, so that `𝒩(F) = ∑_{α ∈ supp F} [z^α]F · ∏_i Ñ_{α_i}(x)`. -/
@[expose]
public noncomputable def narayanaTransform (σ : Type*) : MvPolynomial σ ℝ →ₗ[ℝ] ℝ[X] :=
  (basisMonomials σ ℝ).constr ℝ fun α => α.prod fun _ k => shiftedNarayanaPolynomial k

end MvPolynomial

end

section

/-- `Par_r`, the partitions with at most `r` parts: weakly decreasing `r`-tuples `μ₁ ≥ μ₂ ≥ ⋯ ≥
μᵣ` of natural numbers, indexed by `Fin r`. -/
public abbrev PartitionAtMostParts (r : ℕ) : Type :=
  {μ : Fin r → ℕ // Antitone μ}

namespace PartitionAtMostParts

/-- The shape `(a + d, a^{r-1}) = (a + d, a, …, a)` in `Par_r`. -/
@[expose]
public def hook (r a d : ℕ) : PartitionAtMostParts r :=
  ⟨fun i => if (i : ℕ) = 0 then a + d else a, fun i j hij => by
    by_cases hj : (j : ℕ) = 0
    · have : (i : ℕ) = 0 := Nat.le_zero.mp (hj ▸ (hij : (i : ℕ) ≤ j))
      simp [hj, this]
    · by_cases hi : (i : ℕ) = 0 <;> simp [hi, hj]⟩

end PartitionAtMostParts

namespace PartitionAtMostParts

variable {r : ℕ}

/-- The Young diagram of `μ ∈ Par_r`: its `i`-th row (from `0`) has length `μ i`. -/
@[expose]
public def youngDiagram (μ : PartitionAtMostParts r) : YoungDiagram :=
  YoungDiagram.ofRowLens (List.ofFn μ.1) (List.sortedGE_ofFn_iff.2 μ.2)

/-- `SSYT_r(μ)`: the semistandard Young tableaux of shape `μ` (rows weakly increasing, columns
strictly increasing) all of whose entries lie in `{0, …, r - 1}`, which stands for `[r]`. -/
@[expose]
public def semistandardYoungTableaux (μ : PartitionAtMostParts r) :
    Set (SemistandardYoungTableau μ.youngDiagram) :=
  {T | ∀ i j, (i, j) ∈ μ.youngDiagram → T i j < r}

end PartitionAtMostParts

namespace SemistandardYoungTableau

variable {γ : YoungDiagram}

/-- The content `ct(T) : Fin r → ℕ` of a semistandard Young tableau `T`: its `i`-th coordinate is
the number of cells of the diagram whose entry is `i`. -/
@[expose]
public def content (T : SemistandardYoungTableau γ) (r : ℕ) : Fin r → ℕ :=
  fun i => (γ.cells.filter fun c => T c.1 c.2 = i).card

end SemistandardYoungTableau

namespace PartitionAtMostParts

variable {r : ℕ}

/-- The Kostka number `K_{μ,α}`: the number of semistandard Young tableaux of shape `μ` with
entries in `[r]` (represented by `{0, …, r - 1}`) whose content is `α`. -/
@[expose]
public noncomputable def kostkaNumber (μ : PartitionAtMostParts r) (α : Fin r → ℕ) : ℕ :=
  {T ∈ μ.semistandardYoungTableaux | T.content r = α}.ncard

end PartitionAtMostParts

namespace PartitionAtMostParts

variable {r : ℕ}

/-- The Schur polynomial `s_μ(z₁, …, zᵣ) = ∑_{|α| = |μ|} K_{μ,α} z^α` of a partition `μ` with at
most `r` parts, the sum running over weak compositions `α : Fin r → ℕ` of `|μ| = ∑ i, μ i` and
`K_{μ,α}` being `PartitionAtMostParts.kostkaNumber`. -/
@[expose]
public noncomputable def schurPolynomial (R : Type*) [CommSemiring R]
    (μ : PartitionAtMostParts r) : MvPolynomial (Fin r) R :=
  ∑ α ∈ Finset.Nat.antidiagonalTuple r (∑ i, μ.1 i),
    MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm α) (μ.kostkaNumber α : R)

end PartitionAtMostParts

namespace PartitionAtMostParts

variable {r : ℕ}

/-- The Narayana transform `Φ_{μ,r}(x) = 𝒩(s_μ)(x)` of the Schur polynomial `s_μ(z₁, …, zᵣ)` of a
partition `μ` with at most `r` parts. -/
@[expose]
public noncomputable def schurNarayanaTransform (μ : PartitionAtMostParts r) : Polynomial ℝ :=
  MvPolynomial.narayanaTransform (Fin r) (μ.schurPolynomial ℝ)

end PartitionAtMostParts

end

section

/-- The finite sequence `(b j)_{j=0}^{d}` is *log-concave*: `0 ≤ b j` for `j ≤ d`, and `b (j - 1)
* b (j + 1) ≤ b j ^ 2` for `1 ≤ j ≤ d - 1` (stated with `j + 1` as the middle index). -/
@[expose]
public def IsLogConcaveSeq {R : Type*} [Semiring R] [PartialOrder R] (d : ℕ) (b : ℕ → R) :
    Prop :=
  (∀ j ≤ d, 0 ≤ b j) ∧ ∀ j, j + 2 ≤ d → b j * b (j + 2) ≤ b (j + 1) ^ 2

/-- The finite sequence `(b j)_{j=0}^{d}` has *no internal zeros*: for `i < j < k ≤ d` with
`0 < b i` and `0 < b k`, also `0 < b j`. -/
@[expose]
public def HasNoInternalZeros {R : Type*} [Zero R] [LT R] (d : ℕ) (b : ℕ → R) : Prop :=
  ∀ i j k, i < j → j < k → k ≤ d → 0 < b i → 0 < b k → 0 < b j

namespace Polynomial

/-- A polynomial `f` is *log-concave* if `0 ≤ f.coeff j` for every `j`, and `f.coeff (j - 1) *
f.coeff (j + 1) ≤ f.coeff j ^ 2` for every `j ≥ 1` (stated with `j + 1` as the middle index). -/
@[expose]
public def IsLogConcave {R : Type*} [Semiring R] [PartialOrder R] (f : Polynomial R) :
    Prop :=
  (∀ j, 0 ≤ f.coeff j) ∧ ∀ j, f.coeff j * f.coeff (j + 2) ≤ f.coeff (j + 1) ^ 2

/-- A polynomial `f` is *ultra-log-concave of order `d`*: `f.natDegree ≤ d`, and the sequence
`(f.coeff j / d.choose j)_{j=0}^{d}` is log-concave and has no internal zeros. -/
@[expose]
public def IsUltraLogConcave {R : Type*} [Semifield R] [PartialOrder R] (d : ℕ) (f : R[X]) :
    Prop :=
  f.natDegree ≤ d ∧ IsLogConcaveSeq d (fun j => f.coeff j / (d.choose j : R)) ∧
    HasNoInternalZeros d (fun j => f.coeff j / (d.choose j : R))

end Polynomial

end

section

@[expose] public section

/-- `IsPolytopeEdge P x y` says that the segment `[x, y]` is an *edge* of `P ⊆ ℝ^ι`: `x ≠ y`, and
for some linear functional `ℓ`, `[x, y]` is the set of points `q ∈ P` maximizing `ℓ` over `P`. -/
public def IsPolytopeEdge {ι : Type*} (P : Set (ι → ℝ)) (x y : ι → ℝ) : Prop :=
  x ≠ y ∧ ∃ ℓ : (ι → ℝ) →ₗ[ℝ] ℝ, segment ℝ x y = {q ∈ P | ∀ p ∈ P, ℓ p ≤ ℓ q}

/-- `IsIntegralPolytope P` says that `P ⊆ ℝ^ι` is an *integral polytope*: `P` is the convex hull
of a finite nonempty set of points, and every extreme point of `P` has integer coordinates. -/
public def IsIntegralPolytope {ι : Type*} (P : Set (ι → ℝ)) : Prop :=
  (∃ V : Finset (ι → ℝ), V.Nonempty ∧ P = convexHull ℝ (V : Set (ι → ℝ))) ∧
    ∀ x ∈ P.extremePoints ℝ, ∀ i, x i ∈ Set.range ((↑) : ℤ → ℝ)

/-- `IsGeneralizedPermutohedron P` says that `P ⊆ ℝ^ι` is a *generalized permutohedron*: `P` is
the convex hull of a finite nonempty set of points, and every edge `[x, y]` of `P` satisfies `y -
x = c • (eᵢ - eⱼ)` for some `i ≠ j` and `c : ℝ`. -/
public def IsGeneralizedPermutohedron {ι : Type*} [DecidableEq ι] (P : Set (ι → ℝ)) : Prop :=
  (∃ V : Finset (ι → ℝ), V.Nonempty ∧ P = convexHull ℝ (V : Set (ι → ℝ))) ∧
    ∀ x y : ι → ℝ, IsPolytopeEdge P x y →
      ∃ i j : ι, i ≠ j ∧ ∃ c : ℝ, y - x = c • (Pi.single i 1 - Pi.single j 1)

/-- The vertex `v_S ∈ ℤ^27` of the non-log-concave example polytope, for `S ⊆ [5]`: `v_S = (a, 1 +
1_S)` if `S = {0, 1}` and `v_S = (b, 1 + 1_S)` otherwise, where `a = (23, 1, …, 1)` and `b = (2,
…, 2)` in `ℤ^22` (indices `0`-based). -/
public def nlcVertex (S : Finset (Fin 5)) : Fin 27 → ℤ :=
  Fin.append (m := 22) (n := 5)
    (if S = {0, 1} then fun i => if i = 0 then 23 else 1 else fun _ => 2)
    (fun i => if i ∈ S then 2 else 1)

/-- The non-log-concave example polytope `P^nlc ⊆ ℝ^27`: the convex hull of the points `v_S =
nlcVertex S`, cast to `ℝ`, over the `2`-element subsets `S` of `Fin 5`. -/
public def nlcPolytope : Set (Fin 27 → ℝ) :=
  convexHull ℝ
    ((fun S : Finset (Fin 5) => fun i => (nlcVertex S i : ℝ)) '' {S | S.card = 2})

end

end

section

namespace MvPolynomial

section QAlgebra

variable {σ : Type*} {R : Type*} [CommSemiring R] [Algebra ℚ R]

/-- The higher kernel operator `𝓡^{(m)}_K U = ∂_t^m (U * K)`, where `*` is
`MvPolynomial.tConvolution` and `∂_t = pderiv none`. It is `R`-linear because the convolution is
linear in its first argument. -/
@[expose]
public noncomputable def higherKernelOperator (m : ℕ) (K : MvPolynomial (Option σ) R) :
    MvPolynomial (Option σ) R →ₗ[R] MvPolynomial (Option σ) R where
  toFun U := (pderiv none)^[m] (tConvolution U K)
  map_add' U V := by
    simp only [tConvolution, map_add, add_mul]
    exact iterate_map_add (pderiv (R := R) (none : Option σ)) m _ _
  map_smul' c U := by
    simp only [tConvolution, map_smul, smul_mul_assoc, RingHom.id_apply]
    simpa only [Module.End.pow_apply, Derivation.coeFn_coe] using
      map_smul ((pderiv (none : Option σ)).toLinearMap ^ m) c _

end QAlgebra

section CommSemiring

variable {σ : Type*} {R : Type*} [CommSemiring R]

/-- The `j`-th coefficient `W_j(K) = (m - j)! K_{m-j}(x)` of a kernel `K` of `t`-degree at most
`m`, where `K_h(x)` is the coefficient of `t^h = (X none)^h` in `K`. -/
@[expose]
public noncomputable def kernelCoeff (m j : ℕ) :
    MvPolynomial (Option σ) R →ₗ[R] MvPolynomial σ R :=
  ((m - j).factorial : R) •
    ((Polynomial.lcoeff (MvPolynomial σ R) (m - j)).restrictScalars R ∘ₗ
      (optionEquivLeft R σ).toLinearMap)

end CommSemiring

end MvPolynomial

end

section

/-- An indexed family `A : ι → Set α` of subsets of `α` is *laminar* if any two of its members
that intersect are nested. -/
@[expose]
public def IsLaminar {ι α : Type*} (A : ι → Set α) : Prop :=
  ∀ i j, (A i ∩ A j).Nonempty → A i ⊆ A j ∨ A j ⊆ A i

/-- The *capacity-bounded sets* `𝕀_{𝒜,c}` of a family `A : ι → Set α` with capacities `c : ι → ℕ`
on a ground set `E`: the subsets `I ⊆ E` meeting each `A k` in at most `c k` elements. -/
@[expose]
public def capacityBoundedSets {ι α : Type*} (E : Set α) (A : ι → Set α) (c : ι → ℕ) :
    Set (Set α) :=
  {I | I ⊆ E ∧ ∀ k, (I ∩ A k).encard ≤ c k}

/-- A matroid `M` is *laminar* if there are a finite laminar family `A : ι → Set α` and capacities
`c : ι → ℕ` whose capacity-bounded sets on `M.E` are exactly the independent sets of `M`. -/
@[expose]
public def Matroid.IsLaminar {α : Type*} (M : Matroid α) : Prop :=
  ∃ (ι : Type) (_ : Finite ι) (A : ι → Set α) (c : ι → ℕ),
    _root_.IsLaminar A ∧ ∀ I, M.Indep I ↔ I ∈ capacityBoundedSets M.E A c

end

section

@[expose] public section

/-- A *loopless multigraph* on the vertex type `V` with edge type `E`: each edge `e : E` joins the
two distinct vertices `src e` and `tgt e`. Parallel edges are allowed; the order of the endpoints
only names them. The paper's case is `V = Fin r` with `E` finite. -/
public structure LooplessMultigraph (V : Type*) (E : Type*) where
  /-- The first named endpoint of an edge. -/
  src : E → V
  /-- The second named endpoint of an edge. -/
  tgt : E → V
  /-- No edge is a loop. -/
  src_ne_tgt : ∀ e, src e ≠ tgt e

namespace LooplessMultigraph

section Orientations

variable {V E : Type*}

/-- The set `Or(G)` of *orientations* of a loopless multigraph `G`: the maps `h : E → V` sending
every edge `e` to one of its endpoints, `h e = G.src e` or `h e = G.tgt e` (the edge `e` is
oriented toward `h e`). -/
public def orientations (G : LooplessMultigraph V E) : Set (E → V) :=
  {h | ∀ e, h e = G.src e ∨ h e = G.tgt e}

end Orientations

section Indegree

variable {V E : Type*} [Fintype E]

/-- The *in-degree vector* of an orientation `h : E → V`: its value at a vertex `v` is the number
`|{e ∈ E : h e = v}|` of edges oriented toward `v`, written `indeg_h(v)` in the paper. It is `∑
e, Finsupp.single (h e) 1`. -/
public noncomputable def indegree (h : E → V) : V →₀ ℕ :=
  ∑ e, Finsupp.single (h e) 1

end Indegree

end LooplessMultigraph

end

end

section

@[expose] public section

namespace LooplessMultigraph

section Forest

variable {V E : Type*}

/-- A loopless multigraph `G` is a *forest* if distinct edges have distinct unordered endpoint
pairs and the simple graph on `V` with edge set `{s(G.src e, G.tgt e) | e}` is acyclic. -/
public def IsForest (G : LooplessMultigraph V E) : Prop :=
  Function.Injective (fun e => s(G.src e, G.tgt e)) ∧
    (SimpleGraph.fromEdgeSet (Set.range fun e => s(G.src e, G.tgt e))).IsAcyclic

end Forest

end LooplessMultigraph

end

section Zonotope

variable {R : Type*} {V E : Type*} [Semiring R] [PartialOrder R] [DecidableEq V] [Fintype E]

/-- The polytope `P_{G,a} = a + ∑_{e ∈ E} Δ_{{s(e), t(e)}}`: the set of points `a + ∑ e, p e` with
`p e` in the edge simplex `coordSimplex R {G.src e, G.tgt e}` for every edge `e`. For a forest `G`
and positive integer `a` this is the tree zonotope. -/
@[expose]
public def LooplessMultigraph.zonotope (G : LooplessMultigraph V E) (a : V → R) : Set (V → R) :=
  {x | ∃ p : E → V → R, (∀ e, p e ∈ coordSimplex R {G.src e, G.tgt e}) ∧ x = a + ∑ e, p e}

end Zonotope

end

section

@[expose] public section

/-- A finite set `M` of pairs `(a, b)` of natural numbers is a *noncrossing partial matching on
`[N]`* if every pair satisfies `1 ≤ a < b ≤ N`, no integer is an entry of two distinct pairs, and
no two pairs `(a, b), (c, d)` satisfy `a < c < b < d`. The left endpoint of `p ∈ M` is `p.1`, its
right endpoint `p.2`. -/
structure IsNoncrossingPartialMatching (N : ℕ) (M : Finset (ℕ × ℕ)) : Prop where
  /-- Every pair `(a, b) ∈ M` satisfies `1 ≤ a`. -/
  one_le_fst : ∀ p ∈ M, 1 ≤ p.1
  /-- Every pair `(a, b) ∈ M` satisfies `a < b`. -/
  fst_lt_snd : ∀ p ∈ M, p.1 < p.2
  /-- Every pair `(a, b) ∈ M` satisfies `b ≤ N`. -/
  snd_le : ∀ p ∈ M, p.2 ≤ N
  /-- No integer is an entry of two distinct pairs of `M`. -/
  eq_of_mem_of_mem : ∀ p ∈ M, ∀ q ∈ M, ∀ x : ℕ, (x = p.1 ∨ x = p.2) → (x = q.1 ∨ x = q.2) → p = q
  /-- No two pairs `(a, b), (c, d) ∈ M` satisfy `a < c < b < d`. -/
  noncrossing : ∀ p ∈ M, ∀ q ∈ M, ¬ (p.1 < q.1 ∧ q.1 < p.2 ∧ p.2 < q.2)

/-- The *left endpoints* `LE(M) = {a : (a, b) ∈ M for some b}` of a finite set `M` of pairs. -/
abbrev Finset.leftEndpoints {α β : Type*} [DecidableEq α] (M : Finset (α × β)) :
    Finset α :=
  M.image Prod.fst

/-- The *unmatched vertices* `U(M) = [N] \ (LE(M) ∪ R(M))` of a finite set `M` of pairs in `[N] =
{1, …, N}`: the elements of `[N]` that are not an entry of any pair of `M`. -/
def Finset.unmatchedVertices (N : ℕ) (M : Finset (ℕ × ℕ)) : Finset ℕ :=
  Finset.Icc 1 N \ (M.leftEndpoints ∪ M.image Prod.snd)

namespace List

variable {α : Type*} [LT α] [DecidableRel (α := α) (· < ·)]

/-- The set `𝒜(π)` of *matchings of `π`*: the noncrossing partial matchings `M` on `[π.length -
1]` with `Des(π) ⊆ LE(M)` and `π_a < π_{b+1}` for every `(a, b) ∈ M` (`1`-based positions, so `π_a
= π[a - 1]` and `π_{b+1} = π[b]`). -/
def fiberMatchings (π : List α) : Set (Finset (ℕ × ℕ)) :=
  {M | IsNoncrossingPartialMatching (π.length - 1) M ∧ π.descentSet ⊆ M.leftEndpoints ∧
    ∀ p ∈ M, ∃ (ha : p.1 - 1 < π.length) (hb : p.2 < π.length), π[p.1 - 1] < π[p.2]}

/-- The polynomial `Γ_π(z) = ∑_{M ∈ 𝒜(π)} z^{|M|}`, the generating polynomial of the matchings
`List.fiberMatchings π` of `π` by their number of arcs. -/
noncomputable def fiberMatchingPolynomial (R : Type*) [CommSemiring R] {α : Type*} [LT α]
    [DecidableRel (α := α) (· < ·)] (π : List α) : Polynomial R :=
  ∑ᶠ M ∈ π.fiberMatchings, Polynomial.X ^ M.card

end List

namespace BinaryTree

variable {α : Type*}

open Classical in
/-- The *matching* `M(T)` of a binary plane tree `T` with postorder reading `π = 𝒫(T)` of
length `n`: the set of pairs `(a, b)` with `a ∈ [n]` and `b ∈ [n - 1]` such that the vertex
labelled `π_{b+1}` has two children and its left child is the vertex labelled `π_a`
(`1`-based positions, so `π_a = π[a - 1]` and `π_{b+1} = π[b]`). -/
noncomputable def treeMatching (T : BinaryTree α) : Finset (ℕ × ℕ) :=
  (Finset.Icc 1 T.postorder.length ×ˢ Finset.Icc 1 (T.postorder.length - 1)).filter fun p =>
    ∃ (ha : p.1 - 1 < T.postorder.length) (hb : p.2 < T.postorder.length)
      (L₁ L₂ : BinaryTree α) (d : α) (R₁ R₂ : BinaryTree α),
      Relation.ReflTransGen
        (fun S U : BinaryTree α => ∃ m L R, U = node m L R ∧ (S = L ∨ S = R))
        (node T.postorder[p.2] (node T.postorder[p.1 - 1] L₁ L₂) (node d R₁ R₂)) T

open Classical in
/-- The set `C(T)` of a binary plane tree `T` with postorder reading `π = 𝒫(T)` of length `n`:
the unmatched vertices `j ∈ U(M(T))` in `[n - 1]` such that `π_{j+1} ∈ RC(T)` (`1`-based
positions, so `π_{j+1} = π[j]`). -/
noncomputable def treeRightChoices [DecidableEq α] (T : BinaryTree α) : Finset ℕ :=
  (Finset.unmatchedVertices (T.postorder.length - 1) T.treeMatching).filter fun j =>
    ∃ h : j < T.postorder.length, T.postorder[j] ∈ T.rightChildLabels

end BinaryTree

end

end

section

open MvPolynomial in
/-- The *basis generating polynomial* `B_M = ∑_{B} ∏_{e ∈ B} X e` of a matroid `M` on a finite
type `α`, the sum running over the bases `B` of `M`. -/
@[expose]
public noncomputable def Matroid.basisGeneratingPolynomial {α : Type*} [Fintype α]
    (R : Type*) [CommSemiring R] (M : Matroid α) : MvPolynomial α R :=
  open scoped Classical in
  ∑ B ∈ Finset.univ.filter (fun B : Finset α => M.IsBase B), ∏ e ∈ B, X e

end

section

open Polynomial

/-- The *homogenized shifted Narayana polynomial* `hom_m(Ñ_m)(x, y) = y^m Ñ_m(x / y)`, the degree
`m` homogenization of `shiftedNarayanaPolynomial m`, with `x = X 0` and `y = X 1`. -/
public noncomputable abbrev homogShiftedNarayanaPolynomial (m : ℕ) : MvPolynomial (Fin 2) ℝ :=
  (shiftedNarayanaPolynomial m).homogenize m

open Classical in
/-- The *matroid Narayana polynomial* of a matroid `M` on `α` and `a : α → ℕ`:
`F_{M,a} = ∑_{B ∈ 𝔹(M)} ∏_{i ∈ B} hom(Ñ_{a_i + 1}) ∏_{i ∉ B} hom(Ñ_{a_i})` in `ℝ[x, y]`. -/
@[expose]
public noncomputable def Matroid.narayanaPolynomial {α : Type*} [Fintype α] (M : Matroid α)
    (a : α → ℕ) : MvPolynomial (Fin 2) ℝ :=
  ∑ B ∈ Finset.univ.filter (fun B : Finset α => M.IsBase (B : Set α)),
    (∏ i ∈ B, homogShiftedNarayanaPolynomial (a i + 1)) *
      ∏ i ∈ Bᶜ, homogShiftedNarayanaPolynomial (a i)

end

section

open Polynomial

/-- The deformed Narayana polynomial `N_q^{(λ)}(x) = x · Q_{q-1}(1 + x, λ x)`, that is `x
∑_{j=0}^{⌊(q-1)/2⌋} C_j (q-1 choose 2j) (λ x)^j (1 + x)^(q-1-2j)`. -/
@[expose]
public noncomputable def deformedNarayanaPolynomial (R : Type*) [CommSemiring R] (lam : R)
    (q : ℕ) : R[X] :=
  X * MvPolynomial.aeval ![1 + X, C lam * X] (narayanaQ R (q - 1))

end

section

namespace Finpartition

variable {α : Type*} [Lattice α] [OrderBot α] {a : α}

/-- The number of blocks `|P|` of a finite partition `P`: the cardinality of `P.parts`. -/
public abbrev blockCount (P : Finpartition a) : ℕ := P.parts.card

end Finpartition

namespace Finpartition

variable {α : Type*} [LinearOrder α] {s : Finset α}

/-- A finite partition `P` of a finset `s` of a linear order is *noncrossing* if there are no `a <
b < c < d` with `a, c` in one block of `P` and `b, d` in a different block of `P`. -/
@[expose]
public def IsNoncrossing (P : Finpartition s) : Prop :=
  ∀ B ∈ P.parts, ∀ B' ∈ P.parts, B ≠ B' →
    ∀ a ∈ B, ∀ c ∈ B, ∀ b ∈ B', ∀ d ∈ B', ¬ (a < b ∧ b < c ∧ c < d)

end Finpartition

section

open Polynomial

variable {α : Type*} [LinearOrder α]

open Classical in
/-- The restricted noncrossing refinement polynomial `R^{(a)}_{n,k}` on a finite ground set `s`:
the sum, over noncrossing partitions `τ` of `s` with `k` blocks each of size at least `a`, of
`∑ σ, X ^ |σ|`, where `σ` runs over the noncrossing partitions of `s` refining `τ`. -/
@[expose]
public noncomputable def restrictedNoncrossingRefinementPoly (R : Type*) [Semiring R]
    (s : Finset α) (a k : ℕ) : R[X] :=
  ∑ τ ∈ Finset.univ.filter (fun τ : Finpartition s =>
      τ.IsNoncrossing ∧ τ.blockCount = k ∧ ∀ B ∈ τ.parts, a ≤ B.card),
    ∑ σ ∈ Finset.univ.filter (fun σ : Finpartition s => σ.IsNoncrossing ∧ σ ≤ τ),
      X ^ σ.blockCount

open Classical in
/-- The restricted noncrossing sum `R^{(a),λ}_{n,k}` on a finite ground set `s`: the sum, over
noncrossing partitions `τ` of `s` with `k` blocks each of size at least `a`, of
`∏ B ∈ τ, N^{(λ)}_{|B|}`, where `N^{(λ)}_q` is `deformedNarayanaPolynomial R lam q`. -/
@[expose]
public noncomputable def restrictedNoncrossingDeformedNarayanaPoly (R : Type*) [CommSemiring R]
    (lam : R) (s : Finset α) (a k : ℕ) : R[X] :=
  ∑ τ ∈ Finset.univ.filter (fun τ : Finpartition s =>
      τ.IsNoncrossing ∧ τ.blockCount = k ∧ ∀ B ∈ τ.parts, a ≤ B.card),
    ∏ B ∈ τ.parts, deformedNarayanaPolynomial R lam B.card

end

namespace Finpartition

open Finset

/-- **Kreweras' formula** (Kreweras 1972, Theorem 4): for `m : ℕ → ℕ` with `∑ j ∈ [n], j * m j =
n` and `k = ∑ j ∈ [n], m j`, the number of noncrossing partitions `ρ` of `[n] = Finset.Icc 1 n`
with exactly `m j` blocks of size `j` for each `j ∈ [n]`, multiplied by `(n - k + 1)! * ∏ j ∈ [n],
(m j)!`, equals `n!`. -/
@[expose]
public def KrewerasBlockSizeCount : Prop :=
  ∀ (n : ℕ) (m : ℕ → ℕ), ∑ j ∈ Icc 1 n, j * m j = n →
    open scoped Classical in
    (univ.filter (fun ρ : Finpartition (Icc 1 n) => ρ.IsNoncrossing ∧
        ∀ j ∈ Icc 1 n, (ρ.parts.filter (fun B => B.card = j)).card = m j)).card *
      ((n - ∑ j ∈ Icc 1 n, m j + 1).factorial * ∏ j ∈ Icc 1 n, (m j).factorial) =
      n.factorial

end Finpartition

end

section

@[expose] public section

/-- `IsParentMap N par` says that `par` is a *parent map* on `[N] = {1, …, N}`: every vertex `v ∈
[N]` has `par v = none` (`v` is a root) or `par v = some p` with `v < p ≤ N`, and `par` is `none`
outside `[N]`. Equivalently, `par v = some p` implies `1 ≤ v`, `v < p` and `p ≤ N`. -/
def IsParentMap (N : ℕ) (par : ℕ → Option ℕ) : Prop :=
  ∀ v p, par v = some p → 1 ≤ v ∧ v < p ∧ p ≤ N

/-- `IsAncestorOrSelf par u v` says that `u` is an *ancestor-or-self* of `v` (written `u ⪰ v`) in
the forest encoded by the parent map `par`: some iterate `parᵏ(v)`, with `k ≥ 0`, equals `u`. Here
`parᵏ(v) = (fun o => o.bind par)^[k] (some v)`, which is `none` (that is, `⊥`) once the iteration
has passed a root. -/
def IsAncestorOrSelf (par : ℕ → Option ℕ) (u v : ℕ) : Prop :=
  ∃ k : ℕ, (fun o : Option ℕ => o.bind par)^[k] (some v) = some u

/-- `IsStrictAncestor par u v` says that `u` is a *strict ancestor* of `v` in the forest encoded
by the parent map `par`: `u ⪰ v` (that is, `IsAncestorOrSelf par u v`) and `u ≠ v`. -/
def IsStrictAncestor (par : ℕ → Option ℕ) (u v : ℕ) : Prop :=
  IsAncestorOrSelf par u v ∧ u ≠ v

/-- `IsLeaf par v` says that `v` is a *leaf* of the forest encoded by the parent map `par`: no
vertex `u` has `par u = some v`, i.e. `v` has no children. -/
def IsLeaf (par : ℕ → Option ℕ) (v : ℕ) : Prop :=
  ∀ u, par u ≠ some v

open scoped Classical in
/-- `subtreeVertices N par v` is the vertex set `V_v = {u ∈ [N] : v ⪰ u}` of the subtree rooted
at `v` in the forest on `[N] = Finset.Icc 1 N` encoded by the parent map `par`. -/
noncomputable def subtreeVertices (N : ℕ) (par : ℕ → Option ℕ) (v : ℕ) : Finset ℕ :=
  {u ∈ Finset.Icc 1 N | IsAncestorOrSelf par v u}

/-- `IsPostorderForest N par` says that `par` is a *postorder forest* on `[N] = {1, …, N}`: it is
a parent map on `[N]`, and for every `v ∈ [N]` the vertex set `V_v` of the subtree rooted at `v`
is the interval `[v - |V_v| + 1, v]`. -/
def IsPostorderForest (N : ℕ) (par : ℕ → Option ℕ) : Prop :=
  IsParentMap N par ∧
    ∀ v ∈ Finset.Icc 1 N,
      subtreeVertices N par v = Finset.Icc (v + 1 - (subtreeVertices N par v).card) v

/-- `IsAdmissibleMatching N par L M` says that `M` is an *admissible matching* on `[N]` for the
forest encoded by the parent map `par` and the set `L` of marked vertices: `M` is a noncrossing
partial matching on `[N]`, for every `(a, b) ∈ M` the vertex `b` is a strict ancestor of `a`, and
every marked vertex is a left endpoint of `M`. -/
structure IsAdmissibleMatching (N : ℕ) (par : ℕ → Option ℕ) (L : Finset ℕ)
    (M : Finset (ℕ × ℕ)) : Prop where
  /-- `M` is a noncrossing partial matching on `[N]`. -/
  isNoncrossingPartialMatching : IsNoncrossingPartialMatching N M
  /-- For every pair `(a, b) ∈ M`, the vertex `b` is a strict ancestor of `a`. -/
  isStrictAncestor : ∀ p ∈ M, IsStrictAncestor par p.2 p.1
  /-- Every marked vertex is a left endpoint of `M`. -/
  subset_leftEndpoints : L ⊆ M.leftEndpoints

namespace List

variable {α : Type*} [Preorder α]

/-- The pair `(a, b)` is *adoptable* with respect to `π = π₁ ⋯ π_n` (positions `1`-indexed): `1 ≤
a < b ≤ n - 1`, `π_b = max {π_{a+1}, …, π_b}` and `π_{b+1} > max {π_a, …, π_b}`. -/
def IsAdoptablePair (π : List α) (a b : ℕ) : Prop :=
  1 ≤ a ∧ a < b ∧ ∃ hb : b < π.length,
    (∀ i (_ : a < i) (_ : i ≤ b),
      π[i - 1]'(Nat.lt_of_le_of_lt (Nat.sub_le i 1) (Nat.lt_of_le_of_lt ‹i ≤ b› hb)) ≤
        π[b - 1]'(Nat.lt_of_le_of_lt (Nat.sub_le b 1) hb)) ∧
    ∀ i (_ : a ≤ i) (_ : i ≤ b),
      π[i - 1]'(Nat.lt_of_le_of_lt (Nat.sub_le i 1) (Nat.lt_of_le_of_lt ‹i ≤ b› hb)) < π[b]

open Classical in
/-- The *left bound* `ℓ_b = min ({a ∈ [b - 1] : (a, b) is adoptable w.r.t. π} ∪ {b})` of the
adoptable pairs with right endpoint `b`. -/
noncomputable def adoptableLeftBound (π : List α) (b : ℕ) : ℕ :=
  (insert b ((Finset.Ico 1 b).filter (fun a => π.IsAdoptablePair a b))).min'
    (Finset.insert_nonempty _ _)

/-- The *adoptable interval* `I_b = [ℓ_b, b]`, where `ℓ_b = List.adoptableLeftBound π b`. -/
noncomputable abbrev adoptableInterval (π : List α) (b : ℕ) : Finset ℕ :=
  Finset.Icc (π.adoptableLeftBound b) b

/-- The *adoptable forest* of `π`, as a parent map on `[π.length - 1]`: `π.adoptableForest a` is
`some b` for the least `b ∈ [a + 1, π.length - 1]` with `a ∈ π.adoptableInterval b`, and `none` if
there is no such `b`. -/
noncomputable def adoptableForest (π : List α) (a : ℕ) : Option ℕ :=
  if h : ((Finset.Icc (a + 1) (π.length - 1)).filter (a ∈ π.adoptableInterval ·)).Nonempty then
    some (((Finset.Icc (a + 1) (π.length - 1)).filter (a ∈ π.adoptableInterval ·)).min' h)
  else none

end List

end

end

section

/-- The ground set `E_{N,L} = {x, y} × ([N] \ L) = {v⁺, v⁻ : v ∈ [N] \ L}` of the laminar matroid
of a forest on `[N] = {1, …, N}` with marked vertices `L`. The label `true` stands for `x` (`v⁺ =
(true, v)`) and `false` for `y` (`v⁻ = (false, v)`). -/
@[expose]
public def forestGroundSet (N : ℕ) (L : Finset ℕ) : Finset (Bool × ℕ) :=
  Finset.univ ×ˢ (Finset.Icc 1 N \ L)

/-- The block `E_v = {x, y} × (V_v \ L) = {u⁺, u⁻ : u ∈ V_v \ L}` of the subtree rooted at `v` in
the forest on `[N]` encoded by the parent map `par`, with marked vertices `L`. The label `true`
stands for `x` (`u⁺ = (true, u)`) and `false` for `y` (`u⁻ = (false, u)`). -/
@[expose]
public noncomputable def forestBlock (N : ℕ) (par : ℕ → Option ℕ) (L : Finset ℕ) (v : ℕ) :
    Finset (Bool × ℕ) :=
  Finset.univ ×ˢ (subtreeVertices N par v \ L)

open scoped Classical in
/-- The forest independence family
`𝕀_{par,L} = {I ⊆ E_{N,L} : |I ∩ E_v| ≤ |V_v| for every v ∈ [N]}` of the forest on
`[N] = Finset.Icc 1 N` encoded by the parent map `par`, with marked vertices `L`. -/
@[expose]
public noncomputable def forestIndepFamily (N : ℕ) (par : ℕ → Option ℕ) (L : Finset ℕ) :
    Finset (Finset (Bool × ℕ)) :=
  (forestGroundSet N L).powerset.filter fun I =>
    ∀ v ∈ Finset.Icc 1 N, (I ∩ forestBlock N par L v).card ≤ (subtreeVertices N par v).card

open scoped Classical in
/-- The *forest matching polynomial*
`Z_{par,L}(x, y) = ∑_M ∏_{v ∈ R(M)} x_v y_v ∏_{v ∈ U(M)} (x_v + y_v)`,
the sum over all admissible matchings `M` for `(par, L)` on `[N]`, with `x_v = X (true, v)` and
`y_v = X (false, v)`. -/
@[expose]
public noncomputable def forestMatchingPoly (R : Type*) [CommSemiring R] (N : ℕ)
    (par : ℕ → Option ℕ) (L : Finset ℕ) : MvPolynomial (Bool × ℕ) R :=
  ∑ M ∈ (Finset.Icc 1 N ×ˢ Finset.Icc 1 N).powerset.filter
      (fun M : Finset (ℕ × ℕ) => IsAdmissibleMatching N par L M),
    (∏ v ∈ M.image Prod.snd, MvPolynomial.X (true, v) * MvPolynomial.X (false, v)) *
      ∏ v ∈ Finset.unmatchedVertices N M, (MvPolynomial.X (true, v) + MvPolynomial.X (false, v))

/-- `IsOpenPair N par L M O` says that `(M, O)` is an *open pair* for the forest `par` and the set
`L` on `[N]`: `M` is a noncrossing partial matching on `[N]` whose every pair `(a, b)` has `b` a
strict ancestor of `a`, `O` is a set of unmatched vertices of `M`, each *exposed* (no `(a, b) ∈ M`
has `a < u < b`), and `L ⊆ LE(M) ∪ O`. Note that `L ⊆ [N]` is forced. -/
public structure IsOpenPair (N : ℕ) (par : ℕ → Option ℕ) (L : Finset ℕ)
    (M : Finset (ℕ × ℕ)) (O : Finset ℕ) : Prop where
  /-- `M` is a noncrossing partial matching on `[N]`. -/
  isNoncrossingPartialMatching : IsNoncrossingPartialMatching N M
  /-- For every `(a, b) ∈ M`, `b` is a strict ancestor of `a`. -/
  isStrictAncestor : ∀ p ∈ M, IsStrictAncestor par p.2 p.1
  /-- The open vertices are unmatched: `O ⊆ U(M)`. -/
  subset_unmatchedVertices : O ⊆ Finset.unmatchedVertices N M
  /-- Every open vertex `u` is exposed: no `(a, b) ∈ M` satisfies `a < u < b`. -/
  exposed : ∀ u ∈ O, ∀ p ∈ M, ¬ (p.1 < u ∧ u < p.2)
  /-- `L ⊆ LE(M) ∪ O`. -/
  subset_leftEndpoints_union : L ⊆ M.leftEndpoints ∪ O

end

section

namespace MvPolynomial

variable {σ : Type*} {R : Type*} [CommSemiring R] [Algebra ℚ R]

/-- The factorial normalization `𝓝_t` in the variable `t`: the `R`-linear map on `MvPolynomial σ R`
sending each monomial `z^α` to `z^α / (α_t)!`. -/
@[expose]
public noncomputable def factorialNormalization (t : σ) :
    MvPolynomial σ R →ₗ[R] MvPolynomial σ R :=
  (basisMonomials σ R).constr R fun α =>
    monomial α (algebraMap ℚ R (1 / ((α t).factorial : ℚ)))

end MvPolynomial

end

section

section ConditionalTopPolynomial

open Polynomial

namespace List

/-- The *conditional top polynomial* `F(x) = ∑_{σ ∈ Ω} (∏_{a ∈ DT(σ)} α_a ∏_{b ∈ AT(σ)} β_b)
x^{|DT(σ) ∩ J_d| + |AT(σ) ∩ J_a|}`, where `Ω` is the set of `σ` in the stack-sorting fiber
`s⁻¹(π)` whose descent tops contain `A_d` and avoid `B_d`, and whose ascent tops contain `A_a` and
avoid `B_a`. -/
@[expose]
public noncomputable def conditionalTopPolynomial (R : Type*) [CommSemiring R] (π : List ℕ)
    (A_d B_d A_a B_a J_d J_a : Finset ℕ) (α β : ℕ → R) : R[X] :=
  ∑ σ ∈ (stackFiber π).filter (fun σ ↦ A_d ⊆ σ.descentTops ∧ _root_.Disjoint σ.descentTops B_d ∧
      A_a ⊆ σ.ascentTops ∧ _root_.Disjoint σ.ascentTops B_a),
    C ((∏ a ∈ σ.descentTops, α a) * ∏ b ∈ σ.ascentTops, β b) *
      X ^ ((σ.descentTops ∩ J_d).card + (σ.ascentTops ∩ J_a).card)

end List

end ConditionalTopPolynomial

end

section

/-- A polynomial `f` *has only negative roots* (over `ℝ`: only negative real zeros) if it splits
into linear factors and every element of its multiset of roots is negative. -/
@[expose]
public def Polynomial.HasOnlyNegativeRoots {R : Type*} [CommRing R] [IsDomain R] [LT R]
    (f : Polynomial R) : Prop :=
  f.Splits ∧ ∀ r ∈ f.roots, r < 0

namespace MvPolynomial

/-- The homogenization of degree `D` of `f : MvPolynomial σ R`, in the variables `X (some i)` and
one new variable `X none`: `∑_{|α| ≤ D} (coeff α f) • z^α * y ^ (D - |α|)`. If `f.totalDegree ≤
D`, it is `y ^ D * f(z / y)`. -/
@[expose]
public noncomputable def homogenize {R : Type*} [CommSemiring R] {σ : Type*}
    (f : MvPolynomial σ R) (D : ℕ) : MvPolynomial (Option σ) R :=
  ∑ α ∈ f.support with α.degree ≤ D,
    monomial (α.mapDomain Option.some + Finsupp.single none (D - α.degree)) (coeff α f)

/-- A real polynomial `f` is *real-stable* if `f(ζ) ≠ 0` for every `ζ : σ → ℂ` with `0 < (ζ i).im`
for all `i`. -/
@[expose]
public def IsRealStable {σ : Type*} (f : MvPolynomial σ ℝ) : Prop :=
  ∀ ζ : σ → ℂ, (∀ i, 0 < (ζ i).im) → aeval ζ f ≠ 0

end MvPolynomial

end

section

namespace List

/-- The *valid-composition polynomial* `F_π = ∑_{𝐪 ∈ 𝒱(π)} ∏_{i=0}^{k} z_i^{q_i - 1}` of `π`, with
`k = des(π)` and `q_i - 1` the truncated difference in `ℕ`. -/
@[expose]
public noncomputable def validCompositionPoly (R : Type*) [CommSemiring R] (π : List ℕ) :
    MvPolynomial (Fin (π.numDescents + 1)) R :=
  ∑ q ∈ π.validCompositions, ∏ i, MvPolynomial.X i ^ (q i - 1)

end List

end

section

@[expose] public section

open MvPolynomial

namespace List

/-- The *Schröder postorder polynomial* `𝒞_π(z, w) = ∑ z^{black(𝒯)} w^{white(𝒯)}`, the sum over
the decreasing labelings `𝒯 ∈ ↓𝐒↓` of Schröder two-colored binary trees with postorder reading
`π`, where `z = X 0` and `w = X 1`. -/
public noncomputable def schroederFiberPolynomial (R : Type*) [CommSemiring R] (C : Type*)
    [BinaryTree.TreeColors C] [DecidableEq C] (π : List ℕ) : MvPolynomial (Fin 2) R :=
  ∑ᶠ (𝒯 : BinaryTree (ℕ × C))
    (_ : 𝒯 ∈ BinaryTree.familyDecreasingLabelings (BinaryTree.schroederTrees C) ∧
      (𝒯.map Prod.fst).postorder = π),
    X 0 ^ 𝒯.skeleton.numBlackNodes * X 1 ^ 𝒯.skeleton.numWhiteNodes

end List

end

end

section

namespace MvPolynomial

variable (R : Type*) [CommRing R] (σ : Type*)

/-- The *Appell operator*: the `R`-linear map on `MvPolynomial σ R` sending the monomial `z^α` to
`∏_i η_{α_i}(z_i)`, where `η_m = Polynomial.signedAppell R m`. -/
@[expose]
public noncomputable def appellOperator : MvPolynomial σ R →ₗ[R] MvPolynomial σ R :=
  (basisMonomials σ R).constr R fun α =>
    α.prod fun i k => Polynomial.aeval (X i) (Polynomial.signedAppell R k)

end MvPolynomial

end

section

namespace MvPolynomial

open Polynomial

/-- The deformed Narayana transform `𝒩_λ : R[z_σ] → R[x]`: the `R`-linear map sending the monomial
`z^α` to `∏ i ∈ α.support, Q_{α i}(1 + x, λ x)`, so that
`𝒩_λ(F) = ∑_{α ∈ supp F} [z^α]F · ∏_i Q_{α_i}(1 + x, λ x)`. -/
@[expose]
public noncomputable def deformedNarayanaTransform (R : Type*) [CommSemiring R] (lam : R)
    (σ : Type*) : MvPolynomial σ R →ₗ[R] R[X] :=
  (basisMonomials σ R).constr R fun α =>
    α.prod fun _ k => aeval ![1 + Polynomial.X, Polynomial.C lam * Polynomial.X] (narayanaQ R k)

end MvPolynomial

end

section

namespace MvPolynomial

variable {σ : Type*} {R : Type*} [Semifield R]

/-- The quadratic kernel `K_{A,B}(x, t) = B(x) + A(x) t + t² / 2`, in the variables `X (some i)`
(the `x_i`) and the new variable `t = X none`. -/
@[expose]
public noncomputable def quadraticKernel (A B : MvPolynomial σ R) :
    MvPolynomial (Option σ) R :=
  rename some B + rename some A * X none + C 2⁻¹ * X none ^ 2

end MvPolynomial

end

section

noncomputable section

namespace MvPolynomial

section RootOperator

variable {σ R : Type*} [CommSemiring R] [Algebra ℚ R]

/-- The *root operator* `𝓡_{A,B}(U) = A U + ∫₀ᵗ U ds + B ∂_t U` with respect to the variable `t`,
as an `R`-linear map on `MvPolynomial σ R`. -/
@[expose]
public def rootOperator (t : σ) (A B : MvPolynomial σ R) :
    MvPolynomial σ R →ₗ[R] MvPolynomial σ R :=
  LinearMap.mulLeft R A + antiderivative t + LinearMap.mulLeft R B ∘ₗ (pderiv t).toLinearMap

end RootOperator

end MvPolynomial

end

@[expose] public section

open MvPolynomial

/-- The *vertex-weighted open-pair polynomial* `P^{A,B}_{par,L}(x, t)` of the forest `par` with
marked set `L` on `[N]`, for families `A`, `B` of polynomials in `R[x]`: the sum, over the open
pairs `(M, O)` of `(par, L)`, of `t ^ |O| * ∏_{(a,b) ∈ M} B_b * ∏_{v ∈ U(M) \ O} A_v`. Here
`t = X none` and `R[x]` is embedded in `R[x, t] = MvPolynomial (Option σ) R` by `rename some`. -/
public noncomputable def vertexWeightedOpenPairPolynomial {R σ : Type*} [CommSemiring R]
    (N : ℕ) (par : ℕ → Option ℕ) (L : Finset ℕ) (A B : ℕ → MvPolynomial σ R) :
    MvPolynomial (Option σ) R :=
  open scoped Classical in
  ∑ MO ∈ ((Finset.Icc 1 N ×ˢ Finset.Icc 1 N).powerset ×ˢ (Finset.Icc 1 N).powerset).filter
      (fun MO : Finset (ℕ × ℕ) × Finset ℕ => IsOpenPair N par L MO.1 MO.2),
    X none ^ MO.2.card * (∏ p ∈ MO.1, rename some (B p.2)) *
      ∏ v ∈ Finset.unmatchedVertices N MO.1 \ MO.2, rename some (A v)

/-- The *weighted open-pair polynomial* `P^{A,B}_{par,L}(x, t)` of the forest `par` with marked
set `L` on `[N]`, for `A, B ∈ R[x]`: the vertex-weighted open-pair polynomial for the constant
families `A_v = A` and `B_v = B`, i.e. the sum over the open pairs `(M, O)` of `t ^ |O| * B ^ |M|
* A ^ |U(M) \ O|`. -/
public noncomputable def weightedOpenPairPolynomial {R σ : Type*} [CommSemiring R]
    (N : ℕ) (par : ℕ → Option ℕ) (L : Finset ℕ) (A B : MvPolynomial σ R) :
    MvPolynomial (Option σ) R :=
  vertexWeightedOpenPairPolynomial N par L (fun _ => A) (fun _ => B)

end

end

section

section Cited

open MvPolynomial

/-- **Borcea–Brändén** [BB, Theorem 1.2, (b) ⇒ real stability preserving]: for a finite nonempty
variable type `σ`, every `κ : σ →₀ ℕ` and every `ℝ`-linear `T : restrictSupport ℝ (Set.Iic κ)
→ₗ[ℝ] MvPolynomial σ ℝ` whose algebraic symbol `G_T(z, w) = algebraicSymbol κ T` is real-stable,
`T f` is zero or real-stable for every real-stable `f` in the domain. For an infinite or empty `σ`
the proposition says nothing. -/
@[expose]
public def RealStablePreserverOfSymbol (σ : Type*) : Prop :=
  ∀ [Finite σ] [Nonempty σ] (κ : σ →₀ ℕ)
    (T : restrictSupport ℝ (Set.Iic κ) →ₗ[ℝ] MvPolynomial σ ℝ),
    (algebraicSymbol κ T).IsRealStable →
    ∀ f : restrictSupport ℝ (Set.Iic κ), (f : MvPolynomial σ ℝ).IsRealStable →
      T f = 0 ∨ (T f).IsRealStable

/-- **Borcea–Brändén–Liggett** [BBL, Theorem 4.5, (2) ⇒ (1)], as used in [BH, proof of Corollary
3.9]: for a finite variable type `σ`, if `f ∈ ℝ[z_i : i ∈ σ]` has nonnegative coefficients and is
real-stable, then its homogenization `f_H = homogenize f f.totalDegree` of degree `deg f` is
real-stable. For an infinite `σ` the proposition says nothing. -/
@[expose]
public def IsRealStableHomogenizeOfNonneg (σ : Type*) : Prop :=
  ∀ [Finite σ] (f : MvPolynomial σ ℝ), f.HasNonnegCoeffs → f.IsRealStable →
    (f.homogenize f.totalDegree).IsRealStable

/-- **Brändén–Huh** [BH, Proposition 2.2]: every homogeneous real-stable polynomial `f ∈ ℝ[z_i : i
∈ σ]` with nonnegative coefficients is Lorentzian. -/
@[expose]
public def IsLorentzianOfRealStable (σ : Type*) [Fintype σ] : Prop :=
  ∀ f : MvPolynomial σ ℝ, (∃ d : ℕ, f.IsHomogeneous d) → f.IsRealStable →
    f.HasNonnegCoeffs → f.IsLorentzian

/-- **Wagner** [Wagner, Lemma 2.4(f), with (a)]: for every real-stable polynomial `f ∈ ℝ[z_i : i ∈
σ]` and every `i : σ`, the partial derivative `pderiv i f` is zero or real-stable. -/
@[expose]
public def IsRealStablePDerivClosed (σ : Type*) : Prop :=
  ∀ (f : MvPolynomial σ ℝ), f.IsRealStable → ∀ i : σ,
    pderiv i f = 0 ∨ (pderiv i f).IsRealStable

/-- **Wagner** [Wagner, Lemma 2.4(d), with (a)]: for every real-stable polynomial `f ∈ ℝ[z_j : j ∈
σ]`, every `i : σ` and every `a : ℝ`, the polynomial obtained from `f` by substituting `C a` for
`X i` is zero or real-stable. -/
@[expose]
public def IsRealStableSpecializeClosed (σ : Type*) [DecidableEq σ] : Prop :=
  ∀ (f : MvPolynomial σ ℝ), f.IsRealStable → ∀ (i : σ) (a : ℝ),
    aeval (Function.update X i (C a)) f = 0 ∨
      (aeval (Function.update X i (C a)) f).IsRealStable

end Cited

end

section

namespace PartitionAtMostParts

/-- The one-row shape `(d) = (d, 0, …, 0)` in `Par_r`. -/
public abbrev row (r d : ℕ) : PartitionAtMostParts r :=
  hook r 0 d

end PartitionAtMostParts

namespace Polynomial

/-- The Jacobi polynomial `P^{(α,β)}_d(t) = ∑_{ℓ=0}^{d} C(d+α, d-ℓ) C(d+β, ℓ)
((t-1)/2)^ℓ ((t+1)/2)^(d-ℓ)` with nonnegative integer parameters `α, β`, [DLMF, eq. (18.5.8)]. -/
@[expose]
public noncomputable def jacobi (α β d : ℕ) : ℝ[X] :=
  ∑ ℓ ∈ Finset.range (d + 1),
    C (((d + α).choose (d - ℓ) * (d + β).choose ℓ : ℕ) : ℝ) *
      (C 2⁻¹ * (X - 1)) ^ ℓ * (C 2⁻¹ * (X + 1)) ^ (d - ℓ)

/-- **Zeros of Jacobi polynomials** ([DLMF, §18.2(vi), Table 18.3.1]): for nonnegative integers
`α, β` and every `n`, all `n` zeros of the Jacobi polynomial
`P^{(α,β)}_n = Polynomial.jacobi α β n` are simple and lie in the interval of orthogonality
`(-1, 1)`. -/
@[expose]
public def JacobiRootsSimpleInIoo : Prop :=
  ∀ α β n : ℕ, (jacobi α β n).roots.card = n ∧ (jacobi α β n).roots.Nodup ∧
    ∀ x ∈ (jacobi α β n).roots, x ∈ Set.Ioo (-1 : ℝ) 1

end Polynomial

end

section

namespace MvPolynomial

section Semifield

variable (σ : Type*) (R : Type*) [Fintype σ] [Semifield R]

/-- The elementary kernel `K_m(z, t) = ∑_{j=0}^m e_j(z) t^{m-j} / (m-j)!`, in the variables
`X (some i)` (the `z_i`) and the new variable `t = X none`, where `e_j = esymm σ R j`. -/
@[expose]
public noncomputable def elementaryKernel (m : ℕ) : MvPolynomial (Option σ) R :=
  ∑ j ∈ Finset.range (m + 1),
    rename some (esymm σ R j) * C ((m - j).factorial : R)⁻¹ * X none ^ (m - j)

end Semifield

end MvPolynomial

end

section

@[expose] public section

namespace LooplessMultigraph

section OrientationSums

open Polynomial

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- The *orientation sum* `O_{G,a}(x)` of a loopless multigraph `G` with exponent vector `a`:
the sum over orientations `h` of `G` of `∏_v Ñ_{a v - 1 + indeg_h(v)}(x)`, where `Ñ_m` is
`shiftedNarayanaPolynomial m`. -/
public noncomputable def orientationSum (G : LooplessMultigraph V E) (a : V → ℕ) : ℝ[X] :=
  ∑ h ∈ Fintype.piFinset (fun e => ({G.src e, G.tgt e} : Finset V)),
    ∏ v, shiftedNarayanaPolynomial (a v - 1 + indegree h v)

/-- The *weighted orientation sum* `O^{b,c}_{G,a}(x)` of a loopless multigraph `G` with exponent
vector `a` and edge weights `b c : E → ℝ`: the sum over orientations `h` of `G` of
`∏_e (b_e [h e = src e] + c_e [h e = tgt e]) * ∏_v Ñ_{a v - 1 + indeg_h(v)}(x)`. -/
public noncomputable def weightedOrientationSum (G : LooplessMultigraph V E) (a : V → ℕ)
    (b c : E → ℝ) : ℝ[X] :=
  ∑ h ∈ Fintype.piFinset (fun e => ({G.src e, G.tgt e} : Finset V)),
    C (∏ e, ((if h e = G.src e then b e else 0) + (if h e = G.tgt e then c e else 0))) *
      ∏ v, shiftedNarayanaPolynomial (a v - 1 + indegree h v)

end OrientationSums

end LooplessMultigraph

end

end

section

namespace Polynomial

variable (R : Type*) [Semiring R]

/-- The *Schröder factor* `R_q(z) = ∑_{j=0}^{q} binom(q+j, q-j) C_j z^j`, where `C_j` is the
`j`-th Catalan number. -/
@[expose]
public noncomputable def schroederFactor (q : ℕ) : R[X] :=
  ∑ j ∈ Finset.range (q + 1), C (((q + j).choose (q - j) * catalan j : ℕ) : R) * X ^ j

end Polynomial

/-- **Schröder trees counted by black vertices** (C. Defant, *Troupes, cumulants, and
stack-sorting*, Example 4.12, citing Gu, Corollary 4.2): for every `q`, the sum of
`X ^ T.numBlackNodes` over the Schröder two-colored binary trees `T ∈ BinaryTree.schroederTrees C`
with `q` vertices is `Polynomial.schroederFactor R q`. -/
@[expose]
public def SchroederTreesBlackGenFunEq.{u, v} : Prop :=
  ∀ (C : Type u) [BinaryTree.TreeColors C] [DecidableEq C] (R : Type v) [Semiring R] (q : ℕ),
    ∑ᶠ T ∈ {T ∈ BinaryTree.schroederTrees C | T.numNodes = q},
      (Polynomial.X : Polynomial R) ^ T.numBlackNodes = Polynomial.schroederFactor R q

open Polynomial

/-- **Refined tree fertility formula for Schröder trees** (C. Defant, *Troupes, cumulants, and
stack-sorting*, Theorem 4.5 with Remark 4.4, for the troupe `BinaryTree.schroederTrees C` and the
insertion-additive statistic `black + 1`): for every `n ≥ 1` and `π ∈ permWords n`, the sum of
`X ^ (black(𝒯) + 1)` over the decreasing labelings `𝒯` of Schröder trees with postorder reading `π`
is the sum over `q ∈ π.validCompositions` of `∏ i, ∑_T X ^ (black(T) + 1)`, where `T` ranges over
the Schröder trees with `q i` vertices. -/
@[expose]
public def SchroederRefinedFertilityFormula.{u, v} : Prop :=
  ∀ (C : Type u) [BinaryTree.TreeColors C] [DecidableEq C] (R : Type v) [CommSemiring R] (n : ℕ),
    1 ≤ n → ∀ π ∈ permWords n,
      ∑ᶠ (𝒯 : BinaryTree (ℕ × C))
          (_ : 𝒯 ∈ BinaryTree.familyDecreasingLabelings (BinaryTree.schroederTrees C) ∧
            (𝒯.map Prod.fst).postorder = π),
          (X : R[X]) ^ (𝒯.skeleton.numBlackNodes + 1) =
        ∑ q ∈ π.validCompositions, ∏ i,
          ∑ᶠ T ∈ {T ∈ BinaryTree.schroederTrees C | T.numNodes = q i},
            (X : R[X]) ^ (T.numBlackNodes + 1)

end

section

section Cited

open MvPolynomial

/-- **Hurwitz's theorem** [BB, Theorem 1.6], [Wagner, Section 2]: for a finite type `σ`, let
`Ω ⊆ ℂ^σ` be open and connected and let `F k : ℂ^σ → ℂ` be analytic and non-vanishing on `Ω`,
converging to `f` uniformly on every compact subset of `Ω`. Then `f` is either non-vanishing on
`Ω` or identically zero on `Ω`. -/
@[expose]
public def IsRealStableLimitClosed (σ : Type*) : Prop :=
  ∀ [Fintype σ] (Ω : Set (σ → ℂ)), IsOpen Ω → IsConnected Ω →
    ∀ (F : ℕ → (σ → ℂ) → ℂ) (f : (σ → ℂ) → ℂ),
      (∀ k, AnalyticOnNhd ℂ (F k) Ω) → (∀ k, ∀ z ∈ Ω, F k z ≠ 0) →
      (∀ K ⊆ Ω, IsCompact K → TendstoUniformlyOn F f Filter.atTop K) →
      (∀ z ∈ Ω, f z ≠ 0) ∨ ∀ z ∈ Ω, f z = 0

end Cited

end
