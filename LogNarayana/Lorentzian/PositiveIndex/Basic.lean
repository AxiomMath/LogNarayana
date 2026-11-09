/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module
public import LogNarayana.Lorentzian.PositiveIndex.Defs

/-!
# Properties of the positive index of a square matrix

The positive index `p(A)` of a square matrix `A` is the largest dimension of a subspace on
which the quadratic form `v ↦ vᵀ A v` is positive definite (`Matrix.posIndex`). This file
proves its basic properties.

* Congruence invariance: `v ↦ P v` carries `Pᵀ A P`-positive subspaces onto `A`-positive
  subspaces of the same dimension, so `p(Pᵀ A P) = p(A)` for `P` invertible.
* Adjoining a unit diagonal block: the quadratic form of `fromBlocks A 0 0 1` is
  `(u, t) ↦ uᵀ A u + t²`. If `W` is `A`-positive then `W × R` is positive for the block
  matrix; conversely, if `W'` is positive for it, then the `u` with `(u, 0) ∈ W'` form an
  `A`-positive subspace of codimension at most one in `W'`. Hence the positive index grows
  by exactly one.
* Spectral description: in an orthonormal eigenbasis `(φ_k)` of a real symmetric matrix,
  `vᵀ A v = ∑ λ_k c_k²` for `v = ∑ c_k φ_k`. The span of the eigenvectors with positive
  eigenvalue is `A`-positive, while the span of the others meets every `A`-positive subspace
  trivially, so `p(A)` is the number of positive eigenvalues.
* Reverse Cauchy–Schwarz: if `p(A) ≤ 1`, `A` is symmetric and `uᵀ A u > 0`, then
  `(uᵀ A u)(vᵀ A v) ≤ (uᵀ A v)²`; otherwise the binary form `as² + 2bst + ct²` with
  `a = uᵀ A u`, `b = uᵀ A v`, `c = vᵀ A v` is positive definite and `span {u, v}` is a
  two-dimensional `A`-positive subspace.
* `2 × 2` matrices: for `a, c ≥ 0`, the matrix `!![a, b; b, c]` has at most one positive
  eigenvalue exactly when `a * c ≤ b ^ 2`, since the whole plane is positive for it exactly
  when `a > 0` and `b² < ac`.

## Main results

* `Matrix.posIndex_transpose_mul_mul`: `(Pᵀ * A * P).posIndex = A.posIndex` for `P`
  invertible.
* `Matrix.posIndex_fromBlocks_one`: `(fromBlocks A 0 0 1).posIndex = A.posIndex + 1`.
* `Matrix.IsHermitian.posIndex_eq_card_pos_eigenvalues`: for a real symmetric matrix,
  `p(A) = #{k | 0 < λ_k}`.
* `Matrix.HasAtMostOnePosEigenvalue.mul_le_sq_dotProduct_mulVec`: the reverse Cauchy–Schwarz
  inequality `(uᵀ A u)(vᵀ A v) ≤ (uᵀ A v)²`.
* `Matrix.hasAtMostOnePosEigenvalue_fin_two_iff`: `!![a, b; b, c]` has at most one
  positive eigenvalue if and only if `a * c ≤ b ^ 2`, for `a, c ≥ 0`.

## Implementation notes

The paper works over `ℝ`. Congruence invariance is stated over any commutative ring with a
partial order, with invertibility of `P` expressed as `IsUnit P`; the block lemma over any
linearly ordered field. In the block lemma the new index `∗ ∉ σ` is modelled by the summand
`Unit` of `σ ⊕ Unit`. Over `ℝ` a matrix is Hermitian exactly when it is symmetric, and the
spectral description takes `Matrix.IsHermitian` because `Matrix.IsHermitian.eigenvalues` does.
-/

namespace Matrix

section posDims

variable {σ R : Type*} [Fintype σ]

/-- The set of dimensions of `A`-positive subspaces, whose supremum is `A.posIndex`. -/
private abbrev posDims [CommRing R] [PartialOrder R] (A : Matrix σ σ R) : Set ℕ :=
  {n | ∃ W : Submodule R (σ → R), A.IsPositiveSubspace W ∧ Module.finrank R W = n}

variable [Field R] [PartialOrder R]

private lemma bddAbove_posDims (A : Matrix σ σ R) : BddAbove (posDims A) :=
  ⟨Fintype.card σ, by rintro _ ⟨W, -, rfl⟩; simpa using Submodule.finrank_le W⟩

private lemma nonempty_posDims (A : Matrix σ σ R) : (posDims A).Nonempty :=
  ⟨0, ⊥, fun _ hv hne => absurd ((Submodule.mem_bot R).1 hv) hne, finrank_bot R _⟩

private lemma posIndex_mem_posDims (A : Matrix σ σ R) : A.posIndex ∈ posDims A :=
  Nat.sSup_mem (nonempty_posDims A) (bddAbove_posDims A)

/-- Every `A`-positive subspace has dimension at most the positive index of `A`. -/
private lemma finrank_le_posIndex {A : Matrix σ σ R} {W : Submodule R (σ → R)}
    (hW : A.IsPositiveSubspace W) : Module.finrank R W ≤ A.posIndex :=
  le_csSup (bddAbove_posDims A) ⟨W, hW, rfl⟩

end posDims

section congruence

variable {σ R : Type*} [Fintype σ] [DecidableEq σ] [CommRing R] [PartialOrder R]

omit [DecidableEq σ] [PartialOrder R] in
private lemma dotProduct_transpose_mul_mul_mulVec (A P : Matrix σ σ R) (v : σ → R) :
    v ⬝ᵥ ((Pᵀ * A * P) *ᵥ v) = (P *ᵥ v) ⬝ᵥ (A *ᵥ (P *ᵥ v)) := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec v, vecMul_transpose]

/-- The image of a `Pᵀ A P`-positive subspace under `v ↦ P v` is `A`-positive, and has the
same dimension since `P` is a unit. -/
private lemma posDims_transpose_mul_mul_subset (A : Matrix σ σ R) (u : (Matrix σ σ R)ˣ) :
    posDims ((u : Matrix σ σ R)ᵀ * A * (u : Matrix σ σ R)) ⊆ posDims A := by
  rintro n ⟨W, hW, rfl⟩
  let e : (σ → R) ≃ₗ[R] (σ → R) :=
    { toLinearMap := (u : Matrix σ σ R).mulVecLin
      invFun := ((u⁻¹ : (Matrix σ σ R)ˣ) : Matrix σ σ R).mulVec
      left_inv := fun v => by simp [mulVec_mulVec]
      right_inv := fun v => by simp [mulVec_mulVec] }
  refine ⟨W.map (e : (σ → R) →ₗ[R] (σ → R)), ?_, LinearEquiv.finrank_map_eq e W⟩
  rintro _ ⟨v, hv, rfl⟩ hne
  simpa [e, dotProduct_transpose_mul_mul_mulVec] using
    hW v hv (by rintro rfl; exact hne (map_zero _))

/-- The positive index is invariant under congruence by an invertible matrix:
`p(Pᵀ A P) = p(A)`. Applying the inclusion of positive dimensions to `P` and to `P⁻¹`
shows that `Pᵀ A P` and `A` have the same positive-subspace dimensions. -/
@[lognarayana "lem_pos_eig_congruence"]
public theorem posIndex_transpose_mul_mul (A P : Matrix σ σ R) (hP : IsUnit P) :
    (Pᵀ * A * P).posIndex = A.posIndex := by
  obtain ⟨u, rfl⟩ := hP
  refine congrArg sSup (Set.Subset.antisymm (posDims_transpose_mul_mul_subset A u) ?_)
  have h :=
    posDims_transpose_mul_mul_subset ((u : Matrix σ σ R)ᵀ * A * (u : Matrix σ σ R)) u⁻¹
  rwa [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← transpose_mul, Matrix.mul_assoc,
    Units.mul_inv, transpose_one, Matrix.one_mul, Matrix.mul_one] at h

end congruence

section fromBlocks

variable {σ R : Type*} [Fintype σ] [Field R] [LinearOrder R] [IsStrictOrderedRing R]

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- The quadratic form of `fromBlocks A 0 0 1` splits as `uᵀ A u + t²`. -/
private lemma dotProduct_fromBlocks_one_mulVec (A : Matrix σ σ R) (v : σ ⊕ Unit → R) :
    v ⬝ᵥ (fromBlocks A 0 0 (1 : Matrix Unit Unit R) *ᵥ v) =
      (v ∘ Sum.inl) ⬝ᵥ (A *ᵥ (v ∘ Sum.inl)) + v (Sum.inr ()) * v (Sum.inr ()) := by
  classical
  rw [fromBlocks_mulVec]
  simp [dotProduct, Fintype.sum_sum_type]

omit [Fintype σ] [LinearOrder R] [IsStrictOrderedRing R] in
private lemma finrank_prod_top [Finite σ] (W : Submodule R (σ → R)) :
    Module.finrank R (W.prod (⊤ : Submodule R (Unit → R))) = Module.finrank R W + 1 := by
  let f : W.prod (⊤ : Submodule R (Unit → R)) ≃ₗ[R] W × (⊤ : Submodule R (Unit → R)) :=
    { toFun := fun x => (⟨x.1.1, x.2.1⟩, ⟨x.1.2, trivial⟩)
      invFun := fun p => ⟨(p.1.1, p.2.1), p.1.2, trivial⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [f.finrank_eq, Module.finrank_prod, finrank_top, Module.finrank_fintype_fun_eq_card,
    Fintype.card_unit]

/-- Lower bound: if `W` is `A`-positive then `W × R` is positive for the block matrix. -/
private lemma succ_mem_posDims_fromBlocks (A : Matrix σ σ R) {n : ℕ} (hn : n ∈ posDims A) :
    n + 1 ∈ posDims (fromBlocks A 0 0 (1 : Matrix Unit Unit R)) := by
  obtain ⟨W, hW, rfl⟩ := hn
  let e := LinearEquiv.sumArrowLequivProdArrow σ Unit R R
  refine ⟨(W.prod ⊤).map e.symm.toLinearMap, ?_, ?_⟩
  · rintro _ ⟨p, hp, rfl⟩ hne
    rw [dotProduct_fromBlocks_one_mulVec]
    change p.1 ⬝ᵥ (A *ᵥ p.1) + p.2 () * p.2 () > 0
    by_cases hp1 : p.1 = 0
    · have hp2 : p.2 () ≠ 0 := by
        intro h0
        apply hne
        have : p = 0 := Prod.ext hp1 (funext fun u => by cases u; exact h0)
        simp [this]
      rw [hp1]
      simpa using mul_self_pos.2 hp2
    · exact add_pos_of_pos_of_nonneg (hW _ hp.1 hp1) (mul_self_nonneg _)
  · rw [LinearEquiv.finrank_map_eq, finrank_prod_top]

omit [IsStrictOrderedRing R] in
/-- Upper bound: if `W'` is positive for the block matrix, the vectors `u` with
`(u, 0) ∈ W'` form an `A`-positive subspace of codimension at most one in `W'`. -/
private lemma exists_mem_posDims_le_succ (A : Matrix σ σ R) {m : ℕ}
    (hm : m ∈ posDims (fromBlocks A 0 0 (1 : Matrix Unit Unit R))) :
    ∃ n ∈ posDims A, m ≤ n + 1 := by
  obtain ⟨W', hW', rfl⟩ := hm
  let e := LinearEquiv.sumArrowLequivProdArrow σ Unit R R
  let L : (σ → R) →ₗ[R] (σ ⊕ Unit → R) := e.symm.toLinearMap ∘ₗ LinearMap.inl R _ _
  have hLinj : Function.Injective L := e.symm.injective.comp LinearMap.inl_injective
  have hL1 (u : σ → R) : L u ∘ Sum.inl = u := by
    ext i; simp [L, e, LinearEquiv.sumArrowLequivProdArrow_symm_apply_inl]
  have hL2 (u : σ → R) : L u (Sum.inr ()) = 0 := by
    simp [L, e, LinearEquiv.sumArrowLequivProdArrow_symm_apply_inr]
  refine ⟨Module.finrank R (W'.comap L), ⟨W'.comap L, ?_, rfl⟩, ?_⟩
  · intro u hu hne
    have h := hW' (L u) hu (fun h0 => hne (hLinj (h0.trans (map_zero L).symm)))
    rwa [dotProduct_fromBlocks_one_mulVec, hL1, hL2, mul_zero, add_zero] at h
  · have hmap : Module.finrank R ((W'.comap L).map L) = Module.finrank R (W'.comap L) :=
      LinearEquiv.finrank_eq (Submodule.equivMapOfInjective L hLinj _).symm
    rw [Submodule.map_comap_eq, inf_comm] at hmap
    have hsum := Submodule.finrank_sup_add_finrank_inf_eq W' (LinearMap.range L)
    have hsup : Module.finrank R ↥(W' ⊔ LinearMap.range L) ≤ Fintype.card σ + 1 := by
      simpa using Submodule.finrank_le (W' ⊔ LinearMap.range L)
    have hrange : Module.finrank R (LinearMap.range L) = Fintype.card σ := by
      rw [LinearMap.finrank_range_of_inj hLinj, Module.finrank_fintype_fun_eq_card]
    omega

/-- Adjoining a new index with diagonal entry `1` and no off-diagonal entries raises the
positive index by one: `p(fromBlocks A 0 0 1) = p(A) + 1`. -/
@[lognarayana "lem_pos_eig_block_one"]
public theorem posIndex_fromBlocks_one (A : Matrix σ σ R) :
    (fromBlocks A 0 0 (1 : Matrix Unit Unit R)).posIndex = A.posIndex + 1 := by
  refine le_antisymm (csSup_le (nonempty_posDims _) fun m hm => ?_)
    (le_csSup (bddAbove_posDims _) (succ_mem_posDims_fromBlocks A (posIndex_mem_posDims A)))
  obtain ⟨n, hn, hle⟩ := exists_mem_posDims_le_succ A hm
  exact hle.trans (Nat.add_le_add_right (le_csSup (bddAbove_posDims A) hn) 1)

end fromBlocks

section eigenvalues

variable {σ : Type*} [Fintype σ] [DecidableEq σ] {A : Matrix σ σ ℝ} (hA : A.IsHermitian)

/-- The span of the eigenvectors of `A` indexed by `{k // p k}`. -/
private noncomputable abbrev eigenSpan (p : σ → Prop) : Submodule ℝ (σ → ℝ) :=
  Submodule.span ℝ (Set.range fun k : {k // p k} => ⇑(hA.eigenvectorBasis k))

/-- The eigenvectors of a real symmetric matrix are orthonormal for the dot product. -/
private lemma eigenvectorBasis_dotProduct {p : σ → Prop} (i j : {k // p k}) :
    ⇑(hA.eigenvectorBasis i) ⬝ᵥ ⇑(hA.eigenvectorBasis j) = if i = j then 1 else 0 := by
  have := hA.eigenvectorBasis.inner_eq_ite i j
  rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct_comm] at this
  exact this.trans (if_congr Subtype.ext_iff.symm rfl rfl)

/-- The quadratic form of `A` on a combination of its eigenvectors. -/
private lemma dotProduct_mulVec_sum_eigenvectorBasis {p : σ → Prop} [DecidablePred p]
    (c : {k // p k} → ℝ) :
    (∑ i, c i • ⇑(hA.eigenvectorBasis i)) ⬝ᵥ (A *ᵥ ∑ i, c i • ⇑(hA.eigenvectorBasis i)) =
      ∑ i : {k // p k}, hA.eigenvalues i * c i ^ 2 := by
  simp only [mulVec_sum, mulVec_smul, hA.mulVec_eigenvectorBasis, sum_dotProduct,
    dotProduct_sum, smul_dotProduct, dotProduct_smul, eigenvectorBasis_dotProduct, smul_eq_mul,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  exact Finset.sum_congr rfl fun i _ => by ring

private lemma finrank_eigenSpan (p : σ → Prop) [DecidablePred p] :
    Module.finrank ℝ (eigenSpan hA p) = Fintype.card {k // p k} := by
  refine finrank_span_eq_card (Fintype.linearIndependent_iff.2 fun g hg j => ?_)
  simpa [sum_dotProduct, eigenvectorBasis_dotProduct] using
    congrArg (· ⬝ᵥ ⇑(hA.eigenvectorBasis j)) hg

private lemma isPositiveSubspace_eigenSpan :
    A.IsPositiveSubspace (eigenSpan hA fun k => 0 < hA.eigenvalues k) := by
  intro v hv hv0
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hv
  rw [dotProduct_mulVec_sum_eigenvectorBasis]
  obtain ⟨i, hi⟩ : ∃ i, c i ≠ 0 := by
    by_contra! h
    simp [h] at hv0
  exact Finset.sum_pos' (fun i _ => mul_nonneg i.2.le (sq_nonneg _))
    ⟨i, Finset.mem_univ _, mul_pos i.2 (by positivity)⟩

/-- The span of the eigenvectors with nonpositive eigenvalue meets every `A`-positive
subspace trivially. -/
private lemma disjoint_eigenSpan {W : Submodule ℝ (σ → ℝ)} (hW : A.IsPositiveSubspace W) :
    Disjoint W (eigenSpan hA fun k => ¬ 0 < hA.eigenvalues k) := by
  refine Submodule.disjoint_def.2 fun x hxW hxN => by_contra fun hx0 => ?_
  have hpos := hW x hxW hx0
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hxN
  rw [dotProduct_mulVec_sum_eigenvectorBasis] at hpos
  exact hpos.not_ge <| Finset.sum_nonpos fun i _ =>
    mul_nonpos_of_nonpos_of_nonneg (not_lt.1 i.2) (sq_nonneg _)

/-- For a real symmetric matrix `A`, the positive index `p(A)` equals the number of
positive eigenvalues of `A`, counted with multiplicity. -/
@[lognarayana "lem_pos_index_eq_eig_count"]
public theorem IsHermitian.posIndex_eq_card_pos_eigenvalues {A : Matrix σ σ ℝ}
    (hA : A.IsHermitian) : A.posIndex = Fintype.card {k // 0 < hA.eigenvalues k} := by
  refine le_antisymm (csSup_le (nonempty_posDims A) ?_)
    (finrank_eigenSpan hA (fun k => 0 < hA.eigenvalues k) ▸
      finrank_le_posIndex (isPositiveSubspace_eigenSpan hA))
  rintro n ⟨W, hW, rfl⟩
  have := Submodule.finrank_add_finrank_le_of_disjoint (disjoint_eigenSpan hA hW)
  rw [Module.finrank_fintype_fun_eq_card, finrank_eigenSpan, Fintype.card_subtype_compl] at this
  have := Fintype.card_subtype_le fun k => 0 < hA.eigenvalues k
  omega

end eigenvalues

section reverseCauchySchwarz

variable {σ : Type*} [Fintype σ]

/-- The quadratic form of a symmetric `A` on `s • u + t • v`. -/
private lemma dotProduct_mulVec_smul_add_smul {A : Matrix σ σ ℝ} (hsymm : A.IsSymm)
    (u v : σ → ℝ) (s t : ℝ) :
    (s • u + t • v) ⬝ᵥ A *ᵥ (s • u + t • v) =
      (u ⬝ᵥ A *ᵥ u) * s ^ 2 + 2 * (u ⬝ᵥ A *ᵥ v) * s * t + (v ⬝ᵥ A *ᵥ v) * t ^ 2 := by
  have hvu : v ⬝ᵥ A *ᵥ u = u ⬝ᵥ A *ᵥ v := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hsymm.eq, dotProduct_comm]
  simp only [mulVec_add, mulVec_smul, add_dotProduct, dotProduct_add, smul_dotProduct,
    dotProduct_smul, smul_eq_mul, hvu]
  ring

/-- A positive definite binary form `as² + 2bst + ct²` is nonpositive only at `(0, 0)`:
`a (as² + 2bst + ct²) = (as + bt)² + (ac - b²) t²`. -/
private lemma eq_zero_of_binary_form_nonpos {a b c s t : ℝ} (ha : 0 < a) (hb : b ^ 2 < a * c)
    (h : a * s ^ 2 + 2 * b * s * t + c * t ^ 2 ≤ 0) : s = 0 ∧ t = 0 := by
  have ht : t ^ 2 ≤ 0 := by
    nlinarith [sq_nonneg (a * s + b * t), mul_nonpos_of_nonneg_of_nonpos ha.le h]
  obtain rfl : t = 0 := pow_eq_zero_iff two_ne_zero |>.1 (ht.antisymm (sq_nonneg t))
  exact ⟨pow_eq_zero_iff two_ne_zero |>.1 (by nlinarith [sq_nonneg s]), rfl⟩

/-- **Reverse Cauchy–Schwarz.** If `A` is a real symmetric matrix with at most one positive
eigenvalue and `0 < uᵀ A u`, then `(uᵀ A u)(vᵀ A v) ≤ (uᵀ A v)²` for every `v`. Otherwise
`span {u, v}` would be a two-dimensional `A`-positive subspace. -/
@[lognarayana "lem_pos_eig_reverse_cs"]
public theorem HasAtMostOnePosEigenvalue.mul_le_sq_dotProduct_mulVec {A : Matrix σ σ ℝ}
    (hsymm : A.IsSymm) (hA : A.HasAtMostOnePosEigenvalue) {u : σ → ℝ} (hu : 0 < u ⬝ᵥ A *ᵥ u)
    (v : σ → ℝ) :
    (u ⬝ᵥ A *ᵥ u) * (v ⬝ᵥ A *ᵥ v) ≤ (u ⬝ᵥ A *ᵥ v) ^ 2 := by
  by_contra! hlt
  have hli : LinearIndependent ℝ ![u, v] := by
    refine LinearIndependent.pair_iff.2 fun s t hst => eq_zero_of_binary_form_nonpos hu hlt ?_
    simp [← dotProduct_mulVec_smul_add_smul hsymm, hst]
  have hpos : A.IsPositiveSubspace (Submodule.span ℝ {u, v}) := by
    intro w hw hne
    obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.1 hw
    rw [dotProduct_mulVec_smul_add_smul hsymm]
    by_contra! hle
    obtain ⟨rfl, rfl⟩ := eq_zero_of_binary_form_nonpos hu hlt hle
    simp at hne
  have := finrank_le_posIndex hpos
  rw [← Matrix.range_cons_cons_empty, finrank_span_eq_card hli] at this
  simp at this
  omega

end reverseCauchySchwarz

section finTwo

/-- The quadratic form of `!![a, b; b, c]`. -/
private lemma dotProduct_mulVec_fin_two (a b c : ℝ) (v : Fin 2 → ℝ) :
    v ⬝ᵥ (!![a, b; b, c] : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ v =
      a * v 0 ^ 2 + 2 * b * v 0 * v 1 + c * v 1 ^ 2 := by
  simp [dotProduct, Fin.sum_univ_two, mulVec]
  ring

/-- The positive index of `A` is less than the dimension of the space exactly when the whole
space is not `A`-positive. -/
private lemma posIndex_lt_card_iff {σ R : Type*} [Fintype σ] [Field R] [PartialOrder R]
    (A : Matrix σ σ R) : A.posIndex < Fintype.card σ ↔ ¬ A.IsPositiveSubspace ⊤ := by
  refine ⟨fun h htop => ?_, fun h => ?_⟩
  · have := finrank_le_posIndex htop
    simp only [finrank_top, Module.finrank_fintype_fun_eq_card] at this
    exact absurd h (not_lt.2 this)
  · by_contra! hle
    obtain ⟨W, hW, hWn⟩ := posIndex_mem_posDims A
    refine h (Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le W) ?_) ▸ hW)
    rwa [Module.finrank_fintype_fun_eq_card, hWn]

/-- The whole plane is `!![a, b; b, c]`-positive exactly when `a > 0` and `b² < ac`. -/
private lemma isPositiveSubspace_top_fin_two_iff {a b c : ℝ} :
    (!![a, b; b, c] : Matrix (Fin 2) (Fin 2) ℝ).IsPositiveSubspace ⊤ ↔
      0 < a ∧ b ^ 2 < a * c := by
  refine ⟨fun h => ?_, fun ⟨ha, hlt⟩ v _ hv => ?_⟩
  · have h1 := h ![1, 0] trivial (by simp)
    rw [dotProduct_mulVec_fin_two] at h1
    simp only [Fin.isValue, cons_val_zero, one_pow, mul_one, cons_val_one, cons_val_fin_one,
      mul_zero, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at h1
    have h2 := h ![-b, a] trivial (fun e => h1.ne' (by simpa using congrFun e 1))
    rw [dotProduct_mulVec_fin_two] at h2; simp at h2
    exact ⟨h1, by nlinarith⟩
  · rw [dotProduct_mulVec_fin_two]
    by_contra! hle
    obtain ⟨h0, h1⟩ := eq_zero_of_binary_form_nonpos ha hlt hle
    exact hv (funext fun i => by fin_cases i <;> simp [h0, h1])

/-- For `a ≥ 0`, the real symmetric matrix `!![a, b; b, c]` has at most one positive eigenvalue if
and only if `a * c ≤ b ^ 2`. -/
@[lognarayana "lem_two_by_two_pos_index"]
public theorem hasAtMostOnePosEigenvalue_fin_two_iff {a b c : ℝ} (ha : 0 ≤ a) :
    (!![a, b; b, c] : Matrix (Fin 2) (Fin 2) ℝ).HasAtMostOnePosEigenvalue ↔ a * c ≤ b ^ 2 := by
  rw [HasAtMostOnePosEigenvalue, ← Nat.lt_succ_iff]
  change _ < Fintype.card (Fin 2) ↔ _
  rw [posIndex_lt_card_iff, isPositiveSubspace_top_fin_two_iff]
  constructor
  · intro h; by_contra! hlt
    exact h ⟨ha.lt_of_ne (by rintro rfl; nlinarith [sq_nonneg b]), hlt⟩
  · rintro h ⟨-, hlt⟩; linarith

end finTwo

end Matrix
