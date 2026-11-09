/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module
public import LogNarayana.BinaryTree.Colored.Basic

/-!
# Troupes defined by local rules

Let `P ⊆ 𝔗 × C` be a local rule which admits the pair `(bin, black)` and no other pair
`(bin, c)`. Then the family `𝐔_P` of colored binary plane trees all of whose vertices satisfy
the rule is a troupe. Black-peakedness follows from the monotonicity of `localRuleFamily` in the
rule. For closure under insertion, the new vertex `v*` of `∇_v(T₁, T₂)` has a nonempty left
subtree and a nonempty right subtree `T₂`, so it is a black binary vertex, admitted by `P`;
every other vertex keeps its color and its type, because an insertion is never empty.

The black trees `𝐁`, the families `𝐔_{X_L,X_a,X_b}` colored according to vertex type, and the
Schröder two-colored binary trees `𝐒` are all cut out by such rules, hence are troupes.

## Main results

* `BinaryTree.isTroupe_localRuleFamily`: `𝐔_P` is a troupe when `(bin, black) ∈ P` and
  `(bin, c) ∉ P` for every color `c ≠ black`.
* `BinaryTree.isTroupe_blackTrees`: `𝐁` is a troupe.
* `BinaryTree.isTroupe_localColorFamily`: `𝐔_{X_L,X_a,X_b}` is a troupe.
* `BinaryTree.isTroupe_schroederTrees`: `𝐒` is a troupe.

## References

* [LogNarayana] *Log-Concavity in Narayana Transforms and Stack-Sorting Fibers*, Sections 5–6.
-/

public section

namespace BinaryTree

variable {C : Type*} [TreeColors C]

omit [TreeColors C] in
private lemma node_mem_localRuleFamily {P : Set (VertexType × C)} {a : C}
    {l r : BinaryTree C} :
    node a l r ∈ localRuleFamily P ↔
      (vertexType l r, a) ∈ P ∧ l ∈ localRuleFamily P ∧ r ∈ localRuleFamily P :=
  Iff.rfl

omit [TreeColors C] in
/-- `localRuleFamily` is monotone in the local rule. -/
private lemma localRuleFamily_mono {P Q : Set (VertexType × C)} (hPQ : P ⊆ Q) :
    ∀ T : BinaryTree C, T ∈ localRuleFamily P → T ∈ localRuleFamily Q
  | .nil, _ => trivial
  | .node _ l r, ⟨h, hl, hr⟩ =>
    ⟨hPQ h, localRuleFamily_mono hPQ l hl, localRuleFamily_mono hPQ r hr⟩

/-- An insertion is never the empty tree. -/
private lemma insertion_ne_nil :
    ∀ (T₁ : BinaryTree C) (v : Fin T₁.numNodes) (T₂ : BinaryTree C), insertion T₁ v T₂ ≠ .nil
  | .nil, v, _ => v.elim0
  | .node a l r, v, T₂ => by
    unfold insertion
    split_ifs <;> simp

omit [TreeColors C] in
/-- The type of a vertex does not change when its nonempty left subtree is replaced by another
nonempty one. -/
private lemma vertexType_congr_left {l l' : BinaryTree C} (hl : l ≠ .nil) (hl' : l' ≠ .nil)
    (r : BinaryTree C) : vertexType l r = vertexType l' r := by
  cases l <;> cases l' <;> cases r <;> simp_all [vertexType]

omit [TreeColors C] in
/-- The type of a vertex does not change when its nonempty right subtree is replaced by another
nonempty one. -/
private lemma vertexType_congr_right (l : BinaryTree C) {r r' : BinaryTree C} (hr : r ≠ .nil)
    (hr' : r' ≠ .nil) : vertexType l r = vertexType l r' := by
  cases l <;> cases r <;> cases r' <;> simp_all [vertexType]

/-- The insertion condition for `localRuleFamily P` when `P` admits black binary vertices: the
new vertex is black binary, and every other vertex keeps its color and type. -/
private lemma insertion_mem_localRuleFamily_iff {P : Set (VertexType × C)}
    (hblack : (VertexType.binary, TreeColors.black) ∈ P) :
    ∀ (T₁ : BinaryTree C) (v : Fin T₁.numNodes) {T₂ : BinaryTree C}, T₂ ≠ .nil →
      (T₁ ∈ localRuleFamily P ∧ T₂ ∈ localRuleFamily P ↔
        insertion T₁ v T₂ ∈ localRuleFamily P)
  | .nil, v, _, _ => v.elim0
  | .node a l r, v, T₂, h₂ => by
    unfold insertion
    split_ifs with h₀ h
    · cases T₂ with
      | nil => exact absurd rfl h₂
      | node => simp [node_mem_localRuleFamily, vertexType, hblack]
    · have hl : l ≠ .nil := by rintro rfl; simp [numNodes] at h
      rw [node_mem_localRuleFamily, node_mem_localRuleFamily,
        ← insertion_mem_localRuleFamily_iff hblack _ _ h₂,
        ← vertexType_congr_left hl (insertion_ne_nil _ _ _)]
      tauto
    · have hr : r ≠ .nil := by
        rintro rfl
        have := v.isLt
        simp [numNodes] at this h
        omega
      rw [node_mem_localRuleFamily, node_mem_localRuleFamily,
        ← insertion_mem_localRuleFamily_iff hblack _ _ h₂,
        ← vertexType_congr_right l hr (insertion_ne_nil _ _ _)]
      tauto

/-- If a local rule `P` admits the pair `(bin, black)` and no pair `(bin, c)` with `c ≠ black`,
then the family `𝐔_P` it cuts out is a troupe. -/
@[lognarayana "lem_local_rule_troupe"]
theorem isTroupe_localRuleFamily {P : Set (VertexType × C)}
    (hblack : (VertexType.binary, TreeColors.black) ∈ P)
    (hnot : ∀ c : C, c ≠ TreeColors.black → (VertexType.binary, c) ∉ P) :
    IsTroupe (localRuleFamily P) := by
  refine ⟨localRuleFamily_mono ?_,
    fun T₁ v _ => insertion_mem_localRuleFamily_iff hblack T₁ v⟩
  rintro ⟨t, c⟩ h (rfl : t = .binary)
  exact not_not.mp fun hc => hnot c hc h

/-- The set `𝐁` of binary plane trees (all vertices black) is a troupe. -/
@[lognarayana "lem_black_troupe_is_troupe"]
theorem isTroupe_blackTrees (C : Type*) [TreeColors C] :
    IsTroupe (blackTrees C) :=
  isTroupe_localRuleFamily (by simp) fun _ hc h => hc (Set.mem_singleton_iff.mp h.2)

/-- For all sets of colors `X_L, X_a, X_b`, the family `𝐔_{X_L,X_a,X_b}` is a troupe. -/
@[lognarayana "lem_local_colors_is_troupe"]
theorem isTroupe_localColorFamily (X_L X_a X_b : Set C) :
    IsTroupe (localColorFamily X_L X_a X_b) :=
  isTroupe_localRuleFamily (by simp) fun _ hc h => hc (by simpa using h)

/-- The set `𝐒` of Schröder two-colored binary trees is a troupe. -/
@[lognarayana "lem_schroeder_is_troupe"]
theorem isTroupe_schroederTrees (C : Type*) [TreeColors C] :
    IsTroupe (schroederTrees C) :=
  isTroupe_localRuleFamily (by simp) fun _ hc h => hc (by simpa using h)

end BinaryTree

end
