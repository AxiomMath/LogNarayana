/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib
public import LogNarayana.Attr
public import LogNarayana.Nestohedron.QuadraticReplacement.Defs
public import LogNarayana.AuxiliaryDefinitions

/-!
# Noncrossing partitions and restricted refinements

A partition `ρ` of a finite set `A ⊆ ℤ` has `|ρ|` blocks, and it is *noncrossing* if there are
no `a < b < c < d` with `a, c` in one block and `b, d` in another; `NC(A)` is the set of
noncrossing partitions of `A` and `NC(n) = NC([n])`. For `n, k, a ≥ 1` with `n ≥ a k`, the
*restricted noncrossing refinement polynomial* is
`R^{(a)}_{n,k}(x) = ∑_τ ∑_{σ ∈ NC(n), σ ≤ τ} x^{|σ|}`, and its deformation is
`R^{(a),λ}_{n,k}(x) = ∑_τ ∏_{B ∈ τ} N^{(λ)}_{|B|}(x)`, both sums running over the noncrossing
partitions `τ ∈ NC(n)` with `k` blocks, each of size at least `a`.

The enumerative input on `NC(n)` is cited: Kreweras' count of noncrossing partitions with
prescribed block sizes and Edelman's count of two-element chains, each stated as a proposition
to be taken as a hypothesis by the results using it.

## Main definitions

* `Finpartition.blockCount P`: the number of blocks `|P|` of a finite partition `P`.
* `Finpartition.IsNoncrossing P`: the partition `P` of a finset of a linear order is
  noncrossing.
* `restrictedNoncrossingRefinementPoly R s a k`: the polynomial `R^{(a)}_{n,k}` on the ground
  set `s`.
* `restrictedNoncrossingDeformedNarayanaPoly R lam s a k`: the polynomial `R^{(a),λ}_{n,k}` on
  the ground set `s`.
* `Finpartition.KrewerasBlockSizeCount`: Kreweras' formula [Kreweras1972].
* `Finpartition.EdelmanChainCount`: Edelman's chain count [Edelman1980].

## Implementation notes

A partition of `A` is a `Finpartition A`, and `NC(A)` is the filter of
`Finpartition.IsNoncrossing` on it; the paper's `[n]` is `Finset.Icc 1 n`. The refinement
order `σ ≤ τ` is the partial order of `Finpartition`. The hypotheses `n, k, a ≥ 1` and
`n ≥ a k` are not needed to define the polynomials and are omitted, and the coefficients lie in
an arbitrary (commutative) semiring, the paper's `ℝ[x]` being the case `R = ℝ`. The cited
counts are stated cleared of their denominators, as identities in `ℕ`.

## References

* [LogNarayana], Section 7.
* [Kreweras1972] G. Kreweras, *Sur les partitions non croisées d'un cycle*, Discrete Math. 1
  (1972).
* [Edelman1980] P. H. Edelman, *Chain enumeration and non-crossing partitions*, Discrete Math.
  31 (1980), 171–180.
-/


namespace Finpartition

variable {α : Type*} [Lattice α] [OrderBot α] {a : α}

end Finpartition


namespace Finpartition

variable {α : Type*} [LinearOrder α] {s : Finset α}

end Finpartition


section

open Polynomial

variable {α : Type*} [LinearOrder α]

end


namespace Finpartition

open Finset

end Finpartition


namespace Finpartition

open Finset

/-- **Edelman's chain count** (Edelman 1980): for `1 ≤ k ≤ ℓ ≤ n`, the number of pairs
`(σ, τ)` of noncrossing partitions of `[n] = Finset.Icc 1 n` with `σ ≤ τ`,
`τ.blockCount = k` and `σ.blockCount = ℓ`, multiplied by `n`, equals
`n.choose (k - 1) * n.choose (ℓ - k) * n.choose (n - ℓ)`. -/
@[expose, lognarayana "thm_ext_edelman_chains"]
public def EdelmanChainCount : Prop :=
  ∀ (n k ℓ : ℕ), 1 ≤ k → k ≤ ℓ → ℓ ≤ n →
    open scoped Classical in
    (univ.filter (fun p : Finpartition (Icc 1 n) × Finpartition (Icc 1 n) =>
        p.1.IsNoncrossing ∧ p.2.IsNoncrossing ∧ p.1 ≤ p.2 ∧
          p.2.blockCount = k ∧ p.1.blockCount = ℓ)).card * n =
      n.choose (k - 1) * n.choose (ℓ - k) * n.choose (n - ℓ)

end Finpartition
