/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module
public import Mathlib
public import LogNarayana.Attr
public import LogNarayana.AuxiliaryDefinitions

/-!
# Laminar families and laminar matroids

The definitions documented here are stated in `LogNarayana.Definitions` and
`LogNarayana.AuxiliaryDefinitions`, which this module imports.

A family `𝒜 = (A_k)_{k ∈ K}` of subsets of a set `E` is *laminar* if any two of its members that
intersect are nested: whenever `A_k ∩ A_{k'} ≠ ∅`, either `A_k ⊆ A_{k'}` or `A_{k'} ⊆ A_k`.
Repetitions are allowed, so a laminar family is in general a multiset of subsets.

Given capacities `c : K → ℕ`, the *capacity-bounded sets* are
`𝕀_{𝒜,c} = {I ⊆ E : |I ∩ A_k| ≤ c(k) for every k ∈ K}`. When `𝒜` is laminar these are the
independent sets of a matroid on `E`, and a matroid arising this way from a finite laminar family
is a *laminar matroid*.

## Main definitions

* `IsLaminar A`: the indexed family `A : ι → Set α` is laminar.
* `capacityBoundedSets E A c`: the family `𝕀_{𝒜,c}` of subsets `I ⊆ E` with
  `(I ∩ A k).encard ≤ c k` for every `k`.
* `Matroid.IsLaminar M`: the matroid `M` is a laminar matroid.

## Implementation notes

A multiset of subsets of `E` is modelled as an indexed family `A : ι → Set α`, so repetitions are
the non-injectivity of `A`. Subsets are `Set α`, matching the independent sets of `Matroid α`,
and cardinality is `Set.encard`, so the definitions are meaningful without any finiteness.

The paper takes `E` and the index set `K` finite and the `A_k` contained in `E`. None of this is
needed for `IsLaminar` or `capacityBoundedSets`. In `Matroid.IsLaminar` the index set is a
finite type in `Type` (every finite index set is equivalent to some `Fin n`, so this loses
nothing), but `A_k ⊆ E` is not imposed: since independent sets lie in `E`, only the traces
`A_k ∩ E` matter, and these again form a laminar family, so the notion is equivalent. Finiteness
of `E` is assumed by results that need it, via `Matroid.Finite`.

## References

* [LogNarayana], Section 4.
-/

