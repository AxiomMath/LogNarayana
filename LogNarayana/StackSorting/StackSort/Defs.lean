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
# Words and the stack-sorting map

A *word* is a finite sequence `σ = σ₁ σ₂ ⋯ σ_ℓ` of pairwise distinct positive integers; the set of
all words is `𝒲`. The *set of letters* of a finite sequence `u` is the finite set `Let(u)` of its
entries. For `n ∈ ℤ_{≥0}`, the set `S_n` consists of the words of length `n` whose set of letters
is `[n] = {1, …, n}`: the permutations of `[n]` in one-line notation, with identity
`ι_n = 1 2 ⋯ n`.

West's *stack-sorting map* `s` is defined by recursion on the length: `s(∅) = ∅`, and if `σ` is
nonempty, write `σ = L m R` where `m` is the largest letter of `σ`; then `s(σ) = s(L) s(R) m`.
For `π ∈ S_n`, the *stack-sorting fiber* is `s⁻¹(π) = {σ ∈ S_n : s(σ) = π}`, and its cardinality
is the *fertility* of `π`.

## Main definitions

* `IsWord σ`: the list `σ` of natural numbers has pairwise distinct, positive entries.
* `words`: the set `𝒲` of all words.
* `List.letters u`: the finite set of entries of the list `u`.
* `permWords n`: the set `S_n` of permutations of `[n]` in one-line notation.
* `idPermWord n`: the identity permutation `ι_n = 1 2 ⋯ n`.
* `List.stackSort σ`: the stack-sorting map.
* `List.stackFiber π`: the stack-sorting fiber `s⁻¹(π)`, where `n` is the length of `π`.
* `List.fertility π`: the cardinality of `List.stackFiber π`.

## Implementation notes

A finite sequence is a `List`, and positivity of a letter is `0 < a` in `ℕ`. Length, letters,
the empty word and concatenation are `List.length`, indexing, `[]` and `++`. The set of letters
is defined for lists over any type with decidable equality and is an `abbrev` for
`List.toFinset`, whose API applies directly. Permutations are kept as words rather than as
`Equiv.Perm (Fin n)`, since they are manipulated by concatenation and stack-sorting; `[n]` is
`Finset.Icc 1 n` and `ι_n` is `List.range' 1 n`.

The stack-sorting map is defined on lists over any linear order. A general list is split at the
*first* occurrence of its maximum, which on a word is its unique occurrence; the recursion is
well founded since both parts are strictly shorter. The fiber is a `Finset`, realised as the
permutations of `idPermWord π.length` on which `List.stackSort` takes the value `π`; since `s`
preserves length, `n = π.length` is the only size for which it can be nonempty, and it is empty
unless `π ∈ permWords π.length`.

## References

* [LogNarayana], Sections 1 and 2.
* J. West, *Permutations with forbidden subsequences and stack-sortable permutations*,
  Ph.D. thesis, MIT, 1990.
* C. Defant, *Fertility numbers*.
-/

namespace List

variable {α : Type*} [LinearOrder α]

/-- The *fertility* of `π`: the cardinality `|s⁻¹(π)|` of its stack-sorting fiber. -/
@[expose, lognarayana "def_stack_fiber"]
public def fertility (π : List ℕ) : ℕ :=
  (stackFiber π).card

end List
