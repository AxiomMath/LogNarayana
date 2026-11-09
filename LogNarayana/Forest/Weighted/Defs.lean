/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module
public import Mathlib
public import LogNarayana.Attr
public import LogNarayana.StackSorting.AdoptableForest.Defs
public import LogNarayana.AuxiliaryDefinitions

/-!
# The marked tree of the root-recurrence example

The definitions documented here are stated in `LogNarayana.Definitions` and
`LogNarayana.AuxiliaryDefinitions`, which this module imports.

The marked tree `(𝒯, {1, 2})` on `[3] = {1, 2, 3}` is the tree with root `3` and two leaves
`1` and `2`: its parent map sends `1` and `2` to `3` and leaves `3` without a parent, and its
marked set is `{1, 2}`. It is a postorder forest in the sense of `IsPostorderForest`, and it is
the example on which the root recurrence for the weighted open-pair polynomial is illustrated.

## Main definitions

* `rootRecurrenceExampleTree`: the pair `(par, L)` of the parent map of `𝒯` on `[3]` and the
  marked set `L = {1, 2}`.

## Implementation notes

As for every parent map in this library, `par : ℕ → Option ℕ` is total, with `none` playing
the role of `⊥`; it is `none` at every label other than `1` and `2`, in particular at the root
`3` and outside `[3]`.

## References

* [LogNarayana] *Log-Concavity in Narayana Transforms and Stack-Sorting Fibers*, Section 4.
-/

@[expose] public section

end
