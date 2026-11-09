/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module
public import Mathlib.Combinatorics.Matroid.Basic
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Data.Fintype.Powerset
public import LogNarayana.Attr
public import LogNarayana.AuxiliaryDefinitions

/-!
# The basis generating polynomial of a matroid

The definitions documented here are stated in `LogNarayana.Definitions` and
`LogNarayana.AuxiliaryDefinitions`, which this module imports.

For a matroid `M` on a finite set `E`, its *basis generating polynomial* is
`B_M(z) = ∑_{B base of M} ∏_{e ∈ B} z_e`, a multiaffine homogeneous polynomial of degree
`rank M` in the variables `z_e`, `e ∈ E`.

## Main definitions

* `Matroid.basisGeneratingPolynomial R M`: the polynomial `∑_{B} ∏_{e ∈ B} X e` in
  `MvPolynomial α R`, the sum running over the bases `B` of `M`.

## Implementation notes

The variables are indexed by the ambient finite type `α` of the matroid rather than by its
ground set `M.E`; since every base is contained in `M.E`, only the variables `X e` with
`e ∈ M.E` occur, and for `M.E = univ` this is the paper's polynomial in `ℝ[z_e : e ∈ E]`.
A matroid on a finite subset `E` of a larger finite type is thereby handled without renaming
variables. The coefficient ring is an arbitrary commutative semiring `R`; the paper takes
`R = ℝ`. Bases are enumerated as the finsets `B` with `M.IsBase ↑B`.

## References

* [LogNarayana], Section 2; [BrandenHuh2020], Section 4.
-/

