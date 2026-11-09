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
# Log-concave and ultra-log-concave polynomials

The definitions documented here are stated in `LogNarayana.Definitions` and
`LogNarayana.AuxiliaryDefinitions`, which this module imports.

A finite sequence `b₀, …, b_d` in an ordered semiring is *log-concave* if all its terms are
nonnegative and `b_{j-1} b_{j+1} ≤ b_j²` for `1 ≤ j ≤ d - 1`. It has *no internal zeros* if the
indices of its positive terms form an interval of `{0, …, d}`: whenever `i < j < k ≤ d` with
`b_i > 0` and `b_k > 0`, also `b_j > 0`.

A polynomial `f` is *log-concave* if all its coefficients are nonnegative and its coefficient
sequence, extended by zeros beyond the degree, is log-concave. It is *ultra-log-concave of
order `d`* if it has degree at most `d` and the normalized coefficient sequence
`([x^j] f / (d choose j))_{j=0}^{d}` is log-concave and has no internal zeros. The zero
polynomial is ultra-log-concave of every order.

## Main definitions

* `IsLogConcaveSeq d b`: the sequence `(b j)_{j=0}^{d}` is log-concave.
* `HasNoInternalZeros d b`: the sequence `(b j)_{j=0}^{d}` has no internal zeros.
* `Polynomial.IsLogConcave f`: `f` has nonnegative coefficients and a log-concave coefficient
  sequence.
* `Polynomial.IsUltraLogConcave d f`: `f` is ultra-log-concave of order `d`.

## Implementation notes

A sequence is a function `b : ℕ → R` of which only the values at `0, …, d` enter, so the
coefficient function of a polynomial of degree at most `d` can be passed directly.

The quadratic inequalities are indexed from the left neighbour,
`b j * b (j + 2) ≤ b (j + 1) ^ 2`, which is the condition at the middle index `j + 1 ≥ 1`
without natural number subtraction. For polynomials the coefficients vanish beyond the degree,
so `Polynomial.IsLogConcave f` agrees with `IsLogConcaveSeq f.natDegree f.coeff`.

In `HasNoInternalZeros` the bound `k ≤ d` forces `i, j < d` as well; equivalently, the set
`{j | j ≤ d ∧ 0 < b j}` is `Set.OrdConnected`.

The condition `[x^j] f = 0` for every `j > d` in the ultra-log-concave case is stated as
`f.natDegree ≤ d`, which is equivalent by `Polynomial.natDegree_le_iff_coeff_eq_zero`. On
`0, …, d` the normalizing factors `d.choose j` are nonzero.

The scalars are any semiring (respectively semifield) with a partial order, and for
`HasNoInternalZeros` any type with a zero and a strict order; the paper's case is `R = ℝ`.

## References

* [LogNarayana], Definitions of log-concave sequences and polynomials, sequences with no
  internal zeros, and ultra-log-concave polynomials.
-/

namespace Polynomial

end Polynomial
