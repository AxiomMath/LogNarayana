/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib
public import LogNarayana.Attr
public import LogNarayana.Narayana.Polynomials.Defs
public import LogNarayana.Narayana.Transform.Defs
public import LogNarayana.Lorentzian.Symbol.Defs
public import LogNarayana.Lorentzian.Hessian.Defs
public import LogNarayana.AuxiliaryDefinitions

/-!
# Determinant-twisted Schur polynomials: definitions

A partition with at most `r` parts is a weakly decreasing `r`-tuple `μ = (μ₁, …, μᵣ)` of
natural numbers; the set of these is `Par_r`. The semistandard Young tableaux `SSYT_r(μ)` of
shape `μ` with entries in `[r]` have contents `ct(T) ∈ ℤ_{≥0}^r`, and the Kostka number
`K_{μ,α}` counts the tableaux of content `α`. The Schur polynomial is
`s_μ(z₁, …, zᵣ) = ∑_{|α| = |μ|} K_{μ,α} z^α`, and its Narayana transform is
`Φ_{μ,r} = 𝒩(s_μ) ∈ ℝ[x]`.

This file also defines the Jacobi polynomials `P^{(α,β)}_d` with nonnegative integer
parameters and the generating series `V(z) = ∑_{m ≥ 0} Ñ_m(x) z^m` of the shifted Narayana
polynomials, and records two cited results as propositions, to be taken as hypotheses by the
theorems that use them: the Lorentzian property of normalized Schur polynomials and the location
of the zeros of Jacobi polynomials.

## Main definitions

* `PartitionAtMostParts r`: the type `Par_r` of weakly decreasing maps `Fin r → ℕ`.
* `PartitionAtMostParts.hook r a d`: the shape `(a + d, a^{r-1})`.
* `PartitionAtMostParts.row r d`: the one-row shape `(d) = (d, 0, …, 0)`.
* `PartitionAtMostParts.youngDiagram μ`: the Young diagram of `μ`.
* `PartitionAtMostParts.semistandardYoungTableaux μ`: the set `SSYT_r(μ)`.
* `SemistandardYoungTableau.content T r`: the content `ct(T) : Fin r → ℕ`.
* `PartitionAtMostParts.kostkaNumber μ α`: the Kostka number `K_{μ,α}`.
* `PartitionAtMostParts.schurPolynomial R μ`: the Schur polynomial `s_μ`.
* `PartitionAtMostParts.schurNarayanaTransform μ`: the polynomial `Φ_{μ,r} = 𝒩(s_μ)`.
* `Polynomial.jacobi α β d`: the Jacobi polynomial `P^{(α,β)}_d`.
* `shiftedNarayanaGenSeries`: the power series `V(z) ∈ ℝ[x]⟦z⟧`.
* `PartitionAtMostParts.NormalizedSchurIsLorentzian`: the theorem of Huh, Matherne, Mészáros
  and St. Dizier, as a proposition.
* `Polynomial.JacobiRootsSimpleInIoo`: the zeros of Jacobi polynomials are real, simple and lie
  in `(-1, 1)`, as a proposition.

## Implementation notes

An element of `Par_r` is a map `μ : Fin r → ℕ` with `Antitone μ`. Mathlib indexes the rows and
columns of a Young diagram from `0`, and the alphabet `[r] = {1, …, r}` is represented by
`{0, …, r - 1}`, i.e. by `Fin r`; the letter `i` of the paper is the index `i - 1`. The
definitions make sense for every `r`, including `r = 0`, so the hypothesis `r ≥ 1` is not
imposed on them.

## References

* [LogNarayana] *Log-Concavity in Narayana Transforms and Stack-Sorting Fibers*, Sections 2.1
  and 8.
* [HMMS] J. Huh, J. P. Matherne, K. Mészáros, A. St. Dizier, *Logarithmic concavity of Schur
  and related polynomials*, Trans. Amer. Math. Soc. 375 (2022), 4411–4427, Theorem 3.
* [DLMF] *NIST Digital Library of Mathematical Functions*, §§18.2(vi) and 18.5.
-/

namespace PartitionAtMostParts

end PartitionAtMostParts


namespace PartitionAtMostParts

variable {r : ℕ}

end PartitionAtMostParts


namespace SemistandardYoungTableau

variable {γ : YoungDiagram}

end SemistandardYoungTableau


namespace PartitionAtMostParts

variable {r : ℕ}

end PartitionAtMostParts


namespace PartitionAtMostParts

variable {r : ℕ}

end PartitionAtMostParts


namespace PartitionAtMostParts

variable {r : ℕ}

end PartitionAtMostParts

namespace Polynomial

end Polynomial

section ShiftedNarayanaGenSeries

open Polynomial

end ShiftedNarayanaGenSeries

namespace PartitionAtMostParts


/-- **Huh–Matherne–Mészáros–St. Dizier** ([HMMS, Theorem 3]): for every partition `μ` with at
most `r` parts, the normalized Schur polynomial `∑_α K_{μ,α} z^α / α!`, that is
`MvPolynomial.fullFactorialNormalization` applied to `PartitionAtMostParts.schurPolynomial ℝ μ`,
is Lorentzian. -/
@[expose, lognarayana "thm_ext_hmms_schur_lorentzian"]
public def NormalizedSchurIsLorentzian : Prop :=
  ∀ (r : ℕ) (μ : PartitionAtMostParts r),
    (MvPolynomial.fullFactorialNormalization (Fin r) ℝ (μ.schurPolynomial ℝ)).IsLorentzian

end PartitionAtMostParts

namespace Polynomial

end Polynomial
