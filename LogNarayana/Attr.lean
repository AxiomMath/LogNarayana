/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public meta import Lean

/-!
# The `lognarayana` tag attribute

`@[lognarayana "TAG"]` labels a declaration with the name of the statement of [LogNarayana] it
formalizes. A statement spread over several declarations carries the same label on each of them.

## References

* [LogNarayana] *Log-Concavity in Narayana Transforms and Stack-Sorting Fibers*.
-/

public meta section

open Lean

/-- Attribute syntax: `@[lognarayana "TAG"]`, labelling a declaration with the statement of the
paper it formalizes. -/
syntax (name := lognarayana) "lognarayana " str : attr

initialize Lean.registerBuiltinAttribute {
  name  := `lognarayana
  descr := "labels a declaration with the statement of the paper it formalizes"
  add   := fun _ _ _ => pure ()
}

end
