/-
Copyright (c) 2024 Vasily Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Nesterov
Modified for g509-lean (2026): declarations placed in the namespace `G509` (see the module docstring).
-/
import Mathlib.Analysis.Complex.Basic

/-!
# Basic definitions

COPIED from `HadwigerNelson/Defs.lean` (https://github.com/vasnesterov/HadwigerNelson,
commit ad7843546da5f4db4fcf9827e0951f34295ad7cc, Apache-2.0), without mathematical change.
Modifications: the namespace `G509` was added; the line `open Complex ComplexConjugate Topology Filter`
and the lemma `neq_of_unit` of the original file are not copied (unused). Compiled with Lean v4.35.0-rc2 and Mathlib 065356127b1dc0016f66b7283ce0ce2c4055aa55.

* `unitDistance`: predicate meaning that two points are at an unit distance from each other.
* `planeColorable n`: proposition meaning that one can color the plane in `n` colors such that ends
of any unit segment will not have same color.
-/

namespace G509

def unitDistance (u v : ℂ) : Prop := ‖u - v‖ = 1

def planeColorable (n : ℕ) : Prop := ∃ f : ℂ → Fin n, ∀ u v : ℂ, (unitDistance u v) → f u ≠ f v

end G509
