/-
Copyright (c) 2026 olivierFer3. Released under Apache 2.0 license as described in the file LICENSE.
Authors: olivierFer3 (code produced with Claude Code; see PROVENANCE.md)
-/
import G509.Bridge
import G509.Distinct
import G509.T.C124

/-!
# G509: non-4-colorability, unconditional

`G509.T.unsat` (checker `G509/RUP.lean`, 125 chunks `G509/T/C*.lean`, `decide +kernel`)
+ `G509.notFour_of_unsat` (justified symmetry breaking) give `NotFourColorable`.
-/

namespace G509

theorem notFourColorable : NotFourColorable := notFour_of_unsat G509.T.unsat

/-- Same statement as `plane_non_4_colorable` (proved from Heule's 510-vertex graph) in
`HadwigerNelson.lean` of vasnesterov/HadwigerNelson. -/
theorem plane_non_4_colorable : ¬ planeColorable 4 :=
  plane_non_4_colorable_of notFourColorable

theorem exists_509 : ∃ T : Finset ℂ, T.card = 509 ∧
    ¬ ∃ f : ℂ → Fin 4, ∀ u ∈ T, ∀ v ∈ T, unitDistance u v → f u ≠ f v :=
  exists_509_of notFourColorable

end G509

#print axioms G509.notFourColorable
#print axioms G509.plane_non_4_colorable
#print axioms G509.exists_509
