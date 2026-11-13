/-
Copyright (c) 2026 olivierFer3. Released under Apache 2.0 license as described in the file LICENSE.
Authors: olivierFer3 (code produced with Claude Code; see PROVENANCE.md)
-/
import G509.Final
import G509.ExhaustFinal

/-!
# The 509-vertex Parts graph is a non-4-colorable unit-distance graph

Main results (definitions `unitDistance`, `planeColorable` copied from `HadwigerNelson/Defs.lean` of
vasnesterov/HadwigerNelson into `G509/Defs.lean`):

* `G509.plane_non_4_colorable : ¬ planeColorable 4` (same statement as `plane_non_4_colorable`
  in `HadwigerNelson.lean` of vasnesterov/HadwigerNelson, obtained here from the 509-vertex graph of J. Parts);
* `G509.exists_509 : ∃ T : Finset ℂ, T.card = 509 ∧ ¬ ∃ f : ℂ → Fin 4, ∀ u ∈ T, ∀ v ∈ T,
  unitDistance u v → f u ≠ f v`;
* `G509.unit_edges`: the 2442 listed edges have length exactly 1;
* `G509.EX.edges_exhaustive`: for `i, j < 509`, `P i` and `P j` are at distance 1 iff
  `(i, j)` or `(j, i)` is in `G509.edges`.

Everything is checked by the kernel (`decide +kernel`); no `native_decide`, `ofReduceBool`
or `bv_decide`. The coordinates `√(5(7 ± √33)/2)` of the original file are rewritten as
`(√55 ± √15)/2` (`G509.nested_radical`), so all coordinates lie in `ℚ(√3, √5, √11)`.
-/
