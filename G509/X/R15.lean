/-
Copyright (c) 2026 olivierFer3. Released under Apache 2.0 license as described in the file LICENSE.
Authors: olivierFer3 (code produced with Claude Code; see PROVENANCE.md)
-/
import G509.Exhaust

/-! Exhaustiveness, chunk 15 of the rows (rows 480 to 508). -/

namespace G509.EX

theorem rows_15 : rowsOK (boxes.drop 480) 480 (adjN.drop 480) 32 = true := by decide +kernel

end G509.EX
