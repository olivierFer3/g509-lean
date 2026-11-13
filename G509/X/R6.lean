/-
Copyright (c) 2026 olivierFer3. Released under Apache 2.0 license as described in the file LICENSE.
Authors: olivierFer3 (code produced with Claude Code; see PROVENANCE.md)
-/
import G509.Exhaust

/-! Exhaustiveness, chunk 6 of the rows (rows 192 to 223). -/

namespace G509.EX

theorem rows_6 : rowsOK (boxes.drop 192) 192 (adjN.drop 192) 32 = true := by decide +kernel

end G509.EX
