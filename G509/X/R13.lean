/-
Copyright (c) 2026 olivierFer3. Released under Apache 2.0 license as described in the file LICENSE.
Authors: olivierFer3 (code produced with Claude Code; see PROVENANCE.md)
-/
import G509.Exhaust

/-! Exhaustiveness, chunk 13 of the rows (rows 416 to 447). -/

namespace G509.EX

theorem rows_13 : rowsOK (boxes.drop 416) 416 (adjN.drop 416) 32 = true := by decide +kernel

end G509.EX
