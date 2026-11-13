/-
Copyright (c) 2026 olivierFer3. Released under Apache 2.0 license as described in the file LICENSE.
Authors: olivierFer3 (code produced with Claude Code; see PROVENANCE.md)
-/
import G509.Exhaust

/-! Exhaustiveness, chunk 0 of the rows (rows 0 to 31). -/

namespace G509.EX

theorem rows_0 : rowsOK (boxes.drop 0) 0 (adjN.drop 0) 32 = true := by decide +kernel

end G509.EX
