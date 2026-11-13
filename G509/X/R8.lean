/-
Copyright (c) 2026 olivierFer3. Released under Apache 2.0 license as described in the file LICENSE.
Authors: olivierFer3 (code produced with Claude Code; see PROVENANCE.md)
-/
import G509.Exhaust

/-! Exhaustiveness, chunk 8 of the rows (rows 256 to 287). -/

namespace G509.EX

theorem rows_8 : rowsOK (boxes.drop 256) 256 (adjN.drop 256) 32 = true := by decide +kernel

end G509.EX
