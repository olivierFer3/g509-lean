/-
Copyright (c) 2026 olivierFer3. Released under Apache 2.0 license as described in the file LICENSE.
Authors: olivierFer3 (code produced with Claude Code; see PROVENANCE.md)
-/
import G509.Exhaust

/-! Exhaustiveness, chunk 9 of the rows (rows 288 to 319). -/

namespace G509.EX

theorem rows_9 : rowsOK (boxes.drop 288) 288 (adjN.drop 288) 32 = true := by decide +kernel

end G509.EX
