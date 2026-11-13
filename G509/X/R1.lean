/-
Copyright (c) 2026 olivierFer3. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: olivierFer3 (code produced with Claude Code; see PROVENANCE.md)
-/
import G509.Exhaust

/-! Exhaustiveness, chunk 1 of the rows (rows 32 to 63). -/

namespace G509.EX

theorem rows_1 : rowsOK (boxes.drop 32) 32 (adjN.drop 32) 32 = true := by decide +kernel

end G509.EX
