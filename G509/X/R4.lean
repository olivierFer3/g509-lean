/-
Copyright (c) 2026 olivierFer3. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: olivierFer3 (code produced with Claude Code; see PROVENANCE.md)
-/
import G509.Exhaust

/-! Exhaustiveness, chunk 4 of the rows (rows 128 to 159). -/

namespace G509.EX

theorem rows_4 : rowsOK (boxes.drop 128) 128 (adjN.drop 128) 32 = true := by decide +kernel

end G509.EX
