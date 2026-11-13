/-
Copyright (c) 2026 olivierFer3. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: olivierFer3 (code produced with Claude Code; see PROVENANCE.md)
-/
import G509.Exhaust

/-! Exhaustiveness, chunk 3 of the rows (rows 96 to 127). -/

namespace G509.EX

theorem rows_3 : rowsOK (boxes.drop 96) 96 (adjN.drop 96) 32 = true := by decide +kernel

end G509.EX
