/-
Copyright (c) 2026 olivierFer3. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: olivierFer3 (code produced with Claude Code; see PROVENANCE.md)
-/
import G509.Exhaust

/-! Exhaustiveness, chunk 2 of the rows (rows 64 to 95). -/

namespace G509.EX

theorem rows_2 : rowsOK (boxes.drop 64) 64 (adjN.drop 64) 32 = true := by decide +kernel

end G509.EX
