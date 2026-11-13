/-
Copyright (c) 2026 olivierFer3. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: olivierFer3 (code produced with Claude Code; see PROVENANCE.md)
-/
import G509.Exhaust

/-! Exhaustiveness, chunk 5 of the rows (rows 160 to 191). -/

namespace G509.EX

theorem rows_5 : rowsOK (boxes.drop 160) 160 (adjN.drop 160) 32 = true := by decide +kernel

end G509.EX
