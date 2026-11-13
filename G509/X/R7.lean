/-
Copyright (c) 2026 olivierFer3. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: olivierFer3 (code produced with Claude Code; see PROVENANCE.md)
-/
import G509.Exhaust

/-! Exhaustiveness, chunk 7 of the rows (rows 224 to 255). -/

namespace G509.EX

theorem rows_7 : rowsOK (boxes.drop 224) 224 (adjN.drop 224) 32 = true := by decide +kernel

end G509.EX
