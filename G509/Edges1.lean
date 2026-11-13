/-
Copyright (c) 2026 olivierFer3. Released under Apache 2.0 license as described in the file LICENSE.
Authors: olivierFer3 (code produced with Claude Code; see PROVENANCE.md)
-/
import G509.Data

/-! Kernel check (`decide +kernel`) of edges 204 to 407. -/

namespace G509

theorem edges_ok_1 : ((edges.drop 204).take 204).all edgeOK = true := by decide +kernel

end G509
