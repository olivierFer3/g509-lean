/-
Copyright (c) 2026 olivierFer3. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: olivierFer3 (code produced with Claude Code; see PROVENANCE.md)
-/
import G509.Data

/-! Kernel check (`decide +kernel`) of edges 408 to 611. -/

namespace G509

theorem edges_ok_2 : ((edges.drop 408).take 204).all edgeOK = true := by decide +kernel

end G509
