import Lake
open Lake DSL

/-!
Kernel-checked formalization of the 509-vertex 5-chromatic unit-distance graph of J. Parts (G509).

Build: `lake exe cache get && lake build`.
-/

package g509_lean where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "065356127b1dc0016f66b7283ce0ce2c4055aa55"

@[default_target]
lean_lib G509

/-- Small positive tests of the RUP checker (not needed for the main result; not built by default).
Build with `lake build G509Test`. -/
lean_lib G509Test where
  roots := #[`G509.Test.RMoser.C0, `G509.Test.RM5c.C3]
