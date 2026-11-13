# A kernel-checked Lean 4 formalization of Parts' 509-vertex 5-chromatic unit-distance graph

This repository proves in Lean 4, with the kernel as the only checker, that the 509-vertex unit-distance
graph of Jaan Parts (G509) is not 4-colorable, and hence that the plane cannot be colored with 4 colors so
that points at distance 1 get different colors.

## Final statements

Definitions (`G509/Defs.lean`, copied from vasnesterov/HadwigerNelson, namespace `G509` added):

```lean
def unitDistance (u v : ℂ) : Prop := ‖u - v‖ = 1

def planeColorable (n : ℕ) : Prop := ∃ f : ℂ → Fin n, ∀ u v : ℂ, (unitDistance u v) → f u ≠ f v
```

Main results (`G509/Final.lean`, `G509/ExhaustFinal.lean`, all in the namespace `G509`):

```lean
theorem notFourColorable : NotFourColorable := notFour_of_unsat G509.T.unsat

theorem plane_non_4_colorable : ¬ planeColorable 4 :=
  plane_non_4_colorable_of notFourColorable

theorem exists_509 : ∃ T : Finset ℂ, T.card = 509 ∧
    ¬ ∃ f : ℂ → Fin 4, ∀ u ∈ T, ∀ v ∈ T, unitDistance u v → f u ≠ f v :=
  exists_509_of notFourColorable

theorem edges_exhaustive (i j : ℕ) (hi : i < 509) (hj : j < 509) :
    unitDistance (P i) (P j) ↔ (i, j) ∈ edges ∨ (j, i) ∈ edges := by
  ...
```

(the last one is `G509.EX.edges_exhaustive`), where (`G509/Main.lean`, `G509/Data.lean`)

```lean
def NotFourColorable : Prop := ¬ ∃ c : ℕ → Fin 4, ∀ e ∈ edges, c e.1 ≠ c e.2
noncomputable def P (i : ℕ) : ℂ := (pts.getD i default).toC
```

`pts` is the list of the 509 points of Parts (exact coordinates) and `edges` the list of 2442 pairs
`(i, j)`, `i < j`. `G509.plane_non_4_colorable` has the same statement as `plane_non_4_colorable` in
vasnesterov/HadwigerNelson (proved there from Heule's 510-vertex graph).

## What is checked

- **Non-4-colorability**: the finite graph `edges` on the vertices 0..508 has no proper 4-coloring
  (`notFourColorable`), from a SAT certificate checked inside the kernel; with `G509.unit_edges` (each of the
  2442 pairs is at distance exactly 1) this gives `plane_non_4_colorable`.
- **509 distinct points**: `G509.S_card : S.card = 509`, used in `exists_509`.
- **The 2442 edges are exactly the unit-distance pairs** among the 509 points (`edges_exhaustive`).
  (That `edges` has no duplicate pair is not stated in Lean; it is strictly increasing, checked outside Lean.
  Exhaustiveness is not needed for non-colorability.)
- **Kernel only**: every computation is `decide +kernel`; no `native_decide`, `Lean.ofReduceBool`,
  `bv_decide`, `sorry`, `axiom`, `implemented_by`, `extern`, `unsafe` or `opaque` in the sources (checked by
  grep). `lake env lean tests/Axioms.lean` prints exactly:

  ```
  'G509.notFourColorable' depends on axioms: [propext, Classical.choice, Quot.sound]
  'G509.plane_non_4_colorable' depends on axioms: [propext, Classical.choice, Quot.sound]
  'G509.exists_509' depends on axioms: [propext, Classical.choice, Quot.sound]
  'G509.EX.edges_exhaustive' depends on axioms: [propext, Classical.choice, Quot.sound]
  'G509.unit_edges' depends on axioms: [propext, Classical.choice, Quot.sound]
  'G509.S_card' depends on axioms: [propext, Classical.choice, Quot.sound]
  ```
- **leanchecker** (shipped with the toolchain; it replays all declarations of a module in the kernel from the
  environment of its imports): `lake env leanchecker -v <module>` was run, one module at a time, on all 168
  modules `G509.*` of the library (the 125 certificate chunks included) in the fresh clone used for the
  timings below: 168/168 returned status 0 (output `replaying <module>`, 33 min in total).
  **Mathlib itself was not replayed** (`leanchecker --fresh`, which would replay everything including
  Mathlib, was not run for lack of memory).

## The key idea

The README of vasnesterov/HadwigerNelson notes that G509 is out of reach of its `build_edge` tactic because of
coordinates such as `Sqrt[(5*(7 + Sqrt[33]))/2]`. These nested radicals denest:

  √(5(7 ± √33)/2) = (√55 ± √15)/2

(both sides are positive and have the same square, (70 ± 10√33)/4). With √(11/3) = √33/3, every coordinate
of Parts' file becomes (1/96)·(an integer combination of 1, √3, √5, √15, √11, √33, √55, √165), i.e. lies in
ℚ(√3, √5, √11). Unit distances are then checked by exact integer arithmetic in the tower ℤ[√3][√5][√11]
(`G509/Field.lean`), evaluated by the kernel. `G509.nested_radical` proves the identity (the `+` case) and
`G509.P_448` checks point 448 against the original coordinate.

## How the proof is organized

- `G509/Field.lean`: exact arithmetic, a boolean unit-distance test and its soundness.
- `G509/Data.lean`, `G509/Edges*.lean`, `G509/Main.lean`: points, edges, `unit_edges`.
- `G509/Distinct*.lean`: the points are distinct (integer enclosures of the coordinates).
- `G509/CNF.lean`, `G509/RUP.lean`, `G509/S/FT.lean`, `G509/T/C0..C124.lean`, `G509/Bridge.lean`,
  `G509/Final.lean`: CNF of the 4-coloring problem with the triangle (0, 149, 152) colored (0, 1, 2), a
  kernel-reducible RUP checker, the certificate (CaDiCaL LRAT proof, trimmed to 56 996 steps, split into 125
  chunk modules), and the bridge lemma justifying the symmetry breaking by a permutation of the colors.
- `G509/Exhaust*.lean`, `G509/X/*.lean`: exhaustiveness of the edge list.
- `G509/Test/`: small positive tests of the checker (`lake build G509Test`); `tests/negative/`: two corrupted
  certificates that the kernel must reject (not part of any library, see `tests/negative/README.md`).
- `gen/`: the Python generators (all generated Lean files are reproduced byte for byte), the CNF and the
  compressed trimmed LRAT file. `tests/Axioms.lean`: the axiom check. `scripts/build_sequential.sh`: build one
  module at a time. `PROVENANCE.md`: the origin of every file.

## Building

Toolchain `leanprover/lean4:v4.35.0-rc2`, Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55`.

```sh
lake exe cache get   # downloads the precompiled Mathlib
lake build
lake env lean tests/Axioms.lean
```

Measured on a laptop with 7.4 GB of RAM, from a fresh clone of this repository (November 2026):
`lake exe cache get` took about 5 min (the first attempt reported a few failed downloads; running it a second
time fetched them). The library was then compiled **one module at a time** (`lake build <module>` for each
of the 169 modules in dependency order, `LEAN_NUM_THREADS=1`, each under a memory limit of 2.9–4.3 GB without
swap): 36 min in total (2180 s), of which 30 min for the 125 certificate chunks; the peak resident memory of
a single compilation was 3.95 GB (lake + lean, memory-mapped Mathlib `.olean` files included). A final
`lake build` then had nothing left to do, `lake env lean tests/Axioms.lean` printed the output above,
`lake build G509Test` succeeded, and both negative tests failed as expected (`decide` proved that the
proposition `chunkCheck ... = true` is false).

**Memory warning:** a plain `lake build` compiles several modules in parallel and can need several times this
amount of memory. On a small machine, build one module at a time with `scripts/build_sequential.sh`
(after `lake exe cache get`).

## Context

- G509 is the 509-vertex 5-chromatic unit-distance graph of J. Parts, "Graph minimization, focusing on the
  example of 5-chromatic unit-distance graphs in the plane", arXiv:2010.12665; Geombinatorics 29(4) (2020),
  137–166. It is Parts' record; **this repository does not give a new record**, it formalizes his graph.
- To our knowledge this is the first formalization of G509; it is listed as a TODO item in
  https://github.com/vasnesterov/HadwigerNelson.
- A kernel-only proof of χ(ℝ²) ≥ 5 already existed for other graphs (Heule's 510-vertex graph and others):
  https://github.com/kooshi/hadwiger-nelson.

## Additional computational result (not formalized in Lean)

The directory `minimality/` contains a certificate that G509 is **locally minimal** in two ambient point
sets: in A1 (529 vertices: G509 and 20 more points) and in A3 (544 vertices: G509 and 35 more points) there
is no non-4-colorable subgraph (induced or not) with at most 508 vertices. The method is the
hitting-set/cut approach of Parts (arXiv:2010.12665, §5), organized as an implicit-hitting-set (SMUS) loop
(A. Ignatiev, A. Previti, M. Liffiton, J. Marques-Silva, CP 2015); every cut is re-verified with a stored
witness coloring, and the final infeasibility is certified by DRAT proofs produced by CaDiCaL and checked by
two checkers written for this work. For A3, the certificate also uses the fact that a minimum non-4-colorable subgraph has minimum degree at least 4. This is a **local** result: it says nothing about graphs that are not
contained in these two point sets. It does **not** rely on the Lean kernel (its trusted base is Python code).
Data, scripts and exact commands: `minimality/README.md`.

## Credits

- Jaan Parts, for the graph (data file `vtx/509_parts.vtx`, as distributed in vasnesterov/HadwigerNelson).
- Vasily Nesterov, https://github.com/vasnesterov/HadwigerNelson (Apache-2.0): the definitions
  `unitDistance` and `planeColorable`, the statement of `plane_non_4_colorable`, the data file and the
  overall structure.
- CaDiCaL (untrusted SAT solver, version 2.1.2): A. Biere, T. Faller, K. Fazekas, M. Fleury, N. Froleyks,
  F. Pollitt, "CaDiCaL 2.0", Computer Aided Verification (CAV 2024), LNCS, Springer, 2024, pp. 133–152,
  doi:10.1007/978-3-031-65627-9_7; https://github.com/arminbiere/cadical.
- The LRAT checker of Lean core (`Std.Tactic.BVDecide.LRAT`), the only external source read while writing the
  checker `G509/RUP.lean`.
- Earlier kernel-checked SAT certificates in Lean, of which our RUP checker is a close component, developed
  independently (no code taken; see `PROVENANCE.md` for details):
  LratK (`CoveringLean/LratK.lean` in https://github.com/thiagopatzdorf/Matematica);
  NativeTrust (T. S. Tomar, "Re-proving native_decide facts in Lean's kernel: a study of 16 public packages and
  a converter", 2026, doi:10.5281/zenodo.23818391, https://github.com/tejasvi/native-trust);
  LRAT-Catcher (S. Szeider, arXiv:2607.00815, https://github.com/leansolving/lrat-catcher);
  Mathlib's `Mathlib.Tactic.Sat.FromLRAT` (M. Carneiro); and kooshi/hadwiger-nelson (above).

## Use of AI

I did not review the Lean code line by line myself; its correctness rests on the Lean kernel check (#print axioms, leanchecker) and an independent recompilation. The code was written with Claude Code (Anthropic). ChatGPT (OpenAI) was used only for literature and prior-art searches, not for writing code.

The model used with Claude Code was Claude Opus 5.5.

## License

Apache License 2.0 (`LICENSE`). `G509/Defs.lean` and `vtx/509_parts.vtx` come from
vasnesterov/HadwigerNelson (Apache-2.0, (c) 2024 Vasily Nesterov); see `PROVENANCE.md`.
