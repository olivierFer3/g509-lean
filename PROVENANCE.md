# Provenance

Categories: **COPIED** (taken from another project without mathematical change), **NEW** (written for this
project), **GENERATED** (written by a script of `gen/` from the data; regeneration is checked byte for byte,
see below).

## Reused from vasnesterov/HadwigerNelson (Apache-2.0, (c) 2024 Vasily Nesterov)

Repository https://github.com/vasnesterov/HadwigerNelson, commit `ad7843546da5f4db4fcf9827e0951f34295ad7cc`
("Update README.md"), license Apache License 2.0 (the file `LICENSE` of this repository is that file,
unchanged).

| item | category | how it is used |
|---|---|---|
| `HadwigerNelson/Defs.lean` (`unitDistance`, `planeColorable`) | COPIED | into `G509/Defs.lean`, definitions unchanged, inside the namespace `G509`; the copyright notice is kept. Not copied: the line `open Complex ComplexConjugate Topology Filter` and the lemma `neq_of_unit` (unused). |
| statement of `plane_non_4_colorable` (`HadwigerNelson.lean`, proved there from Heule's 510-vertex graph) | statement reused | `G509.plane_non_4_colorable : ¬ planeColorable 4` has the same statement. |
| `vtx/509_parts.vtx` | COPIED (data) | unchanged; the 509 points of J. Parts' graph. The README of vasnesterov/HadwigerNelson says it was sourced from the Polymath16 thread (https://dustingmixon.wordpress.com/2019/12/12/polymath16-fifteenth-thread-writing-the-paper-and-chasing-down-loose-ends/). Converted exactly by `gen/gen_g509.py`. |
| overall structure | idea | as in the G510 proof: exact unit edges, reduction of the colorability of the plane to that of a finite graph, CNF, SAT certificate. |

No other code of vasnesterov/HadwigerNelson is used (in particular not its LeanSAT/`ofReduceBool`-based
certificate, nor its toolchain).

## Mathematical source

- J. Parts, "Graph minimization, focusing on the example of 5-chromatic unit-distance graphs in the plane",
  arXiv:2010.12665; Geombinatorics 29(4) (2020), 137–166 (the 509-vertex graph).
- The identity √(5(7 ± √33)/2) = (√55 ± √15)/2 (both sides are positive and have the same square,
  (70 ± 10√33)/4), together with √(11/3) = √33/3, puts all coordinates in ℚ(√3, √5, √11). The conversion of
  `vtx/509_parts.vtx` is done exactly in Python (`gen/gen_g509.py`, sympy, with a 1e-30 numerical
  cross-check). In Lean, the `+` case of the identity is proved (`G509.nested_radical`) and point 448 is
  checked against the original file (`G509.P_448`); the other points are not compared with the `.vtx` file
  inside Lean. The theorems are about the 509 points as defined in `G509/Data.lean`.

## Lean files

| file(s) | category | content |
|---|---|---|
| `G509/Defs.lean` | COPIED | see above. |
| `G509/Field.lean` | NEW | tower ℤ[√3][√5][√11] as pairs of integers, evaluation homomorphisms `ev1/ev2/ev3`, boolean test `Pt.isUnit`, lemma `Pt.norm_sub_eq_one`. |
| `G509/Data.lean` | GENERATED (`gen/gen_lean.py`) | the 509 points (base-512 literals) and the 2442 edges. |
| `G509/Edges0..11.lean` | GENERATED (`gen/gen_lean.py`) | `decide +kernel` on 12 slices of the edge list. |
| `G509/Main.lean` | NEW | `unit_edges`, conditional `plane_non_4_colorable_of`, `exists_509_of`, `nested_radical`, `P_448`. |
| `G509/DistinctData.lean` / `G509/Distinct.lean` | GENERATED (`gen/gen_distinct.py`) / NEW | the 509 points are pairwise distinct (`S_card`), via integer-enclosed real keys. |
| `G509/LRAT.lean` | NEW | literal encoding and semantics (`LR.litT`, `LR.SatF`, ...) used by `RUP.lean`; it also contains a first kernel-reducible checker with a dynamic clause database, not used by the main result. |
| `G509/RUP.lean` | NEW | the RUP checker with static tables used for the main result; soundness `RV.chunk_sound`, `RV.ft_good`, `RV.not_empty`. See "Related work": the design is not new. |
| `G509/CNF.lean` | NEW | the CNF `G509C.F` (4-coloring of `edges`, triangle 0, 149, 152 colored 0, 1, 2). |
| `G509/S/FT.lean`, `G509/T/C0..C124.lean` | GENERATED (`gen/rup_chunks2.py`) | the clause table of `F` (checked in Lean against `G509C.F`) and the certificate in 125 chunks. |
| `G509/Bridge.lean` | NEW | `notFour_of_unsat`: unsatisfiability of `F` implies `NotFourColorable`; the symmetry breaking is justified by a permutation of the colors. |
| `G509/Final.lean` | NEW | `notFourColorable`, `plane_non_4_colorable`, `exists_509`. |
| `G509/Exhaust.lean`, `G509/ExhaustFinal.lean` / `G509/ExhaustData.lean`, `G509/X/R0..R15.lean` | NEW / GENERATED (`gen/gen_exhaust.py`) | `G509.EX.edges_exhaustive`: no other pair of the 509 points is at distance 1. |
| `G509.lean` | NEW | root module. |
| `G509/Test/RMoser`, `G509/Test/RM5c` | GENERATED (by earlier versions of the chunk generator) | positive tests of the checker (Moser spindle with 3 colors; a 23-vertex non-4-colorable graph in 4 chunks); library `G509Test`, not built by default. |
| `tests/Axioms.lean`, `scripts/build_sequential.sh` | NEW | axiom check of the main results; one-module-at-a-time build. |
| `tests/negative/Neg1.lean`, `Neg2.lean` | copies of `G509/Test/RM5c/C0.lean`, deliberately corrupted | negative tests, **expected to fail**; not part of any Lake library (see `tests/negative/README.md`). |

The Lean code was written for this project with Claude Code (Anthropic). Apart from `G509/Defs.lean`, no
Lean code is taken from another project.

## Generators and regeneration (`gen/`)

All generators were updated so that they emit the license header and the English comments of the committed
files. When this repository was assembled, every generated file was regenerated from the inputs below and
compared **byte for byte** with the committed file: all identical (`gen/g509.json`, `G509/Data.lean`,
`G509/Edges0..11.lean`, `G509/DistinctData.lean`, `G509/ExhaustData.lean`, `G509/X/R0..R15.lean`,
`G509/S/FT.lean`, `G509/T/C0..C124.lean`; the trimmed LRAT file too).

```sh
python3 gen/gen_g509.py vtx/509_parts.vtx gen/g509.json       # needs sympy, mpmath
python3 gen/gen_lean.py . 12
python3 gen/gen_distinct.py . 1000 write
python3 gen/gen_exhaust.py
xz -dk gen/g509_unsat_trim.lrat.xz
STEPCAP=600 python3 gen/rup_chunks2.py gen/g509_sym.cnf gen/g509_unsat_trim.lrat G509/T G509.T 24000 G509C.F G509.S
STEPCAP=600 python3 gen/rup_chunks2.py gen/g509_sym.cnf gen/g509_unsat_trim.lrat <tmpdir> G509.S 24000 G509C.F   # only <tmpdir>/FT.lean is used: = G509/S/FT.lean
```

- `gen/g509_sym.cnf` (2036 variables, 10 280 clauses, sha256
  `9e3d746edb93e9ff8b1a91430fed82f9eaf8f20f781aa2e85752847b7cbc8595`): checked equal, clause by clause, to the
  CNF `G509C.F` of `G509/CNF.lean` built from the edges of `G509/Data.lean`.
- Certificate: CaDiCaL 2.1.2 (binary shipped with the Lean toolchain v4.35.0-rc2),
  `cadical -q --unsat --lrat=true --binary=false gen/g509_sym.cnf g509_unsat.lrat` (86 113 steps, sha256
  `7068372f1a18e367ddd2be065c61324bf035ebbf30b92444caaf1ffab065ec5c`, not included), backward-trimmed by
  `python3 gen/lrat_trim.py g509_unsat.lrat g509_unsat_trim.lrat` to 56 996 steps (sha256
  `f3f1ebd720475156971b3be1db5d0b4f6597dc37d2e79dcdf28dddf52717785f`; included compressed as
  `gen/g509_unsat_trim.lrat.xz`). The chunks `G509/T/*.lean` are the certificate checked by Lean; the LRAT
  files are not trusted.
- `gen/lean_to_cnf.py` extracts a literal clause list `def F : List (List Nat) := [...]` (as in the test files
  `G509/Test/*/FT.lean`) as DIMACS.
- The generators of the test files (earlier versions of `rup_chunks2.py`) are not included.

## Minimality computation (`minimality/`)

Python scripts written for this project (with Claude Code), translated to English for this repository.
`minimality/drat_check.py` (forward RUP/RAT checker), `drat_check_stream.py`, `hs.py`, `verify_cuts.py`,
`gen_cnf.py`, `core.py`, `test_counter.py`, `check_nonvacuity.py`, `udg.py`, `geom4.py` were written by the
agents doing the computation; `rup_check.py`, `verify_cnf.py`, `verify_ambient_cuts.py` were written
separately by an independent reviewing agent. Changes made for this repository: comments and messages
translated; input from the JSON files of `minimality/data/` instead of pickles (converted by
`export_json.py`, with an exact round-trip check, and with the 509 points checked equal to those of
`gen/g509.json`); paths made relative; in `hs.py`, the project-specific status-table writer and the
automatic certification hook were removed and a `cuts.json` output was added. The four CNFs of
`minimality/data/cnf/` were regenerated from the JSON data and are identical to the original ones except for
their first comment line; the DRAT proofs were regenerated by CaDiCaL 2.1.2 and are byte-identical to the
original ones. Method credits: see `minimality/README.md`.

## Related work (convergent design, no code reused)

The checker `G509/RUP.lean` was written without consulting the works below (according to the logs of the
sessions in which it was written, the agents had no network access; the only external source read for the
SAT part was the LRAT checker of Lean core, `Std.Tactic.BVDecide.LRAT`). Its main ideas already appear,
earlier, in these works, which are cited as prior art:

- LratK, `CoveringLean/LratK.lean` of https://github.com/thiagopatzdorf/Matematica, commit
  `dff10e140501f7adbb7d69c15fb7bd467bebc688` (4 Oct 2026), CC BY 4.0: kernel-reduced RUP checker, literals
  2v/2v+1, static clause database in a binary tree, `Nat` bitmask assignment (GMP), raw recursors, checking by
  blocks, soundness proof `unsat_of_good`.
- kooshi/hadwiger-nelson, https://github.com/kooshi/hadwiger-nelson, `Proofs/HadwigerNelson/Sat/` (first
  commit of `MaskCheck.lean` `956a0ebae6`, 30 Jul 2026; head read `5049e2fbd3595d2939df6e14910b1a7d95039265`),
  Apache-2.0: kernel RUP checker with a clause table emitted as a compact literal and `Nat` masks, used for
  χ(ℝ²) ≥ 5 via Heule's 510-vertex graph, with a fixed triangle and a permutation of the colors.
- T. S. Tomar, "Re-proving native_decide facts in Lean's kernel: a study of 16 public packages and a
  converter", Oct 2026, doi:10.5281/zenodo.23818391; https://github.com/tejasvi/native-trust (Apache-2.0),
  add-ons `lrat/` and `bvs/`: LRAT checker on `Nat` masks, chunks of at most 20 000 hints in separate modules.
- S. Szeider, arXiv:2607.00815 (v1 1 Jul 2026, "LRAT-Catcher: Importing SAT Solver Certificates into Lean4 by
  Reflection"; v2 "Streaming LRAT Certificates into Lean Theorems"); https://github.com/leansolving/lrat-catcher
  (MIT): `+kernel` mode on the core checker made reducible (small certificates only).
- M. Carneiro, `Mathlib.Tactic.Sat.FromLRAT` (`lrat_proof`), Mathlib, Apache-2.0: kernel-checked LRAT via a
  proof term built by the elaborator.
- Neighbouring work only: L. Y. Zhang, "Ratified", https://github.com/Leo-Y-Zhang/Ratified, aiXiv:2610.03288
  (31 Oct 2026). Its license grants no reuse rights; nothing from it is used here.

## Tools

- CaDiCaL 2.1.2 (https://github.com/arminbiere/cadical), MIT license, used as an untrusted solver (binary
  shipped with the Lean toolchain). Reference requested by its README: A. Biere, T. Faller, K. Fazekas,
  M. Fleury, N. Froleyks, F. Pollitt, "CaDiCaL 2.0", CAV 2024, LNCS, Springer, pp. 133–152,
  doi:10.1007/978-3-031-65627-9_7. (The README gives LNCS vol. 14681 and links the DOI of a volume,
  10.1007/978-3-031-37703-7; the chapter DOI above and vol. 14682 are those given by the TU Wien repository
  record https://repositum.tuwien.at/handle/20.500.12708/210752. The volume number was not checked further.)
- Lean 4 `leanprover/lean4:v4.35.0-rc2`, Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55` (Apache-2.0),
  `leanchecker` (shipped with the toolchain).

## Use of AI

See README.md ("Use of AI").
