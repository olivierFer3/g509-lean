# Local minimality of G509 in two ambient graphs (not formalized in Lean)

This directory contains a separate computational result. **It does not use the Lean kernel**: its trusted
base is Python code (exact arithmetic with `fractions`, two DRAT/RUP checkers written for this work) and the
argument below. SAT solvers (CaDiCaL, CP-SAT, pysat) are used to *find* things and are **not** trusted.

## Statement

Let A1 be the 529-point set `data/A1_top20.json` and A3 the 544-point set `data/A3_couv35.json`. In both,
points 0..508 are the 509 points of G509 (`data/g509_points.json`, identical to the points of the Lean
formalization, see `export_json.py`), and the other points are extra unit-distance candidates. The edges of
an ambient are **all** pairs of its points at distance exactly 1 (recomputed exactly).

> **Claim.** In A1 and in A3 there is no non-4-colorable subgraph (induced or not) with at most 508 vertices.

This is a **local** statement: it says nothing about unit-distance graphs that are not contained in these two
point sets, and nothing about the plane.

## Method

Implicit hitting sets (the framework of J. Parts, arXiv:2010.12665, §5; the loop is an implicit-hitting-set /
SMUS algorithm, cf. A. Ignatiev, A. Previti, M. Liffiton, J. Marques-Silva, "Smallest MUS extraction with
minimal hitting set dualization", CP 2015). An earlier attempt of the same kind, on a 757-vertex ambient, is
in kooshi/hadwiger-nelson (`data/m62`). What is added here is a checkable certificate for these two ambients.

1. *Cuts* (`hs.py`, not trusted). For a 4-coloring c of the whole ambient A, let mono(c) be its set of
   monochromatic edges. If U ⊆ V(A) and A[U] contains no edge of mono(c), then c|U properly colors A[U].
   Hence every U with A[U] non-4-colorable contains both ends of some edge of mono(c): the clause
   "∨_{e ∈ mono(c)} y_e" (a *cut*) is valid. `hs.py` generates such cuts (2164 for A1, 2603 for A3).
2. *Re-verification of the cuts* (`verify_cuts.py`): for each cut M, a 4-coloring c of the whole ambient with
   mono(c) = M exactly is found by SAT and re-checked edge by edge in Python; the colorings are stored in
   `data/*_cut_witnesses*.json`. All 2164 cuts of A1 were verified; for A3, the 847 cuts used by the CNF
   (782 cuts of the core and the 392 cuts with one edge, 327 in common).
3. *CNF* (`gen_cnf.py`): variables x_v (v ∈ U), y_e (both ends of e in U), clauses y_e → x_u, y_e → x_v,
   one clause per cut, and Σ x_v ≤ 508 encoded by a sequential counter written here (tested by brute force,
   `test_counter.py`: 9216 cases).
   - A1: all 2164 cuts, no degree constraint: 12 693 variables, 25 964 clauses.
   - A3: the cuts alone are satisfiable. Certified formula: 782 cuts (a core found by `core.py`, a heuristic
     selection only) + the 392 cuts with one edge, whose 446 end vertices are therefore forced (unit
     clauses), the bound Σ ≤ 62 on the 98 other vertices, and the degree constraint
     x_v → (at least 4 neighbours of v in U) for the 3 vertices 310, 322, 437: 4278 variables, 8533 clauses.
4. *Certificate*: CaDiCaL 2.1.2 (`--no-binary`) proves both CNFs unsatisfiable and emits DRAT proofs, which
   are checked by **two checkers written for this work**: `drat_check.py` (RUP + RAT, forward; its streaming
   variant `drat_check_stream.py` imports the same `Checker` class) and `rup_check.py` (written separately by
   an independent reviewing agent, RUP only).
5. *Non-vacuity* (`check_nonvacuity.py`): G509 itself satisfies all cuts, has minimum degree 4 and contains
   the forced vertices; the same CNFs with 509 instead of 508 are satisfiable. So the infeasibility comes from
   the bound 508 only.
6. *Second, independent path* (written separately by a reviewing agent): `verify_ambient_cuts.py` recomputes
   the exact edges of each ambient on all pairs with its own arithmetic and re-checks all stored witness
   colorings (A1: 2164/2164, A3: 847/847, all with mono(c) = M); `verify_cnf.py` rebuilds the four CNFs with
   its own counter and compares the multisets of clauses (identical).

**Why the infeasibility proves the claim.** Suppose some U ⊆ V(A), |U| ≤ 508, has A[U] non-4-colorable (a
non-induced subgraph on U is contained in A[U]); take one of minimum size. Set x_v = [v ∈ U],
y_e = [both ends of e in U], and the counter variables to their canonical values. Every cut clause holds
(step 1, with the verified coloring of step 2); the implications hold by definition; the forced vertices are
in U (cuts with one edge); for A3, each v ∈ U has at least 4 neighbours in U (otherwise a 4-coloring of the
smaller graph A[U − v] would extend to v, contradicting minimality); the counter is satisfied since
|U| ≤ 508. This satisfies the CNF, contradicting the checked DRAT proof. (For A1 the degree argument is not
used, so minimality of U is not needed.)

## Results recorded when the certificate was produced (November 2026)

| | A1 (529 vertices, 2587 edges) | A3 (544 vertices, 2690 edges) |
|---|---|---|
| cuts produced / used | 2164 / 2164 | 2603 / 847 (core 782 ∪ 392 with one edge) |
| CNF | 12 693 var., 25 964 clauses | 4278 var., 8533 clauses |
| CaDiCaL 2.1.2 | UNSAT, 0.18 s | UNSAT, 39 s |
| DRAT proof | 52 381 lines, 1.0 MB (`data/drat/`) | 1 697 929 lines, 212 MB (**not included**) |
| `drat_check.py` | valid: 20 857 RUP, 0 RAT, 101 s | valid (`drat_check_stream.py`): 859 943 RUP, 0 RAT, 4077 s, 1.2 GB |
| `rup_check.py` | valid: 20 421 RUP lemmas, 2 s | valid: 859 858 RUP lemmas, 1218 s, 113 MB |

(The two checkers count differently: `rup_check.py` stops at the first root conflict.) When this repository
was assembled, the A1 checks and the A3 `rup_check.py` check were rerun on the files of this directory (A3: same counts, valid, 1466 s,
110 MB), and both DRAT proofs were regenerated by CaDiCaL: byte-identical (sha256 below).

## Files

- `data/A1_top20.json`, `data/A3_couv35.json`: ambients (exact points, edges, initial witness colorings for
  `hs.py`); `data/g509_points.json`: the 509 points of G509 and its 2442 edges.
- `data/*_cuts.json`: final state of `hs.py` (cuts as sorted lists of indices into the sorted edge list;
  LB = UB = 509, done). `data/A3_core_cuts.txt`, `data/A3_core_deg.txt`: the A3 core (cut indices; vertices
  with a degree constraint).
- `data/*_cut_witnesses*.json`: one witness coloring per verified cut (output of `verify_cuts.py`).
- `data/cnf/`: the four CNFs (`*_cuts.cnf`, `*_core_forced.cnf`, and the two `*_control_K509.cnf`).
- `data/drat/A1_top20_cuts.drat`: the A1 proof
  (sha256 `fb08ede38567486b54ef5045b5a4079e05230dbdffec1f07d44e4baf90405c46`).
- The A3 proof `A3_couv35_core_forced.drat` (212 107 663 bytes, sha256
  `d0d716a0de67f4b4bb000113a3b0fd75bf848cf983515437bd878b5cdecc4bd5`) is not included; it is regenerated by
  the command below (CaDiCaL 2.1.2 is deterministic here: the regenerated file had this hash).
- Scripts: `udg.py`, `geom4.py` (exact arithmetic), `data_io.py` (JSON loading), `export_json.py` (one-off
  conversion from the original pickles, with exact round-trip check; the pickles are not distributed),
  `hs.py`, `verify_cuts.py`, `gen_cnf.py`, `core.py`, `test_counter.py`, `check_nonvacuity.py`,
  `drat_check.py`, `drat_check_stream.py`, `rup_check.py`, `verify_cnf.py`, `verify_ambient_cuts.py`.

## Reproducing

Requirements: Python 3 (tested with 3.12); `python-sat` (pysat) for `verify_cuts.py`, `core.py`,
`test_counter.py`, `hs.py`; `ortools` for `hs.py` only; CaDiCaL 2.1.2 (a binary `cadical` is shipped with
the Lean toolchain `leanprover/lean4:v4.35.0-rc2`, in its `bin/`). The checkers, `gen_cnf.py`,
`verify_cnf.py` and `verify_ambient_cuts.py` need only the standard library. Run from this directory; each
step was run under a 1200 MB memory limit (`systemd-run --user --scope -p MemoryMax=1200M -p MemorySwapMax=0 -q ...`).

```sh
# cuts (slow: about 1.5 h for A1, 40 min for the A3 subset)
python3 verify_cuts.py A1_top20 - out
python3 verify_cuts.py A3_couv35 data/A3_core_cuts.txt out
python3 test_counter.py
# CNFs (identical to data/cnf/ except for the first comment line)
python3 gen_cnf.py A1_top20 out/A1_top20_cuts.cnf
python3 gen_cnf.py A3_couv35 out/A3_couv35_core_forced.cnf --cuts data/A3_core_cuts.txt --degsel data/A3_core_deg.txt --forced
python3 check_nonvacuity.py out cadical
# proofs and checks
cadical --no-binary -q data/cnf/A1_top20_cuts.cnf out/A1_top20_cuts.drat
cadical --no-binary -q data/cnf/A3_couv35_core_forced.cnf out/A3_couv35_core_forced.drat
python3 -B drat_check.py data/cnf/A1_top20_cuts.cnf data/drat/A1_top20_cuts.drat
python3 -B drat_check_stream.py data/cnf/A3_couv35_core_forced.cnf out/A3_couv35_core_forced.drat   # about 70 min
python3 -I rup_check.py data/cnf/A1_top20_cuts.cnf data/drat/A1_top20_cuts.drat
python3 -I rup_check.py data/cnf/A3_couv35_core_forced.cnf out/A3_couv35_core_forced.drat            # about 20 min
# second, independent path
python3 -I verify_ambient_cuts.py A1_top20
python3 -I verify_ambient_cuts.py A3_couv35
python3 -I verify_cnf.py test; python3 -I verify_cnf.py A1; python3 -I verify_cnf.py A3
# the search itself (randomized, not needed to check the certificate)
python3 -B hs.py A1_top20 out/run_A1_top20
```

Not included: the script that built the ambients from a larger pool of candidate points (the claim is about
these two point sets, whatever their origin), and a third ambient A2 (559 vertices) whose search did not
terminate (lower bound 505, best 509).
