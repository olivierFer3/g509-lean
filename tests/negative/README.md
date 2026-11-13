# Negative tests (expected to FAIL)

These two files are copies of the valid chunk `G509/Test/RM5c/C0.lean` (a 23-vertex non-4-colorable test
graph) with one deliberate corruption each:

- `Neg1.lean`: the exported clause 279 is replaced by the empty clause `[]` (a wrong export);
- `Neg2.lean`: one entry of the hint list `hs0` (line 70) is replaced by a different packed list (wrong RUP hints).

The kernel must reject both: `decide +kernel` reports that the proposition `chunkCheck ... = true` is false.
They are deliberately **not** part of any Lake library (so `lake build` does not see them). To run them,
after `lake build G509Test`:

```sh
lake env lean tests/negative/Neg1.lean   # expected: error, exit code 1
lake env lean tests/negative/Neg2.lean   # expected: error, exit code 1
```
