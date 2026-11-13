# SPDX-License-Identifier: Apache-2.0
"""Re-verification of ALL the cuts of an ambient (A1_top20, A3_couv35).

Usage: python3 verify_cuts.py <ambient_name> [index_file] [output_dir]     (e.g. A1_top20)
  index_file: if given (and not "-"), only these cuts (plus all the cuts with one edge) are verified.
  output_dir: default ./out

What hs.py stores: for each cut, only the sorted tuple M of the edge indices (in the sorted edge list of the
ambient) that are monochromatic under the extension c (hs.py, `extend`, `add_cut`). The coloring c itself, and
the set S it comes from, are NOT stored. What can be checked, and is checked here:

  (a) the edges of the ambient are recomputed in exact arithmetic from the stored coordinates; they must be
      equal to those of the file;
  (b) for EACH cut M: there is a map c : V(A) -> {0,1,2,3} whose set of monochromatic edges is EXACTLY M
      (SAT: c proper on A - M, and c(u) = c(v) for uv in M). The coloring c found is re-checked edge by edge
      in Python, without trusting the solver. This is exactly the property "M is the set of monochromatic
      edges of an extension to the ambient"; it implies the validity of the cut: every H such that A[H] has no
      edge of M is properly colored by c|H.
      If exact equality failed, the weaker (sufficient) condition mono(c) ⊆ M is tested.
  (c) edge indices within bounds, non-empty cuts, no duplicates; consistency of LB/UB/done of the file.
Output: a JSON file with, for each cut, the coloring found (one digit per vertex), for re-checking.
(The distributed files data/*_cut_witnesses*.json are the outputs of this script, with English keys.)
"""
import sys, os, time, math, json
from fractions import Fraction
from math import gcd
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from data_io import load_ambient, load_cuts

name = sys.argv[1]
SUB = sys.argv[2] if len(sys.argv) > 2 and sys.argv[2] != "-" else None
OUT = sys.argv[3] if len(sys.argv) > 3 else os.path.join(os.getcwd(), "out")
I = load_ambient(name); st = load_cuts(name)
N = I["n"]; EA = sorted({(min(u, v), max(u, v)) for u, v in I["edges"]})
assert I["k"] == 4
print(f"{name}: n = {N}, edges (file) = {len(EA)}, cuts = {len(st['cuts'])}, LB = {st['LB']}, "
      f"UB = {st['UB']}, done = {st['done']}, it = {st['it']}", flush=True)

# ---------- (a) exact edges ----------
PR = [3, 5, 11]
def kvec(k):
    d = {}
    for m, a in enumerate(k.c):
        if a != 0:
            n = 1
            for i in range(3):
                if (m >> i) & 1: n *= PR[i]
            d[n] = d.get(n, Fraction(0)) + Fraction(a)
    return d
def mul(a, b):
    r = {}
    for m, x in a.items():
        for n, y in b.items():
            g = gcd(m, n); k = (m // g) * (n // g); r[k] = r.get(k, Fraction(0)) + x * y * g
    return {k: v for k, v in r.items() if v != 0}
def add(a, b, s=1):
    r = dict(a)
    for k, v in b.items(): r[k] = r.get(k, Fraction(0)) + s * v
    return {k: v for k, v in r.items() if v != 0}
ALPHA = {15: Fraction(1, 2), 55: Fraction(1, 2)}
def lvec(l): return add(kvec(l.a), mul(kvec(l.b), ALPHA))
P = [(lvec(x), lvec(y)) for x, y in I["pts"]]
fl = lambda a: sum(float(v) * math.sqrt(k) for k, v in a.items())
Fp = [(fl(x), fl(y)) for x, y in P]
assert len({(tuple(sorted(x.items())), tuple(sorted(y.items()))) for x, y in P}) == N, "points not distinct"
E = []
for i in range(N):
    for j in range(i + 1, N):
        d2 = (Fp[i][0] - Fp[j][0]) ** 2 + (Fp[i][1] - Fp[j][1]) ** 2
        if abs(d2 - 1) < 1e-3:
            dx, dy = add(P[i][0], P[j][0], -1), add(P[i][1], P[j][1], -1)
            if add(mul(dx, dx), mul(dy, dy)) == {1: Fraction(1)}: E.append((i, j))
same = set(E) == set(EA)
print(f"(a) exact edges recomputed: {len(E)}; equal to those of the file: {same}", flush=True)
assert same

# ---------- (b) each cut ----------
from pysat.solvers import Solver
var = lambda v, k: 4 * v + k + 1
A0 = 4 * N + 1                 # a_e : "the edge e must be bichromatic"
Q0 = A0 + len(EA)              # q_e : "the edge e must be monochromatic"
S = Solver(name="cadical195")
for v in range(N):
    S.add_clause([var(v, k) for k in range(4)])
    for k in range(4):
        for l in range(k + 1, 4): S.add_clause([-var(v, k), -var(v, l)])
for i, (u, v) in enumerate(EA):
    for k in range(4):
        S.add_clause([-(A0 + i), -var(u, k), -var(v, k)])
        S.add_clause([-(Q0 + i), -var(u, k), var(v, k)]); S.add_clause([-(Q0 + i), var(u, k), -var(v, k)])
cuts = st["cuts"]
res = {"ambient": name, "n": N, "edges": len(EA), "cuts": len(cuts), "exact": 0, "included_only": 0,
       "invalid": [], "anomalies": [], "colorings": []}
if len(set(cuts)) != len(cuts): res["anomalies"].append("duplicate cuts")
t0 = time.time()
todo = None
if SUB:
    todo = set(int(x) for x in open(SUB).read().split()) | {i for i, C in enumerate(cuts) if len(C) == 1}
    res["subset_size"] = len(todo); print(f"subset: {len(todo)} cuts (core + cuts with one edge)", flush=True)
for ci, C in enumerate(cuts):
    if todo is not None and ci not in todo: continue
    M = set(C)
    if not M: res["anomalies"].append(f"cut {ci} empty")
    if any(not (0 <= e < len(EA)) for e in M): res["anomalies"].append(f"cut {ci}: index out of bounds"); continue
    if tuple(sorted(M)) != tuple(C): res["anomalies"].append(f"cut {ci} not sorted")
    ass = [(Q0 + i) if i in M else (A0 + i) for i in range(len(EA))]
    kind = None
    if S.solve(assumptions=ass): kind = "exact"
    elif S.solve(assumptions=[A0 + i for i in range(len(EA)) if i not in M]): kind = "included"
    if kind is None: res["invalid"].append(ci); print(f"  CUT {ci} INVALID", flush=True); continue
    m = S.get_model()
    col = [next(k for k in range(4) if m[var(v, k) - 1] > 0) for v in range(N)]
    mono = {i for i, (u, v) in enumerate(EA) if col[u] == col[v]}       # check independent of the solver
    if kind == "exact":
        assert mono == M, f"cut {ci}: Python check failed"
        res["exact"] += 1
    else:
        assert mono <= M, f"cut {ci}: Python check failed"
        res["included_only"] += 1
    res["colorings"].append("".join(map(str, col)))
    if (ci + 1) % 200 == 0: print(f"  {ci+1} cuts verified ({time.time()-t0:.0f} s)", flush=True)
res["seconds"] = round(time.time() - t0, 1)
sizes = [len(C) for C in cuts]
res["min_size"] = min(sizes); res["max_size"] = max(sizes); res["cuts_with_1_edge"] = sum(s == 1 for s in sizes)
res["state"] = {"LB": st["LB"], "UB": st["UB"], "done": st["done"], "it": st["it"], "H_len": len(st["H"]) if st["H"] else None}
# (c) consistency of the state
if not (st["done"] and st["LB"] == 509 and st["UB"] == 509):
    res["anomalies"].append("unexpected final state")
print(f"(b) {len(cuts)} cuts: exact (mono(c) = M) {res['exact']}; only mono(c) ⊆ M "
      f"{res['included_only']}; INVALID {len(res['invalid'])}; anomalies {res['anomalies']}; "
      f"sizes {res['min_size']}..{res['max_size']}, with 1 edge {res['cuts_with_1_edge']}; {res['seconds']} s", flush=True)
os.makedirs(OUT, exist_ok=True)
suf = "_subset" if SUB else ""
dst = os.path.join(OUT, f"{name}_cut_witnesses{suf}.json"); tmp = dst + ".tmp"
json.dump(res, open(tmp, "w")); os.replace(tmp, dst)
print("RESULT:", "ALL CUTS VALID" if not res["invalid"] and not res["anomalies"] else "ANOMALY", flush=True)
