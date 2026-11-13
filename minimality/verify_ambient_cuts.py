# SPDX-License-Identifier: Apache-2.0
"""Independent check (written separately by a reviewing agent, without reusing verify_cuts.py or gen_cnf.py):
ambients A1/A3, cuts, link with G509. Reads the JSON files of data/ directly (raw rationals only; neither
geom4.py, udg.py nor data_io.py is used).

Usage: python3 -I verify_ambient_cuts.py A1_top20|A3_couv35
(a) separate exact arithmetic: x = Σ_d q_d √d (d squarefree, d | 165); coordinate = a + b·α,
    α = (√15+√55)/2 (α² = (35+5√33)/2). Exact edges recomputed on ALL pairs (floating-point filter
    |d²−1| < 1e-6 then exact check; also checks that the minimum of |d²−1| outside the edges is large).
(b) cuts: for each cut M having a witness coloring in data/<ambient>_cut_witnesses*.json: checks that the
    witness is a map V -> {0,1,2,3} and that mono(c) = M (hence mono(c) ⊆ M).
(c) G509 = vertices 0..508 of the ambient = points of g509_points.json; G509 meets every cut (non-vacuity).
"""
import sys, os, json, math
from fractions import Fraction as Fr
HERE = os.path.dirname(os.path.abspath(__file__)); D = os.path.join(HERE, "data")
name = sys.argv[1]
I = json.load(open(f"{D}/{name}.json")); st = json.load(open(f"{D}/{name}_cuts.json"))
n = I["n"]
PRIMES = (3, 5, 11)
def sqf(mask): return math.prod(p for i, p in enumerate(PRIMES) if mask >> i & 1)
def fromlist(t): return {sqf(m): Fr(q) for m, q in enumerate(t) if Fr(q) != 0}
def mul(a, b):
    r = {}
    for d1, x in a.items():
        for d2, y in b.items():
            g = math.gcd(d1, d2); d = d1 * d2 // (g * g); r[d] = r.get(d, 0) + x * y * g
    return {d: v for d, v in r.items() if v != 0}
def lin(a, b, s):
    r = dict(a)
    for d, v in b.items(): r[d] = r.get(d, 0) + s * v
    return {d: v for d, v in r.items() if v != 0}
ALPHA = {15: Fr(1, 2), 55: Fr(1, 2)}
assert mul(ALPHA, ALPHA) == {1: Fr(35, 2), 33: Fr(5, 2)}
def coord(l): return lin(fromlist(l["a"]), mul(fromlist(l["b"]), ALPHA), 1)
P = [(coord(x), coord(y)) for x, y in I["pts"]]
def fl(a): return sum(float(v) * math.sqrt(d) for d, v in a.items())
F = [(fl(x), fl(y)) for x, y in P]
key = lambda p: (tuple(sorted(p[0].items())), tuple(sorted(p[1].items())))
assert len({key(p) for p in P}) == n, "points not distinct"
E = set(); mind = 9.0
for i in range(n):
    xi, yi = F[i]
    for j in range(i + 1, n):
        d2 = (xi - F[j][0]) ** 2 + (yi - F[j][1]) ** 2
        if abs(d2 - 1) < 1e-6:
            dx = lin(P[i][0], P[j][0], -1); dy = lin(P[i][1], P[j][1], -1)
            if lin(mul(dx, dx), mul(dy, dy), 1) == {1: Fr(1)}: E.add((i, j)); continue
        mind = min(mind, abs(d2 - 1))
EA = sorted({(min(u, v), max(u, v)) for u, v in I["edges"]})
print(f"{name}: n={n}, edges in file={len(EA)}, exact edges recomputed={len(E)}, equal={E == set(EA)}, "
      f"min |d²−1| outside the edges = {mind:.3g}")
assert E == set(EA) and mind > 1e-6
# G509
g = json.load(open(f"{D}/g509_points.json"))["pts"]
G = [(coord(x), coord(y)) for x, y in g]
print("G509 = vertices 0..508:", len(G) == 509 and all(key(G[i]) == key(P[i]) for i in range(509)))
# cuts
cuts = [tuple(c) for c in st["cuts"]]; ne = len(EA)
print(f"cuts file: {len(cuts)} cuts; distinct {len(set(cuts))}; LB={st['LB']} UB={st['UB']} done={st['done']}; "
      f"sizes {min(map(len,cuts))}..{max(map(len,cuts))}; with 1 edge {sum(len(c)==1 for c in cuts)}")
assert all(tuple(sorted(set(c))) == tuple(c) and c and 0 <= c[0] and c[-1] < ne for c in cuts)
js = [f for f in os.listdir(D) if f.startswith(f"{name}_cut_witnesses") and f.endswith(".json")]
ok = {}
for f in js:
    R = json.load(open(f"{D}/{f}"))
    if "subset_size" in R or f.endswith("_subset.json"):
        sub = set(int(x) for x in open(f"{D}/A3_core_cuts.txt").read().split()) | {i for i, c in enumerate(cuts) if len(c) == 1}
        idx = sorted(sub)
    else: idx = list(range(len(cuts)))
    assert len(idx) == len(R["colorings"]), (f, len(idx), len(R["colorings"]))
    for ci, s in zip(idx, R["colorings"]):
        assert len(s) == n and set(s) <= set("0123")
        mono = {k for k, (u, v) in enumerate(EA) if s[u] == s[v]}
        if mono <= set(cuts[ci]): ok[ci] = (mono == set(cuts[ci]))
print(f"cuts with a valid witness (mono(c) ⊆ M): {len(ok)}; of which mono(c) = M: {sum(ok.values())}")
# G509 meets each cut (at least one edge of M inside G509): non-vacuity
inG = [all(u < 509 and v < 509 for u, v in [EA[e]]) for e in range(ne)]
print("G509 meets all the cuts:", all(any(inG[e] for e in c) for c in cuts))
