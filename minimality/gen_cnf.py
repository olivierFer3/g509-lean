# SPDX-License-Identifier: Apache-2.0
"""CNF "all (selected) cuts + at most K vertices kept" (K = 508 by default).

Usage: python3 gen_cnf.py <ambient_name> <output.cnf> [--deg | --degsel vertex_file] [--cuts index_file] [--K 508] [--forced]

Variables:
  x_v  = v + 1                       (v ∈ H)                       v = 0..n-1
  y_e  = n + 1 + j                   (both ends of the edge e are in H), e ranges over the edges
                                      occurring in at least one cut (j = rank of e in that list)
  then the auxiliary variables of the counters.
Clauses:
  (¬y_e ∨ x_u), (¬y_e ∨ x_v)         for e = uv
  (∨_{e ∈ M} y_e)                    for each selected cut M
  Σ_v x_v ≤ K, written Σ_v ¬x_v ≥ r with r = n − K, by a sequential counter WRITTEN HERE (see atleast()).
  --deg : x_v → Σ_{u ∈ N(v)} x_u ≥ 4 (degree constraint, see README), same counter, final clause (¬x_v ∨ s).
  --forced: the ends of the cuts with ONE edge are forced (see build()).
No dependency on pysat.card: the encoding is entirely here, and tested by brute force (test_counter.py).
"""
import sys, os
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from data_io import load_ambient, load_cuts

class CNF:
    def __init__(s, nv): s.nv = nv; s.cl = []
    def new(s): s.nv += 1; return s.nv
    def add(s, c): s.cl.append(list(c))

def atleast(F, lits, r):
    """Returns a literal o such that: (i) every assignment of lits with at least r true literals extends to the
    auxiliary variables making o true; (ii) every assignment satisfying the added clauses with o true has at
    least r true lits. s[i][j] (1 ≤ j ≤ min(i, r)) means "at least j true among lits[0..i-1]".
    Clauses (j ≥ 1): s[i][j] → s[i-1][j] ∨ lits[i-1] ;  s[i][j] → s[i-1][j] ∨ s[i-1][j-1]
    with s[i-1][j] = false if j > i-1, s[i-1][0] = true.
    (ii) by induction on i: if s[i][j] is true then either s[i-1][j] (so ≥ j true before), or lits[i-1] and
    s[i-1][j-1] (so ≥ j-1 true before, plus lits[i-1]). (i): set s[i][j] = [#true(lits[0..i-1]) ≥ j]."""
    n = len(lits)
    if r <= 0:
        o = F.new(); F.add([o]); return o
    if r > n:
        o = F.new(); F.add([-o]); return o
    s = [[None] * (r + 1) for _ in range(n + 1)]
    for i in range(1, n + 1):
        for j in range(1, min(i, r) + 1):
            v = F.new(); s[i][j] = v
            prev_j = s[i - 1][j] if j <= i - 1 else None          # None = false
            prev_jm = s[i - 1][j - 1] if j - 1 >= 1 else True     # True = true (j-1 = 0)
            # s → prev_j ∨ lit
            F.add([-v] + ([prev_j] if prev_j else []) + [lits[i - 1]])
            # s → prev_j ∨ prev_jm
            if prev_jm is not True:
                F.add([-v] + ([prev_j] if prev_j else []) + [prev_jm])
    return s[n][r]

def build(name, deg=False, sel=None, K=508, forced=False):
    I = load_ambient(name); st = load_cuts(name)
    n = I["n"]; EA = sorted({(min(u, v), max(u, v)) for u, v in I["edges"]})
    cuts = st["cuts"] if sel is None else [st["cuts"][i] for i in sel]
    used = sorted({e for C in cuts for e in C}); yid = {e: n + 1 + j for j, e in enumerate(used)}
    F = CNF(n + len(used))
    for e in used:
        u, v = EA[e]; F.add([-yid[e], u + 1]); F.add([-yid[e], v + 1])
    for C in cuts: F.add([yid[e] for e in C])
    if forced:
        # FORCED vertices: ends of the cuts with ONE edge (all cuts, selected or not: each one is valid).
        # Every admissible H contains them; the unit clauses are added and only the other vertices are counted:
        # Σ_{v ∉ Fo} x_v ≤ K − |Fo| (equivalent to Σ x ≤ K as soon as Fo ⊆ H).
        Fo = sorted({w for C in st["cuts"] if len(C) == 1 for w in EA[C[0]]})
        for e in sorted({C[0] for C in st["cuts"] if len(C) == 1}):
            if e not in yid:
                yid[e] = F.new(); u, v = EA[e]; F.add([-yid[e], u + 1]); F.add([-yid[e], v + 1])
            F.add([yid[e]])
        rest = [v for v in range(n) if v not in set(Fo)]
        o = atleast(F, [-(v + 1) for v in rest], len(rest) - (K - len(Fo))); F.add([o])
    else:
        o = atleast(F, [-(v + 1) for v in range(n)], n - K); F.add([o])
    if deg:
        adj = [[] for _ in range(n)]
        for u, v in EA: adj[u].append(v); adj[v].append(u)
        for v in (range(n) if deg is True else deg):
            ov = atleast(F, [u + 1 for u in adj[v]], 4); F.add([-(v + 1), ov])
    return F, dict(n=n, edges=len(EA), cuts=len(cuts), y=len(used), K=K,
                   deg=(deg if isinstance(deg, bool) else "%d vertices" % len(deg)))

def write(F, info, path):
    tmp = path + ".tmp"
    with open(tmp, "w") as f:
        f.write("c %s\n" % info)
        f.write("p cnf %d %d\n" % (F.nv, len(F.cl)))
        for c in F.cl: f.write(" ".join(map(str, c)) + " 0\n")
    os.replace(tmp, path)

if __name__ == "__main__":
    a = sys.argv[1:]; name, out = a[0], a[1]
    deg = "--deg" in a
    if "--degsel" in a: deg = [int(x) for x in open(a[a.index("--degsel") + 1]).read().split()]
    K = int(a[a.index("--K") + 1]) if "--K" in a else 508
    sel = [int(x) for x in open(a[a.index("--cuts") + 1]).read().split()] if "--cuts" in a else None
    F, info = build(name, deg, sel, K, forced="--forced" in a)
    write(F, info, out)
    print("CNF", out, ":", F.nv, "variables,", len(F.cl), "clauses;", info)
