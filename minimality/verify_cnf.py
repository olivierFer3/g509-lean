# SPDX-License-Identifier: Apache-2.0
"""Independent check (written separately by a reviewing agent, without reusing gen_cnf.py): does the CNF encode
exactly "cuts + y_e → ends + [forced vertices] + Σx ≤ 508 [+ degree ≥ 4 for given vertices]"?
Method: reconstruction by separate code (sequential counter rewritten here, tested below in both directions),
then comparison of the multiset of clauses (each clause sorted) with the file, and check of the header.
Reads the JSON files of data/ directly (not through data_io.py).
Usage: python3 -I verify_cnf.py test | A1 | A3     [CNF directory, default data/cnf]
"""
import sys, os, json, itertools
from collections import Counter
HERE = os.path.dirname(os.path.abspath(__file__))
D = os.path.join(HERE, "data")
M = sys.argv[2] if len(sys.argv) > 2 else os.path.join(D, "cnf")

class Enc:
    def __init__(s, nv): s.nv = nv; s.cls = []
    def var(s): s.nv += 1; return s.nv
    def cl(s, *c): s.cls.append(list(c))

def card_ge(E, lits, r):
    """Literal o: o ⇒ at least r of lits; and every assignment with ≥ r true lits extends with o true.
    t(i,j) = "at least j true among the first i", 1 ≤ j ≤ min(i, r)."""
    m = len(lits)
    if r <= 0: o = E.var(); E.cl(o); return o
    if r > m: o = E.var(); E.cl(-o); return o
    t = {}
    for i in range(1, m + 1):
        for j in range(1, min(i, r) + 1):
            t[i, j] = E.var()
            a = [t[i - 1, j]] if (i - 1, j) in t else []          # t(i-1,j) absent = false
            E.cl(-t[i, j], *a, lits[i - 1])                      # needs t(i-1,j) or the i-th literal
            if j >= 2: E.cl(-t[i, j], *a, t[i - 1, j - 1])       # ... and t(i-1,j-1) (true if j = 1)
    return t[m, r]

def dpll(cls, assign):
    """Minimal SAT solver (for the small tests)."""
    cls = [c for c in cls]
    while True:
        changed = False; new = []
        for c in cls:
            if any(assign.get(abs(l)) == (l > 0) for l in c): continue
            c2 = [l for l in c if abs(l) not in assign]
            if not c2: return False
            if len(c2) == 1: assign[abs(c2[0])] = c2[0] > 0; changed = True
            new.append(c2)
        cls = new
        if not changed: break
    if not cls: return True
    v = abs(cls[0][0])
    for b in (True, False):
        a = dict(assign); a[v] = b
        if dpll(cls, a): return True
    return False

def test():
    nt = 0
    for m in range(0, 7):
        for r in range(0, m + 2):
            E = Enc(m); o = card_ge(E, list(range(1, m + 1)), r)
            for bits in itertools.product([False, True], repeat=m):
                a = {i + 1: b for i, b in enumerate(bits)}; a[o] = True
                sat = dpll(E.cls, a); nt += 1
                assert sat == (sum(bits) >= r), (m, r, bits)
            # negated literals too
            E = Enc(m); o = card_ge(E, [-(i + 1) for i in range(m)], r)
            for bits in itertools.product([False, True], repeat=m):
                a = {i + 1: b for i, b in enumerate(bits)}; a[o] = True
                assert dpll(E.cls, a) == (m - sum(bits) >= r); nt += 1
    print(f"counter test: {nt} cases, all as expected (≥ r true ⇔ satisfiable with o)")

def build(name, sel=None, deg=(), forced=False, K=508):
    I = json.load(open(f"{D}/{name}.json")); st = json.load(open(f"{D}/{name}_cuts.json"))
    n = I["n"]; EA = sorted({(min(u, v), max(u, v)) for u, v in I["edges"]})
    allcuts = [tuple(c) for c in st["cuts"]]; cuts = allcuts if sel is None else [allcuts[i] for i in sel]
    used = sorted(set().union(*map(set, cuts)))
    y = {e: n + 1 + k for k, e in enumerate(used)}
    E = Enc(n + len(used))
    for e in used: E.cl(-y[e], EA[e][0] + 1); E.cl(-y[e], EA[e][1] + 1)
    for C in cuts: E.cl(*[y[e] for e in C])
    if forced:
        single = sorted({C[0] for C in allcuts if len(C) == 1})
        Fo = sorted({w for e in single for w in EA[e]})
        for e in single:
            if e not in y:
                y[e] = E.var(); E.cl(-y[e], EA[e][0] + 1); E.cl(-y[e], EA[e][1] + 1)
            E.cl(y[e])
        rest = [v for v in range(n) if v not in set(Fo)]
        o = card_ge(E, [-(v + 1) for v in rest], len(rest) - (K - len(Fo))); E.cl(o)
        info = dict(forced=len(Fo), free=len(rest), bound_on_free=K - len(Fo))
    else:
        o = card_ge(E, [-(v + 1) for v in range(n)], n - K); E.cl(o); info = {}
    if deg:
        adj = [[] for _ in range(n)]
        for u, v in EA: adj[u].append(v); adj[v].append(u)
        for v in deg:
            ov = card_ge(E, [u + 1 for u in adj[v]], 4); E.cl(-(v + 1), ov)
        info["deg"] = {v: len(adj[v]) for v in deg}
    info.update(n=n, cuts=len(cuts), y=len(used))
    return E, info

def readcnf(p):
    hdr = None; cls = []; cur = []
    for line in open(p):
        if line.startswith("c"): continue
        if line.startswith("p"): hdr = tuple(map(int, line.split()[2:])); continue
        for t in line.split():
            x = int(t)
            if x == 0: cls.append(tuple(sorted(cur))); cur = []
            else: cur.append(x)
    return hdr, cls

def compare(E, path):
    hdr, cls = readcnf(path)
    mine = Counter(tuple(sorted(c)) for c in E.cls)
    same = mine == Counter(cls)
    print(f"  {os.path.basename(path)}: header {hdr}; rebuilt ({E.nv}, {len(E.cls)}); identical clauses: {same}")
    return same and hdr == (E.nv, len(E.cls))

if __name__ == "__main__":
    w = sys.argv[1]
    if w == "test": test()
    elif w == "A1":
        E, info = build("A1_top20"); print("A1", info); assert compare(E, f"{M}/A1_top20_cuts.cnf")
        E, info = build("A1_top20", K=509); print("A1 K=509", info); compare(E, f"{M}/A1_top20_control_K509.cnf")
    elif w == "A3":
        sel = [int(x) for x in open(f"{D}/A3_core_cuts.txt").read().split()]
        deg = [int(x) for x in open(f"{D}/A3_core_deg.txt").read().split()]
        print("A3 core: indices", len(sel), "distinct", len(set(sel)), "max", max(sel), "; degree for", deg)
        E, info = build("A3_couv35", sel, deg, forced=True); print("A3 forced", info)
        assert compare(E, f"{M}/A3_couv35_core_forced.cnf")
        E, info = build("A3_couv35", sel, deg, forced=True, K=509); compare(E, f"{M}/A3_couv35_control_K509.cnf")
