# SPDX-License-Identifier: Apache-2.0
"""Reduction: a sufficient subset of the cuts (and of the degree constraints).

Usage: python3 core.py <ambient_name> [--deg] <output_prefix>
Each cut (and each degree constraint for a vertex v) gets a selector; CaDiCaL (pysat, without proof: this is
only a selection HEURISTIC) is asked for an unsatisfiable core, which is reduced by repeated extractions. The
result is a plain LIST of indices: the final CNF is rebuilt by gen_cnf.py with these constraints only, then
proved UNSAT by CaDiCaL + a DRAT proof checked by drat_check.py. Correctness therefore does not depend on this
step: removing valid cuts (or degree constraints) only weakens the formula; if the weakened formula is UNSAT,
so is the full one. (The core is found with a time limit and solver heuristics, so a new run may select a
different core; the distributed one is data/A3_core_cuts.txt, data/A3_core_deg.txt.)
"""
import sys, os, time
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from gen_cnf import build, CNF, atleast
from data_io import load_ambient, load_cuts
from pysat.solvers import Solver

name = sys.argv[1]; deg = "--deg" in sys.argv; out = sys.argv[-1]
F, info = build(name, deg=False)          # without degree: the selectors are added by hand below
I = load_ambient(name); st = load_cuts(name)
n = I["n"]; EA = sorted({(min(u, v), max(u, v)) for u, v in I["edges"]}); cuts = st["cuts"]
ncut = len(cuts)
# locate the cut clauses in F (they follow the 2·|y| implication clauses)
first = 2 * info["y"]; cutcl = F.cl[first:first + ncut]; rest = F.cl[:first] + F.cl[first + ncut:]
sel = {}
G = CNF(F.nv); G.cl = list(rest)
for i, c in enumerate(cutcl):
    s = G.new(); sel[s] = ("cut", i); G.add(c + [-s])
if deg:
    adj = [[] for _ in range(n)]
    for u, v in EA: adj[u].append(v); adj[v].append(u)
    for v in range(n):
        ov = atleast(G, [u + 1 for u in adj[v]], 4); s = G.new(); sel[s] = ("deg", v); G.add([-s, -(v + 1), ov])
S = Solver(name="cadical195", bootstrap_with=G.cl)
A = sorted(sel)
t = time.time()
for it in range(6):
    r = S.solve(assumptions=A)
    assert r is False, "formula satisfiable: no core"
    core = sorted(set(S.get_core())); print(f"extraction {it}: core of {len(core)} selectors ({time.time()-t:.0f} s)", flush=True)
    if len(core) == len(A): break
    A = core
# bounded greedy reduction: try to remove each selector (conflict budget)
keep = list(A); i = 0; tr = time.time()
while i < len(keep) and time.time() - tr < float(os.environ.get("TMIN", "600")):
    trial = keep[:i] + keep[i + 1:]
    S.conf_budget(20000); r = S.solve_limited(assumptions=trial)
    if r is False:
        core = set(S.get_core()); keep = [x for x in trial if x in core]
    else: i += 1
print(f"after greedy reduction: {len(keep)} selectors ({time.time()-t:.0f} s)", flush=True)
cs = sorted(sel[s][1] for s in keep if sel[s][0] == "cut"); ds = sorted(sel[s][1] for s in keep if sel[s][0] == "deg")
open(out + "_cuts.txt", "w").write(" ".join(map(str, cs)) + "\n")
open(out + "_deg.txt", "w").write(" ".join(map(str, ds)) + "\n")
print(f"kept: {len(cs)} cuts out of {ncut}; {len(ds)} degree constraints out of {n if deg else 0}", flush=True)
