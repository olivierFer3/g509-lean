# SPDX-License-Identifier: Apache-2.0
"""Non-vacuity check: H = G509 (vertices 0..508, 509 vertices) satisfies all the cuts, the selected degree
constraints, and contains the "forced" vertices. Hence the CNFs are infeasible ONLY because of the bound
Σx ≤ 508: an encoding error making the CNF trivially contradictory would be detected here (and by CaDiCaL
below: the same CNF with K = 509 must be SATISFIABLE).
Usage: python3 check_nonvacuity.py [output_dir] [cadical_binary]     (defaults: ./out, `cadical` on PATH)"""
import sys, os, subprocess
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from gen_cnf import build, write
from data_io import load_ambient, load_cuts, DATA
OUT = sys.argv[1] if len(sys.argv) > 1 else os.path.join(os.getcwd(), "out")
CAD = sys.argv[2] if len(sys.argv) > 2 else "cadical"
os.makedirs(OUT, exist_ok=True)
for name, opts in [("A1_top20", {}), ("A3_couv35", dict(sel="A3_core_cuts.txt", deg="A3_core_deg.txt", forced=True))]:
    I = load_ambient(name); st = load_cuts(name)
    EA = sorted({(min(u, v), max(u, v)) for u, v in I["edges"]}); H = set(range(509))
    ok = all(any(set(EA[e]) <= H for e in C) for C in st["cuts"])
    adj = [[] for _ in range(I["n"])]
    for u, v in EA: adj[u].append(v); adj[v].append(u)
    mindeg = min(sum(1 for u in adj[v] if u in H) for v in H)
    print(f"{name}: G509 satisfies all the {len(st['cuts'])} cuts: {ok}; minimum degree of G509 in itself: {mindeg}")
    sel = [int(x) for x in open(os.path.join(DATA, opts["sel"])).read().split()] if "sel" in opts else None
    deg = [int(x) for x in open(os.path.join(DATA, opts["deg"])).read().split()] if "deg" in opts else False
    F, info = build(name, deg, sel, K=509, forced=opts.get("forced", False))
    p = os.path.join(OUT, f"{name}_control_K509.cnf"); write(F, info, p)
    r = subprocess.run([CAD, "-q", p], capture_output=True, text=True)
    print(f"  same CNF with K = 509: {[l for l in r.stdout.splitlines() if l.startswith('s ')]} (expected SATISFIABLE)")
