# SPDX-License-Identifier: Apache-2.0
"""Brute-force test of the sequential counter atleast() of gen_cnf.py: for n ≤ 8, every r ∈ 0..n+1,
every assignment of the n literals (for positive as well as negative literals):
CNF + assignment + o satisfiable  ⇔  at least r true literals."""
import itertools, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gen_cnf import CNF, atleast
from pysat.solvers import Solver
nt = 0
for n in range(0, 9):
    for r in range(0, n + 2):
        for sign in (1, -1):
            F = CNF(n); lits = [sign * (i + 1) for i in range(n)]; o = atleast(F, lits, r)
            S = Solver(name="minisat22", bootstrap_with=F.cl)
            for bits in itertools.product([0, 1], repeat=n):
                ass = [(i + 1) if b else -(i + 1) for i, b in enumerate(bits)]
                cnt = sum(1 for l in lits if (l > 0) == bool(bits[abs(l) - 1]))
                assert S.solve(assumptions=ass + [o]) == (cnt >= r), (n, r, sign, bits)
                nt += 1
            S.delete()
print("sequential counter: %d cases tested, all correct" % nt)
