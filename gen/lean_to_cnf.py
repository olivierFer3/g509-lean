# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 olivierFer3 (code produced with Claude Code; see PROVENANCE.md)
"""Extracts the list `def F : List (List Nat) := [...]` from a Lean file (literals 2v / 2v+1) as DIMACS.
Usage: python3 gen/lean_to_cnf.py G509/CNF.lean out.cnf"""
import sys, re
s = open(sys.argv[1]).read()
i = s.index('def F : List (List Nat) := ['); j = s.index(']]', i)
cls = [[int(x) for x in c.split(',')] for c in re.findall(r'\[([0-9, ]+)\]', s[i:j + 2])]
d = lambda l: l // 2 if l % 2 == 0 else -(l // 2)
nv = max(l // 2 for c in cls for l in c)
with open(sys.argv[2], 'w') as f:
    f.write('p cnf %d %d\n' % (nv, len(cls)))
    for c in cls: f.write(' '.join(str(d(l)) for l in c) + ' 0\n')
print(nv, 'variables', len(cls), 'clauses')
