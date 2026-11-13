# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 olivierFer3. Released under Apache 2.0 license as described in the file LICENSE.
# Authors: olivierFer3 (code produced with Claude Code; see PROVENANCE.md)
"""Backward trimming of an LRAT proof: keeps only the steps needed for the empty clause (like drat-trim -L).
Output: textual LRAT without deletions.
Usage: python3 gen/lrat_trim.py in.lrat out_trim.lrat"""
import sys
src, dst = sys.argv[1:3]
steps = {}; order = []
for l in open(src):
    t = l.split()
    if not t or t[1] == 'd': continue
    z = t.index('0', 1)
    i = int(t[0]); c = t[1:z]; h = [int(x) for x in t[z + 1:-1]]
    steps[i] = (c, h); order.append(i)
    if not c: break
need = {order[-1]}; stack = [order[-1]]
while stack:
    i = stack.pop()
    for h in steps[i][1]:
        if h in steps and h not in need: need.add(h); stack.append(h)
kept = [i for i in order if i in need]
with open(dst, 'w') as f:
    for i in kept:
        c, h = steps[i]
        f.write('%d %s0 %s0\n' % (i, ''.join(x + ' ' for x in c), ''.join('%d ' % x for x in h)))
print('steps', len(order), '->', len(kept), 'literals', sum(len(steps[i][0]) for i in kept), 'hints', sum(len(steps[i][1]) for i in kept))
