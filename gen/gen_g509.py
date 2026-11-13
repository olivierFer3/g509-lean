# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 olivierFer3. Released under Apache 2.0 license as described in the file LICENSE.
# Authors: olivierFer3 (code produced with Claude Code; see PROVENANCE.md)
"""Generates the exact data of G509 (Parts) for Lean, from vtx/509_parts.vtx
(repository vasnesterov/HadwigerNelson, commit ad7843546da5f4db4fcf9827e0951f34295ad7cc).
Usage: python3 gen/gen_g509.py vtx/509_parts.vtx gen/g509.json
Coordinates in Q(√3,√5,√11); flat basis 1,√3,√5,√15,√11,√33,√55,√165
(nested order: ((a + b√3) + (c + d√3)√5) + (...)√11).
Simplifications: Sqrt[(5*(7±Sqrt[33]))/2] = (√55 ± √15)/2 ; Sqrt[11/3] = √33/3."""
import sys, re, math, json
from fractions import Fraction as F
from math import lcm
import sympy as sp

path = sys.argv[1]; out = sys.argv[2]
s3, s5, s11 = sp.sqrt(3), sp.sqrt(5), sp.sqrt(11)
BASIS = [1, s3, s5, s3*s5, s11, s3*s11, s5*s11, s3*s5*s11]   # 1,√3,√5,√15,√11,√33,√55,√165
SQ = {3: s3, 5: s5, 11: s11, 15: s3*s5, 33: s3*s11, 55: s5*s11, 165: s3*s5*s11}

A, B, C = sp.symbols('a b c')   # a=√3, b=√5, c=√11
SYM = {3: A, 5: B, 11: C, 15: A*B, 33: A*C, 55: B*C, 165: A*B*C}

def conv(txt):
    t = txt.replace('Sqrt[(5*(7 + Sqrt[33]))/2]', '((s55 + s15)/2)')
    t = t.replace('Sqrt[(5*(7 - Sqrt[33]))/2]', '((s55 - s15)/2)')
    t = t.replace('Sqrt[11/3]', '(s33/3)')
    t = re.sub(r'Sqrt\[(\d+)\]', r's\1', t)
    assert 'Sqrt' not in t and '[' not in t, t
    t = re.sub(r'(?<![s\d])(\d+)', r'Integer(\1)', t)
    env = {'Integer': sp.Integer}
    for n, v in SYM.items(): env['s%d' % n] = v
    return txt, sp.together(eval(t, env))

def coeffs(arg):
    txt, e = arg
    num, den = sp.fraction(e)
    den = sp.Poly(den, A, B, C)
    assert len(den.terms()) == 1, txt
    (m, j0, k0), kq = den.terms()[0]
    assert j0 == 0 and k0 == 0, txt
    p = sp.Poly(sp.expand(num * A**m), A, B, C)
    scale = F(1, int(kq) * 3**m)
    res = [F(0)] * 8
    for (i, j, k), q in p.terms():
        q = F(int(sp.numer(q)), int(sp.denom(q))) * scale
        q *= F(3) ** (i // 2) * F(5) ** (j // 2) * F(11) ** (k // 2)
        res[(i % 2) + 2 * (j % 2) + 4 * (k % 2)] += q
    # independent numerical check (mpmath on the Mathematica text)
    t = txt.replace('Sqrt[', 'sqrt(').replace(']', ')')
    import mpmath
    mpmath.mp.dps = 40
    ref = eval(re.sub(r'(?<![\w.])(\d+)', r'mpmath.mpf(\1)', t), {'sqrt': mpmath.sqrt, 'mpmath': mpmath})
    val = sum(mpmath.mpf(res[t2].numerator) / res[t2].denominator * mpmath.sqrt(BV[t2]) for t2 in range(8))
    assert abs(val - ref) < mpmath.mpf(10) ** -30, (txt, res)
    return res
BV = [1, 3, 5, 15, 11, 33, 55, 165]

lines = [l.strip() for l in open(path) if l.strip()]
pts = []
for l in lines:
    assert l[0] == '{' and l[-1] == '}'
    x, y = l[1:-1].split(', ')
    pts.append((coeffs(conv(x)), coeffs(conv(y))))
n = len(pts)
D = 1
for X, Y in pts:
    for q in X + Y: D = lcm(D, q.denominator)
ipts = [([int(q * D) for q in X], [int(q * D) for q in Y]) for X, Y in pts]

# exact arithmetic in Z[√3,√5,√11] (flat basis, binary index)
def mul(u, v):
    r = [0] * 8
    for i in range(8):
        if u[i] == 0: continue
        for j in range(8):
            if v[j] == 0: continue
            k = i ^ j; com = i & j
            f = (3 if com & 1 else 1) * (5 if com & 2 else 1) * (11 if com & 4 else 1)
            r[k] += u[i] * v[j] * f
    return r
fb = [float(b) for b in BASIS]
fv = lambda u: sum(u[i] * fb[i] for i in range(8))
fp = [(fv(X) / D, fv(Y) / D) for X, Y in ipts]
edges = []
for i in range(n):
    for j in range(i + 1, n):
        dx = fp[i][0] - fp[j][0]; dy = fp[i][1] - fp[j][1]
        if abs(dx * dx + dy * dy - 1) < 1e-6:
            DX = [a - b for a, b in zip(ipts[i][0], ipts[j][0])]
            DY = [a - b for a, b in zip(ipts[i][1], ipts[j][1])]
            s = [a + b for a, b in zip(mul(DX, DX), mul(DY, DY))]
            assert s == [D * D] + [0] * 7, (i, j, s)
            edges.append((i, j))
# distinctness: floats
mind = min(math.hypot(fp[i][0]-fp[j][0], fp[i][1]-fp[j][1]) for i in range(n) for j in range(i+1, n))
print('n =', n, 'D =', D, 'edges =', len(edges), 'min dist =', mind,
      'max |coef| =', max(abs(c) for X, Y in ipts for c in X + Y))
json.dump({'D': D, 'pts': ipts, 'edges': edges}, open(out, 'w'))
