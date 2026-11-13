# SPDX-License-Identifier: Apache-2.0
"""Exact geometry.
NB: α turns out to belong to K (see CORRECTION below): all points are in K.

Field L = K(α), K = Q(√3,√5,√11) (class K of udg.py), α = √(5(7+√33)/2), α² = (35+5√33)/2.
(√(5(7−√33)/2) = 10/α = α(7−√33)/4, checked by an assertion.) This field contains the coordinates of G509 (Parts),
of G510/G529 (Heule) and of the other graphs considered (which lie in K).

- element of L: pair (a, b) of elements of K, representing a + b·α.
- point: pair (x, y) of elements of L; hash key = tuple of the 32 rationals.
- reading of a .vtx file (Mathematica format "{x, y}") by a hand-written parser (no eval).
- edges: candidate pairs in floating point (grid), then EXACT confirmation |p−q|² = 1 in L.
- unit vectors of the graph + hash table of the points: neighbours of a new point without comparing all pairs.
"""
import math, re, pickle, sys, os
from fractions import Fraction as F
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from udg import K, PR

KZ = K.rat(0); K1 = K.rat(1)
SQ33 = K([F(0)] * 5 + [F(1)] + [F(0)] * 2)          # masque 0b101 = √3·√11
ALPHA2 = K.rat(F(35, 2)) + K([F(0)] * 5 + [F(5, 2)] + [F(0)] * 2)
ALPHA_F = math.sqrt(35 / 2 + 2.5 * math.sqrt(33))

def kconj(x, i):
    return K(a if not (m >> i) & 1 else -a for m, a in enumerate(x.c))

def kinv(x):
    assert not x.is_zero()
    prod = K1
    for s in range(1, 8):
        y = x
        for i in range(3):
            if (s >> i) & 1: y = kconj(y, i)
        prod = prod * y
    nrm = (x * prod).c
    assert all(a == 0 for a in nrm[1:])
    return K(a / nrm[0] for a in prod.c)

class L:
    __slots__ = ("a", "b")
    def __init__(s, a, b=None): s.a = a; s.b = KZ if b is None else b
    def __add__(s, o): return L(s.a + o.a, s.b + o.b)
    def __sub__(s, o): return L(s.a - o.a, s.b - o.b)
    def __neg__(s): return L(-s.a, -s.b)
    def __mul__(s, o): return L(s.a * o.a + s.b * o.b * ALPHA2, s.a * o.b + s.b * o.a)
    def inv(s):
        d = s.a * s.a - s.b * s.b * ALPHA2
        di = kinv(d)
        return L(s.a * di, -(s.b * di))
    def __truediv__(s, o): return s * o.inv()
    def __eq__(s, o): return s.a == o.a and s.b == o.b
    def __hash__(s): return hash((s.a.c, s.b.c))
    def is_zero(s): return s.a.is_zero() and s.b.is_zero()
    def is_rat(s): return s.b.is_zero() and all(c == 0 for c in s.a.c[1:])
    def __float__(s): return float(s.a) + float(s.b) * ALPHA_F
    def key(s): return s.a.c + s.b.c

LZ, L1 = L(KZ), L(K1)
# CORRECTION (observed on G509: 45 "floating-point" edges not confirmed with a formal α):
# (7+√33)/2 = ((√3+√11)/2)², hence α = √5(√3+√11)/2 = (√15+√55)/2 is ALREADY in K; likewise
# √(5(7−√33)/2) = (√55−√15)/2. Everything is therefore represented in K (b = 0), a canonical representation.
ALPHA = L(K([F(0), F(0), F(0), F(1, 2), F(0), F(0), F(1, 2), F(0)]))   # masks 0b011=√15, 0b110=√55
assert ALPHA * ALPHA == L(ALPHA2)
BETA = L(K([F(0), F(0), F(0), F(-1, 2), F(0), F(0), F(1, 2), F(0)]))
assert BETA * BETA == L(K.rat(F(35, 2)) - K([F(0)] * 5 + [F(5, 2)] + [F(0)] * 2))
assert float(BETA) > 0 and abs(float(BETA) - math.sqrt(2.5 * (7 - math.sqrt(33)))) < 1e-12

def sqrt_int(N):
    """√N for an integer N > 0: N = m²·sf, sf a product of distinct primes of {3,5,11}."""
    m = 1; sf = 1; n = N; p = 2
    while p * p <= n:
        while n % (p * p) == 0: n //= p * p; m *= p
        if n % p == 0: n //= p; sf *= p
        p += 1
    sf *= n
    mask = 0
    for i, q in enumerate(PR):
        if sf % q == 0: sf //= q; mask |= 1 << i
    if sf != 1: raise ValueError("square root outside the field: √%d" % N)
    v = [F(0)] * 8; v[mask] = F(m)
    return L(K(v))

def lsqrt(v):
    if v.is_rat():
        q = v.a.c[0]; assert q > 0
        r = sqrt_int(q.numerator * q.denominator)
        return r * L(K.rat(F(1, q.denominator)))
    if v == ALPHA * ALPHA: return ALPHA
    if v == BETA * BETA: return BETA
    raise ValueError("square root not recognized")

TOK = re.compile(r"\s*(Sqrt\[|\d+|[-+*/(),{}\]])")

def parse_expr(tokens, i):
    def expr(i):
        v, i = term(i)
        while i < len(tokens) and tokens[i] in "+-":
            op = tokens[i]; w, i = term(i + 1)
            v = v + w if op == "+" else v - w
        return v, i
    def term(i):
        v, i = unary(i)
        while i < len(tokens) and tokens[i] in ("*", "/"):
            op = tokens[i]; w, i = unary(i + 1)
            v = v * w if op == "*" else v / w
        return v, i
    def unary(i):
        if tokens[i] == "-": v, i = unary(i + 1); return -v, i
        if tokens[i] == "+": return unary(i + 1)
        return atom(i)
    def atom(i):
        t = tokens[i]
        if t.isdigit(): return L(K.rat(int(t))), i + 1
        if t == "(":
            v, i = expr(i + 1); assert tokens[i] == ")"; return v, i + 1
        if t == "Sqrt[":
            v, i = expr(i + 1); assert tokens[i] == "]"; return lsqrt(v), i + 1
        raise ValueError("unexpected token %r" % t)
    return expr(i)

def tokenize(s):
    out = []; pos = 0; s = s.strip()
    while pos < len(s):
        m = TOK.match(s, pos)
        if not m: raise ValueError("unexpected character: %r" % s[pos:pos + 20])
        out.append(m.group(1)); pos = m.end()
    return out

def read_vtx(path):
    pts = []
    for line in open(path):
        if not line.strip(): continue
        t = tokenize(line)
        assert t[0] == "{" and t[-1] == "}"
        x, i = parse_expr(t, 1); assert t[i] == ","
        y, j = parse_expr(t, i + 1); assert j == len(t) - 1
        pts.append((x, y))
    return pts

def from_udg(p):        # point udg.P (coordinates in K) -> point over L
    return (L(p.x), L(p.y))

def pkey(p): return p[0].key() + p[1].key()
def pf(p): return complex(float(p[0]), float(p[1]))
def padd(p, q): return (p[0] + q[0], p[1] + q[1])
def psub(p, q): return (p[0] - q[0], p[1] - q[1])
def norm2(p): return p[0] * p[0] + p[1] * p[1]
def is_unit(p, q): return norm2(psub(p, q)) == L1

def unit_edges(pts, tol=1e-6):
    """Exact edges; candidates by a floating-point grid (|d−1| < tol), then exact test."""
    zs = [pf(p) for p in pts]
    grid = {}
    for i, z in enumerate(zs): grid.setdefault((math.floor(z.real), math.floor(z.imag)), []).append(i)
    E = []; nfloat = 0
    for i, z in enumerate(zs):
        gx, gy = math.floor(z.real), math.floor(z.imag)
        for dx in (-1, 0, 1):
            for dy in (-1, 0, 1):
                for j in grid.get((gx + dx, gy + dy), ()):
                    if j > i and abs(abs(z - zs[j]) - 1) < tol:
                        nfloat += 1
                        if is_unit(pts[i], pts[j]): E.append((i, j))
    return E, nfloat

def unit_vectors(pts, E):
    U = {}
    for i, j in E:
        d = psub(pts[j], pts[i]); U[pkey(d)] = d
        d = psub(pts[i], pts[j]); U[pkey(d)] = d
    return U

def distinct(pts): return len({pkey(p) for p in pts}) == len(pts)
