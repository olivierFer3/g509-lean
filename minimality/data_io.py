# SPDX-License-Identifier: Apache-2.0
"""Reading of the JSON data files of `data/` (ambients, cuts, cut witnesses).

The JSON files were produced from the original Python pickles by `export_json.py`, which also checks that the
conversion is exact (round trip). Exact coordinates: each coordinate is a + b·α with a, b in
K = Q(√3, √5, √11) given as 8 rationals (strings "p/q") indexed by the bit mask (bit 0 = √3, bit 1 = √5,
bit 2 = √11), α = (√15 + √55)/2; in these files b = 0 everywhere (see geom4.py, CORRECTION)."""
import os, sys, json
from fractions import Fraction
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from udg import K
from geom4 import L

DATA = os.environ.get("MINIMALITY_DATA", os.path.join(HERE, "data"))

def enc_k(k): return [str(q) for q in k.c]
def dec_k(t): return K([Fraction(q) for q in t])
def enc_l(l): return {"a": enc_k(l.a), "b": enc_k(l.b)}
def dec_l(d): return L(dec_k(d["a"]), dec_k(d["b"]))
def enc_pt(p): return [enc_l(p[0]), enc_l(p[1])]
def dec_pt(p): return (dec_l(p[0]), dec_l(p[1]))

def load_ambient(name, data=DATA):
    """Same dictionary as the original pickle <name>.pkl: name, n, k, edges [(u, v)], witnesses [(S, col)],
    ub0, record, seed, description, pts [(x, y)] (exact, classes of geom4/udg)."""
    d = json.load(open(os.path.join(data, name + ".json")))
    d["edges"] = [tuple(e) for e in d["edges"]]
    d["witnesses"] = [(S, col) for S, col in d["witnesses"]]
    d["pts"] = [dec_pt(p) for p in d["pts"]]
    return d

def load_cuts(name, data=DATA):
    """Final state of the search hs.py for this ambient: cuts (sorted tuples of edge indices), LB, UB, done, it."""
    d = json.load(open(os.path.join(data, name + "_cuts.json")))
    d["cuts"] = [tuple(c) for c in d["cuts"]]
    return d

def load_g509_points(data=DATA):
    """The 509 exact points of G509 (Parts) as used by the searches (vertices 0..508 of each ambient)."""
    return [dec_pt(p) for p in json.load(open(os.path.join(data, "g509_points.json")))["pts"]]
