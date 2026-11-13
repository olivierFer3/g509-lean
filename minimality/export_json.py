# SPDX-License-Identifier: Apache-2.0
"""One-off conversion of the original Python pickles (search runs of hs.py) and of the cut-witness files of
verify_cuts.py into the JSON files of `data/`, with an exact round-trip check. Kept for provenance; the pickles
themselves are not distributed (they need the classes of geom4.py/udg.py to be read).

Usage: python3 export_json.py PICKLE_DIR WITNESS_DIR [LEAN_G509_JSON]
  PICKLE_DIR : contains A1_top20.pkl, A3_couv35.pkl, g509.pkl, run_A1_top20/etat.pkl, run_A3_couv35/etat.pkl
  WITNESS_DIR: contains coupes_A1_top20.json, coupes_A3_couv35_sous.json (outputs of verify_cuts.py, French keys)
  LEAN_G509_JSON (optional): gen/g509.json of the Lean project; the 509 points are then compared with it.
"""
import os, sys, json, pickle
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import udg, geom4                      # needed to unpickle
from data_io import enc_pt, load_ambient, load_cuts, load_g509_points, DATA

PD, WD = sys.argv[1], sys.argv[2]
DESCR = {"A1_top20": "G509 + the 20 candidate points that kill the most witnesses",
         "A3_couv35": "G509 + 35 candidate points chosen greedily to cover the most distinct witnesses"}
def dump(obj, path):
    tmp = path + ".tmp"; json.dump(obj, open(tmp, "w"), separators=(",", ":")); os.replace(tmp, path)

os.makedirs(DATA, exist_ok=True)
for name in ("A1_top20", "A3_couv35"):
    I = pickle.load(open(os.path.join(PD, name + ".pkl"), "rb"))
    st = pickle.load(open(os.path.join(PD, "run_" + name, "etat.pkl"), "rb"))
    assert all(c.b.is_zero() for p in I["pts"] for c in p)          # b = 0 everywhere
    out = dict(name=I["name"], description=DESCR[name], n=I["n"], k=I["k"], ub0=I["ub0"], record=I["record"],
               seed=I["seed"], edges=[list(e) for e in I["edges"]],
               witnesses=[[list(S), list(col)] for S, col in I["witnesses"]],
               added=[{"neighbours_in_G509": a["voisins_G509"], "witnesses_killed": a["temoins_tues"]} for a in I["ajoutes"]],
               pts=[enc_pt(p) for p in I["pts"]])
    dump(out, os.path.join(DATA, name + ".json"))
    dump(dict(cuts=[list(c) for c in st["cuts"]], LB=st["LB"], UB=st["UB"], done=st["done"], it=st["it"],
              H=st["H"], note="final state of hs.py (the cuts are sorted tuples of indices in the sorted edge list)"),
         os.path.join(DATA, name + "_cuts.json"))
    # round trip
    J = load_ambient(name); C = load_cuts(name)
    assert J["n"] == I["n"] and J["k"] == I["k"] and J["edges"] == [tuple(e) for e in I["edges"]]
    assert all(a == b and c == d for (a, c), (b, d) in zip(J["pts"], I["pts"])) and len(J["pts"]) == len(I["pts"])
    assert [(list(S), list(c)) for S, c in J["witnesses"]] == [(list(S), list(c)) for S, c in I["witnesses"]]
    assert C["cuts"] == [tuple(c) for c in st["cuts"]] and (C["LB"], C["UB"], C["done"]) == (st["LB"], st["UB"], st["done"])
    print(name, ": JSON round trip exact (points, edges, witnesses, %d cuts)" % len(C["cuts"]))

g = pickle.load(open(os.path.join(PD, "g509.pkl"), "rb"))
dump(dict(pts=[enc_pt(p) for p in g[0]], edges=[list(e) for e in g[1]]), os.path.join(DATA, "g509_points.json"))
G = load_g509_points(); assert len(G) == 509 and all(a == b and c == d for (a, c), (b, d) in zip(G, g[0]))
for name in ("A1_top20", "A3_couv35"):
    assert all(load_ambient(name)["pts"][i] == G[i] for i in range(509)), name
print("g509_points.json: round trip exact; vertices 0..508 of both ambients are these points")

if len(sys.argv) > 3:   # comparison with the coordinates of the Lean formalization (x 96, same basis order)
    from fractions import Fraction
    LJ = json.load(open(sys.argv[3]))
    assert LJ["D"] == 96
    ok = all([Fraction(int(c), 96) for c in X] == list(p[0].a.c) and [Fraction(int(c), 96) for c in Y] == list(p[1].a.c)
             for (X, Y), p in zip(LJ["pts"], G))
    lean_edges = {tuple(e) for e in LJ["edges"]}
    print("points of G509 identical to those of the Lean formalization (gen/g509.json):", ok,
          "; edges identical:", lean_edges == {tuple(e) for e in g[1]})
    assert ok

KEYS = {"ambiant": "ambient", "n": "n", "aretes": "edges", "coupes": "cuts", "exactes": "exact",
        "incluses_seulement": "included_only", "invalides": "invalid", "anomalies": "anomalies",
        "colorations": "colorings", "secondes": "seconds", "taille_min": "min_size", "taille_max": "max_size",
        "coupes_1_arete": "cuts_with_1_edge", "etat": "state", "sous_ensemble": "subset_size"}
for src, dst in (("coupes_A1_top20.json", "A1_top20_cut_witnesses.json"),
                 ("coupes_A3_couv35_sous.json", "A3_couv35_cut_witnesses_subset.json")):
    R = json.load(open(os.path.join(WD, src)))
    assert not R["anomalies"] and not R["invalides"]
    out = {KEYS[k]: v for k, v in R.items()}
    out["note"] = ("output of verify_cuts.py: for each verified cut (all cuts for A1; for A3 the cuts of the core "
                   "plus all cuts with one edge, in increasing index order), a 4-coloring of the whole ambient "
                   "(one digit per vertex) whose set of monochromatic edges is exactly the cut")
    dump(out, os.path.join(DATA, dst))
    back = json.load(open(os.path.join(DATA, dst)))
    assert back["colorings"] == R["colorations"] and len(back) == len(R) + 1
    print(dst, ":", len(R["colorations"]), "colorings, copied exactly")
