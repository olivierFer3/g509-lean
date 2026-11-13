# SPDX-License-Identifier: Apache-2.0
"""Smallest non-k-colorable (induced) subgraph of an ambient graph, by IMPLICIT HITTING SETS
(the method of Parts, arXiv:2010.12665, §5, organized as an implicit-hitting-set / SMUS loop, cf. Ignatiev,
Previti, Liffiton, Marques-Silva, CP 2015). See README.md for the justification of each constraint.
This program only PRODUCES the cuts; it is not part of the trusted base (the cuts are re-verified by
verify_cuts.py / verify_ambient_cuts.py and the final infeasibility is certified by DRAT).

python3 -B hs.py INSTANCE STATE_DIR [budget_s]

INSTANCE : name of an ambient of data/ (e.g. A1_top20) or path of a JSON file of the same format:
           dict(name, n, k, edges [(u,v), u<v], witnesses [(S, col)] (proper colorings of subsets S),
           ub0 (size of a known non-k-colorable subgraph, or None), record (stopping threshold, or None),
           pts (exact points, optional)).
Loop:
  * hitting-set model (OR-Tools CP-SAT): x_v ∈ {0,1}, y_e ≤ x_u, y_e ≤ x_v for the used edges e=uv;
    for each cut E_c: Σ_{e ∈ E_c} y_e ≥ 1; degree: x_v ⇒ Σ_{u ∈ N(v)} x_u ≥ k; Σ x ≤ UB − 1; min Σ x.
  * the solution S is tested by CaDiCaL (incremental, selectors, one triangle fixed conditionally);
    S colorable -> coloring EXTENDED to the whole ambient (greedy then local search, S fixed) ->
    E_c = monochromatic edges -> new cut (and a few more cuts, other extensions);
    S not colorable -> reduced to a critical subgraph H; UB = |H| (if < record: candidate saved).
  * LOWER BOUND = best bound PROVED by CP-SAT on the relaxed problem (all cuts valid).
Atomic save (.tmp then os.replace) every 5 min and on SIGTERM: STATE_DIR/etat.pkl (internal checkpoint,
pickle), STATE_DIR/resume.json and STATE_DIR/cuts.json (same format as data/<ambient>_cuts.json).
Adapted from the original program: I/O only (JSON instance, cuts.json written, project-specific status-table
writer and automatic certification hook removed); the search itself is unchanged.
"""
import sys, os, time, json, pickle, random, signal, math, resource
sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
from pysat.solvers import Solver
sys.path.insert(0, HERE)
from data_io import load_ambient

SAVE_EVERY = int(os.environ.get("SAVE_EVERY", "300"))
BILAN_EVERY = int(os.environ.get("BILAN_EVERY", "900"))
QUICK_T = float(os.environ.get("QUICK_T", "5"))        # fast CP-SAT (cuts)
OPT_T0 = float(os.environ.get("OPT_T0", "30"))         # "bound" CP-SAT: initial time, doubled up to OPT_TMAX
OPT_TMAX = float(os.environ.get("OPT_TMAX", "240"))
OPT_EVERY = int(os.environ.get("OPT_EVERY", "10"))     # one "bound" solve every OPT_EVERY iterations
WORKERS = int(os.environ.get("WORKERS", "2"))
EXTRA_CUTS = int(os.environ.get("EXTRA_CUTS", "3"))
GROW_CALLS = int(os.environ.get("GROW_CALLS", "8"))
GROW_BUDGET = int(os.environ.get("GROW_BUDGET", "20000"))

def maxrss_mo(): return resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / 1024
def now(): return time.strftime("%Y-%m-%dT%H:%M:%S")

def atomic_dump(obj, path, js=False):
    tmp = path + ".tmp"
    with open(tmp, "w" if js else "wb") as f:
        if js: json.dump(obj, f, indent=1, ensure_ascii=False)
        else: pickle.dump(obj, f, protocol=4)
        f.flush(); os.fsync(f.fileno())
    os.replace(tmp, path)

class Graph:
    def __init__(s, n, edges, k):
        s.n, s.k = n, k
        s.edges = sorted({(min(u, v), max(u, v)) for u, v in edges})
        s.eid = {e: i for i, e in enumerate(s.edges)}
        s.adj = [[] for _ in range(n)]
        for u, v in s.edges: s.adj[u].append(v); s.adj[v].append(u)
        s.inc = [[] for _ in range(n)]
        for i, (u, v) in enumerate(s.edges): s.inc[u].append(i); s.inc[v].append(i)

class Oracle:
    """Incremental CaDiCaL: x(v,c) = k v + c + 1, selector s_v = SEL0 + v; (¬s_v ∨ ∨_c x(v,c)); edges.
    CONDITIONAL symmetry breaking: if the 3 vertices of a triangle are selected, they get the colors 0, 1, 2
    (legitimate: the colors are interchangeable)."""
    def __init__(s, G):
        s.G = G; k = G.k; s.SEL0 = k * G.n + 1
        s.S = Solver(name="cadical195"); s.ncalls = 0; s.tsat = 0.0
        for v in range(G.n): s.S.add_clause([-(s.SEL0 + v)] + [k * v + c + 1 for c in range(k)])
        for u, v in G.edges:
            for c in range(k): s.S.add_clause([-(k * u + c + 1), -(k * v + c + 1)])
        s.tri = None
        for u, v in G.edges:
            w = set(G.adj[u]) & set(G.adj[v])
            if w:
                s.tri = (u, v, min(w))
                for c, a in enumerate(s.tri): s.S.add_clause([-(s.SEL0 + x) for x in s.tri] + [k * a + c + 1])
                break
    def solve(s, sub, budget=None):
        """('SAT', {v: c}) / ('UNSAT', core ⊆ sub) / ('UNK', None)."""
        k = s.G.k; s.ncalls += 1; t = time.time(); A = [s.SEL0 + v for v in sub]
        if budget: s.S.conf_budget(budget); r = s.S.solve_limited(assumptions=A)
        else: r = s.S.solve(assumptions=A)
        s.tsat += time.time() - t
        if r is None: return "UNK", None
        if r:
            m = s.S.get_model(); col = {}
            for v in sub:
                for c in range(k):
                    if m[k * v + c] > 0: col[v] = c; break
            return "SAT", col
        return "UNSAT", {l - s.SEL0 for l in s.S.get_core()}

def extend(G, col, rng, passes=40):
    """Extends the proper coloring col (dict on S) to ALL vertices while minimizing the monochromatic edges:
    greedy (most constrained vertices first, least conflicting color), then local search (min-conflicts)
    on the vertices OUTSIDE S only (S stays fixed, so E_c contains no edge of S).
    Returns (c' list, E_c list of edge indices)."""
    n, k = G.n, G.k
    c = [-1] * n
    for v, x in col.items(): c[v] = x
    free = [v for v in range(n) if c[v] < 0]
    ncol = [sum(1 for u in G.adj[v] if c[u] >= 0) for v in range(n)]
    left = set(free)
    while left:
        v = max(left, key=lambda v: (ncol[v], rng.random()))
        cnt = [0] * k
        for u in G.adj[v]:
            if c[u] >= 0: cnt[c[u]] += 1
        m = min(cnt); opts = [x for x in range(k) if cnt[x] == m]
        c[v] = rng.choice(opts); left.discard(v)
        for u in G.adj[v]: ncol[u] += 1
    for _ in range(passes):
        changed = False; order = free[:]; rng.shuffle(order)
        for v in order:
            cnt = [0] * k
            for u in G.adj[v]: cnt[c[u]] += 1
            if cnt[c[v]] == 0: continue
            m = min(cnt)
            if m < cnt[c[v]]:
                opts = [x for x in range(k) if cnt[x] == m]; c[v] = rng.choice(opts); changed = True
            elif rng.random() < 0.1:          # sideways move (escape from plateaus)
                opts = [x for x in range(k) if cnt[x] == m and x != c[v]]
                if opts: c[v] = rng.choice(opts)
        if not changed: break
    M = [i for i, (u, v) in enumerate(G.edges) if c[u] == c[v]]
    return c, M

def proper_on(G, c, S):
    Ss = set(S); return all(c[u] != c[v] for u, v in G.edges if u in Ss and v in Ss)

class Run:
    def __init__(s, inst_path, sdir):
        s.inst = load_ambient(inst_path) if not inst_path.endswith(".json") else load_ambient(os.path.basename(inst_path)[:-5], os.path.dirname(os.path.abspath(inst_path)))
        s.sdir = sdir; os.makedirs(sdir, exist_ok=True)
        I = s.inst; s.G = Graph(I["n"], I["edges"], I["k"]); s.name = I["name"]
        s.record = I.get("record"); s.fstate = os.path.join(sdir, "etat.pkl")
        s.flog = os.path.join(sdir, "log.txt"); s.stop = False
        s.O = Oracle(s.G)
        if os.path.exists(s.fstate):
            st = pickle.load(open(s.fstate, "rb"))
            s.cuts = st["cuts"]; s.cutset = set(s.cuts); s.LB = st["LB"]; s.UB = st["UB"]; s.H = st["H"]
            s.it = st["it"]; s.cumul = st["cumul"]; s.hist = st["hist"]; s.rng = random.Random()
            s.rng.setstate(st["rng"]); s.optT = st["optT"]; s.done = st["done"]; s.hint = st.get("hint")
            s.nsauv = st["nsauv"]; s.cands = st.get("cands", [])
            s.log("RESUME: save no. %d; it %d; %d cuts; LB %d; UB %s; cumulated time %.0fs"
                  % (s.nsauv, s.it, len(s.cuts), s.LB, s.UB, s.cumul))
        else:
            s.cuts = []; s.cutset = set(); s.LB = 0; s.UB = I.get("ub0"); s.H = None; s.it = 0; s.cumul = 0.0
            s.hist = []; s.rng = random.Random(I.get("seed", 1)); s.optT = OPT_T0; s.done = False; s.hint = None
            s.nsauv = 0; s.cands = []
            s.log("START %s: %d vertices, %d edges, k=%d; initial UB %s; threshold %s; %d initial witnesses"
                  % (s.name, s.G.n, len(s.G.edges), s.G.k, s.UB, s.record, len(I["witnesses"])))
            t0 = time.time()
            for S, col in I["witnesses"]:
                d = dict(zip(S, col)) if not isinstance(col, dict) else col
                assert proper_on(s.G, _arr(s.G.n, d), list(d)), "witness not proper"
                for r in range(1 + EXTRA_CUTS):
                    c, M = extend(s.G, d, s.rng); s.add_cut(M)
            s.cumul += time.time() - t0
            s.log("witnesses extended: %d distinct cuts; mean size %.1f edges; %.0fs"
                  % (len(s.cuts), sum(map(len, s.cuts)) / max(1, len(s.cuts)), time.time() - t0))
        s.ub_size = s.UB if s.UB is not None else s.G.n + 1

    def log(s, msg):
        line = "%s [%s] %s" % (now(), s.inst["name"], msg); print(line, flush=True)
        with open(os.path.join(s.sdir, "log.txt"), "a") as f: f.write(line + "\n")

    def add_cut(s, M):
        t = tuple(sorted(M))
        if not t:      # the whole ambient is k-colorable: no non-k-colorable subgraph
            s.log("EMPTY cut: the whole ambient is %d-colorable (no solution)" % s.G.k); s.LB = math.inf; return
        if t not in s.cutset: s.cutset.add(t); s.cuts.append(t)

    def save(s):
        s.nsauv += 1
        st = dict(version=1, cuts=s.cuts, LB=s.LB, UB=s.UB, H=s.H, it=s.it, cumul=s.cumul, hist=s.hist,
                  rng=s.rng.getstate(), optT=s.optT, done=s.done, hint=s.hint, nsauv=s.nsauv, cands=s.cands)
        atomic_dump(st, s.fstate)
        res = dict(name=s.name, vertices=s.G.n, edges=len(s.G.edges), k=s.G.k, lower_bound=s.LB, best=s.UB,
                   threshold=s.record, iterations=s.it, cuts=len(s.cuts), cumulated_time_s=round(s.cumul),
                   sat_calls=s.O.ncalls, max_memory_mb=round(maxrss_mo()), done=s.done,
                   saved=now(), save_no=s.nsauv, candidates_below_threshold=s.cands)
        atomic_dump(res, os.path.join(s.sdir, "resume.json"), js=True)
        atomic_dump(dict(cuts=[list(c) for c in s.cuts], LB=s.LB if s.LB != math.inf else None, UB=s.UB, done=s.done,
                         it=s.it, H=s.H), os.path.join(s.sdir, "cuts.json"), js=True)

    def model(s, tlim, seed):
        from ortools.sat.python import cp_model
        G = s.G; m = cp_model.CpModel()
        x = [m.NewBoolVar("x%d" % v) for v in range(G.n)]
        used = sorted({e for C in s.cuts for e in C}); y = {}
        for e in used:
            u, v = G.edges[e]; y[e] = m.NewBoolVar("y%d" % e)
            m.AddImplication(y[e], x[u]); m.AddImplication(y[e], x[v])
        for C in s.cuts: m.AddBoolOr([y[e] for e in C])
        for v in range(G.n) if os.environ.get("NODEG") != "1" else ():   # critical subgraph: degree ≥ k
            m.Add(sum(x[u] for u in G.adj[v]) >= G.k).OnlyEnforceIf(x[v])
        m.Add(sum(x) <= s.ub_size - 1)
        if s.LB > 0 and s.LB != math.inf: m.Add(sum(x) >= int(s.LB))
        m.Minimize(sum(x))
        if s.hint:
            hs = set(s.hint)
            for v in range(G.n): m.AddHint(x[v], 1 if v in hs else 0)
        sv = cp_model.CpSolver(); sv.parameters.max_time_in_seconds = tlim
        sv.parameters.num_workers = WORKERS; sv.parameters.random_seed = seed
        st = sv.Solve(m)
        names = {cp_model.OPTIMAL: "OPTIMAL", cp_model.FEASIBLE: "FEASIBLE", cp_model.INFEASIBLE: "INFEASIBLE"}
        stn = names.get(st, "UNKNOWN")
        S = [v for v in range(G.n) if sv.Value(x[v])] if stn in ("OPTIMAL", "FEASIBLE") else None
        bound = sv.BestObjectiveBound() if stn in ("OPTIMAL", "FEASIBLE", "UNKNOWN") else None
        return stn, S, bound

    def reduce_core(s, core):
        """Non-k-colorable subgraph -> critical subgraph (vertex-by-vertex deletion, UNSAT proved)."""
        keep = set(core); order = sorted(keep); s.rng.shuffle(order)
        for v in order:
            if v not in keep: continue
            r, z = s.O.solve(sorted(keep - {v}), budget=2000000)
            if r == "UNSAT": keep = set(z)
        return sorted(keep)

    def found(s, H):
        H = sorted(H)
        if s.UB is None or len(H) < s.UB:
            s.UB = len(H); s.ub_size = s.UB; s.H = H
            s.log("NEW BEST SOLUTION: non-%d-colorable subgraph with %d vertices" % (s.G.k, len(H)))
            if s.record is not None and len(H) < s.record and "pts" in s.inst:
                path = os.path.join(s.sdir, "candidate_%d_%s.json" % (len(H), time.strftime("%Y%m%d%H%M%S")))
                idx = {v: i for i, v in enumerate(H)}
                E = [(idx[u], idx[v]) for u, v in s.G.edges if u in idx and v in idx]
                atomic_dump(dict(vertices=H, edges=E), path, js=True); s.cands.append(path)
                s.log("CANDIDATE BELOW THE THRESHOLD %d: %s -> to be certified independently; NOT a claim" % (s.record, path))

    def step(s):
        s.it += 1; G = s.G
        opt = (s.it % OPT_EVERY == 0)
        tlim = s.optT if opt else QUICK_T
        t = time.time(); stn, S, bound = s.model(tlim, s.it)
        dtm = time.time() - t
        if stn == "INFEASIBLE":
            s.LB = s.ub_size if s.UB is not None else math.inf
            s.log("it %d: relaxation INFEASIBLE under Σx ≤ %d -> lower bound = %s: DONE (%s optimal)"
                  % (s.it, s.ub_size - 1, s.LB, "UB" if s.UB else "no solution")); s.done = True; return
        if bound is not None:
            b = math.ceil(bound - 1e-6)
            if b > s.LB: s.LB = b; s.log("it %d: LOWER BOUND proved %d (CP-SAT %s, %.0fs, %d cuts)" % (s.it, b, stn, dtm, len(s.cuts)))
        if s.UB is not None and s.LB >= s.UB:
            s.log("it %d: LB = UB = %d: DONE (optimum of the ambient)" % (s.it, s.UB)); s.done = True; return
        if S is None:
            if opt: s.optT = min(OPT_TMAX, s.optT * 2)
            return
        if opt:
            if stn == "OPTIMAL": s.optT = max(OPT_T0, s.optT * 0.8)
            else: s.optT = min(OPT_TMAX, s.optT * 2)
        s.hint = S
        r, z = s.O.solve(S, budget=None if len(S) < 300 else 5000000)
        if r == "UNK": s.log("it %d: SAT unknown on |S|=%d (budget); continuing" % (s.it, len(S))); return
        if r == "UNSAT":
            H = s.reduce_core(z); s.found(H)
            if stn == "OPTIMAL" and len(S) == s.LB:
                s.log("it %d: S optimal for the relaxation and not %d-colorable: DONE, optimum %d" % (s.it, G.k, len(H)))
                s.done = True
            return
        col = z
        # "grow": try to add conflicting vertices to the coloring (bounded SAT)
        c, M = extend(G, col, s.rng)
        base = dict(col)
        for _ in range(GROW_CALLS):
            if not M: break
            ends = sorted({w for e in M for w in G.edges[e] if w not in base})
            if not ends: break
            w = s.rng.choice(ends)
            ok = [v for v in range(G.n) if all(c[v] != c[u] for u in G.adj[v])]   # vertices without conflict
            T = sorted(set(ok) | set(base) | {w})
            r2, z2 = s.O.solve(T, budget=GROW_BUDGET)
            if r2 != "SAT": continue
            base = z2; c, M = extend(G, base, s.rng)
        assert proper_on(G, c, S)
        s.add_cut(M)
        for _ in range(EXTRA_CUTS):
            c2, M2 = extend(G, base, s.rng); s.add_cut(M2)
        if s.it % 20 == 0 or s.it < 5:
            s.log("it %d: |S| = %d (CP-SAT %s %.1fs); cut of %d edges; %d cuts; LB %d; UB %s; SAT %d calls %.0fs; %.0f MB"
                  % (s.it, len(S), stn, dtm, len(M), len(s.cuts), s.LB, s.UB, s.O.ncalls, s.O.tsat, maxrss_mo()))

    def main(s, budget):
        T0 = time.time(); tsave = time.time(); tbil = time.time() - BILAN_EVERY + 60
        def term(sig, frm): s.stop = True
        signal.signal(signal.SIGTERM, term); signal.signal(signal.SIGINT, term)
        s.save()
        while not s.done and not s.stop and (budget is None or time.time() - T0 < budget):
            t = time.time(); s.step(); s.cumul += time.time() - t
            if s.LB == math.inf: s.done = True
            if s.record is not None and s.LB >= s.record and not s.done:
                s.log("LOWER BOUND %d ≥ %d: ambient EXHAUSTED (no non-%d-colorable subgraph with fewer than %d vertices)"
                      % (s.LB, s.record, s.G.k, s.record)); s.done = True
            if time.time() - tbil >= BILAN_EVERY:
                tbil = time.time(); s.hist.append((now(), s.cumul, s.LB, s.UB, len(s.cuts), s.it))
                s.log("STATUS: lower bound %s; best solution %s; it %d; %d cuts; cumulated time %.0fs; %.0f MB"
                      % (s.LB, s.UB, s.it, len(s.cuts), s.cumul, maxrss_mo()))
            if time.time() - tsave >= SAVE_EVERY: s.save(); tsave = time.time()
        s.hist.append((now(), s.cumul, s.LB, s.UB, len(s.cuts), s.it)); s.save()
        s.log("STOP (%s): lower bound %s; best solution %s (%s); it %d; %d cuts; save no. %d"
              % ("done" if s.done else "signal/budget", s.LB, s.UB, s.H if s.H and len(s.H) < 40 else "...",
                 s.it, len(s.cuts), s.nsauv))
        return 0 if s.done else 2

def _arr(n, d): return [d.get(v, -1) for v in range(n)]

if __name__ == "__main__":
    R = Run(sys.argv[1], sys.argv[2])
    sys.exit(R.main(float(sys.argv[3]) if len(sys.argv) > 3 else None))
