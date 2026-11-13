# SPDX-License-Identifier: Apache-2.0
r"""Stand-alone DRAT checker (pure Python, no pysat), written to replace drat-trim
(which could not be compiled in the environment where this work was done).

Usage: python3 -B drat_check.py formula.cnf proof.drat

Format: DIMACS for the formula; textual DRAT for the proof (lines "l1 l2 ... 0" = addition,
"d l1 l2 ... 0" = deletion).

Rules checked, FORWARD, for each added clause C:
  * RUP: unit propagation of the negation of C on the active clauses yields a conflict;
  * otherwise RAT on the FIRST literal p of C: for every active clause D containing -p,
    the resolvent C ∪ (D \ {-p}) is RUP (or tautological).
  If neither rule applies, the proof is REJECTED.
Deletions: applied, except those of unit clauses (as drat-trim does) — this is safe:
deleting a clause only preserves satisfiability, and keeping an extra clause can make a
RUP lemma accepted only if it follows from implied clauses (or from clauses added while
preserving satisfiability). Success = the empty clause is derived (or propagation of the
active clauses yields a conflict after the last lemma).
Why this is correct: each step (RUP addition, RAT addition, deletion) preserves
satisfiability; if the empty clause is reached, the initial formula was unsatisfiable.
"""
import sys, time


def read_cnf(path):
    cls = []; cur = []
    for line in open(path):
        if not line.strip() or line[0] in "cp%": continue
        for t in line.split():
            x = int(t)
            if x == 0: cls.append(cur); cur = []
            else: cur.append(x)
    return cls


def read_drat(path):
    steps = []
    for line in open(path):
        t = line.split()
        if not t: continue
        if t[0] == "d":
            assert t[-1] == "0"; steps.append(("d", [int(x) for x in t[1:-1]]))
        else:
            assert t[-1] == "0"; steps.append(("a", [int(x) for x in t[:-1]]))
    return steps


class Checker:
    def __init__(self):
        self.clauses = []; self.watch = {}; self.index = {}; self.units = []
        self.occ = {}  # literal -> clause indices (for RAT)

    def add(self, cl):
        cl = list(dict.fromkeys(cl))
        i = len(self.clauses); self.clauses.append(cl)
        self.index.setdefault(tuple(sorted(cl)), []).append(i)
        for l in cl: self.occ.setdefault(l, []).append(i)
        if len(cl) == 1: self.units.append(i)
        elif len(cl) >= 2:
            for l in cl[:2]: self.watch.setdefault(l, []).append(i)
        return i

    def delete(self, cl):
        lst = self.index.get(tuple(sorted(set(cl))))
        if not lst: return False
        i = lst[-1]
        if len(self.clauses[i]) == 1: return False     # never delete a unit clause
        lst.pop(); self.clauses[i] = None
        return True

    def conflict(self, lits):
        """True if propagating (active units + lits) leads to a conflict."""
        val = set(); trail = []
        def setl(l):
            if -l in val: return False
            if l not in val: val.add(l); trail.append(l)
            return True
        if any(-l in lits for l in lits): return True  # negated tautology = immediate conflict
        for i in self.units:
            c = self.clauses[i]
            if c is not None and not setl(c[0]): return True
        for l in lits:
            if not setl(l): return True
        q = 0
        while q < len(trail):
            nl = -trail[q]; q += 1
            ws = self.watch.get(nl)
            if not ws: continue
            j = 0
            while j < len(ws):
                i = ws[j]; c = self.clauses[i]
                if c is None: ws[j] = ws[-1]; ws.pop(); continue
                if c[0] == nl: c[0], c[1] = c[1], c[0]
                if c[0] in val: j += 1; continue
                moved = False
                for p in range(2, len(c)):
                    if -c[p] not in val:
                        c[1], c[p] = c[p], c[1]
                        self.watch.setdefault(c[1], []).append(i)
                        ws[j] = ws[-1]; ws.pop(); moved = True; break
                if moved: continue
                if -c[0] in val: return True
                setl(c[0]); j += 1
        return False

    def check_lemma(self, lem):
        """Returns 'RUP', 'RAT' or None."""
        neg = [-l for l in lem]
        if self.conflict(neg): return "RUP"
        if not lem: return None
        p = lem[0]
        for i in list(self.occ.get(-p, [])):
            D = self.clauses[i]
            if D is None: continue
            res = set(lem) | {l for l in D if l != -p}
            if any(-l in res for l in res): continue          # tautological resolvent
            if not self.conflict([-l for l in res]): return None
        return "RAT"


def check(cnf, steps, verbose=True):
    t = time.time(); ck = Checker()
    for c in cnf: ck.add(c)
    if ck.conflict([]):
        if verbose: print("formula already contradictory by unit propagation")
        return True, dict(rup=0, rat=0)
    nrup = nrat = ndel = 0
    for k, (typ, cl) in enumerate(steps):
        if typ == "d":
            ndel += ck.delete(cl); continue
        r = ck.check_lemma(cl)
        if r is None:
            if verbose: print("FAILURE: step %d, lemma neither RUP nor RAT: %s" % (k, cl[:12]))
            return False, dict(rup=nrup, rat=nrat, step=k)
        if r == "RUP": nrup += 1
        else: nrat += 1
        if not cl:
            if verbose: print("empty clause derived at step %d" % k)
            return True, dict(rup=nrup, rat=nrat, dele=ndel, sec=time.time() - t)
        ck.add(cl)
        if verbose and (nrup + nrat) % 20000 == 0:
            print("  %d lemmas checked (%.0fs)" % (nrup + nrat, time.time() - t), flush=True)
    ok = ck.conflict([])
    if verbose: print("end of proof; final conflict by propagation:", ok)
    return ok, dict(rup=nrup, rat=nrat, dele=ndel, sec=time.time() - t)


if __name__ == "__main__":
    cnf = read_cnf(sys.argv[1]); steps = read_drat(sys.argv[2])
    print("formula: %d clauses; proof: %d steps" % (len(cnf), len(steps)), flush=True)
    ok, st = check(cnf, steps)
    print("statistics:", st)
    print("RESULT: VALID DRAT PROOF (formula unsatisfiable)" if ok else "RESULT: PROOF REJECTED")
    sys.exit(0 if ok else 1)
