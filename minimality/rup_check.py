# SPDX-License-Identifier: Apache-2.0
"""Second RUP/DRAT checker, written separately by an independent reviewing agent, without reusing anything from
drat_check.py or drat_check_stream.py.

Usage: python3 -I rup_check.py formula.cnf proof.drat [max_lines]

Principle (forward checking, RUP only; a non-RUP lemma makes the check FAIL):
- base = clauses of the formula; root assignment maintained by unit propagation (two watched literals);
  each lemma C is checked RUP: ¬C is assigned above the root, propagation must give a conflict (or a literal
  of C is already true at the root); then C is added.
- 'd C': deletes one occurrence of C (if absent: counted, ignored). Root assignments are never undone: this is
  correct because, the proof being RUP only, each lemma and each root assignment is a logical consequence of
  the original formula (induction); deleting clauses only makes the subsequent checks harder.
- Success only if the empty clause is obtained (empty RUP lemma, or root conflict after adding a checked lemma,
  or the formula itself refuted by propagation).
The proof is read as a stream (no copy in memory).
"""
import sys, time, resource

def lit_idx(l):  # DIMACS -> index; negation = ^1
    return 2 * l if l > 0 else -2 * l + 1

class Checker:
    def __init__(s, nv):
        s.nv = nv
        s.val = [0] * (2 * nv + 2)       # 1 true, -1 false, 0 unassigned (by literal index)
        s.watch = [[] for _ in range(2 * nv + 2)]
        s.trail = []
        s.qhead = 0
        s.db = {}                        # key (sorted tuple) -> list of clauses (lists)
        s.rootconf = False
        s.ndel_miss = 0

    def assign(s, l):
        s.val[l] = 1; s.val[l ^ 1] = -1; s.trail.append(l)

    def propagate(s):
        val = s.val; watch = s.watch; trail = s.trail
        q = s.qhead
        while q < len(trail):
            fl = trail[q] ^ 1; q += 1
            ws = watch[fl]; i = 0; j = 0; n = len(ws)
            while i < n:
                c = ws[i]; i += 1
                if not c: continue                       # deleted clause: removed from the list
                if c[0] == fl: c[0], c[1] = c[1], c[0]
                if c[1] != fl: continue                  # stale watch (should not happen)
                if val[c[0]] == 1: ws[j] = c; j += 1; continue
                moved = False
                for k in range(2, len(c)):
                    l = c[k]
                    if val[l] != -1:
                        c[1] = l; c[k] = fl; watch[l].append(c); moved = True; break
                if moved: continue
                ws[j] = c; j += 1
                if val[c[0]] == -1:
                    while i < n: ws[j] = ws[i]; j += 1; i += 1
                    del ws[j:]
                    s.qhead = q
                    return True                          # conflict
                s.assign(c[0])
            del ws[j:]
        s.qhead = q
        return False

    def add(s, lits):
        """Adds a clause (already normalized, without duplicates or tautology) at the root."""
        key = tuple(sorted(lits))
        c = list(lits)
        s.db.setdefault(key, []).append(c)
        if s.rootconf: return
        val = s.val
        nonfalse = [l for l in c if val[l] != -1]
        if any(val[l] == 1 for l in c):
            # satisfied at the root: watch two non-false literals if possible
            c.sort(key=lambda l: -val[l])
            if len(c) >= 2:
                s.watch[c[0]].append(c); s.watch[c[1]].append(c)
            return
        if not nonfalse:
            s.rootconf = True; return
        if len(nonfalse) == 1:
            s.assign(nonfalse[0])
            if s.propagate(): s.rootconf = True
            # watch it anyway (unit clause, now satisfied)
            c.sort(key=lambda l: -val[l])
            if len(c) >= 2:
                s.watch[c[0]].append(c); s.watch[c[1]].append(c)
            return
        c.sort(key=lambda l: -val[l])                    # unassigned first (val 0 > -1)
        s.watch[c[0]].append(c); s.watch[c[1]].append(c)

    def delete(s, lits):
        key = tuple(sorted(lits))
        L = s.db.get(key)
        if not L: s.ndel_miss += 1; return
        c = L.pop()
        if not L: del s.db[key]
        c.clear()

    def rup(s, lits):
        if s.rootconf: return True
        val = s.val
        save = len(s.trail); saveq = s.qhead
        ok = False
        for l in lits:
            if val[l] == 1: ok = True; break
            if val[l] == 0: s.assign(l ^ 1)
        if not ok: ok = s.propagate()
        for l in s.trail[save:]:
            s.val[l] = 0; s.val[l ^ 1] = 0
        del s.trail[save:]; s.qhead = saveq
        return ok

def norm(nums):
    st = set()
    for x in nums:
        st.add(lit_idx(x))
    if any((l ^ 1) in st for l in st): return None   # tautology
    return sorted(st)

def main():
    cnf, prf = sys.argv[1], sys.argv[2]
    maxl = int(sys.argv[3]) if len(sys.argv) > 3 else None
    t0 = time.time()
    nv = nc = None; clauses = 0; taut = 0; buf = []
    with open(cnf) as f:
        for line in f:
            if line.startswith("c"): continue
            if line.startswith("p"):
                _, _, a, b = line.split(); nv, nc = int(a), int(b); C = Checker(nv); continue
            for t in line.split():
                x = int(t)
                if x == 0:
                    if any(abs(y) > nv for y in buf): raise SystemExit("variable out of bounds in the formula")
                    c = norm(buf); buf = []; clauses += 1
                    if c is None: taut += 1; continue
                    C.add(c)
                else: buf.append(x)
    assert buf == [], "unterminated clause"
    assert clauses == nc, f"number of clauses {clauses} != header {nc}"
    if not C.rootconf and C.propagate(): C.rootconf = True
    print(f"formula: {nv} variables, {nc} clauses (tautologies ignored: {taut}); root conflict: {C.rootconf}", flush=True)
    nl = nr = nd = 0; success = False; where = None
    with open(prf) as f:
        for line in f:
            t = line.split()
            if not t: continue
            nl += 1
            if maxl and nl > maxl: break
            dele = t[0] == "d"
            if dele: t = t[1:]
            nums = [int(x) for x in t]
            assert nums and nums[-1] == 0 and 0 not in nums[:-1], f"line {nl} malformed"
            nums = nums[:-1]
            if any(abs(y) > nv for y in nums):
                # new variable (extension): impossible in pure RUP beyond nv -> grow the tables
                m = max(abs(y) for y in nums)
                C.val.extend([0] * (2 * (m - nv))); C.watch.extend([] for _ in range(2 * (m - nv))); nv = C.nv = m
            c = norm(nums)
            if dele:
                nd += 1
                if c is not None: C.delete(c)
                continue
            if c is None: nr += 1; continue                    # tautological lemma: trivially valid
            if not C.rup(c):
                print(f"FAILURE: lemma at line {nl} not RUP: {nums[:20]}...", flush=True)
                print("RESULT: PROOF REJECTED"); return 1
            nr += 1
            if not c: success = True; where = nl; break
            C.add(c)
            if C.rootconf: success = True; where = nl; break
            if nr % 100000 == 0:
                print(f"  {nl} lines, {nr} RUP lemmas, {nd} deletions, {time.time()-t0:.0f} s, "
                      f"{resource.getrusage(resource.RUSAGE_SELF).ru_maxrss//1024} MB", flush=True)
    dt = time.time() - t0; mem = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss // 1024
    print(f"lines read {nl}; RUP lemmas checked {nr}; deletions {nd} (not found {C.ndel_miss}); {dt:.0f} s; {mem} MB")
    if success: print(f"RESULT: EMPTY CLAUSE OBTAINED at line {where}: VALID PROOF (formula unsatisfiable)"); return 0
    print("RESULT: NO EMPTY CLAUSE (incomplete or truncated proof)"); return 2

if __name__ == "__main__":
    sys.exit(main())
