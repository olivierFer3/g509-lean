# SPDX-License-Identifier: Apache-2.0
r"""Streaming variant of drat_check.py: the SAME checker (the class Checker and the function read_cnf are imported
unchanged from drat_check.py), but the DRAT proof is read line by line instead of being loaded entirely into
memory (the original version was killed by a 1200 MB memory limit on a proof of 1.66 M lines). The loop below
reproduces exactly `check()` of drat_check.py.
Usage: python3 -B drat_check_stream.py formula.cnf proof.drat"""
import sys, time, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from drat_check import Checker, read_cnf

def steps(path):
    for line in open(path):
        t = line.split()
        if not t: continue
        assert t[-1] == "0"
        if t[0] == "d": yield ("d", [int(x) for x in t[1:-1]])
        else: yield ("a", [int(x) for x in t[:-1]])

def main(fc, fp):
    cnf = read_cnf(fc); print("formula: %d clauses" % len(cnf), flush=True)
    t = time.time(); ck = Checker()
    for c in cnf: ck.add(c)
    if ck.conflict([]): print("formula already contradictory by unit propagation"); return True
    nrup = nrat = ndel = 0
    for k, (typ, cl) in enumerate(steps(fp)):
        if typ == "d": ndel += ck.delete(cl); continue
        r = ck.check_lemma(cl)
        if r is None: print("FAILURE: step %d, lemma neither RUP nor RAT: %s" % (k, cl[:12])); return False
        if r == "RUP": nrup += 1
        else: nrat += 1
        if not cl:
            print("empty clause derived at step %d" % k)
            print("statistics:", dict(rup=nrup, rat=nrat, dele=ndel, sec=time.time() - t)); return True
        ck.add(cl)
        if (nrup + nrat) % 20000 == 0: print("  %d lemmas checked (%.0fs)" % (nrup + nrat, time.time() - t), flush=True)
    ok = ck.conflict([]); print("end of proof; final conflict by propagation:", ok)
    print("statistics:", dict(rup=nrup, rat=nrat, dele=ndel, sec=time.time() - t)); return ok

if __name__ == "__main__":
    ok = main(sys.argv[1], sys.argv[2])
    print("RESULT: VALID DRAT PROOF (formula unsatisfiable)" if ok else "RESULT: PROOF REJECTED", flush=True)
    sys.exit(0 if ok else 1)
