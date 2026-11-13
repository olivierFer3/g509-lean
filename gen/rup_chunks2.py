# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 olivierFer3 (code produced with Claude Code; see PROVENANCE.md)
"""Splits a trimmed LRAT proof into Lean chunk modules for G509/RUP.lean; each chunk exports directly to each
of its consuming chunks (lists x<j>_<k>), without transit through the intermediate chunks.
Usage: rup_chunks2.py cnf lrat outdir Pkg hint_budget Fdef(or -) [ftpkg]  (env. STEPCAP: max steps per chunk)
  ftpkg: package containing FT (default Pkg).
Commands used for this repository (see PROVENANCE.md):
  STEPCAP=600 python3 gen/rup_chunks2.py gen/g509_sym.cnf g509_unsat_trim.lrat G509/T G509.T 24000 G509C.F G509.S
  STEPCAP=600 python3 gen/rup_chunks2.py gen/g509_sym.cnf g509_unsat_trim.lrat <tmpdir> G509.S 24000 G509C.F
    (the second command is used only for its FT.lean, which becomes G509/S/FT.lean)
"""
# License header written at the top of each generated Lean file.
HEADER = '/-\nCopyright (c) 2026 olivierFer3. All rights reserved.\nReleased under Apache 2.0 license as described in the file LICENSE.\nAuthors: olivierFer3 (code produced with Claude Code; see PROVENANCE.md)\n-/\n'
import sys, os, bisect
cnf, lrat, outdir, pkg, budget = sys.argv[1:6]; budget = int(budget)
Fdef = sys.argv[6] if len(sys.argv) > 6 and sys.argv[6] != '-' else None
ftpkg = sys.argv[7] if len(sys.argv) > 7 else pkg

def lit(x): return 2 * x if x > 0 else 2 * (-x) + 1
F = []
for l in open(cnf):
    if l[0] in 'pc' or not l.strip(): continue
    F.append([lit(int(x)) for x in l.split()[:-1]])
NF = len(F)
S = []
for l in open(lrat):
    t = l.split()
    if not t or t[1] == 'd': continue
    z = t.index('0', 1)
    c = [lit(int(x)) for x in t[1:z]]; h = [int(x) for x in t[z + 1:-1]]
    assert all(x > 0 for x in h), 'RAT steps are not supported'
    S.append((int(t[0]), c, h))
    if not c: break
assert not S[-1][1]
STEPCAP = int(os.environ.get('STEPCAP', '1000000'))
cuts = [0]; acc = 0
for k, s in enumerate(S):
    if (acc + len(s[2]) > budget or k - cuts[-1] >= STEPCAP) and k > cuts[-1]: cuts.append(k); acc = 0
    acc += len(s[2])
cuts.append(len(S))
NC = len(cuts) - 1
chunk_of = {s[0]: bisect.bisect_right(cuts, k) - 1 for k, s in enumerate(S)}
clause = {s[0]: s[1] for s in S}
# needs[k][j] = sorted list of the clauses of chunk j used by chunk k (j < k)
needs = [dict() for _ in range(NC)]
for k in range(NC):
    seen = set()
    for s in S[cuts[k]:cuts[k + 1]]:
        for x in s[2]:
            if x > NF and chunk_of[x] != k and x not in seen:
                seen.add(x); needs[k].setdefault(chunk_of[x], []).append(x)
for k in range(NC):
    for j in needs[k]: needs[k][j].sort()
consumers = [[k for k in range(NC) if j in needs[k]] for j in range(NC)]

FUEL = 4000
def P(c, off=0):
    assert len(c) < FUEL and all(1 <= x + off < 2 ** 20 for x in c)
    n = 0
    for x in reversed(c): n = (n << 20) | (x + off)
    return n
PC = lambda c: '(U %d %d)' % (FUEL, P(c)) if c else '[]'
PH = lambda h: 'UH %d %d' % (FUEL, P(h, 1))
L = lambda c: '[' + ', '.join(map(str, c)) + ']'
FN = Fdef or 'F'
os.makedirs(outdir, exist_ok=True)
tot_imp = 0
for k in range(NC):
    a, b = cuts[k], cuts[k + 1]
    fs = []; loc = {}
    for (_, _, h) in S[a:b]:
        for x in h:
            if x <= NF and x not in loc: loc[x] = len(fs); fs.append(x)
    imp = []
    srcs = sorted(needs[k])
    for j in srcs: imp += needs[k][j]
    m0 = len(fs)
    for q, x in enumerate(imp): loc[x] = m0 + q
    m = m0 + len(imp)
    for q, s in enumerate(S[a:b]): loc[s[0]] = m + q
    hs = [[loc[x] for x in s[2]] for s in S[a:b]]
    for q in range(b - a): assert all(x < m + q for x in hs[q])
    table = [F[x - 1] for x in fs] + [clause[x] for x in imp] + [s[1] for s in S[a:b]]
    tot_imp += len(imp)
    last = (k == NC - 1)
    name = 'C%d' % k
    with open(os.path.join(outdir, name + '.lean'), 'w') as f:
        f.write(HEADER + 'import G509.RUP\nimport %s.FT\n' % ftpkg + ('import %s.C%d\n' % (pkg, k - 1) if k else ''))
        f.write('\nnamespace %s\nopen RV\n' % pkg + ('open %s\n' % ftpkg if ftpkg != pkg else '') + '\n')
        dep = max(1, (len(table) - 1).bit_length())
        f.write('set_option maxRecDepth 100000 in\nnoncomputable def L%d : List (List Nat) := [\n' % k + ',\n'.join('  ' + PC(c) for c in table) + ']\n\n')
        f.write('noncomputable def t%d : Tb := build %d L%d\n\n' % (k, dep, k))
        f.write('noncomputable def fs%d : List Nat := %s\n\n' % (k, L([x - 1 for x in fs])))
        f.write('set_option maxRecDepth 100000 in\nnoncomputable def hs%d : List (List Nat) := [\n' % k + ',\n'.join('  ' + PH(h) for h in hs) + ']\n\n')
        # exports, one list per consuming chunk
        xs = []
        for c in consumers[k]:
            f.write('set_option maxRecDepth 100000 in\nnoncomputable def x%d_%d : List (Nat × List Nat) := [\n' % (k, c)
                    + ',\n'.join('  (%d, %s)' % (loc[x], PC(clause[x])) for x in needs[c][k]) + ']\n\n')
            xs.append('x%d_%d' % (k, c))
        if last:
            f.write('noncomputable def fin%d : List (Nat × List Nat) := [(%d, [])]\n\n' % (k, loc[S[-1][0]]))
            xs.append('fin%d' % k)
        es = '[]'
        for x in reversed(xs): es = '(appE %s %s)' % (x, es)
        f.write('noncomputable def es%d : List (Nat × List Nat) := %s\n\n' % (k, es))
        impE = '(all_nil τ)'; impT = '[]'
        for j in reversed(srcs):
            impT = '(app (snds x%d_%d) %s)' % (j, k, impT)
            impE = '(all_app τ _ _ (all_snds τ _ (inv%d_%d τ hF)) %s)' % (j, k, impE)
        f.write('noncomputable def imp%d : List (List Nat) := %s\n\n' % (k, impT))
        f.write('set_option profiler true in\nset_option maxRecDepth 1000000 in\ntheorem ok%d : chunkCheck FT %d t%d fs%d imp%d hs%d es%d = true := by decide +kernel\n\n' % (k, NF, k, k, k, k, k))
        f.write('theorem inv%d (τ : Nat → Bool) (hF : LR.SatF τ %s) : ∀ p ∈ es%d, LR.clauseT τ p.2 = true :=\n' % (k, FN, k))
        f.write('  chunk_sound FT %d t%d fs%d imp%d hs%d es%d ok%d τ (FT_good τ hF) %s\n\n' % (NF, k, k, k, k, k, k, impE))
        for i, x in enumerate(xs):
            mem = 'hp'
            mem = 'appE_l _ _ _ %s' % mem if i < len(xs) - 1 or True else mem
            # p ∈ x_i  ->  p ∈ appE x_0 (appE x_1 ... (appE x_i rest))
            pr = 'appE_l _ _ _ hp'
            for _ in range(i): pr = 'appE_r _ _ (%s) _' % pr
            nm = 'inv%s' % x[1:] if x.startswith('x') else 'invfin%d' % k
            f.write('theorem %s (τ : Nat → Bool) (hF : LR.SatF τ %s) : ∀ p ∈ %s, LR.clauseT τ p.2 = true :=\n'
                    '  fun p hp => inv%d τ hF p (%s)\n\n' % (nm, FN, x, k, pr))
        if last:
            f.write('theorem unsat : ∀ τ, ¬ LR.SatF τ %s := fun τ hF =>\n  not_empty τ fin%d %d (by simp [fin%d]) (invfin%d τ hF)\n\n' % (FN, k, loc[S[-1][0]], k, k))
        f.write('end %s\n' % pkg)
        if last: f.write('\n#print axioms %s.unsat\n' % pkg)
    print(name, 'steps', b - a, 'F', m0, 'imports', len(imp), 'sources', len(srcs), 'consumers', len(consumers[k]),
          'hints', sum(map(len, hs)), 'literals', sum(map(len, table)), flush=True)
print('total imports', tot_imp)
if ftpkg == pkg:
    with open(os.path.join(outdir, 'FT.lean'), 'w') as f:
        def tree(items):
            if len(items) <= 1: return 'lf ' + PC(items[0] if items else [])
            return 'nd (' + tree(items[0::2]) + ') (' + tree(items[1::2]) + ')'
        f.write(HEADER + 'import G509.RUP\n' + ('import G509.CNF\n' if Fdef else '') + '\nnamespace %s\nopen RV RV.Tb\n\n' % pkg)
        if not Fdef:
            f.write('noncomputable def F : List (List Nat) := [\n' + ',\n'.join('  ' + L(c) for c in F) + ']\n\n')
        f.write('set_option maxHeartbeats 0 in\nset_option maxRecDepth 100000 in\nnoncomputable def FT : Tb :=\n  ' + tree(F) + '\n\n')
        f.write('set_option maxRecDepth 1000000 in\ntheorem FT_ok : baseOK FT %s 0 = true := by decide +kernel\n\n' % FN)
        f.write('theorem len_F : len %s = %d := by decide +kernel\n\n' % (FN, NF))
        f.write('theorem FT_good (τ : Nat → Bool) (h : LR.SatF τ %s) : Good τ FT %d := by\n'
                '  have := ft_good FT %s FT_ok τ h; rwa [len_F] at this\n\nend %s\n' % (FN, NF, FN, pkg))
