#!/usr/bin/env bash
# Builds the library G509 one module at a time (in dependency order), so that a single Lean process runs at a
# time. This is how the timings of README.md were measured (there, each step also ran under
# `systemd-run --user --scope -p MemoryMax=... -p MemorySwapMax=0`). Run from the repository root, after
# `lake exe cache get`.
set -euo pipefail
export LEAN_NUM_THREADS=${LEAN_NUM_THREADS:-1}
python3 - > .lake/g509_order.txt <<'PY'
import re, sys
sys.setrecursionlimit(10000)
seen, vis = [], set()
def imports(m):
    src = open(m.replace('.', '/') + '.lean').read()
    return [x for x in re.findall(r'^import (\S+)', src, re.M) if x.startswith('G509')]
def dfs(m):
    if m in vis: return
    vis.add(m)
    for x in imports(m): dfs(x)
    seen.append(m)
dfs('G509')
print('\n'.join(seen))
PY
while read -r m; do
  echo "== $m"
  lake build "$m"
done < .lake/g509_order.txt
lake build
