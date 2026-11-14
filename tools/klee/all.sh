#!/usr/bin/env bash
# The whole check on a server set up by tools/klee/setup.sh, from the repository root: build,
# KLEE on every run in parallel (resumable: finished runs are skipped), then measure.sh.
#
#   tools/klee/all.sh <max seconds per run> [run ...]
#     runs: `<family>.<class>` names; default every run of the table (gen_families.py --runs),
#     PART=k/n: the k-th of n shares of the families (one share per server)
#   PAR [default: nproc - 4] KLEE processes at once; KLEE_MEM [MB per KLEE, default 5000]
#   NOBUILD=1: no build.sh / lake build; NOMEASURE=1: the KLEE runs only; MODE: measure.sh's;
#   RERUN=<regex>: make the matching runs again even if done
#
# Prints the summary of the runs (finished or cut, tests, paths) and measure.sh's results.
set -euo pipefail
MAXT=${1:?seconds}; shift
KW=${KW:-$HOME/ws/klee}; RUNS=${RUNS:-$KW/runs}
HERE=$(cd "$(dirname "$0")" && pwd); ROOT=$(cd "$HERE/../.." && pwd)
cd "$ROOT"
mkdir -p "$RUNS"
if [ $# -gt 0 ]; then
  printf '%s\n' "$@" > "$RUNS/../runlist.txt"
else
  tonops=; [ "${TONOPS:-1}" = 1 ] && tonops=--tonops
  python3 -I "$HERE/gen_families.py" docs/progress/tvm_spec_index.json --runs ${PART:+--part=$PART} $tonops \
    > "$RUNS/../runlist.txt"
fi
if [ -z "${NOBUILD:-}" ]; then
  bash "$HERE/build.sh" > "$KW/build.log" 2>&1 || { tail -20 "$KW/build.log"; exit 1; }
  echo "built $(date -u +%T)"
fi
if [ -n "${RERUN:-}" ]; then  # runs to make again (an extended regex over the run names)
  grep -E "$RERUN" "$RUNS/../runlist.txt" | while read -r r; do rm -f "$RUNS/$r/done"; done
fi
echo "runs $(wc -l < "$RUNS/../runlist.txt"), $(cd "$RUNS" && ls */done 2>/dev/null | wc -l) done before"
xargs -a "$RUNS/../runlist.txt" -P "${PAR:-$(( $(nproc) - 4 ))}" -I{} \
  bash -c "bash '$HERE/run.sh' {} $MAXT > /dev/null 2>&1 || echo 'run.sh {} failed'"
echo "explored $(date -u +%T)"
python3 -I - "$RUNS" "$RUNS/../runlist.txt" <<'EOF' | tee "$RUNS/../runs-summary.txt"
import os, sys
runs = [l.strip() for l in open(sys.argv[2]) if l.strip()]
tot = {'finished': 0, 'cut': 0, 'missing': 0, 'tests': 0, 'errors': 0, 'seconds': 0}
for r in runs:
    p = os.path.join(sys.argv[1], r, 'info.txt')
    if not os.path.exists(os.path.join(sys.argv[1], r, 'done')):
        tot['missing'] += 1
        print('missing', r)
        continue
    d = {}
    for l in open(p):
        k, _, v = l.rstrip('\n').partition(' ')
        d.setdefault(k, v)
    tot['finished' if d.get('finished') == 'yes' else 'cut'] += 1
    tot['tests'] += int(d.get('tests', '0').split()[0])
    tot['errors'] += int(d.get('replay_errors', '0') or 0)
    tot['seconds'] += int(d.get('seconds', '0') or 0)
    if d.get('replay_errors', '0') not in ('0', ''):
        print('replay errors', r, d.get('replay_errors'))
print(' '.join(f'{k}={v}' for k, v in tot.items()))
EOF
[ -n "${NOMEASURE:-}" ] && exit 0
if [ -z "${NOBUILD:-}" ]; then  # after the KLEE runs, which need every core
  lake build tvm-lean-tests > "$KW/lean-build.log" 2>&1 || { grep -m5 error "$KW/lean-build.log"; exit 1; }
  echo "lean built $(date -u +%T)"
fi
bash "$HERE/measure.sh" "${MODE:-paths}"
echo "measured $(date -u +%T)"
