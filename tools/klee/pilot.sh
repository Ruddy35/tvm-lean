#!/usr/bin/env bash
# The whole check for a list of instruction families, from the repository root on a server set
# up by tools/klee/setup.sh: build, KLEE on every family in parallel, then measure.sh on each.
#
#   tools/klee/pilot.sh <max seconds per family> <SPEC>...
#   PAR [default: number of specs]  KLEE_MEM [MB per KLEE, default 6000]
#
# Prints per family: KLEE's summary (run.sh info.txt), the Lean-vs-C++ result per version and the
# coverage of KLEE's paths by the existing suites (measure.sh coverage.txt).
set -euo pipefail
MAXT=${1:?seconds}; shift
SPECS=("$@")
KW=${KW:-$HOME/ws/klee}; RUNS=${RUNS:-$KW/runs}
HERE=$(cd "$(dirname "$0")" && pwd); ROOT=$(cd "$HERE/../.." && pwd)
cd "$ROOT"
bash "$HERE/build.sh" > "$KW/build.log" 2>&1 || { tail -20 "$KW/build.log"; exit 1; }
lake build tvm-lean-tests > "$KW/lean-build.log" 2>&1 || { grep -m5 error "$KW/lean-build.log"; exit 1; }
echo "built $(date -u +%T)"
printf '%s\n' "${SPECS[@]}" | xargs -P "${PAR:-${#SPECS[@]}}" -I{} \
  bash -c "bash '$HERE/run.sh' {} $MAXT > /dev/null 2>&1"
echo "explored $(date -u +%T)"
for s in "${SPECS[@]}"; do
  bash "$HERE/measure.sh" "$s" > "$RUNS/$s/measure.log" 2>&1 || echo "$s: measure.sh failed"
done
echo "measured $(date -u +%T)"
for s in "${SPECS[@]}"; do
  R=$RUNS/$s
  echo "=== $s"
  grep -v '^spec \|^err \|KLEE: done: total' "$R/info.txt" | tr '\n' ' '; echo
  grep -h '^cases=' "$R"/diff-v*.txt 2>/dev/null | sort | uniq -c | tr '\n' ' '; echo
  grep -v '^spec ' "$R/coverage.txt" 2>/dev/null | tr '\n' ' '; echo
done
