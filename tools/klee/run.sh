#!/usr/bin/env bash
# Explore one instruction family with KLEE and turn its tests into cases.
#
#   tools/klee/run.sh <SPEC> [max seconds, default 3600]
#   REPLAY_ONLY=1 tools/klee/run.sh <SPEC>   (KLEE's output kept: only the replay and info.txt)
#
# SPEC is a name of harness.cpp's kSpecs (XCHG_IJ, ADD, STIX, DICTGET, ...). Output in
# $RUNS/<SPEC> (default ~/ws/klee/runs): klee/ (KLEE's output, one .ktest per explored path),
# klee.log, info.txt (KLEE's summary: whether the exploration finished, paths, time), and
# cases.tsv: one line per test,
#   <ktest> \t <path signature> \t <global version> \t <gas limit> \t <code BOC hex> \t <stack tokens>
# made by the native replay binary, which rebuilds each test's input, reruns it and checks that
# it takes the path (signature) KLEE recorded; a test that does not is reported as ERROR.
set -euo pipefail
SPEC=${1:?spec}; MAXT=${2:-3600}
KW=${KW:-$HOME/ws/klee}; B=${OUT:-$KW/build}; RUNS=${RUNS:-$KW/runs}
R=$RUNS/$SPEC
if [ -n "${REPLAY_ONLY:-}" ]; then
  [ -d "$R/klee" ] || { echo "no KLEE output in $R" >&2; exit 1; }
  kr=$(grep '^klee_exit ' "$R/info.txt" | cut -d' ' -f2); secs=$(grep '^seconds ' "$R/info.txt" | cut -d' ' -f2)
else
rm -rf "$R"; mkdir -p "$R"
t0=$(date +%s)
set +e
"$KW/klee-build/bin/klee" --libc=uclibc --libcxx \
  --output-dir="$R/klee" --max-time="${MAXT}s" --max-memory="${KLEE_MEM:-6000}" \
  --search="${KLEE_SEARCH:-dfs}" --use-forked-solver=false --dump-states-on-halt=false \
  --watchdog --external-calls=all --external-call-warnings=none \
  --only-output-states-covering-new=false --write-no-tests=false ${KLEE_EXTRA:-} \
  "$B/harness.bc" "$SPEC" > "$R/klee.log" 2>&1
kr=$?
set -e
secs=$(( $(date +%s) - t0 ))
fi
set +o pipefail
{
  echo "spec $SPEC"
  echo "klee_exit $kr"
  echo "seconds $secs"
  grep -E 'KLEE: done:|HaltTimer|halting|max-time|Stack dump' "$R/klee.log" || true  # a crash: no summary
  echo "errors $(find "$R/klee" -name '*.err' | wc -l)"
  find "$R/klee" -name '*.err' | sort | head -20 | while read -r e; do
    echo "err $(basename "$e") $(head -1 "$e")"
  done
} > "$R/info.txt"
# a state KLEE stopped early (time or memory limit, a solver timeout) leaves a test of a partial
# path (and a .early or .solver.err file): not a path, left out
: > "$R/ktests.txt"; : > "$R/partial.txt"
find "$R/klee" -name '*.ktest' | sort | while read -r k; do
  if [ -f "${k%.ktest}.early" ] || [ -f "${k%.ktest}.solver.err" ]; then echo "$k" >> "$R/partial.txt"
  else echo "$k" >> "$R/ktests.txt"; fi
done
set -o pipefail
: > "$R/cases.tsv"
if [ -s "$R/ktests.txt" ]; then
  xargs -a "$R/ktests.txt" -n 100 -P "$(nproc)" "$B/replay" ktest "$SPEC" > "$R/cases.unsorted" || true
  sort "$R/cases.unsorted" > "$R/cases.tsv"; rm -f "$R/cases.unsorted"
fi
echo "tests $(wc -l < "$R/ktests.txt") (partial paths left out: $(wc -l < "$R/partial.txt"))" >> "$R/info.txt"
echo "replay_errors $(grep -c $'\tERROR\t' "$R/cases.tsv" || true)" >> "$R/info.txt"
echo "paths_exact $(grep -v $'\tERROR\t' "$R/cases.tsv" | cut -f2 | sort -u | wc -l)" >> "$R/info.txt"
echo "paths_edges $(grep -v $'\tERROR\t' "$R/cases.tsv" | cut -f3 | sort -u | wc -l)" >> "$R/info.txt"
cat "$R/info.txt"
