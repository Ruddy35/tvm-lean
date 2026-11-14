#!/usr/bin/env bash
# Explore one family under one gas class with KLEE and turn its tests into cases.
#
#   tools/klee/run.sh <FAMILY>.<CLASS> [max seconds, default 600]
#   REPLAY_ONLY=1 tools/klee/run.sh <RUN>   (KLEE's output kept: only the replay and info.txt)
#
# FAMILY is a family of the generated table (`replay families`: an instruction form such as ADD,
# DICTIGETREF, XC2PU, or GAP_<opcode> for an opcode range no form has), CLASS one of S (small gas,
# symbolic), G (gas 10^6), N (gas 10^6, a NaN on the stack); `gen_families.py --runs` lists them.
# Output in $RUNS/<RUN> (default ~/ws/klee/runs): klee/ (KLEE's output; the .ktest files are
# deleted once replayed, unless KEEP_KTESTS=1), klee.log, info.txt (KLEE's summary: whether the
# exploration finished, tests, paths, time), done (the run is complete: run.sh skips it unless
# FORCE=1), and cases.tsv: one line per test (once the tests are replayed and deleted: the first
# test of every exact path and at most KEEP others),
#   <ktest> \t <exact sig> \t <edge sig> \t <coarse sig> \t <global version> \t <gas limit>
#           \t <code BOC hex> \t <stack tokens>
# made by the native replay binary, which rebuilds each test's input, reruns it and checks that
# it takes the path (all three signatures) KLEE recorded; a test that does not is an ERROR line.
set -euo pipefail
RUN=${1:?run}; MAXT=${2:-600}
KW=${KW:-$HOME/ws/klee}; B=${OUT:-$KW/build}; RUNS=${RUNS:-$KW/runs}
R=$RUNS/$RUN
if [ -f "$R/done" ] && [ -z "${FORCE:-}" ] && [ -z "${REPLAY_ONLY:-}" ]; then
  cat "$R/info.txt"; exit 0
fi
if [ -n "${REPLAY_ONLY:-}" ]; then
  [ -d "$R/klee" ] || { echo "no KLEE output in $R" >&2; exit 1; }
  kr=$(grep '^klee_exit ' "$R/info.txt" | cut -d' ' -f2); secs=$(grep '^seconds ' "$R/info.txt" | cut -d' ' -f2)
else
rm -rf "$R"; mkdir -p "$R"
t0=$(date +%s)
set +e
# --output-source=false: no assembly.ll (37 MB a run); the solver in-process (the forked one is
# slower here) with a limit per query (a state whose query times out is dropped, the run goes on);
# depth-first (random-path and coverage-guided search crashed KLEE 3.3 on this module); no
# overshift checks: the optimizer turns the guarded shift of CellBuilder::store_long
# (`val_bits == 0 ? 0 : val << (64 - val_bits)`, crypto/vm/cells/CellBuilder.cpp:337) into a shift
# and a select, and KLEE's check ended the paths that store 0 bits (dict.cpp append_dict_label_same)
# as errors; the native replay checks every path's signatures all the same
timeout --signal=KILL $((MAXT + 600)) "$KW/klee-build/bin/klee" --libc=uclibc --libcxx \
  --output-dir="$R/klee" --max-time="${MAXT}s" --max-memory="${KLEE_MEM:-5000}" \
  --search="${KLEE_SEARCH:-dfs}" --use-forked-solver=false --dump-states-on-halt=false \
  --watchdog --max-solver-time="${SOLVER_TIME:-20}s" --check-overshift=false \
  --external-calls=all --external-call-warnings=none --output-source=false \
  --output-istats=false --only-output-states-covering-new=false --write-no-tests=false \
  ${KLEE_EXTRA:-} "$B/harness.bc" "$RUN" > "$R/klee.log" 2>&1
kr=$?
set -e
secs=$(( $(date +%s) - t0 ))
fi
set +o pipefail
{
  echo "run $RUN"
  echo "klee_exit $kr"
  echo "seconds $secs"
  grep -E 'KLEE: done:|HaltTimer|WATCHDOG|halting|max-time|Stack dump' "$R/klee.log" || true  # a crash: no summary
  echo "errors $(find "$R/klee" -name '*.err' | wc -l)"
  find "$R/klee" -name '*.err' | sort | head -20 | while read -r e; do
    echo "err $(basename "$e") $(head -1 "$e")"
  done
} > "$R/info.txt"
# a state KLEE stopped early (time or memory limit, a solver timeout) or at an error (info.txt
# lists them) leaves a test of a partial path (and a .early or .err file): not a path, left out
: > "$R/ktests.txt"; : > "$R/partial.txt"
find "$R/klee" -name '*.ktest' | sort | while read -r k; do
  if [ -f "${k%.ktest}.early" ] || compgen -G "${k%.ktest}.*.err" > /dev/null; then echo "$k" >> "$R/partial.txt"
  else echo "$k" >> "$R/ktests.txt"; fi
done
set -o pipefail
: > "$R/cases.tsv"
if [ -s "$R/ktests.txt" ]; then
  xargs -a "$R/ktests.txt" -n 200 -P "${REPLAY_JOBS:-2}" "$B/replay" ktest "$RUN" > "$R/cases.unsorted" || true
  sort "$R/cases.unsorted" > "$R/cases.tsv"; rm -f "$R/cases.unsorted"
fi
ok() { grep -v $'\tERROR\t' "$R/cases.tsv" || true; }
# finished: KLEE ended by itself (no time limit, no crash) and left no partial path but the ones
# the harness discards on purpose (silent exits are not tests at all)
fin=no
# (the time limit: the watchdog interrupts KLEE, "WATCHDOG: time expired", or the HaltTimer)
if [ "$kr" = 0 ] && ! grep -qE 'HaltTimer|WATCHDOG: time expired|ctrl-c detected|over memory cap|killing [0-9]+ states' "$R/klee.log" &&
   grep -q 'KLEE: done: generated tests' "$R/klee.log" && [ ! -s "$R/partial.txt" ]; then
  fin=yes
fi
{
  echo "finished $fin"
  echo "tests $(wc -l < "$R/ktests.txt") (partial paths left out: $(wc -l < "$R/partial.txt"))"
  echo "replay_errors $(grep -c $'\tERROR\t' "$R/cases.tsv" || true)"
  echo "paths_exact $(ok | cut -f2 | sort -u | wc -l)"
  echo "paths_edges $(ok | cut -f3 | sort -u | wc -l)"
  echo "paths_coarse $(ok | cut -f4 | sort -u | wc -l)"
} >> "$R/info.txt"
if [ -z "${KEEP_KTESTS:-}" ] && [ "$(grep -c $'\tERROR\t' "$R/cases.tsv" || true)" = 0 ]; then
  find "$R/klee" -name 'test*' -delete
  # every exact path's first test, and at most KEEP (default 300) others spread over the run
  python3 -I - "$R/cases.tsv" "${KEEP:-300}" <<'PY'
import sys
rows = [l for l in open(sys.argv[1]) if '\tERROR\t' not in l]
seen, keep, rest = set(), [], []
for l in rows:
    s = l.split('\t')[1]
    (rest if s in seen else keep).append(l)
    seen.add(s)
k = int(sys.argv[2])
if len(rest) > k:
    rest = [rest[i * len(rest) // k] for i in range(k)]
open(sys.argv[1], 'w').writelines(sorted(keep + rest))
PY
  echo "kept $(wc -l < "$R/cases.tsv") cases" >> "$R/info.txt"
fi
touch "$R/done"
cat "$R/info.txt"
