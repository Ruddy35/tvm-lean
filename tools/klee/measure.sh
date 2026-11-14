#!/usr/bin/env bash
# After tools/klee/run.sh on a set of runs: run KLEE's cases on the Lean model and C++, and
# measure which of KLEE's paths the existing oracle and fuzz suites take. Run from the repository
# root with tvm-lean-tests built and the oracle set up (TON_FIFT_BIN, TON_FIFT_LIB, as for the
# suites).
#
#   tools/klee/measure.sh [paths|all]
#     paths (default): one input per edge path of each family at every version 0..16, and at most
#       OWNCAP (default 100) inputs of each run at the version KLEE found them at
#     all: every input run.sh kept (each exact path's first, KEEP others) at every version
#   SKIP_DIFF=1: no Lean-vs-C++ pass (step 2); ONLY_DIFF=1: no suites' paths and coverage (steps 3, 4)
#   RUNS [~/ws/klee/runs]: the runs (every <family>.<class> with a `done` that RUNLIST, default
#   $RUNS/../runlist.txt as all.sh writes it, names; every one if there is none); M [$RUNS/../measure]
#
# In $M:
#   klee-cases.tsv      KLEE's cases as case lines (Tests/Harness/CaseFile.lean), one per input
#   replay-check.txt    those run back through `replay cases ALL`: each must take the path (all
#                       three signatures) KLEE recorded for it
#   klee-inputs.tsv     one case line per distinct input up to the version
#   diff-v<N>.txt       on the Lean model and C++ (runOracleCase) at global version N, in chunks
#                       (run_cases: a case the model does not finish within CASE_TIME is a TIMEOUT);
#                       fails.txt: the FAIL and TIMEOUT lines of all versions; differential.txt:
#                       the counts
#   existing.tsv        every suite's oracle and fuzz cases as runvmx gets them (--dump-cases;
#                       the cases of Tests.Gen.Klee left out), existing-sigs.tsv: every step of
#                       every instruction family in each of them, at every version (replay)
#   coverage.tsv        per family: classes run (+ finished, - cut by the time limit), seconds,
#                       tests, KLEE's exact/edge/coarse paths, the suites' paths, how many of
#                       KLEE's the suites take, missed (edge, coarse); summary.txt: the totals
#   missed.tsv          one case per missed path (C: coarse path; E: edge path of a taken coarse one)
set -euo pipefail
MODE=${1:-paths}
KW=${KW:-$HOME/ws/klee}; B=${OUT:-$KW/build}; RUNS=${RUNS:-$KW/runs}; JOBS=${JOBS:-$(nproc)}
M=${M:-$RUNS/../measure}
HERE=$(cd "$(dirname "$0")" && pwd); ROOT=$(cd "$HERE/../.." && pwd)
TESTS=$ROOT/.lake/build/bin/tvm-lean-tests
PY="python3 -I $HERE/klee_cases.py"
mkdir -p "$M"
# the runs of the last all.sh (its run list), not whatever else RUNS holds
[ -f "${RUNLIST:-$RUNS/../runlist.txt}" ] && export KLEE_RUNLIST=${RUNLIST:-$RUNS/../runlist.txt}
# run_cases <case lines> <version> <out>: Lean model vs C++ (tvm-lean-tests --cases-file) in chunks
# of CHUNK (200) cases, JOBS at once, a chunk within CHUNK_TIME (600 s); the cases of a chunk cut by
# its limit run again one by one within CASE_TIME (120 s): one cut there is a TIMEOUT line (a case
# the model did not finish in that time; C++ is not run on it). <out>: the OK, FAIL and TIMEOUT lines.
run_cases() {
  local d=$M/chunks-v$2 c
  rm -rf "$d"; mkdir -p "$d"
  split -a 4 -l "${CHUNK:-200}" "$1" "$d/c."
  ls "$d" | xargs -P "$JOBS" -I{} sh -c "TVMLEAN_GLOBAL_VERSION=$2 timeout ${CHUNK_TIME:-600} '$TESTS' --cases-file '$d/{}' --jobs 1 > '$d/{}.out' 2>&1 || true"
  for c in $(ls "$d" | grep -v '\.out$'); do
    grep -q '^cases=' "$d/$c.out" && continue
    mkdir -p "$d/$c.one"
    split -a 4 -l 1 "$d/$c" "$d/$c.one/x."
    ls "$d/$c.one" | xargs -P "$JOBS" -I{} sh -c "TVMLEAN_GLOBAL_VERSION=$2 timeout ${CASE_TIME:-120} '$TESTS' --cases-file '$d/$c.one/{}' --jobs 1 > '$d/$c.one/{}.out' 2>&1 || true"
    for x in $(ls "$d/$c.one" | grep -v '\.out$'); do
      if grep -q '^cases=' "$d/$c.one/$x.out"; then cat "$d/$c.one/$x.out" >> "$d/$c.out"
      else printf '%s\tTIMEOUT\n' "$(cut -f1 "$d/$c.one/$x")" >> "$d/$c.out"; fi
    done
  done
  cat "$d"/*.out | grep -P '^[^\t]+\t(OK|FAIL|TIMEOUT)|^\[worker' > "$3" || true
  rm -rf "$d"
}
par_replay() {  # <case lines> <out>: replay cases ALL, JOBS ways
  split -n l/"$JOBS" "$1" "$M/part."
  ls "$M"/part.* | xargs -P "$JOBS" -I{} sh -c "$B/replay cases ALL {} > {}.out" || true
  cat "$M"/part.*.out > "$2"; rm -f "$M"/part.*
}

# 1. KLEE's cases: the replay of their case lines must take KLEE's paths
$PY lines "$RUNS" > "$M/klee-cases.tsv"
par_replay "$M/klee-cases.tsv" "$M/replay-check.tsv"
$PY replaycheck "$RUNS" "$M/replay-check.tsv" > "$M/replay-check.txt"
tail -1 "$M/replay-check.txt"

# 2. Lean model vs C++ (SKIP_DIFF=1: kept from the last measurement)
if [ -z "${SKIP_DIFF:-}" ]; then
$PY inputs "$M/klee-cases.tsv" > "$M/klee-inputs.tsv"
if [ "$MODE" = paths ]; then
  $PY reps "$RUNS" edges > "$M/klee-reps.tsv"
  $PY own "$RUNS" "${OWNCAP:-100}" > "$M/klee-own.tsv"
fi
: > "$M/fails.txt"
for v in $(seq 0 16); do
  if [ "$MODE" = paths ]; then
    { awk -F'\t' -v v="$v" '$2 == v' "$M/klee-own.tsv"; cat "$M/klee-reps.tsv"; } | sort -u > "$M/run-v$v.tsv"
  else
    cp "$M/klee-inputs.tsv" "$M/run-v$v.tsv"
  fi
  t0=$(date +%s)
  run_cases "$M/run-v$v.tsv" "$v" "$M/diff-v$v.txt"
  grep -P '\tFAIL\t|\tTIMEOUT$|^\[worker' "$M/diff-v$v.txt" | sed "s/^/v$v\t/" >> "$M/fails.txt" || true
  echo "v$v cases=$(wc -l < "$M/run-v$v.tsv") ok=$(grep -cP '\tOK$' "$M/diff-v$v.txt") failures=$(grep -cP '\tFAIL\t|^\[worker' "$M/diff-v$v.txt") timeouts=$(grep -cP '\tTIMEOUT$' "$M/diff-v$v.txt") seconds=$(( $(date +%s) - t0 ))"
  rm -f "$M/run-v$v.tsv"
done | tee "$M/differential.txt"
fi

[ -n "${ONLY_DIFF:-}" ] && exit 0  # steps 1 and 2 only

# 3. the existing suites' paths: every suite (the names of the spec index), every version
# (the suites split over JOBS dumping processes: one process takes hours for all of them)
python3 -I -c 'import json,sys; n=[r["name"] for r in json.load(open(sys.argv[1]))["tvm_instructions"]]; k=int(sys.argv[2]); [print(",".join(n[i::k])) for i in range(k)]' \
  "$ROOT/docs/progress/tvm_spec_index.json" "$JOBS" > "$M/dump-groups.txt"
split -a 3 -l 1 "$M/dump-groups.txt" "$M/dump."
ls "$M"/dump.??? | xargs -P "$JOBS" -I{} sh -c "'$TESTS' --dump-cases \"\$(cat {})\" > {}.tsv 2> {}.err"
cat "$M"/dump.???.tsv > "$M/existing.tsv"; cat "$M"/dump.???.err > "$M/existing.err"
rm -f "$M"/dump.??? "$M"/dump.???.tsv "$M"/dump.???.err "$M/dump-groups.txt"
$PY versions "$M/existing.tsv" > "$M/existing-v.tsv"
par_replay "$M/existing-v.tsv" "$M/existing-sigs.tsv"
rm -f "$M/existing-v.tsv"
echo "existing cases $(grep -vc '/oracle/klee/' "$M/existing.tsv") (not dumped: $(wc -l < "$M/existing.err"))"

# 4. coverage
$PY compare "$RUNS" "$M/existing-sigs.tsv" "$M" | tee "$M/summary.txt"
