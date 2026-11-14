#!/usr/bin/env bash
# After tools/klee/run.sh <SPEC>: run KLEE's cases on the Lean model and C++, and measure which of
# KLEE's paths the existing oracle and fuzz suites reach. Run from the repository root with
# tvm-lean-tests built and the oracle set up (TON_FIFT_BIN, TON_FIFT_LIB, as for the suites).
#
#   tools/klee/measure.sh <SPEC> [versions, default "0 1 ... 16"]
#
# In $RUNS/<SPEC> (default ~/ws/klee/runs):
#   klee-cases.tsv     KLEE's cases as case lines (Tests/Harness/CaseFile.lean), one per input
#   klee-reps.tsv      one of them per exact C++ path
#   diff-v<N>.txt      on the Lean model and C++ (runOracleCase) at global version N: the cases
#                      KLEE found at version N (at most CAP of all, default 20000, every k-th) and
#                      every case of klee-reps.tsv
#   suites.txt         the suites whose opcodes meet the spec's ranges
#   existing.tsv       their oracle and fuzz cases as the oracle gets them (--dump-cases)
#   existing-sigs.tsv  the C++ path of every execution of the instruction in each existing case,
#                      at every version (native replay)
#   coverage.txt       the path counts; missed.tsv: one KLEE case per path no existing case reaches
#   replay-check.tsv   KLEE's cases run back through the replay from their case lines: the path
#                      must be the one KLEE recorded (the case line is the input KLEE found)
set -euo pipefail
SPEC=${1:?spec}; VERSIONS=${2:-$(seq -s ' ' 0 16)}
KW=${KW:-$HOME/ws/klee}; B=${OUT:-$KW/build}; RUNS=${RUNS:-$KW/runs}; JOBS=${JOBS:-$(nproc)}
HERE=$(cd "$(dirname "$0")" && pwd); ROOT=$(cd "$HERE/../.." && pwd)
R=$RUNS/$SPEC
TESTS=$ROOT/.lake/build/bin/tvm-lean-tests
PY="python3 -I $HERE/klee_cases.py"

# 1. KLEE's cases: the replay of their case lines must take KLEE's paths
$PY lines "$R/cases.tsv" > "$R/klee-cases.tsv"
split -n l/"$JOBS" "$R/klee-cases.tsv" "$R/kc.part."
ls "$R"/kc.part.* | xargs -P "$JOBS" -I{} sh -c "$B/replay cases $SPEC {} > {}.out" || true
cat "$R"/kc.part.*.out > "$R/replay-check.tsv"; rm -f "$R"/kc.part.*
python3 -I - "$R/cases.tsv" "$R/klee-cases.tsv" "$R/replay-check.tsv" > "$R/replay-check.txt" <<'EOF'
import sys, os
want = {}
for l in open(sys.argv[1]):
    c = l.rstrip('\n').split('\t')
    if len(c) >= 7 and c[1] != 'ERROR':
        t = os.path.basename(c[0]).replace('.ktest', '')
        want[t] = c[1] + ':' + c[2]
bad = 0; n = 0
for l in open(sys.argv[3]):
    c = l.rstrip('\n').split('\t')
    t = c[0].split('/')[-1]
    n += 1
    if len(c) < 3 or c[2] != want.get(t):
        bad += 1
        print('MISMATCH', l.rstrip())
print(f'replayed {n} case lines, {bad} not on the path KLEE recorded')
EOF
tail -1 "$R/replay-check.txt"

# 2. Lean model vs C++: every case at the version KLEE found it at (the path's version), and one
# case per exact path at every version
$PY reps "$R/cases.tsv" > "$R/klee-reps.tsv"
# at most CAP cases at their own versions (every k-th; the representatives of all paths run anyway)
n=$(wc -l < "$R/klee-cases.tsv"); k=$(( (n + ${CAP:-20000} - 1) / ${CAP:-20000} ))
awk -v k="$k" 'NR % k == 1 || k == 1' "$R/klee-cases.tsv" > "$R/klee-sample.tsv"
echo "differential: $(wc -l < "$R/klee-sample.tsv") of $n cases at their versions, $(wc -l < "$R/klee-reps.tsv") paths at every version"
for v in $VERSIONS; do
  awk -F'\t' -v v="$v" '$2 == v' "$R/klee-sample.tsv" > "$R/own-v$v.tsv"
  cat "$R/own-v$v.tsv" "$R/klee-reps.tsv" | sort -u > "$R/run-v$v.tsv"
  TVMLEAN_GLOBAL_VERSION=$v "$TESTS" --cases-file "$R/run-v$v.tsv" --jobs "$JOBS" > "$R/diff-v$v.txt" || true
  echo "v$v own=$(wc -l < "$R/own-v$v.tsv") $(tail -1 "$R/diff-v$v.txt")"
  rm -f "$R/own-v$v.tsv" "$R/run-v$v.tsv"
done

# 3. the existing suites' paths
"$B/replay" ranges "$SPEC" > "$R/ranges.txt"
$PY suites "$R/ranges.txt" "$ROOT/docs/progress/tvm_spec_index.json" > "$R/suites.txt"
"$TESTS" --dump-cases "$(cat "$R/suites.txt")" > "$R/existing.tsv" 2> "$R/existing.err"
$PY versions "$R/existing.tsv" > "$R/existing-v.tsv"
split -n l/"$JOBS" "$R/existing-v.tsv" "$R/ex.part."
ls "$R"/ex.part.* | xargs -P "$JOBS" -I{} sh -c "$B/replay cases $SPEC {} > {}.out" || true
cat "$R"/ex.part.*.out > "$R/existing-sigs.tsv"; rm -f "$R"/ex.part.* "$R/existing-v.tsv"
echo "suites $(tr ',' ' ' < "$R/suites.txt")"
echo "existing cases $(wc -l < "$R/existing.tsv") (not dumped: $(wc -l < "$R/existing.err"))"
$PY compare "$SPEC" "$R/cases.tsv" "$R/existing-sigs.tsv" "$R"
