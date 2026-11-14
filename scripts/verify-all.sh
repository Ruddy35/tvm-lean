#!/usr/bin/env bash
# Full conformance run of the model against the C++ TVM.
#   TON_FIFT_BIN  path to the fift binary with runvmx (C++ reference)   [required]
#   TON_FIFT_LIB  path to the fift library directory                    [required]
#   FIXTURES      directory with diff-test fixture sets (subdirectories) [optional]
#   OUT           directory for logs                                    [default: ./verify-out]
#   TVMLEAN_TON_BUILD  the C++ reference build (cmake build dir, not a coverage build), used only
#                 to find emulator/libemulator.so for the transaction oracle (TVMLEAN_EMULATOR_LIB)
#   TVMLEAN_EMULATOR_LIB  libemulator.so of the C++ reference (the transaction oracle)
#                 [default: $TVMLEAN_TON_BUILD/emulator/libemulator.so; cmake target `emulator`]
#   TX_FUZZ       random transactions of the transaction fuzz          [default: 3000]
#   VERSIONS      global versions of the full oracle and the fuzz      [default: 0 .. 16]
#   PAR           jobs run at once                                     [default: nproc]
#   SHARDS        processes the oracle run and the fuzz run of a version are each split into
#                 (`--shard k/SHARDS`, one worker each)                [default: 16]
# Runs: build; all unit tests; the opcode check (every suite runs its own opcode, --opcode-check);
# the full oracle and the fuzz category on every global version of VERSIONS; whole transactions
# against the TON transaction emulator (tvm-lean-tx-test: the cases on every version, and fuzz);
# diff fixtures. (The fuzz category, ~400k randomized cases per version, takes about 10 minutes.)
# The oracle and the fuzz run in processes of one worker, SHARDS per version and category, each a
# job of its own; a version's shards add up to one summary line, the line one process running all
# the suites prints. Every case forks a `fift`: the fork of the test process (~250 MB) is serialized
# within the process and costs it more system time the more threads it runs, so the parallelism is
# in processes.
# Exit status: 0 only if the build and every job succeed (each job's status is in the summary);
# a failed build stops the run.
set -u
: "${TON_FIFT_BIN:?}" "${TON_FIFT_LIB:?}"
OUT=${OUT:-./verify-out}; mkdir -p "$OUT"; SUM="$OUT/summary.txt"; : > "$SUM"
export TON_FIFT_BIN TON_FIFT_LIB
S=$(date +%s)
lake build TvmLeanProofs tvm-lean-tests tvm-lean-diff-test tvm-lean-tx-test > "$OUT/build.log" 2>&1
B=$?
echo "build exit=$B sec=$(( $(date +%s)-S ))" >> "$SUM"
if [ "$B" -ne 0 ]; then echo "verify: FAILED (build)" >> "$SUM"; cat "$SUM"; exit 1; fi
T=.lake/build/bin/tvm-lean-tests; DT=.lake/build/bin/tvm-lean-diff-test; TX=.lake/build/bin/tvm-lean-tx-test
export TVMLEAN_EMULATOR_LIB=${TVMLEAN_EMULATOR_LIB:-${TVMLEAN_TON_BUILD:-}/emulator/libemulator.so}
VERSIONS=${VERSIONS:-$(seq -s ' ' 0 16)}; PAR=${PAR:-$(nproc)}; SHARDS=${SHARDS:-16}
FAILED="$OUT/failed"; rm -rf "$FAILED"; mkdir -p "$FAILED"
PARTS="$OUT/parts"; rm -rf "$PARTS"; mkdir -p "$PARTS"
# start a job in the background once fewer than PAR are running
bg() { while [ "$(jobs -rp | wc -l)" -ge "$PAR" ]; do wait -n; done; "$@" & }
# job NAME LOG CMD...: runs CMD into LOG, adds its result lines (the `tx:` / `tx (…)` totals of the
# transaction runs, else the last line of LOG) and the exit status to the summary, and marks NAME
# failed for a nonzero status
job() { n=$1; log=$2; shift 2; "$@" > "$log" 2>&1; rc=$?
  r=$(grep -E '^tx( \(|:)' "$log" | paste -sd ';' -); [ -n "$r" ] || r=$(tail -n 1 "$log")
  echo "$n: $r exit=$rc" >> "$SUM"; [ "$rc" -eq 0 ] || : > "$FAILED/$n"; }
unit() { job unit "$OUT/unit.log" $T --unit-only --no-progress; }
opcheck() { job opcode-check "$OUT/opcode-check.log" $T --opcode-check; }
# part KIND V K: shard K of the KIND (oracle or fuzz) run at version V, one worker; its log and exit
# status go to $PARTS
part() { env TVMLEAN_GLOBAL_VERSION="$2" $T --"$1"-only --no-progress --jobs 1 --shard "$3/$SHARDS" \
    > "$PARTS/$1-v$2.$3.log" 2>&1; echo $? > "$PARTS/$1-v$2.$3.rc"; }
# merge KIND V: the KIND run at version V from its shards, recorded as `job` records one process: the
# shards' logs in order and then the summary line of their counts summed make its log; its exit
# status is the largest of theirs (1 if a shard has none or its log does not end with a summary line)
merge() { local n="$1 v$2" log="$OUT/$1-v$2.log" rc=0 k p r s; : > "$log"
  for k in $(seq 0 $((SHARDS - 1))); do
    p="$PARTS/$1-v$2.$k"; cat "$p.log" >> "$log" 2>/dev/null
    r=$(cat "$p.rc" 2>/dev/null); [ -n "$r" ] || r=1; [ "$r" -gt "$rc" ] && rc=$r
    tail -n 1 "$p.log" 2>/dev/null | grep -qE '^suites=[0-9]+ unit=[0-9]+ oracle=[0-9]+ fuzz=[0-9]+ failures=[0-9]+$' \
      || { [ "$rc" -gt 0 ] || rc=1; }
  done
  s=$(for k in $(seq 0 $((SHARDS - 1))); do tail -n 1 "$PARTS/$1-v$2.$k.log" 2>/dev/null; done | awk '
    /^suites=/ { for (i = 1; i <= NF; i++) { split($i, a, "="); t[a[1]] += a[2] } }
    END { printf "suites=%d unit=%d oracle=%d fuzz=%d failures=%d", t["suites"], t["unit"], t["oracle"], t["fuzz"], t["failures"] }')
  echo "$s" >> "$log"
  echo "$n: $s exit=$rc" >> "$SUM"; [ "$rc" -eq 0 ] || : > "$FAILED/$n"; }
diffset() { job "diff $2" "$OUT/diff-$2.log" $DT --dir "$1" --strict-exit --out "$OUT/diff-$2.json"; }
tx() { job "tx v$1" "$OUT/tx-v$1.log" $TX --versions "$1"; }
txfuzz() { job "tx fuzz" "$OUT/tx-fuzz.log" $TX --fuzz "${TX_FUZZ:-3000}"; }
# the transaction cases first, one job per version: the longest jobs; then the shards of the fuzz,
# longer than those of the oracle
bg unit; bg opcheck; bg txfuzz
for gv in $VERSIONS; do bg tx "$gv"; done
for kind in fuzz oracle; do
  for gv in $VERSIONS; do for k in $(seq 0 $((SHARDS - 1))); do bg part "$kind" "$gv" "$k"; done; done
done
if [ -n "${FIXTURES:-}" ]; then
  for d in "$FIXTURES"/*/; do bg diffset "$d" "$(basename "$d")"; done
fi
wait
for gv in $VERSIONS; do merge oracle "$gv"; merge fuzz "$gv"; done
if [ -n "$(ls -A "$FAILED")" ]; then
  echo "verify: FAILED ($(ls "$FAILED" | tr '\n' ',' | sed 's/,$//'))" >> "$SUM"; cat "$SUM"; exit 1
fi
echo "verify: OK" >> "$SUM"
cat "$SUM"
