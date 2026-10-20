#!/usr/bin/env bash
# Full conformance run of the model against the C++ TVM.
#   TON_FIFT_BIN  path to the fift binary with runvmx (C++ reference)   [required]
#   TON_FIFT_LIB  path to the fift library directory                    [required]
#   FIXTURES      directory with diff-test fixture sets (subdirectories) [optional]
#   OUT           directory for logs                                    [default: ./verify-out]
#   TVMLEAN_TON_BUILD, TVMLEAN_TON_SRC  the C++ reference build (cmake build dir, not a coverage
#                 build) and its sources: on Linux the native crypto links the same blst as C++
#                 (see lakefile.lean). Without them BLS12-381 is a stub and its oracle cases fail.
#                                                                                   [needed on Linux]
#   TVMLEAN_EMULATOR_LIB  libemulator.so of the C++ reference (the transaction oracle)
#                 [default: $TVMLEAN_TON_BUILD/emulator/libemulator.so; cmake target `emulator`]
#   TX_FUZZ       random transactions of the transaction fuzz          [default: 3000]
#   VERSIONS      global versions of the full oracle and the fuzz      [default: 0 .. 16]
#   PAR           jobs run at once                                     [default: 12]
# Runs: build; all unit tests; the opcode check (every suite runs its own opcode, --opcode-check);
# the full oracle and the fuzz category on every global version of VERSIONS; whole transactions
# against the TON transaction emulator (tvm-lean-tx-test: the cases on every version, and fuzz);
# diff fixtures. (The fuzz category, ~400k randomized cases per version, takes about 10 minutes.)
# Exit status: 0 only if the build and every job succeed (each job's status is in the summary);
# a failed build stops the run.
set -u
: "${TON_FIFT_BIN:?}" "${TON_FIFT_LIB:?}"
OUT=${OUT:-./verify-out}; mkdir -p "$OUT"; SUM="$OUT/summary.txt"; : > "$SUM"
export TON_FIFT_BIN TON_FIFT_LIB
S=$(date +%s)
echo "native crypto: ${TVMLEAN_TON_BUILD:-stub (TVMLEAN_TON_BUILD not set)}" >> "$SUM"
lake build TvmLeanProofs tvm-lean-tests tvm-lean-diff-test tvm-lean-tx-test > "$OUT/build.log" 2>&1
B=$?
echo "build exit=$B sec=$(( $(date +%s)-S ))" >> "$SUM"
if [ "$B" -ne 0 ]; then echo "verify: FAILED (build)" >> "$SUM"; cat "$SUM"; exit 1; fi
T=.lake/build/bin/tvm-lean-tests; DT=.lake/build/bin/tvm-lean-diff-test; TX=.lake/build/bin/tvm-lean-tx-test
export TVMLEAN_EMULATOR_LIB=${TVMLEAN_EMULATOR_LIB:-${TVMLEAN_TON_BUILD:-}/emulator/libemulator.so}
VERSIONS=${VERSIONS:-$(seq -s ' ' 0 16)}; PAR=${PAR:-12}
FAILED="$OUT/failed"; rm -rf "$FAILED"; mkdir -p "$FAILED"
# start a job in the background once fewer than PAR are running
bg() { while [ "$(jobs -rp | wc -l)" -ge "$PAR" ]; do wait -n; done; "$@" & }
# job NAME LOG CMD...: runs CMD into LOG, adds the last line of LOG and the exit status to the
# summary, and marks NAME failed for a nonzero status
job() { n=$1; log=$2; shift 2; "$@" > "$log" 2>&1; rc=$?
  echo "$n: $(tail -n 1 "$log") exit=$rc" >> "$SUM"; [ "$rc" -eq 0 ] || : > "$FAILED/$n"; }
unit() { job unit "$OUT/unit.log" $T --unit-only --no-progress; }
opcheck() { job opcode-check "$OUT/opcode-check.log" $T --opcode-check; }
oracle() { job "oracle v$1" "$OUT/oracle-v$1.log" env TVMLEAN_GLOBAL_VERSION="$1" $T --oracle-only --no-progress; }
fuzz() { job "fuzz v$1" "$OUT/fuzz-v$1.log" env TVMLEAN_GLOBAL_VERSION="$1" $T --fuzz-only --no-progress; }
diffset() { job "diff $2" "$OUT/diff-$2.log" $DT --dir "$1" --strict-exit --out "$OUT/diff-$2.json"; }
tx() { job tx "$OUT/tx.log" $TX --versions "$(echo $VERSIONS | tr ' ' ',')"; }
txfuzz() { job "tx fuzz" "$OUT/tx-fuzz.log" $TX --fuzz "${TX_FUZZ:-3000}"; }
bg unit; bg opcheck; bg tx; bg txfuzz
for gv in $VERSIONS; do bg oracle "$gv"; bg fuzz "$gv"; done
if [ -n "${FIXTURES:-}" ]; then
  for d in "$FIXTURES"/*/; do bg diffset "$d" "$(basename "$d")"; done
fi
wait
if [ -n "$(ls -A "$FAILED")" ]; then
  echo "verify: FAILED ($(ls "$FAILED" | tr '\n' ',' | sed 's/,$//'))" >> "$SUM"; cat "$SUM"; exit 1
fi
echo "verify: OK" >> "$SUM"
cat "$SUM"
