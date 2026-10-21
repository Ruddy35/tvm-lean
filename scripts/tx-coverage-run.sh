#!/usr/bin/env bash
# Measured coverage of the C++ transaction code (crypto/block/transaction.cpp) by the transaction
# oracle: the emulator (cmake target `emulator`) built in the coverage build of build-cpp-coverage.sh,
# tvm-lean-tx-test run against it on every version and with fuzz, then the report. The test binary
# must be built (`lake build tvm-lean-tx-test`).
#   WS, TON_SRC, BUILD as in build-cpp-coverage.sh (the coverage build must exist)
#   OUT   directory for logs and the report                                [default: ./tx-coverage]
#   PAR   parallel runs of tvm-lean-tx-test                                [default: nproc]
#   FUZZ  random cases                                                     [default: 3000]
# Report: OUT/summary.txt (branches of transaction.cpp), OUT/coverage.json for
#   python3 tools/coverage/uncovered.py --decisions OUT/coverage.json TON_SRC transaction.cpp
set -u
WS=${WS:-$HOME/ws}; TON_SRC=${TON_SRC:-$WS/ton-src}; BUILD=${BUILD:-$WS/ton-build-cov}
OUT=${OUT:-./tx-coverage}; PAR=${PAR:-$(nproc)}; FUZZ=${FUZZ:-3000}
mkdir -p "$OUT"; SUM="$OUT/run.txt"; : > "$SUM"
export PATH=$WS/tools/local/bin:$WS/tools/venv/bin:$PATH
# the emulator is a shared library: it links gcov's runtime only with --coverage among the shared
# linker flags (build-cpp-coverage.sh sets them; an older coverage build gets them here)
cmake -S "$TON_SRC" -B "$BUILD" -DCMAKE_SHARED_LINKER_FLAGS="--coverage" > "$OUT/build.log" 2>&1 &&
  ninja -C "$BUILD" -j"$(nproc)" emulator >> "$OUT/build.log" 2>&1 || { echo "build failed: $OUT/build.log"; exit 1; }
export TVMLEAN_EMULATOR_LIB=$BUILD/emulator/libemulator.so
find "$BUILD" -name '*.gcda' -delete
TX=.lake/build/bin/tvm-lean-tx-test
# each run accumulates into the same .gcda files; gcov's runtime merges them under a lock
run() { # name args...
  local n=$1; shift
  $TX "$@" > "$OUT/$n.log" 2>&1
  local rc=$?
  echo "$n: $(grep '^tx:' "$OUT/$n.log") exit=$rc" >> "$SUM"
}
active=0
for v in $(seq 0 16); do
  run "v$v" --versions "$v" &
  active=$((active + 1)); if [ "$active" -ge "$PAR" ]; then wait -n; active=$((active - 1)); fi
done
run fuzz --fuzz "$FUZZ" &
wait
cat "$SUM"
G=$WS/tools/venv/bin/gcovr
"$G" -r "$TON_SRC" --object-directory "$BUILD" --filter "$TON_SRC/crypto/block/transaction[.]cpp" \
  --exclude-unreachable-branches --exclude-throw-branches \
  --gcov-ignore-parse-errors suspicious_hits.warn_once_per_file \
  --txt "$OUT/summary.txt" --txt-metric branch --json-summary-pretty --json-summary "$OUT/summary.json" \
  --json "$OUT/coverage.json" --html-details "$OUT/index.html" -j "$(nproc)"
cat "$OUT/summary.txt"
