#!/usr/bin/env bash
# Line and branch coverage of the C++ VM (crypto/vm) accumulated by runs of the coverage fift.
#   WS, TON_SRC, BUILD as in build-cpp-coverage.sh;  OUT = report directory.
# Reset counters before a measured run:  find "$BUILD" -name '*.gcda' -delete
set -eu
WS=${WS:-$HOME/ws}; TON_SRC=${TON_SRC:-$WS/ton-src}; BUILD=${BUILD:-$WS/ton-build-cov}
OUT=${OUT:-./cpp-coverage}; mkdir -p "$OUT"
G=$WS/tools/venv/bin/gcovr
"$G" -r "$TON_SRC" --object-directory "$BUILD" --filter "$TON_SRC/crypto/vm/" \
  --exclude-unreachable-branches --exclude-throw-branches \
  --txt "$OUT/summary.txt" --json-summary-pretty --json-summary "$OUT/summary.json" \
  --html-details "$OUT/index.html" -j "$(nproc)"
cat "$OUT/summary.txt"
