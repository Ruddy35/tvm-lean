#!/usr/bin/env bash
# Line and branch coverage of the C++ VM (crypto/vm) accumulated by runs of the coverage fift.
#   WS, TON_SRC, BUILD as in build-cpp-coverage.sh;  OUT = report directory.
#   SCOPE  exec (default): the code run when the VM executes a contract — crypto/vm without the
#          cell databases (db/), BOC serialization (boc*, large-boc-serializer), Merkle proofs and
#          updates, and fift's own memo/atom; all: the whole of crypto/vm.
# Reset counters before a measured run:  find "$BUILD" -name '*.gcda' -delete
# A full run (oracle and fuzz) executes the hottest lines billions of times; gcovr takes such
# counts for the old gcov bug 68080 ("suspicious hits") unless told to only warn.
set -eu
WS=${WS:-$HOME/ws}; TON_SRC=${TON_SRC:-$WS/ton-src}; BUILD=${BUILD:-$WS/ton-build-cov}
OUT=${OUT:-./cpp-coverage}; SCOPE=${SCOPE:-exec}; mkdir -p "$OUT"
G=$WS/tools/venv/bin/gcovr
EXCL=()
if [ "$SCOPE" = exec ]; then
  for p in 'db/' 'boc[^/]*' 'large-boc-serializer[^/]*' 'cells/Merkle[^/]*' 'memo[^/]*' 'atom[^/]*'; do
    EXCL+=(--exclude "$TON_SRC/crypto/vm/$p")
  done
fi
"$G" -r "$TON_SRC" --object-directory "$BUILD" --filter "$TON_SRC/crypto/vm/" "${EXCL[@]}" \
  --exclude-unreachable-branches --exclude-throw-branches \
  --gcov-ignore-parse-errors suspicious_hits.warn_once_per_file \
  --txt "$OUT/summary.txt" --txt-metric branch --json-summary-pretty --json-summary "$OUT/summary.json" \
  --json "$OUT/coverage.json" --html-details "$OUT/index.html" -j "$(nproc)"
cat "$OUT/summary.txt"
