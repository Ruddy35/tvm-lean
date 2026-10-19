#!/usr/bin/env bash
# Measured coverage run: the oracle and fuzz categories on global versions 13 and 16 against the
# coverage fift (build-cpp-coverage.sh), then the report (cpp-coverage-report.sh). Unit tests and
# diff fixtures do not run C++ and are not part of it. The test binary must be built
# (verify-all.sh or `lake build tvm-lean-tests` with TVMLEAN_TON_BUILD/TVMLEAN_TON_SRC).
#   WS, TON_SRC, BUILD as in build-cpp-coverage.sh;  TON_FIFT_LIB as in verify-all.sh;
#   OUT    directory for logs and the report                               [default: ./cpp-coverage]
#   SUITES optional: only these suites (exact names, space-separated)
set -u
WS=${WS:-$HOME/ws}; BUILD=${BUILD:-$WS/ton-build-cov}
: "${TON_FIFT_LIB:?}"
OUT=${OUT:-./cpp-coverage}; mkdir -p "$OUT"; SUM="$OUT/run.txt"; : > "$SUM"
export TON_FIFT_BIN=$BUILD/crypto/fift TON_FIFT_LIB
find "$BUILD" -name '*.gcda' -delete
T=.lake/build/bin/tvm-lean-tests
run() { # category version
  if [ -z "${SUITES:-}" ]; then
    TVMLEAN_GLOBAL_VERSION=$2 $T --$1-only --no-progress > "$OUT/$1-v$2.log" 2>&1
  else
    for s in $SUITES; do TVMLEAN_GLOBAL_VERSION=$2 $T --$1-only --no-progress --filter "$s"; done \
      > "$OUT/$1-v$2.log" 2>&1
  fi
  echo "$1 v$2: $(awk '/^suites=/ { for (i = 1; i <= NF; i++) { split($i, a, "="); s[a[1]] += a[2] } }
    END { printf "suites=%d oracle=%d fuzz=%d failures=%d", s["suites"], s["oracle"], s["fuzz"], s["failures"] }' \
    "$OUT/$1-v$2.log")" >> "$SUM"
}
for gv in 13 16; do run oracle $gv & run fuzz $gv & done
wait
cat "$SUM"
OUT=$OUT/report "$(dirname "$0")/cpp-coverage-report.sh"
