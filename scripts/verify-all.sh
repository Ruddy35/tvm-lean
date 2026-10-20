#!/usr/bin/env bash
# Full conformance run of the model against the C++ TVM.
#   TON_FIFT_BIN  path to the fift binary with runvmx (C++ reference)   [required]
#   TON_FIFT_LIB  path to the fift library directory                    [required]
#   FIXTURES      directory with diff-test fixture sets (subdirectories) [optional]
#   OUT           directory for logs                                    [default: ./verify-out]
#   TVMLEAN_TON_BUILD, TVMLEAN_TON_SRC  the C++ reference build (cmake build dir, not a coverage
#                 build) and its sources: on Linux the native crypto links the same libsodium,
#                 OpenSSL, secp256k1 and blst as C++ (see lakefile.lean). Without them the curve and
#                 pairing operations are stubs and their oracle cases fail.          [needed on Linux]
#   VERSIONS      global versions of the full oracle and the fuzz      [default: 0 .. 16]
#   PAR           jobs run at once                                     [default: 12]
# Runs: build; all unit tests; the opcode check (every suite runs its own opcode, --opcode-check);
# the full oracle and the fuzz category on every global version of VERSIONS;
# diff fixtures. (The fuzz category, ~400k randomized cases per version, takes about 10 minutes.)
set -u
: "${TON_FIFT_BIN:?}" "${TON_FIFT_LIB:?}"
OUT=${OUT:-./verify-out}; mkdir -p "$OUT"; SUM="$OUT/summary.txt"; : > "$SUM"
export TON_FIFT_BIN TON_FIFT_LIB
S=$(date +%s)
echo "native crypto: ${TVMLEAN_TON_BUILD:-stub (TVMLEAN_TON_BUILD not set)}" >> "$SUM"
lake build TvmLeanProofs tvm-lean-tests tvm-lean-diff-test > "$OUT/build.log" 2>&1
echo "build exit=$? sec=$(( $(date +%s)-S ))" >> "$SUM"
T=.lake/build/bin/tvm-lean-tests; DT=.lake/build/bin/tvm-lean-diff-test
VERSIONS=${VERSIONS:-$(seq -s ' ' 0 16)}; PAR=${PAR:-12}
# start a job in the background once fewer than PAR are running
bg() { while [ "$(jobs -rp | wc -l)" -ge "$PAR" ]; do wait -n; done; "$@" & }
unit() { $T --unit-only --no-progress > "$OUT/unit.log" 2>&1; echo "unit: $(tail -1 "$OUT/unit.log")" >> "$SUM"; }
opcheck() { $T --opcode-check > "$OUT/opcode-check.log" 2>&1; echo "$(tail -1 "$OUT/opcode-check.log")" >> "$SUM"; }
oracle() { TVMLEAN_GLOBAL_VERSION=$1 $T --oracle-only --no-progress > "$OUT/oracle-v$1.log" 2>&1
  echo "oracle v$1: $(tail -n 1 "$OUT/oracle-v$1.log")" >> "$SUM"; }
fuzz() { TVMLEAN_GLOBAL_VERSION=$1 $T --fuzz-only --no-progress > "$OUT/fuzz-v$1.log" 2>&1
  echo "fuzz v$1: $(tail -n 1 "$OUT/fuzz-v$1.log")" >> "$SUM"; }
diffset() { $DT --dir "$1" --strict-exit --out "$OUT/diff-$2.json" > "$OUT/diff-$2.log" 2>&1
  echo "diff $2: $(tail -1 "$OUT/diff-$2.log")" >> "$SUM"; }
bg unit; bg opcheck
for gv in $VERSIONS; do bg oracle "$gv"; bg fuzz "$gv"; done
if [ -n "${FIXTURES:-}" ]; then
  for d in "$FIXTURES"/*/; do bg diffset "$d" "$(basename "$d")"; done
fi
wait
cat "$SUM"
