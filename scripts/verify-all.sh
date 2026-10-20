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
# Runs: build; all unit tests; the opcode check (every suite runs its own opcode, --opcode-check);
# the full oracle and the fuzz category on global versions 13 and 16;
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
( $T --unit-only --no-progress > "$OUT/unit.log" 2>&1; echo "unit: $(tail -1 "$OUT/unit.log")" >> "$SUM" ) &
( $T --opcode-check > "$OUT/opcode-check.log" 2>&1; echo "$(tail -1 "$OUT/opcode-check.log")" >> "$SUM" ) &
for gv in 13 16; do
  ( TVMLEAN_GLOBAL_VERSION=$gv $T --oracle-only --no-progress > "$OUT/oracle-v$gv.log" 2>&1
    echo "oracle v$gv: $(tail -n 1 "$OUT/oracle-v$gv.log")" >> "$SUM" ) &
  ( TVMLEAN_GLOBAL_VERSION=$gv $T --fuzz-only --no-progress > "$OUT/fuzz-v$gv.log" 2>&1
    echo "fuzz v$gv: $(tail -n 1 "$OUT/fuzz-v$gv.log")" >> "$SUM" ) &
done
if [ -n "${FIXTURES:-}" ]; then
  for d in "$FIXTURES"/*/; do n=$(basename "$d")
    ( $DT --dir "$d" --strict-exit --out "$OUT/diff-$n.json" > "$OUT/diff-$n.log" 2>&1
      echo "diff $n: $(tail -1 "$OUT/diff-$n.log")" >> "$SUM" ) &
  done
fi
wait
cat "$SUM"
