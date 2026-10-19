#!/usr/bin/env bash
# Instruction identity over all 2^24 values and both tails: for every value that C++ decodes, the
# C++ dump of the original code must equal the C++ dump of the model's re-encoding (encodeCp0Code)
# of the instruction the model decoded. This covers the arguments in the third byte of 24-bit
# opcodes, which run.sh (one value per 16-bit prefix) does not.
#   TON_FIFT_BIN, TON_FIFT_LIB as in scripts/verify-all.sh;  OUT = output directory;  J = parallel jobs.
set -eu
: "${TON_FIFT_BIN:?}" "${TON_FIFT_LIB:?}"; OUT=${OUT:-./audit-identity}; mkdir -p "$OUT"
HERE=$(cd "$(dirname "$0")" && pwd); ROOT=$(cd "$HERE/../../.." && pwd)
lake build tvm-lean-audit-decoder > "$OUT/build.log" 2>&1
BIN=$ROOT/.lake/build/bin/tvm-lean-audit-decoder
J=${J:-$(nproc)}; N=$((1 << 24)); STEP=$(( (N + J - 1) / J ))
for tail in tail0 tail1; do
  for i in $(seq 0 $((J - 1))); do
    lo=$((i * STEP)); hi=$(( lo + STEP < N ? lo + STEP : N ))
    ( "$TON_FIFT_BIN" -I "$TON_FIFT_LIB" -s "$HERE/cpp.fif" nameall $tail $lo $hi > "$OUT/cpp-name-$tail-$i.txt"
      { cat "$HERE/reasm_head.fif"; "$BIN" reasmall $tail $lo $hi; } > "$OUT/reasm-$tail-$i.fif"
      "$TON_FIFT_BIN" -I "$TON_FIFT_LIB" "$OUT/reasm-$tail-$i.fif" > "$OUT/cpp-reasm-$tail-$i.txt"
      rm -f "$OUT/reasm-$tail-$i.fif" ) &
  done
  wait
done
python3 "$HERE/compare_identity.py" "$OUT" "$J" > "$OUT/summary.md"
cat "$OUT/summary.md"
