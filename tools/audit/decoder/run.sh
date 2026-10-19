#!/usr/bin/env bash
# Exhaustive decoder comparison, model vs C++, over all 24-bit values and two tails.
#   TON_FIFT_BIN, TON_FIFT_LIB as in scripts/verify-all.sh;  OUT = output directory.
set -eu
: "${TON_FIFT_BIN:?}" "${TON_FIFT_LIB:?}"; OUT=${OUT:-./audit-decoder}; mkdir -p "$OUT"
HERE=$(cd "$(dirname "$0")" && pwd); ROOT=$(cd "$HERE/../../.." && pwd)
lake build tvm-lean-audit-decoder > "$OUT/build.log" 2>&1
BIN=$ROOT/.lake/build/bin/tvm-lean-audit-decoder
J=$(nproc); N=$((1 << 24)); STEP=$(( (N + J - 1) / J ))
for tail in tail0 tail1; do
  for i in $(seq 0 $((J - 1))); do
    lo=$((i * STEP)); hi=$(( lo + STEP < N ? lo + STEP : N ))
    "$TON_FIFT_BIN" -I "$TON_FIFT_LIB" -s "$HERE/cpp.fif" len $tail $lo $hi > "$OUT/cpp-len-$tail-$i.txt" &
    "$BIN" len $tail $lo $hi > "$OUT/lean-len-$tail-$i.txt" &
  done
  wait
  "$TON_FIFT_BIN" -I "$TON_FIFT_LIB" -s "$HERE/cpp.fif" name $tail 0 $N > "$OUT/cpp-name-$tail.txt" &
  "$BIN" name $tail 0 $N > "$OUT/lean-name-$tail.txt" &
  wait
done
python3 "$HERE/compare.py" "$OUT" $J > "$OUT/summary.md"
cat "$OUT/summary.md"
