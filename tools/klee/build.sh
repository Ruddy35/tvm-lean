#!/usr/bin/env bash
# Build the C++ TVM of the reference (ton @ 3d478cb, from tools/klee/setup.sh) into one LLVM
# bitcode module with the KLEE harness, and the same module as a native replay binary.
#
#   tools/klee/build.sh            -> $OUT/harness.bc (KLEE) and $OUT/replay (native)
#   KW [default: ~/ws/klee]  OUT [default: $KW/build]  JOBS [default: nproc]
#
# What is compiled: the VM (crypto/vm: dispatch, opcode tables, every op family but tonops),
# cells/slices/builders, dictionaries, BOC, the bigint (crypto/common) and the parts of tdutils
# they use. All against the bitcode libc++ that KLEE links (--libcxx), single-threaded: the few
# std::mutex/std::thread uses of TON compile against tools/klee/harness/compat. Left out and
# stubbed (harness/stubs.cpp): crypto (SHA-256 of cells is a per-run counter, signatures, curves,
# BLS), tonops (register_ton_ops registers nothing: no TON-specific opcodes in the table),
# libsodium. The one source change: VmState::step() calls tvm_klee_step_hook() first, so the
# harness can tell where the instruction under test starts (path signatures, see harness.cpp).
#
# Every basic block of the TON code calls tvm_cov(<block id>) (cov_instrument.py): the hash of
# the block sequence while the instruction under test runs is its C++ path signature, the same in
# KLEE and in the native replay.
set -euo pipefail
KW=${KW:-$HOME/ws/klee}; JOBS=${JOBS:-$(nproc)}
HERE=$(cd "$(dirname "$0")" && pwd)
ENV=$KW/env; TON=$KW/ton; OUT=${OUT:-$KW/build}
LCXX=$KW/libcxx-install
export PATH=$ENV/bin:$PATH
CXX=$ENV/bin/clang++
mkdir -p "$OUT/bc" "$OUT/src/crypto/vm"

# vm.cpp with the step hooks: a step starts (VmState::step); it ends after the gas check that
# follows it in run_inner, or where run_inner/run catch what it threw (VmError, VmNoGas)
sed -e 's|^int VmState::step() {$|int VmState::step() {\n  tvm_klee_step_hook(code.not_null() ? code.get() : nullptr);|' \
    -e 's|^namespace vm {$|extern "C" void tvm_klee_step_hook(const vm::CellSlice* code);\nextern "C" void tvm_klee_step_end();\nnamespace vm {|' \
    -e 's|^        gas.check();$|        gas.check();\n        tvm_klee_step_end();|' \
    -e 's|^    } catch (const VmError\& vme) {$|    } catch (const VmError\& vme) {\n      tvm_klee_step_end();|' \
    -e 's|^    } catch (VmNoGas\& vmoog) {$|    } catch (VmNoGas\& vmoog) {\n      tvm_klee_step_end();|' \
    "$TON/crypto/vm/vm.cpp" > "$OUT/src/crypto/vm/vm.cpp"
[ "$(grep -c '^ *tvm_klee_step_end();$' "$OUT/src/crypto/vm/vm.cpp")" = 3 ] &&
  grep -q 'tvm_klee_step_hook(code' "$OUT/src/crypto/vm/vm.cpp" || { echo "vm.cpp: step hooks not inserted" >&2; exit 1; }
# cp0.cpp without tonops.h (it pulls in the block library and its generated TL-B code)
sed -e 's|^#include "tonops.h"$|namespace vm { void register_ton_ops(OpcodeTable\& cp0); }|' \
    "$TON/crypto/vm/cp0.cpp" > "$OUT/src/crypto/vm/cp0.cpp"
grep -q 'void register_ton_ops' "$OUT/src/crypto/vm/cp0.cpp" || { echo "cp0.cpp: not patched" >&2; exit 1; }

TON_SRCS=(
  crypto/common/bigint.cpp crypto/common/refcnt.cpp crypto/common/refint.cpp crypto/common/bigexp.cpp
  crypto/common/bitstring.cpp crypto/common/util.cpp
  crypto/vm/boc.cpp crypto/vm/dict.cpp
  crypto/vm/cells/Cell.cpp crypto/vm/cells/CellBuilder.cpp crypto/vm/cells/CellHash.cpp
  crypto/vm/cells/CellSlice.cpp crypto/vm/cells/CellString.cpp crypto/vm/cells/CellTraits.cpp
  crypto/vm/cells/CellUsageTree.cpp crypto/vm/cells/DataCell.cpp crypto/vm/cells/LevelMask.cpp
  crypto/vm/cells/MerkleProof.cpp crypto/vm/cells/MerkleUpdate.cpp
  crypto/vm/stack.cpp crypto/vm/atom.cpp crypto/vm/continuation.cpp crypto/vm/memo.cpp
  crypto/vm/dispatch.cpp crypto/vm/opctable.cpp crypto/vm/stackops.cpp
  crypto/vm/tupleops.cpp crypto/vm/arithops.cpp crypto/vm/cellops.cpp crypto/vm/contops.cpp
  crypto/vm/dictops.cpp crypto/vm/debugops.cpp crypto/vm/utils.cpp
  @crypto/vm/vm.cpp @crypto/vm/cp0.cpp
  tdutils/td/utils/check.cpp tdutils/td/utils/logging.cpp tdutils/td/utils/misc.cpp
  tdutils/td/utils/Slice.cpp tdutils/td/utils/Status.cpp tdutils/td/utils/StringBuilder.cpp
  tdutils/td/utils/buffer.cpp tdutils/td/utils/base64.cpp tdutils/td/utils/crypto.cpp
  tdutils/td/utils/StackAllocator.cpp tdutils/td/utils/SharedSlice.cpp tdutils/td/utils/utf8.cpp
  tdutils/td/utils/unicode.cpp tdutils/td/utils/Time.cpp tdutils/td/utils/port/Clocks.cpp
  tdutils/td/utils/port/StdStreams.cpp tdutils/td/utils/port/thread_local.cpp
  tdutils/td/utils/port/stacktrace.cpp tdutils/td/utils/port/detail/NativeFd.cpp
  tdutils/td/utils/port/detail/ThreadIdGuard.cpp tdutils/td/utils/FileLog.cpp
  tdutils/td/utils/port/FileFd.cpp tdutils/td/utils/port/Stat.cpp tdutils/td/utils/port/path.cpp
  tdutils/td/utils/port/PollFlags.cpp tdutils/td/utils/filesystem.cpp tdutils/td/utils/PathView.cpp
  tdutils/td/utils/Timer.cpp tdutils/td/utils/Random.cpp tdutils/td/utils/port/sleep.cpp
  tdutils/td/utils/port/signals.cpp
)

CXXFLAGS=(
  -std=c++20 -O1 -fno-vectorize -fno-slp-vectorize -g0 -DNDEBUG -U_FORTIFY_SOURCE -D_FORTIFY_SOURCE=0
  -fno-stack-protector -w
  -nostdinc++ -I"$HERE/harness/compat" -isystem "$LCXX/include/c++/v1"
  -I"$HERE/harness/td-config" -I"$TON" -I"$TON/crypto" -I"$TON/crypto/vm" -I"$TON/tdutils"
  -I"$TON/tdactor" -I"$TON/tddb" -I"$TON/common"
)
printf '%s\n' "${CXXFLAGS[@]}" > "$OUT/cxxflags.txt"

compile() {  # <src> -> $OUT/bc/<flat name>.bc
  local s=$1 f
  if [[ $s == @* ]]; then s=${s#@}; f=$OUT/src/$s; else f=$TON/$s; fi
  local o=$OUT/bc/$(echo "$s" | tr / _).bc
  if [ ! -f "$o" ] || [ "$f" -nt "$o" ] || [ "$OUT/cxxflags.txt" -nt "$o" ]; then
    "$CXX" "${CXXFLAGS[@]}" -emit-llvm -c "$f" -o "$o" 2> "$o.err" || { echo "FAILED $s"; head -30 "$o.err"; return 1; }
  fi
}
export -f compile; export CXX OUT TON
export CXXFLAGS_STR
fails=0
pids=()
for s in "${TON_SRCS[@]}"; do
  while [ "$(jobs -rp | wc -l)" -ge "$JOBS" ]; do sleep 0.2; done
  compile "$s" &
done
for p in $(jobs -rp); do wait "$p" || fails=$((fails + 1)); done
wait || true
for s in "${TON_SRCS[@]}"; do
  s=${s#@}; [ -f "$OUT/bc/$(echo "$s" | tr / _).bc" ] || { echo "missing bitcode: $s"; fails=$((fails + 1)); }
done
[ "$fails" -eq 0 ] || { echo "$fails TON sources failed"; exit 1; }

# TON module, block-instrumented
llvm-link "$OUT"/bc/*.bc -o "$OUT/ton.bc"
llvm-dis "$OUT/ton.bc" -o "$OUT/ton.ll"
python3 "$HERE/cov_instrument.py" "$OUT/ton.ll" "$OUT/ton-cov.ll" "$OUT/cov-blocks.txt"
llvm-as "$OUT/ton-cov.ll" -o "$OUT/ton-cov.bc"
rm -f "$OUT/ton.ll" "$OUT/ton-cov.ll"

# harness and stubs (KLEE flavour and native flavour)
for flavour in klee native; do
  def=-DTVM_KLEE_NATIVE; [ $flavour = klee ] && def=-DTVM_KLEE_SYMBOLIC
  "$CXX" "${CXXFLAGS[@]}" $def -emit-llvm -c "$HERE/harness/harness.cpp" -o "$OUT/harness-$flavour.bc"
done
"$CXX" "${CXXFLAGS[@]}" -emit-llvm -c "$HERE/harness/stubs.cpp" -o "$OUT/stubs.bc"
llvm-link "$OUT/ton-cov.bc" "$OUT/stubs.bc" "$OUT/harness-klee.bc" -o "$OUT/pre-klee.bc"

# symbols nothing defines: libc (uclibc for KLEE, glibc natively), libc++ and KLEE intrinsics
# provide most; the rest get aborting definitions (gen_stubs.py), so a call is loud, not silent.
llvm-nm --defined-only "$LCXX/lib/libc++.bca" "$KW/klee-uclibc/lib/libc.a" "$KW"/klee-build/runtime/lib/*.bca 2>/dev/null \
  | awk 'NF>=3 {print $3}' | sort -u > "$OUT/provided.txt"
llvm-dis "$OUT/pre-klee.bc" -o - | python3 "$HERE/gen_stubs.py" "$OUT/provided.txt" > "$OUT/autostubs.c"
"$ENV/bin/clang" -O1 -g0 -w -emit-llvm -c "$OUT/autostubs.c" -o "$OUT/autostubs.bc"
llvm-link "$OUT/pre-klee.bc" "$OUT/autostubs.bc" -o "$OUT/harness.bc"
echo "auto stubs: $(grep -c '__asm__' "$OUT/autostubs.c")"

# native replay: the same instrumented TON module and stubs, the native harness flavour; what
# glibc does not provide gets aborting stubs too (the linker's list of undefined symbols)
llvm-link "$OUT/ton-cov.bc" "$OUT/stubs.bc" "$OUT/harness-native.bc" -o "$OUT/replay.bc"
native_link() {
  "$CXX" -O1 -g0 "$OUT/replay.bc" "$@" -o "$OUT/replay" -nostdlib++ -L"$LCXX/lib" -Wl,-rpath,"$LCXX/lib" -Wl,--no-demangle \
    -lc++ -lc++abi -lm
}
if ! native_link 2> "$OUT/link.err"; then
  python3 "$HERE/gen_stubs.py" --linker-errors "$OUT/link.err" > "$OUT/native-stubs.c"
  "$ENV/bin/clang" -O1 -g0 -w -c "$OUT/native-stubs.c" -o "$OUT/native-stubs.o"
  native_link "$OUT/native-stubs.o"
  echo "native stubs: $(grep -c '__asm__' "$OUT/native-stubs.c")"
fi
echo "built: $OUT/harness.bc $OUT/replay"
