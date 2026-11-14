#!/usr/bin/env bash
# Build the C++ TVM of the reference (ton @ 3d478cb, from tools/klee/setup.sh) into one LLVM
# bitcode module with the KLEE harness, and the same module as a native replay binary.
#
#   tools/klee/build.sh            -> $OUT/harness.bc (KLEE) and $OUT/replay (native)
#   tools/klee/build.sh --native   -> $OUT/replay only, with the system clang/LLVM 18 and libstdc++
#                                     (no setup.sh needed: TON=<ton checkout at the commit>)
#   KW [default: ~/ws/klee]  OUT [default: $KW/build]  TON [default: $KW/ton]  JOBS [default: nproc]
#   TONOPS [default: 1]: with tonops.cpp (TON-specific opcodes); 0: without (register_ton_ops
#                        registers nothing, the families of tonops.cpp are not in the table)
#
# What is compiled: the VM (crypto/vm: dispatch, opcode tables, every op family), cells/slices/
# builders, dictionaries, BOC, the bigint (crypto/common), the parts of tdutils they use; with
# tonops: tonops.cpp, the TL-B code tlbc generates from crypto/block/block.tlb (tlbc is built here
# too), block-parse.cpp, mc-config.cpp, the hashers of HASHEXT (Hasher.cpp, keccak). All against the
# bitcode libc++ that KLEE links (--libcxx), single-threaded: the few std::mutex/std::thread uses of
# TON compile against tools/klee/harness/compat. Left out and stubbed: digests (harness/stubs.cpp:
# SHA-256 and the EVP digests of cells and HASHEXT are a per-run counter), the signature and curve
# libraries tonops calls (harness/tonops-stubs.cpp), libsodium, the TL-generated network API
# (compat/auto/tl: declarations only). The one source change: VmState::step() calls
# tvm_klee_step_hook() first, and the end of a step calls tvm_klee_step_end(), so the harness can
# tell where the instruction under test starts and ends (path signatures, see harness.cpp).
#
# Every basic block of the TON code calls tvm_cov(<block id>) or tvm_covf (cov_instrument.py): the
# block ids seen while the instruction under test runs give its C++ path signatures, the same in
# KLEE and in the native replay. The family table ($OUT/families.inc) is generated from
# docs/progress/tvm_spec_index.json by gen_families.py.
set -euo pipefail
KW=${KW:-$HOME/ws/klee}; JOBS=${JOBS:-$(nproc)}; TONOPS=${TONOPS:-1}
HERE=$(cd "$(dirname "$0")" && pwd); ROOT=$(cd "$HERE/../.." && pwd)
NATIVE=0; [ "${1:-}" = --native ] && NATIVE=1
ENV=$KW/env; TON=${TON:-$KW/ton}; OUT=${OUT:-$KW/build}
LCXX=$KW/libcxx-install
if [ $NATIVE = 1 ]; then
  export PATH=/usr/lib/llvm-18/bin:$PATH
  CXX=clang++; CXXFILT=llvm-cxxfilt
else
  export PATH=$ENV/bin:$PATH
  CXX=$ENV/bin/clang++; CXXFILT=$ENV/bin/llvm-cxxfilt
fi
mkdir -p "$OUT/bc" "$OUT/src/crypto/vm" "$OUT/src/gen/block" "$OUT/tlbc"
tonops_flag=; [ "$TONOPS" = 1 ] && tonops_flag=--tonops
python3 "$HERE/gen_families.py" "$ROOT/docs/progress/tvm_spec_index.json" "$OUT/families.inc" $tonops_flag

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
if [ "$TONOPS" = 1 ]; then
  cp "$TON/crypto/vm/cp0.cpp" "$OUT/src/crypto/vm/cp0.cpp.new"
else  # cp0.cpp without tonops.h (it pulls in the block library and its generated TL-B code)
  sed -e 's|^#include "tonops.h"$|namespace vm { void register_ton_ops(OpcodeTable\& cp0); }|' \
      "$TON/crypto/vm/cp0.cpp" > "$OUT/src/crypto/vm/cp0.cpp.new"
  grep -q 'void register_ton_ops' "$OUT/src/crypto/vm/cp0.cpp.new" || { echo "cp0.cpp: not patched" >&2; exit 1; }
fi
cmp -s "$OUT/src/crypto/vm/cp0.cpp.new" "$OUT/src/crypto/vm/cp0.cpp" || mv "$OUT/src/crypto/vm/cp0.cpp.new" "$OUT/src/crypto/vm/cp0.cpp"
rm -f "$OUT/src/crypto/vm/cp0.cpp.new"

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
TONOPS_SRCS=(
  crypto/vm/tonops.cpp crypto/block/block-parse.cpp crypto/block/mc-config.cpp crypto/vm/Hasher.cpp
  crypto/block/transaction.cpp crypto/keccak/keccak.cpp crypto/tl/tlblib.cpp @gen/block/block-auto.cpp
)

CXXFLAGS=(
  -std=c++20 -O1 -fno-vectorize -fno-slp-vectorize -g0 -DNDEBUG -U_FORTIFY_SOURCE -D_FORTIFY_SOURCE=0
  -fno-stack-protector -w
)
COMPAT=$HERE/harness/compat
if [ $NATIVE = 1 ]; then  # the system libstdc++ has threads: only the library stand-ins
  COMPAT=$OUT/compat-native; mkdir -p "$COMPAT"
  for x in openssl sodium.h crc32c auto; do ln -sfn "$HERE/harness/compat/$x" "$COMPAT/$x"; done
else
  CXXFLAGS+=(-nostdinc++ -isystem "$LCXX/include/c++/v1")
fi
CXXFLAGS+=(
  -I"$COMPAT" -I"$HERE/harness/td-config" -I"$TON" -I"$TON/crypto" -I"$TON/crypto/vm"
  -I"$TON/tdutils" -I"$TON/tdactor" -I"$TON/tddb" -I"$TON/common"
  -I"$OUT/src/gen" -I"$OUT/src/gen/block" -I"$TON/crypto/block" -I"$TON/tl"
)
printf '%s\n' "${CXXFLAGS[@]}" > "$OUT/cxxflags.txt"
# tonops.cpp and its stand-ins: tdutils with TD_HAVE_OPENSSL (crypto/Ed25519.h declares td::Ed25519
# only then); tlbc: with TD_HAVE_ZLIB (td::crc32, harness/tlbc-crc32.cpp)
swap_config() {  # CXXFLAGS with another td-config directory, one flag a line
  local x
  for x in "${CXXFLAGS[@]}"; do
    [ "$x" = "-I$HERE/harness/td-config" ] && x=-I$1
    printf '%s\n' "$x"
  done
}
mapfile -t CXXFLAGS_TONOPS < <(swap_config "$HERE/harness/td-config-tonops")
mkdir -p "$OUT/tlbc/cfg/td/utils"
sed 's/#define TD_HAVE_ZLIB 0/#define TD_HAVE_ZLIB 1/' "$HERE/harness/td-config/td/utils/config.h" > "$OUT/tlbc/cfg/td/utils/config.h"
mapfile -t CXXFLAGS_TLBC < <(swap_config "$OUT/tlbc/cfg")
CXXFLAGS_TLBC+=(-I"$TON/crypto/tl")

compile() {  # <src> -> $OUT/bc/<flat name>.bc
  local s=$1 f flags=("${CXXFLAGS[@]}")
  if [[ $s == @* ]]; then s=${s#@}; f=$OUT/src/$s; else f=$TON/$s; fi
  [[ $s == *tonops* ]] && flags=("${CXXFLAGS_TONOPS[@]}")
  local o=$OUT/bc/$(echo "$s" | tr / _).bc
  if [ ! -f "$o" ] || [ "$f" -nt "$o" ] || [ "$OUT/cxxflags.txt" -nt "$o" ]; then
    "$CXX" "${flags[@]}" -emit-llvm -c "$f" -o "$o" 2> "$o.err" || { echo "FAILED $s"; head -30 "$o.err"; return 1; }
  fi
}
compile_all() {
  local fails=0 s
  for s in "$@"; do
    while [ "$(jobs -rp | wc -l)" -ge "$JOBS" ]; do sleep 0.2; done
    compile "$s" &
  done
  for p in $(jobs -rp); do wait "$p" || fails=$((fails + 1)); done
  wait || true
  for s in "$@"; do
    s=${s#@}; [ -f "$OUT/bc/$(echo "$s" | tr / _).bc" ] || { echo "missing bitcode: $s"; fails=$((fails + 1)); }
  done
  [ "$fails" -eq 0 ] || { echo "$fails TON sources failed"; exit 1; }
}
# link_native <out> <bitcode or object>...: a native binary (glibc and, on a server, the native
# libc++ built by setup.sh); what nothing defines gets aborting stubs (the linker's list of
# undefined symbols), so a call is loud, not silent
link_native() {
  local out=$1; shift
  local lib=(-Wl,--no-demangle -lm)
  [ $NATIVE = 1 ] || lib=(-nostdlib++ -L"$LCXX/lib" -Wl,-rpath,"$LCXX/lib" -Wl,--no-demangle -lc++ -lc++abi -lm)
  if ! "$CXX" -O1 -g0 "$@" -o "$out" "${lib[@]}" 2> "$out.link.err"; then
    python3 "$HERE/gen_stubs.py" --linker-errors "$out.link.err" > "$out-stubs.c"
    clang -O1 -g0 -w -c "$out-stubs.c" -o "$out-stubs.o"
    "$CXX" -O1 -g0 "$@" "$out-stubs.o" -o "$out" "${lib[@]}"
    echo "$(basename "$out"): native stubs $(grep -c '__asm__' "$out-stubs.c")"
  fi
}
compile_all "${TON_SRCS[@]}"
STUBDEF=; [ "$TONOPS" = 1 ] && STUBDEF=-DTVM_KLEE_TONOPS
"$CXX" "${CXXFLAGS[@]}" $STUBDEF -emit-llvm -c "$HERE/harness/stubs.cpp" -o "$OUT/stubs.bc"

if [ "$TONOPS" = 1 ]; then
  # tlbc, then the TL-B code of block.tlb, as crypto/CMakeLists.txt makes it
  if [ ! -f "$OUT/src/gen/block/block-auto.cpp" ] || [ "$TON/crypto/block/block.tlb" -nt "$OUT/src/gen/block/block-auto.cpp" ]; then
    for f in "$TON/crypto/tl/tlbc.cpp" "$TON/crypto/parser/srcread.cpp" "$TON/crypto/parser/lexer.cpp" \
             "$TON/crypto/parser/symtable.cpp" "$HERE/harness/tlbc-crc32.cpp"; do
      "$CXX" "${CXXFLAGS_TLBC[@]}" -emit-llvm -c "$f" -o "$OUT/tlbc/$(basename "$f" .cpp).bc"
    done
    llvm-link "$OUT"/tlbc/{tlbc,srcread,lexer,symtable,tlbc-crc32}.bc "$OUT"/bc/crypto_common_*.bc \
      "$OUT"/bc/tdutils_*.bc "$OUT/stubs.bc" -o "$OUT/tlbc/tlbc-all.bc"
    link_native "$OUT/tlbc/tlbc" "$OUT/tlbc/tlbc-all.bc"
    cp "$TON/crypto/block/block.tlb" "$OUT/src/gen/block/"
    (cd "$OUT/src/gen/block" && "$OUT/tlbc/tlbc" -o block-auto -n block::gen -z block.tlb)
  fi
  compile_all "${TONOPS_SRCS[@]}"
  "$CXX" "${CXXFLAGS_TONOPS[@]}" -emit-llvm -c "$HERE/harness/tonops-stubs.cpp" -o "$OUT/tonops-stubs.bc"
else
  rm -f "$OUT/tonops-stubs.bc"
  for s in "${TONOPS_SRCS[@]}"; do rm -f "$OUT/bc/$(echo "${s#@}" | tr / _).bc"; done
fi
STUBS=("$OUT/stubs.bc"); [ "$TONOPS" = 1 ] && STUBS+=("$OUT/tonops-stubs.bc")

# TON module, block-instrumented
llvm-link "$OUT"/bc/*.bc -o "$OUT/ton.bc"
llvm-dis "$OUT/ton.bc" -o "$OUT/ton.ll"
python3 "$HERE/cov_instrument.py" "$OUT/ton.ll" "$OUT/ton-cov.ll" "$OUT/cov-blocks.txt" "$CXXFILT"
llvm-as "$OUT/ton-cov.ll" -o "$OUT/ton-cov.bc"
rm -f "$OUT/ton.ll" "$OUT/ton-cov.ll"

# harness (KLEE flavour and native flavour)
flavours=(klee native); [ $NATIVE = 1 ] && flavours=(native)
for flavour in "${flavours[@]}"; do
  def=-DTVM_KLEE_NATIVE; [ $flavour = klee ] && def=-DTVM_KLEE_SYMBOLIC
  "$CXX" "${CXXFLAGS[@]}" -I"$OUT" $def -emit-llvm -c "$HERE/harness/harness.cpp" -o "$OUT/harness-$flavour.bc"
done

# native replay: the same instrumented TON module and stubs, the native harness flavour
llvm-link "$OUT/ton-cov.bc" "${STUBS[@]}" "$OUT/harness-native.bc" -o "$OUT/replay.bc"
link_native "$OUT/replay" "$OUT/replay.bc"
if [ $NATIVE = 1 ]; then
  echo "built: $OUT/replay"
  exit 0
fi

# KLEE: symbols nothing defines: libc (uclibc), libc++ and KLEE intrinsics provide most; the rest
# get aborting definitions (gen_stubs.py), so a call is loud, not silent.
llvm-link "$OUT/ton-cov.bc" "${STUBS[@]}" "$OUT/harness-klee.bc" -o "$OUT/pre-klee.bc"
llvm-nm --defined-only "$LCXX/lib/libc++.bca" "$KW/klee-uclibc/lib/libc.a" "$KW"/klee-build/runtime/lib/*.bca 2>/dev/null \
  | awk 'NF>=3 {print $3}' | sort -u > "$OUT/provided.txt"
llvm-dis "$OUT/pre-klee.bc" -o - | python3 "$HERE/gen_stubs.py" "$OUT/provided.txt" > "$OUT/autostubs.c"
"$ENV/bin/clang" -O1 -g0 -w -emit-llvm -c "$OUT/autostubs.c" -o "$OUT/autostubs.bc"
# only what main reaches: KLEE loads the module in half the time (25 s -> 13 s with tonops)
llvm-link "$OUT/pre-klee.bc" "$OUT/autostubs.bc" -o "$OUT/harness-all.bc"
opt -passes=internalize,globaldce -internalize-public-api-list=main "$OUT/harness-all.bc" -o "$OUT/harness.bc"
echo "auto stubs: $(grep -c '__asm__' "$OUT/autostubs.c")"
echo "built: $OUT/harness.bc $OUT/replay"
