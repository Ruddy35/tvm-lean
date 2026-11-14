#!/usr/bin/env bash
# User-space KLEE toolchain for the C++ TVM (no root): LLVM/clang 18, cmake, ninja, Z3 and sqlite
# from conda-forge (micromamba), libc++/libc++abi as bitcode (wllvm), klee-uclibc, KLEE 3.3, and
# the C++ reference ton @ 3d478cb. Everything lands under $KW (default ~/ws/klee); each stage
# leaves a marker ($KW/.done-<stage>) and is skipped when rerun.
#   usage: tools/klee/setup.sh [stage ...]     (default: all stages, in order)
#   stages: mamba env llvmsrc libcxx uclibc klee ton
#   KW [default: ~/ws/klee]   JOBS [default: nproc]
# Needs: curl, git, make, tar/xz, gcc/g++ (KLEE itself is built with the system compiler).
set -euo pipefail
KW=${KW:-$HOME/ws/klee}; JOBS=${JOBS:-$(nproc)}
TON_COMMIT=3d478cbde854be03a18ab2a59f8fc3c565cf7d14
KLEE_TAG=v3.3
LLVM_VER=18.1.8
UCLIBC_TAG=klee_uclibc_v1.4
ENV=$KW/env
MM=$KW/mamba/bin/micromamba
mkdir -p "$KW"
cd "$KW"
done_mark() { touch "$KW/.done-$1"; }
is_done() { [ -f "$KW/.done-$1" ]; }

stage_mamba() {
  mkdir -p "$KW/mamba/bin"
  curl -sSfL https://github.com/mamba-org/micromamba-releases/releases/latest/download/micromamba-linux-64 \
    -o "$MM"
  chmod +x "$MM"
  "$MM" --version
}

stage_env() {
  # LLVM 18 is KLEE 3.3's recommended version. llvmdev: llvm-config, headers and libraries for
  # building KLEE; clang/clangxx: the bitcode compilers; llvm-tools: llvm-link, opt, llvm-ar, ...
  MAMBA_ROOT_PREFIX=$KW/mamba "$MM" create -y -p "$ENV" -c conda-forge --override-channels \
    "clang=$LLVM_VER" "clangxx=$LLVM_VER" "llvmdev=$LLVM_VER" "llvm-tools=$LLVM_VER" \
    cmake ninja libz3 sqlite zlib zstd libxml2 "python=3.12" pip
  "$ENV/bin/python" -m pip install -q wllvm lit tabulate
  "$ENV/bin/clang" --version | head -1
  "$ENV/bin/llvm-config" --version
}

stage_llvmsrc() {
  # Sources of the runtimes (libc++, libc++abi, libunwind) of the same LLVM release.
  local t=llvm-project-$LLVM_VER.src
  mkdir -p "$KW/src"; cd "$KW/src"
  [ -f "$t.tar.xz" ] || curl -sSfL \
    "https://github.com/llvm/llvm-project/releases/download/llvmorg-$LLVM_VER/$t.tar.xz" -o "$t.tar.xz"
  rm -rf "$t"
  tar -xJf "$t.tar.xz" "$t/runtimes" "$t/libcxx" "$t/libcxxabi" "$t/libunwind" "$t/cmake" \
    "$t/llvm/cmake" "$t/llvm/utils" "$t/third-party"
  ln -sfn "$t" llvm-project
}

stage_libcxx() {
  # As KLEE's scripts/build/p-libcxx.inc: libc++/libc++abi/libunwind built single-threaded with
  # wllvm, then extract-bc gives the bitcode libraries KLEE links (--libcxx); the native .so/.a
  # from the same build serve the native replay binary.
  local SRC=$KW/src/llvm-project B=$KW/libcxx-build I=$KW/libcxx-install
  rm -rf "$B"
  (
    export PATH=$ENV/bin:$PATH CC=wllvm CXX=wllvm++ LLVM_COMPILER=clang LLVM_COMPILER_PATH=$ENV/bin
    cmake -G Ninja -S "$SRC/runtimes" -B "$B" \
      -DLLVM_ENABLE_RUNTIMES="libcxx;libcxxabi;libunwind" -DLIBCXXABI_USE_LLVM_UNWINDER=ON \
      -DLLVM_ENABLE_THREADS=OFF -DLIBCXX_ENABLE_THREADS=OFF -DLIBCXXABI_ENABLE_THREADS=OFF \
      -DLIBUNWIND_ENABLE_THREADS=OFF -DLIBCXX_ENABLE_SHARED=ON -DLIBCXX_ENABLE_STATIC_ABI_LIBRARY=ON \
      -DLIBCXX_INCLUDE_BENCHMARKS=OFF -DLIBCXX_INCLUDE_TESTS=OFF -DLIBCXXABI_INCLUDE_TESTS=OFF \
      -DLIBUNWIND_INCLUDE_TESTS=OFF -DCMAKE_BUILD_TYPE=Release -DCMAKE_INSTALL_PREFIX="$I"
    ninja -C "$B" -j "$JOBS"
    ninja -C "$B" install
    for p in "$I"/lib/*/lib*.so "$I"/lib/*/lib*.a "$I"/lib/lib*.so "$I"/lib/lib*.a; do
      [ -f "$p" ] && [ ! -L "$p" ] && extract-bc "$p"
    done
  )
  ls "$I"/lib "$I"/lib/* | head -40
}

stage_uclibc() {
  [ -d "$KW/klee-uclibc/.git" ] || git clone -q -b "$UCLIBC_TAG" https://github.com/klee/klee-uclibc \
    "$KW/klee-uclibc"
  cd "$KW/klee-uclibc"
  # configure and the config tool (conf/mconf) need ncurses, which the env has
  export C_INCLUDE_PATH=$ENV/include LIBRARY_PATH=$ENV/lib
  ./configure --make-llvm-lib --with-cc "$ENV/bin/clang" --with-llvm-config "$ENV/bin/llvm-config"
  PATH=$ENV/bin:$PATH make -j"$JOBS"
  unset C_INCLUDE_PATH LIBRARY_PATH
  ls -la lib/libc.a
}

stage_klee() {
  [ -d "$KW/klee-src/.git" ] || git clone -q -b "$KLEE_TAG" https://github.com/klee/klee "$KW/klee-src"
  # gcc 15 no longer pulls <cstdint> in transitively, which LLVM 18 headers rely on: -include it
  local B=$KW/klee-build I=$KW/libcxx-install
  rm -rf "$B"
  PATH=$ENV/bin:$PATH cmake -G Ninja -S "$KW/klee-src" -B "$B" \
    -DCMAKE_BUILD_TYPE=Release -DCMAKE_C_COMPILER=gcc -DCMAKE_CXX_COMPILER=g++ \
    -DCMAKE_CXX_FLAGS="-include cstdint" \
    -DCMAKE_PREFIX_PATH="$ENV" -DLLVM_DIR="$ENV/lib/cmake/llvm" \
    -DCMAKE_EXE_LINKER_FLAGS="-Wl,-rpath,$ENV/lib" -DCMAKE_SHARED_LINKER_FLAGS="-Wl,-rpath,$ENV/lib" \
    -DLLVMCC="$ENV/bin/clang" -DLLVMCXX="$ENV/bin/clang++" \
    -DENABLE_SOLVER_Z3=ON -DZ3_INCLUDE_DIRS="$ENV/include" -DZ3_LIBRARIES="$ENV/lib/libz3.so" \
    -DENABLE_SOLVER_STP=OFF -DENABLE_SOLVER_METASMT=OFF -DENABLE_TCMALLOC=OFF \
    -DENABLE_POSIX_RUNTIME=ON -DKLEE_UCLIBC_PATH="$KW/klee-uclibc" \
    -DENABLE_KLEE_LIBCXX=ON -DKLEE_LIBCXX_DIR="$I" -DKLEE_LIBCXX_INCLUDE_DIR="$I/include/" \
    -DENABLE_KLEE_EH_CXX=ON -DKLEE_LIBCXXABI_SRC_DIR="$KW/src/llvm-project/libcxxabi" \
    -DENABLE_UNIT_TESTS=OFF -DENABLE_SYSTEM_TESTS=OFF -DENABLE_DOCS=OFF
  PATH=$ENV/bin:$PATH ninja -C "$B" -j "$JOBS"
  "$B/bin/klee" --version
}

stage_ton() {
  # The reference sources at the one commit, no submodules: the build compiles no third-party
  # code (crypto, libsodium and crc32c are replaced, see harness/stubs.cpp and harness/compat).
  if [ ! -d "$KW/ton/.git" ]; then
    git init -q "$KW/ton"
    git -C "$KW/ton" remote add origin https://github.com/ton-blockchain/ton
  fi
  cd "$KW/ton"
  git fetch -q --depth 1 origin "$TON_COMMIT"
  git checkout -q -f FETCH_HEAD
  git log --oneline -1
}

stages=("$@")
[ ${#stages[@]} -eq 0 ] && stages=(mamba env llvmsrc libcxx uclibc klee ton)
for s in "${stages[@]}"; do
  if is_done "$s"; then echo "== $s: done before"; continue; fi
  echo "== $s $(date -u +%T)"; "stage_$s"; done_mark "$s"
done
echo "== setup finished $(date -u +%T)"
