#!/usr/bin/env bash
# Build the C++ reference fift with gcc branch/line coverage (phase 2: measured conformance).
# No root needed: build tools go to $WS/tools (venv: cmake, ninja, gcovr; local: m4, autoconf,
# automake, libtool — the bundled secp256k1 is built with autotools).
#   WS        workspace root                       [default: ~/ws]
#   TON_SRC   ton sources at the reference commit  [default: $WS/ton-src]  (with submodules)
#   BUILD     build directory                      [default: $WS/ton-build-cov]
set -eu
WS=${WS:-$HOME/ws}; TON_SRC=${TON_SRC:-$WS/ton-src}; BUILD=${BUILD:-$WS/ton-build-cov}
T=$WS/tools; L=$T/local
if [ ! -x "$T/venv/bin/cmake" ]; then
  python3 -m venv --without-pip "$T/venv"
  curl -sSfL -o /tmp/get-pip.py https://bootstrap.pypa.io/get-pip.py
  "$T/venv/bin/python3" /tmp/get-pip.py -q
  "$T/venv/bin/pip" install -q cmake ninja gcovr
fi
if [ ! -x "$L/bin/autoreconf" ]; then
  mkdir -p "$T/src" "$L"; cd "$T/src"
  export PATH=$L/bin:$PATH CFLAGS="-O2 -std=gnu17"   # old gnulib does not build as C23 (gcc 15)
  for t in m4-1.4.19 autoconf-2.72 automake-1.17 libtool-2.5.4; do
    n=${t%-*}; [ -f $t.tar.gz ] || curl -sSfLO https://ftp.gnu.org/gnu/$n/$t.tar.gz
    rm -rf $t; tar xzf $t.tar.gz; (cd $t && ./configure --prefix="$L" && make -j"$(nproc)" && make install)
  done
  unset CFLAGS
fi
export PATH=$L/bin:$T/venv/bin:$PATH
git -C "$TON_SRC" submodule update --init --recursive --depth 1
cmake -S "$TON_SRC" -B "$BUILD" -G Ninja -DCMAKE_BUILD_TYPE=Debug -DCMAKE_POLICY_VERSION_MINIMUM=3.5 \
  -DCMAKE_C_FLAGS="--coverage -O0" -DCMAKE_CXX_FLAGS="--coverage -O0" -DCMAKE_EXE_LINKER_FLAGS="--coverage" \
  -DTON_USE_JEMALLOC=OFF
ninja -C "$BUILD" -j"$(nproc)" fift
"$BUILD/crypto/fift" -V
