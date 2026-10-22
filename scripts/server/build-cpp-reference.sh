#!/usr/bin/env bash
# Build the C++ reference (ton @ 3d478cb) without root: fift with its library and
# libemulator.so, the oracles of scripts/verify-all.sh. Needs gcc/g++, make, perl, python3 with
# pip, curl, git. cmake and ninja come from pip (--user); GNU m4, autoconf, automake and libtool
# (TON's bundled secp256k1 runs autogen.sh) are built into $WS/tools/local (-std=gnu17: m4 1.4.19
# does not compile as C23, gcc 15's default). TON_ARCH: the -march of the build; the default
# `native` makes binaries that fail ("Illegal instruction") on an older CPU.
#   WS [default: ~/ws]   TON_ARCH [default: native]   JOBS [default: nproc]
# Result: $WS/ton-bin/fift, $WS/ton-bin/lib, $WS/ton-build/emulator/libemulator.so
set -ex
WS=${WS:-$HOME/ws}; TON_ARCH=${TON_ARCH:-native}; JOBS=${JOBS:-$(nproc)}
L=$WS/tools/local; mkdir -p "$L" "$WS/tools/src"
export PATH=$L/bin:$HOME/.local/bin:$PATH
python3 -m pip install -q --user --break-system-packages cmake ninja
cd "$WS/tools/src"
for t in m4-1.4.19 autoconf-2.72 automake-1.17 libtool-2.5.4; do
  n=${t%-*}; b=$n; [ "$n" = libtool ] && b=libtoolize
  [ -x "$L/bin/$b" ] && continue
  curl -sSfL "https://ftp.gnu.org/gnu/$n/$t.tar.gz" -o "$t.tar.gz"
  rm -rf "$t"; tar -xzf "$t.tar.gz"
  (cd "$t" && CFLAGS="-O2 -std=gnu17" ./configure -q --prefix="$L" && make -s -j"$JOBS" && make -s install)
done
[ -d "$WS/ton-src/.git" ] || git clone -q https://github.com/ton-blockchain/ton "$WS/ton-src"
cd "$WS/ton-src"
git checkout -q 3d478cbde854be03a18ab2a59f8fc3c565cf7d14
git submodule update -q --init --recursive
cmake -S "$WS/ton-src" -B "$WS/ton-build" -G Ninja -DCMAKE_BUILD_TYPE=Release -DTON_ARCH="$TON_ARCH"
ninja -C "$WS/ton-build" -j "$JOBS" fift emulator
mkdir -p "$WS/ton-bin"; rm -rf "$WS/ton-bin/lib"
cp "$WS/ton-build/crypto/fift" "$WS/ton-bin/fift"; cp -r "$WS/ton-src/crypto/fift/lib" "$WS/ton-bin/lib"
echo '2 3 + . cr' > /tmp/fift-check.fif; "$WS/ton-bin/fift" -I "$WS/ton-bin/lib" -s /tmp/fift-check.fif
