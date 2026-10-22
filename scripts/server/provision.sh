#!/usr/bin/env bash
# Set up a fresh build server (no root needed) for tvm-lean: the Lean toolchain (elan), the
# repository from GitHub (branch $BRANCH) and a first build of the model, tests and proofs.
# The C++ reference is built separately: scripts/server/build-cpp-reference.sh.
#   BRANCH  [default: claude/bold-turing-6i3ctb]   WS [default: ~/ws]
set -e
BRANCH=${BRANCH:-claude/bold-turing-6i3ctb}; WS=${WS:-$HOME/ws}
mkdir -p "$WS/runs"
if [ ! -x "$HOME/.elan/bin/lake" ]; then
  curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -o /tmp/elan-init.sh
  sh /tmp/elan-init.sh -y --default-toolchain none --no-modify-path
fi
export PATH=$HOME/.elan/bin:$PATH
[ -d "$WS/tvm-lean/.git" ] || git clone -q https://github.com/Ruddy35/tvm-lean -b "$BRANCH" "$WS/tvm-lean"
cd "$WS/tvm-lean"
elan toolchain install "$(cat lean-toolchain)"
lake build TvmLeanProofs tvm-lean-tests tvm-lean-diff-test tvm-lean-tx-test 2>&1 | tail -n 3
