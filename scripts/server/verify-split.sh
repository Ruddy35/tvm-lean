#!/usr/bin/env bash
# The full check (scripts/verify-all.sh) of one commit on part of the global versions, so that
# several servers share it: e.g. "0 1 2 3 4 5", "6 7 8 9 10 11" and "12 13 14 15 16". Each part
# also runs the unit tests, the opcode check and the transaction fuzz. The commit counts as checked
# when every part ends with "verify: OK".
#   usage: verify-split.sh <commit> "<versions>"   (in tmux; WS [default: ~/ws], BRANCH as provision.sh)
H=${1:?commit}; V=${2:?versions}; WS=${WS:-$HOME/ws}; BRANCH=${BRANCH:-claude/bold-turing-6i3ctb}
cd "$WS/tvm-lean" && git fetch -q origin "$BRANCH" && git checkout -q -f "$H" || exit 1
export PATH=$HOME/.elan/bin:$PATH TON_FIFT_BIN=$WS/ton-bin/fift TON_FIFT_LIB=$WS/ton-bin/lib TVMLEAN_TON_BUILD=$WS/ton-build
OUT=$WS/runs/verify-$H VERSIONS="$V" PAR=${PAR:-16} scripts/verify-all.sh > "$WS/runs/verify-$H.out" 2>&1
echo "done rc=$?" >> "$WS/runs/verify-$H.out"
