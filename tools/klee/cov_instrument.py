#!/usr/bin/env python3
"""Insert `call void @tvm_cov(i32 <id>)` at the start of every basic block of every function
defined in an LLVM text module (after the block's phi nodes and its landingpad, which must stay
first). Block ids are 1, 2, ... in module order, so the same input gives the same ids: the harness
hashes the sequence of ids seen while the instruction under test runs (its C++ path signature),
in KLEE and in the native replay alike.

usage: cov_instrument.py <in.ll> <out.ll> <blocks.txt>
blocks.txt lists `<id> <function> <block label>` for reading a signature back."""
import re
import sys

LABEL = re.compile(r'^([-a-zA-Z$._0-9"]+):(\s|$)')
DEFINE = re.compile(r'^define\b.*@("[^"]+"|[-a-zA-Z$._0-9]+)\(')


def main():
    src, dst, blocks = sys.argv[1:4]
    out = open(dst, 'w')
    bl = open(blocks, 'w')
    nid = 0
    fn = None
    pending = None  # label of a block whose call is not inserted yet
    in_landingpad = False
    with open(src) as f:
        for line in f:
            if fn is None:
                m = DEFINE.match(line)
                if m and line.rstrip().endswith('{'):
                    fn = m.group(1)
                    pending = 'entry'
                out.write(line)
                continue
            s = line.strip()
            if s == '}' and not line.startswith(' '):
                fn = None
                pending = None
                out.write(line)
                continue
            if pending is None:
                m = LABEL.match(line)
                if m:
                    pending = m.group(1)
                out.write(line)
                continue
            # inside a block whose call is pending
            if in_landingpad:
                if s.startswith('cleanup') or s.startswith('catch ') or s.startswith('filter '):
                    out.write(line)
                    continue
                in_landingpad = False
            if s == '' or s.startswith(';'):
                out.write(line)
                continue
            m = LABEL.match(line)
            if m:  # a named entry block: its label comes first
                pending = m.group(1)
                out.write(line)
                continue
            if re.match(r'^%\S+ = phi\b', s):
                out.write(line)
                continue
            if re.match(r'^%\S+ = landingpad\b', s):
                in_landingpad = True
                out.write(line)
                continue
            nid += 1
            bl.write(f'{nid} {fn} {pending}\n')
            out.write(f'  call void @tvm_cov(i32 {nid})\n')
            pending = None
            out.write(line)
    out.write('\ndeclare void @tvm_cov(i32)\n')
    out.close()
    bl.close()
    print(f'cov_instrument: {nid} blocks', file=sys.stderr)


if __name__ == '__main__':
    main()
