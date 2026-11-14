#!/usr/bin/env python3
"""Insert a block report at the start of every basic block of every function defined in an LLVM
text module (after the block's phi nodes and its landingpad, which must stay first): `call void
@tvm_cov(i32 <id>)`, or `@tvm_covf` in the folded functions. Block ids are 1, 2, ... in module
order, so the same input gives the same ids: the harness hashes the ids seen while the
instruction under test runs (its C++ path signatures), in KLEE and in the native replay alike.

Folded functions (their blocks count for the exact signatures, not for the coarse, handler-level
one): everything outside namespace vm (td's BigInt, refint, bitstring, Ref and Slice helpers, the
library templates, ...), the bit-level methods of vm::CellSlice and vm::CellBuilder, and
destructors (whether a reference count reaches zero).

usage: cov_instrument.py <in.ll> <out.ll> <blocks.txt> [c++filt]
blocks.txt lists `<id> <F|K> <function> <block label>` (F: folded) for reading a signature back."""
import re
import subprocess
import sys

LABEL = re.compile(r'^([-a-zA-Z$._0-9"]+):(\s|$)')
DEFINE = re.compile(r'^define\b.*@("[^"]+"|[-a-zA-Z$._0-9]+)\(')


def folded(dem):
    if not dem.startswith('vm::'):
        return True
    if dem.startswith(('vm::CellSlice::', 'vm::CellBuilder::')):
        return True
    head = dem.split('(')[0]
    return '::~' in head


def demangle(names, tool):
    try:
        out = subprocess.run([tool], input='\n'.join(names) + '\n', capture_output=True, text=True,
                             check=True).stdout.split('\n')
    except (OSError, subprocess.CalledProcessError) as e:
        sys.exit(f'cov_instrument: {tool}: {e}')
    if len(out) < len(names):
        sys.exit('cov_instrument: demangler output too short')
    return dict(zip(names, out))


def main():
    src, dst, blocks = sys.argv[1:4]
    tool = sys.argv[4] if len(sys.argv) > 4 else 'c++filt'
    fns = []
    with open(src) as f:
        for line in f:
            m = DEFINE.match(line)
            if m and line.rstrip().endswith('{'):
                fns.append(m.group(1).strip('"'))
    dem = demangle(fns, tool)
    fold = {n: folded(dem[n]) for n in fns}
    out = open(dst, 'w')
    bl = open(blocks, 'w')
    nid = nfold = 0
    fn = None
    pending = None  # label of a block whose call is not inserted yet
    in_landingpad = False
    with open(src) as f:
        for line in f:
            if fn is None:
                m = DEFINE.match(line)
                if m and line.rstrip().endswith('{'):
                    fn = m.group(1).strip('"')
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
            fl = fold[fn]
            nfold += fl
            bl.write(f'{nid} {"F" if fl else "K"} {fn} {pending}\n')
            out.write(f'  call void @{"tvm_covf" if fl else "tvm_cov"}(i32 {nid})\n')
            pending = None
            out.write(line)
    out.write('\ndeclare void @tvm_cov(i32)\ndeclare void @tvm_covf(i32)\n')
    out.close()
    bl.close()
    print(f'cov_instrument: {nid} blocks, {nfold} in folded functions '
          f'({sum(fold.values())} of {len(fns)} functions)', file=sys.stderr)


if __name__ == '__main__':
    main()
