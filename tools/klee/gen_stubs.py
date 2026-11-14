#!/usr/bin/env python3
"""C definitions for the symbols an LLVM text module (stdin) declares but nothing defines.

Symbols listed in <provided.txt> (defined by libc++, uclibc or KLEE's runtime), LLVM intrinsics
and KLEE intrinsics are left alone. Every other function gets a body that reports its name and
aborts, so a path that reaches code outside the build stops loudly instead of silently; every
other global gets 256 zero bytes. Output: C source on stdout.

usage: llvm-dis m.bc -o - | gen_stubs.py <provided.txt> [<more provided names> ...]
       gen_stubs.py --linker-errors <ld stderr>   (functions the native link left undefined)"""
import re
import sys

DECL = re.compile(r'^declare\b.*?@("(?:[^"\\]|\\.)+"|[-a-zA-Z$._0-9]+)\(')
EXT = re.compile(r'^@("(?:[^"\\]|\\.)+"|[-a-zA-Z$._0-9]+) = external\b')
LDERR = re.compile(r"undefined reference to [`']([^']+)'")


def main():
    provided = set()
    funcs, datas = [], []
    if sys.argv[1] == '--linker-errors':
        with open(sys.argv[2]) as f:
            for line in f:
                funcs.extend(LDERR.findall(line))
    else:
        for p in sys.argv[1:]:
            with open(p) as f:
                provided.update(x.strip() for x in f if x.strip())
        for line in sys.stdin:
            m = DECL.match(line)
            if m:
                funcs.append(m.group(1).strip('"'))
                continue
            m = EXT.match(line)
            if m:
                datas.append(m.group(1).strip('"'))
    # In the bitcode mode only C++ symbols (_Z...) are stubbed: a C symbol is libc/libm's, which
    # KLEE models (malloc, ...) or calls natively; stubbing it would change the run.
    linker = sys.argv[1] == '--linker-errors'
    skip = lambda n: (n in provided or n.startswith('llvm.') or n.startswith('klee_')
                      or n in ('tvm_cov', 'tvm_klee_step_hook', 'tvm_klee_step_end')
                      or (not linker and not n.startswith('_Z')))
    print('#include <stdio.h>\n#include <stdlib.h>')
    print('static void tvm_stub_fail(const char* s) {\n'
          '  fprintf(stderr, "tvm-klee: call of a stubbed symbol: %s\\n", s);\n  abort();\n}')
    n = 0
    for f in sorted(set(funcs)):
        if skip(f):
            continue
        print(f'void tvm_stub_{n}(void) __asm__("{f}");\n'
              f'void tvm_stub_{n}(void) {{ tvm_stub_fail("{f}"); }}')
        n += 1
    for d in sorted(set(datas)):
        if skip(d):
            continue
        print(f'char tvm_stub_data_{n}[256] __asm__("{d}");')
        n += 1


if __name__ == '__main__':
    main()
