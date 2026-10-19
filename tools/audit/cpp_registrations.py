#!/usr/bin/env python3
"""Static inventory of TVM opcode registrations in the C++ reference (crypto/vm/*.cpp).

Usage: cpp_registrations.py <ton-src> > cpp-registrations.csv

For every OpcodeInstr::mk{simple,fixed,fixedrange,ext,extrange}(...) call it records the file,
the kind, the literal numeric arguments when they are literal, the first string literal (the
mnemonic or its prefix) and a trailing ->require_version(N). Registrations whose opcode is computed
(inside helper functions) are kept with resolved=no: the exhaustive decoder comparison through the
C++ dispatch table (fift (vmoplen)/(vmopdump)) covers them.
"""
import csv, glob, os, re, sys

src = sys.argv[1]
KINDS = ("mksimple", "mkfixedrange", "mkfixed", "mkextrange", "mkext")
num = r"(0x[0-9a-fA-F]+|\d+)"

def call_args(text, start):
    """Return the text of the balanced argument list starting at text[start] == '('."""
    depth, i = 0, start
    while i < len(text):
        c = text[i]
        if c == "(":
            depth += 1
        elif c == ")":
            depth -= 1
            if depth == 0:
                return text[start + 1:i], i + 1
        elif c == '"':
            i += 1
            while text[i] != '"':
                i += 2 if text[i] == "\\" else 1
        i += 1
    return text[start + 1:], len(text)

def split_top(args):
    out, depth, cur, instr = [], 0, "", False
    for c in args:
        if c == '"':
            instr = not instr
        if not instr:
            if c in "([{":
                depth += 1
            elif c in ")]}":
                depth -= 1
            elif c == "," and depth == 0:
                out.append(cur.strip()); cur = ""; continue
        cur += c
    if cur.strip():
        out.append(cur.strip())
    return out

w = csv.writer(sys.stdout)
w.writerow(["file", "line", "kind", "resolved", "min", "max", "total_bits", "arg_bits", "mnemonic", "require_version"])
for path in sorted(glob.glob(os.path.join(src, "crypto", "vm", "*.cpp"))):
    text = open(path, encoding="utf-8", errors="replace").read()
    for m in re.finditer(r"OpcodeInstr::(mksimple|mkfixedrange|mkfixed|mkextrange|mkext)\s*\(", text):
        kind = m.group(1)
        args, end = call_args(text, m.end() - 1)
        parts = split_top(args)
        lits = [p if re.fullmatch(num, p) else None for p in parts]
        mn = re.search(r'"([^"]*)"', args)
        rv = re.match(r"\s*->\s*require_version\((\d+)\)", text[end:end + 60])
        line = text.count("\n", 0, m.start()) + 1
        if kind == "mksimple":
            lo, hi, tot, ab = lits[0], lits[0], lits[1], "0"
        elif kind == "mkfixed" or kind == "mkext":
            lo = hi = lits[0]; tot = None
            ab = lits[2] if len(lits) > 2 else None
            if lits[0] and lits[1] and ab:
                tot = str(int(lits[1], 0) + int(ab, 0))
        else:  # ranges
            lo, hi = lits[0], lits[1]
            tot = lits[2] if len(lits) > 2 else None
            ab = lits[3] if len(lits) > 3 else None
        resolved = "yes" if (lo and hi and tot) else "no"
        w.writerow([os.path.basename(path), line, kind, resolved, lo or "", hi or "", tot or "", ab or "",
                    (mn.group(1).strip() if mn else ""), rv.group(1) if rv else ""])
