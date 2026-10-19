#!/usr/bin/env python3
"""Inventory of global-version checks in the C++ reference.

Usage: cpp_global_version.py <ton-src> > cpp-global-version.csv
Lists every use of get_global_version()/global_version in crypto/vm and crypto/block/transaction.cpp
with the enclosing function, the threshold (if the comparison is literal) and the source line.
"""
import csv, glob, os, re, sys
src = sys.argv[1]
files = sorted(glob.glob(os.path.join(src, "crypto", "vm", "**", "*.cpp"), recursive=True) +
               glob.glob(os.path.join(src, "crypto", "vm", "*.h")) +
               [os.path.join(src, "crypto", "block", "transaction.cpp")])
func_re = re.compile(r"^[A-Za-z_][\w:<>,\s\*&]*?\b([A-Za-z_][\w:]*)\s*\([^;]*\)\s*(const\s*)?\{?\s*$")
w = csv.writer(sys.stdout)
w.writerow(["file", "line", "function", "op", "threshold", "code"])
for path in files:
    if not os.path.exists(path):
        continue
    func = ""
    for n, line in enumerate(open(path, encoding="utf-8", errors="replace"), 1):
        m = func_re.match(line)
        if m and not line.lstrip().startswith(("if", "for", "while", "switch", "return", "else")):
            func = m.group(1)
        if "global_version" in line and not line.lstrip().startswith("//"):
            c = re.search(r"global_version(?:\(\))?\s*(>=|<=|==|!=|<|>)\s*(\d+)", line)
            w.writerow([os.path.relpath(path, src), n, func, c.group(1) if c else "", c.group(2) if c else "",
                        " ".join(line.strip().split())[:160]])
