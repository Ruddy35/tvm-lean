#!/usr/bin/env python3
"""Lists the lines of C++ with uncovered branches (and lines never run) from a gcovr JSON report
(scripts/cpp-coverage-report.sh writes coverage.json), grouped by file and function, with the
source line, for writing targeted oracle cases:

  python3 tools/coverage/uncovered.py [--decisions] coverage.json TON_SRC [FILE_SUBSTRING...]

Each entry: `line  mark  source`, where mark is `-` for a line never run, else the branches
taken/total. --decisions keeps only the branches of the program's own decisions (if, loops,
switch, ?:, &&, ||): gcc also counts branches inside VM_LOG (logging is off in the oracle) and
inside inlined destructors of reference-counted pointers, which no input can steer."""
import json
import os
import re
import subprocess
import sys

DECISION = re.compile(r"\b(if|while|for|switch|case|default)\b|\?|&&|\|\|")
NOISE = re.compile(r"^\s*(VM_LOG|LOG\(|DCHECK|CHECK\()")


def demangle(names):
    names = sorted(set(n for n in names if n))
    try:
        out = subprocess.run(["c++filt"], input="\n".join(names), capture_output=True, text=True,
                             check=True).stdout.splitlines()
        return dict(zip(names, out))
    except (OSError, subprocess.CalledProcessError):
        return {n: n for n in names}


def main():
    args = sys.argv[1:]
    decisions = "--decisions" in args
    args = [a for a in args if a != "--decisions"]
    if len(args) < 2:
        sys.exit(__doc__)
    report, src, only = args[0], args[1], args[2:]
    data = json.load(open(report))
    files = [f for f in sorted(data["files"], key=lambda f: f["file"])
             if not only or any(s in f["file"] for s in only)]
    names = demangle(ln.get("function_name", "") for f in files for ln in f["lines"])
    totals = []
    for f in files:
        name = f["file"]
        try:
            text = open(os.path.join(src, name), encoding="utf-8", errors="replace").read().splitlines()
        except OSError:
            text = []
        # a line may be listed once per instance of a template or inline function: sum them
        by_line = {}
        for ln in f["lines"]:
            n = ln["line_number"]
            e = by_line.setdefault(n, {"count": 0, "branches": None, "fn": ln.get("function_name", "")})
            e["count"] += ln["count"]
            br = [b["count"] for b in ln.get("branches", []) if not b.get("throw")]
            e["branches"] = br if e["branches"] is None else [a + b for a, b in zip(e["branches"], br)]
        out, fn_prev = [], None
        nb = nt = 0
        for n in sorted(by_line):
            e = by_line[n]
            line = text[n - 1].strip() if 0 < n <= len(text) else ""
            brs = e["branches"] or []
            if decisions and (not DECISION.search(line) or NOISE.match(line)):
                brs = []
            taken = sum(1 for c in brs if c > 0)
            nb += len(brs)
            nt += taken
            if e["count"] > 0 and taken == len(brs):
                continue
            if decisions and e["count"] > 0 and not brs:
                continue
            fn = names.get(e["fn"], e["fn"])
            if fn != fn_prev:
                out.append(f"  {fn}")
                fn_prev = fn
            mark = "-" if e["count"] == 0 else f"{taken}/{len(brs)}"
            out.append(f"    {n:5} {mark:>7}  {line}")
        totals.append((name, nt, nb))
        if out:
            print(f"{name}  branches {nt}/{nb}")
            print("\n".join(out))
            print()
    print("summary (branches taken/total):")
    for name, nt, nb in totals:
        pct = f"{100 * nt / nb:.0f}%" if nb else "--"
        print(f"  {name:50} {nt:6}/{nb:<6} {pct}")
    at, ab = sum(t[1] for t in totals), sum(t[2] for t in totals)
    print(f"  {'TOTAL':50} {at:6}/{ab:<6} {100 * at / ab:.0f}%" if ab else "  TOTAL --")


if __name__ == "__main__":
    main()
