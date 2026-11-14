#!/usr/bin/env python3
"""Helpers of tools/klee/measure.sh (no third-party modules; run with python3 -I).

  klee_cases.py suites <ranges.txt> <tvm_spec_index.json>
      the suite names (comma-separated) whose opcode range meets one of the spec's 24-bit
      ranges (`replay ranges <SPEC>`)
  klee_cases.py versions <existing.tsv>
      the dumped suite cases (`tvm-lean-tests --dump-cases`: id, gas, code, tokens), once per
      global version 0..16, as case lines: `<id>@<v> \\t <v> \\t <gas> \\t <code> \\t <tokens>`
  klee_cases.py lines <cases.tsv>
      KLEE's cases (run.sh: ktest, exact sig, edge sig, version, gas, code, tokens) as case lines,
      one per distinct input, the id `<SPEC>/<test>`
  klee_cases.py reps <cases.tsv>
      the same, one per exact path
  klee_cases.py compare <SPEC> <cases.tsv> <existing-sigs.tsv> <out dir>
      which of KLEE's paths the existing cases reach; writes <out>/coverage.txt and
      <out>/missed.tsv (one KLEE case line per path no existing case reaches, then the path's
      edge signature)
  klee_cases.py lean <tvm_spec_index.json> <missed.tsv>...
      Tests/Harness/Gen/Klee.lean (stdout): the case lines, one per path, each after the name of
      the suite of its opcode, in a string the module parses
"""
import json
import os
import sys


def suites(ranges_path, index_path):
    ranges = [tuple(map(int, l.split())) for l in open(ranges_path) if l.strip()]
    idx = json.load(open(index_path))
    names = []
    for row in idx['tvm_instructions']:
        lay = row.get('layout') or {}
        lo, hi = lay.get('min'), lay.get('max')
        if lo is None or hi is None:
            continue
        if any(lo < b and a < hi for a, b in ranges):
            names.append(row['name'])
    print(','.join(sorted(set(names))))


def versions(path):
    for line in open(path):
        line = line.rstrip('\n')
        if not line:
            continue
        cols = line.split('\t')
        if len(cols) < 4:
            continue
        cid, gas, code, toks = cols[0], cols[1], cols[2], cols[3]
        for v in range(17):
            print(f'{cid}@{v}\t{v}\t{gas}\t{code}\t{toks}')


def read_klee(path):
    rows = []
    for line in open(path):
        cols = line.rstrip('\n').split('\t')
        if len(cols) < 7 or cols[1] == 'ERROR':
            continue
        rows.append(cols)
    return rows


def lines(path, reps_only=False):
    seen = set()
    for c in read_klee(path):
        key = c[1] if reps_only else tuple(c[3:7])
        if key in seen:
            continue
        seen.add(key)
        test = os.path.basename(c[0]).replace('.ktest', '')
        spec = os.path.basename(os.path.dirname(os.path.dirname(c[0])))
        print(f'{spec}/{test}\t' + '\t'.join(c[3:7]))


def compare(spec, cases_path, sigs_path, out):
    klee = read_klee(cases_path)
    k_exact = {}
    k_edges = {}
    for c in klee:
        k_exact.setdefault(c[1], c)
        k_edges.setdefault(c[2], c)
    e_exact, e_edges = set(), set()
    n_runs = n_hit = 0
    per_suite = {}
    for line in open(sigs_path):
        cols = line.rstrip('\n').split('\t')
        if len(cols) < 3 or cols[1] == 'ERROR':
            continue
        n_runs += 1
        if cols[2] == '-':
            continue
        n_hit += 1
        suite = cols[0].split('/')[0]
        for s in cols[2].split(' '):
            a, b = s.split(':')
            e_exact.add(a)
            e_edges.add(b)
            per_suite.setdefault(suite, set()).add(b)
    missed = [k_edges[s] for s in sorted(k_edges) if s not in e_edges]
    with open(os.path.join(out, 'missed.tsv'), 'w') as f:
        for c in missed:  # a case line, then the edge signature of its path
            test = os.path.basename(c[0]).replace('.ktest', '')
            f.write(f'{spec}/{test}\t' + '\t'.join(c[3:7]) + f'\t{c[2]}\n')
    with open(os.path.join(out, 'coverage.txt'), 'w') as f:
        f.write(f'spec {spec}\n')
        f.write(f'klee_tests {len(klee)}\n')
        f.write(f'klee_paths_exact {len(k_exact)}\n')
        f.write(f'klee_paths_edges {len(k_edges)}\n')
        f.write(f'existing_runs {n_runs} (case x version)\n')
        f.write(f'existing_runs_reaching_the_instruction {n_hit}\n')
        f.write(f'existing_paths_exact {len(e_exact)}\n')
        f.write(f'existing_paths_edges {len(e_edges)}\n')
        f.write(f'klee_exact_reached {sum(1 for s in k_exact if s in e_exact)}\n')
        f.write(f'klee_edges_reached {len(k_edges) - len(missed)}\n')
        f.write(f'klee_edges_missed {len(missed)}\n')
        f.write(f'existing_edges_outside_klee {len(e_edges - set(k_edges))}\n')
    print(open(os.path.join(out, 'coverage.txt')).read(), end='')


def boc_root_bits(h):
    """The bits (as a '0'/'1' string) of the root cell of a standard BOC in hex."""
    b = bytes.fromhex(h)
    assert b[:4] == bytes.fromhex('b5ee9c72'), 'not a standard BOC'
    flags = b[4]
    has_idx, size = flags & 0x80, flags & 7
    off = b[5]
    p = 6
    rd = lambda n: (int.from_bytes(b[p:p + n], 'big'), p + n)
    cells, p = rd(size)
    roots, p = rd(size)
    _absent, p = rd(size)
    _tot, p = rd(off)
    root, p = rd(size)
    p += size * (roots - 1)
    if has_idx:
        p += cells * off
    # cells in order; the root is cell `root`
    for i in range(cells):
        d1, d2 = b[p], b[p + 1]
        p += 2
        n = (d2 + 1) // 2
        data = b[p:p + n]
        p += n
        refs = d1 & 7
        refsz = size
        if i == root:
            bits = ''.join(f'{x:08b}' for x in data)
            if d2 % 2:
                bits = bits.rstrip('0')[:-1]
            return bits
        p += refs * refsz
    raise ValueError('root not found')


def lean(index_path, missed_paths):
    idx = json.load(open(index_path))
    rows = []
    for row in idx['tvm_instructions']:
        lay = row.get('layout') or {}
        if lay.get('min') is not None:
            rows.append((lay['min'], lay['max'], row['name']))
    out = []
    seen = set()
    for path in missed_paths:
        for line in open(path):
            line = line.rstrip('\n')
            if not line:
                continue
            cols = line.split('\t')
            if len(cols) > 5:  # one case per path over all the runs given
                if cols[5] in seen:
                    continue
                seen.add(cols[5])
                cols = cols[:5]
                line = '\t'.join(cols)
            bits = boc_root_bits(cols[3])
            op = int((bits[:24] + '0' * 24)[:24], 2)
            names = [n for lo, hi, n in rows if lo <= op < hi]
            if not names:
                # an argument combination the handler rejects (inv_opcode) has no row: the suite
                # of the row just below it, the same handler's
                below = [(lo, n) for lo, hi, n in rows if lo <= op]
                names = [max(below)[1]] if below else []
            if len(names) != 1:
                sys.exit(f'{cols[0]}: opcode {op:06x} names {names}')
            out.append((names[0], line))
    out.sort()
    data = ''.join(f'{name}\t{line}\n' for name, line in out)
    assert '"' not in data
    print(LEAN_HEAD + 'private def data : String := r"\n' + data + '"\n' + LEAN_TAIL, end='')


LEAN_HEAD = r"""import Tests.Harness.Registry
import Tests.Harness.CaseFile

/-!
Oracle cases found by `tools/klee` (KLEE on the C++ instruction handlers, `tools/README.md`): each
is an input on which C++ takes a path through the handler (the set of block-to-block edges of the
instruction's step, loop counts aside) that no other oracle or fuzz case of the suites takes, at
any global version. Each runs at every version like the suite's own cases.

`data` holds one case per line: `<suite> \t <case line of Tests.CaseFile>` (id, version found,
gas limit, code BOC, stack tokens). Generated, do not edit: `python3 tools/klee/klee_cases.py lean
docs/progress/tvm_spec_index.json <runs>/*/missed.tsv > Tests/Harness/Gen/Klee.lean`.
-/

namespace Tests.Gen.Klee

open TvmLean

"""

LEAN_TAIL = r"""
/-- (suite, case line) of every line of `data`. -/
private def lines : Array (String × String) :=
  ((data.splitOn "\n").filter (·.trim ≠ "")).toArray.map fun l =>
    match l.splitOn "\t" with
    | s :: rest => (s, "\t".intercalate rest)
    | [] => ("", "")

/-- The KLEE cases of the suite `suite`. -/
def casesFor (suite : String) : Array OracleCase :=
  lines.filterMap fun (s, l) =>
    if s != suite then none
    else
      match Tests.CaseFile.caseOfLine s l with
      | .ok c => some { c with name := s!"oracle/klee/{c.name}" }
      | .error e => panic! s!"Tests.Gen.Klee: {e}"

end Tests.Gen.Klee
"""


def main():
    cmd = sys.argv[1]
    if cmd == 'lean':
        lean(sys.argv[2], sys.argv[3:])
        return
    if cmd == 'suites':
        suites(sys.argv[2], sys.argv[3])
    elif cmd == 'versions':
        versions(sys.argv[2])
    elif cmd == 'lines':
        lines(sys.argv[2])
    elif cmd == 'reps':
        lines(sys.argv[2], reps_only=True)
    elif cmd == 'compare':
        compare(*sys.argv[2:6])
    else:
        sys.exit(f'unknown command {cmd}')


if __name__ == '__main__':
    main()
