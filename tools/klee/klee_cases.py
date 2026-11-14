#!/usr/bin/env python3
"""Helpers of tools/klee/measure.sh (no third-party modules; run with python3 -I).

A run is `<family>.<class>` (run.sh); its cases.tsv lines are
  ktest, exact sig, edge sig, coarse sig, version, gas, code BOC hex, stack tokens.
A case line (Tests/Harness/CaseFile.lean) is `id \\t version \\t gas \\t code \\t tokens`.

  klee_cases.py lines <runs dir>              every run's cases as case lines, one per distinct
                                              input (id `<run>/<test>`)
  klee_cases.py inputs <klee-cases.tsv>       one case line per distinct input up to the version
  klee_cases.py reps <runs dir> [exact|edges|coarse]
                                              one case line per path of each family (default:
                                              edge paths)
  klee_cases.py own <runs dir> <cap>          at most cap case lines of each run
  klee_cases.py versions <existing.tsv>       dumped suite cases (`--dump-cases`: id, gas, code,
                                              tokens) as case lines at every version 0..16, the
                                              cases of Tests.Gen.Klee left out
  klee_cases.py replaycheck <runs dir> <replay out>
                                              the case lines run back through `replay cases ALL`:
                                              each must take the path KLEE recorded
  klee_cases.py compare <runs dir> <existing-sigs.tsv> <out dir>
                                              per family, KLEE's paths (all its runs) against the
                                              steps of that family in every existing case:
                                              <out>/coverage.tsv and <out>/missed.tsv (one case
                                              per path no existing case takes: `C` lines for the
                                              coarse paths, `E` lines for exact edge paths whose
                                              coarse path is taken)
  klee_cases.py lean <tvm_spec_index.json> [--edges] <missed.tsv>...
                                              Tests/Harness/Gen/Klee.lean (stdout): one case per
                                              missed coarse path (`--edges`: and per missed edge
                                              path), each after the name of the suite of its opcode
"""
import json
import os
import sys

CLASSES = 'SGNC'


def runs_of(runs_dir):
    """The finished runs in runs_dir; with KLEE_RUNLIST (a file, a run a line), only those."""
    only = None
    if os.environ.get('KLEE_RUNLIST'):
        only = {l.strip() for l in open(os.environ['KLEE_RUNLIST']) if l.strip()}
    out = []
    for name in sorted(os.listdir(runs_dir)):
        if only is not None and name not in only:
            continue
        d = os.path.join(runs_dir, name)
        if '.' in name and name[-1] in CLASSES and os.path.isfile(os.path.join(d, 'done')):
            out.append(name)
    return out


def read_cases(path):
    rows = []
    for line in open(path):
        cols = line.rstrip('\n').split('\t')
        if len(cols) < 8 or cols[1] == 'ERROR':
            continue
        rows.append(cols)
    return rows


def test_id(run, ktest):
    return f'{run}/' + os.path.basename(ktest).replace('.ktest', '')


def lines(runs_dir):
    for run in runs_of(runs_dir):
        seen = set()
        for c in read_cases(os.path.join(runs_dir, run, 'cases.tsv')):
            key = tuple(c[4:8])
            if key in seen:
                continue
            seen.add(key)
            print(f'{test_id(run, c[0])}\t' + '\t'.join(c[4:8]))


def inputs(path):
    seen = set()
    for line in open(path):
        cols = line.rstrip('\n').split('\t')
        if len(cols) < 5:
            continue
        key = tuple(cols[2:5])
        if key in seen:
            continue
        seen.add(key)
        print(line, end='')


def reps(runs_dir, col):
    """One case line per path of each family (all its runs): col 1 exact, 2 edges, 3 coarse."""
    seen = set()
    for run in runs_of(runs_dir):
        for c in read_cases(os.path.join(runs_dir, run, 'cases.tsv')):
            key = (family(run), c[col])
            if key in seen:
                continue
            seen.add(key)
            print(f'{test_id(run, c[0])}\t' + '\t'.join(c[4:8]))


def own(runs_dir, cap):
    """At most `cap` case lines of each run, spread over it."""
    for run in runs_of(runs_dir):
        rows = read_cases(os.path.join(runs_dir, run, 'cases.tsv'))
        if len(rows) > cap:
            rows = [rows[i * len(rows) // cap] for i in range(cap)]
        for c in rows:
            print(f'{test_id(run, c[0])}\t' + '\t'.join(c[4:8]))


def versions(path):
    for line in open(path):
        line = line.rstrip('\n')
        if not line:
            continue
        cols = line.split('\t')
        if len(cols) < 4 or '/oracle/klee/' in cols[0]:
            continue
        cid, gas, code, toks = cols[0], cols[1], cols[2], cols[3]
        for v in range(17):
            print(f'{cid}@{v}\t{v}\t{gas}\t{code}\t{toks}')


def family(run):
    """The family a run's windows are tagged with (`replay cases ALL`): class C runs follow the
    control transfer (control windows, `<family>+`)."""
    name, cls = run.rsplit('.', 1)
    return name + ('+' if cls == 'C' else '')


def replaycheck(runs_dir, out_path):
    want = {}
    for run in runs_of(runs_dir):
        for c in read_cases(os.path.join(runs_dir, run, 'cases.tsv')):
            want[test_id(run, c[0])] = (family(run), ':'.join(c[1:4]))
    n = bad = 0
    for line in open(out_path):
        cols = line.rstrip('\n').split('\t')
        n += 1
        fam, sig = want.get(cols[0], (None, None))
        # any window of the family: a prelude (classes C and T) can hold the family's opcodes too
        got = [w.split(':', 1)[1] for w in cols[2].split(' ') if w.split(':', 1)[0] == fam] if len(cols) > 2 else []
        if cols[1] == 'ERROR' or sig is None or sig not in got:
            bad += 1
            if bad <= 20:
                print('MISMATCH', line.rstrip()[:300])
    print(f'replayed {n} case lines, {bad} not on the path KLEE recorded')


def info(runs_dir, run):
    d = {}
    for line in open(os.path.join(runs_dir, run, 'info.txt')):
        k, _, v = line.rstrip('\n').partition(' ')
        d.setdefault(k, v)
    return d


def compare(runs_dir, sigs_path, out):
    fams = {}  # family -> {'runs': [...], 'exact': set, 'edges': {sig: case}, 'coarse': {sig: case}}
    for run in runs_of(runs_dir):
        f = fams.setdefault(family(run), {'runs': [], 'exact': set(), 'edges': {}, 'coarse': {}, 'tests': 0,
                                           'secs': 0, 'fin': ''})
        inf = info(runs_dir, run)
        f['runs'].append(run[-1])
        f['fin'] += run[-1] + ('+' if inf.get('finished') == 'yes' else '-')
        f['secs'] += int(inf.get('seconds', '0') or 0)
        rows = read_cases(os.path.join(runs_dir, run, 'cases.tsv'))
        f['tests'] += len(rows)
        for c in rows:
            line = f'{test_id(run, c[0])}\t' + '\t'.join(c[4:8])
            f['exact'].add(c[1])
            f['edges'].setdefault(c[2], (line, c[3]))
            f['coarse'].setdefault(c[3], line)
    ex = {}  # family -> (exact, edges, coarse) sets
    n_runs = 0
    for line in open(sigs_path):
        cols = line.rstrip('\n').split('\t')
        if len(cols) < 3 or cols[1] == 'ERROR':
            continue
        n_runs += 1
        if cols[2] == '-':
            continue
        for w in cols[2].split(' '):
            fam, a, b, c = w.split(':')
            s = ex.setdefault(fam, (set(), set(), set()))
            s[0].add(a)
            s[1].add(b)
            s[2].add(c)
    cov = open(os.path.join(out, 'coverage.tsv'), 'w')
    cov.write('family\tclasses\tseconds\ttests\texact\tedges\tcoarse\tex_exact\tex_edges\tex_coarse\t'
              'reached_exact\treached_edges\treached_coarse\tmissed_edges\tmissed_coarse\n')
    mis = open(os.path.join(out, 'missed.tsv'), 'w')
    tot = [0] * 10
    for name in sorted(fams):
        f = fams[name]
        e = ex.get(name, (set(), set(), set()))
        r_exact = len(f['exact'] & e[0])
        r_edges = sum(1 for s in f['edges'] if s in e[1])
        r_coarse = sum(1 for s in f['coarse'] if s in e[2])
        m_coarse = [s for s in sorted(f['coarse']) if s not in e[2]]
        m_edges = [s for s in sorted(f['edges']) if s not in e[1]]
        for s in m_coarse:
            mis.write(f'C\t{f["coarse"][s]}\t{s}\n')
        for s in m_edges:
            line, coarse = f['edges'][s]
            if coarse in e[2]:
                mis.write(f'E\t{line}\t{s}\n')
        row = [len(f['exact']), len(f['edges']), len(f['coarse']), len(e[0]), len(e[1]), len(e[2]), r_exact,
               r_edges, r_coarse, len(m_edges), len(m_coarse)]
        cov.write(f'{name}\t{f["fin"]}\t{f["secs"]}\t{f["tests"]}\t' + '\t'.join(map(str, row)) + '\n')
        for i, v in enumerate([f['tests']] + row[:3] + row[6:]):
            if i < len(tot):
                tot[i] += v
    cov.close()
    mis.close()
    print(f'families {len(fams)} existing_runs {n_runs} tests {tot[0]} exact {tot[1]} edges {tot[2]} '
          f'coarse {tot[3]} reached_exact {tot[4]} reached_edges {tot[5]} reached_coarse {tot[6]} '
          f'missed_edges {tot[7]} missed_coarse {tot[8]}')


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


def lean(index_path, args):
    edges = '--edges' in args
    missed_paths = [a for a in args if a != '--edges']
    idx = json.load(open(index_path))
    rows = []
    for row in idx['tvm_instructions']:
        lay = row.get('layout') or {}
        # a row without a C++ implementation (EXTCALL) has no suite: its opcodes go with the gaps
        if lay.get('min') is not None and row.get('implementation'):
            rows.append((lay['min'], lay['max'], row['name']))
    out = []
    seen = set()
    for path in missed_paths:
        for line in open(path):
            line = line.rstrip('\n')
            if not line:
                continue
            cols = line.split('\t')
            kind, cols, sig = cols[0], cols[1:6], cols[6]
            if kind == 'E' and not edges:
                continue
            key = (family(cols[0].split('/')[0]), kind, sig)  # a path of a family, once
            if key in seen:
                continue
            seen.add(key)
            line = '\t'.join(cols)
            bits = boc_root_bits(cols[3])
            op = int((bits[:24] + '0' * 24)[:24], 2)
            names = [n for lo, hi, n in rows if lo <= op < hi]
            if not names:
                # an opcode no form has (a GAP_ family, or a form without a C++ implementation):
                # the suite of the row just below it
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
is an input on which C++ takes a path through the instruction (its handler-level path: the set of
block-to-block edges of the instruction's step outside the BigInt, bitstring, refcount and library
internals) that no other oracle or fuzz case of the suites takes, at any global version. Each runs
at every version like the suite's own cases.

`data` holds one case per line: `<suite> \t <case line of Tests.CaseFile>` (id, version found,
gas limit, code BOC, stack tokens). Generated, do not edit: `python3 tools/klee/klee_cases.py lean
docs/progress/tvm_spec_index.json <measure dir>/missed.tsv > Tests/Harness/Gen/Klee.lean`.
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
    elif cmd == 'lines':
        lines(sys.argv[2])
    elif cmd == 'inputs':
        inputs(sys.argv[2])
    elif cmd == 'reps':
        reps(sys.argv[2], {'exact': 1, 'edges': 2, 'coarse': 3}[sys.argv[3] if len(sys.argv) > 3 else 'edges'])
    elif cmd == 'own':
        own(sys.argv[2], int(sys.argv[3]))
    elif cmd == 'versions':
        versions(sys.argv[2])
    elif cmd == 'replaycheck':
        replaycheck(sys.argv[2], sys.argv[3])
    elif cmd == 'compare':
        compare(sys.argv[2], sys.argv[3], sys.argv[4])
    else:
        sys.exit(f'unknown command {cmd}')


if __name__ == '__main__':
    main()
