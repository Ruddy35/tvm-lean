#!/usr/bin/env python3
"""The family table of the KLEE harness (tools/klee/harness/harness.cpp), generated from
docs/progress/tvm_spec_index.json: one family per instruction form, plus one per opcode range that
no form has (the handlers' and the dispatch's invalid-opcode paths).

  gen_families.py <tvm_spec_index.json> <out families.inc>   the C++ table (build.sh)
  gen_families.py <tvm_spec_index.json> --list               the table as text (one family a line)
  gen_families.py <tvm_spec_index.json> --runs [classes] [--part=k/n]
                                                             the KLEE runs, `<family>.<class>`

A family gives the harness:
  * the code alternatives: every opcode of the form with its immediate arguments, each argument
    over all its values (4 bits or fewer) or the values at its bounds; for forms with inline data
    or references (PUSHSLICE, PUSHCONT, PUSHINT_LONG, PUSHREF, DICTPUSHCONST, ...) the data and
    references the arguments ask for, plus a variant that lacks a data bit or a reference; and the
    opcode cut by its last bit (the "too short" path of the dispatch). Each alternative is a
    concrete code cell (a symbolic opcode bit makes the dispatch's table lookup a symbolic read);
  * the stack: one slot per input of the form's stack signature (top first), its entry types (the
    declared ones and one wrong one, for the type check), and for integers a role that picks the
    values (harness.cpp `Role`): arithmetic values (symbolic, any width), keys, small values,
    bit widths, stack/tuple indices and counts, reference counts, numbers with range checks, shift
    amounts. Roles come from the slot's name and the form's category, with overrides by handler;
  * the stack depths: every depth up to the signature's inputs, and around the stack positions the
    immediate arguments and index slots can name.

Classes (the run's name suffix): S = gas limit symbolic 0..kSmallGasMax, no NaN; G = 10^6, no
NaN; N = 10^6 with at least one NaN integer (families with integer slots only).

Forms not in the table (`--list` says why): those of tonops.cpp (not compiled into the bitcode,
`build.sh`), and forms whose layout or signature this script does not understand.
"""
import itertools
import json
import sys

# entry kinds (harness.cpp `Kind`)
K_INT, K_NULL, K_CELL, K_SLICE, K_BUILDER, K_TUPLE, K_CONT, K_DICT = 1, 2, 4, 8, 16, 32, 64, 128
# integer roles (harness.cpp `Role`)
ROLES = ['ARITH', 'KEY', 'SMALL', 'WIDTH', 'INDEX', 'REFS', 'NUM', 'SHIFT', 'NONE']

MAX_CODE = 384  # code alternatives per family (sampled down beyond this)


def die(msg):
    sys.exit(f'gen_families: {msg}')


def irange(a):
    r = a.get('range')
    if not r:
        return None
    return int(r['min']), int(r['max'])


# ------------------------------------------------------------------------------- opcode fields
def fields_of(arg):
    """The fixed-length fields an argument has in the opcode (after the prefix), in order:
    (kind, bits, value range or None). Inline data and references are the arg's tail."""
    t = arg['$']
    if t in ('uint', 'int', 'stack'):
        return [(t, arg['len'], irange(arg))]
    if t == 'delta':
        inner = arg['arg']
        return [(inner['$'], inner['len'], irange(inner))]
    if t in ('tinyInt', 'control'):
        return [('raw', 4, None)]
    if t == 'plduzArg':
        return [('raw', 3, None)]
    if t in ('s1', 'minusOne', 'refCodeSlice', 'dict'):
        return []
    if t == 'slice':
        out = []
        for sub in ('refs', 'bits'):
            f = arg[sub]
            if f['$'] == 'delta':
                f = f['arg']
            if f['len']:
                out.append(('uint', f['len'], irange(f)))
        return out
    if t == 'codeSlice':
        return [('uint', arg['refs']['len'], None), ('uint', arg['bits']['len'], None)]
    if t == 'inlineCodeSlice':
        return [('uint', arg['bits']['len'], None)]
    if t == 'debugstr':
        return [('uint', 4, None)]
    if t == 'largeInt':
        return [('uint', 5, None)]
    raise KeyError(t)


def field_samples(kind, bits, rng, stackish):
    """Values of one field (as unsigned bit patterns): all of them up to 4 bits, else the ones at
    the bounds."""
    n = 1 << bits
    if bits <= 4:
        vals = list(range(n))
    elif kind == 'int':
        lo, hi = -(n >> 1), (n >> 1) - 1
        vals = sorted({lo, lo + 1, -129, -128, -2, -1, 0, 1, 2, 127, 128, hi - 1, hi} & set(range(lo, hi + 1)))
        if rng:
            vals = [v for v in vals if rng[0] <= v <= rng[1]]
        return [v & (n - 1) for v in vals]
    else:
        base = {0, 1, 2, 3, n - 2, n - 1}
        if stackish:
            base |= {14, 15, 16, 17}
        else:
            base |= {7, 8, 15, 16, 63, 64, 127, 128, 255, 256, n // 2 - 1, n // 2}
        vals = sorted(v for v in base if 0 <= v < n)
    if rng:
        vals = [v for v in vals if rng[0] <= v <= rng[1]] or vals[:1]
    return vals


def bits_of(v, n):
    return format(v, f'0{n}b') if n else ''


PATTERN = '1101001011100101' * 80


def tails(arg, fieldvals, form):
    """The tails (data bits, reference kinds) an argument with these field values needs, each with
    a flag saying it is the deliberately incomplete variant."""
    t = arg['$']
    if t == 'refCodeSlice':
        return [('', 'c', False)]
    if t == 'dict':
        return [('', 'p' if form['name'] == 'PFXDICTSWITCH' else 'd', False)]
    if t == 'slice':
        vals = list(fieldvals)
        rf = arg['refs']
        r = vals.pop(0) if (rf['arg'] if rf['$'] == 'delta' else rf)['len'] else 0
        if rf['$'] == 'delta':
            r += rf['delta']
        b = vals.pop(0)
        n = 8 * b + arg.get('pad', 0)
        out = []
        if n:
            out.append((PATTERN[:n - 1] + '1', 'e' * r, False))  # completion tag at the end
            out.append(('0' * n, 'e' * r, False))  # no completion tag
            out.append((PATTERN[:n - 1], 'e' * r, True))  # a data bit short
        else:
            out.append(('', 'e' * r, False))
        if r:
            out.append((PATTERN[:n - 1] + '1' if n else '', 'e' * (r - 1), True))  # a reference short
        return out
    if t in ('codeSlice', 'inlineCodeSlice'):
        vals = list(fieldvals)
        r = vals.pop(0) if t == 'codeSlice' else 0
        n = 8 * vals.pop(0)
        out = [(PATTERN[:n], 'c' * r, False)]
        if n:
            out.append((PATTERN[:n - 1], 'c' * r, True))
        if r:
            out.append((PATTERN[:n], 'c' * (r - 1), True))
        return out
    if t == 'debugstr':
        n = 8 * fieldvals[0] + 8
        return [(PATTERN[:n], '', False), (PATTERN[:n - 1], '', True)]
    if t == 'largeInt':
        w = 8 * fieldvals[0] + 19
        out = []
        for v in (0, -1, 1, (1 << (w - 1)) - 1, -(1 << (w - 1))):
            out.append((bits_of(v & ((1 << w) - 1), w), '', False))
        out.append((bits_of(1, w)[:-1], '', True))
        return out
    return [('', '', False)]


def code_alts(form):
    lay = form['layout']
    L, P = lay['skipLen'], lay['checkLen']
    lo, hi = lay['min'], lay['max']
    args = lay['args']
    flds = []  # (arg index, field)
    for i, a in enumerate(args):
        for f in fields_of(a):
            flds.append((i, f))
    if P + sum(f[1] for _, f in flds) != L:
        raise ValueError(f'fields {sum(f[1] for _, f in flds)} + prefix {P} != {L}')
    prefix = lo >> (24 - P) if P <= 24 else None
    if prefix is None:
        raise ValueError('prefix longer than 24 bits')
    stackish = any(f[0] == 'stack' for _, f in flds)
    samples = [field_samples(f[0], f[1], f[2], stackish) for _, f in flds]
    # sample down until the product is small
    while True:
        total = 1
        for s in samples:
            total *= len(s)
        if total <= MAX_CODE:
            break
        k = max(range(len(samples)), key=lambda i: len(samples[i]))
        s = samples[k]
        samples[k] = sorted(set(s[:2] + s[-2:] + [s[len(s) // 2]])) if len(s) > 5 else s[:len(s) - 1]
    combos = list(itertools.product(*samples))
    # the instances at the bounds of the opcode range itself (fixed-range forms: the samples of
    # the fields can all lie outside it)
    if L <= 24 and flds:
        ilo, ihi = lo >> (24 - L), (hi + (1 << (24 - L)) - 1) >> (24 - L)
        for v in sorted({ilo, ilo + 1, ilo + 2, (ilo + ihi) // 2, ihi - 2, ihi - 1} & set(range(ilo, ihi))):
            b = bits_of(v, L)[P:]
            combo, pos = [], 0
            for _, f in flds:
                combo.append(int(b[pos:pos + f[1]], 2))
                pos += f[1]
            combos.append(tuple(combo))
    alts = []
    for combo in combos:
        bits = bits_of(prefix, P) + ''.join(bits_of(v, f[1]) for v, (_, f) in zip(combo, flds))
        v24 = int((bits + '0' * 24)[:24], 2)
        if not lo <= v24 < hi:
            continue
        # the tails, argument by argument
        per_arg = []
        for i, a in enumerate(args):
            fv = [v for v, (j, _) in zip(combo, flds) if j == i]
            per_arg.append(tails(a, fv, form))
        complete = []
        for parts in itertools.product(*per_arg):
            short = sum(1 for p in parts if p[2])
            if short > 1:
                continue
            code = (bits + ''.join(p[0] for p in parts), ''.join(p[1] for p in parts))
            if len(code[0]) <= 1023 and len(code[1]) <= 4:  # what fits in one cell
                complete.append(code)
        alts.extend(complete)
    if not alts:
        raise ValueError('no opcode in range')
    # the opcode cut by its last bit, if the dispatch still finds this instruction for it
    first = alts[0][0][:L]
    cut = first[:-1]
    if cut and lo <= int((cut + '0' * 24)[:24], 2) < hi:
        alts.append((cut, ''))
    seen = set()
    out = []
    for a in alts:
        if a not in seen:
            seen.add(a)
            out.append(a)
    if len(out) > 4 * MAX_CODE:
        step = len(out) / (4 * MAX_CODE)
        out = [out[int(i * step)] for i in range(4 * MAX_CODE)] + [out[-1]]
    return out


# ------------------------------------------------------------------------------- stack slots
def parse_inputs(sig):
    """The input entries of a stack signature, bottom first: (name, type) or ('...', name)."""
    if sig is None:
        return []
    inp = sig.split('->')[0].strip()
    if inp in ('∅', ''):
        return []
    out = []
    for tok in inp.split():
        if '...' in tok:
            out.append(('...', tok))
        elif ':' in tok:
            n, ty = tok.split(':', 1)
            out.append((n, ty))
        else:
            raise ValueError(f'bad token {tok}')
    return out


# role by handler (layout exec, up to the first '(' or the function name) and slot name
ROLE_BY_EXEC = {
    ('exec_builder_chk_bits', 'x'): 'WIDTH', ('exec_builder_chk_bits_refs', 'x'): 'WIDTH',
    ('exec_builder_chk_bits_refs', 'y'): 'REFS', ('exec_builder_chk_bits', 'y'): 'REFS',
    ('exec_store_same', 'n'): 'WIDTH', ('exec_store_same', 'x'): 'SMALL',
    ('exec_load_same', 'x'): 'SMALL', ('exec_store_end_cell_special', 'x'): 'SMALL',
    ('exec_store_zeroes', 'n'): 'WIDTH', ('exec_store_ones', 'n'): 'WIDTH',
    ('exec_if_bit_jmp', 'x'): 'ARITH',
}
TYPE_KINDS = {
    'Int': K_INT, 'Cell': K_CELL, 'Slice': K_SLICE, 'Builder': K_BUILDER, 'Tuple': K_TUPLE,
    'Continuation': K_CONT, 'Null': K_NULL, 'Bool': K_INT,
}


def exec_name(form):
    e = form['layout']['exec']
    impl = form.get('implementation') or {}
    fn = impl.get('function_name') or ''
    if '=>' in e:
        e = e.split('=>', 1)[1].strip()
    return fn or e.split('(')[0].strip()


def int_role(form, name, top_int, shift_top):
    cat = form['category']
    ex = exec_name(form)
    if (ex, name) in ROLE_BY_EXEC:
        return ROLE_BY_EXEC[(ex, name)]
    if shift_top and top_int:
        return 'SHIFT'
    if cat == 'arithmetic':
        if name == 'width':
            return 'WIDTH'
        return 'ARITH'
    if name == 'cond':
        return 'SMALL'
    if name in ('width', 'length', 'offset', 'skip_len', 'l', 'bits') and cat != 'crypto':
        return 'WIDTH'
    if name in ('refs', 'skip_refs') or (name in ('r', 'y') and cat == 'cell'):
        return 'REFS'
    if cat == 'dictionary':
        if name == 'n':
            return 'WIDTH'
        return 'KEY'
    if name == 'n' and cat == 'cell':
        return 'INDEX'
    if name in ('i', 'j', 'k', 'n', 'p', 'r', 'length') and cat in (
            'stack', 'tuple', 'globals', 'continuation', 'cell', 'config', 'crypto', 'misc'):
        return 'INDEX'
    if name in ('num', 'mode', 'flags', 'mask', 'is_mc', 'seconds', 'cells', 'gas_used', 'fwd_fee', 'amount'):
        return 'NUM'
    if cat in ('exception', 'stack', 'continuation', 'tuple'):
        return 'SMALL'
    return 'ARITH'


def slots_of(form):
    ins = parse_inputs(form['signature_stack_string'])
    # a shift amount from the stack: the top integer of the a9xx shift/divide family and of
    # LSHIFT/RSHIFT with no immediate shift
    name = form['name']
    shift_top = form['category'] == 'arithmetic' and '#' not in name and (
        'SHIFT' in name or 'POW2' in name and name not in ('POW2', 'QPOW2', 'PUSHPOW2', 'PUSHPOW2DEC', 'PUSHNEGPOW2'))
    if name in ('POW2', 'QPOW2'):
        shift_top = True
    variadic = any(n == '...' for n, _ in ins)
    slots = []  # top first
    first_int = True
    for n, ty in reversed(ins):
        if n == '...':
            break  # entries below a variadic run are concrete
        kinds = 0
        alts = ty.split('|')
        for t in alts:
            if t == 'Any':
                kinds |= K_INT | K_NULL
            elif t == 'Cell' and n == 'D':
                kinds |= K_DICT
            else:
                kinds |= TYPE_KINDS[t]
        # one wrong type, for the handler's type check
        if 'Any' not in alts:
            kinds |= K_INT if (kinds & K_NULL or kinds == K_NULL) else K_NULL
        role = 'NONE'
        if kinds & K_INT:
            if 'Any' in alts or 'Int' not in alts and 'Bool' not in alts:
                role = 'SMALL'
            else:
                role = int_role(form, n, first_int, shift_top)
                first_int = False
        slots.append((kinds, role, n))
    return slots, variadic


def depths_of(form, slots, variadic, alts):
    ns = len(slots)
    d = set(range(0, ns + 2))
    lay = form['layout']
    has_stack_arg = any(f[0] == 'stack' for a in lay['args'] for f in fields_of(a)) or form['signature_stack_string'] is None
    wide = any(f[0] in ('stack', 'uint') and f[1] == 8 for a in lay['args'] for f in fields_of(a))
    has_index = any(r == 'INDEX' for _, r, _ in slots)
    if has_stack_arg or variadic or has_index or form['category'] in ('stack', 'tuple'):
        d |= {2, 3, 4, 5, 14, 15, 16, 17, 18}
    if (has_stack_arg and wide) or (has_index and form['category'] == 'stack'):
        d |= {254, 255, 256, 257}
    return sorted(d)


# ------------------------------------------------------------------------------- the table
def load(index_path):
    idx = json.load(open(index_path))
    fams, skipped = [], []
    for form in idx['tvm_instructions']:
        impl = form.get('implementation') or {}
        name = form['name']
        if impl.get('file_path') == 'crypto/vm/tonops.cpp':
            skipped.append((name, 'tonops.cpp: not in the bitcode (register_ton_ops is a stub)'))
            continue
        try:
            alts = code_alts(form)
            slots, variadic = slots_of(form)
        except (ValueError, KeyError) as e:
            skipped.append((name, f'layout or signature not understood: {e}'))
            continue
        lay = form['layout']
        fams.append({
            'name': name, 'lo': lay['min'], 'hi': lay['max'], 'alts': alts, 'slots': slots,
            'depths': depths_of(form, slots, variadic, alts), 'category': form['category'],
            'file': impl.get('file_path') or '-', 'exec': exec_name(form),
        })
    # opcode ranges no form has: the dispatch's invalid opcodes and the handlers' invalid
    # argument combinations (24-bit ranges, the tonops ranges included as covered)
    ranges = sorted((f['layout']['min'], f['layout']['max'], f['name']) for f in idx['tvm_instructions'])
    for (a, b, n1), (c, _, n2) in zip(ranges, ranges[1:]):
        if c < b:
            die(f'opcode ranges overlap: {n1} {a:06x}-{b:06x} and {n2} from {c:06x}')
    gaps = []
    pos = 0
    for a, b, _ in ranges + [(1 << 24, 1 << 24, None)]:
        if a > pos:
            gaps.append((pos, a))
        pos = max(pos, b)
    for a, b in gaps:
        vals = sorted({a, a + 1, (a + b) // 2, b - 2, b - 1} & set(range(a, b)))
        alts = []
        for v in vals:
            bits = bits_of(v, 24).rstrip('0')
            nb = max(8, (len(bits) + 7) // 8 * 8)
            alts.append((bits_of(v, 24)[:nb], ''))
        seen = set()
        alts = [x for x in alts if not (x in seen or seen.add(x))]
        fams.append({
            'name': f'GAP_{a:06X}', 'lo': a, 'hi': b, 'alts': alts, 'slots': [],
            'depths': [0, 3], 'category': 'gap', 'file': '-', 'exec': '-',
        })
    return fams, skipped


def classes_of(f):
    out = ['S', 'G']
    if any(k & K_INT and r not in ('NONE',) for k, r, _ in f['slots']):
        out.append('N')
    return out


def cxx(fams):
    o = ['// generated by tools/klee/gen_families.py from docs/progress/tvm_spec_index.json: do not edit',
         f'// {len(fams)} families']
    for i, f in enumerate(fams):
        o.append(f'static const CodeAlt kCode{i}[] = {{')
        for bits, refs in f['alts']:
            nb = len(bits)
            h = format(int(bits + '0' * ((-nb) % 8), 2), f'0{(nb + 7) // 8 * 2}x') if nb else ''
            o.append(f'    {{"{h}", {nb}, "{refs}"}},')
        o.append('};')
        if f['slots']:
            o.append(f'static const SlotDesc kSlots{i}[] = {{' +
                     ', '.join(f'{{{k}, R_{r}}}' for k, r, _ in f['slots']) + '};')
        o.append(f'static const int kDepths{i}[] = {{' + ', '.join(map(str, f['depths'])) + '};')
    o.append('static const FormSpec kForms[] = {')
    for i, f in enumerate(fams):
        sl = f'kSlots{i}' if f['slots'] else 'nullptr'
        o.append(f'    {{"{f["name"]}", 0x{f["lo"]:06x}, 0x{f["hi"]:06x}, kCode{i}, {len(f["alts"])}, {sl}, '
                 f'{len(f["slots"])}, kDepths{i}, {len(f["depths"])}}},')
    o.append('};')
    return '\n'.join(o) + '\n'


def main():
    if len(sys.argv) < 3:
        die('usage: gen_families.py <tvm_spec_index.json> <out.inc> | --list | --runs [classes]')
    fams, skipped = load(sys.argv[1])
    if sys.argv[2] == '--list':
        for f in fams:
            sl = ' '.join(f'{n}:{k}:{r}' for k, r, n in f['slots']) or '-'
            print(f"{f['name']}\t{f['category']}\t{f['lo']:06x}-{f['hi']:06x}\tcode={len(f['alts'])}\t"
                  f"depths={','.join(map(str, f['depths']))}\tslots={sl}\tclasses={''.join(classes_of(f))}")
        for n, why in skipped:
            print(f'{n}\tNOT COVERED\t{why}')
        return
    if sys.argv[2] == '--runs':
        # costliest families first (stack slots, then code alternatives), so that a parallel batch
        # does not end on a long run; --part k/n: every n-th family from the k-th (all its classes)
        want, part = 'SGN', None
        for a in sys.argv[3:]:
            if a.startswith('--part='):
                k, n = a.split('=')[1].split('/')
                part = (int(k), int(n))
            else:
                want = a
        order = sorted(fams, key=lambda f: (-len(f['slots']), -len(f['alts']), f['name']))
        for i, f in enumerate(order):
            if part and i % part[1] != part[0] - 1:
                continue
            for c in classes_of(f):
                if c in want:
                    print(f"{f['name']}.{c}")
        return
    with open(sys.argv[2], 'w') as out:
        out.write(cxx(fams))
    print(f'gen_families: {len(fams)} families, {len(skipped)} forms not covered', file=sys.stderr)


if __name__ == '__main__':
    main()
