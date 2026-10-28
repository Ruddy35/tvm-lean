#!/usr/bin/env python3
"""spec-coverage: which instructions and control-flow patterns symbolic execution runs.

    spec_coverage.py inventory [--deep] [--jobs N] [--save] [--md docs/audit/spec-coverage.md]
                               [--raw FILE | --from-raw FILE] [--no-build] [--wrap CMD]
    spec_coverage.py patterns [--regen] [--jobs N] [--only P,..] [--timeout S] [--save]
                              [--raw FILE | --from-raw FILE] [--no-build] [--wrap CMD]
    spec_coverage.py precheck [<code> ...] [--save] [--raw FILE | --from-raw FILE] [--no-build]

`inventory`: every instruction form of the decoder (the 919 forms of the C++ dispatch table, one
test suite each: `third_party/tvm-specification/tvm-specification.json`, its 24-bit opcode ranges,
without `EXTCALL`, which the reference does not have, and with `GETEXTRABALANCE`, which the
snapshot lacks), sampled over its arguments (every argument value when there are at most 256, else
64 spread over the range), each sample decoded by the model's decoder and classified by
`tools/spec-coverage/SpecCoverage.lean` in the environment of the proof tools: the `vm_spec` lemmas
whose instruction unifies with it (as `vm_step`'s `applySpec` tries them,
TvmLean/Proofs/Exec/Tactic.lean), else its handler analysed (the VM programs it runs computed by a
`vm_run` lemma, unfolded, or blocking); with `--deep`, the first sample of each form also run on a
symbolic stack of its signature (by a lemma only, and by the handler: `vm_simp`). Two passes: in
contract-check's environment (`TvmLean.Proofs.Check.Tactic`: what a proof gets) and in the
library's (every module of TvmLean/Proofs/Exec/: the lemmas contract-check does not import yet).
Writes the table per family (`--md`), the result per form (`--save`: forms.json, which `precheck`
reads) and the raw lines (`--raw`).

`precheck`: the code of a contract (a BOC file, or a source of `tools/boc2lean`:
`list:tools/txoracle/contracts.txt#wallet3.code`, `file:...`, `b64:...`, `hex:...`), every code cell
reachable from it walked (implicit `JMPREF`, `PUSHCONT`, `CALLREF`, `IF*REF`, the procedures of
`DICTPUSHCONST`) and each instruction classified the same way: what of this code symbolic execution
does not cover, and the control-flow patterns it uses with their status (`patterns`), before a proof
starts. `tools/contract-check/contract-check <code> --precheck` runs it.

`patterns`: the control-flow patterns and whether `vm_run`/`ran_case` handle them: each pattern
tried by small codes (probes.fif, assembled by the reference's Fift into probes.txt with `--regen`),
each run by `ran_case` from an external message with the invariant `True`; a pattern is handled when
every path of its probes reaches its end (`--save`: probe-results.json).

The Lean side needs the modules of TvmLean/Proofs/Exec/ and TvmLean.Proofs.Check.Tactic built; the
script builds them first (`lake build`, skipped with `--no-build`). `LEAN_NUM_THREADS` and a
command prefix (`--wrap`, e.g. a memory cap) apply as in `tools/contract-check`.
"""

from __future__ import annotations

import argparse
import collections
import json
import os
import re
import shutil
import signal
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parent.parent
SPEC_JSON = REPO / "third_party" / "tvm-specification" / "tvm-specification.json"
LEAN_SCRIPT = HERE / "SpecCoverage.lean"
sys.path.insert(0, str(REPO / "tools" / "boc2lean"))

# the families of the report: (category, sub_category) of the specification snapshot
FAMILIES = ["stack", "arith", "cell", "cont/flow", "loops", "exceptions", "dict", "tuple",
            "msg/actions", "tonenv/c7", "crypto", "debug", "misc"]


def family_of(cat: str, sub: str) -> str:
    if cat == "continuation" and sub == "continuation_cond_loop":
        return "loops"
    return {
        "stack": "stack", "arithmetic": "arith", "cell": "cell", "continuation": "cont/flow",
        "codepage": "cont/flow", "exception": "exceptions", "dictionary": "dict", "tuple": "tuple",
        "message": "msg/actions", "address": "msg/actions", "config": "tonenv/c7",
        "globals": "tonenv/c7", "prng": "tonenv/c7", "basic_gas": "tonenv/c7", "crypto": "crypto",
        "debug": "debug", "misc": "misc",
    }[cat]


# ------------------------------------------------------------------------------------------------
# The instruction forms


def load_forms() -> list[dict]:
    """The forms of the reference's dispatch table, with their 24-bit opcode ranges."""
    data = json.loads(SPEC_JSON.read_text())
    forms = []
    for ins in data["instructions"]:
        if ins["name"] == "EXTCALL":
            continue  # not in the reference (docs/audit/README.md, section 2)
        lay = ins["layout"]
        forms.append({
            "name": ins["name"], "family": family_of(ins["category"], ins["sub_category"]),
            "min": lay["min"], "max": lay["max"], "check": lay["checkLen"], "skip": lay["skipLen"],
            "exec": lay.get("exec", ""), "tlb": lay.get("tlb", ""),
        })
    if not any(f["name"] == "GETEXTRABALANCE" for f in forms):
        # mksimple(0xf880, 16, "GETEXTRABALANCE", ...)->require_version(10), tonops.cpp:500
        forms.append({"name": "GETEXTRABALANCE", "family": "tonenv/c7", "min": 0xF88000,
                      "max": 0xF88100, "check": 16, "skip": 16, "exec": "exec_get_extra_currency_balance",
                      "tlb": "#f880"})
    return forms


def form_samples(f: dict) -> list[int]:
    """24-bit opcodes of the form: every argument value if at most 256, else 64 spread out."""
    lo, hi, skip = f["min"], f["max"], f["skip"]
    step = 1 << (24 - skip) if skip <= 24 else 1
    n = max(1, (hi - lo + step - 1) // step)
    if n <= 256:
        vals = [lo + k * step for k in range(n)]
    else:
        vals = sorted({lo + (k * (n - 1) // 63) * step for k in range(64)})
    return [v for v in vals if lo <= v < hi]


def form_of_op(forms: list[dict], op: int) -> dict | None:
    for f in forms:
        if f["min"] <= op < f["max"]:
            return f
    return None


# ------------------------------------------------------------------------------------------------
# The Lean side


def exec_modules() -> list[str]:
    """The modules of symbolic execution (TvmLean/Proofs/Exec/ but the pilots) and the tactic of
    tools/contract-check."""
    mods = ["TvmLean.Proofs.Check.Tactic"]
    root = REPO / "TvmLean" / "Proofs" / "Exec"
    for p in sorted(root.rglob("*.lean")):
        rel = p.relative_to(REPO).with_suffix("")
        if "Pilot" in rel.parts:
            continue
        mods.append(".".join(rel.parts))
    return mods


def write_script(mods: list[str], path: Path) -> None:
    """A copy of SpecCoverage.lean importing `mods`."""
    text = LEAN_SCRIPT.read_text()
    begin = text.index("-- BEGIN IMPORTS")
    end = text.index("-- END IMPORTS")
    head_end = text.index("\n", begin)
    header_comment = text[begin:text.index("import", head_end)]
    block = header_comment + "".join(f"import {m}\n" for m in mods)
    path.write_text(text[:begin] + block + text[end:])


def lake() -> str:
    return shutil.which("lake") or str(Path.home() / ".elan" / "bin" / "lake")


def _big_stack() -> None:
    """The child's stack unlimited where allowed (simp recurses deeply on some handlers)."""
    import resource
    try:
        resource.setrlimit(resource.RLIMIT_STACK, (resource.RLIM_INFINITY, resource.RLIM_INFINITY))
    except (ValueError, OSError):
        pass


def _run_part(script: Path, mode: str, lines: list[str], tmp: Path, tag: str, env: dict,
              prefix: list[str]) -> list[str]:
    """SpecCoverage.lean on `lines`; a process that dies (a stack overflow in `simp`) is run again
    on the lines after the one it died on, which gets a `CRASH` line."""
    out: list[str] = []
    remaining = lines
    first = True
    for attempt in range(10000):
        if not remaining:
            break
        pin = tmp / f"in-{tag}-{attempt}.txt"
        pout = tmp / f"out-{tag}-{attempt}.tsv"
        pin.write_text("\n".join(remaining) + "\n")
        e = dict(env, SPEC_COVERAGE_MODE=mode, SPEC_COVERAGE_IN=str(pin), SPEC_COVERAGE_OUT=str(pout))
        proc = subprocess.run(prefix + [lake(), "env", "lean", "--tstack=262144", str(script)], cwd=REPO,
                              env=e, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
                              preexec_fn=_big_stack)
        got = pout.read_text().splitlines() if pout.exists() else []
        if not first:
            got = [l for l in got if not l.startswith(("HEADS\t", "SPEC\t"))]
        if got and got[-1] == "END":
            out += got[:-1]
            break
        if not any(l.startswith("SAMPLE\t") or l.startswith("HEADS\t") for l in got) and proc.returncode != 0 \
                and "Stack overflow" not in proc.stdout and "error" in proc.stdout:
            sys.stderr.write(proc.stdout[-6000:])
            raise SystemExit("spec-coverage: the Lean side failed")
        out += got
        first = False
        # the line it died on: the first whose SAMPLE (or, with `d=`, DEEP) line is missing
        done_s = {tuple(l.split("\t")[1:3]) for l in got if l.startswith("SAMPLE\t")}
        done_d = {tuple(l.split("\t")[1:3]) for l in got if l.startswith("DEEP\t")}
        idx = len(remaining)
        for k, l in enumerate(remaining):
            parts = l.split()
            key = (parts[0], parts[1])
            if key not in done_s or (any(p.startswith("d=") for p in parts) and key not in done_d):
                idx = k
                break
        if idx == len(remaining):
            break
        parts = remaining[idx].split()
        stage = "sample" if (parts[0], parts[1]) not in done_s else "deep"
        out.append("\t".join(["CRASH", parts[0], parts[1], stage]))
        remaining = remaining[idx + 1:]
    return out


# The two environments: contract-check's (what a module of tools/contract-check imports: the lemmas
# that fire there, its vm_run set, the deep check) and the library's (every module of
# TvmLean/Proofs/Exec: the vm_spec lemmas a contract-check run would get by importing them).
ENV_CHECK = ["TvmLean.Proofs.Check.Tactic"]


def run_lean(mode: str, inp: Path, out: Path, build: bool, wrap: str, jobs: int = 1,
             mods: list[str] | None = None, extra_env: dict | None = None) -> None:
    """Runs SpecCoverage.lean importing `mods` (default: the library's modules) on the lines of
    `inp` (in `jobs` processes, each on a part of the lines, a form's lines kept together), its
    output in `out`."""
    import concurrent.futures
    mods = mods or exec_modules()
    prefix = wrap.split() if wrap else []
    env = dict(os.environ)
    env.setdefault("LEAN_NUM_THREADS", "2")
    env.update(extra_env or {})
    if build:
        r = subprocess.run(prefix + [lake(), "build"] + mods, cwd=REPO, env=env)
        if r.returncode != 0:
            raise SystemExit("spec-coverage: lake build of the modules of symbolic execution failed")
    with tempfile.TemporaryDirectory(prefix="spec-coverage-") as tmpd:
        tmp = Path(tmpd)
        script = tmp / "SpecCoverage.lean"
        write_script(mods, script)
        lines = inp.read_text().splitlines()
        groups: list[list[str]] = []
        for l in lines:
            key = l.split(" ")[0]
            if groups and groups[-1][0].split(" ")[0] == key:
                groups[-1].append(l)
            else:
                groups.append([l])
        jobs = max(1, min(jobs, len(groups)))
        parts = [[l for g in groups[k::jobs] for l in g] for k in range(jobs)]
        with concurrent.futures.ThreadPoolExecutor(max_workers=jobs) as ex:
            futs = [ex.submit(_run_part, script, mode, part, tmp, str(k), env, prefix)
                    for k, part in enumerate(parts)]
            results = [f.result() for f in futs]
        texts = []
        for k, res in enumerate(results):
            if k > 0:  # the listing of the lemmas once
                res = [l for l in res if not l.startswith(("HEADS\t", "SPEC\t"))]
            texts += res
        out.write_text("\n".join(texts) + "\n")


def merge_lib(check_out: Path, lib_out: Path, out: Path) -> None:
    """The output of the pass in contract-check's environment with the lemmas only the library has
    (the column of `SAMPLE` and `INSTR` lines) and the listing of every lemma from the library's."""
    lib_lines = lib_out.read_text().splitlines()
    lib_sl = {}
    for l in lib_lines:
        p = l.split("\t")
        if p[0] in ("SAMPLE", "INSTR") and len(p) > 7:
            lib_sl[(p[0], p[1], p[2])] = p[7]
    res = [l for l in lib_lines if l.startswith("SPEC\t")]
    for l in check_out.read_text().splitlines():
        p = l.split("\t")
        if p[0] == "SPEC":
            continue
        if p[0] in ("SAMPLE", "INSTR") and len(p) > 7:
            p[7] = lib_sl.get((p[0], p[1], p[2]), "")
        res.append("\t".join(p))
    out.write_text("\n".join(res) + "\n")


def json_lines(records: list[dict]) -> str:
    """A JSON array with one record a line (the generated files diff by record)."""
    return "[\n" + ",\n".join(json.dumps(r, ensure_ascii=False) for r in records) + "\n]\n"


def parse_raw(path: Path) -> dict:
    """The lines of SpecCoverage.lean's output, by kind."""
    out = collections.defaultdict(list)
    for line in path.read_text().splitlines():
        if not line:
            continue
        parts = line.split("\t")
        out[parts[0]].append(parts[1:])
    return out


def split_list(s: str) -> list[str]:
    return [x for x in s.split(";") if x] if s else []


# ------------------------------------------------------------------------------------------------
# Inventory


SIG_LETTER = {"Int": "I", "Bool": "I", "Slice": "S", "Cell": "C", "Builder": "B", "Continuation": "K",
              "Tuple": "T", "Null": "N", "Any": "A"}


def signature(name: str, data: dict) -> str:
    """The input stack of a form from the specification snapshot, bottom first, one letter an
    entry (`I` integer, `S` slice, `C` cell, `B` builder, `K` plain continuation, `T` tuple, `N`
    null, `A` any value; an array of values: three `A`); unknown: four `A`."""
    ins = data.get(name, {}).get("signature", {}).get("inputs", {}).get("stack")
    if ins is None:
        return "AAAA"
    out = ""
    for x in ins:
        if x.get("type") == "array":
            out += "AAA"
            continue
        types = x.get("value_types") or ([x["value_type"]] if x.get("value_type") else [])
        types = [t for t in types if t != "Null"] or types
        out += SIG_LETTER.get(types[0], "A") if types else "A"
    return out


def write_samples(forms: list[dict], path: Path, deep: bool, handler: bool = True) -> None:
    """The input of the Lean side: `<form> <opcode> [h] [d=<signature>]`, the handler analysed on
    the first, middle and last sample of each form, the deep check (`deep`) on the first."""
    data = {i["name"]: i for i in json.loads(SPEC_JSON.read_text())["instructions"]}
    lines = []
    for f in forms:
        vals = form_samples(f)
        marks = {0, len(vals) // 2, len(vals) - 1}
        for k, v in enumerate(vals):
            extra = (" h" if handler and k in marks else "") + (f" d={signature(f['name'], data)}" if deep and k == 0 else "")
            lines.append(f"{f['name']} {v:06x}" + extra)
    path.write_text("\n".join(lines) + "\n")


def cmd_inventory(args: argparse.Namespace) -> None:
    forms = load_forms()
    raw = Path(args.raw) if args.raw else Path(tempfile.mkdtemp(prefix="spec-coverage-")) / "inventory.tsv"
    if not args.from_raw:
        with tempfile.TemporaryDirectory(prefix="spec-coverage-") as tmp:
            # the library: the lemmas only (no handler, no deep check)
            inp = Path(tmp) / "samples-lib.txt"
            write_samples(forms, inp, False, handler=False)
            lib_out = Path(tmp) / "lib.tsv"
            run_lean("inventory", inp, lib_out, not args.no_build, args.wrap, args.jobs)
            # contract-check's environment: the lemmas, the handlers, the deep check
            inp = Path(tmp) / "samples.txt"
            write_samples(forms, inp, args.deep)
            check_out = Path(tmp) / "check.tsv"
            run_lean("inventory", inp, check_out, False, args.wrap, args.jobs, mods=ENV_CHECK)
            merge_lib(check_out, lib_out, raw.resolve())
    else:
        raw = Path(args.from_raw)
    data = parse_raw(raw)
    classified = classify_forms(data, forms)
    cnt = collections.Counter(c["status"] for c in classified)
    print(f"spec-coverage: {len(classified)} forms: " + ", ".join(f"{k} {cnt[k]}" for k in STATUS_RU))
    if args.save:
        keep = []
        for c in classified:
            keep.append({k: c[k] for k in ("name", "family", "status", "samples", "with_spec", "lemmas",
                                           "lib_lemmas", "closed", "handler_ok", "blockers", "deep", "versions")})
            keep[-1]["why"] = [why_missing(c)] if c["status"] == "missing" and why_missing(c) else []
        FORMS_JSON.write_text(json_lines(keep))
        print(f"spec-coverage: wrote {FORMS_JSON.relative_to(REPO)}")
    if args.md:
        commit = subprocess.run(["git", "rev-parse", "--short", "HEAD"], cwd=REPO, stdout=subprocess.PIPE,
                                text=True).stdout.strip()
        Path(args.md).write_text(render_md(classified, data, load_probe_results(), commit))
        print(f"spec-coverage: wrote {args.md}")
    if args.raw or args.from_raw:
        print(f"spec-coverage: raw output {raw}")


# ------------------------------------------------------------------------------------------------
# Precheck: the code of a contract


def spec_index(raw: dict) -> dict[str, dict]:
    """The `vm_spec` lemmas by name: module, seen by contract-check, instruction, conditions."""
    out = {}
    for name, module, in_check, instr, conds in (r[:5] for r in raw.get("SPEC", [])):
        cl = split_list(conds)
        out[name] = {"module": module, "check": in_check == "1", "instr": instr, "conds": cl,
                     "closed": any(c.startswith("closed:") for c in cl)}
    return out


FORMS_JSON = HERE / "forms.json"


def load_form_results() -> dict:
    """The inventory's result per form (`inventory --save`): status, handler, deep check."""
    if not FORMS_JSON.exists():
        return {}
    return {r["name"]: r for r in json.loads(FORMS_JSON.read_text())}


def instr_status(specs_check: list[str], specs_lib: list[str], handler: str, specs: dict,
                 form: dict | None = None) -> str:
    """The status of one instruction of a code: `spec` (a lemma contract-check sees unifies with it, its
    exact arguments; its conditions on the state are the run's to meet), `spec-closed` (only lemmas that
    need a closed fact of the code: a dictionary constant, as the method dispatch's), `spec-lib` (only
    lemmas outside contract-check's imports), `unfold` (the handler runs by unfolding: the inventory's
    deep check of the form, else the static analysis), `blocked`, `?`."""
    if specs_check:
        if all(specs.get(n, {}).get("closed") for n in specs_check):
            return "spec-closed"
        return "spec"
    if specs_lib:
        return "spec-lib"
    if form is not None and form.get("samples"):
        return "unfold" if form.get("handler_ok") else "blocked"
    if handler == "unfold":
        return "unfold"
    if handler == "blocked":
        return "blocked"
    return "?"


STATUS_TEXT = {
    "spec": "vm_spec lemma",
    "spec-closed": "vm_spec lemma only for a closed dictionary of the code",
    "spec-lib": "vm_spec lemma outside contract-check's imports",
    "unfold": "handler unfolded (no lemma)",
    "blocked": "not handled",
    "?": "not analysed",
}


PRECHECK_JSON = HERE / "precheck-results.json"


def contract_codes() -> list[str]:
    """The codes of tools/txoracle/contracts.txt (the contracts of the transaction oracle: wallets,
    the elector, the configuration contract, DNS, TON Storage's storage contract, ...)."""
    path = REPO / "tools" / "txoracle" / "contracts.txt"
    return [f"list:tools/txoracle/contracts.txt#{l.split()[0]}" for l in path.read_text().splitlines()
            if l.split() and l.split()[0].endswith(".code")]


def cmd_precheck(args: argparse.Namespace) -> None:
    codes = args.code or contract_codes()
    print(precheck(codes, args.raw, args.from_raw, not args.no_build, args.wrap, save=args.save))


def precheck(sources: list[str], raw: str | None = None, from_raw: str | None = None, build: bool = True,
             wrap: str = "", save: bool = False) -> str:
    """The precheck report of the codes `sources` (BOC files or tools/boc2lean sources); with `save`,
    the summary of each in precheck-results.json (the table of docs/audit/spec-coverage.md)."""
    import boc2lean
    forms = load_forms()
    with tempfile.TemporaryDirectory(prefix="spec-coverage-pre-") as tmpd:
        tmp = Path(tmpd)
        lines, names = [], []
        for k, src in enumerate(sources):
            if not re.match(r"^(list|file|b64|hex):", src):
                src = "file:" + src
            name = re.sub(r"[^A-Za-z0-9._-]", "_", src.split("#")[-1].split("/")[-1]) or f"code{k}"
            name = f"{k}-{name}"
            (tmp / f"{k}.boc").write_bytes(boc2lean.load_source(src))
            lines.append(f"{name} {tmp / f'{k}.boc'}")
            names.append((name, src))
        inp = tmp / "in.txt"
        inp.write_text("\n".join(lines) + "\n")
        rawp = Path(raw) if raw else tmp / "precheck.tsv"
        if from_raw:
            rawp = Path(from_raw)
        else:
            lib_out = tmp / "lib.tsv"
            run_lean("precheck", inp, lib_out, build, wrap, extra_env={"SPEC_COVERAGE_HANDLER": "0"})
            check_out = tmp / "check.tsv"
            run_lean("precheck", inp, check_out, False, wrap, mods=ENV_CHECK)
            merge_lib(check_out, lib_out, rawp.resolve())
        data = parse_raw(rawp)
        reports = [precheck_report(name, src, data, forms) for name, src in names]
    if save:
        PRECHECK_JSON.write_text(json_lines([r[1] for r in reports]))
    return "\n\n".join(r[0] for r in reports)


def precheck_report(name: str, src: str, data: dict, forms: list[dict]) -> tuple[str, dict]:
    specs = spec_index(data)
    fres = load_form_results()
    occ = [r for r in data.get("INSTR", []) if r[0] == name]
    code = [r for r in data.get("CODE", []) if r[0] == name]
    by_form: dict[str, list] = collections.defaultdict(list)
    for r in occ:
        _, loc, op, ver, text, sc, sl, handler, blockers, _heads = (r + [""] * 10)[:10]
        f = form_of_op(forms, int(op, 16))
        fname = f["name"] if f else f"?{op}"
        st = instr_status(split_list(sc), split_list(sl), handler, specs, fres.get(fname))
        why = split_list(blockers)
        if st == "blocked" and fname in fres:
            why = fres[fname].get("why") or why
        by_form[fname].append({"loc": loc, "text": text, "status": st, "ver": int(ver or 0),
                               "blockers": why, "specs": split_list(sc) + split_list(sl),
                               "family": f["family"] if f else "?"})
    cells = len({r[1].rsplit("@", 1)[0] for r in occ} | {r[1] for r in code if "@" not in r[1].rsplit(":", 1)[-1]})
    out = [f"precheck {src}: {len(occ)} instructions, {len(by_form)} instruction forms, "
           f"{cells} code cells and continuations"]
    counts = collections.Counter(o["status"] for v in by_form.values() for o in v)
    out.append("  " + ", ".join(f"{STATUS_TEXT[k]}: {counts[k]}" for k in STATUS_TEXT if counts[k]))
    bad = code_issues(code)
    out += [f"  code: {b}" for b in bad]
    # the gaps: forms with an occurrence not run by a vm_spec lemma contract-check sees
    gaps = []
    gap_list = []
    for fname, os_ in sorted(by_form.items()):
        worst = sorted({o["status"] for o in os_}, key=list(STATUS_TEXT).index)
        if set(worst) <= {"spec", "spec-closed"}:
            continue
        sts = ", ".join(f"{STATUS_TEXT[s]} x{sum(1 for o in os_ if o['status'] == s)}" for s in worst)
        blk = sorted({b for o in os_ for b in o["blockers"]})
        locs = sorted({o["loc"] for o in os_}, key=len)
        where = ", ".join(locs[:2]) + (f" and {len(locs) - 2} more" if len(locs) > 2 else "")
        gaps.append(f"  {fname} ({os_[0]['family']}): {sts}" + (f"; blocked by {'; '.join(blk)}" if blk else "")
                    + f"; at {where}")
        gap_list.append({"form": fname, "family": os_[0]["family"], "count": len(os_),
                         "status": [s for s in worst if s not in ("spec", "spec-closed")]})
    if gaps:
        out.append("  instructions not run by a vm_spec lemma of contract-check:")
        out += ["  " + g for g in gaps]
    vers = sorted({(f, o["ver"]) for f, os_ in by_form.items() for o in os_ if o["ver"] > 0})
    if vers:
        out.append("  opcodes of a global version > 0 (vm_step decodes them only for a known global "
                   "version): " + ", ".join(f"{f} (v{v})" for f, v in vers))
    # SETCP 0 (every FunC contract's first instruction) is not the pattern of another codepage
    used = {f for f, os_ in by_form.items() if not (f == "SETCP" and all(o["text"] == "SETCP 0" for o in os_))}
    pats = patterns_in(used, code, {f for f, _ in vers})
    if pats:
        out.append("  control-flow patterns:")
        for p in pats:
            out.append(f"    {p['title']}: {p['status']}" + (f" — {p['note']}" if p.get("note") else ""))
    summary = {"source": src, "instructions": len(occ), "forms": len(by_form), "cells": cells,
               "counts": dict(counts), "gaps": gap_list, "versions": [f"{f} v{v}" for f, v in vers],
               "patterns": [{"title": p["title"], "status": p["status"]} for p in pats]}
    return "\n".join(out), summary


def code_issues(code: list[list[str]]) -> list[str]:
    out = []
    for r in code:
        if r[2].startswith("no instruction decodes") or r[2].startswith("BOC"):
            out.append(f"{r[1]}: {r[2]}")
    return out


# ------------------------------------------------------------------------------------------------
# Probes: the control-flow patterns, run by ran_case

PROBES_FIF = HERE / "probes.fif"
PROBES_TXT = HERE / "probes.txt"


def regen_probes() -> None:
    """tools/spec-coverage/probes.txt from probes.fif (the reference's Fift: TON_FIFT_BIN, TON_FIFT_LIB)."""
    fift = os.environ.get("TON_FIFT_BIN", "fift")
    lib = os.environ.get("TON_FIFT_LIB", "")
    cmd = [fift] + (["-I", lib] if lib else []) + ["-s", str(PROBES_FIF)]
    r = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    if r.returncode != 0:
        sys.stderr.write(r.stdout)
        raise SystemExit("spec-coverage: fift failed on probes.fif")
    lines = [l for l in r.stdout.splitlines() if re.match(r"^[a-z0-9-]+ [A-Za-z0-9+/=]+$", l)]
    PROBES_TXT.write_text("\n".join(lines) + "\n")
    print(f"spec-coverage: {len(lines)} probes written to {PROBES_TXT.relative_to(REPO)}")


def probe_module(name: str, b64: str) -> str:
    """A Lean file: the probe's code as a literal and the theorem that every run of an external
    message (global version from 4) keeps the invariant `Inv` (`True`), by `ran_case`."""
    import base64
    import boc2lean
    cells, roots = boc2lean.parse_boc(base64.b64decode(b64))
    em = boc2lean.Emitter("code", cells, roots[0])
    ns = "TvmLean.SpecCoverage.Probe." + "".join(w.capitalize() for w in re.split(r"[^a-z0-9]+", name))
    return f"""import TvmLean.Boc
import TvmLean.Proofs.Contracts.CellLiteral
import TvmLean.Proofs.Check.Tactic
import TvmLean.Proofs.Check.Framed

namespace {ns}

open TvmLean TvmLean.Tx TvmLean.Check

{em.defs()}
/-- The invariant: none (a named predicate, as the invariants of contract-check are). -/
def Inv (_data : Option Cell) : Prop := True

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 100000 in
set_option check.maxSteps 3000 in
theorem probe : ∀ bal val msg body,
    RunsKeep code Inv (computePhaseStack bal val msg body true) (4 ≤ ·) := by
  ran_case [Inv]

end {ns}
"""


def _run_probe(name: str, b64: str, tmp: Path, env: dict, prefix: list[str], timeout: int) -> dict:
    import time
    path = tmp / f"Probe_{re.sub(r'[^A-Za-z0-9]', '_', name)}.lean"
    path.write_text(probe_module(name, b64))
    t0 = time.time()
    # its own process group, so that a timeout stops lean too (lake runs it as a child)
    proc = subprocess.Popen(prefix + [lake(), "env", "lean", "--tstack=262144", str(path)], cwd=REPO, env=env,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
                            preexec_fn=_big_stack, start_new_session=True)
    try:
        out, _ = proc.communicate(timeout=timeout)
        rc = proc.returncode
    except subprocess.TimeoutExpired:
        os.killpg(proc.pid, signal.SIGKILL)
        proc.communicate()
        return {"name": name, "result": "timeout", "secs": round(time.time() - t0), "where": [], "detail": ""}
    dt = round(time.time() - t0)
    if rc == 0 and "error" not in out:
        return {"name": name, "result": "proved", "secs": dt, "where": [], "detail": ""}
    where = sorted({m.strip() for m in re.findall(r"last step at: (.*)", out)})
    paths = sorted({m.strip() for m in re.findall(r"path: (.*)", out)})
    first = next((l for l in out.splitlines() if "error" in l), "")
    return {"name": name, "result": "failed", "secs": dt, "where": where, "paths": paths,
            "detail": first[:300], "log": out[-4000:]}


def run_probes(jobs: int, wrap: str, build: bool, only: list[str] | None, timeout: int) -> list[dict]:
    import concurrent.futures
    prefix = wrap.split() if wrap else []
    env = dict(os.environ)
    env.setdefault("LEAN_NUM_THREADS", "2")
    if build:
        r = subprocess.run(prefix + [lake(), "build", "TvmLean.Proofs.Check.Tactic", "TvmLean.Proofs.Check.Framed", "TvmLean.Boc",
                                     "TvmLean.Proofs.Contracts.CellLiteral"], cwd=REPO, env=env)
        if r.returncode != 0:
            raise SystemExit("spec-coverage: lake build failed")
    probes = [l.split(" ", 1) for l in PROBES_TXT.read_text().splitlines() if l.strip()]
    if only:
        probes = [p for p in probes if p[0] in only]
    with tempfile.TemporaryDirectory(prefix="spec-coverage-probes-") as tmpd:
        with concurrent.futures.ThreadPoolExecutor(max_workers=max(1, jobs)) as ex:
            futs = [ex.submit(_run_probe, n, b, Path(tmpd), env, prefix, timeout) for n, b in probes]
            return [f.result() for f in futs]


# The control-flow patterns: the forms that make them in code, the probes that try them, and what
# runs them (the lemmas and tactics of TvmLean/Proofs/Exec and TvmLean/Proofs/Check). The status of
# each is computed from the probes' results (probe-results.json: `patterns --save`): all proved:
# handled; some: partial; none: missing.
PATTERNS: list[dict] = [
    {"id": "plain", "title": "jump/call of an ordinary continuation without closure data "
     "(EXECUTE/CALLX, JMPX, IF, IFNOT, IFJMP, IFNOTJMP, IFELSE, RET, IFRET)",
     "forms": ["EXECUTE", "JMPX", "IF", "IFNOT", "IFJMP", "IFNOTJMP", "IFELSE", "RET", "IFRET", "IFNOTRET"],
     "probes": ["callx", "jmpx", "ifelse-unknown"],
     "how": "Spec.execute, Spec.jmpx, Spec.if_, Spec.ifnot, Spec.ifjmp, Spec.ifnotjmp, Spec.ifelse, "
            "Spec.ret, Spec.ifret (Exec/Spec/Flow.lean); VM.run_jump_ordinary, VM.run_call_plain (Exec/VM.lean)"},
    {"id": "closure", "title": "jump/call of a continuation with closure data or nargs (SETCONTARGS, BLESSARGS, "
     "then EXECUTE/JMPX)",
     "forms": ["SETCONTARGS", "SETCONTVARARGS", "SETNUMVARARGS", "BLESSARGS", "BLESSVARARGS", "BLESS"],
     "probes": ["closure-call", "closure-jump"],
     "how": "Spec.setContArgs_ord, VM.run_jump_ordinary_cdata, VM.run_call_ordinary_cdata (Exec/Closure.lean)"},
    {"id": "xargs", "title": "CALLXARGS / JMPXARGS / RETARGS (arguments and return values counted)",
     "forms": ["CALLXARGS", "CALLXARGS_1", "JMPXARGS", "RETARGS", "CALLXVARARGS", "JMPXVARARGS", "RETVARARGS",
               "RETURNARGS", "RETURNVARARGS"],
     "probes": ["callxargs", "jmpxargs", "retargs"], "how": "the handler unfolded; VM.call/VM.jump with passArgs"},
    {"id": "callcc", "title": "CALLCC and variants (the current continuation as a value)",
     "forms": ["CALLCC", "CALLCCARGS", "CALLCCVARARGS"], "probes": ["callcc", "callccargs"],
     "how": "the handler unfolded (VM.extractCc)"},
    {"id": "retalt", "title": "RETALT / c1 (the alternative return)", "forms": ["RETALT", "IFRETALT", "IFNOTRETALT"],
     "probes": ["retalt"], "how": "the handler unfolded"},
    {"id": "loops-const", "title": "REPEAT / UNTIL with a known count", "forms": [],
     "probes": ["repeat-const", "until-const"],
     "how": "Spec.repeat_, Spec.until_ (Exec/Spec/Loop.lean); the loop rule (vm_loop_c5)"},
    {"id": "loops-unknown", "title": "REPEAT / UNTIL / WHILE with an unknown count, a value carried on the stack",
     "forms": ["REPEAT", "UNTIL", "WHILE"],
     "probes": ["repeat-unknown", "repeat-data", "until-data", "while-data"],
     "how": "the loop rule VmState.runWith_inv at the loop head (vm_loop_c5, Contracts/Wallet3Run/Tactic.lean): "
            "the stack payloads generalized, c5 kept SafeActs"},
    {"id": "loops-end", "title": "REPEATEND / UNTILEND / WHILEEND / AGAINEND (the rest of the code as the body)",
     "forms": ["REPEATEND", "UNTILEND", "WHILEEND", "AGAINEND"],
     "probes": ["repeatend", "untilend", "whileend", "againend"],
     "how": "Spec.untilEnd, Spec.whileEnd, Spec.againEnd; REPEATEND by the handler"},
    {"id": "loops-brk", "title": "the BRK loops (c1 = the exit; RETALT leaves the loop)",
     "forms": ["REPEATBRK", "UNTILBRK", "WHILEBRK", "AGAINBRK", "REPEATENDBRK", "UNTILENDBRK", "WHILEENDBRK",
               "AGAINENDBRK"],
     "probes": ["againbrk", "repeatbrk", "untilbrk", "whilebrk"], "how": "the handlers unfolded"},
    {"id": "again", "title": "AGAIN without an exit (ends by running out of gas)", "forms": ["AGAIN"],
     "probes": ["again"], "how": "Spec.again and the loop rule"},
    {"id": "loop-in-loop", "title": "a loop inside a loop", "forms": [], "probes": ["loop-in-loop"],
     "how": "nested loop rules (check_loop_close takes the latest ih)"},
    {"id": "try", "title": "TRY / TRYARGS: an exception caught by a handler (c2)", "forms": ["TRY", "TRYARGS"],
     "probes": ["try-throw", "try-nothrow", "tryargs"], "how": "the handler unfolded; VM.run_throwToHandler"},
    {"id": "throw", "title": "THROW* to the default handler (the run halts with the exit code)",
     "forms": ["THROW", "THROW_SHORT", "THROWIF", "THROWIF_SHORT", "THROWIFNOT", "THROWIFNOT_SHORT", "THROWARG",
               "THROWANY", "THROWARGANY"],
     "probes": ["throw", "throwarg", "throwif-unknown", "throwifnot-unknown"],
     "how": "Spec.throw, Spec.throwIf, Spec.throwIfNot, Spec.throwArg, Spec.throwAny; VM.run_throwToHandler, "
            "the excQuit continuation unfolded"},
    {"id": "implicit", "title": "implicit RET at the end of a cell, implicit JMPREF to the next reference",
     "forms": [], "probes": ["implicit-jmpref", "nop"],
     "how": "stepCode: VmState.stepOnceWith_implicitRet', VmState.stepOnceWith_implicitJmpRef' (Exec/Tactic.lean)"},
    {"id": "refconts", "title": "CALLREF / JMPREF / IF*REF (continuations in references)",
     "forms": ["CALLREF", "JMPREF", "JMPREFDATA", "IFREF", "IFNOTREF", "IFJMPREF", "IFNOTJMPREF", "IFREFELSE",
               "IFELSEREF", "IFREFELSEREF"],
     "probes": ["callref", "jmpref", "ifjmpref"], "how": "the handlers unfolded (the reference loaded as a cell)"},
    {"id": "dispatch", "title": "the method dispatch: SETCP0, DICTPUSHCONST, DICTIGETJMPZ on the code's dictionary",
     "forms": ["DICTPUSHCONST", "DICTIGETJMPZ", "DICTIGETJMP", "DICTUGETJMP", "DICTUGETJMPZ", "DICTIGETEXEC",
               "DICTUGETEXEC", "DICTIGETEXECZ", "DICTUGETEXECZ"],
     "probes": ["calldict"],
     "how": "Spec.setcp0, Spec.dictPushConst, Spec.dictGetExec_* (Exec/Spec/Dispatch.lean): the lookup a closed "
            "fact of the code (dictLookupLoads, decided by the kernel)"},
    {"id": "dictcall", "title": "CALLDICT / JMPDICT / PREPAREDICT (procedures through c3)",
     "forms": ["CALLDICT", "CALLDICT_LONG", "JMPDICT", "PREPAREDICT"],
     "probes": ["calldict", "jmpdict", "preparedict"], "how": "Spec.callDict, Spec.jmpDict, Spec.prepareDict"},
    {"id": "runvm", "title": "RUNVM / RUNVMX (a child VM)", "forms": ["RUNVM", "RUNVMX"], "probes": ["runvm"],
     "how": "the handler unfolded; the child's run (VmState.runWith) is a recursive function"},
    {"id": "setcp", "title": "SETCP with a codepage other than 0, SETCPX", "forms": ["SETCP", "SETCPX", "SETCP_SHORT"],
     "probes": ["setcp1", "setcpx"], "how": "the handler unfolded; stepCode needs cp = 0, else the step unfolded"},
    {"id": "safe-actions", "title": "SENDRAWMSG / RAWRESERVE actions (c5)", "forms": ["SENDRAWMSG", "RAWRESERVE"],
     "probes": ["sendrawmsg", "rawreserve"],
     "how": "Spec.sendRawMsg, Spec.rawReserve; SafeActs closes c5 (Check/Tactic.lean)"},
    {"id": "other-actions", "title": "SETCODE / SETLIBCODE / CHANGELIB / SENDMSG / RAWRESERVEX actions",
     "forms": ["SETCODE", "SETLIBCODE", "CHANGELIB", "SENDMSG", "RAWRESERVEX"],
     "probes": ["setcode", "setlibcode", "changelib", "sendmsg"],
     "how": "Spec.setCode runs; ran_case proves only invariants of a code that never changes, and SafeActs "
            "admits SENDRAWMSG and RAWRESERVE only"},
    {"id": "regs", "title": "c4 / c5 / c7 updates (POP c4, POP c5, POP c7, SETGLOB)",
     "forms": ["POPCTR", "POPCTRX", "SETGLOB", "SETGLOBVAR", "POPSAVE", "SETRAND", "ADDRAND"],
     "probes": ["c4-update", "c5-update", "c7-update", "setglob"],
     "how": "Spec.popRoot (c4); the handler for c5, c7 and the globals"},
    {"id": "commit", "title": "COMMIT", "forms": ["COMMIT"], "probes": ["commit"],
     "how": "Spec.commit; keeps_haltResult checks the committed state"},
    {"id": "gas", "title": "ACCEPT / SETGASLIMIT", "forms": ["ACCEPT", "SETGASLIMIT"],
     "probes": ["accept", "setgaslimit"], "how": "Spec.accept, GasLimits.changeLimit_infty_min; SETGASLIMIT by the handler"},
    {"id": "dict-unknown", "title": "DICTGET / DICTSET on a dictionary the run does not know",
     "forms": [], "regex": r"^DICT[IU]?(GET|SET|ADD|REPLACE|DEL)(?!NEXT|PREV)(?!.*(JMP|EXEC))",
     "probes": ["dictget-unknown", "dictset-unknown"],
     "how": "Spec.dictGetInt_* need dictLookupLoads facts: closed, or a hypothesis; Exec/FramedDict.lean for "
            "framed cells"},
    {"id": "dict-iter", "title": "dictionary iteration on an unknown dictionary (GETNEXT/PREV/MIN/MAX)",
     "forms": [], "regex": r"^DICT[IU]?(GETNEXT|GETPREV|MIN|MAX|REMMIN|REMMAX)",
     "probes": ["dictgetnext-unknown", "dictmin-unknown"], "how": "the handler unfolded"},
    {"id": "config", "title": "configuration reads (CONFIGPARAM, CONFIGOPTPARAM)",
     "forms": ["CONFIGPARAM", "CONFIGOPTPARAM", "CONFIGDICT", "CONFIGROOT"], "probes": ["configparam", "configoptparam"],
     "how": "the handler unfolded"},
    {"id": "c7-params", "title": "c7 parameters (NOW, BALANCE, MYADDR, GETPARAM) with c7 unknown",
     "forms": ["NOW", "BALANCE", "MYADDR", "GETPARAM", "BLOCKLT", "LTIME", "RANDSEED", "MYCODE", "INCOMINGVALUE"],
     "probes": ["now"], "how": "Spec.getParam and aliases need c7[0]! = .tuple params as a hypothesis; else the handler"},
    {"id": "version", "title": "an opcode of global version > 0 (e.g. GASCONSUMED, v4) under a symbolic global version",
     "forms": [], "version": True, "probes": ["gasconsumed-v4"],
     "how": "stepCode decides `k <= globalVersion` by decide on the state's version"},
]

# The patterns in Russian, for docs/audit/spec-coverage.md: (title, what runs them).
PATTERNS_RU: dict[str, tuple[str, str]] = {
    'plain': (
        'переход/вызов обычного продолжения без замыкания (`EXECUTE`/`CALLX`, `JMPX`, `IF`, `IFNOT`, '
        '`IFJMP`, `IFNOTJMP`, `IFELSE`, `RET`, `IFRET`)',
        '`Spec.execute`, `Spec.jmpx`, `Spec.if_`, `Spec.ifnot`, `Spec.ifjmp`, `Spec.ifnotjmp`, '
        '`Spec.ifelse`, `Spec.ret`, `Spec.ifret` (`Exec/Spec/Flow.lean`); `VM.run_jump_ordinary`, '
        '`VM.run_call_plain`'),
    'closure': (
        'переход/вызов продолжения с замыканием или `nargs` (`SETCONTARGS`, `BLESSARGS`, затем '
        '`EXECUTE`/`JMPX`)',
        '`Spec.setContArgs_ord`, `VM.run_jump_ordinary_cdata`, `VM.run_call_ordinary_cdata` '
        '(`Exec/Closure.lean`)'),
    'xargs': (
        '`CALLXARGS` / `JMPXARGS` / `RETARGS` (число аргументов и результатов)',
        'обработчик; `VM.call`/`VM.jump` с `passArgs`'),
    'callcc': (
        '`CALLCC` и варианты (текущее продолжение как значение)',
        'обработчик (`VM.extractCc`)'),
    'retalt': (
        '`RETALT` / `c1` (альтернативный возврат)',
        'обработчик'),
    'loops-const': (
        '`REPEAT` / `UNTIL` с известным числом итераций',
        '`Spec.repeat_`, `Spec.until_` (`Exec/Spec/Loop.lean`); правило цикла (`vm_loop_c5`)'),
    'loops-unknown': (
        '`REPEAT` / `UNTIL` / `WHILE` с неизвестным числом итераций, значение на стеке',
        'правило цикла `VmState.runWith_inv` в голове цикла (`vm_loop_c5`, '
        '`Contracts/Wallet3Run/Tactic.lean`): полезная нагрузка вершины стека обобщена, `c5` — `SafeActs`'),
    'loops-end': (
        '`REPEATEND` / `UNTILEND` / `WHILEEND` / `AGAINEND` (тело — остаток кода)',
        '`Spec.untilEnd`, `Spec.whileEnd`, `Spec.againEnd`; `REPEATEND` — обработчиком'),
    'loops-brk': (
        'циклы `BRK` (`c1` — выход; `RETALT` выходит из цикла)',
        'обработчики'),
    'again': (
        '`AGAIN` без выхода (кончается нехваткой газа)',
        '`Spec.again` и правило цикла'),
    'loop-in-loop': (
        'цикл в цикле',
        'вложенные правила цикла (`check_loop_close` берёт последний `ih`)'),
    'try': (
        '`TRY` / `TRYARGS`: исключение ловит обработчик (`c2`)',
        'обработчик; `VM.run_throwToHandler`'),
    'throw': (
        '`THROW*` в обработчик по умолчанию (прогон останавливается с кодом выхода)',
        '`Spec.throw`, `Spec.throwIf`, `Spec.throwIfNot`, `Spec.throwArg`, `Spec.throwAny`; '
        '`VM.run_throwToHandler`, продолжение `excQuit` разворачивается'),
    'implicit': (
        'неявный `RET` в конце ячейки, неявный `JMPREF` на следующую ссылку',
        "`stepCode`: `VmState.stepOnceWith_implicitRet'`, `VmState.stepOnceWith_implicitJmpRef'`"),
    'refconts': (
        '`CALLREF` / `JMPREF` / `IF*REF` (продолжения в ссылках)',
        'обработчики (ссылка загружается как ячейка)'),
    'dispatch': (
        'диспетчер методов: `SETCP0`, `DICTPUSHCONST`, `DICTIGETJMPZ` по словарю кода',
        '`Spec.setcp0`, `Spec.dictPushConst`, `Spec.dictGetExec_*` (`Exec/Spec/Dispatch.lean`): поиск — '
        'замкнутый факт кода (`dictLookupLoads`, решает ядро)'),
    'dictcall': (
        '`CALLDICT` / `JMPDICT` / `PREPAREDICT` (процедуры через `c3`)',
        '`Spec.callDict`, `Spec.jmpDict`, `Spec.prepareDict`'),
    'runvm': (
        '`RUNVM` / `RUNVMX` (дочерняя VM)',
        'обработчик; прогон дочерней VM (`VmState.runWith`) рекурсивен'),
    'setcp': (
        '`SETCP` с кодовой страницей не 0, `SETCPX`',
        'обработчик; `stepCode` требует `cp = 0`'),
    'safe-actions': (
        'действия `SENDRAWMSG` / `RAWRESERVE` (`c5`)',
        '`Spec.sendRawMsg`, `Spec.rawReserve`; `SafeActs` закрывает `c5` (`Check/Tactic.lean`)'),
    'other-actions': (
        'действия `SETCODE` / `SETLIBCODE` / `CHANGELIB` / `SENDMSG` / `RAWRESERVEX`',
        '`Spec.setCode` исполняется; `ran_case` доказывает только инварианты неизменного кода, `SafeActs` '
        'допускает лишь `SENDRAWMSG` и `RAWRESERVE`'),
    'regs': (
        'изменение `c4` / `c5` / `c7` (`POP c4`, `POP c5`, `POP c7`, `SETGLOB`)',
        '`Spec.popRoot` (`c4`); остальное — обработчиком'),
    'commit': (
        '`COMMIT`',
        '`Spec.commit`; `keeps_haltResult` проверяет зафиксированное состояние'),
    'gas': (
        '`ACCEPT` / `SETGASLIMIT`',
        '`Spec.accept`, `GasLimits.changeLimit_infty_min`; `SETGASLIMIT` — обработчиком'),
    'dict-unknown': (
        '`DICTGET` / `DICTSET` по словарю, которого прогон не знает',
        '`Spec.dictGetInt_*` требуют фактов `dictLookupLoads`: замкнутых или гипотезы; '
        '`Exec/FramedDict.lean` — для обрамлённых ячеек'),
    'dict-iter': (
        'перебор неизвестного словаря (`GETNEXT`/`PREV`/`MIN`/`MAX`)',
        'обработчик'),
    'config': (
        'чтение конфигурации (`CONFIGPARAM`, `CONFIGOPTPARAM`)',
        'обработчик'),
    'c7-params': (
        'параметры `c7` (`NOW`, `BALANCE`, `MYADDR`, `GETPARAM`) при неизвестном `c7`',
        '`Spec.getParam` и синонимы требуют гипотезы `c7[0]! = .tuple params`; иначе обработчик'),
    'version': (
        'опкод глобальной версии > 0 (например `GASCONSUMED`, v4) при символьной версии',
        '`stepCode`: `k ≤ globalVersion` — `decide` при известной версии, иначе `omega` из гипотез о '
        'версии (`hgv`); не решено — `if` на `k ≤ gv` (`VmState.stepOnceWith_instrVer\'`)'),
}

# What a pattern lacks, from the probes' failures (English for precheck, Russian for the document).
PATTERN_GAPS: dict[str, tuple[str, str]] = {
    'xargs': (
        'VM.call/VM.jump with a number of arguments or results (passArgs, retArgs) have no vm_run lemma',
        'у `VM.call`/`VM.jump` с числом аргументов или результатов (`passArgs`, `retArgs`) нет леммы '
        '`vm_run`'),
    'retalt': (
        'after RETALT (a jump to c1) the next step is left as `VmState.stepFinish` of the state',
        'после `RETALT` (переход в `c1`) следующий шаг остаётся `VmState.stepFinish` состояния'),
    'loops-unknown': (
        'REPEAT with an unknown count: the loop rule generalizes the stack payloads, not the counter kept '
        'in the loop continuation (`repeatBody … n`), so the loop is unrolled until the run hits the '
        'heartbeat limit; UNTIL/WHILE with a value on the stack are handled',
        '`REPEAT` с неизвестным числом итераций: правило цикла обобщает значения на стеке, но не счётчик в'
        ' продолжении цикла (`repeatBody … n`), и цикл разворачивается, пока прогон не упрётся в предел '
        'heartbeats; `UNTIL`/`WHILE` со значением на стеке исполняются'),
    'loops-end': (
        'REPEATEND has the counter of REPEAT (does not end: heartbeat limit); UNTILEND, WHILEEND, AGAINEND are handled',
        'у `REPEATEND` тот же счётчик, что у `REPEAT` (не кончается: предел heartbeats); `UNTILEND`, `WHILEEND`, `AGAINEND` '
        'исполняются'),
    'loops-brk': (
        "REPEATBRK, UNTILBRK, WHILEBRK stop at the instruction (no specification, the handler's run does "
        'not reduce); AGAINBRK is handled',
        '`REPEATBRK`, `UNTILBRK`, `WHILEBRK` останавливаются на инструкции (леммы нет, прогон обработчика '
        'не считается); `AGAINBRK` исполняется'),
    'loop-in-loop': (
        'a REPEAT inside a REPEAT: the inner counter as above (does not end: heartbeat limit)',
        '`REPEAT` в `REPEAT`: внутренний счётчик, как выше (не кончается: предел heartbeats)'),
    'try': (
        'TRY without an exception is handled; with an exception caught by the handler, and TRYARGS, the '
        'run does not end (heartbeat limit)',
        '`TRY` без исключения исполняется; с исключением, пойманным обработчиком, и `TRYARGS` прогон не '
        'кончается (предел heartbeats)'),
    'runvm': (
        'the child run (`VmState.runWith`) is a recursive function: the handler does not reduce',
        'прогон дочерней VM (`VmState.runWith`) — рекурсивная функция: обработчик не считается'),
    'safe-actions': (
        'SENDRAWMSG is handled; the action of RAWRESERVE 0 0 is not closed by safe_acts_close',
        '`SENDRAWMSG` исполняется; действие `RAWRESERVE 0 0` не закрывает `safe_acts_close`'),
    'other-actions': (
        'by design: ran_case proves invariants of a code that never changes; SafeActs admits SENDRAWMSG '
        'and RAWRESERVE only; SENDMSG is also of version 4',
        'по замыслу: `ran_case` доказывает инварианты неизменного кода, `SafeActs` допускает лишь '
        '`SENDRAWMSG` и `RAWRESERVE`; `SENDMSG` к тому же версии 4'),
    'regs': (
        'POP c4 is handled; after POP c5 and POP c7 the next step is left as `VmState.stepFinish` of the '
        'state; SETGLOB stops at the instruction',
        '`POP c4` исполняется; после `POP c5` и `POP c7` следующий шаг остаётся `VmState.stepFinish` '
        'состояния; `SETGLOB` останавливается на инструкции'),
    'commit': (
        'after COMMIT (`Spec.commit`: the checks of `tryCommit` on c4 and c5) the next step is left as '
        '`VmState.stepFinish` of the state',
        'после `COMMIT` (`Spec.commit`: проверки `tryCommit` над `c4` и `c5`) следующий шаг остаётся '
        '`VmState.stepFinish` состояния'),
    'dict-unknown': (
        'DICTUGET/DICTUSET on a dictionary read from the message: the lemmas need dictLookupLoads facts, '
        'the handler stops at the cell loads of the lookup (registerCellLoad of unknown cells)',
        '`DICTUGET`/`DICTUSET` по словарю из сообщения: леммам нужны факты `dictLookupLoads`, обработчик '
        'останавливается на загрузках ячеек поиска (`registerCellLoad` неизвестных ячеек)'),
    'dict-iter': (
        'GETNEXT/MIN on an unknown dictionary: no lemma, the handler stops at the instruction',
        '`GETNEXT`/`MIN` по неизвестному словарю: леммы нет, обработчик останавливается на инструкции'),
    'config': (
        'the lookup in the configuration dictionary (dictLookupWithCells of the unknown c7 config root) '
        'stays a term and the run stops on the shape of the value',
        'поиск в словаре конфигурации (`dictLookupWithCells` по неизвестному корню из `c7`) остаётся '
        'термом, и прогон останавливается на форме значения'),
}

PROBE_RESULTS = HERE / "probe-results.json"


def pattern_status(p: dict, results: dict) -> tuple[str, str]:
    """handled / partial / missing from the probes, and what the failing probes stopped at."""
    rs = [results.get(n) for n in p["probes"]]
    if not rs or any(r is None for r in rs):
        return "not probed", ""
    ok = [r for r in rs if r["result"] == "proved"]
    bad = [r for r in rs if r["result"] != "proved"]
    status = "handled" if not bad else ("partial" if ok else "missing")
    def where(r: dict) -> str:
        if r["result"] == "timeout":
            return ""
        w = [re.sub(r"TvmLean\.SpecCoverage\.Probe\.\w+\.", "", x) for x in r.get("where") or []]
        w = [x for x in w if x != "(unknown)"]
        return f" at {w[0]}" if w else " (the run stops)"
    note = "; ".join(f"{r['name']}: {r['result']}{where(r)}" for r in bad)
    return status, note


def load_probe_results() -> dict:
    if not PROBE_RESULTS.exists():
        return {}
    return {r["name"]: r for r in json.loads(PROBE_RESULTS.read_text())}


def patterns_in(forms_used: set[str], code: list[list[str]], versioned: set[str] = frozenset()) -> list[dict]:
    """The patterns of PATTERNS whose forms the code uses (`versioned`: its forms of a global
    version > 0), with their status."""
    results = load_probe_results()
    out = []
    implicit = any(r[2] == "implicit JMPREF" for r in code)
    for p in PATTERNS:
        used = set(p["forms"]) & forms_used
        if p.get("regex"):
            used |= {f for f in forms_used if re.match(p["regex"], f)}
        if p.get("version"):
            used |= set(versioned)
        if used or (p["id"] == "implicit" and implicit):
            st, note = pattern_status(p, results)
            used = sorted(used)
            gap = PATTERN_GAPS.get(p["id"], ("", ""))[0] if st in ("partial", "missing") else ""
            out.append({"title": p["title"] + (f" [{', '.join(used)}]" if used else ""), "status": st,
                        "note": gap or note})
    return out


def cmd_patterns(args: argparse.Namespace) -> None:
    if args.regen:
        regen_probes()
    if args.from_raw:
        results = json.loads(Path(args.from_raw).read_text())
    else:
        results = run_probes(args.jobs, args.wrap, not args.no_build,
                             args.only.split(",") if args.only else None, args.timeout)
    if args.raw:
        Path(args.raw).write_text(json.dumps(results, indent=1))
    if args.save:
        keep = [{k: r.get(k) or [] if k == "where" else r.get(k) for k in ("name", "result", "where")} for r in results]
        PROBE_RESULTS.write_text(json_lines(sorted(keep, key=lambda r: r["name"])))
    for r in results:
        print(f"{r['name']:24} {r['result']:8} {r['secs']:5}s  {'; '.join(r.get('where', []))[:200]}")


def classify_forms(raw: dict, forms: list[dict]) -> list[dict]:
    """Each form with its samples, the lemmas that unify with them, the handler, the deep check, and
    its status:

    * `spec`: a `vm_spec` lemma contract-check sees unifies with every sample (and, with the deep
      check, fires on a generic symbolic stack of the form's signature);
    * `spec-cond`: such a lemma unifies with some samples only, needs a closed fact of the code (a
      dictionary constant), or does not fire on a generic stack (a condition the run must meet:
      `c.special = false`, a shape of `c7`, an argument); the other cases run by the handler;
    * `spec-lib`: only lemmas of modules contract-check does not import (TvmLean/Proofs/Exec/...);
    * `unfold`: no lemma; the handler runs by unfolding (deep check: computed; else: no blocker);
    * `missing`: no lemma, and the handler is blocked (a recursive program, a combinator outside the
      model) or its run does not compute (deep check: stuck, error).
    """
    specs = spec_index(raw)
    samples = collections.defaultdict(list)
    for r in raw.get("SAMPLE", []):
        samples[r[0]].append(r)
    deep = {r[0]: r for r in raw.get("DEEP", [])}
    crash = {r[0]: r for r in raw.get("CRASH", [])}
    out = []
    for f in forms:
        ok = [r for r in samples.get(f["name"], []) if r[3] == "ok"]
        n = len(ok)
        sc = [split_list(r[5]) for r in ok]
        sl = [split_list(r[6]) for r in ok]
        handlers = [r[7] for r in ok if r[7] in ("unfold", "blocked")]
        blockers = sorted({b for r in ok for b in split_list(r[8])})
        lemmas = sorted({x for xs in sc for x in xs})
        lib_lemmas = sorted({x for xs in sl for x in xs} - set(lemmas))
        with_spec = sum(1 for xs in sc if xs)
        closed = bool(lemmas) and all(specs.get(x, {}).get("closed") for x in lemmas)
        d = deep.get(f["name"])
        dinfo = None
        if d:
            # DEEP form hex sig spec handler left opaque ms
            d = (d + [""] * 9)[:9]
            dinfo = {"sig": d[2], "spec": d[3], "handler": d[4], "left": split_list(d[5]),
                     "opaque": split_list(d[6]), "ms": d[7]}
        elif f["name"] in crash:
            dinfo = {"sig": "", "spec": "?", "handler": "crash", "left": [], "opaque": [], "ms": ""}
        handler_ok = bool(handlers) and all(h == "unfold" for h in handlers)
        if dinfo is not None and dinfo["handler"]:
            handler_ok = dinfo["handler"].startswith("computed") or (
                dinfo["handler"] == "stuck" and dinfo["left"] and all(is_matcher(x) for x in dinfo["left"]))
        if n == 0:
            status = "missing"
        elif with_spec == n and not closed and (dinfo is None or dinfo["spec"] in ("fires", "?")):
            status = "spec"
        elif with_spec > 0:
            status = "spec-cond"
        elif lib_lemmas:
            status = "spec-lib"
        elif handler_ok:
            status = "unfold"
        else:
            status = "missing"
        vers = sorted({int(r[2]) for r in ok if r[2].isdigit() and int(r[2]) > 0})
        out.append(dict(f, samples=n, with_spec=with_spec, lemmas=lemmas, lib_lemmas=lib_lemmas,
                        closed=closed, handler_ok=handler_ok, blockers=blockers, deep=dinfo,
                        status=status, versions=vers, text=ok[0][4] if ok else ""))
    return out


STATUS_RU = {
    "spec": "лемма",
    "spec-cond": "лемма с условием",
    "spec-lib": "лемма вне contract-check",
    "unfold": "развёртка обработчика",
    "missing": "не исполняется",
}


def md_escape(s: str) -> str:
    return s.replace("|", "\\|")


REASON_RU = {
    "outside the model, no vm_run lemma": "вне модели, нет леммы vm_run",
    "recursive, no vm_run lemma": "рекурсивно, нет леммы vm_run",
    "jump/call, no vm_run lemma": "переход/вызов, нет леммы vm_run",
    "the analysis ran out of heartbeats": "анализ не уложился в heartbeats",
}


def short(name: str) -> str:
    """A name of the model without its namespace (a private name by its last part); a blocker
    `name (reason)` with its reason in Russian."""
    m = re.match(r"^(\S+) \((.*)\)$", name)
    if m:
        return f"{short(m.group(1))} ({REASON_RU.get(m.group(2), m.group(2))})"
    m = re.match(r"^_private\..*\.0\.(.*)$", name)
    if m:
        name = m.group(1)
    for p in ("TvmLean.Spec.", "TvmLean.Check.", "TvmLean."):
        if name.startswith(p):
            return name[len(p):]
    return name


def is_matcher(name: str) -> bool:
    """A `match` (its matcher): a run left at one on an unknown value is split by vm_split."""
    return re.search(r"\.match_\d+$", name) is not None


def error_text(m: str) -> str:
    if m == "heartbeats":
        return "предел heartbeats"
    if "maximum recursion" in m:
        return "предел глубины рекурсии simp"
    return f"ошибка ({m})"


def deep_text(d: dict) -> str:
    """The handler's run of the deep check, in words."""
    h = d["handler"]
    m = re.match(r"^computed\[(\d+)\]$", h)
    if m:
        out = f"посчитан, ветвлений {m.group(1)}"
    elif h == "stuck" and d["left"] and all(is_matcher(x) for x in d["left"]):
        out = "посчитан до `match` по неизвестному значению (делит `vm_split`)"
    elif h == "stuck":
        out = "стоит на " + ", ".join(short(x) for x in d["left"] if not is_matcher(x))
    elif h == "error":
        out = error_text(", ".join(d["left"]))
    elif h == "crash":
        out = "переполнение стека"
    else:
        out = h
    if d["opaque"]:
        out += "; остаются термами: " + ", ".join(short(x) for x in d["opaque"][:4])
    return out


def why_missing(c: dict) -> str:
    """What stops a form that is not run: the blockers of its handler, what its deep run left."""
    parts = []
    if c["blockers"]:
        parts.append("обработчик: " + ", ".join(short(b) for b in c["blockers"]))
    d = c["deep"]
    if d:
        if d["handler"] == "crash":
            parts.append("прогон обработчика: переполнение стека")
        elif d["handler"] == "error":
            parts.append("прогон обработчика: " + error_text(", ".join(d["left"])))
        elif d["handler"] == "stuck" and d["left"]:
            parts.append("прогон обработчика остановился на " + ", ".join(
                short(x) for x in d["left"] if not is_matcher(x)))
    return "; ".join(parts)


def render_md(classified: list[dict], raw: dict, results: dict, commit: str) -> str:
    specs = spec_index(raw)
    deep = any(c["deep"] for c in classified)
    fam = collections.OrderedDict((f, []) for f in FAMILIES)
    for c in classified:
        fam[c["family"]].append(c)
    L = []
    L.append("# Покрытие инструкций символьным исполнением")
    L.append("")
    L.append(f"Сгенерировано `tools/spec-coverage/spec_coverage.py` на коммите `{commit}`; руками не править. "
             "Пересоздать (на сервере сборки: нужна собранная библиотека доказательств, Fift эталона — только "
             "для `--regen`):")
    L.append("")
    L.append("```sh")
    L.append("export LEAN_NUM_THREADS=1   # процессов × потоков не больше ядер: под перегрузкой пробы упираются в тайм-аут")
    L.append("python3 tools/spec-coverage/spec_coverage.py patterns --jobs 12 --timeout 2700 --save   # шаблоны: пробы "
             "(--regen: probes.txt из probes.fif)")
    L.append("python3 tools/spec-coverage/spec_coverage.py inventory --deep --jobs 14 --save --raw inv.tsv")
    L.append("python3 tools/spec-coverage/spec_coverage.py precheck --save   # контракты contracts.txt; после inventory (forms.json)")
    L.append("python3 tools/spec-coverage/spec_coverage.py inventory --from-raw inv.tsv --md docs/audit/spec-coverage.md")
    L.append("```")
    L.append("")
    L.append("## Как считается")
    L.append("")
    L.append("- **Формы инструкций** — 919 форм таблицы декодирования C++ (по одному набору тестов на форму): "
             "диапазоны 24-битных опкодов из `third_party/tvm-specification/tvm-specification.json` без `EXTCALL` "
             "(в эталоне его нет) и с `GETEXTRABALANCE` (в снимке его нет). Семейства — по категориям снимка "
             "(`continuation_cond_loop` — циклы; `codepage` — в cont/flow; `address` — в msg/actions; `config`, "
             "`globals`, `prng`, `basic_gas` — в tonenv/c7).")
    L.append("- Каждая форма перебирается по аргументам (все значения, если их не больше 256, иначе 64 по "
             "диапазону); опкод с хвостом из 999 нулей (иначе единиц) и четырьмя пустыми ссылками "
             "декодируется декодером модели, как его декодирует `vm_step`.")
    L.append("- **Лемма**: лемма `vm_spec`, чья инструкция унифицируется с декодированной (`withReducible "
             "isDefEq`, как `applySpec` в `TvmLean/Proofs/Exec/Tactic.lean`), из модулей, которые импортирует "
             "`TvmLean.Proofs.Check.Tactic` (их видит модуль `tools/contract-check`). Условия леммы на состояние "
             "(форма стека, факт кода) — то, что должен дать прогон.")
    L.append("- **Обработчик**: если ни одна лемма не подходит, `runInstr` исполняет обработчик модели "
             "(диспетчеры `execInstr` пройдены, программы VM считаются леммами `vm_run` или разворачиваются, "
             "`unfoldModelRun`). Статически: каждая программа VM обработчика либо считается леммой `vm_run`, "
             "либо разворачивается (нерекурсивное определение модели), либо **блокирует** (рекурсивная "
             "программа, комбинатор вне модели: `forIn`, ...).")
    if deep:
        L.append("- **Прогон** (`--deep`): первая выборка формы исполняется на символьном состоянии — стек из "
                 "значений сигнатуры формы (целые, срезы, ячейки, построители, простые продолжения, кортежи; "
                 "по снимку спецификации) поверх неизвестного стека, `c0` — простое продолжение возврата, `c7` — "
                 "кортеж фазы исполнения из одного неизвестного значения, остальное неизвестно: (1) срабатывает "
                 "ли лемма (`simp` только с `applySpec`, с разрядчиком `vm_disch`); (2) считается ли обработчик "
                 "(`vm_simp`): в цели не остаётся ни `execInstr`, ни прогона программы (`ExceptT.run`), "
                 "только `if` и `match` по неизвестным значениям (на них `vm_split` делит путь). Это "
                 "приближение одного шага на самом общем состоянии: в настоящем прогоне состояние конкретнее "
                 "(например, `CALLCC` и `AGAINBRK` здесь не посчитаны — `simp` упирается в глубину рекурсии, "
                 "— а их пробы ниже проходят), и наоборот, посчитанный шаг не значит, что путь дойдёт до конца "
                 "(`CONFIGOPTPARAM`); целые пути проверяют пробы шаблонов.")
    L.append("")
    L.append("Статусы формы:")
    L.append("")
    L.append("| Статус | Значение |")
    L.append("|---|---|")
    L.append("| лемма | лемма `vm_spec` подходит к каждой выборке" + (" и срабатывает на символьном стеке сигнатуры" if deep else "") + " |")
    L.append("| лемма с условием | лемма подходит не ко всем аргументам, требует факта кода (словарь-константа) "
             "или условия, которого нет на общем символьном стеке (`c.special = false`, форма `c7`); остальное — "
             "обработчиком |")
    L.append("| лемма вне contract-check | лемма есть только в модулях, которые `TvmLean.Proofs.Check.Tactic` не "
             "импортирует (подключить импорт) |")
    L.append("| развёртка обработчика | леммы нет; обработчик считается развёрткой" + (" (прогон: посчитан)" if deep else " (нет блокирующих программ)") + " |")
    L.append("| не исполняется | леммы нет; обработчик блокирует или его прогон не считается |")
    L.append("")
    # --- the summary
    L.append("## Итог по семействам")
    L.append("")
    L.append("Сейчас, в окружении contract-check: **покрыто** — лемма (и лемма с условием); **развёртка** — "
             "обработчик считается (в том числе у форм с леммой вне contract-check: в скобках — сколько из них); "
             "**не исполняется** — остальное.")
    L.append("")
    L.append("| Семейство | Форм | Лемма | Лемма с условием | Лемма вне contract-check (из них развёртка) | "
             "Развёртка обработчика | Не исполняется | Покрыто / развёртка / не исполняется сейчас |")
    L.append("|---|---:|---:|---:|---:|---:|---:|---|")
    tot = collections.Counter()

    def now(cs: list[dict]) -> tuple[int, int, int]:
        cov = sum(1 for c in cs if c["status"] in ("spec", "spec-cond"))
        unf = sum(1 for c in cs if c["status"] == "unfold" or (c["status"] == "spec-lib" and c["handler_ok"]))
        return cov, unf, len(cs) - cov - unf

    for f, cs in fam.items():
        cnt = collections.Counter(c["status"] for c in cs)
        lib_unf = sum(1 for c in cs if c["status"] == "spec-lib" and c["handler_ok"])
        tot.update(cnt)
        tot["all"] += len(cs)
        tot["lib_unf"] += lib_unf
        cov, unf, no = now(cs)
        L.append(f"| {f} | {len(cs)} | {cnt['spec']} | {cnt['spec-cond']} | {cnt['spec-lib']} ({lib_unf}) | "
                 f"{cnt['unfold']} | {cnt['missing']} | {cov} / {unf} / {no} |")
    cov, unf, no = now(classified)
    L.append(f"| **всего** | **{tot['all']}** | **{tot['spec']}** | **{tot['spec-cond']}** | **{tot['spec-lib']}** "
             f"**({tot['lib_unf']})** | **{tot['unfold']}** | **{tot['missing']}** | **{cov} / {unf} / {no}** |")
    L.append("")
    n_check = sum(1 for s in specs.values() if s["check"])
    mods = collections.Counter(s["module"] for s in specs.values() if not s["check"])
    L.append(f"Лемм `vm_spec`: {len(specs)}, из них в импортах contract-check {n_check}; вне их: "
             + (", ".join(f"`{m}` ({k})" for m, k in sorted(mods.items())) or "нет") + ".")
    L.append("")
    # --- patterns
    L.append("## Шаблоны управления")
    L.append("")
    L.append("Каждый шаблон проверяется пробами (`tools/spec-coverage/probes.fif`): маленький код запускается "
             "`ran_case` от начала внешнего сообщения (глобальная версия от 4) с инвариантом `True`; шаблон "
             "**исполняется**, если все пути прогона доходят до конца. Результаты — "
             "`tools/spec-coverage/probe-results.json`.")
    L.append("")
    L.append("| Шаблон | Статус | Чем | Пробы | Где остановились пробы, которые не прошли | Чего не хватает |")
    L.append("|---|---|---|---|---|---|")
    st_ru = {"handled": "исполняется", "partial": "частично", "missing": "нет", "not probed": "не проверен"}
    for p in PATTERNS:
        st, note = pattern_status(p, results)
        title, how = PATTERNS_RU.get(p["id"], (p["title"], p["how"]))
        probes = ", ".join(f"`{n}`" for n in p["probes"])
        gap = PATTERN_GAPS.get(p["id"], ("", ""))[1] if st in ("partial", "missing") else ""
        L.append(f"| {md_escape(title)} | {st_ru[st]} | {md_escape(how)} | {probes} | {md_escape(note) or '—'} | "
                 f"{md_escape(gap) or '—'} |")
    L.append("")
    # --- the contracts
    if PRECHECK_JSON.exists():
        pre = json.loads(PRECHECK_JSON.read_text())
        L.append("## Предпроверка контрактов")
        L.append("")
        L.append("`contract-check <код> --precheck` (`spec_coverage.py precheck ... --save`): весь код, достижимый "
                 "из корня (неявные `JMPREF`, `PUSHCONT`, `CALLREF`, `IF*REF`, процедуры `DICTPUSHCONST`), "
                 "дизассемблирован декодером модели; каждая инструкция — по её точным аргументам (лемма), иначе по "
                 "результату формы выше. Вхождения инструкций:")
        L.append("")
        L.append("| Код | Инструкций | Форм | Лемма | Лемма для словаря-константы | Лемма вне contract-check | Развёртка "
                 "обработчика | Не исполняется | Формы без леммы contract-check |")
        L.append("|---|---:|---:|---:|---:|---:|---:|---:|---|")
        for p in pre:
            c = collections.Counter(p["counts"])
            gaps = ", ".join(f"`{g['form']}`" + (" (нет)" if "blocked" in g["status"] else "")
                             for g in sorted(p["gaps"], key=lambda g: (-g["count"], g["form"]))[:12])
            more = len(p["gaps"]) - 12
            if more > 0:
                gaps += f" и ещё {more}"
            L.append(f"| `{p['source'].split('#')[-1].replace('.code', '')}` | {p['instructions']} | {p['forms']} | "
                     f"{c['spec']} | {c['spec-closed']} | {c['spec-lib']} | {c['unfold']} | "
                     f"{c['blocked'] + c['?']} | {gaps or '—'} |")
        L.append("")
        vers = sorted({v for p in pre for v in p["versions"]})
        if vers:
            L.append("Опкоды версии > 0 в этих кодах (их шаг `vm_step` делает только при известной глобальной "
                     "версии, шаблон «опкод версии > 0» ниже): " + ", ".join(f"`{v}`" for v in vers) + ".")
            L.append("")
    # --- the gaps
    L.append("## Что не покрыто")
    L.append("")
    for f, cs in fam.items():
        miss = [c for c in cs if c["status"] in ("missing",)]
        if not miss:
            continue
        L.append(f"**{f}** ({len(miss)}): " + "; ".join(
            f"`{c['name']}`" + (f" ({md_escape(why_missing(c))})" if why_missing(c) else "") for c in miss) + ".")
        L.append("")
    lib_bad = [c for c in classified if c["status"] == "spec-lib" and not c["handler_ok"]]
    if lib_bad:
        L.append(f"Кроме того, {len(lib_bad)} форм с леммой вне contract-check в нём сейчас не исполняются "
                 "(обработчик не считается; их покроет подключение модулей с леммами): "
                 + ", ".join(f"`{c['name']}`" for c in lib_bad) + ".")
        L.append("")
    # --- every form
    L.append("## Все формы")
    L.append("")
    for f, cs in fam.items():
        L.append(f"### {f}")
        L.append("")
        hdr = "| Форма | Статус | Леммы | Обработчик |" + (" Прогон |" if deep else "")
        L.append(hdr)
        L.append("|---|---|---|---|" + ("---|" if deep else ""))
        for c in cs:
            lem = ", ".join(short(x) for x in c["lemmas"])
            if c["status"] == "spec-cond" and c["with_spec"] < c["samples"]:
                lem += f" ({c['with_spec']}/{c['samples']} аргументов)"
            if c["closed"]:
                lem += " (только словарь-константа)"
            if c["lib_lemmas"]:
                lem += ("; " if lem else "") + "вне: " + ", ".join(short(x) for x in c["lib_lemmas"])
            hand = "развёртка" if not c["blockers"] else "блок: " + ", ".join(short(b) for b in c["blockers"])
            row = f"| `{md_escape(c['name'])}`" + (f" v{c['versions'][0]}" if c["versions"] else "") + \
                  f" | {STATUS_RU[c['status']]} | {md_escape(lem) or '—'} | {md_escape(hand)} |"
            if deep:
                d = c["deep"]
                cell = "—" if d is None else ("лемма срабатывает; " if d["spec"] == "fires" else "") + deep_text(d)
                row += f" {md_escape(cell)} |"
            L.append(row)
        L.append("")
    return "\n".join(L) + "\n"


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    sub = ap.add_subparsers(dest="cmd", required=True)
    inv = sub.add_parser("inventory", help="the coverage of every instruction form")
    inv.add_argument("--md", help="write the table (docs/audit/spec-coverage.md)")
    inv.add_argument("--raw", help="keep the Lean side's output here")
    inv.add_argument("--save", action="store_true", help="write the result per form to "
                     "tools/spec-coverage/forms.json (read by precheck)")
    inv.add_argument("--from-raw", help="use this output of the Lean side instead of running it")
    inv.add_argument("--deep", action="store_true", help="also run each form (its first sample) on a "
                     "symbolic stack of its signature: by a vm_spec lemma, and by its handler (vm_simp)")
    inv.add_argument("--jobs", type=int, default=1, help="Lean processes in parallel (each loads the "
                     "environment: some 3 GB)")
    inv.add_argument("--no-build", action="store_true", help="do not build the modules first")
    inv.add_argument("--wrap", default=os.environ.get("CONTRACT_CHECK_WRAP", ""),
                     help="a command prefix for lake (e.g. a memory cap)")
    pre = sub.add_parser("precheck", help="what of a contract's code symbolic execution does not cover")
    pre.add_argument("code", nargs="*", help="BOC files or tools/boc2lean sources (list:, file:, b64:, hex:); "
                     "default: every code of tools/txoracle/contracts.txt")
    pre.add_argument("--raw", help="keep the Lean side's output here")
    pre.add_argument("--from-raw", help="use this output of the Lean side instead of running it")
    pre.add_argument("--save", action="store_true", help="write the summaries to "
                     "tools/spec-coverage/precheck-results.json (read by inventory --md)")
    pre.add_argument("--no-build", action="store_true")
    pre.add_argument("--wrap", default=os.environ.get("CONTRACT_CHECK_WRAP", ""))
    pat = sub.add_parser("patterns", help="the control-flow patterns, by running the probes")
    pat.add_argument("--regen", action="store_true", help="first write probes.txt from probes.fif (fift)")
    pat.add_argument("--jobs", type=int, default=1, help="probes checked in parallel")
    pat.add_argument("--only", help="only these probes (comma-separated)")
    pat.add_argument("--timeout", type=int, default=900, help="seconds per probe")
    pat.add_argument("--raw", help="keep the results here (JSON)")
    pat.add_argument("--from-raw", help="use these results instead of running the probes")
    pat.add_argument("--save", action="store_true", help="write the results to probe-results.json")
    pat.add_argument("--no-build", action="store_true")
    pat.add_argument("--wrap", default=os.environ.get("CONTRACT_CHECK_WRAP", ""))
    args = ap.parse_args()
    if args.cmd == "inventory":
        cmd_inventory(args)
    elif args.cmd == "patterns":
        cmd_patterns(args)
    elif args.cmd == "precheck":
        cmd_precheck(args)


if __name__ == "__main__":
    main()
