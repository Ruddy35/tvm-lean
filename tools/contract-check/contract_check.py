#!/usr/bin/env python3
"""contract-check: prove an invariant of a contract's data over all transactions, or show where it breaks.

    contract-check <code> <Inv.lean> [--name N] [--out FILE] [--wrap CMD] [--module M]
                   [--only KINDS] [--cut N] [--single] [--split] [--no-check]
    contract-check <code> --precheck

`<code>` is the contract's code as a BOC: a file (binary, base64 or hex text), or any source of
`tools/boc2lean` (`list:tools/txoracle/contracts.txt#wallet3.code`, `b64:...`, `hex:...`).
`<Inv.lean>` is the only thing written by hand: the invariant `P` of the account's data (a
predicate on `Option Cell`), with the definitions it needs, and three comment lines that say what
to check:

    -- contract-check: invariant Stored key sub      (the predicate, applied to the parameters)
    -- contract-check: params (key sub : Nat)         (its parameters, as binders; optional)
    -- contract-check: hints Data.encode, Data.WF    (simp lemmas and definitions to unfold; optional)
    -- contract-check: loop 5 Cleanup key            (a loop invariant; optional, any number of them)
    -- contract-check: code Signed key               (the code may change: see below; optional)

The hints are what the run and the closers need to read the data: the definition that writes the
data as a cell (`Data.encode`, unfolded so that the run reads its fields), definitions to unfold in
the invariant (`Data.WF`), lemmas (decode/encode facts). Definitions to unfold only at the ends of
the paths, when the data a path leaves is compared with the invariant, are tagged in `Inv.lean`
with `attribute [check_close] ...` (TvmLean/Proofs/Check/Attr.lean): a data layout whose reads the
run takes from lemmas among the hints (`examples/storage.lean`).

A `loop k Q` line gives a loop invariant: at a loop head whose top `k` stack entries satisfy `Q`
(a predicate on `k` values, the deepest first, in which the parameters may appear), the loop rule
lets those entries change in any way that keeps `Q` (`check_loop_user`); without one (or where none
holds at the head) a loop may change only its top entry, the action list and the counters.

contract-check generates one Lean module (`--out`, default a temporary file) with

* the code as a cell literal (`tools/boc2lean`: `code`, its BOC, its hash, the `#guard` that the
  project's BOC reader reads the BOC as the literal);
* the contents of `Inv.lean` (its imports moved to the top);
* the runs of the code from every state the compute phase may start it from, one theorem per kind
  of transaction (`runs_ext`, `runs_extOld`, `runs_int`, `runs_intOld`, `runs_tt`, `runs_ttOld`: an
  external message, an internal message, tick-tock; global version from 4 and below), each proved
  by `ran_case [hints]` (TvmLean/Proofs/Check/Tactic.lean), or with `--single` one theorem
  `preserves` proved by `ran_preserves [hints]`;
* `preserves`: the obligation of `Reachable.code_fixed`, and `reachable`: for every shard account
  reachable by transactions under any configuration from start states and deployments that satisfy
  the invariant (the theorem's hypotheses `hstart` and `hdeploy`), an active account has the code
  `code` and data satisfying `P`:

      theorem reachable <params> {configRoot : Cell} {Init Start : Cell → Prop}
          (hstart : ∀ sa, Start sa → Good (fun code' data => code' = some code ∧ P data) sa)
          (hdeploy : ∀ c si, Init c → Reader.runExact Account.Reader.stateInit c = some si →
            si.code = some code ∧ P si.data)
          {sa : Cell} (h : Reachable configRoot Init Start sa) :
          Good (fun code' data => code' = some code ∧ P data) sa

It checks the module (`lake env lean`, through the command `--wrap`, e.g. a memory cap; with
`--module`, `lake build` of the module, written by `--out` into the repository and a root of its
libraries) and prints `PROVED` with the theorem and its axioms, or `NOT PROVED` with, for each kind
of transaction it does not prove, every path where the invariant is not shown: the code position
of its last step (cell, bit, instruction), its exit code, its path condition (the hypotheses of the
path but those about the gas, which are counted) and the goal left.

The runs of a message are stated for an ordinary message cell (`msg.special = false →`, which the
run's `CTOS` of the message needs): `Ran` records it of every compute phase of a transaction of the
model (TvmLean/Proofs/Tx/InMsg.lean: C++ refuses a special message cell before any phase), and
`preserves` comes from `ran_preserves_ord_of` (`ran_self_ord_of`, `ran_installs_ord_of` with `code`;
TvmLean/Proofs/Check/InMsg.lean); `reachable` is the same theorem (not with `--single`).

`--only runs_ext,runs_int,...`: only the runs of these kinds of transaction (no theorem over all
transactions: a quicker look at one kind). `--split`: the same theorems checked in parts, the six
runs at once in processes of their own, `reachable` over them (`check_split`): in one module Lean
checks them one after another, since each run evaluates the code literal, a definition of that
module (TON Storage: its two runs of internal messages take nearly all the time). `--cut N`: cut the paths every N steps into auxiliary
theorems (`check.cut`, default 40; 0: no cut). `--single`: one theorem `preserves` by
`ran_preserves` instead of six. `--no-check`: only generate the module.

`--precheck`: before a proof, what of the code symbolic execution does not cover
(`tools/spec-coverage`): every code cell reachable from the code (implicit `JMPREF`, `PUSHCONT`,
`CALLREF`, `IF*REF`, the procedures of `DICTPUSHCONST`) disassembled by the model's decoder, each
instruction classified (a `vm_spec` lemma the run uses, the handler unfolded, not handled), and the
control-flow patterns of the code with their status; no `Inv.lean` needed, nothing is proved.

A contract whose code may change (`SETCODE`) says so with the line `code`:

* `code K`: `K` (applied to the parameters) is a predicate `Option Slice → Cell → Prop` on the body of
  the message (`none` for tick-tock) and a code: the runs are stated with the action lists `Acts (K
  (some body))` (`Acts (K none)` for tick-tock; TvmLean/Proofs/Tx/Acts.lean: the actions of the
  model's instructions, each `SETCODE` installing a code that satisfies the condition, e.g. "the body
  is signed by the owner's key"), `preserves` collects them (`ran_installs_of`: every `SETCODE`
  installs a code that is `Installable K`, `K` of the body of some message or of tick-tock), and
  `reachable` is `ReachableWhile.good_codes` (TvmLean/Proofs/Tx/Upgrade.lean): in every shard account
  reachable by transactions while the code is `code`, an active account with the code `code` has
  data satisfying the invariant, and an active account has the code `code` or an `Installable K` one
  (what an installed code does is not checked);
* `code self`: every `SETCODE` installs `code` itself (`Acts (· = code)`): `reachable` is
  `Reachable.code_self`, the statement of a code that never changes.

The modules under TvmLean/Proofs/Check/Contracts/ were generated by it (`--out` there).
"""

from __future__ import annotations

import argparse
import os
import re
import shutil
import signal
import subprocess
import sys
import tempfile
import textwrap
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parent.parent
sys.path.insert(0, str(REPO / "tools" / "boc2lean"))
import boc2lean  # noqa: E402

KINDS = [
    ("runs_ext", "computePhaseStack bal val msg body true", "(4 ≤ ·)", "∀ bal val msg body,",
     "an external message, global version from 4"),
    ("runs_extOld", "computePhaseStack bal val msg body true", "(· < 4)", "∀ bal val msg body,",
     "an external message, global version below 4"),
    ("runs_int", "computePhaseStack bal val msg body false", "(4 ≤ ·)", "∀ bal val msg body,",
     "an internal message, global version from 4"),
    ("runs_intOld", "computePhaseStack bal val msg body false", "(· < 4)", "∀ bal val msg body,",
     "an internal message, global version below 4"),
    ("runs_tt", "tickTockStack bal addr tock", "(4 ≤ ·)", "∀ bal addr tock,",
     "tick-tock, global version from 4"),
    ("runs_ttOld", "tickTockStack bal addr tock", "(· < 4)", "∀ bal addr tock,",
     "tick-tock, global version below 4"),
]

DIRECTIVE = re.compile(r"^\s*--\s*contract-check:\s*(\w+)\s*(.*?)\s*$")


def parse_inv(text: str) -> tuple[list[str], str, dict[str, str]]:
    """The imports, the rest of the file and the directives of an Inv.lean."""
    imports, body, directives = [], [], {}
    in_header = True
    for line in text.splitlines():
        m = DIRECTIVE.match(line)
        if m:
            if m.group(1) == "loop":
                directives.setdefault("loops", []).append(m.group(2).strip())
            else:
                directives[m.group(1)] = m.group(2)
            continue
        if in_header and line.startswith("import "):
            imports.append(line.strip())
            continue
        if line.strip() and not line.startswith("--"):
            in_header = False
        body.append(line)
    if "invariant" not in directives:
        raise SystemExit("contract-check: the Inv file has no line `-- contract-check: invariant <predicate>`")
    return imports, "\n".join(body).strip() + "\n", directives


def binder_names(params: str) -> list[str]:
    """The names bound by binders `(a b : T) {c : U} [d : V]`."""
    names = []
    for group in re.findall(r"[({\[]([^(){}\[\]]*?):", params):
        names += group.split()
    return names


def code_literal(source: str, ns: str) -> tuple[str, str]:
    """The cell literal of the code (`code`, its BOC, hash and `#guard`), and the source's description."""
    if not re.match(r"^(list|file|b64|hex):", source):
        source = "file:" + source
    boc = boc2lean.load_source(source)
    cells, roots = boc2lean.parse_boc(boc)
    em = boc2lean.Emitter("code", cells, roots[0])
    root = cells[roots[0]]
    parts = [
        em.defs(),
        f"/-- The BOC of the code (`{source}`). -/\n"
        f"def codeBoc : ByteArray :=\n  ⟨{boc2lean.byte_array(boc, '  ')}⟩\n",
        f"/-- The representation hash of the code, computed by `tools/boc2lean/boc2lean.py` from the BOC. -/\n"
        f"def codeHash : Array UInt8 :=\n  {boc2lean.byte_array(boc2lean.repr_hash(root), '  ')}\n",
        "-- the project's BOC reader reads the BOC as exactly the literal\n"
        "#guard match stdBocDeserializeMulti codeBoc with\n"
        "  | .ok roots => roots[0]?.any (· == code)\n"
        "  | .error _ => false\n",
    ]
    return "\n".join(parts), source


def generate(args: argparse.Namespace) -> tuple[str, str, dict]:
    """The module's text, its namespace, and its parts for `--split`: `common` (the imports, the
    code, the invariant, the fast twins), `open` (what each module of runs opens), `runs` (the
    theorem of each kind) and `tail` (`preserves`, `reachable`, the axioms)."""
    inv_text = Path(args.inv).read_text()
    imports, inv_body, d = parse_inv(inv_text)
    name = args.name or re.sub(r"[^A-Za-z0-9]", "", Path(args.inv).stem.title()) or "Contract"
    ns = f"TvmLean.Contracts.Checked.{name}"
    lit, source = code_literal(args.code, ns)
    params = d.get("params", "")
    pnames = binder_names(params)
    P = d["invariant"]
    hints = d.get("hints", "")
    loops = ""
    for spec in d.get("loops", []):
        km = re.match(r"(\d+)\s+(.+)$", spec)
        if not km:
            raise SystemExit(f"contract-check: a loop line is `loop <k> <predicate>`, not `{spec}`")
        loops += f" (loop {km.group(1)} := {km.group(2)})"
    papp = " ".join(pnames)
    try:
        inv_rel = os.path.relpath(Path(args.inv).resolve(), REPO)
    except ValueError:
        inv_rel = args.inv
    if inv_rel.startswith(".."):
        inv_rel = Path(args.inv).name
    header_imports = ["import TvmLean.Boc", "import TvmLean.Proofs.Contracts.CellLiteral",
                      "import TvmLean.Proofs.Check.Tactic", "import TvmLean.Proofs.Check.Framed",
                      "import TvmLean.Proofs.Check.Loops"]
    if not args.single:
        # the runs of a message from an ordinary message cell (TvmLean/Proofs/Check/InMsg.lean)
        header_imports.append("import TvmLean.Proofs.Check.InMsg")
        # a stack a step leaves as a fold (REVERSE)
        header_imports.append("import TvmLean.Proofs.Check.StackNorm")
        # the slice after a message address, the cell it reads moved forward
        header_imports.append("import TvmLean.Proofs.Check.MsgAddr")
    # the code may change (`code K` or `code self`): the action lists `Acts`
    code_k = d.get("code")
    if code_k is not None:
        header_imports.append("import TvmLean.Proofs.Check.Upgrade")
        if args.single:
            raise SystemExit("contract-check: --single is not available with the line `code`")
    for imp in imports:
        if imp not in header_imports:
            header_imports.append(imp)
    out_rel = "<this file>"
    if args.out:
        rel = os.path.relpath(Path(args.out).resolve(), REPO)
        if not rel.startswith(".."):
            out_rel = rel
    extra = []
    if args.only:
        extra.append(f"--only {args.only}")
    if args.cut is not None:
        extra.append(f"--cut {args.cut}")
    if args.single:
        extra.append("--single")
    cmd = " \\\n      ".join([f"tools/contract-check/contract-check {source}",
                                f"{inv_rel} --name {name}", " ".join(extra + [f"--out {out_rel}"])])
    out = []
    out.append("\n".join(header_imports) + "\n")
    fill = lambda t: textwrap.fill(t, 100, break_on_hyphens=False, break_long_words=False)
    gen = fill(f"Generated by `tools/contract-check` from `{source}` and `{inv_rel}`; do not edit, run again:")
    what = fill(f"`reachable`: under any configuration, from start states and deployments whose accounts have "
                f"the code `code` and data satisfying `{P}`, every shard account reachable by transactions "
                "(any messages, times, random seeds, libraries, tick-tock) has, when active, the code `code` "
                f"and data satisfying `{P}`. Its obligation (`preserves`, "
                "`TvmLean.Tx.Reachable.code_fixed`) is proved by running the code (`ran_case`, "
                "TvmLean/Proofs/Check/Tactic.lean) from every state the compute phase may start it from, "
                "one theorem per kind of transaction; nothing in this module is about the contract but the "
                "code literal and the invariant.")
    if code_k == "self":
        what = fill(f"`reachable`: under any configuration, from start states and deployments whose accounts have "
                    f"the code `code` and data satisfying `{P}`, every shard account reachable by transactions "
                    "has, when active, the code `code` and data satisfying it: the code changes only to itself "
                    "(every `SETCODE` installs `code`, `TvmLean.Tx.Reachable.code_self`). The runs are proved "
                    "by `ran_case`, one theorem per kind of transaction, with the action lists `Acts (· = code)`.")
    elif code_k is not None:
        what = fill(f"The code may change: every `SETCODE` of a committed run installs a code satisfying "
                    f"`{code_k}` for the body of the message (`none` for tick-tock; the runs, one theorem per kind "
                    f"of transaction, with the action lists `Acts`, proved by `ran_case`). `reachable`: under any "
                    "configuration, from start states and deployments whose accounts have, with the code `code`, "
                    f"data satisfying `{P}`, in every shard account reachable by transactions while the code is "
                    f"`code` (`TvmLean.Tx.ReachableWhile.good_codes`) an active account with the code `code` has "
                    f"data satisfying `{P}`, and an active account has the code `code` or a code that "
                    f"`{code_k}` admits for the body of some message (`Installable`). Nothing in this module is "
                    "about the contract but the code literal, the invariant and the condition on new code.")
    out.append(f"""/-!
# {name}: an invariant of the data over all transactions

{gen}

    {cmd}

{what}
-/
""")
    out.append(f"namespace {ns}\n\nopen TvmLean\n")
    out.append("/-! ## The code -/\n")
    out.append(lit)
    out.append(f"/-! ## The invariant (`{inv_rel}`) -/\n")
    out.append(inv_body)
    out.append(f"end {ns}\n")
    out.append("-- the fast twins of the code's literal, for the closed facts of its runs (`vm.fastFacts`)\n"
               f"set_option Elab.async false in\nfast_twin {ns}.code\n")
    parts: dict = {"common": "\n".join(out), "runs": {}}
    parts["open"] = f"namespace {ns}\n\nopen TvmLean TvmLean.Tx TvmLean.Check\n\nset_option vm.fastFacts true\n"
    out.append(parts["open"])
    pbind = (" " + params) if params else ""
    Pfull = f"({P})"
    if args.single:
        out.append(f"""set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- **Every committed run keeps the invariant** (the obligation of `Reachable.code_fixed`). -/
theorem preserves{pbind} : ∀ data c4 c5, {Pfull} data → Ran code data c4 c5 →
    {Pfull} (some c4) ∧ ∀ c, ¬ActionIn c5 (.setCode c) := by
  ran_preserves [{hints}]{loops}
""")
    else:
        out.append("/-! ## The runs, one theorem per kind of transaction -/\n")
        only = set(args.only.split(",")) if args.only else None
        cut_opt = f"\nset_option check.cut {args.cut} in" if args.cut is not None else ""
        if args.progress:
            cut_opt += "\nset_option check.progress true in"
        if args.max_steps is not None:
            cut_opt += f"\nset_option check.maxSteps {args.max_steps} in"
        if args.step_heartbeats is not None:
            cut_opt += f"\nset_option check.stepHeartbeats {args.step_heartbeats} in"
        for thm, stack, g, binders, desc in KINDS:
            if only is not None and thm not in only:
                continue
            if "msg" in binders:
                binders += " msg.special = false →"
            if code_k is None:
                stmt = f"RunsKeep code {Pfull} ({stack}) {g}"
                doc = f"The runs of {desc}: a run that commits keeps the invariant."
            else:
                acts = ("Acts (· = code)" if code_k == "self" else
                        f"Acts (({code_k}) {'none' if thm.startswith('runs_tt') else '(some body)'})")
                stmt = f"RunsKeepActs code {Pfull} ({acts}) ({stack}) {g}"
                doc = (f"The runs of {desc}: a run that commits keeps the invariant, and every `SETCODE` "
                       "it commits installs a code satisfying the condition.")
            parts["runs"][thm] = f"""set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in{cut_opt}
/-- {doc} -/
theorem {thm}{pbind} : {binders}
    {stmt} := by
  ran_case [{hints}]{loops}
"""
            out.append(parts["runs"][thm])
        args_app = (" " + papp) if papp else ""
        if only is not None:
            out.append(f"end {ns}\n")
            return "\n".join(out), ns, parts
        tail_start = len(out)
        runs = (f"(runs_ext{args_app}) (runs_extOld{args_app}) (runs_int{args_app})\n"
                f"    (runs_intOld{args_app}) (runs_tt{args_app}) (runs_ttOld{args_app})")
        if code_k is None:
            out.append(f"""/-- **Every committed run keeps the invariant** (the obligation of `Reachable.code_fixed`). -/
theorem preserves{pbind} : ∀ data c4 c5, {Pfull} data → Ran code data c4 c5 →
    {Pfull} (some c4) ∧ ∀ c, ¬ActionIn c5 (.setCode c) :=
  ran_preserves_ord_of (by rfl) {runs}
""")
        elif code_k == "self":
            out.append(f"""/-- **Every committed run keeps the invariant and installs no other code** (the obligation of
`Reachable.code_self`). -/
theorem preserves{pbind} : ∀ data c4 c5, {Pfull} data → Ran code data c4 c5 →
    {Pfull} (some c4) ∧ ∀ c, ActionIn c5 (.setCode c) → c = code :=
  ran_self_ord_of (by rfl) {runs}
""")
        else:
            out.append(f"""/-- **Every committed run keeps the invariant**, and every `SETCODE` it commits installs a code
that the condition admits for the body of some message (`ran_installs_of`, the obligation of
`ReachableWhile.good_codes`). -/
theorem preserves{pbind} : ∀ data c4 c5, {Pfull} data → Ran code data c4 c5 →
    {Pfull} (some c4) ∧ ∀ c, ActionIn c5 (.setCode c) → Installable ({code_k}) c :=
  ran_installs_ord_of (by rfl) {runs}
""")
    args_app = (" " + papp) if papp else ""
    if code_k is not None and code_k != "self":
        out.append(f"""/-- **The invariant while the code is `code`, and the codes it installs.** Under any configuration,
if every start state has an active account with data satisfying the invariant when its code is
`code`, and with the code `code` or one the condition admits, and every `StateInit` the account may
be deployed with has the code `code` and such data, then in every shard account reachable by
transactions while the code is `code` (`ReachableWhile`), an active account with the code `code` has
data satisfying the invariant, and an active account has the code `code` or a code that the
condition admits for the body of some message (`Installable`). -/
theorem reachable{pbind} {{configRoot : Cell}} {{Init Start : Cell → Prop}}
    (hstart : ∀ sa, Start sa → Good (fun code' data => (code' = some code → {Pfull} data) ∧
      ∀ c, code' = some c → c = code ∨ Installable ({code_k}) c) sa)
    (hdeploy : ∀ c si, Init c → Reader.runExact Account.Reader.stateInit c = some si →
      si.code = some code ∧ {Pfull} si.data)
    {{sa : Cell}} (h : ReachableWhile configRoot Init Start code sa) :
    Good (fun code' data => (code' = some code → {Pfull} data) ∧
      ∀ c, code' = some c → c = code ∨ Installable ({code_k}) c) sa :=
  ReachableWhile.good_codes hstart hdeploy (preserves{args_app}) h

end {ns}

#print axioms {ns}.reachable
""")
        if not args.single:
            parts["tail"] = "\n".join(out[tail_start:])
        return "\n".join(out), ns, parts
    fixed = "Reachable.code_self" if code_k == "self" else "Reachable.code_fixed"
    out.append(f"""/-- **The invariant over all transactions.** Under any configuration, if every start state has
an active account only with the code `code` and data satisfying the invariant, and every `StateInit`
the account may be deployed with has that code and such data, then every shard account reachable by
transactions has an active account only with the code `code` and data satisfying the invariant. -/
theorem reachable{pbind} {{configRoot : Cell}} {{Init Start : Cell → Prop}}
    (hstart : ∀ sa, Start sa → Good (fun code' data => code' = some code ∧ {Pfull} data) sa)
    (hdeploy : ∀ c si, Init c → Reader.runExact Account.Reader.stateInit c = some si →
      si.code = some code ∧ {Pfull} si.data)
    {{sa : Cell}} (h : Reachable configRoot Init Start sa) :
    Good (fun code' data => code' = some code ∧ {Pfull} data) sa :=
  {fixed} hstart hdeploy (preserves{args_app}) h

end {ns}

#print axioms {ns}.reachable
""")
    if not args.single:
        parts["tail"] = "\n".join(out[tail_start:])
    return "\n".join(out), ns, parts


def theorem_at(module: str) -> dict[int, str]:
    """The theorem of each line of the generated module (its name, from the line that declares it)."""
    out, cur = {}, None
    for i, line in enumerate(module.splitlines(), 1):
        m = re.match(r"^theorem (\w+)", line)
        if m:
            cur = m.group(1)
        out[i] = cur
    return out


def report(output: str, ns: str, module: str, partial_check: bool = False) -> tuple[bool, str]:
    """PROVED/NOT PROVED from the checker's output: for each theorem that fails, its error (the
    paths `ran_case` reports, or what else Lean says)."""
    errors = []
    cur = None
    for line in output.splitlines():
        if line.startswith("[check] "):
            continue  # the progress of the runs (`--progress`)
        # `lean`: `file:line:col: error: msg`; `lake build`: `error: file:line:col: msg`
        m = re.match(r"^(?:(?P<k1>error|warning|info): )?(?P<f>[^ :]+\.lean):(?P<l>\d+):(?P<c>\d+): "
                     r"(?:(?P<k2>error|warning|info): ?)?(?P<msg>.*)$", line)
        if m and (m.group("k1") or m.group("k2")):
            if cur is not None:
                errors.append(cur)
            kind = m.group("k1") or m.group("k2")
            cur = (kind, int(m.group("l")), [m.group("msg")]) if kind == "error" else None
            continue
        if re.match(r"^(\S+ )?(error|warning|info|✔|⚠|ℹ|✖)", line) and cur is not None:
            errors.append(cur)
            cur = None
            continue
        if cur is not None:
            cur[2].append(line)
    if cur is not None:
        errors.append(cur)
    axioms = re.search(r"'" + re.escape(ns) + r"\.reachable' depends on axioms: \[(.*?)\]", output, re.S)
    ok_axioms = axioms is not None and set(a.strip() for a in axioms.group(1).split(",")) <= {
        "propext", "Classical.choice", "Quot.sound"}
    no_axioms = re.search(r"'" + re.escape(ns) + r"\.reachable' does not depend on any axioms", output)
    if not errors and partial_check:
        return True, "(only some kinds of transaction: no theorem over all transactions)"
    if not errors and (ok_axioms or no_axioms):
        return True, f"axioms: {axioms.group(1) if axioms else 'none'}"
    where = theorem_at(module)
    descs = {thm: desc for thm, _, _, _, desc in KINDS}
    lines = []
    for _, lineno, msg in errors:
        thm = where.get(lineno)
        head = f"{thm} ({descs[thm]})" if thm in descs else (thm or f"line {lineno}")
        if "unsolved goals" in msg[0]:
            # a goal left by the tactic: its case and its statement, without the hypotheses
            goal = [l for l in msg if l.startswith("case ") or l.startswith("⊢")]
            text = "unsolved goals (left by the tactic, not reported by it):\n  " + "\n  ".join(goal)
        else:
            text = "\n".join(msg).rstrip()
        lines.append(f"== {head} [line {lineno}]\n{text}")
    if not lines:
        lines.append(output[-4000:])
    return False, "\n\n".join(lines)


SPLIT_PKG = "ContractCheckSplit"


def check_split(args: argparse.Namespace, ns: str, parts: dict, out: Path, lake: str) -> None:
    """`--split`: the module checked in parts, each a module of its own compiled by `lean -o` into
    `<out>.split/` (on `LEAN_PATH`): first the code, the invariant and the fast twins
    (`ContractCheckSplit.Common`), then the six runs at once, each in a process of its own, then
    `preserves` and `reachable` over them (`ContractCheckSplit.Main`). The theorems are those of the
    module; what differs is that the runs import the code instead of declaring it: Lean checks the
    theorems of one module one after another once their runs evaluate a definition of that module
    (the code literal), whatever `LEAN_NUM_THREADS` says."""
    root = out.with_suffix(".split")
    if root.exists():
        shutil.rmtree(root)
    pkg = root / SPLIT_PKG
    pkg.mkdir(parents=True)
    common = f"{SPLIT_PKG}.Common"
    texts = {"Common": parts["common"]}
    for thm, block in parts["runs"].items():
        texts[thm] = f"import {common}\n\n{parts['open']}\n{block}\nend {ns}\n"
    texts["Main"] = ("\n".join([f"import {common}"] + [f"import {SPLIT_PKG}.{t}" for t in parts["runs"]])
                     + "\n\n" + parts["open"] + "\n" + parts["tail"])
    for name, text in texts.items():
        (pkg / f"{name}.lean").write_text(text)
    env = dict(os.environ)
    env.setdefault("LEAN_NUM_THREADS", "2")
    env["LEAN_PATH"] = str(root) + (os.pathsep + env["LEAN_PATH"] if env.get("LEAN_PATH") else "")
    t0 = time.time()
    deadline = t0 + args.timeout if args.timeout else None
    outputs: dict[str, str] = {}
    codes: dict[str, int | None] = {}

    def stage(names: list[str]) -> bool:
        procs = {}
        for name in names:
            f = pkg / f"{name}.lean"
            cmd = (args.wrap.split() if args.wrap else []) + [
                lake, "env", "lean", "--tstack=65536", f"--root={root}", "-o", str(f.with_suffix(".olean")), str(f)]
            logf = open(pkg / f"{name}.log", "w")
            procs[name] = (subprocess.Popen(cmd, cwd=REPO, env=env, stdout=logf, stderr=subprocess.STDOUT,
                                            text=True, start_new_session=True), logf)
        timed_out = False
        while any(p.poll() is None for p, _ in procs.values()):
            if deadline is not None and time.time() > deadline:
                for p, _ in procs.values():
                    if p.poll() is None:
                        os.killpg(p.pid, signal.SIGKILL)
                timed_out = True
                break
            time.sleep(2)
        for name, (p, logf) in procs.items():
            p.wait()
            logf.close()
            outputs[name] = (pkg / f"{name}.log").read_text()
            codes[name] = p.returncode
        return not timed_out and all(codes[n] == 0 for n in names)

    ok = stage(["Common"]) and stage(list(parts["runs"])) and stage(["Main"])
    dt = time.time() - t0
    log = out.with_suffix(".log")
    log.write_text("".join(f"=== {n}\n{o}" for n, o in outputs.items()))
    if deadline is not None and time.time() > deadline and not ok:
        print(f"NOT PROVED ({dt:.0f} s): {ns}: stopped after {args.timeout} s (the checker's output: {log})")
        sys.exit(1)
    msgs = []
    for name, output in outputs.items():
        good, msg = report(output, ns, texts[name], partial_check=(name != "Main"))
        if not good or codes[name] != 0:
            msgs.append(msg)
    if ok and not msgs:
        _, msg = report(outputs["Main"], ns, texts["Main"])
        print(f"PROVED ({dt:.0f} s): {ns}.reachable\n  {msg}\n  (checked in parts: {pkg})")
    else:
        print(f"NOT PROVED ({dt:.0f} s): {ns} (the checker's output: {log})\n\n" + "\n\n".join(msgs))
        sys.exit(1)


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("code", help="the code: a BOC file, or a tools/boc2lean source (list:..., b64:..., hex:...)")
    ap.add_argument("inv", nargs="?", help="the Inv.lean file (not with --precheck)")
    ap.add_argument("--name", help="the contract's name (namespace TvmLean.Contracts.Checked.<name>)")
    ap.add_argument("--out", help="where to write the module (default: a temporary file)")
    ap.add_argument("--wrap", default=os.environ.get("CONTRACT_CHECK_WRAP", ""),
                    help="a command the check runs under, e.g. a memory cap (default $CONTRACT_CHECK_WRAP)")
    ap.add_argument("--module", help="build the module (written by --out in the repository and a root of "
                    "its libraries) with `lake build` instead of checking the file alone")
    ap.add_argument("--single", action="store_true", help="one theorem `preserves` by `ran_preserves`")
    ap.add_argument("--only", help="only these runs (comma-separated: runs_ext, runs_extOld, runs_int, "
                    "runs_intOld, runs_tt, runs_ttOld), without the theorems that need all of them")
    ap.add_argument("--cut", type=int, help="cut the paths every N steps into auxiliary theorems "
                    "(`check.cut`; 0: no cut; default that of TvmLean/Proofs/Check/Tactic.lean)")
    ap.add_argument("--progress", action="store_true", help="print each step of the runs to the "
                    "checker's output as it goes (`check.progress`)")
    ap.add_argument("--timeout", type=int, help="stop the check after this many seconds")
    ap.add_argument("--step-heartbeats", type=int, help="the heartbeats (thousands) one step may take "
                    "(`check.stepHeartbeats`): a longer step ends its path, reported where it stands")
    ap.add_argument("--max-steps", type=int, help="at most this many steps of each run (`check.maxSteps`): "
                    "the paths not ended then are reported where they stand")
    ap.add_argument("--no-check", action="store_true", help="only generate the module")
    ap.add_argument("--split", action="store_true", help="check the module in parts, the six runs at once "
                    "in processes of their own (see `check_split`); not with --module, --single, --only")
    ap.add_argument("--precheck", action="store_true", help="only print what of the code symbolic execution "
                    "does not cover (tools/spec-coverage), before a proof")
    args = ap.parse_args()

    if args.precheck:
        sys.path.insert(0, str(REPO / "tools" / "spec-coverage"))
        import spec_coverage  # noqa: E402
        print(spec_coverage.precheck([args.code], wrap=args.wrap))
        return
    if not args.inv:
        ap.error("the Inv.lean file is needed (or --precheck)")

    text, ns, parts = generate(args)
    if args.out:
        out = Path(args.out)
        out.parent.mkdir(parents=True, exist_ok=True)
    else:
        out = Path(tempfile.mkdtemp(prefix="contract-check-")) / "Check.lean"
    out.write_text(text)
    print(f"contract-check: generated {out}")
    if args.no_check:
        return
    lake = shutil.which("lake") or str(Path.home() / ".elan" / "bin" / "lake")
    if args.split:
        if args.module or args.single or args.only:
            ap.error("--split checks the six runs: not with --module, --single or --only")
        check_split(args, ns, parts, out, lake)
        return
    if args.module:
        # a module of the repository's libraries: built by `lake` (its `.olean` kept)
        check = [lake, "build", args.module]
    else:
        # the thread stack of the library's builds (lakefile.lean, `moreLeanArgs`): the kernel checks
        # the runs' proofs on deeply nested terms
        check = [lake, "env", "lean", "--tstack=65536", str(out.resolve())]
    cmd = (args.wrap.split() if args.wrap else []) + check
    env = dict(os.environ)
    env.setdefault("LEAN_NUM_THREADS", "2")
    t0 = time.time()
    log = out.with_suffix(".log")
    print(f"contract-check: checking; the checker's output goes to {log} as it runs", flush=True)
    # its own process group, so that a timeout stops the checker under `--wrap` too
    with open(log, "w") as logf:
        proc = subprocess.Popen(cmd, cwd=REPO, env=env, stdout=logf, stderr=subprocess.STDOUT,
                                text=True, start_new_session=True)
        try:
            proc.wait(timeout=args.timeout)
            timed_out = False
        except subprocess.TimeoutExpired:
            os.killpg(proc.pid, signal.SIGKILL)
            proc.wait()
            timed_out = True
    output = log.read_text(errors="replace")
    if timed_out:
        dt = time.time() - t0
        tail = "\n".join(output.splitlines()[-20:])
        print(f"NOT PROVED ({dt:.0f} s): {ns}: stopped after {args.timeout} s (the checker's output: {log})"
              f"\n\n{tail}")
        sys.exit(1)
    dt = time.time() - t0
    ok, msg = report(output, ns, text, partial_check=bool(args.only))
    if ok and proc.returncode == 0:
        what = f"{ns}.{{{args.only}}}" if args.only else f"{ns}.reachable"
        print(f"PROVED ({dt:.0f} s): {what}\n  {msg}")
    else:
        print(f"NOT PROVED ({dt:.0f} s): {ns} (the checker's output: {log})\n\n{msg}")
        sys.exit(1)


if __name__ == "__main__":
    main()
