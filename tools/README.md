# Tools

Small helper scripts for spec indexing, test scaffolding, validation runs, and backlog sync.

## Generate spec index

```sh
python3 tools/gen_spec_index.py
```

Outputs:

- `docs/progress/tvm_spec_index.json`
- `docs/progress/tvm_spec_index.csv`
- `TvmLean/Spec/Index.lean`

## Generate test scaffold + import index

```sh
python3 tools/gen_test_scaffold.py
```

Outputs:

- `Tests/Instr/<Family>/*.lean` skeletons (for missing instructions)
- `Tests/All.lean`

## Generate progress table

```sh
python3 tools/gen_instruction_progress.py
```

Outputs:

- `docs/progress/instructions_full.csv`

## Cell literals for proofs (BOC to Lean)

```sh
python3 tools/boc2lean/boc2lean.py --module TvmLean.Proofs.Contracts.Wallet3Code \
  --out TvmLean/Proofs/Contracts/Wallet3Code.lean wallet3Code=list:tools/txoracle/contracts.txt#wallet3.code
```

Turns any BOC (a file, base64, hex, or an entry of `tools/txoracle/contracts.txt`) into a Lean module
with `def <name> : Cell` as nested cell literals, the BOC, its representation hash and a `#guard` that
the project's BOC reader reads the BOC as the literal (`--kernel-hash`: also a kernel-checked theorem
on the hash). The script's docstring has the details.

## Invariants of a contract over all transactions

```sh
tools/contract-check/contract-check list:tools/txoracle/contracts.txt#wallet3.code \
  tools/contract-check/examples/wallet3.lean --name Wallet3
```

From a contract's code (a BOC: a file, or any source of `tools/boc2lean`) and a file with the
invariant of its data (`Inv.lean`: a predicate on the data cell, the definitions it needs, and the
lines `-- contract-check: invariant/params/hints`), generates a Lean module that states, for every
shard account reachable by transactions (any messages, times, configurations, libraries,
tick-tock; from start states and deployments that satisfy the invariant, the theorem's
hypotheses), that the account keeps the code and data satisfying the invariant
(`TvmLean.Tx.Reachable.code_fixed`), and proves its obligation with no proof about the contract:
the code runs symbolically from every state the compute phase may start it from (an external
message, an internal message, tick-tock; global version from 4 and below; any gas, `c7`,
libraries, loaded cells), every path to its end (`ran_case`, TvmLean/Proofs/Check/Tactic.lean).
It checks the module (`lake env lean`, under `--wrap`, e.g. a memory cap) and prints `PROVED` with
the axioms of the theorem, or `NOT PROVED` with every path where the invariant is not shown: the
kind of transaction, the code position (cell, bit, instruction), the exit code, the path condition
and the goal left. `--only runs_ext,...` checks some kinds of transaction only, `--cut N` sets
how often a path is cut into auxiliary theorems.

A contract whose code may change (`SETCODE`) adds the line `-- contract-check: code K`: `K` is the
condition on a code a committed run installs, a predicate on the body of the message (`none` for
tick-tock) and the code (e.g. "the body is signed with the owner's key"). The runs are then stated
with the action lists `Acts K` (TvmLean/Proofs/Tx/Acts.lean: the actions of every instruction of the
model, `SETCODE` with a code satisfying `K`), and `reachable` holds while the code is the checked
one (`TvmLean.Tx.ReachableWhile.good_codes`, TvmLean/Proofs/Tx/Upgrade.lean): the data satisfies the
invariant while the code is the checked one, and every code the account has is the checked one or
one that `K` admits for the body of some message (`Installable K`; what an installed code does is
not known). `code self` (every `SETCODE` installs the code itself) keeps the statement of a code
that never changes (`TvmLean.Tx.Reachable.code_self`, by `Reachable.spec`).

`--precheck` prints, before a proof, which instructions and control-flow patterns of the code
symbolic execution does not cover (`tools/spec-coverage`, below).

The runs need nothing about the code beyond the invariant (TvmLean/Proofs/Check/Unknown.lean,
TvmLean/Proofs/Check/Loops.lean):

* loads of cells are taken by their outcomes (`check_havoc`): normally or out of gas, with new gas
  and loaded cells (and, for cells that may be libraries, loaded libraries): the cells of a message
  or of a dictionary the code does not know, and those of the code itself, whose gas followed load
  by load is a term that grows with each load;
* dictionaries the code does not know, of a message or of the data: every outcome of a lookup,
  `DICT*GETNEXT`/`GETPREV`/`MIN`/`MAX`, a delete or a set is a case, and what the map of the
  dictionary says of it is added (`check_dict_facts`, TvmLean/Proofs/Exec/Dict/Near.lean: the key
  found by `DICTIGETNEXT` is the least key of the map after the given one, its value the map's);
  an invariant can speak of a dictionary of the data through its map (`Dict.value`, `Dict.WF`);
* calls with arguments and return values (`CALLXARGS`, `RETARGS`, `CALLDICT`), configuration
  parameters (`CONFIGPARAM` of an unknown configuration);
* a loop is closed with the invariant "the state is the loop head but for the gas, the loaded cells
  and libraries, the counters, the action list (`SafeActs`) and the top stack entry"; a loop whose
  state is more of the stack takes a line `-- contract-check: loop k Q`: the top `k` entries may
  change in any way that keeps `Q` (a predicate of `k` values in which the parameters may appear).

`--progress` writes each step to the checker's log (`<out>.log`) as it goes.

`tools/contract-check/examples/` has the invariants of wallet v3, wallet v2 and the simple wallet
(the code and the key never change), and a false one of wallet v3 (the seqno is always 0: `NOT
PROVED`, the path of an accepted external message); of the highload wallet v1 (`DICTIGETNEXT` over a
dictionary of the message), the simple wallet with procedures (`CALLDICT`), the restricted wallet v1
(calls with arguments, `CONFIGPARAM`), the highload wallet v2 (a dictionary in the data and a loop
over it with a loop invariant) and an upgradable wallet (`upgradable-wallet.fif`, assembled into
`upgradable-wallet.boc` by the reference Fift: an external message signed with the key may install a
new code; the condition `Signed key`). The modules TvmLean/Proofs/Check/Contracts/*.lean were
generated from some of them (`--out` there). It also has the invariants of the corpus of mainnet
contracts (`Tests/Tx/Corpus.lean`): wallet v4r2 and v5r1 (`wallet4.lean`, `wallet5.lean`: the code,
the key and the subwallet or wallet id never change, the seqno never decreases), the jetton wallet
of TEP-74 (`jetton-wallet.lean`: the owner, the master and the wallet code never change, the balance
stays a `Coins` amount) and the NFT item of TEP-62 (`nft-item.lean`: the index and the collection
never change), all `NOT PROVED` for now (docs/audit/README.md, section 4). The script's docstring
has the details.

`examples/storage.lean` is TON Storage (`list:tools/txoracle/contracts.txt#storage.code`, the code
of `storage-contract-code.boc`): the data is `Contracts.Storage.Data.encode d` within its widths (the
layout, TvmLean/Proofs/Contracts/StorageData.lean, and its reads, StorageRun/Read.lean, as hints),
its provider, Merkle root, file size, rate, longest span paid, client and torrent hash never change,
and an active contract stays active. Its runs take what TvmLean/Proofs/Check/Framed.lean adds to the
steps (`check_extra_step`): `CTOS` of a cell of the message and `DICTUGET` on a dictionary of the
body by the framed rules (any slice, any value, or an exception), `LDMSGADDR` of any slice, `CTOS` of
data the run wrote (ordinary by definition), an exception that ends the run closed at once (kept as
`VmState.raiseDead`), `c7` after `RAND` made a variable again (TvmLean/Proofs/Check/Forget.lean);
its Inv file tags with `check_close` (TvmLean/Proofs/Check/Attr.lean) what the ends of the paths
unfold (`Data.encode` written out, compared with the cell the code built). Its two runs of internal
messages take nearly all the time; `--split` checks the six runs at once, in processes of their own
(in one module Lean checks them one after another).

## What symbolic execution covers: instructions, patterns, a contract's code

```sh
export LEAN_NUM_THREADS=1   # processes × threads within the cores: overloaded, probes hit their timeout
python3 tools/spec-coverage/spec_coverage.py patterns --jobs 12 --timeout 2700 --save   # --regen: probes.txt by fift
python3 tools/spec-coverage/spec_coverage.py inventory --deep --jobs 14 --save --raw inv.tsv
python3 tools/spec-coverage/spec_coverage.py precheck --save   # the codes of contracts.txt; after inventory (forms.json)
python3 tools/spec-coverage/spec_coverage.py inventory --from-raw inv.tsv --md docs/audit/spec-coverage.md
tools/contract-check/contract-check list:tools/txoracle/contracts.txt#wallet3.code --precheck
```

`inventory`: every one of the 919 instruction forms of the decoder (the opcode ranges of
`third_party/tvm-specification`), sampled over its arguments and decoded by the model, classified in
the environment of `tools/contract-check` (`tools/spec-coverage/SpecCoverage.lean`, run by
`lake env lean`): a `vm_spec` lemma that `vm_step` uses for it, or its handler, statically (the VM
programs it runs: computed by a `vm_run` lemma, unfolded, or blocking) and, with `--deep`, by running
it on a symbolic stack of its signature; the lemmas of `TvmLean/Proofs/Exec/` that contract-check does
not import are counted apart. Writes the table per family (`docs/audit/spec-coverage.md`) and the
result per form (`tools/spec-coverage/forms.json`). `patterns`: the control-flow patterns (calls with
closure data, loops, `TRY`, `CALLDICT`, `RUNVM`, actions, unknown dictionaries, configuration
reads, ...), each tried by small codes (`probes.fif`) run by `ran_case`; results in
`probe-results.json`. `precheck` (or `contract-check <code> --precheck`): the code reachable from a
contract's code (implicit `JMPREF`, `PUSHCONT`, `CALLREF`, `IF*REF`, the procedures of
`DICTPUSHCONST`) disassembled and classified, with the patterns it uses: the gaps before a proof
starts (`--save`: the summaries of the codes of `tools/txoracle/contracts.txt` for the document).
The Lean side needs the proof library's modules of `TvmLean/Proofs/Exec/` built (some 2 GB of
memory per process); `--deep` takes about an hour with 12 processes on a 16-core server.

## Oracle parity sweeps (Lean vs Fift runvmx)

Run per-instruction parity in parallel (all instructions by default):

```sh
tools/run_oracle_validate.sh --jobs 12 --variants 20 --code-variants 8 --cases 20
```

Notes:

- `--cases auto` resolves to `variants * code-variants` to saturate the generated code×stack matrix.
- Real-time per-instruction PASS/FAIL lines are printed to stdout.
- Progress is also appended to `oracle/runs/<ts>/progress.log`.

Run the extensive all-instruction multi-seed matrix:

```sh
tools/run_oracle_validate_extensive.sh
```

## Collect and promote diff fixtures

Build collector and sweep:

```sh
export TON_FIFT_BIN=/path/to/ton/build/crypto/fift
export TON_FIFT_LIB=/path/to/ton/crypto/fift/lib

cd diff-test/collector
npm ci
npm run build
npm run sweep -- --since 2026-02-06 --until 2026-02-07 --max-fixtures 500 --keep-fixtures --out-dir ../work
```

Test scratch fixtures:

```sh
lake exe tvm-lean-diff-test -- --dir diff-test/work --strict-exit
```

Promote one validated fixture:

```sh
python3 tools/promote_fixture.py diff-test/work/<fixture>.json
```

## Sync Linear backlog (bulk)

This repo tracks the full TVM instruction backlog in Linear (one issue per instruction + one issue per Fift alias).

The `tools/linear_sync.py` script syncs Linear against `docs/progress/tvm_spec_index.json` using the Linear GraphQL API.

Dry-run:

```sh
python3 tools/linear_sync.py
```

Apply (creates/updates issues):

```sh
cp .env.example .env  # then set LINEAR_API_KEY=... (or export LINEAR_API_KEY in your shell)
LINEAR_API_KEY="lin_api_..." python3 tools/linear_sync.py --apply
```

The sync script also reads `LINEAR_API_KEY` from `.env` at the repo root (if present).

Normalize/upgrade older issue descriptions to the canonical template:

```sh
python3 tools/linear_sync.py --apply --sync-descriptions
```

Verify completeness (expects 919 TVM + 116 Fift):

```sh
python3 tools/linear_sync.py --verify
```

## Create standard subissues (ws/*)

To keep “one PR per issue”, we work in subissues labeled `ws/*` (impl/tests/diff/spec-audit/proof) under each
instruction issue.

Dry-run:

```sh
python3 tools/linear_subissues.py
```

Apply (bulk create missing subissues):

```sh
python3 tools/linear_subissues.py --apply
```

## Auto-create PRs for completed Codex tasks

When issues are delegated to Codex via Linear, Codex will usually post a comment and create a cloud task, but **PR
creation still requires a `/pr` call**. This helper automates that step.

Setup:

```sh
cp .env.example .env
# set CODEX_TOKEN=... in .env (kept local; gitignored)
```

One-shot run (recommended for cron):

```sh
python3 tools/codex_autopr.py --once
```

Daemon mode:

```sh
python3 tools/codex_autopr.py --watch --interval-seconds 60
```

Notes:

- The script only targets tasks whose Codex `environment_label` contains `tvm-lean` (configurable via `--env-label-substr`).
- Local state is stored in `.autopr/state.sqlite3` to avoid duplicate PR creation attempts.

## Auto-merge PRs (local daemon)

GitHub Actions scheduling is too coarse for “merge within ~1 minute”, and Codex approvals are currently signaled via
GitHub reactions. This daemon enforces the rules locally and merges PRs automatically.

Setup:

```sh
cp .env.example .env
# GitHub auth: set GITHUB_TOKEN=... in .env, or rely on an existing GitHub CLI login (`gh auth login`).
```

One-shot run:

```sh
python3 tools/github_automerge.py --once --verbose
```

Daemon mode (recommended):

```sh
python3 tools/github_automerge.py --watch --interval-seconds 60 --verbose
```

Defaults (configurable via flags):

- Only considers PRs whose head branch starts with `codex/` (set `--head-branch-prefix ''` to disable).
- Requires `Lean` + `Collector (TypeScript)` checks to pass.
- Requires a `+1` reaction from `chatgpt-codex-connector[bot]`.
- If a PR is behind `main`, it triggers “Update branch” and re-checks on the next cycle.

## GitHub → Linear backflow (close PR as “not planned”)

If you close a PR as “not planned”, it usually means the corresponding Linear issue should go back to `Todo` and be
unassigned from Codex.

Setup:

```sh
cp .env.example .env
# set LINEAR_API_KEY=... in .env (kept local; gitignored)
# GitHub auth: set GITHUB_TOKEN=... in .env, or rely on an existing GitHub CLI login (`gh auth login`).
```

One-shot run:

```sh
python3 tools/github_linear_backflow.py --once --verbose
```

Daemon mode:

```sh
python3 tools/github_linear_backflow.py --watch --interval-seconds 60 --verbose
```

Notes:

- Only scans PRs whose head branch starts with `codex/` by default (set `--head-branch-prefix ''` to disable).
- Detects the Linear issue id from the PR title / branch (e.g. `TVM-5997`).
- Resets the Linear issue state to `Todo` and clears assignee/delegate if it looks like Codex.
