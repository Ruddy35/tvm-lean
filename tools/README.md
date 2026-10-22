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

`tools/contract-check/examples/` has the invariants of wallet v3, wallet v2 and the simple wallet
(the code and the key never change), and a false one of wallet v3 (the seqno is always 0: `NOT
PROVED`, the path of an accepted external message). The modules TvmLean/Proofs/Check/Contracts/*.lean
were generated from them (`--out` there). The script's docstring has the details.

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
