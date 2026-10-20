# Architecture Overview

`tvm-lean` is intentionally split into three layers so proof users can depend only on
what they need.

## Model

`TvmLean/Model/` is the pure data and instruction layer:

- value/cell/slice/builder model
- control registers and VM state
- gas model and stack model
- instruction IDs/AST
- cp0 decode/encode and assembler helpers
- cryptography (hashes, signatures, elliptic curves), in Lean

`Model` contains no FFI, no IO-oriented validation machinery, and no test harness code.

## Semantics

`TvmLean/Semantics/` defines VM execution behavior:

- VM monad and stateful ops
- family handlers and dispatcher (`execInstr`)
- step/run/trace behavior

Semantics depends only on `Model`; every instruction, cryptography included, is defined in
Lean, so execution depends on nothing but the VM state.

## Validation

`TvmLean/Validation/` contains non-core validation and comparison infrastructure:

- diff-test runner and report schema
- oracle runner (Lean vs Fift `runvmx`)
- canonicalization helpers for value/cell/result comparison
- coverage/report helpers

## Spec index and source context

The instruction index is generated from the pinned vendored spec in
`third_party/tvm-specification/`.

Generated outputs:

- `docs/progress/tvm_spec_index.json`
- `docs/progress/tvm_spec_index.csv`
- `TvmLean/Spec/Index.lean`

The local clones `/workspace/ton` and `/workspace/tvm-specification` are reference
inputs for source auditing; this repository uses the pinned vendored snapshot as
source of truth.
