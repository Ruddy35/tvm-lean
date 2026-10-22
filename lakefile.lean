import Lake
open System Lake DSL

package "tvm-lean" where
  version := v!"0.1.0"

@[default_target]
lean_lib TvmLeanModel where
  roots := #[`TvmLean.Model, `TvmLean.Boc, `TvmLean.Spec]

@[default_target]
lean_lib TvmLeanSemantics where
  roots := #[`TvmLean.Semantics]

lean_lib TvmLean where
  roots := #[`TvmLean]

-- Whole transactions (crypto/block/transaction.cpp)
lean_lib TvmLeanTransaction where
  roots := #[`TvmLean.Transaction]

-- Machine-checked facts about the model itself: refactored definitions agree with the original
-- ones, decidable equality, the compute-phase wrapper; contract specifications (Proofs/Contracts),
-- running code on symbolic states (Proofs/Exec), well-formed VM states (Proofs/WF), kernel-fast
-- twins of the model's definitions (Proofs/Fast), induction over the transactions of an account
-- (Proofs/Tx).
lean_lib TvmLeanProofs where
  roots := #[`TvmLean.Proofs.ModelEquiv, `TvmLean.Proofs.DecEq, `TvmLean.Proofs.CellWF,
    `TvmLean.Semantics.Contract, `TvmLean.Proofs.Contracts.CellLiteral,
    `TvmLean.Proofs.Contracts.Wallet3Code, `TvmLean.Proofs.Contracts.Bits, `TvmLean.Proofs.Contracts.Spec,
    `TvmLean.Proofs.Contracts.Wallet3Spec, `TvmLean.Proofs.Contracts.Wallet3Msgs,
    `TvmLean.Proofs.Contracts.Wallet3Kernel, `TvmLean.Proofs.Exec.Step, `TvmLean.Proofs.Exec.Eval,
    `TvmLean.Proofs.Exec.Spec.Stack, `TvmLean.Proofs.Exec.Spec.Arith, `TvmLean.Proofs.Exec.Spec.Flow,
    `TvmLean.Proofs.Exec.Spec.Cell, `TvmLean.Proofs.Exec.Spec.TonEnv, `TvmLean.Proofs.Exec.Run,
    `TvmLean.Proofs.Exec.Tactic, `TvmLean.Proofs.Exec.Pilot.AddOne, `TvmLean.Proofs.Exec.Pilot.Wallet3,
    `TvmLean.Proofs.Exec.Spec.ArithExt, `TvmLean.Proofs.Exec.Pilot.ArithExt,
    `TvmLean.Proofs.Exec.Spec.StackExt, `TvmLean.Proofs.Exec.Pilot.StackExt,
    `TvmLean.Proofs.Exec.Spec.Tuple, `TvmLean.Proofs.Exec.Pilot.Tuple,
    `TvmLean.Proofs.Exec.Spec.CellExt, `TvmLean.Proofs.Exec.Pilot.CellExt,
    `TvmLean.Proofs.WF.Defs, `TvmLean.Proofs.WF.Library, `TvmLean.Proofs.WF.Monad, `TvmLean.Proofs.WF.Decode,
    `TvmLean.Proofs.WF.Step, `TvmLean.Proofs.WF.Exec.Stack, `TvmLean.Proofs.WF.Exec.Arith,
    `TvmLean.Proofs.WF.Cells, `TvmLean.Proofs.WF.Exec.Cell, `TvmLean.Proofs.WF.Exec.CellOp,
    `TvmLean.Proofs.WF.Calls, `TvmLean.Proofs.WF.Exec.Cont, `TvmLean.Proofs.WF.JoinPoints,
    `TvmLean.Proofs.WF.Exec.Flow, `TvmLean.Proofs.WF.Exec.Msg, `TvmLean.Proofs.WF.Exec.Exception,
    `TvmLean.Proofs.WF.Exec.Debug, `TvmLean.Proofs.WF.Exec.Tuple, `TvmLean.Proofs.WF.Exec.Misc,
    `TvmLean.Proofs.WF.Exec.TonEnv, `TvmLean.Proofs.WF.Exec.Crypto, `TvmLean.Proofs.WF.DictPrims,
    `TvmLean.Proofs.WF.Exec.Dict, `TvmLean.Proofs.WF.All, `TvmLean.Proofs.Fast.Twin,
    `TvmLean.Proofs.Fast.Bits, `TvmLean.Proofs.Fast.Sha256, `TvmLean.Proofs.Fast.Sha512,
    `TvmLean.Proofs.Fast.Hash, `TvmLean.Proofs.Fast.Dispatch, `TvmLean.Proofs.Fast.Run,
    `TvmLean.Proofs.Fast.Checkpoint, `TvmLean.Proofs.Fast.Wallet3, `TvmLean.Proofs.Tx.Phases,
    `TvmLean.Proofs.Tx.Compute, `TvmLean.Proofs.Tx.Decompose, `TvmLean.Proofs.Tx.Actions,
    `TvmLean.Proofs.Tx.ActionPhase, `TvmLean.Proofs.Tx.Effect, `TvmLean.Proofs.Tx.ReadBack,
    `TvmLean.Proofs.Tx.Induction, `TvmLean.Proofs.Tx.Example, `TvmLean.Proofs.Exec.Load,
    `TvmLean.Proofs.Exec.Spec.Dispatch, `TvmLean.Proofs.Exec.Spec.Crypto, `TvmLean.Proofs.Exec.Spec.Msg,
    `TvmLean.Proofs.Exec.Cont, `TvmLean.Proofs.Exec.Spec.Loop, `TvmLean.Proofs.Exec.Spec.Dict,
    `TvmLean.Proofs.Tx.Shape]
  -- the kernel checks the proofs that follow every path through a phase of a transaction
  -- (`TvmLean.Proofs.Tx.Tactic`) on deeply nested terms: a larger thread stack than the default
  moreLeanArgs := #["--tstack=65536"]

lean_lib TvmLeanValidation where
  roots := #[`TvmLean.Validation]

lean_lib TvmLeanTests where
  srcDir := "."
  roots := #[
    `Tests.Tests,
    `Tests.All,
    `Tests.Instr,
    `Tests.Harness.Registry,
    `Tests.Harness.OracleHarness,
    `Tests.Harness.FuzzHarness,
    `Tests.Harness.Runner,
    `Tests.Harness.Cli,
    `Tests.Harness.OpcodeCheck,
    `Tests.Harness.Coverage,
    `Tests.Harness.Gen.Arith,
    `Tests.Harness.Gen.Cell,
    `Tests.Harness.Gen.Tuple,
    `Tests.Harness.Gen.TonEnv,
    `Tests.Harness.Gen.Control,
    `Tests.Harness.Gen.Msg,
    `Tests.Harness.Gen.CryptoVectors,
    `Tests.Harness.Gen.Crypto,
    `Tests.Harness.Gen.VmCore,
    `Tests.Harness.Gen.Dict,
    `Tests.Harness.Gen.CellDepth,
    `Tests.Harness.Gen.Loops,
    `Tests.Harness.Gen.OwnOpcode,
    `Tests.Harness.Gen.Versions,
    `Tests.Tx.Oracle,
    `Tests.Tx.Gen,
    `Tests.Tx.Real,
    `Tests.Tx.Coverage
  ]

lean_exe "tvm-lean" where
  root := `Apps.Demo

lean_exe "tvm-lean-tests" where
  root := `Apps.Tests

lean_exe "tvm-lean-tx-test" where
  root := `Apps.TxTest

lean_exe "tvm-lean-tests-subset" where
  root := `Apps.TestsSubset

lean_exe "tvm-lean-diff-test" where
  root := `Apps.DiffTest

lean_exe "tvm-lean-audit-decoder" where
  root := `Apps.AuditDecoder

lean_exe "tvm-lean-actions-debug" where
  root := `Apps.ActionsDebug

lean_exe "tvm-lean-trace-inspect" where
  root := `Apps.TraceInspect

lean_exe "tvm-lean-precompiled-snapshot" where
  root := `Apps.PrecompiledSnapshot

lean_exe "tvm-lean-progress" where
  root := `Apps.Progress

lean_exe "tvm-lean-coverage" where
  root := `Apps.Coverage

lean_exe "tvm-lean-oracle" where
  root := `Apps.Oracle

lean_exe "tvm-lean-oracle-validate" where
  root := `Apps.Oracle
