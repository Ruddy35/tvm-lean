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
-- ones, decidable equality, the compute-phase wrapper.
lean_lib TvmLeanProofs where
  roots := #[`TvmLean.Proofs.ModelEquiv, `TvmLean.Proofs.DecEq, `TvmLean.Semantics.Contract]

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
    `Tests.Tx.Real
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
