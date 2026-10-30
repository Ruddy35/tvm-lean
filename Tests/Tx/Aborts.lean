import Tests.Tx.Coverage

/-!
# Transactions the C++ emulator aborts on

The transaction oracle has no answer for these: `libemulator` throws an exception nothing catches,
and the process aborts. The model answers `unsupported` (as for the other aborts of C++,
`docs/model-changes.md`); `tvm-lean-tx-test` checks that on the model alone (`abortCases`).
-/

namespace Tests.Tx

open TvmLean TvmLean.Tx

/-- A message whose root is a special cell. `transaction_emulator_emulate_transaction` reads it with
`vm::load_cell_slice` (emulator/emulator-extern.cpp:117), outside any `try`, and that throws
`vm::VmError` on a special cell (crypto/vm/cells/CellSlice.cpp:1099-1139: a library cell without a
VM state, a pruned branch, any other special cell; the transaction itself would throw in
`unpack_input_msg`, crypto/block/transaction.cpp:887): the emulator process aborts (`terminate
called after throwing an instance of 'vm::VmError'`, exit by SIGABRT, for a library cell and a Merkle
proof as the message, to an account or to none). The cases: a library cell and a Merkle proof of
level 0 as the message, to an active account and to none (the address then comes from the message);
an internal message flagged special (no cell C++ holds is like it: C++ refuses the root for its flag,
`is_special`, whatever its bits). Each must be `unsupported` with the reason of `emulate`. -/
def abortCases (cfg0 : Cell) (versions : List Nat) : Array TxCase := Id.run do
  let mut out : Array TxCase := #[]
  for v in versions do
    let x : Cov.Ctx := { v, cfg := withVersion cfg0 v 46, cfgAddr := Cov.a1 }
    let msgs : List (String × Cell) :=
      [("library", libraryCellOf Cov.data1),
       ("merkle-proof", Cov.merkleProofOf (Cell.mkOrdinary #[] #[Cov.prunedOf Cov.data1])),
       ("flagged", { Cov.intMsgX (Cov.stdA 0 Cov.a1) 100000000 with special := true })]
    for (mname, m) in msgs do
      let c := x.case s!"special-msg/{mname}" (Cov.active Cov.accept) m
      out := out.push { c with name := s!"v{v}/abort/special-msg/{mname}" }
      let c := x.case s!"special-msg/{mname}/none" (mkAccount 0 Cov.a1 .none 0 0 0 0) m
      out := out.push { c with name := s!"v{v}/abort/special-msg/{mname}/none" }
  return out

/-- The answer of the model to a case the emulator aborts on: `unsupported`, with a reason that says
so. -/
def abortCheck (c : TxCase) : Option String :=
  match c.emulate with
  | .unsupported w => if w.endsWith "(C++ aborts)" then none else some s!"unsupported for another reason: {w}"
  | .ok _ _ => some "the model ran the transaction"
  | .failed r => some s!"the model failed ({r})"
  | .externalNotAccepted e => some s!"the model did not accept the message ({e})"

end Tests.Tx
