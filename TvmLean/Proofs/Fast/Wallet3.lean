import TvmLean.Proofs.Fast.Checkpoint
import TvmLean.Proofs.Contracts.Wallet3Spec
import TvmLean.Proofs.Contracts.Wallet3Msgs

/-!
# Wallet v3 in the kernel, with the fast forms

`TvmLean/Proofs/Contracts/Wallet3Kernel.lean` measured where kernel evaluation of the model is slow
on real code and could not finish a compute phase of wallet v3. With the fast forms of
`TvmLean/Proofs/Fast/` (each proved equal to the model's function for all inputs) and the fast twins
(`fast_decide`, `fast_rfl`), both runs it could not finish are theorems here, from the real initial
state (`initState`: the compute phase of `wallet3Code` on `wallet3Data` and an external message):

* `seqno_run`: the message with seqno 7 (`wallet3MsgSeqno`): exit code 33 (`-34` as the model
  returns `~~~33`), the gas credit untouched (not accepted), 22 steps, nothing committed;
* `ok_run`: the correctly signed message (`wallet3MsgOk`): exit code 0 (`-1`), accepted (credit 0),
  55 steps, committed, and the committed data is the old one with seqno 1 (seqno + 1), the same
  subwallet and key; checked in two declarations, the first 28 steps and the rest
  (`okAt28`, a checkpoint: `TvmLean/Proofs/Fast/Checkpoint.lean`).

## Costs before and after

Each row of `Wallet3Kernel.lean`'s table, then the two runs. *Before*: that table (`decide +kernel`
on the model, without a memory cap, a 10 GB or 8 GB cap where it says so). *After*: the same statement
by `fast_decide` (`fast_rfl` for the checkpoint), one `lake env lean` per row under
`ulimit -v 3500000` (virtual memory) and `LEAN_NUM_THREADS=2`, `Elab.async false`; time is the kernel's
"type checking" of the evaluation, memory the largest resident size of the process (about 1.25 GB of
which are the imports). Measured on the 4-core machine of the project, shared with other builds, so
times vary by some 30 %.

| What | Before | After |
|---|---|---|
| 2 VM steps from the real initial state (`SETCP0`, `19 DICTPUSHCONST`) | 0.9–2.4 s | 0.16 s, 1.29 GB |
| 3 steps, with `DICTIGETJMPZ` (two cell loads, hashing the dictionary) | 131 s; out of memory at 10 GB | 1.9 s, 1.46 GB |
| `dictLookupWithCells` of key -1 in the method dictionary | 0.16 s | 0.08 s |
| decoding an instruction of `recv_external`'s cell at bit 8 / 328 / 584 | 0.9 / 3.4 / 5.1 s, 1.5 GB | 0.08 / 0.11 / 0.10 s, 1.27 GB |
| `Slice.readBits 32` of the message at bit 277 / 853 | 2.7 / 6.7 s, 2.0 GB | 0.02 / 0.10 s, 1.26 GB |
| `bitsToByte` over a cell of 80 / 160 / 240 / 320 bits | 0.85 / 3.1 / 6.9 / 14.4 s, 2.6 GB | 0.08 / 0.17 / 0.44 / 0.36 s, 1.31 GB |
| `sha256Digest`, 1 / 2 / 3 blocks | 4.2 / 10.6 / 17.2 s, 1.8–2.9 GB | 0.35 / 0.21 / 0.27 s, 1.30 GB |
| `Cell.hashBytes`: empty cell / `wallet3Data` / `recv_external`'s cell | 4.5 / 24 s / out of memory at 8 GB | 0.17 / 0.38 / 0.27 s, 1.31 GB |
| `sha512Digest`, 1 / 2 blocks | 12.3 / 23.9 s, 2.3 / 3.5 GB | 0.95 / 1.25 s, 1.39 GB |
| `ExtMsg.signedHash` of `wallet3.msg.ok` (`HASHSU`'s hash) | out of memory at 8 GB | 0.43 s, 1.35 GB |
| `Ed25519.verify` of `wallet3.msg.ok` | 9.8 s | 2.1 s, 1.48 GB |
| `Data.decode wallet3Data` | 27 s | 0.06 s, 1.25 GB |
| `recv_external` from `afterDispatch` to `33 THROWIFNOT` (`wallet3.msg.seqno`) | 74 s, 6.3 GB | 4.2 s, 1.61 GB |
| `seqno_run`: the whole compute phase, exit 33 | some 16 GB, not run | 4.9 s, 1.80 GB |
| `ok_run`: the whole compute phase, seqno + 1 (28 steps, then 27) | out of memory at 8 GB at `HASHSU` | 7.5 + 4.7 s, 2.0 GB |

What each step bought (the sizes are for the seqno run and the first steps of the ok run):

* bit access by `List.drop`/`List.take` (`Slice.readBits`, `Array.extract`) and `bitsToNat` as a fold
  over the list: the decoder's tests went from about 0.45 s to 0.08 s an instruction, independent of
  the position in the cell;
* bits to bytes in one pass and SHA-256/SHA-512 on `Nat` words with the kernel's operations called
  directly (the notation's instances cost a few unfoldings per operation, 4 times the time): 35 ms a
  SHA-256 block instead of 4–6 s;
* the instruction dispatch flattened (`fast_dispatch execInstr`, `TvmLean/Proofs/Fast/Dispatch.lean`):
  the chain of some 300 handlers, each a match over all instructions mentioning `next`, cost about
  250 ms and tens of megabytes per instruction late in the chain (8 ms by the handler alone);
* `Array.ofFn` and `Array.append` on lists: `STU 256` (`natToBits` by 256 pushes, then 256 more
  onto the builder) alone did not fit in the cap before;
* what stays costly: hashing cells on every load (`DICTIGETJMPZ` hashes the dictionary's cells:
  about 0.2 GB for the three dispatch steps), the curve arithmetic of `Ed25519.verify` (2 s), and the
  memory the kernel keeps until a declaration ends, which grows with the length of the run: the ok run
  needs its checkpoint under the cap (in one declaration it runs out of memory).
-/

namespace TvmLean.Contracts.Wallet3.FastRuns

open TvmLean

set_option Elab.async false

/-- The public key of `tools/txoracle/contracts.fif` (of its private key `42` repeated). -/
def key : Nat := 0x2152f8d19b791d24453242e15f2eab6cb7cffa7b6a5ed30097960e069881db12

/-- `c7` of the transaction cases: `now` 1700000200, a balance of 1 Gram. -/
def c7 : Array Value :=
  ({ now := 1700000200, blockLt := 0, txLt := 0, randSeed := .int (.num 0), balanceGrams := 1000000000,
     myAddr := .null, configRoot := .null, myCode := wallet3Code, incomingGrams := 0, storageFees := 0,
     unpackedConfig := #[], duePayment := 0, precompiledGas := .null,
     inMsgParams := .null } : SmartContractInfo).toC7

/-- An external message as the transaction gives it to the VM: the body after the 277 bits of
`ext_in_msg_info`, no gas limit, a gas credit of 10000, gas max 10^6, global version 16. -/
def extInput (msg : Cell) : ComputeInput :=
  { balance := 1000000000, trigger := .message 0 msg { cell := msg, bitPos := 277, refPos := 0 } true,
    c7, gasLimit := 0, gasMax := 1000000, gasCredit := 10000, globalVersion := 16 }

/-- The initial VM state of the compute phase of `wallet3Code` on `wallet3Data`. -/
def initState (msg : Cell) : VmState := (extInput msg).init wallet3Code wallet3Data

/-- Exit code, gas credit left, steps, committed, and the committed data `c4` decoded. -/
def summary : StepResult → Int × Int × Nat × Bool × Option Data
  | .halt ec st => (ec, st.gas.gasCredit, st.steps, st.cstate.committed, Data.decode st.cstate.c4)
  | .continue st => (0, st.gas.gasCredit, st.steps, false, none)

/-- The message with seqno 7 against the stored seqno 0: `recv_external` throws 33 at
`33 THROWIFNOT`, before `ACCEPT`: the gas credit is untouched and nothing is committed. -/
theorem seqno_run :
    summary (VmState.run 100 (initState wallet3MsgSeqno)) = (-34, 10000, 22, false, none) := by
  fast_decide

-- the state after the first 28 steps of the run of `wallet3.msg.ok` (just before `CHKSIGNU`),
-- written out, and `okAt28.eq : VmState.stepsC 28 (initState wallet3MsgOk) = some okAt28`
fast_checkpoint okAt28 := VmState.stepsC 28 (initState wallet3MsgOk)

/-- The correctly signed message: the signature checks, the wallet accepts, sends the order and
commits its data with seqno 1. -/
theorem ok_run :
    summary (VmState.run 100 (initState wallet3MsgOk)) = (-1, 0, 55, true, some ⟨1, 698983191, key⟩) := by
  rw [show (100 : Nat) = 28 + 72 from rfl, VmState.run_of_stepsC 28 72 _ _ okAt28.eq]
  fast_decide

end TvmLean.Contracts.Wallet3.FastRuns
