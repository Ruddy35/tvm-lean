import TvmLean.Proofs.DecEq
import TvmLean.Proofs.Contracts.Wallet3Spec
import TvmLean.Proofs.Contracts.Wallet3Msgs

/-!
# Wallet v3 in the kernel: what `decide +kernel` evaluates, and at what cost

An experiment for the strategy of the contract proofs: can the Lean kernel evaluate the model on
the real code of wallet v3 (`wallet3Code`) and its real messages (`Wallet3Msgs.lean`), so that a
concrete run is a theorem by `decide +kernel` (evaluation by the kernel alone, no axiom)?

**Result: the model reduces in the kernel (it is total, nothing is stuck), but a whole compute
phase does not fit in this machine's memory.** The run of `wallet3.msg.seqno` from the real initial
state passes two steps (`SETCP0`, `19 DICTPUSHCONST`) in about a second. The third, `DICTIGETJMPZ`,
registers the loads of the dictionary's root and of `recv_external`'s cell
(`VmState.registerCellLoad`: gas 100 for a first load, 25 for a reload), which compares their hashes
and so hashes the dictionary's whole subtree, with a cell of 600 bits: the three steps took 131 s in a
run without a memory limit and run out of memory under a 10 GB limit (9.2 GB resident after 68 s).
From the state after the dispatch (`afterDispatch`, built by hand: the real one but for the hashes of
the loaded cells, checked equal in its outcome by the interpreter), `recv_external` runs to
`33 THROWIFNOT`: 19 steps, exit 33, gas credit untouched, in 74 s and 6.3 GB. The kernel keeps what
it evaluated until the declaration ends, so the whole run needs about the sum, some 16 GB. The run of
`wallet3.msg.ok` adds `HASHSU`, `CHKSIGNU`, `SENDRAWMSG` and more cell loads; its `HASHSU` alone does
not fit in 8 GB.

Measured on the 4-core machine of the project (Lean 4.24, one `lake env lean` per fact,
`set_option Elab.async false`; times are the kernel's "type checking", memory the largest resident
size of the process, about 1.2 GB of which are the imports):

| What | Kernel | Memory |
|---|---|---|
| 2 VM steps from the real initial state (`SETCP0`, `19 DICTPUSHCONST`) | 0.9–2.4 s | |
| 3 steps, with `DICTIGETJMPZ` (two cell loads) | 131 s; out of memory under a 10 GB limit | > 9.2 GB |
| `dictLookupWithCells` of key -1 in the method dictionary | 0.16 s | |
| decoding one instruction of `recv_external`'s cell (600 bits) at bit 8 / 328 / 584 | 0.9 / 3.4 / 5.1 s | 1.5 GB |
| `Slice.readBits 32` of the message at bit 277 / 853 | 2.7 / 6.7 s | 2.0 GB |
| the same 32 bits by `List.drop`/`List.take` on `bits.toList` | 0.27 s | |
| `bitsToByte` over a cell of 80 / 160 / 240 / 320 bits | 0.85 / 3.1 / 6.9 / 14.4 s | 2.6 GB at 320 |
| the same in one pass over the bit list, 320 / 1000 bits | 0.08 / 0.23 s | |
| `sha256Digest`, 1 / 2 / 3 blocks | 4.2 / 10.6 / 17.2 s | 1.8 / 2.3 / 2.9 GB |
| SHA-256 on `Nat` words with masks, 1 / 3 blocks | 1.3 / 4.4 s | |
| `Cell.hashBytes`: empty cell / `wallet3Data` (320 bits) / `recv_external`'s cell (600 bits) | 4.5 / 24 s / out of memory at 8 GB | |
| `sha512Digest`, 1 / 2 blocks | 12.3 / 23.9 s | 2.3 / 3.5 GB |
| `ExtMsg.signedHash` of `wallet3.msg.ok` (`HASHSU`: 104 bits at bit 789 and the order's cell of 448 bits) | out of memory at 8 GB after 60 s | > 7 GB |
| `Ed25519.verify` of `wallet3.msg.ok` (hash, key, signature as literals) | 9.8 s | |
| of it: `powMod` (an inversion) / `decodePoint` / SHA-512 | 0.04 / 0.12 / ~10 s | |
| `Data.decode wallet3Data` | 27 s | |
| `recv_external` from `afterDispatch` to `33 THROWIFNOT` (`wallet3.msg.seqno`) | 74 s | 6.3 GB |

Where the time goes (kernel diagnostics: `List.get`, `List.casesOn`, `Nat.casesOn` dominate):

* **bit access**: a `BitString` is an `Array Bool`, a list underneath; `bs[i]!` and the loop of
  `Array.extract` (`Slice.readBits`: the decoder's 24-bit window, every `LDU`/`LDSLICEX`/`PLDU`) walk
  the list from its head with a `Fin` index for every bit, so reading `n` bits at position `p` costs
  `n · p` steps, and the kernel keeps every intermediate term: time and memory grow with the position
  in the cell, quadratically for a whole cell;
* **hashing on every cell load**: the gas of a load depends on whether the cell was loaded before,
  decided by comparing representation hashes (`VmState.registerCellLoad`), so `CTOS`, dictionary
  lookups and implicit jumps compute cell hashes; a hash is `bitsToByte` over the cell (the bit
  access above, quadratic) and SHA-256;
* **SHA-256 and SHA-512 compression** on `UInt32`/`UInt64`: about 0.5 ms per word operation through
  the `BitVec`/`Fin` layers, 4–6 s per SHA-256 block and 12 s per SHA-512 block;
* not the decoder's tables, not gas arithmetic, not the dictionary traversal, not the elliptic-curve
  arithmetic (`Nat` with the kernel's GMP acceleration: microseconds per operation).

What follows for the proofs:

* whole runs by `decide +kernel` are not a basis for the contract proofs, not even for concrete
  ones; the proofs need symbolic execution (rewriting step by step with lemmas per instruction and
  per code position), where the decoder's result at each position of the fixed code is a lemma proved
  once (`decode_*` below: 1–5 s each);
* the hashes of `VmState.registerCellLoad` only decide between gas 100 and 25: an invariant proof can
  take both branches (the cell seen or not) instead of computing hashes, and must, for cells built
  from symbolic data;
* if concrete runs in the kernel are wanted (test vectors as theorems), the model's bit-level
  primitives can be rewritten in a kernel-friendly form with proofs of equality to the current ones,
  as in phase 0: `Slice.readBits`/`Array.extract` of bits by `List.drop`/`List.take` on the bit list
  (25 times faster above), `bitsToByte`/`bitStringToBytesBE` in one pass (180 times faster at 320 bits,
  and linear), SHA-256 on `Nat` words (3–4 times faster).

The theorems below are the cheap facts of the table, kept as a check that kernel evaluation of the
model still works and as a measure of its cost (about 25 s for the module). The heavy ones are
reproduced by these statements (with the definitions of this module):

    theorem seqno_throws_33 : summary (VmState.run 100 (afterDispatch wallet3MsgSeqno)) =
        (-34, 10000, 22, false) := by decide +kernel          -- 74 s, 6.3 GB
    theorem seqno_full : summary (VmState.run 100 (initState wallet3MsgSeqno)) =
        (-34, 10000, 22, false) := by decide +kernel          -- some 16 GB: not run
-/

namespace TvmLean.Contracts.Wallet3.Kernel

open TvmLean

-- one kernel check at a time: each keeps all it evaluated until it ends (the module peaks at 2.6 GB)
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
`ext_in_msg_info` (no `StateInit`, the body in place), no gas limit, a gas credit of 10000, gas max
10^6, global version 16. -/
def extInput (msg : Cell) : ComputeInput :=
  { balance := 1000000000, trigger := .message 0 msg { cell := msg, bitPos := 277, refPos := 0 } true,
    c7, gasLimit := 0, gasMax := 1000000, gasCredit := 10000, globalVersion := 16 }

theorem extInput_valid (msg : Cell) : (extInput msg).Valid := by
  simp [ComputeInput.Valid, extInput, ComputeInput.isExternal]

/-- The initial VM state of the compute phase of `wallet3Code` on `wallet3Data`. -/
def initState (msg : Cell) : VmState := (extInput msg).init wallet3Code wallet3Data

/-- `recv_external`'s cell, the value of key -1 in the method dictionary. -/
def recvExternalCell : Cell := wallet3Code.refs[0]!.refs[1]!

/-- The state after the dispatch (`SETCP0`, `19 DICTPUSHCONST`, `DICTIGETJMPZ`), built by hand: the
continuation of `recv_external` (bit 8 of its cell), the stack without the selector, the gas of the
three steps (286); unlike the real state, no hashes of loaded cells (they change no gas on the
paths of `wallet3.msg.seqno` and `wallet3.msg.ok`: the interpreter gives the same exit code, steps,
gas, `c4` and `c5` from here as from `initState`). -/
def afterDispatch (msg : Cell) : VmState :=
  let s := initState msg
  { s with cc := .ordinary { cell := recvExternalCell, bitPos := 8, refPos := 0 } (.quit 0) OrdCregs.empty
                  OrdCdata.empty,
           stack := s.stack.pop, gas := { s.gas with gasRemaining := 9714 }, steps := 3 }

/-- Exit code, gas credit left, steps, committed. -/
def summary : StepResult → Int × Int × Nat × Bool
  | .halt ec st => (ec, st.gas.gasCredit, st.steps, st.cstate.committed)
  | .continue st => (0, st.gas.gasCredit, st.steps, false)

/-! ## Facts by kernel evaluation -/

/-- The first two steps of the real compute phase (`SETCP0`, `19 DICTPUSHCONST`). -/
theorem run2_steps : (VmState.run 2 (initState wallet3MsgSeqno)).state.steps = 2 := by decide +kernel

/-- The dispatch's lookup: key -1 is `recv_external`, at bit 8 of its cell, two cells visited. -/
theorem lookup_recv_external :
    (match dictLookupWithCells (some wallet3Code.refs[0]!) ((dictKeyBits? (-1) 19 false).getD #[]) with
      | .ok (some s, cells) => (s.bitPos, s.refPos, cells.size)
      | _ => (0, 0, 0)) = (8, 0, 2) := by decide +kernel

/-- The first instruction of the code: `SETCP0`. -/
theorem decode_root : (match decodeCp0WithBits (Slice.ofCell wallet3Code) with
    | .ok (i, n, _) => some (i, n) | .error _ => none) = some (.setcp 0, 16) := by decide +kernel

/-- The first instruction of `recv_external`: `9 PUSHPOW2`. -/
theorem decode_recv_external_first :
    (match decodeCp0WithBits { cell := recvExternalCell, bitPos := 8, refPos := 0 } with
      | .ok (i, n, _) => some (i, n) | .error _ => none) = some (.pushPow2 9, 16) := by decide +kernel

/-- The last instruction of `recv_external`: `c4 POP`, at bit 584 (5 s: the decoder's window is read
bit by bit from the head of the cell). -/
theorem decode_recv_external_last :
    (match decodeCp0WithBits { cell := recvExternalCell, bitPos := 584, refPos := 0 } with
      | .ok (i, n, _) => some (i, n) | .error _ => none) = some (.popCtr 4, 16) := by decide +kernel

/-- The representation hash of the empty cell: one SHA-256 block. -/
theorem empty_cell_hash : Cell.empty.hashBytes =
    #[0x96, 0xa2, 0x96, 0xd2, 0x24, 0xf2, 0x85, 0xc6, 0x7b, 0xee, 0x93, 0xc3, 0x0f, 0x8a, 0x30, 0x91,
      0x57, 0xf0, 0xda, 0xa3, 0x5d, 0xc5, 0xb8, 0x7e, 0x41, 0x0b, 0x78, 0x63, 0x0a, 0x09, 0xcf, 0xc7] := by
  decide +kernel

/-- The hash of the signed part of `wallet3.msg.ok` (what `HASHSU` computes, by
`tools/boc2lean/boc2lean.py`'s hashing). -/
def okSignedHash : Array UInt8 :=
  #[0x12, 0xd6, 0x82, 0x99, 0xd9, 0xbc, 0x46, 0x0f, 0x49, 0x6c, 0x26, 0x25, 0x14, 0x9a, 0x10, 0xc8,
    0x59, 0x0e, 0x42, 0x75, 0x95, 0x4f, 0xf6, 0xcc, 0x85, 0x9f, 0x21, 0xfe, 0x79, 0xe0, 0x31, 0xc3]

/-- The signature of `wallet3.msg.ok` (its first 512 bits after the header). -/
def okSignature : Array UInt8 :=
  #[0xdc, 0x81, 0x63, 0x54, 0xf5, 0x61, 0xa8, 0xec, 0x3c, 0x43, 0x89, 0x0f, 0xe9, 0xd4, 0x91, 0x2e,
    0x22, 0x13, 0xf9, 0x23, 0x96, 0x28, 0x22, 0x82, 0x76, 0x65, 0x34, 0x56, 0xbc, 0x64, 0x11, 0x0b,
    0xe3, 0xfa, 0x80, 0x3a, 0xe9, 0x9a, 0xbb, 0x5b, 0x74, 0x1a, 0x56, 0x5c, 0x72, 0x41, 0x07, 0x5f,
    0x0d, 0x5c, 0x38, 0x1c, 0x44, 0x04, 0x1e, 0xa6, 0x01, 0x82, 0xcf, 0x98, 0xc2, 0x9f, 0x20, 0x06]

/-- Ed25519 in the kernel: the signature of `wallet3.msg.ok` verifies with the wallet's key over the
hash of the signed part (10 s, nearly all of it SHA-512). -/
theorem ok_signature_verifies : Ed25519.verify okSignedHash (natToBytesBEFixed key 32) okSignature = true := by
  decide +kernel

end TvmLean.Contracts.Wallet3.Kernel
