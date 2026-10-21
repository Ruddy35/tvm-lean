import TvmLean.Proofs.Exec.Tactic
import TvmLean.Semantics.Contract

/-!
# Pilot: the opening of wallet v3's `recv_external`, on any message

The code of wallet v3 (`crypto/smartcont/wallet3-code.fc`, compiled `auto/wallet3-code.fif`; the
cell `wallet3.code` of `tools/txoracle/contracts.txt`, which the transaction cases run) written out
as cells (`Wallet3.code`): the root dispatches on the method id through a dictionary whose leaf for
the id -1 holds `recv_external` after an 8-bit label. The procedure starts

  `9 PUSHPOW2  LDSLICEX  DUP  32 LDU  32 LDU  32 LDU  s0 s2 XCHG  NOW  LEQ  35 THROWIF ...  ACCEPT`

(the signature, then the subwallet id, the expiry time and the sequence number of the message
body), so a body shorter than `512 + 32 + 32 + 32` bits makes one of the four loads fail with
cell underflow (exception 9) before `ACCEPT`, whatever the rest of the message, the contract's data
or its balance are.

`Wallet3.recvExternal_short_body` proves it from the bytecode, by `vm_run`, for the state in which
the procedure starts on an external message (`Wallet3.entry`: the stack `balance, value, message,
body` the dispatcher leaves, the gas of an external message before `ACCEPT`, a credit of 10000, the
exception handler of the compute phase); `Wallet3.recvExternal_short_body_outcome` is what the
compute phase keeps: exit code 9, the data and the actions rolled back. The dispatcher's own steps
(`SETCP0`, `DICTPUSHCONST`, `DICTIGETJMPZ`) are not covered here.
-/

namespace TvmLean.Pilot.Wallet3

/-- The bits of the root: `SETCP0`, `19 DICTPUSHCONST` (the dictionary is the reference), `DICTIGETJMPZ`, `11 THROWARG`. -/
def rootBits : BitString := #[
    true, true, true, true, true, true, true, true, false, false, false, false,
    false, false, false, false, true, true, true, true, false, true, false, false,
    true, false, true, false, false, true, false, false, false, false, false, true,
    false, false, true, true, true, true, true, true, false, true, false, false,
    true, false, true, true, true, true, false, false, true, true, true, true,
    false, false, true, false, true, true, false, false, true, false, false, false,
    false, false, false, false, true, false, true, true]

/-- The bits of the root of the method dictionary (a fork). -/
def dictBits : BitString := #[
    false, false]

/-- The bits of the fork of the methods with non-negative ids. -/
def forkBits : BitString := #[
    false, true, false, false]

/-- The bits of `recv_internal` (id 0): the label, then `DROP`. -/
def recvInternalBits : BitString := #[
    true, true, false, true, false, false, false, false, false, false, true, true,
    false, false, false, false]

/-- The bits of the fork of the get-methods. -/
def getterForkBits : BitString := #[
    false, true, false, false]

/-- The bits of `seqno` (id 85143). -/
def seqnoBits : BitString := #[
    true, false, true, true, true, false, true, true, false, false, true, true,
    true, false, false, true, true, true, false, false, true, true, true, false,
    true, true, false, true, false, true, false, false, false, true, false, false,
    true, true, false, true, false, false, false, false, true, true, false, true,
    false, false, true, true, false, false, true, true, true, true, true, true,
    false, false, true, true, false, false, false, true, true, true, false, true,
    false, true, true, true, false, false, false, false, true, false, true, true,
    true, true, true, true, true, true, true, true]

/-- The bits of `get_public_key` (id 78748). -/
def publicKeyBits : BitString := #[
    true, false, true, true, true, false, false, false, true, true, false, false,
    true, false, false, true, false, true, true, true, true, true, true, false,
    true, true, false, true, false, true, false, false, false, true, false, false,
    true, true, false, true, false, false, false, false, true, true, false, true,
    false, true, true, true, false, false, false, false, true, false, true, true,
    false, false, false, true, true, true, true, true]

/-- The bits of `recv_external` (id -1): the 8-bit label (`hml_same`, 18 ones), then the procedure. -/
def recvExternalBits : BitString := #[
    true, true, true, true, false, false, true, false, true, false, false, false,
    false, false, true, true, false, false, false, false, true, false, false, false,
    true, true, false, true, false, true, true, true, false, false, false, true,
    true, false, false, false, false, false, true, false, false, false, false, false,
    true, true, false, true, false, false, true, true, false, false, false, true,
    true, true, true, true, true, true, false, true, false, false, true, true,
    false, false, false, true, true, true, true, true, true, true, false, true,
    false, false, true, true, false, false, false, true, true, true, true, true,
    false, false, false, false, false, false, true, false, true, true, true, true,
    true, false, false, false, false, false, true, false, false, false, true, true,
    true, false, true, true, true, false, true, true, true, true, true, true,
    false, false, true, false, false, true, true, false, false, false, true, true,
    true, true, true, false, true, true, false, true, false, true, false, false,
    false, true, false, false, true, true, false, true, false, false, false, false,
    true, true, false, true, false, false, true, true, false, false, false, true,
    true, true, true, true, true, true, false, true, false, false, true, true,
    false, false, false, true, true, true, true, true, true, true, false, true,
    false, false, true, true, true, true, true, true, true, true, true, true,
    true, true, false, true, false, false, false, true, false, true, false, true,
    false, false, false, true, false, false, true, true, false, false, true, false,
    true, false, true, true, true, false, true, false, true, true, true, true,
    false, false, true, false, true, false, true, false, false, false, false, true,
    false, true, false, true, false, false, false, true, false, true, false, false,
    false, true, false, false, true, false, true, true, true, false, true, false,
    true, true, true, true, false, false, true, false, true, false, true, false,
    false, false, true, false, false, false, false, false, false, true, false, false,
    true, true, true, true, true, false, false, true, false, false, false, false,
    false, false, false, true, false, true, false, true, false, true, false, false,
    false, false, false, true, false, false, false, false, false, true, false, true,
    false, true, false, true, true, true, true, true, true, false, false, true,
    false, false, false, true, false, false, false, false, true, true, true, true,
    false, false, true, false, true, false, true, false, false, false, true, true,
    true, true, true, true, true, false, false, false, false, false, false, false,
    false, false, false, false, true, false, false, true, false, false, true, true,
    false, false, true, false, false, false, false, false, true, true, false, true,
    false, true, true, true, false, true, false, false, true, false, true, false,
    true, false, false, true, false, true, true, false, true, true, false, true,
    false, false, true, true, false, false, false, false, false, true, true, true,
    true, true, false, true, false, true, false, false, false, false, false, false,
    false, false, true, false, true, true, true, true, true, false, true, true,
    false, false, false, false, false, false, false, false, true, true, true, false,
    true, false, false, false, false, false, true, true, false, false, false, false,
    false, false, false, false, false, false, false, true, true, false, true, false,
    false, true, false, false, true, true, false, false, true, false, false, false,
    true, true, false, false, true, false, true, true, false, false, false, true,
    true, true, true, true, true, true, false, false, true, false, true, true,
    false, false, false, true, true, true, true, true, true, true, false, false,
    true, false, true, true, true, true, true, true, true, true, true, true,
    true, true, false, false, true, false, false, true, true, true, true, false,
    true, true, false, true, false, true, false, true, false, true, false, false]

/-- `recv_external`: the leaf of the method dictionary for the id -1. -/
def recvExternal : Cell := Cell.mkOrdinary recvExternalBits #[]

/-- The code of wallet v3. -/
def code : Cell :=
  Cell.mkOrdinary rootBits #[Cell.mkOrdinary dictBits #[
    Cell.mkOrdinary forkBits #[Cell.mkOrdinary recvInternalBits #[],
      Cell.mkOrdinary getterForkBits #[Cell.mkOrdinary seqnoBits #[], Cell.mkOrdinary publicKeyBits #[]]],
    recvExternal]]

/-- `recv_external` is the leaf of the code's method dictionary (reference 1 of the dictionary's
root, reference 0 of the code). -/
theorem recvExternal_in_code : code.refs[0]!.refs[1]! = recvExternal := rfl

/-- The state in which `recv_external` starts on an external message with body `body` (the
dispatcher has dropped the method id): the stack `balance, value, message, body`, the procedure
after its label as the current continuation, `c0` the end of the run and `c2` the exception
handler of the compute phase, the gas of an external message (no limit, a credit of 10000 before
`ACCEPT`); the rest of `st` (the data `c4`, `c7`, the version) is anything. -/
def entry (st : VmState) (balance value : Int) (msg : Cell) (body : Slice) (gasMax : Int) : VmState :=
  { st with stack := (((#[].push (.int (.num balance))).push (.int (.num value))).push (.cell msg)).push (.slice body),
            cc := .ordinary ⟨recvExternal, 8, 0⟩ (.quit 0) OrdCregs.empty OrdCdata.empty, cp := 0,
            chainJumps := 0, librariesRefused := #[], librariesMissed := #[], maxLibraryLoads := none,
            regs := { st.regs with c0 := .quit 0, c2 := .excQuit },
            gas := ⟨gasMax, 0, 10000, 10000, 10000⟩ }

/-- **A body shorter than the signature and the three 32-bit fields makes `recv_external` fail
with cell underflow before `ACCEPT`.** The run halts with exit code `~~~9` (exception 9) and the
gas credit untouched (`ACCEPT` would set it to 0), for any balance, value, message, body of that
length and contract state. -/
theorem recvExternal_short_body (fuel : Nat) (st : VmState) (balance value : Int) (msg : Cell)
    (body : Slice) (gasMax : Int) (hb : body.bitsRemaining < 512 + 32 + 32 + 32) :
    ∃ stF, VmState.runWith execInstr (fuel + 30) (entry st balance value msg body gasMax) =
      .halt (~~~ 9) stF ∧ stF.gas.gasCredit = 10000 := by
  simp only [Slice.bitsRemaining] at hb
  unfold entry
  vm_run [Slice.haveBits, Slice.advanceBits]
  all_goals (simp only [VmState.haltResult]; exact ⟨_, rfl, rfl⟩)

/-- What the compute phase keeps of such a run (`ComputeOutcome.ofHalt`): exit code 9, the data
`data0` and no actions, as the gas credit was not paid off (no `ACCEPT`). -/
theorem recvExternal_short_body_outcome (fuel : Nat) (st : VmState) (balance value : Int) (msg : Cell)
    (body : Slice) (gasMax : Int) (data0 : Cell) (hb : body.bitsRemaining < 512 + 32 + 32 + 32) :
    ∃ ec stF, VmState.runWith execInstr (fuel + 30) (entry st balance value msg body gasMax) = .halt ec stF ∧
      (ComputeOutcome.ofHalt ec stF data0).exitCode = 9 ∧
      (ComputeOutcome.ofHalt ec stF data0).c4 = data0 ∧
      (ComputeOutcome.ofHalt ec stF data0).c5 = Cell.empty := by
  obtain ⟨stF, hrun, hcredit⟩ := recvExternal_short_body fuel st balance value msg body gasMax hb
  refine ⟨_, stF, hrun, ?_, ?_, ?_⟩ <;> simp [ComputeOutcome.ofHalt, hcredit, VM.int_complement]

end TvmLean.Pilot.Wallet3
