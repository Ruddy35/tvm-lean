import TvmLean.Proofs.Exec.Tactic
import TvmLean.Proofs.Contracts.Wallet3Code
import TvmLean.Proofs.Contracts.Wallet3Spec
import TvmLean.Semantics.Contract
import TvmLean.Proofs.Contracts.Wallet3Run.Common

/-!
# Pilot: wallet v3's `recv_external`, by `vm_run`

The code is `TvmLean.Contracts.wallet3Code` (`crypto/smartcont/wallet3-code.fc`, the cell of
`tools/txoracle/contracts.txt` that the transaction cases run). Its root dispatches on the method
id (`SETCP0`, `19 DICTPUSHCONST`, `DICTIGETJMPZ`, `11 THROWARG`); the leaf of the method
dictionary for the id -1 (`recvExternal`, reference 1 of the dictionary) holds `recv_external`
after an 8-bit label:

  `9 PUSHPOW2  LDSLICEX  DUP  32 LDU  32 LDU  32 LDU  s0 s2 XCHG  NOW  LEQ  35 THROWIF`
  `c4 PUSH  CTOS  32 LDU  32 LDU  256 LDU  ENDS  s3 s2 XCPU  EQUAL  33 THROWIFNOT`
  `s4 s4 XCPU  EQUAL  34 THROWIFNOT  s0 s4 XCHG  HASHSU  s0 s5 s5 XC2PU  CHKSIGNU  35 THROWIFNOT`
  `ACCEPT  <{ DUP  SREFS }> PUSHCONT  <{ 8 LDU  LDREF  s0 s2 XCHG  SENDRAWMSG }> PUSHCONT  WHILE`
  `DROP  SWAP  INC  NEWC  32 STU  32 STU  256 STU  ENDC  c4 POP`

* `recvExternal_commit`: **the whole run, from the initial state of the compute phase** of an
  external message (`computePhaseInit` on `wallet3Code`, any data, balance, message and body, any
  `c7` whose parameters give `NOW`, gas credit 10000 and any gas maximum that fits 64 bits, version
  4 or later), for any fuel: if the run commits, the data was 320 bits and no references, the signature of the
  body verified (`CHKSIGNU`) with the stored key over the hash of the signed part, the subwallet and
  seqno of the message are the stored ones, `valid_until > now`, and the new `c4` is the stored data
  with the seqno increased by one (`CommitSpec`). Proved by `vm_run` from the dispatcher on, with
  the loop rule at the `WHILE` loop that sends the orders (`vm_loop`: any number of orders, each
  iteration from any slice, `c5` and gas).
* `recvExternal_commit_decode`: the same for data that decodes (`Wallet3.Data.decode`), in the terms
  of `Wallet3Spec`: `c4` is `encode` of the data with seqno + 1, and `Ed25519.verify` holds.
* `recvExternal_short_body`: a body shorter than the signature and the three 32-bit fields makes
  `recv_external` fail with cell underflow before `ACCEPT` (from the state in which the procedure
  starts, `entry`).
-/

namespace TvmLean.Pilot.Wallet3

-- the closed facts of the code by evaluation over the fast twins (`TvmLean/Proofs/Fast/`; the
-- twins of the decoder and of `wallet3Code` are made in `Contracts/Wallet3Run/Common.lean`)
set_option vm.fastFacts true

open TvmLean.Contracts

/-- `recv_external`: the leaf of the method dictionary of `wallet3Code` for the id -1. -/
def recvExternal : Cell := wallet3Code.refs[0]!.refs[1]!

set_option Elab.async false in
fast_twin TvmLean.Pilot.Wallet3.recvExternal

/-- The state in which `recv_external` starts on an external message with body `body` (the
dispatcher has dropped the method id): the stack `balance, value, message, body` the dispatcher
leaves, the procedure after its label as the current continuation, `c0` the end of the run and
`c2` the exception handler of the compute phase, the gas of an external message (no limit, a
credit of 10000 before `ACCEPT`); the rest of `st` (the data `c4`, `c7`, the version) is anything. -/
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

/-! ## The whole run -/

/-- The data as `recv_external` reads it (`32 LDU`, `32 LDU`, `256 LDU` from `c4`). -/
def dataOf (data : Cell) : Wallet3.Data :=
  ⟨bitsToNat (data.bits.extract 0 32), bitsToNat (data.bits.extract 32 64), bitsToNat (data.bits.extract 64 320)⟩

/-- The signed part of an external message body: everything after the 512 bits of the signature,
as a cell (`HASHSU` hashes it). -/
def signedPart (body : Slice) : Cell :=
  ({ cell := body.cell, bitPos := body.bitPos + 512, refPos := body.refPos } : Slice).toCellRemaining

/-- The 32-bit field of the body at bit `k` (the subwallet at 512, `valid_until` at 544, the
seqno at 576). -/
def field (body : Slice) (k : Nat) : Nat :=
  bitsToNat (body.cell.bits.extract (body.bitPos + k) (body.bitPos + k + 32))

/-- What a run of `recv_external` on the body `body` and the data `data` guarantees when it
commits: the data was 320 bits and no references, the signature (the first 512 bits) verified
with the stored key over the hash of the signed part (`chkSignU`, `CHKSIGNU`), subwallet and seqno
are the stored ones, `now < valid_until`, and the committed data is the stored data with the seqno
increased by one. -/
def CommitSpec (data : Cell) (body : Slice) (now : Int) (gv : Nat) (r : StepResult) : Prop :=
  r.state.cstate.committed = true →
    data.bits.size = 320 ∧ data.refs.size = 0 ∧
    chkSignU gv (cellHash (signedPart body)) (dataOf data).publicKey (body.readBits 512) = true ∧
    field body 512 = (dataOf data).subwallet ∧ now < field body 544 ∧ field body 576 = (dataOf data).seqno ∧
    r.state.cstate.c4 = Wallet3.Data.encode { dataOf data with seqno := (dataOf data).seqno + 1 }

theorem int_toNat_natCast_add_one (x : Nat) : ((x : Int) + 1).toNat = x + 1 := by omega

/-- A path of the run that does not commit: its result keeps the empty committed state. -/
macro "wallet_no_commit" : tactic => `(tactic| (
  simp only [CommitSpec, VmState.haltResult, VmState.runWith_zero, Excno.toInt, Int.reduceEq, Int.reduceNeg,
    or_self, or_false, false_or, if_false, ite_false, StepResult.state_halt, CommittedState.empty,
    Bool.false_eq_true, false_implies]; done))

open Lean Meta Elab Tactic in
/-- `wallet_sig`: the goal `chkSignU ... = true` of `CommitSpec` from the hypothesis of the path
that the signature check passed (found by its head, `chkSignU`), both in the same normal form. -/
elab "wallet_sig" : tactic => withMainContext do
  let g ← getMainGoal
  let some d := (← getLCtx).findDecl? fun d =>
      if !d.isImplementationDetail && (d.type.find? (·.isConstOf ``chkSignU)).isSome then some d else none
    | throwError "wallet_sig: no signature check in the context"
  let g ← g.rename d.fvarId `hsig_w
  replaceMainGoal [g]
  let h := mkIdent `hsig_w
  evalTactic (← `(tactic| (
    simp only [signedPart, dataOf, Slice.toCellRemaining, Slice.readBits, Slice.ofCell, Cell.mkOrdinary,
      Array.extract_extract, Nat.zero_add, Nat.add_zero, Nat.min_self, Nat.add_assoc, Nat.reduceAdd] at $h:ident ⊢
    with_reducible exact $h:ident)))

/-- The path that commits: the facts of the path (the checks of `recv_external`) give `CommitSpec`. -/
macro "wallet_commit" : tactic => `(tactic| (
  unfold CommitSpec VmState.haltResult VmState.tryCommit
  simp only [Int.reduceEq, or_false, if_true]
  split
  · intro _
    try clear ih
    simp only [Slice.bitsRemaining, Slice.refsRemaining, Slice.readBits, Slice.ofCell, Cell.mkOrdinary,
      Array.extract_extract, Nat.zero_add, Nat.add_zero, Nat.min_self, Nat.add_assoc, Nat.reduceAdd,
      StepResult.state_halt, if_true] at *
    refine ⟨by omega, by omega, ?_, ?_, ?_, ?_, ?_⟩
    · wallet_sig
    · simp only [field, dataOf, Nat.add_assoc, Nat.reduceAdd]; omega
    · simp only [field, Nat.add_assoc, Nat.reduceAdd]; omega
    · simp only [field, dataOf, Nat.add_assoc, Nat.reduceAdd]; omega
    · simp only [Wallet3.Data.encode, dataOf, Builder.finalize, Builder.storeBits, Builder.empty,
        int_toNat_natCast_add_one, Array.empty_append, Array.append_assoc]
  · wallet_no_commit))

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- **Wallet v3's `recv_external`, from the initial state of the compute phase.** For any data,
message, body, balance and value, any `c7` whose parameters give `NOW` (a tuple of more than 3 and at
most 255 entries, as `get_param` reads it: tonops.cpp:121-128), any gas maximum up to
`GasLimits.infty` = 2^63 - 1 (stated as the literal, which `vm_run` never unfolds), version 4
or later and any fuel: if the run commits, `CommitSpec` holds (the checks passed, the signature
verified, the new data is the old one with seqno + 1). -/
theorem recvExternal_commit (data msg : Cell) (body : Slice) (bal val : Int) (c7 params : Array Value) (now : Int)
    (hc70 : 0 < c7.size) (hc7 : c7[0]! = .tuple params) (hp : 3 < params.size) (hl : params.size ≤ 255)
    (hnow : params[3]! = .int (.num now)) (hdata : data.special = false)
    (gm : Int) (gv : Nat) (hgv : 4 ≤ gv) (hgm : gm ≤ 9223372036854775807) (fuel : Nat) :
    CommitSpec data body now gv (VmState.runWith execInstr fuel
      (computePhaseInit wallet3Code data (computePhaseStack bal val msg body true) c7 0 gm 10000 gv)) := by
  simp only [computePhaseInit, VmState.initial, computePhaseStack, Regs.initial]
  vm_run [hgv, hnow, Spec.dictJump, Slice.haveBits, Slice.advanceBits]
  -- the `WHILE` loop of the orders, by the loop rule
  all_goals try (vm_has_run; vm_loop)
  all_goals try (vm_has_run; vm_step [hgv, hnow, Spec.dictJump, Slice.haveBits, Slice.advanceBits])
  all_goals try vm_run [hgv, hnow, Spec.dictJump, Slice.haveBits, Slice.advanceBits]
  all_goals first | wallet_no_commit | wallet_commit

/-- The data `recv_external` reads from a cell that decodes (`Wallet3.Data.decode`) is the decoded
data. -/
theorem dataOf_of_decode {data : Cell} {d : Wallet3.Data} (hd : Wallet3.Data.decode data = some d) :
    dataOf data = d ∧ data.special = false := by
  unfold Wallet3.Data.decode at hd
  split at hd
  · rename_i hc
    cases hd
    exact ⟨rfl, hc.1⟩
  · cases hd

/-- **Wallet v3's `recv_external` on data that decodes**, in the terms of `Wallet3Spec`
(`TvmLean/Proofs/Contracts/Wallet3Spec.lean`): if the run from the initial state of the compute
phase commits, the committed data is `encode` of the stored data with seqno + 1 (subwallet and
key unchanged), the signature verified (`Ed25519.verify` of the 32 bytes of the hash of the signed
part with the stored key), and the message's subwallet and seqno are the stored ones and its
`valid_until` is after `now`. -/
theorem recvExternal_commit_decode (data msg : Cell) (body : Slice) (bal val : Int) (c7 params : Array Value)
    (now : Int) (hc70 : 0 < c7.size) (hc7 : c7[0]! = .tuple params) (hp : 3 < params.size)
    (hl : params.size ≤ 255) (hnow : params[3]! = .int (.num now)) (d : Wallet3.Data) (hd : Wallet3.Data.decode data = some d)
    (gm : Int) (gv : Nat) (hgv : 4 ≤ gv) (hgm : gm ≤ 9223372036854775807) (fuel : Nat) :
    let r := VmState.runWith execInstr fuel
      (computePhaseInit wallet3Code data (computePhaseStack bal val msg body true) c7 0 gm 10000 gv)
    r.state.cstate.committed = true →
      r.state.cstate.c4 = Wallet3.Data.encode { d with seqno := d.seqno + 1 } ∧
      Ed25519.verify (natToBytesBEFixed (cellHash (signedPart body)) 32) (natToBytesBEFixed d.publicKey 32)
        (bitStringToBytesBE (body.readBits 512)) = true ∧
      field body 512 = d.subwallet ∧ field body 576 = d.seqno ∧ now < field body 544 := by
  intro r hc
  obtain ⟨hdd, hsp⟩ := dataOf_of_decode hd
  obtain ⟨_, _, hsig, hsub, hnow', hseq, hc4⟩ :=
    recvExternal_commit data msg body bal val c7 params now hc70 hc7 hp hl hnow hsp gm gv hgv hgm fuel hc
  rw [hdd] at hsig hsub hseq hc4
  exact ⟨hc4, verify_of_chkSignU hsig, hsub, hseq, hnow'⟩

end TvmLean.Pilot.Wallet3
