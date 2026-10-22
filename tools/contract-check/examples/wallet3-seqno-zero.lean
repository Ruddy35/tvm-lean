-- A false invariant of wallet v3, to see the report of the path that breaks it: "the seqno is
-- always 0". An external message with the seqno 0, the subwallet and a valid signature commits the
-- seqno 1.
import TvmLean.Proofs.Contracts.Wallet3Spec
-- contract-check: invariant SeqnoZero key sub
-- contract-check: params (key sub : Nat)
-- contract-check: hints Contracts.Wallet3.Data.encode, Contracts.Wallet3.Data.WF

open TvmLean.Contracts

/-- `Stored key sub` with the seqno 0. -/
def SeqnoZero (key sub : Nat) (data : Option Cell) : Prop :=
  ∃ d : Wallet3.Data, data = some d.encode ∧ d.WF ∧ d.publicKey = key ∧ d.subwallet = sub ∧ d.seqno = 0
