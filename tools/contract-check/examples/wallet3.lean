-- Wallet v3 (crypto/smartcont/wallet3-code.fc): the data is `seqno:uint32 subwallet:uint32
-- public_key:uint256`. Invariant: the predicate `Stored key sub` of the hand proof
-- (TvmLean/Proofs/Contracts/Wallet3Induction.lean): the data is `Data.encode` of fields within their
-- widths with public key `key` and subwallet `sub`.
import TvmLean.Proofs.Contracts.Wallet3Spec
-- contract-check: invariant Stored key sub
-- contract-check: params (key sub : Nat)
-- contract-check: hints Contracts.Wallet3.Data.encode, Contracts.Wallet3.Data.WF

open TvmLean.Contracts

/-- The data of wallet v3 with public key `key` and subwallet `sub`. -/
def Stored (key sub : Nat) (data : Option Cell) : Prop :=
  ∃ d : Wallet3.Data, data = some d.encode ∧ d.WF ∧ d.publicKey = key ∧ d.subwallet = sub
