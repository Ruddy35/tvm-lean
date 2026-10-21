import TvmLean.Proofs.Contracts.Bits
import TvmLean.Proofs.Contracts.Spec
import TvmLean.Proofs.Contracts.Wallet3Code

/-!
# Wallet v3: the specification

Wallet v3 (`crypto/smartcont/wallet3-code.fc`, the code `wallet3Code`) keeps
`seqno:uint32 subwallet:uint32 public_key:uint256` in `c4`. Its external message is
`signature:bits512` followed by the signed part `subwallet:uint32 valid_until:uint32 seqno:uint32`
and the orders `(mode:uint8 ^msg)*`; `recv_external` checks `valid_until > now` (35), the stored
data's layout (`end_parse`), the seqno (33), the subwallet (34) and the signature over the hash of
the signed part (`slice_hash`, 35), then `accept_message()`, sends the orders and stores
`seqno + 1`. `recv_internal` does nothing.

The specification, `Wallet3.spec sub key` (a `ContractSpec`, `TvmLean/Proofs/Contracts/Spec.lean`)
for a wallet deployed with subwallet `sub` and key `key`:

* data: `Wallet3.Data`, `decode`/`encode` with both round trips proved (`decode_encode`,
  `encode_decode`);
* invariant: the subwallet is `sub`, the key is `key` (they never change);
* step: subwallet and key unchanged; the seqno grows by exactly 1 when an external message's compute
  phase commits (accepted and successful), else stays (so it never decreases);
* external messages: accepted only if the body parses, the signature verifies with the stored key
  over the hash of the signed part, its subwallet and seqno are the stored ones and
  `valid_until > now`.

`Wallet3Spec` is the statement that `wallet3Code` meets it for every deployment;
`seqnoMonotoneSpec`, `seqnoIncrementSpec`, `constantsSpec` and `acceptSpec` are its parts in
plain form, each implied by it (`Wallet3Spec.seqnoMonotone`, ...).

An external message that is accepted and then fails (an order without its 8 bits of mode, a seqno
of `2^32 - 1`, the gas after `ACCEPT`) does not commit: the seqno stays, as C++ keeps the old data.
-/

namespace TvmLean.Contracts.Wallet3

open TvmLean

/-! ## Data -/

/-- The data of wallet v3. -/
structure Data where
  seqno : Nat
  subwallet : Nat
  publicKey : Nat
  deriving DecidableEq, Repr

/-- The fields fit their widths. -/
def Data.WF (d : Data) : Prop :=
  d.seqno < 2 ^ 32 ∧ d.subwallet < 2 ^ 32 ∧ d.publicKey < 2 ^ 256

/-- The cell `STU`/`ENDC` build (`set_data(begin_cell().store_uint(seqno, 32)...)`). -/
def Data.encode (d : Data) : Cell :=
  Cell.mkOrdinary (natToBits d.seqno 32 ++ natToBits d.subwallet 32 ++ natToBits d.publicKey 256) #[]

/-- The data of a cell the wallet reads (`CTOS`, `32 LDU`, `32 LDU`, `256 LDU`, `ENDS`): an ordinary
cell of exactly 320 bits and no references. -/
def Data.decode (c : Cell) : Option Data :=
  if c.special = false ∧ c.refs.size = 0 ∧ c.levelMask = 0 ∧ c.bits.size = 320 then
    some ⟨bitsToNat (c.bits.extract 0 32), bitsToNat (c.bits.extract 32 64),
      bitsToNat (c.bits.extract 64 320)⟩
  else none

theorem Data.decode_encode (d : Data) (h : d.WF) : decode (encode d) = some d := by
  obtain ⟨h1, h2, h3⟩ := h
  have hl : Cell.computeOrdinaryLevelMask #[] = 0 := rfl
  simp [decode, encode, Cell.mkOrdinary, hl, Array.extract_eq_self_of_le, Array.extract_eq_empty_of_le,
    bitsToNat_natToBits_of_lt, h1, h2, h3]

theorem Data.encode_decode {c : Cell} {d : Data} (h : decode c = some d) : encode d = c ∧ d.WF := by
  unfold decode at h
  split at h
  · rename_i hc
    obtain ⟨hs, hr, hl, hb⟩ := hc
    cases h
    refine ⟨?_, ?_⟩
    · obtain ⟨b, r, sp, lm⟩ := c
      simp only at hs hr hl hb
      subst hs hl
      simp only [encode, Cell.mkOrdinary, Array.eq_empty_of_size_eq_zero hr]
      rw [natToBits_bitsToNat_of_size (by simp [hb]), natToBits_bitsToNat_of_size (by simp [hb]),
        natToBits_bitsToNat_of_size (by simp [hb])]
      simp [Array.extract_append_extract, Array.extract_eq_self_of_le, hb]
      rfl
    · exact ⟨bitsToNat_lt_of_size (by simp [hb]), bitsToNat_lt_of_size (by simp [hb]),
        bitsToNat_lt_of_size (by simp [hb])⟩
  · cases h

/-- A cell decodes to `d` exactly when it is `encode d` of a `d` within the widths. -/
theorem Data.decode_eq_some_iff (c : Cell) (d : Data) : decode c = some d ↔ c = encode d ∧ d.WF := by
  constructor
  · intro h; obtain ⟨h1, h2⟩ := encode_decode h; exact ⟨h1.symm, h2⟩
  · rintro ⟨rfl, h⟩; exact decode_encode d h

/-! ## External messages -/

/-- An external message body: the signature, the signed part (the rest of the body: subwallet,
valid_until, seqno and the orders) and the three numbers at its head. -/
structure ExtMsg where
  signature : BitString
  signed : Slice
  subwallet : Nat
  validUntil : Nat
  seqno : Nat

/-- The body read as `recv_external` reads it (`512 LDSLICEX`, then `32 LDU` three times): `none` if
it is shorter than 512 + 96 bits. -/
def ExtMsg.parse? (body : Slice) : Option ExtMsg :=
  if body.haveBits (512 + 96) then
    let signed := body.advanceBits 512
    some { signature := body.readBits 512, signed
           subwallet := bitsToNat (signed.readBits 32)
           validUntil := bitsToNat ((signed.advanceBits 32).readBits 32)
           seqno := bitsToNat ((signed.advanceBits 64).readBits 32) }
  else none

/-- What the signature is over: the representation hash of the signed part as a cell (`HASHSU`). -/
def ExtMsg.signedHash (m : ExtMsg) : Array UInt8 := m.signed.toCellRemaining.hashBytes

/-- The signature verifies with the key `key` over `signedHash` (Ed25519 as OpenSSL verifies it,
`CHKSIGNU`; from global version 14 `CHKSIGNU` also refuses the weak keys, which only rejects more). -/
def ExtMsg.SignedBy (m : ExtMsg) (key : Nat) : Prop :=
  Ed25519.verify m.signedHash (natToBytesBEFixed key 32) (bitStringToBytesBE m.signature) = true

/-! ## The specification -/

/-- The invariant of a wallet deployed with subwallet `sub` and key `key`. -/
def Inv (sub key : Nat) (d : Data) : Prop := d.subwallet = sub ∧ d.publicKey = key

/-- One compute phase: subwallet and key unchanged; the seqno grows by one exactly when an external
message's compute phase commits. -/
def Step (d : Data) (r : ComputeRun) (d' : Data) : Prop :=
  d'.subwallet = d.subwallet ∧ d'.publicKey = d.publicKey ∧
    d'.seqno = if r.input.isExternal = true ∧ r.committed = true then d.seqno + 1 else d.seqno

/-- An external message is accepted only if its body parses, the signature verifies with the stored
key, subwallet and seqno are the stored ones and `valid_until > now`. -/
def Accept (d : Data) (i : ComputeInput) : Prop :=
  ∃ body m, i.body? = some body ∧ ExtMsg.parse? body = some m ∧ m.SignedBy d.publicKey ∧
    m.subwallet = d.subwallet ∧ m.seqno = d.seqno ∧ ∃ now, i.now? = some now ∧ now < m.validUntil

/-- The specification of wallet v3 deployed with subwallet `sub` and key `key`. -/
def spec (sub key : Nat) : ContractSpec where
  Data := Data
  decode := Data.decode
  Inv := Inv sub key
  Step := Step
  Accept := Accept

end Wallet3

open Wallet3

/-- **Wallet v3 is correct**: for every deployment (subwallet, key), `wallet3Code` meets
`Wallet3.spec`. -/
def Wallet3Spec : Prop := ∀ sub key, (Wallet3.spec sub key).Holds wallet3Code

namespace Wallet3

/-- The hypotheses of every statement below: `r` is a compute phase of `wallet3Code` on a valid
input, started on data `c4` that decodes to `d`. -/
def RunFrom (r : ComputeRun) (d : Data) : Prop :=
  r.Of wallet3Code ∧ r.input.Valid ∧ Data.decode r.data = some d

/-- The seqno never decreases (and the data keeps its layout). -/
def seqnoMonotoneSpec : Prop :=
  ∀ r d, RunFrom r d → ∃ d', Data.decode r.outcome.c4 = some d' ∧ d.seqno ≤ d'.seqno

/-- The seqno grows by exactly one when an external message's compute phase commits. -/
def seqnoIncrementSpec : Prop :=
  ∀ r d, RunFrom r d → r.input.isExternal = true → r.committed = true →
    Data.decode r.outcome.c4 = some { d with seqno := d.seqno + 1 }

/-- The subwallet and the public key never change. -/
def constantsSpec : Prop :=
  ∀ r d, RunFrom r d → ∃ d', Data.decode r.outcome.c4 = some d' ∧
    d'.subwallet = d.subwallet ∧ d'.publicKey = d.publicKey

/-- An external message is accepted only if it is signed with the stored key over the hash of the
rest of the body, its subwallet and seqno match and `valid_until > now`. -/
def acceptSpec : Prop :=
  ∀ r d, RunFrom r d → r.input.isExternal = true → r.accepted = true → Accept d r.input

theorem step_of_spec (h : Wallet3Spec) {r : ComputeRun} {d : Data} (hr : RunFrom r d) :
    ∃ d', Data.decode r.outcome.c4 = some d' ∧ Step d r d' := by
  obtain ⟨d', h1, _, h2⟩ := (h d.subwallet d.publicKey).1 r d hr.1 hr.2.1 hr.2.2 ⟨rfl, rfl⟩
  exact ⟨d', h1, h2⟩

theorem Wallet3Spec.seqnoMonotone (h : Wallet3Spec) : seqnoMonotoneSpec := by
  intro r d hr
  obtain ⟨d', h1, -, -, h2⟩ := step_of_spec h hr
  refine ⟨d', h1, ?_⟩
  rw [h2]; split <;> omega

theorem Wallet3Spec.seqnoIncrement (h : Wallet3Spec) : seqnoIncrementSpec := by
  intro r d hr he hc
  obtain ⟨d', h1, h2, h3, h4⟩ := step_of_spec h hr
  rw [h1]
  simp only [he, hc, and_self, if_true] at h4
  cases d'; cases d; simp_all

theorem Wallet3Spec.constants (h : Wallet3Spec) : constantsSpec := by
  intro r d hr
  obtain ⟨d', h1, h2, h3, -⟩ := step_of_spec h hr
  exact ⟨d', h1, h2, h3⟩

theorem Wallet3Spec.accept (h : Wallet3Spec) : acceptSpec := by
  intro r d hr he ha
  exact (h d.subwallet d.publicKey).2 r d hr.1 hr.2.1 hr.2.2 ⟨rfl, rfl⟩ he ha

end Wallet3

end TvmLean.Contracts
