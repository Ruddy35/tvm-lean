import TvmLean.Proofs.Contracts.StorageData
import TvmLean.Proofs.Exec.Spec.CellExt

/-!
# TON Storage: the reads of the data, as a run makes them

A run of the storage contract loads its data `c4 = Data.encode d` (`CTOS`) and reads it field by
field (`LDI 1`, `LDGRAMS`, `LDMSGADDR`, `256 LDU`, ...), and the client and the torrent hash from its
reference (`PLDREF CTOS LDMSGADDR 256 LDU`). The rewrites here turn what the instructions'
specifications leave (`bitsToNat (Slice.readBits ⟨d.encode, p, r⟩ n)`, `Slice.skipMessageAddr`,
`Slice.prefixCell`, `Slice.toCellRemaining`, the sizes the bound checks compare) into the fields of
`d`, for `d` within its widths (`Data.WF`). The position of a read is a hypothesis `p = ...`
(`omega` proves it, as `vm_run`'s discharger does), so that a position however the run wrote it
matches.
-/

namespace TvmLean.Contracts.Storage

open TvmLean

/-! ## Sizes -/

theorem Data.encode_bits_size (d : Data) :
    d.encode.bits.size = 1 + (4 + coinsLen d.balance * 8) + d.provider.size + 256 + 64 + 64 +
      (4 + coinsLen d.ratePerMbDay * 8) + 32 + 32 := Data.bits_size d

theorem Data.encode_refs_size (d : Data) : d.encode.refs.size = 1 := rfl

theorem Data.encode_ref0 (d : Data) : d.encode.refs[0]! = d.clientCell := rfl

theorem Data.clientCell_bits_size (d : Data) : d.clientCell.bits.size = d.client.size + 256 := by
  simp [Data.clientCell_bits]

theorem Data.clientCell_refs_size (d : Data) : d.clientCell.refs.size = 0 := rfl

/-- A valid address is at most 522 bits (`addr_extern` with 511 bits). -/
theorem MsgAddr.Valid.size_le {a : BitString} (ha : MsgAddr.Valid a) : a.size ≤ 522 := by
  unfold MsgAddr.Valid at ha
  rw [addrLenAt_eq] at ha
  have hsz : (a.extract (0 + 2) (0 + 11)).size ≤ 9 := by simp only [Array.size_extract]; omega
  have hl : bitsToNat (a.extract (0 + 2) (0 + 11)) < 512 :=
    Nat.lt_of_lt_of_le (bitsToNat_lt _) (Nat.pow_le_pow_right (by decide : 2 > 0) hsz)
  split at ha
  · split at ha <;> (try split at ha) <;> omega
  · split at ha <;> omega

/-! ## Reads of the data cell -/

theorem Data.readBits_encode (d : Data) (p r n : Nat) :
    Slice.readBits ⟨d.encode, p, r⟩ n = d.bits.extract p (p + n) := rfl

/-- The flag `active` (`LDI 1`). -/
theorem Data.read_flag (d : Data) : Slice.readBits (Slice.ofCell d.encode) 1 = #[d.active] :=
  Data.extract_flag d rfl rfl

/-- The length in bytes of `balance` (`LDGRAMS`). -/
theorem Data.read_balanceLen (d : Data) (hb : coinsLen d.balance < 16) {p r n : Nat} (hp : p = 1) (hn : n = 4) :
    bitsToNat (Slice.readBits ⟨d.encode, p, r⟩ n) = coinsLen d.balance := by
  subst hp hn
  rw [Data.readBits_encode, Data.extract_balanceLen d rfl rfl]
  exact bitsToNat_coinsLen hb

/-- `balance` (`LDGRAMS`). -/
theorem Data.read_balance (d : Data) {p r n : Nat} (hp : p = 5) (hn : n = coinsLen d.balance * 8) :
    bitsToNat (Slice.readBits ⟨d.encode, p, r⟩ n) = d.balance := by
  subst hp hn
  rw [Data.readBits_encode, Data.extract_balance d rfl rfl]
  exact bitsToNat_coins _

/-- `provider` (`LDMSGADDR`): the address read in full. -/
theorem Data.skip_provider (d : Data) (hv : MsgAddr.Valid d.provider) {p r : Nat} (gv : Nat)
    (hp : p = 5 + coinsLen d.balance * 8) :
    Slice.skipMessageAddr ⟨d.encode, p, r⟩ gv = .ok ⟨d.encode, p + d.provider.size, r⟩ := by
  subst hp
  have hs := Data.bits_size d
  exact skipMessageAddr_of_valid (s := ⟨d.encode, 5 + coinsLen d.balance * 8, r⟩) gv hv
    (Data.extract_provider d rfl rfl) (by simp only [Data.encode_bits]; omega)

/-- The address `LDMSGADDR` pushes for `provider`. -/
theorem Data.prefix_provider (d : Data) {p q r r' : Nat} (hp : p = 5 + coinsLen d.balance * 8)
    (hq : q = p + d.provider.size) (hr : r' = r) :
    Slice.prefixCell ⟨d.encode, p, r⟩ ⟨d.encode, q, r'⟩ = Cell.mkOrdinary d.provider #[] := by
  subst hr
  unfold Slice.prefixCell
  simp only [Data.encode_bits]
  rw [Data.extract_provider d hp hq, Array.extract_eq_empty_of_le (Nat.min_le_left _ _)]

theorem Data.read_merkleHash (d : Data) (hm : d.merkleHash < 2 ^ 256) {p r n : Nat}
    (hp : p = 5 + coinsLen d.balance * 8 + d.provider.size) (hn : n = 256) :
    bitsToNat (Slice.readBits ⟨d.encode, p, r⟩ n) = d.merkleHash := by
  subst hn
  rw [Data.readBits_encode, Data.extract_merkleHash d hp rfl, bitsToNat_natToBits_of_lt hm]

theorem Data.read_fileSize (d : Data) (hf : d.fileSize < 2 ^ 64) {p r n : Nat}
    (hp : p = 5 + coinsLen d.balance * 8 + d.provider.size + 256) (hn : n = 64) :
    bitsToNat (Slice.readBits ⟨d.encode, p, r⟩ n) = d.fileSize := by
  subst hn
  rw [Data.readBits_encode, Data.extract_fileSize d hp rfl, bitsToNat_natToBits_of_lt hf]

theorem Data.read_nextProof (d : Data) (hx : d.nextProof < 2 ^ 64) {p r n : Nat}
    (hp : p = 5 + coinsLen d.balance * 8 + d.provider.size + 320) (hn : n = 64) :
    bitsToNat (Slice.readBits ⟨d.encode, p, r⟩ n) = d.nextProof := by
  subst hn
  rw [Data.readBits_encode, Data.extract_nextProof d hp rfl, bitsToNat_natToBits_of_lt hx]

theorem Data.read_rateLen (d : Data) (hr : coinsLen d.ratePerMbDay < 16) {p r n : Nat}
    (hp : p = 5 + coinsLen d.balance * 8 + d.provider.size + 384) (hn : n = 4) :
    bitsToNat (Slice.readBits ⟨d.encode, p, r⟩ n) = coinsLen d.ratePerMbDay := by
  subst hn
  rw [Data.readBits_encode, Data.extract_rateLen d hp rfl]
  exact bitsToNat_coinsLen hr

theorem Data.read_rate (d : Data) {p r n : Nat}
    (hp : p = 5 + coinsLen d.balance * 8 + d.provider.size + 388) (hn : n = coinsLen d.ratePerMbDay * 8) :
    bitsToNat (Slice.readBits ⟨d.encode, p, r⟩ n) = d.ratePerMbDay := by
  subst hn
  rw [Data.readBits_encode, Data.extract_rate d hp rfl]
  exact bitsToNat_coins _

theorem Data.read_maxSpan (d : Data) (hs : d.maxSpan < 2 ^ 32) {p r n : Nat}
    (hp : p = 5 + coinsLen d.balance * 8 + d.provider.size + 388 + coinsLen d.ratePerMbDay * 8) (hn : n = 32) :
    bitsToNat (Slice.readBits ⟨d.encode, p, r⟩ n) = d.maxSpan := by
  subst hn
  rw [Data.readBits_encode, Data.extract_maxSpan d hp rfl, bitsToNat_natToBits_of_lt hs]

theorem Data.read_lastProofTime (d : Data) (hl : d.lastProofTime < 2 ^ 32) {p r n : Nat}
    (hp : p = 5 + coinsLen d.balance * 8 + d.provider.size + 388 + coinsLen d.ratePerMbDay * 8 + 32)
    (hn : n = 32) :
    bitsToNat (Slice.readBits ⟨d.encode, p, r⟩ n) = d.lastProofTime := by
  subst hn
  rw [Data.readBits_encode, Data.extract_lastProofTime d hp rfl, bitsToNat_natToBits_of_lt hl]

/-- What `STSLICER` stores of the data after `balance` (`add_to_balance`'s residue). -/
theorem Data.rest_afterBalance (d : Data) {p r : Nat} (hp : p = 5 + coinsLen d.balance * 8) (hr : r = 0) :
    Slice.toCellRemaining ⟨d.encode, p, r⟩ =
      Cell.mkOrdinary (d.provider ++ natToBits d.merkleHash 256 ++ natToBits d.fileSize 64 ++
        natToBits d.nextProof 64 ++ natToBits (coinsLen d.ratePerMbDay) 4 ++
        natToBits d.ratePerMbDay (coinsLen d.ratePerMbDay * 8) ++ natToBits d.maxSpan 32 ++
        natToBits d.lastProofTime 32) #[d.clientCell] := by
  subst hr
  unfold Slice.toCellRemaining
  simp only [Data.encode_bits, Data.encode_refs]
  rw [Data.extract_afterBalance d hp (Nat.le_refl _)]
  rfl

/-- What `STSLICER` stores of the data after `provider` (`accept_storage_contract`'s `rest`). -/
theorem Data.rest_afterProvider (d : Data) {p r : Nat} (hp : p = 5 + coinsLen d.balance * 8 + d.provider.size)
    (hr : r = 0) :
    Slice.toCellRemaining ⟨d.encode, p, r⟩ =
      Cell.mkOrdinary (natToBits d.merkleHash 256 ++ natToBits d.fileSize 64 ++ natToBits d.nextProof 64 ++
        natToBits (coinsLen d.ratePerMbDay) 4 ++
        natToBits d.ratePerMbDay (coinsLen d.ratePerMbDay * 8) ++ natToBits d.maxSpan 32 ++
        natToBits d.lastProofTime 32) #[d.clientCell] := by
  subst hr
  unfold Slice.toCellRemaining
  simp only [Data.encode_bits, Data.encode_refs]
  rw [Data.extract_afterProvider d hp (Nat.le_refl _)]
  rfl

/-! ## Reads of the reference: client and torrent hash -/

theorem Data.skip_client (d : Data) (hv : MsgAddr.Valid d.client) (gv : Nat) :
    Slice.skipMessageAddr (Slice.ofCell d.clientCell) gv = .ok ⟨d.clientCell, d.client.size, 0⟩ := by
  have := skipMessageAddr_of_valid (s := Slice.ofCell d.clientCell) gv hv
    (by simp only [Slice.ofCell, Data.clientCell_bits, Nat.zero_add]; exact Data.extract_client d rfl (by simp))
    (by simp [Slice.ofCell, Data.clientCell_bits])
  rw [this]
  simp [Slice.advanceBits, Slice.ofCell]

theorem Data.prefix_client (d : Data) {q r : Nat} (hq : q = d.client.size) (hr : r = 0) :
    Slice.prefixCell (Slice.ofCell d.clientCell) ⟨d.clientCell, q, r⟩ = Cell.mkOrdinary d.client #[] := by
  subst hq hr
  unfold Slice.prefixCell
  simp only [Slice.ofCell, Data.clientCell_bits, Data.clientCell_refs]
  rw [Data.extract_client d rfl (by simp)]
  rfl

theorem Data.read_torrentHash (d : Data) (ht : d.torrentHash < 2 ^ 256) {p r n : Nat} (hp : p = d.client.size)
    (hn : n = 256) : bitsToNat (Slice.readBits ⟨d.clientCell, p, r⟩ n) = d.torrentHash := by
  subst hn
  simp only [Slice.readBits, Data.clientCell_bits]
  rw [Data.extract_torrentHash d hp rfl, bitsToNat_natToBits_of_lt ht]

/-! ## Slices of whole cells, flags -/

theorem readBits_ofCell_all (c : Cell) : (Slice.ofCell c).readBits (Slice.ofCell c).bitsRemaining = c.bits := by
  simp [Slice.readBits, Slice.ofCell, Slice.bitsRemaining]

theorem toCellRemaining_ofCell_mkOrdinary (b : BitString) (r : Array Cell) :
    (Slice.ofCell (Cell.mkOrdinary b r)).toCellRemaining = Cell.mkOrdinary b r := by
  simp [Slice.toCellRemaining, Slice.ofCell, Cell.mkOrdinary]

/-- A flag as `LDI 1` reads it (`-1` for a set bit), under a name the runs do not unfold, so that
a run does not split on the flag until a condition needs it (`flagInt_bounds` for `omega`). -/
@[irreducible] def flagInt (b : Bool) : Int := if b then -1 else 0

theorem flagInt_eq (b : Bool) : flagInt b = if b then -1 else 0 := by unfold flagInt; rfl

theorem flagInt_bounds (b : Bool) : -1 ≤ flagInt b ∧ flagInt b ≤ 0 := by
  rw [flagInt_eq]; cases b <;> decide

theorem flagInt_true : flagInt true = -1 := by rw [flagInt_eq]; rfl
theorem flagInt_false : flagInt false = 0 := by rw [flagInt_eq]; rfl

/-- `LDI 1` of a flag bit. -/
theorem bitsToIntSignedTwos_flag (b : Bool) : bitsToIntSignedTwos #[b] = flagInt b := by
  rw [flagInt_eq]; cases b <;> rfl

/-- `STI 1` of a flag. -/
theorem twosBits_flag (b : Bool) : twosBits (flagInt b) 1 = #[b] := by
  rw [flagInt_eq]; cases b <;> rfl

theorem twosBits_true : twosBits (-1) 1 = #[true] := rfl

theorem flag_fits257 (b : Bool) : (IntVal.num (flagInt b)).signedFits257 = true := by
  rw [flagInt_eq]; cases b <;> simp [VM.intVal_signedFits257_num]

/-- A flag is `0` exactly when it is not set. -/
theorem flagInt_eq_zero (b : Bool) : flagInt b = 0 ↔ b = false := by
  rw [flagInt_eq]; cases b <;> decide

/-- `NOT` of a flag that is not 0 (`THROWIFNOT`, `IFJMP`): the flag is not set. -/
theorem flag_false_of_not {b : Bool} (h : ¬(-flagInt b - 1 = 0)) : b = false := by
  cases b
  · rfl
  · rw [flagInt_true] at h; exact absurd rfl h

/-- `NOT` of a flag that is 0: the flag is set. -/
theorem flag_true_of_not {b : Bool} (h : -flagInt b - 1 = 0) : b = true := by
  cases b
  · rw [flagInt_false] at h; cases h
  · rfl

/-- A flag that is not 0: set. -/
theorem flag_true_of_ne {b : Bool} (h : ¬flagInt b = 0) : b = true := by
  cases b
  · rw [flagInt_false] at h; exact absurd rfl h
  · rfl

/-- A flag that is 0: not set. -/
theorem flag_false_of_eq {b : Bool} (h : flagInt b = 0) : b = false := by
  cases b
  · rfl
  · rw [flagInt_true] at h; cases h

end TvmLean.Contracts.Storage
