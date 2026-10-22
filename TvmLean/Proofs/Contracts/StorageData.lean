import TvmLean.Proofs.Contracts.Bits
import TvmLean.Proofs.DecEq

/-!
# TON Storage: the data of the storage contract

The storage contract of TON Storage (`storage/storage-daemon/smartcont/storage-contract.fc`, the
code `TvmLean.Contracts.storageCode`) keeps in `c4`

    storage#_ active:Bool
              balance:Coins provider:MsgAddress
              merkle_hash:uint256 file_size:uint64 next_proof_byte:uint64
              rate_per_mb_day:Coins
              max_span:uint32 last_proof_time:uint32
              ^[client:MsgAddress torrent_hash:uint256] = Storage;

`Storage.Data` is that record; `Data.encode` the cell the contract writes (`STI 1` of the flag, the
amounts as `STGRAMS` stores them, `coinsBits`, the addresses as their bits, the numbers as `STU`
stores them, the client and the torrent hash in the one reference, `Data.clientCell`).

* `MsgAddr.Valid`: an address that `LDMSGADDR` reads in full at every global version
  (`addr_none`, `addr_extern`, `addr_std` without anycast; `addrLenAt` its length by its tag):
  `skipMessageAddr_of_valid`, the read of such an address at any position of any slice;
* `Data.WF`: the fields within their widths, both addresses `Valid`;
* `Data.decode`: the fields read from a cell as the contract reads them (`Data.parse`: `LDI 1`,
  `LDGRAMS`, `LDMSGADDR`, `256 LDU`, ..., `LDREF`, and in the reference `LDMSGADDR`, `256 LDU`),
  accepted when they are within their widths and written back give the cell; `decode_encode` and
  `encode_decode` are the round trips;
* the reads of `encode d` by position (`Data.extract_*`, `parse_encode`): what the runs of the
  contract read from its data.

Amounts are written in the fewest bytes (`coinsLen`, as `STGRAMS` writes them): `encode` is the
canonical form, the one the contract writes back.
-/

namespace TvmLean.Contracts.Storage

open TvmLean

/-! ## Coins -/

/-- The number of bytes of `n` as `Coins` (`VarUInteger 16`, C++ `store_var_integer` with
`STGRAMS`): the bytes of its binary length. -/
def coinsLen (n : Nat) : Nat := (natLenBits n + 7) / 8

/-- `n` as `Coins`, as `STGRAMS` stores it: the length in bytes in 4 bits, then `n` in that many
bytes. -/
def coinsBits (n : Nat) : BitString := natToBits (coinsLen n) 4 ++ natToBits n (coinsLen n * 8)

theorem coinsBits_size (n : Nat) : (coinsBits n).size = 4 + coinsLen n * 8 := by
  simp [coinsBits]

theorem lt_two_pow_natLenBits (n : Nat) : n < 2 ^ natLenBits n := by
  unfold natLenBits
  split
  · omega
  · exact Nat.lt_log2_self

/-- `n` fits its `Coins` bytes. -/
theorem lt_two_pow_coinsLen (n : Nat) : n < 2 ^ (coinsLen n * 8) := by
  have h2 : natLenBits n ≤ coinsLen n * 8 := by unfold coinsLen; omega
  exact Nat.lt_of_lt_of_le (lt_two_pow_natLenBits n) (Nat.pow_le_pow_right (by decide) h2)

/-- An amount of fewer than 16 bytes is below `2^120` (what `STGRAMS` accepts). -/
theorem lt_of_coinsLen_lt {n : Nat} (h : coinsLen n < 16) : n < 2 ^ 120 := by
  have h1 := lt_two_pow_coinsLen n
  have h2 : coinsLen n * 8 ≤ 120 := by omega
  exact Nat.lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by decide) h2)

/-- The bits of an amount read back (`LDGRAMS`): its length, then the amount. -/
theorem bitsToNat_coinsLen {n : Nat} (h : coinsLen n < 16) : bitsToNat (natToBits (coinsLen n) 4) = coinsLen n :=
  bitsToNat_natToBits_of_lt (by simpa using h)

theorem bitsToNat_coins (n : Nat) : bitsToNat (natToBits n (coinsLen n * 8)) = n :=
  bitsToNat_natToBits_of_lt (lt_two_pow_coinsLen n)

/-! ## Message addresses -/

/-- The length of the message address at bit `p` of `bs` as `LDMSGADDR` reads it at every global
version, by its tag (C++ `skip_message_addr`, tonops.cpp:1621-1646): `addr_none$00` 2 bits,
`addr_extern$01 len:(## 9) external_address:(bits len)` `11 + len` bits, `addr_std$10` without an
anycast (`nothing$0`) `workchain_id:int8 address:bits256` 267 bits; 0 for an anycast or
`addr_var$11` (read only before global version 10). -/
def addrLenAt (bs : BitString) (p : Nat) : Nat :=
  match bs[p]!, bs[p + 1]! with
  | false, false => 2
  | false, true => 11 + bitsToNat (bs.extract (p + 2) (p + 11))
  | true, false => if bs[p + 2]! then 0 else 267
  | true, true => 0

/-- A message address that `LDMSGADDR` reads in full at every global version: its bits are one
address of `addrLenAt`. -/
def MsgAddr.Valid (a : BitString) : Prop := addrLenAt a 0 = a.size

instance (a : BitString) : Decidable (MsgAddr.Valid a) := inferInstanceAs (Decidable (_ = _))

/-- Bit `i` of a slice of bits. -/
theorem getElem!_of_extract {bs a : BitString} {p n i : Nat} (h : bs.extract p (p + n) = a)
    (hn : p + n ≤ bs.size) (hi : i < n) : bs[p + i]! = a[i]! := by
  subst h
  have h1 : p + i < bs.size := by omega
  have h2 : i < (bs.extract p (p + n)).size := by simp; omega
  rw [getElem!_pos bs (p + i) h1, getElem!_pos _ i h2, Array.getElem_extract]

/-- The bits from `i` to `i + k` of a slice of bits. -/
theorem extract_of_extract {bs a : BitString} {p n i k : Nat} (h : bs.extract p (p + n) = a)
    (hk : i + k ≤ n) : bs.extract (p + i) (p + i + k) = a.extract i (i + k) := by
  subst h
  rw [Array.extract_extract]
  congr 1 <;> omega

/-- A bit that is set is within the bit string. -/
theorem lt_size_of_getElem! {a : BitString} {i : Nat} (h : a[i]! = true) : i < a.size := by
  if hc : i < a.size then exact hc
  else
    rw [getElem!_neg a i hc] at h
    cases h

/-- `addrLenAt` by its tag bits. -/
theorem addrLenAt_eq (bs : BitString) (p : Nat) : addrLenAt bs p =
    if bs[p]! then (if bs[p + 1]! then 0 else if bs[p + 2]! then 0 else 267)
    else if bs[p + 1]! then 11 + bitsToNat (bs.extract (p + 2) (p + 11)) else 2 := by
  unfold addrLenAt
  split <;> simp_all

/-- A valid address has at least its two tag bits. -/
theorem MsgAddr.Valid.two_le {a : BitString} (ha : MsgAddr.Valid a) : 2 ≤ a.size := by
  unfold MsgAddr.Valid at ha
  rw [addrLenAt_eq] at ha
  simp only [Nat.zero_add] at ha
  by_cases h0 : a[0]! = true
  · have := lt_size_of_getElem! h0
    by_cases h1 : a[1]! = true
    · simp [h0, h1] at ha; omega
    · by_cases h2 : a[2]! = true
      · simp [h0, h1, h2] at ha; omega
      · simp [h0, h1, h2] at ha; omega
  · by_cases h1 : a[1]! = true
    · simp [h0, h1] at ha; omega
    · simp [h0, h1] at ha; omega

/-- The length `addrLenAt` reads at a position where the bits are a valid address is its size. -/
theorem addrLenAt_of_extract {bs a : BitString} {p : Nat} (ha : MsgAddr.Valid a)
    (h : bs.extract p (p + a.size) = a) (hn : p + a.size ≤ bs.size) : addrLenAt bs p = a.size := by
  have hs := ha.two_le
  have h0 := getElem!_of_extract (i := 0) h hn (by omega)
  have h1 := getElem!_of_extract (i := 1) h hn (by omega)
  rw [Nat.add_zero] at h0
  have ha' := ha
  unfold MsgAddr.Valid at ha'
  rw [addrLenAt_eq] at ha'
  simp only [Nat.zero_add] at ha'
  rw [addrLenAt_eq, h0, h1]
  by_cases a0 : a[0]! = true
  · by_cases a1 : a[1]! = true
    · simp [a0, a1] at ha'; omega
    · have h2 := getElem!_of_extract (i := 2) h hn (by simp [a0, a1] at ha'; split at ha' <;> omega)
      rw [h2]
      simpa [a0, a1] using ha'
  · by_cases a1 : a[1]! = true
    · simp only [a0, a1, Bool.false_eq_true, if_false, if_true] at ha' ⊢
      rw [extract_of_extract (i := 2) (k := 9) h (by omega)]
      exact ha'
    · simpa [a0, a1] using ha'

/-- The value of two bits. -/
theorem bitsToNat_two (x y : Bool) : bitsToNat #[x, y] = 2 * (if x then 1 else 0) + (if y then 1 else 0) := by
  cases x <;> cases y <;> rfl

/-- Two bits of a slice of bits. -/
theorem extract_two {bs : BitString} {p : Nat} (h : p + 2 ≤ bs.size) :
    bs.extract p (p + 2) = #[bs[p]!, bs[p + 1]!] := by
  apply Array.ext
  · simp; omega
  · intro i h1 h2
    simp only [Array.size_extract] at h1
    have : i = 0 ∨ i = 1 := by omega
    rcases this with rfl | rfl
    · simp [Array.getElem_extract, getElem!_pos bs p (by omega)]
    · simp [Array.getElem_extract, getElem!_pos bs (p + 1) (by omega)]

/-- One bit of a slice of bits. -/
theorem extract_one {bs : BitString} {p : Nat} (h : p + 1 ≤ bs.size) : bs.extract p (p + 1) = #[bs[p]!] := by
  apply Array.ext
  · simp; omega
  · intro i h1 h2
    simp only [Array.size_extract] at h1
    have : i = 0 := by omega
    subst this
    simp [Array.getElem_extract, getElem!_pos bs p (by omega)]

/-- **`LDMSGADDR` reads a valid address in full**, at every global version: at any position of a
slice whose bits there are the address, the rest is the slice after the address. -/
theorem skipMessageAddr_of_valid {s : Slice} {a : BitString} (gv : Nat) (ha : MsgAddr.Valid a)
    (h : s.cell.bits.extract s.bitPos (s.bitPos + a.size) = a) (hn : s.bitPos + a.size ≤ s.cell.bits.size) :
    s.skipMessageAddr gv = .ok (s.advanceBits a.size) := by
  have hlen := addrLenAt_of_extract ha h hn
  have hs := ha.two_le
  obtain ⟨c, p, r⟩ := s
  simp only at h hn hlen ⊢
  rw [addrLenAt_eq] at hlen
  have h2 := extract_two (bs := c.bits) (p := p) (by omega)
  unfold Slice.skipMessageAddr
  simp only [Slice.takeBitsAsNatCellUnd, Slice.haveBits, Slice.readBits, Slice.advanceBits,
    decide_eq_true (show p + 2 ≤ c.bits.size by omega), if_true, h2, bind, Except.bind, pure,
    Except.pure, bitsToNat_two]
  by_cases b0 : c.bits[p]! = true
  · by_cases b1 : c.bits[p + 1]! = true
    · simp [b0, b1] at hlen; omega
    · by_cases b2 : c.bits[p + 2]! = true
      · simp [b0, b1, b2] at hlen; omega
      · simp only [b0, b1, b2, Bool.false_eq_true, if_false, if_true] at hlen ⊢
        simp only [Slice.skipMaybeAnycast, Slice.takeBitsAsNatCellUnd,
          Slice.haveBits, Slice.readBits, Slice.advanceBits, bind, Except.bind, pure, Except.pure]
        have h3 : p + 2 + 1 ≤ c.bits.size := by omega
        simp only [decide_eq_true h3, if_true, extract_one h3, Bool.not_eq_true] at b2 ⊢
        simp only [b2, show bitsToNat #[false] = 0 from rfl, if_true]
        have h4 : p + 2 + 1 + (8 + 256) ≤ c.bits.size := by omega
        simp only [decide_eq_true h4, if_true]
        congr 2
        omega
  · by_cases b1 : c.bits[p + 1]! = true
    · simp only [b0, b1, Bool.false_eq_true, if_false, if_true] at hlen ⊢
      have h9 : p + 2 + 9 ≤ c.bits.size := by omega
      have e : p + 2 + 9 = p + 11 := by omega
      simp only [decide_eq_true h9, if_true, e]
      have h11 : p + 11 + bitsToNat (c.bits.extract (p + 2) (p + 11)) ≤ c.bits.size := by omega
      simp only [decide_eq_true h11, if_true]
      congr 2
      omega
    · simp only [b0, b1, Bool.false_eq_true, if_false] at hlen ⊢
      congr 2
      omega

/-! ## The data -/

/-- The data of the storage contract (`storage#_` of `storage-contract.fc`); the addresses are
their bits. -/
structure Data where
  active : Bool
  balance : Nat
  provider : BitString
  merkleHash : Nat
  fileSize : Nat
  nextProof : Nat
  ratePerMbDay : Nat
  maxSpan : Nat
  lastProofTime : Nat
  client : BitString
  torrentHash : Nat
  deriving DecidableEq, Repr

/-- The fields within their widths, the addresses valid at every global version. -/
def Data.WF (d : Data) : Prop :=
  coinsLen d.balance < 16 ∧ MsgAddr.Valid d.provider ∧ d.merkleHash < 2 ^ 256 ∧ d.fileSize < 2 ^ 64 ∧
    d.nextProof < 2 ^ 64 ∧ coinsLen d.ratePerMbDay < 16 ∧ d.maxSpan < 2 ^ 32 ∧ d.lastProofTime < 2 ^ 32 ∧
    MsgAddr.Valid d.client ∧ d.torrentHash < 2 ^ 256

instance (d : Data) : Decidable d.WF := by unfold Data.WF; infer_instance

/-- The reference of the data: `client:MsgAddress torrent_hash:uint256`. -/
def Data.clientCell (d : Data) : Cell := Cell.mkOrdinary (d.client ++ natToBits d.torrentHash 256) #[]

/-- The bits of the data cell. -/
def Data.bits (d : Data) : BitString :=
  #[d.active] ++ coinsBits d.balance ++ d.provider ++ natToBits d.merkleHash 256 ++ natToBits d.fileSize 64 ++
    natToBits d.nextProof 64 ++ coinsBits d.ratePerMbDay ++ natToBits d.maxSpan 32 ++ natToBits d.lastProofTime 32

/-- The data cell, as the contract writes it. -/
def Data.encode (d : Data) : Cell := Cell.mkOrdinary d.bits #[d.clientCell]

theorem Data.bits_size (d : Data) :
    d.bits.size = 1 + (4 + coinsLen d.balance * 8) + d.provider.size + 256 + 64 + 64 +
      (4 + coinsLen d.ratePerMbDay * 8) + 32 + 32 := by
  simp [Data.bits, coinsBits_size]
  omega

/-! ## Reading the data -/

/-- The fields of a data cell, read as the contract reads them: the flag (`LDI 1`), the amounts
(`LDGRAMS`: 4 bits of length, then that many bytes), the provider (`LDMSGADDR`, `addrLenAt`), the
numbers (`LDU`), and in the first reference the client (`LDMSGADDR`) and the torrent hash
(`256 LDU`). Nothing is checked: `decode` checks. -/
def Data.parse (c : Cell) : Data :=
  let bs := c.bits
  let lb := bitsToNat (bs.extract 1 5)
  let p1 := 5 + lb * 8
  let p2 := p1 + addrLenAt bs p1
  let lr := bitsToNat (bs.extract (p2 + 384) (p2 + 388))
  let p3 := p2 + 388 + lr * 8
  let cb := c.refs[0]!.bits
  let lc := addrLenAt cb 0
  { active := bs[0]!
    balance := bitsToNat (bs.extract 5 p1)
    provider := bs.extract p1 p2
    merkleHash := bitsToNat (bs.extract p2 (p2 + 256))
    fileSize := bitsToNat (bs.extract (p2 + 256) (p2 + 320))
    nextProof := bitsToNat (bs.extract (p2 + 320) (p2 + 384))
    ratePerMbDay := bitsToNat (bs.extract (p2 + 388) p3)
    maxSpan := bitsToNat (bs.extract p3 (p3 + 32))
    lastProofTime := bitsToNat (bs.extract (p3 + 32) (p3 + 64))
    client := cb.extract 0 lc
    torrentHash := bitsToNat (cb.extract lc (lc + 256)) }

/-- The data of a cell: its fields as the contract reads them (`parse`), if they are within their
widths and the cell is exactly what the contract writes for them (in particular an ordinary cell
with the flag, the fields in order, nothing after them, the amounts in their fewest bytes, one
reference holding the client and the torrent hash and nothing else). -/
def Data.decode (c : Cell) : Option Data :=
  let d := Data.parse c
  if d.WF ∧ d.encode = c then some d else none

/-- A middle part of three bit strings. -/
theorem extract_mid {A B C : BitString} {p q : Nat} (hp : p = A.size) (hq : q = A.size + B.size) :
    (A ++ B ++ C).extract p q = B := by
  subst hp hq
  rw [Array.append_assoc, Array.extract_append, Array.extract_eq_empty_of_le (by simp),
    Array.empty_append, Nat.sub_self, Nat.add_sub_cancel_left, Array.extract_append,
    Array.extract_eq_self_of_le (by omega), Array.extract_eq_empty_of_le (by simp),
    Array.append_empty]

/-- The last part of two bit strings. -/
theorem extract_last {A B : BitString} {p q : Nat} (hp : p = A.size) (hq : A.size + B.size ≤ q) :
    (A ++ B).extract p q = B := by
  subst hp
  have h1 : A.extract A.size q = #[] := Array.extract_eq_empty_of_le (Nat.min_le_right _ _)
  rw [Array.extract_append, h1, Array.empty_append, Nat.sub_self, Array.extract_eq_self_of_le (by omega)]

/-- The bits of the data cut at a field: those before, the field, those after. -/
private theorem bits_cut (d : Data) (A B C : BitString) (h : d.bits = A ++ (B ++ C)) : d.bits = A ++ B ++ C := by
  rw [h, Array.append_assoc]

/-- The bits of the data at the position of the flag `active` (`LDI 1`). -/
theorem Data.extract_flag (d : Data) {p q : Nat}
    (hp : p = 0) (hq : q = p + 1) :
    d.bits.extract p q = #[d.active] := by
  rw [bits_cut d
    #[]
    (#[d.active])
    (natToBits (coinsLen d.balance) 4 ++ natToBits d.balance (coinsLen d.balance * 8) ++
      d.provider ++ natToBits d.merkleHash 256 ++ natToBits d.fileSize 64 ++
      natToBits d.nextProof 64 ++ natToBits (coinsLen d.ratePerMbDay) 4 ++
      natToBits d.ratePerMbDay (coinsLen d.ratePerMbDay * 8) ++ natToBits d.maxSpan 32 ++
      natToBits d.lastProofTime 32)
    (by simp only [Data.bits, coinsBits, Array.append_assoc, Array.empty_append])]
  exact extract_mid (by simp; omega) (by simp; omega)

/-- The bits of the data at the position of the length in bytes of `balance` (`LDGRAMS`). -/
theorem Data.extract_balanceLen (d : Data) {p q : Nat}
    (hp : p = 1) (hq : q = p + 4) :
    d.bits.extract p q = natToBits (coinsLen d.balance) 4 := by
  rw [bits_cut d
    (#[d.active])
    (natToBits (coinsLen d.balance) 4)
    (natToBits d.balance (coinsLen d.balance * 8) ++ d.provider ++ natToBits d.merkleHash 256 ++
      natToBits d.fileSize 64 ++ natToBits d.nextProof 64 ++ natToBits (coinsLen d.ratePerMbDay) 4 ++
      natToBits d.ratePerMbDay (coinsLen d.ratePerMbDay * 8) ++ natToBits d.maxSpan 32 ++
      natToBits d.lastProofTime 32)
    (by simp only [Data.bits, coinsBits, Array.append_assoc])]
  exact extract_mid (by simp; omega) (by simp; omega)

/-- The bits of the data at the position of `balance` (`LDGRAMS`). -/
theorem Data.extract_balance (d : Data) {p q : Nat}
    (hp : p = 5) (hq : q = p + coinsLen d.balance * 8) :
    d.bits.extract p q = natToBits d.balance (coinsLen d.balance * 8) := by
  rw [bits_cut d
    (#[d.active] ++ natToBits (coinsLen d.balance) 4)
    (natToBits d.balance (coinsLen d.balance * 8))
    (d.provider ++ natToBits d.merkleHash 256 ++ natToBits d.fileSize 64 ++
      natToBits d.nextProof 64 ++ natToBits (coinsLen d.ratePerMbDay) 4 ++
      natToBits d.ratePerMbDay (coinsLen d.ratePerMbDay * 8) ++ natToBits d.maxSpan 32 ++
      natToBits d.lastProofTime 32)
    (by simp only [Data.bits, coinsBits, Array.append_assoc])]
  exact extract_mid (by simp; omega) (by simp; omega)

/-- The bits of the data at the position of `provider` (`LDMSGADDR`). -/
theorem Data.extract_provider (d : Data) {p q : Nat}
    (hp : p = 5 + coinsLen d.balance * 8) (hq : q = p + d.provider.size) :
    d.bits.extract p q = d.provider := by
  rw [bits_cut d
    (#[d.active] ++ natToBits (coinsLen d.balance) 4 ++ natToBits d.balance (coinsLen d.balance * 8))
    (d.provider)
    (natToBits d.merkleHash 256 ++ natToBits d.fileSize 64 ++ natToBits d.nextProof 64 ++
      natToBits (coinsLen d.ratePerMbDay) 4 ++
      natToBits d.ratePerMbDay (coinsLen d.ratePerMbDay * 8) ++ natToBits d.maxSpan 32 ++
      natToBits d.lastProofTime 32)
    (by simp only [Data.bits, coinsBits, Array.append_assoc])]
  exact extract_mid (by simp; omega) (by simp; omega)

/-- The bits of the data at the position of `merkle_hash` (`256 LDU`). -/
theorem Data.extract_merkleHash (d : Data) {p q : Nat}
    (hp : p = 5 + coinsLen d.balance * 8 + d.provider.size) (hq : q = p + 256) :
    d.bits.extract p q = natToBits d.merkleHash 256 := by
  rw [bits_cut d
    (#[d.active] ++ natToBits (coinsLen d.balance) 4 ++
      natToBits d.balance (coinsLen d.balance * 8) ++ d.provider)
    (natToBits d.merkleHash 256)
    (natToBits d.fileSize 64 ++ natToBits d.nextProof 64 ++ natToBits (coinsLen d.ratePerMbDay) 4 ++
      natToBits d.ratePerMbDay (coinsLen d.ratePerMbDay * 8) ++ natToBits d.maxSpan 32 ++
      natToBits d.lastProofTime 32)
    (by simp only [Data.bits, coinsBits, Array.append_assoc])]
  exact extract_mid (by simp; omega) (by simp; omega)

/-- The bits of the data at the position of `file_size` (`64 LDU`). -/
theorem Data.extract_fileSize (d : Data) {p q : Nat}
    (hp : p = 5 + coinsLen d.balance * 8 + d.provider.size + 256) (hq : q = p + 64) :
    d.bits.extract p q = natToBits d.fileSize 64 := by
  rw [bits_cut d
    (#[d.active] ++ natToBits (coinsLen d.balance) 4 ++
      natToBits d.balance (coinsLen d.balance * 8) ++ d.provider ++ natToBits d.merkleHash 256)
    (natToBits d.fileSize 64)
    (natToBits d.nextProof 64 ++ natToBits (coinsLen d.ratePerMbDay) 4 ++
      natToBits d.ratePerMbDay (coinsLen d.ratePerMbDay * 8) ++ natToBits d.maxSpan 32 ++
      natToBits d.lastProofTime 32)
    (by simp only [Data.bits, coinsBits, Array.append_assoc])]
  exact extract_mid (by simp; omega) (by simp; omega)

/-- The bits of the data at the position of `next_proof_byte` (`64 LDU`). -/
theorem Data.extract_nextProof (d : Data) {p q : Nat}
    (hp : p = 5 + coinsLen d.balance * 8 + d.provider.size + 320) (hq : q = p + 64) :
    d.bits.extract p q = natToBits d.nextProof 64 := by
  rw [bits_cut d
    (#[d.active] ++ natToBits (coinsLen d.balance) 4 ++
      natToBits d.balance (coinsLen d.balance * 8) ++ d.provider ++ natToBits d.merkleHash 256 ++
      natToBits d.fileSize 64)
    (natToBits d.nextProof 64)
    (natToBits (coinsLen d.ratePerMbDay) 4 ++
      natToBits d.ratePerMbDay (coinsLen d.ratePerMbDay * 8) ++ natToBits d.maxSpan 32 ++
      natToBits d.lastProofTime 32)
    (by simp only [Data.bits, coinsBits, Array.append_assoc])]
  exact extract_mid (by simp; omega) (by simp; omega)

/-- The bits of the data at the position of the length in bytes of `rate_per_mb_day` (`LDGRAMS`). -/
theorem Data.extract_rateLen (d : Data) {p q : Nat}
    (hp : p = 5 + coinsLen d.balance * 8 + d.provider.size + 384) (hq : q = p + 4) :
    d.bits.extract p q = natToBits (coinsLen d.ratePerMbDay) 4 := by
  rw [bits_cut d
    (#[d.active] ++ natToBits (coinsLen d.balance) 4 ++
      natToBits d.balance (coinsLen d.balance * 8) ++ d.provider ++ natToBits d.merkleHash 256 ++
      natToBits d.fileSize 64 ++ natToBits d.nextProof 64)
    (natToBits (coinsLen d.ratePerMbDay) 4)
    (natToBits d.ratePerMbDay (coinsLen d.ratePerMbDay * 8) ++ natToBits d.maxSpan 32 ++
      natToBits d.lastProofTime 32)
    (by simp only [Data.bits, coinsBits, Array.append_assoc])]
  exact extract_mid (by simp; omega) (by simp; omega)

/-- The bits of the data at the position of `rate_per_mb_day` (`LDGRAMS`). -/
theorem Data.extract_rate (d : Data) {p q : Nat}
    (hp : p = 5 + coinsLen d.balance * 8 + d.provider.size + 388) (hq : q = p + coinsLen d.ratePerMbDay * 8) :
    d.bits.extract p q = natToBits d.ratePerMbDay (coinsLen d.ratePerMbDay * 8) := by
  rw [bits_cut d
    (#[d.active] ++ natToBits (coinsLen d.balance) 4 ++
      natToBits d.balance (coinsLen d.balance * 8) ++ d.provider ++ natToBits d.merkleHash 256 ++
      natToBits d.fileSize 64 ++ natToBits d.nextProof 64 ++ natToBits (coinsLen d.ratePerMbDay) 4)
    (natToBits d.ratePerMbDay (coinsLen d.ratePerMbDay * 8))
    (natToBits d.maxSpan 32 ++ natToBits d.lastProofTime 32)
    (by simp only [Data.bits, coinsBits, Array.append_assoc])]
  exact extract_mid (by simp; omega) (by simp; omega)

/-- The bits of the data at the position of `max_span` (`32 LDU`). -/
theorem Data.extract_maxSpan (d : Data) {p q : Nat}
    (hp : p = 5 + coinsLen d.balance * 8 + d.provider.size + 388 + coinsLen d.ratePerMbDay * 8) (hq : q = p + 32) :
    d.bits.extract p q = natToBits d.maxSpan 32 := by
  rw [bits_cut d
    (#[d.active] ++ natToBits (coinsLen d.balance) 4 ++
      natToBits d.balance (coinsLen d.balance * 8) ++ d.provider ++ natToBits d.merkleHash 256 ++
      natToBits d.fileSize 64 ++ natToBits d.nextProof 64 ++ natToBits (coinsLen d.ratePerMbDay) 4 ++
      natToBits d.ratePerMbDay (coinsLen d.ratePerMbDay * 8))
    (natToBits d.maxSpan 32)
    (natToBits d.lastProofTime 32)
    (by simp only [Data.bits, coinsBits, Array.append_assoc])]
  exact extract_mid (by simp; omega) (by simp; omega)

/-- The bits of the data at the position of `last_proof_time` (`32 LDU`). -/
theorem Data.extract_lastProofTime (d : Data) {p q : Nat}
    (hp : p = 5 + coinsLen d.balance * 8 + d.provider.size + 388 + coinsLen d.ratePerMbDay * 8 + 32) (hq : q = p + 32) :
    d.bits.extract p q = natToBits d.lastProofTime 32 := by
  rw [bits_cut d
    (#[d.active] ++ natToBits (coinsLen d.balance) 4 ++
      natToBits d.balance (coinsLen d.balance * 8) ++ d.provider ++ natToBits d.merkleHash 256 ++
      natToBits d.fileSize 64 ++ natToBits d.nextProof 64 ++ natToBits (coinsLen d.ratePerMbDay) 4 ++
      natToBits d.ratePerMbDay (coinsLen d.ratePerMbDay * 8) ++ natToBits d.maxSpan 32)
    (natToBits d.lastProofTime 32)
    #[]
    (by simp only [Data.bits, coinsBits, Array.append_assoc, Array.append_empty])]
  exact extract_mid (by simp; omega) (by simp; omega)

/-- The bits of the data from the position of `provider` (`LDMSGADDR`) to the end. -/
theorem Data.extract_afterBalance (d : Data) {p q : Nat} (hp : p = 5 + coinsLen d.balance * 8) (hq : d.bits.size ≤ q) :
    d.bits.extract p q =
      d.provider ++ natToBits d.merkleHash 256 ++ natToBits d.fileSize 64 ++
        natToBits d.nextProof 64 ++ natToBits (coinsLen d.ratePerMbDay) 4 ++
        natToBits d.ratePerMbDay (coinsLen d.ratePerMbDay * 8) ++ natToBits d.maxSpan 32 ++
        natToBits d.lastProofTime 32 := by
  have e : d.bits =
      (#[d.active] ++ natToBits (coinsLen d.balance) 4 ++
        natToBits d.balance (coinsLen d.balance * 8)) ++
      (d.provider ++ natToBits d.merkleHash 256 ++ natToBits d.fileSize 64 ++
        natToBits d.nextProof 64 ++ natToBits (coinsLen d.ratePerMbDay) 4 ++
        natToBits d.ratePerMbDay (coinsLen d.ratePerMbDay * 8) ++ natToBits d.maxSpan 32 ++
        natToBits d.lastProofTime 32) := by
    simp only [Data.bits, coinsBits, Array.append_assoc]
  have hs := Data.bits_size d
  rw [e]
  exact extract_last (by simp; omega) (by simp; omega)

/-- The bits of the data from the position of `merkle_hash` (`256 LDU`) to the end. -/
theorem Data.extract_afterProvider (d : Data) {p q : Nat} (hp : p = 5 + coinsLen d.balance * 8 + d.provider.size) (hq : d.bits.size ≤ q) :
    d.bits.extract p q =
      natToBits d.merkleHash 256 ++ natToBits d.fileSize 64 ++ natToBits d.nextProof 64 ++
        natToBits (coinsLen d.ratePerMbDay) 4 ++
        natToBits d.ratePerMbDay (coinsLen d.ratePerMbDay * 8) ++ natToBits d.maxSpan 32 ++
        natToBits d.lastProofTime 32 := by
  have e : d.bits =
      (#[d.active] ++ natToBits (coinsLen d.balance) 4 ++
        natToBits d.balance (coinsLen d.balance * 8) ++ d.provider) ++
      (natToBits d.merkleHash 256 ++ natToBits d.fileSize 64 ++ natToBits d.nextProof 64 ++
        natToBits (coinsLen d.ratePerMbDay) 4 ++
        natToBits d.ratePerMbDay (coinsLen d.ratePerMbDay * 8) ++ natToBits d.maxSpan 32 ++
        natToBits d.lastProofTime 32) := by
    simp only [Data.bits, coinsBits, Array.append_assoc]
  have hs := Data.bits_size d
  rw [e]
  exact extract_last (by simp; omega) (by simp; omega)

/-! ## The cells -/

theorem Data.encode_bits (d : Data) : d.encode.bits = d.bits := rfl
theorem Data.encode_refs (d : Data) : d.encode.refs = #[d.clientCell] := rfl
theorem Data.encode_special (d : Data) : d.encode.special = false := rfl
theorem Data.clientCell_bits (d : Data) : d.clientCell.bits = d.client ++ natToBits d.torrentHash 256 := rfl
theorem Data.clientCell_refs (d : Data) : d.clientCell.refs = #[] := rfl
theorem Data.clientCell_special (d : Data) : d.clientCell.special = false := rfl

/-- The client address in the reference. -/
theorem Data.extract_client (d : Data) {p q : Nat} (hp : p = 0) (hq : q = p + d.client.size) :
    (d.client ++ natToBits d.torrentHash 256).extract p q = d.client := by
  subst hp hq
  rw [Array.extract_append, Nat.zero_add, Array.extract_eq_self_of_le (Nat.le_refl _), Nat.zero_sub, Nat.sub_self,
    Array.extract_eq_empty_of_le (by simp), Array.append_empty]

/-- The torrent hash in the reference. -/
theorem Data.extract_torrentHash (d : Data) {p q : Nat} (hp : p = d.client.size) (hq : q = p + 256) :
    (d.client ++ natToBits d.torrentHash 256).extract p q = natToBits d.torrentHash 256 := by
  subst hp hq
  exact extract_last rfl (by simp)

/-- The flag is the first bit. -/
theorem Data.getElem!_flag (d : Data) : d.bits[0]! = d.active := by
  have h : d.bits.extract 0 (0 + 1) = #[d.active] := Data.extract_flag d rfl rfl
  have hs := Data.bits_size d
  have h1 : 0 + 1 ≤ d.bits.size := by omega
  have := getElem!_of_extract (bs := d.bits) (p := 0) (n := 1) (i := 0) h h1 (Nat.zero_lt_one)
  rw [Nat.add_zero] at this
  exact this.trans rfl

/-! ## Round trips -/

/-- **The contract reads back the data it writes**: the fields `parse` reads from `encode d` are
those of `d`, for fields within their widths and valid addresses. -/
theorem Data.parse_encode (d : Data) (h : d.WF) : Data.parse d.encode = d := by
  obtain ⟨hb, hp, hm, hf, hn, hr, hs, hl, hc, ht⟩ := h
  have hsz := Data.bits_size d
  have hbl : bitsToNat (d.bits.extract 1 5) = coinsLen d.balance := by
    rw [Data.extract_balanceLen d rfl rfl]; exact bitsToNat_coinsLen hb
  have hal : addrLenAt d.bits (5 + coinsLen d.balance * 8) = d.provider.size :=
    addrLenAt_of_extract hp (Data.extract_provider d rfl rfl) (by omega)
  have hrl : bitsToNat (d.bits.extract (5 + coinsLen d.balance * 8 + d.provider.size + 384)
      (5 + coinsLen d.balance * 8 + d.provider.size + 388)) = coinsLen d.ratePerMbDay := by
    rw [Data.extract_rateLen d rfl rfl]; exact bitsToNat_coinsLen hr
  have hcl : addrLenAt (d.client ++ natToBits d.torrentHash 256) 0 = d.client.size :=
    addrLenAt_of_extract hc (Data.extract_client d rfl (by simp)) (by simp)
  have hc0 : (#[d.clientCell] : Array Cell)[0]! = d.clientCell := rfl
  simp only [Data.parse, Data.encode_bits, Data.encode_refs, hc0, Data.clientCell_bits, hbl, hal, hrl, hcl]
  simp (disch := omega) only [Data.getElem!_flag, Data.extract_balance, Data.extract_provider,
    Data.extract_merkleHash, Data.extract_fileSize, Data.extract_nextProof, Data.extract_rate,
    Data.extract_maxSpan, Data.extract_lastProofTime, Data.extract_client, Data.extract_torrentHash,
    bitsToNat_coins, bitsToNat_natToBits_of_lt hm, bitsToNat_natToBits_of_lt hf, bitsToNat_natToBits_of_lt hn,
    bitsToNat_natToBits_of_lt hs, bitsToNat_natToBits_of_lt hl, bitsToNat_natToBits_of_lt ht]

theorem Data.decode_encode (d : Data) (h : d.WF) : Data.decode d.encode = some d := by
  unfold Data.decode
  simp only [Data.parse_encode d h, and_true]
  rw [if_pos h]

theorem Data.encode_decode {c : Cell} {d : Data} (h : Data.decode c = some d) : d.encode = c ∧ d.WF := by
  unfold Data.decode at h
  simp only at h
  split at h
  · rename_i hc
    cases h
    exact ⟨hc.2, hc.1⟩
  · cases h

/-- A cell decodes to `d` exactly when it is `encode d` of a `d` within the widths. -/
theorem Data.decode_eq_some_iff (c : Cell) (d : Data) : Data.decode c = some d ↔ c = d.encode ∧ d.WF := by
  constructor
  · intro h; obtain ⟨h1, h2⟩ := Data.encode_decode h; exact ⟨h1.symm, h2⟩
  · rintro ⟨rfl, h⟩; exact Data.decode_encode d h

end TvmLean.Contracts.Storage
