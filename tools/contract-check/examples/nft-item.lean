-- The NFT item (TEP-62) of ton-blockchain/token-contract (nft/nft-item.fc;
-- tools/txoracle/contracts.txt#nft.item.code, the one most used on the mainnet; nft2.item.code is the
-- repository's head): the data is `index:uint64 collection_address:MsgAddress`, then, once the
-- collection initialized the item, `owner_address:MsgAddress content:^Cell`. Invariant: the data
-- starts with the index `index` and the collection 0:`collection`, whatever follows: whatever
-- messages arrive, the index and the collection never change (and the code never changes). The
-- reads of the layout (`LDU 64`, `LDMSGADDR`) are rewrites of the hints, as those of TON Storage
-- (TvmLean/Proofs/Contracts/StorageRun/Read.lean, whose generic lemmas they use).
import TvmLean.Proofs.Contracts.StorageRun.Read
-- contract-check: invariant Inv index collection
-- contract-check: params (index collection : Nat)
-- contract-check: hints Data.read_index0, Data.skip_collection, Data.prefix_collection, Data.encode_bits_size, Data.encode_refs, Contracts.Storage.toCellRemaining_ofCell_mkOrdinary, Contracts.Storage.readBits_ofCell_all

open TvmLean.Contracts TvmLean.Contracts.Storage

/-- `addr_std$10 anycast:nothing$0 workchain_id:int8 address:bits256` in the workchain 0. -/
def addrBits (h : Nat) : BitString := #[true, false, false] ++ natToBits 0 8 ++ natToBits h 256

theorem addrBits_size (h : Nat) : (addrBits h).size = 267 := by simp [addrBits]

/-- An address of `addrBits` is one `LDMSGADDR` reads in full. -/
theorem addrBits_valid (h : Nat) : MsgAddr.Valid (addrBits h) := by
  have e : (addrBits h).extract 0 (0 + 3) = #[true, false, false] := by
    rw [show addrBits h = #[] ++ #[true, false, false] ++ (natToBits 0 8 ++ natToBits h 256) by
      simp [addrBits, Array.append_assoc]]
    exact extract_mid (by rfl) (by rfl)
  have hn : 0 + 3 ≤ (addrBits h).size := by rw [addrBits_size]; omega
  have b0 := getElem!_of_extract (i := 0) e hn (by omega)
  have b1 := getElem!_of_extract (i := 1) e hn (by omega)
  have b2 := getElem!_of_extract (i := 2) e hn (by omega)
  unfold MsgAddr.Valid
  rw [addrLenAt_eq, addrBits_size]
  simp only [Nat.zero_add] at b0 b1 b2 ⊢
  rw [b0, b1, b2]
  rfl

/-- The fields of the data: the index, the collection, and the rest (the owner and the content once
initialized, nothing before). -/
structure Data where
  index : Nat
  collection : Nat
  rest : BitString
  restRefs : Array Cell

def Data.bits (d : Data) : BitString := natToBits d.index 64 ++ addrBits d.collection ++ d.rest

/-- The data cell. -/
def Data.encode (d : Data) : Cell := Cell.mkOrdinary d.bits d.restRefs

theorem Data.encode_bits_size (d : Data) : d.encode.bits.size = 64 + 267 + d.rest.size := by
  show d.bits.size = _
  simp only [Data.bits, Array.size_append, natToBits_size, addrBits_size]

theorem Data.encode_refs (d : Data) : d.encode.refs = d.restRefs := rfl

/-- The index (`LDU 64`, the first read of the data). -/
theorem Data.read_index0 (d : Data) (h : d.index < 2 ^ 64) :
    bitsToNat (Slice.readBits (Slice.ofCell d.encode) 64) = d.index := by
  show bitsToNat (d.bits.extract 0 (0 + 64)) = d.index
  rw [show d.bits = #[] ++ natToBits d.index 64 ++ (addrBits d.collection ++ d.rest) by
    simp [Data.bits, Array.append_assoc]]
  rw [extract_mid (by rfl) (by simp)]
  exact bitsToNat_natToBits_of_lt h

theorem Data.extract_collection (d : Data) {p q : Nat} (hp : p = 64) (hq : q = p + 267) :
    d.bits.extract p q = addrBits d.collection :=
  extract_mid (by simp [hp]) (by simp [addrBits_size, hp, hq])

/-- The collection (`LDMSGADDR`): the address read in full. -/
theorem Data.skip_collection (d : Data) {p r : Nat} (gv : Nat) (hp : p = 64) :
    Slice.skipMessageAddr ⟨d.encode, p, r⟩ gv = .ok ⟨d.encode, p + 267, r⟩ := by
  have h := skipMessageAddr_of_valid (s := ⟨d.encode, p, r⟩) gv (addrBits_valid d.collection)
    (by rw [addrBits_size]; exact Data.extract_collection d hp rfl)
    (by rw [addrBits_size]; show p + 267 ≤ d.encode.bits.size; rw [Data.encode_bits_size]; omega)
  rw [h, addrBits_size]; rfl

/-- The address `LDMSGADDR` pushes for the collection. -/
theorem Data.prefix_collection (d : Data) {p q r r' : Nat} (hp : p = 64) (hq : q = p + 267) (hr : r' = r) :
    Slice.prefixCell ⟨d.encode, p, r⟩ ⟨d.encode, q, r'⟩ = Cell.mkOrdinary (addrBits d.collection) #[] := by
  subst hr
  unfold Slice.prefixCell
  change Cell.mkOrdinary (d.bits.extract p q) (d.encode.refs.extract _ _) = _
  rw [Data.extract_collection d hp hq, Array.extract_eq_empty_of_le (Nat.min_le_left _ _)]

/-- The data is `encode` with the index `index` and the collection `collection`, within their widths. -/
def Inv (index collection : Nat) (data : Option Cell) : Prop :=
  ∃ d : Data, data = some d.encode ∧ d.index < 2 ^ 64 ∧ d.collection < 2 ^ 256 ∧ d.index = index ∧
    d.collection = collection

-- the data as the cell the code writes, for the ends of the paths: `encode` written out
attribute [check_close] Data.encode Data.bits addrBits
