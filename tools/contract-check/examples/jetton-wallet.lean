-- The jetton wallet (TEP-74) of ton-blockchain/token-contract (ft/jetton-wallet.fc;
-- tools/txoracle/contracts.txt#jetton.wallet.code; the one minter.ton.org deploys is
-- jetton1.wallet.code): the data is `balance:Coins owner_address:MsgAddress
-- jetton_master_address:MsgAddress jetton_wallet_code:^Cell`. Invariant: the data is such a cell
-- with the owner 0:`owner`, the master 0:`master` and the wallet code `wcode`; the balance is a
-- `Coins` amount (a natural number below 2^120) stored as `store_coins` stores it (`coinsBits`, the
-- shortest length): whatever messages arrive, the owner, the master and the code in the data never
-- change and the balance never becomes negative (and the code of the account never changes). The
-- reads of the layout (`LDGRAMS`, `LDMSGADDR`, `LDREF`) are rewrites of the hints, as those of TON
-- Storage (TvmLean/Proofs/Contracts/StorageRun/Read.lean, whose generic lemmas they use).
import TvmLean.Proofs.Contracts.StorageRun.Read
-- contract-check: invariant Inv owner master wcode
-- contract-check: params (owner master : Nat) (wcode : Cell)
-- contract-check: hints Data.read_len0, Data.read_len, Data.read_balance, Data.skip_owner, Data.prefix_owner, Data.skip_master, Data.prefix_master, Data.encode_bits_size, Data.encode_refs_size, Data.encode_ref0, Contracts.Storage.toCellRemaining_ofCell_mkOrdinary, Contracts.Storage.readBits_ofCell_all

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

structure Data where
  balance : Nat
  owner : Nat
  master : Nat
  walletCode : Cell

def Data.bits (d : Data) : BitString := coinsBits d.balance ++ addrBits d.owner ++ addrBits d.master

def Data.encode (d : Data) : Cell := Cell.mkOrdinary d.bits #[d.walletCode]

theorem Data.bits_size (d : Data) : d.bits.size = 4 + coinsLen d.balance * 8 + 534 := by
  simp only [Data.bits, Array.size_append, coinsBits_size, addrBits_size]

theorem Data.encode_bits_size (d : Data) : d.encode.bits.size = 4 + coinsLen d.balance * 8 + 534 :=
  Data.bits_size d
theorem Data.encode_refs_size (d : Data) : d.encode.refs.size = 1 := rfl
theorem Data.encode_ref0 (d : Data) : d.encode.refs[0]! = d.walletCode := rfl

theorem Data.readBits_encode (d : Data) (p r n : Nat) :
    Slice.readBits ⟨d.encode, p, r⟩ n = d.bits.extract p (p + n) := rfl

theorem Data.read_len (d : Data) (h : coinsLen d.balance < 16) {p r n : Nat} (hp : p = 0) (hn : n = 4) :
    bitsToNat (Slice.readBits ⟨d.encode, p, r⟩ n) = coinsLen d.balance := by
  subst hp hn
  rw [Data.readBits_encode]
  have : d.bits.extract 0 (0 + 4) = natToBits (coinsLen d.balance) 4 := by
    rw [show d.bits = #[] ++ natToBits (coinsLen d.balance) 4 ++
        (natToBits d.balance (coinsLen d.balance * 8) ++ addrBits d.owner ++ addrBits d.master) by
      simp [Data.bits, coinsBits, Array.append_assoc]]
    exact extract_mid (by rfl) (by simp)
  rw [this]
  exact bitsToNat_coinsLen h

theorem Data.read_balance (d : Data) {p r n : Nat} (hp : p = 4) (hn : n = coinsLen d.balance * 8) :
    bitsToNat (Slice.readBits ⟨d.encode, p, r⟩ n) = d.balance := by
  subst hp hn
  rw [Data.readBits_encode]
  have : d.bits.extract 4 (4 + coinsLen d.balance * 8) = natToBits d.balance (coinsLen d.balance * 8) := by
    rw [show d.bits = natToBits (coinsLen d.balance) 4 ++ natToBits d.balance (coinsLen d.balance * 8) ++
        (addrBits d.owner ++ addrBits d.master) by simp [Data.bits, coinsBits, Array.append_assoc]]
    exact extract_mid (by simp) (by simp)
  rw [this]
  exact bitsToNat_coins _

theorem Data.extract_owner (d : Data) {p q : Nat} (hp : p = 4 + coinsLen d.balance * 8) (hq : q = p + 267) :
    d.bits.extract p q = addrBits d.owner := by
  rw [show d.bits = coinsBits d.balance ++ addrBits d.owner ++ addrBits d.master from rfl]
  exact extract_mid (by simp [coinsBits_size, hp]) (by simp [coinsBits_size, addrBits_size, hp, hq])

theorem Data.extract_master (d : Data) {p q : Nat} (hp : p = 4 + coinsLen d.balance * 8 + 267) (hq : q = p + 267) :
    d.bits.extract p q = addrBits d.master := by
  rw [show d.bits = (coinsBits d.balance ++ addrBits d.owner) ++ addrBits d.master ++ #[] by simp [Data.bits]]
  exact extract_mid (by simp [coinsBits_size, addrBits_size, hp])
    (by simp [coinsBits_size, addrBits_size, hp, hq])

theorem Data.skip_owner (d : Data) {p r : Nat} (gv : Nat) (hp : p = 4 + coinsLen d.balance * 8) :
    Slice.skipMessageAddr ⟨d.encode, p, r⟩ gv = .ok ⟨d.encode, p + 267, r⟩ := by
  have h := skipMessageAddr_of_valid (s := ⟨d.encode, p, r⟩) gv (addrBits_valid d.owner)
    (by rw [addrBits_size]; exact Data.extract_owner d hp rfl)
    (by rw [addrBits_size]; show p + 267 ≤ d.bits.size; rw [Data.bits_size]; omega)
  rw [h, addrBits_size]; rfl

theorem Data.skip_master (d : Data) {p r : Nat} (gv : Nat) (hp : p = 4 + coinsLen d.balance * 8 + 267) :
    Slice.skipMessageAddr ⟨d.encode, p, r⟩ gv = .ok ⟨d.encode, p + 267, r⟩ := by
  have h := skipMessageAddr_of_valid (s := ⟨d.encode, p, r⟩) gv (addrBits_valid d.master)
    (by rw [addrBits_size]; exact Data.extract_master d hp rfl)
    (by rw [addrBits_size]; show p + 267 ≤ d.bits.size; rw [Data.bits_size]; omega)
  rw [h, addrBits_size]; rfl

theorem Data.prefix_owner (d : Data) {p q r r' : Nat} (hp : p = 4 + coinsLen d.balance * 8) (hq : q = p + 267)
    (hr : r' = r) : Slice.prefixCell ⟨d.encode, p, r⟩ ⟨d.encode, q, r'⟩ = Cell.mkOrdinary (addrBits d.owner) #[] := by
  subst hr
  unfold Slice.prefixCell
  change Cell.mkOrdinary (d.bits.extract p q) (d.encode.refs.extract _ _) = _
  rw [Data.extract_owner d hp hq, Array.extract_eq_empty_of_le (Nat.min_le_left _ _)]

theorem Data.prefix_master (d : Data) {p q r r' : Nat} (hp : p = 4 + coinsLen d.balance * 8 + 267) (hq : q = p + 267)
    (hr : r' = r) : Slice.prefixCell ⟨d.encode, p, r⟩ ⟨d.encode, q, r'⟩ = Cell.mkOrdinary (addrBits d.master) #[] := by
  subst hr
  unfold Slice.prefixCell
  change Cell.mkOrdinary (d.bits.extract p q) (d.encode.refs.extract _ _) = _
  rw [Data.extract_master d hp hq, Array.extract_eq_empty_of_le (Nat.min_le_left _ _)]

/-- The first read of the data (`LDGRAMS` on `Slice.ofCell`): the length of the balance. -/
theorem Data.read_len0 (d : Data) (h : coinsLen d.balance < 16) :
    bitsToNat (Slice.readBits (Slice.ofCell d.encode) 4) = coinsLen d.balance :=
  Data.read_len d h (p := 0) (r := 0) rfl rfl

/-- The data is `encode` of a balance below 2^120 (`Coins`, as `store_coins` stores it) and the
addresses in the workchain 0, with the owner `owner`, the master `master` and the wallet code
`wcode`. -/
def Inv (owner master : Nat) (wcode : Cell) (data : Option Cell) : Prop :=
  ∃ d : Data, data = some d.encode ∧ coinsLen d.balance < 16 ∧ d.owner < 2 ^ 256 ∧ d.master < 2 ^ 256 ∧
    d.owner = owner ∧ d.master = master ∧ d.walletCode = wcode

-- the data as the cell the code writes, for the ends of the paths: `encode` written out
attribute [check_close] Data.encode Data.bits addrBits coinsBits coinsLen
