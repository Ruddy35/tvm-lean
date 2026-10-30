-- The jetton minter (TEP-74, TEP-89) of ton-blockchain/token-contract
-- (ft/jetton-minter-discoverable.fc; tools/txoracle/contracts.txt#jetton.minter.code): the data is
-- `total_supply:Coins admin_address:MsgAddress content:^Cell jetton_wallet_code:^Cell`. Invariant:
-- the data is such a cell, the supply a `Coins` amount (a natural number below 2^120) stored as
-- `store_coins` stores it (`coinsBits`, the shortest length), and the wallet code `wcode`: whatever
-- messages arrive, the code of the jetton wallets the minter mints for and computes the addresses of
-- never changes, nor does the code of the account; the supply never becomes negative. The admin
-- address is any bits the code wrote after the supply (an address `LDMSGADDR` read from a message);
-- the content is any cell (`change_content` replaces it). The reads of the layout (`LDGRAMS`,
-- `LDREF`) are rewrites of the hints, as those of TON Storage
-- (TvmLean/Proofs/Contracts/StorageRun/Read.lean, whose generic lemmas they use); the slice after
-- the admin address is the data cell moved forward (`check_skip_shape`,
-- TvmLean/Proofs/Check/MsgAddr.lean).
import TvmLean.Proofs.Contracts.StorageRun.Read
-- contract-check: invariant Inv wcode
-- contract-check: params (wcode : Cell)
-- contract-check: hints Data.read_len0, Data.read_len, Data.read_supply, Data.encode_bits_size, Data.encode_refs_size, Data.encode_ref0, Data.encode_ref1, Contracts.Storage.toCellRemaining_ofCell_mkOrdinary, Contracts.Storage.readBits_ofCell_all

open TvmLean.Contracts TvmLean.Contracts.Storage

structure Data where
  supply : Nat
  admin : BitString
  content : Cell
  walletCode : Cell

def Data.bits (d : Data) : BitString := coinsBits d.supply ++ d.admin

def Data.encode (d : Data) : Cell := Cell.mkOrdinary d.bits #[d.content, d.walletCode]

theorem Data.bits_size (d : Data) : d.bits.size = 4 + coinsLen d.supply * 8 + d.admin.size := by
  simp only [Data.bits, Array.size_append, coinsBits_size]

theorem Data.encode_bits_size (d : Data) : d.encode.bits.size = 4 + coinsLen d.supply * 8 + d.admin.size :=
  Data.bits_size d
theorem Data.encode_refs_size (d : Data) : d.encode.refs.size = 2 := rfl
theorem Data.encode_ref0 (d : Data) : d.encode.refs[0]! = d.content := rfl
theorem Data.encode_ref1 (d : Data) : d.encode.refs[1]! = d.walletCode := rfl

theorem Data.readBits_encode (d : Data) (p r n : Nat) :
    Slice.readBits ⟨d.encode, p, r⟩ n = d.bits.extract p (p + n) := rfl

/-- The length of the supply (`LDGRAMS`, its first 4 bits). -/
theorem Data.read_len (d : Data) (h : coinsLen d.supply < 16) {p r n : Nat} (hp : p = 0) (hn : n = 4) :
    bitsToNat (Slice.readBits ⟨d.encode, p, r⟩ n) = coinsLen d.supply := by
  subst hp hn
  rw [Data.readBits_encode]
  have : d.bits.extract 0 (0 + 4) = natToBits (coinsLen d.supply) 4 := by
    rw [show d.bits = #[] ++ natToBits (coinsLen d.supply) 4 ++
        (natToBits d.supply (coinsLen d.supply * 8) ++ d.admin) by
      simp [Data.bits, coinsBits, Array.append_assoc]]
    exact extract_mid (by rfl) (by simp)
  rw [this]
  exact bitsToNat_coinsLen h

/-- The supply (`LDGRAMS`, the amount after its length). -/
theorem Data.read_supply (d : Data) {p r n : Nat} (hp : p = 4) (hn : n = coinsLen d.supply * 8) :
    bitsToNat (Slice.readBits ⟨d.encode, p, r⟩ n) = d.supply := by
  subst hp hn
  rw [Data.readBits_encode]
  have : d.bits.extract 4 (4 + coinsLen d.supply * 8) = natToBits d.supply (coinsLen d.supply * 8) := by
    rw [show d.bits = natToBits (coinsLen d.supply) 4 ++ natToBits d.supply (coinsLen d.supply * 8) ++ d.admin by
      simp [Data.bits, coinsBits, Array.append_assoc]]
    exact extract_mid (by simp) (by simp)
  rw [this]
  exact bitsToNat_coins _

/-- The first read of the data (`LDGRAMS` on `Slice.ofCell`): the length of the supply. -/
theorem Data.read_len0 (d : Data) (h : coinsLen d.supply < 16) :
    bitsToNat (Slice.readBits (Slice.ofCell d.encode) 4) = coinsLen d.supply :=
  Data.read_len d h (p := 0) (r := 0) rfl rfl

/-- The data is `encode` of a supply below 2^120 (`Coins`, as `store_coins` stores it) with the
wallet code `wcode`. -/
def Inv (wcode : Cell) (data : Option Cell) : Prop :=
  ∃ d : Data, data = some d.encode ∧ coinsLen d.supply < 16 ∧ d.walletCode = wcode

-- the data as the cell the code writes, for the ends of the paths: `encode` written out
attribute [check_close] Data.encode Data.bits coinsBits coinsLen
