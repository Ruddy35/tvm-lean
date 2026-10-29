-- The jetton wallet (TEP-74) of ton-blockchain/token-contract (ft/jetton-wallet.fc;
-- tools/txoracle/contracts.txt#jetton.wallet.code; the one minter.ton.org deploys is
-- jetton1.wallet.code): the data is `balance:Coins owner_address:MsgAddress
-- jetton_master_address:MsgAddress jetton_wallet_code:^Cell`. Invariant: the data is such a cell
-- with the owner 0:`owner`, the master 0:`master` and the wallet code `wcode`; the balance is a
-- `Coins` amount (a natural number below 2^120): whatever messages arrive, the owner, the master and
-- the code in the data never change and the balance never becomes negative (and the code of the
-- account never changes).
-- contract-check: invariant Inv owner master wcode
-- contract-check: params (owner master : Nat) (wcode : Cell)
-- contract-check: hints Data.encode, addrBits

/-- `addr_std$10 anycast:nothing$0 workchain_id:int8 address:bits256` in the workchain 0. -/
def addrBits (h : Nat) : BitString := #[true, false, false] ++ natToBits 0 8 ++ natToBits h 256

/-- The fields of the data; the balance as `VarUInteger 16`: its length in bytes `len`, then
`8 * len` bits. -/
structure Data where
  len : Nat
  balance : Nat
  owner : Nat
  master : Nat
  walletCode : Cell

/-- The data cell. -/
def Data.encode (d : Data) : Cell :=
  Cell.mkOrdinary (natToBits d.len 4 ++ natToBits d.balance (8 * d.len) ++ addrBits d.owner ++ addrBits d.master)
    #[d.walletCode]

/-- The data is `encode` of fields within their widths, with the owner `owner`, the master `master`
and the wallet code `wcode`. -/
def Inv (owner master : Nat) (wcode : Cell) (data : Option Cell) : Prop :=
  ∃ d : Data, data = some d.encode ∧ d.len < 16 ∧ d.balance < 2 ^ (8 * d.len) ∧ d.owner < 2 ^ 256 ∧
    d.master < 2 ^ 256 ∧ d.owner = owner ∧ d.master = master ∧ d.walletCode = wcode
