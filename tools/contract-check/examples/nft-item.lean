-- The NFT item (TEP-62) of ton-blockchain/token-contract (nft/nft-item.fc;
-- tools/txoracle/contracts.txt#nft.item.code, the one most used on the mainnet; nft2.item.code is the
-- repository's head): the data is `index:uint64 collection_address:MsgAddress`, then, once the
-- collection initialized the item, `owner_address:MsgAddress content:^Cell`. Invariant: the data
-- starts with the index `index` and the collection 0:`collection`, whatever follows: whatever
-- messages arrive, the index and the collection never change (and the code never changes).
-- contract-check: invariant Inv index collection
-- contract-check: params (index collection : Nat)
-- contract-check: hints Data.encode, addrBits

/-- `addr_std$10 anycast:nothing$0 workchain_id:int8 address:bits256` in the workchain 0. -/
def addrBits (h : Nat) : BitString := #[true, false, false] ++ natToBits 0 8 ++ natToBits h 256

/-- The fields of the data: the index, the collection, and the rest (the owner and the content once
initialized, nothing before). -/
structure Data where
  index : Nat
  collection : Nat
  rest : BitString
  restRefs : Array Cell

/-- The data cell. -/
def Data.encode (d : Data) : Cell :=
  Cell.mkOrdinary (natToBits d.index 64 ++ addrBits d.collection ++ d.rest) d.restRefs

/-- The data is `encode` with the index `index` and the collection `collection`, within their widths. -/
def Inv (index collection : Nat) (data : Option Cell) : Prop :=
  ∃ d : Data, data = some d.encode ∧ d.index < 2 ^ 64 ∧ d.collection < 2 ^ 256 ∧ d.index = index ∧
    d.collection = collection
