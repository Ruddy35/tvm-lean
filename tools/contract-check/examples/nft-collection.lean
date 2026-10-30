-- The NFT collection (TEP-62, TEP-66) of ton-blockchain/token-contract (nft/nft-collection.fc;
-- tools/txoracle/contracts.txt#nft.collection.code): the data is `owner_address:MsgAddress
-- next_item_index:uint64 ^[collection_content common_content] nft_item_code:^Cell
-- royalty_params:^RoyaltyParams`. Invariant: the data is such a cell with the content `content`, the
-- item code `icode` and the royalty parameters `royalty`: whatever messages arrive, the code of the
-- items the collection deploys and computes the addresses of never changes, nor do the content and
-- the royalty parameters, nor the code of the account. The owner is any bits the code wrote before
-- the index (an address `LDMSGADDR` read from a message, `change_owner`); the index is any 64 bits,
-- kept as bits (`indexBits`), not as `natToBits` of a number: the address is read first, and the
-- unifier, deciding the bounds of that read on bits ending in `natToBits`, would unfold the
-- conversion. The reads of the references are rewrites of the hints; the slice after the owner is
-- the data cell moved forward (`check_skip_shape`, TvmLean/Proofs/Check/MsgAddr.lean).
import TvmLean.Proofs.Contracts.StorageRun.Read
-- contract-check: invariant Inv content icode royalty
-- contract-check: params (content icode royalty : Cell)
-- contract-check: hints Data.encode_bits_size, Data.encode_refs_size, Data.encode_ref0, Data.encode_ref1, Data.encode_ref2, Contracts.Storage.toCellRemaining_ofCell_mkOrdinary, Contracts.Storage.readBits_ofCell_all

open TvmLean.Contracts TvmLean.Contracts.Storage

structure Data where
  owner : BitString
  indexBits : BitString
  content : Cell
  itemCode : Cell
  royalty : Cell

def Data.bits (d : Data) : BitString := d.owner ++ d.indexBits

def Data.encode (d : Data) : Cell := Cell.mkOrdinary d.bits #[d.content, d.itemCode, d.royalty]

theorem Data.encode_bits_size (d : Data) : d.encode.bits.size = d.owner.size + d.indexBits.size := by
  show d.bits.size = _
  simp only [Data.bits, Array.size_append]
theorem Data.encode_refs_size (d : Data) : d.encode.refs.size = 3 := rfl
theorem Data.encode_ref0 (d : Data) : d.encode.refs[0]! = d.content := rfl
theorem Data.encode_ref1 (d : Data) : d.encode.refs[1]! = d.itemCode := rfl
theorem Data.encode_ref2 (d : Data) : d.encode.refs[2]! = d.royalty := rfl

/-- The data is `encode` of an index of 64 bits with the content `content`, the item code `icode`
and the royalty parameters `royalty` (not named `code`: the code of the contract is `code`). -/
def Inv (content icode royalty : Cell) (data : Option Cell) : Prop :=
  ∃ d : Data, data = some d.encode ∧ d.indexBits.size = 64 ∧ d.content = content ∧ d.itemCode = icode ∧
    d.royalty = royalty

-- the data as the cell the code writes, for the ends of the paths: `encode` written out
attribute [check_close] Data.encode Data.bits
