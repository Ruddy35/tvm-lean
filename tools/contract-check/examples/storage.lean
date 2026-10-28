-- TON Storage (storage/storage-daemon/smartcont/storage-contract.fc with constants.fc, the code of
-- storage-contract-code.boc). The data is `storage#_ active:Bool balance:Coins provider:MsgAddress
-- merkle_hash:uint256 file_size:uint64 next_proof_byte:uint64 rate_per_mb_day:Coins max_span:uint32
-- last_proof_time:uint32 ^[client:MsgAddress torrent_hash:uint256]` (`Contracts.Storage.Data`,
-- TvmLean/Proofs/Contracts/StorageData.lean, with the reads of its layout,
-- TvmLean/Proofs/Contracts/StorageRun/Read.lean). Invariant: the data is such a cell, within its
-- widths, whose provider, Merkle root, file size, rate, longest span paid, client and torrent hash are
-- those of `d0`, and active if `d0` is: the contract never changes them (nor its code), and once
-- active it stays active.
import TvmLean.Proofs.Contracts.StorageRun.Read
-- contract-check: invariant Stored d0
-- contract-check: params (d0 : Contracts.Storage.Data)
-- contract-check: hints Contracts.Storage.Data.WF, Spec.loadIntValue, Contracts.Storage.Data.encode_bits_size, Contracts.Storage.Data.encode_refs_size, Contracts.Storage.Data.encode_ref0, Contracts.Storage.Data.clientCell_bits_size, Contracts.Storage.Data.clientCell_refs_size, Contracts.Storage.Data.read_flag, Contracts.Storage.Data.read_balanceLen, Contracts.Storage.Data.read_balance, Contracts.Storage.Data.skip_provider, Contracts.Storage.Data.prefix_provider, Contracts.Storage.Data.read_merkleHash, Contracts.Storage.Data.read_fileSize, Contracts.Storage.Data.read_nextProof, Contracts.Storage.Data.read_rateLen, Contracts.Storage.Data.read_rate, Contracts.Storage.Data.read_maxSpan, Contracts.Storage.Data.read_lastProofTime, Contracts.Storage.Data.rest_afterBalance, Contracts.Storage.Data.rest_afterProvider, Contracts.Storage.Data.skip_client, Contracts.Storage.Data.prefix_client, Contracts.Storage.Data.read_torrentHash, Contracts.Storage.readBits_ofCell_all, Contracts.Storage.toCellRemaining_ofCell_mkOrdinary, Contracts.Storage.bitsToIntSignedTwos_flag, Contracts.Storage.twosBits_flag, Contracts.Storage.twosBits_true, Contracts.Storage.flag_fits257

open TvmLean.Contracts

/-- The data of the storage contract with the fields of `d0` it never changes: `encode d` of a `d`
within its widths, with the provider, Merkle root, file size, rate, longest span paid, client and
torrent hash of `d0`, active if `d0` is. -/
def Stored (d0 : Storage.Data) (data : Option Cell) : Prop :=
  ∃ d : Storage.Data, data = some d.encode ∧ d.WF ∧ d.provider = d0.provider ∧
    d.merkleHash = d0.merkleHash ∧ d.fileSize = d0.fileSize ∧ d.ratePerMbDay = d0.ratePerMbDay ∧
    d.maxSpan = d0.maxSpan ∧ d.client = d0.client ∧ d.torrentHash = d0.torrentHash ∧
    (d0.active = true → d.active = true)

-- the data as the cell the code writes, for the ends of the paths: `encode` written out
attribute [check_close] Storage.Data.encode Storage.Data.bits Storage.coinsBits Storage.coinsLen
  Storage.Data.clientCell
