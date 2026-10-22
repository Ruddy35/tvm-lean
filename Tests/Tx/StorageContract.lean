import Tests.Tx.Gen

/-!
# Transactions of the storage contract of TON Storage

The contract a storage provider deploys for each of its clients
(`storage/storage-daemon/smartcont/storage-contract.fc`, its constants in `constants.fc`), its code
`storage.code` of `tools/txoracle/contracts.txt`: `contracts.fif` assembles `storage-contract.fif`,
which `func -SPA` made from it, and checks that it is `storage-contract-code.boc`. Its data,

    storage#_ active:Bool balance:Coins provider:MsgAddress merkle_hash:uint256 file_size:uint64
      next_proof_byte:uint64 rate_per_mb_day:Coins max_span:uint32 last_proof_time:uint32
      ^[client:MsgAddress torrent_hash:uint256] = Storage;

and the messages are made here. A proof of storage is a Merkle proof (exotic cell of type 3) of the
file's microchunk tree as `storage/MicrochunkTree.cpp` builds it: a leaf `00` with the 64 bytes of a
microchunk, a node `00` with two references, so that the tree reads as a dictionary whose keys are
the microchunk numbers; the proof keeps the path to one microchunk and prunes the other subtrees
(pruned branches of level 1, `prun`), as `GetMicrochunkProof::get_proof` does for
`[next_proof_byte / 64 * 64, +64)`. The contract (`check_proof`) reads the proof with `XCTOS`,
compares its stored hash with `merkle_hash` and looks up `next_proof_byte / 64` in the tree with
`key_len` bits, the least with `64 << key_len >= file_size`.

The cases (`cases`, on every version): top-ups (an empty body, operation 0, a balance that overflows
`Coins`), `deploy_storage_contract` (also deploying the contract with its `StateInit` to an absent and
an uninitialized account; a value below the two receipts), `accept_storage_contract` by the provider,
the client or another account and on an active contract, `close_contract` by the client, the
provider or another account in both states, `withdraw` (with a zero balance, an account short of the
reserve); `proof_storage` with valid proofs for files from 0 bytes to 2^64 - 1 (key lengths 0 to 58)
and microchunks at the start, middle and end, a proof of a whole tree (nothing pruned), at times
before, at and after `max_span` and before `last_proof_time`, with rates and balances that make the
bounty 0, all of the balance or overflow `Coins`; invalid proofs: of another file, an ordinary cell,
a pruned branch, a library cell and a Merkle update instead of a Merkle proof, a Merkle proof of a
pruned root, a tree without the key, the key in a pruned subtree or out of the key range, trees
shallower or deeper than `key_len`, no proof; from another account, on an inactive contract; small
values (out of gas); bounced messages, an unknown operation, short bodies, external messages (the
contract has no `recv_external`: exit code 11); providers and clients at addresses of other kinds
(`addr_var`, the masterchain, `addr_none`). A message whose body references a pruned branch (or an
ordinary cell over a pruned tree) has level 1: the emulator refuses it as a bag of cells.
`randomCases`: random internal messages (operations, senders, fields, values, proofs, block seeds) to
random states, from a fixed seed, each at its own version.
-/

namespace Tests.Tx

open TvmLean TvmLean.Tx

namespace StorageContract

def caseNow : Nat := 1700000200

def providerA : BitString := natToBits 0x2222222222222222222222222222222222222222222222222222222222222222 256
def clientA : BitString := natToBits 0x4444444444444444444444444444444444444444444444444444444444444444 256
def strangerA : BitString := natToBits 0x6666666666666666666666666666666666666666666666666666666666666666 256
/-- the contract's address (cases without a `StateInit`) -/
def contractA : BitString := natToBits 0x5555555555555555555555555555555555555555555555555555555555555555 256

/-- `addr_std` bits. -/
def stdAddr (wc : Int) (a : BitString) : BitString := (Account.mkAddr wc none a).bits
/-- `addr_var` bits with the same workchain and address. -/
def varAddr (wc : Int) (a : BitString) : BitString :=
  (((((({} : W).uint 3 2).bool false).uint a.size 9).int wc 32).bitStr a).bits
/-- `addr_none`. -/
def noneAddr : BitString := #[false, false]

/-! ## Microchunk trees and proofs -/

def chunkSize : Nat := 64
/-- The bytes of a file after the first `contentBytes` are zeros, so that the trees of large files
have few distinct subtrees. -/
def contentBytes : Nat := 4096

/-- `key_len` of `check_proof`: the least `k` with `CHUNK_SIZE << k >= file_size` (the height of the
microchunk tree, `MicrochunkTree::Builder`: `total_size` doubled from 64 while below the size). -/
def keyLen (fileSize : Nat) : Nat :=
  ((List.range 64).find? fun k => fileSize ≤ chunkSize <<< k).getD 64

/-- The byte `j` of a file of `size` bytes (`salt` tells files apart); zeros after the file (the
last microchunk and the tree padded as `MicrochunkTree::Builder::finalize` does). -/
def fileByte (salt size j : Nat) : UInt8 :=
  if j < Nat.min size contentBytes then UInt8.ofNat ((j * 151 + 17 + salt * 59) % 256) else 0

/-- The leaf of microchunk `i`: `00` and its 64 bytes. -/
def leaf (salt size i : Nat) : Cell :=
  Cell.mkOrdinary (#[false, false] ++ bytesToBits ((List.range chunkSize).toArray.map fun t =>
    fileByte salt size (i * chunkSize + t)))

/-- The hash of a node `00` whose two references have depth `d` and hashes `l`, `r`: the
representation hash of an ordinary cell of level 0 (descriptors 2 and 1, the data byte 0x20, the
depths, the hashes). -/
def nodeHash (l r : Array UInt8) (d : Nat) : Array UInt8 :=
  let dd : Array UInt8 := #[UInt8.ofNat (d >>> 8), UInt8.ofNat (d &&& 0xff)]
  sha256Digest (#[2, 1, 0x20] ++ dd ++ dd ++ l ++ r)

/-- The hashes of the subtrees of zero microchunks of heights 0 to 60. -/
def zeroHashes : Array (Array UInt8) := Id.run do
  let mut hs := #[(leaf 0 0 0).hashBytes]
  for h in [0:60] do
    hs := hs.push (nodeHash hs[h]! hs[h]! h)
  return hs

/-- The hash of the subtree of height `h` over the microchunks from `i * 2^h` (its depth is `h`). -/
def subtreeHash (salt size : Nat) : Nat → Nat → Array UInt8
  | 0, i => if i * chunkSize ≥ Nat.min size contentBytes then zeroHashes[0]! else (leaf salt size i).hashBytes
  | h + 1, i =>
      if i * (chunkSize <<< (h + 1)) ≥ Nat.min size contentBytes then zeroHashes[h + 1]!
      else nodeHash (subtreeHash salt size h (2 * i)) (subtreeHash salt size h (2 * i + 1)) h

/-- A pruned branch of level 1 (exotic, type 1) of a cell with hash `hash` and depth `d` at level 0
(`prun` of `MicrochunkTree.cpp`). -/
def pruned (hash : Array UInt8) (d : Nat) : Cell :=
  { bits := natToBits 1 8 ++ natToBits 1 8 ++ bytesToBits hash ++ natToBits d 16, refs := #[], special := true,
    levelMask := 1 }

def node (l r : Cell) : Cell := Cell.mkOrdinary #[false, false] #[l, r]

/-- The tree of height `h` over the microchunks from `i * 2^h` with only the path to microchunk `k`:
the other subtrees pruned. -/
def proofPath (salt size k : Nat) : Nat → Nat → Cell
  | 0, i => leaf salt size i
  | h + 1, i =>
      if (k >>> h) % 2 == 0 then node (proofPath salt size k h (2 * i)) (pruned (subtreeHash salt size h (2 * i + 1)) h)
      else node (pruned (subtreeHash salt size h (2 * i)) h) (proofPath salt size k h (2 * i + 1))

/-- The whole tree of height `h` over the microchunks from `i * 2^h` (for small trees). -/
def fullTree (salt size : Nat) : Nat → Nat → Cell
  | 0, i => leaf salt size i
  | h + 1, i => node (fullTree salt size h (2 * i)) (fullTree salt size h (2 * i + 1))

/-- A Merkle proof (exotic, type 3) of `child`, a tree whose hash and depth at level 0 are `hash`
and `d` (`CellBuilder::create_merkle_proof`). -/
def merkleProof (hash : Array UInt8) (d : Nat) (child : Cell) : Cell :=
  { bits := natToBits 3 8 ++ bytesToBits hash ++ natToBits d 16, refs := #[child], special := true,
    levelMask := child.levelMask >>> 1 }

/-- A Merkle update (exotic, type 4) from `a` to `b` (hashes and depths at level 0). -/
def merkleUpdate (ha : Array UInt8) (da : Nat) (a : Cell) (hb : Array UInt8) (db : Nat) (b : Cell) : Cell :=
  { bits := natToBits 4 8 ++ bytesToBits ha ++ bytesToBits hb ++ natToBits da 16 ++ natToBits db 16, refs := #[a, b],
    special := true, levelMask := (a.levelMask ||| b.levelMask) >>> 1 }

/-- A file: its size and salt. -/
structure File where
  size : Nat
  salt : Nat := 0

def File.height (f : File) : Nat := keyLen f.size
/-- `merkle_hash`: the hash of the microchunk tree. -/
def File.root (f : File) : Array UInt8 := subtreeHash f.salt f.size f.height 0
/-- The tree with the path to the microchunk of byte `b`. -/
def File.path (f : File) (b : Nat) : Cell := proofPath f.salt f.size (b / chunkSize) f.height 0
/-- The proof of the byte `b` (`MicrochunkTree::get_proof`). -/
def File.proof (f : File) (b : Nat) : Cell := merkleProof f.root f.height (f.path b)

/-- A dictionary of `n`-bit keys, each with a microchunk of zeros: a tree that is not a microchunk
tree (labels of more than 0 bits). -/
def sparseDict (n : Nat) (keys : List Nat) : Option Cell := Id.run do
  let mut root : Option Cell := none
  for k in keys do
    match dictSetBuilderWithCells root (natToBits k n) { bits := natToBits 0 512, refs := #[] } .set with
    | .ok (r, _, _, _) => root := r
    | .error _ => pure ()
  return root

/-- The level information of an exotic cell the cases send, as C++ `DataCell::create` checks it
(the stored hashes and depths of a Merkle proof or update are those of its references at level 0);
a case whose cell is not valid is an error of the cases. -/
def checkCell (what : String) (c : Cell) : Except String Unit :=
  match c.computeLevelInfo? with
  | .ok _ => pure ()
  | .error e => throw s!"storage: the {what} is not a valid cell: {e}"


/-! ## Data and messages -/

/-- The contract's data. -/
structure Data where
  active : Bool := true
  balance : Nat := 1000000000
  provider : BitString := stdAddr 0 providerA
  merkle : BitString
  fileSize : Nat
  nextProof : Nat := 0
  rate : Nat := 1000000
  maxSpan : Nat := 86400
  lastProof : Nat := caseNow - 3600
  client : BitString := stdAddr 0 clientA
  torrent : Nat := 0x7070707070707070707070707070707070707070707070707070707070707070
  /-- without the reference of the client and the torrent hash -/
  noClientRef : Bool := false

def Data.cell (d : Data) : Cell :=
  let inner := ((({} : W).bitStr d.client).uint d.torrent 256).cell
  let w := ((((((((({} : W).bool d.active).grams d.balance).bitStr d.provider).bitStr d.merkle).uint d.fileSize 64).uint
    d.nextProof 64).grams d.rate).uint d.maxSpan 32).uint d.lastProof 32
  (if d.noClientRef then w else w.ref inner).cell

/-- The data for the file `f` with the proof due at byte `b`. -/
def dataFor (f : File) (b : Nat) : Data := { merkle := bytesToBits f.root, fileSize := f.size, nextProof := b }

def opDeploy : Nat := 0xe4748df1
def opAccept : Nat := 0x7a361688
def opClose : Nat := 0x79f937ea
def opWithdraw : Nat := 0x46ed2e94
def opProof : Nat := 0x419d5d4d

/-- `op query_id`. -/
def opq (op qid : Nat) : BitString := natToBits op 32 ++ natToBits qid 64

/-- An internal message to `dest` (the contract) from `(srcWc, src)`, the body inline with the
references `refs`. -/
def msg (src : BitString) (value : Nat) (body : BitString) (refs : Array Cell := #[]) (bounce : Bool := true)
    (bounced : Bool := false) (init : Option Cell := none) (dest : BitString := contractA) (srcWc : Int := 0) : Cell :=
  intMsg 0 dest value bounce init body (bodyRefs := refs) (src := (srcWc, src)) (bounced := bounced)

/-- The contract's account at `contractA` with the data `d` and `bal` nanograms. -/
def account (code : Cell) (d : Data) (bal : Nat) : Cell := mkAccount 0 contractA (.active code d.cell) bal 1700000000 0 1000

/-! ## The cases -/

/-- The cases of one version (`mk name account message` makes the case `storage/<name>`). -/
def cases (code : Cell) (mk : String → Cell → Cell → TxCase) : Except String (Array TxCase) := do
  let mut out : Array TxCase := #[]
  -- (name, data, account balance, message)
  let mut cs : Array (String × Data × Nat × Cell) := #[]
  let rich : Nat := 2000000000
  -- the file of 1 MiB (key_len 14), the proof due at byte 123456 (microchunk 1929)
  let f1 : File := { size := 1048576 }
  let d0 := dataFor f1 123456
  let p0 := f1.proof 123456
  checkCell "proof" p0
  let dIn := { d0 with active := false }
  -- top-ups: an empty body or operation 0 add the value to the balance
  cs := cs.push ("top-up/empty/active", d0, rich, msg providerA 1000000000 #[])
  cs := cs.push ("top-up/empty/inactive", dIn, rich, msg providerA 1000000000 #[])
  cs := cs.push ("top-up/empty/client", d0, rich, msg clientA 1000000000 #[])
  cs := cs.push ("top-up/empty/stranger", d0, rich, msg strangerA 1000000000 #[] (bounce := false))
  cs := cs.push ("top-up/op0", d0, rich, msg clientA 1000000000 (natToBits 0 32))
  cs := cs.push ("top-up/op0-comment", d0, rich, msg clientA 1000000000 (natToBits 0 32 ++ natToBits 0x73746f72616765 56))
  cs := cs.push ("top-up/op0-ref", dIn, rich, msg clientA 1000000000 (opq 0 5) #[Cell.empty])
  cs := cs.push ("top-up/large", { d0 with balance := 2 ^ 119 }, rich, msg clientA 1000000000 #[])
  -- the balance overflows Coins (STGRAMS: range check)
  cs := cs.push ("top-up/overflow", { d0 with balance := 2 ^ 120 - 1 - 500000000 }, rich, msg clientA 1000000000 #[])
  cs := cs.push ("top-up/overflow/no-bounce", { d0 with balance := 2 ^ 120 - 1 - 500000000 }, rich,
    msg clientA 1000000000 #[] (bounce := false))
  cs := cs.push ("top-up/zero-value", d0, rich, msg clientA 0 #[])
  cs := cs.push ("top-up/account-poor", d0, 1000, msg clientA 1000000000 #[])
  -- deploy_storage_contract: balance += value - 0.04 Gram, 0.02 Gram to the client (mode 0)
  cs := cs.push ("deploy/inactive", dIn, rich, msg providerA 100000000 (opq opDeploy 77))
  cs := cs.push ("deploy/active", d0, rich, msg providerA 100000000 (opq opDeploy 77))
  cs := cs.push ("deploy/stranger", dIn, rich, msg strangerA 100000000 (opq opDeploy 78))
  cs := cs.push ("deploy/low-value", { dIn with balance := 0 }, rich, msg providerA 30000000 (opq opDeploy 79))
  cs := cs.push ("deploy/low-value-funded", dIn, rich, msg providerA 30000000 (opq opDeploy 80))
  cs := cs.push ("deploy/client-none", { dIn with client := noneAddr }, rich, msg providerA 100000000 (opq opDeploy 81))
  cs := cs.push ("deploy/client-masterchain", { dIn with client := stdAddr (-1) clientA }, rich,
    msg providerA 100000000 (opq opDeploy 82))
  cs := cs.push ("deploy/no-client-ref", { dIn with noClientRef := true }, rich, msg providerA 100000000 (opq opDeploy 83))
  cs := cs.push ("deploy/bounced", dIn, rich, msg providerA 100000000 (opq opDeploy 84) (bounce := false) (bounced := true))
  -- accept_storage_contract: only the provider, only while inactive
  cs := cs.push ("accept/provider", dIn, rich, msg providerA 100000000 (opq opAccept 1))
  cs := cs.push ("accept/client", dIn, rich, msg clientA 100000000 (opq opAccept 2))
  cs := cs.push ("accept/stranger", dIn, rich, msg strangerA 100000000 (opq opAccept 3))
  cs := cs.push ("accept/active", d0, rich, msg providerA 100000000 (opq opAccept 4))
  cs := cs.push ("accept/provider-var", { dIn with provider := varAddr 0 providerA }, rich,
    msg providerA 100000000 (opq opAccept 5))
  cs := cs.push ("accept/provider-masterchain", { dIn with provider := stdAddr (-1) providerA }, rich,
    msg providerA 100000000 (opq opAccept 6))
  cs := cs.push ("accept/provider-masterchain/sender-masterchain", { dIn with provider := stdAddr (-1) providerA }, rich,
    msg providerA 100000000 (opq opAccept 7) (srcWc := -1))
  cs := cs.push ("accept/client-none", { dIn with client := noneAddr }, rich, msg providerA 100000000 (opq opAccept 8))
  -- close_contract: by the client or the provider; inactive: everything to the client (mode 128 + 32);
  -- active: the balance to the client (64), the rest to the provider (128 + 32)
  for (n, d) in [("active", d0), ("inactive", dIn)] do
    for (sn, s) in [("client", clientA), ("provider", providerA), ("stranger", strangerA)] do
      cs := cs.push (s!"close/{n}/{sn}", d, rich, msg s 100000000 (opq opClose 9))
  cs := cs.push ("close/active/client/balance-zero", { d0 with balance := 0 }, rich, msg clientA 100000000 (opq opClose 10))
  cs := cs.push ("close/active/client/balance-above-account", { d0 with balance := 5000000000 }, rich,
    msg clientA 100000000 (opq opClose 11))
  cs := cs.push ("close/inactive/client/balance-above-account", { dIn with balance := 5000000000 }, rich,
    msg clientA 100000000 (opq opClose 12))
  cs := cs.push ("close/active/provider/client-none", { d0 with client := noneAddr }, rich,
    msg providerA 100000000 (opq opClose 13))
  cs := cs.push ("close/active/client/client-masterchain", { d0 with client := stdAddr (-1) clientA }, rich,
    msg clientA 100000000 (opq opClose 14))
  -- withdraw: the provider takes all but balance + 0.01 Gram (RAWRESERVE mode 2; none for a zero balance)
  cs := cs.push ("withdraw/provider", d0, rich, msg providerA 100000000 (opq opWithdraw 15))
  cs := cs.push ("withdraw/provider/balance-zero", { d0 with balance := 0 }, rich, msg providerA 100000000 (opq opWithdraw 16))
  cs := cs.push ("withdraw/provider/account-short", d0, 500000000, msg providerA 100000000 (opq opWithdraw 17))
  cs := cs.push ("withdraw/provider/balance-huge", { d0 with balance := 2 ^ 100 }, rich,
    msg providerA 100000000 (opq opWithdraw 18))
  cs := cs.push ("withdraw/inactive", dIn, rich, msg providerA 100000000 (opq opWithdraw 19))
  cs := cs.push ("withdraw/stranger", d0, rich, msg strangerA 100000000 (opq opWithdraw 20))
  cs := cs.push ("withdraw/client", d0, rich, msg clientA 100000000 (opq opWithdraw 21))
  -- proof_storage, valid proofs: file sizes around the key lengths (0 .. 58), the proof due at the
  -- start, in the middle and at the end of the file
  let sizes : List (Nat × List Nat) :=
    [(0, [0]), (1, [0]), (64, [0, 63]), (65, [64]), (128, [127]), (129, [128]), (1000, [999]), (4096, [4095]),
     (4097, [4096]), (1048576, [0, 1048575]), (1048577, [1048576]), (1000000000, [999999999, 500000000]),
     (2 ^ 40, [2 ^ 40 - 1, 2 ^ 39 + 12345]), (2 ^ 64 - 1, [0, 2 ^ 64 - 2])]
  for (size, bytes) in sizes do
    let f : File := { size := size }
    for b in bytes do
      let p := f.proof b
      checkCell s!"proof of {size}/{b}" p
      cs := cs.push (s!"proof/size-{size}/byte-{b}", dataFor f b, rich, msg providerA 100000000 (opq opProof 22) #[p])
  cs := cs.push ("proof/valid", d0, rich, msg providerA 100000000 (opq opProof 23) #[p0])
  -- the whole tree of a file of 1000 bytes (16 microchunks, nothing pruned: the proof and the message of
  -- level 0)
  let fWhole : File := { size := 1000 }
  let pWhole := merkleProof fWhole.root fWhole.height (fullTree 0 1000 fWhole.height 0)
  checkCell "proof of the whole tree" pWhole
  let dWhole := dataFor fWhole 640
  cs := cs.push ("proof/whole-tree", dWhole, rich, msg providerA 100000000 (opq opProof 23) #[pWhole])
  -- the time since the last proof, capped at max_span: none, 1 s, max_span - 1, max_span, max_span + 1,
  -- since 0; the last proof in the future (a negative bounty: the balance grows, and overflows Coins)
  let times : List (String × Data) :=
    [("now", { d0 with lastProof := caseNow }), ("1s", { d0 with lastProof := caseNow - 1 }),
     ("span-1", { d0 with lastProof := caseNow - 86399 }), ("span", { d0 with lastProof := caseNow - 86400 }),
     ("span+1", { d0 with lastProof := caseNow - 86401 }), ("zero", { d0 with lastProof := 0 }),
     ("future", { d0 with lastProof := caseNow + 1000 }),
     ("future/overflow", { d0 with lastProof := caseNow + 1000, balance := 2 ^ 120 - 100 }),
     ("max-span-zero", { d0 with maxSpan := 0, lastProof := 0 }),
     ("max-span-max", { d0 with maxSpan := 2 ^ 32 - 1, lastProof := 0 }),
     ("max-span-max/future", { d0 with maxSpan := 2 ^ 32 - 1, lastProof := 2 ^ 32 - 1 })]
  for (n, d) in times do
    cs := cs.push (s!"proof/time/{n}", d, rich, msg providerA 100000000 (opq opProof 24) #[p0])
  -- the bounty: none, all of the balance, of the largest rate on the largest file
  let fMax : File := { size := 2 ^ 64 - 1 }
  let pMax := fMax.proof 0
  let dMax := dataFor fMax 0
  for (n, d, p) in [("rate-zero", { d0 with rate := 0 }, p0), ("rate-high", { d0 with rate := 10 ^ 15 }, p0),
      ("balance-zero", { d0 with balance := 0 }, p0), ("balance-max", { d0 with balance := 2 ^ 120 - 1 }, p0),
      ("rate-max", { dMax with rate := 2 ^ 120 - 1, lastProof := 0, maxSpan := 2 ^ 32 - 1 }, pMax),
      ("rate-max/future", { dMax with rate := 2 ^ 120 - 1, lastProof := 2 ^ 32 - 1, maxSpan := 2 ^ 32 - 1 }, pMax)] do
    cs := cs.push (s!"proof/bounty/{n}", d, rich, msg providerA 100000000 (opq opProof 25) #[p])
  -- invalid proofs
  let fOther : File := { size := 1048576, salt := 1 }
  let pOther := fOther.proof 123456
  let path0 := f1.path 123456
  let update := merkleUpdate f1.root f1.height path0 fOther.root fOther.height (fOther.path 123456)
  checkCell "Merkle update" update
  -- a dictionary of 14-bit keys without the key 1929
  let some sparse := sparseDict 14 [1928, 1930, 7] | throw "storage: the sparse dictionary"
  let sparseRoot ← match sparse.computeLevelInfo? with
    | .ok info => pure (info.getHash 0)
    | .error e => throw s!"storage: the sparse dictionary: {e}"
  let pSparse := merkleProof sparseRoot (sparse.depthAt 0) sparse
  checkCell "proof of the sparse dictionary" pSparse
  -- a tree of 64 KiB (height 10) for key_len 14: the path to microchunk 120 (the top 10 bits of 1929)
  -- ends in a leaf with 4 bits of the key left
  let fSmall : File := { size := 65536 }
  let pSmall := fSmall.proof (120 * 64)
  -- the tree of 1 MiB (height 14) for key_len 6 (a file of 4096 bytes, byte 576: key 9): the path to
  -- microchunk 9 << 8 (found: the node at depth 6) or to 9 (the key's path pruned at depth 3)
  let invalid : List (String × Data × Array Cell) :=
    [("other-file", d0, #[pOther]),
     ("hash-mismatch", { d0 with merkle := natToBits 0x1234 256 }, #[p0]),
     ("ordinary", d0, #[Cell.mkOrdinary p0.bits p0.refs]),
     ("ordinary/whole-tree", dWhole, #[Cell.mkOrdinary pWhole.bits pWhole.refs]),
     ("pruned", d0, #[pruned f1.root f1.height]),
     ("root-pruned", d0, #[merkleProof f1.root f1.height (pruned f1.root f1.height)]),
     ("library", d0, #[libraryCellOf path0]),
     ("update", d0, #[update]),
     ("key-missing", { d0 with merkle := bytesToBits sparseRoot }, #[pSparse]),
     ("key-pruned", d0, #[f1.proof 0]),
     ("key-out-of-range", { d0 with nextProof := 1048576 + 100 }, #[p0]),
     ("tree-shallower", { d0 with merkle := bytesToBits fSmall.root }, #[pSmall]),
     ("tree-deeper", { d0 with fileSize := 4096, nextProof := 576 }, #[f1.proof (9 * 256 * 64)]),
     ("tree-deeper/pruned", { d0 with fileSize := 4096, nextProof := 576 }, #[f1.proof 576]),
     ("no-proof", d0, #[])]
  for (n, d, refs) in invalid do
    cs := cs.push (s!"proof/invalid/{n}", d, rich, msg providerA 100000000 (opq opProof 26) refs)
  cs := cs.push ("proof/invalid/other-file/no-bounce", d0, rich, msg providerA 100000000 (opq opProof 27) #[pOther] (bounce := false))
  cs := cs.push ("proof/no-query-id", d0, rich, msg providerA 100000000 (natToBits opProof 32) #[p0])
  cs := cs.push ("proof/stranger", d0, rich, msg strangerA 100000000 (opq opProof 28) #[p0])
  cs := cs.push ("proof/client", d0, rich, msg clientA 100000000 (opq opProof 29) #[p0])
  cs := cs.push ("proof/inactive", dIn, rich, msg providerA 100000000 (opq opProof 30) #[p0])
  cs := cs.push ("proof/bounced", d0, rich, msg providerA 100000000 (opq opProof 31) #[p0] (bounce := false) (bounced := true))
  cs := cs.push ("proof/value-small", d0, rich, msg providerA 10000000 (opq opProof 32) #[p0])
  cs := cs.push ("proof/value-tiny", d0, rich, msg providerA 3000000 (opq opProof 33) #[p0])
  cs := cs.push ("proof/account-poor", d0, 1000, msg providerA 100000000 (opq opProof 34) #[p0])
  -- other bodies
  cs := cs.push ("unknown-op", d0, rich, msg providerA 100000000 (opq 0x12345678 35))
  cs := cs.push ("unknown-op/no-query-id", d0, rich, msg providerA 100000000 (natToBits 0x12345678 32))
  cs := cs.push ("short/16", d0, rich, msg providerA 100000000 (natToBits 0x419d 16))
  cs := cs.push ("short/query-id", d0, rich, msg providerA 100000000 (natToBits opClose 32 ++ natToBits 5 10))
  cs := cs.push ("bounced/empty", d0, rich, msg clientA 100000000 #[] (bounce := false) (bounced := true))
  cs := cs.push ("bounced/close", d0, rich, msg clientA 100000000 (opq opClose 36) (bounce := false) (bounced := true))
  -- external messages: no recv_external (exit code 11, not accepted)
  for (n, d) in [("active", d0), ("inactive", dIn)] do
    cs := cs.push (s!"external/{n}/empty", d, rich, extMsg 0 contractA none #[])
    cs := cs.push (s!"external/{n}/close", d, rich, extMsg 0 contractA none (opq opClose 37))
  for (n, d, bal, m) in cs do
    out := out.push (mk s!"storage/{n}" (account code d bal) m)
  -- deploying the contract: the provider's message with the StateInit, to an absent or uninitialized account
  let si := stateInit code (Data.cell { dIn with balance := 0 })
  let siAddr := bytesToBits si.hashBytes
  let deployMsg := msg providerA 100000000 (opq opDeploy 85) (init := some si) (dest := siAddr)
  out := out.push (mk "storage/deploy/state-init/none" (mkAccount 0 siAddr .none 0 0 0 0) deployMsg)
  out := out.push (mk "storage/deploy/state-init/uninit" (mkAccount 0 siAddr .uninit 50000000 1700000000 0 1000) deployMsg)
  return out

/-! ## Random messages -/

/-- A random case: the version, the state (active or not, balance, file, the byte due, rate, times,
the provider's and client's addresses of several kinds), the account's balance, the message (operation,
sender, query id, value, flags; for a proof: valid, of another microchunk or file, an ordinary cell, a
library cell, a pruned branch, none; truncated and random bodies), the block's seed. Most values pay
for the gas, most senders and stored providers are the provider, so that most proofs reach
`check_proof`. -/
def randomCase (code cfg0 : Cell) (i : Nat) (rng : StdGen) : Except String (TxCase × StdGen) := do
  let (v, rng) := randNat rng 0 16
  let (ak, rng) := randNat rng 0 3
  let active := ak != 0
  let (bk, rng) := randNat rng 0 4
  let (bal0, rng) := randAmount rng
  let (bal1, rng) := randNat rng 0 (2 ^ 120 - 1)
  let (bal2, rng) := randNat rng 0 100000
  let balance := if bk = 0 then 0 else if bk = 1 then bal1 else if bk = 2 then 2 ^ 120 - 1 - bal2 else bal0
  let (sk, rng) := randNat rng 0 4
  let (s0, rng) := randNat rng 0 5000
  let (s1, rng) := randNat rng 0 (2 ^ 24)
  let (e, rng) := randNat rng 0 64
  let (s2, rng) := randNat rng 0 (2 ^ e - 1)
  let (s3, rng) := pick rng #[0, 1, 64, 65, 128, 129, 4096, 4097, 1048576, 2 ^ 64 - 1]
  let size := if sk = 0 then s0 else if sk = 1 then s1 else if sk = 2 then s2 else s3
  let (nk, rng) := randNat rng 0 5
  let (n0, rng) := randNat rng 0 (Nat.max size 1 - 1)
  let (n1, rng) := randNat rng 0 (2 ^ 64 - 1)
  let next := if nk = 0 then n1 else n0
  let (salt, rng) := pick rng #[0, 0, 0, 1]
  let (rk, rng) := randNat rng 0 3
  let (rate, rng) := randNat rng 0 (if rk = 0 then 0 else if rk = 1 then 10 ^ 7 else if rk = 2 then 2 ^ 64 else 2 ^ 120 - 1)
  let (ms, rng) := randNat rng 0 (2 ^ 32 - 1)
  let (maxSpan, rng) := pick rng #[0, 3600, 86400, ms]
  let (lk, rng) := randNat rng 0 4
  let (l0, rng) := randNat rng 0 200000
  let (l1, rng) := randNat rng 1 100000
  let (l2, rng) := randNat rng 0 (2 ^ 32 - 1)
  let lastProof := if lk ≤ 1 then caseNow - l0 else if lk = 2 then caseNow + l1 else if lk = 3 then 0 else l2
  let (prov, rng) := pick rng #[stdAddr 0 providerA, stdAddr 0 providerA, stdAddr 0 providerA, stdAddr 0 providerA,
    stdAddr 0 providerA, stdAddr 0 providerA, stdAddr 0 providerA, stdAddr 0 providerA, varAddr 0 providerA,
    stdAddr (-1) providerA, stdAddr 0 strangerA]
  let (cli, rng) := pick rng #[stdAddr 0 clientA, stdAddr 0 clientA, stdAddr 0 clientA, stdAddr 0 clientA, noneAddr,
    stdAddr (-1) clientA]
  let (torrent, rng) := randNat rng 0 (2 ^ 256 - 1)
  let f : File := { size := size, salt := salt }
  let (fk, rng) := randNat rng 0 9
  let d : Data :=
    { active := active, balance := balance, provider := prov,
      merkle := (if fk = 0 then natToBits torrent 256 else bytesToBits f.root), fileSize := size, nextProof := next,
      rate := rate, maxSpan := maxSpan, lastProof := lastProof, client := cli, torrent := torrent }
  let (abk, rng) := randNat rng 0 3
  let (accBal0, rng) := randAmount rng
  let (accBal1, rng) := randNat rng 10000000 100000000000
  let accBal := if abk = 0 then accBal0 else accBal1
  let (sender, rng) := pick rng #[providerA, providerA, providerA, providerA, providerA, providerA, clientA, strangerA]
  let (senderWc, rng) := pick rng #[(0 : Int), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1]
  let (ok, rng) := randNat rng 0 17
  let (qid, rng) := randNat rng 0 (2 ^ 64 - 1)
  let (unknown, rng) := randNat rng 0 (2 ^ 32 - 1)
  let (junkLen, rng) := randNat rng 0 300
  let (junk, rng) := randNat rng 0 (2 ^ 300 - 1)
  let (pk, rng) := randNat rng 0 12
  let (other, rng) := randNat rng 0 (2 ^ 64 - 1)
  let proof : Array Cell :=
    if pk ≤ 6 then #[f.proof next]
    else if pk = 7 then #[f.proof other]
    else if pk = 8 then #[({ f with salt := salt + 1 } : File).proof next]
    else if pk = 9 then #[Cell.mkOrdinary (f.proof next).bits (f.proof next).refs]
    else if pk = 10 then #[libraryCellOf (f.path next)]
    else if pk = 11 then #[pruned f.root f.height]
    else #[]
  for p in proof do
    if p.special then checkCell s!"proof of random case {i}" p
  let (body, refs) : BitString × Array Cell :=
    if ok = 0 then (#[], #[])
    else if ok = 1 then (natToBits 0 32, #[])
    else if ok = 2 then (opq opDeploy qid, #[])
    else if ok = 3 then (opq opAccept qid, #[])
    else if ok = 4 then (opq opClose qid, #[])
    else if ok = 5 then (opq opWithdraw qid, #[])
    else if ok ≤ 12 then (opq opProof qid, proof)
    else if ok = 13 then (opq unknown qid, #[])
    else if ok = 14 then (natToBits unknown 32, #[])
    else if ok = 15 then ((opq opProof qid).extract 0 (unknown % 96), proof)
    else if ok = 16 then (natToBits 0 32 ++ natToBits qid 64, #[Cell.empty])
    else (natToBits junk junkLen, #[])
  let (vk, rng) := randNat rng 0 3
  let (value0, rng) := randAmount rng
  let (value1, rng) := randNat rng 50000000 10000000000
  let value := if vk = 0 then value0 else value1
  let (bounce, rng) := randBool rng
  let (bk2, rng) := randNat rng 0 9
  let (blockSeed, rng) := randNat rng 0 (2 ^ 256 - 1)
  let m := msg sender value body refs bounce (bk2 = 0) (srcWc := senderWc)
  let c : TxCase :=
    { name := s!"v{v}/real/storage/random/{i}", config := withVersion cfg0 v 46, account := account code d accBal,
      msg := m, now := caseNow, lt := 3000000, seed := natToBits blockSeed 256 }
  return (c, rng)

/-- The random cases `0 .. count - 1` from the seed `seed` whose versions are in `versions` (the
cases do not depend on `versions`). -/
def randomCases (code cfg0 : Cell) (versions : List Nat) (count : Nat := 500) (seed : Nat := 20261022) :
    Except String (Array TxCase) := do
  let mut rng := mkStdGen seed
  let mut out : Array TxCase := #[]
  for i in [0:count] do
    let (c, rng') ← randomCase code cfg0 i rng
    rng := rng'
    if versions.any fun v => c.name.startsWith s!"v{v}/" then out := out.push c
  return out

end StorageContract

end Tests.Tx
