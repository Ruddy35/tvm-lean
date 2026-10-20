import TvmLean.Transaction.Config

/-!
# Storage statistics of cell trees

C++ `vm::CellStorageStat` (`crypto/vm/boc.cpp`, with `kill_dup`: every distinct cell counted once)
and `block::AccountStorageStat` (`crypto/block/account-storage-stat.cpp`: the distinct cells of the
account's storage with their reference counts and Merkle depths, kept in a dictionary whose hash is
stored in the account from version 11).
-/

namespace TvmLean.Tx

def bytesToBits (bs : Array UInt8) : BitString :=
  bs.foldl (fun acc b => acc ++ natToBits b.toNat 8) #[]

/-- A distinct cell of a tree: its bits, the number of references to it (from the distinct cells
and the roots), its Merkle depth (capped at 3). -/
structure CellEntry where
  bits : Nat
  refcnt : Nat
  merkleDepth : Nat

/-- The Merkle depth of a cell from those of its children: one more for a Merkle proof or update
(exotic types 3 and 4). -/
def merkleBump (c : Cell) (d : Nat) : Nat :=
  if c.special && c.bits.size ≥ 8 && (bitsToNat (c.bits.extract 0 8) == 3 || bitsToNat (c.bits.extract 0 8) == 4)
  then d + 1 else d

/-- The distinct cells reachable from `roots` (keyed by hash), each root and each reference from a
distinct cell counted in `refcnt` (`AccountStorageStat::add_cell`). `fuel` bounds the depth. -/
def collectCells (roots : List Cell) : Std.HashMap (Array UInt8) CellEntry :=
  let rec go : Nat → Cell → Std.HashMap (Array UInt8) CellEntry → Nat × Std.HashMap (Array UInt8) CellEntry
    | 0, _, m => (0, m)
    | fuel + 1, c, m =>
        let h := c.hashBytes
        match m.get? h with
        | some e => (e.merkleDepth, m.insert h { e with refcnt := e.refcnt + 1 })
        | none =>
            let (d, m) := c.refs.foldl (fun (d, m) r =>
              let (dr, m) := go fuel r m
              (Nat.max d dr, m)) (0, m)
            let d := Nat.min (merkleBump c d) 3
            (d, m.insert h { bits := c.bits.size, refcnt := 1, merkleDepth := d })
  roots.foldl (fun m r => (go (Cell.maxDepth + 2) r m).2) {}

/-- The number of distinct cells and their bits. -/
def cellsAndBits (m : Std.HashMap (Array UInt8) CellEntry) : Nat × Nat :=
  m.fold (fun (c, b) _ e => (c + 1, b + e.bits)) (0, 0)

/-- `CellStorageStat::compute_used_storage` of a slice: the slice as a root cell (its bits), and the
distinct cells it references. -/
def sliceStorage (s : Slice) : Nat × Nat × Nat :=
  let refs := (s.cell.refs.extract s.refPos s.cell.refs.size).toList
  let m := collectCells refs
  let (c, b) := cellsAndBits m
  let depth := refs.foldl (fun d r => Nat.max d ((m.get? r.hashBytes).map (·.merkleDepth) |>.getD 0)) 0
  (c + 1, b + s.bitsRemaining, depth)

/-- `AccountStorageStat::get_dict_hash` of a fresh statistic of `roots`: the dictionary of the
distinct cells (`HashmapE 256`: refcnt:uint32 max_merkle_depth:uint2), its root hash (zero if empty). -/
def storageDictHash (m : Std.HashMap (Array UInt8) CellEntry) : Option BitString := do
  let entries := m.toArray.qsort (fun a b => bytesToNatBE a.1 < bytesToNatBE b.1)
  let root ← entries.foldlM (init := (none : Option Cell)) fun root (h, e) =>
    let val : Builder := { bits := natToBits e.refcnt 32 ++ natToBits e.merkleDepth 2, refs := #[] }
    match dictSetBuilderWithCells root (bytesToBits h) val .set with
    | .ok (r, _, _, _) => some r
    | .error _ => none
  return match root with
    | none => natToBits 0 256
    | some c => bytesToBits c.hashBytes

end TvmLean.Tx
