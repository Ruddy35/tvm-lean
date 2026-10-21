import TvmLean.Proofs.Fast.Sha256
import TvmLean.Proofs.ModelEquiv

/-!
# The cell hash in a form the kernel evaluates fast

`Cell.hashBytes` is `Cell.computeLevelInfo?`'s hash at the highest level; the level information is
computed bottom-up by `Cell.levelInfoFromChildren`, whose hashed representation of a cell is the two
descriptor bytes, the data bytes, the children's depths and hashes, then SHA-256. The model makes the
data bytes one at a time, `bitsToByte c.bits (i * 8) 8` for byte `i`: in the kernel each call walks
the bit list from its head, quadratic in the length of the cell, and SHA-256 runs on `UInt32`.

`Cell.levelInfoFromChildrenFast` is the model's text with the data bytes made in one pass
(`bitStringToBytesBEFast`, `bitsToPaddedLastByteFast`) and `sha256DigestFast`;
`Cell.computeLevelInfoFast?` and `Cell.hashBytesFast` call it. Each is proved equal to the model's
function for every cell (`Cell.levelInfoFromChildren_eq_fast`, `Cell.computeLevelInfo?_eq_fast`,
`Cell.hashBytes_eq_fast`).
-/

namespace TvmLean

set_option Elab.async false

/-- `Cell.levelInfoFromChildren` with the data bytes of the hashed representation made in one pass
over the bits (`bitStringToBytesBEFast` and `bitsToPaddedLastByteFast`: the model's loop reads byte
`i` with `bitsToByte c.bits (i * 8) 8`, which walks the bit list from its head), the bytes of pruned
branches and Merkle cells by `bitStringToBytesBEFast`, and SHA-256 by `sha256DigestFast`; the rest is
the model's text. -/
def Cell.levelInfoFromChildrenFast (c : Cell) (childInfos : Array CellLevelInfo) :
    Except String CellLevelInfo := do
  let ty : CellSpecialType ←
    if !c.special then
      pure .ordinary
    else
      if c.bits.size < 8 then
        throw "Not enough data for a special cell"
      let tyByte := bitsToNat (c.bits.take 8)
      match CellSpecialType.ofByte? tyByte with
      | some .ordinary => throw "Invalid special cell type"
      | some t => pure t
      | none => throw "Invalid special cell type"

  let maxLevel : Nat := Cell.maxLevel
  let mut levelMask : Nat := 0
  let mut depths : Array Nat := Array.replicate (maxLevel + 1) 0

  let mut prunedBytes : Option (Array UInt8) := none
  let mut prunedHashesCount : Nat := 0

  match ty with
  | .ordinary =>
      for ci in childInfos do
        levelMask := levelMask ||| ci.levelMask
        for lvl in List.range' (0) ((maxLevel + 1) - (0)) do
          let d := ci.getDepth lvl
          if d > depths[lvl]! then
            depths := depths.set! lvl d
      if c.refs.size != 0 then
        depths := depths.map (fun d => d + 1)
  | .prunedBranch =>
      if c.refs.size != 0 then
        throw "Pruned branch cannot have references"
      if c.bits.size < 16 then
        throw "Length mismatch in a pruned branch"
      if c.bits.size % 8 != 0 then
        throw "Length mismatch in a pruned branch"
      let bytes := bitStringToBytesBEFast c.bits
      prunedBytes := some bytes
      if bytes.size < 2 then
        throw "Not enough data for a special cell"
      levelMask := bytes[1]!.toNat
      let lvl := LevelMask.getLevel levelMask
      if lvl = 0 || lvl > maxLevel then
        throw "Invalid level mask in a pruned branch"
      prunedHashesCount := LevelMask.getHashI levelMask
      let expectedBytes : Nat := 2 + prunedHashesCount * (32 + 2)
      if bytes.size != expectedBytes then
        throw "Length mismatch in a pruned branch"
      -- depth[maxLevel] = 0
      for off in List.range' (0) ((maxLevel) - (0)) do
        let i := maxLevel - 1 - off
        if LevelMask.isSignificant levelMask (i + 1) then
          let hashesBefore := LevelMask.getHashI (LevelMask.apply levelMask i)
          let depthOff := 2 + prunedHashesCount * 32 + hashesBefore * 2
          let d ← readDepthBE bytes depthOff
          depths := depths.set! i d
        else
          depths := depths.set! i (depths[i + 1]!)
  | .library =>
      if c.refs.size != 0 then
        throw "Library cell cannot have references"
      if c.bits.size != 8 * (1 + 32) then
        throw "Length mismatch in a library cell"
      levelMask := 0
      depths := Array.replicate (maxLevel + 1) 0
  | .merkleProof =>
      if c.refs.size != 1 then
        throw "Merkle proof must have exactly one reference"
      if c.bits.size != 8 * (1 + 32 + 2) then
        throw "Length mismatch in a Merkle proof"
      if c.bits.size % 8 != 0 then
        throw "Length mismatch in a Merkle proof"
      let bytes := bitStringToBytesBEFast c.bits
      let child ←
        match childInfos[0]? with
        | some v => pure v
        | none => throw "internal error (missing Merkle child)"
      let storedHash := bytes.extract 1 (1 + 32)
      if storedHash != child.getHash 0 then
        throw "Invalid hash in a Merkle proof or update"
      let storedDepth ← readDepthBE bytes (1 + 32)
      if storedDepth != child.getDepth 0 then
        throw "Invalid depth in a Merkle proof or update"
      for lvl in List.range' (0) ((maxLevel + 1) - (0)) do
        let childLevel := Nat.min maxLevel (lvl + 1)
        depths := depths.set! lvl (Nat.max depths[lvl]! (child.getDepth childLevel + 1))
      levelMask := LevelMask.shiftRight child.levelMask
  | .merkleUpdate =>
      if c.refs.size != 2 then
        throw "Merkle update must have exactly two references"
      if c.bits.size != 8 * (1 + (32 + 2) * 2) then
        throw "Length mismatch in a Merkle update"
      if c.bits.size % 8 != 0 then
        throw "Length mismatch in a Merkle update"
      let bytes := bitStringToBytesBEFast c.bits
      let c0 ←
        match childInfos[0]? with
        | some v => pure v
        | none => throw "internal error (missing Merkle child 0)"
      let c1 ←
        match childInfos[1]? with
        | some v => pure v
        | none => throw "internal error (missing Merkle child 1)"
      let storedHash0 := bytes.extract 1 (1 + 32)
      if storedHash0 != c0.getHash 0 then
        throw "Invalid hash in a Merkle proof or update"
      let storedHash1 := bytes.extract (1 + 32) (1 + 2 * 32)
      if storedHash1 != c1.getHash 0 then
        throw "Invalid hash in a Merkle proof or update"
      let storedDepth0 ← readDepthBE bytes (1 + 2 * 32)
      if storedDepth0 != c0.getDepth 0 then
        throw "Invalid depth in a Merkle proof or update"
      let storedDepth1 ← readDepthBE bytes (1 + 2 * 32 + 2)
      if storedDepth1 != c1.getDepth 0 then
        throw "Invalid depth in a Merkle proof or update"
      for lvl in List.range' (0) ((maxLevel + 1) - (0)) do
        let childLevel := Nat.min maxLevel (lvl + 1)
        depths := depths.set! lvl (Nat.max depths[lvl]! (c0.getDepth childLevel + 1))
        depths := depths.set! lvl (Nat.max depths[lvl]! (c1.getDepth childLevel + 1))
      levelMask := LevelMask.shiftRight (c0.levelMask ||| c1.levelMask)

  if c.levelMask != levelMask then
    throw "level mask mismatch"

  let effectiveLevel := LevelMask.getLevel levelMask
  if effectiveLevel > maxLevel then
    throw "Invalid level mask"

  let zeroHash : Array UInt8 := Array.replicate 32 0
  let mut hashes : Array (Array UInt8) := Array.replicate (maxLevel + 1) zeroHash
  let mut lastComputed : Option Nat := none

  let isMerkleNode : Bool := ty == .merkleProof || ty == .merkleUpdate

  for lvl in List.range' (0) ((maxLevel + 1) - (0)) do
    let shouldCompute : Bool :=
      lvl == maxLevel || LevelMask.isSignificant levelMask (lvl + 1)
    if !shouldCompute then
      continue

    let h : Array UInt8 ←
      match ty, prunedBytes with
      | .prunedBranch, some bytes =>
          if lvl != maxLevel then
            let hashesBefore := LevelMask.getHashI (LevelMask.apply levelMask lvl)
            let off := 2 + hashesBefore * 32
            if off + 32 > bytes.size then
              throw "Length mismatch in a pruned branch"
            pure (bytes.extract off (off + 32))
          else
            -- computed below as an ordinary hash (no chaining for pruned branches)
            pure #[] -- placeholder, overwritten below
      | _, _ =>
          pure #[] -- placeholder, overwritten below

    let h :=
      if h.isEmpty then
        let refsCnt : Nat := c.refs.size
        let bitLen : Nat := c.bits.size
        let fullBytes : Nat := bitLen / 8
        let remBits : Nat := bitLen % 8
        let d1 : Nat :=
          refsCnt +
            (if c.special then 8 else 0) +
              (LevelMask.apply levelMask lvl <<< 5)
        let d2 : Nat := (fullBytes <<< 1) + (if remBits = 0 then 0 else 1)
        Id.run do
          let mut msg : Array UInt8 := #[UInt8.ofNat d1, UInt8.ofNat d2]
          match lastComputed with
          | some last =>
              if ty != .prunedBranch then
                msg := msg ++ hashes[last]!
              else
                -- pruned branch: no chaining; always hash original data
                msg := msg ++ bitStringToBytesBEFast c.bits
                if remBits ≠ 0 then
                  msg := msg.push (bitsToPaddedLastByteFast c.bits (fullBytes * 8) remBits)
          | none =>
              msg := msg ++ bitStringToBytesBEFast c.bits
              if remBits ≠ 0 then
                msg := msg.push (bitsToPaddedLastByteFast c.bits (fullBytes * 8) remBits)

          let childLevel : Nat := if isMerkleNode then Nat.min maxLevel (lvl + 1) else lvl
          for ci in childInfos do
            let d := ci.getDepth childLevel
            msg := msg.push (UInt8.ofNat ((d >>> 8) &&& 0xff))
            msg := msg.push (UInt8.ofNat (d &&& 0xff))
          for ci in childInfos do
            msg := msg ++ ci.getHash childLevel
          sha256DigestFast msg
      else
        h

    -- Store + fill gaps.
    let start : Nat :=
      match lastComputed with
      | none => 0
      | some last => last + 1
    for j in List.range' (start) ((lvl) - (start)) do
      hashes := hashes.set! j h
    hashes := hashes.set! lvl h
    lastComputed := some lvl

  return { ty, levelMask, effectiveLevel, depths, hashes }

/-- The model's loop over the data bytes of a cell is `bitStringToBytesBEFast` appended. -/
theorem foldl_push_bitsToByte (bits : BitString) (msg : Array UInt8) :
    List.foldl (fun b a => b.push (bitsToByte bits (a * 8) 8)) msg (List.range' 0 (bits.size / 8)) =
      msg ++ bitStringToBytesBEFast bits := by
  apply Array.ext'
  rw [foldl_push_toList, ← bitStringToBytesBE_eq_fast, Array.toList_append]
  simp only [bitStringToBytesBE, Id.run, Nat.sub_zero, List.forIn_pure_yield_eq_foldl, bind_pure_comp,
    map_pure, pure_bind]
  rw [foldl_push_toList]
  simp

@[fast_forms] theorem Cell.levelInfoFromChildren_eq_fast (c : Cell) (childInfos : Array CellLevelInfo) :
    Cell.levelInfoFromChildren c childInfos = Cell.levelInfoFromChildrenFast c childInfos := by
  unfold Cell.levelInfoFromChildren Cell.levelInfoFromChildrenFast
  simp only [Id.run, List.forIn_pure_yield_eq_foldl, bind_pure_comp, map_pure, pure_bind, Nat.sub_zero,
    foldl_push_bitsToByte, bitStringToBytesBE_eq_fast, bitsToPaddedLastByte_eq_fast, sha256Digest_eq_fast]
  matchers_rfl

@[fast_repl] theorem Cell.levelInfoFromChildren_eq_fast_fun :
    @Cell.levelInfoFromChildren = @Cell.levelInfoFromChildrenFast := by
  funext c childInfos; exact Cell.levelInfoFromChildren_eq_fast c childInfos

mutual
/-- `Cell.computeLevelInfo?` with `Cell.levelInfoFromChildrenFast`. -/
def Cell.computeLevelInfoFast? : Cell → Except String CellLevelInfo
  | c@⟨_, ⟨refs⟩, _, _⟩ => do
    if c.refs.size > 4 then
      throw "Too many references"
    if c.bits.size > 1023 then
      throw "Too many data bits"
    let childInfos ← Cell.childLevelInfosFast? refs
    Cell.levelInfoFromChildrenFast c childInfos
termination_by structural c => c
/-- `Cell.childLevelInfos?` with `Cell.computeLevelInfoFast?`. -/
def Cell.childLevelInfosFast? : List Cell → Except String (Array CellLevelInfo)
  | [] => pure #[]
  | r :: rs => do
    let i ← Cell.computeLevelInfoFast? r
    let is ← Cell.childLevelInfosFast? rs
    pure (#[i] ++ is)
termination_by structural rs => rs
end

mutual
theorem Cell.computeLevelInfo?_eq_fast : (c : Cell) → Cell.computeLevelInfo? c = Cell.computeLevelInfoFast? c
  | ⟨bits, ⟨refs⟩, special, levelMask⟩ => by
    rw [Cell.computeLevelInfo?, Cell.computeLevelInfoFast?, Cell.childLevelInfos?_eq_fast refs]
    simp only [Cell.levelInfoFromChildren_eq_fast]
termination_by structural c => c
theorem Cell.childLevelInfos?_eq_fast : (l : List Cell) → Cell.childLevelInfos? l = Cell.childLevelInfosFast? l
  | [] => by rw [Cell.childLevelInfos?, Cell.childLevelInfosFast?]
  | r :: rs => by
    rw [Cell.childLevelInfos?, Cell.childLevelInfosFast?, Cell.computeLevelInfo?_eq_fast r,
      Cell.childLevelInfos?_eq_fast rs]
termination_by structural rs => rs
end

/-- `Cell.hashBytes` by `Cell.computeLevelInfoFast?`. -/
def Cell.hashBytesFast (c : Cell) : Array UInt8 :=
  match c.computeLevelInfoFast? with
  | .ok info => info.getHash Cell.maxLevel
  | .error _ => Array.replicate 32 0

@[fast_forms] theorem Cell.hashBytes_eq_fast (c : Cell) : c.hashBytes = c.hashBytesFast := by
  rw [Cell.hashBytes, Cell.hashBytesFast, Cell.computeLevelInfo?_eq_fast]
  rfl

@[fast_repl] theorem Cell.hashBytes_eq_fast_fun : @Cell.hashBytes = @Cell.hashBytesFast := by
  funext c; exact Cell.hashBytes_eq_fast c

end TvmLean
