import TvmLean.Semantics

/-!
# The refactored model functions and the original definitions of tvm-lean `e1f334f`

`TvmLean.Orig.*` are **verbatim copies** of the original definitions (commit `e1f334f`). For
every function whose original is a total definition, the current definition is proved equal to
it. (Originals marked `partial`, and `while` loops, have no logical content in Lean; for those
the current definition is proved to satisfy the original defining equation: see section 2.)
-/

namespace TvmLean.Orig

open TvmLean

def bitsToByte (bs : BitString) (start len : Nat) : UInt8 :=
  Id.run do
    let mut acc : Nat := 0
    for j in [0:len] do
      if bs[start + j]! then
        acc := acc ||| (1 <<< (7 - j))
    UInt8.ofNat acc

def bitsToPaddedLastByte (bs : BitString) (start usedBits : Nat) : UInt8 :=
  -- `usedBits` ∈ {1..7}: data bits in the high bits, then a single `1` tag bit, then zeros.
  Id.run do
    let mut acc : Nat := 0
    for j in [0:usedBits] do
      if bs[start + j]! then
        acc := acc ||| (1 <<< (7 - j))
    acc := acc ||| (1 <<< (7 - usedBits))
    UInt8.ofNat acc

def byteArrayToNatBE (bs : ByteArray) : Nat :=
  Id.run do
    let mut acc : Nat := 0
    for i in [0:bs.size] do
      acc := (acc <<< 8) + (bs.get! i).toNat
    return acc

def bitStringToBytesBE (bs : BitString) : Array UInt8 :=
  -- Mirrors `td::BitSliceWrite{buffer, bytes*8} = prefetch_bits(bytes*8)` used by `CellSlice::prefetch_bytes`.
  -- Bit order: first bit is the MSB of the first byte.
  Id.run do
    let bytes : Nat := bs.size / 8
    let mut out : Array UInt8 := #[]
    for i in [0:bytes] do
      out := out.push (bitsToByte bs (i * 8) 8)
    out

def sha256Digest (msg : Array UInt8) : Array UInt8 :=
  Id.run do
    let padded := sha256Pad msg
    let mut h := sha256Init
    let blocks := padded.size / 64
    for bi in [0:blocks] do
      let base := bi * 64
      let mut w : Array UInt32 := Array.replicate 64 0
      for i in [0:16] do
        let j := base + i * 4
        let b0 := padded[j]!
        let b1 := padded[j + 1]!
        let b2 := padded[j + 2]!
        let b3 := padded[j + 3]!
        w := w.set! i (u32FromBytesBE b0 b1 b2 b3)
      for i in [16:64] do
        let s0 := shaSmallSigma0 (w[i - 15]!)
        let s1 := shaSmallSigma1 (w[i - 2]!)
        w := w.set! i (w[i - 16]! + s0 + w[i - 7]! + s1)

      let mut a := h[0]!
      let mut b := h[1]!
      let mut c := h[2]!
      let mut d := h[3]!
      let mut e := h[4]!
      let mut f := h[5]!
      let mut g := h[6]!
      let mut hh := h[7]!

      for i in [0:64] do
        let t1 := hh + shaBigSigma1 e + shaCh e f g + sha256K[i]! + w[i]!
        let t2 := shaBigSigma0 a + shaMaj a b c
        hh := g
        g := f
        f := e
        e := d + t1
        d := c
        c := b
        b := a
        a := t1 + t2

      h := h.set! 0 (h[0]! + a)
      h := h.set! 1 (h[1]! + b)
      h := h.set! 2 (h[2]! + c)
      h := h.set! 3 (h[3]! + d)
      h := h.set! 4 (h[4]! + e)
      h := h.set! 5 (h[5]! + f)
      h := h.set! 6 (h[6]! + g)
      h := h.set! 7 (h[7]! + hh)

    let mut out : Array UInt8 := #[]
    for i in [0:8] do
      let x := h[i]!
      out := out.push (UInt8.ofNat ((x >>> 24).toNat &&& 0xff))
      out := out.push (UInt8.ofNat ((x >>> 16).toNat &&& 0xff))
      out := out.push (UInt8.ofNat ((x >>> 8).toNat &&& 0xff))
      out := out.push (UInt8.ofNat (x.toNat &&& 0xff))
    out

/-! Minimal SHA512 (used for TON PRNG: RANDU256 / RAND).

This is engineering code for diff-testing and coverage; it is not formally verified yet.
-/

def sha512Digest (msg : Array UInt8) : Array UInt8 :=
  Id.run do
    let padded := sha512Pad msg
    let mut h := sha512Init
    let blocks := padded.size / 128
    for bi in [0:blocks] do
      let base := bi * 128
      let mut w : Array UInt64 := Array.replicate 80 0
      for i in [0:16] do
        let j := base + i * 8
        let b0 := padded[j]!
        let b1 := padded[j + 1]!
        let b2 := padded[j + 2]!
        let b3 := padded[j + 3]!
        let b4 := padded[j + 4]!
        let b5 := padded[j + 5]!
        let b6 := padded[j + 6]!
        let b7 := padded[j + 7]!
        w := w.set! i (u64FromBytesBE b0 b1 b2 b3 b4 b5 b6 b7)
      for i in [16:80] do
        let s0 := sha512SmallSigma0 (w[i - 15]!)
        let s1 := sha512SmallSigma1 (w[i - 2]!)
        w := w.set! i (w[i - 16]! + s0 + w[i - 7]! + s1)

      let mut a := h[0]!
      let mut b := h[1]!
      let mut c := h[2]!
      let mut d := h[3]!
      let mut e := h[4]!
      let mut f := h[5]!
      let mut g := h[6]!
      let mut hh := h[7]!

      for i in [0:80] do
        let t1 := hh + sha512BigSigma1 e + sha512Ch e f g + sha512K[i]! + w[i]!
        let t2 := sha512BigSigma0 a + sha512Maj a b c
        hh := g
        g := f
        f := e
        e := d + t1
        d := c
        c := b
        b := a
        a := t1 + t2

      h := h.set! 0 (h[0]! + a)
      h := h.set! 1 (h[1]! + b)
      h := h.set! 2 (h[2]! + c)
      h := h.set! 3 (h[3]! + d)
      h := h.set! 4 (h[4]! + e)
      h := h.set! 5 (h[5]! + f)
      h := h.set! 6 (h[6]! + g)
      h := h.set! 7 (h[7]! + hh)

    let mut out : Array UInt8 := #[]
    for i in [0:8] do
      let x := h[i]!
      out := out.push (UInt8.ofNat ((x >>> 56).toNat &&& 0xff))
      out := out.push (UInt8.ofNat ((x >>> 48).toNat &&& 0xff))
      out := out.push (UInt8.ofNat ((x >>> 40).toNat &&& 0xff))
      out := out.push (UInt8.ofNat ((x >>> 32).toNat &&& 0xff))
      out := out.push (UInt8.ofNat ((x >>> 24).toNat &&& 0xff))
      out := out.push (UInt8.ofNat ((x >>> 16).toNat &&& 0xff))
      out := out.push (UInt8.ofNat ((x >>> 8).toNat &&& 0xff))
      out := out.push (UInt8.ofNat (x.toNat &&& 0xff))
    out

def dictLabelMatches (lbl : DictLabel) (key : BitString) (pos : Nat) : Bool :=
  if pos + lbl.len > key.size then
    false
  else
    match lbl.sameBit with
    | some b =>
        Id.run do
          let mut ok := true
          for i in [0:lbl.len] do
            if key[pos + i]! != b then
              ok := false
          return ok
    | none =>
        let bs := lbl.remainder.readBits lbl.len
        Id.run do
          let mut ok := true
          for i in [0:lbl.len] do
            if bs[i]! != key[pos + i]! then
              ok := false
          return ok

/-- The body of the original `partial def Cell.computeLevelInfo?` (verbatim), with the recursive
call abstracted as `rec`. -/
def levelBody (rec : Cell → Except String CellLevelInfo) (c : Cell) : Except String CellLevelInfo := do
  if c.refs.size > 4 then
    throw "Too many references"
  if c.bits.size > 1023 then
    throw "Too many data bits"

  let mut childInfos : Array CellLevelInfo := #[]
  for r in c.refs do
    childInfos := childInfos.push (← rec r)

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
        for lvl in [0:maxLevel + 1] do
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
      let bytes := bitStringToBytesBE c.bits
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
      for off in [0:maxLevel] do
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
      let bytes := bitStringToBytesBE c.bits
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
      for lvl in [0:maxLevel + 1] do
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
      let bytes := bitStringToBytesBE c.bits
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
      for lvl in [0:maxLevel + 1] do
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

  for lvl in [0:maxLevel + 1] do
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
                for i in [0:fullBytes] do
                  msg := msg.push (bitsToByte c.bits (i * 8) 8)
                if remBits ≠ 0 then
                  msg := msg.push (bitsToPaddedLastByte c.bits (fullBytes * 8) remBits)
          | none =>
              for i in [0:fullBytes] do
                msg := msg.push (bitsToByte c.bits (i * 8) 8)
              if remBits ≠ 0 then
                msg := msg.push (bitsToPaddedLastByte c.bits (fullBytes * 8) remBits)

          let childLevel : Nat := if isMerkleNode then Nat.min maxLevel (lvl + 1) else lvl
          for ci in childInfos do
            let d := ci.getDepth childLevel
            msg := msg.push (UInt8.ofNat ((d >>> 8) &&& 0xff))
            msg := msg.push (UInt8.ofNat (d &&& 0xff))
          for ci in childInfos do
            msg := msg ++ ci.getHash childLevel
          sha256Digest msg
      else
        h

    -- Store + fill gaps.
    let start : Nat :=
      match lastComputed with
      | none => 0
      | some last => last + 1
    for j in [start:lvl] do
      hashes := hashes.set! j h
    hashes := hashes.set! lvl h
    lastComputed := some lvl

  return { ty, levelMask, effectiveLevel, depths, hashes }

end TvmLean.Orig

namespace TvmLean

/-! ## 1. Originals that are total: equality -/


theorem bitsToByte_eq_orig : @bitsToByte = @Orig.bitsToByte := by
  funext
  simp [bitsToByte, Orig.bitsToByte, Std.Range.forIn_eq_forIn_range', Std.Range.size]

theorem bitsToPaddedLastByte_eq_orig : @bitsToPaddedLastByte = @Orig.bitsToPaddedLastByte := by
  funext
  simp [bitsToPaddedLastByte, Orig.bitsToPaddedLastByte, Std.Range.forIn_eq_forIn_range', Std.Range.size]

theorem byteArrayToNatBE_eq_orig : @byteArrayToNatBE = @Orig.byteArrayToNatBE := by
  funext
  simp [byteArrayToNatBE, Orig.byteArrayToNatBE, Std.Range.forIn_eq_forIn_range', Std.Range.size]

theorem bitStringToBytesBE_eq_orig : @bitStringToBytesBE = @Orig.bitStringToBytesBE := by
  funext
  simp [bitStringToBytesBE, Orig.bitStringToBytesBE, Std.Range.forIn_eq_forIn_range', Std.Range.size, bitsToByte_eq_orig]

theorem sha256Digest_eq_orig : @sha256Digest = @Orig.sha256Digest := by
  funext
  simp [sha256Digest, Orig.sha256Digest, Std.Range.forIn_eq_forIn_range', Std.Range.size]

theorem sha512Digest_eq_orig : @sha512Digest = @Orig.sha512Digest := by
  funext
  simp [sha512Digest, Orig.sha512Digest, Std.Range.forIn_eq_forIn_range', Std.Range.size]

theorem allBelow_eq_all (n : Nat) (p : Nat → Bool) : allBelow n p = (List.range' 0 n).all p := by
  induction n with
  | zero => rfl
  | succ n ih => rw [allBelow, ih, List.range'_concat, List.all_append]; simp

/-- The original "flag" loop: `ok` stays as it was while the condition holds, becomes `false` otherwise. -/
theorem forIn_flag (l : List Nat) (q : Nat → Prop) [DecidablePred q] (ok : Bool) :
    (forIn (m := Id) l ok (fun i r => if q i then pure (ForInStep.yield r) else pure (ForInStep.yield false))).run =
      (ok && l.all (fun i => decide (q i))) := by
  induction l generalizing ok with
  | nil => simp
  | cons a l ih =>
    simp only [List.forIn_cons, List.all_cons]
    by_cases h : q a
    · simp [h, ih]
    · simp [h, ih]

theorem bool_beq_decide (a b : Bool) : (a == b) = decide (a = b) := by cases a <;> cases b <;> rfl

theorem dictLabelMatches_eq_orig : @dictLabelMatches = @Orig.dictLabelMatches := by
  funext lbl key pos
  simp [dictLabelMatches, Orig.dictLabelMatches, Std.Range.forIn_eq_forIn_range', Std.Range.size, allBelow_eq_all, forIn_flag, bool_beq_decide]
  rfl

/-! ## 2. Originals that are `partial`: the current function satisfies the original defining equation -/

/-- The reference loop of the original level computation is `childLevelInfos?`, appended. -/
theorem forIn_push_childLevelInfos (l : List Cell) (acc : Array CellLevelInfo) :
    forIn (m := Except String) l acc (fun r childInfos =>
        Cell.computeLevelInfo? r >>= fun x => pure (ForInStep.yield (childInfos.push x))) =
      (fun is => acc ++ is) <$> Cell.childLevelInfos? l := by
  induction l generalizing acc with
  | nil => simp [Cell.childLevelInfos?]
  | cons r l ih =>
    rw [List.forIn_cons, Cell.childLevelInfos?]
    cases h : Cell.computeLevelInfo? r with
    | error e => rfl
    | ok x =>
      show forIn l (acc.push x) _ = (fun is => acc ++ is) <$> (Cell.childLevelInfos? l >>= fun is => pure (#[x] ++ is))
      rw [ih]
      cases Cell.childLevelInfos? l with
      | error e => rfl
      | ok is =>
        show Except.ok (acc.push x ++ is) = Except.ok (acc ++ (#[x] ++ is))
        rw [← Array.append_assoc]; rfl

end TvmLean
