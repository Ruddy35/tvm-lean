import TvmLean.Model.Instr.Codepage.Cp0

namespace TvmLean

def intToBitsTwos (n : Int) (bits : Nat) : Except Excno BitString := do
  if bits = 0 then
    return #[]
  -- For signed `bits`-wide two's complement, require `-(2^(bits-1)) ≤ n < 2^(bits-1)`.
  let half : Int := intPow2 (bits - 1)
  if decide (n < -half ∨ n ≥ half) then
    throw .rangeChk
  let modulus : Nat := 1 <<< bits
  if n ≥ 0 then
    let u := n.toNat
    return natToBits u bits
  else
    -- two's complement: 2^bits - |n|
    let abs : Nat := (-n).toNat
    return natToBits (modulus - abs) bits

def Slice.takeBitsAsNatCellUnd (s : Slice) (n : Nat) : Except Excno (Nat × Slice) := do
  if s.haveBits n then
    let bs := s.readBits n
    return (bitsToNat bs, s.advanceBits n)
  else
    throw .cellUnd

def Slice.skipMaybeAnycast (s : Slice) : Except Excno Slice := do
  -- Mirrors C++ `skip_maybe_anycast` for modern TVM (global_version >= 10):
  -- only `nothing$0` is accepted.
  let (b, s1) ← s.takeBitsAsNatCellUnd 1
  if b = 0 then
    return s1
  else
    throw .cellUnd

def Slice.skipMessageAddr (s : Slice) : Except Excno Slice := do
  -- Mirrors C++ `skip_message_addr` for modern TVM (global_version >= 10):
  -- `addr_var$11` and anycast `just$1` are rejected.
  let (tag, s2) ← s.takeBitsAsNatCellUnd 2
  match tag with
  | 0 =>
      -- addr_none$00
      return s2
  | 1 =>
      -- addr_extern$01 len:(## 9) external_address:(bits len)
      let (len, s11) ← s2.takeBitsAsNatCellUnd 9
      if s11.haveBits len then
        return s11.advanceBits len
      else
        throw .cellUnd
  | 2 =>
      -- addr_std$10 anycast:(Maybe Anycast) workchain_id:int8 address:bits256
      let s3 ← s2.skipMaybeAnycast
      let need : Nat := 8 + 256
      if s3.haveBits need then
        return s3.advanceBits need
      else
        throw .cellUnd
  | 3 =>
      -- addr_var$11 is unavailable for modern TVM.
      throw .cellUnd
  | _ =>
      throw .cellUnd

/-- `Maybe Anycast` as the TL-B schema defines it (block.tlb: `anycast_info$_ depth:(#<= 30)
{ depth >= 1 } rewrite_pfx:(bits depth)`), for the validation of whole messages (the generated
unpackers), unlike `skipMaybeAnycast` (C++ `skip_maybe_anycast`, which rejects anycasts). -/
def Slice.skipMaybeAnycastTlb (s : Slice) : Except Excno Slice := do
  let (b, s1) ← s.takeBitsAsNatCellUnd 1
  if b = 0 then
    return s1
  let (depth, s2) ← s1.takeBitsAsNatCellUnd 5
  if depth < 1 ∨ depth > 30 ∨ !s2.haveBits depth then
    throw .cellUnd
  return s2.advanceBits depth

/-- TL-B `MsgAddressInt`: `addr_std$10 anycast:(Maybe Anycast) workchain_id:int8 address:bits256`
or `addr_var$11 anycast:(Maybe Anycast) addr_len:(## 9) workchain_id:int32 address:(bits addr_len)`. -/
def Slice.skipMsgAddressIntTlb (s : Slice) : Except Excno Slice := do
  let (tag, s1) ← s.takeBitsAsNatCellUnd 2
  if tag < 2 then
    throw .cellUnd
  let s2 ← s1.skipMaybeAnycastTlb
  let (len, s3) ← if tag = 2 then pure (256, s2) else s2.takeBitsAsNatCellUnd 9
  let need : Nat := (if tag = 2 then 8 else 32) + len
  if !s3.haveBits need then
    throw .cellUnd
  return s3.advanceBits need

/-- TL-B `MsgAddressExt` as the generated `MsgAddressExt::skip` (block-auto.cpp) reads it: tag `00`
is `addr_none$00`; `get_tag` is `bselect(2, 3)`, so `01`, `10` and `11` all read as
`addr_extern$01 len:(## 9) external_address:(bits len)` (the tag bits are not checked again). -/
def Slice.skipMsgAddressExtTlb (s : Slice) : Except Excno Slice := do
  let (tag, s1) ← s.takeBitsAsNatCellUnd 2
  if tag = 0 then
    return s1
  let (len, s2) ← s1.takeBitsAsNatCellUnd 9
  if !s2.haveBits len then
    throw .cellUnd
  return s2.advanceBits len

/-- TL-B `MsgAddress`: `MsgAddressExt` or `MsgAddressInt`. -/
def Slice.skipMsgAddressTlb (s : Slice) : Except Excno Slice := do
  let (b, _) ← s.takeBitsAsNatCellUnd 1
  if b = 0 then s.skipMsgAddressExtTlb else s.skipMsgAddressIntTlb

def Slice.parseMaybeAnycast (s : Slice) : Except Excno (Value × Slice) := do
  -- Mirrors C++ `parse_maybe_anycast` for modern TVM (global_version >= 10):
  -- only `nothing$0` is accepted.
  let (b, s1) ← s.takeBitsAsNatCellUnd 1
  if b = 0 then
    return (.null, s1)
  else
    throw .cellUnd

def Slice.parseMessageAddr (s : Slice) : Except Excno (Array Value × Slice) := do
  -- Mirrors C++ `parse_message_addr` for modern TVM (global_version >= 10).
  let (tag, s2) ← s.takeBitsAsNatCellUnd 2
  match tag with
  | 0 =>
      -- addr_none$00 = MsgAddressExt; -> (0)
      return (#[.int (.num 0)], s2)
  | 1 =>
      -- addr_extern$01 len:(## 9) external_address:(bits len) = MsgAddressExt; -> (1, addr)
      let (len, s3) ← s2.takeBitsAsNatCellUnd 9
      if !s3.haveBits len then
        throw .cellUnd
      let addrBits := s3.readBits len
      let s4 := s3.advanceBits len
      return (#[.int (.num 1), .slice (Slice.ofCell (Cell.mkOrdinary addrBits #[]))], s4)
  | 2 =>
      -- addr_std$10 anycast:(Maybe Anycast) workchain_id:int8 address:bits256 = MsgAddressInt;
      -- -> (2, anycast_or_null, workchain, addr256)
      let (anycast, s3) ← s2.parseMaybeAnycast
      let (wcNat, s4) ← s3.takeBitsAsNatCellUnd 8
      if !s4.haveBits 256 then
        throw .cellUnd
      let addrBits := s4.readBits 256
      let s5 := s4.advanceBits 256
      let wc : Int := natToIntSignedTwos wcNat 8
      return (#[.int (.num 2), anycast, .int (.num wc), .slice (Slice.ofCell (Cell.mkOrdinary addrBits #[]))], s5)
  | 3 =>
      -- addr_var$11 is unavailable for modern TVM.
      throw .cellUnd
  | _ =>
      throw .cellUnd

def Slice.takeVarUIntegerCellUnd (s : Slice) (lenBits : Nat) : Except Excno (Nat × Slice) := do
  let (len, s1) ← s.takeBitsAsNatCellUnd lenBits
  let dataBits : Nat := len * 8
  if s1.haveBits dataBits then
    let bs := s1.readBits dataBits
    return (bitsToNat bs, s1.advanceBits dataBits)
  else
    throw .cellUnd

def Slice.takeGramsCellUnd (s : Slice) : Except Excno (Int × Slice) := do
  -- Grams = VarUInteger 16, which uses 4-bit length (bytes) prefix in practice.
  let (n, s1) ← s.takeVarUIntegerCellUnd 4
  return (Int.ofNat n, s1)

def Slice.skipHashmapECellUnd (s : Slice) : Except Excno Slice := do
  -- HashmapE is encoded as: `hme_empty$0` or `hme_root$1 root:^Hashmap`.
  let (tag, s1) ← s.takeBitsAsNatCellUnd 1
  if tag = 0 then
    return s1
  else
    if s1.haveRefs 1 then
      return { s1 with refPos := s1.refPos + 1 }
    else
      throw .cellUnd

def Slice.takeCurrencyCollectionGramsCellUnd (s : Slice) : Except Excno (Int × Slice) := do
  -- CurrencyCollection = currencies$_ grams:Grams other:ExtraCurrencyCollection.
  let (grams, s1) ← s.takeGramsCellUnd
  -- ExtraCurrencyCollection = extra_currencies$_ dict:(HashmapE 32 (VarUInteger 32))
  let s2 ← s1.skipHashmapECellUnd
  return (grams, s2)

def Slice.skipStateInitCellUnd (s : Slice) : Except Excno Slice := do
  -- StateInit = _ fixed_prefix_length:(Maybe (## 5)) special:(Maybe TickTock)
  --              code:(Maybe ^Cell) data:(Maybe ^Cell) library:(Maybe ^Cell)
  let (hasFixed, s1) ← s.takeBitsAsNatCellUnd 1
  let s2 ←
    if hasFixed = 0 then
      pure s1
    else if s1.haveBits 5 then
      pure (s1.advanceBits 5)
    else
      throw .cellUnd
  let (hasSpecial, s3) ← s2.takeBitsAsNatCellUnd 1
  let s4 ←
    if hasSpecial = 0 then
      pure s3
    else if s3.haveBits 2 then
      pure (s3.advanceBits 2)
    else
      throw .cellUnd
  let (hasCode, s5) ← s4.takeBitsAsNatCellUnd 1
  let s6 ←
    if hasCode = 0 then
      pure s5
    else if s5.haveRefs 1 then
      pure { s5 with refPos := s5.refPos + 1 }
    else
      throw .cellUnd
  let (hasData, s7) ← s6.takeBitsAsNatCellUnd 1
  let s8 ←
    if hasData = 0 then
      pure s7
    else if s7.haveRefs 1 then
      pure { s7 with refPos := s7.refPos + 1 }
    else
      throw .cellUnd
  let (hasLib, s9) ← s8.takeBitsAsNatCellUnd 1
  if hasLib = 0 then
    return s9
  else if s9.haveRefs 1 then
    return { s9 with refPos := s9.refPos + 1 }
  else
    throw .cellUnd

def Slice.prefixCell (start stop : Slice) : Cell :=
  Cell.mkOrdinary
    (start.cell.bits.extract start.bitPos stop.bitPos)
    (start.cell.refs.extract start.refPos stop.refPos)

structure SendMsgParsed where
  extMsg : Bool
  dest : Slice
  value : Int
  userFwdFee : Int
  extraFlagsLen : Nat
  haveExtraCurrencies : Bool
  haveInit : Bool
  initRef : Bool
  initInlineBits : Nat
  initRefs : Nat
  bodyRef : Bool
  bodyInlineBits : Nat
  bodyRefs : Nat
  deriving Repr

def natLenBits (n : Nat) : Nat :=
  if n = 0 then 0 else Nat.log2 n + 1

def Slice.countLeading (s : Slice) (b : Bool) : Nat :=
  -- `s.bitPos + k < size` ⇔ `k < size - s.bitPos` (also when `bitPos > size`: both never hold)
  countWhile (s.cell.bits.size - s.bitPos) (fun k => s.cell.bits[s.bitPos + k]! == b) 0

structure DictLabel where
  remainder : Slice
  len : Nat
  sameBit : Option Bool
  storedBits : Nat
  deriving Repr

/-- A cell loaded as a slice outside the VM (no library collections): an exotic cell is cell_und.
The default resolver of the dictionary functions. -/
def Cell.rejectSpecial (c : Cell) : Except Excno Cell :=
  if c.special then .error .cellUnd else .ok c

/-- A dictionary node: TON C++ loads every node via `load_cell_slice` (crypto/vm/cells/CellSlice.cpp,
`load_cell_slice_impl`), which `resolve` stands for: in the VM it replaces a library cell by the
root of its library and rejects any other exotic cell (cell_und, e.g. a pruned branch inside a
Merkle proof); the default `Cell.rejectSpecial` rejects every exotic cell. Gas for the load of
`cell` (the library cell, not its root) is charged by the callers, also on `.error`. -/
def parseDictLabel (cell : Cell) (maxLen : Nat) (resolve : Cell → Except Excno Cell := Cell.rejectSpecial) :
    Except Excno DictLabel := do
  let cell ← resolve cell
  let mut cs := Slice.ofCell cell
  if !cs.haveBits 2 then
    throw .cellUnd
  let p2 := bitsToNat (cs.readBits 2)
  match p2 with
  | 0 =>
      cs := cs.advanceBits 2
      return { remainder := cs, len := 0, sameBit := none, storedBits := 0 }
  | 1 =>
      -- hml_short: `0 1^len 0 <len bits>`
      cs := cs.advanceBits 1
      let lBits := cs.countLeading true
      if lBits > maxLen then
        throw .cellUnd
      if !cs.haveBits (2 * lBits + 1) then
        throw .cellUnd
      cs := cs.advanceBits (lBits + 1)
      return { remainder := cs, len := lBits, sameBit := none, storedBits := lBits }
  | 2 =>
      -- hml_long: `10 <lenBits bits len> <len bits>`
      let lenBits := natLenBits maxLen
      cs := cs.advanceBits 2
      let (lBits, cs') ← cs.takeBitsAsNatCellUnd lenBits
      if lBits > maxLen then
        throw .cellUnd
      if !cs'.haveBits lBits then
        throw .cellUnd
      return { remainder := cs', len := lBits, sameBit := none, storedBits := lBits }
  | 3 =>
      -- hml_same: `11b <lenBits bits len>`
      let lenBits := natLenBits maxLen
      if !cs.haveBits (3 + lenBits) then
        throw .cellUnd
      let (same3, cs3) ← cs.takeBitsAsNatCellUnd 3
      let sameBit := (same3 &&& 1) = 1
      let (lBits, cs') ← cs3.takeBitsAsNatCellUnd lenBits
      if lBits > maxLen then
        throw .cellUnd
      return { remainder := cs', len := lBits, sameBit := some sameBit, storedBits := 0 }
  | _ =>
      throw .cellUnd

def dictKeyBits? (idx : Int) (n : Nat) (unsigned : Bool) : Option BitString :=
  if n = 0 then
    if idx = 0 then some #[] else none
  else if unsigned then
    if idx < 0 then
      none
    else
      let u := idx.toNat
      if u ≥ (1 <<< n) then
        none
      else
        some (natToBits u n)
  else
    let half : Int := intPow2 (n - 1)
    if idx < -half ∨ idx ≥ half then
      none
    else
      match intToBitsTwos idx n with
      | .ok bs => some bs
      | .error _ => none

def dictLabelMatches (lbl : DictLabel) (key : BitString) (pos : Nat) : Bool :=
  if pos + lbl.len > key.size then
    false
  else
    match lbl.sameBit with
    | some b => allBelow lbl.len (fun i => key[pos + i]! == b)
    | none =>
        let bs := lbl.remainder.readBits lbl.len
        allBelow lbl.len (fun i => bs[i]! == key[pos + i]!)

def dictLabelBits (lbl : DictLabel) : BitString :=
  match lbl.sameBit with
  | some b => Array.replicate lbl.len b
  | none => lbl.remainder.readBits lbl.len

def dictValidateNodeExt (lbl : DictLabel) (remaining : Nat) : Except Excno Nat := do
  let rem0 : Nat := remaining - lbl.len
  -- Match C++ `LabelParser::validate_ext` (used by `Dictionary`):
  -- non-leaf nodes must keep exactly label payload bits and exactly two refs.
  if rem0 > 0 then
    if lbl.remainder.bitsRemaining != lbl.storedBits || lbl.remainder.refsRemaining != 2 then
      throw .dictErr
  return rem0

/-- Same as `dictValidateNodeExt` (identical result and errors), but also returns the fact
`rem0 ≤ remaining`. Used only to make the recursive dictionary walkers provably terminating. -/
def dictValidateNodeExtLe (lbl : DictLabel) (remaining : Nat) : Except Excno {r : Nat // r ≤ remaining} := do
  let rem0 : Nat := remaining - lbl.len
  if rem0 > 0 then
    if lbl.remainder.bitsRemaining != lbl.storedBits || lbl.remainder.refsRemaining != 2 then
      throw .dictErr
  return ⟨rem0, Nat.sub_le remaining lbl.len⟩

def bitsCommonPrefixLen (a b : BitString) : Nat :=
  let m : Nat := Nat.min a.size b.size
  countWhile m (fun k => a[k]! == b[k]!) 0

/-- The common prefix is never longer than the second string. -/
theorem bitsCommonPrefixLen_le_right (a b : BitString) : bitsCommonPrefixLen a b ≤ b.size := by
  have h := countWhile_le (Nat.min a.size b.size) (fun k => a[k]! == b[k]!) 0
  have h2 : Nat.min a.size b.size ≤ b.size := Nat.min_le_right _ _
  simp only [bitsCommonPrefixLen]
  omega

-- Total version: terminates because `pos` strictly increases and recursion stops at `key.size`.
/-- One step of the dictionary lookup. `rec` is the recursive call on the chosen child; it
receives proofs that the new position lies strictly beyond `pos` and not beyond `key.size`.
Body identical to the former recursive definition. -/
def dictLookupStep (key : BitString) (pos : Nat)
    (rec : Cell → (p : Nat) → pos < p → p ≤ key.size → Nat → Except Excno (Option Slice))
    (cell : Cell) (remaining : Nat) (resolve : Cell → Except Excno Cell := Cell.rejectSpecial) : Except Excno (Option Slice) := do
  let lbl ← parseDictLabel (resolve := resolve) cell remaining
  let rem0 ← dictValidateNodeExt lbl remaining
  if !dictLabelMatches lbl key pos then
    return none
  if rem0 = 0 then
    return some (lbl.remainder.advanceBits lbl.storedBits)
  else
    if h : pos + lbl.len ≥ key.size then
      return none
    else
      let nextPos : Nat := pos + lbl.len
      let sw : Bool := key[nextPos]!
      let child := lbl.remainder.cell.refs[if sw then 1 else 0]!
      rec child (nextPos + 1) (by omega) (by omega) (rem0 - 1)

/-- The lookup with an explicit step budget (structural recursion: kernel-reducible).
`dictLookupAuxF_fuel` proves that any budget above `key.size - pos` gives the same result, so
the budget-0 branch is never reached from `dictLookupAux`. -/
def dictLookupAuxF (resolve : Cell → Except Excno Cell := Cell.rejectSpecial) : Nat → Cell → BitString → Nat → Nat → Except Excno (Option Slice)
  | 0, _, _, _, _ => .ok none
  | f + 1, cell, key, pos, remaining =>
      dictLookupStep (resolve := resolve) key pos (fun c p _ _ r => dictLookupAuxF (resolve := resolve) f c key p r) cell remaining

def dictLookupAux (cell : Cell) (key : BitString) (pos remaining : Nat) (resolve : Cell → Except Excno Cell := Cell.rejectSpecial) : Except Excno (Option Slice) :=
  dictLookupAuxF (resolve := resolve) (key.size - pos + 1) cell key pos remaining

/-- **Budget independence.** Any budget larger than `key.size - pos` gives the same result. -/
theorem dictLookupAuxF_fuel (resolve : Cell → Except Excno Cell) (f g : Nat) (cell : Cell) (key : BitString) (pos remaining : Nat)
    (hf : key.size - pos < f) (hg : key.size - pos < g) :
    dictLookupAuxF (resolve := resolve) f cell key pos remaining = dictLookupAuxF (resolve := resolve) g cell key pos remaining := by
  induction f generalizing g cell pos remaining with
  | zero => omega
  | succ f ih =>
    cases g with
    | zero => omega
    | succ g =>
      simp only [dictLookupAuxF]
      congr 1
      funext c p hp hpk r
      exact ih g c p r (by omega) (by omega)

/-- The recursive equation of the lookup holds exactly (the budget never runs out). -/
theorem dictLookupAux_eq (resolve : Cell → Except Excno Cell) (cell : Cell) (key : BitString) (pos remaining : Nat) :
    dictLookupAux (resolve := resolve) cell key pos remaining =
      dictLookupStep (resolve := resolve) key pos (fun c p _ _ r => dictLookupAux (resolve := resolve) c key p r) cell remaining := by
  unfold dictLookupAux
  rw [show key.size - pos + 1 = (key.size - pos) + 1 from rfl, dictLookupAuxF]
  congr 1
  funext c p hp hpk r
  exact dictLookupAuxF_fuel resolve _ _ c key p r (by omega) (by omega)

def dictLookup (root : Option Cell) (key : BitString) (resolve : Cell → Except Excno Cell := Cell.rejectSpecial) : Except Excno (Option Slice) := do
  match root with
  | none => return none
  | some cell =>
      dictLookupAux (resolve := resolve) cell key 0 key.size

/-- C++ `lookup_library_in` (vm.cpp): the root stored under `hashBits` in a library collection
(a dictionary of 256-bit hashes to a reference to the root) if its hash matches. C++ runs the lookup
without a VM interface (`load_library`), so library cells inside the collection are not resolved;
any error reads as not found. -/
def lookupLibraryIn? (hashBits : BitString) (libCollection : Cell) : Option Cell :=
  match dictLookup (some libCollection) hashBits with
  | .error _ => none
  | .ok none => none
  | .ok (some val) =>
      if !val.haveRefs 1 then
        none
      else
        let root := val.cell.refs[val.refPos]!
        if Cell.hashBytes root == bitStringToBytesBE hashBits then some root else none

/-- C++ `load_cell_slice_impl` (cells/CellSlice.cpp) in a VM with the library collections `libs`
(global version >= 5): an ordinary cell loads as itself; a library cell (exotic type 2: the type
byte and a 256-bit hash) loads as the root of its library, which must not be exotic again (a
recursive library, a pruned branch, ...); a missing library and every other exotic cell are
cell_und. Only the library cell's load is charged, by the caller (`register_cell_load` runs
before the library is followed, not for its root). -/
def libraryResolver (libs : Array Cell) (c : Cell) : Except Excno Cell := do
  if !c.special then
    return c
  if c.bits.size != 8 + 256 || bitsToNat (c.bits.extract 0 8) != 2 then
    throw .cellUnd
  let hashBits : BitString := c.bits.extract 8 (8 + 256)
  match libs.findSome? (lookupLibraryIn? hashBits) with
  | some root => Cell.rejectSpecial root
  | none => throw .cellUnd

/-- One step of the lookup that also records the visited cells (for gas); structured like
`dictLookupStep`. Body identical to the former recursive definition. -/
def dictLookupWithCellsStep (key : BitString) (pos : Nat)
    (rec : Cell → (p : Nat) → pos < p → p ≤ key.size → Nat → Except Excno (Option Slice × Array Cell))
    (cell : Cell) (remaining : Nat) (resolve : Cell → Except Excno Cell := Cell.rejectSpecial) : Except Excno (Option Slice × Array Cell) := do
  let lbl ← parseDictLabel (resolve := resolve) cell remaining
  let rem0 ← dictValidateNodeExt lbl remaining
  if !dictLabelMatches lbl key pos then
    return (none, #[cell])
  if rem0 = 0 then
    return (some (lbl.remainder.advanceBits lbl.storedBits), #[cell])
  else
    if h : pos + lbl.len ≥ key.size then
      return (none, #[cell])
    else
      let nextPos : Nat := pos + lbl.len
      let sw : Bool := key[nextPos]!
      let child := lbl.remainder.cell.refs[if sw then 1 else 0]!
      match (← rec child (nextPos + 1) (by omega) (by omega) (rem0 - 1)) with
      | (res, cells) => return (res, #[cell] ++ cells)

def dictLookupAuxWithCellsF (resolve : Cell → Except Excno Cell := Cell.rejectSpecial) : Nat → Cell → BitString → Nat → Nat → Except Excno (Option Slice × Array Cell)
  | 0, cell, _, _, _ => .ok (none, #[cell])
  | f + 1, cell, key, pos, remaining =>
      dictLookupWithCellsStep (resolve := resolve) key pos (fun c p _ _ r => dictLookupAuxWithCellsF (resolve := resolve) f c key p r) cell remaining

def dictLookupAuxWithCells (cell : Cell) (key : BitString) (pos remaining : Nat) (resolve : Cell → Except Excno Cell := Cell.rejectSpecial) :
    Except Excno (Option Slice × Array Cell) :=
  dictLookupAuxWithCellsF (resolve := resolve) (key.size - pos + 1) cell key pos remaining

theorem dictLookupAuxWithCellsF_fuel (resolve : Cell → Except Excno Cell) (f g : Nat) (cell : Cell) (key : BitString) (pos remaining : Nat)
    (hf : key.size - pos < f) (hg : key.size - pos < g) :
    dictLookupAuxWithCellsF (resolve := resolve) f cell key pos remaining = dictLookupAuxWithCellsF (resolve := resolve) g cell key pos remaining := by
  induction f generalizing g cell pos remaining with
  | zero => omega
  | succ f ih =>
    cases g with
    | zero => omega
    | succ g =>
      simp only [dictLookupAuxWithCellsF]
      congr 1
      funext c p hp hpk r
      exact ih g c p r (by omega) (by omega)

theorem dictLookupAuxWithCells_eq (resolve : Cell → Except Excno Cell) (cell : Cell) (key : BitString) (pos remaining : Nat) :
    dictLookupAuxWithCells (resolve := resolve) cell key pos remaining =
      dictLookupWithCellsStep (resolve := resolve) key pos (fun c p _ _ r => dictLookupAuxWithCells (resolve := resolve) c key p r) cell remaining := by
  unfold dictLookupAuxWithCells
  rw [show key.size - pos + 1 = (key.size - pos) + 1 from rfl, dictLookupAuxWithCellsF]
  congr 1
  funext c p hp hpk r
  exact dictLookupAuxWithCellsF_fuel resolve _ _ c key p r (by omega) (by omega)

def dictLookupWithCells (root : Option Cell) (key : BitString) (resolve : Cell → Except Excno Cell := Cell.rejectSpecial) : Except Excno (Option Slice × Array Cell) := do
  match root with
  | none => return (none, #[])
  | some cell =>
      dictLookupAuxWithCells (resolve := resolve) cell key 0 key.size

/-- One step of collecting the cells visited by a lookup (for gas on the error path). Body
identical to the former recursive definition. -/
def dictLookupVisitedStep (key : BitString) (pos : Nat)
    (rec : Cell → (p : Nat) → pos < p → p ≤ key.size → Nat → Array Cell)
    (cell : Cell) (remaining : Nat) (resolve : Cell → Except Excno Cell := Cell.rejectSpecial) : Array Cell :=
  let here : Array Cell := #[cell]
  match parseDictLabel (resolve := resolve) cell remaining with
  | .error _ => here
  | .ok lbl =>
      let rem0 : Nat := remaining - lbl.len
      if rem0 = 0 then
        here
      else if lbl.remainder.bitsRemaining != lbl.storedBits || lbl.remainder.refsRemaining != 2 then
        here
      else if !dictLabelMatches lbl key pos then
        here
      else
        if h : pos + lbl.len ≥ key.size then
          here
        else
          let nextPos : Nat := pos + lbl.len
          let sw : Bool := key[nextPos]!
          let child := lbl.remainder.cell.refs[if sw then 1 else 0]!
          here ++ rec child (nextPos + 1) (by omega) (by omega) (rem0 - 1)

def dictLookupVisitedCellsAuxF (resolve : Cell → Except Excno Cell := Cell.rejectSpecial) : Nat → Cell → BitString → Nat → Nat → Array Cell
  | 0, cell, _, _, _ => #[cell]
  | f + 1, cell, key, pos, remaining =>
      dictLookupVisitedStep (resolve := resolve) key pos (fun c p _ _ r => dictLookupVisitedCellsAuxF (resolve := resolve) f c key p r) cell remaining

def dictLookupVisitedCellsAux (cell : Cell) (key : BitString) (pos remaining : Nat) (resolve : Cell → Except Excno Cell := Cell.rejectSpecial) : Array Cell :=
  dictLookupVisitedCellsAuxF (resolve := resolve) (key.size - pos + 1) cell key pos remaining

theorem dictLookupVisitedCellsAuxF_fuel (resolve : Cell → Except Excno Cell) (f g : Nat) (cell : Cell) (key : BitString) (pos remaining : Nat)
    (hf : key.size - pos < f) (hg : key.size - pos < g) :
    dictLookupVisitedCellsAuxF (resolve := resolve) f cell key pos remaining = dictLookupVisitedCellsAuxF (resolve := resolve) g cell key pos remaining := by
  induction f generalizing g cell pos remaining with
  | zero => omega
  | succ f ih =>
    cases g with
    | zero => omega
    | succ g =>
      simp only [dictLookupVisitedCellsAuxF]
      congr 1
      funext c p hp hpk r
      exact ih g c p r (by omega) (by omega)

theorem dictLookupVisitedCellsAux_eq (resolve : Cell → Except Excno Cell) (cell : Cell) (key : BitString) (pos remaining : Nat) :
    dictLookupVisitedCellsAux (resolve := resolve) cell key pos remaining =
      dictLookupVisitedStep (resolve := resolve) key pos (fun c p _ _ r => dictLookupVisitedCellsAux (resolve := resolve) c key p r) cell remaining := by
  unfold dictLookupVisitedCellsAux
  rw [show key.size - pos + 1 = (key.size - pos) + 1 from rfl, dictLookupVisitedCellsAuxF]
  congr 1
  funext c p hp hpk r
  exact dictLookupVisitedCellsAuxF_fuel resolve _ _ c key p r (by omega) (by omega)

def dictLookupVisitedCells (root : Option Cell) (key : BitString) (resolve : Cell → Except Excno Cell := Cell.rejectSpecial) : Array Cell :=
  match root with
  | none => #[]
  | some cell => dictLookupVisitedCellsAux (resolve := resolve) cell key 0 key.size

def dictMinMaxVisitedCellsAux (cell : Cell) (n pos : Nat) (firstBit restBit : Bool) (resolve : Cell → Except Excno Cell := Cell.rejectSpecial) : Array Cell :=
  let here : Array Cell := #[cell]
  match parseDictLabel (resolve := resolve) cell n with
  | .error _ => here
  | .ok lbl =>
      let rem0 : Nat := n - lbl.len
      if rem0 = 0 then
        here
      else if lbl.remainder.bitsRemaining != lbl.storedBits || lbl.remainder.refsRemaining != 2 then
        here
      else
        let posAfter : Nat := pos + lbl.len
        let bit : Bool := if posAfter = 0 then firstBit else restBit
        let child := lbl.remainder.cell.refs[if bit then 1 else 0]!
        here ++ dictMinMaxVisitedCellsAux (resolve := resolve) child (rem0 - 1) (posAfter + 1) firstBit restBit
termination_by n
decreasing_by all_goals (simp_wf; omega)

def dictMinMaxVisitedCells (root : Option Cell) (n : Nat) (fetchMax invertFirst : Bool) (resolve : Cell → Except Excno Cell := Cell.rejectSpecial) : Array Cell :=
  match root with
  | none => #[]
  | some cell =>
      let restBit : Bool := fetchMax
      let firstBit : Bool := restBit != invertFirst
      dictMinMaxVisitedCellsAux (resolve := resolve) cell n 0 firstBit restBit

inductive DictDeleteVisitStatus where
  | found
  | none
  | err
  deriving Inhabited

structure DictDeleteVisit where
  status : DictDeleteVisitStatus
  loaded : Array Cell
  deriving Inhabited

private def dictDeleteVisitedTraceAux (cell : Cell) (key : BitString) (pos remaining : Nat) (resolve : Cell → Except Excno Cell := Cell.rejectSpecial) :
    DictDeleteVisit :=
  let here : Array Cell := #[cell]
  match parseDictLabel (resolve := resolve) cell remaining with
  | .error _ =>
      { status := .err, loaded := here }
  | .ok lbl =>
      match dictValidateNodeExt lbl remaining with
      | .error _ =>
          { status := .err, loaded := here }
      | .ok rem0 =>
          if !dictLabelMatches lbl key pos then
            { status := .none, loaded := here }
          else if rem0 = 0 then
            { status := .found, loaded := here }
          else
            let nextPos : Nat := pos + lbl.len
            if h : nextPos ≥ key.size then
              { status := .err, loaded := here }
            else
              let swBit : Bool := key[nextPos]!
              let left0 := lbl.remainder.cell.refs[0]!
              let right0 := lbl.remainder.cell.refs[1]!
              let child0 : Cell := if swBit then right0 else left0
              let sibling0 : Cell := if swBit then left0 else right0
              let childTrace := dictDeleteVisitedTraceAux (resolve := resolve) child0 key (nextPos + 1) (rem0 - 1)
              match childTrace.status with
              | .err =>
                  -- Error while descending: sibling merge path is not reached.
                  { status := .err, loaded := here ++ childTrace.loaded }
              | .none =>
                  { status := .none, loaded := here ++ childTrace.loaded ++ #[sibling0] }
              | .found =>
                  { status := .found, loaded := here ++ childTrace.loaded ++ #[sibling0] }
termination_by key.size - pos
decreasing_by all_goals (simp_wf; omega)

def dictDeleteVisitedCells (root : Option Cell) (key : BitString) (resolve : Cell → Except Excno Cell := Cell.rejectSpecial) : Array Cell :=
  match root with
  | none => #[]
  | some cell => (dictDeleteVisitedTraceAux (resolve := resolve) cell key 0 key.size).loaded

def dictReplaceBuilderAuxWithCells (cell : Cell) (key : BitString) (pos remaining : Nat) (newVal : Builder) (resolve : Cell → Except Excno Cell := Cell.rejectSpecial) :
    Except Excno (Cell × Bool × Nat × Array Cell) := do
  let lbl ← parseDictLabel (resolve := resolve) cell remaining
  let ⟨rem0, hle⟩ ← dictValidateNodeExtLe lbl remaining
  if !dictLabelMatches lbl key pos then
    return (cell, false, 0, #[cell])
  if h0 : rem0 = 0 then
    let valueStart := lbl.remainder.advanceBits lbl.storedBits
    let prefixBits := cell.bits.take valueStart.bitPos
    let newBits := prefixBits ++ newVal.bits
    if newBits.size > 1023 || newVal.refs.size > 4 then
      throw .cellOv
    let newCell : Cell := Cell.mkOrdinary newBits newVal.refs
    return (newCell, true, 1, #[cell])
  else
    let nextPos : Nat := pos + lbl.len
    if nextPos ≥ key.size then
      return (cell, false, 0, #[cell])
    let sw : Bool := key[nextPos]!
    if cell.refs.size < 2 then
      throw .dictErr
    let left := cell.refs[0]!
    let right := cell.refs[1]!
    let (childNew, ok, created, loaded) ←
      if sw then
        dictReplaceBuilderAuxWithCells (resolve := resolve) right key (nextPos + 1) (rem0 - 1) newVal
      else
        dictReplaceBuilderAuxWithCells (resolve := resolve) left key (nextPos + 1) (rem0 - 1) newVal
    if !ok then
      return (cell, false, 0, #[cell] ++ loaded)
    let newRefs : Array Cell :=
      if sw then
        #[left, childNew]
      else
        #[childNew, right]
    let newCell : Cell := Cell.mkOrdinary cell.bits newRefs
    return (newCell, true, created + 1, #[cell] ++ loaded)
termination_by remaining
decreasing_by all_goals (simp_wf; omega)

def dictReplaceBuilderWithCells (root : Option Cell) (key : BitString) (newVal : Builder) (resolve : Cell → Except Excno Cell := Cell.rejectSpecial) :
    Except Excno (Option Cell × Bool × Nat × Array Cell) := do
  match root with
  | none => return (none, false, 0, #[])
  | some cell =>
      let (c', ok, created, loaded) ← dictReplaceBuilderAuxWithCells (resolve := resolve) cell key 0 key.size newVal
      return (some c', ok, created, loaded)

def bitsAllSame? (bs : BitString) : Option Bool :=
  if 0 < bs.size then
    let b0 := bs[0]!
    Id.run do
      let mut ok := true
      for i in [0:bs.size] do
        if bs[i]! != b0 then
          ok := false
      if ok then some b0 else none
  else
    none

def dictLabelEncodeSame (same : Bool) (len maxLen : Nat) : BitString :=
  let k : Nat := natLenBits maxLen
  if len > 1 && k < 2 * len - 1 then
    -- mode '11'
    natToBits (6 + (if same then 1 else 0)) 3 ++ natToBits len k
  else if k < len then
    -- mode '10'
    natToBits 2 2 ++ natToBits len k ++ Array.replicate len same
  else
    -- mode '0'
    #[false] ++ Array.replicate len true ++ #[false] ++ Array.replicate len same

def dictLabelEncode (labelBits : BitString) (len maxLen : Nat) : BitString :=
  if len = 0 then
    -- mode '0' with len=0: `0 0`
    #[false, false]
  else
    match bitsAllSame? (labelBits.take len) with
    | some b => dictLabelEncodeSame b len maxLen
    | none =>
        let k : Nat := natLenBits maxLen
        if k < len then
          -- mode '10'
          natToBits 2 2 ++ natToBits len k ++ labelBits.take len
        else
          -- mode '0'
          #[false] ++ Array.replicate len true ++ #[false] ++ labelBits.take len

def builderStoreBitsChecked (b : Builder) (bs : BitString) : Except Excno Builder := do
  if b.canExtendBy bs.size then
    return b.storeBits bs
  else
    throw .cellOv

def builderStoreRefChecked (b : Builder) (c : Cell) : Except Excno Builder := do
  if b.canExtendBy 0 1 then
    return { b with refs := b.refs.push c }
  else
    throw .cellOv

def builderAppendCellChecked (b : Builder) (c : Cell) : Except Excno Builder := do
  if b.canExtendBy c.bits.size c.refs.size then
    return { bits := b.bits ++ c.bits, refs := b.refs ++ c.refs }
  else
    throw .cellOv

def builderAppendBuilderChecked (b : Builder) (v : Builder) : Except Excno Builder := do
  if b.canExtendBy v.bits.size v.refs.size then
    return { bits := b.bits ++ v.bits, refs := b.refs ++ v.refs }
  else
    throw .cellOv

def dictMinMaxAuxWithCells (cell : Cell) (n pos : Nat) (firstBit restBit : Bool) (resolve : Cell → Except Excno Cell := Cell.rejectSpecial) :
    Except Excno (Slice × BitString × Array Cell) := do
  let lbl ← parseDictLabel (resolve := resolve) cell n
  let ⟨rem0, hle⟩ ← dictValidateNodeExtLe lbl n
  let labelBits := dictLabelBits lbl
  let payload := lbl.remainder.advanceBits lbl.storedBits
  if h0 : rem0 = 0 then
    return (payload, labelBits, #[cell])
  else
    let posAfter : Nat := pos + lbl.len
    let bit : Bool := if posAfter = 0 then firstBit else restBit
    let child := lbl.remainder.cell.refs[if bit then 1 else 0]!
    let (val, keyTail, loaded) ← dictMinMaxAuxWithCells (resolve := resolve) child (rem0 - 1) (posAfter + 1) firstBit restBit
    return (val, labelBits ++ #[bit] ++ keyTail, #[cell] ++ loaded)
termination_by n
decreasing_by all_goals (simp_wf; omega)

def dictMinMaxWithCells (root : Option Cell) (n : Nat) (fetchMax invertFirst : Bool) (resolve : Cell → Except Excno Cell := Cell.rejectSpecial) :
    Except Excno (Option (Slice × BitString) × Array Cell) := do
  match root with
  | none => return (none, #[])
  | some cell =>
      let restBit : Bool := fetchMax
      let firstBit : Bool := restBit != invertFirst
      let (val, keyBits, loaded) ← dictMinMaxAuxWithCells (resolve := resolve) cell n 0 firstBit restBit
      return (some (val, keyBits), loaded)

def dictNearestAuxWithCells (cell : Cell) (hint : BitString) (n pos : Nat) (allowEq : Bool)
    (firstBit restBit : Bool) (resolve : Cell → Except Excno Cell := Cell.rejectSpecial) : Except Excno (Option (Slice × BitString) × Array Cell) := do
  let lbl ← parseDictLabel (resolve := resolve) cell n
  let ⟨rem0, hle⟩ ← dictValidateNodeExtLe lbl n
  let labelBits := dictLabelBits lbl

  -- Compare the hint against the edge label.
  let pfxLen : Nat := bitsCommonPrefixLen labelBits (hint.take lbl.len)
  if pfxLen < lbl.len then
    let hintBit : Bool := hint[pfxLen]!
    let expectedBit : Bool := if pos = 0 ∧ pfxLen = 0 then firstBit else restBit
    if hintBit = expectedBit then
      return (none, #[cell])
    else
      let firstBit' : Bool := !firstBit
      let restBit' : Bool := !restBit
      let (val, keyBits, loadedMin) ← dictMinMaxAuxWithCells (resolve := resolve) cell n pos firstBit' restBit'
      return (some (val, keyBits), #[cell] ++ loadedMin)

  -- Label fully matches: recurse into child.
  let payload := lbl.remainder.advanceBits lbl.storedBits
  let posAfter : Nat := pos + lbl.len
  let hintRest : BitString := hint.extract lbl.len hint.size
  if h0 : rem0 = 0 then
    if allowEq then
      return (some (payload, labelBits), #[cell])
    else
      return (none, #[cell])
  else
    if hintRest.isEmpty then
      throw .dictErr
    let bit : Bool := hintRest[0]!
    let child := lbl.remainder.cell.refs[if bit then 1 else 0]!
    let hintChild : BitString := hintRest.extract 1 hintRest.size
    let (resChild, loadedChild) ← dictNearestAuxWithCells (resolve := resolve) child hintChild (rem0 - 1) (posAfter + 1) allowEq firstBit restBit
    match resChild with
    | some (val, keyTail) =>
        return (some (val, labelBits ++ #[bit] ++ keyTail), #[cell] ++ loadedChild)
    | none =>
        let expectedBit : Bool := if posAfter = 0 then firstBit else restBit
        if bit = expectedBit then
          return (none, #[cell] ++ loadedChild)
        else
          let altChild := lbl.remainder.cell.refs[if expectedBit then 1 else 0]!
          let firstBit' : Bool := !firstBit
          let restBit' : Bool := !restBit
          let (valAlt, keyAlt, loadedAlt) ← dictMinMaxAuxWithCells (resolve := resolve) altChild (rem0 - 1) (posAfter + 1) firstBit' restBit'
          return (some (valAlt, labelBits ++ #[expectedBit] ++ keyAlt), #[cell] ++ loadedChild ++ loadedAlt)
termination_by n
decreasing_by all_goals (simp_wf; omega)

def dictNearestWithCells (root : Option Cell) (hint : BitString) (fetchNext allowEq invertFirst : Bool) (resolve : Cell → Except Excno Cell := Cell.rejectSpecial) :
    Except Excno (Option (Slice × BitString) × Array Cell) := do
  match root with
  | none => return (none, #[])
  | some cell =>
      let restBit : Bool := fetchNext
      let firstBit : Bool := restBit != invertFirst
      dictNearestAuxWithCells (resolve := resolve) cell hint hint.size 0 allowEq firstBit restBit

inductive DictNearestVisitStatus where
  | found
  | none
  | err
  deriving Inhabited

structure DictNearestVisit where
  status : DictNearestVisitStatus
  loaded : Array Cell
  deriving Inhabited

private def dictNearestVisitedTraceAux (cell : Cell) (hint : BitString) (n pos : Nat) (allowEq : Bool)
    (firstBit restBit : Bool) (resolve : Cell → Except Excno Cell := Cell.rejectSpecial) : DictNearestVisit :=
  let here : Array Cell := #[cell]
  match parseDictLabel (resolve := resolve) cell n with
  | .error _ =>
      { status := .err, loaded := here }
  | .ok lbl =>
      let rem0 : Nat := n - lbl.len
      if rem0 > 0 && (lbl.remainder.bitsRemaining != lbl.storedBits || lbl.remainder.refsRemaining != 2) then
        { status := .err, loaded := here }
      else
        let labelBits : BitString := dictLabelBits lbl
        let pfxLen : Nat := bitsCommonPrefixLen labelBits (hint.take lbl.len)
        if pfxLen < lbl.len then
          let hintBit : Bool := hint[pfxLen]!
          let expectedBit : Bool := if pos = 0 ∧ pfxLen = 0 then firstBit else restBit
          if hintBit = expectedBit then
            { status := .none, loaded := here }
          else
            let firstBit' : Bool := !firstBit
            let restBit' : Bool := !restBit
            let loadedMin : Array Cell := dictMinMaxVisitedCellsAux (resolve := resolve) cell n pos firstBit' restBit'
            match dictMinMaxAuxWithCells (resolve := resolve) cell n pos firstBit' restBit' with
            | .ok _ =>
                -- Includes a second visit of this node (reload) via `loadedMin`.
                { status := .found, loaded := here ++ loadedMin }
            | .error _ =>
                { status := .err, loaded := here ++ loadedMin }
        else if rem0 = 0 then
          { status := (if allowEq then .found else .none), loaded := here }
        else
          let hintRest : BitString := hint.extract lbl.len hint.size
          if hintRest.isEmpty then
            { status := .err, loaded := here }
          else
            let posAfter : Nat := pos + lbl.len
            let bit : Bool := hintRest[0]!
            let child := lbl.remainder.cell.refs[if bit then 1 else 0]!
            let hintChild : BitString := hintRest.extract 1 hintRest.size
            let childTrace :=
              dictNearestVisitedTraceAux (resolve := resolve) child hintChild (rem0 - 1) (posAfter + 1) allowEq firstBit restBit
            match childTrace.status with
            | .err =>
                { status := .err, loaded := here ++ childTrace.loaded }
            | .found =>
                { status := .found, loaded := here ++ childTrace.loaded }
            | .none =>
                let expectedBit : Bool := if posAfter = 0 then firstBit else restBit
                if bit = expectedBit then
                  { status := .none, loaded := here ++ childTrace.loaded }
                else
                  let altChild := lbl.remainder.cell.refs[if expectedBit then 1 else 0]!
                  let firstBit' : Bool := !firstBit
                  let restBit' : Bool := !restBit
                  let loadedAlt : Array Cell :=
                    dictMinMaxVisitedCellsAux (resolve := resolve) altChild (rem0 - 1) (posAfter + 1) firstBit' restBit'
                  match dictMinMaxAuxWithCells (resolve := resolve) altChild (rem0 - 1) (posAfter + 1) firstBit' restBit' with
                  | .ok _ =>
                      { status := .found, loaded := here ++ childTrace.loaded ++ loadedAlt }
                  | .error _ =>
                      { status := .err, loaded := here ++ childTrace.loaded ++ loadedAlt }
termination_by n
decreasing_by all_goals (simp_wf; omega)

def dictNearestVisitedCells (root : Option Cell) (hint : BitString) (fetchNext allowEq invertFirst : Bool) (resolve : Cell → Except Excno Cell := Cell.rejectSpecial) :
    Array Cell :=
  match root with
  | none => #[]
  | some cell =>
      let restBit : Bool := fetchNext
      let firstBit : Bool := restBit != invertFirst
      (dictNearestVisitedTraceAux (resolve := resolve) cell hint hint.size 0 allowEq firstBit restBit).loaded

def dictDeleteAuxWithCells (cell : Cell) (key : BitString) (pos remaining : Nat) (resolve : Cell → Except Excno Cell := Cell.rejectSpecial) :
    Except Excno (Option Slice × Option Cell × Nat × Array Cell) := do
  let lbl ← parseDictLabel (resolve := resolve) cell remaining
  let ⟨rem0, hle⟩ ← dictValidateNodeExtLe lbl remaining
  if !dictLabelMatches lbl key pos then
    return (none, some cell, 0, #[cell])
  let payload := lbl.remainder.advanceBits lbl.storedBits
  if h0 : rem0 = 0 then
    -- Delete leaf.
    return (some payload, none, 0, #[cell])
  else
    let nextPos : Nat := pos + lbl.len
    let swBit : Bool := key[nextPos]!
    let left0 := lbl.remainder.cell.refs[0]!
    let right0 := lbl.remainder.cell.refs[1]!
    let child0 := if swBit then right0 else left0
    let (oldVal?, childNew?, createdChild, loadedChild) ← dictDeleteAuxWithCells (resolve := resolve) child0 key (nextPos + 1) (rem0 - 1)
    match oldVal? with
    | none =>
        -- Not found in subtree: unchanged.
        return (none, some cell, 0, #[cell] ++ loadedChild)
    | some oldVal =>
        match childNew? with
        | some childNew =>
            -- Both children present: rebuild fork with updated child.
            let newRefs : Array Cell := if swBit then #[left0, childNew] else #[childNew, right0]
            let newCell : Cell := Cell.mkOrdinary cell.bits newRefs
            return (some oldVal, some newCell, createdChild + 1, #[cell] ++ loadedChild)
        | none =>
            -- One child removed: merge current edge with the surviving child.
            let survivorBit : Bool := !swBit
            let survivor : Cell := if swBit then left0 else right0
            let lbl2 ← parseDictLabel (resolve := resolve) survivor (rem0 - 1)
            let _ ← dictValidateNodeExt lbl2 (rem0 - 1)
            let childLabelBits := dictLabelBits lbl2
            let combinedLabelBits : BitString := dictLabelBits lbl ++ #[survivorBit] ++ childLabelBits
            let combinedLen : Nat := lbl.len + 1 + lbl2.len
            let enc : BitString := dictLabelEncode combinedLabelBits combinedLen remaining
            let payload2 := lbl2.remainder.advanceBits lbl2.storedBits
            let payloadCell2 : Cell := payload2.toCellRemaining
            let b0 ← builderStoreBitsChecked Builder.empty enc
            let b1 ← builderAppendCellChecked b0 payloadCell2
            return (some oldVal, some b1.finalize, createdChild + 1, #[cell] ++ loadedChild ++ #[survivor])
termination_by remaining
decreasing_by all_goals (simp_wf; omega)

def dictDeleteWithCells (root : Option Cell) (key : BitString) (resolve : Cell → Except Excno Cell := Cell.rejectSpecial) :
    Except Excno (Option Slice × Option Cell × Nat × Array Cell) := do
  match root with
  | none => return (none, none, 0, #[])
  | some cell =>
      dictDeleteAuxWithCells (resolve := resolve) cell key 0 key.size

def dictCommonPrefixLen (lbl : DictLabel) (key : BitString) : Nat :=
  let l := lbl.len
  match lbl.sameBit with
  | some b =>
      countWhile (Nat.min l key.size) (fun k => key[k]! == b) 0
  | none =>
      let bs := lbl.remainder.readBits l
      countWhile (Nat.min l key.size) (fun k => bs[k]! == key[k]!) 0

def dictSetGenAuxWithCells (root : Option Cell) (key : BitString)
    (storeVal : Builder → Except Excno Builder) (mode : DictSetMode) (resolve : Cell → Except Excno Cell := Cell.rejectSpecial) :
    Except Excno (Option Cell × Bool × Nat × Array Cell) := do
  let n : Nat := key.size
  match root with
  | none =>
      if mode == .replace then
        return (none, false, 0, #[])
      let enc : BitString := dictLabelEncode key n n
      let b0 := Builder.empty
      let b1 ← builderStoreBitsChecked b0 enc
      let b2 ← storeVal b1
      return (some b2.finalize, true, 1, #[])
  | some cell =>
      let lbl ← parseDictLabel (resolve := resolve) cell n
      let ⟨rem0, hle⟩ ← dictValidateNodeExtLe lbl n
      let pfxLen : Nat := dictCommonPrefixLen lbl key
      if pfxLen < lbl.len then
        if mode == .replace then
          return (some cell, false, 0, #[cell])

        -- Insert a new fork inside the current edge.
        let m : Nat := n - pfxLen - 1
        let keySuffix : BitString := key.extract (pfxLen + 1) n

        -- New leaf for the inserted key.
        let enc1 : BitString := dictLabelEncode keySuffix m m
        let b1 ← builderStoreBitsChecked Builder.empty enc1
        let b1 ← storeVal b1
        let cNew := b1.finalize

        -- Lower part of the old edge.
        let t : Nat := lbl.len - pfxLen - 1
        let oldLabelBits : BitString :=
          match lbl.sameBit with
          | some b => Array.replicate lbl.len b
          | none => lbl.remainder.readBits lbl.len
        let oldSuffix : BitString := oldLabelBits.extract (pfxLen + 1) lbl.len
        let payloadSlice : Slice := lbl.remainder.advanceBits lbl.storedBits
        let payloadCell : Cell := payloadSlice.toCellRemaining
        let enc2 : BitString := dictLabelEncode oldSuffix t m
        let b2 ← builderStoreBitsChecked Builder.empty enc2
        let b2 ← builderAppendCellChecked b2 payloadCell
        let cOld := b2.finalize

        -- Fork node with the shared prefix.
        let prefBits : BitString := key.take pfxLen
        let encF : BitString := dictLabelEncode prefBits pfxLen n
        let bF ← builderStoreBitsChecked Builder.empty encF
        let swBit : Bool := key[pfxLen]!
        let (left, right) := if swBit then (cOld, cNew) else (cNew, cOld)
        let bF ← builderStoreRefChecked bF left
        let bF ← builderStoreRefChecked bF right
        return (some bF.finalize, true, 3, #[cell])

      if h0 : rem0 = 0 then
        -- Leaf node: key matches the whole label.
        if mode == .add then
          return (some cell, false, 0, #[cell])
        let enc : BitString := dictLabelEncode key n n
        let b0 ← builderStoreBitsChecked Builder.empty enc
        let b0 ← storeVal b0
        return (some b0.finalize, true, 1, #[cell])

      else
        -- Fork node: recurse into the selected child.
        let swBit : Bool := key[lbl.len]!
        let childKey : BitString := key.extract (lbl.len + 1) n
        let left0 := lbl.remainder.cell.refs[0]!
        let right0 := lbl.remainder.cell.refs[1]!
        if swBit then
          let (rightNew?, ok, created, loaded) ← dictSetGenAuxWithCells (resolve := resolve) (some right0) childKey storeVal mode
          if !ok then
            return (some cell, false, 0, #[cell] ++ loaded)
          match rightNew? with
          | none => throw .dictErr
          | some rightNew =>
              let labelBits : BitString := key.take lbl.len
              let enc : BitString := dictLabelEncode labelBits lbl.len n
              let b ← builderStoreBitsChecked Builder.empty enc
              let b ← builderStoreRefChecked b left0
              let b ← builderStoreRefChecked b rightNew
              return (some b.finalize, true, created + 1, #[cell] ++ loaded)
        else
          let (leftNew?, ok, created, loaded) ← dictSetGenAuxWithCells (resolve := resolve) (some left0) childKey storeVal mode
          if !ok then
            return (some cell, false, 0, #[cell] ++ loaded)
          match leftNew? with
          | none => throw .dictErr
          | some leftNew =>
              let labelBits : BitString := key.take lbl.len
              let enc : BitString := dictLabelEncode labelBits lbl.len n
              let b ← builderStoreBitsChecked Builder.empty enc
              let b ← builderStoreRefChecked b leftNew
              let b ← builderStoreRefChecked b right0
              return (some b.finalize, true, created + 1, #[cell] ++ loaded)
termination_by key.size
decreasing_by all_goals (simp_wf; have hn : n = Array.size key := rfl; omega)

/-- The nodes on the path of `key` in a dictionary with `key.size`-bit keys: from `root` down to the
leaf of `key`, or to where the path ends. For the result of a set operation for `key`, the nodes it
created along the path. -/
def dictKeyPath (root : Cell) (key : BitString) : Array Cell :=
  go (key.size + 1) root 0 #[]
where
  go : Nat → Cell → Nat → Array Cell → Array Cell
    | 0, _, _, acc => acc
    | fuel + 1, cell, pos, acc =>
        let acc := acc.push cell
        match parseDictLabel cell (key.size - pos) with
        | .error _ => acc
        | .ok lbl =>
            let pos' := pos + lbl.len
            if pos' ≥ key.size then acc
            else
              match lbl.remainder.cell.refs[if key[pos']! then 1 else 0]? with
              | some child => go fuel child (pos' + 1) acc
              | none => acc

/-- `dictKeyPath` in a prefix dictionary with keys of at most `n` bits: a node is a label, then 0 and
the value (a leaf) or 1 and two references (a fork). -/
def pfxDictKeyPath (root : Cell) (key : BitString) (n : Nat) : Array Cell :=
  go (key.size + 1) root 0 n #[]
where
  go : Nat → Cell → Nat → Nat → Array Cell → Array Cell
    | 0, _, _, _, acc => acc
    | fuel + 1, cell, pos, n, acc =>
        let acc := acc.push cell
        match parseDictLabel cell n with
        | .error _ => acc
        | .ok lbl =>
            let payload := lbl.remainder.advanceBits lbl.storedBits
            let pos' := pos + lbl.len
            if !payload.haveBits 1 || !(payload.readBits 1)[0]! || pos' ≥ key.size || n < lbl.len + 1 then acc
            else
              match payload.cell.refs[if key[pos']! then 1 else 0]? with
              | some child => go fuel child (pos' + 1) (n - lbl.len - 1) acc
              | none => acc

def dictSetRefWithCells (root : Option Cell) (key : BitString) (valRef : Cell) (mode : DictSetMode) (resolve : Cell → Except Excno Cell := Cell.rejectSpecial) :
    Except Excno (Option Cell × Bool × Nat × Array Cell) := do
  let storeVal : Builder → Except Excno Builder :=
    fun b => builderStoreRefChecked b valRef
  dictSetGenAuxWithCells (resolve := resolve) root key storeVal mode

def dictSetSliceWithCells (root : Option Cell) (key : BitString) (val : Slice) (mode : DictSetMode) (resolve : Cell → Except Excno Cell := Cell.rejectSpecial) :
    Except Excno (Option Cell × Bool × Nat × Array Cell) := do
  let c := val.toCellRemaining
  let storeVal : Builder → Except Excno Builder :=
    fun b => builderAppendCellChecked b c
  dictSetGenAuxWithCells (resolve := resolve) root key storeVal mode

def dictSetBuilderWithCells (root : Option Cell) (key : BitString) (val : Builder) (mode : DictSetMode) (resolve : Cell → Except Excno Cell := Cell.rejectSpecial) :
    Except Excno (Option Cell × Bool × Nat × Array Cell) := do
  let storeVal : Builder → Except Excno Builder :=
    fun b => builderAppendBuilderChecked b val
  dictSetGenAuxWithCells (resolve := resolve) root key storeVal mode

def dictLookupSetGenAuxWithCells (root : Option Cell) (key : BitString)
    (storeVal : Builder → Except Excno Builder) (mode : DictSetMode) (resolve : Cell → Except Excno Cell := Cell.rejectSpecial) :
    Except Excno (Option Slice × Option Cell × Bool × Nat × Array Cell) := do
  let n : Nat := key.size
  match root with
  | none =>
      if mode == .replace then
        return (none, none, false, 0, #[])
      let enc : BitString := dictLabelEncode key n n
      let b0 := Builder.empty
      let b1 ← builderStoreBitsChecked b0 enc
      let b2 ← storeVal b1
      return (none, some b2.finalize, true, 1, #[])
  | some cell =>
      let lbl ← parseDictLabel (resolve := resolve) cell n
      let ⟨rem0, hle⟩ ← dictValidateNodeExtLe lbl n
      let pfxLen : Nat := dictCommonPrefixLen lbl key
      if pfxLen < lbl.len then
        if mode == .replace then
          return (none, some cell, false, 0, #[cell])

        -- Insert a new fork inside the current edge.
        let m : Nat := n - pfxLen - 1
        let keySuffix : BitString := key.extract (pfxLen + 1) n

        -- New leaf for the inserted key.
        let enc1 : BitString := dictLabelEncode keySuffix m m
        let b1 ← builderStoreBitsChecked Builder.empty enc1
        let b1 ← storeVal b1
        let cNew := b1.finalize

        -- Lower part of the old edge.
        let t : Nat := lbl.len - pfxLen - 1
        let oldLabelBits : BitString := dictLabelBits lbl
        let oldSuffix : BitString := oldLabelBits.extract (pfxLen + 1) lbl.len
        let payloadSlice : Slice := lbl.remainder.advanceBits lbl.storedBits
        let payloadCell : Cell := payloadSlice.toCellRemaining
        let enc2 : BitString := dictLabelEncode oldSuffix t m
        let b2 ← builderStoreBitsChecked Builder.empty enc2
        let b2 ← builderAppendCellChecked b2 payloadCell
        let cOld := b2.finalize

        -- Fork node with the shared prefix.
        let prefBits : BitString := key.take pfxLen
        let encF : BitString := dictLabelEncode prefBits pfxLen n
        let bF ← builderStoreBitsChecked Builder.empty encF
        let swBit : Bool := key[pfxLen]!
        let (left, right) := if swBit then (cOld, cNew) else (cNew, cOld)
        let bF ← builderStoreRefChecked bF left
        let bF ← builderStoreRefChecked bF right
        return (none, some bF.finalize, true, 3, #[cell])

      if h0 : rem0 = 0 then
        -- Leaf node.
        let oldVal : Slice := lbl.remainder.advanceBits lbl.storedBits
        if mode == .add then
          return (some oldVal, some cell, false, 0, #[cell])
        let enc : BitString := dictLabelEncode key n n
        let b0 ← builderStoreBitsChecked Builder.empty enc
        let b0 ← storeVal b0
        return (some oldVal, some b0.finalize, true, 1, #[cell])

      else
        -- Fork node: recurse into the selected child.
        let swBit : Bool := key[lbl.len]!
        let childKey : BitString := key.extract (lbl.len + 1) n
        let left0 := lbl.remainder.cell.refs[0]!
        let right0 := lbl.remainder.cell.refs[1]!
        if swBit then
          let (oldVal?, rightNew?, ok, created, loaded) ←
            dictLookupSetGenAuxWithCells (resolve := resolve) (some right0) childKey storeVal mode
          if !ok then
            return (oldVal?, some cell, false, 0, #[cell] ++ loaded)
          match rightNew? with
          | none => throw .dictErr
          | some rightNew =>
              let labelBits : BitString := key.take lbl.len
              let enc : BitString := dictLabelEncode labelBits lbl.len n
              let b ← builderStoreBitsChecked Builder.empty enc
              let b ← builderStoreRefChecked b left0
              let b ← builderStoreRefChecked b rightNew
              return (oldVal?, some b.finalize, true, created + 1, #[cell] ++ loaded)
        else
          let (oldVal?, leftNew?, ok, created, loaded) ←
            dictLookupSetGenAuxWithCells (resolve := resolve) (some left0) childKey storeVal mode
          if !ok then
            return (oldVal?, some cell, false, 0, #[cell] ++ loaded)
          match leftNew? with
          | none => throw .dictErr
          | some leftNew =>
              let labelBits : BitString := key.take lbl.len
              let enc : BitString := dictLabelEncode labelBits lbl.len n
              let b ← builderStoreBitsChecked Builder.empty enc
              let b ← builderStoreRefChecked b leftNew
              let b ← builderStoreRefChecked b right0
              return (oldVal?, some b.finalize, true, created + 1, #[cell] ++ loaded)
termination_by key.size
decreasing_by all_goals (simp_wf; have hn : n = Array.size key := rfl; omega)

def dictLookupSetRefWithCells (root : Option Cell) (key : BitString) (valRef : Cell) (mode : DictSetMode) (resolve : Cell → Except Excno Cell := Cell.rejectSpecial) :
    Except Excno (Option Slice × Option Cell × Bool × Nat × Array Cell) := do
  let storeVal : Builder → Except Excno Builder :=
    fun b => builderStoreRefChecked b valRef
  dictLookupSetGenAuxWithCells (resolve := resolve) root key storeVal mode

def dictLookupSetSliceWithCells (root : Option Cell) (key : BitString) (val : Slice) (mode : DictSetMode) (resolve : Cell → Except Excno Cell := Cell.rejectSpecial) :
    Except Excno (Option Slice × Option Cell × Bool × Nat × Array Cell) := do
  let c := val.toCellRemaining
  let storeVal : Builder → Except Excno Builder :=
    fun b => builderAppendCellChecked b c
  dictLookupSetGenAuxWithCells (resolve := resolve) root key storeVal mode

def dictLookupSetBuilderWithCells (root : Option Cell) (key : BitString) (val : Builder) (mode : DictSetMode) (resolve : Cell → Except Excno Cell := Cell.rejectSpecial) :
    Except Excno (Option Slice × Option Cell × Bool × Nat × Array Cell) := do
  let storeVal : Builder → Except Excno Builder :=
    fun b => builderAppendBuilderChecked b val
  dictLookupSetGenAuxWithCells (resolve := resolve) root key storeVal mode

/-- The `go` loop of `dictExtractPrefixSubdictWithCells`, lifted to the top level so that its
termination can be proved (measure: `prefixLen - m`). Behaviour is unchanged. -/
def dictExtractPrefixGo (keyBits : Nat) (pfx : BitString) (prefixLen : Nat) (removePrefix : Bool)
    (rootCell : Cell) (cell : Cell) (m : Nat) (loaded : Array Cell) (resolve : Cell → Except Excno Cell := Cell.rejectSpecial) :
    Except Excno (Option Cell × Bool × Nat × Array Cell) := do
  let loaded := loaded.push cell
  let remaining : Nat := keyBits - m
  let lbl ← parseDictLabel (resolve := resolve) cell remaining
  -- C++ parses every node with `LabelParser(..., label_mode())`, i.e. `validate_ext`: a fork
  -- node must have exactly the stored label bits and two references, otherwise `dict_err`.
  let _ ← dictValidateNodeExt lbl remaining
  let labelBits : BitString := dictLabelBits lbl
  let l : Nat := Nat.min (prefixLen - m) lbl.len
  let prefixPart : BitString := pfx.extract m (m + l)
  if bitsCommonPrefixLen labelBits prefixPart < l then
    return (none, true, 0, loaded)

  if hlt : m + lbl.len < prefixLen then
    -- proof-only fact (no runtime effect): needed for the termination argument
    have hdec : prefixLen - (m + lbl.len + 1) < prefixLen - m := by omega
    let m1 : Nat := m + lbl.len
    if m1 ≥ prefixLen then
      throw .fatal
    if !lbl.remainder.haveRefs 2 then
      throw .dictErr
    let swBit : Bool := pfx[m1]!
    let child := lbl.remainder.cell.refs[if swBit then 1 else 0]!
    dictExtractPrefixGo (resolve := resolve) keyBits pfx prefixLen removePrefix rootCell child (m1 + 1) loaded
  else
    let payload := lbl.remainder.advanceBits lbl.storedBits
    if !removePrefix then
      if m = 0 then
        return (some rootCell, false, 0, loaded)
      let combinedLabelBits : BitString := pfx.take m ++ labelBits
      let combinedLen : Nat := m + lbl.len
      let enc : BitString := dictLabelEncode combinedLabelBits combinedLen keyBits
      let b0 ← builderStoreBitsChecked Builder.empty enc
      let b1 ← builderAppendCellChecked b0 payload.toCellRemaining
      return (some b1.finalize, true, 1, loaded)
    else
      let newKeyBits : Nat := keyBits - prefixLen
      let keep : Nat := m + lbl.len - prefixLen
      let suffixBits : BitString := labelBits.drop (lbl.len - keep)
      let enc : BitString := dictLabelEncode suffixBits keep newKeyBits
      let b0 ← builderStoreBitsChecked Builder.empty enc
      let b1 ← builderAppendCellChecked b0 payload.toCellRemaining
      return (some b1.finalize, true, 1, loaded)
termination_by prefixLen - m
decreasing_by all_goals (simp_wf; omega)

def dictExtractPrefixSubdictWithCells (root : Option Cell) (keyBits : Nat)
    (pfx : BitString) (prefixLen : Nat) (removePrefix : Bool) (resolve : Cell → Except Excno Cell := Cell.rejectSpecial) :
    Except Excno (Option Cell × Bool × Nat × Array Cell) := do
  match root with
  | none =>
      return (none, false, 0, #[])
  | some rootCell =>
      if prefixLen = 0 then
        return (some rootCell, false, 0, #[])
      if prefixLen > keyBits then
        if removePrefix then
          throw .dictErr
        else
          return (none, true, 0, #[])

      dictExtractPrefixGo (resolve := resolve) keyBits pfx prefixLen removePrefix rootCell rootCell 0 #[]

end TvmLean
