import TvmLean.Transaction.Config

/-!
# Extra currencies

`ExtraCurrencyCollection` is `HashmapE 32 (VarUInteger 32)`, kept as its root. C++ adds and subtracts
two of them with `dict_combine_with` (`crypto/vm/dict.cpp`), removes zero amounts with
`dict_filter` and clamps a reserve with `lookup_delete`/`set` (`block::CurrencyCollection`,
`crypto/block/block.cpp`). These keep every subtree they do not change and re-encode the labels of
the nodes they rebuild (`append_dict_label`), so the cells of the result depend on how the operands
were built: the operations here follow the C++ recursion node by node.

Amounts are read by `block::tlb::VarUInteger` (`crypto/block/block-parse.cpp`), which, unlike the
generated TL-B code, rejects a leading zero byte.
-/

namespace TvmLean.Tx

/-- How a dictionary operation fails: `combine` is the `CombineError` the operation catches (the
result is invalid), `malformed` a `VmError` of a malformed dictionary that C++ does not catch on
this path (not modelled). -/
inductive DictFail where
  | combine
  | malformed

abbrev DictM := Except DictFail

/-- `block::tlb::VarUInteger::as_integer_skip` with `len:(#< n)`: the amount, its first byte not zero,
and the rest of the slice. -/
def varUIntSkip? (n : Nat) (s : Slice) : Option (Nat × Slice) := do
  let lenBits := (n - 1).log2 + 1
  if !s.haveBits lenBits then none
  let len := bitsToNat (s.readBits lenBits)
  if len ≥ n then none
  let s := s.advanceBits lenBits
  if !s.haveBits (8 * len) then none
  let v := bitsToNat (s.readBits (8 * len))
  if len > 0 && v >>> (8 * len - 8) == 0 then none
  return (v, s.advanceBits (8 * len))

/-- `as_integer` of the whole slice. -/
def varUIntExact? (n : Nat) (s : Slice) : Option Nat := do
  let (v, r) ← varUIntSkip? n s
  if r.bitsRemaining != 0 || r.refsRemaining != 0 then none
  return v

/-- `VarUInteger::store_integer_value` (`len:(#< n)`, the fewest bytes): `none` if it does not fit. -/
def varUIntBits? (n v : Nat) : Option BitString :=
  let len := if v = 0 then 0 else (v.log2 + 8) / 8
  if len ≥ n then none else some ((({} : W).varUInt v n).bits)

/-- The label of node `c` of a dictionary with `n + skip`-bit keys after its first `skip` bits
(`LabelParser` with `n + skip`), and the payload after the label. -/
def dictNode (c : Cell) (n skip : Nat) : DictM (BitString × Slice) := do
  let lbl ← match parseDictLabel c (n + skip) with
    | .ok l => pure l
    | .error _ => throw .malformed
  if lbl.len < skip then throw .malformed
  return ((dictLabelBits lbl).extract skip lbl.len, lbl.remainder.advanceBits lbl.storedBits)

/-- The two children of a fork. -/
def dictChildren (p : Slice) : DictM (Cell × Cell) :=
  if p.haveRefs 2 then pure (p.cell.refs[p.refPos]!, p.cell.refs[p.refPos + 1]!) else throw .malformed

/-- `append_dict_label` of `label` (keys of `maxLen` bits), then the payload. -/
def dictMkNode (label : BitString) (maxLen : Nat) (payload : Slice) : DictM Cell := do
  let bits := dictLabelEncode label label.size maxLen ++ payload.readBits payload.bitsRemaining
  let refs := payload.cell.refs.extract payload.refPos payload.cell.refs.size
  if bits.size > 1023 || refs.size > 4 then throw .malformed
  return Cell.mkOrdinary bits refs

/-- `finish_create_fork`. -/
def dictFork (label : BitString) (maxLen : Nat) (l r : Cell) : Cell :=
  Cell.mkOrdinary (dictLabelEncode label label.size maxLen) #[l, r]

/-- A node with label `pfx` (keys of `n` bits) whose children became `r0` and `r1`: a fork if both
remain, else the remaining child with its edge merged into the node's (`lookup_delete`). -/
def dictJoin (pfx : BitString) (n : Nat) (r0 r1 : Option Cell) : DictM (Option Cell) :=
  match r0, r1 with
  | some a, some b => pure (some (dictFork pfx n a b))
  | none, none => pure none
  | some a, none => join a false
  | none, some b => join b true
where
  join (c : Cell) (bit : Bool) : DictM (Option Cell) := do
    let (lb, p) ← dictNode c (n - pfx.size - 1) 0
    return some (← dictMkNode (pfx.push bit ++ lb) n p)

/-- `DictionaryFixed::dict_combine_with`: `d1` and `d2` with `n`-bit keys left, the first `skip1`
(`skip2`) bits of their root labels already matched. `leaf` combines two values (`none`: the key
is dropped); mode bit 0: a key only in `d2` is an error, bit 1: a key only in `d1`. -/
def dictCombine (leaf : Slice → Slice → DictM (Option BitString)) (mode : Nat) :
    Nat → Option Cell → Option Cell → Nat → Nat → Nat → DictM (Option Cell)
  | 0, _, _, _, _, _ => throw .malformed
  | fuel + 1, d1, d2, n, skip1, skip2 =>
    match d1, d2 with
    | none, d2 => if mode &&& 1 != 0 && d2.isSome then throw .combine else pure d2
    | some d1, none => if mode &&& 2 != 0 then throw .combine else pure (some d1)
    | some d1, some d2 => do
      let (lb1, p1) ← dictNode d1 n skip1
      let (lb2, p2) ← dictNode d2 n skip2
      let l1 := lb1.size
      let l2 := lb2.size
      let c := bitsCommonPrefixLen lb1 lb2
      let pfx := lb1.extract 0 c
      if c < l1 && c < l2 then
        -- disjoint keys: both roots lose the first c + 1 bits of their labels
        if mode &&& 3 != 0 then throw .combine
        let a ← dictMkNode (lb1.extract (c + 1) l1) (n - c - 1) p1
        let b ← dictMkNode (lb2.extract (c + 1) l2) (n - c - 1) p2
        return some (if lb1[c]! then dictFork pfx n b a else dictFork pfx n a b)
      else if c == l1 && c == l2 then
        if c == n then
          match ← leaf p1 p2 with
          | none => return none
          | some v => return some (← dictMkNode lb1 n (Slice.ofCell (Cell.mkOrdinary v)))
        else
          let (a0, a1) ← dictChildren p1
          let (b0, b1) ← dictChildren p2
          let r0 ← dictCombine leaf mode fuel (some a0) (some b0) (n - c - 1) 0 0
          let r1 ← dictCombine leaf mode fuel (some a1) (some b1) (n - c - 1) 0 0
          dictJoin pfx n r0 r1
      else if c == l1 then
        -- d2 lies under one child of d1
        if mode &&& 2 != 0 then throw .combine
        let (a0, a1) ← dictChildren p1
        if !lb2[c]! then
          let r0 ← dictCombine leaf mode fuel (some a0) (some d2) (n - c - 1) 0 (skip2 + c + 1)
          dictJoin pfx n r0 (some a1)
        else
          let r1 ← dictCombine leaf mode fuel (some a1) (some d2) (n - c - 1) 0 (skip2 + c + 1)
          dictJoin pfx n (some a0) r1
      else
        -- d1 lies under one child of d2
        if mode &&& 1 != 0 then throw .combine
        let (b0, b1) ← dictChildren p2
        if !lb1[c]! then
          let r0 ← dictCombine leaf mode fuel (some d1) (some b0) (n - c - 1) (skip1 + c + 1) 0
          dictJoin pfx n r0 (some b1)
        else
          let r1 ← dictCombine leaf mode fuel (some d1) (some b1) (n - c - 1) (skip1 + c + 1) 0
          dictJoin pfx n (some b0) r1

/-- `DictionaryFixed::dict_filter` with `n`-bit keys left: the new subtree and whether it changed
(unchanged subtrees are kept as they are). `keep` decides on a value, counting the values seen. -/
def dictFilter (keep : Slice → StateT Nat DictM Bool) :
    Nat → Cell → Nat → StateT Nat DictM (Option Cell × Bool)
  | 0, _, _ => throw .malformed
  | fuel + 1, c, n => do
    let (lb, p) ← dictNode c n 0
    if lb.size == n then
      return if ← keep p then (some c, false) else (none, true)
    let (a0, a1) ← dictChildren p
    let (r0, ch0) ← dictFilter keep fuel a0 (n - lb.size - 1)
    let (r1, ch1) ← dictFilter keep fuel a1 (n - lb.size - 1)
    if !ch0 && !ch1 then return (some c, false)
    return (← dictJoin lb n r0 r1, true)

/-! ## `ExtraCurrencyCollection` -/

/-- `add_extra_currency`: `none` if the sum does not fit (`CombineError`). -/
def extraAdd (a b : Option Cell) : DictM (Option (Option Cell)) :=
  match a, b with
  | a, none => pure (some a)
  | none, b => pure (some b)
  | a, b =>
      let leaf (x y : Slice) : DictM (Option BitString) := do
        let some (u, _) := varUIntSkip? 32 x | throw .combine
        let some (v, _) := varUIntSkip? 32 y | throw .combine
        let some bits := varUIntBits? 32 (u + v) | throw .combine
        return some bits
      match dictCombine leaf 0 33 a b 32 0 0 with
      | .ok r => pure (some r)
      | .error .combine => pure none
      | .error .malformed => throw .malformed

/-- `sub_extra_currency`: `none` if `b` has a currency `a` lacks or more of one (`CombineError`);
currencies that become zero are removed. -/
def extraSub (a b : Option Cell) : DictM (Option (Option Cell)) :=
  match a, b with
  | a, none => pure (some a)
  | none, some _ => pure none
  | a, b =>
      let leaf (x y : Slice) : DictM (Option BitString) := do
        let some (u, _) := varUIntSkip? 32 x | throw .combine
        let some (v, _) := varUIntSkip? 32 y | throw .combine
        if u < v then throw .combine
        if u == v then return none
        let some bits := varUIntBits? 32 (u - v) | throw .combine
        return some bits
      match dictCombine leaf 1 33 a b 32 0 0 with
      | .ok r => pure (some r)
      | .error .combine => pure none
      | .error .malformed => throw .malformed

/-- `CurrencyCollection::remove_zero_extra_currencies`: `none` if there are more than `max`
currencies or an amount is not a `VarUInteger 32`. -/
def extraRemoveZero (root : Option Cell) (max : Nat) : DictM (Option (Option Cell)) :=
  match root with
  | none => pure (some none)
  | some c =>
      let keep (v : Slice) : StateT Nat DictM Bool := do
        let count := (← get) + 1
        set count
        if count > max then throw .combine
        let some x := varUIntExact? 32 v | throw .combine
        return x > 0
      match (dictFilter keep 33 c 32).run' 0 with
      | .ok (r, _) => pure (some r)
      | .error .combine => pure none
      | .error .malformed => throw .malformed

/-- The currencies of a collection in key order (`check_for_each`). -/
def extraEntries (root : Option Cell) : DictM (Array (BitString × Slice)) :=
  match dictEntries root 32 with
  | some es => pure es
  | none => throw .malformed

/-- `block::tlb::t_ExtraCurrencyCollection` validation (`HashmapE 32 (VarUIntegerPos 32)`): ordinary
cells, forks of exactly two references, amounts above zero without a leading zero byte, nothing after
them (`validate_ref`: the cell is read to its end). -/
def extraValidAux : Nat → Cell → Nat → Bool
  | 0, _, _ => false
  | fuel + 1, c, n =>
    if c.special then false
    else match dictNode c n 0 with
      | .error _ => false
      | .ok (lb, p) =>
          if lb.size == n then
            match varUIntExact? 32 p with
            | some x => x > 0
            | none => false
          else if p.bitsRemaining != 0 || p.refsRemaining != 2 then false
          else
            extraValidAux fuel p.cell.refs[p.refPos]! (n - lb.size - 1) &&
              extraValidAux fuel p.cell.refs[p.refPos + 1]! (n - lb.size - 1)

def extraValid (root : Option Cell) : Bool :=
  match root with
  | none => true
  | some c => extraValidAux 33 c 32

/-- `block::tlb::t_CurrencyCollection` validation. -/
def Currencies.valid (c : Currencies) : Bool := c.gramsCanonical && extraValid c.extra

/-- `CurrencyCollection::check_extra_currency_limit`. -/
def extraWithin (root : Option Cell) (max : Nat) : DictM Bool := do
  return (← extraEntries root).size ≤ max

/-- `CurrencyCollection::clamp` of the extra currencies of `reserve` by `avail` (`VarUIntegerPos 32`
amounts): a currency above what is available is lowered to it, or removed if none is. `none` if an
amount is not a positive `VarUInteger 32`. -/
def extraClamp (reserve avail : Option Cell) : DictM (Option (Option Cell)) := do
  let pos (v : Slice) : Option Nat := do
    let x ← varUIntExact? 32 v
    if x = 0 then none else some x
  let mut root := reserve
  for (key, v1) in ← extraEntries reserve do
    let some x1 := pos v1 | return none
    let v2 := dictGet avail key
    let mut x2 := 0
    if let some v := v2 then
      let some x := pos v | return none
      x2 := x
    if x1 > x2 then
      match v2 with
      | none =>
          match dictDeleteWithCells root key with
          | .ok (_, r, _, _) => root := r
          | .error _ => throw .malformed
      | some v =>
          let b : Builder := { bits := v.readBits v.bitsRemaining, refs := v.cell.refs.extract v.refPos v.cell.refs.size }
          match dictSetBuilderWithCells root key b .set with
          | .ok (r, _, _, _) => root := r
          | .error _ => throw .malformed
  return some root

end TvmLean.Tx
