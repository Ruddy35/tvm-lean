import TvmLean.Transaction.Extra

/-!
# Accounts

C++ `block::Account` (`crypto/block/transaction.cpp`, `transaction.h`): the state of an account as
the transaction reads it from a `ShardAccount`, built as the emulator does
(`emulator/emulator-extern.cpp`: the address from the account or, for `account_none`, from the
message; `Account::unpack` or `Account::init_new`).
-/

namespace TvmLean.Tx

inductive AccStatus where
  | nonexist | uninit | frozen | active | deleted
  deriving BEq, Repr, Inhabited

/-- The storage statistics (`storage_used$_ cells:(VarUInteger 7) bits:(VarUInteger 7)`). -/
structure StorageUsed where
  cells : Nat := 0
  bits : Nat := 0
  deriving BEq, Inhabited

structure Account where
  status : AccStatus := .nonexist
  origStatus : AccStatus := .nonexist
  isSpecial : Bool := false
  tick : Bool := false
  tock : Bool := false
  fixedPrefixLength : Nat := 0
  workchain : Int
  /-- 32 bits: the anycast rewrite prefix (only the first `addrRewriteLength` matter) -/
  addrRewrite : BitString
  addrRewriteLengthSet : Bool := false
  addrRewriteLength : Nat := 0
  /-- the address after the rewrite (the key in the shard) -/
  addr : BitString
  /-- the address in the account (the hash of its `StateInit`) -/
  addrOrig : BitString
  /-- `MsgAddressInt` as stored, and without anycast -/
  myAddr : Cell
  myAddrExact : Cell
  lastTransEndLt : Nat := 0
  lastTransLt : Nat := 0
  lastTransHash : BitString := natToBits 0 256
  blockLt : Nat := 0
  lastPaid : Nat := 0
  storageUsed : StorageUsed := {}
  storageDictHash : Option BitString := none
  balance : Currencies := { grams := 0 }
  duePayment : Nat := 0
  origTotalState : Cell
  totalState : Cell
  /-- `AccountStorage` (none for a new account) -/
  storage : Option Slice := none
  /-- the `StateInit` of an active account -/
  innerState : Option Slice := none
  stateHash : BitString
  code : Option Cell := none
  data : Option Cell := none
  library : Option Cell := none

namespace Account

def isMasterchain (a : Account) : Bool := a.workchain == -1

/-- `addr_std$10` (or `addr_var$11` outside -128..`stdLimit - 1`, by default -128..127) with the
optional anycast `pfx`, the workchain and `addr`. -/
def mkAddr (wc : Int) (anycast : Option BitString) (addr : BitString) (stdLimit : Int := 128) : Cell :=
  let w : W := {}
  let std := -128 ≤ wc ∧ wc < stdLimit
  let w := w.uint (if std then 2 else 3) 2
  let w := match anycast with
    | some pfx => ((w.bool true).uint pfx.size 5).bitStr pfx
    | none => w.bool false
  let w := if std then w.int wc 8 else (w.uint 256 9).int wc 32
  (w.bitStr addr).cell

/-- `Account::compute_my_addr(force = true)`: the address as stored (with the anycast prefix if
any, and `addr_orig`) and exact (`addr`, without anycast). `addr_std` only for the workchains -128..126
(`workchain < 127`, transaction.cpp:350): in workchain 127 both are `addr_var`. -/
def withMyAddr (a : Account) : Account :=
  let pfx := if a.addrRewriteLengthSet && a.addrRewriteLength > 0 then some (a.addrRewrite.extract 0 a.addrRewriteLength) else none
  { a with myAddr := mkAddr a.workchain pfx a.addrOrig 127, myAddrExact := mkAddr a.workchain none a.addr 127 }

/-- `Account::init_new`: a new account at the address `(wc, addr)`. -/
def initNew (wc : Int) (addr : BitString) : Account :=
  let exact := mkAddr wc none addr
  let noneState : Cell := (W.bool {} false).cell
  { workchain := wc, addr, addrOrig := addr, addrRewrite := addr.extract 0 32, myAddr := exact,
    myAddrExact := exact, origTotalState := noneState, totalState := noneState, stateHash := addr }

/-- `StateInit` (`tlb::unpack_exact`): fixed prefix length (`Maybe (## 5)`), tick-tock, code, data,
library. -/
structure StateInit where
  fixedPrefixLength : Option Nat
  special : Option (Bool × Bool)
  code : Option Cell
  data : Option Cell
  library : Option Cell

def Reader.stateInit : Reader StateInit := do
  let fpl ← Reader.maybe (Reader.uint 5)
  let special ← Reader.maybe (do return (← Reader.bool, ← Reader.bool))
  let code ← Reader.maybe Reader.ref
  let data ← Reader.maybe Reader.ref
  let library ← Reader.hashmapE
  return { fixedPrefixLength := fpl, special, code, data, library }

/-- `addr_std$10 anycast:(Maybe Anycast) workchain_id:int8 address:bits256` (an anycast depth is
`#<= 30`, at least 1). -/
def Reader.addrStd : Reader (Option BitString × Int × BitString) := do
  if (← Reader.uint 2) != 2 then Reader.fail
  let pfx ← Reader.maybe (do
    let depth ← Reader.uint 5
    if depth = 0 ∨ depth > 30 then Reader.fail
    Reader.bits depth)
  return (pfx, ← Reader.int 8, ← Reader.bits 256)

/-- `Account::unpack_address`: the account's `(wc, addr)` must be the stored address rewritten by
its anycast prefix (only `addr_std` is accepted). -/
def unpackAddress (a : Account) (pfx? : Option BitString) (wc : Int) (addrOrig : BitString) : Option Account := do
  let len := (pfx?.map (·.size)).getD 0
  if len > 0 then
    if (pfx?.getD #[]) ++ addrOrig.extract len 256 != a.addr then none
  else if a.addr != addrOrig then none
  if a.workchain != wc then none
  let a := { a with addrOrig, addrRewriteLengthSet := true, addrRewriteLength := len, addrRewrite := a.addr.extract 0 32 }
  -- without anycast `my_addr_exact` is the stored address and `compute_my_addr` (`Account::unpack`,
  -- transaction.cpp:341) keeps both; with it both are computed
  if len = 0 then
    let stored := mkAddr wc none addrOrig
    return { a with myAddr := stored, myAddrExact := stored }
  return withMyAddr a

/-- `Account::unpack_storage_info` (exact): storage used, the storage dict hash (`storage_extra_info$001`),
last paid, due payment. -/
def Reader.storageInfo : Reader (StorageUsed × Option BitString × Nat × Nat) := do
  -- `block::tlb::StorageInfo` (the `t_ShardAccount.validate_csr` of `Account::unpack`): amounts
  -- without a leading zero byte
  let cells ← Reader.varUIntStrict 7
  let bits ← Reader.varUIntStrict 7
  let tag ← Reader.uint 3
  let dictHash ← if tag == 1 then some <$> Reader.bits 256 else if tag == 0 then pure none else Reader.fail
  let lastPaid ← Reader.uint 32
  let due ← Reader.maybe Reader.gramsStrict
  return ({ cells, bits }, dictHash, lastPaid, due.getD 0)

/-- `Account::unpack` of a `ShardAccount` for the account at `(wc, addr)`. The validation of the whole
structure (`block::tlb::t_ShardAccount.validate_csr`, `block-parse.cpp`) is the exact read of each
part with the amounts of `block::tlb` (no leading zero byte, positive extra currencies). -/
def unpack (shardAccount : Cell) (wc : Int) (addr : BitString) (special : Bool) : Option Account := do
  let (acc, lastTransHash, lastTransLt) ← Reader.runExact (do
    return (← Reader.ref, ← Reader.bits 256, ← Reader.uint 64)) shardAccount
  let base := { initNew wc addr with isSpecial := special, lastTransLt, lastTransHash }
  let s := Slice.ofCell acc
  if !s.haveBits 1 then none
  if !(s.readBits 1)[0]! then
    -- account_none$0 (`init_new`)
    if s.bitsRemaining != 1 || s.refsRemaining != 0 then none
    return base
  -- account$1 addr:MsgAddressInt storage_stat:StorageInfo storage:AccountStorage
  let ((pfx, awc, addrOrig, (used, dictHash, lastPaid, due)), storage) ← (do
      let _ ← Reader.bits 1
      let (pfx, awc, addrOrig) ← Reader.addrStd
      return (pfx, awc, addrOrig, ← Reader.storageInfo)) s
  let a ← unpackAddress base pfx awc addrOrig
  let ((lastTransEnd, balance), state) ← (do return (← Reader.uint 64, ← Reader.currencies)) storage
  if !balance.valid then none
  if !(Nat.max lastTransEnd 1 > lastTransLt) then none
  let a := { a with totalState := acc, origTotalState := acc, lastTransEndLt := lastTransEnd, lastPaid,
                    storageUsed := used, storageDictHash := dictHash, duePayment := due, balance,
                    storage := some storage }
  if !state.haveBits 1 then none
  if (state.readBits 1)[0]! then
    -- account_active$1 _:StateInit (`unpack_state`, exact)
    let inner := state.advanceBits 1
    let si ← Reader.runExact Reader.stateInit inner.toCellRemaining
    let (tick, tock) := si.special.getD (false, false)
    return { a with status := .active, origStatus := .active, innerState := some inner,
                    fixedPrefixLength := si.fixedPrefixLength.getD 0, tick, tock, code := si.code, data := si.data,
                    library := si.library, stateHash := natToBits 0 256 }
  else if !state.haveBits 2 then none
  else if (state.readBits 2)[1]! then
    -- account_frozen$01 state_hash:bits256
    if state.bitsRemaining != 2 + 256 || state.refsRemaining != 0 then none
    return { a with status := .frozen, origStatus := .frozen, stateHash := (state.advanceBits 2).readBits 256 }
  else
    -- account_uninit$00: `forget_addr_rewrite_length`, the state hash is the address
    if state.bitsRemaining != 2 || state.refsRemaining != 0 then none
    return { a with status := .uninit, origStatus := .uninit, stateHash := a.addr, addrRewriteLengthSet := false,
                    addrRewriteLength := 0, addrOrig := a.addr, myAddr := a.myAddrExact,
                    addrRewrite := a.addr.extract 0 32 }

end Account

end TvmLean.Tx
