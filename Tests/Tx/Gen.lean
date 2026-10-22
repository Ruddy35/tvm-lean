import Tests.Tx.Oracle

/-!
# Transaction cases

Ordinary transactions on the testnet configuration of the emulator's tests
(`emulator/test/emulator-tests.cpp`, 2024-06-27; `tools/txoracle/testnet-config.b64`) with the global
version (parameter 8) set to each version: accounts that are active (contracts below), uninitialized,
absent or frozen; internal and external messages, with a `StateInit` that deploys or not; balances
around the gas and storage limits.
-/

namespace Tests.Tx

open TvmLean TvmLean.Tx

/-- The configuration with parameter 8 set to `capabilities#c4 version caps`. -/
def withVersion (cfg : Cell) (version caps : Nat) : Cell :=
  let p8 := ((({} : W).uint 0xc4 8).uint version 32).uint caps 64 |>.cell
  match dictSetRefWithCells (some cfg) (natToBits 8 32) p8 .set with
  | .ok (some r, _, _, _) => r
  | _ => cfg

/-- The configuration with parameter 5 set to `burning_config#01` with the blackhole address `addr`. -/
def withBlackhole (cfg : Cell) (addr : BitString) : Cell :=
  let p5 := ((((({} : W).uint 1 8).bool true).bitStr addr).uint 1 32).uint 2 32 |>.cell
  match dictSetRefWithCells (some cfg) (natToBits 5 32) p5 .set with
  | .ok (some r, _, _, _) => r
  | _ => cfg

/-- The configuration with parameter 45 (`precompiled_contracts_config#c0`) listing the code hashes
with their `gas_usage`. -/
def withPrecompiled (cfg : Cell) (list : List (Cell × Nat)) : Cell := Id.run do
  let mut root : Option Cell := none
  for (code, g) in list do
    match dictSetBuilderWithCells root (bytesToBits code.hashBytes) { bits := natToBits 0xb0 8 ++ natToBits g 64, refs := #[] } .set with
    | .ok (r, _, _, _) => root := r
    | .error _ => pure ()
  let p45 := (({} : W).uint 0xc0 8).maybeRef root |>.cell
  match dictSetRefWithCells (some cfg) (natToBits 45 32) p45 .set with
  | .ok (some r, _, _, _) => r
  | _ => cfg

/-- The configuration with parameter 43 set to `size_limits_config_v3#03` (block.tlb:829-834) with
`max_transaction_library_loads` = `loads` and the other fields at the defaults of C++
`SizeLimitsConfig` (mc-config.h:394-417), which the testnet configuration, without parameter 43, has. -/
def withLibraryLoads (cfg : Cell) (loads : Option Nat) : Cell :=
  let w : W := (((((({} : W).uint 3 8).uint (2 ^ 21) 32).uint (2 ^ 13) 32).uint 1000 32).uint 512 16).uint 65535 32
  let w := ((((((w.uint 512 16).uint (2 ^ 16) 32).uint (2 ^ 11) 32).uint 256 32).uint 256 32).uint 2 32)
  let w := (w.uint 8 8).uint 26 32
  let w := match loads with
    | some n => (w.bool true).uint n 32
    | none => w.bool false
  let p43 := ((w.uint (2 ^ 21 * 5 / 2) 32).uint (2 ^ 13 * 5 / 2) 32).cell
  match dictSetRefWithCells (some cfg) (natToBits 43 32) p43 .set with
  | .ok (some r, _, _, _) => r
  | _ => cfg

/-- A library cell (exotic, type 2) for the cell `c`. -/
def libraryCellOf (c : Cell) : Cell :=
  { bits := natToBits 2 8 ++ bytesToBits c.hashBytes, refs := #[], special := true, levelMask := 0 }

/-- A library dictionary `HashmapE 256 X` of the cells `cs`, each value made by `val`. -/
def libDict (cs : List Cell) (val : Cell → Builder) : Option Cell := Id.run do
  let mut root : Option Cell := none
  for c in cs do
    match dictSetBuilderWithCells root (bytesToBits c.hashBytes) (val c) .set with
    | .ok (r, _, _, _) => root := r
    | .error _ => pure ()
  return root

/-- The account's libraries (`simple_lib$_ public:Bool root:^Cell`) and the emulator's (`^Cell`). -/
def simpleLibs (pub : Bool) (cs : List Cell) : Option Cell := libDict cs fun c => { bits := #[pub], refs := #[c] }
def globalLibsOf (cs : List Cell) : Option Cell := libDict cs fun c => { bits := #[], refs := #[c] }

/-- The code cell of `code`: `encodeCp0Code`, whose references (`PUSHREF`, `PUSHCONT` with
references, ...) become references of the cell. -/
def asm? (code : List Instr) : Except String Cell := do
  let mut bits : BitString := #[]
  let mut refs : Array Cell := #[]
  for i in code do
    match encodeCp0Code i with
    | .ok (b, r) =>
        bits := bits ++ b
        refs := refs ++ r
    | .error e => throw s!"cannot assemble {reprStr i}: {reprStr e}"
  if bits.size > 1023 || refs.size > 4 then throw "the code does not fit a cell"
  return Cell.mkOrdinary bits refs

/-- `asm?`, an empty cell if it fails: `programsAssemble` checks the fixed contracts. -/
def asm (code : List Instr) : Cell :=
  match asm? code with
  | .ok c => c
  | .error _ => Cell.empty

def stur (bits : Nat) : Instr := .stIntFixed true true false bits

/-- The contracts of active accounts. -/
def programs : List (String × List Instr) :=
  [("empty", []),
   ("accept", [.tonEnvOp .accept]),
   ("throw42", [.throw 42]),
   ("accept-throw", [.tonEnvOp .accept, .throw 42]),
   ("c7", [.newc, .tonEnvOp .now, stur 32, .tonEnvOp .blockLt, stur 64, .tonEnvOp .lTime, stur 64,
           .tonEnvOp .randSeed, stur 256, .tonEnvOp .balance, .tupleOp (.index 0), stur 128,
           .tonEnvOp .myAddr, .stSlice true false, .endc, .popCtr 4]),
   ("c7-v4", [.newc, .tonEnvOp .incomingValue, .tupleOp (.index 0), stur 128, .tonEnvOp .storageFees, stur 128,
              .tonEnvOp .myCode, .cryptoOp .hashCU, stur 256, .endc, .popCtr 4]),
   ("c7-v6", [.newc, .tonEnvOp .duePayment, stur 128, .tonEnvOp .getPrecompiledGas, .endc, .popCtr 4]),
   ("in-msg-params", [.newc, .tonEnvOp (.inMsgParam 4), stur 64, .tonEnvOp (.inMsgParam 7), stur 128, .endc,
                      .popCtr 4]),
   ("burn", [.pushInt (.num 300), .pushCont (Slice.ofCell Cell.empty), .contExt (.repeat false)]),
   ("loop", [.contExt (.againEnd false)]),
   ("accept-loop", [.tonEnvOp .accept, .contExt (.againEnd false)]),
   ("commit-throw", [.newc, .pushInt (.num 7), stur 8, .endc, .popCtr 4, .tonEnvOp .commit, .throw 5]),
   ("bad-c4", [.pushInt (.num 1), .popCtr 4]),
   ("deep-c4", [.newc, .endc] ++ (List.replicate 20 [.newc, .stref, .endc]).flatten ++ [.popCtr 4]),
   -- the extra currencies of the balance and of the inbound message (c7, version 4)
   ("c7-extra", [.tonEnvOp .balance, .tupleOp (.index 1), .newc, .stdict, .tonEnvOp .incomingValue,
                 .tupleOp (.index 1), .xchg0 1, .stdict, .endc, .popCtr 4]),
   ("in-msg-extra", [.tonEnvOp (.inMsgParam 8), .newc, .stdict, .endc, .popCtr 4])]

def addrStd (wc : Int) (a : BitString) : W := (((({} : W).uint 2 2).bool false).int wc 8).bitStr a

def other : BitString := natToBits 0x3333333333333333333333333333333333333333333333333333333333333333 256

/-- An amount of an extra currency (`VarUInteger 32`, the fewest bytes). -/
def amt (v : Nat) : BitString := (({} : W).varUInt v 32).bits

/-- `ExtraCurrencyCollection` with the given currencies and raw amounts, set in this order. -/
def extraOf (es : List (Nat × BitString)) : Option Cell := Id.run do
  let mut root : Option Cell := none
  for (k, v) in es do
    match dictSetBuilderWithCells root (natToBits k 32) { bits := v, refs := #[] } .set with
    | .ok (r, _, _, _) => root := r
    | .error _ => pure ()
  return root

/-- Extra currencies of the tests: 7, 100 and 4000000000 of them (amounts in units). -/
def extra2 : Option Cell := extraOf [(7, amt 500), (100, amt 1000000)]
def extra3 : Option Cell := extraOf [(7, amt 500), (100, amt 1000000), (4000000000, amt 3)]

/-- An outbound internal message as a contract proposes it (`MessageRelaxed`): source `addr_none`
or `src`, destination `(wc, dest)`, the value, the bounce flag, a body of `body` bits inline or in a
reference. -/
def relaxedInt (wc : Int) (dest : BitString) (value : Nat) (bounce : Bool := false) (body : BitString := #[])
    (bodyRef : Bool := false) (src : Option BitString := none) (fwdFee : Nat := 0) (extra : Option Cell := none) : Cell :=
  let w : W := (((({} : W).bool false).bool true).bool bounce).bool false
  let w := match src with | some a => w.bitStr (addrStd 0 a).bits | none => w.uint 0 2
  let w := (((w.bitStr (addrStd wc dest).bits).grams value).maybeRef extra).grams 0 |>.grams fwdFee
  let w := ((w.uint 0 64).uint 0 32).bool false
  if bodyRef then ((w.bool true).ref (Cell.mkOrdinary body)).cell else ((w.bool false).bitStr body).cell

/-- An outbound external message to `addr_extern` of 8 bits. -/
def relaxedExt (body : BitString := #[]) : Cell :=
  let w : W := ((((({} : W).uint 3 2).uint 0 2).uint 1 2).uint 8 9).uint 0x77 8
  (((((w.uint 0 64).uint 0 32).bool false).bool false).bitStr body).cell

def sendRaw (msg : Cell) (mode : Nat) : List Instr :=
  [.pushRef msg, .pushInt (.num (Int.ofNat mode)), .tonEnvOp .sendRawMsg]

def libCell : Cell := (({} : W).uint 0xc0de 16).cell

/-- An action list set directly in c5. -/
def setC5 (c : Cell) : List Instr := [.pushRef c, .popCtr 5]

/-- Contracts that make actions. -/
def actionPrograms : List (String × List Instr) :=
  -- fits the proposed message (with `addr_none` as the source), not the rewritten one: the body goes
  -- into a reference (`redoing`)
  let big := natToBits 0 600
  [("send", sendRaw (relaxedInt 0 other 10000000) 0),
   ("send-pay-fees", sendRaw (relaxedInt 0 other 10000000) 1),
   ("send-too-much", sendRaw (relaxedInt 0 other 5000000000) 0),
   ("send-too-much-skip", sendRaw (relaxedInt 0 other 5000000000) 2),
   ("send-too-much-bounce", sendRaw (relaxedInt 0 other 5000000000) 16),
   ("send-carry-in", sendRaw (relaxedInt 0 other 0) 64),
   ("send-all", sendRaw (relaxedInt 0 other 0) 128),
   ("send-all-delete", sendRaw (relaxedInt 0 other 0) 160),
   ("send-two", sendRaw (relaxedInt 0 other 10000000) 0 ++ sendRaw (relaxedInt 0 other 20000000 true) 1),
   ("send-ext", sendRaw (relaxedExt (natToBits 5 8)) 0),
   ("send-body-ref", sendRaw (relaxedInt 0 other 10000000 false (natToBits 7 300) true) 0),
   ("send-big-body", sendRaw (relaxedInt 0 other 10000000 false big) 0),
   ("send-bad-wc", sendRaw (relaxedInt 5 other 10000000) 0),
   ("send-bad-wc-skip", sendRaw (relaxedInt 5 other 10000000) 2),
   ("send-mc", sendRaw (relaxedInt (-1) other 10000000) 1),
   ("send-bad-src", sendRaw (relaxedInt 0 other 10000000 false #[] false (some other)) 0),
   ("send-fwd-fee", sendRaw (relaxedInt 0 other 10000000 false #[] false none 12345) 0),
   ("send-bad-mode", sendRaw (relaxedInt 0 other 10000000) 4),
   ("reserve", [.pushInt (.num 100000), .pushInt (.num 0), .tonEnvOp .rawReserve] ++ sendRaw (relaxedInt 0 other 0) 128),
   ("reserve-all-but", [.pushInt (.num 100000), .pushInt (.num 1), .tonEnvOp .rawReserve]),
   ("reserve-orig", [.pushInt (.num 100), .pushInt (.num 4), .tonEnvOp .rawReserve] ++ sendRaw (relaxedInt 0 other 0) 128),
   ("reserve-too-much", [.pushInt (.num 5000000000), .pushInt (.num 0), .tonEnvOp .rawReserve]),
   ("reserve-bounded", [.pushInt (.num 5000000000), .pushInt (.num 2), .tonEnvOp .rawReserve]),
   ("set-code", [.pushRef (asm [.tonEnvOp .accept]), .tonEnvOp .setCode]),
   ("set-lib", [.pushRef libCell, .pushInt (.num 1), .tonEnvOp .setLibCode]),
   ("set-public-lib", [.pushRef libCell, .pushInt (.num 2), .tonEnvOp .setLibCode]),
   ("c5-bad-tag", setC5 (Cell.mkOrdinary (natToBits 0xdeadbeef 32) #[Cell.empty])),
   ("c5-no-next", setC5 (Cell.mkOrdinary (natToBits 1 8))),
   ("c5-skip-bad-msg", setC5 (Cell.mkOrdinary (natToBits 0x0ec3c86d 32 ++ natToBits 2 8) #[Cell.empty, Cell.empty])),
   ("c5-bounce-bad-msg", setC5 (Cell.mkOrdinary (natToBits 0x0ec3c86d 32 ++ natToBits 16 8) #[Cell.empty, Cell.empty]))]

/-- `StateInit` with code and data. -/
def stateInit (code data : Cell) : Cell :=
  (((({} : W).bool false).bool false).maybeRef (some code) |>.maybeRef (some data) |>.bool false).cell

inductive AccState where
  | active (code data : Cell)
  | uninit
  | frozen (hash : BitString)
  | none

/-- `VarUInteger n` of `v` with one leading zero byte more than needed (the generated TL-B code reads
it, `block::tlb` does not). -/
def _root_.TvmLean.Tx.W.varUIntPadded (w : W) (v n : Nat) : W :=
  let len := (if v = 0 then 0 else (v.log2 + 8) / 8) + 1
  (w.uint len (n - 1).log2.succ).uint v (8 * len)

/-- A `ShardAccount` at `(wc, addr)` with the storage statistics C++ computes; `padded` stores one
amount with a leading zero byte: 1 the balance, 2 the cells used, 3 the due payment. An active state
may have a fixed prefix length `fpl`, the tick-tock flags `special` and no code (`noCode`, the code
cell unused); `dictHash` is stored as `storage_extra_info$001 dict_hash`; `usedBits` replaces the
bits of the storage statistics (C++ does not check them against the storage). -/
def mkAccount (wc : Int) (addr : BitString) (st : AccState) (bal lastPaid due lt : Nat) (extra : Option Cell := none)
    (padded : Nat := 0) (library : Option Cell := none) (anycast : Option BitString := none)
    (fpl : Option Nat := none) (special : Option (Bool × Bool) := none) (dictHash : Option BitString := none)
    (noCode : Bool := false) (usedBits : Option Nat := none) : Cell :=
  let stateBits : W :=
    match st with
    | .active code data =>
        let w : W := ({} : W).bool true
        let w := match fpl with | some d => (w.bool true).uint d 5 | none => w.bool false
        let w := match special with | some (tk, tc) => ((w.bool true).bool tk).bool tc | none => w.bool false
        ((w.maybeRef (if noCode then none else some code)).maybeRef (some data)).maybeRef library
    | .uninit => ({} : W).uint 0 2
    | .frozen h => (({} : W).uint 1 2).bitStr h
    | .none => {}
  let storage : W := (({} : W).uint lt 64)
  let storage := (if padded == 1 then storage.varUIntPadded bal 16 else storage.grams bal).maybeRef extra
  let storage := { storage with bits := storage.bits ++ stateBits.bits, refs := storage.refs ++ stateBits.refs }
  let sc := storage.cell
  let acc : Cell :=
    match st with
    | .none => (({} : W).bool false).cell
    | _ =>
        let (c, b) := cellsAndBits (collectCells sc.refs.toList)
        -- the stored address: `addr` itself, or with an anycast prefix (then `addr` is addr_orig)
        let w : W := (({} : W).bool true).bitStr (Account.mkAddr wc anycast addr).bits
        let w := if padded == 2 then w.varUIntPadded (c + 1) 7 else w.varUInt (c + 1) 7
        let w := w.varUInt (usedBits.getD (b + sc.bits.size)) 7
        let w := match dictHash with | some h => (w.uint 1 3).bitStr h | none => w.uint 0 3
        let w := w.uint lastPaid 32
        let w := if due > 0 then (if padded == 3 then (w.bool true).varUIntPadded due 16 else (w.bool true).grams due)
          else w.bool false
        (w.slice (Slice.ofCell sc)).cell
  ((({} : W).ref acc).uint 0 256).uint (if lt > 0 then lt - 1 else 0) 64 |>.cell

/-- An internal message to `(wc, dest)` from `src` (by default 0:2222..22), with an optional
`StateInit` in a reference and a body of `body` bits inline; `bounced` sets its bounced flag. -/
def intMsg (wc : Int) (dest : BitString) (value : Nat) (bounce : Bool) (init : Option Cell) (body : BitString)
    (extraFlags : Nat := 0) (bodyRefs : Array Cell := #[]) (extra : Option Cell := none) (padded : Nat := 0)
    (anycast : Option BitString := none)
    (src : Int × BitString := (0, natToBits 0x2222222222222222222222222222222222222222222222222222222222222222 256))
    (bounced : Bool := false) : Cell :=
  let w : W := (((({} : W).bool false).bool true).bool bounce).bool bounced
  let w := (w.bitStr (addrStd src.1 src.2).bits).bitStr (Account.mkAddr wc anycast dest).bits
  -- `padded`: one amount with a leading zero byte (1 the value, 2 extra_flags, 3 fwd_fee)
  let pad (k v : Nat) (w : W) : W := if padded == k then w.varUIntPadded v 16 else w.grams v
  let w := (((pad 1 value w).maybeRef extra) |> pad 2 extraFlags |> pad 3 0) |>.uint 2000 64 |>.uint 1700000100 32
  let w := match init with
    | some c => ((w.bool true).bool true).ref c
    | none => w.bool false
  { ((w.bool false).bitStr body) with refs := (w.bool false).refs ++ bodyRefs }.cell

/-- An external inbound message (`addr_none` source, no import fee). -/
def extMsg (wc : Int) (dest : BitString) (init : Option Cell) (body : BitString) (anycast : Option BitString := none) : Cell :=
  let w : W := ((({} : W).uint 2 2).uint 0 2).bitStr (Account.mkAddr wc anycast dest).bits |>.grams 0
  let w := match init with
    | some c => ((w.bool true).bool true).ref c
    | none => w.bool false
  ((w.bool false).bitStr body).cell

def seed : BitString := natToBits 0x5eed5eed 256

/-- Contracts that move extra currencies (the balance has `extra2`). -/
def extraPrograms : List (String × List Instr) :=
  let rsv (v : Nat) (e : Option Cell) (mode : Nat) : List Instr :=
    let d := (({} : W).maybeRef e).cell
    -- RAWRESERVEX: x D y
    [.pushInt (.num (Int.ofNat v)), .pushRef d, .ctos, .lddict true false, .pushInt (.num (Int.ofNat mode)),
     .tonEnvOp .rawReserveX]
  let one := extraOf [(7, amt 200)]
  let lz := extraOf [(7, natToBits 2 5 ++ natToBits 5 16)]
  [("x-send", sendRaw (relaxedInt 0 other 10000000 (extra := one)) 0),
   ("x-send-pay", sendRaw (relaxedInt 0 other 10000000 (extra := one)) 1),
   ("x-send-zero", sendRaw (relaxedInt 0 other 10000000 (extra := extraOf [(7, amt 0), (100, amt 5)])) 0),
   ("x-send-zero-only", sendRaw (relaxedInt 0 other 10000000 (extra := extraOf [(7, amt 0)])) 0),
   ("x-send-missing", sendRaw (relaxedInt 0 other 10000000 (extra := extraOf [(9, amt 1)])) 0),
   ("x-send-missing-skip", sendRaw (relaxedInt 0 other 10000000 (extra := extraOf [(9, amt 1)])) 2),
   ("x-send-too-much", sendRaw (relaxedInt 0 other 10000000 (extra := extraOf [(7, amt 501)])) 0),
   ("x-send-all-of-one", sendRaw (relaxedInt 0 other 10000000 (extra := extraOf [(7, amt 500)])) 0),
   ("x-send-three", sendRaw (relaxedInt 0 other 10000000 (extra := extraOf [(7, amt 1), (100, amt 1), (200, amt 0)])) 0),
   ("x-send-three-skip", sendRaw (relaxedInt 0 other 10000000 (extra := extraOf [(7, amt 1), (100, amt 1), (200, amt 1)])) 2),
   ("x-send-leading-zero", sendRaw (relaxedInt 0 other 10000000 (extra := lz)) 0),
   ("x-send-leading-zero-fees", sendRaw (relaxedInt 0 other 10000000 (extra := lz)) 1),
   ("x-send-all", sendRaw (relaxedInt 0 other 0) 128),
   ("x-send-all-extra", sendRaw (relaxedInt 0 other 0 (extra := one)) 128),
   ("x-send-all-delete", sendRaw (relaxedInt 0 other 0) 160),
   ("x-send-carry", sendRaw (relaxedInt 0 other 0) 64),
   ("x-send-carry-extra", sendRaw (relaxedInt 0 other 1000 (extra := one)) 65),
   ("x-send-two", sendRaw (relaxedInt 0 other 1000000 (extra := one)) 1 ++ sendRaw (relaxedInt 0 other 1000000 (extra := one)) 1),
   ("x-bounce-body", sendRaw (relaxedInt 0 other 10000000 (extra := one)) 0 ++ [.throw 77]),
   ("x-reserve", rsv 1000 one 0),
   ("x-reserve-all-but", rsv 1000 one 1),
   ("x-reserve-bounded", rsv 1000 (extraOf [(7, amt 900), (9, amt 1)]) 2),
   ("x-reserve-missing", rsv 1000 (extraOf [(9, amt 1)]) 0),
   ("x-reserve-orig", rsv 1000 one 4 ++ sendRaw (relaxedInt 0 other 0) 128),
   ("x-reserve-orig-minus", rsv 1000 one 12),
   ("x-reserve-orig-grams", rsv 1000 none 4 ++ sendRaw (relaxedInt 0 other 0) 128),
   ("x-reserve-then-delete", rsv 0 one 0 ++ sendRaw (relaxedInt 0 other 0) 160)]

/-- Extra currencies: in the balance, in the inbound message, in the actions, in a bounce, in the
storage phase. -/
def extraCases (mk : String → Cell → Cell → TxCase) (a : BitString) (data : Cell) : Array TxCase := Id.run do
  let mut out : Array TxCase := #[]
  let msgX := extraOf [(100, amt 5), (3, amt 77)]
  let msgSame := extraOf [(7, amt 1), (100, amt 2)]
  for (pname, prog) in (programs.filter fun (n, _) => n == "accept" || n == "throw42" || n.startsWith "c7" || n == "in-msg-extra") do
    for (xname, accX) in [("acc", extra2), ("acc3", extra3), ("noacc", none)] do
      for (mname, mX) in [("msg", msgX), ("msg-same", msgSame), ("nomsg", none)] do
        let acc := mkAccount 0 a (.active (asm prog) data) 1000000000 1700000000 0 1000 accX
        out := out.push (mk s!"x/{pname}/{xname}/{mname}" acc (intMsg 0 a 100000000 false none #[] (extra := mX)))
        out := out.push (mk s!"x/{pname}/{xname}/{mname}/bounce" acc (intMsg 0 a 100000000 true none (natToBits 3 8) (extra := mX)))
      out := out.push (mk s!"x/{pname}/{xname}/ext" (mkAccount 0 a (.active (asm prog) data) 1000000000 1700000000 0 1000 accX)
        (extMsg 0 a none #[]))
  for (pname, prog) in extraPrograms do
    for (bname, bal) in [("rich", 1000000000), ("poor", 3000000)] do
      let acc := mkAccount 0 a (.active (asm prog) data) bal 1700000000 0 1000 extra2
      out := out.push (mk s!"{pname}/{bname}/int" acc (intMsg 0 a 100000000 false none #[]))
      out := out.push (mk s!"{pname}/{bname}/int-extra" acc (intMsg 0 a 100000000 true none #[] (extra := msgX)))
      out := out.push (mk s!"{pname}/{bname}/ext" acc (extMsg 0 a none #[]))
  -- the new bounce format carries the original value
  out := out.push (mk "x/bounce-new" (mkAccount 0 a (.active (asm [.throw 42]) data) 1000000000 1700000000 0 1000)
    (intMsg 0 a 100000000 true none (natToBits 5 8) 1 #[] msgX))
  -- uninitialized and absent accounts get extra currencies; a large due keeps them
  out := out.push (mk "x/none" (mkAccount 0 a .none 0 0 0 0) (intMsg 0 a 100000000 false none #[] (extra := msgX)))
  out := out.push (mk "x/none-bounce" (mkAccount 0 a .none 0 0 0 0) (intMsg 0 a 100000000 true none #[] (extra := msgX)))
  out := out.push (mk "x/none-zero-grams" (mkAccount 0 a .none 0 0 0 0) (intMsg 0 a 0 false none #[] (extra := msgX)))
  out := out.push (mk "x/uninit-old" (mkAccount 0 a .uninit 5000 1600000000 0 1000 extra2) (intMsg 0 a 1000 false none #[]))
  out := out.push (mk "x/uninit-old-noextra" (mkAccount 0 a .uninit 5000 1600000000 0 1000) (intMsg 0 a 1000 false none #[]))
  out := out.push (mk "x/frozen-old" (mkAccount 0 a (.frozen (natToBits 77 256)) 5000 1600000000 0 1000 extra2)
    (intMsg 0 a 1000 false none #[]))
  out := out.push (mk "x/active-old" (mkAccount 0 a (.active (asm []) data) 5000 1600000000 0 1000 extra2)
    (intMsg 0 a 1000 false none #[]))
  -- before version 9 `original_balance` is the account's balance less the fees so far: below zero it is
  -- invalid and a reserve relative to it fails
  for (pname, prog) in (actionPrograms ++ extraPrograms).filter (fun (n, _) => (n.splitOn "reserve-orig").length > 1) do
    out := out.push (mk s!"{pname}/tiny-old" (mkAccount 0 a (.active (asm prog) data) 1000 1600000000 0 1000 extra2)
      (intMsg 0 a 100000000 false none #[]))
  return out

namespace LibLoads

def lib (k : Nat) : Cell := (({} : W).uint k 16).cell
def libA : Cell := lib 0xa1a1
def libB : Cell := lib 0xb2b2
def libC : Cell := lib 0xc3c3
/-- in no library collection -/
def missing : Cell := lib 0xdddd

def accept : Instr := .tonEnvOp .accept
def ctos (c : Cell) : List Instr := [.pushRef (libraryCellOf c), .ctos, .pop 0]
def xload (quiet : Bool) (c : Cell) : List Instr := [.pushRef (libraryCellOf c), .cellExt (.xload quiet)]
/-- `body` under `TRY`, its exception dropped -/
def tryLoad (body : List Instr) : List Instr := [.pushRefCont (asm body), .pushRefCont (asm [.drop2]), .try_]
/-- the depth of the stack in c4, committed -/
def saveDepth : List Instr := [.depth, .newc, .stIntFixed true false false 8, .endc, .popCtr 4, .tonEnvOp .commit]

/-- A dictionary with the keys 1 and 200 (8 bits): the node of key 1 is its first reference. -/
def dict : Cell := Id.run do
  let mut root : Option Cell := none
  for (k, v) in [(1, 0x11), (200, 0x22)] do
    if let .ok (r, _, _, _) := dictSetBuilderWithCells root (natToBits k 8) { bits := natToBits v 8, refs := #[] } .set then
      root := r
  return root.getD Cell.empty
def node1 : Cell := dict.refs[0]!
/-- `dict` with the node of key 1 as a library cell -/
def dictLibNode : Cell := { dict with refs := dict.refs.set! 0 (libraryCellOf node1) }
/-- DICTUGET -/
def dictGet (key : Nat) (root : Cell) : List Instr :=
  [.pushInt (.num key), .pushRef root, .pushInt (.num 8), .dictGet true true false]

def child : List Instr := ctos libB ++ ctos libA
def codeBody : List Instr := accept :: ctos libB ++ ctos libC
def callB : List Instr := [.pushInt (.num 7), .pop 0]
def callC : List Instr := [.pushInt (.num 8), .pop 0]
def head : List Instr := accept :: ctos libA
def tail : List Instr := ctos libB ++ ctos libC
def chainEnd : List Instr := [.pushInt (.num 9), .pop 0]
/-- a library cell whose library's root is a library cell again -/
def inner : Cell := libraryCellOf (asm chainEnd)
/-- a message for SENDMSG -/
def msg : Cell := relaxedInt 0 other 1000
/-- extra currencies for GETEXTRABALANCE -/
def extraDict : Cell := (extraOf [(7, amt 500)]).getD Cell.empty
/-- the extra currencies of the balance in c7 replaced by `root` -/
def setExtra (root : Cell) : List Instr :=
  [.pushCtr 7, .push 0, .tupleOp (.index 0), .push 0, .tupleOp (.index 7), .pushRef root, .tupleOp (.setIndex 1),
   .tupleOp (.setIndex 7), .tupleOp (.setIndex 0), .popCtr 7]

/-- The contracts (and the code of their parts). -/
def programs : List (String × List Instr) :=
  [("plain", [accept]),
   ("ctos3", accept :: ctos libA ++ ctos libB ++ ctos libC),
   ("ctos-again", accept :: ctos libA ++ ctos libA ++ ctos libB),
   ("missing", accept :: tryLoad (ctos missing) ++ ctos libA ++ ctos libB),
   ("after-refusal-cont", ctos libA ++ tryLoad (ctos libC) ++ ctos libB),
   ("after-refusal", accept :: ctos libA ++ tryLoad (ctos libB) ++
     [.callRef (Slice.ofCell (asm (ctos libA ++ tryLoad (ctos libC) ++ ctos libB)))]),
   ("xload", accept :: xload false libA ++ xload false libB ++ xload false libC),
   ("xloadq", accept :: xload true libA ++ xload true missing ++ xload true libB ++
     [.callRef (Slice.ofCell (asm (xload true libC ++ xload true libA ++ saveDepth)))]),
   ("dict", accept :: dictGet 200 (libraryCellOf dict) ++ dictGet 1 dictLibNode ++ saveDepth),
   ("runvm", accept :: ctos libA ++ [.pushInt (.num 0), .pushRefSlice (asm child), .contExt (.runvm 0), .newc,
     .stIntFixed false false false 32, .endc, .popCtr 4, .tonEnvOp .commit] ++ ctos libC),
   ("child", child), ("code-body", codeBody), ("call-b", callB), ("call-c", callC), ("head", head),
   ("tail", tail), ("chain-end", chainEnd),
   ("callref", [accept, .callRef (Slice.ofCell (libraryCellOf (asm callB))),
     .callRef (Slice.ofCell (libraryCellOf (asm callC)))]),
   ("chain", accept :: [.pushRef (libraryCellOf inner), .ctos, .pop 0] ++ ctos libA),
   ("sendmsg", accept :: [.pushRef (libraryCellOf msg), .pushInt (.num 1024), .tonEnvOp .sendMsg, .pop 0] ++ ctos libA),
   ("extra-balance", accept :: setExtra (libraryCellOf extraDict) ++
     [.pushInt (.num 7), .tonEnvOp .getExtraBalance, .pop 0] ++ ctos libA),
   -- CDATASIZE loads a library cell as it is (`load_cell_slice_special`): no library
   ("cdatasize", accept :: [.pushRef (libraryCellOf libA), .pushInt (.num 100), .cellExt (.cdataSize false)] ++
     saveDepth ++ ctos libB)]

/-- The contracts of the cases: `programs`, code that is a library cell, code whose implicit
`JMPREF` goes to a library cell. -/
def codes : List (String × Cell) :=
  ["plain", "ctos3", "ctos-again", "missing", "after-refusal", "xload", "xloadq", "dict", "runvm", "callref",
    "chain", "sendmsg", "extra-balance", "cdatasize"].map (fun n => (n, asm ((programs.lookup n).getD []))) ++
  [("lib-code", libraryCellOf (asm codeBody)),
   ("jmpref", Cell.mkOrdinary (asm head).bits ((asm head).refs.push (libraryCellOf (asm tail))))]

/-- The roots of the libraries the cases load. -/
def bodies : List Cell :=
  [libA, libB, libC, dict, node1, asm codeBody, asm callB, asm callC, asm tail, asm chainEnd, msg, extraDict]

end LibLoads

/-- `max_transaction_library_loads` (parameter 43; C++ `VmState::load_library`, vm.cpp:643-670): a
library not yet loaded is refused once that many are, also a missing one counts. Contracts that load
several libraries (`CTOS` of a library cell, `XLOAD`, `XLOADQ`, a dictionary whose root or node is a
library cell, `CALLREF`, the implicit `JMPREF`, code that is a library cell, a chain of libraries,
loads after a refusal caught by `TRY`, a `RUNVM` child that loads more, `SENDMSG` of a library cell,
`GETEXTRABALANCE` of extra currencies that are a library cell; `CDATASIZE` of a library cell, which
loads no library), the libraries in the
account (read before version 15) or in the emulator's, the limit unset, 0, 1 or 2. -/
def libraryLoadCases (mk : String → Cell → Cell → TxCase) (a : BitString) (data : Cell) : Array TxCase := Id.run do
  let mut out : Array TxCase := #[]
  for (lname, loads) in [("none", none), ("0", some 0), ("1", some 1), ("2", some 2)] do
    for (pname, code) in LibLoads.codes do
      for (where_, accLib, glob) in [("acc", simpleLibs true LibLoads.bodies, none),
          ("global", none, globalLibsOf (LibLoads.inner :: LibLoads.bodies))] do
        let acc := mkAccount 0 a (.active code data) 1000000000 1700000000 0 1000 (library := accLib)
        let c := mk s!"libloads/{pname}/{where_}/{lname}" acc (intMsg 0 a 100000000 true none #[])
        out := out.push { c with config := withLibraryLoads c.config loads, libs := glob }
  return out

/-- Contracts for tick-tock: the stack is `balance address is_tock -2`. -/
def tickTockPrograms : List (String × List Instr) :=
  [("tt-stack", [.newc, .stIntFixed false false false 8, .stIntFixed false false false 8,
                 .stIntFixed true false false 256, .stIntFixed true false false 64, .endc, .popCtr 4])]

/-- The contracts of the cases that do not assemble (none should). -/
def programsAssemble : List String :=
  (programs ++ actionPrograms ++ extraPrograms ++ tickTockPrograms ++ LibLoads.programs).filterMap fun (n, p) =>
    match asm? p with
    | .ok _ => none
    | .error e => some s!"{n}: {e}"

/-- Tick-tock transactions: of the configuration contract (special), of an ordinary masterchain and
basechain account; contracts that read the stack, use gas, make actions; accounts without gas,
without state, with storage fees due. -/
def tickTockCases (cfg : Cell) (mk : String → Cell → Cell → TxCase) (a : BitString) (data : Cell) :
    Array TxCase := Id.run do
  let mut out : Array TxCase := #[]
  let cfgAddr := (Config.decode cfg).map (·.configAddr) |>.getD a
  let tt (name : String) (acc : Cell) (isTock : Bool) : TxCase :=
    { mk s!"tt/{name}/{if isTock then "tock" else "tick"}" acc Cell.empty with tickTock := some isTock }
  let progs := tickTockPrograms ++ programs.filter (fun (n, _) => ["empty", "throw42", "burn", "c7", "c7-v4",
    "in-msg-params", "accept-loop", "commit-throw", "c7-extra"].contains n) ++
    actionPrograms.filter (fun (n, _) => ["send", "send-all", "send-all-delete", "reserve", "set-code",
      "set-lib", "send-mc", "c5-bad-tag"].contains n)
  for (pname, prog) in progs do
    for (aname, wc, addr) in [("special", (-1 : Int), cfgAddr), ("mc", -1, a), ("bc", 0, a)] do
      for isTock in [false, true] do
        out := out.push (tt s!"{pname}/{aname}" (mkAccount wc addr (.active (asm prog) data) 1000000000 1700000000 0 1000) isTock)
  for (aname, wc, addr) in [("special", (-1 : Int), cfgAddr), ("mc", -1, a), ("bc", 0, a)] do
    out := out.push (tt s!"no-gas/{aname}" (mkAccount wc addr (.active (asm []) data) 0 1700000000 0 1000) false)
    out := out.push (tt s!"old/{aname}" (mkAccount wc addr (.active (asm []) data) 50000 1600000000 0 1000) true)
    out := out.push (tt s!"extra/{aname}" (mkAccount wc addr (.active (asm (programs.lookup "c7-extra" |>.getD [])) data)
      1000000000 1700000000 0 1000 extra2) false)
    out := out.push (tt s!"uninit/{aname}" (mkAccount wc addr .uninit 1000000000 1700000000 0 1000) false)
    out := out.push (tt s!"frozen/{aname}" (mkAccount wc addr (.frozen (natToBits 5 256)) 1000000000 1600000000 0 1000) true)
  out := out.push (tt "none" (mkAccount 0 a .none 0 0 0 0) false)
  return out

/-- The configuration with parameter `n` set to the cell `c`. -/
def withParam (cfg : Cell) (n : Nat) (c : Cell) : Cell :=
  match dictSetRefWithCells (some cfg) (natToBits n 32) c .set with
  | .ok (some r, _, _, _) => r
  | _ => cfg

namespace Configs

/-- `gas_prices#dd` (block.tlb:714-716). -/
def gasPlain (price limit credit block freeze delete : Nat) : Cell :=
  (((((((({} : W).uint 0xdd 8).uint price 64).uint limit 64).uint credit 64).uint block 64).uint freeze 64).uint delete 64).cell

/-- `gas_prices_ext#de` (block.tlb:718-720), under `gas_flat_pfx#d1` (block.tlb:722-723) if `flat` is
given. -/
def gasExt (price limit special credit block freeze delete : Nat) (flat : Option (Nat × Nat) := none) : Cell :=
  let w : W := match flat with
    | some (fl, fp) => ((({} : W).uint 0xd1 8).uint fl 64).uint fp 64
    | none => {}
  ((((((((w.uint 0xde 8).uint price 64).uint limit 64).uint special 64).uint credit 64).uint block 64).uint freeze 64).uint
    delete 64).cell

/-- `msg_forward_prices#ea` (block.tlb:743-745). -/
def msgPrices (lump bit cell ihr first next : Nat) : Cell :=
  ((((((({} : W).uint 0xea 8).uint lump 64).uint bit 64).uint cell 64).uint ihr 32).uint first 16).uint next 16 |>.cell

/-- Parameter 18 (`Hashmap 32 StoragePrices`, block.tlb:708-710): `storage_prices#cc` entries keyed
by their `utime_since`. -/
def storagePrices (entries : List (Nat × Nat × Nat × Nat × Nat)) : Cell := Id.run do
  let mut root : Option Cell := none
  for (since, bit, cell, mcBit, mcCell) in entries do
    let w : W := (((((({} : W).uint 0xcc 8).uint since 32).uint bit 64).uint cell 64).uint mcBit 64).uint mcCell 64
    let b : Builder := { bits := w.bits, refs := #[] }
    if let .ok (r, _, _, _) := dictSetBuilderWithCells root (natToBits since 32) b .set then root := r
  return root.getD Cell.empty

/-- The fields of `size_limits_config` v1 (block.tlb:823-824). -/
def limitsV1 (w : W) (msgBits msgCells libCells vmDepth extSize extDepth : Nat) : W :=
  (((((w.uint msgBits 32).uint msgCells 32).uint libCells 32).uint vmDepth 16).uint extSize 32).uint extDepth 16

/-- The fields `size_limits_config_v2` adds (block.tlb:825-828), the library loads unset. -/
def limitsV2 (w : W) (accCells mcAccCells pubLibs defer extra prefixLen storageDict : Nat) : W :=
  ((((((((w.uint accCells 32).uint mcAccCells 32).uint pubLibs 32).uint defer 32).uint extra 32).uint prefixLen 8).uint
    storageDict 32).bool false)

/-- The C++ defaults of `SizeLimitsConfig` (mc-config.h:398-412) in v1. -/
def defaultsV1 (w : W) : W := limitsV1 w (2 ^ 21) (2 ^ 13) 1000 512 65535 512

end Configs

/-- Configurations other than the testnet one, at global version `v` (parameter 8 with the
capabilities of the other cases, 46, unless the variant changes them): the gas prices of the
basechain (parameter 21) as `gas_prices#dd`, with a flat price for the first 1000 gas, tight (gas limit
5000, credit 1000), dear with low due limits for freezing and deleting; those of the masterchain
(parameter 20) dear; message prices (parameters 24, 25) cheap or dear; storage prices (parameter 18)
changing in time or dear; size limits (parameter 43) of v1 with small messages and VM data depth, of
v2 with small account states, no extra currencies in messages and the storage dictionary from one
cell, of v3 with small totals of messages; capabilities without `capBounceMsgBody`. -/
def configVariants (cfg0 : Cell) (v : Nat) : List (String × Cell) :=
  let cfg := withVersion cfg0 v 46
  [("gas-dd", withParam cfg 21 (Configs.gasPlain 65536000 1000000 10000 10000000 100000000 1000000000)),
   ("gas-flat", withParam cfg 21 (Configs.gasExt 26214400 1000000 1000000 10000 10000000 100000000 1000000000
      (some (1000, 1000000)))),
   ("gas-tight", withParam cfg 21 (Configs.gasExt 26214400 5000 5000 1000 10000000 100000000 1000000000)),
   ("gas-dear", withParam cfg 21 (Configs.gasExt 6553600000 1000000 1000000 10000 10000000 1000 200000)),
   ("gas-mc-dear", withParam cfg 20 (Configs.gasExt 655360000 1000000 70000000 10000 10000000 1000 200000
      (some (100, 1000000)))),
   ("msg-cheap", withParam (withParam cfg 24 (Configs.msgPrices 1 1 1 0 0 0)) 25 (Configs.msgPrices 1 1 1 0 0 0)),
   ("msg-dear", withParam (withParam cfg 24 (Configs.msgPrices 1000000000 655360000000 65536000000000 98304 65535 32768))
      25 (Configs.msgPrices 100000000 65536000000 6553600000000 98304 65535 32768)),
   ("storage-steps", withParam cfg 18 (Configs.storagePrices
      [(0, 1, 500, 1000, 500000), (1695000000, 1000, 1000000, 100000, 10000000)])),
   ("storage-dear", withParam cfg 18 (Configs.storagePrices [(0, 65536000, 6553600000, 655360000, 65536000000)])),
   ("limits-v1", withParam cfg 43 (Configs.limitsV1 (({} : W).uint 1 8) 1000 3 1 3 200 2).cell),
   ("limits-v2", withParam cfg 43 (Configs.limitsV2 (Configs.defaultsV1 (({} : W).uint 2 8)) 4 4 0 256 0 0 1).cell),
   ("limits-v3", withParam cfg 43 ((Configs.limitsV2 (Configs.defaultsV1 (({} : W).uint 3 8)) (2 ^ 16) (2 ^ 11) 256 256 2 8 26
      ).uint 500 32 |>.uint 2 32).cell),
   ("caps-0", withVersion cfg0 v 0)]

/-- Under each configuration of `configVariants`: the contracts of `programs` with a rich, a poor, an
old account, one that cannot pay its storage since long and one in debt, with an internal message,
the rich one with an external message too; those of
`actionPrograms` (rich, internal); four of `programs` sent a bounceable message with a body; some in
the masterchain; a deployment. -/
def configCases (cfg0 : Cell) (v : Nat) (a : BitString) (data : Cell) : Array TxCase := Id.run do
  let mut out : Array TxCase := #[]
  for (cname, cfg) in configVariants cfg0 v do
    let mk (name : String) (acc msg : Cell) : TxCase :=
      { name := s!"v{v}/config-{cname}/{name}", config := cfg, account := acc, msg, now := 1700000200, lt := 3000000, seed }
    for (pname, prog) in programs do
      let code := asm prog
      for (bname, bal, lastPaid, due) in [("rich", 1000000000, 1700000000, 0), ("poor", 30000, 1700000000, 0),
                                           ("old", 1000000000, 1690000000, 0), ("broke", 30000, 1600000000, 0),
                                           ("in-debt", 1000, 1700000000, 150000)] do
        out := out.push (mk s!"{pname}/{bname}/int" (mkAccount 0 a (.active code data) bal lastPaid due 1000)
          (intMsg 0 a 100000000 false none #[]))
      out := out.push (mk s!"{pname}/rich/ext" (mkAccount 0 a (.active code data) 1000000000 1700000000 0 1000)
        (extMsg 0 a none (natToBits 5 8)))
    for (pname, prog) in actionPrograms do
      out := out.push (mk s!"{pname}/rich/int" (mkAccount 0 a (.active (asm prog) data) 1000000000 1700000000 0 1000)
        (intMsg 0 a 100000000 false none #[]))
    for (pname, prog) in programs.take 4 do
      out := out.push (mk s!"bounce-{pname}" (mkAccount 0 a (.active (asm prog) data) 1000000000 1700000000 0 1000)
        (intMsg 0 a 100000000 true none (natToBits 0xabcdef 300)))
    for (pname, prog) in programs.filter (fun (n, _) => ["accept", "c7", "c7-v6", "burn", "loop"].contains n) ++
        actionPrograms.filter (fun (n, _) => ["send", "send-mc"].contains n) do
      out := out.push (mk s!"mc-{pname}" (mkAccount (-1) a (.active (asm prog) data) 1000000000 1690000000 0 1000)
        (intMsg (-1) a 100000000 false none #[]))
    let si := stateInit (asm [.tonEnvOp .accept]) data
    let addr := bytesToBits si.hashBytes
    out := out.push (mk "deploy/none" (mkAccount 0 addr .none 0 0 0 0) (intMsg 0 addr 100000000 false (some si) #[]))
  return out

/-- The cases on the configuration `cfg0`, for each version of `versions`. -/
def cases (cfg0 : Cell) (versions : List Nat) : Array TxCase := Id.run do
  let mut out : Array TxCase := #[]
  let a := natToBits 0x1111111111111111111111111111111111111111111111111111111111111111 256
  let data := (({} : W).uint 0xabcd 16).cell
  for v in versions do
    let cfg := withVersion cfg0 v 46
    let mk (name : String) (acc msg : Cell) : TxCase :=
      { name := s!"v{v}/{name}", config := cfg, account := acc, msg, now := 1700000200, lt := 3000000, seed }
    for (pname, prog) in programs do
      let code := asm prog
      for (bname, bal, lastPaid, due) in [("rich", 1000000000, 1700000000, 0), ("old", 1000000000, 1690000000, 0),
                                         ("poor", 30000, 1700000000, 0), ("due", 1000000000, 1700000000, 5000)] do
        let acc := mkAccount 0 a (.active code data) bal lastPaid due 1000
        out := out.push (mk s!"{pname}/{bname}/int" acc (intMsg 0 a 100000000 false none #[]))
        out := out.push (mk s!"{pname}/{bname}/int-small" acc (intMsg 0 a 1000 false none #[]))
        out := out.push (mk s!"{pname}/{bname}/ext" acc (extMsg 0 a none (natToBits 5 8)))
    for (pname, prog) in actionPrograms do
      let code := asm prog
      for (bname, bal) in [("rich", 1000000000), ("poor", 3000000)] do
        let acc := mkAccount 0 a (.active code data) bal 1700000000 0 1000
        out := out.push (mk s!"{pname}/{bname}/int" acc (intMsg 0 a 100000000 false none #[]))
        out := out.push (mk s!"{pname}/{bname}/int-bounce" acc (intMsg 0 a 100000000 true none (natToBits 0x1234 16)))
        out := out.push (mk s!"{pname}/{bname}/ext" acc (extMsg 0 a none #[]))
    -- bounceable messages to contracts that fail
    for (pname, prog) in programs do
      let acc := mkAccount 0 a (.active (asm prog) data) 1000000000 1700000000 0 1000
      out := out.push (mk s!"bounce-{pname}" acc (intMsg 0 a 100000000 true none (natToBits 0xabcdef 300)))
      out := out.push (mk s!"bounce-{pname}/small" acc (intMsg 0 a 3000000 true none (natToBits 1 8)))
    -- the new bounce format (extra_flags 1: the body's bits, 3: the body with its references; from
    -- version 12; before, extra_flags is the IHR fee)
    for (pname, prog) in (programs.take 5) ++ (actionPrograms.filter (·.1.startsWith "send-too-much")) do
      let acc := mkAccount 0 a (.active (asm prog) data) 1000000000 1700000000 0 1000
      for ef in [1, 3, 2] do
        out := out.push (mk s!"bounce-new{ef}-{pname}" acc
          (intMsg 0 a 100000000 true none (natToBits 0xabcdef 100) ef #[(({} : W).uint 0x77 8).cell]))
    out := out.push (mk "bounce-new1/no-state" (mkAccount 0 a .uninit 50000000 1700000000 0 1000)
      (intMsg 0 a 100000000 true none (natToBits 5 8) 1))
    out := out.push (mk "bounce/no-state" (mkAccount 0 a .uninit 50000000 1700000000 0 1000) (intMsg 0 a 100000000 true none #[]))
    out := out.push (mk "bounce/none" (mkAccount 0 a .none 0 0 0 0) (intMsg 0 a 100000000 true none #[]))
    -- deploying: uninit and absent accounts at the address of the StateInit
    for (pname, prog) in programs.take 6 do
      let si := stateInit (asm prog) data
      let addr := bytesToBits si.hashBytes
      out := out.push (mk s!"deploy-{pname}/none/int" (mkAccount 0 addr .none 0 0 0 0) (intMsg 0 addr 100000000 false (some si) #[]))
      out := out.push (mk s!"deploy-{pname}/uninit/int" (mkAccount 0 addr .uninit 50000000 1700000000 0 1000)
        (intMsg 0 addr 100000000 false (some si) #[]))
      out := out.push (mk s!"deploy-{pname}/uninit/ext" (mkAccount 0 addr .uninit 50000000 1700000000 0 1000)
        (extMsg 0 addr (some si) #[]))
      out := out.push (mk s!"deploy-{pname}/wrong-addr" (mkAccount 0 a .uninit 50000000 1700000000 0 1000)
        (intMsg 0 a 100000000 false (some si) #[]))
      out := out.push (mk s!"deploy-{pname}/frozen" (mkAccount 0 addr (.frozen (bytesToBits si.hashBytes)) 50000000 1700000000 0 1000)
        (intMsg 0 addr 100000000 false (some si) #[]))
    out := out.push (mk "none/int" (mkAccount 0 a .none 0 0 0 0) (intMsg 0 a 100000000 false none #[]))
    out := out.push (mk "uninit/int" (mkAccount 0 a .uninit 50000000 1690000000 0 1000) (intMsg 0 a 100000000 false none #[]))
    out := out.push (mk "frozen/int" (mkAccount 0 a (.frozen (natToBits 77 256)) 5000 1690000000 0 1000) (intMsg 0 a 100000000 false none #[]))
    out := out ++ extraCases mk a data
    out := out ++ tickTockCases cfg mk a data
    -- code that is a library cell (`convert_code_cell`): its library in the account (public or not,
    -- read before version 15), in the emulator's libraries, in the message's StateInit, missing, or a
    -- library whose root is a library cell again
    let libBody := asm (programs.lookup "c7-v4" |>.getD [.tonEnvOp .accept])
    let libCode := libraryCellOf libBody
    let inner := libraryCellOf (asm [.tonEnvOp .accept, .throw 9])
    let chain := libraryCellOf inner
    let withLibs (c : TxCase) (libs : Option Cell) : TxCase := { c with libs }
    for (lname, accLib, glob) in [("none", none, none), ("acc-public", simpleLibs true [libBody], none),
        ("acc-private", simpleLibs false [libBody], none), ("global", none, globalLibsOf [libBody]),
        ("both", simpleLibs true [libBody], globalLibsOf [libBody])] do
      let acc := mkAccount 0 a (.active libCode data) 1000000000 1700000000 0 1000 (library := accLib)
      out := out.push (withLibs (mk s!"lib-code/{lname}/int" acc (intMsg 0 a 100000000 true none #[])) glob)
      out := out.push (withLibs (mk s!"lib-code/{lname}/ext" acc (extMsg 0 a none #[])) glob)
      out := out.push (withLibs { mk s!"lib-code/{lname}/tick" acc Cell.empty with tickTock := some false } glob)
    out := out.push (withLibs (mk "lib-code/chain" (mkAccount 0 a (.active chain data) 1000000000 1700000000 0 1000)
      (intMsg 0 a 100000000 true none #[])) (globalLibsOf [inner, asm [.tonEnvOp .accept, .throw 9]]))
    out := out ++ libraryLoadCases mk a data
    if [3, 5, 9, 12, 16].contains v then out := out ++ configCases cfg0 v a data
    -- deploying a contract whose code is a library cell, the library in the message's StateInit
    let siLib := (((((({} : W).bool false).bool false).maybeRef (some libCode)).maybeRef (some data)).maybeRef
      (simpleLibs true [libBody])).cell
    let siAddr := bytesToBits siLib.hashBytes
    out := out.push (mk "lib-code/deploy" (mkAccount 0 siAddr .none 0 0 0 0) (intMsg 0 siAddr 100000000 false (some siLib) #[]))
    out := out.push (withLibs (mk "lib-code/deploy-global" (mkAccount 0 siAddr .none 0 0 0 0)
      (intMsg 0 siAddr 100000000 false (some siLib) #[])) (globalLibsOf [libBody]))
    -- special accounts of parameter 31 (masterchain only): no storage or forwarding fees, the special
    -- gas limit, no action fines; the same address in the basechain is ordinary
    let specials := ((Config.decode cfg).bind fun c => dictEntries c.specialSmc 256).getD #[]
    for (key, _) in specials.toList.take 2 do
      let tag := (bitStringToBytesBE key).toList.take 1 |>.map (·.toNat) |>.headD 0
      for (pname, prog) in programs.filter (fun (n, _) => ["accept", "c7", "burn", "throw42"].contains n) ++
          actionPrograms.filter (fun (n, _) => ["send", "send-all", "send-all-delete", "send-too-much",
            "send-big-body", "reserve", "set-public-lib"].contains n) do
        for (wname, wc) in [("mc", (-1 : Int)), ("bc", 0)] do
          for (bname, bal, paid) in [("rich", 1000000000, 1700000000), ("old", 5000000, 1600000000)] do
            let acc := mkAccount wc key (.active (asm prog) data) bal paid 0 1000
            out := out.push (mk s!"p31-{tag}/{pname}/{wname}/{bname}/int" acc (intMsg wc key 100000000 true none #[]))
            out := out.push (mk s!"p31-{tag}/{pname}/{wname}/{bname}/ext" acc (extMsg wc key none #[]))
    -- accounts with an anycast address (`addr` is addr_orig, the account lives at the rewritten
    -- address): messages to the rewritten address or to the anycast form, contracts that read
    -- MYADDR or send (the source is replaced by the address with its anycast before version 10)
    for d in [1, 8, 30] do
      let pfx : BitString := (List.range d).toArray.map (fun i => i % 3 == 0)
      let actual := pfx ++ a.extract d 256
      for (pname, prog) in programs.filter (fun (n, _) => ["accept", "c7"].contains n) ++
          actionPrograms.filter (fun (n, _) => ["send", "send-bad-src", "send-all"].contains n) do
        let acc := mkAccount 0 a (.active (asm prog) data) 1000000000 1700000000 0 1000 (anycast := some pfx)
        out := out.push (mk s!"anycast{d}/{pname}/int" acc (intMsg 0 actual 100000000 false none #[]))
        out := out.push (mk s!"anycast{d}/{pname}/int-anycast" acc (intMsg 0 a 100000000 true none #[] (anycast := some pfx)))
        out := out.push (mk s!"anycast{d}/{pname}/ext" acc (extMsg 0 actual none #[]))
        out := out.push (mk s!"anycast{d}/{pname}/ext-anycast" acc (extMsg 0 a none #[] (anycast := some pfx)))
    -- precompiled contracts (parameter 45): the VM runs with the gas limits of the configuration and
    -- the gas usage of the list is reported; out of gas, C++ fails
    let pre := ["accept", "throw42", "c7-v6", "accept-loop", "burn", "empty"].filterMap fun n =>
      (programs.lookup n).map fun p => (n, asm p)
    for (usage, uname) in [(100, "cheap"), (20000, "dear"), (100000000, "too-dear")] do
      let cfgP := withPrecompiled cfg (pre.map fun (_, c) => (c, usage))
      let mkP (name : String) (acc msg : Cell) : TxCase := { mk name acc msg with config := cfgP }
      for (pname, code) in pre do
        let acc := mkAccount 0 a (.active code data) 1000000000 1700000000 0 1000
        out := out.push (mkP s!"precompiled/{uname}/{pname}/int" acc (intMsg 0 a 100000000 false none #[]))
        out := out.push (mkP s!"precompiled/{uname}/{pname}/int-small" acc (intMsg 0 a 30000 true none #[]))
        out := out.push (mkP s!"precompiled/{uname}/{pname}/ext" acc (extMsg 0 a none #[]))
        out := out.push (mkP s!"precompiled/{uname}/{pname}/special"
          (mkAccount (-1) ((Config.decode cfg).map (·.configAddr) |>.getD a) (.active code data) 1000000000 1700000000 0 1000)
          (intMsg (-1) ((Config.decode cfg).map (·.configAddr) |>.getD a) 100000000 false none #[]))
    -- the blackhole address burns the grams of an inbound message (masterchain only)
    let cfgB := withBlackhole cfg a
    let mkB (name : String) (acc msg : Cell) : TxCase := { mk name acc msg with config := cfgB }
    let cfgAddr := (Config.decode cfg).map (·.configAddr) |>.getD a
    for (pname, prog) in programs.filter (fun (n, _) => ["accept", "c7", "c7-v4", "throw42", "in-msg-params"].contains n) do
      for (wname, wc) in [("mc", (-1 : Int)), ("bc", 0)] do
        out := out.push (mkB s!"blackhole/{pname}/{wname}" (mkAccount wc a (.active (asm prog) data) 1000000000 1700000000 0 1000)
          (intMsg wc a 100000000 false none #[] (extra := extraOf [(7, amt 3)])))
        out := out.push (mkB s!"blackhole/{pname}/{wname}/bounce" (mkAccount wc a (.active (asm prog) data) 1000000000 1700000000 0 1000)
          (intMsg wc a 100000000 true none #[]))
      out := out.push (mkB s!"blackhole/{pname}/special" (mkAccount (-1) cfgAddr (.active (asm prog) data) 1000000000 1700000000 0 1000)
        (intMsg (-1) cfgAddr 100000000 false none #[]))
    out := out.push (mkB "blackhole/none" (mkAccount (-1) a .none 0 0 0 0) (intMsg (-1) a 100000000 false none #[]))
    out := out.push (mkB "blackhole/ext" (mkAccount (-1) a (.active (asm [.tonEnvOp .accept]) data) 1000000000 1700000000 0 1000)
      (extMsg (-1) a none #[]))
    -- amounts with a leading zero byte: the generated TL-B code reads them, block::tlb does not
    let code := asm [.tonEnvOp .accept]
    for k in [1, 2, 3] do
      out := out.push (mk s!"padded-acc{k}" (mkAccount 0 a (.active code data) 1000000000 1700000000 7000 1000 (padded := k))
        (intMsg 0 a 100000000 false none #[]))
    out := out.push (mk "padded-acc-extra-zero" (mkAccount 0 a (.active code data) 1000000000 1700000000 0 1000
      (extraOf [(7, amt 0)])) (intMsg 0 a 100000000 false none #[]))
    out := out.push (mk "padded-acc-extra" (mkAccount 0 a (.active code data) 1000000000 1700000000 0 1000
      (extraOf [(7, natToBits 2 5 ++ natToBits 5 16)])) (intMsg 0 a 100000000 false none #[]))
    out := out.push (mk "padded-msg-extra-zero" (mkAccount 0 a (.active code data) 1000000000 1700000000 0 1000)
      (intMsg 0 a 100000000 false none #[] (extra := extraOf [(7, amt 0)])))
    for k in [1, 2, 3] do
      out := out.push (mk s!"padded-msg{k}" (mkAccount 0 a (.active code data) 1000000000 1700000000 0 1000)
        (intMsg 0 a 100000000 true none #[] (padded := k)))
  return out


/-! ## Fuzz -/

def pick (rng : StdGen) (xs : Array α) [Inhabited α] : α × StdGen :=
  let (i, rng) := randNat rng 0 (xs.size - 1)
  (xs[i]!, rng)

/-- A random amount: zero, small, or log-uniform up to about 10^11. -/
def randAmount (rng : StdGen) : Nat × StdGen :=
  let (k, rng) := randNat rng 0 9
  if k = 0 then (0, rng)
  else
    let (e, rng) := randNat rng 2 11
    let (m, rng) := randNat rng 1 9
    (m * 10 ^ e, rng)

/-- A random action (as instructions). -/
def randAction (rng0 : StdGen) : List Instr × StdGen := Id.run do
  let (k, rng) := randNat rng0 0 9
  let (value, rng) := randAmount rng
  let (mode, rng) := pick rng #[0, 1, 2, 3, 16, 17, 64, 65, 66, 128, 130, 160, 162, 4, 192]
  let (bounce, rng) := randBool rng
  let (bodyLen, rng) := randNat rng 0 400
  let (bodyRef, rng) := randBool rng
  let (wc, rng) := pick rng #[(0 : Int), 0, 0, -1, 7]
  let (xk, rng) := randNat rng 0 5
  let x : Option Cell :=
    if xk = 0 then extraOf [(7, amt 100)] else if xk = 1 then extraOf [(7, amt 0), (100, amt 999)]
    else if xk = 2 then extraOf [(9, amt 1)] else none
  if k ≤ 4 then
    let body := natToBits 0x5a5a5a5a 32 ++ natToBits 0 (bodyLen - Nat.min bodyLen 32)
    let body := if bodyRef then body else body.extract 0 (Nat.min body.size 300)
    return (sendRaw (relaxedInt wc other value bounce body bodyRef (extra := x)) mode, rng)
  else if k = 5 then
    return (sendRaw (relaxedExt (natToBits 9 8)) (mode &&& 3), rng)
  else if k = 6 then
    let (rmode, rng) := randNat rng 0 18
    if x.isSome then
      return ([.pushInt (.num (Int.ofNat value)), .pushRef (({} : W).maybeRef x).cell, .ctos, .lddict true false,
               .pushInt (.num (Int.ofNat rmode)), .tonEnvOp .rawReserveX], rng)
    return ([.pushInt (.num (Int.ofNat value)), .pushInt (.num (Int.ofNat rmode)), .tonEnvOp .rawReserve], rng)
  else if k = 7 then
    return ([.pushRef (asm [.tonEnvOp .accept]), .tonEnvOp .setCode], rng)
  else if k = 8 then
    let (lmode, rng) := randNat rng 0 3
    return ([.pushRef libCell, .pushInt (.num (Int.ofNat lmode)), .tonEnvOp .setLibCode], rng)
  else
    let (c, rng) := randNat rng 0 99
    return ([.throw (Int.ofNat c)], rng)

/-- A random contract: maybe ACCEPT, up to four actions. -/
def randProgram (rng0 : StdGen) : List Instr × StdGen := Id.run do
  let (acc, rng) := randBool rng0
  let (n, rng) := randNat rng 0 4
  let mut rng := rng
  let mut code : List Instr := if acc then [.tonEnvOp .accept] else []
  for _ in [0:n] do
    let (a, rng') := randAction rng
    code := code ++ a
    rng := rng'
  return (code, rng)

/-- A random transaction case on the configuration `cfg0`. -/
def randCase (cfg0 : Cell) (i : Nat) (rng0 : StdGen) : TxCase × StdGen := Id.run do
  let (v, rng) := randNat rng0 0 16
  let cfg := withVersion cfg0 v 46
  let (prog, rng) := randProgram rng
  let code := asm prog
  let data := (({} : W).uint 0xabcd 16).cell
  let (kind, rng) := randNat rng 0 9
  let (bal, rng) := randAmount rng
  let (paidAgo, rng) := pick rng #[0, 100, 100000, 10000000]
  let (due, rng) := pick rng #[0, 0, 0, 7000, 2000000000]
  let (value, rng) := randAmount rng
  let (bounce, rng) := randBool rng
  let (ext, rng) := randNat rng 0 4
  let (bodyBits, rng) := randNat rng 0 200
  let a := natToBits 0x1111111111111111111111111111111111111111111111111111111111111111 256
  let si := stateInit code data
  let siAddr := bytesToBits si.hashBytes
  let (addr, st, init) :=
    if kind ≤ 5 then (a, AccState.active code data, none)
    else if kind = 6 then (siAddr, AccState.uninit, some si)
    else if kind = 7 then (siAddr, AccState.none, some si)
    else if kind = 8 then (siAddr, AccState.frozen siAddr, some si)
    else (a, AccState.frozen (natToBits 99 256), none)
  let (accX, rng) := pick rng #[none, none, extra2, extra3]
  let (msgX, rng) := pick rng #[none, none, extraOf [(7, amt 1)], extraOf [(100, amt 5), (3, amt 77)]]
  let acc := mkAccount 0 addr st (if kind = 7 then 0 else bal) (1700000200 - paidAgo) (if kind = 7 then 0 else due)
    (if kind = 7 then 0 else 1000) (if kind = 7 then none else accX)
  let body := natToBits 0x12345678 32 ++ natToBits 0 bodyBits
  let msg := if ext = 0 then extMsg 0 addr init body else intMsg 0 addr value bounce init body (extra := msgX)
  return ({ name := s!"fuzz/{i}/v{v}", config := cfg, account := acc, msg, now := 1700000200, lt := 3000000, seed }, rng)

def fuzzCases (cfg0 : Cell) (count seed : Nat) : Array TxCase := Id.run do
  let mut rng := mkStdGen seed
  let mut out := #[]
  for i in [0:count] do
    let (c, rng') := randCase cfg0 i rng
    out := out.push c
    rng := rng'
  return out

end Tests.Tx
