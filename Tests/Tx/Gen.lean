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

def asm (code : List Instr) : Cell :=
  match assembleCp0 code with
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
   ("deep-c4", [.newc, .endc] ++ (List.replicate 20 [.newc, .stref, .endc]).flatten ++ [.popCtr 4])]

def addrStd (wc : Int) (a : BitString) : W := (((({} : W).uint 2 2).bool false).int wc 8).bitStr a

/-- `StateInit` with code and data. -/
def stateInit (code data : Cell) : Cell :=
  (((({} : W).bool false).bool false).maybeRef (some code) |>.maybeRef (some data) |>.bool false).cell

inductive AccState where
  | active (code data : Cell)
  | uninit
  | frozen (hash : BitString)
  | none

/-- A `ShardAccount` at `(wc, addr)` with the storage statistics C++ computes. -/
def mkAccount (wc : Int) (addr : BitString) (st : AccState) (bal lastPaid due lt : Nat) : Cell :=
  let stateBits : W :=
    match st with
    | .active code data => ((((({} : W).bool true).bool false).bool false).maybeRef (some code)).maybeRef (some data) |>.bool false
    | .uninit => ({} : W).uint 0 2
    | .frozen h => (({} : W).uint 1 2).bitStr h
    | .none => {}
  let storage : W := (({} : W).uint lt 64).grams bal |>.bool false
  let storage := { storage with bits := storage.bits ++ stateBits.bits, refs := storage.refs ++ stateBits.refs }
  let sc := storage.cell
  let acc : Cell :=
    match st with
    | .none => (({} : W).bool false).cell
    | _ =>
        let (c, b) := cellsAndBits (collectCells sc.refs.toList)
        let w : W := (({} : W).bool true).bitStr (addrStd wc addr).bits
        let w := ((w.varUInt (c + 1) 7).varUInt (b + sc.bits.size) 7).uint 0 3 |>.uint lastPaid 32
        let w := if due > 0 then (w.bool true).grams due else w.bool false
        (w.slice (Slice.ofCell sc)).cell
  ((({} : W).ref acc).uint 0 256).uint (if lt > 0 then lt - 1 else 0) 64 |>.cell

/-- An internal message to `(wc, dest)`, with an optional `StateInit` in a reference and a body of
`body` bits inline. -/
def intMsg (wc : Int) (dest : BitString) (value : Nat) (bounce : Bool) (init : Option Cell) (body : BitString) : Cell :=
  let src := natToBits 0x2222222222222222222222222222222222222222222222222222222222222222 256
  let w : W := (((({} : W).bool false).bool true).bool bounce).bool false
  let w := (w.bitStr (addrStd 0 src).bits).bitStr (addrStd wc dest).bits
  let w := (((w.grams value).bool false).grams 0).grams 0 |>.uint 2000 64 |>.uint 1700000100 32
  let w := match init with
    | some c => ((w.bool true).bool true).ref c
    | none => w.bool false
  ((w.bool false).bitStr body).cell

/-- An external inbound message (`addr_none` source, no import fee). -/
def extMsg (wc : Int) (dest : BitString) (init : Option Cell) (body : BitString) : Cell :=
  let w : W := ((({} : W).uint 2 2).uint 0 2).bitStr (addrStd wc dest).bits |>.grams 0
  let w := match init with
    | some c => ((w.bool true).bool true).ref c
    | none => w.bool false
  ((w.bool false).bitStr body).cell

def seed : BitString := natToBits 0x5eed5eed 256

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
  return out

end Tests.Tx
