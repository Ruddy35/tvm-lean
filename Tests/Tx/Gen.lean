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

def other : BitString := natToBits 0x3333333333333333333333333333333333333333333333333333333333333333 256

/-- An outbound internal message as a contract proposes it (`MessageRelaxed`): source `addr_none`
or `src`, destination `(wc, dest)`, the value, the bounce flag, a body of `body` bits inline or in a
reference. -/
def relaxedInt (wc : Int) (dest : BitString) (value : Nat) (bounce : Bool := false) (body : BitString := #[])
    (bodyRef : Bool := false) (src : Option BitString := none) (fwdFee : Nat := 0) : Cell :=
  let w : W := (((({} : W).bool false).bool true).bool bounce).bool false
  let w := match src with | some a => w.bitStr (addrStd 0 a).bits | none => w.uint 0 2
  let w := (((w.bitStr (addrStd wc dest).bits).grams value).bool false).grams 0 |>.grams fwdFee
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
  let big := natToBits 0 900
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
def intMsg (wc : Int) (dest : BitString) (value : Nat) (bounce : Bool) (init : Option Cell) (body : BitString)
    (extraFlags : Nat := 0) (bodyRefs : Array Cell := #[]) : Cell :=
  let src := natToBits 0x2222222222222222222222222222222222222222222222222222222222222222 256
  let w : W := (((({} : W).bool false).bool true).bool bounce).bool false
  let w := (w.bitStr (addrStd 0 src).bits).bitStr (addrStd wc dest).bits
  let w := (((w.grams value).bool false).grams extraFlags).grams 0 |>.uint 2000 64 |>.uint 1700000100 32
  let w := match init with
    | some c => ((w.bool true).bool true).ref c
    | none => w.bool false
  { ((w.bool false).bitStr body) with refs := (w.bool false).refs ++ bodyRefs }.cell

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
  if k ≤ 4 then
    let body := natToBits 0x5a5a5a5a 32 ++ natToBits 0 (bodyLen - Nat.min bodyLen 32)
    let body := if bodyRef then body else body.extract 0 (Nat.min body.size 300)
    return (sendRaw (relaxedInt wc other value bounce body bodyRef) mode, rng)
  else if k = 5 then
    return (sendRaw (relaxedExt (natToBits 9 8)) (mode &&& 3), rng)
  else if k = 6 then
    let (rmode, rng) := randNat rng 0 18
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
  let acc := mkAccount 0 addr st (if kind = 7 then 0 else bal) (1700000200 - paidAgo) (if kind = 7 then 0 else due)
    (if kind = 7 then 0 else 1000)
  let body := natToBits 0x12345678 32 ++ natToBits 0 bodyBits
  let msg := if ext = 0 then extMsg 0 addr init body else intMsg 0 addr value bounce init body
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
