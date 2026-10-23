import Tests.Tx.Gen
import Tests.Tx.Real

/-!
# Transactions for the uncovered branches of `transaction.cpp`

The first measurement of the coverage of `crypto/block/transaction.cpp` by `tvm-lean-tx-test`
(`scripts/tx-coverage-run.sh`, `docs/coverage/README.md`) left decisions that ordinary and tick-tock
transactions of the emulator can take. The cases below take them; each group names the C++ lines.
Groups that do not depend on the version run at versions 9 and 16 only.
-/

namespace Tests.Tx

open TvmLean TvmLean.Tx

namespace Cov

def a1 : BitString := natToBits 0x1111111111111111111111111111111111111111111111111111111111111111 256
def src0 : BitString := natToBits 0x2222222222222222222222222222222222222222222222222222222222222222 256
def data0 : Cell := (({} : W).uint 0xabcd 16).cell
def data1 : Cell := (({} : W).uint 0x1234 16).cell
def accept : Cell := asm [.tonEnvOp .accept]
/-- `ACCEPT`, then the `c7` program of `programs` (the time, logical times, seed, balance and `MYADDR`
in c4). -/
def acceptC7 : Cell := asm ([.tonEnvOp .accept] ++ (programs.lookup "c7").getD [])

/-- `MsgAddressInt` bits: `addr_std` (with an optional anycast prefix) or `addr_var`. -/
def stdA (wc : Int) (a : BitString) (anycast : Option BitString := none) : BitString :=
  (Account.mkAddr wc anycast a).bits
def varA (wc : Int) (a : BitString) : BitString :=
  (((((({} : W).uint 3 2).bool false).uint a.size 9).int wc 32).bitStr a).bits

def gramsBits (v : Nat) : BitString := (({} : W).grams v).bits
/-- `Grams` with one leading zero byte (the generated TL-B code reads it, `block::tlb` does not). -/
def gramsPadded (v : Nat) : BitString := (({} : W).varUIntPadded v 16).bits

/-- `init` and `body` of a message: the `StateInit` inline or in a reference, the body inline or in a
reference. -/
def W.initBody (w : W) (init : Option Cell) (initInline : Bool) (body : BitString) (bodyRef : Option Cell) : W :=
  let w := match init with
    | some c => if initInline then ((w.bool true).bool false).slice (Slice.ofCell c) else ((w.bool true).bool true).ref c
    | none => w.bool false
  match bodyRef with
  | some c => (w.bool true).ref c
  | none => (w.bool false).bitStr body

/-- An inbound internal message with every field given (`dest`, `src`: `MsgAddressInt` bits). -/
def intMsgX (dest : BitString) (value : Nat) (bounce : Bool := false) (bounced : Bool := false)
    (src : BitString := stdA 0 src0) (extraFlags : BitString := gramsBits 0) (fwdFee : Nat := 0)
    (createdLt : Nat := 2000) (init : Option Cell := none) (initInline : Bool := false) (body : BitString := #[])
    (bodyRef : Option Cell := none) : Cell :=
  let w : W := (((({} : W).bool false).bool true).bool bounce).bool bounced
  let w := (((w.bitStr src).bitStr dest).grams value).bool false
  let w := (((w.bitStr extraFlags).grams fwdFee).uint createdLt 64).uint 1700000100 32
  (W.initBody w init initInline body bodyRef).cell

/-- An outbound internal message as a contract proposes it (`MessageRelaxed`), every field given. -/
def relaxedX (dest : BitString) (value : Nat) (ihrDisabled : Bool := true) (src : BitString := #[false, false])
    (extraFlags : BitString := gramsBits 0) (fwdFee : BitString := gramsBits 0) (init : Option Cell := none)
    (initInline : Bool := false) (body : BitString := #[]) (bodyRef : Option Cell := none) : Cell :=
  let w : W := (((({} : W).bool false).bool ihrDisabled).bool false).bool false
  let w := (((w.bitStr src).bitStr dest).grams value).bool false
  let w := (((w.bitStr extraFlags).bitStr fwdFee).uint 0 64).uint 0 32
  (W.initBody w init initInline body bodyRef).cell

/-- An outbound external message to an `addr_extern` of `len` bits with a body inline. -/
def relaxedExtX (len : Nat) (body : BitString) : Cell :=
  let w : W := (((({} : W).uint 3 2).uint 0 2).uint 1 2).uint len 9 |>.uint 0x77 len
  (((((w.uint 0 64).uint 0 32).bool false).bool false).bitStr body).cell

/-- `StateInit` with each field given. -/
def stateInitX (code data : Option Cell) (fpl : Option Nat := none) (special : Option (Bool × Bool) := none)
    (library : Option Cell := none) : Cell :=
  let w : W := match fpl with | some d => (({} : W).bool true).uint d 5 | none => ({} : W).bool false
  let w := match special with | some (tk, tc) => ((w.bool true).bool tk).bool tc | none => w.bool false
  (((w.maybeRef code).maybeRef data).maybeRef library).cell

/-- An action list node `prev:^OutList action` with the action's bits and references. -/
def node (prev : Cell) (bits : BitString) (refs : Array Cell := #[]) : Cell := Cell.mkOrdinary bits (#[prev] ++ refs)
/-- `action_change_library#26fa1dd4 mode:(## 7) libref:LibRef` (`libref_hash$0` or `libref_ref$1`). -/
def actChangeLib (mode : Nat) (lib : Sum BitString Cell) : Cell :=
  match lib with
  | .inl h => node Cell.empty (natToBits 0x26fa1dd4 32 ++ natToBits mode 7 ++ #[false] ++ h)
  | .inr c => node Cell.empty (natToBits 0x26fa1dd4 32 ++ natToBits mode 7 ++ #[true]) #[c]
/-- `action_reserve_currency#36e6b809 mode:(## 8) currency:CurrencyCollection`. -/
def actReserve (mode value : Nat) : Cell := node Cell.empty (natToBits 0x36e6b809 32 ++ natToBits mode 8 ++ gramsBits value ++ #[false])
/-- A Merkle proof of a level-0 cell `c` (as `Tests.Gen.VmCore.merkleProof`), `n` times nested: a Merkle
depth of `n`. -/
def merkleProofs (c : Cell) : Nat → Cell
  | 0 => c
  | n + 1 =>
    let inner := merkleProofs c n
    { bits := natToBits 3 8 ++ bytesToBits inner.hashBytes ++ natToBits inner.depth 16, refs := #[inner], special := true,
      levelMask := 0 }

/-- A pruned branch of level 1 of the level-0 cell `c` (its hash and depth). -/
def prunedOf (c : Cell) : Cell :=
  { bits := natToBits 1 8 ++ natToBits 1 8 ++ bytesToBits c.hashBytes ++ natToBits c.depth 16, refs := #[], special := true,
    levelMask := 1 }

/-- A Merkle proof of `c` of any level (its hash and depth at level 0): of level one less. -/
def merkleProofOf (c : Cell) : Cell :=
  let (h, d) := match c.computeLevelInfo? with
    | .ok info => (info.getHash 0, info.getDepth 0)
    | .error _ => (#[], 0)
  { bits := natToBits 3 8 ++ bytesToBits h ++ natToBits d 16, refs := #[c], special := true, levelMask := c.levelMask >>> 1 }

/-- `n` nodes with nothing but the reference to the previous one. -/
def chain (n : Nat) : Cell := (List.range n).foldl (fun c _ => Cell.mkOrdinary #[] #[c]) Cell.empty

/-- The configuration without parameter `n`. -/
def withoutParam (cfg : Cell) (n : Nat) : Cell :=
  match dictDeleteWithCells (some cfg) (natToBits n 32) with
  | .ok (_, some r, _, _) => r
  | _ => cfg

/-- Parameter 12 with workchain `wc`: that of workchain 0 with `accept_msgs` set to `accept`
(`workchain#a6`, the bit after `basic` and `active`). -/
def withWorkchain (cfg : Cell) (wc : Nat) (accept : Bool) : Cell := Id.run do
  let some c := Config.decode cfg | return cfg
  let some v := dictGet c.workchains (natToBits 0 32) | return cfg
  let bits := (v.readBits v.bitsRemaining).set! 66 accept
  match dictSetBuilderWithCells c.workchains (natToBits wc 32) { bits, refs := v.cell.refs.extract v.refPos v.cell.refs.size } .set with
  | .ok (some root, _, _, _) => withParam cfg 12 ((({} : W).bool true).ref root).cell
  | _ => cfg

/-- Parameter 12 with workchain `wc` not accepting messages. -/
def withClosedWorkchain (cfg : Cell) (wc : Nat) : Cell := withWorkchain cfg wc false

/-- Parameter 44 (`suspended_address_list#00 addresses:(HashmapE 288 Unit) suspended_until:uint32`). -/
def withSuspended (cfg : Cell) (addrs : List (Int × BitString)) (untilTime : Nat) : Cell := Id.run do
  let mut root : Option Cell := none
  for (wc, a) in addrs do
    if let .ok (r, _, _, _) := dictSetBuilderWithCells root ((({} : W).int wc 32).bits ++ a) { bits := #[], refs := #[] } .set then
      root := r
  withParam cfg 44 (((({} : W).uint 0 8).maybeRef root).uint untilTime 32).cell

/-- Parameter 43 v1 with messages of at most 1000 bits and 3 cells, libraries of one cell, external
messages of depth 2. -/
def limitsSmall (cfg : Cell) : Cell := withParam cfg 43 (Configs.limitsV1 (({} : W).uint 1 8) 1000 3 1 512 65535 2).cell
/-- Parameter 43 v3 with at most 500 bits and 2 cells of messages in a transaction. -/
def limitsTotal (cfg : Cell) : Cell :=
  withParam cfg 43 ((Configs.limitsV2 (Configs.defaultsV1 (({} : W).uint 3 8)) (2 ^ 16) (2 ^ 11) 256 256 2 8 26).uint 500 32
    |>.uint 2 32).cell
/-- Parameter 43 v2 with no public library allowed in a masterchain account. -/
def limitsNoPublicLibs (cfg : Cell) : Cell :=
  withParam cfg 43 (Configs.limitsV2 (Configs.defaultsV1 (({} : W).uint 2 8)) (2 ^ 16) (2 ^ 11) 0 256 2 8 26).cell

/-- The accounts whose gas limit `override_gas_limit` raises (transaction.cpp:1356-1376): from version 5
and from version 9. -/
def override5 : BitString := natToBits 0xFFBFD8F5AE5B2E1C7C3614885CB02145483DFAEE575F0DD08A72C366369211CD 256
def override9 : BitString := natToBits 0x5e4a5f9dba638789e6770c990d2959237aca3bc19d15a734782c26cb19343cc6 256

/-- A program that stores the bounce and bounced flags, the forwarding fee, the logical time, the time
and the original value of the inbound message (`INMSG_*`, version 11) in c4. -/
def inMsgParamsProg : List Instr :=
  let stir (n : Nat) : Instr := .stIntFixed false true false n
  [.newc, .tonEnvOp (.inMsgParam 0), stir 8, .tonEnvOp (.inMsgParam 1), stir 8, .tonEnvOp (.inMsgParam 3), stur 64,
   .tonEnvOp (.inMsgParam 4), stur 64, .tonEnvOp (.inMsgParam 5), stur 32, .tonEnvOp (.inMsgParam 6), stur 128, .endc,
   .popCtr 4]

/-- The case context: the version and its configuration. -/
structure Ctx where
  v : Nat
  cfg : Cell
  cfgAddr : BitString

def Ctx.case (x : Ctx) (name : String) (acc msg : Cell) (config : Cell := x.cfg) (now : Nat := 1700000200) : TxCase :=
  { name := s!"v{x.v}/cov/{name}", config, account := acc, msg, now, lt := 3000000, seed }

def Ctx.tt (x : Ctx) (name : String) (acc : Cell) (isTock : Bool := false) (config : Cell := x.cfg)
    (now : Nat := 1700000200) : TxCase :=
  { x.case name acc Cell.empty config now with tickTock := some isTock }

/-- An active basechain account at `a1` with 1 TON. -/
def active (code : Cell) (bal : Nat := 1000000000) : Cell := mkAccount 0 a1 (.active code data0) bal 1700000000 0 1000

/-! ## Configuration, storage and credit phases -/

/-- `fetch_config_params` (transaction.cpp:4270-4370): without parameter 18, 20, 21, 24, 25 or 14, or
with an invalid one, the emulator fails, except without parameter 14 (block creation fees, not used by a
transaction); parameter 20 is read for an account of any workchain (`get_gas_limits_prices(true)`, not
exactly), exactly as the gas prices of a masterchain account. `ComputePhaseConfig::is_address_suspended`
(1244-1255) without parameter 44, with its time passed and with a malformed dictionary; an address it
suspends (1876-1879, `cskip_suspended` 3922). -/
def configCases (x : Ctx) : Array TxCase := Id.run do
  let mut out : Array TxCase := #[]
  let bad : Cell := (({} : W).uint 0xff 8).cell
  let msg := intMsg 0 a1 100000000 false none #[]
  let mcAcc := mkAccount (-1) a1 (.active accept data0) 1000000000 1700000000 0 1000
  let mcMsg := intMsg (-1) a1 100000000 false none #[]
  for n in [18, 20, 21, 24, 25, 14] do
    out := out.push (x.case s!"config/no-p{n}" (active accept) msg (withoutParam x.cfg n))
    -- parameter 18 a dictionary with an entry of another tag (a malformed dictionary makes
    -- `get_storage_prices` throw, mc-config.cpp:751: the emulator aborts)
    let b := if n == 18 then
        let e : W := ((((({} : W).uint 0xcd 8).uint 0 32).uint 1 64).uint 500 64 |>.uint 1000 64).uint 500000 64
        match dictSetBuilderWithCells none (natToBits 0 32) { bits := e.bits, refs := #[] } .set with
        | .ok (some r, _, _, _) => r
        | _ => bad
      else bad
    out := out.push (x.case s!"config/bad-p{n}" (active accept) msg (withParam x.cfg n b))
  for n in [20, 21] do
    out := out.push (x.case s!"config/mc/no-p{n}" mcAcc mcMsg (withoutParam x.cfg n))
  -- `gas_flat_pfx` before `gas_prices#dd`: read for the gas prices of the account's workchain, not as
  -- the masterchain's (`do_get_gas_limits_prices` then reads `dd` from the start of the cell)
  let flatDd : Cell :=
    let p := Configs.gasPlain 26214400 1000000 10000 10000000 100000000 1000000000
    Cell.mkOrdinary ((((({} : W).uint 0xd1 8).uint 100 64).uint 40000 64).bits ++ p.bits)
  out := out.push (x.case "config/p21-flat-dd" (active accept) msg (withParam x.cfg 21 flatDd))
  out := out.push (x.case "config/p20-flat-dd" (active accept) msg (withParam x.cfg 20 flatDd))
  -- parameter 20 with one more bit
  if let some c := Config.decode x.cfg then
    if let some p20 := c.param 20 then
      let longer := withParam x.cfg 20 (Cell.mkOrdinary (p20.bits.push true) p20.refs)
      out := out.push (x.case "config/p20-longer" (active accept) msg longer)
      out := out.push (x.case "config/mc/p20-longer" mcAcc mcMsg longer)
  -- deployments and parameter 44
  let si := stateInitX (some accept) (some data0)
  let addr := bytesToBits si.hashBytes
  let deploy (name : String) (config : Cell) : TxCase :=
    x.case s!"suspended/{name}" (mkAccount 0 addr .none 0 0 0 0) (intMsg 0 addr 100000000 false (some si) #[]) config
  out := out.push (deploy "listed" (withSuspended x.cfg [(0, addr)] 1800000000))
  out := out.push (x.case "suspended/listed-uninit-ext" (mkAccount 0 addr .uninit 50000000 1700000000 0 1000)
    (extMsg 0 addr (some si) #[]) (withSuspended x.cfg [(0, addr)] 1800000000))
  out := out.push (deploy "until-passed" (withSuspended x.cfg [(0, addr)] 1700000200))
  out := out.push (deploy "no-param" (withoutParam x.cfg 44))
  out := out.push (deploy "malformed" (withParam x.cfg 44 (((({} : W).uint 0 8).ref Cell.empty |>.bool true).uint 1800000000 32).cell))
  return out

/-- `prepare_storage_phase` (transaction.cpp:1057-1119): `last_paid` after `now` (the emulator fails); a
special account (parameter 31: the configuration address) in debt beyond its balance keeps its due
payment (1084); `compute_storage_fees` (791-809) with storage prices from after `now`, from after
`last_paid` only, and one starting after `now`. `prepare_credit_phase` (1150-1152): an extra currency of
the message added to the balance's does not fit `VarUInteger 32`, the emulator fails. -/
def storageCreditCases (x : Ctx) : Array TxCase := Id.run do
  let mut out : Array TxCase := #[]
  out := out.push (x.case "storage/last-paid-later" (mkAccount 0 a1 (.active accept data0) 1000000000 1700000300 0 1000)
    (intMsg 0 a1 100000000 false none #[]))
  let special := mkAccount (-1) x.cfgAddr (.active accept data0) 1000 1700000000 5000 1000
  out := out.push (x.case "storage/special-due" special (intMsg (-1) x.cfgAddr 1000 false none #[]))
  out := out.push (x.case "storage/special-due/bounce" special (intMsg (-1) x.cfgAddr 1000 true none #[]))
  out := out.push (x.tt "storage/special-due/tick" special)
  -- `StoragePrices::compute_storage_fees` (791-809): prices valid only after `now`, valid only after
  -- `last_paid` (no earlier price: `i` stays 0), a price that starts after `now`
  let old := mkAccount 0 a1 (.active accept data0) 1000000000 1600000000 0 1000
  for (pname, entries) in [("later", [(1800000000, 1, 500, 1000, 500000)]),
      ("after-last-paid", [(1650000000, 1, 500, 1000, 500000)]),
      ("future-entry", [(0, 1, 500, 1000, 500000), (1800000000, 1000, 1000000, 100000, 10000000)])] do
    out := out.push (x.case s!"storage/prices-{pname}" old (intMsg 0 a1 100000000 false none #[])
      (withParam x.cfg 18 (Configs.storagePrices entries)))
  let full := mkAccount 0 a1 (.active accept data0) 1000000000 1700000000 0 1000 (extraOf [(7, amt (2 ^ 248 - 1))])
  for bounce in [false, true] do
    out := out.push (x.case s!"credit/extra-overflow/{if bounce then "bounce" else "plain"}" full
      (intMsg 0 a1 100000000 bounce none #[] (extra := extraOf [(7, amt 1)])))
  return out

/-- `override_gas_limit` and `Transaction::gas_bought_for` (transaction.cpp:1379-1414): the accounts
whose gas limit is raised, before and from the version that raises it and after its time: tick-tock (the
gas limit is all the balance buys: the whole raised limit, a part, nothing below the flat price) and a
message whose value buys the whole limit. -/
def gasOverrideCases (x : Ctx) : Array TxCase := Id.run do
  let mut out : Array TxCase := #[]
  for (aname, addr) in [("from5", override5), ("from9", override9)] do
    for (bname, bal) in [("rich", 30000000000), ("mid", 1000000000), ("poor", 30000)] do
      out := out.push (x.tt s!"gas-override/{aname}/{bname}" (mkAccount 0 addr (.active accept data0) bal 1700000000 0 1000))
    out := out.push (x.case s!"gas-override/{aname}/int-value" (mkAccount 0 addr (.active accept data0) 1000000000 1700000000 0 1000)
      (intMsg 0 addr 30000000000 false none #[]))
    out := out.push (x.tt s!"gas-override/{aname}/later" (mkAccount 0 addr (.active accept data0) 30000000000 1700000000 0 1000)
      (now := 1740787200))
  return out

/-! ## Compute phase -/

/-- The `exit_arg` of a failed compute phase (transaction.cpp:2055-2060): the top of the stack not an
integer, not 32 bits; an external message not accepted with an empty stack. `GETFORWARDFEE`, which calls
`MsgPrices::compute_fwd_fees256` (2454-2457). A code-less active account (`VmState::run` of no code:
`fatal`, vm.cpp:513-516). A precompiled code (parameter 45) of a special account with an external
message (the credit of 1956). -/
def computeCases (x : Ctx) : Array TxCase := Id.run do
  let mut out : Array TxCase := #[]
  let progs : List (String × List Instr) := [("cell", [.pushRef data0, .throwArg 42]),
    ("int40", [.pushInt (.num (2 ^ 40)), .throwArg 42]), ("neg", [.pushInt (.num (-5)), .throwArg 42])]
  for (pname, prog) in progs do
    out := out.push (x.case s!"exit-arg/{pname}" (active (asm prog)) (intMsg 0 a1 100000000 true none #[]))
  out := out.push (x.case "exit-arg/ext-empty-stack" (active (asm [.blkdrop 5])) (extMsg 0 a1 none #[]))
  -- GETFORWARDFEE (version 6) is `MsgPrices::compute_fwd_fees256` of transaction.cpp (2454-2457)
  for (mname, mc) in [("bc", 0), ("mc", -1)] do
    out := out.push (x.case s!"get-forward-fee/{mname}" (active (asm [.pushInt (.num 2), .pushInt (.num 1000), .pushInt (.num mc),
      .tonEnvOp .getForwardFee, .newc, .stIntFixed true false false 64, .endc, .popCtr 4])) (intMsg 0 a1 100000000 false none #[]))
  let noCode := mkAccount 0 a1 (.active Cell.empty data0) 1000000000 1700000000 0 1000 (noCode := true)
  out := out.push (x.case "no-code/int" noCode (intMsg 0 a1 100000000 false none #[]))
  out := out.push (x.case "no-code/int-bounce" noCode (intMsg 0 a1 100000000 true none #[]))
  out := out.push (x.case "no-code/ext" noCode (extMsg 0 a1 none #[]))
  out := out.push (x.tt "no-code/tick" noCode)
  -- a precompiled code (parameter 45) on a special account with an external message: the VM gets the
  -- credit of the configuration's limit (1956)
  let cfgP := withPrecompiled x.cfg [(accept, 100)]
  out := out.push (x.case "precompiled/special-ext" (mkAccount (-1) x.cfgAddr (.active accept data0) 1000000000 1700000000 0 1000)
    (extMsg (-1) x.cfgAddr none #[]) cfgP)
  return out

/-- Deployments with the `StateInit` fields `unpack_msg_state` reads (transaction.cpp:1664-1702): a
fixed prefix length of 3 (also at an address whose first 3 bits differ from the hash, the legacy
`recompute_tmp_addr` 393-430 before version 10, there also in workchain 1000), 9 (above
`max_acc_fixed_prefix_length` from version 10, 1900-1903), 31 (`check_addr_rewrite_length`, 1887-1891);
tick-tock flags; no code; in the masterchain (`max_acc_public_libraries` 0 for a new account,
1693-1702), with a public library. Unfreezing with a fixed prefix length (allowed for a frozen account
from version 16). The new state with them (`compute_state` 3612-3617). -/
def deployCases (x : Ctx) : Array TxCase := Id.run do
  let mut out : Array TxCase := #[]
  let si (fpl : Option Nat) (special : Option (Bool × Bool)) : Cell := stateInitX (some acceptC7) (some data0) fpl special
  for (name, s) in [("fpl3", si (some 3) none), ("fpl9", si (some 9) none), ("fpl31", si (some 31) none),
      ("tick-tock", si none (some (true, true))), ("tock-fpl2", si (some 2) (some (false, true))),
      ("no-code", stateInitX none (some data0))] do
    let addr := bytesToBits s.hashBytes
    out := out.push (x.case s!"deploy/{name}/none" (mkAccount 0 addr .none 0 0 0 0) (intMsg 0 addr 100000000 false (some s) #[]))
    out := out.push (x.case s!"deploy/{name}/uninit-ext" (mkAccount 0 addr .uninit 50000000 1700000000 0 1000)
      (extMsg 0 addr (some s) #[]))
  let s3 := si (some 3) none
  let h := bytesToBits s3.hashBytes
  let addr' := (h.extract 0 3).map (!·) ++ h.extract 3 256
  out := out.push (x.case "deploy/fpl3-prefix/none" (mkAccount 0 addr' .none 0 0 0 0) (intMsg 0 addr' 100000000 false (some s3) #[]))
  out := out.push (x.case "deploy/fpl3-prefix/uninit" (mkAccount 0 addr' .uninit 50000000 1700000000 0 1000)
    (intMsg 0 addr' 100000000 false (some s3) #[]))
  -- in workchain 1000 (`addr_var`): before version 10 `recompute_tmp_addr` builds an `addr_var` (418-425)
  out := out.push (x.case "deploy/fpl3-prefix/wc1000" (mkAccount 1000 addr' .none 0 0 0 0)
    (intMsg 1000 addr' 100000000 false (some s3) #[]))
  let smc := si none none
  let mcAddr := bytesToBits smc.hashBytes
  out := out.push (x.case "deploy/mc" (mkAccount (-1) mcAddr .none 0 0 0 0) (intMsg (-1) mcAddr 100000000 false (some smc) #[]))
  let slib := stateInitX (some accept) (some data0) (library := simpleLibs true [libCell])
  let libAddr := bytesToBits slib.hashBytes
  out := out.push (x.case "deploy/mc-public-lib" (mkAccount (-1) libAddr .none 0 0 0 0)
    (intMsg (-1) libAddr 100000000 false (some slib) #[]))
  out := out.push (x.case "unfreeze/fpl3" (mkAccount 0 a1 (.frozen h) 50000000 1700000000 0 1000)
    (intMsg 0 a1 100000000 false (some s3) #[]))
  return out

/-- Active accounts with a fixed prefix length or tick-tock flags in their state (`unpack_state`
transaction.cpp:315-325): a message, a freeze (the frozen hash of a `StateInit` with them, 3582-3584),
tick-tock of a special account. -/
def activeStateCases (x : Ctx) : Array TxCase := Id.run do
  let mut out : Array TxCase := #[]
  for (name, fpl, sp) in [("tick-tock", none, some (true, true)), ("fpl4", some 4, none),
      ("fpl4-tock", some 4, some (false, true))] do
    out := out.push (x.case s!"active-state/{name}/int" (mkAccount 0 a1 (.active accept data0) 1000000000 1700000000 0 1000
      (fpl := fpl) (special := sp)) (intMsg 0 a1 100000000 false none #[]))
    out := out.push (x.case s!"active-state/{name}/freeze" (mkAccount 0 a1 (.active accept data0) 1000 1700000000 200000000 1000
      (fpl := fpl) (special := sp)) (intMsg 0 a1 1000 false none #[]))
  out := out.push (x.tt "active-state/tick-tock/special-tick" (mkAccount (-1) x.cfgAddr (.active accept data0) 1000000000
    1700000000 0 1000 (special := some (true, true))))
  return out

/-- An active account receiving a `StateInit` (transaction.cpp:1909-1924): with an internal message
(only its libraries are used: before version 15 the VM finds the library of the account's code in it,
1717-1718), with an external one whose hash is not the address (from version 8 1911-1915, before
1921-1924) or is. -/
def activeInitCases (x : Ctx) : Array TxCase := Id.run do
  let mut out : Array TxCase := #[]
  let sOther := stateInitX (some accept) (some data1)
  out := out.push (x.case "active-init/int" (active accept) (intMsg 0 a1 100000000 false (some sOther) #[]))
  out := out.push (x.case "active-init/ext-other" (active accept) (extMsg 0 a1 (some sOther) #[]))
  let sSelf := stateInitX (some accept) (some data0)
  let selfAddr := bytesToBits sSelf.hashBytes
  out := out.push (x.case "active-init/ext-self" (mkAccount 0 selfAddr (.active accept data0) 1000000000 1700000000 0 1000)
    (extMsg 0 selfAddr (some sSelf) #[]))
  let body := asm [.tonEnvOp .accept, .pushInt (.num 7), .pop 0]
  for (lname, pub) in [("private", false), ("public", true)] do
    let sLib := stateInitX none none (library := simpleLibs pub [body])
    out := out.push (x.case s!"active-init/msg-library-{lname}" (active (libraryCellOf body))
      (intMsgX (stdA 0 a1) 100000000 (bounce := true) (init := some sLib)))
  return out

/-! ## Action phase -/

/-- The action list (transaction.cpp:2131-2192): c5 a library cell, its second node one, 256 and 255
nodes, an invalid `action_send_msg` without the modes 2 and 16, a tag without a mode;
`action_change_library` (2346-2414): mode 16 (from version 4) and above 2, a library by hash (in the
account, unknown), larger than `max_library_cells` or of Merkle depth 3 (2402-2403), a malformed library
dictionary in the account (`VmError`: 42), a public library of an ordinary masterchain account (counted,
3263; none allowed: 50); `action_reserve_currency` (3165-3173): mode 16 (from version 4), mode 32. -/
def actionListCases (x : Ctx) (perVersion : Bool) : Array TxCase := Id.run do
  let mut out : Array TxCase := #[]
  let libHash := bytesToBits libCell.hashBytes
  let lib2 := Cell.mkOrdinary (natToBits 0xc0de 16) #[Cell.mkOrdinary (natToBits 5 8)]
  let msg := intMsg 0 a1 100000000 false none #[]
  let special (code : Cell) (library : Option Cell := none) : Cell :=
    mkAccount (-1) x.cfgAddr (.active code data0) 1000000000 1700000000 0 1000 (library := library)
  let spMsg := intMsg (-1) x.cfgAddr 100000000 false none #[]
  if perVersion then
    out := out.push (x.case "lib/mode17-ref" (active (asm (setC5 (actChangeLib 17 (.inr libCell))))) msg)
    out := out.push (x.case "lib/mode18-ref/special" (special (asm (setC5 (actChangeLib 18 (.inr libCell))))) spMsg)
    out := out.push (x.case "reserve/mode16" (active (asm (setC5 (actReserve 16 1000)))) msg)
    -- a public library of an ordinary masterchain account (from version 15 only special accounts)
    let mcPub := mkAccount (-1) a1 (.active (asm [.pushRef libCell, .pushInt (.num 2), .tonEnvOp .setLibCode]) data0)
      1000000000 1700000000 0 1000
    let mcMsg := intMsg (-1) a1 100000000 false none #[]
    out := out.push (x.case "lib/mc-public" mcPub mcMsg)
    out := out.push (x.case "lib/mc-public/none-allowed" mcPub mcMsg (limitsNoPublicLibs x.cfg))
  else
    for (pname, c5) in [("c5-library-cell", libraryCellOf libCell),
        ("c5-second-library-cell", node (libraryCellOf libCell) (natToBits 0x36e6b809 32 ++ natToBits 0 8 ++ gramsBits 5 ++ #[false])),
        ("c5-256-nodes", chain 256), ("c5-255-nodes", chain 255),
        ("c5-bad-msg-mode0", node Cell.empty (natToBits 0x0ec3c86d 32 ++ natToBits 0 8) #[Cell.empty]),
        ("c5-bad-msg-mode1", node Cell.empty (natToBits 0x0ec3c86d 32 ++ natToBits 1 8) #[Cell.empty]),
        ("c5-send-tag-only", node Cell.empty (natToBits 0x0ec3c86d 32) #[Cell.empty]),
        ("lib/mode3", actChangeLib 3 (.inr libCell)), ("reserve/mode32", actReserve 32 1000)] do
      out := out.push (x.case pname (active (asm (setC5 c5))) msg)
    let accLib := simpleLibs false [libCell]
    for (pname, c5) in [("lib/hash/same", actChangeLib 2 (.inl libHash)), ("lib/hash/make-private", actChangeLib 1 (.inl libHash)),
        ("lib/hash/unknown", actChangeLib 2 (.inl (natToBits 5 256))), ("lib/hash/remove", actChangeLib 0 (.inl libHash))] do
      out := out.push (x.case pname (special (asm (setC5 c5)) (simpleLibs true [libCell])) spMsg)
    out := out.push (x.case "lib/hash/make-public" (special (asm (setC5 (actChangeLib 2 (.inl libHash)))) accLib) spMsg)
    out := out.push (x.case "lib/too-big" (special (asm (setC5 (actChangeLib 2 (.inr lib2))))) spMsg (limitsSmall x.cfg))
    out := out.push (x.case "lib/merkle3" (special (asm (setC5 (actChangeLib 2 (.inr (merkleProofs data1 3)))))) spMsg)
    out := out.push (x.case "lib/malformed-dict" (special (asm [.pushRef libCell, .pushInt (.num 2), .tonEnvOp .setLibCode])
      (some Cell.empty)) spMsg)
    -- the account's entry at the hash of `libCell` holds another root (`ShardAccount` validation does
    -- not compare them, 2387): by hash the library is not found (41), by reference it is added
    if let .ok (some wrong, _, _, _) := dictSetBuilderWithCells none libHash { bits := #[true], refs := #[lib2] } .set then
      out := out.push (x.case "lib/hash/key-mismatch" (special (asm (setC5 (actChangeLib 2 (.inl libHash)))) (some wrong)) spMsg)
      out := out.push (x.case "lib/ref/key-mismatch" (special (asm (setC5 (actChangeLib 2 (.inr libCell)))) (some wrong)) spMsg)
  return out

/-- `try_action_send_msg` (transaction.cpp:2700-3100) and the address checks (2520-2654): a message with
IHR enabled (before version 11 its fee, 2472-2475, 2914-2931), `extra_flags` 4 (from version 12: 45),
the forwarding fee and `extra_flags` with a leading zero byte (before version 8: invalid, 2771; from 12:
45), a `StateInit` whose library is no dictionary (2704-2706: from version 13 skipped with mode 2; after
a valid message), the `StateInit` inline with a body that does not fit after the rewrite (-2 twice,
2709-2723, 2217-2218), an external message to a long `addr_extern` (3080-3086) and with mode 64
(2751-2752), a message that does not fit even then (amounts of 15 bytes, an anycast destination, IHR:
39, 3030-3032) and one whose header alone does not (3026: the action phase fails), messages above the
size limits (2889-2892) or with a Merkle depth of 3 (2894-2897), the total of a transaction (from
version 15: 47, 3092-3096); destinations `addr_var` (repacked), anycast (rewritten before version 10,
invalid from it), an invalid length, a workchain not accepting messages; sources `addr_extern` and the
account's own address. An exotic body or `^StateInit` (refused by the validation of the action list, 2169). -/
def sendCases (x : Ctx) (perVersion : Bool) : Array TxCase := Id.run do
  let mut out : Array TxCase := #[]
  let msg := intMsg 0 a1 100000000 false none #[]
  let send (pname : String) (m : Cell) (mode : Nat) (config : Cell := x.cfg) : TxCase :=
    x.case s!"send/{pname}" (active (asm (sendRaw m mode))) msg config
  let dest := stdA 0 other
  let pfx5 : BitString := natToBits 0b10101 5
  if perVersion then
    out := out.push (send "ihr" (relaxedX dest 10000000 (ihrDisabled := false)) 0)
    out := out.push (send "extra-flags4" (relaxedX dest 10000000 (extraFlags := gramsBits 4)) 0)
    out := out.push (send "extra-flags4-skip" (relaxedX dest 10000000 (extraFlags := gramsBits 4)) 2)
    out := out.push (send "fwd-fee-padded" (relaxedX dest 10000000 (fwdFee := gramsPadded 100)) 0)
    out := out.push (send "extra-flags-padded" (relaxedX dest 10000000 (extraFlags := gramsPadded 100)) 0)
    out := out.push (send "extra-flags-padded1" (relaxedX dest 10000000 (extraFlags := gramsPadded 1)) 0)
    -- an exotic body reference: the action list is invalid (from version 8 mode 2 skips it)
    out := out.push (send "body-exotic" (relaxedX dest 10000000 (bodyRef := some (merkleProofs data1 1))) 0)
    out := out.push (send "body-exotic-skip" (relaxedX dest 10000000 (bodyRef := some (merkleProofs data1 1))) 2)
    let badLib := relaxedX dest 10000000 (init := some (stateInitX (some accept) (some data0) (library := some Cell.empty)))
    out := out.push (send "bad-lib" badLib 0)
    out := out.push (send "bad-lib-skip" badLib 2)
    out := out.push (x.case "send/valid-then-bad-lib" (active (asm (sendRaw (relaxedX dest 10000000) 0 ++ sendRaw badLib 0))) msg)
    out := out.push (send "anycast-dest" (relaxedX (stdA 0 other (some pfx5)) 10000000) 0)
    -- an anycast account whose message names its exact address as the source: before version 10
    -- `my_addr` keeps the prefix and only `my_addr_exact` matches (2530)
    let pfx3 : BitString := natToBits 0b101 3
    let exact := pfx3 ++ a1.extract 3 256
    out := out.push (x.case "send/src-exact-anycast"
      (mkAccount 0 a1 (.active (asm (sendRaw (relaxedX dest 10000000 (src := stdA 0 exact)) 0)) data0) 1000000000 1700000000 0 1000
        (anycast := some pfx3))
      (intMsg 0 exact 100000000 false none #[]))
    -- workchain 1000 open: an anycast `addr_var` destination of 256 bits is rewritten before version 10
    -- and repacked as `addr_var` (2640-2650), invalid from version 10 (36)
    out := out.push (send "addr-var-dest-wc1000-anycast" (relaxedX (((((({} : W).uint 3 2).bool true).uint 5 5).bitStr pfx5
      |>.uint 256 9 |>.int 1000 32 |>.bitStr other).bits) 10000000) 0 (withWorkchain x.cfg 1000 true))
    out := out.push (send "anycast-dest-mine" (relaxedX (stdA 0 other (some (a1.extract 0 5))) 10000000) 0)
    if x.v ≥ 15 then
      out := out.push (send "ext-total" (relaxedExtX 8 (natToBits 0 300)) 0 (limitsTotal x.cfg))
      out := out.push (send "ext-total-skip" (relaxedExtX 8 (natToBits 0 300)) 2 (limitsTotal x.cfg))
    if [3, 4, 7].contains x.v then
      -- 15-byte amounts (value, IHR and forwarding fees, before version 8), an anycast destination of
      -- depth `d`: the rewritten header has 1012 + d bits; with `init` and `body` it does not fit at
      -- d = 10 (39), alone it does not at d = 30 (`csr_pack` fails: the action phase fails)
      let big : Nat := 2 ^ 116
      for d in [10, 30] do
        let m := relaxedX (stdA 0 other (some (natToBits 0 d))) big (ihrDisabled := false) (extraFlags := gramsBits big)
          (fwdFee := gramsBits big)
        for mode in [1, 3] do
          out := out.push (x.case s!"send/never-fits/d{d}/{mode}" (active (asm (sendRaw m mode)) (2 ^ 119)) msg)
  else
    out := out.push (send "init-inline-big-body" (relaxedX dest 10000000 (init := some (stateInitX (some accept) (some data0)))
      (initInline := true) (body := natToBits 0 600)) 0)
    out := out.push (send "ext-long-dest" (relaxedExtX 511 (natToBits 0 300)) 0)
    out := out.push (send "ext-mode64" (relaxedExt (natToBits 5 8)) 64)
    out := out.push (send "too-many-bits" (relaxedX dest 10000000
      (bodyRef := some (Cell.mkOrdinary (natToBits 0 600) #[Cell.mkOrdinary (natToBits 0 600)]))) 0 (limitsSmall x.cfg))
    out := out.push (send "too-many-cells" (relaxedX dest 10000000 (bodyRef := some (chain 4))) 0 (limitsSmall x.cfg))
    for n in [2, 3] do
      out := out.push (send s!"merkle{n}" (relaxedX dest 10000000 (bodyRef := some (Cell.mkOrdinary #[] #[merkleProofs data1 n]))) 0)
    -- an exotic `^StateInit` (the generated `validate_ref` refuses it)
    out := out.push (send "init-exotic" (relaxedX dest 10000000 (init := some (libraryCellOf (stateInitX (some accept) (some data0))))) 0)
    out := out.push (send "addr-var-dest" (relaxedX (varA 0 other) 10000000) 0)
    out := out.push (send "addr-var-dest-len100" (relaxedX (varA 0 (natToBits 1 100)) 10000000) 0)
    out := out.push (send "addr-var-dest-mc-len100" (relaxedX (varA (-1) (natToBits 1 100)) 10000000) 0)
    -- `addr_var` of 256 bits outside -128..127 is not repacked (2569): unknown workchains (36), and
    -- workchain 1000 open (sent as it is)
    for wc in [(1000 : Int), -1000] do
      out := out.push (send s!"addr-var-dest-wc{wc}" (relaxedX (varA wc other) 10000000) 0)
    out := out.push (send "addr-var-dest-wc1000-open" (relaxedX (varA 1000 other) 10000000) 0 (withWorkchain x.cfg 1000 true))
    out := out.push (send "closed-workchain" (relaxedX (stdA 7 other) 10000000) 0 (withClosedWorkchain x.cfg 7))
    out := out.push (send "closed-workchain-skip" (relaxedX (stdA 7 other) 10000000) 2 (withClosedWorkchain x.cfg 7))
    out := out.push (send "src-extern" (relaxedX dest 10000000 (src := #[false, true] ++ natToBits 8 9 ++ natToBits 0x77 8)) 0)
    out := out.push (send "src-self" (relaxedX dest 10000000 (src := stdA 0 a1)) 0)
  return out

/-- Tick-tock transactions have no inbound message: `msg_balance_remaining` is not a valid amount
(transaction.cpp:2839). Mode 64 before version 10 then fails (`req += msg_balance_remaining` invalidates
the value: 37, 2953-2965); from version 10 (2951), and with mode 65, C++ dereferences its null grams and
aborts, so no case has them. -/
def tickTockCarryCases (x : Ctx) : Array TxCase := Id.run do
  let mut out : Array TxCase := #[]
  for (vname, value) in [("zero", 0), ("value", 10000000)] do
    let code := asm (sendRaw (relaxedInt 0 other value) 64)
    for (aname, wc, addr) in [("special", (-1 : Int), x.cfgAddr), ("mc", -1, a1), ("bc", 0, a1)] do
      out := out.push (x.tt s!"tick-tock/send-carry/{vname}/{aname}" (mkAccount wc addr (.active code data0) 1000000000 1700000000 0 1000))
  return out

/-! ## Bounce phase, inbound message, account -/

/-- `prepare_bounce_phase` (transaction.cpp:3374-3496): a body in a reference (3387-3388), a value of
2^64 (3459-3460) whose old-format bounce body does not fit the message (3488-3493); sources the bounce
goes back to: anycast (rewritten to the account's prefix) or not, an unknown workchain, one not
accepting messages, `addr_var` of 100 bits in workchain 0 and -1 (the emulator fails, 3433-3436). -/
def bounceCases (x : Ctx) : Array TxCase := Id.run do
  let mut out : Array TxCase := #[]
  let thrower := active (asm [.throw 42])
  let dest := stdA 0 a1
  out := out.push (x.case "bounce/body-ref" thrower (intMsgX dest 100000000 (bounce := true)
    (bodyRef := some (Cell.mkOrdinary (natToBits 0xabcdef 300)))))
  out := out.push (x.case "bounce/value-2^64" thrower (intMsgX dest (2 ^ 64) (bounce := true) (body := natToBits 5 300)))
  for (sname, src, config) in [("anycast", stdA 0 src0 (some (natToBits 0b10101 5)), x.cfg),
      ("anycast-mine", stdA 0 src0 (some (a1.extract 0 5)), x.cfg),
      ("unknown-wc", stdA 5 src0, x.cfg), ("closed-wc", stdA 7 src0, withClosedWorkchain x.cfg 7),
      ("var-len100", varA 0 (natToBits 1 100), x.cfg), ("mc-var-len100", varA (-1) (natToBits 1 100), x.cfg)] do
    out := out.push (x.case s!"bounce/src-{sname}" thrower (intMsgX dest 100000000 (bounce := true) (src := src)) config)
  return out

/-- `unpack_input_msg` (transaction.cpp:877-1046): a `created_lt` after the transaction's (921-923); a
header without the `init` bit, without the body bit, a body reference missing or with another one, a
`StateInit` inline or in a reference whose library is no dictionary, an `ext_out_msg_info` header, an
`ext_in_msg_info` tag alone (the emulator fails); an external message to `addr_var` (from version 10
rejected, 940-942), deeper or larger than parameter 43 allows (951-963), of Merkle depth 2 and 3
(965-967). The `INMSG_*` of a bounced message with a forwarding fee (c7 from version 11, 1597-1599). -/
def inMsgCases (x : Ctx) : Array TxCase := Id.run do
  let mut out : Array TxCase := #[]
  let acc := active accept
  let dest := stdA 0 a1
  out := out.push (x.case "in-msg/created-lt-later" acc (intMsgX dest 100000000 (createdLt := 5000000)))
  let header : W := (((((((({} : W).bool false).bool true).bool false).bool false).bitStr (stdA 0 src0)).bitStr dest).grams 100000000
    |>.bool false |>.grams 0 |>.grams 0 |>.uint 2000 64 |>.uint 1700000100 32)
  let badLib := stateInitX (some accept) (some data0) (library := some Cell.empty)
  for (mname, m) in [("no-init-bit", header.cell), ("no-body-bit", (header.bool false).cell),
      ("body-ref-none", ((header.bool false).bool true).cell),
      ("body-ref-two", (((header.bool false).bool true).ref data0 |>.ref data1).cell),
      ("init-inline-bad-lib", intMsgX dest 100000000 (init := some badLib) (initInline := true)),
      ("init-ref-bad-lib", intMsgX dest 100000000 (init := some badLib)),
      ("ext-out-header", ((((((({} : W).uint 3 2).bitStr (stdA 0 src0)).uint 0 2).uint 0 64).uint 0 32).bool false |>.bool false).cell)] do
    out := out.push (x.case s!"in-msg/{mname}" acc m)
  out := out.push (x.case "in-msg/ext-in-tag-only" acc (Cell.mkOrdinary #[true, false]))
  out := out.push (x.case "in-msg/ext-addr-var" acc ((((({} : W).uint 2 2).uint 0 2).bitStr (varA 0 a1) |>.grams 0 |>.bool false).bool false).cell)
  -- a Merkle depth above 2 (965-967)
  for n in [2, 3] do
    out := out.push (x.case s!"in-msg/ext-merkle{n}" acc (extMsgRef 0 a1 (Cell.mkOrdinary #[] #[merkleProofs data1 n])))
  out := out.push (x.case "in-msg/ext-deep" acc (extMsgRef 0 a1 (chain 2)) (limitsSmall x.cfg))
  out := out.push (x.case "in-msg/ext-large" acc (extMsgRef 0 a1 (Cell.mkOrdinary (natToBits 0 600) #[Cell.mkOrdinary (natToBits 0 600)]))
    (limitsSmall x.cfg))
  -- 5 cells of few bits (depth 2): above `max_msg_cells` only (961)
  out := out.push (x.case "in-msg/ext-many-cells" acc
    (extMsgRef 0 a1 (Cell.mkOrdinary #[] ((List.range 4).toArray.map fun i => Cell.mkOrdinary (natToBits (i + 1) 8)))) (limitsSmall x.cfg))
  let params := active (asm inMsgParamsProg)
  out := out.push (x.case "in-msg/params-bounced" params (intMsgX dest 100000000 (bounced := true) (fwdFee := 12345)))
  return out

/-- The emulator's inputs are bags of cells, and `std_boc_deserialize` refuses a root of non-zero
level (crypto/vm/boc.cpp:975-977; emulator-extern.cpp:69, 383-387, 112-115, 120-123, 232-235): a
message whose body has a pruned branch (internal, external), an account whose data has one (also for
tick-tock), the emulator's libraries with one, a configuration with one (parameter 1000); the same
under a Merkle proof (level 0) runs. (A body in a reference that is itself an exotic cell is loaded
outside the VM, transaction.cpp:1031, and the emulator aborts: no case.) -/
def levelCases (x : Ctx) : Array TxCase := Id.run do
  let mut out : Array TxCase := #[]
  let acc := active accept
  let dest := stdA 0 a1
  let pr := prunedOf data1
  let underPruned := Cell.mkOrdinary #[] #[pr]
  out := out.push (x.case "level/msg-pruned" acc (intMsgX dest 100000000 (bodyRef := some pr)))
  out := out.push (x.case "level/msg-under-pruned" acc (intMsgX dest 100000000 (bodyRef := some underPruned)))
  let proof := Cell.mkOrdinary #[] #[merkleProofOf underPruned]
  out := out.push (x.case "level/msg-proof" acc (intMsgX dest 100000000 (bodyRef := some proof)))
  out := out.push (x.case "level/ext-pruned" acc (extMsgRef 0 a1 underPruned))
  out := out.push (x.case "level/ext-proof" acc (extMsgRef 0 a1 proof))
  for (dname, d) in [("pruned", underPruned), ("proof", proof)] do
    let a := mkAccount 0 a1 (.active accept d) 1000000000 1700000000 0 1000
    out := out.push (x.case s!"level/account-{dname}" a (intMsgX dest 100000000))
    out := out.push (x.tt s!"level/account-{dname}/tick" (mkAccount (-1) x.cfgAddr (.active accept d) 1000000000 1700000000 0 1000))
  out := out.push { x.case "level/libs-pruned" acc (intMsgX dest 100000000) with libs := globalLibsOf [pr] }
  out := out.push { x.case "level/libs-proof" acc (intMsgX dest 100000000) with libs := globalLibsOf [merkleProofOf underPruned] }
  out := out.push (x.case "level/config-pruned" acc (intMsgX dest 100000000) (withParam x.cfg 1000 underPruned))
  out := out.push (x.case "level/config-proof" acc (intMsgX dest 100000000) (withParam x.cfg 1000 (merkleProofOf underPruned)))
  return out

/-- `Account::unpack` (transaction.cpp:206-530) of accounts the emulator accepts: an `addr_var` address
(workchain 1000: `unpack_address` refuses it, 220-222), a `ShardAccount` whose logical time is not below
the account's (493), a storage dictionary hash (276-277: kept from version 11 in the basechain while the
references do not change); an anycast account in workchain 127 (`compute_my_addr` builds `addr_var` for
it, 350-372), and without anycast; an absent account at an `addr_var` destination (`init_new`, 555-561).
-/
def accountCases (x : Ctx) (perVersion : Bool) : Array TxCase := Id.run do
  let mut out : Array TxCase := #[]
  let h := natToBits 0x7777 256
  if perVersion then
    out := out.push (x.case "account/dict-hash/same" (mkAccount 0 a1 (.active accept data0) 1000000000 1700000000 0 1000
      (dictHash := some h)) (intMsg 0 a1 100000000 false none #[]))
    out := out.push (x.case "account/dict-hash/new-data" (mkAccount 0 a1 (.active (asm [.newc, .endc, .popCtr 4, .tonEnvOp .accept])
      data0) 1000000000 1700000000 0 1000 (dictHash := some h)) (intMsg 0 a1 100000000 false none #[]))
    out := out.push (x.case "account/dict-hash/mc" (mkAccount (-1) a1 (.active accept data0) 1000000000 1700000000 0 1000
      (dictHash := some h)) (intMsg (-1) a1 100000000 false none #[]))
  else
    out := out.push (x.case "account/addr-var" (mkAccount 1000 a1 (.active accept data0) 1000000000 1700000000 0 1000)
      (intMsg 1000 a1 100000000 false none #[]))
    let sa := active accept
    out := out.push (x.case "account/lt-not-below" (Cell.mkOrdinary (sa.bits.extract 0 256 ++ natToBits 1000 64) sa.refs)
      (intMsg 0 a1 100000000 false none #[]))
    let pfx : BitString := natToBits 0b101 3
    let actual := pfx ++ a1.extract 3 256
    out := out.push (x.case "account/wc127-anycast" (mkAccount 127 a1 (.active accept data0) 1000000000 1700000000 0 1000
      (anycast := some pfx)) (intMsg 127 actual 100000000 false none #[]))
    out := out.push (x.case "account/wc127" (mkAccount 127 a1 (.active accept data0) 1000000000 1700000000 0 1000)
      (intMsg 127 a1 100000000 false none #[]))
    out := out.push (x.case "account/none-addr-var" (mkAccount 1000 a1 .none 0 0 0 0) (intMsg 1000 a1 100000000 false none #[]))
    -- an absent account in workchain -1000, below `addr_std` (`init_new`, 555)
    out := out.push (x.case "account/none-wc-1000" (mkAccount (-1000) a1 .none 0 0 0 0) (intMsg (-1000) a1 100000000 false none #[]))
  return out

/-- `Transaction::compute_state` (transaction.cpp:3552-3735) fails when a field of the new account does
not fit its store, and the emulator fails (`serialize`, transaction-emulator.cpp:70-73):
* the balance (`balance.store`, 3572-3573: `Grams`, below 2^120) at 2^120 - 1 plus a message's value,
  of an active and of an uninitialized account; with a bounce the value goes back (it fits), and with a
  value of 1 the fees take more than it adds (it fits);
* the due payment (`t_Grams.store_integer_ref`, 3720) at 2^120 - 1 plus the storage fees (1060, 1082;
  kept from version 4, `enable_due_payment`, 1112-1113 and 4301), of an active account the storage phase
  freezes (1105) and of an uninitialized one with an extra currency (not deleted, 1089). Before version 4
  the due payment stays as it was, but the storage phase's `fees_due` does not fit either: `serialize`
  fails after `compute_state` (`serializeCases`);
* the bits of the storage statistics (`store_UInt7`, 3714-3715: `VarUInteger 7`, below 2^48) updated by
  the bits of the storage root when its references do not change (3704-3705, 64-bit arithmetic): at
  2^48 - 1 with a root that grows (paid up to now: no storage fees on them); at 0 with a root that grows
  (the difference is stored) and one that shrinks (the subtraction wraps around below 0, the store
  fails).
The cells of the storage statistics are the account's (below 2^48 as read) or counted from the cells of
the new storage: they cannot reach 2^48. -/
def stateCases (x : Ctx) : Array TxCase := Id.run do
  let mut out : Array TxCase := #[]
  let big := 2 ^ 120 - 1
  let msg (v : Nat) (bounce : Bool := false) : Cell := intMsg 0 a1 v bounce none #[]
  out := out.push (x.case "state/balance-overflow/active" (active accept big) (msg 10000000000))
  out := out.push (x.case "state/balance-overflow/uninit" (mkAccount 0 a1 .uninit big 1700000000 0 1000)
    (msg 10000000000))
  out := out.push (x.case "state/balance-overflow/uninit-bounce" (mkAccount 0 a1 .uninit big 1700000000 0 1000)
    (msg 10000000000 true))
  out := out.push (x.case "state/balance-max" (active accept big) (msg 1))
  out := out.push (x.case "state/due-overflow/active" (mkAccount 0 a1 (.active accept data0) 0 1600000000 big 1000)
    (msg 1000 true))
  out := out.push (x.case "state/due-overflow/uninit-extra"
    (mkAccount 0 a1 .uninit 0 1600000000 big 1000 (extraOf [(7, amt 1)])) (msg 1000 true))
  -- paid up to `now`: no storage fees on 2^48 - 1 bits
  out := out.push (x.case "state/used-bits/overflow"
    (mkAccount 0 a1 (.active accept data0) 1000 1700000200 0 1000 (usedBits := some (2 ^ 48 - 1))) (msg 10000000000))
  out := out.push (x.case "state/used-bits/below-root-grows"
    (mkAccount 0 a1 (.active accept data0) 1000 1700000000 0 1000 (usedBits := some 0)) (msg 10000000000))
  out := out.push (x.case "state/used-bits/below-root-shrinks"
    (mkAccount 0 a1 (.active accept data0) (2 ^ 32) 1700000000 0 1000 (usedBits := some 0)) (msg 1))
  return out

/-- `Transaction::serialize` (transaction.cpp:3746-3860) fails when a field of the transaction does not
fit its store, and the emulator fails (transaction-emulator.cpp:70-73):
* `total_fees:CurrencyCollection` (3773): an account at 2^120 - 1 with a due payment of 2^120 - 1, paid
  up to now (no storage fee), receives 2^120 - 1 (credit first, 1149): the storage phase collects
  the due payment (1069-1075), the gas fees take the total fees above 2^120 - 1;
* `storage_fees_collected:Grams` (3871): the same with storage fees on top of the due payment;
* `storage_fees_due:(Maybe Grams)` (3876): before version 4 the due payment cases of `stateCases`; an
  uninitialized account the storage phase deletes (1089-1092) whose message bounces back: no account
  is written (`account_none`), the due payment only in the storage phase;
* `gas_limit:(VarUInteger 7)` (3937): parameter 21 with a gas limit of 2^50 at one nanoton per gas and a
  message of 2^50 (`compute_gas_limits`, 1427-1450); at 2^48 - 1 it fits;
* `gas_credit:(Maybe (VarUInteger 3))` (3939): parameter 21 with a gas credit of 2^16 + 5 and an
  external message the contract accepts (1444); at 2^16 - 1 it fits;
* the bounce phase's fees (`t_Grams.store_long` of a `uint64` as `long long`, 4000, 4004-4005): an
  uninitialized account without a `StateInit` (no state, 1907) bounces the message, parameter 25 with
  a lump price of 2^63 or more (`compute_fwd_fees`, 2432-2438). A message of one TON: the model has
  no funds for the bounce (`req_fwd_fees` of 2^63, which `serialize` refuses); C++ compares the fee
  as `long long` (3459-3460), negative, goes on and fails at the bounced message's value, below zero
  (3478-3481). A message of 2^64 (more than 64 signed bits: never short of funds in C++): a fee of
  2^63 + 2^62 kept whole (`first_frac` 0) fails C++ at the message's `fwd_fee` (3484) and the
  model's `serialize` (`fwd_fees`); with `first_frac` 65535 the part collected (`msg_fees`, 2496-2498)
  is above 2^63 and both fail in `serialize`; a fee of 2^63 - 1 fits. -/
def serializeCases (x : Ctx) : Array TxCase := Id.run do
  let mut out : Array TxCase := #[]
  let big := 2 ^ 120 - 1
  out := out.push (x.case "serialize/total-fees" (mkAccount 0 a1 (.active accept data0) big 1700000200 big 1000)
    (intMsg 0 a1 big false none #[]))
  out := out.push (x.case "serialize/fees-collected" (mkAccount 0 a1 (.active accept data0) big 1600000000 big 1000)
    (intMsg 0 a1 big false none #[]))
  out := out.push (x.case "serialize/fees-due-deleted" (mkAccount 0 a1 .uninit 0 1600000000 big 1000)
    (intMsg 0 a1 1000000000 true none #[]))
  let gas (limit credit price : Nat) (flat : Nat × Nat) : Cell :=
    withParam x.cfg 21 (Configs.gasExt price limit limit credit (4 * limit) 100000000 1000000000 (some flat))
  out := out.push (x.case "serialize/gas-limit" (active accept (2 ^ 60)) (intMsg 0 a1 (2 ^ 50) false none #[])
    (gas (2 ^ 50) 10000 65536 (100, 100)))
  out := out.push (x.case "serialize/gas-limit-max" (active accept (2 ^ 60)) (intMsg 0 a1 (2 ^ 50) false none #[])
    (gas (2 ^ 48 - 1) 10000 65536 (100, 100)))
  out := out.push (x.case "serialize/gas-credit" (active accept) (extMsg 0 a1 none #[])
    (gas 1000000 (2 ^ 16 + 5) 26214400 (100, 40000)))
  out := out.push (x.case "serialize/gas-credit-max" (active accept) (extMsg 0 a1 none #[])
    (gas 1000000 (2 ^ 16 - 1) 26214400 (100, 40000)))
  let uninit := mkAccount 0 a1 .uninit 1000000000 1700000200 0 1000
  let fwd (lump first : Nat) : Cell := withParam x.cfg 25 (Configs.msgPrices lump 0 0 0 first 0)
  out := out.push (x.case "serialize/bounce-nofunds-fees" uninit (intMsg 0 a1 1000000000 true none #[])
    (fwd (2 ^ 63) 0))
  out := out.push (x.case "serialize/bounce-fwd-fees" uninit (intMsg 0 a1 (2 ^ 64) true none #[])
    (fwd (2 ^ 63 + 2 ^ 62) 0))
  out := out.push (x.case "serialize/bounce-msg-fees" uninit (intMsg 0 a1 (2 ^ 64) true none #[])
    (fwd (2 ^ 63 + 2 ^ 62) 65535))
  out := out.push (x.case "serialize/bounce-fees-max" uninit (intMsg 0 a1 (2 ^ 64) true none #[])
    (fwd (2 ^ 63 - 1) 0))
  return out

/-- The gas limits of the compute phase are `td::uint64`, those of the VM `long long` (`vm::GasLimits`,
transaction.cpp:1938, 1955); parameter 21 with gas limits of 2^63 or more, at a price of one nanoton
per 2^16 gas, a balance of 2^50 and a message of one TON:
* a gas limit of 2^64 - 2^20 above a flat limit of 100: `compute_max_gas_threshold` multiplies by
  the difference as `long long` (1271, refint.h:42), negative, so the threshold is below the message's
  value, which buys all the gas (1298): a gas limit of 2^64 - 2^20, negative for the VM, which runs out
  of gas at once, and which `serialize` refuses (`VarUInteger 7`, 3937);
* a gas limit of 2^63 + 2^20 above a flat limit of 2^20 + 1 (a difference below 2^63): the balance
  buys all of it, the message about 2^46 gas; `ACCEPT` sets the VM's gas limit to the maximum,
  negative (vm.cpp:414-419), the VM runs out of gas and `gas_used` (`std::min<long long>` as a
  `td::uint64`, 2016) is the maximum, which `serialize` refuses; a code without `ACCEPT` runs as with
  any limit; a precompiled code (parameter 45) runs with the configuration's gas limit (1955-1956),
  negative: out of gas, which fails (2027-2030). -/
def gas64Cases (x : Ctx) : Array TxCase := Id.run do
  let mut out : Array TxCase := #[]
  let gas (limit : Nat) (flat : Nat × Nat) : Cell :=
    withParam x.cfg 21 (Configs.gasExt 1 limit limit 10000 limit 100000000 1000000000 (some flat))
  let msg := intMsg 0 a1 1000000000 false none #[]
  let wide := gas (2 ^ 64 - 2 ^ 20) (100, 100)
  let high := gas (2 ^ 63 + 2 ^ 20) (2 ^ 20 + 1, 100)
  out := out.push (x.case "gas64/threshold" (active (asm []) (2 ^ 50)) msg wide)
  out := out.push (x.case "gas64/accept" (active accept (2 ^ 50)) msg high)
  out := out.push (x.case "gas64/no-accept" (active (asm []) (2 ^ 50)) msg high)
  out := out.push (x.case "gas64/precompiled" (active accept (2 ^ 50)) msg (withPrecompiled high [(accept, 100)]))
  return out

/-- The address on the stack of tick-tock (`prepare_vm_stack`, transaction.cpp:1463) is `import_bits` of
its 256 bits, signed by default (bigint.hpp:644): an address of 2^255 or more is negative, and the
`tt-stack` contract, which stores it with `STU 256`, fails its range check. -/
def tickTockAddrCases (x : Ctx) : Array TxCase := Id.run do
  let mut out : Array TxCase := #[]
  let hi := natToBits (0xF0 * 2 ^ 248 + 0x1234) 256
  let code := asm ((tickTockPrograms.lookup "tt-stack").getD [])
  for (aname, wc) in [("mc", (-1 : Int)), ("bc", 0)] do
    for isTock in [false, true] do
      out := out.push (x.tt s!"tick-tock/stack-addr/{aname}/{if isTock then "tock" else "tick"}"
        (mkAccount wc hi (.active code data0) 1000000000 1700000000 0 1000) isTock)
  return out

/-- The VM's gas in `long long` (`GasLimits`, vm.h:34-80) leaving its range under parameter 21 with gas
limits of 2^63 or so, where C++ wraps around (two's complement):
* `gas-wrap/credit-high`: an external message under gas limits of 2^64 - 2^20 and a gas credit of
  2^63 + 5: the message buys no gas (a limit of 0), the credit is -2^63 + 5 for the VM
  (transaction.cpp:1938), which starts out of gas, but nothing checks the gas before the first
  charge (vm.cpp:438-475); `ACCEPT`'s 26 gas (vm.h:61) wrap it around to 2^63 - 21 and `ACCEPT`
  runs: the limit becomes the maximum, -2^20 for the VM (vm.cpp:414-419), the gas left negative, out
  of gas at the end of the step, accepted; the gas used (the minimum with the limit, transaction.cpp:
  2016) is no `VarUInteger 7` (3937): C++ fails;
* `gas-wrap/credit-sum`: an external message at a gas price of 0 (all gas for any balance), a gas
  limit of 2^63 - 1 and a credit of 2^62: the sum (vm.h:43) is -2^62 - 1 for the VM, out of gas at
  its first charge from version 4 (not accepted); before version 4 `ACCEPT` runs and moves the gas
  left back into range (vm.h:50-53), and the gas limit of 2^63 - 1 is no `VarUInteger 7`: C++ fails;
* `gas-wrap/precompiled`: a precompiled code (parameter 45) runs with the configuration's gas limit,
  2^63, which is -2^63 for the VM (transaction.cpp:1955-1956): its first charge makes the gas left
  2^63 - 26, the code runs to its end and the transaction is made with the gas usage of the
  configuration (2027-2030). -/
def gasWrapCases (x : Ctx) : Array TxCase := Id.run do
  let mut out : Array TxCase := #[]
  let gas (price limit credit : Nat) (flat : Nat × Nat) : Cell :=
    withParam x.cfg 21 (Configs.gasExt price limit limit credit limit 100000000 1000000000 (some flat))
  out := out.push (x.case "gas-wrap/credit-high" (active accept (2 ^ 50)) (extMsg 0 a1 none #[])
    (gas 1 (2 ^ 64 - 2 ^ 20) (2 ^ 63 + 5) (100, 100)))
  out := out.push (x.case "gas-wrap/credit-sum" (active accept (2 ^ 50)) (extMsg 0 a1 none #[])
    (gas 0 (2 ^ 63 - 1) (2 ^ 62) (100, 0)))
  out := out.push (x.case "gas-wrap/precompiled" (active accept (2 ^ 50)) (intMsg 0 a1 1000000000 false none #[])
    (withPrecompiled (gas 1 (2 ^ 63) 10000 (100, 100)) [(accept, 100)]))
  return out

/-- A flat gas price of 2^63 or more (parameter 21, `gas_flat_pfx`), which C++ takes as `long long` in
the threshold (transaction.cpp:1271), the purchase (1301, 1304) and the price (1317), but whole within
the flat limit (1273, 1316); an internal message of one TON to `ACCEPT`, 31 gas:
* `flat64/threshold`: a flat price of 2^63 + 5 and limit of 100 under a gas limit of 10^6 at one
  nanoton per gas, an account of 2^64 nanotons: the threshold is negative, the message buys all the
  gas; the 31 gas cost the flat price whole, which the account pays;
* `flat64/fee-negative`: the same with a flat limit of 10 and a balance of one TON: the fee is negative
  (1317), C++ takes it and `serialize` refuses it (`gas_fees:Grams`, 3935);
* `flat64/bought-wrap`: a gas limit of 50 within the flat limit of 100: the threshold is the flat
  price whole (1273), above the value, which is not below the flat price as `long long` (1301): the
  quotient (1304) is no `long long`, `to_long()` is -2^63 and the gas bought 2^63 + 100 (1305),
  negative for the VM, out of gas at once; the gas used is no `VarUInteger 7`: C++ fails;
* `flat64/bought-zero-price`: the same at a gas price of 0 (a quotient of NaN, `to_long()` -2^63);
* `flat64/max`: a flat price of 2^63 - 1 (and a limit of 100): the value buys no gas;
* `flat64/fee-low-digit`: a flat price of 2^63 - 1 above a flat limit of 0, a message of 2^63 + 10^9
  nanotons to an account of 2^64: the message buys all the gas, and the 31 gas cost 31 plus the flat
  price by `operator+(RefInt256, long long)`, whose `normalize` overflows (the lowest digit, 31 +
  2^63 - 1, plus 2^51 leaves 64 bits, bigint.hpp:706-730): 2^64 less, a negative fee, which
  `serialize` refuses: C++ fails (the sum whole, 2^63 + 30, the account would pay);
* `flat64/bought-low-digit`: a flat price of 2^63 + 5 (limit 100) at a gas price of 2^64 - 1, an
  account of 2^64 + 2^62: the purchase subtracts the flat price as `long long` by `operator-(RefInt256,
  long long)` (1304), whose `normalize` overflows: 2^64 less, the flat price whole. The message buys
  2^64 - 32668 gas (a negative quotient), the balance 49252: the gas limit is 49252 (with the sum
  exact, 32868 and 114788); `ACCEPT` within the flat limit costs the flat price whole.
The flat price whole above a balance below 2^63 is no case: C++ `balance -= cp.gas_fees` leaves no
balance (block.cpp:1321-1329) and `td::sgn` of it (2072) aborts the emulator. -/
def flatGasCases (x : Ctx) : Array TxCase := Id.run do
  let mut out : Array TxCase := #[]
  let gas (price limit : Nat) (flat : Nat × Nat) : Cell :=
    withParam x.cfg 21 (Configs.gasExt price limit limit 10000 limit 100000000 1000000000 (some flat))
  let msg := intMsg 0 a1 1000000000 false none #[]
  out := out.push (x.case "flat64/threshold" (active accept (2 ^ 64)) msg (gas 65536 1000000 (100, 2 ^ 63 + 5)))
  out := out.push (x.case "flat64/fee-negative" (active accept) msg (gas 65536 1000000 (10, 2 ^ 63 + 5)))
  out := out.push (x.case "flat64/bought-wrap" (active accept) msg (gas 1 50 (100, 2 ^ 63 + 5)))
  out := out.push (x.case "flat64/bought-zero-price" (active accept) msg (gas 0 50 (100, 2 ^ 63 + 5)))
  out := out.push (x.case "flat64/max" (active accept) msg (gas 65536 1000000 (100, 2 ^ 63 - 1)))
  out := out.push (x.case "flat64/fee-low-digit" (active accept (2 ^ 64)) (intMsg 0 a1 (2 ^ 63 + 1000000000) false none #[])
    (gas 65536 1000000 (0, 2 ^ 63 - 1)))
  out := out.push (x.case "flat64/bought-low-digit" (active accept (2 ^ 64 + 2 ^ 62)) msg (gas (2 ^ 64 - 1) 1000000 (100, 2 ^ 63 + 5)))
  return out

/-- Forwarding fees as C++ computes them, `td::uint64` (`compute_fwd_fees`, transaction.cpp:2432-2438:
modulo 2^64; the IHR fee the low 64 bits of `fwd * ihr_factor >> 16`, 2469-2476), under parameter 25
with prices near 2^64:
* `fwd64/send-high`: a contract sends a message whose computed fee is 2^63 + 5: as `long long`
  below the message's fee of 0 (2911-2913), it is not charged;
* `fwd64/send-wrap`: a lump price of 2^64 - 1 and 3 per cell, the body in a reference: the fee is
  (2^64 + 2) modulo 2^64 = 2;
* `fwd64/ihr-high`, `fwd64/ihr-wrap`: before version 11, a message with IHR (`ihr_disabled` 0), sent
  with mode 1 (the fees paid apart from the value), and an IHR factor of 2^32 - 1: a lump price of
  2^48 + 1 makes an IHR fee of 2^63 or more, not charged (2914-2916); 2^48 + 2^16 + 1 an IHR fee of
  2^64 + 65534, modulo 2^64 65534: the account pays the forwarding fee and that;
* `fwd64/import-wrap`: an inbound external message with its body in a reference, its import fee
  (973-980) (2^64 + 2) modulo 2^64;
* `fwd64/bounce-wrap`: a bounce in the new format (from version 12, `extra_flags` 1), the original
  body and information in references (2 cells at 1 each): (2^64 + 1) modulo 2^64 = 1, and the bounce
  is made (3450-3460); before version 12 the fee is 2^64 - 1, which C++ compares as `long long`
  (3460), takes, and fails at the bounced message's value, below zero (3481). -/
def fwd64Cases (x : Ctx) : Array TxCase := Id.run do
  let mut out : Array TxCase := #[]
  let fwd (lump bit cell ihr : Nat) : Cell := withParam x.cfg 25 (Configs.msgPrices lump bit cell ihr 21845 21845)
  let send (ihr : Bool) (body : Option Cell) (mode : Nat := 0) : Cell :=
    asm (sendRaw (relaxedX (stdA 0 src0) 1000000 (ihrDisabled := !ihr) (bodyRef := body)) mode)
  let msg := intMsg 0 a1 1000000000 false none #[]
  let leaf : Cell := Cell.mkOrdinary (natToBits 5 8) #[]
  out := out.push (x.case "fwd64/send-high" (active (send false none) (2 ^ 50)) msg (fwd (2 ^ 63 + 5) 0 0 0))
  out := out.push (x.case "fwd64/send-wrap" (active (send false (some leaf)) (2 ^ 50)) msg (fwd (2 ^ 64 - 1) 0 (3 * 65536) 0))
  if x.v < 11 then
    out := out.push (x.case "fwd64/ihr-high" (active (send true none 1) (2 ^ 50)) msg (fwd (2 ^ 48 + 1) 0 0 (2 ^ 32 - 1)))
    out := out.push (x.case "fwd64/ihr-wrap" (active (send true none 1) (2 ^ 50)) msg
      (fwd (2 ^ 48 + 2 ^ 16 + 1) 0 0 (2 ^ 32 - 1)))
  let ext : Cell :=
    let w : W := ((({} : W).uint 2 2).uint 0 2).bitStr (Account.mkAddr 0 none a1).bits |>.grams 0
    (((w.bool false).bool true).ref leaf).cell
  out := out.push (x.case "fwd64/import-wrap" (active accept (2 ^ 50)) ext (fwd (2 ^ 64 - 1) 0 (3 * 65536) 0))
  out := out.push (x.case "fwd64/bounce-wrap" (active (asm [.throw 42])) (intMsgX (stdA 0 a1) 100000000 (bounce := true)
    (extraFlags := gramsBits 1) (body := natToBits 5 300)) (fwd (2 ^ 64 - 1) 0 65536 0))
  return out

/-- Storage prices of 2^63 or more (parameter 18), which `add_partial_storage_payment` multiplies by as
`long long` (`mul_short`, transaction.cpp:757-774; negative from 2^63 on), an account 100 seconds after
its last payment:
* `storage64/bit-high`: a bit price of 2^64 - 1 (-1) and a cell price of 2^20: the payment is
  `(cells * 2^20 - bits) * 100`, a few thousand nanotons (the price whole would freeze the account);
* `storage64/cell-high`: a cell price of 2^64 - 2^30 (-2^30) and a bit price of 2^30: `(bits - cells) *
  2^30 * 100`;
* `storage64/mc-high`: an account in the masterchain, its prices (`mc_bit_price` 2^64 - 1).
A negative payment is no case: C++ adds the due payment to the null `compute_storage_fees` returns
(1060) and aborts. -/
def storage64Cases (x : Ctx) : Array TxCase := Id.run do
  let mut out : Array TxCase := #[]
  let acc (wc : Int) : Cell := mkAccount wc a1 (.active accept data0) 1000000000 1700000100 0 1000
  let prices (bit cell mcBit mcCell : Nat) : Cell := withParam x.cfg 18 (Configs.storagePrices [(0, bit, cell, mcBit, mcCell)])
  out := out.push (x.case "storage64/bit-high" (acc 0) (intMsg 0 a1 100000000 false none #[]) (prices (2 ^ 64 - 1) (2 ^ 20) 1 500))
  out := out.push (x.case "storage64/cell-high" (acc 0) (intMsg 0 a1 100000000 false none #[])
    (prices (2 ^ 30) (2 ^ 64 - 2 ^ 30) 1 500))
  out := out.push (x.case "storage64/mc-high" (acc (-1)) (intMsg (-1) a1 100000000 false none #[])
    (prices 1 500 (2 ^ 64 - 1) (2 ^ 20)))
  return out

/-- Logical times are `ton::LogicalTime`, `td::uint64`, and wrap around (the `c7` contract stores `NOW`,
`BLOCKLT` and `LTIME`):
* `lt64/created-max`: a message created at 2^64 - 1 to an account that never had a transaction: `start_lt
  = created_lt + 1` is 0 and `end_lt` 1 (transaction.cpp:921-924), which `commit` accepts (4071): the
  transaction is made at 0;
* `lt64/created-near-max`: created at 2^64 - 2: `start_lt` 2^64 - 1, `end_lt` 0: `commit` fails;
* `lt64/account-max`: an account whose last transaction ended at 2^64 - 1: `end_lt = start_lt + 1` is 0
  (860-861), `commit` fails;
* `lt64/emulator-lt-zero`, `lt64/emulator-lt-zero-wrap`: the emulator without a logical time takes the
  block after the account's last transaction (transaction-emulator.cpp:42-45): after 5000006 the block
  at 6000000; after 2^64 - 100001 the block at 2^64 + 448384, modulo 2^64 448384 (and `start_lt` the
  account's end). -/
def lt64Cases (x : Ctx) : Array TxCase := Id.run do
  let mut out : Array TxCase := #[]
  let c7 : Cell := asm ((programs.lookup "c7").getD [])
  let acc (lt : Nat) : Cell := mkAccount 0 a1 (.active c7 data0) 1000000000 1700000000 0 lt
  out := out.push (x.case "lt64/created-max" (acc 0) (intMsgX (stdA 0 a1) 100000000 (createdLt := 2 ^ 64 - 1)))
  out := out.push (x.case "lt64/created-near-max" (acc 0) (intMsgX (stdA 0 a1) 100000000 (createdLt := 2 ^ 64 - 2)))
  out := out.push (x.case "lt64/account-max" (acc (2 ^ 64 - 1)) (intMsg 0 a1 100000000 false none #[]))
  out := out.push { x.case "lt64/emulator-lt-zero" (acc 5000007) (intMsg 0 a1 100000000 false none #[]) with lt := 0 }
  out := out.push { x.case "lt64/emulator-lt-zero-wrap" (acc (2 ^ 64 - 100000)) (intMsg 0 a1 100000000 false none #[]) with
    lt := 0 }
  return out

/-- The fine of a message that fails is computed in `td::uint64` and compared as `long long`
(transaction.cpp:2823-2883): `fine64/cmp-wrap`, a cell price of 2^64 - 1 (a fine of 2^46 - 1 per cell) and
`max_msg_cells` 2^18 (parameter 43): `max_cells * fine_per_cell` is 2^64 - 2^18, -2^18 as `long long`
(2854), so the funds are never below it and `max_cells` stays 2^18 (the product whole would cut it to 0
and fail the message with 40); the message, with its body in a reference, then costs 2^48 + 1, more than
its value of 10^6 (mode 0): 37, the balance taken as the fine. -/
def fine64Cases (x : Ctx) : Array TxCase := Id.run do
  let mut out : Array TxCase := #[]
  let cfg := withParam (withParam x.cfg 25 (Configs.msgPrices 1 0 (2 ^ 64 - 1) 98304 21845 21845)) 43
    (Configs.limitsV1 (({} : W).uint 1 8) (2 ^ 21) (2 ^ 18) 1000 512 65535 512).cell
  let leaf : Cell := Cell.mkOrdinary (natToBits 5 8) #[]
  let send : Cell := asm (sendRaw (relaxedX (stdA 0 src0) 1000000 (bodyRef := some leaf)) 0)
  out := out.push (x.case "fine64/cmp-wrap" (active send) (intMsg 0 a1 1000000000 false none #[]) cfg)
  return out

/-- `SETGASLIMIT` below the gas consumed (`exec_set_gas_generic`, tonops.cpp:70-74) is out of gas with the
limits as they were: the gas used is the gas consumed (`std::min` with the old limit, transaction.cpp:
2016), and the credit of an external message stays (not accepted, 2017). `PUSHINT 1 SETGASLIMIT` on an
internal and an external message; from version 4 (`GASCONSUMED`) the new limit at and one below the gas
consumed when `SETGASLIMIT` has been charged (`GASCONSUMED`, `ADDINT`, `SETGASLIMIT`: 26 gas each). -/
def setGasLimitCases (x : Ctx) : Array TxCase := Id.run do
  let mut out : Array TxCase := #[]
  let setGas : Instr := .tonEnvOp .setGasLimit
  let low := asm [.pushInt (.num 1), setGas]
  out := out.push (x.case "setgaslimit/below/int" (active low) (intMsg 0 a1 1000000000 false none #[]))
  out := out.push (x.case "setgaslimit/below/ext" (active low) (extMsg 0 a1 none #[]))
  if x.v ≥ 4 then
    for (name, k) in [("at-consumed", (52 : Int)), ("below-consumed", 51)] do
      let code := asm [.tonEnvOp .gasConsumed, .addInt k, setGas]
      out := out.push (x.case s!"setgaslimit/{name}/int" (active code) (intMsg 0 a1 1000000000 false none #[]))
      out := out.push (x.case s!"setgaslimit/{name}/ext" (active code) (extMsg 0 a1 none #[]))
  return out

end Cov

open Cov in
/-- The cases of the module at each version of `versions` (the version-independent groups at 9 and 16
only). -/
def coverageCases (cfg0 : Cell) (versions : List Nat) : Array TxCase := Id.run do
  let mut out : Array TxCase := #[]
  for v in versions do
    let cfg := withVersion cfg0 v 46
    let x : Ctx := { v, cfg, cfgAddr := (Config.decode cfg).map (·.configAddr) |>.getD a1 }
    let once := v == 9 || v == 16
    if once then
      out := out ++ Cov.configCases x ++ Cov.storageCreditCases x ++ Cov.computeCases x ++ Cov.actionListCases x false ++ Cov.sendCases x false ++
        Cov.bounceCases x ++ Cov.inMsgCases x ++ Cov.levelCases x ++ Cov.accountCases x false
    if [4, 5, 9, 16].contains v then out := out ++ Cov.gasOverrideCases x
    if [3, 4, 7, 9].contains v then out := out ++ Cov.tickTockCarryCases x
    out := out ++ Cov.deployCases x ++ Cov.activeStateCases x ++ Cov.activeInitCases x ++ Cov.actionListCases x true ++ Cov.sendCases x true ++
      Cov.accountCases x true ++ Cov.stateCases x ++ Cov.serializeCases x ++ Cov.gas64Cases x ++ Cov.tickTockAddrCases x ++
      Cov.setGasLimitCases x ++ Cov.gasWrapCases x ++ Cov.flatGasCases x ++ Cov.fwd64Cases x ++
      Cov.storage64Cases x ++ Cov.lt64Cases x ++ Cov.fine64Cases x
  return out

end Tests.Tx
