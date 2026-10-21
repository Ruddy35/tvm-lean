import Tests.Tx.Gen

/-!
# Transactions of real contracts

The code the reference compiles from FunC (`crypto/smartcont/auto/*.fif`), with initial data and
external messages signed with a fixed key, made by `tools/txoracle/contracts.fif` (its output is
`tools/txoracle/contracts.txt`, one `name base64-BOC` per line):

- wallet v3 (`wallet3-code.fc`): transfers with the modes 3, 1, 128, 160, 2 and 0 (the last two for
  more than the balance), an expired message, a wrong seqno, subwallet and signature, a message
  without an order; deployment by an external message with the `StateInit`, to an uninitialized and
  to an absent account; an internal message;
- highload wallet v2 (`highload-wallet-v2-code.fc`): two, five and no orders in the dictionary of
  orders, an expired query, a wrong signature; with a query already processed and one old enough to
  be removed from the dictionary of processed queries;
- the elector (`elector-code.fc`, the data of `gen-zerostate.fif`) at the address of configuration
  parameter 1: internal messages (a simple transfer, a stake, a request to recover a stake, an
  unknown operation, an empty body) and its tick and tock transactions, which read the validator
  sets and election parameters of the configuration;
- the configuration contract (`config-code.fc`) at the address of parameter 0, its data the
  configuration of the case with the fixed key: external messages that set a parameter, the public
  key, the code, the elector's code, do nothing or an unknown action, with a wrong seqno, expired, a
  validator's vote and a wrong signature; internal messages from the masterchain (a new validator
  set from the elector, valid or not, a voting proposal, an unknown operation, a simple transfer)
  and from the basechain; tick and tock, also with a next validator set (parameter 36) due;
- manual DNS (`dns-manual-code.fc`), its records in a prefix-code dictionary: setting a record, a
  chain of operations that sets, deletes a category, deletes a name, clears a table and sends a
  message, replacing and clearing the root, a new key, an invalid operation, a name without its zero
  byte, new code, an expired query, a wrong contract id and a wrong signature; an internal message;
- the simple wallet (`simple-wallet-code.fc`) and wallet v2 (`wallet-code.fc`, four messages in one
  order): transfers, no order, wrong seqno, expiry and signature;
- the proof-of-work test giver (`pow-testgiver-code.fc`, `randomize_lt`, `random`, `muldivr`): a
  solution ("Mine") under a complexity every hash meets and one none meets, with a wrong seed and
  expired; rescaling the complexity, too early; a signed transfer;
- multisig (`multisig-code.fc`, three owners): initialization; a query sent at once (one signature
  needed); with two needed, a query left pending, one carrying a second owner's signature, the
  confirmation of a pending query by the second owner and again by the first; an unknown owner, a
  wrong signature, wallet id, an expired query and one due too soon;
- restricted wallet v3 (`restricted-wallet3-code.fc`): the first message, which sets the final key
  and the schedule of locked grams; transfers 500 s after the start (part of the balance reserved),
  with the start read from configuration parameter -13 (absent, and set 2000 s before), for more
  than the balance; a wrong seqno, subwallet, signature and an expired message.
-/

namespace Tests.Tx

open TvmLean TvmLean.Tx

/-- The cells of `tools/txoracle/contracts.txt` by name. -/
def loadContracts (file : String := "tools/txoracle/contracts.txt") : IO (List (String × Cell)) := do
  let mut out : List (String × Cell) := []
  for line in (← IO.FS.readFile file).splitOn "\n" do
    match line.trim.splitOn " " with
    | [name, b64] =>
        match stdBocDeserialize (base64Decode b64) with
        | .ok c => out := (name, c) :: out
        | .error _ => throw (IO.userError s!"{file}: cannot read the cell {name}")
    | _ => pure ()
  return out.reverse

/-- An external inbound message to `(wc, dest)` with the body `body` in a reference. -/
def extMsgRef (wc : Int) (dest : BitString) (body : Cell) : Cell :=
  ((((({} : W).uint 2 2).uint 0 2).bitStr (Account.mkAddr wc none dest).bits |>.grams 0).bool false).bool true
    |>.ref body |>.cell

/-- The validator set `vset` (`validators_ext#12 utime_since utime_until ...`) with other times. -/
def vsetAt (vset : Cell) (since untilTime : Nat) : Cell :=
  Cell.mkOrdinary (vset.bits.extract 0 8 ++ natToBits since 32 ++ natToBits untilTime 32 ++ vset.bits.extract 72 vset.bits.size)
    vset.refs

/-- The transactions of the real contracts at each version of `versions` (`contracts`: the cells of
`loadContracts`; a missing one is an error). -/
def realCases (contracts : List (String × Cell)) (cfg0 : Cell) (versions : List Nat) : Except String (Array TxCase) := do
  let get (n : String) : Except String Cell :=
    match contracts.lookup n with
    | some c => .ok c
    | none => .error s!"no cell {n} in tools/txoracle/contracts.txt"
  let w3 := (← get "wallet3.code", ← get "wallet3.data", (← get "wallet3.addr").bits)
  let hl := (← get "highload2.code", ← get "highload2.data", (← get "highload2.addr").bits)
  let hlSeen ← get "highload2.data.seen"
  let el := (← get "elector.code", ← get "elector.data")
  let w3msgs ← ["ok", "pay-fees", "all", "destroy", "too-much-ignored", "too-much", "expired", "seqno", "subwallet",
    "bad-signature", "no-order"].mapM fun n => return (n, ← get s!"wallet3.msg.{n}")
  let w3deploy ← ["deploy", "deploy-transfer"].mapM fun n => return (n, ← get s!"wallet3.msg.{n}")
  let hlmsgs ← ["two", "five", "none", "expired", "bad-signature"].mapM fun n => return (n, ← get s!"highload2.msg.{n}")
  let dns := (← get "dns.code", ← get "dns.data", (← get "dns.addr").bits)
  let dnsmsgs ← ["set", "multi", "root-null", "root-clear", "set-key", "bad-op", "bad-name", "set-code", "expired",
    "wrong-id", "bad-signature"].mapM fun n => return (n, ← get s!"dns.msg.{n}")
  let simple (pfx : String) (msgs : List String) : Except String (Cell × Cell × BitString × List (String × Cell)) := do
    return (← get s!"{pfx}.code", ← get s!"{pfx}.data", (← get s!"{pfx}.addr").bits,
      ← msgs.mapM fun n => return (n, ← get s!"{pfx}.msg.{n}"))
  let wallets ← [("simple-wallet", ["ok", "none", "seqno", "bad-signature"]),
    ("wallet2", ["four", "none", "expired", "seqno", "bad-signature"])].mapM fun (p, ms) => return (p, ← simple p ms)
  let pow := (← get "pow.code", ← get "pow.data.easy", ← get "pow.data.hard", (← get "pow.addr").bits)
  let powmsgs ← ["mine", "mine-wrong-seed", "mine-expired", "rescale", "rescale-early", "transfer"].mapM fun n =>
    return (n, ← get s!"pow.msg.{n}")
  let ms := (← get "multisig.code", ← get "multisig.data.k1", (← get "multisig.addr.k1").bits,
    ← get "multisig.data.k2", (← get "multisig.addr.k2").bits, ← get "multisig.data.k2-pending")
  let msmsg (n : String) := get s!"multisig.msg.{n}"
  let msK2 ← ["init", "k2-root", "k2-cosigned", "unknown-owner", "bad-signature", "wrong-wallet", "expired",
    "too-soon"].mapM fun n => return (n, ← msmsg n)
  let msPending ← ["k2-confirm", "k2-root"].mapM fun n => return (n, ← msmsg n)
  let msK1 ← msmsg "k1-send"
  let rw := (← get "restricted3.code", (← get "restricted3.addr").bits, ← get "restricted3.data.new",
    ← get "restricted3.data.started", ← get "restricted3.data.from-config")
  let rwmsg (n : String) := get s!"restricted3.msg.{n}"
  let rwInit ← rwmsg "init"
  let rwmsgs ← ["transfer", "transfer-small", "transfer-too-much", "seqno", "subwallet", "expired",
    "bad-signature"].mapM fun n => return (n, ← rwmsg n)
  let cfgCode ← get "config.code"
  let pub := (← get "key.pub").bits
  let cfgBodies ← ["set-param", "set-key", "set-code", "elector-code", "noop", "unknown", "seqno", "expired", "vote",
    "bad-signature"].mapM fun n => return (n, ← get s!"config.body.{n}")
  let mut out : Array TxCase := #[]
  for v in versions do
    let cfg := withVersion cfg0 v 46
    -- the elector: the address of parameter 1
    let elAddr := ((Config.decode cfg).bind (·.param 1)).map (·.bits) |>.getD (natToBits 0 256)
    let mk (name : String) (acc msg : Cell) : TxCase :=
      { name := s!"v{v}/real/{name}", config := cfg, account := acc, msg, now := 1700000200, lt := 3000000, seed }
    let (code, data, addr) := w3
    for (bname, bal) in [("rich", 1000000000), ("poor", 2000000)] do
      for (n, m) in w3msgs do
        out := out.push (mk s!"wallet3/{n}/{bname}" (mkAccount 0 addr (.active code data) bal 1700000000 0 1000) m)
    for (n, m) in w3deploy do
      out := out.push (mk s!"wallet3/{n}/uninit" (mkAccount 0 addr .uninit 1000000000 1700000000 0 1000) m)
      out := out.push (mk s!"wallet3/{n}/uninit-poor" (mkAccount 0 addr .uninit 300000 1700000000 0 1000) m)
      out := out.push (mk s!"wallet3/{n}/none" (mkAccount 0 addr .none 0 0 0 0) m)
    out := out.push (mk "wallet3/internal" (mkAccount 0 addr (.active code data) 1000000000 1700000000 0 1000)
      (intMsg 0 addr 100000000 true none (natToBits 0 32)))
    let (code, data, addr) := hl
    for (dname, d) in [("fresh", data), ("seen", hlSeen)] do
      for (n, m) in hlmsgs do
        out := out.push (mk s!"highload2/{n}/{dname}" (mkAccount 0 addr (.active code d) 1000000000 1700000000 0 1000) m)
    let (code, data, addr) := dns
    for (bname, bal) in [("rich", 1000000000), ("poor", 3000000)] do
      for (n, m) in dnsmsgs do
        out := out.push (mk s!"dns/{n}/{bname}" (mkAccount 0 addr (.active code data) bal 1700000000 0 1000) m)
    out := out.push (mk "dns/internal" (mkAccount 0 addr (.active code data) 1000000000 1700000000 0 1000)
      (intMsg 0 addr 100000000 true none (natToBits 0x12345678 32)))
    for (p, (code, data, addr, msgs)) in wallets do
      for (bname, bal) in [("rich", 1000000000), ("poor", 2000000)] do
        for (n, m) in msgs do
          out := out.push (mk s!"{p}/{n}/{bname}" (mkAccount 0 addr (.active code data) bal 1700000000 0 1000) m)
    let (code, easy, hard, addr) := pow
    for (dname, data) in [("easy", easy), ("hard", hard)] do
      for (n, m) in powmsgs do
        out := out.push (mk s!"pow/{n}/{dname}" (mkAccount 0 addr (.active code data) 100000000000 1700000000 0 1000) m)
    let (code, d1, a1, d2, a2, d2p) := ms
    let msAcc (d : Cell) (a : BitString) := mkAccount 0 a (.active code d) 1000000000 1700000000 0 1000
    out := out.push (mk "multisig/k1-send" (msAcc d1 a1) msK1)
    for (n, m) in msK2 do
      out := out.push (mk s!"multisig/{n}" (msAcc d2 a2) m)
    for (n, m) in msPending do
      out := out.push (mk s!"multisig/pending/{n}" (msAcc d2p a2) m)
    out := out.push (mk "multisig/internal" (msAcc d2 a2) (intMsg 0 a2 100000000 true none #[]))
    let (code, addr, dNew, dStarted, dFromCfg) := rw
    let rwAcc (d : Cell) := mkAccount 0 addr (.active code d) 1000000000 1700000000 0 1000
    out := out.push (mk "restricted3/init" (rwAcc dNew) rwInit)
    -- configuration parameter -13 (the key 2^32 - 13): the start, 2000 s before the case
    let cfgStart := withParam cfg (2 ^ 32 - 13) (({} : W).uint (1700000200 - 2000) 32).cell
    for (dname, d, c) in [("started", dStarted, cfg), ("from-config", dFromCfg, cfg), ("from-config-set", dFromCfg, cfgStart)] do
      for (n, m) in rwmsgs do
        out := out.push { mk s!"restricted3/{dname}/{n}" (rwAcc d) m with config := c }
    let (code, data) := el
    let elAcc := mkAccount (-1) elAddr (.active code data) 500000000000 1700000000 0 1000
    for (n, body) in [("transfer", natToBits 0 32), ("stake", natToBits 0x4e73744b 32 ++ natToBits 7 64),
        ("recover", natToBits 0x47657424 32 ++ natToBits 8 64), ("unknown", natToBits 0x12345678 32 ++ natToBits 9 64),
        ("empty", #[])] do
      out := out.push (mk s!"elector/{n}" elAcc (intMsg (-1) elAddr 10000000000 true none body))
    for isTock in [false, true] do
      out := out.push { mk s!"elector/{if isTock then "tock" else "tick"}" elAcc Cell.empty with tickTock := some isTock }
    -- the configuration contract, its data the configuration dictionary of the case
    let some c := Config.decode cfg | throw "configuration"
    let cfgAddr := c.configAddr
    let cfgData (dict : Cell) : Cell := (((({} : W).ref dict).uint 0 32).bitStr pub |>.bool false).cell
    let cfgAcc (dict : Cell) := mkAccount (-1) cfgAddr (.active cfgCode (cfgData dict)) 1000000000000 1700000000 0 1000
    for (n, body) in cfgBodies do
      out := out.push (mk s!"config/{n}" (cfgAcc cfg) (extMsgRef (-1) cfgAddr body))
    let vset := (c.param 34).getD Cell.empty
    -- a next validator set (parameter 36) due since 1690000000
    let cfgNext := withParam cfg 36 (vsetAt vset 1690000000 1800000000)
    for (dname, dict) in [("", cfg), ("/next-due", cfgNext)] do
      for isTock in [false, true] do
        out := out.push { mk s!"config/{if isTock then "tock" else "tick"}{dname}" (cfgAcc dict) Cell.empty with
          tickTock := some isTock }
    let mc (a : BitString) : Int × BitString := (-1, a)
    -- not the elector (`other`, -1:3333..33, is the elector's address in the testnet configuration)
    let stranger := natToBits 0x4444444444444444444444444444444444444444444444444444444444444444 256
    let q (tag : Nat) : BitString := natToBits tag 32 ++ natToBits 11 64
    for (n, src, body, refs) in [("new-vset-from-elector", mc elAddr, q 0x4e565354, #[vsetAt vset 1700001000 1700100000]),
        ("new-vset-from-elector-past", mc elAddr, q 0x4e565354, #[vsetAt vset 1690000000 1700100000]),
        ("new-vset-from-other", mc stranger, q 0x4e565354, #[vsetAt vset 1700001000 1700100000]),
        ("proposal", mc stranger, q 0x6e565052, #[]), ("unknown", mc stranger, q 0x11111111, #[]),
        ("transfer", mc stranger, #[], #[]), ("from-basechain", (0, stranger), q 0x6e565052, #[])] do
      out := out.push (mk s!"config/internal/{n}" (cfgAcc cfg) (intMsg (-1) cfgAddr 2000000000 true none body
        (bodyRefs := refs) (src := src)))
  return out

end Tests.Tx
