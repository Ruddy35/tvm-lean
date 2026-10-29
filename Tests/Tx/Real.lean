import Tests.Tx.Gen
import Tests.Tx.StorageContract
import Tests.Tx.Corpus
import TvmLean.Proofs.Contracts.Wallet3Code

/-!
# Transactions of real contracts

The code the reference compiles from FunC (`crypto/smartcont/auto/*.fif`), with initial data and
external messages signed with a fixed key, made by `tools/txoracle/contracts.fif` (its output is
`tools/txoracle/contracts.txt`, one `name base64-BOC` per line):

- wallet v3 (`wallet3-code.fc`; the code is the cell literal `TvmLean.Contracts.wallet3Code`, checked
  equal to `wallet3.code`): transfers with the modes 3, 1, 128, 160, 2 and 0 (the last two for
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
  than the balance; a wrong seqno, subwallet, signature and an expired message;
- the payment channel (`payment-channel-code.fc`), in each state: init messages (internal, with
  value) signed by A, by B, by both, with a wrong channel and more than the value, again by A; close
  messages (external) signed by A or B with the other's promise, without a promise, by both; timeouts
  before and after expiry; the payout with and without enough balance; an unknown operation, a
  simple transfer and an empty body;
- highload wallet v1 (`highload-wallet-code.fc`, `new-highload-wallet.fif`): the first message of
  `new-highload-wallet.fif` (also deploying it, to an uninitialized and an absent account), two and
  five orders, an order at a key of 2^15 or more (negative for `idict_get_next?`, not sent), no
  orders, a wrong seqno, subwallet and signature, an expired message and one with bits after the
  orders; an internal message;
- the simple wallet ext (`simple-wallet-ext-code.fc`, a message signature seqno [mode ^msg]):
  transfers with the modes 3 and 128 and for more than the balance, no order, two references or
  more bits after the order (`end_parse` failing after `accept_message`), a wrong seqno and
  signature; deployment with its `StateInit` and a transfer; an internal message;
- restricted wallet v1 (`restricted-wallet-code.fc`, `new-restricted-wallet.fif`, in the
  masterchain): the message of `new-restricted-wallet.fif` (seqno 0, accepted without a signature;
  also deploying it, and on the wallet after it), messages to the elector (`-1:3333..33`, parameter
  1), to it in the basechain, to the basechain and four at once (with another masterchain account and
  an external message), with configuration parameter -13 absent, before, at and after the case's
  time, and of 16 bits; for more than the balance, no order, a wrong seqno and signature, expired;
  an internal message;
- restricted wallet v2 (`restricted-wallet2-code.fc`, `new-restricted-wallet2.fif`, in the
  masterchain): the first message (seqno 0, without a signature; deploying it too); transfers of 0.5
  and 0.05 Gram, two at once and one for more than the balance, with the start in the data before,
  after and long before the case, and the start read from configuration parameter -13 (absent,
  before, at the case's time, of 16 bits), so that the schedule keeps 0.9, 0.8, 0.1, 0 or nothing;
  the same with the 16-bit schedule of `new-restricted-wallet2.fif`, which the wallet's 32-bit lookup
  cannot read (exit codes 10 and 9); no order, a wrong seqno and signature, expired; an internal
  message;
- the automatic DNS (`dns-auto-code.fc`, `new-auto-dns.fif`, `auto-dns.fif`; `dnsAutoCases`):
  registrations of a new name (with enough value and with less than 2^30 nanograms plus the price,
  from the owner and another account), an existing one, an expired one, subdomains of an owned name
  (by its owner and another account) and of one without an owner, the name in a reference; invalid
  names (empty, without the zero byte, in a reference of 12 bits, of 17 bytes or with a reference),
  four and five zero bytes; categories with a malformed owner record, of more than 100 cells, absent;
  no expiry; names whose stored owner record is malformed; prolong and update (always `notf`);
  housekeeping due, recent and disabled, the gc operation for all, one and no steps; the control
  operations ChPr and CDel (domains left, none, only expired ones) from the owner and another
  account, Take, an unknown control operation; an unknown operation with and without a query id, an
  answer, a comment, a short and an empty body, a bounced message; external messages before and
  after the initialization, the message of `new-auto-dns.fif` with its `StateInit`;
- the storage contract of TON Storage (`storage/storage-daemon/smartcont/storage-contract.fc`,
  `Tests/Tx/StorageContract.lean`): every operation of `recv_internal`, proofs of storage (Merkle
  proofs of microchunk trees) valid and invalid, external messages; and 500 random internal messages
  from a fixed seed, each at its own version (`StorageContract.randomCases`);
- the most used contracts of the mainnet (`Tests/Tx/Corpus.lean`, `Corpus.cases`):
  wallet v4r2, wallet v5r1, jettons, NFT.
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

/-- The restricted wallet v1 (`restricted-wallet-code.fc`) in the masterchain, on the configuration
`cfg` of a version (`get`: the cells of `tools/txoracle/contracts.txt`, `mk`: a case of `realCases`).
Configuration parameter -13 is absent, 2000 s before the case, at its time, 1000 s after it (the
wallet is restricted while it is absent or after now) or a cell of 16 bits. -/
def restricted1Cases (get : String → Except String Cell) (cfg : Cell) (mk : String → Cell → Cell → TxCase) :
    Except String (Array TxCase) := do
  let code ← get "restricted1.code"
  let addr := (← get "restricted1.addr").bits
  let dNew ← get "restricted1.data.new"
  let dStarted ← get "restricted1.data"
  let msgs (ns : List String) := ns.mapM fun n => return (n, ← get s!"restricted1.msg.{n}")
  let acc (d : Cell) := mkAccount (-1) addr (.active code d) 10000000000 1700000000 0 1000
  let p13 (c : Cell) := withParam cfg (2 ^ 32 - 13) c
  let u32 (t : Nat) := (({} : W).uint t 32).cell
  let mut out : Array TxCase := #[]
  for (cname, c) in [("absent", cfg), ("past", p13 (u32 (1700000200 - 2000))), ("now", p13 (u32 1700000200)),
      ("future", p13 (u32 (1700000200 + 1000))), ("short", p13 (({} : W).uint 7 16).cell)] do
    for (n, m) in ← msgs ["four", "elector", "elector-basechain", "basechain"] do
      out := out.push { mk s!"restricted1/{cname}/{n}" (acc dStarted) m with config := c }
  for (n, m) in ← msgs ["too-much", "none", "seqno", "expired", "bad-signature", "init-noinit"] do
    out := out.push (mk s!"restricted1/{n}" (acc dStarted) m)
  for (n, m) in ← msgs ["init", "init-noinit", "four"] do
    out := out.push (mk s!"restricted1/new/{n}" (acc dNew) m)
  let init ← get "restricted1.msg.init"
  out := out.push (mk "restricted1/new/init/uninit" (mkAccount (-1) addr .uninit 10000000000 1700000000 0 1000) init)
  out := out.push (mk "restricted1/new/init/none" (mkAccount (-1) addr .none 0 0 0 0) init)
  out := out.push (mk "restricted1/internal" (acc dStarted) (intMsg (-1) addr 100000000 true none (natToBits 0 32)))
  return out

/-- The restricted wallet v2 (`restricted-wallet2-code.fc`) in the masterchain, on the configuration
`cfg` of a version (as `restricted1Cases`). Its schedule `rdict` is looked up at `now - start_at`:
`start_at` 500 s before the case (0.8 Gram kept of 1), 500 s after it (no key at or before -500),
200000 s before it (0 kept), or 0 (configuration parameter -13: absent, -1 and 0.9 kept; 2000 s before
the case, 0.1 kept; at the case's time, 0.8 kept; a cell of 16 bits); and the 16-bit dictionary of
`new-restricted-wallet2.fif`, which the wallet reads as one of 32-bit keys. -/
def restricted2Cases (get : String → Except String Cell) (cfg : Cell) (mk : String → Cell → Cell → TxCase) :
    Except String (Array TxCase) := do
  let code ← get "restricted2.code"
  let addr := (← get "restricted2.addr").bits
  let data (n : String) := get s!"restricted2.data.{n}"
  let msgs (ns : List String) := ns.mapM fun n => return (n, ← get s!"restricted2.msg.{n}")
  let acc (d : Cell) := mkAccount (-1) addr (.active code d) 1000000000 1700000000 0 1000
  let p13 (c : Cell) := withParam cfg (2 ^ 32 - 13) c
  let u32 (t : Nat) := (({} : W).uint t 32).cell
  let past := p13 (u32 (1700000200 - 2000))
  let mut out : Array TxCase := #[]
  for (dname, d, cfgs) in [("started", ← data "started", [("", cfg)]), ("not-started", ← data "not-started", [("", cfg)]),
      ("unlocked", ← data "unlocked", [("", cfg)]),
      ("from-config", ← data "from-config", [("/absent", cfg), ("/past", past), ("/now", p13 (u32 1700000200)),
        ("/short", p13 (({} : W).uint 7 16).cell)]),
      ("script", ← data "script", [("/absent", cfg), ("/past", past)])] do
    for (cname, c) in cfgs do
      for (n, m) in ← msgs ["transfer", "transfer-small", "two", "transfer-too-much"] do
        out := out.push { mk s!"restricted2/{dname}{cname}/{n}" (acc d) m with config := c }
  for (n, m) in ← msgs ["none", "seqno", "expired", "bad-signature", "init-noinit"] do
    out := out.push (mk s!"restricted2/{n}" (acc (← data "started")) m)
  for (n, m) in ← msgs ["init", "init-noinit", "transfer"] do
    out := out.push (mk s!"restricted2/new/{n}" (acc (← data "new")) m)
  let init ← get "restricted2.msg.init"
  out := out.push (mk "restricted2/new/init/uninit" (mkAccount (-1) addr .uninit 1000000000 1700000000 0 1000) init)
  out := out.push (mk "restricted2/new/init/none" (mkAccount (-1) addr .none 0 0 0 0) init)
  out := out.push (mk "restricted2/internal" (acc (← data "started")) (intMsg (-1) addr 100000000 true none (natToBits 0 32)))
  return out

/-- The automatic DNS (`dns-auto-code.fc`) with 5 Gram (`get`, `mk` as for `restricted1Cases`).
Internal messages with 2 Gram (or 1.1, less than 2^30 nanograms plus the price) from 0:2222..22, the
owner of the contract and of the names test, old and older, or from 0:4444..44, the owner of other,
to the states of `contracts.fif`: names registered with housekeeping
due, the same with housekeeping 10 s before, disabled (stdperiod 0), after the initialization
message, only expired names, as `new-auto-dns.fif` makes it. External messages, accepted only while
last_housekeeping is 0. In the lookup loop of `recv_internal`, `cell cat_table = val~load_ref()`
declares a new variable (`auto/dns-auto-code.fif`: LDREF, DICTUGETREF, the result dropped), so the
outer `cat_table` is null after it: registering an existing name replaces it, prolong and update
answer `notf` (0xee6f7466); the cases take the branches that remain. -/
def dnsAutoCases (get : String → Except String Cell) (mk : String → Cell → Cell → TxCase) :
    Except String (Array TxCase) := do
  let code ← get "dnsauto.code"
  let addr := (← get "dnsauto.addr").bits
  let data (n : String) := get s!"dnsauto.data.{n}"
  let acc (d : Cell) := mkAccount 0 addr (.active code d) 5000000000 1700000000 0 1000
  let owner : Int × BitString := (0, natToBits 0x2222222222222222222222222222222222222222222222222222222222222222 256)
  let other : Int × BitString := (0, natToBits 0x4444444444444444444444444444444444444444444444444444444444444444 256)
  -- (state, bodies, from 0:4444..44, with 1.1 Gram)
  let groups : List (String × List String × Bool × Bool) :=
    [("registered", ["reg-new", "reg-test", "reg-old", "reg-sub", "reg-free-sub", "reg-ref", "reg-empty", "reg-no-zero",
        "reg-ref-bits", "reg-ref-long", "reg-ref-refs", "reg-four-zeros", "reg-five-zeros", "reg-bad-owner",
        "reg-bad-owner-tag", "reg-big", "reg-no-data", "reg-no-expiry", "reg-bad2", "reg-bad3-sub", "prolong-test",
        "prolong-old", "prolong-missing", "update-test", "update-missing", "gc-all", "gc-one", "gc-zero", "unknown",
        "unknown-no-qid", "answer", "comment", "short", "chpr", "cdel", "take", "ctl-unknown"], false, false),
     ("registered", ["reg-new", "reg-sub"], false, true),
     ("registered", ["reg-new", "reg-test", "reg-sub", "update-test", "chpr", "cdel"], true, false),
     ("recent", ["reg-new", "gc-all"], false, false),
     ("disabled", ["reg-new", "gc-all", "chpr"], false, false),
     ("init", ["reg-new", "cdel", "gc-all", "unknown"], false, false),
     ("new", ["reg-new"], false, false),
     ("expired", ["cdel", "reg-old", "gc-all"], false, false)]
  let mut out : Array TxCase := #[]
  for (dname, bodies, fromOther, poor) in groups do
    let d ← data dname
    for n in bodies do
      let b ← get s!"dnsauto.body.{n}"
      let name := s!"dnsauto/{dname}/{n}" ++ (if fromOther then "/other" else "") ++ (if poor then "/poor" else "")
      out := out.push (mk name (acc d) (intMsg 0 addr (if poor then 1100000000 else 2000000000) true none b.bits
        (bodyRefs := b.refs) (src := if fromOther then other else owner)))
  let reg ← data "registered"
  out := out.push (mk "dnsauto/registered/empty" (acc reg) (intMsg 0 addr 2000000000 true none #[]))
  let regNew ← get "dnsauto.body.reg-new"
  out := out.push (mk "dnsauto/registered/reg-new/bounced" (acc reg)
    (intMsg 0 addr 2000000000 false none regNew.bits (bodyRefs := regNew.refs) (bounced := true)))
  -- the message of new-auto-dns.fif, with the StateInit
  let init ← get "dnsauto.msg.init"
  out := out.push (mk "dnsauto/ext/init/new" (acc (← data "new")) init)
  out := out.push (mk "dnsauto/ext/init/uninit" (mkAccount 0 addr .uninit 1000000000 1700000000 0 1000) init)
  out := out.push (mk "dnsauto/ext/init/none" (mkAccount 0 addr .none 0 0 0 0) init)
  for dname in ["new", "init", "registered"] do
    out := out.push (mk s!"dnsauto/ext/{dname}" (acc (← data dname)) (extMsg 0 addr none #[]))
  out := out.push (mk "dnsauto/ext/new/body" (acc (← data "new")) (extMsg 0 addr none (natToBits 0x1234 64)))
  return out

/-- The transactions of the real contracts at each version of `versions` (`contracts`: the cells of
`loadContracts`; a missing one is an error). -/
def realCases (contracts : List (String × Cell)) (cfg0 : Cell) (versions : List Nat) : Except String (Array TxCase) := do
  let get (n : String) : Except String Cell :=
    match contracts.lookup n with
    | some c => .ok c
    | none => .error s!"no cell {n} in tools/txoracle/contracts.txt"
  -- the cell literal of `TvmLean/Proofs/Contracts/Wallet3Code.lean` is the code of contracts.txt; the
  -- wallet's cases run the literal
  unless (← get "wallet3.code") == TvmLean.Contracts.wallet3Code do
    throw "wallet3.code of tools/txoracle/contracts.txt is not TvmLean.Contracts.wallet3Code"
  let w3 := (TvmLean.Contracts.wallet3Code, ← get "wallet3.data", (← get "wallet3.addr").bits)
  let hl := (← get "highload2.code", ← get "highload2.data", (← get "highload2.addr").bits)
  let hlSeen ← get "highload2.data.seen"
  let el := (← get "elector.code", ← get "elector.data")
  let w3msgs ← ["ok", "pay-fees", "all", "destroy", "too-much-ignored", "too-much", "expired", "seqno", "subwallet",
    "bad-signature", "no-order"].mapM fun n => return (n, ← get s!"wallet3.msg.{n}")
  let w3deploy ← ["deploy", "deploy-transfer"].mapM fun n => return (n, ← get s!"wallet3.msg.{n}")
  let hlmsgs ← ["two", "five", "none", "expired", "bad-signature"].mapM fun n => return (n, ← get s!"highload2.msg.{n}")
  let hl1 := (← get "highload1.code", ← get "highload1.data", (← get "highload1.addr").bits)
  let hl1msgs ← ["init", "two", "five", "negative-key", "none", "expired", "seqno", "subwallet", "bad-signature",
    "trailing"].mapM fun n => return (n, ← get s!"highload1.msg.{n}")
  let dns := (← get "dns.code", ← get "dns.data", (← get "dns.addr").bits)
  let dnsmsgs ← ["set", "multi", "root-null", "root-clear", "set-key", "bad-op", "bad-name", "set-code", "expired",
    "wrong-id", "bad-signature"].mapM fun n => return (n, ← get s!"dns.msg.{n}")
  let simple (pfx : String) (msgs : List String) : Except String (Cell × Cell × BitString × List (String × Cell)) := do
    return (← get s!"{pfx}.code", ← get s!"{pfx}.data", (← get s!"{pfx}.addr").bits,
      ← msgs.mapM fun n => return (n, ← get s!"{pfx}.msg.{n}"))
  let wallets ← [("simple-wallet", ["ok", "none", "seqno", "bad-signature"]),
    ("wallet2", ["four", "none", "expired", "seqno", "bad-signature"]),
    ("simple-wallet-ext", ["ok", "all", "too-much", "none", "two", "trailing", "seqno", "bad-signature"])].mapM
    fun (p, ms) => return (p, ← simple p ms)
  let swxDeploy ← get "simple-wallet-ext.msg.deploy"
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
  let pcCode ← get "pchan.code"
  let pcAddr := (← get "pchan.addr").bits
  let pcData (n : String) := get s!"pchan.data.{n}"
  let pcBody (n : String) := get s!"pchan.body.{n}"
  -- (state, message, internal value or none for an external message, balance)
  let pcCases : List (String × String × Option Nat × Nat) :=
    [("init", "init-a", some 3000000000, 1000000000), ("init", "init-both", some 3500000000, 1000000000),
     ("init", "init-wrong-channel", some 3000000000, 1000000000), ("init", "init-too-much", some 3000000000, 1000000000),
     ("init", "transfer", some 100000000, 1000000000), ("init", "unknown", some 100000000, 1000000000),
     ("init", "timeout", none, 5000000000), ("init-a", "init-b", some 1500000000, 3000000000),
     ("init-a", "init-a", some 3000000000, 3000000000), ("init-expired", "timeout", none, 3000000000),
     ("close", "close-a", none, 5000000000), ("close", "close-a-nosig", none, 5000000000),
     ("close", "close-both", none, 5000000000), ("close", "timeout", none, 5000000000),
     ("close-a", "close-b", none, 5000000000), ("close-a", "close-a", none, 5000000000),
     ("close-expired", "timeout", none, 5000000000), ("payout", "payout", none, 5000000000),
     ("payout", "payout", none, 3500000000), ("payout", "transfer", none, 5000000000)]
  let pcRun ← pcCases.mapM fun (st, m, v, bal) => return (st, m, v, bal, ← pcData st, ← pcBody m)
  let cfgCode ← get "config.code"
  let pub := (← get "key.pub").bits
  let stCode ← get "storage.code"
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
    let (code, data, addr) := hl1
    for (bname, bal) in [("rich", 1000000000), ("poor", 2000000)] do
      for (n, m) in hl1msgs do
        out := out.push (mk s!"highload1/{n}/{bname}" (mkAccount 0 addr (.active code data) bal 1700000000 0 1000) m)
    for (n, m) in hl1msgs.filter (·.1 == "init") do
      out := out.push (mk s!"highload1/{n}/uninit" (mkAccount 0 addr .uninit 1000000000 1700000000 0 1000) m)
      out := out.push (mk s!"highload1/{n}/none" (mkAccount 0 addr .none 0 0 0 0) m)
    out := out.push (mk "highload1/internal" (mkAccount 0 addr (.active code data) 1000000000 1700000000 0 1000)
      (intMsg 0 addr 100000000 true none (natToBits 0 32)))
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
      if p == "simple-wallet-ext" then
        out := out.push (mk s!"{p}/deploy/uninit" (mkAccount 0 addr .uninit 1000000000 1700000000 0 1000) swxDeploy)
        out := out.push (mk s!"{p}/deploy/none" (mkAccount 0 addr .none 0 0 0 0) swxDeploy)
        out := out.push (mk s!"{p}/internal" (mkAccount 0 addr (.active code data) 1000000000 1700000000 0 1000)
          (intMsg 0 addr 100000000 true none (natToBits 0 32)))
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
    out := out ++ (← restricted1Cases get cfg mk)
    out := out ++ (← restricted2Cases get cfg mk)
    out := out ++ (← dnsAutoCases get mk)
    out := out ++ (← StorageContract.cases stCode mk)
    for (st, m, v, bal, d, body) in pcRun do
      let acc := mkAccount 0 pcAddr (.active pcCode d) bal 1700000000 0 1000
      let msg := match v with
        | some value => intMsg 0 pcAddr value true none body.bits (bodyRefs := body.refs)
        | none => extMsgRef 0 pcAddr body
      out := out.push (mk s!"pchan/{st}/{m}/{bal}" acc msg)
    out := out.push (mk "pchan/init/empty" (mkAccount 0 pcAddr (.active pcCode (← pcData "init")) 1000000000 1700000000 0 1000)
      (intMsg 0 pcAddr 100000000 true none #[]))
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
  return out ++ (← Corpus.cases get cfg0 versions) ++ (← StorageContract.randomCases stCode cfg0 versions)

end Tests.Tx
