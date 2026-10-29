import Tests.Tx.Gen

/-!
# Transactions of the most used mainnet contracts

The codes, data, addresses, external messages and internal message bodies are made by
`tools/txoracle/contracts.fif` (each code checked there against its code hash; its output is
`tools/txoracle/contracts.txt`); the cases below put them in accounts and internal messages. The
owner of every contract is 0:2222..22, the source of the internal messages unless said otherwise;
another account is 0:4444..44.

- wallet v4r2 (`wallet4Cases`);
- wallet v5r1 (`wallet5Cases`).
-/

namespace Tests.Tx.Corpus

open TvmLean TvmLean.Tx Tests.Tx

/-- 0:2222..22: the owner of every contract here, the default source of internal messages. -/
def owner : Int × BitString := (0, natToBits 0x2222222222222222222222222222222222222222222222222222222222222222 256)
/-- 0:4444..44: another account. -/
def stranger : Int × BitString := (0, natToBits 0x4444444444444444444444444444444444444444444444444444444444444444 256)

/-- An internal message to `(wc, dest)` from `src` with `value`, the body `body` inline when it fits
in the message cell and in a reference otherwise (`bodyRef` forces one), the `StateInit` `init` in a
reference and `fwdFee` in the field the receiver reads as the forwarding fee. -/
def intMsgCell (wc : Int) (dest : BitString) (value : Nat) (body : Cell) (src : Int × BitString := owner)
    (bounce : Bool := true) (bounced : Bool := false) (init : Option Cell := none) (fwdFee : Nat := 0)
    (bodyRef : Option Bool := none) : Cell :=
  let w : W := (((({} : W).bool false).bool true).bool bounce).bool bounced
  let w := (w.bitStr (addrStd src.1 src.2).bits).bitStr (Account.mkAddr wc none dest).bits
  let w := ((((w.grams value).bool false).grams 0).grams fwdFee).uint 2000 64 |>.uint 1700000100 32
  let w := match init with
    | some c => ((w.bool true).bool true).ref c
    | none => w.bool false
  let fits := w.bits.size + 1 + body.bits.size ≤ 1023 ∧ w.refs.size + body.refs.size ≤ 4
  if bodyRef.getD (!decide fits) then ((w.bool true).ref body).cell
  else { ((w.bool false).bitStr body.bits) with refs := w.refs ++ body.refs }.cell

/-- The messages of `pfx.msg.<n>` (`get`: the cells of `tools/txoracle/contracts.txt`). -/
def msgs (get : String → Except String Cell) (pfx : String) (ns : List String) : Except String (List (String × Cell)) :=
  ns.mapM fun n => return (n, ← get s!"{pfx}.msg.{n}")

/-- Wallet v4r2 (`ton-blockchain/wallet-contract`, `wallet-v4-code.fc`; `mk`, `get` as for
`Tests.Tx.restricted1Cases`). External messages with 1 Gram and with 0.002 Gram (too little for the
gas of the signature check): transfers (one, four with the modes 3, 1, 0 for more than the balance and
2, all with mode 128, more than the balance with mode 0), no message, no op (`load_uint(8)` fails after
the seqno is committed), an unknown op, an expired message, a wrong seqno, subwallet and signature; op
1 (deploy and install a plugin), op 2 (install 0:4444..44, and 0:2222..22 when it is installed: 39
after the commit), op 3 (remove 0:2222..22 when installed, and one never installed); the seqno 2^32 - 1
(`store_uint(seqno + 1, 32)` fails after `accept_message`); deployment by the first message with the
`StateInit`. Internal messages: from the plugin 0:2222..22, requests of 0.1 Gram, of 50 (80), of 0.1
and an extra currency the wallet does not have, removal with and without the bounce flag, a request
without query_id, a comment, an unknown operation, an empty body, a bounced request; the same requests
from an account that is not a plugin and to a wallet without plugins. -/
def wallet4Cases (get : String → Except String Cell) (mk : String → Cell → Cell → TxCase) :
    Except String (Array TxCase) := do
  let code ← get "wallet4.code"
  let addr := (← get "wallet4.addr").bits
  let data (n : String) := get s!"wallet4.data{n}"
  let acc (d : Cell) (bal : Nat) := mkAccount 0 addr (.active code d) bal 1700000000 0 1000
  let mut out : Array TxCase := #[]
  for (dname, d, ns) in [("fresh", "", ["ok", "four", "all", "too-much", "none", "no-op", "unknown-op", "expired",
      "seqno", "subwallet", "bad-signature", "deploy-plugin", "install", "remove-other", "last-seqno"]),
      ("plugin", ".plugin", ["ok", "install-plugin", "remove-plugin"]), ("last-seqno", ".last-seqno", ["last-seqno", "ok"])] do
    for (bname, bal) in [("rich", 1000000000), ("poor", 2000000)] do
      for (n, m) in ← msgs get "wallet4" ns do
        out := out.push (mk s!"wallet4/{dname}/{n}/{bname}" (acc (← data d) bal) m)
  let deploy ← get "wallet4.msg.deploy"
  out := out.push (mk "wallet4/deploy/uninit" (mkAccount 0 addr .uninit 1000000000 1700000000 0 1000) deploy)
  out := out.push (mk "wallet4/deploy/uninit-poor" (mkAccount 0 addr .uninit 300000 1700000000 0 1000) deploy)
  out := out.push (mk "wallet4/deploy/none" (mkAccount 0 addr .none 0 0 0 0) deploy)
  let body (n : String) := get s!"wallet4.body.{n}"
  for (dname, d) in [("plugin", ".plugin"), ("fresh", "")] do
    for (n, bounce) in [("plug", true), ("plug-too-much", true), ("plug-extra", true), ("dstr", true), ("dstr", false),
        ("plug-short", true), ("comment", true), ("unknown", true)] do
      out := out.push (mk s!"wallet4/{dname}/internal/{n}{if bounce then "" else "/no-bounce"}" (acc (← data d) 1000000000)
        (intMsgCell 0 addr 100000000 (← body n) (bounce := bounce)))
  for n in ["plug", "dstr"] do
    out := out.push (mk s!"wallet4/plugin/internal/{n}/stranger" (acc (← data ".plugin") 1000000000)
      (intMsgCell 0 addr 100000000 (← body n) (src := stranger)))
  out := out.push (mk "wallet4/plugin/internal/plug/bounced" (acc (← data ".plugin") 1000000000)
    (intMsgCell 0 addr 100000000 (← body "plug") (bounce := false) (bounced := true)))
  out := out.push (mk "wallet4/plugin/internal/empty" (acc (← data ".plugin") 1000000000)
    (intMsgCell 0 addr 100000000 Cell.empty))
  return out

/-- Wallet v5r1 (`ton-blockchain/wallet-contract-v5`, `wallet_v5.fc`; `mk`, `get` as for
`wallet4Cases`). External requests with 1 Gram and with 0.002 Gram: one send (in a reference and
inline), three, a send without the +2 mode bit (137 after the commit), one for more than the balance
with +2, an `action_set_code` in the list and a send with a 9-bit mode (147), 255 and 256 sends; the
extended actions: add an extension (0:4444..44; in the masterchain: 145), remove one that is not there
(140), allow the signature (only an extension may: 146), an unsupported action (141), add and remove in
a chain, a send and an add; no action; a wrong prefix (138), a body of 16 bits, a wrong seqno, wallet
id, signature, an expired request. With the extension 0:2222..22: add it again (139), remove it, a
send; with the signature disabled (132 while there is an extension; without one the wallet works);
deployment with the `StateInit`. Internal messages: signed requests (from anyone: a send, a send with
mode 0, a wrong seqno, a wrong signature, too short), a comment, an empty body, a bounced message;
the extension's requests from 0:2222..22 when it is one (a send, disallow the signature, remove itself
and disallow (142), remove itself, add another, an unsupported action, a list with a send of three
references (147)), when it is not, from 0:4444..44 and from the masterchain; with the signature
disabled: disallow again (143), allow, remove the last extension (144), a send, a signed request. -/
def wallet5Cases (get : String → Except String Cell) (mk : String → Cell → Cell → TxCase) :
    Except String (Array TxCase) := do
  let code ← get "wallet5.code"
  let addr := (← get "wallet5.addr").bits
  let data (n : String) := get s!"wallet5.data{n}"
  let acc (d : Cell) (bal : Nat) := mkAccount 0 addr (.active code d) bal 1700000000 0 1000
  let mut out : Array TxCase := #[]
  let fresh := ["ok", "ok-inline", "three", "mode-1", "too-much-ignored", "set-code-action", "bad-mode-bits", "send-255",
    "send-256", "add-ext", "add-ext-masterchain", "remove-ext-missing", "set-signature", "unsupported-action", "add-remove",
    "send-add-ext", "none", "bad-prefix", "short", "seqno", "wallet-id", "expired", "bad-signature"]
  for (dname, d, ns, bals) in [("fresh", "", fresh, [("rich", 1000000000), ("poor", 2000000)]),
      ("ext", ".ext", ["add-ext-existing", "remove-ext", "ok", "add-ext"], [("rich", 1000000000)]),
      ("disabled-ext", ".disabled-ext", ["ok", "none"], [("rich", 1000000000)]),
      ("disabled", ".disabled", ["ok", "none"], [("rich", 1000000000)])] do
    for (bname, bal) in bals do
      for (n, m) in ← msgs get "wallet5" ns do
        out := out.push (mk s!"wallet5/{dname}/{n}/{bname}" (acc (← data d) bal) m)
  let deploy ← get "wallet5.msg.deploy"
  out := out.push (mk "wallet5/deploy/uninit" (mkAccount 0 addr .uninit 1000000000 1700000000 0 1000) deploy)
  out := out.push (mk "wallet5/deploy/uninit-poor" (mkAccount 0 addr .uninit 300000 1700000000 0 1000) deploy)
  out := out.push (mk "wallet5/deploy/none" (mkAccount 0 addr .none 0 0 0 0) deploy)
  let body (n : String) := get s!"wallet5.body.{n}"
  let int (name : String) (d : String) (b : Cell) (src : Int × BitString := owner) (bounced := false) : Except String TxCase := do
    return mk s!"wallet5/{name}" (acc (← data d) 1000000000)
      (intMsgCell 0 addr 100000000 b (src := src) (bounce := !bounced) (bounced := bounced))
  for n in ["signed", "signed-mode-0", "signed-seqno", "signed-bad-signature", "signed-short", "comment", "ext-send"] do
    out := out.push (← int s!"fresh/internal/{n}" "" (← body n) (src := stranger))
  out := out.push (← int "fresh/internal/empty" "" Cell.empty)
  out := out.push (← int "fresh/internal/bounced" "" (← body "bounced") (bounced := true))
  for n in ["ext-send", "ext-disallow", "ext-remove-disallow", "ext-remove-self", "ext-add", "ext-unsupported", "ext-bad-c5"] do
    out := out.push (← int s!"ext/internal/{n}" ".ext" (← body n))
  out := out.push (← int "ext/internal/ext-send/stranger" ".ext" (← body "ext-send") (src := stranger))
  out := out.push (← int "ext/internal/ext-send/masterchain" ".ext" (← body "ext-send") (src := (-1, owner.2)))
  for n in ["ext-disallow", "ext-allow", "ext-remove-self", "ext-send", "signed"] do
    out := out.push (← int s!"disabled-ext/internal/{n}" ".disabled-ext" (← body n))
  return out

/-- The cases of the corpus at each version of `versions`, as `Tests.Tx.realCases` makes its own
(`get`: the cells of `tools/txoracle/contracts.txt`; `cfg0` the configuration). -/
def cases (get : String → Except String Cell) (cfg0 : Cell) (versions : List Nat) : Except String (Array TxCase) := do
  let mut out : Array TxCase := #[]
  for v in versions do
    let cfg := withVersion cfg0 v 46
    let mk (name : String) (acc msg : Cell) : TxCase :=
      { name := s!"v{v}/real/{name}", config := cfg, account := acc, msg, now := 1700000200, lt := 3000000, seed }
    out := out ++ (← wallet4Cases get mk)
    out := out ++ (← wallet5Cases get mk)
  return out

end Tests.Tx.Corpus
