import Tests.Tx.Gen

/-!
# Transactions of the most used mainnet contracts

The codes, data, addresses, external messages and internal message bodies are made by
`tools/txoracle/contracts.fif` (each code checked there against its code hash; its output is
`tools/txoracle/contracts.txt`); the cases below put them in accounts and internal messages. The
owner of every contract is 0:2222..22, the source of the internal messages unless said otherwise;
another account is 0:4444..44.

- wallet v4r2 (`wallet4Cases`);
- wallet v5r1 (`wallet5Cases`);
- the jetton wallet and minter (TEP-74) of `ton-blockchain/token-contract` and the ones most used on
  the mainnet (`jettonCases`);
- the NFT collection and item (TEP-62) of `ton-blockchain/token-contract`, the item as most used on
  the mainnet and as of the repository's head (`nftCases`).
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

/-- Jettons (TEP-74): the wallet and the discoverable minter of `ton-blockchain/token-contract`
(`jetton`) and the ones minter.ton.org deploys (`jetton1`), each family with its own minter address
(`mk`, `get` as for `wallet4Cases`). The wallet of 0:2222..22 (1000 jettons, 1 Gram) gets, with 0.1
Gram from its owner: transfers (plain, with a notification, the payload in a reference, a custom
payload, no response, no forward payload (708), all of the balance, more (706), to the masterchain
(333), a forward amount above the value (709)), burns (plain, no response, more than the balance),
excesses, an unknown operation, 16 bits, an empty body; a transfer with a notification, a forward fee
of 0.005 Gram and 0.06 Gram (709 for one family only: their gas constants differ); from 0:4444..44 a
transfer and a burn (705); a transfer with 0.03 Gram (709), a burn with 0.01 (707), a transfer with
0.0005 Gram (out of gas); internal transfers from the minter (plain, with a notification, without a
response, a forward amount above the value, a mint from addr_none) and from 0:4444..44 (707); bounced
internal transfers, burn notifications and transfers (709). The empty wallet gets a transfer (706). The
wallet of 0:4444..44 gets the internal transfer of 0:2222..22's wallet, active, and deploying it
(absent and uninitialized) as the wallet sends it, and the minter's mint deploying it. The minter
(1 Gram) gets from its admin: mints (plain, with a notification, a message without the jetton amount
or without a message (cell underflow), no query id), admin and content changes, wallet address
requests (with and without the owner, for the masterchain, for addr_none), an unknown operation, 16
bits, an empty body; mint and changes from 0:4444..44 (73), a request from it; a request with 0.005
Gram (75); burn notifications from 0:2222..22's wallet (plain, no response, more than the supply: a
negative total supply does not store) and from 0:2222..22 itself (74); a bounced mint; a mint with a
balance of 0.01 Gram. -/
def jettonCases (get : String → Except String Cell) (mk : String → Cell → Cell → TxCase) :
    Except String (Array TxCase) := do
  let body (n : String) := get s!"jetton.body.{n}"
  let mut out : Array TxCase := #[]
  for fam in ["jetton", "jetton1"] do
    let c (n : String) := get s!"{fam}.{n}"
    let wcode ← c "wallet.code"
    let mcode ← c "minter.code"
    let maddr := (← c "addr.minter").bits
    let waddr := (← c "addr.wallet").bits
    let oaddr := (← c "addr.wallet-other").bits
    let wacc (d : Cell) (a : BitString) (bal : Nat := 1000000000) := mkAccount 0 a (.active wcode d) bal 1700000000 0 1000
    let macc (bal : Nat := 1000000000) : Except String Cell := do return mkAccount 0 maddr (.active mcode (← c "data.minter")) bal 1700000000 0 1000
    let toW (name : String) (acc : Cell) (n : String) (value : Nat := 100000000) (src : Int × BitString := owner)
        (bounced := false) (fwdFee : Nat := 0) : Except String TxCase := do
      return mk s!"{fam}/{name}" acc
        (intMsgCell 0 waddr value (← body n) (src := src) (bounce := !bounced) (bounced := bounced) (fwdFee := fwdFee))
    let w ← c "data.wallet"
    for n in ["transfer", "transfer-notify", "transfer-payload-ref", "transfer-custom", "transfer-no-response",
        "transfer-no-payload", "transfer-all", "transfer-too-much", "transfer-masterchain", "transfer-big-forward", "burn",
        "burn-no-response", "burn-too-much", "excesses", "unknown", "short"] do
      out := out.push (← toW s!"wallet/{n}" (wacc w waddr) n)
    out := out.push (mk s!"{fam}/wallet/empty" (wacc w waddr) (intMsgCell 0 waddr 100000000 Cell.empty))
    out := out.push (← toW "wallet/transfer-notify/fwd-fee" (wacc w waddr) "transfer-notify" (fwdFee := 5000000))
    out := out.push (← toW "wallet/transfer-notify/fwd-fee/0.06" (wacc w waddr) "transfer-notify" 60000000 (fwdFee := 5000000))
    for n in ["transfer", "burn"] do
      out := out.push (← toW s!"wallet/{n}/stranger" (wacc w waddr) n (src := stranger))
    out := out.push (← toW "wallet/transfer/0.03" (wacc w waddr) "transfer" 30000000)
    out := out.push (← toW "wallet/burn/0.01" (wacc w waddr) "burn" 10000000)
    out := out.push (← toW "wallet/transfer/out-of-gas" (wacc w waddr) "transfer" 500000)
    for n in ["internal-transfer", "internal-transfer-notify", "internal-transfer-no-response",
        "internal-transfer-big-forward", "internal-transfer-mint"] do
      out := out.push (← toW s!"wallet/{n}" (wacc w waddr) n (src := (0, maddr)))
    out := out.push (← toW "wallet/internal-transfer/stranger" (wacc w waddr) "internal-transfer" (src := stranger))
    for n in ["bounced-internal-transfer", "bounced-burn-notification", "bounced-transfer"] do
      out := out.push (← toW s!"wallet/{n}" (wacc w waddr) n (bounced := true))
    out := out.push (← toW "wallet-empty/transfer" (wacc (← c "data.wallet-empty") waddr) "transfer")
    -- the wallet of 0:4444..44: an internal transfer from the wallet of 0:2222..22, and deploying it
    let fromOwner ← body "internal-transfer-from-owner"
    let oinit ← c "init.wallet-other"
    let toOther (b : Cell) (src : Int × BitString) (init : Option Cell) :=
      intMsgCell 0 oaddr 100000000 b (src := src) (init := init)
    out := out.push (mk s!"{fam}/wallet-other/internal-transfer-from-owner"
      (wacc (← c "data.wallet-other") oaddr) (toOther fromOwner (0, waddr) none))
    out := out.push (mk s!"{fam}/wallet-other/deploy/none" (mkAccount 0 oaddr .none 0 0 0 0)
      (toOther fromOwner (0, waddr) (some oinit)))
    out := out.push (mk s!"{fam}/wallet-other/deploy/uninit" (mkAccount 0 oaddr .uninit 1000000 1700000000 0 1000)
      (toOther fromOwner (0, waddr) (some oinit)))
    out := out.push (mk s!"{fam}/wallet-other/deploy/mint" (mkAccount 0 oaddr .none 0 0 0 0)
      (toOther (← body "internal-transfer-mint") (0, maddr) (some oinit)))
    -- the minter
    let toM (name : String) (n : String) (value : Nat := 100000000) (src : Int × BitString := owner) (bounced := false)
        (bal : Nat := 1000000000) : Except String TxCase := do
      return mk s!"{fam}/{name}" (← macc bal)
        (intMsgCell 0 maddr value (← body n) (src := src) (bounce := !bounced) (bounced := bounced))
    for n in ["mint", "mint-notify", "mint-bad-message", "mint-no-message", "mint-no-query", "change-admin",
        "change-admin-none", "change-content", "provide", "provide-no-include", "provide-masterchain", "provide-none",
        "unknown", "short"] do
      out := out.push (← toM s!"minter/{n}" n)
    out := out.push (mk s!"{fam}/minter/empty" (← macc) (intMsgCell 0 maddr 100000000 Cell.empty))
    for n in ["mint", "change-admin", "change-content", "provide"] do
      out := out.push (← toM s!"minter/{n}/stranger" n (src := stranger))
    out := out.push (← toM "minter/provide/0.005" "provide" 5000000)
    for n in ["burn-notification", "burn-notification-no-response", "burn-notification-too-much"] do
      out := out.push (← toM s!"minter/{n}" n (src := (0, waddr)))
    out := out.push (← toM "minter/burn-notification/owner" "burn-notification")
    out := out.push (← toM "minter/mint/bounced" "mint" (bounced := true))
    out := out.push (← toM "minter/mint/poor" "mint" (bal := 10000000))
  return out

/-- NFT (TEP-62) of `ton-blockchain/token-contract`: the item as most used on the mainnet (`nft`) and as
of the repository's head (`nft2`), and the collection (`mk`, `get` as for `wallet4Cases`). The item 3
of 0:2222..22 (0.06 Gram) gets, with 0.05 Gram from its owner: transfers to 0:4444..44 (with a
response and a notification, plain, without the forward payload bit (708 for `nft2` only), the payload
in a reference, a custom payload, to the masterchain and with the response in the masterchain (333),
a forward amount above the balance (402)), get_static_data, an unknown operation, 16 bits, an empty
body; a transfer with a forward fee of 0.001 Gram; from 0:4444..44 a transfer (401) and get_static_data;
a transfer of an item with no balance and 0.01 Gram (402); a bounced transfer. The item not yet
initialized gets the collection's initialization, the same from 0:4444..44 (405), and a transfer; item
5 is deployed (absent, uninitialized) by the collection's message. The collection (1 Gram) gets from
its owner: royalty parameters, deploy the next item, a deployed one, one beyond the next (402); batches
of 3 items, with a gap (405), of 250 items (with 20 Gram); an owner change, an unknown operation, 16
bits, a deploy without query id, an empty body; from 0:4444..44 royalty parameters, a deploy and an
owner change (401); a bounced deploy. -/
def nftCases (get : String → Except String Cell) (mk : String → Cell → Cell → TxCase) :
    Except String (Array TxCase) := do
  let body (n : String) := get s!"nft.body.{n}"
  let caddr := (← get "nft.addr.collection").bits
  let mut out : Array TxCase := #[]
  for fam in ["nft", "nft2"] do
    let c (n : String) := get s!"{fam}.{n}"
    let code ← c "item.code"
    let iaddr := (← c "addr.item").bits
    let iacc (d : Cell) (bal : Nat := 60000000) := mkAccount 0 iaddr (.active code d) bal 1700000000 0 1000
    let toI (name : String) (acc : Cell) (n : String) (value : Nat := 50000000) (src : Int × BitString := owner)
        (bounced := false) (fwdFee : Nat := 0) : Except String TxCase := do
      return mk s!"{fam}/{name}" acc
        (intMsgCell 0 iaddr value (← body n) (src := src) (bounce := !bounced) (bounced := bounced) (fwdFee := fwdFee))
    let d ← c "data.item"
    for n in ["transfer", "transfer-plain", "transfer-no-payload", "transfer-payload-ref", "transfer-custom",
        "transfer-masterchain", "transfer-response-masterchain", "transfer-big-forward", "get-static-data", "unknown",
        "short"] do
      out := out.push (← toI s!"item/{n}" (iacc d) n)
    out := out.push (mk s!"{fam}/item/empty" (iacc d) (intMsgCell 0 iaddr 50000000 Cell.empty))
    out := out.push (← toI "item/transfer/fwd-fee" (iacc d) "transfer" (fwdFee := 1000000))
    for n in ["transfer", "get-static-data"] do
      out := out.push (← toI s!"item/{n}/stranger" (iacc d) n (src := stranger))
    out := out.push (← toI "item/transfer/poor" (iacc d 0) "transfer" 10000000)
    out := out.push (← toI "item/transfer/bounced" (iacc d) "transfer" (bounced := true))
    let d0 ← c "data.item-new"
    out := out.push (← toI "item-new/init" (iacc d0) "init" (src := (0, caddr)))
    out := out.push (← toI "item-new/init/stranger" (iacc d0) "init" (src := stranger))
    out := out.push (← toI "item-new/transfer" (iacc d0) "transfer")
    -- item 5, deployed by the collection
    let a5 := (← c "addr.item5").bits
    let init5 ← c "init.item5"
    for (aname, acc) in [("none", mkAccount 0 a5 .none 0 0 0 0), ("uninit", mkAccount 0 a5 .uninit 1000000 1700000000 0 1000)] do
      out := out.push (mk s!"{fam}/item5/deploy/{aname}" acc
        (intMsgCell 0 a5 50000000 (← body "init5") (src := (0, caddr)) (init := some init5)))
  -- the collection
  let ccode ← get "nft.collection.code"
  let cacc (bal : Nat := 1000000000) : Except String Cell := do
    return mkAccount 0 caddr (.active ccode (← get "nft.data.collection")) bal 1700000000 0 1000
  let toC (name : String) (n : String) (value : Nat := 100000000) (src : Int × BitString := owner) (bounced := false)
      (bal : Nat := 1000000000) : Except String TxCase := do
    return mk s!"nft/{name}" (← cacc bal)
      (intMsgCell 0 caddr value (← body n) (src := src) (bounce := !bounced) (bounced := bounced))
  for n in ["royalty", "deploy", "deploy-existing", "deploy-gap", "batch", "batch-gap", "change-owner", "unknown", "short",
      "deploy-no-query"] do
    out := out.push (← toC s!"collection/{n}" n)
  out := out.push (← toC "collection/batch-250" "batch-250" (bal := 20000000000))
  out := out.push (mk "nft/collection/empty" (← cacc) (intMsgCell 0 caddr 100000000 Cell.empty))
  for n in ["royalty", "deploy", "change-owner"] do
    out := out.push (← toC s!"collection/{n}/stranger" n (src := stranger))
  out := out.push (← toC "collection/deploy/bounced" "deploy" (bounced := true))
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
    out := out ++ (← jettonCases get mk)
    out := out ++ (← nftCases get mk)
  return out

end Tests.Tx.Corpus
