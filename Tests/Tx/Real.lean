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
  sets and election parameters of the configuration.
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
    let (code, data) := el
    let elAcc := mkAccount (-1) elAddr (.active code data) 500000000000 1700000000 0 1000
    for (n, body) in [("transfer", natToBits 0 32), ("stake", natToBits 0x4e73744b 32 ++ natToBits 7 64),
        ("recover", natToBits 0x47657424 32 ++ natToBits 8 64), ("unknown", natToBits 0x12345678 32 ++ natToBits 9 64),
        ("empty", #[])] do
      out := out.push (mk s!"elector/{n}" elAcc (intMsg (-1) elAddr 10000000000 true none body))
    for isTock in [false, true] do
      out := out.push { mk s!"elector/{if isTock then "tock" else "tick"}" elAcc Cell.empty with tickTock := some isTock }
  return out

end Tests.Tx
