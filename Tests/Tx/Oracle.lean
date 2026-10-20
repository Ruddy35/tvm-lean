import Lean.Data.Json
import TvmLean.Boc
import TvmLean.Transaction.Emulate

/-!
# The C++ oracle of whole transactions

`tools/txoracle/txoracle.py` runs the TON transaction emulator (`libemulator.so` of the reference
build) on a batch of cases; the transaction and the new account are compared with the model by
their cell hashes.
-/

namespace Tests.Tx

open TvmLean TvmLean.Tx

/-- A transaction case: the configuration, the `ShardAccount`, the inbound message, the time, the
logical time and the block's random seed; `tickTock`: a tick (`false`) or tock (`true`) transaction,
the message unused. -/
structure TxCase where
  name : String
  config : Cell
  account : Cell
  msg : Cell
  now : Nat
  lt : Nat
  seed : BitString
  tickTock : Option Bool := none

/-- The model's run of a case. -/
def TxCase.emulate (c : TxCase) : Outcome :=
  match c.tickTock with
  | some isTock => emulateTickTock c.config c.account isTock c.now c.lt c.seed
  | none => TvmLean.Tx.emulate c.config c.account c.msg c.now c.lt c.seed

def base64Chars : Array Char :=
  "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/".toList.toArray

def base64Encode (b : ByteArray) : String := Id.run do
  let mut out : Array Char := #[]
  let n := b.size
  for i in [0:(n + 2) / 3] do
    let b0 := b.get! (3 * i)
    let b1 := if 3 * i + 1 < n then b.get! (3 * i + 1) else 0
    let b2 := if 3 * i + 2 < n then b.get! (3 * i + 2) else 0
    let v := (b0.toNat <<< 16) ||| (b1.toNat <<< 8) ||| b2.toNat
    out := out.push base64Chars[v >>> 18 &&& 63]!
    out := out.push base64Chars[v >>> 12 &&& 63]!
    out := out.push (if 3 * i + 1 < n then base64Chars[v >>> 6 &&& 63]! else '=')
    out := out.push (if 3 * i + 2 < n then base64Chars[v &&& 63]! else '=')
  return String.mk out.toList

def base64Decode (s : String) : ByteArray := Id.run do
  let idx (c : Char) : Nat := (base64Chars.findIdx? (· == c)).getD 0
  let cs := (s.toList.filter (· != '=')).toArray
  let mut out : Array UInt8 := #[]
  let mut acc := 0
  let mut bits := 0
  for c in cs do
    acc := (acc <<< 6) ||| idx c
    bits := bits + 6
    if bits ≥ 8 then
      bits := bits - 8
      out := out.push (UInt8.ofNat ((acc >>> bits) &&& 0xff))
      acc := acc &&& ((1 <<< bits) - 1)
  return ByteArray.mk out

def cellB64 (c : Cell) : String :=
  match stdBocSerialize c with
  | .ok b => base64Encode b
  | .error _ => ""

/-- What C++ answered. -/
inductive TxAnswer where
  | ok (transaction : Cell) (account : Cell)
  | externalNotAccepted (exitCode : Int)
  | error (msg : String)

/-- The emulator's answers for `cases`, in order. -/
def runOracle (cases : Array TxCase) (workDir : String := ".") : IO (Array TxAnswer) := do
  let reqFile := s!"{workDir}/.txoracle-req-{← IO.monoNanosNow}.jsonl"
  let lines := cases.map fun c =>
    Lean.Json.compress (Lean.Json.mkObj ([
      ("config", Lean.Json.str (cellB64 c.config)), ("account", Lean.Json.str (cellB64 c.account)),
      ("msg", Lean.Json.str (cellB64 c.msg)), ("utime", Lean.Json.num c.now), ("lt", Lean.Json.num c.lt),
      ("rand_seed", Lean.Json.str (String.join ((bitStringToBytesBE c.seed).toList.map fun x =>
        let s := (Nat.toDigits 16 x.toNat).asString
        if s.length = 1 then "0" ++ s else s)))] ++
      (match c.tickTock with
       | some isTock => [("tick_tock", Lean.Json.str (if isTock then "tock" else "tick"))]
       | none => [])))
  IO.FS.writeFile reqFile (String.intercalate "\n" lines.toList ++ "\n")
  let script := (← IO.getEnv "TVMLEAN_TXORACLE").getD "tools/txoracle/txoracle.py"
  let out ← IO.Process.output { cmd := "sh", args := #["-c", s!"python3 {script} < {reqFile}"] }
  IO.FS.removeFile reqFile
  if out.exitCode != 0 then
    throw (IO.userError s!"txoracle failed: {out.stderr}")
  let answers := (out.stdout.splitOn "\n").filter (· != "") |>.toArray
  answers.mapM fun line => do
    match Lean.Json.parse line with
    | .error e => return .error s!"bad json: {e}"
    | .ok j =>
        let str (k : String) : String := (j.getObjValAs? String k).toOption.getD ""
        if (j.getObjValAs? Bool "success").toOption == some true then
          let cell (k : String) : Option Cell :=
            match stdBocDeserialize (base64Decode (str k)) with
            | .ok c => some c
            | .error _ => none
          match cell "transaction", cell "shard_account" with
          | some tx, some sa =>
              -- the new ShardAccount: ^Account last_trans_hash:bits256 last_trans_lt:uint64
              match sa.refs[0]? with
              | some acc => return .ok tx acc
              | none => return .error "shard account without account"
          | _, _ => return .error "bad boc"
        else if (j.getObjValAs? Bool "external_not_accepted").toOption == some true then
          return .externalNotAccepted ((j.getObjValAs? Int "vm_exit_code").toOption.getD 0)
        else
          return .error (str "error")

end Tests.Tx
