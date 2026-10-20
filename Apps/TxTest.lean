import Tests.Tx.Gen
import TvmLean.Native

/-!
`tvm-lean-tx-test`: whole ordinary transactions of the model against the C++ transaction emulator
(`tools/txoracle/txoracle.py`, `libemulator.so` of `TVMLEAN_TON_BUILD` or `TVMLEAN_EMULATOR_LIB`).
For each case the transaction and the new account must have the same hashes, or both sides fail the
same way. Options: `--versions a,b,...` (default 0..16), `--filter <substring>`; `--fuzz <n>`
`--seed <s>`: `n` random cases (versions, accounts, contracts with actions, messages) instead.
-/

open TvmLean TvmLean.Tx Tests.Tx

def hexOf (c : Cell) : String :=
  match stdBocSerialize c with
  | .ok b => String.join (b.toList.map fun x =>
      let s := (Nat.toDigits 16 x.toNat).asString
      if s.length = 1 then "0" ++ s else s)
  | .error _ => "?"

def main (args : List String) : IO UInt32 := do
  let rec opt : List String → List Nat × String × Nat × Nat → List Nat × String × Nat × Nat
    | "--versions" :: v :: rest, (_, f, n, sd) => opt rest ((v.splitOn ",").filterMap String.toNat?, f, n, sd)
    | "--filter" :: f :: rest, (vs, _, n, sd) => opt rest (vs, f, n, sd)
    | "--fuzz" :: n :: rest, (vs, f, _, sd) => opt rest (vs, f, n.toNat!, sd)
    | "--seed" :: sd :: rest, (vs, f, n, _) => opt rest (vs, f, n, sd.toNat!)
    | _ :: rest, acc => opt rest acc
    | [], acc => acc
  let (versions, filter, fuzzCount, fuzzSeed) := opt args ((List.range 17), "", 0, 20261020)
  let cfgFile := "tools/txoracle/testnet-config.b64"
  let cfg ← match stdBocDeserialize (base64Decode (← IO.FS.readFile cfgFile).trim) with
    | .ok c => pure c
    | .error _ => throw (IO.userError s!"cannot read {cfgFile}")
  let base := if fuzzCount > 0 then fuzzCases cfg fuzzCount fuzzSeed else cases cfg versions
  let all := base.filter (fun c => filter.isEmpty || (c.name.splitOn filter).length > 1)
  let answers ← runOracle all
  let mut failures := 0
  let mut unsupported : Array String := #[]
  let mut same := 0
  let mut kinds : Std.HashMap String Nat := {}
  for (c, ans) in all.zip answers do
    let model := emulate nativeHost c.config c.account c.msg c.now c.lt c.seed
    let verdict : Option String :=
      match model, ans with
      | .unsupported w, _ => some s!"unsupported: {w}"
      | .ok tx acc, .ok tx' acc' =>
          if tx.hashBytes != tx'.hashBytes then some s!"FAIL transaction differs\n  C++   {hexOf tx'}\n  model {hexOf tx}"
          else if acc.hashBytes != acc'.hashBytes then some s!"FAIL account differs\n  C++   {hexOf acc'}\n  model {hexOf acc}"
          else none
      | .externalNotAccepted e, .externalNotAccepted e' =>
          if e == e' then none else some s!"FAIL not accepted with {e}, C++ {e'}"
      | .failed _, .error _ => none
      | .ok _ _, .error e => some s!"FAIL model ok, C++ error: {e}"
      | .failed r, _ => some s!"FAIL model failed ({r}), C++ succeeded"
      | .externalNotAccepted e, _ => some s!"FAIL model: not accepted ({e})"
      | .ok _ _, .externalNotAccepted e => some s!"FAIL C++: not accepted ({e})"
    let kind := match ans with
      | .ok _ _ => "ok" | .externalNotAccepted _ => "not-accepted" | .error _ => "error"
    kinds := kinds.insert kind ((kinds.getD kind 0) + 1)
    match verdict with
    | none => same := same + 1
    | some v =>
        if v.startsWith "unsupported" then unsupported := unsupported.push s!"{c.name}: {v}"
        else
          failures := failures + 1
          IO.println s!"[FAIL] {c.name}: {v}"
  for u in unsupported do IO.println s!"[unsupported] {u}"
  IO.println s!"C++ outcomes: {kinds.toList}"
  IO.println s!"tx: cases={all.size} same={same} unsupported={unsupported.size} failures={failures}"
  return if failures = 0 then 0 else 1
