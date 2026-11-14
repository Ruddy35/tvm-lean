import TvmLean.Validation.Oracle.Runner

/-!
Many oracle runs in one `fift` process, each with the result `runOracle` gives for it alone.

A `fift` start costs about 6 ms, and a fork of the test process (~250 MB) more: most of the CPU of a
fuzz case when every case runs a `fift` of its own. `runOracleMany` writes a script of up to
`oracleBatchSize` cases that includes `oracle/fif/ton_oracle_runvm_lib.fif` and runs, per case, the
words `oracle/fif/ton_oracle_runvm.fif` runs on its arguments (the gas limit, the library
collection, the stack tokens, the code), between `oracle-case-begin`, which starts the case from the
state that script starts from (an empty stack, no library collection, the default `c7` and gas
limit), and `oracle-case-end`, which marks its output as complete. `runvmx` builds a fresh `VmState`
from its arguments (crypto/vm/vm.cpp:579-588).

A case whose output block is not complete (`fift` stopped on a Fift error in it, or died) or does not
parse runs alone (`runOracle`), and the cases after it in a new process; a case that cannot be
written in a script (a token with `"` or a line break, more than one library collection, a cell
without a BOC) runs alone. So the result of every case is the one of a process of its own: its
output if its block is complete, else what `runOracle` gives.
-/

namespace TvmLeanOracleValidate

open TvmLean

/-- One run of `runvmx` as `runOracle` makes it: the code cell, the stack tokens (bottom first, as
`push-token` of `oracle/fif/ton_oracle_runvm_lib.fif` reads them), the library collections (at most
one) and the gas limit. -/
structure OracleInvocation where
  code : Cell
  stackArgs : List String
  libraries : Array Cell := #[]
  gasLimit : Int := 1_000_000

/-- What `runOracle` gives for `inv`: its output, or the exception it throws. -/
def runOracleAlone (inv : OracleInvocation) : IO (Except IO.Error OracleOut) := do
  try
    pure (.ok (← runOracle inv.code inv.stackArgs inv.libraries inv.gasLimit))
  catch e =>
    pure (.error e)

/-- Cases per `fift` process in `runOracleMany`: env `TVMLEAN_ORACLE_BATCH`, default 512; `0` or `1`:
every case in a process of its own (`runOracle`). -/
def oracleBatchSize : IO Nat := do
  match (← IO.getEnv "TVMLEAN_ORACLE_BATCH") with
  | none => pure 512
  | some v =>
      match v.trim.toNat? with
      | some n => pure n
      | none => throw (IO.userError s!"TVMLEAN_ORACLE_BATCH: expected a number of cases, got '{v}'")

/-- `s` as a Fift string literal. The word `"` takes the text up to the next `"` on its line, with no
escapes (`interpret_quote_str`, crypto/fift/words.cpp:2206-2208; `ParseCtx::scan_word_to`,
crypto/fift/IntCtx.cpp:86-101, which also stops at a NUL), and a script is read by lines
(`ParseCtx::load_next_line`, `std::getline`): `none` for a string with `"`, a line break or a NUL. -/
private def fiftLiteral? (s : String) : Option String :=
  if s.any (fun ch => ch == '"' || ch == '\n' || ch == '\r' || ch == '\x00') then none
  else some ("\"" ++ s ++ "\"")

/-- The lines of case `id` of a script: the words `ton_oracle_runvm.fif` runs on the arguments
`runOracle` gives it (`GAS <limit>`, `LIB <hex>`, the tokens, the code), in its order, between
`oracle-case-begin` and `oracle-case-end`; `none` if `inv` cannot be written in a script (it runs
alone and gets `runOracle`'s error, if any). -/
private def caseScript? (id : Nat) (inv : OracleInvocation) : Option String := do
  let codeLit ← fiftLiteral? (bytesToHex (← (stdBocSerialize inv.code).toOption))
  let gasLit ← fiftLiteral? (toString inv.gasLimit)
  let libLine ←
    match inv.libraries.toList with
    | [] => pure ""
    | [lib] =>
        let libLit ← fiftLiteral? (bytesToHex (← (stdBocSerialize lib).toOption))
        pure s!"{libLit} x>B B>boc vmlibs !\n"
    | _ => none
  let toks ← inv.stackArgs.mapM fun t => (fiftLiteral? t).map (· ++ " push-token\n")
  pure (s!"\"{id}\" oracle-case-begin\n{gasLit} parse-int oracle_gas_limit !\n" ++ libLine ++
    String.join toks ++ s!"{codeLit} oracle-run\n\"{id}\" oracle-case-end\n")

/-- The output of the cases `0 .. n - 1` of a script from its stdout: the lines between `CASE <id>`
and `ENDCASE <id>`, for a case whose `ENDCASE` line is there. Only whole lines count (the text after
the last line break is a line `fift` did not finish). -/
private def batchBlocks (stdout : String) (n : Nat) : Array (Option String) := Id.run do
  let mut blocks : Array (Option String) := Array.replicate n none
  let mut cur : Option Nat := none
  let mut buf : Array String := #[]
  for ln in (stdout.splitOn "\n").dropLast do
    match ln.trim.splitOn "\t" with
    | ["CASE", x] =>
        cur := x.toNat?
        buf := #[]
    | ["ENDCASE", x] =>
        if let some i := cur then
          if x.toNat? == some i && i < n then
            blocks := blocks.set! i (some ("\n".intercalate buf.toList))
        cur := none
        buf := #[]
    | _ =>
        if cur.isSome then
          buf := buf.push ln
  pure blocks

/-- `parseOracle` of a case's output, `none` where it throws. -/
private def parseOracle? (out : String) : IO (Option OracleOut) := do
  try
    pure (some (← parseOracle out))
  catch _ =>
    pure none

/-- Removes the file `path`, if it is there. -/
private def removeFileQuietly (path : System.FilePath) : IO Unit := do
  try
    IO.FS.removeFile path
  catch _ =>
    pure ()

/-- The stdout of `fift` on the script in the file `path`. -/
private def runFiftScript (path : System.FilePath) : IO String := do
  let tonFift := (← IO.getEnv "TON_FIFT_BIN").getD "/Users/daniil/Coding/ton/build/crypto/fift"
  let tonLib := (← IO.getEnv "TON_FIFT_LIB").getD "/Users/daniil/Coding/ton/crypto/fift/lib"
  let res ← IO.Process.output
    { cmd := tonFift, args := #[s!"-I{tonLib}", "-s", path.toString], env := #[("GLOG_minloglevel", "2")] }
  pure res.stdout

/-- The stdout of `fift` on the script `script` (its exit code aside: a case's output counts when its
block is complete), or `""` if the process could not be run. -/
private def runBatchScript (script : String) : IO String := do
  let keepTmp : Bool := (← IO.getEnv "TVMLEANTON_ORACLE_KEEP_TMP").getD "0" == "1"
  try
    let (h, path) ← IO.FS.createTempFile
    try
      h.putStr script
      h.flush
      runFiftScript path
    finally
      if !keepTmp then
        removeFileQuietly path
  catch _ =>
    pure ""

/-- `runOracleAlone` of every invocation of `invs`, in order, run `oracleBatchSize` to a `fift`
process (see the module doc): each result is the one `runOracle` gives for its case alone. -/
def runOracleMany (invs : Array OracleInvocation) : IO (Array (Except IO.Error OracleOut)) := do
  let size ← oracleBatchSize
  if size ≤ 1 then
    return (← invs.mapM runOracleAlone)
  -- the library by its absolute path: `include` looks a relative name up next to the script first
  let libRel := (← IO.getEnv "TVMLEANTON_ORACLE_LIB_FIF").getD "oracle/fif/ton_oracle_runvm_lib.fif"
  let libPath := (← IO.currentDir) / libRel
  let some libLit := fiftLiteral? libPath.toString
    | return (← invs.mapM runOracleAlone)
  let mut outs : Array (Except IO.Error OracleOut) := Array.mkEmpty invs.size
  let mut next : Nat := 0
  -- a round settles at least the case `next`
  for _ in [0:invs.size] do
    if next ≥ invs.size then
      break
    -- the cases of the round: from `next`, at most `size`, up to the first without a script
    let mut body : String := ""
    let mut count : Nat := 0
    for inv in invs.extract next (next + size) do
      match caseScript? count inv with
      | some s =>
          body := body ++ s
          count := count + 1
      | none => break
    if count == 0 then
      for inv in invs.extract next (next + 1) do
        outs := outs.push (← runOracleAlone inv)
      next := next + 1
      continue
    let stdout ← runBatchScript (s!"{libLit} include\n" ++ body ++ "bye\n")
    let cases := invs.extract next (next + count)
    let blocks := batchBlocks stdout count
    -- the cases up to the first without a complete block take their blocks; that one runs alone,
    -- and the next round starts after it
    let mut settled : Nat := 0
    for (inv, block?) in cases.zip blocks do
      match block? with
      | some block =>
          let out ←
            match (← parseOracle? block) with
            | some out => pure (.ok out)
            | none => runOracleAlone inv
          outs := outs.push out
          settled := settled + 1
      | none =>
          outs := outs.push (← runOracleAlone inv)
          settled := settled + 1
          break
    next := next + settled
  pure outs

end TvmLeanOracleValidate
