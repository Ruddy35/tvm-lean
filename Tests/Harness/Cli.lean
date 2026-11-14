import Tests.Harness.Runner

namespace Tests

private def parsePositiveNatArg (flag : String) (value : String) : IO Nat :=
  match value.trim.toNat? with
  | some n =>
      if n > 0 then
        pure n
      else
        throw (IO.userError s!"{flag}: expected positive integer, got {value}")
  | none =>
      throw (IO.userError s!"{flag}: expected positive integer, got {value}")

def parseCliArgs (args : List String) (opts : RunnerOpts := {}) : IO RunnerOpts :=
  match args with
  | [] => pure opts
  | "--filter" :: id :: rest =>
      parseCliArgs rest { opts with filter? := some id }
  | "--jobs" :: n :: rest => do
      let jobs ← parsePositiveNatArg "--jobs" n
      parseCliArgs rest { opts with jobs? := some jobs }
  | "--shard" :: kn :: rest =>
      match kn.splitOn "/" with
      | [k, n] =>
          match k.trim.toNat?, n.trim.toNat? with
          | some k, some n =>
              if k < n then parseCliArgs rest { opts with shard? := some (k, n) }
              else throw (IO.userError s!"--shard: expected k/n with k < n, got {kn}")
          | _, _ => throw (IO.userError s!"--shard: expected k/n, got {kn}")
      | _ => throw (IO.userError s!"--shard: expected k/n, got {kn}")
  | "--no-progress" :: rest =>
      parseCliArgs rest { opts with progress := false }
  | "--unit-only" :: rest =>
      parseCliArgs rest { opts with unitOnly := true }
  | "--oracle-only" :: rest =>
      parseCliArgs rest { opts with oracleOnly := true }
  | "--fuzz-only" :: rest =>
      parseCliArgs rest { opts with fuzzOnly := true }
  | "--opcode-check" :: rest =>
      parseCliArgs rest { opts with opcodeCheck := true }
  | "--opcode-share" :: rest =>
      parseCliArgs rest { opts with opcodeShare := true }
  | "--dump-cases" :: names :: rest =>
      parseCliArgs rest { opts with dumpCases? := some names }
  | "--cases-file" :: path :: rest =>
      parseCliArgs rest { opts with casesFile? := some path }
  | "--" :: rest =>
      parseCliArgs rest opts
  | arg :: _ =>
      throw (IO.userError s!"unknown argument: {arg}")
termination_by structural args

end Tests
