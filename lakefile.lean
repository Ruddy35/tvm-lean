import Lake
open System Lake DSL

/-- The C++ reference build, if given (`TVMLEAN_TON_BUILD`: the cmake build directory of `ton`,
`TVMLEAN_TON_SRC`: its sources, for the blst headers). On Linux the native crypto is then compiled
against and linked with the same libsodium, OpenSSL, secp256k1 and blst as C++ TVM; without it the
system libsodium is used and the curve operations (`c/tvmlean_crypto_ext.c`) are stubs. -/
def tonCryptoDirs : IO (Option (FilePath × FilePath)) := do
  match (← IO.getEnv "TVMLEAN_TON_BUILD"), (← IO.getEnv "TVMLEAN_TON_SRC") with
  | some b, some s => return some (b, s)
  | _, _ => return none

/-- Linux: the crypto libraries to link, one per line (a response file for the linker), written by
`libtvmlean_crypto` before anything is linked. -/
def cryptoLinkRsp : FilePath := __dir__ / ".lake" / "tvmlean-crypto-link.rsp"

/-- Include directories of the crypto libraries of the C++ reference build. -/
def tonCryptoIncludes (b s : FilePath) : Array String :=
  #["-I", (b / "third-party" / "sodium" / "include").toString,
    "-I", (b / "third-party" / "openssl" / "include").toString,
    "-I", (b / "third-party" / "secp256k1" / "include").toString,
    "-I", (s / "third-party" / "blst" / "bindings").toString]

package "tvm-lean" where
  version := v!"0.1.0"
  moreLinkArgs :=
    if System.Platform.isOSX then
      #[
        "-L/opt/homebrew/lib",
        "-L/usr/local/lib",
        "-lsodium",
        "/Users/daniil/Coding/ton/build/third-party/secp256k1/lib/libsecp256k1.a",
        "/Users/daniil/Coding/ton/build/third-party/openssl/lib/libssl.a",
        "/Users/daniil/Coding/ton/build/third-party/openssl/lib/libcrypto.a",
        "/Users/daniil/Coding/ton/build/third-party/blst/libblst.a"
      ]
    else
      -- Static crypto libraries (avoids glibc version mismatches between system shared libraries and
      -- Lean's sysroot toolchain), listed in a response file: see `cryptoLinkRsp`.
      #[s!"@{cryptoLinkRsp}"]

@[default_target]
lean_lib TvmLeanModel where
  roots := #[`TvmLean.Model, `TvmLean.Boc, `TvmLean.Spec]

@[default_target]
lean_lib TvmLeanSemantics where
  roots := #[`TvmLean.Semantics]

lean_lib TvmLean where
  roots := #[`TvmLean]

-- Machine-checked facts about the model itself: refactored definitions agree with the original
-- ones, decidable equality, the compute-phase wrapper.
lean_lib TvmLeanProofs where
  roots := #[`TvmLean.Proofs.ModelEquiv, `TvmLean.Proofs.DecEq, `TvmLean.Semantics.Contract]

lean_lib TvmLeanNative where
  roots := #[`TvmLean.Native]
  needs := #[`@/libtvmlean_crypto]
  extraDepTargets := #[`libtvmlean_crypto]
  defaultFacets := #[LeanLib.leanArtsFacet, LeanLib.extraDepFacet]

lean_lib TvmLeanValidation where
  roots := #[`TvmLean.Validation]

lean_lib TvmLeanTests where
  srcDir := "."
  roots := #[
    `Tests.Tests,
    `Tests.All,
    `Tests.Instr,
    `Tests.Harness.Registry,
    `Tests.Harness.OracleHarness,
    `Tests.Harness.FuzzHarness,
    `Tests.Harness.Runner,
    `Tests.Harness.Cli,
    `Tests.Harness.Coverage,
    `Tests.Harness.Gen.Arith,
    `Tests.Harness.Gen.Cell,
    `Tests.Harness.Gen.Tuple,
    `Tests.Harness.Gen.TonEnv,
    `Tests.Harness.Gen.Control,
    `Tests.Harness.Gen.Msg,
    `Tests.Harness.Gen.CryptoVectors,
    `Tests.Harness.Gen.Crypto,
    `Tests.Harness.Gen.VmCore,
    `Tests.Harness.Gen.Dict,
    `Tests.Harness.Gen.CellDepth
  ]

target tvmlean_hash.o pkg : FilePath := do
  let oFile := pkg.buildDir / "c" / "tvmlean_hash.o"
  let srcJob ← inputTextFile <| pkg.dir / "c" / "tvmlean_hash.cpp"
  let ton := match ← tonCryptoDirs with | some (b, s) => tonCryptoIncludes b s | none => #[]
  let weakArgs :=
    #["-I", (← getLeanIncludeDir).toString, "-I", (pkg.dir / "c").toString] ++ ton ++
      #["-I", "/opt/homebrew/include", "-I", "/usr/local/include"]
  buildO oFile srcJob weakArgs #["-fPIC", "-std=c++11"] "cc" getLeanTrace

target tvmlean_crypto_ext.o pkg : FilePath := do
  let oFile := pkg.buildDir / "c" / "tvmlean_crypto_ext.o"
  let leanIncludeDir := (← getLeanIncludeDir).toString
  let ton? ← tonCryptoDirs
  let srcPath :=
    if System.Platform.isOSX || ton?.isSome then
      pkg.dir / "c" / "tvmlean_crypto_ext.c"
    else
      pkg.dir / "c" / "tvmlean_crypto_ext_stub.c"
  let srcJob ← inputTextFile srcPath
  let weakArgs :=
    if System.Platform.isOSX then
      #[
        "-I", leanIncludeDir,
        "-I", (pkg.dir / "c").toString,
        "-I", "/opt/homebrew/include",
        "-I", "/usr/local/include",
        "-I", "/Users/daniil/Coding/ton/build/third-party/secp256k1/include",
        "-I", "/Users/daniil/Coding/ton/build/third-party/openssl/include",
        "-I", "/Users/daniil/Coding/ton/third-party/blst/bindings"
      ]
    else
      #["-I", leanIncludeDir, "-I", (pkg.dir / "c").toString] ++
        (match ton? with | some (b, s) => tonCryptoIncludes b s | none => #[])
  buildO oFile srcJob weakArgs #["-fPIC", "-std=gnu17"] "cc" getLeanTrace

target tvmlean_keccak.o pkg : FilePath := do
  let oFile := pkg.buildDir / "c" / "tvmlean_keccak.o"
  let srcJob ← inputTextFile <| pkg.dir / "c" / "keccak.cpp"
  let weakArgs := #["-I", (pkg.dir / "c").toString]
  buildO oFile srcJob weakArgs #["-fPIC", "-std=c++11"] "cc" getLeanTrace

extern_lib libtvmlean_crypto pkg := do
  if !System.Platform.isOSX then
    let libs : List String :=
      match ← tonCryptoDirs with
      | some (b, _) =>
          [(b / "third-party" / "sodium" / "lib" / "libsodium.a").toString,
           (b / "third-party" / "openssl" / "lib" / "libcrypto.a").toString,
           (b / "third-party" / "secp256k1" / "lib" / "libsecp256k1.a").toString,
           (b / "third-party" / "blst" / "libblst.a").toString, "-ldl", "-lpthread"]
      | none => ["/usr/lib/x86_64-linux-gnu/libsodium.a"]
    IO.FS.createDirAll (cryptoLinkRsp.parent.getD ".")
    IO.FS.writeFile cryptoLinkRsp (String.intercalate "\n" libs ++ "\n")
  let oHash ← tvmlean_hash.o.fetch
  let oKeccak ← tvmlean_keccak.o.fetch
  let oExt ← tvmlean_crypto_ext.o.fetch
  let name := nameToStaticLib "tvmlean_crypto"
  buildStaticLib (pkg.staticLibDir / name) #[oHash, oKeccak, oExt]

lean_exe "tvm-lean" where
  root := `Apps.Demo

lean_exe "tvm-lean-tests" where
  root := `Apps.Tests

lean_exe "tvm-lean-tests-subset" where
  root := `Apps.TestsSubset

lean_exe "tvm-lean-diff-test" where
  root := `Apps.DiffTest

lean_exe "tvm-lean-audit-decoder" where
  root := `Apps.AuditDecoder

lean_exe "tvm-lean-actions-debug" where
  root := `Apps.ActionsDebug

lean_exe "tvm-lean-trace-inspect" where
  root := `Apps.TraceInspect

lean_exe "tvm-lean-precompiled-snapshot" where
  root := `Apps.PrecompiledSnapshot

lean_exe "tvm-lean-progress" where
  root := `Apps.Progress

lean_exe "tvm-lean-coverage" where
  root := `Apps.Coverage

lean_exe "tvm-lean-oracle" where
  root := `Apps.Oracle

lean_exe "tvm-lean-oracle-validate" where
  root := `Apps.Oracle
