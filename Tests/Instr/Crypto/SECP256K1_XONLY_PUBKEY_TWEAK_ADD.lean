import Tests.Harness.Registry
import Tests.Harness.Gen.Crypto
import TvmLean.Spec.Index

open TvmLean
open Tests

namespace Tests.Instr.Crypto.SECP256K1_XONLY_PUBKEY_TWEAK_ADD

def suite : InstrSuite where
  id := { name := "SECP256K1_XONLY_PUBKEY_TWEAK_ADD" }
  unit := Tests.Gen.Crypto.unitFor "SECP256K1_XONLY_PUBKEY_TWEAK_ADD"
  oracle := Tests.Gen.Crypto.casesFor "SECP256K1_XONLY_PUBKEY_TWEAK_ADD"
  fuzz := #[]

initialize registerSuite suite

end Tests.Instr.Crypto.SECP256K1_XONLY_PUBKEY_TWEAK_ADD
