import TvmLean.Semantics.Exec.Common
import TvmLean.Semantics.Exec.Crypto.HashExt
import TvmLean.Semantics.Exec.Crypto.HashCU
import TvmLean.Semantics.Exec.Crypto.HashSU
import TvmLean.Semantics.Exec.Crypto.Sha256U
import TvmLean.Semantics.Exec.Crypto.ChkSignU
import TvmLean.Semantics.Exec.Crypto.ChkSignS
import TvmLean.Semantics.Exec.Crypto.Ext

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrCrypto (i : Instr) (next : VM Unit) : VM Unit :=
  execInstrCryptoHashExt i <|
  execInstrCryptoHashCU i <|
  execInstrCryptoHashSU i <|
  execInstrCryptoSha256U i <|
  execInstrCryptoChkSignU i <|
  execInstrCryptoChkSignS i <|
  execInstrCryptoExt i <|
    next

end TvmLean
