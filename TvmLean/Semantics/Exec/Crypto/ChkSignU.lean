import TvmLean.Semantics.Exec.Common

namespace TvmLean

set_option maxHeartbeats 1000000 in
def execInstrCryptoChkSignU (host : Host) (i : Instr) (next : VM Unit) : VM Unit := do
  match i with
  | .cryptoOp .chkSignU =>
      VM.checkUnderflow 3
      let key ← VM.popInt
      let sigSlice ← VM.popSlice
      let hash ← VM.popInt

      let msgBytes ←
        match exportUInt256BE hash with
        | .ok bs => pure bs
        | .error e => throw e
      let sigBytes ←
        match sigSlice.prefetchBytesCellUnd 64 with
        | .ok bs => pure bs
        | .error e => throw e
      let keyBytes ←
        match exportUInt256BE key with
        | .ok bs => pure bs
        | .error e => throw e

      modify fun st => st.registerChkSgnCall
      -- TVM 14 rejects the zero key and the identity encoding `01 00..00` before verification
      -- (C++ exec_ed25519_check_signature).
      let weakKey : Bool :=
        ((← get).globalVersion ≥ 14) && (keyBytes[0]! == 0 || keyBytes[0]! == 1) &&
          (List.range 31).all (fun j => keyBytes[j + 1]! == 0)
      let ok := !weakKey && host.ed25519Verify (ByteArray.mk msgBytes) (ByteArray.mk keyBytes) (ByteArray.mk sigBytes)
      VM.pushSmallInt (if ok then (-1) else 0)
  | _ => next

end TvmLean
