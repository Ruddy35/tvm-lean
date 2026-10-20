/-!
C++ `OpcodeInstr::require_version` (`crypto/vm/*.cpp`; inventory: `docs/audit/cpp-registrations.csv`):
the opcodes of codepage 0 that exist from a global version on. Below it `OpcodeInstrWithVersion::dispatch`
(`opctable.cpp:457-461`) charges `gas_per_instr` and throws inv_opcode, before the instruction itself
looks at its arguments or at the length of the code.
-/

namespace TvmLean

/-- Ranges `[lo, hi)` of the 24-bit opcode (the code's first 24 bits, zero-padded, as
`OpcodeTable::lookup_instr` reads it) and the global version they need. -/
def cp0VersionedOpcodes : Array (Nat × Nat × Nat) := #[
  (0xb7f921, 0xb7f926, 4),  -- RIST255_QVALIDATE, RIST255_QADD, RIST255_QSUB, RIST255_QMUL, RIST255_QMULBASE
  (0xcf5000, 0xcf5100, 12),  -- BTOS
  (0xd76600, 0xd77200, 6),  -- CLEVEL, CLEVELMASK, CHASHI, CDEPTHI, CHASHIX, CDEPTHIX
  (0xdb4000, 0xdb5100, 4),  -- RUNVM, RUNVMX
  (0xede300, 0xede500, 9),  -- SETCONTCTRMANY, SETCONTCTRMANYX
  (0xf80700, 0xf80800, 4),  -- GASCONSUMED
  (0xf83400, 0xf83402, 4),  -- PREVMCBLOCKS, PREVKEYBLOCK
  (0xf83402, 0xf83403, 9),  -- PREVMCBLOCKS_100
  (0xf83500, 0xf83600, 4),  -- GLOBALID
  (0xf83600, 0xf83d00, 6),  -- GETGASFEE, GETSTORAGEFEE, GETFORWARDFEE, GETPRECOMPILEDGAS, GETORIGINALFWDFEE, GETGASFEESIMPLE, GETFORWARDFEESIMPLE
  (0xf88000, 0xf88100, 10),  -- GETEXTRABALANCE
  (0xf88100, 0xf881ff, 11),  -- GETPARAMLONG, INMSGPARAMS
  (0xf89000, 0xf8a000, 11),  -- INMSG_BOUNCE, INMSG_BOUNCED, INMSG_SRC, INMSG_FWDFEE, INMSG_LT, INMSG_UTIME, INMSG_ORIGVALUE, INMSG_VALUE, INMSG_VALUEEXTRA, INMSG_STATEINIT, INMSGPARAM
  (0xf90400, 0xf90800, 4),  -- HASHEXT
  (0xf91200, 0xf91300, 4),  -- ECRECOVER
  (0xf91300, 0xf91400, 9),  -- SECP256K1_XONLY_PUBKEY_TWEAK_ADD
  (0xf91400, 0xf91600, 4),  -- P256_CHKSIGNU, P256_CHKSIGNS
  (0xf91600, 0xf91700, 12),  -- HASHBU
  (0xf92000, 0xf92700, 4),  -- RIST255_FROMHASH, RIST255_VALIDATE, RIST255_ADD, RIST255_SUB, RIST255_MUL, RIST255_MULBASE, RIST255_PUSHL
  (0xf93000, 0xf93004, 4),  -- BLS_VERIFY, BLS_AGGREGATE, BLS_FASTAGGREGATEVERIFY, BLS_AGGREGATEVERIFY
  (0xf93010, 0xf93019, 4),  -- BLS_G1_ADD, BLS_G1_SUB, BLS_G1_NEG, BLS_G1_MUL, BLS_G1_MULTIEXP, BLS_G1_ZERO, BLS_MAP_TO_G1, BLS_G1_INGROUP, BLS_G1_ISZERO
  (0xf93020, 0xf93029, 4),  -- BLS_G2_ADD, BLS_G2_SUB, BLS_G2_NEG, BLS_G2_MUL, BLS_G2_MULTIEXP, BLS_G2_ZERO, BLS_MAP_TO_G2, BLS_G2_INGROUP, BLS_G2_ISZERO
  (0xf93030, 0xf93032, 4),  -- BLS_PAIRING, BLS_PUSHR
  (0xfa4800, 0xfa4a00, 12),  -- LDSTDADDR, LDSTDADDRQ
  (0xfa5000, 0xfa5600, 12),  -- LDOPTSTDADDR, LDOPTSTDADDRQ, STSTDADDR, STSTDADDRQ, STOPTSTDADDR, STOPTSTDADDRQ
  (0xfb0800, 0xfb0900, 4)   -- SENDMSG
]

/-- The global version the opcode `opcode24` needs (0: every version). -/
def cp0RequiredVersion (opcode24 : Nat) : Nat :=
  match cp0VersionedOpcodes.find? (fun (lo, hi, _) => lo ≤ opcode24 && opcode24 < hi) with
  | some (_, _, v) => v
  | none => 0

end TvmLean
