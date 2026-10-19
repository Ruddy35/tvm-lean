import Tests.Harness.Registry

/-!
Oracle cases for the TON environment instructions (C++ `crypto/vm/tonops.cpp`): each instruction
variant runs under a pool of `c7` values (the default `c7` of the oracle, full / long / short / empty
parameter tuples, a non-tuple `c7[0]`, parameters of wrong types, globals) and a pool of stacks
(integers incl. out-of-range ones, address slices, wrong types), and the model is compared with C++:
exit code, gas, stack, `c4`/`c5`. `initC7 = #[]` means the oracle's default `c7`.
-/

namespace Tests.Gen.TonEnv

open TvmLean

private def iv (n : Int) : Value := .int (.num n)
private def tup (xs : Array Value) : Value := .tuple xs
private def sl (bits : BitString) : Value := .slice (Slice.ofCell (Cell.mkOrdinary bits #[]))

/-- addr_std$10 anycast:nothing wc:int8 addr:bits256 -/
private def addrStdBits (wc : Nat) (h : Nat) : BitString :=
  natToBits 0b10 2 ++ #[false] ++ natToBits wc 8 ++ natToBits h 256

/-- Message address slices: valid forms of every kind, truncated and with trailing bits. -/
def addrPool : Array Value :=
  #[ sl (natToBits 0 2),                                                   -- addr_none
     sl (natToBits 0b01 2 ++ natToBits 8 9 ++ natToBits 0xa5 8),           -- addr_extern
     sl (addrStdBits 0 0x1234567890abcdef),                                -- addr_std, basechain
     sl (addrStdBits 255 0xfedcba),                                        -- addr_std, masterchain
     sl (natToBits 0b10 2 ++ #[true] ++ natToBits 3 5 ++ natToBits 5 3 ++ natToBits 0 8 ++
         natToBits 0x77 256),                                              -- addr_std with anycast
     sl (natToBits 0b11 2 ++ #[false] ++ natToBits 64 9 ++ natToBits 7 32 ++ natToBits 0xab 64), -- addr_var
     sl (natToBits 0b10 2 ++ #[false] ++ natToBits 0 8 ++ natToBits 1 100), -- truncated addr_std
     sl (addrStdBits 0 0x42 ++ natToBits 5 3),                             -- addr_std + 3 extra bits
     sl #[true],                                                           -- too short
     iv 5, .null ]

/-- A full parameter tuple of length `len` (the slots TON defines get values of the right shape). -/
def params (len : Nat) : Array Value :=
  (Array.range len).map fun i =>
    match i with
    | 0 => iv 0x076ef1ea
    | 7 => tup #[iv 5000, .null]
    | 8 => sl (addrStdBits 0 0x99)
    | 9 => .null
    | 10 => .cell Cell.empty
    | 11 => tup #[iv 777, .null]
    | 13 => tup #[tup #[iv 1, iv 2], tup #[iv 3], tup #[]]
    | 14 => tup #[iv 11, iv 12, iv 13]
    | 17 => tup ((Array.range 10).map (fun k => iv (300 + Int.ofNat k)))
    | _ => iv (1000 + Int.ofNat i)

/-- Parameters whose structured slots hold integers instead of tuples. -/
private def paramsWrongTypes : Array Value :=
  (params 18).set! 7 (iv 1) |>.set! 13 (iv 2) |>.set! 14 (iv 3) |>.set! 17 (iv 4)

/-- The `c7` pool (contents of `c7`; `#[]` = the oracle's default). -/
def c7Pool : Array (String × Array Value) :=
  #[ ("default", #[]),
     ("full18", #[tup (params 18)]),
     ("long20-globals", #[tup (params 20), iv 1, iv 2, .null, tup #[iv 3]]),
     ("short10", #[tup (params 10)]),
     ("empty-params", #[tup #[]]),
     ("c7-0-not-tuple", #[iv 5]),
     ("wrong-types", #[tup paramsWrongTypes]) ]

private def cross (suite : String) (variants : Array (String × Instr)) (c7s : Array (String × Array Value))
    (stacks : Array (Array Value)) : Array OracleCase := Id.run do
  let mut out : Array OracleCase := #[]
  for (vl, i) in variants do
    for (cl, c7) in c7s do
      for k in [0:stacks.size] do
        out := out.push
          { name := s!"oracle/{vl}/{cl}/stack{k}", instr := { name := suite }, program := #[i],
            initStack := stacks[k]!, initC7 := c7 }
  return out

private def noArgs : Array (Array Value) := #[#[], #[iv 1]]
private def bigInts : Array Int := #[0, 1, 7, 255, 65536, -1, 2 ^ 63, 2 ^ 256, -(2 ^ 256)]
private def intArgs : Array (Array Value) := bigInts.map (fun n => #[iv n]) ++ #[#[.null], #[]]

/-- One integer argument per stack, plus wrong types. -/
private def ints1 (xs : Array Int) : Array (Array Value) := xs.map (fun n => #[iv n]) ++ #[#[.null], #[]]

private def env (o : TonEnvInstr) : Instr := .tonEnvOp o

/-- Oracle cases of the suite named `suite`. -/
def casesFor (suite : String) : Array OracleCase :=
  let one (o : TonEnvInstr) : Array OracleCase := cross suite #[(suite, env o)] c7Pool noArgs
  match suite with
  | "NOW" => one .now
  | "BLOCKLT" => one .blockLt
  | "LTIME" => one .lTime
  | "RANDSEED" => one .randSeed
  | "BALANCE" => one .balance
  | "MYADDR" => one .myAddr
  | "CONFIGROOT" => one .configRoot
  | "MYCODE" => one .myCode
  | "INCOMINGVALUE" => one .incomingValue
  | "STORAGEFEES" => one .storageFees
  | "PREVBLOCKSINFOTUPLE" => one .prevBlocksInfoTuple
  | "PREVMCBLOCKS" => one .prevMcBlocks
  | "PREVKEYBLOCK" => one .prevKeyBlock
  | "PREVMCBLOCKS_100" => one .prevMcBlocks100
  | "UNPACKEDCONFIGTUPLE" => one .unpackedConfigTuple
  | "DUEPAYMENT" => one .duePayment
  | "GETPRECOMPILEDGAS" => one .getPrecompiledGas
  | "GLOBALID" => one .globalId
  | "GASCONSUMED" => one .gasConsumed
  | "ACCEPT" => one .accept
  | "COMMIT" => one .commit
  | "INMSGPARAMS" => cross suite #[("idx17", env (.getParam 17))] c7Pool noArgs
  | "GETPARAM" => cross suite (#[0, 1, 3, 6, 9, 15].map (fun k => (s!"k{k}", env (.getParam k)))) c7Pool noArgs
  | "GETPARAMLONG" => cross suite (#[16, 17, 18, 19, 20, 100].map (fun k => (s!"k{k}", env (.getParam k)))) c7Pool noArgs
  | "GETPARAMLONG2" => cross suite (#[127, 128, 200, 254].map (fun k => (s!"k{k}", env (.getParam k)))) c7Pool noArgs
  | "INMSG_BOUNCE" => one (.inMsgParam 0)
  | "INMSG_BOUNCED" => one (.inMsgParam 1)
  | "INMSG_SRC" => one (.inMsgParam 2)
  | "INMSG_FWDFEE" => one (.inMsgParam 3)
  | "INMSG_LT" => one (.inMsgParam 4)
  | "INMSG_UTIME" => one (.inMsgParam 5)
  | "INMSG_ORIGVALUE" => one (.inMsgParam 6)
  | "INMSG_VALUE" => one (.inMsgParam 7)
  | "INMSG_VALUEEXTRA" => one (.inMsgParam 8)
  | "INMSG_STATEINIT" => one (.inMsgParam 9)
  | "INMSGPARAM" => cross suite (#[10, 11, 15].map (fun k => (s!"k{k}", env (.inMsgParam k)))) c7Pool noArgs
  | "GETGLOB" => cross suite (#[1, 2, 3, 5, 31].map (fun k => (s!"k{k}", env (.getGlob k)))) c7Pool noArgs
  | "SETGLOB" => cross suite (#[1, 2, 5, 31].map (fun k => (s!"k{k}", env (.setGlob k)))) c7Pool
      #[#[iv 42], #[tup #[iv 1]], #[]]
  | "GETGLOBVAR" => cross suite #[("var", env .getGlobVar)] c7Pool (ints1 #[0, 1, 2, 3, 5, 31, 254, 255, -1])
  | "SETGLOBVAR" => cross suite #[("var", env .setGlobVar)] c7Pool
      ((#[0, 1, 2, 5, 31, 254, 255, -1] : Array Int).map (fun k => #[iv 42, iv k]) ++ #[#[iv 42], #[]])
  | "RANDU256" => one .randu256
  | "RAND" => cross suite #[("rand", env .rand)] c7Pool (ints1 #[0, 1, 1000, -5, 2 ^ 256 - 1])
  | "SETRAND" => cross suite #[("setrand", env (.setRand false))] c7Pool (ints1 #[0, 1, 2 ^ 256 - 1, 2 ^ 256, -1])
  | "ADDRAND" => cross suite #[("addrand", env (.setRand true))] c7Pool (ints1 #[0, 1, 2 ^ 256 - 1, 2 ^ 256, -1])
  | "SETGASLIMIT" => cross suite #[("setgaslimit", env .setGasLimit)] #[("default", #[])]
      (ints1 #[0, 1, 100, 1000000, -1, 2 ^ 63, 2 ^ 64])
  | "CONFIGDICT" => one .configDict
  | "CONFIGPARAM" => cross suite #[("param", env (.configParam false))] c7Pool (ints1 #[0, 1, 8, 34, -1, 2 ^ 32])
  | "CONFIGOPTPARAM" => cross suite #[("optparam", env (.configParam true))] c7Pool (ints1 #[0, 1, 8, 34, -1, 2 ^ 32])
  | "PARSEMSGADDR" => cross suite #[("parse", env (.parseMsgAddr false))] #[("default", #[])] (addrPool.map (fun a => #[a]))
  | "PARSEMSGADDRQ" => cross suite #[("parseq", env (.parseMsgAddr true))] #[("default", #[])] (addrPool.map (fun a => #[a]))
  | "REWRITESTDADDR" => cross suite #[("rw", env (.rewriteStdAddr false))] #[("default", #[])] (addrPool.map (fun a => #[a]))
  | "REWRITESTDADDRQ" => cross suite #[("rwq", env (.rewriteStdAddr true))] #[("default", #[])] (addrPool.map (fun a => #[a]))
  | "REWRITEVARADDR" => cross suite #[("rw", env (.rewriteVarAddr false))] #[("default", #[])] (addrPool.map (fun a => #[a]))
  | "REWRITEVARADDRQ" => cross suite #[("rwq", env (.rewriteVarAddr true))] #[("default", #[])] (addrPool.map (fun a => #[a]))
  | "GETGASFEE" => cross suite #[("fee", env .getGasFee)] c7Pool
      ((#[0, 1, 1000, 1000000, -1, 2 ^ 63] : Array Int).flatMap (fun g => #[#[iv g, iv 0], #[iv g, iv (-1)]]) ++ #[#[iv 1], #[]])
  | "GETGASFEESIMPLE" => cross suite #[("fee", env .getGasFeeSimple)] c7Pool
      ((#[0, 1, 1000, 1000000, -1, 2 ^ 63] : Array Int).flatMap (fun g => #[#[iv g, iv 0], #[iv g, iv (-1)]]) ++ #[#[iv 1], #[]])
  | "GETSTORAGEFEE" => cross suite #[("fee", env .getStorageFee)] c7Pool
      #[#[iv 1, iv 100, iv 3600, iv 0], #[iv 10, iv 10000, iv 86400, iv (-1)], #[iv 0, iv 0, iv 0, iv 0],
        #[iv (-1), iv 1, iv 1, iv 0], #[iv (2 ^ 63), iv 1, iv 1, iv 0], #[iv 1, iv 1, iv 1], #[]]
  | "GETFORWARDFEE" => cross suite #[("fee", env .getForwardFee)] c7Pool
      #[#[iv 1, iv 100, iv 0], #[iv 10, iv 10000, iv (-1)], #[iv 0, iv 0, iv 0], #[iv (-1), iv 1, iv 0],
        #[iv (2 ^ 63), iv 1, iv 0], #[iv 1, iv 1], #[]]
  | "GETFORWARDFEESIMPLE" => cross suite #[("fee", env .getForwardFeeSimple)] c7Pool
      #[#[iv 1, iv 100, iv 0], #[iv 10, iv 10000, iv (-1)], #[iv 0, iv 0, iv 0], #[iv (-1), iv 1, iv 0],
        #[iv (2 ^ 63), iv 1, iv 0], #[iv 1, iv 1], #[]]
  | "GETORIGINALFWDFEE" => cross suite #[("fee", env .getOriginalFwdFee)] c7Pool
      #[#[iv 0, iv 0], #[iv 1000, iv 0], #[iv 1000, iv (-1)], #[iv (-1), iv 0], #[iv (2 ^ 63), iv 0], #[iv 1], #[]]
  | _ => #[]

end Tests.Gen.TonEnv
