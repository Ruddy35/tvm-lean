import Tests.Harness.Registry

/-!
Oracle cases for the action instructions (C++ `tonops.cpp`: SENDRAWMSG, SENDMSG, RAWRESERVE{X},
SETCODE, SETLIBCODE, CHANGELIB). They append output actions to `c5`; the oracle compares the `c5`
hash with C++, so the exact serialization of every action is checked, together with exit code,
gas and stack. Messages are serialized by hand per `block.tlb` (internal to basechain and
masterchain, body inline or in a reference, large value; external outbound; malformed cells).
-/

namespace Tests.Gen.Msg

open TvmLean

private def iv (n : Int) : Value := .int (.num n)

/-- Grams (VarUInteger 16): 4-bit byte length, then the value. -/
private def grams (g : Nat) : BitString :=
  let len := (Nat.log2 g + 8) / 8
  let len := if g = 0 then 0 else len
  natToBits len 4 ++ natToBits g (8 * len)

private def addrStd (wc : Nat) (h : Nat) : BitString :=
  natToBits 0b10 2 ++ #[false] ++ natToBits wc 8 ++ natToBits h 256

/-- int_msg_info$0 ihr_disabled bounce bounced src dest value ihr_fee fwd_fee created_lt created_at,
then no init and the body (inline empty, or in a reference). -/
private def intMsg (wc : Nat) (value : Nat) (bodyRef : Option Cell) : Cell :=
  let hdr := #[false, true, true, false] ++ natToBits 0 2 ++ addrStd wc 0x1234 ++ grams value ++ #[false] ++
    grams 0 ++ grams 0 ++ natToBits 0 64 ++ natToBits 0 32 ++ #[false]
  match bodyRef with
  | none => Cell.mkOrdinary (hdr ++ #[false]) #[]
  | some b => Cell.mkOrdinary (hdr ++ #[true]) #[b]

/-- ext_out_msg_info$11 src:addr_none dest:addr_none created_lt created_at, no init, empty body. -/
private def extOutMsg : Cell :=
  Cell.mkOrdinary (natToBits 0b11 2 ++ natToBits 0 2 ++ natToBits 0 2 ++ natToBits 0 64 ++ natToBits 0 32 ++
    #[false, false]) #[]

private def body : Cell := Cell.mkOrdinary (natToBits 0xdeadbeef 32) #[]

/-- Message cells. -/
def msgPool : Array Cell :=
  #[ intMsg 0 100 none, intMsg 255 1000000000 none, intMsg 0 (2 ^ 100) (some body), extOutMsg,
     Cell.empty, Cell.mkOrdinary (natToBits 0x5a 8) #[] ]

private def cross (suite : String) (i : Instr) (stacks : Array (Array Value)) : Array OracleCase := Id.run do
  let mut out : Array OracleCase := #[]
  for k in [0:stacks.size] do
    out := out.push
      { name := s!"oracle/stack{k}", instr := { name := suite }, program := #[i], initStack := stacks[k]! }
  return out

private def env (o : TonEnvInstr) : Instr := .tonEnvOp o

private def msgModeStacks (modes : Array Int) : Array (Array Value) :=
  (msgPool.flatMap (fun c => modes.map (fun m => #[.cell c, iv m]))) ++
    #[#[.null, iv 0], #[.cell (msgPool[0]!)], #[]]

/-- Oracle cases of the suite named `suite`. -/
def casesFor (suite : String) : Array OracleCase :=
  match suite with
  | "SENDRAWMSG" => cross suite (env .sendRawMsg) (msgModeStacks #[0, 1, 2, 64, 128, 130, 255, 256, -1])
  | "SENDMSG" => cross suite (env .sendMsg) (msgModeStacks #[0, 1, 64, 128, 1024, 1025, 255, 256, -1])
  | "RAWRESERVE" => cross suite (env .rawReserve)
      (((#[0, 1, 1000000000, 2 ^ 120 - 1, 2 ^ 120, -1] : Array Int).flatMap
        (fun a => (#[0, 1, 2, 3, 4, 8, 15, 16, 31, 32, -1] : Array Int).map (fun m => #[iv a, iv m]))) ++
        #[#[.null, iv 0], #[iv 5], #[]])
  | "RAWRESERVEX" => cross suite (env .rawReserveX)
      (((#[0, 1000, 2 ^ 120] : Array Int).flatMap (fun a =>
        (#[Value.null, .cell Cell.empty] : Array Value).flatMap (fun d =>
          (#[0, 2, 16, 32, -1] : Array Int).map (fun m => #[iv a, d, iv m])))) ++
        #[#[iv 1, iv 2, iv 0], #[iv 1, .null], #[]])
  | "SETCODE" => cross suite (env .setCode) #[#[.cell Cell.empty], #[.cell body], #[.null], #[iv 1], #[]]
  | "SETLIBCODE" => cross suite (env .setLibCode)
      (((#[0, 1, 2, 3, 16, 17, 18, -1] : Array Int).map (fun m => #[.cell body, iv m])) ++
        #[#[.null, iv 1], #[.cell body], #[]])
  | "CHANGELIB" => cross suite (env .changeLib)
      (((#[0, 2 ^ 256 - 1, -1] : Array Int).flatMap (fun h =>
        (#[0, 1, 2, 16, 17, -1] : Array Int).map (fun m => #[iv h, iv m]))) ++ #[#[.null, iv 1], #[iv 5], #[]])
  | _ => #[]

end Tests.Gen.Msg
