import Tests.Harness.Registry

/-!
Oracle cases for the hash instructions (C++ `tonops.cpp`, `Hasher.cpp`): HASHCU, HASHSU, HASHBU,
SHA256U and HASHEXT{A}{R} with every hash algorithm (sha256, sha512, blake2b, keccak256, keccak512),
the algorithm taken from the stack, invalid algorithms, slices and builders mixed, data that is not
byte-aligned, appending to a builder and reversed order. Results, exceptions and the per-byte gas
are compared with C++.
-/

namespace Tests.Gen.Crypto

open TvmLean

private def iv (n : Int) : Value := .int (.num n)
private def sl (bits : BitString) : Value := .slice (Slice.ofCell (Cell.mkOrdinary bits #[]))
private def bl (bits : BitString) : Value := .builder { bits := bits, refs := #[] }

private def cross (suite : String) (variants : Array (String × Instr)) (stacks : Array (Array Value)) :
    Array OracleCase := Id.run do
  let mut out : Array OracleCase := #[]
  for (vl, i) in variants do
    for k in [0:stacks.size] do
      out := out.push
        { name := s!"oracle/{vl}/stack{k}", instr := { name := suite }, program := #[i],
          initStack := stacks[k]! }
  return out

private def bytes (n : Nat) (seed : Nat) : BitString := natToBits (seed % (2 ^ (8 * n))) (8 * n)

private def cellPool : Array Cell :=
  let c1 := Cell.mkOrdinary (bytes 4 0xdeadbeef) #[]
  #[Cell.empty, c1, Cell.mkOrdinary (natToBits 5 3) #[c1, c1], Cell.mkOrdinary (bytes 127 7) #[]]

/-- Data pieces for HASHEXT: byte-aligned slices and builders of several lengths, one unaligned. -/
private def pieces : Array Value :=
  #[ sl #[], sl (bytes 1 0x61), sl (bytes 32 0x1234567), bl (bytes 3 0x616263), bl (bytes 100 9),
     sl (bytes 127 3) ]

private def unaligned : Value := sl (natToBits 5 3)

/-- HASHEXT stacks: [builder (append)] x1..xn n [id (from stack)]. -/
private def hashExtStacks (append fromStack : Bool) : Array (Array Value) := Id.run do
  let mut out : Array (Array Value) := #[]
  let pre : Array Value := if append then #[bl (bytes 2 0xffee)] else #[]
  let ids : Array Int := if fromStack then #[0, 1, 2, 3, 4, 5, 254, 255, -1] else #[0]
  for idv in ids do
    let post : Array Value := if fromStack then #[iv idv] else #[]
    for n in [0:4] do
      out := out.push (pre ++ (pieces.extract 0 n) ++ #[iv (Int.ofNat n)] ++ post)
    out := out.push (pre ++ #[pieces[2]!, pieces[4]!, pieces[5]!] ++ #[iv 3] ++ post)
    out := out.push (pre ++ #[unaligned, iv 1] ++ post)
    out := out.push (pre ++ #[iv 7, iv 1] ++ post)
    out := out.push (pre ++ #[pieces[1]!, iv 2] ++ post)
    out := out.push (pre ++ #[iv (-1)] ++ post)
  return out

private def hashExtVariants (append rev : Bool) : Array (String × Instr) :=
  #[0, 1, 2, 3, 4].map (fun id => (s!"id{id}", Instr.cryptoOp (.hashExt id append rev)))

private def hashExtCases (suite : String) (append rev : Bool) : Array OracleCase :=
  cross suite (hashExtVariants append rev) (hashExtStacks append false) ++
    cross suite #[("id-from-stack", .cryptoOp (.hashExt 255 append rev))] (hashExtStacks append true)

/-- Oracle cases of the suite named `suite` (hash instructions; other crypto suites: none yet). -/
def casesFor (suite : String) : Array OracleCase :=
  match suite with
  | "HASHCU" => cross suite #[("hashcu", .cryptoOp .hashCU)]
      ((cellPool.map (fun c => #[.cell c])) ++ #[#[sl #[]], #[.null], #[]])
  | "HASHSU" => cross suite #[("hashsu", .cryptoOp .hashSU)]
      ((cellPool.map (fun c => #[.slice (Slice.ofCell c)])) ++ #[#[.cell Cell.empty], #[.null], #[]])
  | "HASHBU" => cross suite #[("hashbu", .cellExt .hashbu)]
      #[#[bl #[]], #[bl (bytes 4 0xabcd)], #[bl (bytes 127 1)], #[sl #[]], #[.null], #[]]
  | "SHA256U" => cross suite #[("sha256u", .cryptoOp .sha256U)]
      #[#[sl #[]], #[sl (bytes 1 0x61)], #[sl (bytes 127 5)], #[unaligned], #[bl (bytes 1 1)], #[.null], #[]]
  | "HASHEXT" => hashExtCases suite false false
  | "HASHEXTR" => hashExtCases suite false true
  | "HASHEXTA" => hashExtCases suite true false
  | "HASHEXTAR" => hashExtCases suite true true
  | _ => #[]

end Tests.Gen.Crypto
