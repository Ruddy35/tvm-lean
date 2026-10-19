import Tests.Harness.Registry

/-!
Oracle cases for the tuple and null instructions (C++ `crypto/vm/tupleops.cpp`). Every variant of an
instruction is run on a pool of initial stacks — tuples of several sizes and contents, nested
tuples, `null`, integers and other types, too shallow stacks, out-of-range indices — and the model
is compared with C++: exit code, gas, resulting stack. Stacks list the bottom first, top last.
-/

namespace Tests.Gen.Tuple

open TvmLean

private def iv (n : Int) : Value := .int (.num n)
private def tup (xs : Array Value) : Value := .tuple xs

/-- Tuples used as operands. -/
def tuplePool : Array Value :=
  #[ tup #[],
     tup #[iv 1],
     tup #[iv 1, iv 2],
     tup #[iv 7, .null, iv (-3)],
     tup #[iv 1, iv 2, iv 3, iv 4],
     tup #[tup #[iv 1, iv 2], tup #[iv 3, tup #[iv 4, iv 5], iv 6], iv 7, tup #[]],
     tup ((Array.range 15).map (fun i => iv (Int.ofNat i))),
     tup ((Array.range 16).map (fun i => iv (100 + Int.ofNat i))) ]

/-- Operands that are not tuples. -/
def nonTuplePool : Array Value :=
  #[iv 5, .null, .cell Cell.empty, .slice (Slice.ofCell Cell.empty)]

private def cross (suite : String) (variants : Array (String × Instr)) (stacks : Array (Array Value)) :
    Array OracleCase := Id.run do
  let mut out : Array OracleCase := #[]
  for (vl, i) in variants do
    for k in [0:stacks.size] do
      out := out.push
        { name := s!"oracle/{vl}/stack{k}", instr := { name := suite }, program := #[i],
          initStack := stacks[k]! }
  return out

/-- One operand on top: each tuple, each other type, a value below the tuple, an empty stack. -/
private def oneTuple : Array (Array Value) :=
  tuplePool.map (fun t => #[t]) ++ nonTuplePool.map (fun v => #[v]) ++
    #[#[iv 9, tup #[iv 1, iv 2]], #[]]

/-- A tuple and a value on top of it. -/
private def tupleAndValue : Array (Array Value) :=
  tuplePool.map (fun t => #[t, iv 42]) ++
    #[#[tup #[iv 1], .null], #[tup #[iv 1], tup #[iv 2]], #[iv 1, iv 2], #[.null, iv 3],
      #[tup #[iv 1]], #[], #[tup ((Array.range 255).map (fun i => iv (Int.ofNat i))), iv 1]]

private def idxs : Array Int := #[0, 1, 2, 3, 15, -1, 255, 256]

/-- A tuple and an integer index or count on top. -/
private def tupleAndInt : Array (Array Value) :=
  (tuplePool.flatMap (fun t => idxs.map (fun k => #[t, iv k]))) ++
    #[#[iv 1, iv 0], #[tup #[iv 1], .null], #[tup #[iv 1]], #[]]

/-- A tuple, a value and an integer index on top. -/
private def tupleValueInt : Array (Array Value) :=
  (tuplePool.flatMap (fun t => idxs.map (fun k => #[t, iv 42, iv k]))) ++
    #[#[iv 1, iv 2, iv 0], #[tup #[iv 1], iv 2, .null], #[tup #[iv 1], iv 2], #[]]

/-- `n` integers 0..n-1. -/
private def ints (n : Nat) : Array Value := (Array.range n).map (fun i => iv (10 + Int.ofNat i))

/-- Stacks for TUPLEVAR: values then the count. -/
private def valuesAndCount : Array (Array Value) :=
  #[ #[iv 0], ints 1 ++ #[iv 1], ints 3 ++ #[iv 3], ints 2 ++ #[iv 3], ints 15 ++ #[iv 15],
     ints 16 ++ #[iv 16], #[iv (-1)], #[iv 256], ints 3 ++ #[iv 255], #[.null], #[] ]

/-- Stacks for the null instructions. -/
private def nullStacks : Array (Array Value) :=
  #[ #[], #[iv 0], #[iv 1], #[iv (-1)], #[.null], #[tup #[]], #[.cell Cell.empty],
     #[iv 5, iv 0], #[iv 5, iv 1], #[iv 5, iv 6, iv 0], #[iv 5, iv 6, iv 1], #[.null, iv 7] ]

private def small : Array Nat := #[0, 1, 2, 3, 4, 15]

/-- Oracle cases of the suite named `suite`. -/
def casesFor (suite : String) : Array OracleCase :=
  let op (o : TupleInstr) : Instr := .tupleOp o
  match suite with
  | "INDEX" => cross suite (#[0, 1, 2, 3, 14, 15].map (fun k => (s!"k{k}", op (.index k)))) oneTuple
  | "INDEXQ" => cross suite (#[0, 1, 2, 3, 14, 15].map (fun k => (s!"k{k}", op (.indexQ k)))) oneTuple
  | "INDEX2" => cross suite (#[(0, 0), (0, 1), (1, 0), (1, 1), (2, 3), (3, 3)].map
      (fun (i, j) => (s!"i{i}j{j}", op (.index2 i j)))) oneTuple
  | "INDEX3" => cross suite (#[(0, 0, 0), (1, 1, 0), (1, 1, 1), (0, 1, 1), (3, 3, 3)].map
      (fun (i, j, k) => (s!"i{i}j{j}k{k}", op (.index3 i j k)))) oneTuple
  | "UNTUPLE" => cross suite (small.map (fun n => (s!"n{n}", op (.untuple n)))) oneTuple
  | "UNPACKFIRST" => cross suite (small.map (fun n => (s!"n{n}", op (.unpackFirst n)))) oneTuple
  | "EXPLODE" => cross suite (small.map (fun n => (s!"n{n}", op (.explode n)))) oneTuple
  | "TLEN" => cross suite #[("tlen", op .tlen)] oneTuple
  | "QTLEN" => cross suite #[("qtlen", op .qtlen)] oneTuple
  | "ISTUPLE" => cross suite #[("istuple", op .isTuple)] oneTuple
  | "LAST" => cross suite #[("last", op .last)] oneTuple
  | "TPOP" => cross suite #[("tpop", op .tpop)] oneTuple
  | "SETINDEX" => cross suite (#[0, 1, 2, 3, 15].map (fun k => (s!"k{k}", op (.setIndex k)))) tupleAndValue
  | "SETINDEXQ" => cross suite (#[0, 1, 2, 3, 15].map (fun k => (s!"k{k}", op (.setIndexQ k)))) tupleAndValue
  | "TPUSH" => cross suite #[("tpush", op .tpush)] tupleAndValue
  | "INDEXVAR" => cross suite #[("indexvar", op .indexVar)] tupleAndInt
  | "INDEXVARQ" => cross suite #[("indexvarq", op .indexVarQ)] tupleAndInt
  | "UNTUPLEVAR" => cross suite #[("untuplevar", op .untupleVar)] tupleAndInt
  | "UNPACKFIRSTVAR" => cross suite #[("unpackfirstvar", op .unpackFirstVar)] tupleAndInt
  | "EXPLODEVAR" => cross suite #[("explodevar", op .explodeVar)] tupleAndInt
  | "SETINDEXVAR" => cross suite #[("setindexvar", op .setIndexVar)] tupleValueInt
  | "SETINDEXVARQ" => cross suite #[("setindexvarq", op .setIndexVarQ)] tupleValueInt
  | "TUPLEVAR" => cross suite #[("tuplevar", op .mktupleVar)] valuesAndCount
  | "TUPLE" => cross suite (#[0, 1, 2, 3, 15].map (fun n => (s!"n{n}", op (.mktuple n))))
      (#[0, 1, 2, 3, 4, 14, 15, 16].map ints)
  | "PUSHNULL" => cross suite #[("pushnull", .pushNull)] nullStacks
  | "ISNULL" => cross suite #[("isnull", .isNull)] nullStacks
  | "NULLSWAPIF" => cross suite #[("i", .nullSwapIf)] nullStacks
  | "NULLSWAPIFNOT" => cross suite #[("i", .nullSwapIfNot)] nullStacks
  | "NULLROTRIF" => cross suite #[("i", .nullRotrIf)] nullStacks
  | "NULLROTRIFNOT" => cross suite #[("i", .nullRotrIfNot)] nullStacks
  | "NULLSWAPIF2" => cross suite #[("i", .nullSwapIf2)] nullStacks
  | "NULLSWAPIFNOT2" => cross suite #[("i", .nullSwapIfNot2)] nullStacks
  | "NULLROTRIF2" => cross suite #[("i", .nullRotrIf2)] nullStacks
  | "NULLROTRIFNOT2" => cross suite #[("i", .nullRotrIfNot2)] nullStacks
  | _ => #[]

end Tests.Gen.Tuple
