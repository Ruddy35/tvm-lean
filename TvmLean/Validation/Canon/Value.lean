import TvmLean.Model

namespace TvmLean

def bytesHex (bs : Array UInt8) : String :=
  let hexDigit (n : Nat) : Char :=
    if n < 10 then
      Char.ofNat ('0'.toNat + n)
    else
      Char.ofNat ('a'.toNat + (n - 10))
  let byteHex (b : UInt8) : String :=
    let n := b.toNat
    String.singleton (hexDigit (n / 16)) ++ String.singleton (hexDigit (n % 16))
  String.intercalate "" (bs.toList.map byteHex)

def canonContTy : Continuation → String
  | .ordinary .. => "vmc_std"
  | .envelope .. => "vmc_envelope"
  | .quit _ => "vmc_quit"
  | .excQuit => "vmc_quit_exc"
  | .whileCond .. => "vmc_while_cond"
  | .whileBody .. => "vmc_while_body"
  | .untilBody .. => "vmc_until"
  | .repeatBody .. => "vmc_repeat"
  | .againBody .. => "vmc_again"
  | .pushInt .. => "vmc_pushint"

def canonValue (v : Value) : String :=
  match v with
  | .null => "null"
  | .nullCell => "null"
  | .int .nan => "nan"
  | .int (.num n) => s!"int:{n}"
  | .cell c => s!"cell:{bytesHex (Cell.hashBytes c)}"
  | .slice s => s!"slice:{bytesHex (Cell.hashBytes s.toCellRemaining)}"
  | .builder b => s!"builder:{bytesHex (Cell.hashBytes b.finalize)}"
  | .tuple t =>
      let inner := String.intercalate "," (t.attach.toList.map fun ⟨x, _⟩ => canonValue x)
      "tuple[" ++ toString t.size ++ "]{" ++ inner ++ "}"
  | .cont k => "cont:Cont{" ++ canonContTy k ++ "}"
termination_by sizeOf v
decreasing_by
  have h1 := Array.sizeOf_lt_of_mem ‹x ∈ t›
  simp_wf
  omega

def valueEqNormalized : Value → Value → Bool
  | .null, .null => true
  | .nullCell, .nullCell => true
  | .int x, .int y => x == y
  | .cell x, .cell y => x == y
  | .builder x, .builder y => x == y
  | .cont x, .cont y => x == y
  | .slice x, .slice y => x.toCellRemaining == y.toCellRemaining
  | .tuple x, .tuple y =>
      if x.size != y.size then
        false
      else
        Id.run do
          let mut ok := true
          for h : i in [0:x.size] do
            if ok then
              ok := valueEqNormalized x[i] y[i]!
          return ok
  | _, _ => false
termination_by a _ => sizeOf a
decreasing_by
  have h1 : sizeOf x[i] < sizeOf x := Array.sizeOf_getElem x i h.upper
  simp_wf
  omega

def firstValueMismatch (expected actual : Value) : Option (List Nat × Value × Value) :=
  if valueEqNormalized expected actual then
    none
  else
    match expected, actual with
    | .tuple e, .tuple a =>
        if e.size != a.size then
          some ([], expected, actual)
        else
          Id.run do
            for h : i in [0:e.size] do
              let ev := e[i]
              let av := a[i]!
              if !valueEqNormalized ev av then
                match firstValueMismatch ev av with
                | some (path, leafE, leafA) => return some (i :: path, leafE, leafA)
                | none => return some ([i], ev, av)
            return some ([], expected, actual)
    | _, _ =>
        some ([], expected, actual)
termination_by sizeOf expected
decreasing_by
  have h1 : sizeOf e[i] < sizeOf e := Array.sizeOf_getElem e i h.upper
  simp_wf
  omega


end TvmLean
