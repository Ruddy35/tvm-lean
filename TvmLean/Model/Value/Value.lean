import TvmLean.Model.Cont.Continuation

namespace TvmLean

instance : Inhabited Value := ⟨.null⟩

def Value.pretty : Value → String
  | .int .nan => "NaN"
  | .int (.num n) => toString n
  | .null => "null"
  | .nullCell => "<cell:none>"
  | .cell _ => "<cell>"
  | .slice _ => "<slice>"
  | .builder _ => "<builder>"
  | .tuple t => s!"<tuple:{t.size}>"
  | .cont k =>
      match k with
      | .ordinary _ _ _ _ => "<cont:ord>"
      | .envelope _ _ _ => "<cont:env>"
      | .quit n => s!"<cont:quit {n}>"
      | .excQuit => "<cont:excquit>"
      | .whileCond _ _ _ => "<cont:while-cond>"
      | .whileBody _ _ _ => "<cont:while-body>"
      | .untilBody _ _ => "<cont:until-body>"
      | .repeatBody _ _ _ => "<cont:repeat-body>"
      | .againBody _ => "<cont:again-body>"
      | .pushInt n _ => s!"<cont:pushint {n}>"

instance : ToString Value := ⟨Value.pretty⟩

def arrayBeqBy {α : Type} (a b : Array α) (beq : α → α → Bool) : Bool :=
  if a.size != b.size then
    false
  else
    Id.run do
      let mut ok := true
      for i in [0:a.size] do
        match a[i]?, b[i]? with
        | some x, some y =>
            if !(beq x y) then
              ok := false
        | _, _ =>
            ok := false
      return ok

def arrayBeq {α : Type} [BEq α] (a b : Array α) : Bool :=
  arrayBeqBy a b (fun x y => x == y)

-- Total version. The tuple case is `arrayBeqBy x y Value.beq` with the loop inlined so that
-- each element comes with a proof `i < x.size` (needed for termination); since `i < x.size`,
-- `x[i]?` is always `some`, so the result is the same as before.
def Value.beq : Value → Value → Bool
  | .null, .null => true
  | .nullCell, .nullCell => true
  | .int x, .int y => x == y
  | .cell x, .cell y => x == y
  | .slice x, .slice y => x == y
  | .builder x, .builder y => x == y
  | .tuple x, .tuple y =>
      if x.size != y.size then
        false
      else
        Id.run do
          let mut ok := true
          for h : i in [0:x.size] do
            match y[i]? with
            | some yi =>
                if !(Value.beq x[i] yi) then
                  ok := false
            | none =>
                ok := false
          return ok
  | .cont x, .cont y => x == y
  | _, _ => false
termination_by a _ => sizeOf a
decreasing_by
  all_goals
    have hi : i < x.size := h.upper
    have h1 : sizeOf x[i] < sizeOf x := Array.sizeOf_getElem x i hi
    simp_wf
    omega

instance : BEq Value := ⟨Value.beq⟩

end TvmLean
