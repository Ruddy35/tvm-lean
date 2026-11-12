import TvmLean.Proofs.Exec.Spec.FlowRef
import TvmLean.Proofs.Exec.Spec.VarArgs

/-!
# Specifications: the jumps and returns with the rest of the code, `JMPXVARARGS`, `SETNUMVARARGS`

In the format of `Proofs/Exec/Spec/Flow.lean`, while running the code `code` (C++ contops.cpp):

* `JMPXDATA` (C++ `exec_jmpx_data`) on the stack `s k`: the rest of the code pushed
  (`push_code`), then the jump to `k`; `RETDATA` (C++ `exec_ret_data`): the rest of the code pushed,
  then the return;
* `JMPREFDATA` (C++ `exec_do_with_ref` with the jump of `exec_jmpref_data`): the load of the cell
  charged (out of gas at once), the rest of the code pushed, then its code jumped to;
* `JMPXVARARGS` (C++ `exec_jmpx_varargs`) on the stack `s k p`: `p` in `-1..254` (range_chk),
  stk_und if `s` has fewer than `p` values, then the jump to `k` with `p` arguments (`VM.jump`);
* `SETNUMVARARGS` (C++ `exec_setnum_varargs`, `exec_setcontargs_common` with `copy = 0`) on the
  stack `s k more`: `more` in `-1..255` (range_chk); `k` back if `more = -1`, else its closure data
  (`Continuation.forceCdata`) take `more` arguments (`Spec.numArgs`); type_chk for a continuation
  without closure data.
-/

namespace TvmLean.Spec

set_option maxHeartbeats 4000000

/-- `JMPXDATA` on the stack `s k` while running `code`. -/
@[vm_spec] theorem jmpxData (st : VmState) (s : Stack) (k : Continuation) (code : Slice) (saved : Continuation)
    (cregs : OrdCregs) (cdata : OrdCdata) (hcc : st.cc = .ordinary code saved cregs cdata)
    (hs : st.stack = s.push (.cont k)) :
    ExceptT.run (execInstr .jmpxData) st = ExceptT.run (VM.jump k) { st with stack := s.push (.slice code) } := by
  vm_simp [hs, hcc, VM.pushCode]

/-- `RETDATA` while running `code`. -/
@[vm_spec] theorem retData (st : VmState) (code : Slice) (saved : Continuation) (cregs : OrdCregs)
    (cdata : OrdCdata) (hcc : st.cc = .ordinary code saved cregs cdata) :
    ExceptT.run (execInstr .retData) st = ExceptT.run VM.ret { st with stack := st.stack.push (.slice code) } := by
  vm_simp [hcc, VM.pushCode]

/-- `JMPREFDATA` of an ordinary cell while running `code`. -/
@[vm_spec] theorem jmpRefData (st : VmState) (ref : Slice) (hc : ref.cell.special = false) (code : Slice)
    (saved : Continuation) (cregs : OrdCregs) (cdata : OrdCdata) (hcc : st.cc = .ordinary code saved cregs cdata) :
    ExceptT.run (execInstr (.jmpRefData ref)) st =
      if (st.registerCellLoad ref.cell).gasExhaustedNow then
        (.error .outOfGas, st.registerCellLoad ref.cell)
      else
        (.ok (), { st.registerCellLoad ref.cell with
          stack := st.stack.push (.slice code),
          cc := .ordinary (Slice.ofCell ref.cell) (.quit 0) OrdCregs.empty OrdCdata.empty }) := by
  have hcc' : (st.registerCellLoad ref.cell).cc = .ordinary code saved cregs cdata := by
    rw [← hcc]; simp only [VmState.registerCellLoad]; split <;> rfl
  vm_simp [hc, hcc', VM.pushCode]

/-- `JMPXVARARGS` on the stack `s k p`. -/
@[vm_spec] theorem jmpxVarArgs (st : VmState) (s : Stack) (k : Continuation) (p : Int)
    (hs : st.stack = (s.push (.cont k)).push (.int (.num p))) :
    ExceptT.run (execInstr .jmpxVarArgs) st =
      if p < -1 ∨ p > 254 then (.error .rangeChk, { st with stack := s.push (.cont k) })
      else if 0 ≤ p ∧ s.size < p.toNat then (.error .stkUnd, { st with stack := s.push (.cont k) })
      else ExceptT.run (VM.jump k p) { st with stack := s } := by
  by_cases h1 : p < -1 ∨ p > 254
  · vm_simp [hs, h1]
  · by_cases h0 : 0 ≤ p
    · by_cases h2 : s.size < p.toNat
      · have h3 : s.size + 1 < p.toNat + 1 := by omega
        vm_simp [hs, h1, h0, h2, h3]
      · have h3 : ¬ s.size + 1 < p.toNat + 1 := by omega
        vm_simp [hs, h1, h0, h2, h3]
    · vm_simp [hs, h1, h0]

/-- The closure data `SETNUMVARARGS more` gives (`more ≥ 0`, C++ `exec_setcontargs_common`): no more
arguments than it takes already (`0x40000000`, too many, if it takes fewer than `more`), `more` if it
took any number. -/
def numArgs (cdata : OrdCdata) (more : Int) : OrdCdata :=
  if more < cdata.nargs then { cdata with nargs := 0x40000000 }
  else if cdata.nargs < 0 then { cdata with nargs := more } else cdata

/-- `SETNUMVARARGS` on the stack `s k more`. -/
@[vm_spec] theorem setNumVarArgs (st : VmState) (s : Stack) (k : Continuation) (more : Int)
    (hs : st.stack = (s.push (.cont k)).push (.int (.num more))) :
    ExceptT.run (execInstr .setNumVarArgs) st =
      if more < -1 ∨ 255 < more then (.error .rangeChk, { st with stack := s.push (.cont k) })
      else if more = -1 then (.ok (), { st with stack := s.push (.cont k) })
      else match k.forceCdata with
        | .ordinary code saved cregs cdata =>
            (.ok (), { st with stack := s.push (.cont (.ordinary code saved cregs (numArgs cdata more))) })
        | .envelope ext cregs cdata =>
            (.ok (), { st with stack := s.push (.cont (.envelope ext cregs (numArgs cdata more))) })
        | _ => (.error .typeChk, { st with stack := s }) := by
  by_cases h1 : more < -1 ∨ 255 < more
  · vm_simp [hs, h1]
  · by_cases h2 : more = -1
    · subst h2; vm_simp [hs]
    · -- the handler once, then the cases of the continuation on both sides
      vm_simp [hs, h1, h2]
      cases k.forceCdata with
      | ordinary code saved cregs cdata =>
        by_cases hn : more < cdata.nargs <;> by_cases hz : cdata.nargs < 0 <;> vm_simp [numArgs, hn, hz]
      | envelope ext cregs cdata =>
        by_cases hn : more < cdata.nargs <;> by_cases hz : cdata.nargs < 0 <;> vm_simp [numArgs, hn, hz]
      | _ => rfl

end TvmLean.Spec
