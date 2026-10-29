import TvmLean.Proofs.Exec.Spec.Loop

/-!
# Specifications: `AGAINBRK`

In the format of `Proofs/Exec/Spec/Loop.lean`: `AGAINBRK` (C++ `exec_again` with `brk`,
contops.cpp:546), `AGAIN` (`Spec.again`) after the continuation after the loop is made `c1`
(`extract_cc(3)`: the rest of the code, saving `c0` and `c1`), so that `RETALT` in the body leaves
the loop.
-/

namespace TvmLean

/-- `VM.extractCc 3` (C++ `extract_cc(3)`) of a running ordinary continuation: the rest of the
code, saving `c0` and `c1`, which become `quit 0` and `quit 1`. -/
@[vm_run] theorem VM.run_extractCc_3 (st : VmState) :
    ExceptT.run (VM.extractCc 3) st =
      match st.cc with
      | .ordinary code _ _ _ =>
          (.ok (.ordinary code (.quit 0) { OrdCregs.empty with c0 := some st.regs.c0, c1 := some st.regs.c1 }
            OrdCdata.empty), { st with regs := { st.regs with c0 := .quit 0, c1 := .quit 1 } })
      | _ => (.error .typeChk, st) := by
  unfold VM.extractCc
  rcases st with ⟨stack, regs, cc, _⟩
  cases cc <;> simp [VM.run_bind, VM.run_get, VM.bindRes_ok, VM.run_throw] <;> rfl

namespace Spec

/-- `AGAINBRK` (C++ `exec_again` with `brk`, contops.cpp:546-552, opcode `E31A`) on the stack
`s body` while running `code`: `c1` becomes the rest of the code saving `c0` and `c1`
(`extract_cc(3)`, `c0` then `quit 0`), then `body` runs forever (`againBody`), as `AGAIN`. -/
@[vm_spec] theorem againBrk (st : VmState) (s : Stack) (body : Continuation) (code : Slice) (saved : Continuation)
    (cregs : OrdCregs) (cdata : OrdCdata) (hcc : st.cc = .ordinary code saved cregs cdata)
    (hs : st.stack = s.push (.cont body)) :
    ExceptT.run (execInstr (.contExt (.again true))) st =
      (.ok (), { st with
        stack := s, cc := .againBody body,
        regs := { st.regs with
          c0 := .quit 0,
          c1 := .ordinary code (.quit 0) { OrdCregs.empty with c0 := some st.regs.c0, c1 := some st.regs.c1 }
            OrdCdata.empty } }) := by
  vm_simp [hs, hcc]

end Spec

end TvmLean
