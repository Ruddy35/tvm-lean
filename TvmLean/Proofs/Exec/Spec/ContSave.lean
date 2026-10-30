import TvmLean.Proofs.Exec.Spec.ContMany

/-!
# Specifications: `BLESS`, `SAMEALTSAVE`, `SAVECTR`, `RETALT`

In the format of `Proofs/Exec/Spec/Stack.lean`:

* `BLESS` (C++ `exec_bless`, contops.cpp): the slice of the stack as an ordinary continuation
  without saved registers or closure data;
* `SAMEALTSAVE` (C++ `exec_samealt`, `save = true`): `c1` saved in `c0` (if `c0` saves none,
  `Continuation.defineC1`), then `c1 := c0`;
* `SAVECTR c<i>` (C++ `exec_save_ctr`): the register `i` saved in `c0` (`Continuation.defineCtr`;
  type_chk if `c0` saves one already, kept from version 14), the result `saveCtrRes`; a
  continuation that is neither ordinary nor an envelope is wrapped in an envelope first
  (`Continuation.defineCtr_quit`, `Continuation.forceCdata`);
* `RETALT` (C++ `exec_ret_alt`): `c1 := quit 1` and a jump to the old `c1`, an ordinary
  continuation or an envelope without closure data, or `quit n`.
-/

namespace TvmLean

/-- The result of `SAVECTR`: `c0` replaced by the continuation that saves the register, or the
exception of `Continuation.defineCtr`, the state unchanged. -/
def saveCtrRes (st : VmState) : Except Excno Continuation → Except Excno Unit × VmState
  | .ok k => (.ok (), { st with regs := { st.regs with c0 := k } })
  | .error e => (.error e, st)

@[vm_run] theorem saveCtrRes_ok (st : VmState) (k : Continuation) :
    saveCtrRes st (.ok k) = (.ok (), { st with regs := { st.regs with c0 := k } }) := rfl

@[vm_run] theorem saveCtrRes_error (st : VmState) (e : Excno) : saveCtrRes st (.error e) = (.error e, st) := rfl

/-- `Continuation.defineCtr` of `quit n`: of its envelope without saved registers
(`Continuation.forceCdata`). -/
@[vm_run] theorem Continuation.defineCtr_quit (n : Int) (idx : Nat) (v : Value) (silent : Bool) :
    (Continuation.quit n).defineCtr idx v silent =
      (Continuation.envelope (.quit n) OrdCregs.empty OrdCdata.empty).defineCtr idx v silent := rfl

namespace Spec

/-- `BLESS` (C++ `exec_bless`) on the stack `s cs`: the ordinary continuation of the code `cs`. -/
@[vm_spec] theorem bless (st : VmState) (s : Stack) (cs : Slice) (hs : st.stack = s.push (.slice cs)) :
    ExceptT.run (execInstr .bless) st =
      (.ok (), { st with stack := s.push (.cont (.ordinary cs (.quit 0) OrdCregs.empty OrdCdata.empty)) }) := by
  vm_simp [hs]

/-- `SAMEALTSAVE` (C++ `exec_samealt`, `save = true`): `c0` saves `c1` (unless it saves one), and
`c1` becomes that `c0`. -/
@[vm_spec] theorem sameAltSave (st : VmState) :
    ExceptT.run (execInstr .sameAltSave) st =
      (.ok (), { st with regs := { st.regs with c0 := st.regs.c0.defineC1 st.regs.c1,
                                                c1 := st.regs.c0.defineC1 st.regs.c1 } }) := by
  vm_simp

/-- `RETALT` (C++ `exec_ret_alt`) when `c1` is an ordinary continuation without closure data:
`c1` becomes `quit 1` and the old `c1` the current continuation. -/
@[vm_spec] theorem retAlt (st : VmState) (code : Slice) (saved : Continuation) (cregs : OrdCregs)
    (hc1 : st.regs.c1 = .ordinary code saved cregs OrdCdata.empty) :
    ExceptT.run (execInstr .retAlt) st =
      (.ok (), { st with regs := { st.regs with c1 := .quit 1 }, cc := .ordinary code saved cregs OrdCdata.empty }) := by
  vm_simp [hc1]

/-- `RETALT` when `c1` is an envelope without closure data. -/
@[vm_spec] theorem retAlt_envelope (st : VmState) (ext : Continuation) (cregs : OrdCregs)
    (hc1 : st.regs.c1 = .envelope ext cregs OrdCdata.empty) :
    ExceptT.run (execInstr .retAlt) st =
      (.ok (), { st with regs := { st.regs with c1 := .quit 1 }, cc := .envelope ext cregs OrdCdata.empty }) := by
  vm_simp [hc1]

/-- `RETALT` when `c1` is `quit n`: the VM goes to `quit n`. -/
@[vm_spec] theorem retAlt_quit (st : VmState) (n : Int) (hc1 : st.regs.c1 = .quit n) :
    ExceptT.run (execInstr .retAlt) st =
      (.ok (), { st with regs := { st.regs with c1 := .quit 1 }, cc := .quit n }) := by
  vm_simp [hc1]

/-! `SAVECTR c<i>` for each register (`c6` is not one: type_chk, the handler's `null`). -/

/-- `SAVECTR c0` (C++ `exec_save_ctr`). -/
@[vm_spec] theorem saveCtr0 (st : VmState) :
    ExceptT.run (execInstr (.saveCtr 0)) st =
      saveCtrRes st (st.regs.c0.defineCtr 0 (.cont st.regs.c0) (decide (14 ≤ st.globalVersion))) := by
  vm_simp [Nat.reduceAnd]
  first
  | (cases st.regs.c0.defineCtr 0 (.cont st.regs.c0) (decide (14 ≤ st.globalVersion)) <;> vm_simp [saveCtrRes])
  | (split <;> rename_i h <;> vm_simp [saveCtrRes, h])

/-- `SAVECTR c1`. -/
@[vm_spec] theorem saveCtr1 (st : VmState) :
    ExceptT.run (execInstr (.saveCtr 1)) st =
      saveCtrRes st (st.regs.c0.defineCtr 1 (.cont st.regs.c1) (decide (14 ≤ st.globalVersion))) := by
  vm_simp [Nat.reduceAnd]
  first
  | (cases st.regs.c0.defineCtr 1 (.cont st.regs.c1) (decide (14 ≤ st.globalVersion)) <;> vm_simp [saveCtrRes])
  | (split <;> rename_i h <;> vm_simp [saveCtrRes, h])

/-- `SAVECTR c2`. -/
@[vm_spec] theorem saveCtr2 (st : VmState) :
    ExceptT.run (execInstr (.saveCtr 2)) st =
      saveCtrRes st (st.regs.c0.defineCtr 2 (.cont st.regs.c2) (decide (14 ≤ st.globalVersion))) := by
  vm_simp [Nat.reduceAnd]
  first
  | (cases st.regs.c0.defineCtr 2 (.cont st.regs.c2) (decide (14 ≤ st.globalVersion)) <;> vm_simp [saveCtrRes])
  | (split <;> rename_i h <;> vm_simp [saveCtrRes, h])

/-- `SAVECTR c3`. -/
@[vm_spec] theorem saveCtr3 (st : VmState) :
    ExceptT.run (execInstr (.saveCtr 3)) st =
      saveCtrRes st (st.regs.c0.defineCtr 3 (.cont st.regs.c3) (decide (14 ≤ st.globalVersion))) := by
  vm_simp [Nat.reduceAnd]
  first
  | (cases st.regs.c0.defineCtr 3 (.cont st.regs.c3) (decide (14 ≤ st.globalVersion)) <;> vm_simp [saveCtrRes])
  | (split <;> rename_i h <;> vm_simp [saveCtrRes, h])

/-- `SAVECTR c4`. -/
@[vm_spec] theorem saveCtr4 (st : VmState) :
    ExceptT.run (execInstr (.saveCtr 4)) st =
      saveCtrRes st (st.regs.c0.defineCtr 4 (.cell st.regs.c4) (decide (14 ≤ st.globalVersion))) := by
  vm_simp [Nat.reduceAnd]
  first
  | (cases st.regs.c0.defineCtr 4 (.cell st.regs.c4) (decide (14 ≤ st.globalVersion)) <;> vm_simp [saveCtrRes])
  | (split <;> rename_i h <;> vm_simp [saveCtrRes, h])

/-- `SAVECTR c5`. -/
@[vm_spec] theorem saveCtr5 (st : VmState) :
    ExceptT.run (execInstr (.saveCtr 5)) st =
      saveCtrRes st (st.regs.c0.defineCtr 5 (.cell st.regs.c5) (decide (14 ≤ st.globalVersion))) := by
  vm_simp [Nat.reduceAnd]
  first
  | (cases st.regs.c0.defineCtr 5 (.cell st.regs.c5) (decide (14 ≤ st.globalVersion)) <;> vm_simp [saveCtrRes])
  | (split <;> rename_i h <;> vm_simp [saveCtrRes, h])

/-- `SAVECTR c7`. -/
@[vm_spec] theorem saveCtr7 (st : VmState) :
    ExceptT.run (execInstr (.saveCtr 7)) st =
      saveCtrRes st (st.regs.c0.defineCtr 7 (.tuple st.regs.c7) (decide (14 ≤ st.globalVersion))) := by
  vm_simp [Nat.reduceAnd]
  first
  | (cases st.regs.c0.defineCtr 7 (.tuple st.regs.c7) (decide (14 ≤ st.globalVersion)) <;> vm_simp [saveCtrRes])
  | (split <;> rename_i h <;> vm_simp [saveCtrRes, h])

end Spec

end TvmLean
