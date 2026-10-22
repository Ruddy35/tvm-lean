import TvmLean.Proofs.Exec.Tactic
import TvmLean.Proofs.Exec.Spec.DictDel
import TvmLean.Proofs.Exec.Spec.DictSetGet

/-!
# Pilot: dictionary updates on an unknown dictionary

The specifications of `Proofs/Exec/Spec/DictSet.lean` and `Proofs/Exec/Spec/DictDel.lean` used by
`vm_run` on a dictionary given by a variable `D` (well-formed for 8-bit keys, `Dict.WF (some D) 8`).
The well-formedness of the new root, which the lookup after the update needs, is found by the
discharger (`vm_dict_wf`, from the hypothesis that `vm_run` leaves when it splits on the result of
the update).

* `run_set_get`: `DICTUSET; PUSHINT 5; SWAP; PUSHINT 8; DICTUGET` (`DictSetPilot.code_eq`) on the
  stack `[val, 5, D, 8]` ends normally with the stack `[v, -1]`, `v` a value with the contents of
  `val`; or the set fails (with its error), or a new cell is too deep (cell_ov), or the gas runs
  out (`Outcome`).
* `run_range`: the same code with the key `300`, out of the range of 8-bit keys: `DICTUSET`
  raises range_chk (exit code `~~~5`).
* `run_del_get`: `DICTUDEL; DROP; PUSHINT 5; SWAP; PUSHINT 8; DICTUGET` (`codeDel_eq`) on the stack
  `[5, D, 8]` ends normally with the stack `[0]` (the key is gone, whether the dictionary became
  empty or not); or the delete fails, or the gas runs out (`OutcomeDel`).
* `run_setget`: `DICTUSETGET` on `[val, 5, D, 8]` ends normally with `[D', v, -1]`, `v` a value
  with the contents the key had in `D`, or with `[D', 0]` if the key was absent; or the update
  fails, or a new cell is too deep, or the gas runs out (`OutcomeSetGet`).
-/

namespace TvmLean.Pilot.DictSetPilot

/-- The bits of `DICTUSET` (`0xf416`), `PUSHINT 5` (`0x75`), `SWAP` (`0x01`), `PUSHINT 8` (`0x78`)
and `DICTUGET` (`0xf40e`). -/
def bits : BitString :=
  #[true, true, true, true, false, true, false, false, false, false, false, true, false, true, true, false,
    false, true, true, true, false, true, false, true,
    false, false, false, false, false, false, false, true,
    false, true, true, true, true, false, false, false,
    true, true, true, true, false, true, false, false, false, false, false, false, true, true, true, false]

/-- The code `DICTUSET; PUSHINT 5; SWAP; PUSHINT 8; DICTUGET`. -/
def code : Cell := Cell.mkOrdinary bits #[]

/-- It is what the model's assembler makes of the five instructions. -/
theorem code_eq : assembleCp0 [.dictSet true true false .set, .pushInt (.num 5), .xchg0 1, .pushInt (.num 8),
    .dictGet true true false] = .ok code := by decide

/-- The state that runs `code` on the stack `[val, idx, D, 8]` with 1000000 gas, `c0` the end of the
run and `c2` the exception handler of the compute phase; the rest of `st` is anything. -/
def start (st : VmState) (val : Slice) (idx : Int) (D : Cell) : VmState :=
  { st with stack := #[.slice val, .int (.num idx), .cell D, .int (.num 8)],
            cc := .ordinary (Slice.ofCell code) (.quit 0) OrdCregs.empty OrdCdata.empty,
            cp := 0, chainJumps := 0, librariesRefused := #[], librariesMissed := #[], maxLibraryLoads := none,
            regs := { st.regs with c0 := .quit 0, c2 := .excQuit }, gas := ⟨1000000, 1000000, 0, 1000000, 1000000⟩ }

/-- The key `5` of 8 bits. -/
def key5 : BitString := #[false, false, false, false, false, true, false, true]

/-- The ways the run ends: normally with the value read back (its contents those of `val`), or by
the failure of the set, a cell too deep, or the gas. -/
def Outcome (val : Slice) (D : Cell) (r : StepResult) : Prop :=
  (∃ stF v, r = VmState.haltResult (~~~ 0) stF ∧
      stF.stack = (#[].push (.slice v)).push (.int (.num (-1))) ∧ v.toCellRemaining = val.toCellRemaining) ∨
    (∃ e stF, Dict.setSetRes (some D) key5 (DictMap.sliceB val) = .error e ∧
      r = VmState.haltResult (~~~ e.toInt) stF) ∨
    (∃ stF, r = VmState.haltResult (~~~ Excno.cellOv.toInt) stF) ∨
    (∃ stF, r = VmState.haltResult Excno.outOfGas.toInt stF)

/-- The value read back after the set has the contents stored. -/
theorem read_back {D c : Cell} {val v : Slice} {created : Nat} {rest : List Cell} (hwf : Dict.WF (some D) 8)
    (h : Dict.setSetRes (some D) key5 (DictMap.sliceB val) = .ok (c, created, rest))
    (hg : Dict.get (some c) key5 = some v) : v.toCellRemaining = val.toCellRemaining := by
  obtain ⟨v', hv', hc⟩ := Dict.get_setSet (key := key5) hwf h
  rw [hg] at hv'
  cases hv'
  simpa using hc

/-- After the set the key is never absent. -/
theorem not_absent {D c : Cell} {val : Slice} {created : Nat} {rest : List Cell} (hwf : Dict.WF (some D) 8)
    (h : Dict.setSetRes (some D) key5 (DictMap.sliceB val) = .ok (c, created, rest))
    (hg : Dict.get (some c) key5 = none) : False := by
  obtain ⟨v', hv', -⟩ := Dict.get_setSet (key := key5) hwf h
  rw [hg] at hv'
  cases hv'

set_option maxHeartbeats 4000000 in
/-- **Get after set, run by `vm_run`.** -/
theorem run_set_get (fuel : Nat) (st : VmState) (val : Slice) (D : Cell) (hwf : Dict.WF (some D) 8) :
    Outcome val D (VmState.runWith execInstr (fuel + 7) (start st val 5 D)) := by
  unfold start
  vm_run
  all_goals unfold Outcome
  all_goals first
    | (right; right; right; exact ⟨_, rfl⟩)
    | (right; right; left; exact ⟨_, rfl⟩)
    | (right; left; exact ⟨_, _, by assumption, by rfl⟩)
    | (exfalso; exact not_absent hwf (by assumption) (by assumption))
    | (left; exact ⟨_, _, rfl, rfl, read_back hwf (by assumption) (by assumption)⟩)

/-- **A key out of range**: `DICTUSET` of the key `300` in a dictionary of 8-bit keys raises
range_chk. -/
theorem run_range (fuel : Nat) (st : VmState) (val : Slice) (D : Cell) (hwf : Dict.WF (some D) 8) :
    ∃ stF, VmState.runWith execInstr (fuel + 7) (start st val 300 D) = .halt (~~~ 5) stF := by
  unfold start
  vm_run
  all_goals (first | (simp only [VmState.haltResult]; exact ⟨_, rfl⟩) | exact ⟨_, rfl⟩)


/-! ## Get after delete -/

/-- The bits of `DICTUDEL` (`0xf45b`), `DROP` (`0x30`), `PUSHINT 5`, `SWAP`, `PUSHINT 8` and
`DICTUGET`. -/
def bitsDel : BitString :=
  #[true, true, true, true, false, true, false, false, false, true, false, true, true, false, true, true,
    false, false, true, true, false, false, false, false,
    false, true, true, true, false, true, false, true,
    false, false, false, false, false, false, false, true,
    false, true, true, true, true, false, false, false,
    true, true, true, true, false, true, false, false, false, false, false, false, true, true, true, false]

/-- The code `DICTUDEL; DROP; PUSHINT 5; SWAP; PUSHINT 8; DICTUGET`. -/
def codeDel : Cell := Cell.mkOrdinary bitsDel #[]

/-- It is what the model's assembler makes of the six instructions. -/
theorem codeDel_eq : assembleCp0 [.dictExt (.del true true), .pop 0, .pushInt (.num 5), .xchg0 1,
    .pushInt (.num 8), .dictGet true true false] = .ok codeDel := by decide

/-- The state that runs `codeDel` on the stack `[idx, D, 8]`. -/
def startDel (st : VmState) (idx : Int) (D : Cell) : VmState :=
  { st with stack := #[.int (.num idx), .cell D, .int (.num 8)],
            cc := .ordinary (Slice.ofCell codeDel) (.quit 0) OrdCregs.empty OrdCdata.empty,
            cp := 0, chainJumps := 0, librariesRefused := #[], librariesMissed := #[], maxLibraryLoads := none,
            regs := { st.regs with c0 := .quit 0, c2 := .excQuit }, gas := ⟨1000000, 1000000, 0, 1000000, 1000000⟩ }

/-- The ways the run ends: normally with the key not found (`[0]`), or by the failure of the
delete, or the gas. -/
def OutcomeDel (D : Cell) (r : StepResult) : Prop :=
  (∃ stF, r = VmState.haltResult (~~~ 0) stF ∧ stF.stack = #[].push (.int (.num 0))) ∨
    (∃ e l stF, Dict.delRes (some D) key5 = .error (e, l) ∧ r = VmState.haltResult (~~~ e.toInt) stF) ∨
    (∃ stF, r = VmState.haltResult Excno.outOfGas.toInt stF)

/-- After the delete the key is absent. -/
theorem gone {D c : Cell} {found : Bool} {created : Nat} {rest : List Cell} {v : Slice}
    (hwf : Dict.WF (some D) 8) (h : Dict.delRes (some D) key5 = .ok (found, some c, created, rest))
    (hg : Dict.get (some c) key5 = some v) : False := by
  have hv := (Dict.value_delRes (key := key5) hwf h).2 key5 rfl
  rw [if_pos rfl] at hv
  unfold Dict.value at hv
  rw [hg] at hv
  cases hv

set_option maxHeartbeats 4000000 in
/-- **Get after delete, run by `vm_run`.** -/
theorem run_del_get (fuel : Nat) (st : VmState) (D : Cell) (hwf : Dict.WF (some D) 8) :
    OutcomeDel D (VmState.runWith execInstr (fuel + 8) (startDel st 5 D)) := by
  unfold startDel
  vm_run
  all_goals unfold OutcomeDel
  all_goals first
    | (right; right; exact ⟨_, rfl⟩)
    | (right; left; exact ⟨_, _, _, by assumption, by rfl⟩)
    | (exfalso; exact gone hwf (by assumption) (by assumption))
    | (left; exact ⟨_, rfl, rfl⟩)


/-! ## Lookup-and-set -/

/-- The bits of `DICTUSETGET` (`0xf41e`). -/
def bitsSetGet : BitString :=
  #[true, true, true, true, false, true, false, false, false, false, false, true, true, true, true, false]

/-- The code `DICTUSETGET`. -/
def codeSetGet : Cell := Cell.mkOrdinary bitsSetGet #[]

/-- It is what the model's assembler makes of the instruction. -/
theorem codeSetGet_eq : assembleCp0 [.dictExt (.mutGet true true false .set)] = .ok codeSetGet := by decide

/-- The state that runs `codeSetGet` on the stack `[val, idx, D, 8]`. -/
def startSetGet (st : VmState) (val : Slice) (idx : Int) (D : Cell) : VmState :=
  { st with stack := #[.slice val, .int (.num idx), .cell D, .int (.num 8)],
            cc := .ordinary (Slice.ofCell codeSetGet) (.quit 0) OrdCregs.empty OrdCdata.empty,
            cp := 0, chainJumps := 0, librariesRefused := #[], librariesMissed := #[], maxLibraryLoads := none,
            regs := { st.regs with c0 := .quit 0, c2 := .excQuit }, gas := ⟨1000000, 1000000, 0, 1000000, 1000000⟩ }

/-- The ways the run ends: normally with the new root and the old value (its contents those the key
had) and `-1`, or the new root and `0` if the key was absent; or by the failure of the update, a
cell too deep, or the gas. -/
def OutcomeSetGet (val : Slice) (D : Cell) (r : StepResult) : Prop :=
  (∃ stF D' v, r = VmState.haltResult (~~~ 0) stF ∧
      stF.stack = ((#[].push D').push (.slice v)).push (.int (.num (-1))) ∧
      Dict.value (some D) key5 = some v.toCellRemaining) ∨
    (∃ stF D', r = VmState.haltResult (~~~ 0) stF ∧ stF.stack = (#[].push D').push (.int (.num 0)) ∧
      Dict.value (some D) key5 = none) ∨
    (∃ e stF, Dict.setGetRes (some D) key5 (DictMap.sliceB val) .set = .error e ∧
      r = VmState.haltResult (~~~ e.toInt) stF) ∨
    (∃ stF, r = VmState.haltResult (~~~ Excno.cellOv.toInt) stF) ∨
    (∃ stF, r = VmState.haltResult Excno.outOfGas.toInt stF)

/-- The old value is the value the key had. -/
theorem old_value {D : Cell} {val v : Slice} {r : Option Cell} {ok : Bool} {created : Nat}
    {rest : List Cell} (hwf : Dict.WF (some D) 8)
    (h : Dict.setGetRes (some D) key5 (DictMap.sliceB val) .set = .ok (some v, r, ok, created, rest)) :
    Dict.value (some D) key5 = some v.toCellRemaining :=
  ((Dict.value_setGetRes (key := key5) hwf h).1).symm

/-- No old value: the key was absent. -/
theorem old_absent {D : Cell} {val : Slice} {r : Option Cell} {ok : Bool} {created : Nat}
    {rest : List Cell} (hwf : Dict.WF (some D) 8)
    (h : Dict.setGetRes (some D) key5 (DictMap.sliceB val) .set = .ok (none, r, ok, created, rest)) :
    Dict.value (some D) key5 = none :=
  ((Dict.value_setGetRes (key := key5) hwf h).1).symm

set_option maxHeartbeats 4000000 in
/-- **Lookup-and-set, run by `vm_run`.** -/
theorem run_setget (fuel : Nat) (st : VmState) (val : Slice) (D : Cell) (hwf : Dict.WF (some D) 8) :
    OutcomeSetGet val D (VmState.runWith execInstr (fuel + 3) (startSetGet st val 5 D)) := by
  unfold startSetGet
  vm_run
  all_goals unfold OutcomeSetGet
  all_goals first
    | (right; right; right; right; exact ⟨_, rfl⟩)
    | (right; right; right; left; exact ⟨_, rfl⟩)
    | (right; right; left; exact ⟨_, _, by assumption, by rfl⟩)
    | (left; exact ⟨_, _, _, rfl, rfl, old_value hwf (by assumption)⟩)
    | (right; left; exact ⟨_, _, rfl, rfl, old_absent hwf (by assumption)⟩)

end TvmLean.Pilot.DictSetPilot
