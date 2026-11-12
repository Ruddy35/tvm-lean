import TvmLean.Proofs.Exec.Spec.Cell

/-!
# Specifications: standard addresses loaded and stored

In the format of `Proofs/Exec/Spec/Cell.lean` (C++ `exec_load_std_message_addr`,
`exec_load_opt_std_message_addr`, `exec_store_std_address`, `exec_store_opt_std_address`,
tonops.cpp), the address checked as the model checks it (`Slice.skipStdMessageAddr`: `addr_std$10`
without anycast; `isValidStdMsgAddr`: exactly those 267 bits, no references):

* `LDSTDADDR{Q}`: the address as a new slice (`Slice.prefixCell`), then the rest (then -1 if quiet);
  if the slice does not start with one, its error, or (quiet) the slice back and 0;
* `LDOPTSTDADDR{Q}`: `addr_none$00` read as `null`, else as `LDSTDADDR`; cell_und (quiet: the slice
  back and 0) if the slice has fewer than 2 bits;
* `STSTDADDR{Q}`: the address stored (then 0 if quiet); cell_ov, or (quiet) both back and -1, if it
  is not one or the builder has no room;
* `STOPTSTDADDR{Q}`: `null` stored as `00`, a slice as `STSTDADDR`.
-/

namespace TvmLean.Spec

/-- `LDSTDADDR` (`q` false), `LDSTDADDRQ` (`q` true) on the stack `s sl`. -/
@[vm_spec] theorem ldStdAddr (st : VmState) (s : Stack) (sl : Slice) (q : Bool) (hs : st.stack = s.push (.slice sl)) :
    ExceptT.run (execInstr (.tonEnvOp (.ldStdAddr q))) st =
      match sl.skipStdMessageAddr with
      | .ok rest =>
          let s1 := (s.push (.slice (Slice.ofCell (Slice.prefixCell sl rest)))).push (.slice rest)
          (.ok (), { st with stack := if q then s1.push (.int (.num (-1))) else s1 })
      | .error e =>
          if q then (.ok (), { st with stack := (s.push (.slice sl)).push (.int (.num 0)) })
          else (.error e, { st with stack := s }) := by
  cases h : sl.skipStdMessageAddr <;> cases q <;> vm_simp [hs, h]

/-- `LDOPTSTDADDR` (`q` false), `LDOPTSTDADDRQ` (`q` true) on the stack `s sl`. -/
@[vm_spec] theorem ldOptStdAddr (st : VmState) (s : Stack) (sl : Slice) (q : Bool) (hs : st.stack = s.push (.slice sl)) :
    ExceptT.run (execInstr (.tonEnvOp (.ldOptStdAddr q))) st =
      if sl.haveBits 2 then
        if bitsToNat (sl.readBits 2) = 0 then
          let s1 := (s.push .null).push (.slice (sl.advanceBits 2))
          (.ok (), { st with stack := if q then s1.push (.int (.num (-1))) else s1 })
        else
          match sl.skipStdMessageAddr with
          | .ok rest =>
              let s1 := (s.push (.slice (Slice.ofCell (Slice.prefixCell sl rest)))).push (.slice rest)
              (.ok (), { st with stack := if q then s1.push (.int (.num (-1))) else s1 })
          | .error e =>
              if q then (.ok (), { st with stack := (s.push (.slice sl)).push (.int (.num 0)) })
              else (.error e, { st with stack := s })
      else if q then (.ok (), { st with stack := (s.push (.slice sl)).push (.int (.num 0)) })
      else (.error .cellUnd, { st with stack := s }) := by
  by_cases h1 : sl.haveBits 2 = true
  · by_cases h2 : bitsToNat (sl.readBits 2) = 0
    · cases q <;> vm_simp [hs, h1, h2]
    · cases h : sl.skipStdMessageAddr <;> cases q <;> vm_simp [hs, h1, h2, h]
  · cases q <;> vm_simp [hs, h1]

/-- `STSTDADDR` (`q` false), `STSTDADDRQ` (`q` true) on the stack `s sl b`. -/
@[vm_spec] theorem stStdAddr (st : VmState) (s : Stack) (sl : Slice) (b : Builder) (q : Bool)
    (hs : st.stack = (s.push (.slice sl)).push (.builder b)) :
    ExceptT.run (execInstr (.tonEnvOp (.stStdAddr q))) st =
      if isValidStdMsgAddr sl ∧ b.canExtendBy sl.toCellRemaining.bits.size sl.toCellRemaining.refs.size then
        let s1 := s.push (.builder { bits := b.bits ++ sl.toCellRemaining.bits, refs := b.refs ++ sl.toCellRemaining.refs })
        (.ok (), { st with stack := if q then s1.push (.int (.num 0)) else s1 })
      else if q then (.ok (), { st with stack := ((s.push (.slice sl)).push (.builder b)).push (.int (.num (-1))) })
      else (.error .cellOv, { st with stack := s }) := by
  cases h1 : isValidStdMsgAddr sl <;>
    cases h2 : b.canExtendBy sl.toCellRemaining.bits.size sl.toCellRemaining.refs.size <;>
    cases q <;> vm_simp [hs, h1, h2]

/-- `STOPTSTDADDR` (`q` false), `STOPTSTDADDRQ` (`q` true) of `null` on the stack `s null b`. -/
@[vm_spec] theorem stOptStdAddr_null (st : VmState) (s : Stack) (b : Builder) (q : Bool)
    (hs : st.stack = (s.push .null).push (.builder b)) :
    ExceptT.run (execInstr (.tonEnvOp (.stOptStdAddr q))) st =
      if b.canExtendBy 2 then
        let s1 := s.push (.builder (b.storeBits (Array.replicate 2 false)))
        (.ok (), { st with stack := if q then s1.push (.int (.num 0)) else s1 })
      else if q then (.ok (), { st with stack := ((s.push .null).push (.builder b)).push (.int (.num (-1))) })
      else (.error .cellOv, { st with stack := s }) := by
  cases h1 : b.canExtendBy 2 <;> cases q <;> vm_simp [hs, h1]

/-- `STOPTSTDADDR{Q}` of a slice on the stack `s sl b`: as `STSTDADDR{Q}`. -/
@[vm_spec] theorem stOptStdAddr_slice (st : VmState) (s : Stack) (sl : Slice) (b : Builder) (q : Bool)
    (hs : st.stack = (s.push (.slice sl)).push (.builder b)) :
    ExceptT.run (execInstr (.tonEnvOp (.stOptStdAddr q))) st =
      if isValidStdMsgAddr sl ∧ b.canExtendBy sl.toCellRemaining.bits.size sl.toCellRemaining.refs.size then
        let s1 := s.push (.builder { bits := b.bits ++ sl.toCellRemaining.bits, refs := b.refs ++ sl.toCellRemaining.refs })
        (.ok (), { st with stack := if q then s1.push (.int (.num 0)) else s1 })
      else if q then (.ok (), { st with stack := ((s.push (.slice sl)).push (.builder b)).push (.int (.num (-1))) })
      else (.error .cellOv, { st with stack := s }) := by
  cases h1 : isValidStdMsgAddr sl <;>
    cases h2 : b.canExtendBy sl.toCellRemaining.bits.size sl.toCellRemaining.refs.size <;>
    cases q <;> vm_simp [hs, h1, h2]

end TvmLean.Spec
