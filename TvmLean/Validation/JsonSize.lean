import Lean.Data.Json.Basic
import Std.Data.DTreeMap.Internal.WF.Lemmas

/-!
Termination of recursion over JSON values: a value of an object, looked up by its key
(`Json.getObjVal?`) or taken from the object's list of entries (`TreeMap.Raw.toList`), is smaller
(`sizeOf`) than the object.
-/

namespace TvmLean.JsonSize

open Lean Std.DTreeMap.Internal

theorem sizeOf_get?_lt {_ : Ord String} {t : Impl String (fun _ => Json)} {k : String} {v : Json}
    (h : Impl.Const.get? t k = some v) : sizeOf v < sizeOf t := by
  induction t with
  | leaf => simp [Impl.Const.get?] at h
  | inner sz k' v' l r ihl ihr =>
    simp only [Impl.Const.get?] at h
    split at h
    · have := ihl h; simp; omega
    · have := ihr h; simp; omega
    · cases h; simp; omega

theorem sizeOf_lt_of_mem_toListModel {t : Impl String (fun _ => Json)} {e : (_ : String) × Json}
    (h : e ∈ t.toListModel) : sizeOf e.2 < sizeOf t := by
  induction t with
  | leaf => simp at h
  | inner sz k v l r ihl ihr =>
    simp only [Impl.toListModel, List.mem_append, List.mem_cons] at h
    rcases h with h | h | h
    · have := ihl h; simp; omega
    · subst h; simp; omega
    · have := ihr h; simp; omega

/-- The value of a key of an object is smaller than the object. -/
theorem sizeOf_getObjVal?_lt {j v : Json} {k : String} (h : j.getObjVal? k = .ok v) :
    sizeOf v < sizeOf j := by
  cases j with
  | obj kvs =>
    rcases kvs with ⟨⟨t⟩⟩
    simp only [Json.getObjVal?, Std.TreeMap.Raw.get?, Std.DTreeMap.Raw.Const.get?] at h
    split at h
    · rename_i v' hv'
      cases h
      have := sizeOf_get?_lt hv'
      simp; omega
    · cases h
  | _ => simp [Json.getObjVal?] at h <;> cases h

/-- A value in the list of entries of an object is smaller than the object. -/
theorem sizeOf_lt_of_mem_toList {kvs : Std.TreeMap.Raw String Json compare} {k : String} {v : Json}
    (h : (k, v) ∈ kvs.toList) : sizeOf v < sizeOf (Json.obj kvs) := by
  rcases kvs with ⟨⟨t⟩⟩
  simp only [Std.TreeMap.Raw.toList, Std.DTreeMap.Raw.Const.toList,
    Impl.Const.toList_eq_toListModel_map, List.mem_map] at h
  obtain ⟨e, he, heq⟩ := h
  have := sizeOf_lt_of_mem_toListModel he
  cases heq
  simp; omega

end TvmLean.JsonSize
