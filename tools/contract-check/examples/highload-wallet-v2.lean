-- Highload wallet v2 (crypto/smartcont/highload-wallet-v2-code.fc): the data is `subwallet:uint32
-- last_cleaned:uint64 public_key:uint256 old_queries:(HashmapE 64 ^Cell)`. An external message
-- signed by the key, with a query id not among the old queries, sends up to 254 messages (one per
-- entry of a dictionary of the message, `idict_get_next?` in a loop), records its query id in the
-- old queries (`udict_set_builder`), then removes the queries more than 64 seconds old
-- (`udict_delete_get_min` in a loop, `last_cleaned` the last removed). Invariant: the key and the
-- subwallet never change, and the old queries are a well-formed dictionary of 64-bit query ids
-- (`Dict.WF`) whose every value is empty (`Dict.value`: what `udict_set_builder` stores of
-- `begin_cell()`). The cleanup loop changes its whole state: its invariant is `Cleanup`.
-- contract-check: invariant Inv key sub
-- contract-check: params (key sub : Nat)
-- contract-check: hints Data.bits, Queries, Queries.set, Queries.delete, Queries.delete_some
-- contract-check: loop 5 Cleanup key sub

/-- The fields of the data before the dictionary. -/
structure Data where
  subwallet : Nat
  lastCleaned : Nat
  publicKey : Nat

/-- `subwallet` in 32 bits, `last_cleaned` in 64, `public_key` in 256. -/
def Data.bits (d : Data) : BitString :=
  natToBits d.subwallet 32 ++ natToBits d.lastCleaned 64 ++ natToBits d.publicKey 256

/-- The old queries: a well-formed dictionary of 64-bit keys whose every value is empty. -/
def Queries (q : Cell) : Prop :=
  Dict.WF (some q) 64 ∧
    ∀ k : BitString, k.size = 64 → ∀ v, Dict.value (some q) k = some v → v = Cell.mkOrdinary #[] #[]

/-- The data: the fields within their widths, the key `key` and the subwallet `sub`, and no old
query (the bit `0`) or a dictionary of them (the bit `1` and the root). -/
def Inv (key sub : Nat) (data : Option Cell) : Prop :=
  ∃ d : Data, d.subwallet < 2 ^ 32 ∧ d.lastCleaned < 2 ^ 64 ∧ d.publicKey < 2 ^ 256 ∧
    d.publicKey = key ∧ d.subwallet = sub ∧
    (data = some (Cell.mkOrdinary (d.bits ++ #[false]) #[]) ∨
      ∃ q : Cell, data = some (Cell.mkOrdinary (d.bits ++ #[true]) #[q]) ∧ Queries q)

/-- The head of the cleanup loop, its stack `last_cleaned public_key subwallet bound old_queries`:
integers, the key and the subwallet, and the old queries (no dictionary, or one of `Queries`). -/
def Cleanup (key sub : Nat) (lc pk sw b q : Value) : Prop :=
  (∃ n : Int, lc = .int (.num n)) ∧ pk = .int (.num key) ∧ sw = .int (.num sub) ∧
    (∃ x : Int, b = .int (.num x)) ∧ (q = .null ∨ ∃ c, q = .cell c ∧ Queries c)

/-- A set of an empty value (`DICTUSETB` of `begin_cell()`) keeps the old queries. -/
theorem Queries.set {root : Option Cell} {key : BitString} {c : Cell} {created : Nat} {rest : List Cell}
    (hq : root = none ∨ ∃ q, root = some q ∧ Queries q) (hk : key.size = 64)
    (h : Dict.setSetRes root key Builder.empty = .ok (c, created, rest)) : Queries c := by
  have hwf : Dict.WF root 64 := by
    rcases hq with rfl | ⟨q, rfl, hq⟩
    · exact Dict.WF.empty 64
    · exact hq.1
  refine ⟨Dict.WF.setSet hwf hk h, fun k hk' v hv => ?_⟩
  rw [Dict.value_setSet (by rw [hk]; exact hwf) h k (by rw [hk, hk'])] at hv
  split at hv
  · cases hv; rfl
  · rcases hq with rfl | ⟨q, rfl, hq⟩
    · cases hv
    · exact hq.2 k hk' v hv

/-- A delete keeps the old queries. -/
theorem Queries.delete {q : Cell} {root' : Option Cell} {key : BitString} {old : Option Slice}
    {created : Nat} {loaded : Array Cell} (hq : Queries q) (hk : key.size = 64)
    (h : dictDeleteWithLoads (some q) key = .ok (old, root', created, loaded)) :
    root' = none ∨ ∃ c, root' = some c ∧ Queries c := by
  have hwf : Dict.WF (some q) key.size := by rw [hk]; exact hq.1
  have hwf' := Dict.WF.delete hwf h
  cases root' with
  | none => exact Or.inl rfl
  | some c =>
    refine Or.inr ⟨c, rfl, by rw [← hk]; exact hwf', fun k hk' v hv => ?_⟩
    rw [(Dict.value_deleteAny hwf h).2 k (by rw [hk, hk'])] at hv
    split at hv
    · cases hv
    · exact hq.2 k hk' v hv

/-- A delete that leaves a dictionary keeps the old queries in it. -/
theorem Queries.delete_some {q c : Cell} {key : BitString} {old : Option Slice} {created : Nat}
    {loaded : Array Cell} (hq : Queries q) (hk : key.size = 64)
    (h : dictDeleteWithLoads (some q) key = .ok (old, some c, created, loaded)) : Queries c := by
  rcases Queries.delete hq hk h with h1 | ⟨c', h1, h2⟩
  · cases h1
  · cases h1
    exact h2
