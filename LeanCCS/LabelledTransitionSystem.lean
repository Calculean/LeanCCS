@[ext]
structure State where
  val : String
deriving BEq

theorem State.beq_iff {s t : State} : (s == t) ↔ s.val = t.val := by
  rw [show s == t ↔ s.val == t.val from Iff.rfl, beq_iff_eq]

instance : LawfulBEq State where
  rfl := by simp [State.beq_iff]
  eq_of_beq h := State.ext _ _ (State.beq_iff.1 h)

structure Action where
  val : String

structure LTS where
  states : List State
  actions : List Action
  transition : State → Action → List { s : State // s ∈ states }
  s0 : State

def map_lts_statesList (lts : LTS) : List { s : State // s ∈ lts.states } :=
  lts.states.filterMap fun s ↦ if h : s ∈ lts.states then some ⟨s, h⟩ else none
