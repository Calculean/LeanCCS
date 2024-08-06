@[ext]
structure State where
  val : String
deriving BEq

theorem State.beq_iff {s t : State} : (s == t) ↔ s.val = t.val := by
  rw [show s == t ↔ s.val == t.val from Iff.rfl, beq_iff_eq]

instance : LawfulBEq State where
  rfl := by simp [State.beq_iff]
  eq_of_beq h := State.ext _ _ (State.beq_iff.1 h)

@[ext]
structure Action where
  val : String
deriving BEq

theorem Action.beq_iff {a b : Action} : (a == b) ↔ a.val = b.val := by
  rw [show a == b ↔ a.val == b.val from Iff.rfl, beq_iff_eq]

instance : LawfulBEq Action where
  rfl := by simp [Action.beq_iff]
  eq_of_beq h := Action.ext _ _ (Action.beq_iff.1 h)

structure LTS where
  states : List State
  actions : List Action
  transition : { s : State // s ∈ states } → { a : Action // a ∈ actions } → List { s : State // s ∈ states }
  s0 : { s : State // s ∈ states }

def map_lts_statesList (lts : LTS) : List { s : State // s ∈ lts.states } :=
  lts.states.filterMap fun s ↦ if h : s ∈ lts.states then some ⟨s, h⟩ else none

def map_lts_actionsList (lts : LTS) : List { a : Action // a ∈ lts.actions } :=
  lts.actions.filterMap fun a ↦ if h : a ∈ lts.actions then some ⟨a, h⟩ else none

-- Main theorem
theorem reach_iff_pre_star {lts : LTS}
  (s : { s : State // s ∈ lts.states })
  (s' : { s : State // s ∈ lts.states }) :
  s'.val ∈ reach [s] ↔ s.val ∈ pre_star [s'] := by
  sorry
