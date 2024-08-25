import Batteries.Data.List.Perm

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

/-- Labelled transition systems definition as defined in Lecture A1 -/
structure LTS where
  states : List State
  actions : List Action
  transition : { s : State // s ∈ states } → { a : Action // a ∈ actions } → List { s : State // s ∈ states }
  s0 : { s : State // s ∈ states }

/-- BEq instance for subtypes -/
instance instBEqSubtype {α : Type _} [BEq α] (P : α → Prop) : BEq (Subtype P) where
  beq a b := a.val == b.val

/-- BEq instance for states in LTS -/
instance {lts : LTS} : BEq { s : State // s ∈ lts.states } := instBEqSubtype _

/-- Define an example LTS with 3 states and 3 actions-/
def exampleLTS : LTS where
  states := [
    { val := "S1" },
    { val := "S2" },
    { val := "S3" }
  ]
  actions := [
    { val := "a" },
    { val := "b" },
    { val := "c" }
  ]

  transition := fun s a =>
    match s.val.val, a.val.val with
    | "S1", "a" => [⟨{ val := "S2" }, by simp⟩]
    | "S1", "b" => [⟨{ val := "S3" }, by simp ⟩]
    | "S2", "b" => [⟨{ val := "S1" }, by simp⟩, ⟨{ val := "S3" }, by simp⟩]
    | "S2", "c" => [⟨{ val := "S3" }, by simp⟩]
    | "S3", "a" => [⟨{ val := "S1" }, by simp ⟩]
    | "S3", "c" => [⟨{ val := "S2" }, by simp⟩]
    | _, _ => []
  s0 := ⟨{ val := "S1" }, by simp⟩



/-- Proof that S1 is in the states list -/
theorem s1_in_states :
  { val := "S1" } ∈ exampleLTS.states := by simp [exampleLTS]

/-- Proof that S2 is in the states list -/
theorem s2_in_states :
  { val := "S2" } ∈ exampleLTS.states := by simp [exampleLTS]

/-- Proof that a is in the actions list -/
theorem a_in_actions :
  { val := "a" } ∈ exampleLTS.actions := by simp [exampleLTS]

/-- Proof that b is in the actions list -/
theorem b_in_actions :
  { val := "b" } ∈ exampleLTS.actions := by simp [exampleLTS]
