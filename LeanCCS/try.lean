import Batteries.Data.List.Perm

open List

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
  transition : { s : State // s ∈ states } → { a : Action // a ∈ actions } → List { s : State // s ∈ states }
  s0 : { s : State // s ∈ states }

def post {lts : LTS} (s : { s : State // s ∈ lts.states }) (a : {a : Action // a ∈ lts.actions }) : List { s : State // s ∈ lts.states } :=
  lts.transition s a

-- Define the LTS
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


-- Proof that S1 is in the states list
theorem s1_in_states : { val := "S1" } ∈ exampleLTS.states := by simp [exampleLTS]
