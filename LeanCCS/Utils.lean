import LeanCCS.LabelledTransitionSystem

theorem List.not_mem_of_indexOf?_eq_none [BEq α] [LawfulBEq α] (l : List α) (a : α)
    (ha : l.indexOf? a = none) : a ∉ l := by
  induction l with
  | nil => simp
  | cons b t ih =>
    simp [indexOf?] at ha ⊢
    split at ha
    · simp at ha
    · rw [Option.map_eq_none'] at ha
      refine ⟨Ne.symm ?_, ih ha⟩
      next h =>
      rintro rfl
      exact h LawfulBEq.rfl

def map_lts_actionsList (lts : LTS) : List { a : Action // a ∈ lts.actions } :=
  lts.actions.filterMap fun a ↦ if h : a ∈ lts.actions then some ⟨a, h⟩ else none


def map_lts_statesList (lts : LTS) : List { s : State // s ∈ lts.states } :=
  lts.states.filterMap fun s ↦ if h : s ∈ lts.states then some ⟨s, h⟩ else none
