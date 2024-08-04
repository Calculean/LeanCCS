import Batteries.Data.List.Perm

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
