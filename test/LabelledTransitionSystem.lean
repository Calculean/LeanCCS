import LeanCCS.pre
import LeanCCS.post

def states : List State :=
  [State.mk "UNUSED", State.mk "BURNING", State.mk "EXTINCT"]

def actions : List Action :=
  [Action.mk "strike", Action.mk "extinguish"]

def transition (s : State) (a : Action) : List { s : State // s ∈ states } :=
  match (s.val, a.val) with
  | ("UNUSED", "strike") => [⟨State.mk "BURNING", by simp [states]⟩]
  | ("BURNING", "extinguish") => [⟨State.mk "EXTINCT", by simp [states]⟩]
  | _ => []

def lts_example : LTS :=
  LTS.mk
    states
    actions
    transition
    <| State.mk "UNUSED"
