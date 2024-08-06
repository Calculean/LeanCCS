import LeanCCS.pre
import LeanCCS.Post


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
theorem s1_in_states :
  { val := "S1" } ∈ exampleLTS.states := by simp [exampleLTS]

-- Proof that S2 is in the states list
theorem s2_in_states :
  { val := "S2" } ∈ exampleLTS.states := by simp [exampleLTS]

-- Proof that S1 is in the states list
theorem a_in_actions :
  { val := "a" } ∈ exampleLTS.actions := by simp [exampleLTS]
theorem b_in_actions :
  { val := "b" } ∈ exampleLTS.actions := by simp [exampleLTS]

-- Example usage of the post function
#eval (post exampleLTS.s0 ⟨{ val := "a" }, a_in_actions⟩).map (fun s => s.val.val)

#eval (post ⟨{ val := "S2" }, s2_in_states⟩ ⟨{ val := "b" }, b_in_actions⟩).map (fun s => s.val.val)

theorem c_in_actions :
  { val := "c" } ∈ exampleLTS.actions := by simp [exampleLTS]


#eval "Initial state: S1"
#eval "Actions sequence: a, b, c"

def initial_states : List { s : State // s ∈ exampleLTS.states } := [⟨{ val := "S1" }, s1_in_states⟩]
def actions : List { a : Action // a ∈ exampleLTS.actions } := [
  ⟨{ val := "a" }, a_in_actions⟩,
  ⟨{ val := "b" }, b_in_actions⟩,
  ⟨{ val := "c" }, c_in_actions⟩
]


#eval (post_S_n initial_states actions 0).map (fun s => s.val.val)
#eval (post_S_n initial_states actions 1).map (fun s => s.val.val)
#eval (post_S_n initial_states actions 2).map (fun s => s.val.val)


-- Define the Match Lifecycle LTS
def matchLTS : LTS where
  states := [
    { val := "UNUSED" },
    { val := "BURNING" },
    { val := "EXTINCT" }
  ]
  actions := [
    { val := "strike" },
    { val := "extinguish" }
  ]
  transition := fun s a =>
    match s.val.val, a.val.val with
    | "UNUSED", "strike" => [⟨{ val := "BURNING" }, by simp⟩]
    | "BURNING", "extinguish" => [⟨{ val := "EXTINCT" }, by simp⟩]
    | _, _ => []
  s0 := ⟨{ val := "UNUSED" }, by simp⟩

-- Proofs for states and actions
theorem unused_in_states : { val := "UNUSED" } ∈ matchLTS.states := by simp [matchLTS]
theorem burning_in_states : { val := "BURNING" } ∈ matchLTS.states := by simp [matchLTS]
theorem extinct_in_states : { val := "EXTINCT" } ∈ matchLTS.states := by simp [matchLTS]
theorem strike_in_actions : { val := "strike" } ∈ matchLTS.actions := by simp [matchLTS]
theorem extinguish_in_actions : { val := "extinguish" } ∈ matchLTS.actions := by simp [matchLTS]


def match_initial_states : List { s : State // s ∈ matchLTS.states } := [⟨{ val := "UNUSED" }, unused_in_states⟩]
def match_actions : List { a : Action // a ∈ matchLTS.actions } := [
  ⟨{ val := "strike" }, strike_in_actions⟩,
  ⟨{ val := "extinguish" }, extinguish_in_actions⟩
]

#eval (post_S_n match_initial_states match_actions 2).map (fun s => s.val.val)

-- Set up initial states for exampleLTS
def example_initial_states : List { s : State // s ∈ exampleLTS.states } := [
  ⟨{ val := "S1" }, s1_in_states⟩
]

-- Evaluation for reach
#eval "Reachable states from S1:"
#eval (reach example_initial_states).map (fun s => s.val)

-- Set up target states for pre_star
def example_target_states : List { s : State // s ∈ exampleLTS.states } := [
  ⟨{ val := "S3" }, by simp [exampleLTS]⟩
]

-- Evaluation for pre_star
#eval "States that can reach S3:"
#eval (pre_star example_target_states).map (fun s => s.val)

-- Additional evaluations
#eval "Reachable states from S2:"
#eval (reach [⟨{ val := "S2" }, s2_in_states⟩]).map (fun s => s.val)

#eval "States that can reach S2:"
#eval (pre_star [⟨{ val := "S2" }, s2_in_states⟩]).map (fun s => s.val)
