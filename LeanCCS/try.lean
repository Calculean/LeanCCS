import Batteries.Data.List.Perm
import Mathlib.Tactic.NthRewrite

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

def post_S {lts : LTS} (states : List { s : State // s ∈ lts.states }) (a : { a : Action // a ∈ lts.actions }) : List { s : State // s ∈ lts.states } :=
  states.foldl (fun acc state => acc ++ post state a) []

def post_A {lts : LTS} (s : { s : State // s ∈ lts.states }) (actions : List { a : Action // a ∈ lts.actions }) : List { s : State // s ∈ lts.states } :=
  actions.foldl (fun acc act => acc ++ post s act) []

def post_S_A {lts : LTS} (states : List { s : State // s ∈ lts.states }) (actions : List { a : Action // a ∈ lts.actions }) : List { s : State // s ∈ lts.states } :=
  actions.foldl (fun acc act => acc ++ post_S states act) []

def post_S_n {lts : LTS} (states : List { s : State // s ∈ lts.states }) (actions : List { a : Action // a ∈ lts.actions }) (n : Nat) : List { s : State // s ∈ lts.states } :=
  match n with
  | 0 => states
  | n' + 1 => post_S_A (post_S_n states actions n') actions

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

def reach_aux (lts : LTS) (visited : { l : List State // l <+~ lts.states } )
(to_visit : List { s : State // s ∈ lts.states }) (acc : List State): List State :=
  match to_visit with
  | [] => acc
  | s::ss =>
    if h : visited.1.indexOf? s.1 != none then
      reach_aux lts visited ss acc
    else
      have hx : (s.1 :: visited.1) <+~ lts.states := by
        refine List.cons_subperm_of_not_mem_of_mem ?_ s.2 visited.2
        rw [Bool.not_eq_true, bne_eq_false_iff_eq] at h
        exact List.not_mem_of_indexOf?_eq_none _ _ h
      have : lts.states.length - (visited.1.length + 1) < lts.states.length - visited.1.length := by
        refine Nat.sub_add_lt_sub ?_ Nat.zero_lt_one
        simpa using hx.length_le
      let actions_with_proof := map_lts_actionsList lts
      reach_aux lts ⟨s::visited, hx⟩ (post_A s actions_with_proof ++ ss) ((post_A s actions_with_proof).map Subtype.val ++ acc)
termination_by (lts.states.length - visited.1.length, to_visit.length)

def reach {lts : LTS} (initial_states : List { s : State // s ∈ lts.states }) : List State :=
  reach_aux lts ⟨[], nil_subperm⟩ initial_states []

theorem post_S_n_succ_eq_post_S_n_post_S_n {lts : LTS}
  (states : List { s : State // s ∈ lts.states })
  (actions : List { a : Action // a ∈ lts.actions })
  (n : Nat) :
  post_S_n states actions (n + 1) = post_S_n (post_S_n states actions n) actions 1 := by
  rfl

-- Assuming this function is already defined in your code
def map_lts_statesList (lts : LTS) : List { s : State // s ∈ lts.states } :=
  lts.states.filterMap fun s ↦ if h : s ∈ lts.states then some ⟨s, h⟩ else none

-- BEq instance for subtypes
instance instBEqSubtype {α : Type _} [BEq α] (P : α → Prop) : BEq (Subtype P) where
  beq a b := a.val == b.val

-- BEq instance for states in LTS
instance {lts : LTS} : BEq { s : State // s ∈ lts.states } := instBEqSubtype _

-- Pre function
def pre {lts : LTS} (s : { s : State // s ∈ lts.states }) (a : { a : Action // a ∈ lts.actions }) : List { s : State // s ∈ lts.states } :=
  List.filter (fun st => (lts.transition st a).indexOf? s != none) (map_lts_statesList lts)

-- Pre_A function
def pre_A (lts : LTS) (s : State) (actions : List { a : Action // a ∈ lts.actions }) : List State :=
  let s_subtype : Option { s : State // s ∈ lts.states } :=
    if h : s ∈ lts.states then some ⟨s, h⟩ else none
  match s_subtype with
  | none => []
  | some s' =>
    actions.foldl (fun acc a => acc ++ (pre s' a).map Subtype.val) []

-- Pre_S function
def pre_S (lts : LTS) (states : List State) (a : { a : Action // a ∈ lts.actions }) : List State :=
  states.foldl (fun acc s =>
    let s_subtype : Option { s : State // s ∈ lts.states } :=
      if h : s ∈ lts.states then some ⟨s, h⟩ else none
    match s_subtype with
    | none => acc
    | some s' => acc ++ (pre s' a).map Subtype.val
  ) []

-- Pre_S_A function
def pre_S_A (lts : LTS) (states : List State) (actions : List { a : Action // a ∈ lts.actions }) : List State :=
  actions.foldl (fun acc action => acc ++ pre_S lts states action) []

-- Pre_S_n function
def pre_S_n (lts : LTS) (states : List State) (actions : List { a : Action // a ∈ lts.actions }) (n : Nat) : List State :=
  match n with
  | 0 => states
  | n' + 1 => pre_S_A lts (pre_S_n lts states actions n') actions


def pre_star_aux (lts : LTS) (visited : { l : List State // l <+~ lts.states })
(to_visit : List { s : State // s ∈ lts.states }) (acc : List State) : List State :=
  match to_visit with
  | [] => acc
  | s::ss =>
    if h : visited.1.indexOf? s.1 != none then
      pre_star_aux lts visited ss acc
    else
      have hx : (s.1 :: visited.1) <+~ lts.states := by
        refine List.cons_subperm_of_not_mem_of_mem ?_ s.2 visited.2
        rw [Bool.not_eq_true, bne_eq_false_iff_eq] at h
        exact List.not_mem_of_indexOf?_eq_none _ _ h
      have : lts.states.length - (visited.1.length + 1) < lts.states.length - visited.1.length := by
        refine Nat.sub_add_lt_sub ?_ Nat.zero_lt_one
        simpa using hx.length_le
      let actions_with_proof := map_lts_actionsList lts
      let predecessors := actions_with_proof.foldl (fun acc a => acc ++ pre s a) []
      pre_star_aux lts ⟨s.1::visited.1, hx⟩ (predecessors ++ ss) (s.1 :: acc)
termination_by (lts.states.length - visited.1.length, to_visit.length)

def pre_star {lts : LTS} (initial_states : List { s : State // s ∈ lts.states }) : List State :=
  pre_star_aux lts ⟨[], nil_subperm⟩ initial_states []


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


-- Main theorem
theorem reach_iff_pre_star {lts : LTS}
  (s : { s : State // s ∈ lts.states })
  (s' : { s : State // s ∈ lts.states }) :
  s'.val ∈ reach [s] ↔ s.val ∈ pre_star [s'] := by
  sorry
