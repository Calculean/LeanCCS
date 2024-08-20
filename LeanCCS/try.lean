import Batteries.Data.List.Perm
import Mathlib.Tactic.NthRewrite
import Lean.Elab.Tactic

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


theorem post_n_plus_one_eq_post_of_post_n {lts : LTS}
  (s : { s : State // s ∈ lts.states })
  (n : Nat) :
  (post_S_n [s] (map_lts_actionsList lts) (n + 1)).map Subtype.val =
  (post_S_A (post_S_n [s] (map_lts_actionsList lts) n) (map_lts_actionsList lts)).map Subtype.val := by
  -- Proof goes here
  rfl



-- Add the new theorem
theorem reach_iff_exists_post_S_n {lts : LTS}
(initial_states : List { s : State // s ∈ lts.states })
(s : State) :
s ∈ reach initial_states →
∃ n : Nat, s ∈ (post_S_n initial_states (map_lts_actionsList lts) n).map Subtype.val := by
intro h_reach
unfold post_S_n

-- The proof goes here
sorry  -- For now, we use sorry as a placeholder for the actual proof

-- Main theorem
theorem reach_iff_pre_star {lts : LTS}
  (s : { s : State // s ∈ lts.states })
  (s' : { s : State // s ∈ lts.states }) :
  s'.val ∈ reach [s] ↔ s.val ∈ pre_star [s'] := by
  sorry



theorem post_n_plus_1_equiv_post_n_post {lts : LTS} (s : { s : State // s ∈ lts.states }) (n : Nat) :
  ∀ s', s' ∈ (post_S_n [s] (map_lts_actionsList lts) (n + 1)).map Subtype.val ↔
    ∃ s'', s'' ∈ (post_S_n [s] (map_lts_actionsList lts) n).map Subtype.val ∧
           s' ∈ (post_S_A [⟨s'', by sorry⟩] (map_lts_actionsList lts)).map Subtype.val := by
  intro s'
  apply Iff.intro
  -- Forward direction
  intro h_post_n_plus_1
  have h_eq : (post_S_n [s] (map_lts_actionsList lts) (n + 1)).map Subtype.val =
              (post_S_A (post_S_n [s] (map_lts_actionsList lts) n) (map_lts_actionsList lts)).map Subtype.val := by
    apply post_n_plus_one_eq_post_of_post_n

  rw [h_eq] at h_post_n_plus_1
  sorry

-- Backward direction

  intro h_exists
  cases h_exists with
  | intro s'' h_and =>
      cases h_and with
      | intro h_s''_in_post_n h_s'_in_post_s'' =>
        have h_eq : (post_S_n [s] (map_lts_actionsList lts) (n + 1)).map Subtype.val =
                    (post_S_A (post_S_n [s] (map_lts_actionsList lts) n) (map_lts_actionsList lts)).map Subtype.val := by
          apply post_n_plus_one_eq_post_of_post_n
        rw [h_eq]
        apply List.mem_map.2
        sorry











theorem post_pre_equivalence_precise {lts : LTS}
  (s : { s : State // s ∈ lts.states })
  (s' : { s : State // s ∈ lts.states })
  (n : Nat) :
  s'.val ∈ (post_S_n [s] (map_lts_actionsList lts) n).map Subtype.val ↔
  s.val ∈ pre_S_n lts [s'.val] (map_lts_actionsList lts) n := by
  induction n with
  | zero =>
    -- Base case: n = 0
    simp [post_S_n, pre_S_n]
    apply Iff.intro
    intro h
    rw [h]

    intro h
    rw [h]
  | succ n ih =>
    rw [post_S_n_succ_eq_post_S_n_post_S_n]
    apply Iff.intro
    intro h
    simp [post_S_n] at h
    sorry


-- Define the syntax of CCS0
inductive CCS0 : Type
| null : CCS0
| choice : CCS0 → CCS0 → CCS0
| prefix : Action → CCS0 → CCS0

-- Notation to make writing CCS0 expressions easier
notation "nil" => CCS0.null
infixr:65 "+" => CCS0.choice
notation:max α:max "." P:max => CCS0.prefix α P

-- Helper function to create actions easily
def act (s : String) : Action := Action.mk s

-- Examples from the image
def firecracker : CCS0 :=
  (Action.mk ("light")) . (Action.mk "bang") . nil

def defective_firecracker : CCS0 :=
  (Action.mk "light") . (Action.mk "τ") . nil

def possibly_defective_firecracker : CCS0 :=
  CCS0.prefix (act "light")
    (CCS0.choice
      (CCS0.prefix (act "τ") CCS0.null)
      (CCS0.prefix (act "bang") CCS0.null))

-- Function to print CCS0 expressions (for demonstration)
def CCS0.toString : CCS0 → String
  | CCS0.null => "0"
  | CCS0.choice p q => s!"({p.toString} + {q.toString})"
  | CCS0.prefix a p => s!"{a.val}.{p.toString}"

-- Define the transition relation for CCS0
inductive step : CCS0 → Action → CCS0 → Prop
| choice_l : ∀ P P' Q, step P α P' → step (CCS0.choice P Q) α P'
| choice_r : ∀ P Q Q', step Q α Q' → step (CCS0.choice P Q) α Q'
| prefix_inf   : ∀ α P P', step (CCS0.prefix α P) α P'

#eval firecracker.toString
#eval defective_firecracker.toString
#eval possibly_defective_firecracker.toString
#eval ((CCS0.prefix (Action.mk "a") CCS0.null + CCS0.null) + (CCS0.prefix (act "b") (CCS0.null + CCS0.null))).toString
-- Define the CCS0 expression

-- Prove the semantics using the step relation
theorem example_step_proof :
  step (CCS0.prefix (act "a") CCS0.null) (act "a") CCS0.null := by

  -- with prefix
  apply step.prefix_inf




theorem example_choice_l_proof (h : step (CCS0.prefix (act "a") CCS0.null) (act "a") CCS0.null) :
  step ((CCS0.prefix (act "a") CCS0.null + CCS0.null)) (act "a") CCS0.null := by

  -- with choice_l
  apply step.choice_l
  exact h

theorem example_choice_l_2_proof :
  step ((CCS0.prefix (act "a") CCS0.null + CCS0.null) + (CCS0.prefix (act "b") (CCS0.null + CCS0.null))) (act "a") CCS0.null := by

  apply step.choice_l
  -- Apply the previous proof
  apply example_choice_l_proof
  -- Transitioning from a.0 to 0 (with prefix)
  apply example_step_proof
