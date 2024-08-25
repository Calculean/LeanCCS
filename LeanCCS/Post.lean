import LeanCCS.LabelledTransitionSystem
import LeanCCS.Utils


/-- Post (s,a)  definition (from lecture A1)-/
def post {lts : LTS} (s : { s : State // s ∈ lts.states }) (a : {a : Action // a ∈ lts.actions }) :
    List { s : State // s ∈ lts.states } :=
  lts.transition s a


#eval (post exampleLTS.s0 ⟨{ val := "a" }, a_in_actions⟩).map (fun s => s.val.val)
#eval (post ⟨{ val := "S2" }, s2_in_states⟩ ⟨{ val := "b" }, b_in_actions⟩).map (fun s => s.val.val)

/-- Post (S,a) definition (from lecture A1)-/
def post_S {lts : LTS} (states : List { s : State // s ∈ lts.states }) (a : { a : Action // a ∈ lts.actions }) :
    List { s : State // s ∈ lts.states } :=
  states.foldl (fun acc state => acc ++ post state a) []

/-- Post (s,A) definition (from lecture A1)-/
def post_A {lts : LTS} (s : { s : State // s ∈ lts.states }) (actions : List { a : Action // a ∈ lts.actions }) :
    List { s : State // s ∈ lts.states } :=
  actions.foldl (fun acc act => acc ++ post s act) []

/-- Post (S,A) definition (from lecture A1)-/
def post_S_A {lts : LTS} (states : List { s : State // s ∈ lts.states }) (actions : List { a : Action // a ∈ lts.actions }) :
    List { s : State // s ∈ lts.states } :=
  actions.foldl (fun acc act => acc ++ post_S states act) []

/-- Post definition from Reachability section (from lecture A2)-/
def post_S_n {lts : LTS} (states : List { s : State // s ∈ lts.states }) (actions : List { a : Action // a ∈ lts.actions }) (n : Nat) :
    List { s : State // s ∈ lts.states } :=
  match n with
  | 0 => states
  | n' + 1 => post_S_A (post_S_n states actions n') actions

theorem c_in_actions :
    { val := "c" } ∈ exampleLTS.actions := by
  simp [exampleLTS]

#eval "Initial state: S1"
#eval "Actions sequence: a, b, c"

def initial_states : List { s : State // s ∈ exampleLTS.states } :=
  [⟨{ val := "S1" }, s1_in_states⟩]

def actions : List { a : Action // a ∈ exampleLTS.actions } :=
[
  ⟨{ val := "a" }, a_in_actions⟩,
  ⟨{ val := "b" }, b_in_actions⟩,
  ⟨{ val := "c" }, c_in_actions⟩
]

#eval (post_S_n initial_states actions 0).map (fun s => s.val.val)
#eval (post_S_n initial_states actions 1).map (fun s => s.val.val)
#eval (post_S_n initial_states actions 2).map (fun s => s.val.val)
#eval (post_S_n initial_states actions 0).map (fun s => s.val.val)
#eval (post_S_n initial_states actions 1).map (fun s => s.val.val)
#eval (post_S_n initial_states actions 2).map (fun s => s.val.val)

/-- Define the Match Lifecycle LTS (from Lecture A1) -/
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

/-- Proofs for states and actions-/

theorem unused_in_states : { val := "UNUSED" } ∈ matchLTS.states := by
  simp [matchLTS]

theorem burning_in_states : { val := "BURNING" } ∈ matchLTS.states := by
  simp [matchLTS]

theorem extinct_in_states : { val := "EXTINCT" } ∈ matchLTS.states := by
  simp [matchLTS]

theorem strike_in_actions : { val := "strike" } ∈ matchLTS.actions := by
  simp [matchLTS]

theorem extinguish_in_actions : { val := "extinguish" } ∈ matchLTS.actions := by
  simp [matchLTS]

def match_initial_states : List { s : State // s ∈ matchLTS.states } :=
  [⟨{ val := "UNUSED" }, unused_in_states⟩]

def match_actions : List { a : Action // a ∈ matchLTS.actions } :=
[
  ⟨{ val := "strike" }, strike_in_actions⟩,
  ⟨{ val := "extinguish" }, extinguish_in_actions⟩
]

#eval (post_S_n match_initial_states match_actions 2).map (fun s => s.val.val)

open List


/-- Reach definition from Lecture B1-/
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


/-- Theorem : post_S_n states actions (n + 1) = post_S_n (post_S_n states actions n) actions 1 --/
theorem post_S_n_succ_eq_post_S_n_post_S_n {lts : LTS}
    (states : List { s : State // s ∈ lts.states })
    (actions : List { a : Action // a ∈ lts.actions })
    (n : Nat) :
    post_S_n states actions (n + 1) = post_S_n (post_S_n states actions n) actions 1 :=
  rfl

/-- Theorem : (post_S_n [s] (map_lts_actionsList lts) (n + 1)) = (post_S_A (post_S_n [s] (map_lts_actionsList lts) n) (map_lts_actionsList lts)) --/
theorem post_n_plus_one_eq_post_of_post_n {lts : LTS}
    (s : { s : State // s ∈ lts.states })
    (n : Nat) :
    (post_S_n [s] (map_lts_actionsList lts) (n + 1)).map Subtype.val =
    (post_S_A (post_S_n [s] (map_lts_actionsList lts) n) (map_lts_actionsList lts)).map Subtype.val :=
  rfl
