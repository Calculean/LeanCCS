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
theorem post_S_n_zero {lts : LTS}
  (states : List { s : State // s ∈ lts.states })
  (actions : List { a : Action // a ∈ lts.actions }) :
  post_S_n states actions 0 = states := by
  rfl  -- reflexivity is enough because this is true by definition

theorem post_S_n_plus_one_eq_postA_post_S_n {lts : LTS}
  (states : List { s : State // s ∈ lts.states })
  (actions : List { a : Action // a ∈ lts.actions }) :
  post_S_n states actions (n + 1) = post_S_A (post_S_n states actions n) actions := by
  simp
  rfl


theorem post_S_n_succ_eq_post_S_n_post_S_n {lts : LTS}
  (states : List { s : State // s ∈ lts.states })
  (actions : List { a : Action // a ∈ lts.actions })
  (n : Nat) :
  post_S_n states actions (n + 1) = post_S_n (post_S_n states actions n) actions 1 := by
  induction n with
  | zero =>
    simp
    rw [post_S_n_zero]
  | succ n IH =>
    rw [post_S_n_plus_one_eq_postA_post_S_n]







-- Theorem: Post_S_n (n+1) = Post_S_A (Post_S_n n)
--theorem post_S_n_succ_eq_post_S_n_post_S_n_2 {lts : LTS}
  --(states : List { s : State // s ∈ lts.states })
  --(actions : List { a : Action // a ∈ lts.actions })
  --(n : Nat) :
  --post_S_n states actions (n + 1) = post_S_n (post_S_n states actions n) actions 1 := by
  --induction n generalizing states
  --simp
  --rw [post_S_n_zero]
  --rw [post_S_n_plus_one_eq_postA_post_S_n]
