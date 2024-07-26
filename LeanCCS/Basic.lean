import Batteries.Data.List.Perm

open List

set_option autoImplicit true

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
  transition : State → Action → List { s : State // s ∈ states }
  s0 : State

def ValidState (lts : LTS) :=
  { s : State // s ∈ lts.states }

def post {lts : LTS} (s : { s : State // s ∈ lts.states }) (a : Action) : List { s : State // s ∈ lts.states } :=
  lts.transition s a


def post_S {lts : LTS} (states : List { s : State // s ∈ lts.states }) (a : Action) : List { s : State // s ∈ lts.states } :=
  states.foldl (fun acc state => acc ++ post state a) []

def post_A {lts : LTS} (s : { s : State // s ∈ lts.states }) (actions : List Action) : List { s : State // s ∈ lts.states } :=
  actions.foldl (fun acc act => acc ++ post s act) []

def post_S_A {lts : LTS} (states : List { s : State // s ∈ lts.states }) (actions : List Action) : List { s : State // s ∈ lts.states } :=
  actions.foldl (fun acc act => acc ++ post_S states act) []

def post_S_n {lts : LTS} (states : List { s : State // s ∈ lts.states }) (actions : List Action) (n : Nat) : List { s : State // s ∈ lts.states } :=
  match n with
  | 0 => states
  | n' + 1 => post_S_A (post_S_n states actions n') actions

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
      reach_aux lts ⟨s::visited, hx⟩ (  (post_A  s lts.actions)  ++ ss) ( (post_A  s lts.actions).map Subtype.val ++ acc )
termination_by (lts.states.length - visited.1.length, to_visit.length)


def reach {lts : LTS} (initial_states : List { s : State // s ∈ lts.states }) : List State :=
  reach_aux lts ⟨[], nil_subperm⟩ initial_states []

local instance instBEqSubtype {α : Type _} [BEq α] (P: α → Prop) : BEq (Subtype P) where
  beq a b := a.val == b.val

local instance instLawfulBEqSubtype {α :Type _} [BEq α] [i:LawfulBEq α] (P : α → Prop) :
    LawfulBEq (Subtype P) where
  eq_of_beq := by
    intro a b
    dsimp [BEq.beq]
    intro h
    ext
    exact i.eq_of_beq h
  rfl := by
    intro a
    dsimp [BEq.beq]
    exact i.rfl


def pre {lts : LTS} (s : { s : State // s ∈ lts.states }) (a : Action) : List { s : State // s ∈ lts.states } :=
  List.filter (fun st => (lts.transition st a).indexOf? s != none  ) lts.states













/-
def transition {lts : LTS} (h : lts.states = [State.mk "UNUSED", State.mk "BURNING", State.mk "EXTINCT"]) (s : State) (a : Action) : List { s : State // s ∈ lts.states } :=
  match (s.val, a.val) with
  | ("UNUSED", "strike") => [State.mk "BURNING"]
  | ("BURNING", "extinguish") => [State.mk "EXTINCT"]
  | _ => []

example : LTS :=
  LTS.mk
    [State.mk "UNUSED", State.mk "BURNING", State.mk "EXTINCT"]

    [Action.mk "strike",Action.mk "extinguish",]
    transition
    (State.mk "UNUSED")

def post (lts : LTS) (s : State) (a : Action) : List State :=
  lts.transition s a

def post_S (lts : LTS) (states : List State) (a : Action) : List State :=
  states.foldl (fun acc state => acc ++ post lts state a) []

def post_A (lts : LTS) (s : State) (actions : List Action) : List State :=
  actions.foldl (fun acc act => acc ++ post lts s act) []

def post_S_A (lts : LTS) (states : List State) (actions : List Action) : List State :=
  actions.foldl (fun acc act => acc ++ post_S lts states act) []

def post_S_n (lts : LTS) (states : List State) (actions : List Action) (n : Nat) : List State :=
  match n with
  | 0 => states
  | n' + 1 => post_S_A lts (post_S_n lts states actions n') actions

def elem {α} [BEq α] (x : α) (xs : List α) : Bool :=
  xs.any (fun y => x == y)

partial def reach_aux (lts : LTS) (visited : List State) (to_visit : List State) (acc : List State): List State :=
  match to_visit with
  | [] => acc
  | s::ss =>
    if visited.indexOf? s != none then
      reach_aux lts visited ss acc
    else
      reach_aux lts (s::visited) (  (post_A lts s lts.actions)  ++ ss) ( (post_A lts s lts.actions) ++ acc )

def reach (lts : LTS) (initial_states : List State) : List State :=
  reach_aux lts [] initial_states []

def reach_lts (lts : LTS) : List State :=
  reach lts [lts.s0]

def pre (lts : LTS) (s : State) (a : Action) : List State :=
  List.filter (fun s' => (post lts s' a).any (fun s'' => s'' == s)) lts.states

def pre_A (lts : LTS) (s : State) (actions : List Action) : List State :=
  List.filter (fun s' => actions.all (fun a => (post lts s' a).any (fun s'' => s'' == s))) lts.states

def pre_S_a (lts : LTS) (states : List State) (a : Action) : List State :=
  states.foldl (fun acc state => acc ++ pre lts state a) []

def pre_S_A (lts : LTS) (states : List State) (actions : List Action) : List State :=
  actions.foldl (fun acc action => acc ++ pre_S_a lts states action) []


def pre_S_n (lts : LTS) (states : List State) (actions : List Action) (n : Nat) : List State :=
  match n with
  | 0 => states
  | n' + 1 => pre_S_A lts (pre_S_n lts states actions n') actions


partial def pre_star_aux (lts : LTS) (visited : List State) (to_visit : List State) : List State :=
  match to_visit with
  | [] => visited
  | s::ss =>
    if elem s  visited then
      pre_star_aux lts visited ss
    else
      pre_star_aux lts (s::visited) ((concatLists (List.map (fun a => pre lts s a) lts.actions)) ++ ss)

def pre_star (lts : LTS) (initial_states : List State) : List State :=
  pre_star_aux lts [] initial_states


theorem reach_pre_star_equivalence (lts : LTS) (s s' : State) :
    s' ∈ reach lts [s] ↔ s ∈ pre_star lts [s'] :=
  sorry
-/
