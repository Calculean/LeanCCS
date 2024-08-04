import LeanCCS.LabelledTransitionSystem
import LeanCCS.Utils

open List

protected def LTS.post {lts : LTS} (s : { s : State // s ∈ lts.states }) (a : Action) : List { s : State // s ∈ lts.states } :=
  lts.transition s a

def post_S {lts : LTS} (states : List { s : State // s ∈ lts.states }) (a : Action) : List { s : State // s ∈ lts.states } :=
  states.foldl (fun acc state => acc ++ lts.post state a) []

def post_A {lts : LTS} (s : { s : State // s ∈ lts.states }) (actions : List Action) : List { s : State // s ∈ lts.states } :=
  actions.foldl (fun acc act => acc ++ lts.post s act) []

def post_S_A {lts : LTS} (states : List { s : State // s ∈ lts.states }) (actions : List Action) : List { s : State // s ∈ lts.states } :=
  actions.foldl (fun acc act => acc ++ post_S states act) []

def post_S_n {lts : LTS} (states : List { s : State // s ∈ lts.states }) (actions : List Action) (n : Nat) : List { s : State // s ∈ lts.states } :=
  match n with
  | 0 => states
  | n' + 1 => post_S_A (post_S_n states actions n') actions

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
