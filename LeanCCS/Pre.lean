import LeanCCS.LabelledTransitionSystem
import LeanCCS.Utils

open List

local instance instBEqSubtype {α : Type _} [BEq α] (P: α → Prop) : BEq (Subtype P) where
  beq a b := a.val == b.val

local instance {lts : LTS} : BEq { s : State // s ∈ lts.states } := instBEqSubtype _

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
