import LeanCCS.LabelledTransitionSystem
import LeanCCS.Utils

open List

local instance instBEqSubtype {α : Type _} [BEq α] (P: α → Prop) : BEq (Subtype P) where
  beq a b := a.val == b.val

local instance {lts : LTS} : BEq { s : State // s ∈ lts.states } := instBEqSubtype _

def pre {lts : LTS} (s : { s : State // s ∈ lts.states }) (a : Action) : List { s : State // s ∈ lts.states } :=
  List.filter (fun st => (lts.transition st a).indexOf? s != none) <| map_lts_statesList lts

def pre_A (lts : LTS) (s : State) (actions : List Action) : List State :=
  let s_subtype : Option { s : State // s ∈ lts.states } :=
    if h : s ∈ lts.states then some ⟨s, h⟩ else none
  match s_subtype with
  | none => []
  | some s' =>
    actions.foldl (fun acc a => acc ++ (pre s' a).map Subtype.val) []

def pre_S (lts : LTS) (states : List State) (a : Action) : List State :=
  states.foldl (fun acc s =>
    let s_subtype : Option { s : State // s ∈ lts.states } :=
      if h : s ∈ lts.states then some ⟨s, h⟩ else none
    match s_subtype with
    | none => acc
    | some s' => acc ++ (pre s' a).map Subtype.val
  ) []

def pre_S_A (lts : LTS) (states : List State) (actions : List Action) : List State :=
  actions.foldl (fun acc action => acc ++ pre_S lts states action) []

def pre_S_n (lts : LTS) (states : List State) (actions : List Action) (n : Nat) : List State :=
  match n with
  | 0 => states
  | n' + 1 => pre_S_A lts (pre_S_n lts states actions n') actions
