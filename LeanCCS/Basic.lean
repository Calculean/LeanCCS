import Batteries.Data.List.Basic

structure State where
  val : String
deriving BEq

structure Action where
  val : String

structure LTS where
  states : List State
  actions : List Action
  transition : State → Action → List State
  s0 : State

def transition (s : State) (a : Action) : List State :=
  match (s.val, a.val) with
  | ("UNUSED", "strike") => [State.mk "BURNING"]
  | ("BURNING", "extinguish") => [State.mk "EXTINCT"]
  | _ => []


def concatLists (lists : List (List α)) : List α :=
  lists.foldl (init := []) (fun acc lst => acc ++ lst)

#eval concatLists [[1, 2, 3], [4, 5], [6, 7, 8, 9]]

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
