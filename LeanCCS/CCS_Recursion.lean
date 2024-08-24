import LeanCCS.LabelledTransitionSystem
-- First, let's define a type for recursion variables
inductive Var : Type
| mk : String → Var
deriving DecidableEq

-- Now, let's modify the CCS0 definition
inductive CCS0 : Type
| null : CCS0
| var : Var → CCS0  -- New constructor for variables
| choice : CCS0 → CCS0 → CCS0
| prefix : Action → CCS0 → CCS0

-- Define a type for recursion equations
def RecursionEquation := Var -> Option CCS0

-- Define the type for the recursion function
structure RecursionFunction where
  func : Var → Option CCS0
-- Notation to make writing CCS0 expressions easier
notation "nil" => CCS0.null
infixr:65 "+" => CCS0.choice
notation:max α:max "." P:max => CCS0.prefix α P
notation:max "var" v:max => CCS0.var v

-- Helper function to create actions easily
def act (s : String) : Action := Action.mk s

-- Helper function to create variables easily
def var_ (s : String) : Var := Var.mk s

-- Example of how to use the new syntax:
def example_with_recursion (Γ : RecursionFunction) : CCS0 :=
  CCS0.var (var_ "X")

-- The actual behavior would depend on Γ, which would contain the defining equations
-- For example, Γ might be [(var "X", act "a" . act "b" . var "X")]

inductive step : RecursionFunction → CCS0 → Action → CCS0 → Prop
| choice_l {Γ : RecursionFunction} {P Q P' : CCS0} {α : Action} :
    step Γ P α P' → step Γ (CCS0.choice P Q) α P'
| choice_r {Γ : RecursionFunction} {P Q Q' : CCS0} {α : Action} :
    step Γ Q α Q' → step Γ (CCS0.choice P Q) α Q'
| prefix {Γ : RecursionFunction} {α : Action} {P : CCS0} :
    step Γ (CCS0.prefix α P) α P
| recursion {Γ : RecursionFunction} { X : Var } {α : Action} {P P' : CCS0} :
    Γ.func X = some P → step Γ P α P' → step Γ (CCS0.var (X) ) α P'

-- First, let's define the specific variable we want to use
def X : Var := var_ "X"


-- Now, let's define our recursion function
def recursion_alpha_X : RecursionFunction := {
  func := fun v =>
    if v = X then
      some (CCS0.prefix (act "α") (CCS0.var X))
    else
      none
}
theorem step_X_to_X :
  step recursion_alpha_X (CCS0.var X) (act "α") (CCS0.var X) := by
sorry
