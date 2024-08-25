import LeanCCS.LabelledTransitionSystem

/-- Defining a type for recursion variables -/
inductive Var : Type
  | mk : String → Var
deriving DecidableEq

/-- Definition of CCS with Recursion (From Lecture B2) -/
inductive CCS₀ : Type
  | null : CCS₀
/-- New constructor for variables -/
  | var : Var → CCS₀
  | choice : CCS₀ → CCS₀ → CCS₀
  | prefix : Action → CCS₀ → CCS₀

namespace CCS₀

/-- Define a type for recursion equations -/
def RecursionEquation := Var -> Option CCS₀

/-- Define the type for the recursion function -/
structure RecursionFunction where
  func : Var → Option CCS₀

namespace RecursionFunction

/-- Notation to make writing CCS₀ expressions easier -/
notation "nil" => CCS₀.null
infixr:65 "+" => CCS₀.choice
notation:max α:max "." P:max => CCS₀.prefix α P
notation:max "var" v:max => CCS₀.var v

section String

variable (s : String)

/-- Helper function to create actions easily -/
def act : Action :=
  Action.mk s

/-- Helper function to create variables easily -/
def var_ : Var :=
  Var.mk s

end String

/-- Example of how to use the new syntax: -/
def example_with_recursion : CCS₀ :=
  CCS₀.var (var_ "X")

/--
  Inference rules for CCS with Recursion
-/
inductive inference : RecursionFunction → CCS₀ → Action → CCS₀ → Prop
  | choice_l {Γ : RecursionFunction} {P Q P' : CCS₀} {α : Action} :
      inference Γ P α P' → inference Γ (CCS₀.choice P Q) α P'
  | choice_r {Γ : RecursionFunction} {P Q Q' : CCS₀} {α : Action} :
      inference Γ Q α Q' → inference Γ (CCS₀.choice P Q) α Q'
  | prefix {Γ : RecursionFunction} {α : Action} {P : CCS₀} :
      inference Γ (CCS₀.prefix α P) α P
  | recursion {Γ : RecursionFunction} { X : Var } {α : Action} {P P' : CCS₀} :
      Γ.func X = some P → inference Γ P α P' → inference Γ (CCS₀.var (X) ) α P'

/-- Define variable X -/
def X : Var := var_ "X"

/-- Define a recursion function Γ = {(X, a.X)} -/
def recursion_alpha_X : RecursionFunction where
  func := fun v =>
    if v = X then
      some (CCS₀.prefix (act "α") (CCS₀.var X))
    else
      none

/-- Inference tree for X -> X with Γ = {(X, a.X)} (From Lecture B2 )-/
theorem inference_X_to_X :
    inference recursion_alpha_X (CCS₀.var X) (act "α") (CCS₀.var X) :=
  inference.recursion rfl inference.prefix

def Y : Var := var_ "Y"

/-- Define a recursion function Γ = {(X, 0 + Y) , (Y , a.X)} -/
def recursion_alpha_X_2 : RecursionFunction where
  func := fun v =>
    if v = X then
      some (CCS₀.choice CCS₀.null (CCS₀.var Y))
    else if v = Y then
      some (CCS₀.prefix (act "α") (CCS₀.var X))
    else
      none

/-- Inference tree for X -> X with Γ = {(X, 0 + Y) , (Y , a.X)}  (From Lecture B2 )-/
theorem inference_X_to_X_2 :
    inference recursion_alpha_X_2 (CCS₀.var X) (act "α") (CCS₀.var X) :=
  inference.recursion
    (show recursion_alpha_X_2.func X = some (CCS₀.choice CCS₀.null (CCS₀.var Y)) from rfl)
    (inference.choice_r
      (inference.recursion
        (show recursion_alpha_X_2.func Y = some (CCS₀.prefix (act "α") (CCS₀.var X)) from rfl)
        inference.prefix))


end RecursionFunction

end CCS₀
