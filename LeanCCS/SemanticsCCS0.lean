import LeanCCS.LabelledTransitionSystem

/-- Define the syntax of CCS₀ (From Lecture B1) -/
inductive CCS₀ : Type
| null : CCS₀
| choice : CCS₀ → CCS₀ → CCS₀
| prefix : Action → CCS₀ → CCS₀

/-- Notation to make writing CCS₀ expressions easier -/
notation "nil" => CCS₀.null
infixr : 65 "+" => CCS₀.choice
notation : max α : max "." P : max => CCS₀.prefix α P

/-- Helper function to create actions easily -/
def act (s : String) : Action := Action.mk s

/-- Examples from lecture B1 -/
def firecracker : CCS₀ :=
  (Action.mk ("light")) . (Action.mk "bang") . nil

def defective_firecracker : CCS₀ :=
  (Action.mk "light") . (Action.mk "τ") . nil

def possibly_defective_firecracker : CCS₀ :=
    CCS₀.prefix (act "light")
  (CCS₀.choice
    (CCS₀.prefix (act "τ") CCS₀.null)
    (CCS₀.prefix (act "bang") CCS₀.null))

/-- Function to print CCS₀ expressions (for demonstration) -/
def CCS₀.toString : CCS₀ → String
  | CCS₀.null => "0"
  | CCS₀.choice p q => s!"({p.toString} + {q.toString})"
  | CCS₀.prefix a p => s!"{a.val}.{p.toString}"

/-- Inference tree rules for CCS₀ (From lecture B1) -/
inductive inference : CCS₀ → Action → CCS₀ → Prop
| choice_l (h : inference P α P') : inference (CCS₀.choice P Q) α P'
| choice_r (h : inference Q α Q') : inference (CCS₀.choice P Q) α Q'
| prefix_inf : inference (CCS₀.prefix α P) α P'

/- Printing our examples -/

#eval firecracker.toString
#eval defective_firecracker.toString
#eval possibly_defective_firecracker.toString
#eval ((CCS₀.prefix (Action.mk "a") CCS₀.null + CCS₀.null) + (CCS₀.prefix (act "b") (CCS₀.null + CCS₀.null))).toString

/-- Proof of  (a.0 + 0) + b.(0 + 0) −→ 0 (From Lecture B1)--/
theorem example_step_proof :
    inference (CCS₀.prefix (act "a") CCS₀.null) (act "a") CCS₀.null :=
  .prefix_inf

theorem example_choice_l_proof (h : inference (CCS₀.prefix (act "a") CCS₀.null) (act "a") CCS₀.null) :
    inference ((CCS₀.prefix (act "a") CCS₀.null + CCS₀.null)) (act "a") CCS₀.null :=
  h.choice_l

theorem example_choice_l_2_proof :
    inference ((CCS₀.prefix (act "a") CCS₀.null + CCS₀.null) + (CCS₀.prefix (act "b") (CCS₀.null + CCS₀.null))) (act "a") CCS₀.null :=
  inference.choice_l <| example_choice_l_proof example_step_proof
