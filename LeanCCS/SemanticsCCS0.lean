import LeanCCS.LabelledTransitionSystem

-- Define the syntax of CCS0
inductive CCS0 : Type
| null : CCS0
| choice : CCS0 → CCS0 → CCS0
| prefix : Action → CCS0 → CCS0

-- Notation to make writing CCS0 expressions easier
notation "nil" => CCS0.null
infixr:65 "+" => CCS0.choice
notation:max α:max "." P:max => CCS0.prefix α P

-- Helper function to create actions easily
def act (s : String) : Action := Action.mk s

-- Examples from the image
def firecracker : CCS0 :=
  (Action.mk ("light")) . (Action.mk "bang") . nil

def defective_firecracker : CCS0 :=
  (Action.mk "light") . (Action.mk "τ") . nil

def possibly_defective_firecracker : CCS0 :=
  CCS0.prefix (act "light")
    (CCS0.choice
      (CCS0.prefix (act "τ") CCS0.null)
      (CCS0.prefix (act "bang") CCS0.null))

-- Function to print CCS0 expressions (for demonstration)
def CCS0.toString : CCS0 → String
  | CCS0.null => "0"
  | CCS0.choice p q => s!"({p.toString} + {q.toString})"
  | CCS0.prefix a p => s!"{a.val}.{p.toString}"

-- Define the transition relation for CCS0
inductive inference : CCS0 → Action → CCS0 → Prop
| choice_l : ∀ P P' Q, inference P α P' → inference (CCS0.choice P Q) α P'
| choice_r : ∀ P Q Q', inference Q α Q' → inference (CCS0.choice P Q) α Q'
| prefix_inf   : ∀ α P P', inference (CCS0.prefix α P) α P'

#eval firecracker.toString
#eval defective_firecracker.toString
#eval possibly_defective_firecracker.toString
#eval ((CCS0.prefix (Action.mk "a") CCS0.null + CCS0.null) + (CCS0.prefix (act "b") (CCS0.null + CCS0.null))).toString



-- Prove the semantics using the step relation
theorem example_step_proof :
  inference (CCS0.prefix (act "a") CCS0.null) (act "a") CCS0.null := by

  -- with prefix
  apply inference.prefix_inf




theorem example_choice_l_proof (h : inference (CCS0.prefix (act "a") CCS0.null) (act "a") CCS0.null) :
  inference ((CCS0.prefix (act "a") CCS0.null + CCS0.null)) (act "a") CCS0.null := by

  -- with choice_l
  apply inference.choice_l
  exact h

theorem example_choice_l_2_proof :
  inference ((CCS0.prefix (act "a") CCS0.null + CCS0.null) + (CCS0.prefix (act "b") (CCS0.null + CCS0.null))) (act "a") CCS0.null := by

  apply inference.choice_l
  -- Apply the previous proof
  apply example_choice_l_proof
  -- Transitioning from a.0 to 0 (with prefix)
  apply example_step_proof
