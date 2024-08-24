

def firecracker : CCS0 :=
  (Action.mk ("light")) . (Action.mk "bang") . nil

def defective_firecracker : CCS0 :=
  (Action.mk "light") . (Action.mk "τ") . nil

def possibly_defective_firecracker : CCS0 :=
  CCS0.prefix (act "light")
    (CCS0.choice
      (CCS0.prefix (act "τ") CCS0.null)
      (CCS0.prefix (act "bang") CCS0.null))
