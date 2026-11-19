/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §3 Group 1 axioms (A1)–(A6); vision.md page 5
-/
module

public import ContinuousFOL.LukasiewiczAndContinuous.CLPropForm

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

namespace CLPropForm

/-- Axioms (A1)–(A6) for Continuous Propositional Logic (§3). -/
inductive IsAxiom {I : Type*} : CLPropForm I → Prop
  | A1 (φ ψ)   : IsAxiom (.tsub (.tsub φ ψ) φ)
  | A2 (φ ψ χ) : IsAxiom (.tsub (.tsub (.tsub χ φ) (.tsub χ ψ)) (.tsub ψ φ))
  | A3 (φ ψ)   : IsAxiom (.tsub (.tsub φ (.tsub φ ψ)) (.tsub ψ (.tsub ψ φ)))
  | A4 (φ ψ)   : IsAxiom (.tsub (.tsub φ ψ) (.tsub (.neg ψ) (.neg φ)))
  | A5 (φ)     : IsAxiom (.tsub (.half φ) (.tsub φ (.half φ)))
  | A6 (φ)     : IsAxiom (.tsub (.tsub φ (.half φ)) (.half φ))

end CLPropForm

end ContinuousFOL
