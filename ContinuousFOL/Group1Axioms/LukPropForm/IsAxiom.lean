/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §3 Group 1 axioms (A1)–(A4); vision.md page 5
-/
module

public import ContinuousFOL.LukasiewiczAndContinuous.LukPropForm

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

namespace LukPropForm

/-- Axioms (A1)–(A4) for Łukasiewicz propositional logic (§3). -/
inductive IsAxiom {I : Type*} : LukPropForm I → Prop
  | A1 (φ ψ)   : IsAxiom (.tsub (.tsub φ ψ) φ)
  | A2 (φ ψ χ) : IsAxiom (.tsub (.tsub (.tsub χ φ) (.tsub χ ψ)) (.tsub ψ φ))
  | A3 (φ ψ)   : IsAxiom (.tsub (.tsub φ (.tsub φ ψ)) (.tsub ψ (.tsub ψ φ)))
  | A4 (φ ψ)   : IsAxiom (.tsub (.tsub φ ψ) (.tsub (.neg ψ) (.neg φ)))

end LukPropForm

end ContinuousFOL
