/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §7 (A1)–(A9); vision.md page 14
-/
module

public import ContinuousFOL.SubstitutionAndCompletions.FormulaFreeSubst
public import ContinuousFOL.Group2Axioms.FormulaGenList

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

/-- Core axiom schemata (A1)–(A9) for an arbitrary continuous signature `L` (§3, §7). -/
inductive BaseAxiomSchema {L : Signature} : Formula L → Prop
  | A1 (φ ψ)   : BaseAxiomSchema (.tsub (.tsub φ ψ) φ)
  | A2 (φ ψ χ) : BaseAxiomSchema (.tsub (.tsub (.tsub χ φ) (.tsub χ ψ)) (.tsub ψ φ))
  | A3 (φ ψ)   : BaseAxiomSchema (.tsub (.tsub φ (.tsub φ ψ)) (.tsub ψ (.tsub ψ φ)))
  | A4 (φ ψ)   : BaseAxiomSchema (.tsub (.tsub φ ψ) (.tsub (.neg ψ) (.neg φ)))
  | A5 (φ)     : BaseAxiomSchema (.tsub (.half φ) (.tsub φ (.half φ)))
  | A6 (φ)     : BaseAxiomSchema (.tsub (.tsub φ (.half φ)) (.half φ))
  | A7 (x φ ψ) : BaseAxiomSchema (.tsub (.tsub (.sup x ψ) (.sup x φ)) (.sup x (.tsub ψ φ)))
  | A8 (x t φ) : φ.FreeSubstCorrect t x → BaseAxiomSchema (.tsub (φ.freeSubst t x) (.sup x φ))
  | A9 (x φ)   : x ∉ φ.freeVars → BaseAxiomSchema (.tsub (.sup x φ) φ)

end ContinuousFOL
