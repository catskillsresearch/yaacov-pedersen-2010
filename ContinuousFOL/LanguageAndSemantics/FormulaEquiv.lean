/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §5 Definition 5.14; vision.md page 10
-/
module

public import ContinuousFOL.LanguageAndSemantics.FormulaEval

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

/-- Logical equivalence `φ ≡ ψ` (Definition 5.14). -/
def FormulaEquiv {L : Signature} (φ ψ : Formula L) : Prop :=
  ∀ (M : PreStructure L) (σ : Var → M.Carrier), φ.eval M σ = ψ.eval M σ

infix:50 " ≡ᶠ " => FormulaEquiv

end ContinuousFOL
