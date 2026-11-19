/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §6 Lemma 6.2; vision.md page 11
-/
module

public import ContinuousFOL.SubstitutionAndCompletions.FormulaFreeSubst
public import ContinuousFOL.LanguageAndSemantics.FormulaEval
public import ContinuousFOL.LanguageAndSemantics.UpdateAssign

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

/-- Lemma 6.2 (Substitution Lemma). -/
theorem substitution_lemma {L : Signature} (M : PreStructure L) (σ : Var → M.Carrier)
    (t : Term L) (x : Var) (φ : Formula L) (hcorr : φ.FreeSubstCorrect t x) :
    (φ.freeSubst t x).eval M σ = φ.eval M (updateAssign σ x (t.eval M σ)) := by
  sorry

end ContinuousFOL
