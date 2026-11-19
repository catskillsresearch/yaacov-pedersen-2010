/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §6 Theorem 6.8; vision.md page 12–13
-/
module

public import ContinuousFOL.LanguageAndSemantics.MetricPreStructure
public import ContinuousFOL.LanguageAndSemantics.FormulaEval
public import ContinuousFOL.SubstitutionAndCompletions.FormulaFreeVars

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

/-- Theorem 6.8: Induced mappings of terms and formulae on `M^n` are uniformly continuous. -/
theorem eval_uniformly_continuous {LM : MetricSignature} (M : MetricPreStructure LM)
    (n : ℕ) (xs : Fin n ↪ Var) (φ : Formula LM.toSignature)
    (hvars : ∀ v ∈ φ.freeVars, v ∈ Set.range xs) :
    ∀ ε > 0, ∃ δ > 0, ∀ (a b : Fin n → M.Carrier),
      (∀ i, M.distVal (a i) (b i) < δ) →
      |φ.eval M.toPreStructure (fun v =>
          if h : ∃ i, xs i = v then a (Classical.choose h) else Classical.arbitrary M.Carrier) -
       φ.eval M.toPreStructure (fun v =>
          if h : ∃ i, xs i = v then b (Classical.choose h) else Classical.arbitrary M.Carrier)| ≤ ε := by
  sorry

end ContinuousFOL
