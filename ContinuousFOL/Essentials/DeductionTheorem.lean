/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §8 Theorem 8.1; vision.md page 16
-/
module

public import ContinuousFOL.Group2Axioms.ProvableQ
public import ContinuousFOL.Group2Axioms.ProvableMetricQ
public import ContinuousFOL.LanguageAndSemantics.FormulaIterSub

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

/-- Theorem 8.1 (Weak Deduction Theorem). -/
theorem deduction_theorem {L : Signature} (Γ : Set (Formula L)) (φ ψ : Formula L) :
    ProvableQ (Γ ∪ {ψ}) φ ↔ ∃ n : ℕ, ProvableQ Γ (Formula.iterSub φ ψ n) := by
  sorry

theorem deduction_theorem_metric {LM : MetricSignature}
    (Γ : Set (Formula LM.toSignature)) (φ ψ : Formula LM.toSignature) :
    ProvableMetricQ (Γ ∪ {ψ}) φ ↔
      ∃ n : ℕ, ProvableMetricQ Γ (Formula.iterSub φ ψ n) := by
  sorry

end ContinuousFOL
