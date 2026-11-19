/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §7 Theorem 7.2 with metric; vision.md page 15
-/
module

public import ContinuousFOL.Group2Axioms.ConsistentQ
public import ContinuousFOL.LanguageAndSemantics.CompletelySatisfiable
public import ContinuousFOL.LanguageAndSemantics.FormulaOne

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

/-- Theorem 7.2 (Soundness) for signatures with a metric. -/
theorem soundness_metric {LM : MetricSignature} (Γ : Set (Formula LM.toSignature))
    (φ : Formula LM.toSignature) :
    ProvableMetricQ Γ φ → EntailsComplete Γ φ := by
  sorry

theorem satisfiable_consistent_metric {LM : MetricSignature}
    (Γ : Set (Formula LM.toSignature)) :
    CompletelySatisfiable Γ → ConsistentMetricQ Γ := by
  rintro ⟨M, σ, hM⟩
  refine ⟨Formula.one LM.toSignature, fun hprov => ?_⟩
  have hval := soundness_metric Γ (Formula.one LM.toSignature) hprov M σ hM
  simp at hval

end ContinuousFOL
