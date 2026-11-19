/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §6 Corollary 6.11; vision.md page 13
-/
module

public import ContinuousFOL.SubstitutionAndCompletions.ExistsMetricCompletion
public import ContinuousFOL.LanguageAndSemantics.EntailsPre
public import ContinuousFOL.LanguageAndSemantics.CompletelySatisfiable

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

/-- Corollary 6.11: Pre-structure entailment/satisfiability coincides with complete metric
    entailment/satisfiability. -/
theorem entails_metric_iff_complete {LM : MetricSignature}
    (Γ : Set (Formula LM.toSignature)) (φ : Formula LM.toSignature) :
    EntailsMetricPre Γ φ ↔ EntailsComplete Γ φ := by
  constructor
  · intro h M σ hM
    exact h M.toMetricPreStructure σ hM
  · intro h M σ hM
    obtain ⟨Mhat, ⟨e⟩⟩ := exists_metric_completion M
    have hMhat : ModelsPre Mhat.toPreStructure (e.toFun ∘ σ) Γ := by
      intro ψ hψ
      rw [← e.map_eval σ ψ]
      exact hM ψ hψ
    rw [e.map_eval σ φ]
    exact h Mhat (e.toFun ∘ σ) hMhat

theorem satisfiable_metric_iff_complete {LM : MetricSignature}
    (Γ : Set (Formula LM.toSignature)) :
    SatisfiableMetricPre Γ ↔ CompletelySatisfiable Γ := by
  constructor
  · rintro ⟨M, σ, hM⟩
    obtain ⟨Mhat, ⟨e⟩⟩ := exists_metric_completion M
    refine ⟨Mhat, e.toFun ∘ σ, ?_⟩
    intro ψ hψ
    rw [← e.map_eval σ ψ]
    exact hM ψ hψ
  · rintro ⟨M, σ, hM⟩
    exact ⟨M.toMetricPreStructure, σ, hM⟩

end ContinuousFOL
