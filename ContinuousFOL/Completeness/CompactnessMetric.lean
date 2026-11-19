/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §9 Corollary 9.12 with metric; vision.md page 25–26
-/
module

public import ContinuousFOL.Completeness.CompletenessMetric
public import ContinuousFOL.Group2Axioms.SoundnessMetric
public import ContinuousFOL.LanguageAndSemantics.FormulaOne
public import ContinuousFOL.Essentials.DeductionTheorem
public import Mathlib.Data.Finset.Basic

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

/-- Corollary 9.12, metric pre-structure clause: if every finite subset is
    satisfiable, then `Γ` is satisfiable. -/
theorem compactness_metric_pre {LM : MetricSignature} (Γ : Set (Formula LM.toSignature))
    (hfin : ∀ Γ₀ : Finset (Formula LM.toSignature),
      (Γ₀ : Set (Formula LM.toSignature)) ⊆ Γ →
        SatisfiableMetricPre (Γ₀ : Set (Formula LM.toSignature))) :
    SatisfiableMetricPre Γ := by
  by_contra hsat
  have hincons : ¬ ConsistentMetricQ Γ := fun hcons =>
    hsat (metric_prestructure_model_of_consistent hcons)
  have hprov1 : ProvableMetricQ Γ (Formula.one LM.toSignature) := by
    by_contra hnot
    exact hincons ⟨Formula.one LM.toSignature, hnot⟩
  obtain ⟨Γ₀, hsub, hprov₀⟩ := ProvableMetricQ.compact hprov1
  obtain ⟨M, σ, hM⟩ := hfin Γ₀ hsub
  have hv := soundness_metric_pre (Γ₀ : Set _) (Formula.one LM.toSignature) hprov₀ M σ hM
  simp at hv

/-- Corollary 9.12, complete-structure clause. -/
theorem compactness_metric_complete {LM : MetricSignature} (Γ : Set (Formula LM.toSignature))
    (hfin : ∀ Γ₀ : Finset (Formula LM.toSignature),
      (Γ₀ : Set (Formula LM.toSignature)) ⊆ Γ →
        CompletelySatisfiable (Γ₀ : Set (Formula LM.toSignature))) :
    CompletelySatisfiable Γ := by
  rw [← completeness_metric_iff]
  by_contra hincons
  have hprov1 : ProvableMetricQ Γ (Formula.one LM.toSignature) := by
    by_contra hnot
    exact hincons ⟨Formula.one LM.toSignature, hnot⟩
  obtain ⟨Γ₀, hsub, hprov₀⟩ := ProvableMetricQ.compact hprov1
  obtain ⟨M, σ, hM⟩ := hfin Γ₀ hsub
  have hv := soundness_metric (Γ₀ : Set _) (Formula.one LM.toSignature) hprov₀ M σ hM
  simp at hv

/-- Corollary 9.12 for a signature with a metric: if every finite subset of `Γ`
    is (completely) satisfiable, then `Γ` is (completely) satisfiable. -/
theorem compactness_metric {LM : MetricSignature} (Γ : Set (Formula LM.toSignature)) :
    ((∀ Γ₀ : Finset (Formula LM.toSignature),
        (Γ₀ : Set (Formula LM.toSignature)) ⊆ Γ →
          SatisfiableMetricPre (Γ₀ : Set (Formula LM.toSignature))) →
      SatisfiableMetricPre Γ) ∧
    ((∀ Γ₀ : Finset (Formula LM.toSignature),
        (Γ₀ : Set (Formula LM.toSignature)) ⊆ Γ →
          CompletelySatisfiable (Γ₀ : Set (Formula LM.toSignature))) →
      CompletelySatisfiable Γ) :=
  ⟨compactness_metric_pre Γ, compactness_metric_complete Γ⟩

end ContinuousFOL
