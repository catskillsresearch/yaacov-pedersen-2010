/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §9 Theorem 9.5 with metric; vision.md page 23
-/
module

public import ContinuousFOL.Completeness.HenkinModelExistenceMetric
public import ContinuousFOL.Group2Axioms.SoundnessMetric
public import ContinuousFOL.SubstitutionAndCompletions.EntailsMetricIffComplete

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

/-- Theorem 9.5 (Completeness for Continuous First-Order Logic — with complete metric). -/
theorem completeness_metric {LM : MetricSignature} (Γ : Set (Formula LM.toSignature)) :
    ConsistentMetricQ Γ → CompletelySatisfiable.{0} Γ := by
  intro hcons
  obtain ⟨M, σ, hM⟩ := metric_prestructure_model_of_consistent hcons
  exact (satisfiable_metric_iff_complete.{0} Γ).mp ⟨M, σ, hM⟩

/-- Theorem 9.5 (metric) together with soundness (Theorem 7.2): `Γ` is consistent iff
completely satisfiable (helper; not a paper statement). -/
theorem completeness_metric_iff {LM : MetricSignature} (Γ : Set (Formula LM.toSignature)) :
    ConsistentMetricQ Γ ↔ CompletelySatisfiable.{0} Γ :=
  ⟨completeness_metric Γ, satisfiable_consistent_metric Γ⟩

end ContinuousFOL
