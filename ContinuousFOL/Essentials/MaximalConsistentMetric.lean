/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §8 Definition 8.8 (metric) / Theorem 8.10 metric; vision.md pages 18–19
-/
module

public import ContinuousFOL.Group2Axioms.ConsistentQ
public import ContinuousFOL.LanguageAndSemantics.FormulaDyadic

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

structure MaximalConsistentMetric {LM : MetricSignature}
    (Δ : Set (Formula LM.toSignature)) : Prop where
  consistent : ConsistentMetricQ Δ
  archimedean : ∀ φ,
    (∀ n : ℕ, ProvableMetricQ Δ (.tsub φ (Formula.pow2Neg LM.toSignature n))) → φ ∈ Δ
  comparable  : ∀ φ ψ, Formula.tsub φ ψ ∈ Δ ∨ Formula.tsub ψ φ ∈ Δ

/-- Theorem 8.10 metric variant. -/
theorem exists_maximal_consistent_metric {LM : MetricSignature}
    {Γ : Set (Formula LM.toSignature)} (hcons : ConsistentMetricQ Γ) :
    ∃ Δ : Set (Formula LM.toSignature), Γ ⊆ Δ ∧ MaximalConsistentMetric Δ := by
  sorry

end ContinuousFOL
